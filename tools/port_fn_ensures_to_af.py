#!/usr/bin/env python3
"""
Port function-level ensures Q → ensures af(Q) in Verus source files.

ONLY wraps function/method/closure ensures. Does NOT wrap:
- Loop ensures (while/loop/for ... ensures ...)
- Spec function ensures
- Already-temporal ensures (ag, af, au, etc.)
- requires, invariant, decreases clauses

Strategy: Track whether we're in a function signature context vs loop context
by looking at preceding keywords.
"""
import re
import sys
import os

TEMPORAL_OPS = frozenset(['ag', 'af', 'au', 'eg', 'ef', 'eu', 'an', 'en', 'ax', 'ex'])

def is_temporal(s):
    s = s.strip()
    for op in TEMPORAL_OPS:
        if s.startswith(op + '(') or s.startswith(op + ' (') or s.startswith(op + '\n'):
            return True
    return False

def process_file(filepath, dry_run=False):
    with open(filepath, 'r') as f:
        lines = f.readlines()
    
    changes = 0
    new_lines = []
    
    # Track context: are we in a loop spec or function spec?
    # We look backwards from each `ensures` to determine context.
    
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()
        
        # Quick check: does this line start with `ensures`?
        if not re.match(r'^ensures\b', stripped):
            new_lines.append(line)
            i += 1
            continue
        
        # Found `ensures` keyword. Determine context by looking backwards.
        context = determine_context(lines, new_lines, i)
        
        if context == 'loop':
            # Loop ensures — don't wrap
            new_lines.append(line)
            i += 1
            continue
        
        if context == 'spec':
            # Spec function ensures — don't wrap
            new_lines.append(line)
            i += 1
            continue
        
        # Function/proof/exec ensures — collect the full ensures clause
        # and wrap each non-temporal expression in af()
        
        indent_match = re.match(r'^(\s*)', line)
        indent = indent_match.group(1) if indent_match else ''
        
        # Collect ensures expressions spanning multiple lines
        ensures_lines = [line]
        j = i + 1
        # Continue collecting lines that are continuations (not a new keyword)
        while j < len(lines):
            next_stripped = lines[j].lstrip()
            # Stop at next clause keyword, block delimiter, or empty line that ends the clause
            if re.match(r'^(requires\b|ensures\b|decreases\b|invariant\b|recommends\b|opens_invariants\b|no_unwind\b|fn\b|pub\b|proof\b|exec\b|spec\b|trait\b|impl\b|\{|\}|$)', next_stripped):
                break
            ensures_lines.append(lines[j])
            j += 1
        
        # Join all ensures content (after the `ensures` keyword)
        first_line_content = re.sub(r'^ensures\b\s*', '', stripped)
        rest_content = ''.join(ensures_lines[1:])
        full_content = first_line_content + rest_content
        
        # Process: wrap non-temporal expressions in af()
        modified, new_content = wrap_ensures_content(full_content, indent)
        
        if modified:
            changes += 1
            new_lines.append(indent + 'ensures ' + new_content)
        else:
            for el in ensures_lines:
                new_lines.append(el)
        
        i = j
        continue
    
    if changes > 0 and not dry_run:
        with open(filepath, 'w') as f:
            f.writelines(new_lines)
    
    return changes

def determine_context(original_lines, processed_lines, current_idx):
    """Look backwards to determine if this ensures is for a loop or function."""
    # Search backwards through original lines for the nearest context keyword
    for k in range(current_idx - 1, max(current_idx - 50, -1), -1):
        s = original_lines[k].lstrip() if k < len(original_lines) else ''
        
        # Loop context indicators
        if re.match(r'^(while\b|loop\b|for\b)', s):
            return 'loop'
        if re.match(r'^invariant\b', s):
            return 'loop'  # invariant only appears in loops
        
        # Function context indicators
        if re.match(r'^(pub\s+)?(exec\s+|proof\s+)?fn\b', s):
            return 'exec_or_proof'
        if re.match(r'^spec\s+fn\b', s):
            return 'spec'
        if re.match(r'^requires\b', s):
            # requires before ensures = function context (loops use invariant, not requires typically)
            # But we need to check if there's a fn before the requires
            for kk in range(k - 1, max(k - 30, -1), -1):
                ss = original_lines[kk].lstrip()
                if re.match(r'^spec\s+fn\b', ss):
                    return 'spec'
                if re.match(r'^(pub\s+)?(exec\s+|proof\s+)?fn\b', ss):
                    return 'exec_or_proof'
                if re.match(r'^(while\b|loop\b|for\b)', ss):
                    return 'loop'
            return 'exec_or_proof'  # default: function context
        
        # Opening brace or closing paren = we've gone too far back
        if s.startswith('{') or s.startswith('}'):
            break
    
    return 'exec_or_proof'  # default assumption

def wrap_ensures_content(content, indent):
    """Wrap non-temporal expressions in af(). Returns (modified, new_content)."""
    # Split into individual expressions respecting nesting
    exprs = split_top_level_commas(content.rstrip().rstrip(','))
    
    modified = False
    new_exprs = []
    
    for expr in exprs:
        expr_stripped = expr.strip()
        if not expr_stripped:
            continue
        
        # Check for return binding: |ret| or |ret: Type|
        ret_match = re.match(r'^(\|[^|]*\|)\s*(.*)', expr_stripped, re.DOTALL)
        if ret_match:
            binding = ret_match.group(1)
            inner = ret_match.group(2).strip()
            if is_temporal(inner):
                new_exprs.append(expr)
            else:
                new_exprs.append(f'{binding} af({inner})')
                modified = True
            continue
        
        # Check for #![...] attribute — keep outside af()
        attr_match = re.match(r'^(#!\[[^\]]*\])\s*(.*)', expr_stripped, re.DOTALL)
        if attr_match:
            attr = attr_match.group(1)
            inner = attr_match.group(2).strip()
            if is_temporal(inner):
                new_exprs.append(expr)
            else:
                new_exprs.append(f'{attr}\n{indent}    af({inner})')
                modified = True
            continue
        
        if is_temporal(expr_stripped):
            new_exprs.append(expr)
        else:
            # Check for trailing comment
            # Simple heuristic: find // not inside string/parens
            comment = extract_trailing_comment(expr_stripped)
            if comment:
                code_part = expr_stripped[:expr_stripped.rfind('//')].rstrip()
                new_exprs.append(f'af({code_part}) {comment}')
            else:
                new_exprs.append(f'af({expr_stripped})')
            modified = True
    
    if not modified:
        return False, content
    
    # Reconstruct
    if len(new_exprs) == 1:
        result = new_exprs[0].strip() + ',\n'
    else:
        result = '\n'.join(f'{indent}    {e.strip()},' for e in new_exprs) + '\n'
        # Remove the indent from the first expression since it follows `ensures `
        result = result.lstrip()
    
    return True, result

def split_top_level_commas(text):
    """Split text on commas at depth 0, respecting parens/brackets/braces."""
    parts = []
    current = []
    depth = 0
    in_str = False
    i = 0
    while i < len(text):
        ch = text[i]
        if in_str:
            current.append(ch)
            if ch == '\\' and i + 1 < len(text):
                current.append(text[i+1])
                i += 2
                continue
            if ch == '"':
                in_str = False
        elif ch == '"':
            in_str = True
            current.append(ch)
        elif ch in '([{':
            depth += 1
            current.append(ch)
        elif ch in ')]}':
            depth -= 1
            current.append(ch)
        elif ch == ',' and depth == 0:
            parts.append(''.join(current))
            current = []
        elif ch == '/' and i + 1 < len(text) and text[i+1] == '/':
            # Line comment — include rest of line in current part
            while i < len(text) and text[i] != '\n':
                current.append(text[i])
                i += 1
            if i < len(text):
                current.append(text[i])  # include \n
        else:
            current.append(ch)
        i += 1
    
    remainder = ''.join(current).strip()
    if remainder:
        parts.append(remainder)
    return parts

def extract_trailing_comment(s):
    """Extract trailing // comment if present at top level."""
    depth = 0
    in_str = False
    for i, ch in enumerate(s):
        if in_str:
            if ch == '\\': continue
            if ch == '"': in_str = False
        elif ch == '"':
            in_str = True
        elif ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        elif ch == '/' and i + 1 < len(s) and s[i+1] == '/' and depth == 0 and not in_str:
            return s[i:]
    return None

def main():
    dry_run = '--dry-run' in sys.argv
    paths = [p for p in sys.argv[1:] if p != '--dry-run']
    
    if not paths:
        print("Usage: port_fn_ensures_to_af.py [--dry-run] <file_or_dir> [...]")
        sys.exit(1)
    
    total_changes = 0
    total_files = 0
    
    for path in paths:
        if os.path.isfile(path):
            files = [path]
        elif os.path.isdir(path):
            files = []
            for root, _, filenames in os.walk(path):
                for fn in filenames:
                    if fn.endswith('.rs'):
                        files.append(os.path.join(root, fn))
        else:
            continue
        
        for filepath in sorted(files):
            changes = process_file(filepath, dry_run)
            if changes > 0:
                action = "would modify" if dry_run else "modified"
                print(f"  {action}: {filepath} ({changes} ensures)")
                total_changes += changes
                total_files += 1
    
    action = "Would modify" if dry_run else "Modified"
    print(f"\n{action} {total_changes} ensures in {total_files} files")

if __name__ == '__main__':
    main()
