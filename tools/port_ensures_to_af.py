#!/usr/bin/env python3
"""
Port non-temporal ensures clauses to af() in Verus source files.

Transforms `ensures Q` → `ensures af(Q)` for each non-temporal ensures expression,
preserving temporal operators (ag, af, au, eg, ef, eu, an, en, ax, ex) that are
already temporal.

Usage:
    python3 tools/port_ensures_to_af.py [--dry-run] <file_or_dir> [...]

Operates inside verus!{} blocks only. Handles:
- Single-line ensures: `ensures Q,` → `ensures af(Q),`
- Multi-expression ensures: `ensures Q1, Q2,` → `ensures af(Q1), af(Q2),`
- Return bindings: `ensures |ret| Q` → `ensures |ret| af(Q)`
- Already-temporal expressions are left unchanged
- Preserves // FAILS markers and comments
"""

import re
import sys
import os

TEMPORAL_OPS = {'ag', 'af', 'au', 'eg', 'ef', 'eu', 'an', 'en', 'ax', 'ex'}

def is_temporal(expr_str):
    """Check if an expression starts with a temporal operator call."""
    stripped = expr_str.strip()
    for op in TEMPORAL_OPS:
        if stripped.startswith(op + '(') or stripped.startswith(op + ' ('):
            return True
    return False

def wrap_af(expr_str):
    """Wrap a non-temporal expression in af(...)."""
    if is_temporal(expr_str):
        return expr_str
    stripped = expr_str.strip()
    if not stripped:
        return expr_str
    # Preserve leading whitespace
    leading = expr_str[:len(expr_str) - len(expr_str.lstrip())]
    return f"{leading}af({stripped})"

def find_matching_paren(text, start):
    """Find the matching closing paren for an opening paren at `start`."""
    depth = 0
    i = start
    while i < len(text):
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
            if depth == 0:
                return i
        elif text[i] == '"':
            # Skip string literals
            i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == '\\':
                    i += 1
                i += 1
        i += 1
    return -1

def split_ensures_exprs(text):
    """Split a comma-separated ensures expression list, respecting nesting."""
    exprs = []
    depth = 0
    current = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in '([{':
            depth += 1
            current.append(ch)
        elif ch in ')]}':
            depth -= 1
            current.append(ch)
        elif ch == ',' and depth == 0:
            exprs.append(''.join(current))
            current = []
            i += 1
            continue
        elif ch == '"':
            current.append(ch)
            i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == '\\':
                    current.append(text[i])
                    i += 1
                current.append(text[i])
                i += 1
            if i < len(text):
                current.append(text[i])
        else:
            current.append(ch)
        i += 1
    remainder = ''.join(current)
    if remainder.strip():
        exprs.append(remainder)
    return exprs

def process_ensures_line(line):
    """Process a single line that is part of an ensures clause."""
    # Don't modify lines that are just comments
    stripped = line.strip()
    if stripped.startswith('//'):
        return line
    return line

def process_file(filepath, dry_run=False):
    """Process a single .rs file, wrapping non-temporal ensures in af()."""
    with open(filepath, 'r') as f:
        content = f.read()

    # Only process files that contain 'ensures'
    if 'ensures' not in content:
        return 0

    lines = content.split('\n')
    new_lines = []
    changes = 0
    i = 0

    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()

        # Detect `ensures` keyword (not inside comments or strings)
        # Match: `ensures expr,` or `ensures` followed by expressions on next lines
        ensures_match = re.match(r'^(\s*)(ensures\b)(.*)', line)

        if ensures_match:
            indent = ensures_match.group(1)
            keyword = ensures_match.group(2)
            rest = ensures_match.group(3)

            # Check for return binding: `ensures |ret| ...`
            ret_binding_match = re.match(r'^(\s*\|[^|]*\|)(.*)', rest)
            if ret_binding_match:
                binding = ret_binding_match.group(1)
                rest = ret_binding_match.group(2)
                prefix = f"{indent}{keyword}{binding}"
            else:
                binding = ''
                prefix = f"{indent}{keyword}"

            # Collect the full ensures expression(s) which may span multiple lines
            # The ensures clause ends at: next keyword (requires, ensures, decreases,
            # invariant, fn, pub, {, }) or end of block
            ensures_text = rest
            continuation_lines = []

            # Check if this line has content or just `ensures` keyword
            j = i + 1
            while j < len(lines):
                next_stripped = lines[j].lstrip()
                # Stop at next clause keyword or block delimiter
                if re.match(r'^(requires|ensures|decreases|invariant|recommends|opens_invariants|no_unwind|fn\b|pub\b|proof\b|exec\b|spec\b|\{|\}|$)', next_stripped):
                    break
                # This line is a continuation of the ensures clause
                continuation_lines.append(lines[j])
                j += 1

            # Combine all ensures text
            full_text = ensures_text
            for cl in continuation_lines:
                full_text += '\n' + cl

            # Split into individual expressions
            # Remove trailing comma if present
            full_stripped = full_text.rstrip()
            trailing_comma = full_stripped.endswith(',')
            if trailing_comma:
                full_stripped = full_stripped[:-1]

            exprs = split_ensures_exprs(full_stripped)

            # Wrap each non-temporal expression
            new_exprs = []
            line_changed = False
            for expr in exprs:
                expr_stripped = expr.strip()
                if not expr_stripped:
                    continue
                if is_temporal(expr_stripped):
                    new_exprs.append(expr)
                else:
                    # Check for inline comment
                    comment = ''
                    # Simple heuristic: find // that's not inside a string
                    comment_idx = expr.find('//')
                    if comment_idx >= 0:
                        # Make sure it's not inside parens/strings
                        depth = 0
                        in_str = False
                        for ci, ch in enumerate(expr[:comment_idx]):
                            if ch in '([{': depth += 1
                            elif ch in ')]}': depth -= 1
                            elif ch == '"': in_str = not in_str
                        if depth == 0 and not in_str:
                            comment = ' ' + expr[comment_idx:].strip()
                            expr_stripped = expr[:comment_idx].strip()

                    wrapped = f"af({expr_stripped})"
                    # Preserve the original leading whitespace
                    leading = expr[:len(expr) - len(expr.lstrip())]
                    new_exprs.append(f"{leading}{wrapped}{comment}")
                    line_changed = True

            if line_changed:
                changes += 1
                # Reconstruct the ensures clause
                if len(new_exprs) == 1 and not continuation_lines:
                    # Single expression, single line
                    expr_text = new_exprs[0].strip()
                    comma = ',' if trailing_comma else ''
                    new_line = f"{prefix} {expr_text}{comma}"
                    new_lines.append(new_line)
                else:
                    # Multi-expression or multi-line
                    if not continuation_lines:
                        # All on one line, just rejoin
                        joined = ', '.join(e.strip() for e in new_exprs)
                        comma = ',' if trailing_comma else ''
                        new_line = f"{prefix} {joined}{comma}"
                        new_lines.append(new_line)
                    else:
                        # Multi-line: first expr on ensures line, rest on continuation lines
                        if new_exprs:
                            first_comma = ',' if len(new_exprs) > 1 or trailing_comma else ''
                            new_lines.append(f"{prefix} {new_exprs[0].strip()},")
                            for ei, expr in enumerate(new_exprs[1:]):
                                is_last = (ei == len(new_exprs) - 2)
                                comma = ',' if not is_last or trailing_comma else ''
                                # Use continuation indent
                                cont_indent = indent + '    '
                                new_lines.append(f"{cont_indent}{expr.strip()}{comma}")
                        else:
                            new_lines.append(line)

                # Skip continuation lines (already incorporated)
                i = j
                continue
            else:
                # No changes needed, keep original lines
                new_lines.append(line)
                for cl in continuation_lines:
                    new_lines.append(cl)
                i = j
                continue
        else:
            new_lines.append(line)

        i += 1

    if changes > 0 and not dry_run:
        with open(filepath, 'w') as f:
            f.write('\n'.join(new_lines))

    return changes

def main():
    dry_run = '--dry-run' in sys.argv
    paths = [p for p in sys.argv[1:] if p != '--dry-run']

    if not paths:
        print("Usage: port_ensures_to_af.py [--dry-run] <file_or_dir> [...]")
        sys.exit(1)

    total_changes = 0
    total_files = 0

    for path in paths:
        if os.path.isfile(path):
            files = [path]
        elif os.path.isdir(path):
            files = []
            for root, dirs, filenames in os.walk(path):
                for fn in filenames:
                    if fn.endswith('.rs'):
                        files.append(os.path.join(root, fn))
        else:
            print(f"Warning: {path} not found, skipping")
            continue

        for filepath in sorted(files):
            changes = process_file(filepath, dry_run)
            if changes > 0:
                action = "would modify" if dry_run else "modified"
                print(f"  {action}: {filepath} ({changes} ensures clauses)")
                total_changes += changes
                total_files += 1

    action = "Would modify" if dry_run else "Modified"
    print(f"\n{action} {total_changes} ensures clauses in {total_files} files")

if __name__ == '__main__':
    main()
