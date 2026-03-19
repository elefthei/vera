#!/usr/bin/env python3
"""
Transform ensures clauses: ensures Q -> ensures af(Q)
"""
import re
import sys

TEMPORAL_OPS = {'ag', 'af', 'au', 'eg', 'ef', 'eu', 'an', 'en', 'ax', 'ex'}


def find_comment_start(line):
    """Find start of // comment not inside a string. Returns index or len(line)."""
    in_str = False
    esc = False
    for i, c in enumerate(line):
        if esc:
            esc = False
            continue
        if in_str:
            if c == '\\':
                esc = True
            elif c == '"':
                in_str = False
            continue
        if c == '"':
            in_str = True
        elif c == '/' and i + 1 < len(line) and line[i + 1] == '/':
            return i
    return len(line)


def is_temporal_call(expr):
    """Check if expression starts with a temporal operator call."""
    s = expr.strip()
    for op in TEMPORAL_OPS:
        if re.match(r'^' + re.escape(op) + r'\s*\(', s):
            return True
    return False


def is_in_string(line, pos):
    """Check if position is inside a string literal."""
    in_str = False
    esc = False
    for i, c in enumerate(line):
        if i >= pos:
            return in_str
        if esc:
            esc = False
            continue
        if in_str:
            if c == '\\':
                esc = True
            elif c == '"':
                in_str = False
            continue
        if c == '"':
            in_str = True
    return in_str


def find_clause_ensures(line):
    """Find clause-level 'ensures' keyword in a line.
    Returns match object or None."""
    cmt = find_comment_start(line)
    # Skip ensures inside #[verus_spec(...)] attributes
    if re.search(r'#\[verus_spec\(', line[:cmt]):
        return None
    for m in re.finditer(r'\bensures\b', line[:cmt]):
        pos = m.start()
        before = line[:pos].rstrip()
        if before.endswith('.'):
            continue
        if is_in_string(line, pos):
            continue
        return m
    return None


def count_braces_backwards(line):
    """Count net braces for backward scanning: } = +1, { = -1.
    Ignores braces in strings and comments."""
    cmt = find_comment_start(line)
    text = line[:cmt]
    count = 0
    in_str = False
    esc = False
    for c in text:
        if esc:
            esc = False
            continue
        if in_str:
            if c == '\\':
                esc = True
            elif c == '"':
                in_str = False
            continue
        if c == '"':
            in_str = True
        elif c == '}':
            count += 1
        elif c == '{':
            count -= 1
    return count


def is_spec_context(lines, idx):
    """Determine if the ensures at lines[idx] is in a spec fn context."""
    # First check if fn keyword is on the same line as ensures
    ensures_line = lines[idx]
    ens_match = find_clause_ensures(ensures_line)
    if ens_match:
        before_ensures = ensures_line[:ens_match.start()]
        if re.search(r'\b(open\s+)?spec\s+fn\b', before_ensures) or re.search(r'\bclosed\s+spec\s+fn\b', before_ensures):
            return True
        if re.search(r'\bfn\b', before_ensures) and not re.search(r'\bspec\b', before_ensures):
            return False

    # Scan backwards with brace depth tracking
    brace_depth = 0
    for i in range(idx - 1, max(-1, idx - 150), -1):
        line = lines[i]
        s = line.lstrip()

        prev_depth = brace_depth
        brace_depth += count_braces_backwards(line)

        # If we were inside a previous block body, skip this line
        if prev_depth > 0:
            continue

        # If we just entered a block going backwards (more } than {), skip
        if brace_depth > 0:
            continue

        if not s or s.startswith('//'):
            continue
        if re.match(r'(requires|ensures|recommends|decreases|invariant|invariant_except_break|opens_invariants)\b', s):
            continue
        if s.startswith('#[') or s.startswith('#!['):
            continue
        if re.search(r'\b(open\s+)?spec\s+fn\b', s) or re.search(r'\bclosed\s+spec\s+fn\b', s):
            return True
        if re.search(r'\bproof\s+fn\b', s):
            return False
        if re.search(r'\bfn\b', s) and not re.search(r'\bspec\b', s):
            return False
        if re.match(r'(loop|while)\b', s):
            return False
        if 'verus_code!' in s or 'test_verify_one_file' in s or '=> code!' in s:
            return False
    return False


def compute_depth_and_find_top_level_commas(text):
    """Process text tracking depth. Track <> after :: as angle brackets.
    Track |...| after forall/exists/choose as quantifier bindings.
    Returns (final_depth, list_of_positions_of_top_level_commas)."""
    depth = 0
    angle_depth = 0
    pipe_depth = 0
    in_str = False
    esc = False
    commas = []
    prev_was_colon_colon = False
    for i, c in enumerate(text):
        if esc:
            esc = False
            prev_was_colon_colon = False
            continue
        if in_str:
            if c == '\\':
                esc = True
            elif c == '"':
                in_str = False
            prev_was_colon_colon = False
            continue
        if c == '"':
            in_str = True
            prev_was_colon_colon = False
        elif c == ':' and i + 1 < len(text) and text[i+1] == ':':
            pass
        elif c == ':' and i > 0 and text[i-1] == ':':
            prev_was_colon_colon = True
            continue
        elif c == '<' and (prev_was_colon_colon or angle_depth > 0):
            angle_depth += 1
            prev_was_colon_colon = False
        elif c == '>' and angle_depth > 0:
            angle_depth -= 1
            prev_was_colon_colon = False
        elif c == '|' and i + 1 < len(text) and text[i+1] == '|':
            # || operator - skip both chars
            prev_was_colon_colon = False
        elif c == '|' and i > 0 and text[i-1] == '|':
            # second char of || - already handled
            prev_was_colon_colon = False
        elif c == '|':
            if pipe_depth > 0:
                pipe_depth -= 1
            else:
                # Check if preceded by forall/exists/choose
                before = text[:i].rstrip()
                if before.endswith('forall') or before.endswith('exists') or before.endswith('choose'):
                    pipe_depth += 1
                # else: it's a bitwise OR, don't change pipe_depth
            prev_was_colon_colon = False
        elif c in '([{':
            depth += 1
            prev_was_colon_colon = False
        elif c in ')]}':
            depth -= 1
            prev_was_colon_colon = False
        elif c == ',' and depth == 0 and angle_depth == 0 and pipe_depth == 0:
            commas.append(i)
            prev_was_colon_colon = False
        elif c == ';' and depth == 0 and angle_depth == 0 and pipe_depth == 0:
            prev_was_colon_colon = False
        else:
            prev_was_colon_colon = False
    return depth, commas


def depth_at_end(text):
    d, _ = compute_depth_and_find_top_level_commas(text)
    return d


def append_comment(base, comment):
    """Append a comment to a line, ensuring proper spacing."""
    if not comment:
        return base
    if base and not base.endswith(' '):
        return base + ' ' + comment
    return base + comment


def strip_trailing_semi(expr):
    """Strip trailing semicolon from expression. Returns (expr_without_semi, had_semi)."""
    stripped = expr.rstrip()
    if stripped.endswith(';'):
        return stripped[:-1].rstrip(), True
    return expr, False


class FileProcessor:
    def __init__(self, lines):
        self.lines = lines
        self.output = []
        self.i = 0
        self.multi_line_expr_lines = []

    def process(self):
        while self.i < len(self.lines):
            line = self.lines[self.i]
            m = find_clause_ensures(line)

            if m is not None and not is_spec_context(self.lines, self.i):
                self.transform_ensures(m)
            else:
                self.output.append(line)
                self.i += 1

        return self.output

    def transform_ensures(self, m):
        line = self.lines[self.i]
        ensures_kw_end = m.end()
        ensures_indent = m.start()

        cmt_start = find_comment_start(line)
        after_ensures_full = line[ensures_kw_end:cmt_start]
        after_ensures = after_ensures_full.strip()

        if not after_ensures:
            self.output.append(line)
            self.i += 1
            self.process_multiline_ensures(ensures_indent)
        else:
            self.process_ensures_with_content(m, ensures_kw_end, ensures_indent)

    def process_multiline_ensures(self, ensures_indent):
        """Process continuation lines of a multi-line ensures clause."""
        depth = 0

        while self.i < len(self.lines):
            line = self.lines[self.i]
            stripped = line.lstrip()
            indent = len(line) - len(stripped) if stripped else 9999

            if not stripped:
                if depth == 0:
                    break
                self.output.append(line)
                self.i += 1
                continue

            if depth == 0 and indent <= ensures_indent:
                break

            if depth == 0 and self.is_clause_terminator(stripped):
                break

            cmt_start = find_comment_start(line)
            content = line[:cmt_start]
            comment = line[cmt_start:] if cmt_start < len(line) else ''

            # Check if this is a comment-only line (no expression content)
            content_trimmed = content.strip()
            if not content_trimmed:
                # Comment-only line or blank - output unchanged
                self.output.append(line)
                self.i += 1
                continue

            line_depth, top_commas = compute_depth_and_find_top_level_commas(content)

            if depth == 0 and line_depth == 0 and not top_commas:
                # Single expression on this line at depth 0
                leading_ws = content[:len(content) - len(content.lstrip())]
                expr = content.strip()
                # Strip trailing semicolon
                expr, had_semi = strip_trailing_semi(expr)
                has_trailing_comma = expr.rstrip().endswith(',')
                semi_suffix = ';' if had_semi else ''
                if has_trailing_comma:
                    core = expr[:-1].rstrip()
                    if is_temporal_call(core):
                        new_line = append_comment(leading_ws + core + ',' + semi_suffix, comment)
                    else:
                        new_line = append_comment(leading_ws + 'af(' + core + '),' + semi_suffix, comment)
                else:
                    core = expr
                    if is_temporal_call(core):
                        new_line = append_comment(leading_ws + core + semi_suffix, comment)
                    else:
                        new_line = append_comment(leading_ws + 'af(' + core + ')' + semi_suffix, comment)
                self.output.append(new_line)
                self.i += 1

            elif depth == 0 and line_depth == 0 and top_commas:
                new_line = self.wrap_comma_separated_exprs(content, comment)
                self.output.append(new_line)
                self.i += 1

            elif depth == 0 and line_depth > 0:
                depth = line_depth
                self.multi_line_expr_lines = [(self.i, line)]
                self.i += 1

            elif depth > 0:
                self.multi_line_expr_lines.append((self.i, line))
                depth += line_depth
                if depth <= 0:
                    depth = 0
                    self.wrap_multiline_expression()
                else:
                    self.i += 1

            else:
                self.output.append(line)
                self.i += 1

    def wrap_multiline_expression(self):
        if not self.multi_line_expr_lines:
            return

        first_idx, first_line = self.multi_line_expr_lines[0]
        last_idx, last_line = self.multi_line_expr_lines[-1]

        first_cmt = find_comment_start(first_line)
        first_comment = first_line[first_cmt:] if first_cmt < len(first_line) else ''
        leading_ws = first_line[:len(first_line) - len(first_line.lstrip())]

        last_cmt = find_comment_start(last_line)
        last_content = last_line[:last_cmt].rstrip()
        last_comment = last_line[last_cmt:] if last_cmt < len(last_line) else ''

        # Strip trailing semicolon from last line
        last_content_stripped, had_semi = strip_trailing_semi(last_content)
        semi_suffix = ';' if had_semi else ''
        has_trailing_comma = last_content_stripped.rstrip().endswith(',')

        # First line: insert af(
        first_expr = first_line[len(leading_ws):first_cmt].rstrip()
        first_new = leading_ws + 'af(' + first_expr
        first_new = append_comment(first_new, first_comment)
        self.output.append(first_new)

        # Middle lines unchanged
        for idx, mid_line in self.multi_line_expr_lines[1:-1]:
            self.output.append(mid_line)

        if len(self.multi_line_expr_lines) > 1:
            if has_trailing_comma:
                new_last = append_comment(last_content_stripped[:-1].rstrip() + '),' + semi_suffix, last_comment)
            else:
                new_last = append_comment(last_content_stripped + ')' + semi_suffix, last_comment)
            self.output.append(new_last)

        self.i = last_idx + 1
        self.multi_line_expr_lines = []

    def process_ensures_with_content(self, m, ensures_kw_end, ensures_indent):
        line = self.lines[self.i]
        cmt_start = find_comment_start(line)
        content_after = line[ensures_kw_end:cmt_start]
        comment = line[cmt_start:] if cmt_start < len(line) else ''

        prefix = line[:ensures_kw_end]

        content_stripped = content_after.strip()

        # Check for ensures(|ret: Type| expr) pattern
        ret_bind_match = re.match(r'\s*\(\s*\|([^|]*)\|\s*', content_after)
        if ret_bind_match:
            self.process_paren_return_binding(m, ensures_kw_end, ensures_indent, ret_bind_match)
            return

        # Check if the expression starts with { (block expression)
        if content_stripped.startswith('{'):
            self.process_block_expression_ensures(m, ensures_kw_end, ensures_indent)
            return

        # Check depth
        line_depth, top_commas = compute_depth_and_find_top_level_commas(content_after)

        if line_depth == 0:
            if not top_commas:
                # Single expression
                # Strip trailing semicolon first
                expr_clean, had_semi = strip_trailing_semi(content_stripped)
                semi_suffix = ';' if had_semi else ''
                has_trailing_comma = expr_clean.rstrip().endswith(',')
                space_before = content_after[:len(content_after) - len(content_after.lstrip())]

                if has_trailing_comma:
                    core = expr_clean[:-1].rstrip()
                    if is_temporal_call(core):
                        new_line = append_comment(prefix + space_before + core + ',' + semi_suffix, comment)
                    else:
                        new_line = append_comment(prefix + space_before + 'af(' + core + '),' + semi_suffix, comment)
                else:
                    core = expr_clean
                    # Check if line ends with { body }
                    body_match = self.find_body_start_in_expr(core)
                    if body_match is not None:
                        expr_part = core[:body_match].rstrip()
                        body_part = core[body_match:]
                        if is_temporal_call(expr_part):
                            new_line = append_comment(prefix + space_before + expr_part + ' ' + body_part + semi_suffix, comment)
                        else:
                            new_line = append_comment(prefix + space_before + 'af(' + expr_part + ') ' + body_part + semi_suffix, comment)
                    else:
                        if is_temporal_call(core):
                            new_line = append_comment(prefix + space_before + core + semi_suffix, comment)
                        else:
                            new_line = append_comment(prefix + space_before + 'af(' + core + ')' + semi_suffix, comment)
                self.output.append(new_line)
                self.i += 1
            else:
                # Multiple expressions separated by commas
                new_content = self.wrap_comma_separated_exprs_raw(content_after)
                new_line = append_comment(prefix + new_content, comment)
                self.output.append(new_line)
                self.i += 1
        else:
            # Expression continues on next lines
            self.process_multiline_same_line_start(m, ensures_kw_end, ensures_indent, line_depth)

    def find_body_start_in_expr(self, expr):
        """Find position of '{' that starts a function/closure body."""
        depth = 0
        in_str = False
        esc = False
        has_content = False
        for i, c in enumerate(expr):
            if esc:
                esc = False
                continue
            if in_str:
                if c == '\\':
                    esc = True
                elif c == '"':
                    in_str = False
                continue
            if c == '"':
                in_str = True
                has_content = True
                continue
            if c.isspace():
                continue
            has_content = True
            if c == '(' or c == '[':
                depth += 1
            elif c == ')' or c == ']':
                depth -= 1
            elif c == '{':
                if depth == 0 and has_content:
                    rest = expr[i:]
                    rest_depth = depth_at_end(rest)
                    if rest_depth == 0:
                        return i
                depth += 1
            elif c == '}':
                depth -= 1
        return None

    def process_block_expression_ensures(self, m, ensures_kw_end, ensures_indent):
        line = self.lines[self.i]
        cmt_start = find_comment_start(line)
        content_after = line[ensures_kw_end:cmt_start]
        comment = line[cmt_start:] if cmt_start < len(line) else ''
        prefix = line[:ensures_kw_end]
        space_before = content_after[:len(content_after) - len(content_after.lstrip())]

        depth = 0
        collected_lines = []
        j = self.i
        while j < len(self.lines):
            cur = self.lines[j]
            cur_cmt = find_comment_start(cur)
            cur_content = cur[:cur_cmt]
            depth += depth_at_end(cur_content)
            collected_lines.append(j)
            if depth <= 0 and j >= self.i:
                break
            j += 1

        if len(collected_lines) == 1:
            c = content_after.strip()
            c, had_semi = strip_trailing_semi(c)
            semi_suffix = ';' if had_semi else ''
            has_trailing_comma = c.endswith(',')
            if has_trailing_comma:
                core = c[:-1].rstrip()
                new_line = append_comment(prefix + space_before + 'af(' + core + '),' + semi_suffix, comment)
            else:
                core = c
                new_line = append_comment(prefix + space_before + 'af(' + core + ')' + semi_suffix, comment)
            self.output.append(new_line)
            self.i += 1
        else:
            first = self.lines[collected_lines[0]]
            first_cmt = find_comment_start(first)
            first_expr = first[ensures_kw_end:first_cmt].strip()
            first_comment = first[first_cmt:] if first_cmt < len(first) else ''
            new_first = append_comment(prefix + space_before + 'af(' + first_expr, first_comment)
            self.output.append(new_first)

            for idx in collected_lines[1:-1]:
                self.output.append(self.lines[idx])

            last = self.lines[collected_lines[-1]]
            last_cmt = find_comment_start(last)
            last_content = last[:last_cmt].rstrip()
            last_comment = last[last_cmt:] if last_cmt < len(last) else ''
            last_content, had_semi = strip_trailing_semi(last_content)
            semi_suffix = ';' if had_semi else ''
            has_trailing_comma = last_content.rstrip().endswith(',')
            if has_trailing_comma:
                new_last = append_comment(last_content[:-1].rstrip() + '),' + semi_suffix, last_comment)
            else:
                new_last = append_comment(last_content + ')' + semi_suffix, last_comment)
            self.output.append(new_last)

            self.i = collected_lines[-1] + 1

    def process_paren_return_binding(self, m, ensures_kw_end, ensures_indent, ret_match):
        line = self.lines[self.i]
        cmt_start = find_comment_start(line)
        comment = line[cmt_start:] if cmt_start < len(line) else ''
        prefix = line[:ensures_kw_end]

        bind_end = ensures_kw_end + ret_match.end()
        remaining_text = line[bind_end:cmt_start]

        inner_depth = 1
        in_str = False
        esc = False
        for ci, c in enumerate(remaining_text):
            if esc:
                esc = False
                continue
            if in_str:
                if c == '\\':
                    esc = True
                elif c == '"':
                    in_str = False
                continue
            if c == '"':
                in_str = True
            elif c in '([{':
                inner_depth += 1
            elif c in ')]}':
                inner_depth -= 1
                if inner_depth == 0:
                    expr_part = remaining_text[:ci].rstrip()
                    after_paren = remaining_text[ci + 1:]

                    binding_part = line[ensures_kw_end:bind_end]

                    if is_temporal_call(expr_part.strip()):
                        wrapped_expr = ' ' + expr_part.strip()
                    else:
                        wrapped_expr = ' af(' + expr_part.strip() + ')'

                    new_line = prefix + binding_part + wrapped_expr + ')' + after_paren.rstrip()
                    new_line = append_comment(new_line, comment)
                    self.output.append(new_line)
                    self.i += 1
                    return

        # Multi-line case: closing paren not on this line
        binding_prefix = line[ensures_kw_end:bind_end]
        collected = [(self.i, line)]
        outer_depth = 1
        for c in remaining_text:
            if c in '([{':
                outer_depth += 1
            elif c in ')]}':
                outer_depth -= 1

        j = self.i + 1
        while j < len(self.lines) and outer_depth > 0:
            cur = self.lines[j]
            cur_cmt = find_comment_start(cur)
            cur_content = cur[:cur_cmt]
            outer_depth += depth_at_end(cur_content)
            collected.append((j, cur))
            j += 1

        if outer_depth != 0:
            for idx, ln in collected:
                self.output.append(ln)
            self.i = j
            return

        first_remaining = line[bind_end:find_comment_start(line)]
        first_comment_part = line[find_comment_start(line):] if find_comment_start(line) < len(line) else ''

        new_first = prefix + binding_prefix + 'af(' + first_remaining.strip()
        new_first = append_comment(new_first, first_comment_part)
        self.output.append(new_first)

        for idx, mid_line in collected[1:-1]:
            self.output.append(mid_line)

        if len(collected) > 1:
            last_idx, last_line = collected[-1]
            last_cmt = find_comment_start(last_line)
            last_content = last_line[:last_cmt].rstrip()
            last_comment_part = last_line[last_cmt:] if last_cmt < len(last_line) else ''

            last_paren_idx = last_content.rindex(')')
            before_paren = last_content[:last_paren_idx]
            after_and_paren = last_content[last_paren_idx:]
            new_last = before_paren.rstrip() + ')' + after_and_paren
            new_last = append_comment(new_last, last_comment_part)
            self.output.append(new_last)

        self.i = collected[-1][0] + 1

    def process_multiline_same_line_start(self, m, ensures_kw_end, ensures_indent, initial_depth):
        line = self.lines[self.i]
        cmt_start = find_comment_start(line)
        content_after = line[ensures_kw_end:cmt_start]
        comment = line[cmt_start:] if cmt_start < len(line) else ''
        prefix = line[:ensures_kw_end]
        space_before = content_after[:len(content_after) - len(content_after.lstrip())]
        expr_text = content_after.strip()

        depth = initial_depth
        collected = [(self.i, line)]
        j = self.i + 1
        while j < len(self.lines) and depth > 0:
            cur = self.lines[j]
            cur_cmt = find_comment_start(cur)
            cur_content = cur[:cur_cmt]
            depth += depth_at_end(cur_content)
            collected.append((j, cur))
            j += 1

        if depth != 0:
            for idx, ln in collected:
                self.output.append(ln)
            self.i = j
            return

        last_idx, last_line = collected[-1]
        last_cmt = find_comment_start(last_line)
        last_content = last_line[:last_cmt].rstrip()
        last_comment = last_line[last_cmt:] if last_cmt < len(last_line) else ''

        # Strip trailing semicolon
        last_content, had_semi = strip_trailing_semi(last_content)
        semi_suffix = ';' if had_semi else ''
        has_trailing_comma = last_content.rstrip().endswith(',')

        if is_temporal_call(expr_text):
            new_first = append_comment(prefix + space_before + expr_text, comment)
        else:
            new_first = append_comment(prefix + space_before + 'af(' + expr_text, comment)
        self.output.append(new_first)

        for idx, mid_line in collected[1:-1]:
            self.output.append(mid_line)

        if len(collected) > 1:
            if is_temporal_call(expr_text):
                new_last = append_comment(last_content + semi_suffix, last_comment)
            else:
                if has_trailing_comma:
                    new_last = append_comment(last_content[:-1].rstrip() + '),' + semi_suffix, last_comment)
                else:
                    new_last = append_comment(last_content + ')' + semi_suffix, last_comment)
            self.output.append(new_last)

        self.i = last_idx + 1

    def wrap_comma_separated_exprs(self, content, comment):
        leading_ws = content[:len(content) - len(content.lstrip())]
        inner = content.strip()
        wrapped = self.wrap_comma_separated_inner(inner)
        return append_comment(leading_ws + wrapped, comment)

    def wrap_comma_separated_exprs_raw(self, content_after):
        space_before = content_after[:len(content_after) - len(content_after.lstrip())]
        inner = content_after.strip()
        wrapped = self.wrap_comma_separated_inner(inner)
        return space_before + wrapped

    def wrap_comma_separated_inner(self, inner):
        """Split at top-level commas and wrap each expression in af()."""
        depth = 0
        angle_depth = 0
        pipe_depth = 0
        in_str = False
        esc = False
        parts = []
        current = ''
        prev_was_colon_colon = False
        prev_char = ''
        for i, c in enumerate(inner):
            if esc:
                esc = False
                current += c
                prev_was_colon_colon = False
                prev_char = c
                continue
            if in_str:
                if c == '\\':
                    esc = True
                elif c == '"':
                    in_str = False
                current += c
                prev_was_colon_colon = False
                prev_char = c
                continue
            if c == '"':
                in_str = True
                current += c
                prev_was_colon_colon = False
            elif c == ':' and len(current) > 0 and current[-1] == ':':
                current += c
                prev_was_colon_colon = True
                prev_char = c
                continue
            elif c == '<' and (prev_was_colon_colon or angle_depth > 0):
                angle_depth += 1
                current += c
                prev_was_colon_colon = False
            elif c == '>' and angle_depth > 0:
                angle_depth -= 1
                current += c
                prev_was_colon_colon = False
            elif c == '|' and i + 1 < len(inner) and inner[i+1] == '|':
                # || operator
                current += c
                prev_was_colon_colon = False
            elif c == '|' and prev_char == '|':
                # second char of ||
                current += c
                prev_was_colon_colon = False
            elif c == '|':
                if pipe_depth > 0:
                    pipe_depth -= 1
                else:
                    before = current.rstrip()
                    if before.endswith('forall') or before.endswith('exists') or before.endswith('choose'):
                        pipe_depth += 1
                current += c
                prev_was_colon_colon = False
            elif c in '([{':
                depth += 1
                current += c
                prev_was_colon_colon = False
            elif c in ')]}':
                depth -= 1
                current += c
                prev_was_colon_colon = False
            elif c == ',' and depth == 0 and angle_depth == 0 and pipe_depth == 0:
                parts.append(current)
                current = ''
                prev_was_colon_colon = False
            else:
                current += c
                if c != ':':
                    prev_was_colon_colon = False
            prev_char = c
        if current:
            parts.append(current)

        # Strip trailing semicolon from the last part
        had_semi = False
        if parts:
            last = parts[-1].rstrip()
            if last.endswith(';'):
                parts[-1] = last[:-1]
                had_semi = True

        wrapped_parts = []
        for p in parts:
            stripped = p.strip()
            if not stripped:
                wrapped_parts.append(p)
            elif is_temporal_call(stripped):
                wrapped_parts.append(p)
            else:
                ls = len(p) - len(p.lstrip())
                leading = p[:ls]
                core = p.strip()
                wrapped_parts.append(leading + 'af(' + core + ')')

        result = ','.join(wrapped_parts)
        # Preserve trailing comma
        if inner.rstrip().rstrip(';').rstrip().endswith(','):
            if not result.rstrip().endswith(','):
                result = result.rstrip() + ','
        if had_semi:
            result = result.rstrip() + ';'
        return result

    def is_clause_terminator(self, stripped):
        terminators = [
            'requires', 'recommends', 'decreases', 'invariant ',
            'invariant_except_break', 'opens_invariants', 'via ',
        ]
        for t in terminators:
            if stripped.startswith(t):
                return True
        if stripped == '{':
            return True
        return False


def process_file(filepath):
    with open(filepath) as f:
        content = f.read()

    lines = content.split('\n')
    processor = FileProcessor(lines)
    result = processor.process()

    with open(filepath, 'w') as f:
        f.write('\n'.join(result))


if __name__ == '__main__':
    for filepath in sys.argv[1:]:
        print(f"Processing {filepath}...")
        process_file(filepath)
    print("Done.")
