"""Build the single-file JIS export pemmasani_jis.tex from the multi-file sources.

Each \\input{...} in pemmasani.tex is replaced by the contents of that file, recursively,
with trailing newlines stripped. Then every LaTeX comment is removed, since the JIS style
guide forbids % comments in the submitted file. A line whose first non-space character is %
is dropped. A comment after code on a line is removed together with the line end and the
leading spaces of the next line, which is what TeX itself does with it, so the typeset text
does not change. An escaped \\% is kept as text. The TODO comments stay in the multi-file
sources.

Usage, from the jis folder:
    python scripts/make_jis_single_file.py [root] [output]
The defaults are the jis folder and pemmasani_jis.tex inside it. The output uses LF line
endings.
"""

import os
import re
import sys

BS = chr(92)
PAT = re.compile(re.escape(BS + 'input{') + r'([^}]+)\}')


def read(root, path):
    with open(os.path.join(root, path), encoding='utf-8', newline='') as fh:
        return fh.read().replace('\r\n', '\n')


def expand(root, text):
    def rep(mo):
        name = mo.group(1)
        if not name.endswith('.tex'):
            name += '.tex'
        return expand(root, read(root, name)).rstrip('\n')
    return PAT.sub(rep, text)


def comment_start(line):
    """Index of the first unescaped %, or -1."""
    i = line.find('%')
    while i != -1:
        k = i
        while k > 0 and line[k - 1] == BS:
            k -= 1
        if (i - k) % 2 == 0:
            return i
        i = line.find('%', i + 1)
    return -1


def strip_comments(text):
    out = []
    join = False
    for line in text.split('\n'):
        if join:
            line = line.lstrip(' \t')
        if line.lstrip(' \t').startswith('%'):
            # A pure comment line. If a trailing comment asked to join, keep joining.
            continue
        c = comment_start(line)
        if c == -1:
            if join:
                out[-1] += line
            else:
                out.append(line)
            join = False
        else:
            code = line[:c]
            if join:
                out[-1] += code
            else:
                out.append(code)
            join = True
    return '\n'.join(out)


def main():
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    root = sys.argv[1] if len(sys.argv) > 1 else here
    target = sys.argv[2] if len(sys.argv) > 2 else os.path.join(root, 'pemmasani_jis.tex')
    text = strip_comments(expand(root, read(root, 'pemmasani.tex')))
    if '%' in text.replace(BS + '%', ''):
        sys.exit('an unescaped % is left in the output')
    with open(target, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write(text)
    print('wrote', target)


if __name__ == '__main__':
    main()
