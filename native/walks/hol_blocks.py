#!/usr/bin/env python3
"""hol_blocks.py NOTES TEXT NAME -- HOL definitions of a p1 program's blocks.

Reads the notes p1.metta writes (tisa_note ... "block" NAME [`TEXT`]) and the
program's text, and prints one new_definition per block, innermost first,
each block's text with its direct sub-blocks replaced by their names, then
the program's definition over its blocks, then NAME_TERM: the program is the
text, term for term (proved by unfolding every block). Nothing here is
trusted: the HOL file states the program as the text, and the proof checks it.
"""
import re
import sys

notes_path, text_path, name = sys.argv[1:4]
notes = open(notes_path).read()
text = open(text_path).read().strip()

blocks = []
for m in re.finditer(r'tisa_note "[^"]*" "([0-9.]*)" "block" "([A-Za-z_0-9]+)" \[`(.*?)`\];;', notes, re.S):
    path, bname, btext = m.group(1), m.group(2), m.group(3)
    blocks.append((path, bname, btext))


def is_prefix(p, q):
    return p == "" or q == p or q.startswith(p + ".")


def children(path):
    out = []
    for (q, n, t) in blocks:
        if q != path and is_prefix(path, q):
            # direct: no other block strictly between
            if not any(r != path and r != q and is_prefix(path, r) and is_prefix(r, q) for (r, _, _) in blocks):
                out.append((q, n, t))
    return out


def folded(btext, path):
    out = btext
    for (q, n, t) in sorted(children(path), key=lambda b: -len(b[2])):
        k = out.count(t)
        if k != 1:
            sys.exit("hol_blocks: block %s occurs %d times in its parent" % (n, k))
        out = out.replace(t, n)
    return out


m = re.match(r'\(TProg (\[[^\]]*\]) (\[[^\]]*\]) (.*)\)$', text, re.S)
if not m:
    sys.exit("hol_blocks: the text is not a TProg")
decls, inits, root = m.group(1), m.group(2), m.group(3)

order = sorted(blocks, key=lambda b: -len(b[0].split(".")) if b[0] else 0)
for (p, n, t) in order:
    print("let %s = new_definition\n `%s = %s`;;\n" % (n, n, folded(t, p)))
top = [(p, n, t) for (p, n, t) in blocks if not any(r != p and is_prefix(r, p) for (r, _, _) in blocks)]
rootf = root
for (p, n, t) in sorted(top, key=lambda b: -len(b[2])):
    k = rootf.count(t)
    if k != 1:
        sys.exit("hol_blocks: top block %s occurs %d times in the root" % (n, k))
    rootf = rootf.replace(t, n)
print("let %s = new_definition\n `%s = TProg %s %s %s`;;\n" % (name, name, decls, inits, rootf))
print("let %s_TERM = prove\n (`%s = %s`,\n  REWRITE_TAC[%s]);;" %
      (name.upper(), name, text, "; ".join([name] + [n for (_, n, _) in blocks])))
