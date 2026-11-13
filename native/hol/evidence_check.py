#!/usr/bin/env python3
"""Compare a session's evidence (the EVIDENCE lines evidence_gate.ml prints:
MD5 digest and file name, for every file HOL Light's loader loaded) with the
files on disk, and name the stale evidence.

HOL Light's loader records base names only, so each name is looked up under
the source roots (evidence directories and their copied sources excluded).
A loaded file is current when some file of that name on disk has the
recorded digest, stale when files of that name exist but none has it, and
missing when no file of that name exists. Exit status 1 when any is stale or
missing.

Usage: evidence_check.py LOG [ROOT ...]
"""
import hashlib, os, re, sys

# The source roots, unless given on the command line: the trees named by
# HOLLIGHT_DIR, S2N_BIGNUM_DIR and METTAPEDIA_HOL_LIGHT when they are set, and
# this repository (TCALC_DIR, else two directories above this file).
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ROOTS = [os.environ[v] for v in ('HOLLIGHT_DIR', 'S2N_BIGNUM_DIR', 'METTAPEDIA_HOL_LIGHT')
         if os.environ.get(v)] + [os.environ.get('TCALC_DIR', REPO)]
SKIP = re.compile(r'(^|/)(evidence[^/]*|sources|\.git|_opam|_build)(/|$)')

def index(roots):
    by_name = {}
    for root in roots:
        for d, dirs, files in os.walk(root):
            if SKIP.search(d):
                dirs[:] = []
                continue
            dirs[:] = [x for x in dirs if not SKIP.search(os.path.join(d, x))]
            for f in files:
                by_name.setdefault(f, []).append(os.path.join(d, f))
    return by_name

def md5(path):
    h = hashlib.md5()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def main():
    log = sys.argv[1]
    roots = sys.argv[2:] or ROOTS
    ev = []
    text = re.sub(r'\x1B\[[0-9;]*m', '', open(log, errors='replace').read())
    for line in text.splitlines():
        m = re.match(r'^#?\s*EVIDENCE ([0-9a-f]{32}) (\S+)\s*$', line)
        if m:
            ev.append((m.group(1), m.group(2)))
    by_name = index(roots)
    bad = 0
    for dg, name in ev:
        paths = by_name.get(name, [])
        hit = [p for p in paths if md5(p) == dg]
        if hit:
            print('current  %s  %s' % (name, hit[0]))
        elif paths:
            bad += 1
            print('STALE    %s  (on disk: %s)' % (name, ', '.join(paths)))
        else:
            bad += 1
            print('MISSING  %s' % name)
    print('EVIDENCE-CHECK files %d, stale or missing %d' % (len(ev), bad))
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
