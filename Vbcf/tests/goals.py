#!/usr/bin/env python3
"""Goal-comparison tests: verifier arenas for each proof, with expectations.

For a proof, writes arena files (little-endian u32 words, like BCF's
`struct bcf_expr` array) into an output directory and prints one line per
case:

    <proof> <arena-file> <goal> <expect>

`expect` is `same` (the result must equal the result with a NULL arena) or
`reject` (the result must be non-zero).  Cases:

* self:    the proof's own expression section, goal = the ASSUME parameter.
* relaid:  the goal DAG copied into a fresh arena: junk nodes in front and
           between, variables renamed (new positions), children in a random
           order of emission, some subterms unshared (emitted twice).
* merge:   two distinct proof variables of the same sort become one arena
           variable (not a bijection).
* split:   one proof variable becomes two arena variables (not a function).
* const:   one bit-vector literal changed.
* op:      one operator replaced by another of the same arity and sort.
* fwd:     an argument pointing at a later node, or at the node itself.
* overlap: an argument pointing into the middle of an earlier node.

usage: goals.py <out-dir> <seed> <file.bcf>...
"""
import os
import random
import struct
import sys

BV_VAL, BV_VAR, BOOL_VAL, BOOL_VAR = 0x08, 0x18, 0x09, 0x19
LEAVES = (BV_VAL, BV_VAR, BOOL_VAL, BOOL_VAR)
# operators with the same arity and argument/result sorts, for `op`
SWAP = {0x00: 0x50, 0x50: 0x40, 0x40: 0xa0, 0xa0: 0x00,      # bvadd/and/or/xor
        0x20: 0x10, 0x10: 0x20,                              # bvmul/sub
        0x21: 0x31, 0x31: 0xa1, 0xa1: 0xb1, 0xb1: 0x21,      # ugt/uge/ult/ule
        0x61: 0x71, 0x71: 0xc1, 0xc1: 0xd1, 0xd1: 0x61,      # sgt/sge/slt/sle
        0x01: 0x41, 0x41: 0x01}                              # and/or


def parse(path):
    b = open(path, 'rb').read()
    if len(b) < 12 or len(b) % 4:
        return None
    w = struct.unpack('<%dI' % (len(b) // 4), b)
    ne, ns = w[1], w[2]
    if 3 + ne + ns != len(w):
        return None
    E, S = list(w[3:3 + ne]), w[3 + ne:]
    p, g, n = 0, None, 0
    while p < ns:
        h = S[p]
        pc, ac = (h >> 16) & 0xff, h >> 24
        if h & 0xffff == 1:
            n += 1
            if ac == 1 and p + 1 + pc < ns:
                g = S[p + 1 + pc]
        p += 1 + pc + ac
    if n != 1 or g is None or g >= ne:
        return None
    return E, g


def node(E, p):
    h = E[p]
    vl = (h >> 8) & 0xff
    return h, E[p + 1:p + 1 + vl]


def reach(E, g):
    """Positions reachable from g (each a valid backward-pointing node)."""
    seen, st = set(), [g]
    while st:
        x = st.pop()
        if x in seen:
            continue
        if x >= len(E):
            return None
        seen.add(x)
        h, args = node(E, x)
        if len(args) != (h >> 8) & 0xff:
            return None
        if h & 0xff not in LEAVES:
            for a in args:
                if a >= x:
                    return None
                st.append(a)
    return seen


class Arena:
    def __init__(self, rnd):
        self.w = []
        self.rnd = rnd

    def emit(self, hdr, args):
        p = len(self.w)
        self.w.append(hdr)
        self.w.extend(args)
        return p

    def junk(self):
        r = self.rnd.random()
        if r < 0.4:
            self.emit(BV_VAR | (self.rnd.choice([8, 32, 64]) << 16), [])
        elif r < 0.7:
            self.emit(BV_VAL | (1 << 8) | (32 << 16), [self.rnd.getrandbits(32)])
        else:
            self.emit(BOOL_VAR, [])


def relay(E, g, rnd, varmap=None, unshare=0.0, junk=0.2, budget=200000):
    """Copy the DAG at g into a fresh arena.  varmap(p) -> key decides which
    proof variables share an arena variable (default: one per proof var)."""
    A = Arena(rnd)
    memo, vmemo = {}, {}
    for _ in range(rnd.randint(0, 3)):
        A.junk()

    def go(p, parent_key):
        h, args = node(E, p)
        code = h & 0xff
        if code in (BV_VAR, BOOL_VAR):
            key = varmap(p, parent_key) if varmap else p
            if key not in vmemo:
                if rnd.random() < junk:
                    A.junk()
                vmemo[key] = A.emit(h, [])
            return vmemo[key]
        share = not (unshare and rnd.random() < unshare and len(A.w) < budget)
        if share and p in memo:
            return memo[p]
        if code in (BV_VAL, BOOL_VAL):
            out = A.emit(h, list(args))
        else:
            order = list(range(len(args)))
            rnd.shuffle(order)
            kids = [None] * len(args)
            for k in order:
                kids[k] = go(args[k], (p, k))
            if rnd.random() < junk:
                A.junk()
            out = A.emit(h, kids)
        if share:
            memo[p] = out
        return out

    root = go(g, None)
    for _ in range(rnd.randint(0, 2)):
        A.junk()
    return A.w, root


def write(path, words):
    with open(path, 'wb') as f:
        f.write(struct.pack('<%dI' % len(words), *words))


def cases(path, out, rnd):
    r = parse(path)
    if r is None:
        return []
    E, g = r
    R = reach(E, g)
    if R is None:
        return []
    name = os.path.basename(path)[:-4]
    res = []

    def add(tag, words, root, expect):
        f = os.path.join(out, f'{name}.{tag}.arena')
        write(f, words)
        res.append((path, f, root, expect))

    add('self', E, g, 'same')
    for i in range(2):
        w, root = relay(E, g, rnd, unshare=0.3 * i)
        add(f'relaid{i}', w, root, 'same')

    vars_ = [p for p in R if E[p] & 0xff in (BV_VAR, BOOL_VAR)]
    bysort = {}
    for p in vars_:
        bysort.setdefault(E[p], []).append(p)
    pairs = [ps for ps in bysort.values() if len(ps) >= 2]
    if pairs:
        a, b = rnd.sample(rnd.choice(pairs), 2)
        w, root = relay(E, g, rnd, varmap=lambda p, _k: a if p == b else p)
        add('merge', w, root, 'reject')
    # a proof variable used at two or more argument slots
    uses = {}
    for p in R:
        h, args = node(E, p)
        if h & 0xff not in LEAVES:
            for k, a in enumerate(args):
                if E[a] & 0xff in (BV_VAR, BOOL_VAR):
                    uses.setdefault(a, []).append((p, k))
    multi = [v for v, u in uses.items() if len(u) >= 2]
    if multi:
        v = rnd.choice(multi)
        first = uses[v][0]
        w, root = relay(E, g, rnd,
                        varmap=lambda p, k: (p, 'split') if p == v and k != first else p)
        add('split', w, root, 'reject')
    # mutations of the self arena
    vals = [p for p in R if E[p] & 0xff == BV_VAL]
    if vals:
        p = rnd.choice(vals)
        wd = (E[p] >> 16) & 0xff
        w = list(E)
        w[p + 1] ^= 1 << rnd.randrange(min(wd, 32))
        add('const', w, g, 'reject')
    ops = [p for p in R if E[p] & 0xff in SWAP]
    if ops:
        p = rnd.choice(ops)
        w = list(E)
        w[p] = (w[p] & ~0xff) | SWAP[w[p] & 0xff]
        add('op', w, g, 'reject')
    inner = [p for p in R if E[p] & 0xff not in LEAVES and (E[p] >> 8) & 0xff]
    if inner:
        p = rnd.choice(inner)
        k = rnd.randrange((E[p] >> 8) & 0xff)
        w = list(E)
        w[p + 1 + k] = p if rnd.random() < 0.5 else min(p + 1 + rnd.randrange(8), len(E) - 1)
        add('fwd', w, g, 'reject')
        # point into an earlier node with arguments, past its header
        cands = [q for q in R if q < p and (E[q] >> 8) & 0xff]
        if cands:
            q = rnd.choice(cands)
            w = list(E)
            w[p + 1 + k] = q + 1
            add('overlap', w, g, 'reject')
    return res


def main():
    out, seed, files = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
    rnd = random.Random(seed)
    for f in files:
        for c in cases(f, out, rnd):
            print(*c)


if __name__ == '__main__':
    main()
