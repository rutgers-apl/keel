#!/usr/bin/env python3
"""Tiny .bcf proofs exercising the boolean elimination / CNF rules.
One file per case, so every node a rule creates is fresh and the node-by-node
comparison against the Lean trace checks creation order."""
import struct, sys, os

CONJ, BVAL, EQ, BVAR, ITE, XOR, DISJ, NOT, IMP = 0x01, 0x09, 0x11, 0x19, 0x29, 0x39, 0x41, 0x81, 0x91
BV_VAR, BV_ITE = 0x18, 0x28
ASSUME, AND_ELIM = 0x0001, 0x2009
R = dict(implies_elim=0x200c, not_implies_elim=0x200d, equiv_elim=0x200e, not_equiv_elim=0x200f,
         xor_elim=0x2010, not_xor_elim=0x2011, ite_elim=0x2012, not_ite_elim=0x2013, not_and=0x2014,
         cnf_and_pos=0x2015, cnf_and_neg=0x2016, cnf_or_pos=0x2017, cnf_or_neg=0x2018,
         cnf_implies_pos=0x2019, cnf_implies_neg=0x201a, cnf_equiv_pos=0x201b, cnf_equiv_neg=0x201c,
         cnf_xor_pos=0x201d, cnf_xor_neg=0x201e, cnf_ite_pos=0x201f, cnf_ite_neg=0x2020, ite_eq=0x2021)

class P:
    def __init__(self):
        self.ex = []; self.steps = []; self.nsteps = 0
    def node(self, code, args=(), params=0, leaf=False):
        pos = len(self.ex)
        self.ex.append(code | (len(args) << 8) | (params << 16))
        self.ex.extend(args)
        return pos
    def bvar(self): return self.node(BVAR)
    def bvvar(self, w): return self.node(BV_VAR, params=w)
    def step(self, rule, prems=(), pars=()):
        self.steps.append(rule | (len(prems) << 16) | (len(pars) << 24))
        self.steps.extend(prems); self.steps.extend(pars)
        self.nsteps += 1
        return self.nsteps - 1
    def write(self, path):
        w = [0x0BCF, len(self.ex), len(self.steps)] + self.ex + self.steps
        with open(path, 'wb') as f:
            f.write(struct.pack('<%dI' % len(w), *w))

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
count = 0

def shapes(p):
    """A dictionary of formulas over fresh variables."""
    x, y, z = p.bvar(), p.bvar(), p.bvar()
    a, b, c1 = p.bvvar(8), p.bvvar(8), p.bvvar(1)
    s = {}
    s['x'] = x
    s['imp'] = p.node(IMP, [x, y])
    s['eq'] = p.node(EQ, [x, y])
    s['bveq'] = p.node(EQ, [a, b])
    s['xor'] = p.node(XOR, [x, y])
    s['xor3'] = p.node(XOR, [x, y, z])
    s['ite'] = p.node(ITE, [x, y, z])
    s['conj'] = p.node(CONJ, [x, y, z])
    s['conj2'] = p.node(CONJ, [y, x])
    s['disj'] = p.node(DISJ, [x, y, z])
    s['disj2'] = p.node(DISJ, [z, y])
    s['bvite'] = p.node(BV_ITE, [x, a, b], params=8)
    s['bvite1'] = p.node(BV_ITE, [c1, a, b], params=8)
    for k in list(s):
        if k not in ('bvite', 'bvite1'):
            s['n' + k] = p.node(NOT, [s[k]])
    s['nnimp'] = p.node(NOT, [s['nimp']])
    return s

def prem_case(name, rule, shape, pars, np=1):
    """rule applied to a premise of the given shape (obtained by AND_ELIM from the goal)."""
    global count
    p = P()
    s = shapes(p)
    g = p.node(CONJ, [s[shape], s['x']])
    p.step(ASSUME, [], [g])
    f = p.step(AND_ELIM, [0], [0])
    prems = [f] * np
    p.step(R[rule], prems, pars)
    p.write(os.path.join(out, name + '.bcf')); count += 1

def cnf_case(name, rule, shape, pars, np=0, raw=None):
    global count
    p = P()
    s = shapes(p)
    p.step(ASSUME, [], [s['x']])
    e = s[shape] if raw is None else raw(s)
    p.step(R[rule], [0] * np, [e] + list(pars))
    p.write(os.path.join(out, name + '.bcf')); count += 1

BIG = [2, 3, 4, 255, 256, 257, 0x10000, 0x10001, 0xffffffff]

# ---- premise rules: (rule, right shape, valid params) ----
prem_rules = [
    ('implies_elim', 'imp', [[]]),
    ('not_implies_elim', 'nimp', [[0], [1]]),
    ('equiv_elim', 'eq', [[0], [1]]),
    ('not_equiv_elim', 'neq', [[0], [1]]),
    ('xor_elim', 'xor', [[0], [1]]),
    ('not_xor_elim', 'nxor', [[0], [1]]),
    ('ite_elim', 'ite', [[0], [1]]),
    ('not_ite_elim', 'nite', [[0], [1]]),
    ('not_and', 'nconj', [[], [0], [7, 9], [1, 2, 3]]),
    ('not_and', 'nconj2', [[]]),
]
all_shapes = ['x', 'imp', 'eq', 'bveq', 'xor', 'xor3', 'ite', 'conj', 'conj2', 'disj', 'disj2',
              'nx', 'nimp', 'neq', 'nbveq', 'nxor', 'nxor3', 'nite', 'nconj', 'nconj2', 'ndisj',
              'ndisj2', 'nnimp']
for rule, shape, plist in prem_rules:
    for ps in plist:
        prem_case('ok_%s_%s_%s' % (rule, shape, '_'.join(map(str, ps))), rule, shape, ps)
    nparams = len(plist[0])
    # every shape with every small parameter (most are rejected by both)
    if shape != 'nconj2':
        for sh in all_shapes:
            for v in ([[]] if nparams == 0 else [[0], [1]]):
                prem_case('sh_%s_%s_%s' % (rule, sh, '_'.join(map(str, v))), rule, sh, v)
        # out-of-range parameters
        if nparams == 1:
            for v in BIG:
                prem_case('big_%s_%d' % (rule, v), rule, shape, [v])
        # wrong parameter / premise counts
        for na in range(0, 4):
            if na != nparams:
                prem_case('na_%s_%d' % (rule, na), rule, shape, [0] * na)
                prem_case('na1_%s_%d' % (rule, na), rule, shape, [1] * na)
        for np in (0, 2, 3):
            prem_case('np_%s_%d' % (rule, np), rule, shape, plist[0], np=np)

# ---- CNF rules ----
cnf_rules = [
    ('cnf_and_pos', 'conj', [[0], [1], [2]]),
    ('cnf_and_neg', 'conj', [[]]),
    ('cnf_or_pos', 'disj', [[]]),
    ('cnf_or_neg', 'disj', [[0], [1], [2]]),
    ('cnf_implies_pos', 'imp', [[]]),
    ('cnf_implies_neg', 'imp', [[0], [1]]),
    ('cnf_equiv_pos', 'eq', [[0], [1]]),
    ('cnf_equiv_neg', 'eq', [[0], [1]]),
    ('cnf_xor_pos', 'xor', [[0], [1]]),
    ('cnf_xor_neg', 'xor', [[0], [1]]),
    ('cnf_ite_pos', 'ite', [[0], [1], [2]]),
    ('cnf_ite_neg', 'ite', [[0], [1], [2]]),
    ('ite_eq', 'ite', [[]]),
    ('ite_eq', 'bvite', [[]]),
    ('ite_eq', 'bvite1', [[]]),
]
seen = set()
for rule, shape, plist in cnf_rules:
    for ps in plist:
        cnf_case('ok_%s_%s_%s' % (rule, shape, '_'.join(map(str, ps))), rule, shape, ps)
    if rule in seen:
        continue
    seen.add(rule)
    nparams = len(plist[0])
    for sh in all_shapes + ['bvite', 'bvite1']:
        for v in ([[]] if nparams == 0 else [[0], [1], [2]]):
            cnf_case('sh_%s_%s_%s' % (rule, sh, '_'.join(map(str, v))), rule, sh, v)
    if nparams == 1:
        for v in BIG:
            cnf_case('big_%s_%d' % (rule, v), rule, shape, [v])
    for na in range(0, 4):
        if na != nparams:
            cnf_case('na_%s_%d' % (rule, na), rule, shape, [0] * na)
    # no expression parameter at all
    p = P(); s = shapes(p); p.step(ASSUME, [], [s['x']]); p.step(R[rule], [], [])
    p.write(os.path.join(out, 'na_%s_none.bcf' % rule)); count += 1
    for np in (1, 2):
        cnf_case('np_%s_%d' % (rule, np), rule, shape, plist[0], np=np)
    # expression positions that are not expressions
    cnf_case('pos_%s_mid' % rule, rule, shape, plist[0], raw=lambda s: s[shape] + 1)
    cnf_case('pos_%s_end' % rule, rule, shape, plist[0], raw=lambda s: 100000)
    cnf_case('pos_%s_max' % rule, rule, shape, plist[0], raw=lambda s: 0xffffffff)

# ---- wide operands: n-ary conj / disj with n = 2, 254, 255 ----
for n in (2, 3, 100, 254, 255):
    for rule, code in (('cnf_and_neg', CONJ), ('cnf_or_pos', DISJ), ('cnf_and_pos', CONJ),
                       ('cnf_or_neg', DISJ)):
        p = P()
        vs = [p.bvar() for _ in range(n)]
        e = p.node(code, vs)
        p.step(ASSUME, [], [vs[0]])
        pars = [e] if rule in ('cnf_and_neg', 'cnf_or_pos') else [e, n - 1]
        p.step(R[rule], [], pars)
        p.write(os.path.join(out, 'wide_%s_%d.bcf' % (rule, n))); count += 1
        if rule in ('cnf_and_pos', 'cnf_or_neg'):
            p = P()
            vs = [p.bvar() for _ in range(n)]
            e = p.node(code, vs)
            p.step(ASSUME, [], [vs[0]])
            p.step(R[rule], [], [e, n])
            p.write(os.path.join(out, 'wide_%s_%d_oob.bcf' % (rule, n))); count += 1
    p = P()
    vs = [p.bvar() for _ in range(n)]
    e = p.node(CONJ, vs)
    ne = p.node(NOT, [e])
    g = p.node(CONJ, [ne, vs[0]])
    p.step(ASSUME, [], [g])
    f = p.step(AND_ELIM, [0], [0])
    p.step(R['not_and'], [f], [])
    p.write(os.path.join(out, 'wide_not_and_%d.bcf' % n)); count += 1

# ---- repeated literals (interning hits inside one step) ----
def rep_case(name, build):
    global count
    p = P(); build(p); p.write(os.path.join(out, name + '.bcf')); count += 1

def rep_and(p):
    x = p.bvar(); e = p.node(CONJ, [x, x, x])
    p.step(ASSUME, [], [x]); p.step(R['cnf_and_neg'], [], [e])
rep_case('rep_cnf_and_neg', rep_and)
def rep_eq(form, rule):
    def b(p):
        x = p.bvar(); e = p.node(EQ, [x, x])
        p.step(ASSUME, [], [x]); p.step(R[rule], [], [e, form])
    return b
for rule in ('cnf_equiv_pos', 'cnf_equiv_neg'):
    for form in (0, 1):
        rep_case('rep_%s_%d' % (rule, form), rep_eq(form, rule))
def rep_xor(form, rule):
    def b(p):
        x = p.bvar(); e = p.node(XOR, [x, x])
        p.step(ASSUME, [], [x]); p.step(R[rule], [], [e, form])
    return b
for rule in ('cnf_xor_pos', 'cnf_xor_neg'):
    for form in (0, 1):
        rep_case('rep_%s_%d' % (rule, form), rep_xor(form, rule))
def rep_ite(lit, rule):
    def b(p):
        x = p.bvar(); e = p.node(ITE, [x, x, x])
        p.step(ASSUME, [], [x]); p.step(R[rule], [], [e] + ([lit] if lit is not None else []))
    return b
for rule in ('cnf_ite_pos', 'cnf_ite_neg'):
    for lit in (0, 1, 2):
        rep_case('rep_%s_%d' % (rule, lit), rep_ite(lit, rule))
rep_case('rep_ite_eq', rep_ite(None, 'ite_eq'))
# ite whose branches are the ite's own condition negated etc.: e = ite(x, e', e') nested
def nest(p):
    x, y = p.bvar(), p.bvar()
    i1 = p.node(ITE, [x, y, x]); i2 = p.node(ITE, [i1, i1, y])
    p.step(ASSUME, [], [x]); p.step(R['ite_eq'], [], [i2]); p.step(R['cnf_ite_pos'], [], [i2, 0])
    p.step(R['cnf_ite_neg'], [], [i2, 2]); p.step(R['ite_eq'], [], [i1])
rep_case('rep_nest', nest)

# ---- one combined proof using every rule in sequence (shared pool) ----
p = P(); s = shapes(p)
names = ['imp', 'nimp', 'eq', 'neq', 'xor', 'nxor', 'ite', 'nite', 'nconj']
g = p.node(CONJ, [s[k] for k in names])
p.step(ASSUME, [], [g])
fact = {k: p.step(AND_ELIM, [0], [i]) for i, k in enumerate(names)}
for rule, shape, plist in prem_rules:
    if shape in fact:
        for ps in plist:
            p.step(R[rule], [fact[shape]], ps)
for rule, shape, plist in cnf_rules:
    if shape != 'bvite1':
        for ps in plist:
            p.step(R[rule], [], [s[shape]] + ps)
p.write(os.path.join(out, 'all_in_one.bcf')); count += 1
print(count, 'files')
