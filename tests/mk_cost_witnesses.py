#!/usr/bin/env python3
# Valid proofs whose single ACI_NORM / POLY_NORM / EVALUATE / ABSORB step is exponential for a
# checker that walks the shared DAG as a tree: x_k = op(x_{k-1}, x_{k-1}), depth K, about 50 words.
# The Lean checker accepts them (exponential time, except EVALUATE which is memoised); the C checker
# rejects them once the step exceeds its work budget (depth 16 for aci/poly, 20 for eval).
# usage: mk_cost_witnesses.py <aci|poly|eval|absorb> <K> <out.bcf>
import struct, sys
kind, K, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
exprs = []; pos = 0
def add(code, params, words):
    global pos
    exprs.append((code, params, words)); r = pos; pos += 1 + len(words); return r
ASSUME=1; EVAL=2; ACI=4; ABSORB=5; CONTRA=0x2008; POLY=0x4002; REFL=7; TRANS=9; SYMM=8
steps = []
if kind == 'aci':
    x0 = add(0x18, 8, [])                      # var:8
    x = x0
    for _ in range(K): x = add(0x50, 8, [x, x])  # bvand8(x, x)
    eq = add(0x11, 0, [x, x0]); goal = add(0x81, 0, [eq])
    steps = [(ASSUME, [], [goal]), (ACI, [], [eq]), (CONTRA, [1, 0], [])]
elif kind == 'poly':
    x0 = add(0x18, 32, [])
    x = x0
    for _ in range(K): x = add(0x00, 32, [x, x])  # bvadd32(x, x)
    c = add(0x08, 32, [(1 << K) & 0xffffffff])
    rhs = add(0x20, 32, [c, x0])                   # bvmul32(2^K, x0)
    eq = add(0x11, 0, [x, rhs]); goal = add(0x81, 0, [eq])
    steps = [(ASSUME, [], [goal]), (POLY, [], [eq]), (CONTRA, [1, 0], [])]
elif kind == 'eval':
    x = add(0x08, 32, [1])
    for _ in range(K): x = add(0x00, 32, [x, x])  # bvadd32(c, c) = 2^K
    c = add(0x08, 32, [(1 << K) & 0xffffffff])
    eq = add(0x11, 0, [x, c]); goal = add(0x81, 0, [eq])
    steps = [(ASSUME, [], [goal]), (EVAL, [], [x]), (CONTRA, [1, 0], [])]
elif kind == 'absorb':
    x0 = add(0x18, 8, [])
    z = add(0x08, 8, [0])
    x = add(0x50, 8, [x0, z])                      # bvand8(x0, 0)  -- contains the zero
    for _ in range(K): x = add(0x50, 8, [x, x])
    eq = add(0x11, 0, [x, z]); goal = add(0x81, 0, [eq])
    steps = [(ASSUME, [], [goal]), (ABSORB, [], [eq]), (CONTRA, [1, 0], [])]
def nb(code, params, words):
    return struct.pack('<I', (code & 255) | (len(words) << 8) | (params << 16)) + b''.join(struct.pack('<I', w) for w in words)
def sb(rule, prems, params):
    return struct.pack('<I', rule | (len(prems) << 16) | (len(params) << 24)) + b''.join(struct.pack('<I', w) for w in prems + params)
es = b''.join(nb(*e) for e in exprs); ss = b''.join(sb(*s) for s in steps)
open(out, 'wb').write(struct.pack('<III', 0xBCF, len(es) // 4, len(ss) // 4) + es + ss)
print(out, len(es) // 4 + len(ss) // 4 + 3, 'words')
