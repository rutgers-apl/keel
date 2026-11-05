import struct, sys, os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bool_gen.py')).read().split("out = sys.argv[1]")[0])
out = sys.argv[1]
CONTRA = 0x2008
for idx in (0, 1):
    p = P(); x, y = p.bvar(), p.bvar()
    imp = p.node(IMP, [x, y]); nimp = p.node(NOT, [imp])
    other = p.node(NOT, [x]) if idx == 0 else y
    g = p.node(CONJ, [nimp, other])
    p.step(ASSUME, [], [g]); a = p.step(AND_ELIM, [0], [0]); b = p.step(AND_ELIM, [0], [1])
    c = p.step(R['not_implies_elim'], [a], [idx])
    p.step(CONTRA, [c, b] if idx == 0 else [b, c], [])
    p.write(os.path.join(out, 'accept_not_implies_elim_%d.bcf' % idx))
