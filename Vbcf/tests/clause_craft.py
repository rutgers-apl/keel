import struct, sys
class P:
    def __init__(s): s.e=[]; s.s=[]; s.nf=0
    def node(s, code, args=(), params=0):
        pos=len(s.e); s.e.append(code | len(args)<<8 | params<<16); s.e += list(args); return pos
    def bvval(s, w, v):
        pos=len(s.e); nw=(w+31)//32; s.e.append(0x08 | nw<<8 | w<<16); s.e.append(v & 0xffffffff)
        if nw==2: s.e.append(v>>32)
        return pos
    def step(s, rule, prems=(), params=()):
        s.s.append(rule | len(prems)<<16 | len(params)<<24); s.s += list(prems); s.s += list(params)
        s.nf += 1; return s.nf-1
    def write(s, path):
        w=[0x0BCF, len(s.e), len(s.s)] + s.e + s.s
        open(path,'wb').write(struct.pack('<%dI'%len(w), *w))
BVAR=0x19; NOT=0x81; OR=0x41; AND=0x01; EQ=0x11; BVAL=0x09
ASSUME=1; ACI=4; ABSORB=5; RES=0x2001; FAC=0x2002; REO=0x2003; ANDEL=0x2009
p=P()
a=p.node(BVAR); b=p.node(BVAR); c=p.node(BVAR); d=p.node(BVAR)
na=p.node(NOT,[a]); nb=p.node(NOT,[b]); nc=p.node(NOT,[c])
tt=p.node(BVAL,[],1); ff=p.node(BVAL,[],0)
c1=p.node(OR,[a,b,b]); c2=p.node(OR,[na,b]); c3=nb; c4=p.node(OR,[a,b,c]); c5=p.node(OR,[nc,d,a])
G=p.node(AND,[c1,c2,c3,c4,c5])
x=p.node(0x18,[],8); y=p.node(0x18,[],8); z=p.node(0x18,[],8); u=p.node(0x18,[],40)
def eq(l,r): return p.node(EQ,[l,r])
ab=p.node(AND,[a,b])
e1=eq(p.node(AND,[a,p.node(AND,[b,a])]), ab)
e1b=eq(ab, p.node(AND,[b,p.node(AND,[a,b]),a]))
e2=eq(p.node(AND,[a,tt]), a)
e2b=eq(a, p.node(OR,[ff,a]))
e3=eq(p.node(OR,[ff,ff]), ff)
e3b=eq(tt, p.node(AND,[tt,tt]))
e4=eq(p.node(0xa0,[x,p.node(0xa0,[y,x],8)],8), p.node(0xa0,[x,x,y],8))
xy=p.node(0x98,[x,y],16); yz=p.node(0x98,[y,z],16)
e5=eq(p.node(0x98,[xy,z],24), p.node(0x98,[x,yz],24))
e6=eq(p.node(0x50,[x,p.bvval(8,0xff)],8), x)
z40=p.bvval(40,0); o40=p.bvval(40,(1<<40)-1)
e7=eq(p.node(0x40,[u,z40],40), u)
e7b=eq(p.node(0xa0,[z40,u],40), u)
e8=eq(p.node(OR,[a,p.node(OR,[tt,b])]), tt)
z8=p.bvval(8,0)
e9=eq(p.node(0x50,[x,p.node(0x50,[y,z8],8)],8), z8)
e10=eq(p.node(0x40,[u,o40],40), o40)
e11=eq(p.node(AND,[a,p.node(AND,[b,ff])]), ff)
f0=p.step(ASSUME,[],[G])
f1=p.step(ANDEL,[f0],[0]); f2=p.step(ANDEL,[f0],[1]); f3=p.step(ANDEL,[f0],[2]); f4=p.step(ANDEL,[f0],[3]); f5=p.step(ANDEL,[f0],[4])
f6=p.step(FAC,[f1],[2 | 1<<8 | 2<<16])
f7=p.step(RES,[f4,f5],[1,c])
f8=p.step(FAC,[f7],[2 | 0<<8 | 3<<16])
f9=p.step(REO,[f8],[1 | (0x0200<<16)])
f10=p.step(REO,[f8],[2 | (0x0100<<16), 0x0201])
f11=p.step(REO,[f3],[12345])
f12=p.step(REO,[f8],[])
for e in [e1,e1b,e2,e2b,e3,e3b,e4,e5,e6,e7,e7b]: p.step(ACI,[],[e])
for e in [e8,e9,e10,e11]: p.step(ABSORB,[],[e])
f13=p.step(RES,[f6,f2,f3],[3,a,b])
f14=p.step(RES,[f3,f13],[0,b])
p.write(sys.argv[1])
