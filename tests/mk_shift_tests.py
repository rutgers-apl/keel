# Tiny .bcf proofs exercising the BITBLAST rule on shifts and bv ite.
# Circuits follow bcf_checker.c (bb_shift_limit, bb_bv_lsh, bb_rsh, bb_bv_ite).
import struct, sys, os
OUT = sys.argv[1]

class Pool:
    def __init__(self):
        self.exprs=[]; self.pos=0; self.memo={}
    def add(self, code, params, words, dedup=True):
        key=(code,params,tuple(words))
        if dedup and key in self.memo: return self.memo[key]
        r=self.pos; self.exprs.append((code,params,list(words))); self.pos+=1+len(words)
        if dedup: self.memo[key]=r
        return r
    # bool ops (ty=1)
    def T(self): return self.add(0x09,1,[])
    def F(self): return self.add(0x09,0,[])
    def NOT(self,a): return self.add(0x81,0,[a])
    def BITOF(self,i,v): return self.add(0x49,i,[v])
    def EQ(self,a,b): return self.add(0x11,0,[a,b])
    def ITE(self,c,t,e): return self.add(0x29,0,[c,t,e])
    def CONJ(self,*a): return self.add(0x01,0,list(a))
    def DISJ(self,*a): return self.add(0x41,0,list(a))
    # bv ops (ty=0)
    def VAR(self,w): return self.add(0x18,w,[],dedup=False)
    def FROMBOOL(self,bits): return self.add(0x88,0,list(bits))
    def SHL(self,w,a,b): return self.add(0x60,w,[a,b])
    def LSHR(self,w,a,b): return self.add(0x70,w,[a,b])
    def ASHR(self,w,a,b): return self.add(0xc0,w,[a,b])
    def BVITE(self,w,c,a,b): return self.add(0x28,w,[c,a,b])
    def bits(self,v,w): return [self.BITOF(i,v) for i in range(w)]
    def words(self):
        def nb(code,params,ws):
            hdr=(code&0xff)|((len(ws)&0xff)<<8)|((params&0xffff)<<16)
            return struct.pack('<I',hdr)+b''.join(struct.pack('<I',w&0xffffffff) for w in ws)
        return b''.join(nb(*e) for e in self.exprs)

def log2ceil(n): return 0 if n<=1 else (n-1).bit_length()

def ult(p, lhs_msb_first, rhs_msb_first):
    """bb_ult, strict: res = ((l==r) ∧ rest) ∨ (¬l ∧ r); base ¬l0 ∧ r0."""
    l, r = lhs_msb_first[0], rhs_msb_first[0]
    if len(lhs_msb_first)==1:
        return p.CONJ(p.NOT(l), r)
    rest = ult(p, lhs_msb_first[1:], rhs_msb_first[1:])
    return p.DISJ(p.CONJ(p.EQ(l,r), rest), p.CONJ(p.NOT(l), r))

def shift_circuit(p, kind, w, xs, ys, fill_wrong=False, swap_wrong=False):
    fill = p.F() if kind!='ashr' else xs[w-1]
    cur = list(xs)
    for i in range(log2ceil(w)):
        T = 1<<i; b = ys[i]; nxt=[]
        for j in range(w):
            if kind=='shl':
                inj = p.F() if j<T else cur[j-T]
                nxt.append(p.ITE(b, inj, cur[j]))
            else:
                if j+T >= w: nxt.append(p.ITE(b, fill, cur[j]))
                else: nxt.append(p.ITE(p.NOT(b), cur[j], cur[j+T]))
        cur = nxt
    res = cur
    wbits = [p.T() if (w>>i)&1 else p.F() for i in range(w)]
    cond = ult(p, list(reversed(ys)), list(reversed(wbits)))
    if fill_wrong: fill = p.T()
    out = [p.ITE(cond, res[j], fill) for j in range(w)]
    if swap_wrong: out[0], out[1] = out[1], out[0]
    return out

def ite_circuit(p, c, ts, es):
    return [p.CONJ(p.DISJ(p.NOT(c), ts[i]), p.DISJ(c, es[i])) for i in range(len(ts))]

def proof(pool, E):
    G = pool.NOT(E)
    ASSUME=1; BITBLAST=0x4001; CONTRA=0x2008
    steps=[(ASSUME,[],[G]), (BITBLAST,[],[E]), (CONTRA,[1,0],[])]
    def sb(rule,prems,params):
        hdr=(rule&0xffff)|((len(prems)&0xff)<<16)|((len(params)&0xff)<<24)
        return struct.pack('<I',hdr)+b''.join(struct.pack('<I',w&0xffffffff) for w in prems+params)
    step_sec=b''.join(sb(*s) for s in steps)
    expr_sec=pool.words()
    return struct.pack('<III',0x0BCF,len(expr_sec)//4,len(step_sec)//4)+expr_sec+step_sec

def mk_shift(kind, w, **bad):
    p=Pool(); x=p.VAR(w); y=p.VAR(w)
    xs=p.bits(x,w); ys=p.bits(y,w)
    term={'shl':p.SHL,'lshr':p.LSHR,'ashr':p.ASHR}[kind](w,p.FROMBOOL(xs),p.FROMBOOL(ys))
    bs=shift_circuit(p,kind,w,xs,ys,**bad)
    return proof(p, p.EQ(term, p.FROMBOOL(bs)))

def mk_ite(w, wrong=False):
    p=Pool(); c=p.add(0x19,0,[],dedup=False); a=p.VAR(w); b=p.VAR(w)
    ts=p.bits(a,w); es=p.bits(b,w)
    term=p.BVITE(w,c,p.FROMBOOL(ts),p.FROMBOOL(es))
    bs=ite_circuit(p,c,ts,es) if not wrong else ite_circuit(p,c,es,ts)
    return proof(p, p.EQ(term, p.FROMBOOL(bs)))

tests = {
  'shl_w1.bcf': mk_shift('shl',1), 'shl_w2.bcf': mk_shift('shl',2), 'shl_w5.bcf': mk_shift('shl',5),
  'shl_w8.bcf': mk_shift('shl',8), 'lshr_w4.bcf': mk_shift('lshr',4), 'lshr_w6.bcf': mk_shift('lshr',6),
  'ashr_w2.bcf': mk_shift('ashr',2), 'ashr_w8.bcf': mk_shift('ashr',8), 'ite_w3.bcf': mk_ite(3),
  'BAD_shl_fill.bcf': mk_shift('shl',4,fill_wrong=True), 'BAD_lshr_swap.bcf': mk_shift('lshr',4,swap_wrong=True),
  'BAD_ashr_fill.bcf': mk_shift('ashr',4,fill_wrong=True), 'BAD_ite_swapped.bcf': mk_ite(3,wrong=True),
}
for name,data in tests.items():
    open(os.path.join(OUT,name),'wb').write(data)
print("wrote", len(tests), "files")
