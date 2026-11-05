# Differential test generator for BITBLAST: canonical circuits for every bbTerm/bbAtom case, plus mutants.
# usage: fuzz.py <outdir> <count> <seed>
import struct, sys, os, random
OUT, COUNT, SEED = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
JUNK = len(sys.argv) > 4
rnd = random.Random(SEED)
BOOL2 = [0x01, 0x41, 0x39, 0x11]   # conj disj xor eq

class Pool:
    def __init__(self, mut_at=None):
        self.exprs=[]; self.pos=0; self.memo={}; self.ty={}; self.calls=0; self.mut_at=mut_at; self.frozen=True
        self.mutated=None
    def raw(self, code, params, words, ty, dedup=True):
        key=(code,params,tuple(words))
        if dedup and key in self.memo: return self.memo[key]
        r=self.pos; self.exprs.append((code,params,list(words))); self.pos+=1+len(words)
        self.ty[r]=ty
        if dedup: self.memo[key]=r
        return r
    def add(self, code, params, words, ty, dedup=True):
        words=list(words)
        if not self.frozen:
            self.calls+=1
            if self.calls==self.mut_at:
                code,params,words=self.mutate(code,params,words,ty)
        return self.raw(code,params,words,ty,dedup)
    def some_bool(self):
        c=[p for p,t in self.ty.items() if t=='b']
        return rnd.choice(c)
    def mutate(self, code, params, words, ty):
        k=rnd.randrange(6)
        self.mutated=(hex(code),k)
        if code==0x09:  # bool const: flip
            return code, params^1, words
        if code==0x49 and k<3:  # bitof: other index
            return code, (params-1 if params>0 else params), words
        if k==0 and len(words)>=2:
            i,j=rnd.sample(range(len(words)),2); words[i],words[j]=words[j],words[i]; return code,params,words
        if k==1 and code in BOOL2 and len(words)==2 and all(self.ty[w]=='b' for w in words):
            return rnd.choice([c for c in BOOL2 if c!=code]), params, words
        if k==2 and code in (0x01,0x41,0x39):
            return code, params, words+[self.some_bool()]
        # replace one argument with another node of the same type
        if words:
            i=rnd.randrange(len(words)); t=self.ty[words[i]]
            c=[p for p,tt in self.ty.items() if tt==t and p!=words[i]]
            if c: words[i]=rnd.choice(c)
        return code,params,words
    # bool ops
    def T(self): return self.add(0x09,1,[],'b')
    def F(self): return self.add(0x09,0,[],'b')
    def NOT(self,a): return self.add(0x81,0,[a],'b')
    def BITOF(self,i,v): return self.add(0x49,i,[v],'b')
    def EQ(self,a,b): return self.add(0x11,0,[a,b],'b')
    def XOR(self,*a): return self.add(0x39,0,list(a),'b')
    def ITE(self,c,t,e): return self.add(0x29,0,[c,t,e],'b')
    def CONJ(self,*a): return self.add(0x01,0,list(a),'b')
    def DISJ(self,*a): return self.add(0x41,0,list(a),'b')
    def BVAR(self): return self.raw(0x19,0,[],'b',dedup=False)
    def VAR(self,w): return self.raw(0x18,w,[],w,dedup=False)
    def VAL(self,w,v):
        ws=[v&0xffffffff] if w<=32 else [v&0xffffffff, v>>32]
        return self.raw(0x08,w,ws,w)
    def FROMBOOL(self,bits): return self.raw(0x88,0,list(bits),len(bits))
    def words(self):
        def nb(code,params,ws):
            hdr=(code&0xff)|((len(ws)&0xff)<<8)|((params&0xffff)<<16)
            return struct.pack('<I',hdr)+b''.join(struct.pack('<I',w&0xffffffff) for w in ws)
        return b''.join(nb(*e) for e in self.exprs)

def log2ceil(n): return 0 if n<=1 else (n-1).bit_length()

def ult(p, l, r, weq=False):
    """l, r most significant first."""
    if len(l)==1:
        base = p.CONJ(p.NOT(l[0]), r[0])
        return p.DISJ(base, p.EQ(l[0], r[0])) if weq else base
    rest = ult(p, l[1:], r[1:], weq)
    return p.DISJ(p.CONJ(p.EQ(l[0],r[0]), rest), p.CONJ(p.NOT(l[0]), r[0]))

def slt(p, l, r, weq=False):
    rest = ult(p, l[1:], r[1:], weq)
    return p.DISJ(p.CONJ(p.EQ(l[0],r[0]), rest), p.CONJ(l[0], p.NOT(r[0])))

def ripple(p, a, b, init):
    c = p.T() if init else p.F()
    out=[]
    for j in range(len(a)):
        if j>0:
            c = p.DISJ(p.CONJ(a[j-1],b[j-1]), p.CONJ(p.XOR(a[j-1],b[j-1]), c))
        out.append(p.XOR(p.XOR(a[j],b[j]), c))
    return out

def shift_circuit(p, kind, xs, ys):
    w=len(xs)
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
    wbits = [p.T() if (w>>i)&1 else p.F() for i in range(len(ys))]
    cond = ult(p, list(reversed(ys)), list(reversed(wbits)))
    return [p.ITE(cond, cur[j], fill) for j in range(w)]

def chain(p, op, col):
    acc=col[0]
    for c in col[1:]: acc=p.add(op,0,[acc,c],'b')
    return acc

def operand(p, w):
    """bits of a fresh operand: mostly bitof of a variable, sometimes other boolean nodes."""
    r=rnd.random()
    x=p.VAR(w)
    if r<0.7: return [p.raw(0x49,i,[x],'b') for i in range(w)]
    if r<0.8: return [p.BVAR() for i in range(w)]
    out=[]
    for i in range(w):
        q=rnd.random()
        if q<0.4: out.append(p.raw(0x49,i,[x],'b'))
        elif q<0.6: out.append(p.BVAR())
        elif q<0.7: out.append(p.raw(0x09,rnd.randrange(2),[],'b'))
        elif q<0.85: out.append(p.raw(0x81,0,[p.raw(0x49,i,[x],'b')],'b'))
        else: out.append(p.raw(0x01,0,[p.BVAR(),p.raw(0x49,i,[x],'b')],'b'))
    return out

def junk(p, d=0):
    """a random boolean node of arbitrary shape (leaves included)."""
    q=rnd.randrange(14 if d<3 else 5)
    if q==0: return p.raw(0x09,rnd.randrange(2),[],'b')
    if q==1: return p.BVAR()
    if q==2:
        w=rnd.randint(1,8); return p.raw(0x49,rnd.randrange(w),[p.VAR(w)],'b')
    if q==3:
        w=rnd.randint(1,64); return p.raw(0x49,rnd.randrange(w),[p.VAL(w,rnd.getrandbits(w))],'b')
    if q==4:
        w=rnd.randint(1,8); return p.raw(0x49,rnd.randrange(w),[p.FROMBOOL([p.BVAR() for _ in range(w)])],'b')
    if q==5: return p.raw(0x81,0,[junk(p,d+1)],'b')
    if q in (6,7,8,9): return p.raw(BOOL2[q-6],0,[junk(p,d+1),junk(p,d+1)],'b')
    if q==10: return p.raw(0x29,0,[junk(p,d+1),junk(p,d+1),junk(p,d+1)],'b')
    if q==11: return p.raw(rnd.choice([0x01,0x41,0x39]),0,[junk(p,d+1) for _ in range(3)],'b')
    if q==12:
        w=rnd.randint(1,4); return p.raw(rnd.choice([0xa1,0xb1,0xc1,0xd1,0x11]),0,[p.VAR(w),p.VAL(w,rnd.getrandbits(w))],'b')
    return p.raw(0x91,0,[junk(p,d+1),junk(p,d+1)],'b')

TERMS=['var','val','ite','not','neg','add','sub','and','or','xor','concat','extract','sext','shl','lshr','ashr',
       'mul','zext','frombool']
ATOMS=['eq','ult','ule','slt','sle','ugt','booleq']
BIN={'sub':0x10,'shl':0x60,'lshr':0x70,'ashr':0xc0}
NARY={'add':0x00,'and':0x50,'or':0x40,'xor':0xa0,'mul':0x20}
BOP={'and':0x01,'or':0x41,'xor':0x39}
ACODE={'eq':0x11,'ult':0xa1,'ule':0xb1,'slt':0xc1,'sle':0xd1,'ugt':0x21}

def pick_w(kind):
    r=rnd.random()
    if kind=='val': return rnd.choice([1,2,3,7,8,31,32,33,63,64]) if r<0.5 else rnd.randint(1,64)
    if r<0.75: return rnd.randint(1,9)
    if r<0.93: return rnd.randint(10,40)
    return rnd.choice([64,65,128,129,200,255])

def circuit(p, kind, xss):
    """claimed bits (term) for the circuit kind over operand bit lists."""
    if kind=='not': return [p.NOT(b) for b in xss[0]]
    if kind=='neg':
        pre=[p.NOT(b) for b in xss[0]]
        return ripple(p, pre, [p.F()]*len(pre), True)
    if kind in ('add','mul'):
        acc=xss[0]
        for x in xss[1:]: acc=ripple(p, acc, x, False)
        return acc
    if kind=='sub': return ripple(p, xss[0], [p.NOT(b) for b in xss[1]], True)
    if kind in BOP: return [chain(p, BOP[kind], [xs[i] for xs in xss]) for i in range(len(xss[0]))]
    if kind in ('shl','lshr','ashr'): return shift_circuit(p, kind, xss[0], xss[1])
    raise Exception(kind)

def build(kind, ckind, mut):
    p=Pool(mut_at=mut)
    w=pick_w(kind)
    if kind in ATOMS:
        if kind=='booleq':
            x=p.BVAR(); y=p.BVAR(); a=p.raw(0x11,0,[x,y],'b'); p.frozen=False
            b=p.CONJ(p.EQ(x,y),p.EQ(x,y)); return p,a,b
        xs=operand(p,w); ys=operand(p,w)
        a=p.raw(ACODE[kind],0,[p.FROMBOOL(xs),p.FROMBOOL(ys)],'b')
        p.frozen=False
        l=list(reversed(xs)); r=list(reversed(ys))
        if ckind=='eq':
            if w==1: b=p.EQ(xs[0],ys[0])
            else: b=p.CONJ(*[p.EQ(x,y) for x,y in zip(xs,ys)])
        elif ckind in ('ult','ugt'): b=ult(p,l,r)
        elif ckind=='ule': b=ult(p,l,r,True)
        elif ckind in ('slt','sle'):
            if w==1: b=ult(p,l,r,ckind=='sle')
            else: b=slt(p,l,r,ckind=='sle')
        if mut==-2: b=junk(p); p.mutated=('junk',0)
        return p,a,b
    if kind=='var':
        a=p.VAR(w); p.frozen=False
        bs=[p.BITOF(i,a) for i in range(w)]
    elif kind=='val':
        v=rnd.getrandbits(w); a=p.VAL(w,v); p.frozen=False
        bs=[p.T() if (v>>i)&1 else p.F() for i in range(w)]
    elif kind=='ite':
        c=p.BVAR(); ts=operand(p,w); es=operand(p,w)
        a=p.raw(0x28,w,[c,p.FROMBOOL(ts),p.FROMBOOL(es)],w); p.frozen=False
        bs=[p.CONJ(p.DISJ(p.NOT(c), ts[i]), p.DISJ(c, es[i])) for i in range(w)]
    elif kind=='concat':
        n=rnd.randint(2,5); ws=[rnd.randint(1,max(1,min(w,51))) for _ in range(n)]
        xss=[operand(p,x) for x in ws]
        a=p.raw(0x98,sum(ws),[p.FROMBOOL(x) for x in xss],sum(ws)); p.frozen=False
        bs=[b for xs in reversed(xss) for b in xs]
    elif kind=='extract':
        xs=operand(p,w); lo=rnd.randrange(w); hi=rnd.randint(lo,w-1)
        a=p.raw(0x38,lo|(hi<<8),[p.FROMBOOL(xs)],hi-lo+1); p.frozen=False
        bs=xs[lo:hi+1]
    elif kind in ('sext','zext'):
        xs=operand(p,w); e=rnd.randint(0,min(20,255-w))
        a=p.raw(0x48 if kind=='sext' else 0x58,(w+e)|(e<<8),[p.FROMBOOL(xs)],w+e); p.frozen=False
        bs=xs+[xs[-1] if kind=='sext' else p.F()]*e
    elif kind=='frombool':
        xs=operand(p,w); a=p.FROMBOOL(xs); p.frozen=False; bs=list(xs)
    else:
        if kind in NARY: n=rnd.choice([2,2,2,3,3,4,6])
        elif kind in BIN: n=2
        else: n=1
        if kind in NARY and w>40: w=rnd.randint(1,40)
        xss=[operand(p,w) for _ in range(n)]
        code={**BIN,**NARY,'not':0x78,'neg':0x80}[kind]
        a=p.raw(code,w,[p.FROMBOOL(x) for x in xss],w); p.frozen=False
        ck=ckind
        need={'sub':2,'shl':2,'lshr':2,'ashr':2}
        if ck in need and need[ck]>len(xss): ck=kind
        if ck=='mul': ck='add'
        bs=circuit(p, ck, xss)
    # list-level mutation of the claimed bits
    if mut==-1 and len(bs)>=2:
        i,j=rnd.sample(range(len(bs)),2)
        if rnd.random()<0.5: bs[i],bs[j]=bs[j],bs[i]
        else: bs[i]=bs[j]
        p.mutated=('bits',0)
    if mut==-2:
        if rnd.random()<0.5: bs=[junk(p) for _ in bs]
        else:
            for i in range(len(bs)):
                if rnd.random()<0.3: bs[i]=junk(p)
        p.mutated=('junk',0)
    b=p.FROMBOOL(bs)
    return p,a,b

def proof(pool, E):
    G = pool.raw(0x81,0,[E],'b')
    steps=[(1,[],[G]), (0x4001,[],[E]), (0x2008,[1,0],[])]
    def sb(rule,prems,params):
        hdr=(rule&0xffff)|((len(prems)&0xff)<<16)|((len(params)&0xff)<<24)
        return struct.pack('<I',hdr)+b''.join(struct.pack('<I',w&0xffffffff) for w in prems+params)
    step_sec=b''.join(sb(*s) for s in steps)
    expr_sec=pool.words()
    return struct.pack('<III',0x0BCF,len(expr_sec)//4,len(step_sec)//4)+expr_sec+step_sec

SWAP={'shl':['lshr','ashr'],'lshr':['shl','ashr'],'ashr':['lshr','shl'],'add':['sub','or','xor'],'sub':['add'],
      'and':['or','xor'],'or':['and','xor'],'xor':['or','add'],'not':['neg'],'neg':['not'],
      'eq':['ult'],'ult':['ule','slt','eq'],'ule':['ult','sle'],'slt':['sle','ult'],'sle':['slt','ule']}
man=open(os.path.join(OUT,'MANIFEST'),'w')
n=0
while n<COUNT:
    kind=rnd.choice(TERMS+ATOMS+['shl','lshr','ashr','sub','and','ule','sle','add','neg'])
    mode=rnd.random()
    ckind=kind; mut=None
    if JUNK: mut=-2
    elif mode<0.35: pass
    elif mode<0.45 and kind in SWAP: ckind=rnd.choice(SWAP[kind])
    elif mode<0.55: mut=-1
    else:
        # count the mutable calls first with the same random stream
        state=rnd.getstate(); p,_,_=build(kind,ckind,None); rnd.setstate(state)
        if p.calls==0: continue
        mut=rnd.randint(1,p.calls)
    p,a,b=build(kind,ckind,mut)
    if p.ty[a]!=p.ty[b]: continue
    E=p.raw(0x11,0,[a,b],'b')
    name='t%05d_%s%s.bcf'%(n,kind,'' if (ckind==kind and mut is None) else '_M')
    open(os.path.join(OUT,name),'wb').write(proof(p,E))
    man.write('%s %s %s %s %s\n'%(name,kind,ckind,mut,p.mutated))
    n+=1
print('wrote',n)
