import struct, random, sys, os

BV_ADD=0x00; BV_VAL=0x08; BV_SUB=0x10; BV_VAR=0x18; BV_MUL=0x20; BV_AND=0x50; BV_NOT=0x78; BV_NEG=0x80
BOOL_EQ=0x11
ASSUME=1; POLY_NORM=0x4002; POLY_NORM_EQ=0x4003

class B:
    def __init__(self):
        self.exprs=[]; self.pos=0; self.memo={}
    def add(self, code, params, words, share=True):
        key=(code,params,tuple(words))
        if share and code!=BV_VAR and key in self.memo: return self.memo[key]
        r=self.pos; self.exprs.append((code,params,list(words))); self.pos+=1+len(words)
        self.memo[key]=r; return r
    def var(self,w): return self.add(BV_VAR,w,[],share=False)
    def lit(self,w,v):
        v&=(1<<w)-1
        return self.add(BV_VAL,w,[v&0xffffffff] if w<=32 else [v&0xffffffff, v>>32])
    def write(self, path, steps):
        def nb(code, params, words):
            hdr=(code&0xff)|((len(words)&0xff)<<8)|((params&0xffff)<<16)
            return struct.pack('<I',hdr)+b''.join(struct.pack('<I',x&0xffffffff) for x in words)
        es=b''.join(nb(*e) for e in self.exprs)
        def sb(rule,prems,params):
            hdr=(rule&0xffff)|((len(prems)&0xff)<<16)|((len(params)&0xff)<<24)
            return struct.pack('<I',hdr)+b''.join(struct.pack('<I',x&0xffffffff) for x in prems+params)
        ss=b''.join(sb(*s) for s in steps)
        open(path,'wb').write(struct.pack('<III',0x0BCF,self.pos,len(ss)//4)+es+ss)

def emit(b,w,vars,e):
    t=e[0]
    if t=='var': return vars[e[1]]
    if t=='lit': return b.lit(w,e[1])
    if t=='add': return b.add(BV_ADD,w,[emit(b,w,vars,x) for x in e[1]])
    if t=='sub': return b.add(BV_SUB,w,[emit(b,w,vars,e[1]),emit(b,w,vars,e[2])])
    if t=='neg': return b.add(BV_NEG,w,[emit(b,w,vars,e[1])])
    if t=='mul': return b.add(BV_MUL,w,[emit(b,w,vars,x) for x in e[1]])
    if t=='and': return b.add(BV_AND,w,[emit(b,w,vars,e[1]),emit(b,w,vars,e[2])])
    if t=='not': return b.add(BV_NOT,w,[emit(b,w,vars,e[1])])
    raise Exception(t)

def rlit(rng,w):
    m=(1<<w)-1
    c=rng.random()
    if c<0.15: return 0
    if c<0.3: return 1
    if c<0.45: return m
    if c<0.6: return 1<<rng.randrange(w)
    if c<0.7: return (1<<(w-1))
    return rng.getrandbits(w)

def gen(rng,w,nv,d):
    c=rng.random()
    if d==0 or c<0.2: return ('var',rng.randrange(nv))
    if c<0.3: return ('lit',rlit(rng,w))
    if c<0.5: return ('add',[gen(rng,w,nv,d-1) for _ in range(rng.randint(2,4))])
    if c<0.62: return ('sub',gen(rng,w,nv,d-1),gen(rng,w,nv,d-1))
    if c<0.7: return ('neg',gen(rng,w,nv,d-1))
    if c<0.8: return ('mul',[('lit',rlit(rng,w)),gen(rng,w,nv,d-1)])
    if c<0.88: return ('mul',[gen(rng,w,nv,d-1),('lit',rlit(rng,w))])
    if c<0.91: return ('mul',[gen(rng,w,nv,d-1),gen(rng,w,nv,d-1)])
    if c<0.94: return ('mul',[('lit',rlit(rng,w)),gen(rng,w,nv,d-1),gen(rng,w,nv,d-1)])
    if c<0.97: return ('and',gen(rng,w,nv,d-1),gen(rng,w,nv,d-1))
    return ('not',gen(rng,w,nv,d-1))

def islit(e): return e[0]=='lit'

def tr(rng,w,e):
    """an expression with the same linear normal form (atoms untouched)"""
    t=e[0]; M=(1<<w)-1
    if t in('var','lit','and','not'): r=e
    elif t=='add':
        xs=[tr(rng,w,x) for x in e[1]]; rng.shuffle(xs)
        if len(xs)>2 and rng.random()<0.5: xs=[('add',xs[:2])]+xs[2:]
        r=('add',xs)
    elif t=='sub':
        a=tr(rng,w,e[1]); b=tr(rng,w,e[2]); c=rng.random()
        if c<0.3: r=('add',[a,('neg',b)])
        elif c<0.5: r=('add',[('mul',[('lit',M),b]),a])
        elif c<0.7: r=('sub',a,b)
        else: r=('neg',('sub',b,a))
    elif t=='neg':
        a=tr(rng,w,e[1]); c=rng.random()
        if c<0.3: r=('mul',[('lit',M),a])
        elif c<0.5: r=('mul',[a,('lit',M)])
        elif c<0.7: r=('sub',('lit',0),a)
        else: r=('neg',a)
    elif t=='mul':
        xs=e[1]
        if len(xs)==2 and islit(xs[0]):
            k=xs[0]; a=tr(rng,w,xs[1])
            if a[0]=='add' and rng.random()<0.6: r=('add',[('mul',[k,x]) for x in a[1]])
            elif rng.random()<0.3 and not islit(a): r=('mul',[a,k])
            else: r=('mul',[k,a])
        elif len(xs)==2 and islit(xs[1]):
            k=xs[1]; a=tr(rng,w,xs[0])
            if rng.random()<0.5: r=('mul',[k,a])
            else: r=('mul',[a,k]) if not islit(a) else ('mul',[k,a])
        else: r=e
    c=rng.random()
    if c<0.08: r=('add',[r,('lit',0)])
    elif c<0.14:
        x=('var',0); r=('sub',('add',[r,x]),x)
    return r

def perturb(rng,w,e):
    return ('add',[e,('lit',rng.choice([1,(1<<w)-1,1<<(w-1)]))]) if rng.random()<0.5 else ('add',[e,('var',0)])

def one(path,seed):
    rng=random.Random(seed)
    w=rng.choice([1,2,2,3,4,8,31,32,33,63,64,64,64])
    nv=rng.randint(1,3)
    b=B(); vars=[b.var(w) for _ in range(nv)]
    mode=rng.random()
    d=rng.randint(1,4)
    l=gen(rng,w,nv,d)
    if mode<0.45: r=tr(rng,w,l)
    elif mode<0.6: r=perturb(rng,w,tr(rng,w,l))
    else: r=gen(rng,w,min(nv,2),rng.randint(0,2)); l=gen(rng,w,min(nv,2),rng.randint(0,2)) if w<=3 else l
    pl=emit(b,w,vars,l); pr=emit(b,w,vars,r)
    e=b.add(BOOL_EQ,0,[pl,pr])
    b.write(path,[(ASSUME,[],[e]),(POLY_NORM,[],[e])])

def one_eq(path,seed):
    rng=random.Random(seed)
    w=rng.choice([1,2,8,32,33,64,64,100])
    b=B(); v=[b.var(w) for _ in range(4)]
    def side(x0,x1):
        c=rng.random()
        if w>64: k=x0  # no literal possible
        else:
            kv=rlit(rng,w)
            if rng.random()<0.6: kv|=1
            if rng.random()<0.2 and w==64: kv=(rng.getrandbits(32)<<32)|rng.choice([0,1])
            k=b.lit(w,kv)
        s=b.add(BV_SUB,w,[x0,x1]) if c<0.85 else b.add(BV_ADD,w,[x0,x1])
        c=rng.random()
        if c<0.8: return b.add(BV_MUL,w,[k,s])
        if c<0.9: return b.add(BV_MUL,w,[s,k])
        if c<0.95: return b.add(BV_MUL,w,[k,s,s])
        return s
    m0=side(v[0],v[1]); m1=side(v[rng.choice([2,0])],v[rng.choice([3,1])])
    e=b.add(BOOL_EQ,0,[m0,m1])
    b.write(path,[(ASSUME,[],[e]),(POLY_NORM_EQ,[0],[])])

def special(dir):
    # w > 64: Lean accepts, C must reject
    for w in (65,128,255):
        b=B(); x=b.var(w); y=b.var(w)
        e=b.add(BOOL_EQ,0,[b.add(BV_ADD,w,[x,y]),b.add(BV_ADD,w,[y,x])])
        b.write(f"{dir}/sp_wide{w}.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e])])
    # depth: chain of n negations
    for n in (62,63,64,65,66,100):
        b=B(); x=b.var(8); t=x
        for _ in range(n): t=b.add(BV_NEG,8,[t])
        rhs = x if n%2==0 else b.add(BV_NEG,8,[x])
        e=b.add(BOOL_EQ,0,[t,rhs])
        b.write(f"{dir}/sp_depth{n}.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e])])
    # zero coefficient by scaling: 16*(16*x) = 0 at w=8 ; 2^32 * (2^32 * x) = 0 at w=64
    for w,k in ((8,16),(64,1<<32),(33,1<<17),(64,1<<63)):
        b=B(); x=b.var(w); kk=b.lit(w,k)
        t=b.add(BV_MUL,w,[kk,b.add(BV_MUL,w,[kk,b.add(BV_ADD,w,[x,b.lit(w,1)])])])
        e=b.add(BOOL_EQ,0,[t,b.lit(w,k*k)])
        b.write(f"{dir}/sp_zero{w}_{k.bit_length()}.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e])])
    # 64-bit high-word coefficients
    b=B(); w=64; x=b.var(w); y=b.var(w)
    k1=b.lit(w,0xdeadbeef12345678); k2=b.lit(w,0x0123456789abcdef)
    l=b.add(BV_ADD,w,[b.add(BV_MUL,w,[k1,x]),b.add(BV_MUL,w,[y,k2]),k1])
    r=b.add(BV_SUB,w,[b.add(BV_ADD,w,[k1,b.add(BV_MUL,w,[k2,y])]),b.add(BV_MUL,w,[b.lit(w,-0xdeadbeef12345678),x])])
    e=b.add(BOOL_EQ,0,[l,r])
    r2=b.add(BV_SUB,w,[b.add(BV_ADD,w,[k1,b.add(BV_MUL,w,[k2,y])]),b.add(BV_MUL,w,[b.lit(w,-0xdeadbeef12345678+(1<<40)),x])])
    e2=b.add(BOOL_EQ,0,[l,r2])
    b.write(f"{dir}/sp_hi64_ok.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e])])
    b.write(f"{dir}/sp_hi64_bad.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e2])])
    # not an equation / boolean equation / wrong arity
    b=B(); x=b.var(8); e=b.add(BOOL_EQ,0,[x,x]); ee=b.add(BOOL_EQ,0,[e,e])
    b.write(f"{dir}/sp_booleq.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[ee])])
    b.write(f"{dir}/sp_noteq.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[x])])
    b.write(f"{dir}/sp_arity.bcf",[(ASSUME,[],[e]),(POLY_NORM,[0],[e])])
    b.write(f"{dir}/sp_arity2.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e,e])])
    b.write(f"{dir}/sp_badpos.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e+1])])
    b.write(f"{dir}/sp_eq_arity.bcf",[(ASSUME,[],[e]),(POLY_NORM_EQ,[0],[e])])
    b.write(f"{dir}/sp_eq_arity2.bcf",[(ASSUME,[],[e]),(POLY_NORM_EQ,[0,0],[])])
    b.write(f"{dir}/sp_eq_noteq.bcf",[(ASSUME,[],[e]),(POLY_NORM_EQ,[0],[])])
    # many-argument add with cancellation
    b=B(); w=64; vs=[b.var(w) for _ in range(40)]
    l=b.add(BV_ADD,w,vs+[b.add(BV_NEG,w,[v]) for v in vs[:39]])
    e=b.add(BOOL_EQ,0,[l,vs[39]])
    b.write(f"{dir}/sp_cancel.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e])])
    # 255-argument add, big scratch stack
    b=B(); w=64; vs=[b.var(w) for _ in range(255)]
    l=b.add(BV_ADD,w,vs); r=b.add(BV_ADD,w,list(reversed(vs)))
    e=b.add(BOOL_EQ,0,[l,r])
    b.write(f"{dir}/sp_big.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e])])

d=sys.argv[1]; n=int(sys.argv[2]); os.makedirs(d,exist_ok=True)
special(d)
off=int(sys.argv[3]) if len(sys.argv)>3 else 0
for i in range(n): one(f"{d}/pn_{i}.bcf",off+i)
for i in range(n//4): one_eq(f"{d}/pe_{i}.bcf",off+100000+i)
# exponential DAG: x_{k+1} = x_k + x_k
for depth in (20,24):
    b=B(); x=b.var(32); t=x
    for _ in range(depth): t=b.add(BV_ADD,32,[t,t])
    e=b.add(BOOL_EQ,0,[t,b.add(BV_MUL,32,[b.lit(32,1<<depth),x])])
    b.write(f"{d}/sp_dag{depth}.bcf",[(ASSUME,[],[e]),(POLY_NORM,[],[e])])
