import struct, sys, random, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
class P:
    def __init__(s): s.e=[]; s.s=[]; s.nf=0
    def node(s, code, args=(), params=0):
        pos=len(s.e); s.e.append(code | len(args)<<8 | params<<16); s.e += list(args); return pos
    def bvval(s, w, v):
        pos=len(s.e); nw=(w+31)//32; s.e.append(0x08 | nw<<8 | w<<16); s.e.append(v & 0xffffffff)
        if nw==2: s.e.append(v>>32)
        return pos
    def step(s, rule, prems=(), params=()):
        s.s.append(rule | len(prems)<<16 | len(params)<<24); s.s += [x & 0xffffffff for x in prems]; s.s += [x & 0xffffffff for x in params]
        s.nf += 1; return s.nf-1
    def write(s, path):
        w=[0x0BCF, len(s.e), len(s.s)] + s.e + s.s
        open(path,'wb').write(struct.pack('<%dI'%len(w), *w))
BVAR=0x19; NOT=0x81; OR=0x41; AND=0x01; EQ=0x11; BVAL=0x09
ASSUME=1; ACI=4; ABSORB=5; RES=0x2001; FAC=0x2002; REO=0x2003; ANDEL=0x2009

def clause_case(rng, path):
    p=P()
    nv=rng.randint(2,5)
    vs=[p.node(BVAR) for _ in range(nv)]
    nots=[p.node(NOT,[v]) for v in vs]
    lits=vs+nots
    D=p.node(OR,[vs[0],vs[1]]); nD=p.node(NOT,[D]); nn=p.node(NOT,[nots[0]])
    D2=p.node(OR,[nots[0],vs[1],vs[0]])
    lits += [D,nD,nn,D2]
    unused=p.node(NOT,[D2]) if rng.random()<0.5 else None   # may make find_not succeed for D2
    k=rng.randint(2,6)
    cl=[]; clits=[]
    for _ in range(k):
        r=rng.random()
        if r<0.15:
            l=rng.choice(lits); cl.append(l); clits.append([l])
        else:
            n=rng.randint(2,6) if r<0.9 else rng.randint(100,255)
            small=rng.sample(lits, rng.randint(1,min(len(lits),4))) if rng.random()<0.6 else lits
            ls=[rng.choice(small) for _ in range(n)]
            cl.append(p.node(OR,ls)); clits.append(ls)
    G=p.node(AND,cl)
    f0=p.step(ASSUME,[],[G])
    fs=[p.step(ANDEL,[f0],[i]) for i in range(k)]
    kind=rng.choice(['res','res','fac','fac','reo'])
    nsteps=rng.randint(1,3)
    for _ in range(nsteps):
        kind=rng.choice(['res','res','fac','fac','reo'])
        allf=list(range(1,p.nf))
        if kind=='res':
            m=rng.randint(1,4)
            prem=[rng.choice(allf) for _ in range(m+1)]
            if rng.random()<0.03: prem=prem[:1]
            pw=(m+31)//32
            pols=[rng.getrandbits(32) if rng.random()<0.7 else rng.getrandbits(m)]
            piv=[]
            for i in range(m):
                r=rng.random()
                if r<0.75:
                    # a literal from the next premise, possibly its complement var
                    src=rng.choice(lits)
                    piv.append(src)
                elif r<0.9: piv.append(rng.choice(cl))
                elif r<0.95: piv.append(rng.randrange(len(p.e)+3))
                else: piv.append(rng.getrandbits(32))
            params=pols+piv
            r=rng.random()
            if r<0.03: params=params[:-1]
            elif r<0.06: params=params+[rng.choice(lits)]
            p.step(RES,prem,params)
        elif kind=='fac':
            i=rng.randrange(k); f=fs[i] if rng.random()<0.9 else rng.choice(allf); ls=clits[i]
            # true duplicate structure
            first={}; groups={}
            for j,l in enumerate(ls):
                if l in first: groups.setdefault(first[l],[]).append(j)
                else: first[l]=j
            by=[]
            us=sorted(groups)
            if rng.random()<0.15: rng.shuffle(us)
            for uq in us:
                ds=groups[uq]
                if rng.random()<0.3: ds=rng.sample(ds, rng.randint(1,len(ds)))
                if rng.random()<0.1: ds=ds+[rng.choice(ds)]
                if rng.random()<0.2 and len(ds)>1:
                    # chain: use a dup as later uniq
                    by += [2, uq, ds[0]]
                    by += [len(ds), ds[0]] + ds[1:]
                else:
                    by += [1+len(ds), uq] + ds
                if len(by) > 900: break
            r=rng.random()
            if r<0.1 and by: by[rng.randrange(len(by))]=rng.randrange(256)
            elif r<0.15 and by: by[rng.randrange(len(by))]^=1<<rng.randrange(8)
            elif r<0.2: by += [0, rng.randrange(256)]
            elif r<0.25: by += [0,0,0,0,0]
            elif r<0.3: by = by[:-1]
            elif r<0.33: by = [rng.randrange(4) for _ in range(rng.randint(0,8))]
            by=by[:1020]
            while len(by)%4: by.append(0 if rng.random()<0.95 else 1)
            params=[by[q]|by[q+1]<<8|by[q+2]<<16|by[q+3]<<24 for q in range(0,len(by),4)]
            p.step(FAC,[f],params)
        else:
            i=rng.randrange(k); f=fs[i] if rng.random()<0.9 else rng.choice(allf); n=len(clits[i])
            r=rng.random()
            cnt=rng.randint(0,min(n,8)) if r<0.8 else (rng.randint(0,min(n+2,255)))
            hs=[cnt]
            for _ in range(cnt):
                j=rng.randrange(n); kk=rng.randrange(n)
                if rng.random()<0.05: j=rng.randrange(256)
                if rng.random()<0.05: kk=rng.randrange(256)
                hs.append(j|kk<<8)
            if len(hs)%2: hs.append(0 if rng.random()<0.9 else rng.randrange(1,65536))
            r=rng.random()
            if r<0.04: hs += [0,0]
            elif r<0.08: hs=hs[:-2]
            elif r<0.1: hs=[]
            elif r<0.13 and hs: hs[rng.randrange(len(hs))]=rng.getrandbits(16)
            params=[hs[q]|hs[q+1]<<16 for q in range(0,len(hs),2)]
            prem=[f] if rng.random()<0.97 else [f,f]
            p.step(REO,prem,params)
    p.write(path)

def aci_case(rng, path):
    p=P()
    g=p.node(BVAR)
    fam=rng.choice(['conj','disj','and','or','xor','concat'])
    tt=p.node(BVAL,[],1); ff=p.node(BVAL,[],0)
    memo={}
    def mk(code,args,params=0):
        key=(code,tuple(args),params)
        if key not in memo: memo[key]=p.node(code,args,params)
        return memo[key]
    if fam in('conj','disj'):
        code=AND if fam=='conj' else OR; other=OR if fam=='conj' else AND
        leaves=[p.node(BVAR) for _ in range(rng.randint(1,4))]
        leaves.append(p.node(NOT,[leaves[0]]))
        special=[tt,ff]
        def op(args): return mk(code,args)
        def oth(args): return mk(other,args)
        zero = tt if fam=='disj' else ff
    elif fam=='concat':
        leaves=[(p.node(0x18,[],w),w) for w in [rng.choice([1,2,3,8]) for _ in range(rng.randint(1,4))]]
    else:
        w=rng.choice([1,8,32,33,40,64])
        code={'and':0x50,'or':0x40,'xor':0xa0}[fam]; other={'and':0x40,'or':0x50,'xor':0x50}[fam]
        leaves=[p.node(0x18,[],w) for _ in range(rng.randint(1,4))]
        leaves.append(p.node(0x78,[leaves[0]],w))
        z=p.bvval(w,0); o=p.bvval(w,(1<<w)-1); q=p.bvval(w,1) if w>1 else z
        special=[z,o,q]
        w2 = 8 if w!=8 else 16
        def op(args): return mk(code,args,w)
        def oth(args): return mk(other,args,w)
        zero = z if fam=='and' else o
    if fam=='concat':
        def tree(depth):
            if depth==0 or rng.random()<0.3: return rng.choice(leaves)
            n=rng.randint(2,3); ch=[tree(depth-1) for _ in range(n)]
            wsum=sum(c[1] for c in ch)
            if wsum>64: return ch[0]
            return (mk(0x98,[c[0] for c in ch],wsum), wsum)
        def flat(t):
            return t
        a=tree(rng.randint(1,4))
        # rhs: regroup the same leaves
        def leaves_of(pos):
            hdr=p.e[pos]
            if hdr&0xff==0x98:
                r=[]
                for i in range((hdr>>8)&0xff): r+=leaves_of(p.e[pos+1+i])
                return r
            return [(pos,(hdr>>16)&0xff)]
        ls=leaves_of(a[0])
        r=rng.random()
        if r<0.15 and len(ls)>1: i=rng.randrange(len(ls)-1); ls[i],ls[i+1]=ls[i+1],ls[i]
        elif r<0.25: ls=ls[:-1]
        def regroup(ls):
            if len(ls)==1: return ls[0]
            if len(ls)==2 or rng.random()<0.3:
                parts=ls
            else:
                c=rng.randint(1,len(ls)-1); parts=[regroup(ls[:c]),regroup(ls[c:])]
            return (mk(0x98,[c[0] for c in parts],sum(c[1] for c in parts)), sum(c[1] for c in parts))
        b=regroup(ls) if ls else a
        if a[1]!=b[1]:
            b=a
        ea=a[0]; eb=b[0]
        cands=[(ea,eb),(eb,ea)]
    else:
        def tree(depth):
            r=rng.random()
            if depth==0 or r<0.25: return rng.choice(leaves)
            if r<0.4: return rng.choice(special)
            if r<0.47: return oth([tree(depth-1) for _ in range(2)])
            return op([tree(depth-1) for _ in range(rng.randint(2,4))])
        a=tree(rng.randint(1,5))
        def leaves_of(pos):
            hdr=p.e[pos]
            if (hdr&0xff)==code and pos not in special and (fam in('conj','disj') or ((hdr>>16)&0xff)==w):
                r=[]
                for i in range((hdr>>8)&0xff): r+=leaves_of(p.e[pos+1+i])
                return r
            return [pos]
        ls=leaves_of(a)
        r=rng.random()
        if r<0.7:
            rng.shuffle(ls)
            if rng.random()<0.5: ls=list(dict.fromkeys(ls))
            if rng.random()<0.5: ls=[l for l in ls if l not in special] or ls
            if rng.random()<0.07 and ls: ls.append(rng.choice(ls))
            if rng.random()<0.07 and len(ls)>1: ls.pop()
            if rng.random()<0.07: ls.append(rng.choice(leaves+special))
            def regroup(ls):
                if len(ls)==1: return ls[0]
                if len(ls)<=3 and rng.random()<0.6: return op(ls)
                c=rng.randint(1,len(ls)-1); return op([regroup(ls[:c]),regroup(ls[c:])])
            b=regroup(ls) if ls else rng.choice(special)
        elif r<0.8: b=rng.choice(special)
        elif r<0.9: b=rng.choice(leaves)
        else: b=tree(rng.randint(0,3))
        cands=[(a,b),(b,a)]
    es=[p.node(EQ,[l,r]) for (l,r) in cands]
    if fam!='concat':
        def ztree(depth):
            # a tree that contains the absorbing element somewhere, usually under the same operator
            if depth==0: return zero
            ch=[tree(rng.randint(0,2)) for _ in range(rng.randint(1,3))]
            inner=ztree(depth-1)
            if rng.random()<0.12: inner=oth([inner, tree(1)])
            ch.insert(rng.randrange(len(ch)+1), inner)
            return op(ch)
        az=ztree(rng.randint(1,4)) if rng.random()<0.7 else a
        zs=[p.node(EQ,[az,zero]), p.node(EQ,[az,zero]), p.node(EQ,[zero,az]), p.node(EQ,[az,rng.choice(special)])]
    else:
        zs=es
    p.step(ASSUME,[],[g])
    r=rng.random()
    if r<0.45: rule,e=ACI,rng.choice(es)
    elif r<0.8: rule,e=ABSORB,rng.choice(zs)
    elif r<0.9: rule,e=ACI,rng.choice(zs)
    elif r<0.97: rule,e=ABSORB,rng.choice(es)
    else: rule,e=rng.choice([ACI,ABSORB]),rng.choice([g,rng.randrange(len(p.e)+2)])
    params=[e]
    if rng.random()<0.02: params=[e,e]
    if rng.random()<0.01: params=[]
    p.step(rule,[0] if rng.random()<0.01 else [],params)
    p.write(path)

if __name__=='__main__':
    kind=sys.argv[1]; seed0=int(sys.argv[2]); n=int(sys.argv[3]); out=sys.argv[4]
    for i in range(n):
        rng=random.Random(seed0+i)
        (clause_case if kind=='clause' else aci_case)(rng, f"{out}/{kind}_{seed0+i}.bcf")
