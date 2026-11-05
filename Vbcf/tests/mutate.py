import struct, sys, random, os
MY={0x2001,0x2002,0x2003,0x0004,0x0005}
def load(path):
    b=open(path,'rb').read(); return list(struct.unpack('<%dI'%(len(b)//4), b))
def mutants(path, outdir, n, seed):
    w=load(path); ne, ns = w[1], w[2]
    # expression header positions
    pos=[]; p=0
    while p<ne:
        pos.append(p); p += 1 + ((w[3+p]>>8)&0xff)
    base=3+ne; steps=[]; p=0; k=0
    while p<ns:
        h=w[base+p]; pc=(h>>16)&0xff; ac=h>>24
        steps.append((p,h&0xffff,pc,ac,k)); p+=1+pc+ac; k+=1
    mine=[s for s in steps if s[1] in MY and (s[2]+s[3])>0]
    if not mine: return 0
    name=os.path.basename(path)[:-4]
    rng=random.Random(seed)
    for i in range(n):
        m=list(w)
        (off,rule,pc,ac,k)=rng.choice(mine)
        j=rng.randrange(pc+ac); idx=base+off+1+j
        r=rng.random()
        if j<pc:
            m[idx]=rng.randrange(max(k,1)) if r<0.9 else rng.getrandbits(32)
        elif rule in (4,5) or (rule==0x2001 and j-pc >= ((pc-1)+31)//32):
            m[idx]=rng.choice(pos) if r<0.9 else rng.randrange(ne+2)
        else:
            if r<0.4: m[idx]^=1<<rng.randrange(32)
            elif r<0.6: m[idx]^=rng.randrange(256)<<(8*rng.randrange(4))
            elif r<0.8:
                sh=8*rng.randrange(4); m[idx]=(m[idx]&~(0xff<<sh))|(rng.randrange(8)<<sh)
            else: m[idx]=rng.getrandbits(32)
        open(f"{outdir}/{name}_m{i}.bcf",'wb').write(struct.pack('<%dI'%len(m), *m))
    return n
if __name__=='__main__':
    out=sys.argv[1]; n=int(sys.argv[2])
    for s,path in enumerate(sys.argv[3:]):
        mutants(path,out,n,s)
