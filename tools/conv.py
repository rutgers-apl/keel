import re, sys, os
# usage: conv.py <path to BCF's bcf-checker directory>
BCF = sys.argv[1] if len(sys.argv) > 1 else os.environ.get('BCF_CHECKER_DIR', '../bcf-checker')
src = open(os.path.join(BCF, 'bcf_rewrites.h')).read()
enum = open(os.path.join(BCF, 'include/uapi/linux/bcf.h')).read()
names = re.findall(r'FN\((\w+)\)', enum.split('BCF_REWRITES_TABLE(FN)')[1].split('enum bcf_rewrite_id')[0])
ids = {n: i+1 for i, n in enumerate(names)}

def tokenize(s):
    return re.findall(r'\w+|[(),]', s)

def parse(toks, i):
    t = toks[i]; i += 1
    if i < len(toks) and toks[i] == '(':
        i += 1; args = []
        while toks[i] != ')':
            a, i = parse(toks, i); args.append(a)
            if toks[i] == ',': i += 1
        i += 1
        return (t, args), i
    return (t, []), i

TY = {'Q': '.any', 'Bool': '.bool', 'Int': '.bv 32', 'BVQ': '.bvq', 'Bools': '.bools', 'BVQs': '.bvqs'}
BIN = {'eq': "eq'", 'neq': "neq'", 'implies': "implies'", 'bvult': "ult'", 'bvule': "ule'", 'bvugt': "ugt'",
       'bvuge': "uge'", 'bvslt': "slt'", 'bvsle': "sle'", 'bvsgt': "sgt'", 'bvsge': "sge'", 'bvsub': "bvsub'",
       'bvshl': "bvshl'", 'bvlshr': "bvlshr'", 'bvashr': "bvashr'"}
UN = {'not': "not'", 'bvneg': "bvneg'", 'bvnot': "bvnot'", 'bvsize': "bvsize'"}
VAR = {'conj': "conj'", 'disj': "disj'", 'xor': "xor'", 'bvadd': "bvadd'", 'bvmul': "bvmul'", 'bvor': "bvor'",
       'bvand': "bvand'", 'bvxor': "bvxor'", 'concat': "concat'"}

def lean(e):
    h, a = e
    if h == 'V': return f"var {a[0][0]}"
    if h == '_TRUE': return 'tt'
    if h == '_FALSE': return 'ff'
    if h == 'bv_val':
        assert a[0][0] == '32'
        v = int(a[1][0], 0)
        return 'l0' if v == 0 else 'l1' if v == 1 else f'lit {v}'
    if h == 'bv_sym_val': return f"symVal ({lean(a[0])}) ({lean(a[1])})"
    if h == 'bvmax': return f"bvmax ({lean(a[0])})"
    if h in ('ite', 'bvite'): return f"ite ({lean(a[0])}) ({lean(a[1])}) ({lean(a[2])})"
    if h == 'extract': return f"extract ({lean(a[0])}) ({lean(a[1])}) ({lean(a[2])})"
    if h == 'zero_extend': return f"zext ({lean(a[0])}) ({lean(a[1])})"
    if h == 'sign_extend': return f"sext ({lean(a[0])}) ({lean(a[1])})"
    if h == 'repeat': return f"«repeat» ({lean(a[0])}) ({lean(a[1])})"
    if h in BIN: return f"{BIN[h]} ({lean(a[0])}) ({lean(a[1])})"
    if h in UN: return f"{UN[h]} ({lean(a[0])})"
    if h in VAR: return f"{VAR[h]} [{', '.join(lean(x) for x in a)}]"
    raise Exception(h)

def strip(s):
    # remove outer parens of single-arg wrappers for readability
    return s

out = {}
for m in re.finditer(r'REWRITE(_COND)?\((.*)\);', src):
    cond = m.group(1) is not None
    toks = tokenize(m.group(2))
    name = toks[0]; i = 1
    assert toks[i] == ','; i += 1
    assert toks[i] == '('; i += 1
    tys = []
    while toks[i] != ')':
        if toks[i] == 'BV':
            assert toks[i+1] == '(' and toks[i+3] == ')'
            tys.append(f'.bv {toks[i+2]}'); i += 4
        else:
            tys.append(TY[toks[i]]); i += 1
        if toks[i] == ',': i += 1
    i += 1; assert toks[i] == ','; i += 1
    exprs = []
    while i < len(toks):
        e, i = parse(toks, i); exprs.append(e)
        if i < len(toks) and toks[i] == ',': i += 1
    if cond:
        c, l, r = exprs
        cs = f"some ({lean(c)})"
    else:
        l, r = exprs; cs = 'none'
    out[ids[name]] = (name, f"[{', '.join(tys)}]", cs, lean(l), lean(r))

for k in sorted(out):
    name, tys, cs, l, r = out[k]
    print(f"  | {k} => some ⟨{tys}, {cs},\n      {l},\n      {r}⟩  -- {name}")
