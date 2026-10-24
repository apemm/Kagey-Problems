import re,sys,os,collections
d=sys.argv[1]
files=['problem131_levy.tex','sec_intro.tex','sec_setting.tex','sec_bulk.tex','sec_bigjump.tex','sec_preparation.tex','sec_shape.tex','sec_inverse.tex','sec_verify.tex']
labels=collections.defaultdict(list); refs=collections.defaultdict(list); cites=collections.defaultdict(list); bib={}
BS=chr(92)
for f in files:
    for i,l in enumerate(open(os.path.join(d,f),encoding='utf8'),1):
        # strip comments
        out='';j=0
        while j<len(l):
            if l[j]==BS and j+1<len(l): out+=l[j:j+2]; j+=2; continue
            if l[j]=='%': break
            out+=l[j]; j+=1
        s=out
        for m in re.finditer(r'\\label\{([^}]*)\}',s): labels[m.group(1)].append((f,i))
        for m in re.finditer(r'\\(?:eq|c|C|auto|name|page)?ref\*?\{([^}]*)\}',s):
            for k in m.group(1).split(','): refs[k.strip()].append((f,i))
        for m in re.finditer(r'\\cite[pt]?\*?(?:\[[^\]]*\])?\{([^}]*)\}',s):
            for k in m.group(1).split(','): cites[k.strip()].append((f,i))
        for m in re.finditer(r'\\bibitem\{([^}]*)\}',s): bib[m.group(1)]=(f,i)
print("DUP LABELS",{k:v for k,v in labels.items() if len(v)>1})
print("UNDEF REFS",{k:v for k,v in refs.items() if k not in labels})
print("UNREF LABELS")
for k,v in labels.items():
    if k not in refs: print(' ',k,v)
print("UNDEF CITES",{k:v for k,v in cites.items() if k not in bib})
print("UNCITED BIB",[k for k in bib if k not in cites])
print("CITE COUNTS",{k:len(cites[k]) for k in bib})
print("ALL LABELS")
for k,v in labels.items(): print(' ',k,v,'refs:',len(refs.get(k,[])))
