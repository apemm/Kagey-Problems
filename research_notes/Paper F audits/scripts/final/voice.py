import re,sys,os
d=sys.argv[1]
files=['problem131_levy.tex','sec_intro.tex','sec_setting.tex','sec_bulk.tex','sec_bigjump.tex','sec_preparation.tex','sec_shape.tex','sec_inverse.tex','sec_verify.tex']
BS=chr(92)
for f in files:
    txt=open(os.path.join(d,f),encoding='utf8').read()
    if f=='problem131_levy.tex':
        txt=txt.split(BS+'begin{thebibliography}')[0]
    lines=txt.split('\n')
    clean=[]
    for l in lines:
        out='';j=0
        while j<len(l):
            if l[j]==BS and j+1<len(l): out+=l[j:j+2]; j+=2; continue
            if l[j]=='%': break
            out+=l[j]; j+=1
        clean.append(out)
    s='\n'.join(clean)
    def blank(m): return re.sub(r'[^\n]',' ',m.group(0))
    pats=[r'\\\[.*?\\\]',r'\\begin\{(equation|align|gather|split|multline)\*?\}.*?\\end\{\1\*?\}',r'\$\$.*?\$\$',r'\$[^$]*\$',
          r'\\label\{[^}]*\}',r'\\ref\{[^}]*\}',r'\\eqref\{[^}]*\}',r'\\cite(\[[^\]]*\])?\{[^}]*\}',r'\\url\{[^}]*\}',
          r'\\nolinkurl\{[^}]*\}',r'\\texttt\{[^}]*\}',r'\\(begin|end)\{[^}]*\}(\[[^\]]*\])?(\{[^}]*\})?',r'\\item\[[^\]]*\]',
          r'\\BEMAIL\{[^}]*\}',r'\\(AMSSUBJ|AMSSUBJSECONDARY|KEYWORDS)\{[^}]*\}']
    for pat in pats:
        s=re.sub(pat,blank,s,flags=re.S)
    for i,l in enumerate(s.split('\n'),1):
        for ch,name in [(';','SEMI'),(':','COLON'),('---','EMDASH')]:
            if ch in l: print(f,i,name,'|',lines[i-1].strip()[:160])
        if re.search(r'\bclearly\b|\bobviously\b|\bevidently\b',l,re.I): print(f,i,'WORD','|',lines[i-1].strip()[:160])
        if '\u2014' in l or '\u2013' in l: print(f,i,'UNICODE DASH','|',lines[i-1].strip()[:160])
