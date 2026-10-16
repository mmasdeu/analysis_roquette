import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from items import ITEMS

import re, glob
_LEAN=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','AnalyticTheory')+'/'
def _sorry_status():
    """name (last component) -> True if its declaration contains `sorry`."""
    status={}
    pat=re.compile(r"^(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)",re.M)
    for f in glob.glob(_LEAN+'*.lean'):
        src=open(f,encoding='utf8').read()
        src=re.sub(r'/-.*?-/','',src,flags=re.S)
        src=re.sub(r'--[^\n]*','',src)
        ms=list(pat.finditer(src))
        for i,m in enumerate(ms):
            end=ms[i+1].start() if i+1<len(ms) else len(src)
            body=src[m.start():end]
            name=m.group(2).split('.')[-1]
            status[name]=status.get(name,False) or bool(re.search(r'\bsorry\b',body))
    return status
_SORRY=_sorry_status()
def _proved(names):
    return bool(names) and all(not _SORRY.get(n.split('.')[-1],True) for n in names)
CHAPTERS=[
 ('Introduction and terminology', lambda l: l.startswith(('def:local','def:function','def:genus','def:conservative','def:elliptic','def:degree-one','def:constant','def:splitting','def:prime-div','def:divisor-ff','def:rr','def:principal-divisor-ff','def:aut-action'))),
 ('Fields of periodic functions (\\S 2)', lambda l: l.startswith(('def:omega','def:convolution','lem:ext','def:convergent','def:holomorphic','def:H-K','lem:H-K','def:M-K','def:const','def:analytic','def:translation','def:Fq','def:divisor','def:Dq','def:mod','def:conj','def:deg-q','def:Phi','def:theta','prop:theta','prop:abel','cor:periodic','prop:deg-q','thm:fq','lem:binomial','lem:gauss','lem:unit-conv','prop:laurent-co','cor:hol-units','prop:taylor','lem:identity','prop:finite-order','lem:weierstrass-prep','prop:tie','prop:zeros','prop:rational','prop:divisor','def:principal','def:D0q','def:C0q','thm:abel','def:translation-class','cor:translation','rem:S2'))),
 ('The Weierstra\\ss\\ function and the absolute invariant (\\S 3)', lambda l: l.startswith(('def:D-','def:theta-M','def:zeta','def:wp','def:s-k','def:coeff','thm:VI','def:reflection','rem:normal','def:Delta','def:jq','lem:1','thm:VII','rem:delta','thm:VIII'))),
 ('Semi-periodic functions (\\S\\S 4--5)', lambda l: l.startswith(('def:galois','def:characters','def:K-chi','def:q-trivial','def:H1','lem:2','def:char-inv','thm:IX','thm:X','def:semi','def:tau','def:FKQ','thm:XI','thm:XII','thm:XIII','thm:XIV','cor:XIII','thm:XV','cor:XVa','thm:XVI','tab:','cor:XVI'))),
 ('Elliptic subfields and isogenies (\\S 6)', lambda l: l.startswith(('def:commensurable','def:rel','def:Fq-qbar','def:elliptic-sub','lem:XVII','thm:XVII','thm:XVIII','def:isogeny','cor:XVIII','def:complex','prop:abs','thm:XIX','cor:XIX'))),
 ('Appendix \\S A1: fields with a prime divisor of degree 1', lambda l: l.startswith(('def:square','def:pi','def:normal','def:weierstrass','def:absolute-invariant','def:hasse-invariant','prop:absinv','prop:hasse','lem:A','rem:A','thm:A-'))),
 ('Appendix \\S A2: arbitrary elliptic fields', lambda l: l.startswith(('def:splits','def:absolute-invariant-gen','def:hasse-general','thm:A2','def:jacobian','def:char-cocycle','def:translation-group','def:H1-GT','prop:A2'))),
]
def esc(s): return s
out=[]
out.append('% Generated from the list of items (see scratchpad generator). Each node records the Lean\n% declaration(s) formalizing it. \\notready marks placeholders (opaque objects or True-statements).\n')
assigned=set()
for title,pred in CHAPTERS:
    out.append('\\section{%s}\n' % title)
    for it in ITEMS:
        if it['label'] in assigned: continue
        if not pred(it['label']): continue
        assigned.add(it['label'])
        env=it['env']
        out.append('\\begin{%s}[%s]' % (env, it['title']))
        out.append('\\label{%s}' % it['label'])
        if it['lean']:
            out.append('\\lean{%s}' % ', '.join('AnalyticTheory.'+n for n in it['lean']))
        if it['uses']:
            out.append('\\uses{%s}' % ', '.join(it['uses']))
        if it['notready']:
            out.append('\\notready')
        elif it['lean']:
            out.append('\\leanok')
        out.append(it['text'])
        out.append('\\end{%s}' % env)
        if env != 'definition' and it['lean']:
            out.append('\\begin{proof}')
            if _proved(it['lean']):
                out.append('\\leanok')
            out.append('See the Lean proof of \\texttt{%s}.' % ', '.join(n.split('.')[-1].replace('_','\\_') for n in it['lean']))
            out.append('\\end{proof}')
        out.append('')
missing=[i['label'] for i in ITEMS if i['label'] not in assigned]
if missing: print('UNASSIGNED', missing)
open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','src','content.tex'),'w',encoding='utf8').write('\n'.join(out))
print('wrote', len(assigned), 'items')
