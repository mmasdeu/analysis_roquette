import re, glob, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from items import ITEMS
LEAN=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','AnalyticTheory')+'/'
labels={i['label'] for i in ITEMS}
bad=[]
for it in ITEMS:
    for u in it['uses']:
        if u not in labels: bad.append(('uses',it['label'],u))
labels_dup=[l for l in labels if sum(1 for i in ITEMS if i['label']==l)>1]
# check lean names exist
src=''.join(open(f,encoding='utf8').read() for f in glob.glob(LEAN+'*.lean'))
names=set(re.findall(r'(?:theorem|lemma|def|abbrev|opaque|instance|structure|class|noncomputable def|noncomputable opaque|noncomputable abbrev|noncomputable instance|noncomputable def)\s+([A-Za-z_][A-Za-z0-9_\']*)',src))
names|=set(re.findall(r'(?:structure|class)\s+([A-Za-z_][A-Za-z0-9_\']*)',src))
names|={x.split('.')[-1] for x in re.findall(r"(?:theorem|lemma|def|abbrev|instance|structure)\s+([A-Za-z_][A-Za-z0-9_'.]*)",src)}
missing=[]
for it in ITEMS:
    for n in it['lean']:
        if n.split('.')[-1] not in names: missing.append((it['label'],n))
print('bad uses:',bad); print('dup labels:',labels_dup); print('missing lean:',missing)
