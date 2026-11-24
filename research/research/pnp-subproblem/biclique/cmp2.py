import csv,collections
ns={};sh={}
for l in open('sweep.out'):
    p=l.split(' ',8)
    if len(p)>=8 and p[1].isdigit(): ns[p[0]]=dict(n=int(p[1]),m=int(p[2]),girth=p[3],tau=int(p[4]),P=int(p[5]),star=int(p[6]),bc=int(p[7]),cover=p[8].strip())
for l in open('sweep2.out'):
    p=l.split()
    if len(p)==3: sh[p[0]]=int(p[1])
print(len(ns),len(sh))
# structural checks
print('star==P all:',all(d['star']==d['P'] for d in ns.values()))
print('bcs<=bc all:',all(sh[g]<=ns[g]['bc'] for g in sh if g in ns))
c=collections.Counter()
for g in sh:
    if g in ns: c[(ns[g]['bc']<ns[g]['P'], sh[g]<ns[g]['bc'])]+=1
print(c)
tot=eq=eqns=0
for r in csv.DictReader(open('../sat-girth34/results.csv')):
    if r['status']!='EXACT' or r['graph6'] not in sh: continue
    tot+=1; s=int(r['s']); eq+=(s==sh[r['graph6']]); eqns+=(s==ns[r['graph6']]['bc'])
    if s!=sh[r['graph6']]: print('MISMATCH',r['graph6'],s,sh[r['graph6']],r['circuit'])
print('csv exact',tot,'eq bcs',eq,'eq bc',eqns)
