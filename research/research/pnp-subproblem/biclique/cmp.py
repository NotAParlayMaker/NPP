import csv
bc={}
for l in open('sweep.out'):
    p=l.split(' ',8)
    if len(p)>=8 and p[1].isdigit(): bc[p[0]]=(int(p[1]),int(p[2]),(int(p[3]) if p[3]!="inf" else 0),int(p[4]),int(p[5]),int(p[6]),int(p[7]),p[8].strip())
tot=eq=0;diff=[]
for r in csv.DictReader(open('../sat-girth34/results.csv')):
    g=r['graph6']
    if g not in bc or r['status']!='EXACT': continue
    tot+=1; s=int(r['s']); b=bc[g][6]
    if s==b: eq+=1
    else: diff.append((g,bc[g][0],bc[g][1],bc[g][2],'P',bc[g][4],'s',s,'bc',b,r['circuit']))
print(tot,eq)
for d in diff: print(*d)
