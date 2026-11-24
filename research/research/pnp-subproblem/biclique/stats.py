import csv,collections,networkx as nx
ns={}
for l in open('sweep.out'):
    p=l.split(' ',8)
    if len(p)>=8 and p[1].isdigit(): ns[p[0]]=dict(n=int(p[1]),m=int(p[2]),tau=int(p[4]),P=int(p[5]),bc=int(p[7]))
sh={}
for f in ('sweep2.out','sweep3_6.out','sweep3_7.out'):
    for l in open(f):
        p=l.split()
        if len(p)>=2 and p[1]!='TIMEOUT': sh[p[0]]=int(p[1])
def c4free(g):
    G=nx.from_graph6_bytes(g.encode())
    return not any(len(set(G[u])&set(G[v]))>=2 for u in G for v in G if u<v)
c=collections.Counter(); bad=[]
byn=collections.defaultdict(lambda:[0,0,0,0])
for g,b in sh.items():
    d=ns.get(g); 
    if not d: continue
    free=c4free(g)
    r=byn[d['n']]; r[0]+=1; r[1]+= b<d['P']; r[2]+= free; r[3]+= (free and b==d['P'])
    if free and b!=d['P']: bad.append(g)
    assert b<=d['bc']<=d['P']
print('n: graphs, bcs<P, C4free, C4free&bcs==P'); 
for n in sorted(byn): print(n,byn[n])
print('bad',bad)
print('sharing strictly better than nosharing:',sum(sh[g]<ns[g]['bc'] for g in sh if g in ns))
r=list(csv.DictReader(open('../sat-girth34/results.csv')))
ex=[x for x in r if x['status']=='EXACT' and x['graph6'] in sh]
print('csv rows',len(r),'exact',len(ex),'s==bcs',sum(int(x['s'])==sh[x['graph6']] for x in ex),'s<bcs',[x['graph6'] for x in ex if int(x['s'])<sh[x['graph6']]],'s>bcs',[x['graph6'] for x in ex if int(x['s'])>sh[x['graph6']]])
print('s<P among csv',sum(int(x['s'])<int(x['P']) for x in ex))
print('lowerbounds/timeouts',[(x['graph6'],x['s'],x['status']) for x in r if x['status']!='EXACT'])
