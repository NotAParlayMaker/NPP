import csv, ast, sys
import networkx as nx
from exact_edge_fn import synth, target
from synth2 import evaluate
rows=list(csv.DictReader(open('results.csv')))
out=[]
for r in rows:
    if r['status']!='EXACT' or int(r['n'])>5: continue
    G=nx.from_graph6_bytes(r['graph6'].encode()); n=G.number_of_nodes(); T=target(G); s=int(r['s'])
    # independent brute-force witness check
    c=ast.literal_eval(r['circuit']); assert len(c)==s
    wit=all(evaluate(c,n,x)==T[x] for x in range(1<<n))
    # original encoder: UNSAT for all k<s? and SAT at s
    res={k:synth(n,T,k) for k in range(n-1,s+1)}
    orig=min(k for k,v in res.items() if v) if any(res.values()) else None
    print(r['graph6'],s,'orig=',orig,'witness_ok=',wit,'AGREE' if orig==s else 'DISAGREE',flush=True)
