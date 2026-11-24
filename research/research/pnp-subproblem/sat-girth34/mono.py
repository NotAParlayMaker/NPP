import csv, os, sys, subprocess, time
from concurrent.futures import ThreadPoolExecutor
TO=int(os.environ.get('TO',600))
rows=list(csv.DictReader(open('results.csv')))
def work(r):
    if r['status']!='EXACT': return ''
    g=r['graph6'];s=int(r['s']);P=int(r['P'])
    for k in range(s,P+4):
        try: o=subprocess.run(['python3','synth2.py',g,str(k)],capture_output=True,text=True,timeout=TO,env=dict(os.environ,MONO='1')).stdout
        except subprocess.TimeoutExpired: return f">={k}(TIMEOUT)"
        print(g,k,o[:5],flush=True)
        if o.startswith('SAT'): return str(k)
    return f">{P+3}"
with ThreadPoolExecutor(int(sys.argv[1])) as ex: res=list(ex.map(work,rows))
for r,x in zip(rows,res): r['s_mono']=x
w=csv.DictWriter(open('results_mono.csv','w',newline=''),fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
