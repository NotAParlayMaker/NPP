"""Live view of which open steps already have a pull request upstream.

The public list's pull request counts lag by a long time. This reads the pull request
heads straight from the upstream repository (trees only, no file contents) and reports,
for each open step, which pull requests add its file.

Usage: python3 generator/pr_index.py <gaps.json> [first PR number to look at]
"""
import json, re, subprocess, sys, collections

def sh(*a):
    return subprocess.run(a, capture_output=True, text=True).stdout

def build(first=5400):
    heads = [l.split() for l in sh('git', 'ls-remote', 'upstream', 'refs/pull/*/head').splitlines()]
    have = {l.split()[1].split('/')[-1]: l.split()[0] for l in sh('git', 'for-each-ref', '--format=%(objectname) %(refname)', 'refs/prs').splitlines()}
    todo = []
    for sha, ref in heads:
        n = ref.split('/')[2]
        if int(n) >= first and have.get(n) != sha:
            todo.append(f'+refs/pull/{n}/head:refs/prs/{n}')
    for i in range(0, len(todo), 300):
        subprocess.run(['git', 'fetch', '-q', '--depth=1', '--filter=blob:none', 'upstream'] + todo[i:i+300])
    main = set(sh('git', 'ls-tree', '--name-only', 'upstream/main', 'lean/PEqualNP/Outside/').split())
    index = collections.defaultdict(list)
    for l in sh('git', 'for-each-ref', '--format=%(refname)', 'refs/prs').splitlines():
        n = int(l.split('/')[-1])
        files = set(sh('git', 'ls-tree', '--name-only', l, 'lean/PEqualNP/Outside/').split())
        for f in files - main:
            index[f.split('/')[-1][:-5]].append(n)
    return index, max(int(r.split('/')[2]) for _, r in heads)

if __name__ == '__main__':
    gaps = json.load(open(sys.argv[1]))
    index, newest = build(int(sys.argv[2]) if len(sys.argv) > 2 else 5400)
    json.dump({k: sorted(v) for k, v in index.items()}, open('/tmp/pr_index.json', 'w'))
    print('newest pull request seen:', newest, '| list updated', gaps['updated_at'])
    for r in gaps['gaps']:
        mod = r['file'].split('/')[-1][:-5]
        stem = mod[2:]
        proofs = sorted(index.get(mod, []))
        reds = sorted(n for k, v in index.items() if k.startswith('R_' + stem + '_') for n in v)
        r['_proofs'], r['_reds'] = proofs, reds
    json.dump(gaps, open('/tmp/gaps_live.json', 'w'))
    free = [r for r in gaps['gaps'] if not r['_proofs'] and not r['_reds']]
    print('open steps:', len(gaps['gaps']), '| with no pull request of any kind:', len(free))
