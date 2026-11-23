"""The finite graph calculations for L-meta-583. Run with Python 3."""
from itertools import combinations

HUBS = tuple(range(4))
PAIRS = tuple(combinations(HUBS, 2))
MIDPOINT = dict(zip(PAIRS, range(4, 10)))
EDGES = {(hub, MIDPOINT[pair]) for pair in PAIRS for hub in pair}


def midpoint(u, v):
    return MIDPOINT[tuple(sorted((u, v)))]


def check_restriction(u, v):
    removed = midpoint(u, v)
    a, b = (hub for hub in HUBS if hub not in (u, v))
    paths = [
        [a, midpoint(a, b), b],
        [a, midpoint(a, u), u, midpoint(u, b), b],
        [a, midpoint(a, v), v, midpoint(v, b), b],
    ]
    remaining = {edge for edge in EDGES if edge[1] != removed}
    path_edges = {tuple(sorted(edge)) for path in paths for edge in zip(path, path[1:])}
    assert path_edges == remaining
    interior = [node for path in paths for node in path[1:-1]]
    assert len(interior) == len(set(interior)) == 7
    assert [len(path) - 1 for path in paths] == [2, 4, 4]
    matching = {(u, midpoint(a, u)), (v, midpoint(a, v)),
                (a, midpoint(a, b)), (b, midpoint(b, v))}
    assert matching <= remaining
    assert len({node for edge in matching for node in edge}) == 8
    assert all(hub in HUBS for hub, _ in remaining)


def check_upper_bound():
    gates = []

    def append_gate(operation, left, right):
        gates.append((operation, left, right))
        return 10 + len(gates) - 1

    terms = []
    for hub in HUBS:
        a, b, c = [mid for h, mid in sorted(EDGES) if h == hub]
        any_neighbor = append_gate("or", append_gate("or", a, b), c)
        terms.append(append_gate("and", hub, any_neighbor))
    left = append_gate("or", terms[0], terms[1])
    right = append_gate("or", terms[2], terms[3])
    output = append_gate("or", left, right)
    assert len(gates) == 15

    for row in range(1 << 10):
        wires = [bool(row & (1 << i)) for i in range(10)]
        expected = any(wires[h] and wires[m] for h, m in EDGES)
        for operation, a, b in gates:
            wires.append(wires[a] and wires[b] if operation == "and" else wires[a] or wires[b])
        assert wires[output] == expected


if __name__ == "__main__":
    for u, v in PAIRS:
        check_restriction(u, v)
    check_upper_bound()
    print("Verified six theta restrictions and their minimum cover sizes of four.")
    print("Verified the 15-gate upper bound on all 1,024 inputs.")
