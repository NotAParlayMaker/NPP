"""Generate nonconstant restrictions fixing 1–8 inputs and their gate lower bounds."""

from functools import lru_cache
from itertools import combinations, product

N = 10
EDGES = [(0,4), (4,1), (0,5), (5,2), (0,6), (6,3),
         (1,7), (7,2), (1,8), (8,3), (2,9), (9,3)]
TARGET = frozenset(1 << a | 1 << b for a, b in EDGES)


def variables(terms):
    result = 0
    for term in terms:
        result |= term
    return result


@lru_cache(None)
def restrict(terms, bit, value):
    reduced = [term & ~bit for term in terms if value or not term & bit]
    return frozenset(term for term in reduced
                     if not any(other != term and other & term == other
                                for other in reduced))


@lru_cache(None)
def lower_bound(terms):
    mask = variables(terms)
    bits = [1 << i for i in range(N) if mask & (1 << i)]
    n = len(bits)
    basic = max(0, n - 1)
    if n <= 2 or len(terms) == 1 or all(t.bit_count() == 1 for t in terms):
        return basic

    # In a minimum circuit the first binary gate has distinct inputs a and b.
    # For each first gate, take the strongest result of fixing one operand.
    bounds = []
    for a, b in combinations(bits, 2):
        for controlling in (0, 1):
            score = basic
            for fixed, partner in [(a, b), (b, a)]:
                more = bool(variables(restrict(terms, partner, controlling)) & fixed)
                score = max(score,
                            lower_bound(restrict(terms, fixed, controlling)) + 2 + more,
                            lower_bound(restrict(terms, fixed, 1-controlling)) + 1 + more)
            bounds.append(score)
    return min(bounds)


def main():
    positives = sorted(TARGET)
    false_inputs = {x for x in range(1 << N) if not any(t & x == t for t in TARGET)}
    negatives = sorted(x for x in false_inputs if all(
        (x | 1 << i) not in false_inputs for i in range(N) if not x & (1 << i)))
    rules = []
    # Omitted restrictions simply leave fewer lower bounds available for pruning.
    for n_fixed in range(1, N-1):
        for fixed in combinations(range(N), n_fixed):
            for values in product((0, 1), repeat=n_fixed):
                terms = TARGET
                ones = zeros = 0
                for i, value in zip(fixed, values):
                    bit = 1 << i
                    terms = restrict(terms, bit, value)
                    if value:
                        ones |= bit
                    else:
                        zeros |= bit
                if terms and 0 not in terms:
                    rules.append((ones, zeros, lower_bound(terms)))
    rules.sort(key=lambda r: -(r[2] + (r[0] | r[1]).bit_count()))

    print(N, len(positives), len(negatives), len(rules), 14, 8)
    print(*positives)
    print(*negatives)
    for rule in rules:
        print(*rule)


if __name__ == '__main__':
    main()
