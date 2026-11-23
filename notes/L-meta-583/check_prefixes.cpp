// Input format is produced by make_instance.py. No SAT solver is needed.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <tuple>
#include <vector>

using Mask = std::uint32_t;

struct Wire {
    Mask positive, negative;
    int left = -1, right = -1;
    bool is_or = false;
};

struct Restriction {
    Mask ones, zeros;
    int bound;
};

struct Search {
    int inputs, num_pos, num_neg, limit, depth;
    std::vector<Wire> wires;
    std::vector<Restriction> rules;
    Mask distinguish[20][20]{};
    long long tried[24]{}, kept[24]{};

    bool impossible(int prefix, Mask used) const {
        int end = inputs + prefix;
        Mask required = ((1u << end) - 1) & ~used;
        for (int p = 0; p < num_pos; ++p)
            for (int n = 0; n < num_neg; ++n)
                if (std::has_single_bit(distinguish[p][n]))
                    required |= distinguish[p][n];

        if (prefix + std::popcount(required) - 1 > limit) return true;

        for (auto [ones, zeros, bound] : rules) {
            Mask constant = ones | zeros;
            if (bound + 2 * prefix + std::popcount(constant & required) <= limit)
                continue;

            int removed = 0;
            int rep[32];
            for (int i = 0; i < inputs; ++i) rep[i] = i;
            for (int i = inputs; i < end; ++i) {
                const auto &gate = wires[i];
                int a = rep[gate.left], b = rep[gate.right];
                bool a_constant = (constant >> a) & 1u;
                bool b_constant = (constant >> b) & 1u;
                rep[i] = i;
                if (a_constant || b_constant) {
                    ++removed;
                    Mask &controlling = gate.is_or ? ones : zeros;
                    if ((controlling & (1u << a)) || (controlling & (1u << b))) {
                        controlling |= 1u << i;
                        constant |= 1u << i;
                    } else {
                        rep[i] = a_constant ? b : a;
                    }
                } else if (a == b) {
                    ++removed;
                    rep[i] = a;
                }
                if (constant & (1u << rep[i])) {
                    constant |= 1u << i;
                    (ones & (1u << rep[i]) ? ones : zeros) |= 1u << i;
                }
            }
            int suffix_savings = std::popcount(constant & required);
            if (bound + removed + suffix_savings > limit) return true;
        }
        return false;
    }

    void enumerate(int prefix, Mask used) {
        ++tried[prefix];
        if (prefix && impossible(prefix, used)) return;
        ++kept[prefix];
        if (prefix == depth) return;
        int end = static_cast<int>(wires.size());

        for (int a = 0; a < end; ++a) for (int b = a + 1; b < end; ++b) {
            for (bool is_or : {false, true}) {
                // Choose the least available (right, left, operation) each time.
                if (prefix && b != end - 1) {
                    const Wire &last = wires.back();
                    if (std::tie(b, a, is_or) < std::tie(last.right, last.left, last.is_or))
                        continue;
                }

                Wire gate{
                    is_or ? wires[a].positive | wires[b].positive
                          : wires[a].positive & wires[b].positive,
                    is_or ? wires[a].negative | wires[b].negative
                          : wires[a].negative & wires[b].negative,
                    a, b, is_or};
                if (!gate.positive || gate.negative == (1u << num_neg) - 1)
                    continue;
                if (std::any_of(wires.begin(), wires.end(), [&](const Wire &w) {
                    return !(gate.positive & ~w.positive) && !(w.negative & ~gate.negative);
                })) continue;

                wires.push_back(gate);
                for (int p = 0; p < num_pos; ++p) if (gate.positive & (1u << p))
                    for (int n = 0; n < num_neg; ++n) if (!(gate.negative & (1u << n)))
                        distinguish[p][n] |= 1u << end;
                enumerate(prefix + 1, used | (1u << a) | (1u << b));
                for (int p = 0; p < num_pos; ++p)
                    for (int n = 0; n < num_neg; ++n)
                        distinguish[p][n] &= ~(1u << end);
                wires.pop_back();
            }
        }
    }

    bool run(std::istream &in) {
        int num_rules;
        in >> inputs >> num_pos >> num_neg >> num_rules >> limit >> depth;
        assert(inputs == 10 && num_pos == 12 && num_neg == 12);
        assert(num_rules == 19896 && limit == 14 && depth == 8);
        std::vector<Mask> positives(num_pos), negatives(num_neg);
        for (auto &x : positives) in >> x;
        for (auto &x : negatives) in >> x;
        for (int i = 0; i < num_rules; ++i) {
            Restriction rule;
            in >> rule.ones >> rule.zeros >> rule.bound;
            rules.push_back(rule);
        }
        assert(in.good());
        for (int i = 0; i < inputs; ++i) {
            Wire input{};
            for (int p = 0; p < num_pos; ++p)
                if (positives[p] & (1u << i)) input.positive |= 1u << p;
            for (int n = 0; n < num_neg; ++n)
                if (negatives[n] & (1u << i)) input.negative |= 1u << n;
            wires.push_back(input);
        }
        for (int p = 0; p < num_pos; ++p)
            for (int n = 0; n < num_neg; ++n)
                distinguish[p][n] = positives[p] & ~negatives[n];
        enumerate(0, 0);
        std::cout << "prefix tried surviving\n";
        for (int i = 0; i <= depth; ++i)
            std::cout << i << ' ' << tried[i] << ' ' << kept[i] << '\n';
        return kept[depth] == 0;
    }
};

int main() {
    Search search{};
    return search.run(std::cin) ? 0 : 1;
}
