import Mathlib
import PEqualNP.Defs

-- Cut of L-meta-2828 by the number of NOT gates a translation into AND, OR and NOT gates needs. Fix a
-- polarity p for every gate wire (the inputs and the given OR wire positive) and a set q of wires that get a
-- NOT. Each signed gate becomes one AND or OR gate; a read whose sign does not match the polarity of the wire
-- it reads needs that wire in q, and so does the output when its polarity does not match.
-- h1: if the gates plus those NOT gates number at most 13, the translation with the first gate OR(x0, x1)
-- has at most 14 gates, the case that L_meta_2012 excludes.
-- h3: at most 11 gates is excluded by the count of L_meta_2165 (one more gate for OR(x0, x1)).
-- h2: what remains, circuits of 12 or 13 gates whose every such translation needs at least 14 gates
-- besides OR(x0, x1): the circuits that need negations.
theorem PEqualNP.Outside.R_meta_2828_812
    (h1 : ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool) (sl sr p q : ℕ → Bool),
      (∀ i : ℕ, i < 10 → p i = true) →
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), C.gates[j]? = some g →
        g.op = (fun u v : Bool => u == sl j && v == sr j) ∧
        (g.left < 11 + j → g.left ≠ 10 → (sl j == p (11 + j)) ≠ p g.left → q g.left = true) ∧
        (g.right < 11 + j → g.right ≠ 10 → (sr j == p (11 + j)) ≠ p g.right → q g.right = true)) →
      (p C.output = b → q C.output = true) →
      (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) = [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e : ℕ => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) →
      C.size + (List.range 10).countP q + (List.range C.size).countP (fun j => q (11 + j)) ≤ 13 → False)
    (h2 : ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool),
      (∀ g ∈ C.gates, ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) = [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e : ℕ => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) →
      12 ≤ C.size →
      (∀ (sl sr p q : ℕ → Bool), (∀ i : ℕ, i < 10 → p i = true) →
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), C.gates[j]? = some g →
        g.op = (fun u v : Bool => u == sl j && v == sr j) ∧
        (g.left < 11 + j → g.left ≠ 10 → (sl j == p (11 + j)) ≠ p g.left → q g.left = true) ∧
        (g.right < 11 + j → g.right ≠ 10 → (sr j == p (11 + j)) ≠ p g.right → q g.right = true)) →
      (p C.output = b → q C.output = true) →
      14 ≤ C.size + (List.range 10).countP q + (List.range C.size).countP (fun j => q (11 + j))) →
      14 ≤ C.size)
    (h3 : ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool),
      (∀ g ∈ C.gates, ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) = ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e : ℕ => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) →
      C.size ≤ 11 → False) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C b hops hfun
  have hG : ∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) =
      [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e : ℕ => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)) := by
    intro x
    rw [hfun x]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  apply h2 C b hops hG
  · by_contra hlt
    exact h3 C b hops hG (by omega)
  · intro sl sr p q hp H ho
    by_contra hlt
    exact h1 C b sl sr p q hp H ho hG (by omega)
