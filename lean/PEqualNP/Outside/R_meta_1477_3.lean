import Mathlib
import PEqualNP.Defs

-- A shared binary OR program builds one set of incident lines for each point.
-- Selecting the 21 outputs uses 21 AND gates and joining them uses 20 OR gates.
-- The bank bound applies to any family whose distinct members intersect in at most one input.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1477_3
    (extract :
      let N := fun p : Fin 21 => Finset.univ.filter (fun l : Fin 21 =>
        (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42,
          (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
          x u = true ∧ x v = true) →
        ∃ W : List (Finset (Fin 21)), W.length + 41 ≤ C.size ∧
          (∀ j < W.length, ∃ A D : Finset (Fin 21), W.getD j ∅ = A ∪ D ∧
            (A.card ≤ 1 ∨ ∃ i < j, W.getD i ∅ = A) ∧ (D.card ≤ 1 ∨ ∃ i < j, W.getD i ∅ = D)) ∧
          ∀ p : Fin 21, ∃ j < W.length, W.getD j ∅ = N p)
    (countBank : ∀ (n b k : ℕ) (B : Fin b → Finset (Fin n)) (W : List (Finset (Fin n))),
      (∀ p, k + 1 ≤ (B p).card) →
      (∀ p q, p ≠ q → ((B p) ∩ (B q)).card ≤ 1) →
      (∀ j < W.length, ∃ A D : Finset (Fin n), W.getD j ∅ = A ∪ D ∧
        (A.card ≤ 1 ∨ ∃ i < j, W.getD i ∅ = A) ∧ (D.card ≤ 1 ∨ ∃ i < j, W.getD i ∅ = D)) →
      (∀ p, ∃ j < W.length, W.getD j ∅ = B p) → b * k ≤ W.length) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hm, hs, hC⟩
  let N := fun p : Fin 21 => Finset.univ.filter (fun l : Fin 21 =>
    (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
  have incidence : ∀ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ↔
      u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) := by
    decide +kernel
  obtain ⟨W, budget, steps, outputs⟩ := extract C hm (by
    intro x
    simpa only [incidence] using hC x)
  have degree : ∀ p : Fin 21, 4 + 1 ≤ (N p).card := by decide +kernel
  have intersection : ∀ p q : Fin 21, p ≠ q → ((N p) ∩ (N q)).card ≤ 1 := by decide +kernel
  have lower := countBank 21 21 4 N W degree intersection steps outputs
  omega
