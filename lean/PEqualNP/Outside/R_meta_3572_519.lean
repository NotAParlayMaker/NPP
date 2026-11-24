import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- Up to order 299 the circuit floor pays for a chain of unions on each whole line.
-- At larger orders, normalize the circuit and start the chains on just the points
-- for which neither endpoint has a single-read proof. Reserve one union for every
-- other point and allow the remaining gates for the starting sets.
theorem PEqualNP.Outside.R_meta_3572_519
  (floorBound : ∀ (q n : ℕ) (F : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q ^ 2 + q + 1 → (∀ l, (F l).card = q + 1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ F l ∧ r ∈ F l) → Monotone2 C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        circuitFun (n+n) C x = decide (∃ p l, p ∈ F l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      3 * n ≤ C.size + 1)
  (prepare : ∀ (q n : ℕ) (F : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n=q^2+q+1 → (∀ l, (F l).card=q+1) →
      (∀ p r, p≠r → ∃! l, p ∈ F l ∧ r ∈ F l) →
      let good := fun D : Circuit => ∀ x : Fin (n+n) → Bool,
        Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        circuitFun (n+n) D x = decide (∃ p l, p ∈ F l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)
      let hard := fun (D : Circuit) (l : Fin n) => (F l).filter fun p =>
        lineSingle D (n+n) (fun i => decide (i < n)) p.val (n+l.val) = false ∧
        lineSingle D (n+n) (fun i => decide (n ≤ i)) p.val (n+l.val) = false
      Monotone2 C → good C →
      ∃ D : Circuit, IsAO2 (n+n) D ∧ good D ∧ D.size ≤ C.size ∧
        (∑ l : Fin n, ((F l) \ hard D l).card) ≤ 20*D.size)
  (residual : ∀ (q n : ℕ) (F : Fin n → Finset (Fin n)) (C : Circuit),
      300 ≤ q → n=q^2+q+1 → (∀ l, (F l).card=q+1) →
      (∀ p r, p≠r → ∃! l, p ∈ F l ∧ r ∈ F l) →
      let good := fun D : Circuit => ∀ x : Fin (n+n) → Bool,
        Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        circuitFun (n+n) D x = decide (∃ p l, p ∈ F l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)
      let hard := fun (D : Circuit) (l : Fin n) => (F l).filter fun p =>
        lineSingle D (n+n) (fun i => decide (i < n)) p.val (n+l.val) = false ∧
        lineSingle D (n+n) (fun i => decide (n ≤ i)) p.val (n+l.val) = false
      let valid := fun P : List (Finset (Fin n)) => ∀ j A, P[j]? = some A →
        ∃ B T : Finset (Fin n), A=B∪T ∧ (B.card ≤ 1 ∨ B ∈ P.take j) ∧ (T.card ≤ 1 ∨ T ∈ P.take j)
      IsAO2 (n+n) C → good C → ∃ P : List (Finset (Fin n)), P.length ≤ 100*C.size - ∑ l, (F l \ hard C l).card ∧
        (∀ l, (hard C l).card ≤ 1 ∨ hard C l ∈ P) ∧ valid P)
  (extendRows : ∀ (n m : ℕ) (F H : Fin m → Finset (Fin n)) (P : List (Finset (Fin n))),
      let valid := fun P : List (Finset (Fin n)) => ∀ j A, P[j]? = some A →
        ∃ B T : Finset (Fin n), A=B∪T ∧ (B.card ≤ 1 ∨ B ∈ P.take j) ∧ (T.card ≤ 1 ∨ T ∈ P.take j)
      (∀ l, H l ⊆ F l) → (∀ l, 1 < (F l).card) →
      (∀ l, (H l).card ≤ 1 ∨ H l ∈ P) → valid P →
      ∃ Y : List (Finset (Fin n)), Y.length ≤ P.length + ∑ l, (F l \ H l).card ∧
        (∀ l, F l ∈ Y) ∧ valid Y) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) → ∃ (x11 : List (Finset (Fin x2))), x11.length ≤ (100 : ℕ) * x4.size ∧ (∀ (x12 : Fin x2), x3 x12 ∈ x11) ∧ ∀ (x12 : ℕ) (x13 : Finset (Fin x2)), x11[x12]? = Option.some x13 → ∃ (x15 : Finset (Fin x2)) (x16 : Finset (Fin x2)), x13 = x15 ∪ x16 ∧ (x15.card ≤ (1 : ℕ) ∨ x15 ∈ List.take x12 x11) ∧ (x16.card ≤ (1 : ℕ) ∨ x16 ∈ List.take x12 x11) := by
  intro q n F C hq hn hcard hpair hm hgood
  by_cases hlarge : 300 ≤ q
  case neg =>
    classical
    have bound := floorBound q n F C hq hn hcard hpair hm hgood
    have nonempty (l : Fin n) : (F l).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
    let D (l : Fin n) : Finset (Fin n) := {(F l).min' (nonempty l)}
    have sub (l : Fin n) : D l ⊆ F l := Finset.singleton_subset_iff.mpr (Finset.min'_mem _ _)
    have each (l : Fin n) : (F l \ D l).card = q := by
      rw [Finset.card_sdiff_of_subset (sub l), hcard]
      simp [D]
    obtain ⟨ys, len, rows, valid⟩ := extendRows n n F D [] sub (fun l => by rw [hcard]; omega)
      (fun l => Or.inl (by simp [D])) (by intro _ _ h; simp at h)
    refine ⟨ys, len.trans ?_, rows, valid⟩
    simp only [List.length_nil, zero_add, each, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change n*q ≤ 100*C.size
    have many : 100 ≤ n := by rw [hn]; omega
    have upper := Nat.mul_le_mul_left n (show q ≤ 299 by omega)
    omega
  let H (D : Circuit) (l : Fin n) := (F l).filter fun p =>
    lineSingle D (n+n) (fun i => decide (i < n)) p.val (n+l.val) = false ∧
    lineSingle D (n+n) (fun i => decide (n ≤ i)) p.val (n+l.val) = false
  obtain ⟨D,hao,hdgood,hdsize,heasy⟩ := prepare q n F C hq hn hcard hpair hm hgood
  obtain ⟨P,hbudget,hcover,hvalid⟩ := residual q n F D hlarge hn hcard hpair hao hdgood
  have hsub (l : Fin n) : H D l ⊆ F l := Finset.filter_subset _ _
  obtain ⟨Y,hy,hrows,hbuild⟩ := extendRows n n F (H D) P hsub (fun l => by rw [hcard]; omega) hcover hvalid
  change (∑ l, (F l \ H D l).card) ≤ 20*D.size at heasy
  change P.length ≤ 100 * D.size - ∑ l, (F l \ H D l).card at hbudget
  exact ⟨Y,by omega,hrows,hbuild⟩
