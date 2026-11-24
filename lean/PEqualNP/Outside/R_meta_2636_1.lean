import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- Separate deletion on the edge function from the exact cost of independent OR inputs.
theorem PEqualNP.Outside.R_meta_2636_1
    (edgeOnly :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool),
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
        (∀ i j, G.Adj i j → i ∉ A) →
        (∃ i j, G.Adj i j) →
        (∀ x, f x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
        ∀ s, HasCircuitSize n f s →
          ∃ z ∉ A, ∃ t, t + 4 ≤ s ∧
            HasCircuitSize n (fun x => f (Function.update x z false)) t)
    (removeOr :
      ∀ (n : ℕ) (A : Finset (Fin n)) (f g : (Fin n → Bool) → Bool),
        (∀ a ∈ A, ∀ (x : Fin n → Bool) (b : Bool), f (Function.update x a b) = f x) →
        (∃ x, f x = false) → (∃ x, f x = true) →
        (∀ x, g x = true ↔ (∃ a ∈ A, x a = true) ∨ f x = true) →
        ∀ s, HasCircuitSize n g s →
          ∃ t, t + A.card ≤ s ∧ HasCircuitSize n f t)
    (addOr :
      ∀ (n : ℕ) (A : Finset (Fin n)) (f g : (Fin n → Bool) → Bool),
        (∃ x, f x = true) →
        (∀ x, g x = true ↔ (∃ a ∈ A, x a = true) ∨ f x = true) →
        ∀ s, HasCircuitSize n f s → HasCircuitSize n g (s + A.card)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 →
      Bool) →
      Bool), (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) →
      (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle →
      (7 : ℕ) ≤ x7.length) →
      (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 →
      x7 ∉ x3) →
      (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) →
      (∀ (x9 : Fin x1 →
      Bool), x4 x9 = Bool.true ↔ (∃ x10 ∈ x3, x9 x10 = Bool.true) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) →
      ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x10 →
      ∃ x12 ∉ x3, ∃ (x13 : ℕ), x13 + (4 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x14 : Fin x1 →
      Bool) => x4 (Function.update x14 x12 Bool.false)) x13 := by
  classical
  intro n G A f deg girth isolated hasEdge spec s cs
  let edge : (Fin n → Bool) → Bool :=
    fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
  have edgeSpec (x : Fin n → Bool) :
      edge x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
    simp [edge]
  have ignore (a : Fin n) (ha : a ∈ A) (x : Fin n → Bool) (b : Bool) :
      edge (Function.update x a b) = edge x := by
    apply Bool.eq_iff_iff.mpr
    simp only [edgeSpec]
    constructor <;> rintro ⟨i, j, adj, hi, hj⟩
    all_goals
      have ia : i ≠ a := fun e => isolated i j adj (e.symm ▸ ha)
      have ja : j ≠ a := fun e => isolated j i adj.symm (e.symm ▸ ha)
      exact ⟨i, j, adj, by simpa only [Function.update_of_ne ia] using hi,
        by simpa only [Function.update_of_ne ja] using hj⟩
  have edgeFalse : edge (fun _ => false) = false := by
    unfold edge
    simp
  have edgeTrue : edge (fun _ => true) = true :=
    (edgeSpec _).mpr (by simpa using hasEdge)
  have combined (x : Fin n → Bool) :
      f x = true ↔ (∃ a ∈ A, x a = true) ∨ edge x = true := by
    rw [edgeSpec, spec]
  obtain ⟨r, rBound, cr⟩ := removeOr n A edge f ignore
    ⟨_, edgeFalse⟩ ⟨_, edgeTrue⟩ combined s cs
  obtain ⟨z, hz, t, tBound, ct⟩ := edgeOnly n G A edge deg girth isolated hasEdge edgeSpec r cr
  have otherEdge : ∃ i j, G.Adj i j ∧ i ≠ z ∧ j ≠ z := by
    have d := deg z hz
    have nonempty : (G.neighborSet z).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨v, hv⟩ := nonempty
    have vz : G.Adj v z := (show G.Adj z v from hv).symm
    have va : v ∉ A := isolated v z vz
    have vne : v ≠ z := G.ne_of_adj vz
    have dv := deg v va
    have existsW : ∃ w ∈ G.neighborSet v, w ≠ z := by
      by_contra! no
      have sub : G.neighborSet v ⊆ {z} := fun w hw => no w hw
      have le := Set.ncard_le_ncard sub (Set.finite_singleton z)
      rw [Set.ncard_singleton] at le
      omega
    obtain ⟨w, hw, hne⟩ := existsW
    exact ⟨v, w, hw, vne, hne⟩
  have stillTrue : ∃ x : Fin n → Bool, edge (Function.update x z false) = true := by
    obtain ⟨i, j, adj, iz, jz⟩ := otherEdge
    exact ⟨fun _ => true, (edgeSpec _).mpr
      ⟨i, j, adj, by simp [Function.update_of_ne iz], by simp [Function.update_of_ne jz]⟩⟩
  have combinedAfter (x : Fin n → Bool) :
      f (Function.update x z false) = true ↔
        (∃ a ∈ A, x a = true) ∨ edge (Function.update x z false) = true := by
    rw [combined]
    have ha : (∃ a ∈ A, Function.update x z false a = true) ↔ (∃ a ∈ A, x a = true) := by
      constructor <;> rintro ⟨a, aA, ax⟩
      all_goals
        have az : a ≠ z := fun e => hz (e ▸ aA)
        exact ⟨a, aA, by simpa only [Function.update_of_ne az] using ax⟩
    rw [ha]
  exact ⟨z, hz, t + A.card, by omega, addOr n A _ _ stillTrue combinedAfter t ct⟩
