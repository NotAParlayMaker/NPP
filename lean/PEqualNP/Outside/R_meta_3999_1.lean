import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3999_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 2 →
      (∀ v : Fin n, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∃ a b : Fin n, G.Adj a b) → 30 ≤ n)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool), G.Colorable 2 →
      (∀ v : Fin n, (G.neighborSet v).ncard = 3) →
      (∃ a b : Fin n, G.Adj a b) →
      (∀ x : Fin n → Bool, f x = true ↔ ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) →
      ∃ u w : Fin n, u ≠ w ∧ ¬ G.Adj u w ∧ ∃ s : ℕ, s + 9 ≤ 2 * n ∧
        PEqualNP.MetaComplexity.HasCircuitSize n
          (fun x : Fin n → Bool => f (Function.update (Function.update x u false) w false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → (30 : ℕ) ≤ x1 ∧ Even x1 ∧ ∃ (x9 : Fin x1) (x10 : Fin x1), x9 ≠ x10 ∧ ¬x2.Adj x9 x10 ∧ ∃ (x11 : ℕ), x11 + (9 : ℕ) ≤ (2 : ℕ) * x1 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update (Function.update x12 x9 Bool.false) x10 Bool.false)) x11 := by
  intro x1 x2 x3 hcol hdeg hgirth hedge hf
  refine ⟨h1 x1 x2 hcol hdeg hgirth hedge, ?_, h2 x1 x2 x3 hcol hdeg hedge hf⟩
  classical
  obtain ⟨C⟩ := hcol
  have hdegF : ∀ v : Fin x1, (Finset.univ.filter (fun w => x2.Adj v w)).card = 3 := by
    intro v
    have e : x2.neighborSet v = ↑(Finset.univ.filter (fun w => x2.Adj v w)) := by
      ext w
      simp [SimpleGraph.mem_neighborSet]
    rw [← hdeg v, e, Set.ncard_coe_finset]
  have hcol01 : ∀ v : Fin x1, C v = 0 ∨ C v = 1 := by
    intro v
    rcases C v with ⟨k, hk⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  let A := Finset.univ.filter (fun v : Fin x1 => C v = 0)
  let B := Finset.univ.filter (fun v : Fin x1 => C v = 1)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro v _ h0 h1'
    rw [h0] at h1'
    exact absurd h1' (by decide)
  have hunion : A ∪ B = Finset.univ := by
    ext v
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => hcol01 v⟩
  have hcard : A.card + B.card = x1 := by
    rw [← Finset.card_union_of_disjoint hAB, hunion, Finset.card_univ, Fintype.card_fin]
  have habove : ∀ a ∈ A, (B.bipartiteAbove x2.Adj a).card = 3 := by
    intro a ha
    rw [← hdegF a]
    congr 1
    ext w
    simp only [Finset.bipartiteAbove, B, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have hne : C a ≠ C w := C.valid h
      have ha0 : C a = 0 := (Finset.mem_filter.mp ha).2
      rcases hcol01 w with hw | hw
      · exact absurd (ha0.trans hw.symm) hne
      · exact hw
  have hbelow : ∀ b ∈ B, (A.bipartiteBelow x2.Adj b).card = 3 := by
    intro b hb
    rw [← hdegF b]
    congr 1
    ext w
    simp only [Finset.bipartiteBelow, A, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2.symm
    · intro h
      refine ⟨?_, h.symm⟩
      have hne : C b ≠ C w := C.valid h
      have hb1 : C b = 1 := (Finset.mem_filter.mp hb).2
      rcases hcol01 w with hw | hw
      · exact hw
      · exact absurd (hb1.trans hw.symm) hne
  have hsum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := A) (t := B)
    (r := x2.Adj)
  rw [Finset.sum_congr rfl habove, Finset.sum_congr rfl hbelow] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  refine ⟨A.card, ?_⟩
  omega
