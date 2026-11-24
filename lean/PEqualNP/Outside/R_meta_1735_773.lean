import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1735_773
    (replace : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let subsumes := fun v w : Fin n =>
        ∀ g ∈ junk G C, ∀ b : Fin 2, v ∈ side C g b → w ∈ side C g b
      IsLeastAO G C → TopForm G C →
      ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
        (∀ w, subsumes v w → G.Adj u w) ∨ (∀ w, subsumes u w → G.Adj v w))
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let subsumes := fun v w : Fin n =>
        ∀ g ∈ junk G C, ∀ b : Fin 2, v ∈ side C g b → w ∈ side C g b
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → ∀ E : Finset (Sym2 (Fin n)),
      (∀ e ∈ E, ∃ u v, e = s(u, v) ∧ (∃ w, w ≠ v ∧ subsumes v w) ∧
        (∀ w, subsumes v w → G.Adj u w)) → E.card ≤ C.size + 1)
    (remaining : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      let subsumes := fun v w : Fin n =>
        ∀ g ∈ junk G C, ∀ b : Fin 2, v ∈ side C g b → w ∈ side C g b
      ∀ E : Finset (Sym2 (Fin n)), E ⊆ Ustar G C →
      (∀ u v : Fin n, s(u, v) ∈ E → (∀ w, subsumes v w → G.Adj u w) →
        ∀ w, subsumes v w → w = v) →
      (∀ e ∈ E, ∃ u v, e = s(u, v) ∧ ∀ w, subsumes v w → w = v) →
      E.card ≤ c * (C.size + 1)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c, bound⟩ := remaining
  refine ⟨c + 1, ?_⟩
  intro n G _ girth edges C least top
  classical
  let subsumes := fun v w : Fin n =>
    ∀ g ∈ junk G C, ∀ b : Fin 2, v ∈ side C g b → w ∈ side C g b
  let hasCharge (e : Sym2 (Fin n)) :=
    ∃ u v, e = s(u, v) ∧ (∃ w, w ≠ v ∧ subsumes v w) ∧
      (∀ w, subsumes v w → G.Adj u w)
  let easy := (Ustar G C).filter hasCharge
  let hard := Ustar G C \ easy
  have easyBound : easy.card ≤ C.size + 1 := by
    apply charge n G C girth least easy
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hardSubset : hard ⊆ Ustar G C := Finset.sdiff_subset
  have maximal (u v : Fin n) (he : s(u, v) ∈ hard)
      (adj : ∀ w, subsumes v w → G.Adj u w) : ∀ w, subsumes v w → w = v := by
    intro w hw
    by_contra hn
    obtain ⟨hu, hneasy⟩ := Finset.mem_sdiff.mp he
    exact hneasy (Finset.mem_filter.mpr ⟨hu, u, v, rfl, ⟨w, hn, hw⟩, adj⟩)
  have orient (e : Sym2 (Fin n)) (he : e ∈ hard) :
      ∃ u v, e = s(u, v) ∧ ∀ w, subsumes v w → w = v := by
    induction e using Sym2.ind with
    | _ u v =>
      rcases replace n G C least top u v (hardSubset he) with adj | adj
      · exact ⟨u, v, rfl, maximal u v he adj⟩
      · exact ⟨v, u, Sym2.eq_swap, maximal v u (Sym2.eq_swap ▸ he) adj⟩
  have hardBound := bound n G girth edges C least top hard hardSubset maximal orient
  have easySubset : easy ⊆ Ustar G C := Finset.filter_subset _ _
  have sumCards : hard.card + easy.card = (Ustar G C).card :=
    Finset.card_sdiff_add_card_eq_card easySubset
  rw [Nat.add_mul, one_mul]
  omega
