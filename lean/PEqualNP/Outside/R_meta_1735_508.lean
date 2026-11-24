import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1735_508
    (traces : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → TopForm G C → ∀ e ∈ Ustar G C, (∃ g∈junk G C, e∈gammaE G C g ∧ ∃ u∈wmax G C g, u∈e) ∨
        (∃ g∈junk G C, ∃ h∈junk G C, g≠h ∧
          (∀ j : ℕ, j=g ∨ j=h → e∈gammaE G C j ∧ ∀ u∈e, gateVal n C j (pairInput u u)=false) ∧
          ∀ x, gateVal n C g x=true → gateVal n C h x=true → graphFun G ∅ x=true))
    (centres : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C → ∀ E : Finset (Sym2 (Fin n)), E ⊆ Ustar G C →
      (∀ e∈E, (∃ g∈junk G C, e∈gammaE G C g ∧ ∃ u∈wmax G C g, u∈e)) → E.card ≤ c*(C.size+1))
    (pairs : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C → ∀ E : Finset (Sym2 (Fin n)), E ⊆ Ustar G C →
      (∀ e∈E, ¬ (∃ g∈junk G C, e∈gammaE G C g ∧ ∃ u∈wmax G C g, u∈e) ∧ (∃ g∈junk G C, ∃ h∈junk G C, g≠h ∧
          (∀ j : ℕ, j=g ∨ j=h → e∈gammaE G C j ∧ ∀ u∈e, gateVal n C j (pairInput u u)=false) ∧
          ∀ x, gateVal n C g x=true → gateVal n C h x=true → graphFun G ∅ x=true)) → E.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨a,ha⟩ := centres
  obtain ⟨b,hb⟩ := pairs
  refine ⟨a+b,?_⟩
  intro n G _ girth nonempty C least top
  let U := Ustar G C
  let W (e : Sym2 (Fin n)) := (∃ g∈junk G C, e∈gammaE G C g ∧ ∃ u∈wmax G C g, u∈e)
  let A := U.filter W
  have hA : A ⊆ U := Finset.filter_subset _ _
  have one := ha n G girth nonempty C least top A hA (fun e h => (Finset.mem_filter.mp h).2)
  have two := hb n G girth nonempty C least top (U \ A) Finset.sdiff_subset (by
    intro e he
    obtain ⟨hu,hn⟩ := Finset.mem_sdiff.mp he
    have hw : ¬ W e := fun h => hn (Finset.mem_filter.mpr ⟨hu,h⟩)
    exact ⟨hw,(traces n G C least top e hu).resolve_left hw⟩)
  rw [Nat.add_mul]
  have sum := Finset.card_sdiff_add_card_eq_card hA
  change U.card ≤ _
  omega

