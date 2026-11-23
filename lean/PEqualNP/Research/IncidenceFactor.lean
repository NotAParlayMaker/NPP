import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.IncidenceFactor

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge
open PEqualNP.MetaComplexity.LowMergeProof

def hits {P L : ℕ} (inc : Fin P → Fin L → Bool) (x : Fin P → Bool)
    (y : Fin L → Bool) : Prop :=
  ∃ p l, inc p l = true ∧ x p = true ∧ y l = true

def accepts {P L : ℕ} (C : Circuit) (g : ℕ) (x : Fin P → Bool)
    (y : Fin L → Bool) : Prop :=
  wireVal C (List.ofFn x ++ List.ofFn y) g = true

private lemma accepts_mono {P L : ℕ} (C : Circuit) (hC : IsMonotoneCircuit C)
    (g : ℕ) (x x' : Fin P → Bool) (y : Fin L → Bool)
    (h : ∀ p, x p = true → x' p = true) :
    accepts C g x y → accepts C g x' y := by
  apply wires_mono C hC _ _ (by simp) _ g
  intro i hi
  by_cases hlt : i < P
  · rw [List.getD_append _ _ _ _ (by simpa using hlt)] at hi ⊢
    simpa [List.getD_eq_getElem?_getD, hlt] using
      h ⟨i, hlt⟩ (by simpa [List.getD_eq_getElem?_getD, hlt] using hi)
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi ⊢
    simpa using hi

/-- If the conjunction of two wires detects incidence, then fixing all line inputs
    makes one wire detect incidence on every point assignment. The choice of wire
    may depend on the line assignment. -/
theorem exact_factor_on_fixed_lines {P L : ℕ} (inc : Fin P → Fin L → Bool)
    (C : Circuit) (hC : IsMonotoneCircuit C) (a b : ℕ)
    (correct : ∀ x y, (accepts C a x y ∧ accepts C b x y) ↔ hits inc x y)
    (y : Fin L → Bool) :
    (∀ x, accepts C a x y ↔ hits inc x y) ∨
    (∀ x, accepts C b x y ↔ hits inc x y) := by
  let outside : Fin P → Bool := fun p => decide (∀ l, y l = true → inc p l = false)
  have misses : ¬ hits inc outside y := by
    rintro ⟨p, l, hpl, hp, hl⟩
    have hall : ∀ j, y j = true → inc p j = false := of_decide_eq_true hp
    simpa [hpl] using hall l hl
  have subset (x : Fin P → Bool) (hx : ¬ hits inc x y) :
      ∀ p, x p = true → outside p = true := by
    intro p hp
    apply decide_eq_true
    intro l hl
    cases hpl : inc p l with
    | false => rfl
    | true => exact (hx ⟨p, l, hpl, hp, hl⟩).elim
  have sound (g : ℕ) (hg : ¬ accepts C g outside y) :
      ∀ x, accepts C g x y → hits inc x y := by
    intro x hx
    by_contra hm
    exact hg (accepts_mono C hC g x outside y (subset x hm) hx)
  by_cases ha : accepts C a outside y
  · have hb : ¬ accepts C b outside y := fun hb => misses ((correct _ _).mp ⟨ha, hb⟩)
    exact Or.inr fun x => ⟨sound b hb x, fun h => ((correct x y).mpr h).2⟩
  · exact Or.inl fun x => ⟨sound a ha x, fun h => ((correct x y).mpr h).1⟩

end PEqualNP.IncidenceFactor
