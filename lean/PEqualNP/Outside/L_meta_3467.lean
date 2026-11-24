import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3467

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

lemma fold_shape (gs : List Gate) :
    ∀ w : List Bool, ∃ u : List Bool, u.length = gs.length ∧ gs.foldl stepW w = w ++ u := by
  induction gs with
  | nil => intro w; exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨u, hu, he⟩ := ih (stepW w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ u, ?_, ?_⟩
    · simp [hu]
    · rw [List.foldl_cons, he]
      simp [stepW]

lemma fold_old (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  obtain ⟨u, _, he⟩ := fold_shape gs w
  rw [he, List.getD_append _ _ _ _ h]

lemma eval_inp {n : ℕ} (C : Circuit) (X Y : Finset (Fin n)) (h : C.output < n + n) :
    C.eval (incidenceInput X Y) = (incidenceInput X Y).getD C.output false := by
  show (C.gates.foldl stepW _).getD C.output false = _
  rw [fold_old _ _ _ (by simp [incidenceInput]; omega)]

lemma inc_lo {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (incidenceInput X Y).getD i false = decide ((⟨i, hi⟩ : Fin n) ∈ X) := by
  unfold incidenceInput
  rw [List.getD_append _ _ _ _ (by simp; exact hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma inc_hi {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi : n ≤ i) (h2 : i < n + n) :
    (incidenceInput X Y).getD i false = decide ((⟨i - n, by omega⟩ : Fin n) ∈ Y) := by
  unfold incidenceInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; exact hi)]
  have : i - n < n := by omega
  simp [this]

end PEqualNP.Outside.L_meta_3467

open PEqualNP.Outside.L_meta_3467 in
theorem PEqualNP.Outside.L_meta_3467 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 h1 h2 h3 h4 _ h6 h7 _
  exfalso
  have hsq : x1 + 2 ≤ x2 := by subst h2; nlinarith
  by_cases ho : x4.output < x2
  · set p0 : Fin x2 := ⟨x4.output, ho⟩
    have hc : 1 < (x3 p0).card := by rw [h3]; omega
    obtain ⟨p, hp, hne⟩ := Finset.exists_mem_ne hc p0
    have e := h7 p0 p hp
    rw [eval_inp _ _ _ h6, inc_lo _ _ _ ho] at e
    simp at e
    exact hne e.symm
  · have ho' : x2 ≤ x4.output := by omega
    set l0 : Fin x2 := ⟨x4.output - x2, by omega⟩
    have hp : ∃ p, p ∉ x3 l0 := by
      by_contra hn
      push_neg at hn
      have : (Finset.univ : Finset (Fin x2)) ⊆ x3 l0 := fun a _ => hn a
      have := Finset.card_le_card this
      rw [Finset.card_univ, Fintype.card_fin, h3] at this
      omega
    obtain ⟨p, hp⟩ := hp
    have hc : 1 < (Finset.univ : Finset (Fin x2)).card := by
      rw [Finset.card_univ, Fintype.card_fin]; omega
    obtain ⟨q, _, hq⟩ := Finset.exists_mem_ne hc p
    obtain ⟨l, ⟨hpl, _⟩, _⟩ := h4 p q (Ne.symm hq)
    have e := h7 l p hpl
    rw [eval_inp _ _ _ h6, inc_hi _ _ _ ho' h6] at e
    simp at e
    have : l = l0 := by
      rw [← e]
    exact hp (this ▸ hpl)
