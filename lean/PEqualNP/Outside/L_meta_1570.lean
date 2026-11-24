import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_prefix (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, step_length, List.length_cons]
    omega

lemma fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by rw [step_length]; omega)]
    exact step_prefix w g i hi

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (gs.foldl step x).getD o false := rfl

lemma eval_low (gs : List Gate) (o : ℕ) (x : Fin 13 → Bool) (ho : o < 13) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = x ⟨o, ho⟩ := by
  rw [eval_eq, fold_prefix _ _ _ (by simpa using ho)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using ho), List.getElem_ofFn]
  rfl

lemma eval_high (gs : List Gate) (o : ℕ) (x : Fin 13 → Bool) (ho : 13 + gs.length ≤ o) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = false := by
  rw [eval_eq]
  exact List.getD_eq_default _ _ (by rw [fold_length]; simpa using ho)

end PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ h
  obtain rfl : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  have e0 := h 0 (fun v => decide (v = 0)) (Or.inl (by decide))
  have e1 := h 0 (fun v => decide (v = 1)) (Or.inr (Or.inl (by decide)))
  have e2 := h 0 (fun v => decide (v ∉ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13))))
    (Or.inr (Or.inr (by decide)))
  have e3 : ∀ t : Fin 13, t ≠ 0 → _ := fun t ht =>
    h 0 (fun v => decide (v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13))))
      (by revert t; decide)
  have d0 : decide (∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)), decide (v = 0) = true) = true := by decide
  have d1 : decide (∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)), decide (v = 1) = true) = true := by decide
  have d2 : decide (∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)),
      decide (v ∉ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13))) = true) = false := by decide
  have d3 : ∀ t : Fin 13, t ≠ 0 → decide (∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)),
      decide (v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13))) = true) = true := by decide
  rw [d0] at e0
  rw [d1] at e1
  rw [d2] at e2
  refine ⟨?_, ?_, e0, e1, e2, fun t ht => (e3 t ht).trans (d3 t ht)⟩
  · by_contra hc
    have ho : o 0 < 13 := by omega
    rw [PEqualNP.Outside.L_meta_1570.eval_low _ _ _ ho] at e0 e1
    have a0 : (⟨o 0, ho⟩ : Fin 13) = 0 := by simpa using e0
    have a1 : (⟨o 0, ho⟩ : Fin 13) = 1 := by simpa using e1
    rw [a0] at a1
    exact absurd a1 (by decide)
  · by_contra hc
    rw [PEqualNP.Outside.L_meta_1570.eval_high _ _ _ (by omega)] at e0
    exact absurd e0 (by decide)
