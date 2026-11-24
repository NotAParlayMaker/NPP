import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1570

lemma wires_prefix (gates : List Gate) : ∀ (w : List Bool),
    ∃ r : List Bool,
      gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ r ∧
      r.length = gates.length := by
  induction gates with
  | nil =>
    intro w
    exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨r, hr, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: r, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hr]
    simp

lemma eval_input (gates : List Gate) (o : ℕ) (x : Fin 13 → Bool) (h : o < 13) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = x ⟨o, h⟩ := by
  obtain ⟨r, hr, _⟩ := wires_prefix gates (List.ofFn x)
  show (gates.foldl _ (List.ofFn x)).getD o false = _
  rw [hr]
  have h' : o < (List.ofFn x).length := by simpa using h
  rw [List.getD_append _ _ _ _ h', List.getD_eq_getElem _ _ h', List.getElem_ofFn]

lemma eval_out (gates : List Gate) (o : ℕ) (x : Fin 13 → Bool) (h : 13 + gates.length ≤ o) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = false := by
  obtain ⟨r, hr, hl⟩ := wires_prefix gates (List.ofFn x)
  show (gates.foldl _ (List.ofFn x)).getD o false = _
  rw [hr]
  have h' : (List.ofFn x ++ r).length ≤ o := by
    simp only [List.length_append, List.length_ofFn, hl]
    omega
  exact List.getD_eq_default _ _ h'

lemma zero_one_not_both : ∀ t : Fin 13, t ≠ 0 →
    (0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∨
      (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  decide

lemma line_zero_not_sub : ∀ t : Fin 13, t ≠ 0 →
    ∃ v ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  decide

end PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ hout
  have hL0 : L 0 = {0, 1, 3, 9} := by
    rw [hL]
    decide
  have h3 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    rw [hout 0 (fun v : Fin 13 => decide (v = 0)) (Or.inl (by simp))]
    have hm : (0 : Fin 13) ∈ L 0 := by
      rw [hL0]
      decide
    exact decide_eq_true ⟨0, hm, by decide⟩
  have h4 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    rw [hout 0 (fun v : Fin 13 => decide (v = 1)) (Or.inr (Or.inl (by simp)))]
    have hm : (1 : Fin 13) ∈ L 0 := by
      rw [hL0]
      decide
    exact decide_eq_true ⟨1, hm, by decide⟩
  have h5 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false := by
    have hdom : ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L 0)) v = true := by
      intro v hv
      simpa using hv
    rw [hout 0 (fun v : Fin 13 => decide (v ∉ L 0)) (Or.inr (Or.inr hdom))]
    apply decide_eq_false
    rintro ⟨v, hv, hx⟩
    simp [hv] at hx
  have h6 : ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
    intro t ht
    have hdom : (fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨
        (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨
        ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true := by
      rcases PEqualNP.Outside.L_meta_1570.zero_one_not_both t ht with h | h
      · left
        simp only [decide_eq_true_eq]
        rw [hL]
        exact h
      · right
        left
        simp only [decide_eq_true_eq]
        rw [hL]
        exact h
    rw [hout 0 (fun v : Fin 13 => decide (v ∉ L t)) hdom]
    obtain ⟨v, hv, hvt⟩ := PEqualNP.Outside.L_meta_1570.line_zero_not_sub t ht
    apply decide_eq_true
    refine ⟨v, ?_, ?_⟩
    · rw [hL0]
      exact hv
    · simp only [decide_eq_true_eq]
      rw [hL]
      exact hvt
  have hlt : o 0 < 13 + gates.length := by
    by_contra hcon
    have hle : 13 + gates.length ≤ o 0 := by omega
    have e := PEqualNP.Outside.L_meta_1570.eval_out gates (o 0)
      (fun v : Fin 13 => decide (v = 0)) hle
    rw [h3] at e
    exact absurd e (by decide)
  have hge : 13 ≤ o 0 := by
    by_contra hcon
    have hlt13 : o 0 < 13 := by omega
    have e0 : (fun v : Fin 13 => decide (v = 0)) ⟨o 0, hlt13⟩ = true :=
      (PEqualNP.Outside.L_meta_1570.eval_input gates (o 0) _ hlt13).symm.trans h3
    have e1 : (fun v : Fin 13 => decide (v = 1)) ⟨o 0, hlt13⟩ = true :=
      (PEqualNP.Outside.L_meta_1570.eval_input gates (o 0) _ hlt13).symm.trans h4
    have a0 : (⟨o 0, hlt13⟩ : Fin 13) = 0 := of_decide_eq_true e0
    have a1 : (⟨o 0, hlt13⟩ : Fin 13) = 1 := of_decide_eq_true e1
    rw [a0] at a1
    exact absurd a1 (by decide)
  exact ⟨hge, hlt, h3, h4, h5, h6⟩
