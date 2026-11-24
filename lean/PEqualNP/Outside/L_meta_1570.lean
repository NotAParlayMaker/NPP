import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570_aux

open PEqualNP.CircuitLowerBounds

/-- One gate applied to a wire list: append its value. -/
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons, step]
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

private lemma getD_append_single {w : List Bool} {b : Bool} {i : ℕ} (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons]
      have hp : i < (step w g).length := by
        rw [step, List.length_append]
        simp only [List.length_cons, List.length_nil]
        omega
      rw [ih (step w g) hp]
      simpa only [step] using getD_append_single hi

private lemma wires_length (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length := by
  show (gs.foldl step x).length = _
  exact foldl_step_length gs x

private lemma wires_getD_input (gs : List Gate) (o : ℕ) (x : List Bool) (i : ℕ)
    (hi : i < x.length) :
    (Circuit.wires ⟨gs, o⟩ x).getD i false = x.getD i false := by
  show (gs.foldl step x).getD i false = _
  exact foldl_step_getD gs x i hi

private lemma wires_getD_oob (gs : List Gate) (o : ℕ) (x : List Bool) (i : ℕ)
    (hi : x.length + gs.length ≤ i) :
    (Circuit.wires ⟨gs, o⟩ x).getD i false = false := by
  have hlen := wires_length gs o x
  rw [← hlen] at hi
  exact List.getD_eq_default (l := Circuit.wires ⟨gs, o⟩ x) (d := false) hi

private lemma ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

end PEqualNP.Outside.L_meta_1570_aux

open PEqualNP.Outside.L_meta_1570_aux

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o hg hlen hfun
  -- evaluation at the unit inputs and at the complements of the lines
  have eval_e0 :
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
        (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    rw [hfun 0 (fun v : Fin 13 => decide (v = 0)) (Or.inl rfl)]
    rw [hL 0]
    decide
  have eval_e1 :
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
        (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    rw [hfun 0 (fun v : Fin 13 => decide (v = 1)) (Or.inr (Or.inl rfl))]
    rw [hL 0]
    decide
  have eval_not0 :
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
        (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false := by
    rw [hfun 0 (fun v : Fin 13 => decide (v ∉ L 0))
      (Or.inr (Or.inr (by intro v hv; exact decide_eq_true_eq.mpr hv)))]
    rw [hL 0]
    decide
  -- the output wire is a gate, not an input wire
  have ho_ge : 13 ≤ o 0 := by
    by_contra hlt
    push_neg at hlt
    have hwire :
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, o 0⟩
            (List.ofFn (fun v : Fin 13 => decide (v = 0)))).getD (o 0) false
          = (fun v : Fin 13 => decide (v = 0)) ⟨o 0, hlt⟩ := by
      rw [wires_getD_input gates (o 0) _ (o 0) (by simpa using hlt)]
      exact ofFn_getD _ (o 0) hlt
    have hdec : decide ((⟨o 0, hlt⟩ : Fin 13) = 0) = true := by
      have h := eval_e0
      rw [PEqualNP.CircuitLowerBounds.Circuit.eval, hwire] at h
      exact h
    have ho0 : o 0 = 0 := by
      have h := of_decide_eq_true hdec
      simpa using h
    have hwire1 :
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, o 0⟩
            (List.ofFn (fun v : Fin 13 => decide (v = 1)))).getD (o 0) false = false := by
      rw [ho0]
      rw [wires_getD_input gates 0 _ 0 (by simp)]
      rw [ofFn_getD (fun v : Fin 13 => decide (v = 1)) 0 (by norm_num)]
      decide
    have hfalse :
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
          (List.ofFn (fun v : Fin 13 => decide (v = 1))) = false := by
      rw [PEqualNP.CircuitLowerBounds.Circuit.eval, hwire1]
    rw [hfalse] at eval_e1
    exact Bool.false_ne_true eval_e1
  -- the output wire exists
  have ho_lt : o 0 < 13 + gates.length := by
    by_contra hle
    push_neg at hle
    have hval :
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, o 0⟩
            (List.ofFn (fun v : Fin 13 => decide (v = 0)))).getD (o 0) false = false := by
      apply wires_getD_oob
      simpa using hle
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval, hval] at eval_e0
    exact Bool.false_ne_true eval_e0
  -- for the other lines, the complement input satisfies the promise and hits line zero
  have key : ∀ t : Fin 13, t ≠ 0 →
      (0 ∉ L t ∨ 1 ∉ L t) ∧ (∃ v ∈ L 0, v ∉ L t) := by
    intro t ht
    have hLt := hL t
    fin_cases t
    · exact absurd rfl ht
    all_goals
      rw [hL 0, hLt]
      decide
  refine ⟨ho_ge, ho_lt, eval_e0, eval_e1, eval_not0, ?_⟩
  intro t ht
  obtain ⟨h01, hlt⟩ := key t ht
  have hprom :
      (fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨
        (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨
        ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true := by
    rcases h01 with h0 | h1
    · exact Or.inl (decide_eq_true_eq.mpr h0)
    · exact Or.inr (Or.inl (decide_eq_true_eq.mpr h1))
  rw [hfun 0 (fun v : Fin 13 => decide (v ∉ L t)) hprom, decide_eq_true_eq]
  obtain ⟨v, hv0, hvt⟩ := hlt
  exact ⟨v, hv0, decide_eq_true_eq.mpr hvt⟩

