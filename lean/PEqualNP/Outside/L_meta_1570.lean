import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem eval_input (gs : List Gate) (o : ℕ) (x : Fin 13 → Bool) (h : o < 13) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = x ⟨o, h⟩ := by
  unfold Circuit.eval
  rw [wires_eq, getD_wiresFrom _ _ _ (by simpa using h)]
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

theorem eval_big (gs : List Gate) (o : ℕ) (x : Fin 13 → Bool) (h : 13 + gs.length ≤ o) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = false := by
  unfold Circuit.eval
  rw [wires_eq]
  apply List.getD_eq_default
  rw [length_wiresFrom]
  simpa using h

def Lt (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

theorem cond_off : ∀ t : Fin 13, t ≠ 0 →
    (decide ((0 : Fin 13) ∉ Lt t) = true ∨ decide ((1 : Fin 13) ∉ Lt t) = true) := by
  decide

theorem meets_off : ∀ t : Fin 13, t ≠ 0 →
    decide (∃ v ∈ Lt 0, decide (v ∉ Lt t) = true) = true := by
  decide

end PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ hev
  have hLe : L = PEqualNP.Outside.L_meta_1570.Lt := funext hL
  subst hLe
  have h0 := hev 0 (fun v => decide (v = 0)) (Or.inl (by decide))
  have h1 := hev 0 (fun v => decide (v = 1)) (Or.inr (Or.inl (by decide)))
  have hc := hev 0 (fun v => decide (v ∉ PEqualNP.Outside.L_meta_1570.Lt 0))
    (Or.inr (Or.inr (fun v hv => by simpa using hv)))
  have r0 : decide (∃ v ∈ PEqualNP.Outside.L_meta_1570.Lt 0, decide (v = 0) = true) = true := by
    decide
  have r1 : decide (∃ v ∈ PEqualNP.Outside.L_meta_1570.Lt 0, decide (v = 1) = true) = true := by
    decide
  have rc : decide (∃ v ∈ PEqualNP.Outside.L_meta_1570.Lt 0,
      decide (v ∉ PEqualNP.Outside.L_meta_1570.Lt 0) = true) = false := by
    decide
  rw [r0] at h0
  rw [r1] at h1
  rw [rc] at hc
  have hlo : 13 ≤ o 0 := by
    by_contra hlt
    rw [not_le] at hlt
    rw [PEqualNP.Outside.L_meta_1570.eval_input _ _ _ hlt] at h0 h1
    simp [Fin.ext_iff] at h0 h1
    omega
  have hhi : o 0 < 13 + gates.length := by
    by_contra hge
    rw [not_lt] at hge
    rw [PEqualNP.Outside.L_meta_1570.eval_big _ _ _ hge] at h0
    exact Bool.false_ne_true h0
  refine ⟨hlo, hhi, h0, h1, hc, ?_⟩
  intro t ht
  have h := hev 0 (fun v => decide (v ∉ PEqualNP.Outside.L_meta_1570.Lt t))
    (by
      rcases PEqualNP.Outside.L_meta_1570.cond_off t ht with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
  rw [h]
  exact PEqualNP.Outside.L_meta_1570.meets_off t ht
