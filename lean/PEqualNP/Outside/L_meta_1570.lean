import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem val_eval (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) :
    val gates w x = Circuit.eval ⟨gates, w⟩ (List.ofFn x) := rfl

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def lines (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma geom : (0 : Fin 13) ∈ lines 0 ∧ (1 : Fin 13) ∈ lines 0 ∧
    (∀ t : Fin 13, t ≠ 0 → ((0 : Fin 13) ∉ lines t ∨ (1 : Fin 13) ∉ lines t)) ∧
    (∀ t : Fin 13, t ≠ 0 → ∃ v : Fin 13, v ∈ lines 0 ∧ v ∉ lines t) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o hleg hconn hcomp
  have hLeq : L = lines := funext hL
  subst L
  obtain ⟨h0, h1, hsep, hdiff⟩ := geom
  have key : ∀ (t : Fin 13) (x : Fin 13 → Bool),
      (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ lines 0 → x v = true) →
      val gates (o t) x = decide (∃ v ∈ lines t, x v = true) := by
    intro t x hx
    rw [val_eval]
    exact hcomp t x hx
  have hC : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    have hk := key 0 (fun v : Fin 13 => decide (v = 0)) (Or.inl (by simp))
    rw [← val_eval, hk]
    exact decide_eq_true ⟨0, h0, by simp⟩
  have hD : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    have hk := key 0 (fun v : Fin 13 => decide (v = 1)) (Or.inr (Or.inl (by simp)))
    rw [← val_eval, hk]
    exact decide_eq_true ⟨1, h1, by simp⟩
  have hE : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ lines 0))) = false := by
    have hk := key 0 (fun v : Fin 13 => decide (v ∉ lines 0))
      (Or.inr (Or.inr (fun v hv => decide_eq_true hv)))
    rw [← val_eval, hk, decide_eq_false_iff_not]
    rintro ⟨v, hv, hd⟩
    exact (of_decide_eq_true hd) hv
  have hF : ∀ t : Fin 13, t ≠ 0 →
      Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ lines t))) = true := by
    intro t ht
    have hk := key 0 (fun v : Fin 13 => decide (v ∉ lines t))
      (by
        rcases hsep t ht with h | h
        · exact Or.inl (decide_eq_true h)
        · exact Or.inr (Or.inl (decide_eq_true h)))
    rw [← val_eval, hk]
    obtain ⟨v, hv0, hvt⟩ := hdiff t ht
    exact decide_eq_true ⟨v, hv0, decide_eq_true hvt⟩
  have hA : 13 ≤ o 0 := by
    by_contra hcon
    have hlt : o 0 < 13 := by omega
    have h1' := hC
    have h2' := hD
    rw [← val_eval, val_input gates (fun v : Fin 13 => decide (v = 0)) (o 0) hlt] at h1'
    rw [← val_eval, val_input gates (fun v : Fin 13 => decide (v = 1)) (o 0) hlt] at h2'
    have e1 : (⟨o 0, hlt⟩ : Fin 13) = 0 := of_decide_eq_true h1'
    have e2 : (⟨o 0, hlt⟩ : Fin 13) = 1 := of_decide_eq_true h2'
    exact absurd (e1.symm.trans e2) (by decide)
  have hB : o 0 < 13 + gates.length := by
    by_contra hcon
    have hbig : 13 + gates.length ≤ o 0 := by omega
    have h1' := hC
    rw [← val_eval, val_big gates (fun v : Fin 13 => decide (v = 0)) (o 0) hbig] at h1'
    exact absurd h1' (by decide)
  exact ⟨hA, hB, hC, hD, hE, hF⟩
