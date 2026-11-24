import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_2352

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma length_fold (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma getD_fold (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (step w g) i (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma gate_wire (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ i ∈ gs[j].inputs, i < w.length + j) :
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl step w).getD i false) := by
  have hWlen : ((gs.take j).foldl step w).length = w.length + j := by
    rw [length_fold, List.length_take]
    omega
  have hfull : gs.foldl step w =
      (gs.drop (j + 1)).foldl step (step ((gs.take j).foldl step w) gs[j]) := by
    rw [← List.foldl_cons, ← List.foldl_append, ← List.drop_eq_getElem_cons hj,
      List.take_append_drop]
  have hpre : ∀ i, i < w.length + j →
      (gs.foldl step w).getD i false = ((gs.take j).foldl step w).getD i false := by
    intro i hi
    rw [hfull, getD_fold _ _ _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega : i < ((gs.take j).foldl step w).length)]
  have hat : (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step w).getD i false) := by
    rw [hfull, getD_fold _ _ _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, ← hWlen]
  rw [hat]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hpre i (hback i hi)).symm

lemma wire_gate (n : ℕ) (C : Circuit) (hback : ReadsBack n C) (z : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    (C.wires (List.ofFn z)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (C.wires (List.ofFn z)).getD i false) := by
  have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have h := gate_wire C.gates (List.ofFn z) j hj (by
    intro i hi
    rw [List.length_ofFn]
    exact hback j hj i (hg ▸ hi))
  rw [List.length_ofFn] at h
  rw [hg]
  exact h

end PEqualNP.Outside.L_meta_2352

theorem PEqualNP.Outside.L_meta_2352 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List (ℕ × ℕ)) (z : Fin n → Bool), T top L → (∀ gv ∈ L, (C.wires (List.ofFn z)).getD (gv.1) false = true) → (C.wires (List.ofFn z)).getD (top) false = true := by
  intro n C hC R hR T hT top L z hTL hL
  subst hR
  subst hT
  obtain ⟨_, hback, htwo⟩ := hC
  have orUp : ∀ a b, Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧
      rj < C.gates.length ∧ (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b →
      (C.wires (List.ofFn z)).getD a false = true →
      (C.wires (List.ofFn z)).getD b false = true := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hbc ih =>
      obtain ⟨_, rj, rfl, hrj, hop, hmem⟩ := hbc
      rw [PEqualNP.Outside.L_meta_2352.wire_gate n C hback z rj hrj, hop]
      simp only [GateOp.eval, List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨_, hmem, ih⟩, rfl⟩
  refine hTL (fun t L => (∀ gv ∈ L, (C.wires (List.ofFn z)).getD gv.1 false = true) →
    (C.wires (List.ofFn z)).getD t false = true) ?_ ?_ hL
  · intro v t _ _ h
    exact h (t, v) (by simp)
  · intro j t L1 L2 hj hop hRt ih1 ih2 h
    apply orUp _ _ hRt
    have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    have hlen : (gateAt C j).inputs.length = 2 := by
      rw [hg]
      exact htwo _ (List.getElem_mem hj)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have h1 := ih1 (fun gv hgv => h gv (List.mem_append_left _ hgv))
    have h2 := ih2 (fun gv hgv => h gv (List.mem_append_right _ hgv))
    rw [PEqualNP.Outside.L_meta_2352.wire_gate n C hback z j hj, hop]
    rw [hab] at h1 h2 ⊢
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2
    rw [List.getD_eq_getElem?_getD] at h1 h2
    simp [GateOp.eval, h1, h2]
