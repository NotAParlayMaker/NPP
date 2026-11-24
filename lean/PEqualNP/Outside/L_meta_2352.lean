import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2352_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (w : List Bool) : C.wires w = C.gates.foldl step w := rfl

theorem foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp [step, List.getD, List.getElem?_append_left hi]

theorem step_getD_last (W : List Bool) (g : Gate) :
    (step W g).getD W.length false = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  unfold step
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ (gs[j]).inputs, i < w.length + j) :
    (gs.foldl step w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (gs.foldl step w).getD i false) := by
  have hWlen : ((gs.take j).foldl step w).length = w.length + j := by
    rw [foldl_step_length, List.length_take]
    omega
  have hfull : gs.foldl step w = (gs.drop (j + 1)).foldl step (step ((gs.take j).foldl step w) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [List.foldl_append, List.foldl_cons]
  have hget : ∀ i < w.length + j, (gs.foldl step w).getD i false = ((gs.take j).foldl step w).getD i false := by
    intro i hi
    rw [hfull, foldl_step_getD_lt _ _ _ (by simp [step]; omega)]
    simp only [step, List.getD]
    rw [List.getElem?_append_left (by omega)]
  have hL : (gs.foldl step w).getD (w.length + j) false =
      (step ((gs.take j).foldl step w) gs[j]).getD (w.length + j) false := by
    rw [hfull, foldl_step_getD_lt _ _ _ (by simp [step]; omega)]
  have hv := step_getD_last ((gs.take j).foldl step w) gs[j]
  rw [hWlen] at hv
  rw [hL, hv]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [hget i (hin i hi)]

theorem wire_gate (n : ℕ) (C : Circuit) (z : List Bool) (hz : z.length = n) (j : ℕ)
    (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, i < n + j) :
    (C.wires z).getD (n + j) false = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map
        fun i => (C.wires z).getD i false) := by
  have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD, hj]
  rw [hg] at hrb ⊢
  rw [wires_eq]
  subst hz
  exact foldl_step_gate C.gates z j hj hrb

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
  have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD, hj]
  rw [hg]
  exact List.getElem_mem hj

end PEqualNP.Outside.L_meta_2352_aux

theorem PEqualNP.Outside.L_meta_2352 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List (ℕ × ℕ)) (z : Fin n → Bool), T top L → (∀ gv ∈ L, (C.wires (List.ofFn z)).getD (gv.1) false = true) → (C.wires (List.ofFn z)).getD (top) false = true := by
  intro n C hC R hR T hT top L z hTL hL
  subst hR
  subst hT
  obtain ⟨-, hrb, hlen⟩ := hC
  have hz : (List.ofFn z).length = n := List.length_ofFn
  have hmono : ∀ a b, Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧
      rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) a b →
      (C.wires (List.ofFn z)).getD a false = true → (C.wires (List.ofFn z)).getD b false = true := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hbc ih =>
      obtain ⟨-, rj, rfl, hrj, hor, hmem⟩ := hbc
      rw [PEqualNP.Outside.L_meta_2352_aux.wire_gate n C _ hz rj hrj (hrb rj hrj), hor]
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id]
      exact ⟨_, hmem, ih⟩
  refine hTL (fun t L => (∀ gv ∈ L, (C.wires (List.ofFn z)).getD gv.1 false = true) →
    (C.wires (List.ofFn z)).getD t false = true) ?_ ?_ hL
  · intro qv qt _ _ h
    exact h (qt, qv) (List.mem_singleton_self _)
  · intro qj qt L1 L2 hqj hand hR h1 h2 h
    have v1 := h1 (fun gv hgv => h gv (List.mem_append_left _ hgv))
    have v2 := h2 (fun gv hgv => h gv (List.mem_append_right _ hgv))
    apply hmono _ _ hR
    rw [PEqualNP.Outside.L_meta_2352_aux.wire_gate n C _ hz qj hqj (hrb qj hqj), hand]
    have h2len := hlen _ (PEqualNP.Outside.L_meta_2352_aux.gateAt_mem C qj hqj)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2len
    rw [hab] at v1 v2 ⊢
    simp only [List.getD_cons_zero, List.getD_cons_succ] at v1 v2
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, v1, v2, Bool.and_self]
