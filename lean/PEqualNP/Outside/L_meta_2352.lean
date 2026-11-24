import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2352

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma foldl_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma wire_before (gs : List Gate) (x : List Bool) (j i : ℕ) (hi : i < x.length + j)
    (hj : j ≤ gs.length) :
    ((gs.take j).foldl step x).getD i false = (gs.foldl step x).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, List.foldl_append]
  rw [foldl_prefix (gs.drop j) _ i (by rw [foldl_length, List.length_take]; omega)]

lemma wire_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step x).getD i false) := by
  have e : gs.foldl step x = (gs.drop j).foldl step ((gs.take j).foldl step x) := by
    rw [← List.foldl_append, List.take_append_drop]
  have d : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
  rw [e, d, List.foldl_cons]
  have hl : ((gs.take j).foldl step x).length = x.length + j := by
    rw [foldl_length, List.length_take]
    omega
  rw [foldl_prefix _ _ _ (by simp [step, hl])]
  simp only [step, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hl]
  simp

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]

lemma or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a rj : ℕ) (hrj : rj < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = GateOp.or)
    (hin : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) (hlt : a < n + rj)
    (ha : (C.wires (List.ofFn z)).getD a false = true) :
    (C.wires (List.ofFn z)).getD (n + rj) false = true := by
  rw [gateAt_eq C rj hrj] at hop hin
  rw [wires_eq] at ha ⊢
  have hx : (List.ofFn z).length = n := List.length_ofFn
  have hw := wire_gate C.gates (List.ofFn z) rj hrj
  rw [hx] at hw
  rw [hw, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  refine ⟨a, hin, ?_⟩
  rw [wire_before C.gates (List.ofFn z) rj a (by rw [hx]; exact hlt) hrj.le]
  exact ha

lemma and_up (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (z : Fin n → Bool)
    (qj : ℕ) (hqj : qj < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = GateOp.and)
    (h0 : (C.wires (List.ofFn z)).getD
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) false = true)
    (h1 : (C.wires (List.ofFn z)).getD
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) false = true) :
    (C.wires (List.ofFn z)).getD (n + qj) false = true := by
  obtain ⟨_, hrb, hlen⟩ := hC
  have hback := hrb qj hqj
  rw [gateAt_eq C qj hqj] at hop h0 h1 hback
  have h2 : C.gates[qj].inputs.length = 2 := hlen _ (List.getElem_mem hqj)
  rw [wires_eq] at h0 h1 ⊢
  have hx : (List.ofFn z).length = n := List.length_ofFn
  have hw := wire_gate C.gates (List.ofFn z) qj hqj
  rw [hx] at hw
  rw [hw, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  intro i hi
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
  have hilt := hback _ hi
  rw [wire_before C.gates (List.ofFn z) qj _ (by rw [hx]; exact hilt) hqj.le]
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with rfl | rfl
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using h0
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using h1

end PEqualNP.Outside.L_meta_2352

theorem PEqualNP.Outside.L_meta_2352 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List (ℕ × ℕ)) (z : Fin n → Bool), T top L → (∀ gv ∈ L, (C.wires (List.ofFn z)).getD (gv.1) false = true) → (C.wires (List.ofFn z)).getD (top) false = true := by
  intro n C hC R hR T hT top L z hTL hL
  have hRup : ∀ a b, R a b → (C.wires (List.ofFn z)).getD a false = true →
      (C.wires (List.ofFn z)).getD b false = true := by
    intro a b hab
    subst hR
    induction hab with
    | refl => exact id
    | tail _ hbc ih =>
      intro ha
      obtain ⟨hlt, rj, rfl, hrj, hop, hin⟩ := hbc
      exact PEqualNP.Outside.L_meta_2352.or_up n C z _ rj hrj hop hin hlt (ih ha)
  subst hT
  have key := hTL (fun t l => (∀ gv ∈ l, (C.wires (List.ofFn z)).getD gv.1 false = true) →
      (C.wires (List.ofFn z)).getD t false = true)
    (fun qv qt _ _ h => h (qt, qv) (by simp))
    (fun qj qt qL1 qL2 hqj hop hR' ih1 ih2 h =>
      hRup _ _ hR' (PEqualNP.Outside.L_meta_2352.and_up n C hC z qj hqj hop
        (ih1 fun gv hg => h gv (List.mem_append_left _ hg))
        (ih2 fun gv hg => h gv (List.mem_append_right _ hg))))
  exact key hL
