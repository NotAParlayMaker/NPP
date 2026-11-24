import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1598_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

private def step {α β : Type} (f : List α → β → α) (s : List α) (g : β) : List α :=
  s ++ [f s g]

private theorem trace_length {α β : Type} (f : List α → β → α) (gs : List β) (s : List α) :
    (gs.foldl (step f) s).length = s.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

private theorem trace_preserve {α β : Type} (f : List α → β → α) (gs : List β)
    (s : List α) (i : ℕ) (d : α) (hi : i < s.length) :
    (gs.foldl (step f) s).getD i d = s.getD i d := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step f s g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem trace_take {α β : Type} (f : List α → β → α) (gs : List β)
    (s : List α) (j i : ℕ) (d : α) (hi : i < s.length + (gs.take j).length) :
    (gs.foldl (step f) s).getD i d = ((gs.take j).foldl (step f) s).getD i d := by
  have eq := trace_preserve f (gs.drop j) ((gs.take j).foldl (step f) s) i d
    (by rwa [trace_length])
  rwa [← List.foldl_append, List.take_append_drop] at eq

private theorem trace_gate {α β : Type} (f : List α → β → α) (gs : List β)
    (s : List α) (j : ℕ) (d : α) (hj : j < gs.length) :
    (gs.foldl (step f) s).getD (s.length + j) d =
      f ((gs.take j).foldl (step f) s) gs[j] := by
  let prior := (gs.take j).foldl (step f) s
  have hp : prior.length = s.length + j := by simp [prior, trace_length, Nat.min_eq_left (by omega : j ≤ gs.length)]
  have ht := trace_take f gs s (j + 1) (s.length + j) d (by
    simp only [List.length_take, Nat.min_eq_left (by omega : j + 1 ≤ gs.length)]
    omega)
  rw [ht, ← List.take_concat_get hj, List.concat_eq_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  change (step f prior gs[j]).getD (s.length + j) d = f prior gs[j]
  rw [← hp]
  simp [step]

private def wireStep (s : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => s.getD i false)

private theorem input_value (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  change (C.gates.foldl (step wireStep) (List.ofFn x)).getD i false = _
  rw [trace_preserve _ _ _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private theorem value_oob (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : wireVal n C i x = false := by
  change (C.gates.foldl (step wireStep) (List.ofFn x)).getD i false = false
  exact List.getD_eq_default _ _ (by simpa [trace_length] using hi)

private theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  exact List.getD_eq_getElem _ _ hj

private theorem gate_value (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    wireVal n C (n + j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => if i < n + j then wireVal n C i x else false) := by
  let w := List.ofFn x
  have hw : w.length = n := List.length_ofFn
  have ht := trace_gate wireStep C.gates w j false hj
  rw [hw] at ht
  change (C.gates.foldl (step wireStep) w).getD (n + j) false = _
  rw [ht, gateAt_eq C j hj]
  unfold wireStep
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((C.gates.take j).foldl (step wireStep) w).length = n + j := by
    simp [trace_length, hw, Nat.min_eq_left (by omega : j ≤ C.gates.length)]
  by_cases hi : i < n + j
  · rw [ite_eq_left hi]
    have ht' : i < w.length + (C.gates.take j).length := by
      rwa [hw, List.length_take, Nat.min_eq_left (by omega : j ≤ C.gates.length)]
    exact (trace_take wireStep C.gates w j i false ht').symm
  · rw [ite_eq_right hi]
    exact List.getD_eq_default _ _ (hlen.le.trans (Nat.le_of_not_lt hi))

private def closureStep (n : ℕ) (s : List (List ℕ)) (g : Gate) : List ℕ := by
  letI := gateOpDecEq
  exact s.length :: (if g.op = GateOp.or then
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + s.length))).flatMap
      (fun w => s.getD (w - n) []) else [])

private theorem closure_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  refine ⟨by omega, ?_⟩
  have ht := trace_gate (closureStep n) C.gates [] j [] hj
  simp only [List.length_nil, Nat.zero_add] at ht
  change j ∈ (C.gates.foldl (step (closureStep n)) []).getD (n + j - n) []
  rw [Nat.add_sub_cancel_left, ht]
  simp [closureStep, trace_length, Nat.min_eq_left (by omega : j ≤ C.gates.length)]

private theorem closure_inherit (n : ℕ) (C : Circuit) (j v g : ℕ) (hj : j < C.gates.length)
    (ho : (gateAt C j).op = GateOp.or) (hv : v ∈ (gateAt C j).inputs)
    (hlt : v < n + j) (hg : OrReaches n C v g) : OrReaches n C (n + j) g := by
  refine ⟨by omega, ?_⟩
  rw [gateAt_eq C j hj] at ho hv
  have ht := trace_gate (closureStep n) C.gates [] j [] hj
  simp only [List.length_nil, Nat.zero_add] at ht
  change g ∈ (C.gates.foldl (step (closureStep n)) []).getD (n + j - n) []
  rw [Nat.add_sub_cancel_left, ht]
  unfold closureStep
  rw [ite_eq_left ho]
  apply List.mem_cons.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨v, List.mem_filter.mpr ⟨hv, ?_⟩, ?_⟩
  · apply decide_eq_true_eq.mpr
    exact ⟨hg.1, by
      simpa [trace_length, Nat.min_eq_left (by omega : j ≤ C.gates.length)] using hlt⟩
  · have hv' : v - n < ([] : List (List ℕ)).length + (C.gates.take j).length := by
      simp only [List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (by omega : j ≤ C.gates.length)]
      have := hg.1
      omega
    change g ∈ ((C.gates.take j).foldl (step (closureStep n)) []).getD (v - n) []
    rw [← trace_take (closureStep n) C.gates [] j (v - n) [] hv']
    exact hg.2

theorem singleton (n : ℕ) (C : Circuit) (hC : AndOrOnly C) (U : Finset (Fin n)) (w : ℕ)
    (hw : wireVal n C w (fun k : Fin n => decide (k ∈ U)) = true)
    (hAnd : ∀ g, OrReaches n C w g → (gateAt C g).op = GateOp.and →
      gateVal n C g (fun k : Fin n => decide (k ∈ U)) = false) :
    ∃ i ∈ U, wireVal n C w (fun k : Fin n => decide (k = i)) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlow : w < n
    · let i : Fin n := ⟨w, hlow⟩
      refine ⟨i, ?_, ?_⟩
      · rw [input_value n C _ w hlow] at hw
        exact of_decide_eq_true hw
      · rw [input_value n C _ w hlow]
        exact decide_eq_true rfl
    · let j := w - n
      have hwa : w = n + j := by omega
      have hj : j < C.gates.length := by
        by_contra h
        rw [value_oob n C _ w (by omega)] at hw
        cases hw
      have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
        apply hC
        rw [gateAt_eq C j hj]
        exact List.getElem_mem hj
      rcases hop with ha | ho
      · have hfalse := hAnd j (hwa ▸ closure_self n C j hj) ha
        change wireVal n C (n + j) _ = false at hfalse
        rw [hwa] at hw
        rw [hfalse] at hw
        cases hw
      · have hv := hw
        rw [hwa, gate_value n C _ j hj, ho] at hv
        simp only [GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true] at hv
        obtain ⟨v, hvin, hvv⟩ := hv
        split at hvv
        next hlt =>
          obtain ⟨i, hi, hiw⟩ := ih v (by omega) hvv (fun g hg ha =>
            hAnd g (hwa ▸ closure_inherit n C j v g hj ho hvin hlt hg) ha)
          refine ⟨i, hi, ?_⟩
          rw [hwa, gate_value n C _ j hj, ho]
          simp only [GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
          exact ⟨v, hvin, by simpa only [ite_eq_left hlt] using hiw⟩
        next _ => cases hvv

end PEqualNP.Outside.L_meta_1598_aux

theorem PEqualNP.Outside.L_meta_1598 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → ∀ (U : Finset (Fin n)) (w : ℕ), PEqualNP.CleanedNonEdge.wireVal n C w (fun k : Fin n => decide (k ∈ U)) = true → (∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal n C g (fun l : Fin n => decide (l ∈ U)) = false) → ∃ i ∈ U, PEqualNP.CleanedNonEdge.wireVal n C w (fun r : Fin n => decide (r = i)) = true := by
  exact PEqualNP.Outside.L_meta_1598_aux.singleton
