import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection

namespace PEqualNP.Outside.L_meta_2780_aux

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

private theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp
    omega

private theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem run_append (l1 l2 : List Gate) (w : List Bool) :
    run (l1 ++ l2) w = run l2 (run l1 w) := by
  induction l1 generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.cons_append, run_cons, run_cons, ih]

private theorem run_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (run (gs.take j) w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      rw [run_cons, run_preserves _ _ _ (by simp)]
      simp [run, Circuit.wires]
    | succ j =>
      rw [run_cons]
      have hj' : j < gs.length := by simpa using hj
      have h := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) j hj'
      have hl : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length + j
          = w.length + (j + 1) := by simp; omega
      rw [hl] at h
      rw [h]
      simp [List.take_succ_cons, run_cons]

private theorem wv_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    wireValue C x i = x.getD i false :=
  run_preserves C.gates x i hi

private theorem wv_beyond (C : Circuit) (x : List Bool) (i : ℕ)
    (hi : x.length + C.gates.length ≤ i) : wireValue C x i = false := by
  show (run C.gates x).getD i false = false
  apply List.getD_eq_default
  rw [run_length]
  exact hi

private theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

private theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]
  exact List.getElem_mem hj

private theorem wv_gate (C : Circuit) (x : List Bool) (N j : ℕ) (hN : x.length = N)
    (hj : j < C.gates.length) (hin : ∀ i ∈ (gateAt C j).inputs, i < N + j) :
    wireValue C x (N + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireValue C x i) := by
  show (run C.gates x).getD (N + j) false = _
  rw [← hN, run_gate C.gates x j hj, ← gateAt_eq C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := hin i hi
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  show _ = (run C.gates x).getD i false
  conv_rhs => rw [hsplit, run_append]
  exact (run_preserves _ _ _ (by rw [run_length, List.length_take]; omega)).symm

private theorem mono (N : ℕ) (C : Circuit) (hC : AndOrOnly C) (hR : ReadsBack N C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ w, wireValue C x w = true → wireValue C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases h1 : w < N
  · rw [wv_input C y w (by omega)]
    rw [wv_input C x w (by omega)] at hw
    exact hxy w hw
  by_cases h2 : w < N + C.gates.length
  · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    have hin := hR j hj
    rw [wv_gate C x N j hx hj hin] at hw
    rw [wv_gate C y N j hy hj hin]
    rcases hC _ (gateAt_mem C j hj) with hop | hop
    · rw [hop] at hw ⊢
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hw ⊢
      rintro b ⟨i, hi, rfl⟩
      exact ih i (by have := hin i hi; omega) (hw _ ⟨i, hi, rfl⟩)
    · rw [hop] at hw ⊢
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hw ⊢
      obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hw
      exact ⟨_, ⟨i, hi, rfl⟩, ih i (by have := hin i hi; omega) hb⟩
  · rw [wv_beyond C x w (by omega)] at hw
    exact absurd hw (by simp)

private theorem rep_getD (N i : ℕ) (b : Bool) : (List.replicate N b).getD i false =
    (decide (i < N) && b) := by
  by_cases h : i < N
  · rw [List.getD_replicate _ h]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

private theorem allfalse (N : ℕ) (C : Circuit) (hC : AndOrOnly C) (hR : ReadsBack N C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ w, wireValue C (List.replicate N false) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  by_cases h1 : w < N
  · rw [wv_input C _ w (by simp; omega), rep_getD]
    simp
  by_cases hb : w < N + C.gates.length
  · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    have hin := hR j hj
    rw [wv_gate C _ N j (by simp) hj hin]
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem C j hj))
    have hp : p < N + j := hin p (by rw [hpq]; simp)
    have hq : q < N + j := hin q (by rw [hpq]; simp)
    simp only [hpq, List.map_cons, List.map_nil, ih p hp, ih q hq]
    rcases hC _ (gateAt_mem C j hj) with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
  · exact wv_beyond C _ w (by simp; omega)

private theorem alltrue (N : ℕ) (C : Circuit) (hC : AndOrOnly C) (hR : ReadsBack N C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ w, w < N + C.gates.length → wireValue C (List.replicate N true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hb
  by_cases h1 : w < N
  · rw [wv_input C _ w (by simp; omega), rep_getD]
    simp [h1]
  · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    have hin := hR j hj
    rw [wv_gate C _ N j (by simp) hj hin]
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem C j hj))
    have hp : p < N + j := hin p (by rw [hpq]; simp)
    have hq : q < N + j := hin q (by rw [hpq]; simp)
    simp only [hpq, List.map_cons, List.map_nil, ih p hp (by omega), ih q hq (by omega)]
    rcases hC _ (gateAt_mem C j hj) with hop | hop <;> rw [hop] <;> simp [GateOp.eval]

private theorem le_app_left (a l1 l2 : List Bool)
    (h : ∀ i, l1.getD i false = true → l2.getD i false = true) :
    ∀ i, (a ++ l1).getD i false = true → (a ++ l2).getD i false = true := by
  intro i hi
  by_cases hl : i < a.length
  · rw [List.getD_append _ _ _ _ hl] at hi ⊢
    exact hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    exact h _ hi

private theorem le_app_right (a l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (h : ∀ i, l1.getD i false = true → l2.getD i false = true) :
    ∀ i, (l1 ++ a).getD i false = true → (l2 ++ a).getD i false = true := by
  intro i hi
  by_cases hl : i < l1.length
  · rw [List.getD_append _ _ _ _ hl] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h _ hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
    exact hi

private theorem le_false (N : ℕ) (l : List Bool) :
    ∀ i, (List.replicate N false).getD i false = true → l.getD i false = true := by
  intro i hi
  rw [rep_getD] at hi
  simp at hi

private theorem le_true (N : ℕ) (l : List Bool) (hl : l.length = N) :
    ∀ i, l.getD i false = true → (List.replicate N true).getD i false = true := by
  intro i hi
  rw [rep_getD]
  by_cases h : i < N
  · simp [h]
  · rw [List.getD_eq_default _ _ (by omega)] at hi
    exact absurd hi (by simp)

private theorem sandwich (a b c : Bool) (h1 : a = true → b = true) (h2 : b = true → c = true)
    (h3 : a = c) : b = a := by
  subst h3
  cases a <;> cases b <;> simp_all

end PEqualNP.Outside.L_meta_2780_aux

open PEqualNP.Outside.L_meta_2780_aux

theorem PEqualNP.Outside.L_meta_2780 :
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.false) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.true) x4) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.false ++ List.ofFn x6) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.true ++ List.ofFn x6) x4); ∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x2 + x2) x3 → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 → x1 x2 x3 x7 → x6 ∈ x4) → ∀ x7 < x3.size, x7 ∉ x4 → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : Finset (Fin x2) → Bool) (x12 : Finset (Fin x2) → Bool), ∀ (x13 x14 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x3 (PEqualNP.GenericRejection.incidenceInput x13 x14) (x2 + x2 + x7) = (x11 x13 && x12 x14) := by
  dsimp only
  intro n C S hAO hS j hj hjS hand
  obtain ⟨hC, hR, h2⟩ := hAO
  have hjl : j < C.gates.length := hj
  have hget : C.gates[j]? = some (gateAt C j) := by
    rw [gateAt_eq C j hjl]
    exact List.getElem?_eq_getElem hjl
  have hnotP := fun hP => hjS (hS j (gateAt C j) hget hP)
  have hA : ¬ ∀ x4 ∈ (gateAt C j).inputs, ∃ x6 : Fin n → Bool,
      wireValue C (List.ofFn x6 ++ List.replicate n false) x4 ≠
        wireValue C (List.ofFn x6 ++ List.replicate n true) x4 :=
    fun h => hnotP ⟨hand, Or.inl h⟩
  have hB : ¬ ∀ x4 ∈ (gateAt C j).inputs, ∃ x6 : Fin n → Bool,
      wireValue C (List.replicate n false ++ List.ofFn x6) x4 ≠
        wireValue C (List.replicate n true ++ List.ofFn x6) x4 :=
    fun h => hnotP ⟨hand, Or.inr h⟩
  push Not at hA hB
  obtain ⟨u, hu, hu'⟩ := hA
  obtain ⟨v, hv, hv'⟩ := hB
  have hin := hR j hjl
  have hAF := allfalse (n + n) C hC hR h2
  have hAT := alltrue (n + n) C hC hR h2
  have huv : u ≠ v := by
    rintro rfl
    have e1 := hu' (fun _ => false)
    have e2 := hv' (fun _ => true)
    have k1 : List.replicate n false ++ List.replicate n false = List.replicate (n + n) false :=
      (List.replicate_add _ _ _).symm
    have k2 : List.replicate n true ++ List.replicate n true = List.replicate (n + n) true :=
      (List.replicate_add _ _ _).symm
    simp only [List.ofFn_const, k1, k2] at e1 e2
    have e3 := e1.trans e2
    rw [hAF, hAT u (by have := hin u hu; omega)] at e3
    exact absurd e3 (by simp)
  have hU : ∀ X Y : Finset (Fin n), wireValue C (incidenceInput X Y) u =
      wireValue C (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.replicate n false) u := by
    intro X Y
    unfold incidenceInput
    apply sandwich _ _
      (wireValue C (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.replicate n true) u)
    · exact mono (n + n) C hC hR _ _ (by simp) (by simp)
        (le_app_left _ _ _ (le_false n _)) u
    · exact mono (n + n) C hC hR _ _ (by simp) (by simp)
        (le_app_left _ _ _ (le_true n _ (by simp))) u
    · exact hu' _
  have hV : ∀ X Y : Finset (Fin n), wireValue C (incidenceInput X Y) v =
      wireValue C (List.replicate n false ++ List.ofFn (fun l : Fin n => decide (l ∈ Y))) v := by
    intro X Y
    unfold incidenceInput
    apply sandwich _ _
      (wireValue C (List.replicate n true ++ List.ofFn (fun l : Fin n => decide (l ∈ Y))) v)
    · exact mono (n + n) C hC hR _ _ (by simp) (by simp)
        (le_app_right _ _ _ (by simp) (le_false n _)) v
    · exact mono (n + n) C hC hR _ _ (by simp) (by simp)
        (le_app_right _ _ _ (by simp) (le_true n _ (by simp))) v
    · exact hv' _
  refine ⟨fun X => wireValue C
      (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.replicate n false) u,
    fun Y => wireValue C
      (List.replicate n false ++ List.ofFn (fun l : Fin n => decide (l ∈ Y))) v, ?_⟩
  intro X Y
  beta_reduce
  have hlenI : (incidenceInput X Y).length = n + n := by simp [incidenceInput]
  rw [wv_gate C _ (n + n) j hlenI hjl hin, hand, ← hU X Y, ← hV X Y]
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem C j hjl))
  rw [hpq] at hu hv ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
    Bool.and_true]
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · rfl
  · exact Bool.and_comm _ _
  · exact absurd rfl huv
