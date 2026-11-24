import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3313_aux

open PEqualNP.CircuitLowerBounds

def circ : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 41] }], output := 43 }

def full : ℕ := 2 ^ 16384 - 1

def opB : GateOp → List ℕ → ℕ
  | .and, l => l.foldr (· &&& ·) full
  | .or, l => l.foldr (· ||| ·) 0
  | _, _ => 0

def wB (gs : List Gate) (w : List ℕ) : List ℕ :=
  gs.foldl (fun w g => w ++ [opB g.op (g.inputs.map fun i => w.getD i 0)]) w

def step (i j : ℕ) (acc : ℕ) : ℕ := if j.testBit i then acc ||| (1 <<< j) else acc

def mask (i : ℕ) : ℕ := (List.range 16384).foldr (step i) 0

def masks : List ℕ := (List.range 14).map mask

def edges : List (Fin 14 × Fin 14) := [(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)]

def target : ℕ :=
  edges.foldr (fun e acc => (masks.getD e.1.val 0 &&& masks.getD e.2.val 0) ||| acc) 0

theorem chk : (wB circ.gates masks).getD circ.output 0 = target := by
  decide +kernel

theorem foldr_step (i j : ℕ) : ∀ (L : List ℕ) (acc : ℕ),
    (L.foldr (step i) acc).testBit j = ((decide (j ∈ L) && j.testBit i) || acc.testBit j) := by
  intro L
  induction L with
  | nil => intro acc; simp
  | cons a L ih =>
    intro acc
    rw [List.foldr_cons]
    by_cases h : a.testBit i = true
    · have e : step i a (L.foldr (step i) acc) = L.foldr (step i) acc ||| (1 <<< a) := by
        simp [step, h]
      rw [e, Nat.testBit_lor, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hja : j = a
      · subst hja; simp [h]
      · simp [hja, Ne.symm hja]
    · have e : step i a (L.foldr (step i) acc) = L.foldr (step i) acc := by
        simp [step, h]
      rw [e, ih]
      by_cases hja : j = a
      · subst hja; simp [h]
      · simp [hja]

theorem mask_spec (i j : ℕ) (hj : j < 16384) : (mask i).testBit j = j.testBit i := by
  unfold mask
  rw [foldr_step]
  simp [List.mem_range, hj]

theorem full_spec (j : ℕ) (hj : j < 16384) : full.testBit j = true := by
  unfold full
  rw [Nat.testBit_two_pow_sub_one]
  simpa using hj

theorem opB_spec (j : ℕ) (hj : j < 16384) (op : GateOp) (hop : op = .and ∨ op = .or)
    (l : List ℕ) : (opB op l).testBit j = op.eval (l.map fun n => n.testBit j) := by
  rcases hop with rfl | rfl
  · induction l with
    | nil => simp [opB, GateOp.eval, full_spec j hj]
    | cons a l ih =>
      simp only [opB, List.foldr_cons, Nat.testBit_land] at ih ⊢
      rw [ih]
      simp [GateOp.eval]
  · induction l with
    | nil => simp [opB, GateOp.eval]
    | cons a l ih =>
      simp only [opB, List.foldr_cons, Nat.testBit_lor] at ih ⊢
      rw [ih]
      simp [GateOp.eval]

theorem getD_bits (j : ℕ) (w : List ℕ) (i : ℕ) :
    (w.map fun n => n.testBit j).getD i false = (w.getD i 0).testBit j := by
  have h := List.getD_map (f := fun n : ℕ => n.testBit j) (l := w) (n := i) (d := 0)
  simpa using h

theorem wB_spec (j : ℕ) (hj : j < 16384) : ∀ (gs : List Gate) (w : List ℕ),
    (∀ g ∈ gs, g.op = .and ∨ g.op = .or) →
    (wB gs w).map (fun n => n.testBit j) =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
        (w.map fun n => n.testBit j) := by
  intro gs
  induction gs with
  | nil => intro w _; simp [wB]
  | cons g gs ih =>
    intro w hg
    simp only [wB, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    rw [List.map_append, List.map_singleton, opB_spec j hj g.op (hg g List.mem_cons_self),
      List.map_map]
    simp only [Function.comp_def, getD_bits]

theorem ops_ok : ∀ g ∈ circ.gates, g.op = .and ∨ g.op = .or := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem inputs_eq (j : ℕ) (hj : j < 16384) :
    masks.map (fun n => n.testBit j) = List.ofFn (fun i : Fin 14 => j.testBit i) := by
  simp only [masks, List.map_map]
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  apply List.map_congr_left
  intro i _
  simp [mask_spec _ _ hj]

theorem target_spec (j : ℕ) (hj : j < 16384) :
    target.testBit j = edges.any (fun e => j.testBit e.1 && j.testBit e.2) := by
  have hm : ∀ k : Fin 14, (masks.getD k.val 0).testBit j = j.testBit k := by
    intro k
    have hk : k.val < 14 := k.isLt
    simp [masks, List.getD_eq_getElem?_getD, hk, mask_spec _ _ hj]
  unfold target
  induction edges with
  | nil => simp
  | cons e L ih =>
    simp only [List.foldr_cons, Nat.testBit_lor, Nat.testBit_land, hm, ih, List.any_cons]

theorem tab (j : ℕ) (hj : j < 16384) :
    PEqualNP.MetaComplexity.circuitFun 14 circ (fun i : Fin 14 => j.testBit i) =
      decide (∃ e ∈ edges, j.testBit e.1 = true ∧ j.testBit e.2 = true) := by
  have h1 : PEqualNP.MetaComplexity.circuitFun 14 circ (fun i : Fin 14 => j.testBit i) =
      target.testBit j := by
    unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires
    rw [← inputs_eq j hj, ← wB_spec j hj _ _ ops_ok, getD_bits, chk]
  rw [h1, target_spec j hj]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
  simp [Bool.and_eq_true]

theorem bridge (x : Fin 14 → Bool) : ∃ j < 16384, (fun i : Fin 14 => j.testBit i) = x := by
  let y : Fin 14 → Fin 2 := fun i => if x i then 1 else 0
  refine ⟨(finFunctionFinEquiv y : ℕ), ?_, ?_⟩
  · have h := (finFunctionFinEquiv y).isLt
    norm_num at h
    exact h
  · funext i
    have h := congrArg (fun z : Fin 14 → Fin 2 => ((z i : Fin 2) : ℕ))
      (finFunctionFinEquiv.symm_apply_apply y)
    simp only [finFunctionFinEquiv_symm_apply_val] at h
    rw [Nat.testBit_eq_decide_div_mod_eq, h]
    cases hx : x i <;> simp [y, hx]

end PEqualNP.Outside.L_meta_3313_aux

theorem PEqualNP.Outside.L_meta_3313 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 41] }], output := 43 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 30 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (([(3, [5, 8], [3, 9], [5, 9]), (4, [5, 8], [8, 9], [5, 9]), (7, [8], [4], [4, 8]), (9, [9], [6], [6, 9]), (11, [10], [5], [5, 10]), (14, [7], [2], [2, 7]), (17, [11], [6], [6, 11]), (20, [12], [6], [6, 12]), (23, [13], [5], [5, 13])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))).map (fun t => t.1) ++ ([(0, [3, 8], [5, 9], [5, 8]), (1, [5, 9], [3, 8], [3, 9]), (2, [3, 10], [5, 10], [10]), (5, [5, 9], [0, 9], [9]), (6, [3, 8], [4, 8], [8]), (8, [5, 9], [6, 9], [9]), (10, [5, 10], [1, 10], [10]), (12, [1, 7], [2, 7], [7]), (13, [2, 7], [0, 7], [7]), (15, [4, 11], [6, 11], [11]), (16, [6, 11], [1, 11], [11]), (18, [2, 12], [3, 12], [12]), (19, [3, 12], [6, 12], [12]), (21, [2, 13], [5, 13], [13]), (22, [5, 13], [4, 13], [13]), (24, [4, 8], [2, 7], []), (25, [4, 8], [6, 9], []), (26, [6, 9], [5, 13], []), (27, [6, 12], [6, 11], []), (28, [6, 9], [5, 10], []), (29, [6, 9], [6, 12], [])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))).map (fun t => t.1)).Perm (List.range 30) ∧
  (∀ t ∈ ([(3, [5, 8], [3, 9], [5, 9]), (4, [5, 8], [8, 9], [5, 9]), (7, [8], [4], [4, 8]), (9, [9], [6], [6, 9]), (11, [10], [5], [5, 10]), (14, [7], [2], [2, 7]), (17, [11], [6], [6, 11]), (20, [12], [6], [6, 12]), (23, [13], [5], [5, 13])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))), (PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 1 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 0 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.2)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.2))) ∧
  (∀ t ∈ ([(0, [3, 8], [5, 9], [5, 8]), (1, [5, 9], [3, 8], [3, 9]), (2, [3, 10], [5, 10], [10]), (5, [5, 9], [0, 9], [9]), (6, [3, 8], [4, 8], [8]), (8, [5, 9], [6, 9], [9]), (10, [5, 10], [1, 10], [10]), (12, [1, 7], [2, 7], [7]), (13, [2, 7], [0, 7], [7]), (15, [4, 11], [6, 11], [11]), (16, [6, 11], [1, 11], [11]), (18, [2, 12], [3, 12], [12]), (19, [3, 12], [6, 12], [12]), (21, [2, 13], [5, 13], [13]), (22, [5, 13], [4, 13], [13]), (24, [4, 8], [2, 7], []), (25, [4, 8], [6, 9], []), (26, [6, 9], [5, 13], []), (27, [6, 12], [6, 11], []), (28, [6, 9], [5, 10], []), (29, [6, 9], [6, 12], [])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))), (PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 1 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 0 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.2)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.2))) := by
  intro C hC
  subst hC
  refine ⟨by decide, rfl, ?_, by decide, ?_, ?_⟩
  · intro x
    obtain ⟨j, hj, rfl⟩ := PEqualNP.Outside.L_meta_3313_aux.bridge x
    exact PEqualNP.Outside.L_meta_3313_aux.tab j hj
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
