import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

namespace PEqualNP.Outside.L_meta_3306

def swapAnd (first second : Finset ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
      if g.inputs.getD 0 0 ∈ first ∧ g.inputs.getD 1 0 ∈ second then g
      else ⟨GateOp.and, [g.inputs.getD 1 0, g.inputs.getD 0 0]⟩
  | _ => g

lemma swapAnd_op (first second : Finset ℕ) (g : Gate) :
    (swapAnd first second g).op = g.op := by
  unfold swapAnd
  split
  · split <;> simp [*]
  · rfl

lemma swapAnd_or (first second : Finset ℕ) (g : Gate) (h : g.op = GateOp.or) :
    swapAnd first second g = g := by
  unfold swapAnd
  split
  · simp [h] at *
  · rfl

lemma and_comm_eval (u v : Bool) :
    GateOp.and.eval [u, v] = GateOp.and.eval [v, u] := by
  simp [GateOp.eval, Bool.and_comm]

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma step_eq (first second : Finset ℕ) (g : Gate) (w : List Bool)
    (hao : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hand : g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧
      (a ∈ second ∧ b ∈ first ∨ a ∈ first ∧ b ∈ second)) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      (swapAnd first second g).op.eval
        ((swapAnd first second g).inputs.map fun i => w.getD i false) := by
  classical
  by_cases hop : g.op = GateOp.and
  · obtain ⟨a, b, hinputs, hab⟩ := hand hop
    have ha : g.inputs.getD 0 0 = a := by simp [hinputs]
    have hb : g.inputs.getD 1 0 = b := by simp [hinputs]
    unfold swapAnd
    by_cases hkeep : a ∈ first ∧ b ∈ second
    · simp [hop, hkeep, hinputs]
    · have hord : a ∈ second ∧ b ∈ first := by
        rcases hab with hab | hab
        · exact hab
        · exact absurd hab hkeep
      simp [hop, hkeep, hinputs, and_comm_eval]
  · have hor : g.op = GateOp.or := by
      rcases hao with hao | hao
      · exact absurd hao hop
      · exact hao
    simp [swapAnd_or first second g hor]

lemma fold_eq (first second : Finset ℕ) :
    ∀ (gs : List Gate) (w : List Bool),
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      (∀ g ∈ gs, g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧
        (a ∈ second ∧ b ∈ first ∨ a ∈ first ∧ b ∈ second)) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
        (gs.map (swapAnd first second)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  intro gs
  induction gs with
  | nil => intro w _ _; simp
  | cons g gs ih =>
    intro w hao hand
    have hstep := step_eq first second g w (hao g (by simp)) (fun hop => hand g (by simp) hop)
    have hlist :
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] =
          w ++ [(swapAnd first second g).op.eval
            ((swapAnd first second g).inputs.map fun i => w.getD i false)] := by
      simpa using congrArg (fun b => w ++ [b]) hstep
    simp only [List.foldl_cons, List.map_cons]
    rw [hlist]
    exact ih _
      (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' hop => hand g' (List.mem_cons_of_mem _ hg') hop)

end PEqualNP.Outside.L_meta_3306

open PEqualNP.Outside.L_meta_3306

theorem PEqualNP.Outside.L_meta_3306 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  classical
  intro n C A B hAO hcross
  let D : Circuit := ⟨C.gates.map (swapAnd B A), C.output⟩
  have hmem : ∀ g ∈ C.gates, g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧
      (a ∈ A ∧ b ∈ B ∨ a ∈ B ∧ b ∈ A) := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    simpa [gateAt_get C j hj] using hcross j hj
  have hfold : ∀ w, C.wires w = D.wires w := by
    intro w
    simpa [Circuit.wires, D] using fold_eq B A C.gates w (fun g hg => hAO.1 g hg) hmem
  have hsize : D.size = C.size := by simp [D, Circuit.size]
  have hgat (j : ℕ) (hj : j < C.gates.length) :
      gateAt D j = swapAnd B A (C.gates[j]) := by
    simp [gateAt, D, hj]
  refine ⟨D, ?_, hsize, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      rw [swapAnd_op]
      exact hAO.1 g0 hg0
    · intro j hj i hi
      have hj0 : j < C.gates.length := by simpa [D, List.length_map] using hj
      rw [hgat j hj0] at hi
      by_cases hop : (C.gates[j]).op = GateOp.and
      · obtain ⟨a, b, hinputs, -⟩ := hmem (C.gates[j]) (by simp) hop
        have hold : i = a ∨ i = b → i ∈ (gateAt C j).inputs := by
          intro hie
          rw [gateAt_get C j hj0, hinputs]
          rcases hie with rfl | rfl <;> simp
        by_cases hkeep : a ∈ B ∧ b ∈ A
        · have hs : swapAnd B A (C.gates[j]) = C.gates[j] := by
            simp [swapAnd, hop, hinputs, hkeep]
          rw [hs] at hi
          exact hAO.2.1 j hj0 i (by simpa [gateAt_get C j hj0] using hi)
        · have hs : swapAnd B A (C.gates[j]) = ⟨GateOp.and, [b, a]⟩ := by
            simp [swapAnd, hop, hinputs, hkeep]
          rw [hs] at hi
          exact hAO.2.1 j hj0 i (hold (by
            simpa [List.mem_cons, List.mem_singleton, or_comm] using hi))
      · have hor : (C.gates[j]).op = GateOp.or := by
          rcases hAO.1 (C.gates[j]) (by simp) with h | h
          · exact absurd h hop
          · exact h
        rw [swapAnd_or B A _ hor] at hi
        exact hAO.2.1 j hj0 i (by simpa [gateAt_get C j hj0] using hi)
    · intro g hg
      simp only [D, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      by_cases hop : g0.op = GateOp.and
      · obtain ⟨a, b, hinputs, -⟩ := hmem g0 hg0 hop
        by_cases hkeep : a ∈ B ∧ b ∈ A
        · simp [swapAnd, hop, hinputs, hkeep]
        · simp [swapAnd, hop, hinputs, hkeep]
      · rw [swapAnd_or B A g0 (by
          rcases hAO.1 g0 hg0 with h | h
          · exact absurd h hop
          · exact h)]
        exact hAO.2.2 g0 hg0
  · funext x
    simp [circuitFun, Circuit.eval, D, hfold]
  · intro j
    by_cases hj : j < C.gates.length
    · rw [hgat j hj, swapAnd_op, gateAt_get C j hj]
    · have hle : C.gates.length ≤ j := Nat.le_of_not_gt hj
      have hleD : D.gates.length ≤ j := by simpa [D, List.length_map] using hle
      simp only [gateAt]
      rw [List.getD_eq_default _ _ hleD, List.getD_eq_default _ _ hle]
  · intro j hor
    by_cases hj : j < C.gates.length
    · rw [hgat j hj, swapAnd_or B A _ (by simpa [gateAt_get C j hj] using hor), gateAt_get C j hj]
    · have hle : C.gates.length ≤ j := Nat.le_of_not_gt hj
      have hleD : D.gates.length ≤ j := by simpa [D, List.length_map] using hle
      simp only [gateAt]
      rw [List.getD_eq_default _ _ hleD, List.getD_eq_default _ _ hle]
  · intro j hj hop
    have hj0 : j < C.gates.length := by simpa [D, List.length_map] using hj
    rw [hgat j hj0] at hop
    obtain ⟨a, b, hinputs, hab⟩ := hmem (C.gates[j]) (by simp)
      (by simpa [swapAnd_op, gateAt_get C j hj0] using hop)
    have hop' : (C.gates[j]).op = GateOp.and := by
      simpa [swapAnd_op] using hop
    rw [hgat j hj0]
    by_cases hkeep : a ∈ B ∧ b ∈ A
    · refine ⟨a, b, ?_, hkeep⟩
      simp [swapAnd, hop', hinputs, hkeep]
    · have hord : b ∈ B ∧ a ∈ A := by
        rcases hab with hab | hab
        · exact ⟨hab.2, hab.1⟩
        · exact absurd hab hkeep
      refine ⟨b, a, ?_, hord⟩
      simp [swapAnd, hop', hinputs, hkeep]
