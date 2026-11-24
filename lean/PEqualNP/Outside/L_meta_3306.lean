import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- Reorder the two inputs of an AND gate so that the first lies in T and the second in S.
def fix (S T : Finset ℕ) : Gate → Gate
  | ⟨GateOp.and, [a, b]⟩ =>
      if a ∈ T ∧ b ∈ S then ⟨GateOp.and, [a, b]⟩ else ⟨GateOp.and, [b, a]⟩
  | g => g

lemma fix_op (S T : Finset ℕ) (g : Gate) : (fix S T g).op = g.op := by
  unfold fix
  split
  · split <;> rfl
  · rfl

lemma fix_or (S T : Finset ℕ) (g : Gate) (h : g.op = GateOp.or) : fix S T g = g := by
  unfold fix
  split
  · simp at h
  · rfl

lemma fix_len (S T : Finset ℕ) (g : Gate) : (fix S T g).inputs.length = g.inputs.length := by
  unfold fix
  split
  · split <;> rfl
  · rfl

lemma fix_mem (S T : Finset ℕ) (g : Gate) (i : ℕ) :
    i ∈ (fix S T g).inputs ↔ i ∈ g.inputs := by
  unfold fix
  split
  · split
    · rfl
    · simp [or_comm]
  · rfl

lemma fix_eval (S T : Finset ℕ) (g : Gate) (w : List Bool) :
    (fix S T g).op.eval ((fix S T g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold fix
  split
  · split
    · rfl
    · simp [GateOp.eval, Bool.and_comm]
  · rfl

lemma fix_and (S T : Finset ℕ) (g : Gate) (h : g.op = GateOp.and)
    (hg : ∃ a b : ℕ, g.inputs = [a, b] ∧ (a ∈ S ∧ b ∈ T ∨ a ∈ T ∧ b ∈ S)) :
    ∃ a b : ℕ, (fix S T g).inputs = [a, b] ∧ a ∈ T ∧ b ∈ S := by
  obtain ⟨a, b, hab, hst⟩ := hg
  obtain ⟨op, inputs⟩ := g
  simp only at h hab
  subst h
  subst hab
  by_cases hc : a ∈ T ∧ b ∈ S
  · exact ⟨a, b, by simp [fix, hc], hc.1, hc.2⟩
  · rcases hst with hst | hst
    · exact ⟨b, a, by simp [fix, hc], hst.2, hst.1⟩
    · exact absurd hst hc

lemma wires_fix (S T : Finset ℕ) (l : List Gate) (x : List Bool) :
    (l.map (fix S T)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x =
      l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := by
  induction l generalizing x with
  | nil => rfl
  | cons g t ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [fix_eval]
    exact ih _

lemma gateAt_fix (S T : Finset ℕ) (C : Circuit) (j : ℕ) :
    gateAt ⟨C.gates.map (fix S T), C.output⟩ j = fix S T (gateAt C j) := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? with
  | none => rfl
  | some g => rfl

end PEqualNP.Outside.L_meta_3306

theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro n C S T hAO hand
  obtain ⟨hao, hrb, hlen⟩ := hAO
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_3306.fix S T), C.output⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [PEqualNP.Outside.L_meta_3306.fix_op]
    exact hao g0 hg0
  · intro j hj i hi
    rw [PEqualNP.Outside.L_meta_3306.gateAt_fix, PEqualNP.Outside.L_meta_3306.fix_mem] at hi
    exact hrb j (by simpa using hj) i hi
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [PEqualNP.Outside.L_meta_3306.fix_len]
    exact hlen g0 hg0
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · funext x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires]
    rw [PEqualNP.Outside.L_meta_3306.wires_fix]
  · intro j
    rw [PEqualNP.Outside.L_meta_3306.gateAt_fix, PEqualNP.Outside.L_meta_3306.fix_op]
  · intro j hj
    rw [PEqualNP.Outside.L_meta_3306.gateAt_fix]
    exact PEqualNP.Outside.L_meta_3306.fix_or S T _ hj
  · intro j hj hop
    rw [PEqualNP.Outside.L_meta_3306.gateAt_fix] at hop ⊢
    rw [PEqualNP.Outside.L_meta_3306.fix_op] at hop
    exact PEqualNP.Outside.L_meta_3306.fix_and S T _ hop (hand j (by simpa using hj) hop)
