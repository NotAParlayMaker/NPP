import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3505_aux

open PEqualNP.CircuitLowerBounds

open Classical in
noncomputable def sw (s t : Finset ℕ) (g : Gate) : Gate :=
  if g.op = GateOp.and ∧ ¬ (g.inputs.headD 0 ∈ s ∧ g.inputs.getD 1 0 ∈ t) then ⟨g.op, g.inputs.reverse⟩ else g

theorem sw_op (s t : Finset ℕ) (g : Gate) : (sw s t g).op = g.op := by
  unfold sw; split_ifs <;> rfl

theorem sw_len (s t : Finset ℕ) (g : Gate) : (sw s t g).inputs.length = g.inputs.length := by
  unfold sw; split_ifs <;> simp

theorem sw_mem (s t : Finset ℕ) (g : Gate) (i : ℕ) : i ∈ (sw s t g).inputs ↔ i ∈ g.inputs := by
  unfold sw; split_ifs <;> simp

theorem sw_eval (s t : Finset ℕ) (g : Gate) (w : List Bool) :
    (sw s t g).op.eval ((sw s t g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold sw
  split_ifs with h
  · obtain ⟨h1, _⟩ := h
    simp only [h1, GateOp.eval, List.map_reverse, List.all_reverse]
  · rfl

theorem sw_def (s t : Finset ℕ) : sw s t ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩ := by
  unfold sw; simp

theorem gateAt_sw (s t : Finset ℕ) (C : Circuit) (j : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.gateAt ⟨C.gates.map (sw s t), C.output⟩ j
      = sw s t (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [← sw_def s, List.getD_map, sw_def]

end PEqualNP.Outside.L_meta_3505_aux

open PEqualNP.Outside.L_meta_3505_aux in
theorem PEqualNP.Outside.L_meta_3505_aux.old3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro x1 x2 x3 x4 hA hP
  refine ⟨⟨x2.gates.map (sw x4 x3), x2.output⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hA
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      rw [sw_op]; exact h1 g0 hg0
    · intro j hj i hi
      rw [gateAt_sw, sw_mem] at hi
      simp only [List.length_map] at hj
      exact h2 j hj i hi
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      rw [sw_len]; exact h3 g0 hg0
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · funext x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_map, sw_eval]
  · intro j
    rw [gateAt_sw, sw_op]
  · intro j hj
    rw [gateAt_sw]
    unfold sw
    simp [hj]
  · intro j hj hand
    simp only [List.length_map] at hj
    rw [gateAt_sw, sw_op] at hand
    obtain ⟨a, b, hab, hc⟩ := hP j hj hand
    rw [gateAt_sw]
    unfold sw
    by_cases ha : a ∈ x4 ∧ b ∈ x3
    · rw [if_neg (by simp [hab, ha])]
      exact ⟨a, b, hab, ha.1, ha.2⟩
    · rw [if_pos ⟨hand, by simp [hab, ha]⟩]
      refine ⟨b, a, by simp [hab], ?_, ?_⟩ <;> rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto

theorem PEqualNP.Outside.L_meta_3505 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x3 ∧ x12 ∈ x4 := by
  intro x1 x2 x3 x4 h hc
  exact PEqualNP.Outside.L_meta_3505_aux.old3306 x1 x2 x4 x3 h (fun x6 hx ho => by
    obtain ⟨a, b, e, hab⟩ := hc x6 hx ho
    exact ⟨a, b, e, hab.symm⟩)
