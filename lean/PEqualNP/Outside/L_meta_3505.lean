import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3505

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Reorder the two operands of an AND gate so that the first lies in P and the second in L.
def fix (P L : Finset ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => if a ∈ P ∧ b ∈ L then g else ⟨GateOp.and, [b, a]⟩
  | _, _ => g

lemma fix_op (P L : Finset ℕ) (g : Gate) : (fix P L g).op = g.op := by
  rcases g with ⟨op, ins⟩
  unfold fix
  split
  · split_ifs <;> simp_all
  · rfl

lemma fix_or (P L : Finset ℕ) (g : Gate) (h : g.op = GateOp.or) : fix P L g = g := by
  rcases g with ⟨op, ins⟩
  unfold fix
  split
  · simp_all
  · rfl

lemma fix_perm (P L : Finset ℕ) (g : Gate) : (fix P L g).inputs.Perm g.inputs := by
  rcases g with ⟨op, ins⟩
  unfold fix
  split
  · rename_i a b h1 h2
    simp only at h2
    subst h2
    split_ifs
    · exact List.Perm.refl _
    · exact List.Perm.swap _ _ _
  · exact List.Perm.refl _

lemma fix_eval (P L : Finset ℕ) (g : Gate) (f : ℕ → Bool) :
    (fix P L g).op.eval ((fix P L g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  rcases g with ⟨op, ins⟩
  unfold fix
  split
  · rename_i a b h1 h2
    simp only at h1 h2
    subst h1
    subst h2
    split_ifs
    · rfl
    · simp [GateOp.eval, Bool.and_comm]
  · rfl

lemma fix_and (P L : Finset ℕ) (g : Gate) (hop : g.op = GateOp.and) (a b : ℕ)
    (hin : g.inputs = [a, b]) (h : a ∈ P ∧ b ∈ L ∨ a ∈ L ∧ b ∈ P) :
    ∃ c d : ℕ, (fix P L g).inputs = [c, d] ∧ c ∈ P ∧ d ∈ L := by
  rcases g with ⟨op, ins⟩
  simp only at hop hin
  subst hop
  subst hin
  unfold fix
  simp only
  split_ifs with h1
  · exact ⟨a, b, rfl, h1.1, h1.2⟩
  · rcases h with h | h
    · exact absurd h h1
    · exact ⟨b, a, rfl, h.2, h.1⟩

def fixC (P L : Finset ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (fix P L), C.output⟩

lemma gateAt_fixC (P L : Finset ℕ) (C : Circuit) (j : ℕ) :
    gateAt (fixC P L C) j = fix P L (gateAt C j) := by
  unfold gateAt fixC
  simp only
  have h : (⟨GateOp.or, []⟩ : Gate) = fix P L ⟨GateOp.or, []⟩ := by
    unfold fix
    rfl
  conv_lhs => rw [h]
  exact List.getD_map _ _ _

lemma wires_fixC (P L : Finset ℕ) (C : Circuit) (x : List Bool) :
    (fixC P L C).wires x = C.wires x := by
  unfold Circuit.wires fixC
  simp only
  rw [List.foldl_map]
  congr 1
  funext w g
  rw [fix_eval]

end PEqualNP.Outside.L_meta_3505

theorem PEqualNP.Outside.L_meta_3505 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x3 ∧ x12 ∈ x4 := by
  intro n C P L hC hand
  obtain ⟨hAO, hRB, hLen⟩ := hC
  refine ⟨PEqualNP.Outside.L_meta_3505.fixC P L C, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_3505.fixC, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [PEqualNP.Outside.L_meta_3505.fix_op]
    exact hAO g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by
      simpa [PEqualNP.Outside.L_meta_3505.fixC] using hj
    rw [PEqualNP.Outside.L_meta_3505.gateAt_fixC] at hi
    exact hRB j hj' i ((PEqualNP.Outside.L_meta_3505.fix_perm P L _).mem_iff.mp hi)
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_3505.fixC, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    rw [(PEqualNP.Outside.L_meta_3505.fix_perm P L g0).length_eq]
    exact hLen g0 hg0
  · simp [PEqualNP.Outside.L_meta_3505.fixC, PEqualNP.CircuitLowerBounds.Circuit.size]
  · funext x
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_3505.wires_fixC]
    rfl
  · intro j
    rw [PEqualNP.Outside.L_meta_3505.gateAt_fixC, PEqualNP.Outside.L_meta_3505.fix_op]
  · intro j hj
    rw [PEqualNP.Outside.L_meta_3505.gateAt_fixC]
    exact PEqualNP.Outside.L_meta_3505.fix_or P L _ hj
  · intro j hj hop
    have hj' : j < C.gates.length := by
      simpa [PEqualNP.Outside.L_meta_3505.fixC] using hj
    rw [PEqualNP.Outside.L_meta_3505.gateAt_fixC] at hop ⊢
    rw [PEqualNP.Outside.L_meta_3505.fix_op] at hop
    obtain ⟨a, b, hin, hab⟩ := hand j hj' hop
    exact PEqualNP.Outside.L_meta_3505.fix_and P L _ hop a b hin hab
