import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def flip (P L : Finset ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => if a ∈ L ∧ b ∈ P then g else ⟨GateOp.and, [b, a]⟩
  | _, _ => g

lemma flip_op (P L : Finset ℕ) (g : Gate) : (flip P L g).op = g.op := by
  unfold flip
  split
  · rename_i h1 h2
    split_ifs
    · rfl
    · exact h1.symm
  · rfl

lemma flip_inputs (P L : Finset ℕ) (g : Gate) :
    (flip P L g).inputs = g.inputs ∨
      ∃ a b : ℕ, g.inputs = [a, b] ∧ (flip P L g).inputs = [b, a] := by
  unfold flip
  split
  · rename_i a b h1 h2
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr ⟨a, b, h2, rfl⟩
  · exact Or.inl rfl

lemma flip_mem (P L : Finset ℕ) (g : Gate) (i : ℕ) :
    i ∈ (flip P L g).inputs ↔ i ∈ g.inputs := by
  rcases flip_inputs P L g with h | ⟨a, b, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact or_comm

lemma flip_len (P L : Finset ℕ) (g : Gate) :
    (flip P L g).inputs.length = g.inputs.length := by
  rcases flip_inputs P L g with h | ⟨a, b, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    rfl

lemma flip_eval (P L : Finset ℕ) (g : Gate) (w : List Bool) :
    (flip P L g).op.eval ((flip P L g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold flip
  split
  · rename_i a b h1 h2
    split_ifs
    · rfl
    · rw [h1, h2]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
        Bool.and_true]
      exact Bool.and_comm _ _
  · rfl

lemma flip_or (P L : Finset ℕ) (g : Gate) (h : g.op = GateOp.or) : flip P L g = g := by
  unfold flip
  split
  · rename_i h1 h2
    rw [h] at h1
    cases h1
  · rfl

lemma flip_spec (P L : Finset ℕ) (g : Gate) (a b : ℕ) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) (hab : (a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) :
    ∃ c d : ℕ, (flip P L g).inputs = [c, d] ∧ c ∈ L ∧ d ∈ P := by
  unfold flip
  split
  · rename_i a' b' h1 h2
    rw [hin] at h2
    simp only [List.cons.injEq, and_true] at h2
    obtain ⟨rfl, rfl⟩ := h2
    split_ifs with hc
    · exact ⟨a, b, hin, hc.1, hc.2⟩
    · rcases hab with h | h
      · exact ⟨b, a, rfl, h.2, h.1⟩
      · exact absurd h hc
  · rename_i hne
    exact absurd hin (hne a b hop)

def flipC (P L : Finset ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (flip P L), C.output⟩

lemma gateAt_flipC (P L : Finset ℕ) (C : Circuit) (i : ℕ) :
    gateAt (flipC P L C) i = flip P L (gateAt C i) := by
  have hd : flip P L ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩ := flip_or P L _ rfl
  unfold gateAt flipC
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : C.gates[i]? with
  | none => simpa using hd.symm
  | some g => simp

lemma wires_flipC (P L : Finset ℕ) (C : Circuit) (x : List Bool) :
    (flipC P L C).wires x = C.wires x := by
  unfold Circuit.wires flipC
  simp only [List.foldl_map]
  congr 1
  funext w g
  rw [flip_eval]

end PEqualNP.Outside.L_meta_3306

open PEqualNP.Outside.L_meta_3306 in
theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro n C P L hC hands
  obtain ⟨hao, hrb, hlen⟩ := hC
  refine ⟨flipC P L C, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [flip_op]
    exact hao g0 hg0
  · intro j hj i hi
    rw [gateAt_flipC, flip_mem] at hi
    exact hrb j (by simpa [flipC] using hj) i hi
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [flip_len]
    exact hlen g0 hg0
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, flipC]
  · funext z
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [wires_flipC]
    rfl
  · intro i
    rw [gateAt_flipC, flip_op]
  · intro i hi
    rw [gateAt_flipC, flip_or P L _ hi]
  · intro i hi hop
    rw [gateAt_flipC] at hop ⊢
    rw [flip_op] at hop
    obtain ⟨a, b, hin, hab⟩ := hands i (by simpa [flipC] using hi) hop
    exact flip_spec P L _ a b hop hin hab
