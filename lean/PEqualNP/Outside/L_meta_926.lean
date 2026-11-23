import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926

def c1 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩

theorem e1 : ∀ b0 b1 : Bool, (c1).eval [b0, b1] = ((b0 && b1)) := by
  decide

theorem h1 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  refine ⟨c1, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c1, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e1 _ _

def c2 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩], 4⟩

theorem e2 : ∀ b0 b1 b2 : Bool, (c2).eval [b0, b1, b2] = ((b0 && b1) || (b0 && b2)) := by
  decide

theorem h2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  refine ⟨c2, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c2, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e2 _ _ _

def c3 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩], 6⟩

theorem e3 : ∀ b0 b1 b2 : Bool, (c3).eval [b0, b1, b2] = ((b0 && b1) || (b0 && b2) || (b1 && b2)) := by
  decide

theorem h3 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨c3, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c3, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e3 _ _ _

def c4 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩], 6⟩

theorem e4 : ∀ b0 b1 b2 b3 : Bool, (c4).eval [b0, b1, b2, b3] = ((b0 && b1) || (b2 && b3)) := by
  decide

theorem h4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  refine ⟨c4, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c4, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e4 _ _ _ _

def c5 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩], 6⟩

theorem e5 : ∀ b0 b1 b2 b3 : Bool, (c5).eval [b0, b1, b2, b3] = ((b0 && b1) || (b0 && b2) || (b0 && b3)) := by
  decide

theorem h5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  refine ⟨c5, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c5, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e5 _ _ _ _

def c6 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩], 7⟩

theorem e6 : ∀ b0 b1 b2 b3 : Bool, (c6).eval [b0, b1, b2, b3] = ((b0 && b1) || (b0 && b2) || (b1 && b3)) := by
  decide

theorem h6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  refine ⟨c6, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c6, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e6 _ _ _ _

def c7 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩], 8⟩

theorem e7 : ∀ b0 b1 b2 b3 : Bool, (c7).eval [b0, b1, b2, b3] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2)) := by
  decide

theorem h7 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  refine ⟨c7, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c7, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e7 _ _ _ _

def c8 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩], 8⟩

theorem e8 : ∀ b0 b1 b2 b3 b4 : Bool, (c8).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b3 && b4)) := by
  decide

theorem h8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  refine ⟨c8, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c8, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e8 _ _ _ _ _

def c9 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩], 8⟩

theorem e9 : ∀ b0 b1 b2 b3 b4 : Bool, (c9).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4)) := by
  decide

theorem h9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  refine ⟨c9, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c9, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e9 _ _ _ _ _

def c10 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩], 9⟩

theorem e10 : ∀ b0 b1 b2 b3 b4 : Bool, (c10).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4)) := by
  decide

theorem h10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  refine ⟨c10, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c10, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e10 _ _ _ _ _

def c11 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩], 10⟩

theorem e11 : ∀ b0 b1 b2 b3 b4 : Bool, (c11).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4)) := by
  decide

theorem h11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  refine ⟨c11, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c11, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e11 _ _ _ _ _

def c12 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩], 9⟩

theorem e12 : ∀ b0 b1 b2 b3 b4 : Bool, (c12).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4)) := by
  decide

theorem h12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  refine ⟨c12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c12, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e12 _ _ _ _ _

def c13 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩], 10⟩

theorem e13 : ∀ b0 b1 b2 b3 b4 : Bool, (c13).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2)) := by
  decide

theorem h13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  refine ⟨c13, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c13, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e13 _ _ _ _ _

def c14 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩], 10⟩

theorem e14 : ∀ b0 b1 b2 b3 b4 : Bool, (c14).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4)) := by
  decide

theorem h14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  refine ⟨c14, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c14, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e14 _ _ _ _ _

def c15 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩], 11⟩

theorem e15 : ∀ b0 b1 b2 b3 b4 : Bool, (c15).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4)) := by
  decide

theorem h15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  refine ⟨c15, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c15, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e15 _ _ _ _ _

def c16 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩], 11⟩

theorem e16 : ∀ b0 b1 b2 b3 b4 : Bool, (c16).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b4)) := by
  decide

theorem h16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  refine ⟨c16, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c16, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e16 _ _ _ _ _

def c17 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩], 12⟩

theorem e17 : ∀ b0 b1 b2 b3 b4 : Bool, (c17).eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b4)) := by
  decide

theorem h17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  refine ⟨c17, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c17, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e17 _ _ _ _ _

def c18 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩], 10⟩

theorem e18 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c18).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b2 && b3) || (b4 && b5)) := by
  decide

theorem h18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨c18, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c18, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e18 _ _ _ _ _ _

def c19 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩], 10⟩

theorem e19 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c19).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b4 && b5)) := by
  decide

theorem h19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨c19, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c19, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e19 _ _ _ _ _ _

def c20 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩], 11⟩

theorem e20 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c20).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b4 && b5)) := by
  decide

theorem h20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  refine ⟨c20, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c20, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e20 _ _ _ _ _ _

def c21 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩], 10⟩

theorem e21 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c21).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b3 && b4) || (b3 && b5)) := by
  decide

theorem h21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  refine ⟨c21, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c21, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e21 _ _ _ _ _ _

def c22 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩], 10⟩

theorem e22 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c22).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5)) := by
  decide

theorem h22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  refine ⟨c22, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c22, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e22 _ _ _ _ _ _

def c23 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩], 11⟩

theorem e23 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c23).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5)) := by
  decide

theorem h23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨c23, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c23, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e23 _ _ _ _ _ _

def c24 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩], 12⟩

theorem e24 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c24).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b4 && b5)) := by
  decide

theorem h24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  refine ⟨c24, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c24, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e24 _ _ _ _ _ _

def c25 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩], 11⟩

theorem e25 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c25).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b1 && b5)) := by
  decide

theorem h25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨c25, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c25, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e25 _ _ _ _ _ _

def c26 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩], 12⟩

theorem e26 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c26).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5)) := by
  decide

theorem h26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  refine ⟨c26, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c26, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e26 _ _ _ _ _ _

def c27 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩], 11⟩

theorem e27 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c27).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b4 && b5)) := by
  decide

theorem h27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  refine ⟨c27, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c27, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e27 _ _ _ _ _ _

def c28 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩], 12⟩

theorem e28 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c28).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4) || (b3 && b5)) := by
  decide

theorem h28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨c28, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c28, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e28 _ _ _ _ _ _

def c29 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩], 12⟩

theorem e29 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c29).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5)) := by
  decide

theorem h29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨c29, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c29, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e29 _ _ _ _ _ _

def c30 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩], 12⟩

theorem e30 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c30).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2)) := by
  decide

theorem h30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  refine ⟨c30, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c30, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e30 _ _ _ _ _ _

def c31 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩], 12⟩

theorem e31 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c31).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5)) := by
  decide

theorem h31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  refine ⟨c31, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c31, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e31 _ _ _ _ _ _

def c32 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e32 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c32).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5)) := by
  decide

theorem h32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  refine ⟨c32, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c32, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e32 _ _ _ _ _ _

def c33 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e33 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c33).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b2 && b5)) := by
  decide

theorem h33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  refine ⟨c33, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c33, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e33 _ _ _ _ _ _

def c34 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e34 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c34).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5)) := by
  decide

theorem h34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨c34, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c34, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e34 _ _ _ _ _ _

def c35 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e35 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c35).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b3 && b5)) := by
  decide

theorem h35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨c35, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c35, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e35 _ _ _ _ _ _

def c36 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e36 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c36).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b4 && b5)) := by
  decide

theorem h36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  refine ⟨c36, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c36, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e36 _ _ _ _ _ _

def c37 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e37 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c37).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b5)) := by
  decide

theorem h37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨c37, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c37, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e37 _ _ _ _ _ _

def c38 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩], 14⟩

theorem e38 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c38).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4) || (b3 && b5) || (b4 && b5)) := by
  decide

theorem h38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨c38, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c38, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e38 _ _ _ _ _ _

def c39 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e39 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c39).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b5)) := by
  decide

theorem h39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨c39, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c39, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e39 _ _ _ _ _ _

def c40 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e40 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c40).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b3 && b4)) := by
  decide

theorem h40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  refine ⟨c40, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c40, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e40 _ _ _ _ _ _

def c41 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e41 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c41).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b3 && b4)) := by
  decide

theorem h41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  refine ⟨c41, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c41, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e41 _ _ _ _ _ _

def c42 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e42 : ∀ b0 b1 b2 b3 b4 b5 : Bool, (c42).eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b4 && b5)) := by
  decide

theorem h42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨c42, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c42, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e42 _ _ _ _ _ _

def c43 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩], 12⟩

theorem e43 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c43).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide

theorem h43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨c43, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c43, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e43 _ _ _ _ _ _ _

def c44 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩], 12⟩

theorem e44 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c44).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b5 && b6)) := by
  decide

theorem h44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨c44, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c44, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e44 _ _ _ _ _ _ _

def c45 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e45 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c45).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b5 && b6)) := by
  decide

theorem h45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨c45, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c45, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e45 _ _ _ _ _ _ _

def c46 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩], 12⟩

theorem e46 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c46).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b4 && b5) || (b4 && b6)) := by
  decide

theorem h46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  refine ⟨c46, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c46, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e46 _ _ _ _ _ _ _

def c47 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩], 14⟩

theorem e47 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c47).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide

theorem h47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨c47, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c47, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e47 _ _ _ _ _ _ _

def c48 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e48 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c48).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b5 && b6)) := by
  decide

theorem h48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨c48, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c48, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e48 _ _ _ _ _ _ _

def c49 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

theorem e49 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c49).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b4 && b5) || (b4 && b6)) := by
  decide

theorem h49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨c49, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c49, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e49 _ _ _ _ _ _ _

def c50 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩], 12⟩

theorem e50 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c50).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b0 && b6)) := by
  decide

theorem h50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  refine ⟨c50, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c50, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e50 _ _ _ _ _ _ _

def c51 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩], 13⟩

theorem e51 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c51).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b6)) := by
  decide

theorem h51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨c51, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c51, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e51 _ _ _ _ _ _ _

def c52 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e52 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c52).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b5 && b6)) := by
  decide

theorem h52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  refine ⟨c52, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c52, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e52 _ _ _ _ _ _ _

def c53 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩], 13⟩

theorem e53 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c53).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b1 && b6)) := by
  decide

theorem h53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨c53, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c53, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e53 _ _ _ _ _ _ _

def c54 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e54 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c54).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b2 && b6)) := by
  decide

theorem h54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨c54, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c54, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e54 _ _ _ _ _ _ _

def c55 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩], 13⟩

theorem e55 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c55).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b5 && b6)) := by
  decide

theorem h55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  refine ⟨c55, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c55, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e55 _ _ _ _ _ _ _

def c56 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e56 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c56).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b5 && b6)) := by
  decide

theorem h56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨c56, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c56, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e56 _ _ _ _ _ _ _

def c57 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩], 15⟩

theorem e57 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c57).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide

theorem h57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨c57, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c57, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e57 _ _ _ _ _ _ _

def c58 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e58 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c58).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b4 && b5) || (b4 && b6)) := by
  decide

theorem h58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c58, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c58, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e58 _ _ _ _ _ _ _

def c59 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e59 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c59).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b1 && b5) || (b2 && b6)) := by
  decide

theorem h59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨c59, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c59, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e59 _ _ _ _ _ _ _

def c60 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e60 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c60).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b3 && b6)) := by
  decide

theorem h60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  refine ⟨c60, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c60, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e60 _ _ _ _ _ _ _

def c61 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e61 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c61).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b6)) := by
  decide

theorem h61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c61, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c61, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e61 _ _ _ _ _ _ _

def c62 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩], 13⟩

theorem e62 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c62).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b4 && b5) || (b4 && b6)) := by
  decide

theorem h62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨c62, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c62, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e62 _ _ _ _ _ _ _

def c63 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e63 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c63).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b4 && b5) || (b5 && b6)) := by
  decide

theorem h63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  refine ⟨c63, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c63, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e63 _ _ _ _ _ _ _

def c64 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e64 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c64).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b4 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide

theorem h64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  refine ⟨c64, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c64, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e64 _ _ _ _ _ _ _

def c65 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩], 15⟩

theorem e65 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c65).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4) || (b3 && b5) || (b4 && b6)) := by
  decide

theorem h65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c65, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c65, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e65 _ _ _ _ _ _ _

def c66 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩], 15⟩

theorem e66 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c66).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b4) || (b5 && b6)) := by
  decide

theorem h66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨c66, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c66, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e66 _ _ _ _ _ _ _

def c67 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], 14⟩

theorem e67 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c67).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b6)) := by
  decide

theorem h67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c67, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c67, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e67 _ _ _ _ _ _ _

def c68 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩], 14⟩

theorem e68 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c68).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b0 && b6) || (b1 && b2)) := by
  decide

theorem h68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  refine ⟨c68, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c68, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e68 _ _ _ _ _ _ _

def c69 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩], 14⟩

theorem e69 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c69).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b1 && b6)) := by
  decide

theorem h69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  refine ⟨c69, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c69, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e69 _ _ _ _ _ _ _

def c70 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e70 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c70).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b3 && b6)) := by
  decide

theorem h70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  refine ⟨c70, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c70, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e70 _ _ _ _ _ _ _

def c71 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩], 14⟩

theorem e71 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c71).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b1 && b6)) := by
  decide

theorem h71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  refine ⟨c71, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c71, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e71 _ _ _ _ _ _ _

def c72 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e72 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c72).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b2 && b6)) := by
  decide

theorem h72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  refine ⟨c72, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c72, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e72 _ _ _ _ _ _ _

def c73 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e73 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c73).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b3 && b6)) := by
  decide

theorem h73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c73, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c73, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e73 _ _ _ _ _ _ _

def c74 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e74 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c74).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b5 && b6)) := by
  decide

theorem h74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c74, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c74, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e74 _ _ _ _ _ _ _

def c75 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e75 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c75).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5) || (b3 && b6)) := by
  decide

theorem h75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c75, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c75, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e75 _ _ _ _ _ _ _

def c76 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e76 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c76).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5) || (b5 && b6)) := by
  decide

theorem h76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c76, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c76, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e76 _ _ _ _ _ _ _

def c77 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e77 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c77).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b1 && b6) || (b5 && b6)) := by
  decide

theorem h77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c77, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c77, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e77 _ _ _ _ _ _ _

def c78 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e78 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c78).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b2 && b6) || (b5 && b6)) := by
  decide

theorem h78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c78, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c78, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e78 _ _ _ _ _ _ _

def c79 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e79 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c79).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b2 && b5) || (b3 && b6)) := by
  decide

theorem h79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c79, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c79, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e79 _ _ _ _ _ _ _

def c80 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e80 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c80).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b3 && b6)) := by
  decide

theorem h80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c80, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c80, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e80 _ _ _ _ _ _ _

def c81 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e81 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c81).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b5 && b6)) := by
  decide

theorem h81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c81, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c81, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e81 _ _ _ _ _ _ _

def c82 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e82 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c82).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b4 && b5) || (b4 && b6)) := by
  decide

theorem h82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c82, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c82, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e82 _ _ _ _ _ _ _

def c83 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e83 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c83).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b1 && b5) || (b2 && b6) || (b4 && b6)) := by
  decide

theorem h83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  refine ⟨c83, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c83, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e83 _ _ _ _ _ _ _

def c84 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e84 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c84).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b5) || (b4 && b6)) := by
  decide

theorem h84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c84, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c84, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e84 _ _ _ _ _ _ _

def c85 : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

theorem e85 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, (c85).eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide

theorem h85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c85, ?_, by decide, ?_⟩
  · intro g hg
    simp only [c85, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact e85 _ _ _ _ _ _ _

end PEqualNP.Outside.L_meta_926

theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  exact ⟨PEqualNP.Outside.L_meta_926.h1, PEqualNP.Outside.L_meta_926.h2, PEqualNP.Outside.L_meta_926.h3, PEqualNP.Outside.L_meta_926.h4, PEqualNP.Outside.L_meta_926.h5, PEqualNP.Outside.L_meta_926.h6, PEqualNP.Outside.L_meta_926.h7, PEqualNP.Outside.L_meta_926.h8, PEqualNP.Outside.L_meta_926.h9, PEqualNP.Outside.L_meta_926.h10, PEqualNP.Outside.L_meta_926.h11, PEqualNP.Outside.L_meta_926.h12, PEqualNP.Outside.L_meta_926.h13, PEqualNP.Outside.L_meta_926.h14, PEqualNP.Outside.L_meta_926.h15, PEqualNP.Outside.L_meta_926.h16, PEqualNP.Outside.L_meta_926.h17, PEqualNP.Outside.L_meta_926.h18, PEqualNP.Outside.L_meta_926.h19, PEqualNP.Outside.L_meta_926.h20, PEqualNP.Outside.L_meta_926.h21, PEqualNP.Outside.L_meta_926.h22, PEqualNP.Outside.L_meta_926.h23, PEqualNP.Outside.L_meta_926.h24, PEqualNP.Outside.L_meta_926.h25, PEqualNP.Outside.L_meta_926.h26, PEqualNP.Outside.L_meta_926.h27, PEqualNP.Outside.L_meta_926.h28, PEqualNP.Outside.L_meta_926.h29, PEqualNP.Outside.L_meta_926.h30, PEqualNP.Outside.L_meta_926.h31, PEqualNP.Outside.L_meta_926.h32, PEqualNP.Outside.L_meta_926.h33, PEqualNP.Outside.L_meta_926.h34, PEqualNP.Outside.L_meta_926.h35, PEqualNP.Outside.L_meta_926.h36, PEqualNP.Outside.L_meta_926.h37, PEqualNP.Outside.L_meta_926.h38, PEqualNP.Outside.L_meta_926.h39, PEqualNP.Outside.L_meta_926.h40, PEqualNP.Outside.L_meta_926.h41, PEqualNP.Outside.L_meta_926.h42, PEqualNP.Outside.L_meta_926.h43, PEqualNP.Outside.L_meta_926.h44, PEqualNP.Outside.L_meta_926.h45, PEqualNP.Outside.L_meta_926.h46, PEqualNP.Outside.L_meta_926.h47, PEqualNP.Outside.L_meta_926.h48, PEqualNP.Outside.L_meta_926.h49, PEqualNP.Outside.L_meta_926.h50, PEqualNP.Outside.L_meta_926.h51, PEqualNP.Outside.L_meta_926.h52, PEqualNP.Outside.L_meta_926.h53, PEqualNP.Outside.L_meta_926.h54, PEqualNP.Outside.L_meta_926.h55, PEqualNP.Outside.L_meta_926.h56, PEqualNP.Outside.L_meta_926.h57, PEqualNP.Outside.L_meta_926.h58, PEqualNP.Outside.L_meta_926.h59, PEqualNP.Outside.L_meta_926.h60, PEqualNP.Outside.L_meta_926.h61, PEqualNP.Outside.L_meta_926.h62, PEqualNP.Outside.L_meta_926.h63, PEqualNP.Outside.L_meta_926.h64, PEqualNP.Outside.L_meta_926.h65, PEqualNP.Outside.L_meta_926.h66, PEqualNP.Outside.L_meta_926.h67, PEqualNP.Outside.L_meta_926.h68, PEqualNP.Outside.L_meta_926.h69, PEqualNP.Outside.L_meta_926.h70, PEqualNP.Outside.L_meta_926.h71, PEqualNP.Outside.L_meta_926.h72, PEqualNP.Outside.L_meta_926.h73, PEqualNP.Outside.L_meta_926.h74, PEqualNP.Outside.L_meta_926.h75, PEqualNP.Outside.L_meta_926.h76, PEqualNP.Outside.L_meta_926.h77, PEqualNP.Outside.L_meta_926.h78, PEqualNP.Outside.L_meta_926.h79, PEqualNP.Outside.L_meta_926.h80, PEqualNP.Outside.L_meta_926.h81, PEqualNP.Outside.L_meta_926.h82, PEqualNP.Outside.L_meta_926.h83, PEqualNP.Outside.L_meta_926.h84, PEqualNP.Outside.L_meta_926.h85⟩
