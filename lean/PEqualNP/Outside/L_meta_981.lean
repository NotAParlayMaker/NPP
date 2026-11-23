import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_981

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b3 && b5) || (b4 && b5)) := by
  decide +kernel

def C1 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem ok1 : FanInTwo C1 := by
  intro g hg
  simp only [C1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev1 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C1.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C2 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem ok2 : FanInTwo C2 := by
  intro g hg
  simp only [C2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev2 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C2.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5) || (b4 && b6)) := by
  decide +kernel

def C3 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem ok3 : FanInTwo C3 := by
  intro g hg
  simp only [C3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev3 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C3.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b4 && b6)) := by
  decide +kernel

def C4 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem ok4 : FanInTwo C4 := by
  intro g hg
  simp only [C4, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev4 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C4.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b3 && b5) || (b4 && b6)) := by
  decide +kernel

def C5 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem ok5 : FanInTwo C5 := by
  intro g hg
  simp only [C5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev5 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C5.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b4 && b5) || (b5 && b6)) := by
  decide +kernel

def C6 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem ok6 : FanInTwo C6 := by
  intro g hg
  simp only [C6, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev6 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C6.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b4 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide +kernel

def C7 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem ok7 : FanInTwo C7 := by
  intro g hg
  simp only [C7, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev7 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C7.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b3 && b6) || (b4 && b5)) := by
  decide +kernel

def C8 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem ok8 : FanInTwo C8 := by
  intro g hg
  simp only [C8, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev8 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C8.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide +kernel

def C9 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ok9 : FanInTwo C9 := by
  intro g hg
  simp only [C9, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev9 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C9.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b0 && b6) || (b1 && b2) || (b3 && b4)) := by
  decide +kernel

def C10 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ok10 : FanInTwo C10 := by
  intro g hg
  simp only [C10, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev10 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C10.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b1 && b6) || (b3 && b4)) := by
  decide +kernel

def C11 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok11 : FanInTwo C11 := by
  intro g hg
  simp only [C11, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev11 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C11.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C12 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ok12 : FanInTwo C12 := by
  intro g hg
  simp only [C12, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev12 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C12.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b1 && b6) || (b3 && b4)) := by
  decide +kernel

def C13 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok13 : FanInTwo C13 := by
  intro g hg
  simp only [C13, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev13 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C13.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b2 && b6) || (b3 && b4)) := by
  decide +kernel

def C14 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ok14 : FanInTwo C14 := by
  intro g hg
  simp only [C14, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev14 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C14.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b3 && b4) || (b3 && b6)) := by
  decide +kernel

def C15 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok15 : FanInTwo C15 := by
  intro g hg
  simp only [C15, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev15 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C15.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C16 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ok16 : FanInTwo C16 := by
  intro g hg
  simp only [C16, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev16 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C16.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b3 && b6) || (b5 && b6)) := by
  decide +kernel

def C17 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok17 : FanInTwo C17 := by
  intro g hg
  simp only [C17, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev17 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C17.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5) || (b3 && b6) || (b5 && b6)) := by
  decide +kernel

def C18 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok18 : FanInTwo C18 := by
  intro g hg
  simp only [C18, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev18 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C18.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide +kernel

def C19 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok19 : FanInTwo C19 := by
  intro g hg
  simp only [C19, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev19 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C19.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b2 && b5) || (b3 && b6) || (b4 && b6)) := by
  decide +kernel

def C20 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok20 : FanInTwo C20 := by
  intro g hg
  simp only [C20, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev20 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C20.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b3 && b6) || (b4 && b5)) := by
  decide +kernel

def C21 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok21 : FanInTwo C21 := by
  intro g hg
  simp only [C21, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev21 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C21.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b3 && b6) || (b5 && b6)) := by
  decide +kernel

def C22 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [12, 6]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ok22 : FanInTwo C22 := by
  intro g hg
  simp only [C22, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev22 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C22.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b4 && b5) || (b5 && b6)) := by
  decide +kernel

def C23 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok23 : FanInTwo C23 := by
  intro g hg
  simp only [C23, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev23 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C23.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide +kernel

def C24 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok24 : FanInTwo C24 := by
  intro g hg
  simp only [C24, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev24 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C24.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b4 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide +kernel

def C25 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem ok25 : FanInTwo C25 := by
  intro g hg
  simp only [C25, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev25 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C25.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b3 && b6) || (b4 && b5) || (b4 && b6)) := by
  decide +kernel

def C26 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem ok26 : FanInTwo C26 := by
  intro g hg
  simp only [C26, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev26 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C26.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b0 && b6) || (b1 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C27 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem ok27 : FanInTwo C27 := by
  intro g hg
  simp only [C27, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev27 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C27.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b1 && b6) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C28 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem ok28 : FanInTwo C28 := by
  intro g hg
  simp only [C28, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev28 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C28.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b3 && b4) || (b3 && b6) || (b5 && b6)) := by
  decide +kernel

def C29 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [13, 5]⟩, ⟨GateOp.and, [6, 14]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [16, 12]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem ok29 : FanInTwo C29 := by
  intro g hg
  simp only [C29, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev29 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C29.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b2 && b5) || (b3 && b6) || (b4 && b6) || (b5 && b6)) := by
  decide +kernel

def C30 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 14]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [16, 13]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem ok30 : FanInTwo C30 := by
  intro g hg
  simp only [C30, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev30 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C30.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b3 && b6) || (b4 && b5) || (b5 && b6)) := by
  decide +kernel

theorem ofFn6 (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

theorem ofFn7 (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_981

theorem PEqualNP.Outside.L_meta_981 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) 10) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) 11) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 12) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) 12) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) 12) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) 12) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) 12) :=
  ⟨⟨PEqualNP.Outside.L_meta_981.C0, PEqualNP.Outside.L_meta_981.ok0, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn6]
      exact PEqualNP.Outside.L_meta_981.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C1, PEqualNP.Outside.L_meta_981.ok1, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C2, PEqualNP.Outside.L_meta_981.ok2, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev2 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C3, PEqualNP.Outside.L_meta_981.ok3, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev3 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C4, PEqualNP.Outside.L_meta_981.ok4, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev4 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C5, PEqualNP.Outside.L_meta_981.ok5, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev5 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C6, PEqualNP.Outside.L_meta_981.ok6, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev6 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C7, PEqualNP.Outside.L_meta_981.ok7, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C8, PEqualNP.Outside.L_meta_981.ok8, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev8 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C9, PEqualNP.Outside.L_meta_981.ok9, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev9 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C10, PEqualNP.Outside.L_meta_981.ok10, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev10 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C11, PEqualNP.Outside.L_meta_981.ok11, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev11 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C12, PEqualNP.Outside.L_meta_981.ok12, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev12 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C13, PEqualNP.Outside.L_meta_981.ok13, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev13 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C14, PEqualNP.Outside.L_meta_981.ok14, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev14 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C15, PEqualNP.Outside.L_meta_981.ok15, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev15 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C16, PEqualNP.Outside.L_meta_981.ok16, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev16 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C17, PEqualNP.Outside.L_meta_981.ok17, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev17 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C18, PEqualNP.Outside.L_meta_981.ok18, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev18 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C19, PEqualNP.Outside.L_meta_981.ok19, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev19 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C20, PEqualNP.Outside.L_meta_981.ok20, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev20 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C21, PEqualNP.Outside.L_meta_981.ok21, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev21 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C22, PEqualNP.Outside.L_meta_981.ok22, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev22 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C23, PEqualNP.Outside.L_meta_981.ok23, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev23 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C24, PEqualNP.Outside.L_meta_981.ok24, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev24 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C25, PEqualNP.Outside.L_meta_981.ok25, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev25 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C26, PEqualNP.Outside.L_meta_981.ok26, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev26 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C27, PEqualNP.Outside.L_meta_981.ok27, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev27 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C28, PEqualNP.Outside.L_meta_981.ok28, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev28 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C29, PEqualNP.Outside.L_meta_981.ok29, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev29 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_981.C30, PEqualNP.Outside.L_meta_981.ok30, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_981.ofFn7]
      exact PEqualNP.Outside.L_meta_981.ev30 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩⟩
