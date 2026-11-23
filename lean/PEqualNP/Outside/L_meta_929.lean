import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_929

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩], 2⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl <;> simp

theorem ev0 : ∀ b0 b1 : Bool,
    C0.eval [b0, b1] = ((b0 && b1)) := by
  decide +kernel

def C1 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩], 4⟩

theorem ok1 : Monotone2 C1 := by
  intro g hg
  simp only [C1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

theorem ev1 : ∀ b0 b1 b2 : Bool,
    C1.eval [b0, b1, b2] = ((b0 && b1) || (b0 && b2)) := by
  decide +kernel

def C2 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

theorem ok2 : Monotone2 C2 := by
  intro g hg
  simp only [C2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem ev2 : ∀ b0 b1 b2 : Bool,
    C2.eval [b0, b1, b2] = ((b0 && b1) || (b0 && b2) || (b1 && b2)) := by
  decide +kernel

def C3 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

theorem ok3 : Monotone2 C3 := by
  intro g hg
  simp only [C3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem ev3 : ∀ b0 b1 b2 b3 : Bool,
    C3.eval [b0, b1, b2, b3] = ((b0 && b1) || (b2 && b3)) := by
  decide +kernel

def C4 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩], 6⟩

theorem ok4 : Monotone2 C4 := by
  intro g hg
  simp only [C4, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem ev4 : ∀ b0 b1 b2 b3 : Bool,
    C4.eval [b0, b1, b2, b3] = ((b0 && b1) || (b0 && b2) || (b0 && b3)) := by
  decide +kernel

def C5 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩

theorem ok5 : Monotone2 C5 := by
  intro g hg
  simp only [C5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem ev5 : ∀ b0 b1 b2 b3 : Bool,
    C5.eval [b0, b1, b2, b3] = ((b0 && b1) || (b0 && b2) || (b1 && b3)) := by
  decide +kernel

def C6 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 7]⟩], 8⟩

theorem ok6 : Monotone2 C6 := by
  intro g hg
  simp only [C6, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev6 : ∀ b0 b1 b2 b3 : Bool,
    C6.eval [b0, b1, b2, b3] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2)) := by
  decide +kernel

def C7 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩], 8⟩

theorem ok7 : Monotone2 C7 := by
  intro g hg
  simp only [C7, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem ev7 : ∀ b0 b1 b2 b3 b4 : Bool,
    C7.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b3 && b4)) := by
  decide +kernel

def C8 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩], 8⟩

theorem ok8 : Monotone2 C8 := by
  intro g hg
  simp only [C8, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem ev8 : ∀ b0 b1 b2 b3 b4 : Bool,
    C8.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4)) := by
  decide +kernel

def C9 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [7, 8]⟩], 9⟩

theorem ok9 : Monotone2 C9 := by
  intro g hg
  simp only [C9, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev9 : ∀ b0 b1 b2 b3 b4 : Bool,
    C9.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4)) := by
  decide +kernel

def C10 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩

theorem ok10 : Monotone2 C10 := by
  intro g hg
  simp only [C10, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev10 : ∀ b0 b1 b2 b3 b4 : Bool,
    C10.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4)) := by
  decide +kernel

def C11 : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [6, 8]⟩], 9⟩

theorem ok11 : Monotone2 C11 := by
  intro g hg
  simp only [C11, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev11 : ∀ b0 b1 b2 b3 b4 : Bool,
    C11.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4)) := by
  decide +kernel

def C12 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩

theorem ok12 : Monotone2 C12 := by
  intro g hg
  simp only [C12, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev12 : ∀ b0 b1 b2 b3 b4 : Bool,
    C12.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2)) := by
  decide +kernel

def C13 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩

theorem ok13 : Monotone2 C13 := by
  intro g hg
  simp only [C13, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev13 : ∀ b0 b1 b2 b3 b4 : Bool,
    C13.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4)) := by
  decide +kernel

def C14 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

theorem ok14 : Monotone2 C14 := by
  intro g hg
  simp only [C14, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev14 : ∀ b0 b1 b2 b3 b4 : Bool,
    C14.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4)) := by
  decide +kernel

def C15 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

theorem ok15 : Monotone2 C15 := by
  intro g hg
  simp only [C15, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev15 : ∀ b0 b1 b2 b3 b4 : Bool,
    C15.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b4)) := by
  decide +kernel

def C16 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem ok16 : Monotone2 C16 := by
  intro g hg
  simp only [C16, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev16 : ∀ b0 b1 b2 b3 b4 : Bool,
    C16.eval [b0, b1, b2, b3, b4] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b4)) := by
  decide +kernel

def C17 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩

theorem ok17 : Monotone2 C17 := by
  intro g hg
  simp only [C17, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev17 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C17.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b2 && b3) || (b4 && b5)) := by
  decide +kernel

def C18 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩

theorem ok18 : Monotone2 C18 := by
  intro g hg
  simp only [C18, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev18 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C18.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b4 && b5)) := by
  decide +kernel

def C19 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

theorem ok19 : Monotone2 C19 := by
  intro g hg
  simp only [C19, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev19 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C19.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b4 && b5)) := by
  decide +kernel

def C20 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩

theorem ok20 : Monotone2 C20 := by
  intro g hg
  simp only [C20, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev20 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C20.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b3 && b4) || (b3 && b5)) := by
  decide +kernel

def C21 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩], 10⟩

theorem ok21 : Monotone2 C21 := by
  intro g hg
  simp only [C21, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev21 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C21.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5)) := by
  decide +kernel

def C22 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [9, 10]⟩], 11⟩

theorem ok22 : Monotone2 C22 := by
  intro g hg
  simp only [C22, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev22 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C22.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5)) := by
  decide +kernel

def C23 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem ok23 : Monotone2 C23 := by
  intro g hg
  simp only [C23, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev23 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C23.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b4 && b5)) := by
  decide +kernel

def C24 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩

theorem ok24 : Monotone2 C24 := by
  intro g hg
  simp only [C24, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev24 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C24.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b1 && b5)) := by
  decide +kernel

def C25 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem ok25 : Monotone2 C25 := by
  intro g hg
  simp only [C25, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev25 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C25.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5)) := by
  decide +kernel

def C26 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩

theorem ok26 : Monotone2 C26 := by
  intro g hg
  simp only [C26, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev26 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C26.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b4 && b5)) := by
  decide +kernel

def C27 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem ok27 : Monotone2 C27 := by
  intro g hg
  simp only [C27, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev27 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C27.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4) || (b3 && b5)) := by
  decide +kernel

def C28 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem ok28 : Monotone2 C28 := by
  intro g hg
  simp only [C28, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev28 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C28.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5)) := by
  decide +kernel

def C29 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩

theorem ok29 : Monotone2 C29 := by
  intro g hg
  simp only [C29, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev29 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C29.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2)) := by
  decide +kernel

def C30 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem ok30 : Monotone2 C30 := by
  intro g hg
  simp only [C30, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev30 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C30.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5)) := by
  decide +kernel

def C31 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok31 : Monotone2 C31 := by
  intro g hg
  simp only [C31, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev31 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C31.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5)) := by
  decide +kernel

def C32 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok32 : Monotone2 C32 := by
  intro g hg
  simp only [C32, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev32 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C32.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b2 && b5)) := by
  decide +kernel

def C33 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok33 : Monotone2 C33 := by
  intro g hg
  simp only [C33, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev33 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C33.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5)) := by
  decide +kernel

def C34 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok34 : Monotone2 C34 := by
  intro g hg
  simp only [C34, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev34 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C34.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b3 && b5)) := by
  decide +kernel

def C35 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok35 : Monotone2 C35 := by
  intro g hg
  simp only [C35, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev35 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C35.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b4 && b5)) := by
  decide +kernel

def C36 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok36 : Monotone2 C36 := by
  intro g hg
  simp only [C36, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev36 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C36.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b5)) := by
  decide +kernel

def C37 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩

theorem ok37 : Monotone2 C37 := by
  intro g hg
  simp only [C37, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev37 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C37.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4) || (b3 && b5) || (b4 && b5)) := by
  decide +kernel

def C38 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok38 : Monotone2 C38 := by
  intro g hg
  simp only [C38, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev38 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C38.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b5)) := by
  decide +kernel

def C39 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok39 : Monotone2 C39 := by
  intro g hg
  simp only [C39, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev39 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C39.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b3 && b4)) := by
  decide +kernel

def C40 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok40 : Monotone2 C40 := by
  intro g hg
  simp only [C40, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev40 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C40.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b3 && b4)) := by
  decide +kernel

def C41 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok41 : Monotone2 C41 := by
  intro g hg
  simp only [C41, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev41 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C41.eval [b0, b1, b2, b3, b4, b5] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b4 && b5)) := by
  decide +kernel

def C42 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem ok42 : Monotone2 C42 := by
  intro g hg
  simp only [C42, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev42 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C42.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C43 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩

theorem ok43 : Monotone2 C43 := by
  intro g hg
  simp only [C43, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev43 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C43.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b5 && b6)) := by
  decide +kernel

def C44 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok44 : Monotone2 C44 := by
  intro g hg
  simp only [C44, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev44 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C44.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b5 && b6)) := by
  decide +kernel

def C45 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem ok45 : Monotone2 C45 := by
  intro g hg
  simp only [C45, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev45 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C45.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b4 && b5) || (b4 && b6)) := by
  decide +kernel

def C46 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩

theorem ok46 : Monotone2 C46 := by
  intro g hg
  simp only [C46, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev46 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C46.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C47 : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok47 : Monotone2 C47 := by
  intro g hg
  simp only [C47, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev47 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C47.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b5 && b6)) := by
  decide +kernel

def C48 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem ok48 : Monotone2 C48 := by
  intro g hg
  simp only [C48, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev48 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C48.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b4 && b5) || (b4 && b6)) := by
  decide +kernel

def C49 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩], 12⟩

theorem ok49 : Monotone2 C49 := by
  intro g hg
  simp only [C49, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev49 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C49.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b0 && b6)) := by
  decide +kernel

def C50 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem ok50 : Monotone2 C50 := by
  intro g hg
  simp only [C50, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev50 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C50.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b6)) := by
  decide +kernel

def C51 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok51 : Monotone2 C51 := by
  intro g hg
  simp only [C51, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev51 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C51.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b5 && b6)) := by
  decide +kernel

def C52 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

theorem ok52 : Monotone2 C52 := by
  intro g hg
  simp only [C52, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev52 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C52.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b1 && b6)) := by
  decide +kernel

def C53 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok53 : Monotone2 C53 := by
  intro g hg
  simp only [C53, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev53 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C53.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b2 && b6)) := by
  decide +kernel

def C54 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

theorem ok54 : Monotone2 C54 := by
  intro g hg
  simp only [C54, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev54 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C54.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b5 && b6)) := by
  decide +kernel

def C55 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok55 : Monotone2 C55 := by
  intro g hg
  simp only [C55, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev55 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C55.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b5 && b6)) := by
  decide +kernel

def C56 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem ok56 : Monotone2 C56 := by
  intro g hg
  simp only [C56, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev56 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C56.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C57 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok57 : Monotone2 C57 := by
  intro g hg
  simp only [C57, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev57 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C57.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b4 && b5) || (b4 && b6)) := by
  decide +kernel

def C58 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok58 : Monotone2 C58 := by
  intro g hg
  simp only [C58, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev58 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C58.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b1 && b5) || (b2 && b6)) := by
  decide +kernel

def C59 : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok59 : Monotone2 C59 := by
  intro g hg
  simp only [C59, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev59 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C59.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b3 && b6)) := by
  decide +kernel

def C60 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok60 : Monotone2 C60 := by
  intro g hg
  simp only [C60, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev60 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C60.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b6)) := by
  decide +kernel

def C61 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 12]⟩], 13⟩

theorem ok61 : Monotone2 C61 := by
  intro g hg
  simp only [C61, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev61 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C61.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b4 && b5) || (b4 && b6)) := by
  decide +kernel

def C62 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok62 : Monotone2 C62 := by
  intro g hg
  simp only [C62, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev62 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C62.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b4 && b5) || (b5 && b6)) := by
  decide +kernel

def C63 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok63 : Monotone2 C63 := by
  intro g hg
  simp only [C63, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev63 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C63.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b4 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide +kernel

def C64 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem ok64 : Monotone2 C64 := by
  intro g hg
  simp only [C64, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev64 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C64.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b2) || (b3 && b4) || (b3 && b5) || (b4 && b6)) := by
  decide +kernel

def C65 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem ok65 : Monotone2 C65 := by
  intro g hg
  simp only [C65, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev65 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C65.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b4) || (b5 && b6)) := by
  decide +kernel

def C66 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem ok66 : Monotone2 C66 := by
  intro g hg
  simp only [C66, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev66 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C66.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b6)) := by
  decide +kernel

def C67 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

theorem ok67 : Monotone2 C67 := by
  intro g hg
  simp only [C67, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev67 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C67.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b0 && b6) || (b1 && b2)) := by
  decide +kernel

def C68 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

theorem ok68 : Monotone2 C68 := by
  intro g hg
  simp only [C68, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev68 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C68.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b1 && b6)) := by
  decide +kernel

def C69 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok69 : Monotone2 C69 := by
  intro g hg
  simp only [C69, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev69 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C69.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) || (b1 && b2) || (b3 && b6)) := by
  decide +kernel

def C70 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩

theorem ok70 : Monotone2 C70 := by
  intro g hg
  simp only [C70, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev70 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C70.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b1 && b6)) := by
  decide +kernel

def C71 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok71 : Monotone2 C71 := by
  intro g hg
  simp only [C71, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev71 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C71.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b2 && b6)) := by
  decide +kernel

def C72 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok72 : Monotone2 C72 := by
  intro g hg
  simp only [C72, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev72 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C72.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b3 && b6)) := by
  decide +kernel

def C73 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok73 : Monotone2 C73 := by
  intro g hg
  simp only [C73, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev73 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C73.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b1 && b5) || (b5 && b6)) := by
  decide +kernel

def C74 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok74 : Monotone2 C74 := by
  intro g hg
  simp only [C74, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev74 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C74.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5) || (b3 && b6)) := by
  decide +kernel

def C75 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok75 : Monotone2 C75 := by
  intro g hg
  simp only [C75, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev75 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C75.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b2) || (b3 && b5) || (b5 && b6)) := by
  decide +kernel

def C76 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok76 : Monotone2 C76 := by
  intro g hg
  simp only [C76, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev76 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C76.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b1 && b6) || (b5 && b6)) := by
  decide +kernel

def C77 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok77 : Monotone2 C77 := by
  intro g hg
  simp only [C77, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev77 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C77.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b2 && b6) || (b5 && b6)) := by
  decide +kernel

def C78 : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok78 : Monotone2 C78 := by
  intro g hg
  simp only [C78, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev78 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C78.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b2 && b5) || (b3 && b6)) := by
  decide +kernel

def C79 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok79 : Monotone2 C79 := by
  intro g hg
  simp only [C79, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev79 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C79.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b3 && b6)) := by
  decide +kernel

def C80 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok80 : Monotone2 C80 := by
  intro g hg
  simp only [C80, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev80 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C80.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b1 && b4) || (b3 && b5) || (b5 && b6)) := by
  decide +kernel

def C81 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok81 : Monotone2 C81 := by
  intro g hg
  simp only [C81, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev81 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C81.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b2) || (b3 && b4) || (b4 && b5) || (b4 && b6)) := by
  decide +kernel

def C82 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok82 : Monotone2 C82 := by
  intro g hg
  simp only [C82, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev82 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C82.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b1 && b5) || (b2 && b6) || (b4 && b6)) := by
  decide +kernel

def C83 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok83 : Monotone2 C83 := by
  intro g hg
  simp only [C83, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev83 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C83.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b5) || (b4 && b6)) := by
  decide +kernel

def C84 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem ok84 : Monotone2 C84 := by
  intro g hg
  simp only [C84, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev84 : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    C84.eval [b0, b1, b2, b3, b4, b5, b6] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b6) || (b5 && b6)) := by
  decide +kernel

theorem ofFn2 (x : Fin 2 → Bool) : List.ofFn x = [x 0, x 1] := by
  simp [List.ofFn_succ]

theorem ofFn3 (x : Fin 3 → Bool) : List.ofFn x = [x 0, x 1, x 2] := by
  simp [List.ofFn_succ]

theorem ofFn4 (x : Fin 4 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3] := by
  simp [List.ofFn_succ]

theorem ofFn5 (x : Fin 5 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
  simp [List.ofFn_succ]

theorem ofFn6 (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

theorem ofFn7 (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_929

theorem PEqualNP.Outside.L_meta_929 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 1 ∧ ∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = (fun x : Fin 2 → Bool => (x 0 && x 1)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 2 ∧ ∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 3 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 3 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) :=
  ⟨⟨PEqualNP.Outside.L_meta_929.C0, PEqualNP.Outside.L_meta_929.ok0, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn2]
      exact PEqualNP.Outside.L_meta_929.ev0 (x 0) (x 1)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C1, PEqualNP.Outside.L_meta_929.ok1, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn3]
      exact PEqualNP.Outside.L_meta_929.ev1 (x 0) (x 1) (x 2)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C2, PEqualNP.Outside.L_meta_929.ok2, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn3]
      exact PEqualNP.Outside.L_meta_929.ev2 (x 0) (x 1) (x 2)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C3, PEqualNP.Outside.L_meta_929.ok3, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn4]
      exact PEqualNP.Outside.L_meta_929.ev3 (x 0) (x 1) (x 2) (x 3)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C4, PEqualNP.Outside.L_meta_929.ok4, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn4]
      exact PEqualNP.Outside.L_meta_929.ev4 (x 0) (x 1) (x 2) (x 3)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C5, PEqualNP.Outside.L_meta_929.ok5, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn4]
      exact PEqualNP.Outside.L_meta_929.ev5 (x 0) (x 1) (x 2) (x 3)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C6, PEqualNP.Outside.L_meta_929.ok6, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn4]
      exact PEqualNP.Outside.L_meta_929.ev6 (x 0) (x 1) (x 2) (x 3)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C7, PEqualNP.Outside.L_meta_929.ok7, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev7 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C8, PEqualNP.Outside.L_meta_929.ok8, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev8 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C9, PEqualNP.Outside.L_meta_929.ok9, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev9 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C10, PEqualNP.Outside.L_meta_929.ok10, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev10 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C11, PEqualNP.Outside.L_meta_929.ok11, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev11 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C12, PEqualNP.Outside.L_meta_929.ok12, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev12 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C13, PEqualNP.Outside.L_meta_929.ok13, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev13 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C14, PEqualNP.Outside.L_meta_929.ok14, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev14 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C15, PEqualNP.Outside.L_meta_929.ok15, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev15 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C16, PEqualNP.Outside.L_meta_929.ok16, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn5]
      exact PEqualNP.Outside.L_meta_929.ev16 (x 0) (x 1) (x 2) (x 3) (x 4)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C17, PEqualNP.Outside.L_meta_929.ok17, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev17 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C18, PEqualNP.Outside.L_meta_929.ok18, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev18 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C19, PEqualNP.Outside.L_meta_929.ok19, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev19 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C20, PEqualNP.Outside.L_meta_929.ok20, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev20 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C21, PEqualNP.Outside.L_meta_929.ok21, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev21 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C22, PEqualNP.Outside.L_meta_929.ok22, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev22 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C23, PEqualNP.Outside.L_meta_929.ok23, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev23 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C24, PEqualNP.Outside.L_meta_929.ok24, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev24 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C25, PEqualNP.Outside.L_meta_929.ok25, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev25 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C26, PEqualNP.Outside.L_meta_929.ok26, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev26 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C27, PEqualNP.Outside.L_meta_929.ok27, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev27 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C28, PEqualNP.Outside.L_meta_929.ok28, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev28 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C29, PEqualNP.Outside.L_meta_929.ok29, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev29 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C30, PEqualNP.Outside.L_meta_929.ok30, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev30 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C31, PEqualNP.Outside.L_meta_929.ok31, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev31 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C32, PEqualNP.Outside.L_meta_929.ok32, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev32 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C33, PEqualNP.Outside.L_meta_929.ok33, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev33 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C34, PEqualNP.Outside.L_meta_929.ok34, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev34 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C35, PEqualNP.Outside.L_meta_929.ok35, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev35 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C36, PEqualNP.Outside.L_meta_929.ok36, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev36 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C37, PEqualNP.Outside.L_meta_929.ok37, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev37 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C38, PEqualNP.Outside.L_meta_929.ok38, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev38 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C39, PEqualNP.Outside.L_meta_929.ok39, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev39 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C40, PEqualNP.Outside.L_meta_929.ok40, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev40 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C41, PEqualNP.Outside.L_meta_929.ok41, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn6]
      exact PEqualNP.Outside.L_meta_929.ev41 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C42, PEqualNP.Outside.L_meta_929.ok42, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev42 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C43, PEqualNP.Outside.L_meta_929.ok43, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev43 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C44, PEqualNP.Outside.L_meta_929.ok44, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev44 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C45, PEqualNP.Outside.L_meta_929.ok45, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev45 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C46, PEqualNP.Outside.L_meta_929.ok46, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev46 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C47, PEqualNP.Outside.L_meta_929.ok47, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev47 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C48, PEqualNP.Outside.L_meta_929.ok48, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev48 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C49, PEqualNP.Outside.L_meta_929.ok49, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev49 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C50, PEqualNP.Outside.L_meta_929.ok50, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev50 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C51, PEqualNP.Outside.L_meta_929.ok51, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev51 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C52, PEqualNP.Outside.L_meta_929.ok52, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev52 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C53, PEqualNP.Outside.L_meta_929.ok53, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev53 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C54, PEqualNP.Outside.L_meta_929.ok54, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev54 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C55, PEqualNP.Outside.L_meta_929.ok55, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev55 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C56, PEqualNP.Outside.L_meta_929.ok56, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev56 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C57, PEqualNP.Outside.L_meta_929.ok57, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev57 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C58, PEqualNP.Outside.L_meta_929.ok58, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev58 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C59, PEqualNP.Outside.L_meta_929.ok59, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev59 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C60, PEqualNP.Outside.L_meta_929.ok60, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev60 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C61, PEqualNP.Outside.L_meta_929.ok61, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev61 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C62, PEqualNP.Outside.L_meta_929.ok62, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev62 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C63, PEqualNP.Outside.L_meta_929.ok63, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev63 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C64, PEqualNP.Outside.L_meta_929.ok64, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev64 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C65, PEqualNP.Outside.L_meta_929.ok65, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev65 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C66, PEqualNP.Outside.L_meta_929.ok66, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev66 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C67, PEqualNP.Outside.L_meta_929.ok67, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev67 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C68, PEqualNP.Outside.L_meta_929.ok68, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev68 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C69, PEqualNP.Outside.L_meta_929.ok69, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev69 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C70, PEqualNP.Outside.L_meta_929.ok70, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev70 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C71, PEqualNP.Outside.L_meta_929.ok71, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev71 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C72, PEqualNP.Outside.L_meta_929.ok72, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev72 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C73, PEqualNP.Outside.L_meta_929.ok73, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev73 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C74, PEqualNP.Outside.L_meta_929.ok74, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev74 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C75, PEqualNP.Outside.L_meta_929.ok75, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev75 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C76, PEqualNP.Outside.L_meta_929.ok76, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev76 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C77, PEqualNP.Outside.L_meta_929.ok77, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev77 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C78, PEqualNP.Outside.L_meta_929.ok78, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev78 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C79, PEqualNP.Outside.L_meta_929.ok79, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev79 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C80, PEqualNP.Outside.L_meta_929.ok80, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev80 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C81, PEqualNP.Outside.L_meta_929.ok81, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev81 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C82, PEqualNP.Outside.L_meta_929.ok82, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev82 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C83, PEqualNP.Outside.L_meta_929.ok83, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev83 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩,
    ⟨PEqualNP.Outside.L_meta_929.C84, PEqualNP.Outside.L_meta_929.ok84, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_929.ofFn7]
      exact PEqualNP.Outside.L_meta_929.ev84 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩⟩
