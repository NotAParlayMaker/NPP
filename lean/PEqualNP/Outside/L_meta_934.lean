import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_934_aux
open PEqualNP.CircuitLowerBounds
-- Every circuit below is the one given in the statement; the kernel evaluates it on all inputs.
theorem shape8 (x : Fin 8 → Bool) : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  funext i
  fin_cases i <;> rfl
theorem list8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]
set_option maxRecDepth 100000 in
theorem t1 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 3), (2, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f1 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c1 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 3), (2, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f1, by decide, fun x => ?_⟩
  have h := t1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t2 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 3), (3, 4), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f2 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c2 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 3), (3, 4), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f2, by decide, fun x => ?_⟩
  have h := t2 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t3 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 4), (3, 6), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f3 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c3 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 4), (3, 6), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f3, by decide, fun x => ?_⟩
  have h := t3 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t4 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 4), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f4 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c4 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 4), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f4, by decide, fun x => ?_⟩
  have h := t4 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t5 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 5), (3, 6), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f5 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c5 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 5), (3, 6), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f5, by decide, fun x => ?_⟩
  have h := t5 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t6 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 6), (3, 6), (4, 5), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f6 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c6 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 6), (3, 6), (4, 5), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f6, by decide, fun x => ?_⟩
  have h := t6 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t7 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 7), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f7 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c7 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (2, 7), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f7, by decide, fun x => ?_⟩
  have h := t7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t8 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 2), (1, 2), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f8 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c8 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 2), (1, 2), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f8, by decide, fun x => ?_⟩
  have h := t8 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t9 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 2), (1, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f9 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c9 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 2), (1, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f9, by decide, fun x => ?_⟩
  have h := t9 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t10 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 3), (1, 3), (2, 4), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f10 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c10 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 3), (1, 3), (2, 4), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f10, by decide, fun x => ?_⟩
  have h := t10 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t11 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 3), (1, 4), (2, 7), (3, 4), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f11 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c11 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 3), (1, 4), (2, 7), (3, 4), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f11, by decide, fun x => ?_⟩
  have h := t11 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
set_option maxRecDepth 100000 in
theorem t12 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 3), (1, 7), (2, 7), (3, 7), (4, 5), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧
        (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) u = true ∧ (![b0, b1, b2, b3, b4, b5, b6, b7] : Fin 8 → Bool) v = true) := by
  decide +kernel
theorem f12 : PEqualNP.MetaComplexity.FanInTwo (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem c12 (C : Circuit) (h : C = (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩ : Circuit)) :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 3), (1, 7), (2, 7), (3, 7), (4, 5), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  subst h
  refine ⟨f12, by decide, fun x => ?_⟩
  have h := t12 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [← shape8 x] at h
  rw [list8 x]
  exact h
end PEqualNP.Outside.L_meta_934_aux
theorem PEqualNP.Outside.L_meta_934 : (∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 10 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 1), (2, 3), (2, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true))) ∧ (∀ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C2 ∧ C2.size = 10 ∧ (∀ x2 : Fin 8 → Bool, (C2.eval (List.ofFn x2) = true ↔ ∃ u2 v2 : Fin 8, (u2.val, v2.val) ∈ ([(0, 1), (2, 3), (3, 4), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x2 u2 = true ∧ x2 v2 = true))) ∧ (∀ C3 : PEqualNP.CircuitLowerBounds.Circuit, C3 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C3 ∧ C3.size = 10 ∧ (∀ x3 : Fin 8 → Bool, (C3.eval (List.ofFn x3) = true ↔ ∃ u3 v3 : Fin 8, (u3.val, v3.val) ∈ ([(0, 1), (2, 4), (3, 6), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x3 u3 = true ∧ x3 v3 = true))) ∧ (∀ C4 : PEqualNP.CircuitLowerBounds.Circuit, C4 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C4 ∧ C4.size = 10 ∧ (∀ x4 : Fin 8 → Bool, (C4.eval (List.ofFn x4) = true ↔ ∃ u4 v4 : Fin 8, (u4.val, v4.val) ∈ ([(0, 1), (2, 4), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x4 u4 = true ∧ x4 v4 = true))) ∧ (∀ C5 : PEqualNP.CircuitLowerBounds.Circuit, C5 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C5 ∧ C5.size = 10 ∧ (∀ x5 : Fin 8 → Bool, (C5.eval (List.ofFn x5) = true ↔ ∃ u5 v5 : Fin 8, (u5.val, v5.val) ∈ ([(0, 1), (2, 5), (3, 6), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x5 u5 = true ∧ x5 v5 = true))) ∧ (∀ C6 : PEqualNP.CircuitLowerBounds.Circuit, C6 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C6 ∧ C6.size = 10 ∧ (∀ x6 : Fin 8 → Bool, (C6.eval (List.ofFn x6) = true ↔ ∃ u6 v6 : Fin 8, (u6.val, v6.val) ∈ ([(0, 1), (2, 6), (3, 6), (4, 5), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x6 u6 = true ∧ x6 v6 = true))) ∧ (∀ C7 : PEqualNP.CircuitLowerBounds.Circuit, C7 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C7 ∧ C7.size = 10 ∧ (∀ x7 : Fin 8 → Bool, (C7.eval (List.ofFn x7) = true ↔ ∃ u7 v7 : Fin 8, (u7.val, v7.val) ∈ ([(0, 1), (2, 7), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x7 u7 = true ∧ x7 v7 = true))) ∧ (∀ C8 : PEqualNP.CircuitLowerBounds.Circuit, C8 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C8 ∧ C8.size = 10 ∧ (∀ x8 : Fin 8 → Bool, (C8.eval (List.ofFn x8) = true ↔ ∃ u8 v8 : Fin 8, (u8.val, v8.val) ∈ ([(0, 2), (1, 2), (3, 4), (3, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x8 u8 = true ∧ x8 v8 = true))) ∧ (∀ C9 : PEqualNP.CircuitLowerBounds.Circuit, C9 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C9 ∧ C9.size = 10 ∧ (∀ x9 : Fin 8 → Bool, (C9.eval (List.ofFn x9) = true ↔ ∃ u9 v9 : Fin 8, (u9.val, v9.val) ∈ ([(0, 2), (1, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x9 u9 = true ∧ x9 v9 = true))) ∧ (∀ C10 : PEqualNP.CircuitLowerBounds.Circuit, C10 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C10 ∧ C10.size = 10 ∧ (∀ x10 : Fin 8 → Bool, (C10.eval (List.ofFn x10) = true ↔ ∃ u10 v10 : Fin 8, (u10.val, v10.val) ∈ ([(0, 3), (1, 3), (2, 4), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x10 u10 = true ∧ x10 v10 = true))) ∧ (∀ C11 : PEqualNP.CircuitLowerBounds.Circuit, C11 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C11 ∧ C11.size = 10 ∧ (∀ x11 : Fin 8 → Bool, (C11.eval (List.ofFn x11) = true ↔ ∃ u11 v11 : Fin 8, (u11.val, v11.val) ∈ ([(0, 3), (1, 4), (2, 7), (3, 4), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x11 u11 = true ∧ x11 v11 = true))) ∧ (∀ C12 : PEqualNP.CircuitLowerBounds.Circuit, C12 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C12 ∧ C12.size = 10 ∧ (∀ x12 : Fin 8 → Bool, (C12.eval (List.ofFn x12) = true ↔ ∃ u12 v12 : Fin 8, (u12.val, v12.val) ∈ ([(0, 3), (1, 7), (2, 7), (3, 7), (4, 5), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x12 u12 = true ∧ x12 v12 = true))) :=
  ⟨fun C h => PEqualNP.Outside.L_meta_934_aux.c1 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c2 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c3 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c4 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c5 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c6 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c7 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c8 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c9 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c10 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c11 C h,
   fun C h => PEqualNP.Outside.L_meta_934_aux.c12 C h⟩
