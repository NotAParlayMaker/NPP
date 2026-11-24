import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
lemma w0 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  refine ⟨⟨[⟨GateOp.and, [0, 1]⟩], 2⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w1 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  refine ⟨⟨[⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [0, 3]⟩], 4⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [3, 1]⟩, ⟨GateOp.and, [5, 4]⟩], 6⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w3 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  refine ⟨⟨[⟨GateOp.and, [3, 2]⟩, ⟨GateOp.and, [1, 0]⟩, ⟨GateOp.or, [5, 4]⟩], 6⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  refine ⟨⟨[⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [5, 0]⟩], 6⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  refine ⟨⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [4, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 0]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [6, 7]⟩], 8⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w7 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  refine ⟨⟨[⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [7, 5]⟩], 8⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  refine ⟨⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [5, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [7, 0]⟩], 8⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  refine ⟨⟨[⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [5, 1]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [6, 0]⟩, ⟨GateOp.or, [7, 8]⟩], 9⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [1, 0]⟩, ⟨GateOp.and, [5, 2]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  refine ⟨⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [4, 0]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [6, 8]⟩], 9⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [7, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [6, 1]⟩, ⟨GateOp.and, [7, 0]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  refine ⟨⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [6, 1]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [10, 8]⟩], 11⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [7, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [10, 0]⟩, ⟨GateOp.or, [7, 11]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w17 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [5, 4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.and, [2, 0]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [10, 8]⟩], 11⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  refine ⟨⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  refine ⟨⟨[⟨GateOp.or, [5, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [7, 1]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.and, [0, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [8, 1]⟩, ⟨GateOp.or, [9, 10]⟩], 11⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  refine ⟨⟨[⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [10, 2]⟩, ⟨GateOp.or, [11, 9]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.and, [10, 9]⟩], 11⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 1]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.and, [8, 2]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [5, 1]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [1, 0]⟩, ⟨GateOp.or, [8, 7]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [5, 1]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [6, 3]⟩, ⟨GateOp.or, [8, 7]⟩, ⟨GateOp.or, [4, 0]⟩, ⟨GateOp.and, [10, 2]⟩, ⟨GateOp.or, [11, 9]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [11, 9]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.and, [8, 0]⟩, ⟨GateOp.and, [9, 1]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [9, 6]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [10, 0]⟩, ⟨GateOp.and, [11, 12]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [3, 1]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [4, 1]⟩, ⟨GateOp.and, [7, 2]⟩, ⟨GateOp.or, [11, 10]⟩, ⟨GateOp.or, [12, 9]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [3, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [2, 0]⟩, ⟨GateOp.and, [9, 1]⟩, ⟨GateOp.or, [8, 0]⟩, ⟨GateOp.and, [11, 7]⟩, ⟨GateOp.or, [12, 10]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [10, 4]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [5, 1]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [7, 2]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [2, 0]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [2, 0]⟩, ⟨GateOp.and, [12, 1]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [5, 2]⟩, ⟨GateOp.or, [5, 1]⟩, ⟨GateOp.and, [7, 3]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [12, 8]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [8, 0]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.and, [13, 12]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [4, 3]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [11, 7]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.and, [10, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [2, 0]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.and, [6, 0]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w42 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨⟨[⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [7, 4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [9, 1]⟩, ⟨GateOp.and, [10, 0]⟩, ⟨GateOp.or, [8, 11]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [2, 0]⟩, ⟨GateOp.or, [2, 0]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [12, 8]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [3, 0]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [9, 2]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [10, 4]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [7, 12]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [0, 11]⟩], 12⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [4, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [7, 1]⟩, ⟨GateOp.or, [9, 8]⟩, ⟨GateOp.and, [10, 0]⟩, ⟨GateOp.and, [6, 1]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [8, 1]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.and, [12, 0]⟩, ⟨GateOp.or, [13, 10]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.and, [7, 1]⟩, ⟨GateOp.or, [9, 0]⟩, ⟨GateOp.or, [8, 1]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.and, [12, 10]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [5, 1]⟩, ⟨GateOp.or, [9, 0]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [12, 10]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [9, 1]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [2, 0]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [12, 9]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [6, 5]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [8, 0]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [7, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [12, 9]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [6, 2]⟩, ⟨GateOp.or, [5, 0]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [10, 1]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [12, 9]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [5, 2]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [6, 1]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [12, 10]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [4, 1]⟩, ⟨GateOp.or, [9, 0]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [12, 10]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [7, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [9, 4]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.and, [10, 0]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 8]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [3, 1]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.and, [10, 4]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [9, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [5, 1]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.and, [12, 4]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  refine ⟨⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [9, 6]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.or, [11, 5]⟩, ⟨GateOp.and, [12, 0]⟩, ⟨GateOp.or, [7, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [11, 8]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.and, [9, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [9, 1]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [3, 1]⟩, ⟨GateOp.or, [1, 0]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [5, 0]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [11, 9]⟩, ⟨GateOp.or, [12, 2]⟩, ⟨GateOp.and, [8, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [5, 1]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [4, 1]⟩, ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [12, 0]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.and, [9, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [6, 3]⟩, ⟨GateOp.or, [3, 1]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [11, 8]⟩, ⟨GateOp.and, [10, 1]⟩, ⟨GateOp.or, [13, 9]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [9, 1]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [12, 1]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [7, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [4, 1]⟩, ⟨GateOp.and, [13, 0]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [13, 5]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [13, 12]⟩, ⟨GateOp.or, [14, 11]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [9, 1]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [13, 11]⟩, ⟨GateOp.or, [14, 8]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [4, 0]⟩, ⟨GateOp.and, [7, 1]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.and, [10, 3]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [13, 12]⟩, ⟨GateOp.or, [14, 11]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.and, [10, 3]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [1, 0]⟩, ⟨GateOp.or, [9, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [12, 5]⟩, ⟨GateOp.and, [11, 10]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [9, 0]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [14, 8]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [11, 6]⟩, ⟨GateOp.or, [13, 12]⟩, ⟨GateOp.or, [10, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.and, [5, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [9, 4]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [13, 12]⟩, ⟨GateOp.or, [7, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

set_option maxRecDepth 100000 in
lemma w84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [6, 2]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [8, 4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [10, 2]⟩, ⟨GateOp.and, [11, 0]⟩, ⟨GateOp.and, [7, 5]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    decide +revert

end PEqualNP.Outside.L_meta_926_aux

open PEqualNP.Outside.L_meta_926_aux

theorem PEqualNP.Outside.L_meta_926 :
    (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80, w81, w82, w83, w84⟩
