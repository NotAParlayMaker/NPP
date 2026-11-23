import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_926

set_option maxRecDepth 100000 in
theorem c1 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 1] }], output := 2 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c2 : (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 3] }], output := 4 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c3 : (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.or, inputs := [3, 5] }], output := 6 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c4 : (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [2, 3] }, { op := GateOp.or, inputs := [4, 5] }], output := 6 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c5 : (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [4, 3] }, { op := GateOp.and, inputs := [0, 5] }], output := 6 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c6 : (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 5] }, { op := GateOp.or, inputs := [4, 6] }], output := 7 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c7 : (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 4] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 6] }, { op := GateOp.or, inputs := [5, 7] }], output := 8 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c8 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 5] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [6, 7] }], output := 8 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c9 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 3] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.and, inputs := [0, 7] }], output := 8 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c10 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 5] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [6, 8] }], output := 9 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c11 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 6] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.or, inputs := [9, 8] }], output := 10 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c12 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 5] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [2, 7] }, { op := GateOp.or, inputs := [6, 8] }], output := 9 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c13 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [5, 4] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [7, 9] }], output := 10 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c14 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 5] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [6, 9] }], output := 10 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c15 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 6] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [3, 8] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.or, inputs := [10, 9] }], output := 11 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c16 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 6] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [4, 8] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.or, inputs := [10, 9] }], output := 11 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c17 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [0, 5] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [3, 9] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [11, 10] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c18 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [2, 3] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [9, 8] }], output := 10 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c19 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [8, 9] }], output := 10 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c20 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [10, 9] }], output := 11 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c21 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [3, 8] }, { op := GateOp.or, inputs := [7, 9] }], output := 10 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c22 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [0, 9] }], output := 10 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c23 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [8, 10] }], output := 11 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c24 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [11, 10] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c25 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [7, 10] }], output := 11 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c26 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 3] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [2, 9] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [11, 10] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c27 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.and, inputs := [4, 9] }, { op := GateOp.or, inputs := [8, 10] }], output := 11 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c28 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [3, 9] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [11, 10] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c29 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [2, 7] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.and, inputs := [3, 9] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [11, 10] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c30 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c31 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [8, 11] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c32 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [3, 10] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c33 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 3] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [2, 10] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c34 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [3, 10] }, { op := GateOp.or, inputs := [6, 9] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c35 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [3, 10] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c36 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c37 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [5, 10] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c38 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.and, inputs := [3, 5] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [12, 9] }, { op := GateOp.or, inputs := [13, 11] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c39 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.and, inputs := [3, 8] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c40 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 4] }, { op := GateOp.or, inputs := [6, 5] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [3, 11] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c41 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [3, 11] }, { op := GateOp.or, inputs := [7, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c42 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [3, 4] }, { op := GateOp.and, inputs := [5, 11] }, { op := GateOp.or, inputs := [7, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c43 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [11, 10] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c44 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [10, 11] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c45 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c46 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [9, 11] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c47 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [12, 10] }, { op := GateOp.or, inputs := [13, 11] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c48 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [2, 9] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c49 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [12, 11] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c50 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.or, inputs := [10, 6] }, { op := GateOp.and, inputs := [0, 11] }], output := 12 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c51 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [1, 11] }, { op := GateOp.or, inputs := [10, 12] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c52 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c53 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.or, inputs := [10, 6] }, { op := GateOp.and, inputs := [1, 11] }, { op := GateOp.or, inputs := [9, 12] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c54 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [3, 4] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [2, 11] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c55 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.and, inputs := [5, 11] }, { op := GateOp.or, inputs := [10, 12] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c56 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [9, 4] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [8, 11] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c57 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [3, 10] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [13, 11] }, { op := GateOp.or, inputs := [14, 12] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c58 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c59 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 3] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [2, 11] }, { op := GateOp.or, inputs := [7, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c60 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [2, 9] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [3, 11] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c61 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [2, 9] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c62 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.or, inputs := [10, 6] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [9, 12] }], output := 13 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c63 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.and, inputs := [5, 11] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c64 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [4, 6] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.and, inputs := [5, 11] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c65 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.and, inputs := [3, 5] }, { op := GateOp.or, inputs := [3, 6] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [13, 10] }, { op := GateOp.or, inputs := [14, 12] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c66 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [13, 11] }, { op := GateOp.or, inputs := [14, 12] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c67 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.and, inputs := [3, 9] }, { op := GateOp.or, inputs := [2, 6] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [13, 12] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c68 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.or, inputs := [9, 6] }, { op := GateOp.and, inputs := [0, 10] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 12] }, { op := GateOp.or, inputs := [11, 13] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c69 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [1, 12] }, { op := GateOp.or, inputs := [10, 13] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c70 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 4] }, { op := GateOp.or, inputs := [7, 5] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [3, 12] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c71 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [10, 5] }, { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [1, 12] }, { op := GateOp.or, inputs := [9, 13] }], output := 14 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c72 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [3, 4] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [2, 12] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c73 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [3, 12] }, { op := GateOp.or, inputs := [8, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c74 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c75 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [3, 12] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c76 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [3, 6] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c77 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c78 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [6, 12] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c79 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [2, 10] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [3, 12] }, { op := GateOp.or, inputs := [8, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c80 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.and, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [3, 12] }, { op := GateOp.or, inputs := [7, 10] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c81 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [9, 4] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [3, 6] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [8, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c82 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [4, 12] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c83 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [6, 12] }, { op := GateOp.or, inputs := [8, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c84 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [2, 9] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [4, 12] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem c85 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨{ gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [2, 6] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [14, 13] }], output := 15 },
   by
     intro g hg
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
     rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals exact ⟨by simp, by decide⟩,
   by decide, by decide⟩

end PEqualNP.Outside.L_meta_926

theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  exact ⟨PEqualNP.Outside.L_meta_926.c1, ⟨PEqualNP.Outside.L_meta_926.c2, ⟨PEqualNP.Outside.L_meta_926.c3, ⟨PEqualNP.Outside.L_meta_926.c4, ⟨PEqualNP.Outside.L_meta_926.c5, ⟨PEqualNP.Outside.L_meta_926.c6, ⟨PEqualNP.Outside.L_meta_926.c7, ⟨PEqualNP.Outside.L_meta_926.c8, ⟨PEqualNP.Outside.L_meta_926.c9, ⟨PEqualNP.Outside.L_meta_926.c10, ⟨PEqualNP.Outside.L_meta_926.c11, ⟨PEqualNP.Outside.L_meta_926.c12, ⟨PEqualNP.Outside.L_meta_926.c13, ⟨PEqualNP.Outside.L_meta_926.c14, ⟨PEqualNP.Outside.L_meta_926.c15, ⟨PEqualNP.Outside.L_meta_926.c16, ⟨PEqualNP.Outside.L_meta_926.c17, ⟨PEqualNP.Outside.L_meta_926.c18, ⟨PEqualNP.Outside.L_meta_926.c19, ⟨PEqualNP.Outside.L_meta_926.c20, ⟨PEqualNP.Outside.L_meta_926.c21, ⟨PEqualNP.Outside.L_meta_926.c22, ⟨PEqualNP.Outside.L_meta_926.c23, ⟨PEqualNP.Outside.L_meta_926.c24, ⟨PEqualNP.Outside.L_meta_926.c25, ⟨PEqualNP.Outside.L_meta_926.c26, ⟨PEqualNP.Outside.L_meta_926.c27, ⟨PEqualNP.Outside.L_meta_926.c28, ⟨PEqualNP.Outside.L_meta_926.c29, ⟨PEqualNP.Outside.L_meta_926.c30, ⟨PEqualNP.Outside.L_meta_926.c31, ⟨PEqualNP.Outside.L_meta_926.c32, ⟨PEqualNP.Outside.L_meta_926.c33, ⟨PEqualNP.Outside.L_meta_926.c34, ⟨PEqualNP.Outside.L_meta_926.c35, ⟨PEqualNP.Outside.L_meta_926.c36, ⟨PEqualNP.Outside.L_meta_926.c37, ⟨PEqualNP.Outside.L_meta_926.c38, ⟨PEqualNP.Outside.L_meta_926.c39, ⟨PEqualNP.Outside.L_meta_926.c40, ⟨PEqualNP.Outside.L_meta_926.c41, ⟨PEqualNP.Outside.L_meta_926.c42, ⟨PEqualNP.Outside.L_meta_926.c43, ⟨PEqualNP.Outside.L_meta_926.c44, ⟨PEqualNP.Outside.L_meta_926.c45, ⟨PEqualNP.Outside.L_meta_926.c46, ⟨PEqualNP.Outside.L_meta_926.c47, ⟨PEqualNP.Outside.L_meta_926.c48, ⟨PEqualNP.Outside.L_meta_926.c49, ⟨PEqualNP.Outside.L_meta_926.c50, ⟨PEqualNP.Outside.L_meta_926.c51, ⟨PEqualNP.Outside.L_meta_926.c52, ⟨PEqualNP.Outside.L_meta_926.c53, ⟨PEqualNP.Outside.L_meta_926.c54, ⟨PEqualNP.Outside.L_meta_926.c55, ⟨PEqualNP.Outside.L_meta_926.c56, ⟨PEqualNP.Outside.L_meta_926.c57, ⟨PEqualNP.Outside.L_meta_926.c58, ⟨PEqualNP.Outside.L_meta_926.c59, ⟨PEqualNP.Outside.L_meta_926.c60, ⟨PEqualNP.Outside.L_meta_926.c61, ⟨PEqualNP.Outside.L_meta_926.c62, ⟨PEqualNP.Outside.L_meta_926.c63, ⟨PEqualNP.Outside.L_meta_926.c64, ⟨PEqualNP.Outside.L_meta_926.c65, ⟨PEqualNP.Outside.L_meta_926.c66, ⟨PEqualNP.Outside.L_meta_926.c67, ⟨PEqualNP.Outside.L_meta_926.c68, ⟨PEqualNP.Outside.L_meta_926.c69, ⟨PEqualNP.Outside.L_meta_926.c70, ⟨PEqualNP.Outside.L_meta_926.c71, ⟨PEqualNP.Outside.L_meta_926.c72, ⟨PEqualNP.Outside.L_meta_926.c73, ⟨PEqualNP.Outside.L_meta_926.c74, ⟨PEqualNP.Outside.L_meta_926.c75, ⟨PEqualNP.Outside.L_meta_926.c76, ⟨PEqualNP.Outside.L_meta_926.c77, ⟨PEqualNP.Outside.L_meta_926.c78, ⟨PEqualNP.Outside.L_meta_926.c79, ⟨PEqualNP.Outside.L_meta_926.c80, ⟨PEqualNP.Outside.L_meta_926.c81, ⟨PEqualNP.Outside.L_meta_926.c82, ⟨PEqualNP.Outside.L_meta_926.c83, ⟨PEqualNP.Outside.L_meta_926.c84, PEqualNP.Outside.L_meta_926.c85⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
