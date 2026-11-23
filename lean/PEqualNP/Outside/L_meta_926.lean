import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926_aux

theorem c1 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 :=
  ⟨⟨[⟨.and, [0, 1]⟩], 2⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩], 4⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c3 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩], 6⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 :=
  ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩], 6⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c7 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩], 8⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩], 8⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩], 8⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 :=
  ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩], 10⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩], 11⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 9]⟩], 11⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 :=
  ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩], 11⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩], 10⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [11, 10]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [11, 10]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 :=
  ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩], 12⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [11, 12]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 :=
  ⟨⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [12, 13]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem c85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_926_aux

theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  exact ⟨PEqualNP.Outside.L_meta_926_aux.c1, PEqualNP.Outside.L_meta_926_aux.c2, PEqualNP.Outside.L_meta_926_aux.c3, PEqualNP.Outside.L_meta_926_aux.c4, PEqualNP.Outside.L_meta_926_aux.c5, PEqualNP.Outside.L_meta_926_aux.c6, PEqualNP.Outside.L_meta_926_aux.c7, PEqualNP.Outside.L_meta_926_aux.c8, PEqualNP.Outside.L_meta_926_aux.c9, PEqualNP.Outside.L_meta_926_aux.c10, PEqualNP.Outside.L_meta_926_aux.c11, PEqualNP.Outside.L_meta_926_aux.c12, PEqualNP.Outside.L_meta_926_aux.c13, PEqualNP.Outside.L_meta_926_aux.c14, PEqualNP.Outside.L_meta_926_aux.c15, PEqualNP.Outside.L_meta_926_aux.c16, PEqualNP.Outside.L_meta_926_aux.c17, PEqualNP.Outside.L_meta_926_aux.c18, PEqualNP.Outside.L_meta_926_aux.c19, PEqualNP.Outside.L_meta_926_aux.c20, PEqualNP.Outside.L_meta_926_aux.c21, PEqualNP.Outside.L_meta_926_aux.c22, PEqualNP.Outside.L_meta_926_aux.c23, PEqualNP.Outside.L_meta_926_aux.c24, PEqualNP.Outside.L_meta_926_aux.c25, PEqualNP.Outside.L_meta_926_aux.c26, PEqualNP.Outside.L_meta_926_aux.c27, PEqualNP.Outside.L_meta_926_aux.c28, PEqualNP.Outside.L_meta_926_aux.c29, PEqualNP.Outside.L_meta_926_aux.c30, PEqualNP.Outside.L_meta_926_aux.c31, PEqualNP.Outside.L_meta_926_aux.c32, PEqualNP.Outside.L_meta_926_aux.c33, PEqualNP.Outside.L_meta_926_aux.c34, PEqualNP.Outside.L_meta_926_aux.c35, PEqualNP.Outside.L_meta_926_aux.c36, PEqualNP.Outside.L_meta_926_aux.c37, PEqualNP.Outside.L_meta_926_aux.c38, PEqualNP.Outside.L_meta_926_aux.c39, PEqualNP.Outside.L_meta_926_aux.c40, PEqualNP.Outside.L_meta_926_aux.c41, PEqualNP.Outside.L_meta_926_aux.c42, PEqualNP.Outside.L_meta_926_aux.c43, PEqualNP.Outside.L_meta_926_aux.c44, PEqualNP.Outside.L_meta_926_aux.c45, PEqualNP.Outside.L_meta_926_aux.c46, PEqualNP.Outside.L_meta_926_aux.c47, PEqualNP.Outside.L_meta_926_aux.c48, PEqualNP.Outside.L_meta_926_aux.c49, PEqualNP.Outside.L_meta_926_aux.c50, PEqualNP.Outside.L_meta_926_aux.c51, PEqualNP.Outside.L_meta_926_aux.c52, PEqualNP.Outside.L_meta_926_aux.c53, PEqualNP.Outside.L_meta_926_aux.c54, PEqualNP.Outside.L_meta_926_aux.c55, PEqualNP.Outside.L_meta_926_aux.c56, PEqualNP.Outside.L_meta_926_aux.c57, PEqualNP.Outside.L_meta_926_aux.c58, PEqualNP.Outside.L_meta_926_aux.c59, PEqualNP.Outside.L_meta_926_aux.c60, PEqualNP.Outside.L_meta_926_aux.c61, PEqualNP.Outside.L_meta_926_aux.c62, PEqualNP.Outside.L_meta_926_aux.c63, PEqualNP.Outside.L_meta_926_aux.c64, PEqualNP.Outside.L_meta_926_aux.c65, PEqualNP.Outside.L_meta_926_aux.c66, PEqualNP.Outside.L_meta_926_aux.c67, PEqualNP.Outside.L_meta_926_aux.c68, PEqualNP.Outside.L_meta_926_aux.c69, PEqualNP.Outside.L_meta_926_aux.c70, PEqualNP.Outside.L_meta_926_aux.c71, PEqualNP.Outside.L_meta_926_aux.c72, PEqualNP.Outside.L_meta_926_aux.c73, PEqualNP.Outside.L_meta_926_aux.c74, PEqualNP.Outside.L_meta_926_aux.c75, PEqualNP.Outside.L_meta_926_aux.c76, PEqualNP.Outside.L_meta_926_aux.c77, PEqualNP.Outside.L_meta_926_aux.c78, PEqualNP.Outside.L_meta_926_aux.c79, PEqualNP.Outside.L_meta_926_aux.c80, PEqualNP.Outside.L_meta_926_aux.c81, PEqualNP.Outside.L_meta_926_aux.c82, PEqualNP.Outside.L_meta_926_aux.c83, PEqualNP.Outside.L_meta_926_aux.c84, PEqualNP.Outside.L_meta_926_aux.c85⟩
