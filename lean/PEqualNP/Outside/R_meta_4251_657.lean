import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4251_657
    (rows :
      let P : List (List ℕ) := [[0],[1],[2],[13],[14],[15],[17],[18],[19],[23],[24],[25],[13,15],[14,17],[15,17],[15,17,18],[19,23],[18,19,23],[17,24],[17,19,24],[18,25],[13,19],[14,23],[15,23],[15,23,24],[24,25]]
      let D : Finset (Fin 13) := {0,1,3,9}
      let W := fun m : ℕ => List.ofFn (fun i : Fin 26 => m.testBit i.val)
      ∀ p l : Fin 13, p.val < 3 → (∃ d ∈ D, p = l+d) →
      (List.ofFn fun i : Fin 26 => (P.getD i.val []).any fun j =>
        decide (Fin.ofNat 26 j = Fin.castAdd 13 p ∨ Fin.ofNat 26 j = Fin.natAdd 13 l)) ∈
      ([2101257,34605057,29557249,843841,4202514,2101258,51119106,1212546,25219108,4202516,34605060,2818308]).map W)
    (search :
      let W := fun m : ℕ => List.ofFn (fun i : Fin 26 => m.testBit i.val)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 13 ∧
      (∀ m ∈ [2101257,34605057,29557249,843841,4202514,2101258,51119106,1212546,25219108,4202516,34605060,2818308], C.eval (W m) = true) ∧
      (∀ m ∈ [67108856,67106225,67107682,28037411,67106508,52331653,30401094,7], C.eval (W m) = false)) :

    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : List (List ℕ) := [[(0 : ℕ)], [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)], [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)], [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]]; have x4 : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (26 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x6 : Fin (26 : ℕ)) => (x3.getD ↑x6 []).any fun (x7 : ℕ) => x5 (Fin.ofNat (26 : ℕ) x7); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ (13 : ℕ) ∧ (∀ (x6 x7 : Fin (13 : ℕ)), ↑x6 < (3 : ℕ) → x2 x6 x7 → (x4 x5 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) = Bool.true) ∧ ∀ (x6 : Finset (Fin (3 : ℕ))), (x4 x5 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide ((3 : ℕ) ≤ ↑x8 ∨ ∃ x9 ∈ x6, Fin.castAdd (10 : ℕ) x9 = x8)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (∀ x9 ∈ x6, ¬x2 (Fin.castAdd (10 : ℕ) x9) x8)) x7) = Bool.false := by
  intro D E P F
  obtain ⟨C,hm,sz,yes,no⟩ := search
  refine ⟨C,hm,sz,?_,?_⟩
  · intro p l hp he
    obtain ⟨m,hm,eq⟩ := List.mem_map.mp (rows p l hp he)
    have z := yes m hm
    change C.eval (List.ofFn fun i : Fin 26 => m.testBit i.val) = true at z
    rw [eq] at z
    exact z
  · let W := fun m : ℕ => List.ofFn (fun i : Fin 26 => m.testBit i.val)
    let Neg := fun A : Finset (Fin 3) => List.ofFn fun i : Fin 26 =>
      (P.getD i.val []).any fun j => Fin.addCases
        (fun p : Fin 13 => decide (3 ≤ p.val ∨ ∃ a ∈ A, Fin.castAdd 10 a = p))
        (fun l : Fin 13 => decide (∀ a ∈ A, ¬ E (Fin.castAdd 10 a) l))
        (Fin.ofNat 26 j)
    have complete : ∀ A : Finset (Fin 3), Neg A ∈ ([67108856,67106225,67107682,28037411,67106508,52331653,30401094,7]).map W := by
      decide +kernel
    intro A
    obtain ⟨m,hm,eq⟩ := List.mem_map.mp (complete A)
    have z := no m hm
    change C.eval (W m) = false at z
    rw [eq] at z
    exact z
