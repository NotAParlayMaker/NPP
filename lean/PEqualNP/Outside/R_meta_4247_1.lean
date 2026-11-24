import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Each of the sixteen input columns occupies 59 bits, least significant row first.
-- Rows 0 through 18 are incident pairs. The other 40 are maximal negative assignments
-- after allowing all four optional terms. Only the four optional assignments are undecided.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_4247_1
    (build : ∀ (n w : Nat) (cols : Fin n → BitVec w) (xs : List (BitVec w)) (target : BitVec w),
      (∀ i : Fin xs.length, let bank := List.ofFn cols ++ xs.take i.val
        ∃ a ∈ bank, ∃ b ∈ bank, xs[i.val] = a &&& b ∨ xs[i.val] = a ||| b) →
      target ∈ List.ofFn cols ++ xs →
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.size=xs.length ∧
        ∀ r : Fin w, circuitFun n C (fun i => (cols i).getLsbD r)=target.getLsbD r)
    (search : let raw := List.ofFn (fun (i : Fin 16) => BitVec.ofNat 59 ((0xff80000000c0001feffc0000040003c1e07fe000400066330f03f004000fe8119861c0400154a92a8a2404003c1c1008000060060300e084000300cc00180448001814000220000000e22110000000000387c3d003bf88a203399e1e8170830800fdccf3470814156adaaebb4080500000fefffb0401 : Nat) >>> (59*i.val)))
      ∃ xs : List (BitVec 59), xs.length≤22 ∧
        (∀ i : Fin xs.length, let bank := raw ++ xs.take i.val
          xs[i.val] ∉ bank ∧ ∃ a ∈ bank, ∃ b ∈ bank, a.toNat < b.toNat ∧
            (xs[i.val] = a &&& b ∨ xs[i.val] = a ||| b)) ∧
        (524287 : BitVec 59) ∈ raw ++ xs)
    (extend : ∀ C : Circuit, Monotone2 C → ReadsBack 16 C →
      (∀ r : Fin 59, circuitFun 16 C (fun i => ((fun (i : Fin 16) => BitVec.ofNat 59 ((0xff80000000c0001feffc0000040003c1e07fe000400066330f03f004000fe8119861c0400154a92a8a2404003c1c1008000060060300e084000300cc00180448001814000220000000e22110000000000387c3d003bf88a203399e1e8170830800fdccf3470814156adaaebb4080500000fefffb0401 : Nat) >>> (59*i.val))) i).getLsbD r) =
        (524287 : BitVec 59).getLsbD r) →
      have x1 : List ℕ := [(33 : ℕ), (34 : ℕ), (40 : ℕ), (66 : ℕ), (68 : ℕ), (80 : ℕ), (132 : ℕ), (136 : ℕ), (264 : ℕ), (272 : ℕ), (513 : ℕ), (528 : ℕ), (1026 : ℕ), (2052 : ℕ), (4104 : ℕ), (8208 : ℕ), (16385 : ℕ), (32769 : ℕ), (32772 : ℕ)]; have x2 : List ℕ := [(6291 : ℕ), (12551 : ℕ), (25102 : ℕ), (51226 : ℕ)]; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (6 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x3 ∧ x3.size = C.size ∧ ∀ (x5 : Fin (16 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x3 x5 = Decidable.decide (∃ x6 ∈ x1 ++ if ↑x4 = (5 : ℕ) then [(6291 : ℕ), (25102 : ℕ)] else List.take (↑x4) x2, ∀ (x7 : Fin (16 : ℕ)), x6.testBit ↑x7 = Bool.true → x5 x7 = Bool.true)) :
    have x1 : List ℕ := [(33 : ℕ), (34 : ℕ), (40 : ℕ), (66 : ℕ), (68 : ℕ), (80 : ℕ), (132 : ℕ), (136 : ℕ), (264 : ℕ), (272 : ℕ), (513 : ℕ), (528 : ℕ), (1026 : ℕ), (2052 : ℕ), (4104 : ℕ), (8208 : ℕ), (16385 : ℕ), (32769 : ℕ), (32772 : ℕ)]; have x2 : List ℕ := [(6291 : ℕ), (12551 : ℕ), (25102 : ℕ), (51226 : ℕ)]; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (6 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x3 ∧ x3.size ≤ (22 : ℕ) ∧ ∀ (x5 : Fin (16 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x3 x5 = Decidable.decide (∃ x6 ∈ x1 ++ if ↑x4 = (5 : ℕ) then [(6291 : ℕ), (25102 : ℕ)] else List.take (↑x4) x2, ∀ (x7 : Fin (16 : ℕ)), x6.testBit ↑x7 = Bool.true → x5 x7 = Bool.true) := by
  let cols := (fun (i : Fin 16) => BitVec.ofNat 59 ((0xff80000000c0001feffc0000040003c1e07fe000400066330f03f004000fe8119861c0400154a92a8a2404003c1c1008000060060300e084000300cc00180448001814000220000000e22110000000000387c3d003bf88a203399e1e8170830800fdccf3470814156adaaebb4080500000fefffb0401 : Nat) >>> (59*i.val)))
  obtain ⟨xs,len,chain,out⟩ := search
  have well : ∀ i : Fin xs.length, let bank := List.ofFn cols ++ xs.take i.val
      ∃ a ∈ bank, ∃ b ∈ bank, xs[i.val] = a &&& b ∨ xs[i.val] = a ||| b := by
    intro i
    obtain ⟨_,a,ha,b,hb,_,op⟩ := chain i
    exact ⟨a,ha,b,hb,op⟩
  obtain ⟨C,mono,back,size,rows⟩ := build 16 59 cols xs 524287 well out
  obtain ⟨D,s,md,bd,sd,correct⟩ := extend C mono back rows
  exact ⟨D,s,md,bd,by omega,correct⟩
