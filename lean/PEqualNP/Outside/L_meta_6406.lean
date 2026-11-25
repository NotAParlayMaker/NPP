import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6406
open PEqualNP.CircuitLowerBounds



theorem all_ok : (List.range 1024).all (fun m =>
    ([65, 66, 72, 129, 132, 160, 258, 272, 288, 516, 520, 528] : List ℕ).any (fun a => a &&& m == a) ||
    ([63, 116, 154, 208, 269, 324, 392, 547, 608, 642, 769, 960] : List ℕ).any (fun b => m &&& b == m)) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_6406

open PEqualNP.Outside.L_meta_6406 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6406 : ∀ (x1 : Fin (10 : ℕ) → Bool), (∃ x2 ∈ [(65 : ℕ), (66 : ℕ), (72 : ℕ), (129 : ℕ), (132 : ℕ), (160 : ℕ), (258 : ℕ), (272 : ℕ), (288 : ℕ), (516 : ℕ), (520 : ℕ), (528 : ℕ)], ∀ (x3 : Fin (10 : ℕ)), x2.testBit ↑x3 = Bool.true → x1 x3 = Bool.true) ∨ ∃ x2 ∈ [(63 : ℕ), (116 : ℕ), (154 : ℕ), (208 : ℕ), (269 : ℕ), (324 : ℕ), (392 : ℕ), (547 : ℕ), (608 : ℕ), (642 : ℕ), (769 : ℕ), (960 : ℕ)], ∀ (x3 : Fin (10 : ℕ)), x1 x3 = Bool.true → x2.testBit ↑x3 = Bool.true := by
  intro x
  have hm : Nat.ofBits x < 1024 := Nat.ofBits_lt_two_pow x
  have hbit : ∀ i : Fin 10, (Nat.ofBits x).testBit i = x i := fun i => Nat.testBit_ofBits_lt x i.1 i.2
  have h := List.all_eq_true.1 all_ok (Nat.ofBits x) (List.mem_range.2 hm)
  simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h
  rcases h with ⟨a, ha, hae⟩ | ⟨b, hb, hbe⟩
  · left
    refine ⟨a, ha, fun i hi => ?_⟩
    have h1 := congrArg (fun z => z.testBit i) hae
    simp only [Nat.testBit_and, hbit i, hi, Bool.true_and] at h1
    exact h1
  · right
    refine ⟨b, hb, fun i hi => ?_⟩
    have h1 := congrArg (fun z => z.testBit i) hbe
    simp only [Nat.testBit_and, hbit i, hi, Bool.true_and] at h1
    exact h1
