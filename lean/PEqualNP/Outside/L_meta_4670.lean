import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4670

def witness : List (Fin 24 → Bool) := [
    fun r : Fin 24 => Nat.testBit 135168 r.val,
    fun r : Fin 24 => Nat.testBit 16642047 r.val,
    fun r : Fin 24 => Nat.testBit 16330008 r.val,
    fun r : Fin 24 => Nat.testBit 9434179 r.val,
    fun r : Fin 24 => Nat.testBit 16641368 r.val,
    fun r : Fin 24 => Nat.testBit 16741063 r.val,
    fun r : Fin 24 => Nat.testBit 16346526 r.val,
    fun r : Fin 24 => Nat.testBit 16343174 r.val,
    fun r : Fin 24 => Nat.testBit 8 r.val,
    fun r : Fin 24 => Nat.testBit 430080 r.val,
    fun r : Fin 24 => Nat.testBit 16343040 r.val,
    fun r : Fin 24 => Nat.testBit 16773120 r.val,
    fun r : Fin 24 => Nat.testBit 4095 r.val]

end PEqualNP.Outside.L_meta_4670

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_4670 : ¬ (∀ x1 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (18 : ℕ), (23 : ℕ), (28 : ℕ)],   have x3 : Fin (24 : ℕ) → Fin (9 : ℕ) → Bool := fun (x3 : Fin (24 : ℕ)) (x4 : Fin (9 : ℕ)) => ([(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑x4;   have x4 : Fin (24 : ℕ) → List Bool := fun (x4 : Fin (24 : ℕ)) => List.ofFn (x3 x4) ++ [!x3 x4 (0 : Fin (9 : ℕ)), x3 x4 (Fin.ofNat (9 : ℕ) (x1 / (10 : ℕ))) || x3 x4 (Fin.ofNat (9 : ℕ) (x1 % (10 : ℕ)))];   have x5 : List (Fin (24 : ℕ) → Bool) := (List.ofFn fun (x5 : Fin (11 : ℕ)) (x6 : Fin (24 : ℕ)) => (x4 x6).getD (↑x5) Bool.false) ++ [fun (x5 : Fin (24 : ℕ)) => Bool.false, fun (x5 : Fin (24 : ℕ)) => Bool.true];   ∀ (x6 : List (Fin (24 : ℕ) → Bool)),     x6.length ≤ (13 : ℕ) →       (∀ (x8 : Fin x6.length),           have x9 : List (Fin (24 : ℕ) → Bool) := x5 ++ List.take (↑x8) x6;           (∃ x10 ∈ x9, x6.get x8 = fun (x11 : Fin (24 : ℕ)) => !x10 x11) ∨ ∃ x10 ∈ x9, ∃ x11 ∈ x9, (x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 && x11 x12) ∨ x6.get x8 = fun (x12 : Fin (24 : ℕ)) => x10 x12 || x11 x12) →         (fun (x9 : Fin (24 : ℕ)) => Decidable.decide (↑x9 < (12 : ℕ))) ∉ x5 ++ x6) := by
  intro h
  exact h 12 (by decide) PEqualNP.Outside.L_meta_4670.witness (by decide +kernel)
    (by intro k; fin_cases k <;> decide +kernel) (by decide +kernel)
