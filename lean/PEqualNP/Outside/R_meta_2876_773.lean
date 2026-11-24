import Mathlib
import PEqualNP.Defs

-- Each row is a 14-bit mask. A pivot entry packs two rows, and a table word packs four.
theorem PEqualNP.Outside.R_meta_2876_773
  (h1 : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin C.size) (k : Fin 16),
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 25 ∧ a < b ∧
    let atMask := fun (table : List ℕ) (i : ℕ) => (table.getD (i / 4) 0 >>> (14 * (i % 4))) % 16384
    let op := if k.val < 3 then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and
    let t := ([2130049, 4259969, 8913025, 3997823, 7078015, 60883071, 266338431, 5144820, 7078132, 12976372, 21135604, 60883188, 121667828, 10813872, 19988912, 25362864] : List ℕ).getD k.val 0
    let p := t % 16384
    let q := t / 16384
    let W := fun (w : Fin C.size) (m : ℕ) =>
      (C.wires (List.ofFn fun j : Fin 14 => m.testBit j.val)).getD (14 + w.val) false
    let V := fun m : ℕ => op.eval [W a m, W b m]
    W a p ≠ W b p ∧ W a p = W b q ∧ W b p = W a q ∧
    (∀ i : Fin 21, V (atMask [1130334462705793, 2392675283108100, 4644616305394240, 18032557665028104, 36048588832772104, 8208] i.val) = true) ∧
    (∀ i : Fin 37, V (atMask [1900040385527935, 4846859866931741, 9179138627896516, 13537875736430756, 19220618668199556, 27036184092086801, 37332878074993922, 45183814167831049, 65310217798183328, 16256] i.val) = false))
  (h2 : let F := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true
  let U := fun m : ℕ => fun j : Fin 14 => m.testBit j.val
  (∀ x, Minimal F x → ∃ m : ℕ, m ∈ [129, 130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064, 2112, 4100, 4104, 4128, 8194, 8196, 8208] ∧ x = U m) ∧
  (∀ x, Maximal (fun y => ¬ F y) x → ∃ m : ℕ, m ∈ [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] ∧ x = U m)) :
  have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (25 : ℕ) ∧       (14 : ℕ) ≤ x4 ∧         x4 < x5 ∧           x5 < (14 : ℕ) + x2.size ∧             (x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 ∈ [((129 : ℕ), (130 : ℕ)), ((129 : ℕ), (260 : ℕ)), ((129 : ℕ), (544 : ℕ))] ∨ x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6 ∈ [((127 : ℕ), (244 : ℕ)), ((127 : ℕ), (432 : ℕ)), ((127 : ℕ), (3716 : ℕ)), ((127 : ℕ), (16256 : ℕ)), ((244 : ℕ), (314 : ℕ)), ((244 : ℕ), (432 : ℕ)), ((244 : ℕ), (792 : ℕ)), ((244 : ℕ), (1290 : ℕ)), ((244 : ℕ), (3716 : ℕ)), ((244 : ℕ), (7426 : ℕ)), ((432 : ℕ), (660 : ℕ)), ((432 : ℕ), (1220 : ℕ)), ((432 : ℕ), (1548 : ℕ))]) ∧               have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;               have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;               have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;               have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];               x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false := by
  obtain ⟨C, a, b, k, mono, size, order, diff, swapA, swapB, pos, neg⟩ := h1
  let atMask := fun (table : List ℕ) (i : ℕ) => (table.getD (i / 4) 0 >>> (14 * (i % 4))) % 16384
  let op := if k.val < 3 then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and
  let t := ([2130049, 4259969, 8913025, 3997823, 7078015, 60883071, 266338431, 5144820, 7078132, 12976372, 21135604, 60883188, 121667828, 10813872, 19988912, 25362864] : List ℕ).getD k.val 0
  let p := t % 16384
  let q := t / 16384
  have allPairs : ∀ k : Fin 16,
      let op := if k.val < 3 then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and
      let pairCode := ([2130049, 4259969, 8913025, 3997823, 7078015, 60883071, 266338431, 5144820, 7078132, 12976372, 21135604, 60883188, 121667828, 10813872, 19988912, 25362864] : List ℕ).getD k.val 0
      let t := (pairCode % 16384, pairCode / 16384)
      (op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ t ∈ [(129,130),(129,260),(129,544)]) ∨
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ t ∈ [(127,244),(127,432),(127,3716),(127,16256),(244,314),(244,432),(244,792),(244,1290),(244,3716),(244,7426),(432,660),(432,1220),(432,1548)]) := by
    intro i
    fin_cases i <;> first
      | exact Or.inl ⟨rfl, by decide +kernel⟩
      | exact Or.inr ⟨rfl, by decide +kernel⟩
  have listPos : List.ofFn (fun i : Fin 21 => atMask [1130334462705793, 2392675283108100, 4644616305394240, 18032557665028104, 36048588832772104, 8208] i.val) = [129, 130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064, 2112, 4100, 4104, 4128, 8194, 8196, 8208] := by decide +kernel
  have listNeg : List.ofFn (fun i : Fin 37 => atMask [1900040385527935, 4846859866931741, 9179138627896516, 13537875736430756, 19220618668199556, 27036184092086801, 37332878074993922, 45183814167831049, 65310217798183328, 16256] i.val) = [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] := by decide +kernel
  refine ⟨C, op, 14 + a.val, 14 + b.val, (p,q), mono, size, ?_, ?_, ?_, allPairs k,
    diff, swapA, swapB, ?_, ?_⟩
  · omega
  · exact Nat.add_lt_add_left order 14
  · exact Nat.add_lt_add_left b.isLt 14
  · intro x minimal
    obtain ⟨m, hm, rfl⟩ := h2.1 x minimal
    rw [← listPos, List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact Or.inr (pos i)
  · intro x maximal
    obtain ⟨m, hm, rfl⟩ := h2.2 x maximal
    rw [← listNeg, List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact Or.inr (neg i)
