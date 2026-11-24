import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Compile both settings of the copied wire into a single 512-row table.
-- Each instruction has one of four operations and two five-bit addresses.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2191_1
  (compiler : let step := fun (w : List (BitVec 512)) (q : Fin 4 × Fin 32 × Fin 32) =>
    let a := w.getD q.2.1.val 0
    let b := w.getD q.2.2.val 0
    w ++ [if q.1 = 0 then a &&& b else if q.1 = 1 then a ||| b
      else if q.1 = 2 then ~~~a else BitVec.allOnes 512]
  ∀ C : Circuit, FanInTwo C → ∃ (p : List (Fin 4 × Fin 32 × Fin 32)) (o : Fin 32),
    p.length = C.size ∧ ∀ (w : List (BitVec 512)) (j : Fin 512), w.length + C.size ≤ 30 →
      let bit := fun v : BitVec 512 => v.getLsbD j.val
      (p.foldl step w).map bit = C.wires (w.map bit) ∧
        bit ((p.foldl step w).getD o.val 0) = C.eval (w.map bit))
  (exclude : let step := fun (w : List (BitVec 512)) (q : Fin 4 × Fin 32 × Fin 32) =>
    let a := w.getD q.2.1.val 0
    let b := w.getD q.2.2.val 0
    w ++ [if q.1 = 0 then a &&& b else if q.1 = 1 then a ||| b
      else if q.1 = 2 then ~~~a else BitVec.allOnes 512]
  let raw := List.ofFn (fun v : Fin 8 =>
      let p := ([1,2,4,8,16,32,64,128] : List ℕ).getD v.val 0
      let t := (2 : ℕ)^p
      BitVec.ofNat 512 (((2^512 - 1) / (t + 1)) * t))
  ∀ (p s : List (Fin 4 × Fin 32 × Fin 32)) (i o : Fin 32) (b : Bool),
    p.length + s.length ≤ 13 → i.val < 8 + p.length →
    let w := p.foldl step raw
    let u := w.getD i.val 0
    let m : BitVec 512 := BitVec.ofNat 512 (2^256 - 1)
    let z := if b then u ||| ~~~m else u &&& m
    (s.foldl step (w ++ [z])).getD o.val 0 ≠ (0xfffffffffffffffaffffffffffffffeafffffffefffffffaffeeffeeffeaffeafffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8 : BitVec 512))
  : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   PEqualNP.MetaComplexity.FanInTwo x3 →     PEqualNP.MetaComplexity.FanInTwo x4 →       x3.size + x4.size ≤ (13 : ℕ) →         x5 < (8 : ℕ) + x3.size →           have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x3.wires (List.ofFn x11);           have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x5 Bool.false;           (∀ (x13 : Fin (8 : ℕ)), (x12 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => x14 x13) ∧ x12 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => !x14 x13) → (∀ (x14 : Fin (8 : ℕ) → Bool), x1 x14 ≠ x2 x14 → x12 x14 = !x6) → (∀ (x15 : Fin (8 : ℕ) → Bool), x4.eval (x11 x15 ++ [x12 x15]) = x1 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x4.eval (x11 x16 ++ [x6]) ≠ x2 x16 := by
  let step := fun (w : List (BitVec 512)) (q : Fin 4 × Fin 32 × Fin 32) =>
    let a := w.getD q.2.1.val 0
    let b := w.getD q.2.2.val 0
    w ++ [if q.1 = 0 then a &&& b else if q.1 = 1 then a ||| b
      else if q.1 = 2 then ~~~a else BitVec.allOnes 512]
  let raw := List.ofFn (fun v : Fin 8 =>
      let p := ([1,2,4,8,16,32,64,128] : List ℕ).getD v.val 0
      let t := (2 : ℕ)^p
      BitVec.ofNat 512 (((2^512 - 1) / (t + 1)) * t))
  let f := fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
    (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let h := fun x : Fin 8 → Bool => f x || x 0 || x 3
  let input := fun (j : Fin 512) (v : Fin 8) => j.val.testBit v.val
  let bit := fun (j : Fin 512) (v : BitVec 512) => v.getLsbD j.val
  let mask := BitVec.ofNat 512 (2^256-1)
  let target : BitVec 512 := 0xfffffffffffffffaffffffffffffffeafffffffefffffffaffeeffeeffeaffeafffffffffffffff8ffffffffffffffc8fffffcfcfffff8f8feeefcccfaeaf8c8
  have rawLength : raw.length = 8 := List.length_ofFn
  have rawBits : ∀ j : Fin 512, raw.map (bit j) = List.ofFn (input j) := by decide +kernel
  have maskBits : ∀ j : Fin 512, bit j mask = decide (j.val < 256) := by decide +kernel
  have targetBits : ∀ j : Fin 512, bit j target = if j.val < 256 then f (input j) else h (input j) := by
    decide +kernel
  have getBit (w : List (BitVec 512)) (j : Fin 512) (i : ℕ) :
      (w.map (bit j)).getD i false = bit j (w.getD i 0) := by
    have hb : bit j 0 = false := @BitVec.getLsbD_zero 512 j.val
    simpa only [hb] using List.getD_map w 0 (n:=i) (bit j)
  have lengthRun (p : List (Fin 4 × Fin 32 × Fin 32)) (w : List (BitVec 512)) :
      (p.foldl step w).length = w.length + p.length := by
    induction p generalizing w with
    | nil => simp
    | cons q p ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  dsimp only
  intro P S i b hp hs size index
  try dsimp only
  intro _ _ lo
  by_contra! hi
  change ∀ x, S.eval (P.wires (List.ofFn x) ++ [(P.wires (List.ofFn x)).getD i false]) = f x at lo
  change ∀ x, S.eval (P.wires (List.ofFn x) ++ [b]) = h x at hi
  obtain ⟨p, _, hpLen, pCorr⟩ := compiler P hp
  obtain ⟨s, o, hsLen, sCorr⟩ := compiler S hs
  let A := p.foldl step raw
  let u := A.getD i 0
  let z := if b then u ||| ~~~mask else u &&& mask
  let ix : Fin 32 := ⟨i, by omega⟩
  have hx : ix.val < 8 + p.length := by simpa [ix, hpLen] using index
  have ha : A.length = 8 + P.size := by
    change (p.foldl step raw).length = _
    rw [lengthRun, rawLength, hpLen]
  have readA (j : Fin 512) : A.map (bit j) = P.wires (List.ofFn (input j)) := by
    have H := (pCorr raw j (by rw [rawLength]; omega)).1
    exact H.trans (congrArg P.wires (rawBits j))
  have readZ (j : Fin 512) :
      bit j z = if j.val < 256 then (P.wires (List.ofFn (input j))).getD i false else b := by
    have hu : bit j u = (P.wires (List.ofFn (input j))).getD i false := by
      change bit j (A.getD i 0) = _
      rw [← getBit, readA]
    have hm := maskBits j
    have hj := j.isLt
    change mask.getLsbD j.val = _ at hm
    change u.getLsbD j.val = _ at hu
    cases b <;> by_cases hj' : j.val < 256 <;>
      simp only [bit, z, Bool.false_eq_true, ite_true, ite_false, Bool.true_eq,
        BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hj, hj', hm, hu,
        decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.false_and, Bool.true_and,
        Bool.or_true, Bool.or_false, Bool.not_true, Bool.not_false]
  apply exclude p s ix o b (by omega) hx
  change (s.foldl step (A ++ [z])).getD o.val 0 = target
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  let j : Fin 512 := ⟨n,hn⟩
  have evalS := (sCorr (A ++ [z]) j (by
    simp only [List.length_append, List.length_cons, List.length_nil, ha]; omega)).2
  change bit j ((s.foldl step (A ++ [z])).getD o.val 0) = _ at evalS
  change bit j ((s.foldl step (A ++ [z])).getD o.val 0) = bit j target
  rw [evalS, targetBits]
  change S.eval ((A ++ [z]).map (bit j)) = _
  rw [List.map_append, List.map_cons, List.map_nil, readA, readZ]
  by_cases hj : j.val < 256
  · simpa only [if_pos hj] using lo (input j)
  · simpa only [if_neg hj] using hi (input j)
