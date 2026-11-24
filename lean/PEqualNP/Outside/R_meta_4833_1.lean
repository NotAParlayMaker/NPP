import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.EdgeOwnership

-- The four faces restrict to at most thirty-two boundary rows each.
-- Packing rows into words preserves every AND and OR gate.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4833_1
    (firstFaces : ∀ i : Fin 2,
      let raw : List (BitVec 32) := if i.val = 0 then [0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752] else [8372227, 0, 32849932, 3935354928, 26198208, 101352196, 19074064, 340530208, 410001728, 3783275009, 4261415050]
      ∀ t : List (BitVec 32), t.length ≤ 18 →
        (∀ j : Fin t.length, let prior := raw ++ t.take j.val
          ∃ a ∈ prior, ∃ b ∈ prior, t.get j = a &&& b ∨ t.get j = a ||| b) →
        (16383 : BitVec 32) ∉ raw ++ t)
    (lastFaces : ∀ i : Fin 2,
      let raw : List (BitVec 32) := if i.val = 0 then [8372227, 3439673356, 0, 3566256176, 42631364, 202359552, 52628496, 676074528, 812654920, 3279958529, 4227860610] else [16760835, 4111810572, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 4076876289, 4227860642]
      ∀ t : List (BitVec 32), t.length ≤ 18 →
        (∀ j : Fin t.length, let prior := raw ++ t.take j.val
          ∃ a ∈ prior, ∃ b ∈ prior, t.get j = a &&& b ∨ t.get j = a ||| b) →
        (16383 : BitVec 32) ∉ raw ++ t) :
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (19 : ℕ) ≤ x3.size
 := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wire_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step w g)).length = _
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

  have old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      apply List.getD_append
      exact hi

  have gate_value (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
      (valid : ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < w.length + j) :
      let W := gs.foldl step w
      W.getD (w.length + j) false = (gs.getD j ⟨.or, []⟩).op.eval
        ((gs.getD j ⟨.or, []⟩).inputs.map fun i => W.getD i false) := by
    induction gs using List.reverseRecOn with
    | nil => simp at hj
    | append_singleton gs g ih =>
      have before : ((gs ++ [g]).foldl step w) = step (gs.foldl step w) g := by
        rw [List.foldl_append]; rfl
      rw [List.length_append, List.length_singleton] at hj
      by_cases he : j < gs.length
      · rw [List.getD_append _ _ _ _ he] at valid
        simp only [before, List.getD_append _ _ _ _ he]
        have h₁ : w.length + j < (gs.foldl step w).length := by rw [wire_len]; omega
        have h₂ (i : ℕ) (hi : i ∈ (gs.getD j ⟨.or, []⟩).inputs) :
            (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
          apply List.getD_append
          rw [wire_len]
          have := valid i hi
          omega
        change (step (gs.foldl step w) g).getD (w.length + j) false = _
        rw [show (step (gs.foldl step w) g).getD (w.length + j) false =
          (gs.foldl step w).getD (w.length + j) false from List.getD_append _ _ _ _ h₁,
          List.map_congr_left h₂]
        exact ih he valid
      · have heq : j = gs.length := by omega
        subst j
        simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at valid ⊢
        rw [before]
        have h₁ : w.length + gs.length = (gs.foldl step w).length := (wire_len gs w).symm
        have h₂ (i : ℕ) (hi : i ∈ g.inputs) :
            (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
          apply List.getD_append
          exact (valid i hi).trans_eq h₁
        change (step (gs.foldl step w) g).getD (w.length + gs.length) false = _
        rw [List.map_congr_left h₂, h₁]
        simp [step, List.getD_eq_getElem?_getD]

  have gateAt_formula (C : Circuit) (j : ℕ) :
      gateAt C j = C.gates.getD j ⟨.or, []⟩ := rfl
  have wire_at {n : ℕ} (C : Circuit) (B : ReadsBack n C) (x : Fin n → Bool)
      (j : ℕ) (hj : j < C.gates.length) :
      wireVal n C (n + j) x = (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
    have h := gate_value C.gates (List.ofFn x) j hj (by simpa only [List.length_ofFn, gateAt_formula] using B j hj)
    let W := C.gates.foldl step (List.ofFn x)
    change W.getD (n + j) false = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => W.getD i false)
    simpa only [W, List.length_ofFn, gateAt_formula] using h

  have input_at {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
      wireVal n C i x = x i := by
    unfold wireVal
    change (C.gates.foldl step (List.ofFn x)).getD i false = x i
    rw [old_read _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]

  have sample_counterexample {n r : ℕ} (C : Circuit) (AO : IsAO2 n C)
      (inputs : Fin r → Fin n → Bool) (out : Fin r → Bool)
      (yes : ∃ i, out i = true) (compute : ∀ i, circuitFun n C (inputs i) = out i) :
      let pins := List.ofFn (fun (j : Fin n) (i : Fin r) => inputs i j)
      ∃ table : List (Fin r → Bool), table.length = C.size ∧
        (∀ j : Fin table.length, let avail := pins ++ table.take j.val
          ∃ a ∈ avail, ∃ b ∈ avail,
            table.get j = (fun i => a i && b i) ∨ table.get j = (fun i => a i || b i)) ∧
        out ∈ pins ++ table := by
    let pins := List.ofFn (fun (j : Fin n) (i : Fin r) => inputs i j)
    let trace (w : ℕ) (i : Fin r) := wireVal n C w (inputs i)
    let values (j : Fin C.gates.length) := trace (n + j.val)
    let table := List.ofFn values
    have eqLen : table.length = C.gates.length := by simp [table]
    have member (j : ℕ) (p : ℕ) (h : p < n + j) (hle : j ≤ C.gates.length) :
        trace p ∈ pins ++ table.take j := by
      by_cases raw : p < n
      · apply List.mem_append.mpr
        left
        have eql : trace p = fun i => inputs i ⟨p,raw⟩ := funext fun i => input_at C (inputs i) ⟨p,raw⟩
        rw [eql]
        exact List.mem_ofFn.mpr ⟨⟨p,raw⟩, rfl⟩
      · have hIdx : p - n < j := by omega
        have hGate : p - n < table.length := by omega
        have hTake : p - n < (table.take j).length := by simp [List.length_take, hIdx, hGate]
        have m : (table.take j)[p-n] ∈ table.take j := List.getElem_mem hTake
        apply List.mem_append.mpr
        right
        have pEq : n + (p-n) = p := by omega
        simpa [table, values, pEq] using m
    have outBound : C.output < n+C.gates.length := by
      obtain ⟨i,hi⟩ := yes
      have on : (C.wires (List.ofFn (inputs i))).getD C.output false = true := (compute i).trans hi
      by_contra bad
      have len : (C.wires (List.ofFn (inputs i))).length = n + C.gates.length := by
        change (C.gates.foldl step (List.ofFn (inputs i))).length = _
        rw [wire_len, List.length_ofFn]
      rw [List.getD_eq_default _ _ (by omega)] at on
      contradiction
    refine ⟨table, eqLen, ?_, ?_⟩
    · intro j
      have hj : j.val < C.gates.length := j.isLt.trans_eq eqLen
      have gm : gateAt C j.val ∈ C.gates := by
        rw [gateAt_formula]
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem _
      obtain ⟨a,b,ab⟩ := List.length_eq_two.mp (AO.2.2 _ gm)
      have ra : a < n+j.val := AO.2.1 _ hj _ (by simp [ab])
      have rb : b < n+j.val := AO.2.1 _ hj _ (by simp [ab])
      refine ⟨trace a, member _ _ ra hj.le, trace b, member _ _ rb hj.le, ?_⟩
      have gval : table.get j = trace (n+j.val) := by simp [table, values]
      rw [gval]
      rcases AO.1 _ gm with op | op
      · left
        funext i
        simp only [trace, wire_at C AO.2.1 (inputs i) j.val hj, op, ab, List.map_cons, List.map_nil]
        change (wireVal n C a (inputs i) && (wireVal n C b (inputs i) && true)) = _
        rw [Bool.and_true]
      · right
        funext i
        simp only [trace, wire_at C AO.2.1 (inputs i) j.val hj, op, ab, List.map_cons, List.map_nil]
        change (wireVal n C a (inputs i) || (wireVal n C b (inputs i) || false)) = _
        rw [Bool.or_false]
    · have ext : trace C.output = out := funext compute
      rw [← ext, ← List.take_length (l := table)]
      exact member table.length C.output (outBound.trans_eq (congrArg (n+·) eqLen.symm)) (by omega)

  let pack {r : ℕ} (f : Fin r → Bool) : BitVec r :=
    (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

  have pack_bit {r : ℕ} (f : Fin r → Bool) (i : Fin r) : (pack f).getLsbD i.val = f i := by
    dsimp only [pack]
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

  have pack_and {r : ℕ} (a b : Fin r → Bool) :
      pack (fun i => a i && b i) = pack a &&& pack b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    change (pack (fun j => a j && b j)).getLsbD (⟨i,hi⟩ : Fin r).val = _
    rw [pack_bit, pack_bit a ⟨i,hi⟩, pack_bit b ⟨i,hi⟩]

  have pack_or {r : ℕ} (a b : Fin r → Bool) :
      pack (fun i => a i || b i) = pack a ||| pack b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_or]
    change (pack (fun j => a j || b j)).getLsbD (⟨i,hi⟩ : Fin r).val = _
    rw [pack_bit, pack_bit a ⟨i,hi⟩, pack_bit b ⟨i,hi⟩]

  have packed_counterexample {n r : ℕ} (C : Circuit) (AO : IsAO2 n C)
      (inputs : Fin r → Fin n → Bool) (out : Fin r → Bool)
      (yes : ∃ i, out i = true) (compute : ∀ i, circuitFun n C (inputs i) = out i) :
      let pins := List.ofFn (fun (j : Fin n) => pack (fun i => inputs i j))
      ∃ table : List (BitVec r), table.length = C.size ∧
        (∀ j : Fin table.length, let avail := pins ++ table.take j.val
          ∃ a ∈ avail, ∃ b ∈ avail, table.get j = a &&& b ∨ table.get j = a ||| b) ∧
        pack out ∈ pins ++ table := by
    let raw := List.ofFn (fun (j : Fin n) (i : Fin r) => inputs i j)
    obtain ⟨t, lt, ht, final⟩ := sample_counterexample C AO inputs out yes compute
    let w := t.map pack
    have eqRaw : raw.map pack = List.ofFn (fun (j : Fin n) => pack (fun i => inputs i j)) := by
      simp only [raw, List.map_ofFn, Function.comp_def]
    refine ⟨w, by simpa [w] using lt, ?_, ?_⟩
    · intro j
      let k : Fin t.length := ⟨j.val, by simpa [w] using j.isLt⟩
      obtain ⟨a, ha, b, hb, h⟩ := ht k
      have mapAvail (f : Fin r → Bool) (member : f ∈ raw ++ t.take k.val) :
          pack f ∈ raw.map pack ++ w.take j.val := by
        have m : pack f ∈ (raw ++ t.take k.val).map pack := List.mem_map.mpr ⟨f, member, rfl⟩
        simpa only [w, k, List.map_append, List.map_take] using m
      rw [← eqRaw]
      refine ⟨pack a, mapAvail a ha, pack b, mapAvail b hb, ?_⟩
      have hget : w.get j = pack (t.get k) := by simp [w, k]
      rw [hget]
      rcases h with h | h
      · exact Or.inl ((congrArg pack h).trans (pack_and a b))
      · exact Or.inr ((congrArg pack h).trans (pack_or a b))
    · rw [← eqRaw]
      have m : pack out ∈ (raw ++ t).map pack := List.mem_map.mpr ⟨out, final, rfl⟩
      simpa only [w, List.map_append] using m

  let rowMask : Fin 4 → Fin 32 → ℕ :=
    ![
      ![18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768, 56, 98, 112, 134, 148, 176, 268, 324, 388, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546],
      ![513, 1025, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768, 29, 57, 85, 113, 149, 177, 269, 325, 389, 540, 596, 1064, 1184, 1288, 1408, 1544, 1544, 1544],
      ![513, 1025, 18, 258, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768, 43, 57, 99, 113, 163, 177, 265, 321, 385, 536, 578, 592, 1066, 1186, 1288, 1408, 1546, 1546],
      ![513, 1025, 18, 258, 36, 1028, 272, 1040, 288, 544, 192, 1088, 640, 768, 71, 85, 99, 113, 135, 149, 163, 177, 325, 389, 582, 596, 1186, 1408, 1538, 1538, 1538, 1538]]

  let rowBits (k : Fin 4) (r : Fin 32) (w : Fin 11) : Bool := (rowMask k r).testBit w.val

  let target (r : Fin 32) : Bool := decide (r.val < 14)

  have sample_correct : ∀ (k : Fin 4) (r : Fin 32),
      rowBits k r (Fin.castLE (by decide) k) = false ∧
      graphFun (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) ∅ (rowBits k r) = target r := by
    dsimp only [rowBits, rowMask, target]
    decide +kernel

  let rawWords (k : Fin 4) : List (BitVec 32) :=
    if k.val = 0 then [0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752]
    else if k.val = 1 then [8372227, 0, 32849932, 3935354928, 26198208, 101352196, 19074064, 340530208, 410001728, 3783275009, 4261415050]
    else if k.val = 2 then [8372227, 3439673356, 0, 3566256176, 42631364, 202359552, 52628496, 676074528, 812654920, 3279958529, 4227860610]
    else [16760835, 4111810572, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 4076876289, 4227860642]
  have raw_eq : ∀ k : Fin 4, List.ofFn (fun (j : Fin 11) => pack (fun r => rowBits k r j)) = rawWords k := by
    dsimp only [pack, rowBits, rowMask, rawWords]
    decide +kernel
  have out_eq : pack target = (16383 : BitVec 32) := by
    dsimp only [pack, target]
    decide +kernel
  have impossible (k : Fin 4) (table : List (BitVec 32)) (lim : table.length ≤ 18)
      (formed : ∀ j : Fin table.length, let prior := rawWords k ++ table.take j.val
        ∃ a ∈ prior, ∃ b ∈ prior, table.get j = a &&& b ∨ table.get j = a ||| b) :
      (16383 : BitVec 32) ∉ rawWords k ++ table := by
    fin_cases k
    · exact firstFaces 0 table lim formed
    · exact firstFaces 1 table lim formed
    · exact lastFaces 0 table lim formed
    · exact lastFaces 1 table lim formed
  intro G v C hv AO face
  by_contra large
  let k : Fin 4 := ⟨v.val, hv⟩
  have kEq : Fin.castLE (by decide : 4 ≤ 11) k = v := Fin.ext rfl
  have computes (r : Fin 32) : circuitFun 11 C (rowBits k r) = target r := by
    have hzero : rowBits k r v = false := by
      rw [← kEq]
      exact (sample_correct k r).1
    exact (face _ hzero).trans (sample_correct k r).2
  have someTrue : ∃ r, target r = true := ⟨0, rfl⟩
  obtain ⟨table, eqLen, formed, out⟩ := packed_counterexample C AO (rowBits k) target someTrue computes
  have lim : table.length ≤ 18 := by omega
  rw [raw_eq k] at formed out
  rw [out_eq] at out
  exact impossible k table lim formed out
