import PEqualNP.Defs

-- Renumber the first pair of input columns while preserving every test row.
-- Each remaining search starts with one representative and has at most 60 further gates.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4957_24
    (firstAnd :
      let codes : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
      let column := fun (v : ℕ) => ((List.finRange 285).filter (fun r =>
        (codes.getD ((r.val+1)/13) 0).testBit (v/13*13+(v+13-(r.val+1)%13)%13))).toFinset
      ∀ k ∈ ([1, 2, 13, 14, 17, 28, 29, 39, 40, 41, 43, 56, 60, 65, 66, 68, 69, 77, 352, 355, 379, 381, 382, 465] : List ℕ),
        let base := (List.range 26).map column ++ [column (k/26) ∩ column (k % 26)]
        ∀ t : List (Finset (Fin 285)), t.length ≤ 60 →
          (∀ i : Fin t.length, let pool := base ++ t.take i.val
            ∃ u ∈ pool, ∃ v ∈ pool, ¬u⊆v ∧ ¬v⊆u ∧ t.get i ∉ pool ∧
              (t.get i=u∩v ∨ t.get i=u∪v)) →
          ∀ u ∈ base ++ t, ∀ v ∈ base ++ t, ¬u⊆v → ¬v⊆u →
            u∪v ≠ ((List.finRange 285).filter (fun i => decide (i.val<51))).toFinset)
    (firstOr :
      let codes : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
      let column := fun (v : ℕ) => ((List.finRange 285).filter (fun r =>
        (codes.getD ((r.val+1)/13) 0).testBit (v/13*13+(v+13-(r.val+1)%13)%13))).toFinset
      ∀ k ∈ ([1, 2, 13, 14, 17, 28, 29, 39, 40, 41, 43, 56, 60, 65, 66, 68, 69, 77, 352, 355, 379, 381, 382, 465] : List ℕ),
        let base := (List.range 26).map column ++ [column (k/26) ∪ column (k % 26)]
        ∀ t : List (Finset (Fin 285)), t.length ≤ 60 →
          (∀ i : Fin t.length, let pool := base ++ t.take i.val
            ∃ u ∈ pool, ∃ v ∈ pool, ¬u⊆v ∧ ¬v⊆u ∧ t.get i ∉ pool ∧
              (t.get i=u∩v ∨ t.get i=u∪v)) →
          ∀ u ∈ base ++ t, ∀ v ∈ base ++ t, ¬u⊆v → ¬v⊆u →
            u∪v ≠ ((List.finRange 285).filter (fun i => decide (i.val<51))).toFinset)
    : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   x3.length ≤ (61 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) →       ∀ x6 ∈ x2 ++ x3, ∀ x8 ∈ x2 ++ x3, ¬x6 ⊆ x8 → ¬x8 ⊆ x6 → x6 ∪ x8 ≠ (List.filter (fun (x12 : Fin (285 : ℕ)) => Decidable.decide (↑x12 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset := by
  classical
  let codes : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
  let column := fun (v : ℕ) => ((List.finRange 285).filter (fun r =>
    (codes.getD ((r.val+1)/13) 0).testBit (v/13*13+(v+13-(r.val+1)%13)%13))).toFinset
  -- A representative pair with indices i and j is stored as 26*i+j, with i < j.
  let picks : List ℕ := [1, 2, 13, 14, 17, 28, 29, 39, 40, 41, 43, 56, 60, 65, 66, 68, 69, 77, 352, 355, 379, 381, 382, 465]
  let raw (r : Fin 285) (v : Fin 26) : Bool :=
    (codes.getD ((r.val+1)/13) 0).testBit (v.val/13*13+(v.val+13-(r.val+1)%13)%13)
  let src := (List.range 26).map column
  let goal := ((List.finRange 285).filter (fun i => decide (i.val<51))).toFinset
  let valid (base t : List (Finset (Fin 285))) := ∀ i : Fin t.length,
    let pool := base ++ t.take i.val
    ∃ u ∈ pool, ∃ v ∈ pool, ¬u⊆v ∧ ¬v⊆u ∧ t.get i ∉ pool ∧
      (t.get i=u∩v ∨ t.get i=u∪v)
  let safe (base t : List (Finset (Fin 285))) := ∀ u ∈ base++t, ∀ v ∈ base++t,
    ¬u⊆v → ¬v⊆u → u∪v ≠ goal
  let gate (meet : Bool) (u v : Finset (Fin 285)) := if meet then u ∩ v else u ∪ v
  have canonical (meet : Bool) (k : ℕ) (hk : k ∈ picks) (t : List (Finset (Fin 285)))
      (len : t.length ≤ 60) : let base := src ++ [gate meet (column (k/26)) (column (k % 26))]
      valid base t → safe base t := by
    cases meet
    · exact firstOr k hk t len
    · exact firstAnd k hk t len
  have memSrc (w : Finset (Fin 285)) : w ∈ src ↔ ∃ a : Fin 26, column a.val = w := by
    constructor
    · intro hw
      obtain ⟨a,ha,eq⟩ := List.mem_map.mp hw
      exact ⟨⟨a,List.mem_range.mp ha⟩,eq⟩
    · rintro ⟨a,rfl⟩
      exact List.mem_map.mpr ⟨a.val,List.mem_range.mpr a.isLt,rfl⟩
  have colMem (r : Fin 285) (v : Fin 26) : r ∈ column v.val ↔ raw r v = true := by
    simp [column,raw]
  have goalMem (r : Fin 285) : r ∈ goal ↔ r.val < 51 := by simp [goal]
  have negativeUse : ∀ a : Fin 26, ∃ r : Fin 285, 51 ≤ r.val ∧ raw r a = true := by
    have witness : ∀ a : Fin 26, ∃ i : Fin 13, raw ⟨51+i.val,by omega⟩ a = true := by
      dsimp only [raw,codes]
      decide +kernel
    intro a
    obtain ⟨i,hi⟩ := witness a
    exact ⟨⟨51+i.val,by omega⟩,by simp,hi⟩
  -- Two permutations of the rows and columns generate the renamings used below.
  let cols (s : Bool) (v : Fin 26) : Fin 26 :=
    (if s then (#[0, 3, 8, 9, 10, 11, 5, 6, 2, 1, 7, 4, 12, 13, 20, 21, 22, 23, 15, 18, 19, 14, 24, 17, 16, 25] : Array (Fin 26)) else #[0, 1, 5, 9, 8, 12, 11, 2, 7, 3, 6, 10, 4, 13, 18, 22, 21, 25, 24, 15, 19, 20, 16, 23, 14, 17]).getD v.val 0
  let rows (s : Bool) (v : Fin 285) : Fin 285 :=
    (if s then (#[
      45, 7, 8, 9, 40, 4, 5, 13, 36, 29, 15, 11, 25, 19, 20, 21, 22, 27, 17, 44, 0, 49, 3, 41, 24,
      38, 32, 33, 47, 48, 1, 43, 18, 26, 23, 42, 2, 50, 12, 6, 46, 34, 35, 14, 30, 31, 39, 10, 16,
      28, 37, 72, 164, 147, 108, 222, 231, 104, 143, 245, 76, 219, 220, 215, 241, 132, 57, 86,
      217, 82, 53, 180, 155, 91, 224, 229, 100, 233, 145, 163, 73, 134, 159, 206, 77, 78, 195,
      237, 178, 75, 225, 197, 176, 281, 69, 270, 102, 181, 66, 284, 136, 204, 228, 256, 236, 196,
      226, 227, 205, 160, 116, 63, 188, 106, 263, 60, 238, 249, 248, 239, 235, 257, 258, 103, 232,
      207, 279, 280, 177, 251, 93, 261, 138, 277, 172, 154, 167, 168, 169, 71, 216, 87, 264, 171,
      278, 208, 213, 274, 141, 187, 51, 267, 84, 184, 59, 246, 183, 85, 58, 185, 186, 129, 65,
      182, 247, 250, 88, 115, 174, 190, 98, 121, 81, 218, 64, 130, 131, 242, 149, 140, 275, 142,
      105, 189, 175, 198, 192, 193, 90, 156, 162, 146, 165, 166, 212, 209, 202, 260, 94, 114, 89,
      194, 79, 111, 97, 191, 199, 152, 254, 56, 133, 74, 179, 54, 118, 151, 201, 210, 211, 200,
      112, 113, 95, 68, 282, 62, 117, 55, 255, 61, 283, 67, 96, 125, 269, 70, 170, 265, 266, 52,
      83, 268, 126, 110, 80, 122, 272, 273, 214, 221, 109, 127, 128, 161, 157, 124, 123, 158, 135,
      243, 244, 144, 234, 240, 101, 271, 259, 203, 137, 262, 107, 148, 150, 119, 120, 99, 230,
      223, 92, 252, 253, 153, 173, 276, 139] : Array (Fin 285)) else #[
      43, 47, 20, 50, 23, 40, 44, 6, 2, 48, 39, 3, 12, 4, 8, 7, 11, 10, 1, 18, 45, 28, 9, 26, 42,
      38, 30, 34, 33, 37, 49, 14, 5, 32, 15, 35, 0, 16, 25, 17, 21, 46, 24, 36, 27, 31, 19, 41,
      22, 13, 29, 225, 111, 199, 99, 214, 232, 223, 209, 94, 204, 103, 230, 221, 89, 281, 196, 71,
      228, 218, 227, 66, 194, 273, 81, 216, 207, 179, 208, 56, 215, 135, 74, 274, 168, 130, 171,
      133, 280, 76, 264, 189, 173, 177, 278, 240, 210, 90, 213, 158, 276, 137, 141, 150, 102, 121,
      183, 83, 87, 270, 253, 91, 142, 226, 107, 229, 251, 151, 95, 203, 70, 139, 172, 152, 143,
      256, 234, 238, 242, 166, 138, 144, 279, 236, 282, 198, 51, 181, 269, 68, 72, 284, 60, 202,
      258, 262, 105, 109, 191, 116, 201, 52, 212, 85, 211, 64, 260, 132, 96, 59, 114, 266, 78, 54,
      197, 120, 178, 101, 272, 162, 275, 148, 176, 245, 283, 65, 69, 184, 259, 61, 205, 62, 104,
      119, 145, 122, 165, 127, 155, 117, 93, 57, 263, 88, 125, 182, 271, 249, 261, 250, 140, 77,
      277, 80, 174, 124, 192, 188, 128, 108, 163, 224, 75, 231, 235, 106, 246, 265, 185, 268, 84,
      267, 186, 86, 131, 219, 244, 222, 146, 220, 167, 217, 170, 136, 254, 206, 58, 79, 187, 113,
      53, 97, 169, 193, 73, 92, 123, 156, 160, 164, 118, 149, 153, 129, 175, 67, 200, 98, 154,
      110, 63, 82, 190, 55, 100, 257, 243, 247, 233, 252, 147, 255, 115, 239, 248, 237, 241, 180,
      134, 157, 161, 126, 159, 112, 195]).getD v.val 0
  let colsInv (s : Bool) (v : Fin 26) : Fin 26 :=
    (if s then (#[0, 9, 8, 1, 11, 6, 7, 10, 2, 3, 4, 5, 12, 13, 21, 18, 24, 23, 19, 20, 14, 15, 16, 17, 22, 25] : Array (Fin 26)) else #[0, 1, 7, 9, 12, 2, 10, 8, 4, 3, 11, 6, 5, 13, 24, 19, 22, 25, 14, 20, 21, 16, 15, 23, 18, 17]).getD v.val 0
  let rowsInv (s : Bool) (v : Fin 285) : Fin 285 :=
    (if s then (#[
      20, 30, 36, 22, 5, 6, 39, 1, 2, 3, 47, 11, 38, 7, 43, 10, 48, 18, 32, 13, 14, 15, 16, 34,
      24, 12, 33, 17, 49, 9, 44, 45, 26, 27, 41, 42, 8, 50, 25, 46, 4, 23, 35, 31, 19, 0, 40, 28,
      29, 21, 37, 150, 239, 70, 213, 227, 209, 66, 158, 154, 115, 229, 225, 111, 174, 162, 98,
      231, 223, 94, 235, 139, 51, 80, 211, 89, 60, 84, 85, 202, 244, 172, 69, 240, 152, 157, 67,
      141, 166, 200, 188, 73, 278, 130, 198, 222, 232, 204, 170, 275, 76, 264, 96, 123, 57, 182,
      113, 270, 54, 250, 243, 203, 220, 221, 199, 167, 110, 226, 214, 273, 274, 171, 245, 256,
      255, 233, 242, 251, 252, 161, 175, 176, 65, 210, 81, 258, 100, 268, 132, 284, 179, 148, 181,
      58, 261, 78, 191, 53, 271, 178, 272, 215, 207, 281, 135, 72, 189, 254, 257, 82, 109, 253,
      190, 79, 52, 192, 193, 136, 137, 138, 236, 143, 134, 282, 168, 184, 92, 128, 88, 212, 71,
      97, 163, 156, 153, 159, 160, 149, 112, 183, 169, 205, 186, 187, 201, 86, 105, 91, 185, 206,
      219, 216, 196, 267, 101, 108, 83, 125, 145, 195, 217, 218, 194, 146, 248, 63, 140, 68, 173,
      61, 62, 249, 55, 277, 74, 90, 106, 107, 102, 75, 276, 56, 124, 77, 262, 120, 104, 87, 116,
      119, 263, 64, 177, 259, 260, 59, 155, 164, 118, 117, 165, 129, 279, 280, 208, 228, 103, 121,
      122, 266, 197, 131, 269, 114, 142, 237, 238, 151, 241, 234, 95, 265, 246, 247, 147, 180,
      283, 133, 144, 126, 127, 93, 224, 230, 99] : Array (Fin 285)) else #[
      36, 18, 8, 11, 13, 32, 7, 15, 14, 22, 17, 16, 12, 49, 31, 34, 37, 39, 19, 46, 2, 40, 48, 4,
      42, 38, 23, 44, 21, 50, 26, 45, 33, 28, 27, 35, 43, 29, 25, 10, 5, 47, 24, 0, 6, 20, 41, 1,
      9, 30, 3, 136, 151, 240, 163, 263, 79, 191, 236, 159, 142, 179, 181, 260, 155, 175, 71, 255,
      139, 176, 120, 67, 140, 244, 82, 212, 89, 201, 162, 237, 203, 74, 261, 107, 220, 153, 223,
      108, 193, 64, 97, 111, 245, 190, 59, 118, 158, 241, 257, 54, 264, 167, 104, 61, 182, 146,
      215, 114, 209, 147, 259, 52, 283, 239, 160, 272, 149, 189, 250, 183, 165, 105, 185, 246,
      205, 194, 281, 187, 208, 253, 85, 224, 157, 87, 278, 81, 233, 101, 130, 121, 200, 102, 112,
      124, 131, 184, 228, 270, 171, 251, 103, 117, 123, 252, 258, 188, 247, 279, 99, 282, 248,
      280, 169, 210, 249, 186, 129, 230, 84, 242, 232, 86, 122, 92, 204, 254, 172, 93, 166, 77,
      277, 137, 195, 106, 177, 218, 222, 238, 207, 91, 262, 148, 206, 243, 72, 284, 66, 164, 135,
      53, 256, 150, 143, 119, 60, 180, 235, 76, 78, 58, 96, 154, 152, 98, 55, 80, 75, 231, 69,
      225, 229, 63, 227, 57, 211, 51, 113, 70, 68, 115, 62, 213, 56, 268, 126, 214, 133, 275, 127,
      273, 95, 276, 128, 266, 226, 173, 216, 267, 274, 197, 199, 116, 269, 110, 234, 271, 125,
      265, 144, 178, 156, 198, 145, 192, 90, 217, 161, 221, 219, 138, 109, 196, 168, 73, 83, 170,
      100, 202, 94, 132, 88, 65, 134, 174, 141]).getD v.val 0
  have invCols : ∀ s v, colsInv s (cols s v) = v := by
    dsimp only [cols, colsInv]
    decide +kernel
  have invRows : ∀ s r, rowsInv s (rows s r) = r := by
    dsimp only [rows, rowsInv]
    decide +kernel
  have permRaw : ∀ s r v, raw (rows s r) (cols s v) = raw r v := by
    dsimp only [cols, rows, raw, codes]
    decide +kernel
  have permGoal : ∀ s r, (rows s r).val < 51 ↔ r.val < 51 := by
    dsimp only [rows]
    decide +kernel
  let colEq (s : Bool) : Fin 26 ≃ Fin 26 := Equiv.ofBijective (cols s)
    (Finite.injective_iff_bijective.mp (Function.LeftInverse.injective (invCols s)))
  let rowEq (s : Bool) : Fin 285 ≃ Fin 285 := Equiv.ofBijective (rows s)
    (Finite.injective_iff_bijective.mp (Function.LeftInverse.injective (invRows s)))
  let act (w : List Bool) (v : Fin 26) := w.foldl (fun i s => cols s i) v
  have actPerm (w : List Bool) :
      ∃ (p : Fin 26 ≃ Fin 26) (e : Fin 285 ≃ Fin 285),
        (∀ v, p v = act w v) ∧
        (∀ r v, raw (e r) (p v) = raw r v) ∧
        (∀ r, (e r).val < 51 ↔ r.val < 51) := by
    induction w with
    | nil => exact ⟨Equiv.refl _, Equiv.refl _, fun _ => rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
    | cons s w ih =>
      obtain ⟨p, e, hv, hraw, hgoal⟩ := ih
      exact ⟨(colEq s).trans p, (rowEq s).trans e, fun v => hv (cols s v),
        fun r v => (hraw (rows s r) (cols s v)).trans (permRaw s r v),
        fun r => (hgoal (rows s r)).trans (permGoal s r)⟩
  -- For an ordered pair of columns, read generator choices from the low bits.
  -- The leading one records the word length.
  let words : Array ℕ := #[
      1, 1, 1, 6, 6, 21, 20, 2, 3, 3, 5, 10, 12, 1, 1, 7, 6, 1, 4, 9, 18, 3, 5, 3, 2, 2, 1, 1, 1,
      1, 8, 21, 26, 2, 4, 2, 37, 13, 16, 1, 1, 1, 16, 1, 4, 2, 4, 8, 32, 15, 2, 2, 1, 1, 1, 7, 1,
      7, 9, 14, 1, 9, 39, 54, 9, 1, 1, 7, 1, 1, 9, 9, 39, 54, 7, 9, 31, 1, 6, 1, 7, 1, 6, 24, 34,
      18, 19, 5, 29, 10, 25, 6, 6, 7, 6, 7, 24, 7, 18, 10, 25, 6, 18, 11, 6, 8, 1, 6, 1, 8, 6, 2,
      38, 38, 30, 58, 11, 6, 8, 75, 6, 6, 6, 8, 38, 38, 30, 6, 11, 8, 21, 21, 7, 24, 8, 1, 21, 18,
      4, 27, 27, 10, 22, 21, 35, 24, 21, 21, 21, 102, 27, 32, 27, 21, 24, 32, 20, 26, 9, 34, 6,
      21, 1, 43, 15, 20, 20, 10, 45, 20, 55, 20, 34, 34, 26, 20, 26, 34, 49, 20, 43, 20, 2, 2, 14,
      18, 2, 18, 43, 1, 19, 14, 18, 13, 2, 2, 18, 14, 99, 2, 41, 14, 18, 78, 2, 18, 2, 2, 3, 4, 1,
      19, 38, 4, 15, 19, 1, 3, 29, 3, 4, 3, 79, 4, 15, 4, 4, 19, 19, 3, 63, 3, 3, 3, 3, 2, 9, 5,
      38, 27, 20, 14, 3, 1, 5, 17, 12, 3, 9, 17, 20, 22, 3, 9, 5, 3, 5, 3, 12, 5, 5, 37, 39, 29,
      30, 27, 20, 18, 29, 5, 1, 5, 5, 5, 37, 98, 5, 37, 29, 40, 29, 37, 5, 5, 110, 5, 10, 13, 54,
      10, 58, 10, 10, 13, 3, 17, 5, 1, 23, 10, 58, 10, 61, 10, 151, 13, 17, 17, 10, 10, 13, 17,
      12, 16, 9, 25, 11, 22, 45, 2, 4, 12, 5, 23, 1, 12, 12, 51, 25, 16, 22, 45, 16, 25, 12, 12,
      16, 12, 1, 1, 1, 6, 6, 21, 20, 2, 3, 3, 5, 10, 12, 1, 1, 7, 6, 1, 4, 9, 18, 3, 5, 3, 2, 2,
      1, 1, 1, 6, 8, 35, 55, 18, 79, 9, 37, 58, 12, 1, 1, 1, 6, 1, 1, 9, 29, 8, 37, 30, 2, 8, 7,
      1, 7, 7, 75, 24, 20, 14, 4, 17, 98, 10, 51, 7, 1, 1, 10, 7, 21, 7, 7, 10, 27, 24, 74, 35, 6,
      16, 1, 6, 6, 21, 34, 99, 15, 20, 5, 61, 25, 6, 6, 10, 1, 25, 26, 20, 6, 38, 25, 6, 16, 11,
      1, 1, 1, 7, 6, 21, 34, 2, 4, 22, 37, 10, 16, 1, 1, 7, 25, 1, 4, 31, 19, 58, 22, 1, 13, 5, 4,
      4, 9, 24, 6, 21, 26, 41, 4, 3, 29, 151, 22, 4, 1, 21, 26, 4, 1, 43, 4, 3, 32, 15, 4, 26, 9,
      2, 9, 7, 8, 102, 20, 14, 19, 9, 40, 13, 45, 9, 9, 7, 20, 31, 43, 1, 14, 3, 9, 9, 2, 14, 18,
      4, 39, 18, 38, 27, 26, 18, 19, 5, 29, 17, 16, 18, 29, 7, 6, 19, 4, 14, 1, 19, 5, 18, 18, 29,
      3, 8, 54, 10, 38, 32, 34, 78, 3, 3, 37, 17, 25, 3, 8, 10, 38, 58, 3, 3, 19, 1, 5, 3, 13, 17,
      5, 32, 7, 25, 30, 27, 49, 2, 63, 5, 5, 10, 12, 5, 37, 27, 25, 22, 32, 9, 5, 5, 1, 12, 12, 5,
      3, 15, 9, 6, 6, 21, 20, 18, 3, 3, 5, 10, 12, 3, 30, 24, 6, 1, 15, 9, 18, 3, 12, 1, 51, 2, 2,
      2, 31, 18, 11, 24, 43, 2, 3, 12, 110, 13, 16, 2, 2, 74, 16, 13, 4, 2, 18, 13, 12, 51, 1, 2,
      2, 2, 1, 11, 8, 32, 20, 2, 3, 5, 5, 17, 12, 2, 8, 35, 11, 5, 26, 14, 29, 17, 5, 2, 2, 1]
  let word (a b : Fin 26) : List Bool :=
    let n := words.getD (a.val * 26 + b.val) 1
    (List.range n.log2).map n.testBit
  have covers : ∀ a b : Fin 26, a ≠ b →
      let va := (act (word a b) a).val
      let vb := (act (word a b) b).val
      min va vb * 26 + max va vb ∈ picks := by
    dsimp only [word, words, act, cols, picks]
    decide +kernel
  have normalize (a b : Fin 26) (ne : a ≠ b) :
      ∃ (p : Fin 26 ≃ Fin 26) (e : Fin 285 ≃ Fin 285),
        (∀ r v, raw (e r) (p v) = raw r v) ∧
        (∀ r, (e r).val < 51 ↔ r.val < 51) ∧
        min (p a).val (p b).val * 26 + max (p a).val (p b).val ∈ picks := by
    obtain ⟨p,e,hc,hr,hg⟩ := actPerm (word a b)
    exact ⟨p,e,hr,hg,by simpa only [hc] using covers a b ne⟩
  -- Map every suffix gate and both final operands through the same row permutation.
  have transport (z : Finset (Fin 285)) (t : List (Finset (Fin 285)))
      (e : Fin 285 ≃ Fin 285)
      (sources : ∀ w, w ∈ src ↔ w.map e.toEmbedding ∈ src)
      (target : goal.map e.toEmbedding = goal)
      (ok : valid src (z::t)) (bad : ¬safe src (z::t)) :
      valid (src++[z.map e.toEmbedding]) (t.map (fun w => w.map e.toEmbedding)) ∧
      ¬safe (src++[z.map e.toEmbedding]) (t.map (fun w => w.map e.toEmbedding)) := by
    let f := Finset.map e.toEmbedding
    have inj : Function.Injective f := Finset.map_injective _
    have pool (r : List (Finset (Fin 285))) (w : Finset (Fin 285)) :
        w ∈ src ++ z::r ↔ f w ∈ (src++[f z]) ++ r.map f := by
      have mapped : f w ∈ r.map f ↔ w ∈ r := by
        constructor
        · intro h
          obtain ⟨a,ha,eq⟩ := List.mem_map.mp h
          exact inj eq ▸ ha
        · exact List.mem_map_of_mem
      have original : f w ∈ src ↔ w ∈ src := (sources w).symm
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,mapped,
        original,inj.eq_iff]
      tauto
    constructor
    · intro i
      have ih : i.val < t.length := by simpa using i.isLt
      obtain ⟨u,hu,v,hv,uv,vu,fresh,op⟩ := ok ⟨i.val+1,by simpa using ih⟩
      simp only [List.take_succ_cons,List.get_eq_getElem,List.getElem_cons_succ] at hu hv fresh op
      simp only [List.get_eq_getElem,List.getElem_map,← List.map_take]
      refine ⟨f u,(pool _ _).mp hu,f v,(pool _ _).mp hv,
        fun h => uv (Finset.map_subset_map.mp h),fun h => vu (Finset.map_subset_map.mp h),
        fun h => fresh ((pool _ _).mpr h),?_⟩
      rcases op with e' | e'
      · left
        simpa only [f,Finset.map_inter] using congrArg f e'
      · right
        simpa only [f,Finset.map_union] using congrArg f e'
    · intro good
      apply bad
      intro u hu v hv uv vu eq
      apply good (f u) ((pool _ _).mp hu) (f v) ((pool _ _).mp hv)
          (fun h => uv (Finset.map_subset_map.mp h)) (fun h => vu (Finset.map_subset_map.mp h))
      simpa only [f,Finset.map_union,target] using congrArg f eq
  change ∀ t : List (Finset (Fin 285)), t.length ≤ 61 → valid src t → safe src t
  intro gates bound ok
  cases gates with
  | nil =>
    intro u hu v _ _ _ eq
    obtain ⟨a,rfl⟩ := (memSrc u).mp (by simpa using hu)
    obtain ⟨r,cold,hit⟩ := negativeUse a
    have inside : r ∈ column a.val ∪ v := Finset.mem_union_left _ ((colMem r a).mpr hit)
    exact (Nat.not_lt_of_ge cold) ((goalMem r).mp (eq ▸ inside))
  | cons z tail =>
    by_contra bad
    have first := ok ⟨0,by simp⟩
    simp only [List.take_zero,List.append_nil,List.get_eq_getElem,List.getElem_cons_zero] at first
    obtain ⟨u,hu,v,hv,uv,_,_,kind⟩ := first
    obtain ⟨a,rfl⟩ := (memSrc u).mp hu
    obtain ⟨b,rfl⟩ := (memSrc v).mp hv
    have ne : a ≠ b := fun eq => uv (eq ▸ Finset.Subset.refl _)
    obtain ⟨p,e,rawMap,hotMap,picked⟩ := normalize a b ne
    have colMap (i : Fin 26) : (column i.val).map e.toEmbedding = column (p i).val := by
      ext s
      obtain ⟨r,rfl⟩ := e.surjective s
      simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply,colMem,rawMap]
    have sources (w : Finset (Fin 285)) : w ∈ src ↔ w.map e.toEmbedding ∈ src := by
      constructor
      · intro hw
        obtain ⟨i,rfl⟩ := (memSrc w).mp hw
        exact (memSrc _).mpr ⟨p i,(colMap i).symm⟩
      · intro hw
        obtain ⟨j,eq⟩ := (memSrc _).mp hw
        obtain ⟨i,rfl⟩ := p.surjective j
        exact (memSrc _).mpr ⟨i,Finset.map_inj.mp ((colMap i).trans eq)⟩
    have target : goal.map e.toEmbedding = goal := by
      ext s
      obtain ⟨r,rfl⟩ := e.surjective s
      simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply,goalMem,hotMap]
    obtain ⟨good,fails⟩ := transport z tail e sources target ok bad
    obtain ⟨meet,form⟩ : ∃ meet, z = gate meet (column a.val) (column b.val) := by
      rcases kind with h | h
      · exact ⟨true,h⟩
      · exact ⟨false,h⟩
    let lo := min (p a).val (p b).val
    let hi := max (p a).val (p b).val
    let k := lo*26+hi
    have small : hi < 26 := max_lt (p a).isLt (p b).isLt
    have div : k/26 = lo := by dsimp [k]; omega
    have mod : k % 26 = hi := by dsimp [k]; omega
    have head : z.map e.toEmbedding = gate meet (column (k/26)) (column (k % 26)) := by
      rw [div,mod,form]
      have mapped (x y : Finset (Fin 285)) :
          (gate meet x y).map e.toEmbedding = gate meet (x.map e.toEmbedding) (y.map e.toEmbedding) := by
        cases meet
        · exact Finset.map_union _ _
        · exact Finset.map_inter _ _
      rw [mapped,colMap,colMap]
      rcases le_total (p a).val (p b).val with le | le
      · simp only [lo,hi,min_eq_left le,max_eq_right le]
      · simp only [lo,hi,min_eq_right le,max_eq_left le]
        cases meet
        · exact Finset.union_comm _ _
        · exact Finset.inter_comm _ _
    rw [head] at good fails
    have len : tail.length ≤ 60 := by
      simp only [List.length_cons] at bound
      omega
    exact fails (canonical meet k picked _ (by simpa only [List.length_map] using len) good)
