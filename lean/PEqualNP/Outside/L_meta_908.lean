import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_908_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

/-! ## Section 1: The 9-vertex graph G9 and its 16 MIS -/

abbrev V := Fin 9

def E9 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)]

def g9Adj (a b : V) : Bool :=
  decide (a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ E9 ∨ ((b : ℕ), (a : ℕ)) ∈ E9))

def Good9 (I : Finset V) : Prop :=
  (∀ a ∈ I, ∀ c ∈ I, g9Adj a c = false) ∧
  (∀ w : V, w ∉ I → ∃ a ∈ I, g9Adj a w = true)

def misMask : Fin 16 → Nat :=
  ![25, 28, 49, 73, 97, 98, 134, 145, 148, 193, 194, 262, 265, 268, 289, 290]

def rows9 : Fin 16 → Finset V :=
  ![{0, 3, 4}, {2, 3, 4}, {0, 4, 5}, {0, 3, 6}, {0, 5, 6}, {1, 5, 6}, {1, 2, 7}, {0, 4, 7},
    {2, 4, 7}, {0, 6, 7}, {1, 6, 7}, {1, 2, 8}, {0, 3, 8}, {2, 3, 8}, {0, 5, 8}, {1, 5, 8}]

theorem rows9_bit (k : Fin 16) (v : V) : v ∈ rows9 k ↔ (misMask k).testBit v.val = true := by
  revert k v; decide +kernel

theorem rows9_good : ∀ k : Fin 16, Good9 (rows9 k) := by
  unfold Good9; decide +kernel

def throughV : V → Fin 5 → Fin 16 :=
  ![![0, 2, 3, 4, 7],
    ![5, 6, 10, 11, 15],
    ![1, 6, 8, 11, 13],
    ![0, 1, 3, 12, 13],
    ![0, 1, 2, 7, 8],
    ![2, 4, 5, 14, 15],
    ![3, 4, 5, 9, 10],
    ![6, 7, 8, 9, 10],
    ![11, 12, 13, 14, 15]]

theorem throughV_mem : ∀ (v : V) (i : Fin 5), v ∈ rows9 (throughV v i) := by decide +kernel

theorem throughV_diff : ∀ (v : V) (i j : Fin 5), i ≠ j →
    ∃ w ∈ rows9 (throughV v i), w ∉ rows9 (throughV v j) := by decide +kernel

def rows0 : Fin 8 → Fin 16 := ![0, 2, 3, 4, 7, 9, 12, 14]

theorem rows0_has0 : ∀ r : Fin 8, (0 : V) ∈ rows9 (rows0 r) := by decide +kernel

def v36 (t : Fin 4) : V := ⟨t.val + 3, by omega⟩

def through0 : Fin 4 → Fin 3 → Fin 8 :=
  ![![0, 2, 6], ![0, 1, 4], ![1, 3, 7], ![2, 3, 5]]

theorem through0_mem : ∀ (t : Fin 4) (i : Fin 3), v36 t ∈ rows9 (rows0 (through0 t i)) := by
  decide +kernel

theorem through0_diff : ∀ (t : Fin 4) (i j : Fin 3), i ≠ j →
    ∃ w ∈ rows9 (rows0 (through0 t i)), w ∉ rows9 (rows0 (through0 t j)) := by decide +kernel

theorem sep0_in : ∀ t1 t2 : Fin 4, t1 ≠ t2 →
    ∃ r : Fin 8, v36 t2 ∈ rows9 (rows0 r) ∧ v36 t1 ∉ rows9 (rows0 r) := by decide +kernel

theorem sep0_out : ∀ t1 t2 : Fin 4, t1 ≠ t2 →
    ∃ r : Fin 8, v36 t1 ∉ rows9 (rows0 r) ∧ v36 t2 ∉ rows9 (rows0 r) := by decide +kernel

theorem cover_all : ∀ v : V, ∃ k : Fin 16, v ∈ rows9 k := by decide +kernel

theorem cover_no0 : ∀ v : V, v ≠ 0 → ∃ k : Fin 16, (0 : V) ∉ rows9 k ∧ v ∈ rows9 k := by
  decide +kernel

theorem avoid_all : ∀ v : V, ∃ k : Fin 16, v ∉ rows9 k := by decide +kernel

/-! ## Section 2: Generic `AndCountCircuit` semantics, `stripCircuit`, `pad5`, `swapSide`, `proj_count`, `mis_cover` -/

lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

lemma sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

lemma eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔ ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

lemma sideTrue_mono_U {n k : ℕ} {U W : Finset (Fin n)} (hUW : U ⊆ W)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) : sideTrue W B F i v2 = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUW hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U W : Finset (Fin n)} (hUW : U ⊆ W) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel W d i = true := by
  intro d
  induction d with
  | zero => intro i hi; simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUW _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUW _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U W : Finset (Fin n)} (hUW : U ⊆ W)
    (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal W i = true :=
  gateValFuel_mono_U C hUW C.size i h

lemma eval_mono_U {n : ℕ} (C : AndCountCircuit n) {U W : Finset (Fin n)} (hUW : U ⊆ W)
    (h : C.eval U = true) : C.eval W = true := by
  rw [eval_iff] at h ⊢
  rcases h with ⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩
  · exact Or.inl ⟨v, hv, hUW hvU⟩
  · exact Or.inr ⟨j, hj, gateVal_mono_U C hUW j hg⟩

def sideL {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U)

def sideR {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)

/-! ### `stripCircuit`: makes `leftVars i` and `rightVars i` disjoint while preserving `eval` and `size` -/

def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

lemma mem_singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  simp [singSet]

def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

lemma strip_wf {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) : (stripCircuit C).WellFormed := hW

lemma mem_strip_leftVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  simp [stripCircuit, mem_singSet, and_assoc]

lemma mem_strip_rightVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  simp [stripCircuit, mem_singSet, and_assoc]

lemma strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hL hR
  rw [mem_strip_leftVars] at hL
  rw [mem_strip_rightVars] at hR
  apply hL.2
  rw [gateVal_unfold C {v} i, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]
  constructor
  · rcases hL.1 with hv | ⟨j, hj, hji, hgv⟩
    · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
    · exact Or.inr ⟨j, hj, hji, hgv⟩
  · rcases hR.1 with hv | ⟨j, hj, hji, hgv⟩
    · exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
    · exact Or.inr ⟨j, hj, hji, hgv⟩

lemma strip_gateVal_le {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal U i = true → C.gateVal U i = true := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hv
    rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true] at hv
    rw [gateVal_unfold C U i, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]
    have hL := (decide_eq_true_iff.mp hv.1)
    have hR := (decide_eq_true_iff.mp hv.2)
    constructor
    · rcases hL with ⟨v, hvL, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rcases ((mem_strip_leftVars C i v).mp hvL).1 with hvb | ⟨j, hjF, hji, hjs⟩
        · exact Or.inl ⟨v, hvb, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjs⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    · rcases hR with ⟨v, hvR, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rcases ((mem_strip_rightVars C i v).mp hvR).1 with hvb | ⟨j, hjF, hji, hjs⟩
        · exact Or.inl ⟨v, hvb, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjs⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩

lemma strip_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → C.gateVal U i = true →
      (∃ v ∈ U, C.gateVal {v} i = true) ∨ (stripCircuit C).gateVal U i = true := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    by_cases hsing : ∃ v ∈ U, C.gateVal {v} i = true
    · exact Or.inl hsing
    · right
      have hno : ∀ v ∈ U, C.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
      rw [gateVal_unfold C U i, Bool.and_eq_true, sideTrue_iff, sideTrue_iff] at hval
      rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true]
      constructor
      · refine decide_eq_true ?_
        rcases hval.1 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩
      · refine decide_eq_true ?_
        rcases hval.2 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩

lemma strip_eval_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · simp only [stripCircuit, Finset.mem_union, Finset.mem_biUnion, mem_singSet] at hvO
      rcases hvO with hvC | ⟨j, hjO, hvs⟩
      · exact Or.inl ⟨v, hvC, hvU⟩
      · exact Or.inr ⟨j, hjO, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hjO, strip_gateVal_le C U C.size j j.isLt hjv⟩
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨v, Finset.mem_union_left _ hvO, hvU⟩
    · rcases strip_gateVal_ge C U C.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
      · refine Or.inl ⟨v, Finset.mem_union_right _ ?_, hvU⟩
        exact Finset.mem_biUnion.mpr ⟨j, hjO, (mem_singSet C j v).mpr hvs⟩
      · exact Or.inr ⟨j, hjO, hj'⟩

/-! ### `swapSide`: swaps left/right of selected gates while preserving `eval`, `WellFormed`, `Disjoint` -/

def swapSide {n : ℕ} (C : AndCountCircuit n) (ε : Fin C.size → Bool) : AndCountCircuit n where
  size := C.size
  leftVars i := cond (ε i) (C.rightVars i) (C.leftVars i)
  leftGates i := cond (ε i) (C.rightGates i) (C.leftGates i)
  rightVars i := cond (ε i) (C.leftVars i) (C.rightVars i)
  rightGates i := cond (ε i) (C.leftGates i) (C.rightGates i)
  outVars := C.outVars
  outGates := C.outGates

lemma swapSide_wf {n : ℕ} (C : AndCountCircuit n) (ε : Fin C.size → Bool) (hW : C.WellFormed) :
    (swapSide C ε).WellFormed := by
  intro i
  cases h : ε i
  · constructor
    · intro j hj; change j ∈ cond (ε i) (C.rightGates i) (C.leftGates i) at hj
      rw [h, Bool.cond_false] at hj; exact (hW i).1 j hj
    · intro j hj; change j ∈ cond (ε i) (C.leftGates i) (C.rightGates i) at hj
      rw [h, Bool.cond_false] at hj; exact (hW i).2 j hj
  · constructor
    · intro j hj; change j ∈ cond (ε i) (C.rightGates i) (C.leftGates i) at hj
      rw [h, Bool.cond_true] at hj; exact (hW i).2 j hj
    · intro j hj; change j ∈ cond (ε i) (C.leftGates i) (C.rightGates i) at hj
      rw [h, Bool.cond_true] at hj; exact (hW i).1 j hj

lemma swapSide_disjoint {n : ℕ} (C : AndCountCircuit n) (ε : Fin C.size → Bool)
    (hD : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (i : Fin C.size) :
    Disjoint ((swapSide C ε).leftVars i) ((swapSide C ε).rightVars i) := by
  cases h : ε i
  · simpa [swapSide, h] using hD i
  · simpa [swapSide, h] using (hD i).symm

lemma swapSide_gateVal {n : ℕ} (C : AndCountCircuit n) (ε : Fin C.size → Bool) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (swapSide C ε).gateVal U i = C.gateVal U i := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [gateVal_unfold (swapSide C ε) U i, gateVal_unfold C U i]
    have hlt : ∀ j : Fin C.size, j < i → (swapSide C ε).gateVal U j = C.gateVal U j :=
      fun j hji => ih j (by omega)
    have hL : sideTrue U (C.leftVars i) (C.leftGates i) i ((swapSide C ε).gateVal U) =
        sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) :=
      sideTrue_congr U _ _ i _ _ hlt
    have hR : sideTrue U (C.rightVars i) (C.rightGates i) i ((swapSide C ε).gateVal U) =
        sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U) :=
      sideTrue_congr U _ _ i _ _ hlt
    cases h : ε i
    · change (sideTrue U (cond (ε i) (C.rightVars i) (C.leftVars i))
        (cond (ε i) (C.rightGates i) (C.leftGates i)) i ((swapSide C ε).gateVal U) &&
        sideTrue U (cond (ε i) (C.leftVars i) (C.rightVars i))
        (cond (ε i) (C.leftGates i) (C.rightGates i)) i ((swapSide C ε).gateVal U)) = _
      rw [h, Bool.cond_false, Bool.cond_false, Bool.cond_false, Bool.cond_false, hL, hR]
    · change (sideTrue U (cond (ε i) (C.rightVars i) (C.leftVars i))
        (cond (ε i) (C.rightGates i) (C.leftGates i)) i ((swapSide C ε).gateVal U) &&
        sideTrue U (cond (ε i) (C.leftVars i) (C.rightVars i))
        (cond (ε i) (C.leftGates i) (C.rightGates i)) i ((swapSide C ε).gateVal U)) = _
      rw [h, Bool.cond_true, Bool.cond_true, Bool.cond_true, Bool.cond_true, hL, hR, Bool.and_comm]

lemma swapSide_eval {n : ℕ} (C : AndCountCircuit n) (ε : Fin C.size → Bool) (U : Finset (Fin n)) :
    (swapSide C ε).eval U = C.eval U := by
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  have hgv : ∀ j : Fin C.size, (swapSide C ε).gateVal U j = C.gateVal U j :=
    fun j => swapSide_gateVal C ε U C.size j j.isLt
  constructor
  · rintro (h | ⟨j, hj, hgv'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, by rwa [← hgv j]⟩
  · rintro (h | ⟨j, hj, hgv'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, by rwa [hgv j]⟩

/-! ### `pad5`: pads any circuit of `size ≤ 5` to `size = 5` with dummy gates -/

def pad5 {n : ℕ} (C : AndCountCircuit n) (hsz : C.size ≤ 5) : AndCountCircuit n where
  size := 5
  leftVars i := if h : i.val < C.size then C.leftVars ⟨i.val, h⟩ else ∅
  leftGates i := if h : i.val < C.size then (C.leftGates ⟨i.val, h⟩).image (Fin.castLE hsz) else ∅
  rightVars i := if h : i.val < C.size then C.rightVars ⟨i.val, h⟩ else ∅
  rightGates i := if h : i.val < C.size then (C.rightGates ⟨i.val, h⟩).image (Fin.castLE hsz) else ∅
  outVars := C.outVars
  outGates := C.outGates.image (Fin.castLE hsz)

lemma pad5_wf {n : ℕ} (C : AndCountCircuit n) (hsz : C.size ≤ 5) (hW : C.WellFormed) :
    (pad5 C hsz).WellFormed := by
  intro i
  by_cases hi : i.val < C.size
  · constructor
    · intro j hj
      change j ∈ (if h : i.val < C.size then (C.leftGates ⟨i.val, h⟩).image (Fin.castLE hsz) else ∅) at hj
      rw [dite_eq_left hi] at hj
      obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.mp hj
      exact (hW ⟨i.val, hi⟩).1 j0 hj0
    · intro j hj
      change j ∈ (if h : i.val < C.size then (C.rightGates ⟨i.val, h⟩).image (Fin.castLE hsz) else ∅) at hj
      rw [dite_eq_left hi] at hj
      obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.mp hj
      exact (hW ⟨i.val, hi⟩).2 j0 hj0
  · constructor
    · intro j hj
      change j ∈ (if h : i.val < C.size then (C.leftGates ⟨i.val, h⟩).image (Fin.castLE hsz) else ∅) at hj
      rw [dite_eq_right hi] at hj
      exact (Finset.notMem_empty j hj).elim
    · intro j hj
      change j ∈ (if h : i.val < C.size then (C.rightGates ⟨i.val, h⟩).image (Fin.castLE hsz) else ∅) at hj
      rw [dite_eq_right hi] at hj
      exact (Finset.notMem_empty j hj).elim

lemma pad5_disjoint {n : ℕ} (C : AndCountCircuit n) (hsz : C.size ≤ 5)
    (hD : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (i : Fin 5) :
    Disjoint ((pad5 C hsz).leftVars i) ((pad5 C hsz).rightVars i) := by
  by_cases hi : i.val < C.size
  · simpa [pad5, hi] using hD ⟨i.val, hi⟩
  · simp [pad5, hi]

lemma pad5_gateVal {n : ℕ} (C : AndCountCircuit n) (hsz : C.size ≤ 5) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin 5), i.val < m →
      (pad5 C hsz).gateVal U i = if h : i.val < C.size then C.gateVal U ⟨i.val, h⟩ else false := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    by_cases hlt : i.val < C.size
    · simp only [hlt, ↓reduceDIte]
      rw [Bool.eq_iff_iff, gateVal_unfold (pad5 C hsz) U i, gateVal_unfold C U ⟨i.val, hlt⟩,
          Bool.and_eq_true, Bool.and_eq_true]
      have hside : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
          sideTrue U B (F.image (Fin.castLE hsz)) i ((pad5 C hsz).gateVal U) = true ↔
          sideTrue U B F ⟨i.val, hlt⟩ (C.gateVal U) = true := by
        intro B F
        simp only [sideTrue, decide_eq_true_eq]
        constructor
        · rintro (h | ⟨j, hj, hji, hgv⟩)
          · exact Or.inl h
          · obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.mp hj
            have hgv' := ih (Fin.castLE hsz j0) (by change j0.val < m; exact Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi))
            simp only [Fin.val_castLE, j0.isLt, ↓reduceDIte] at hgv'
            rw [hgv'] at hgv
            exact Or.inr ⟨j0, hj0, hji, hgv⟩
        · rintro (h | ⟨j0, hj0, hji, hgv⟩)
          · exact Or.inl h
          · refine Or.inr ⟨Fin.castLE hsz j0, Finset.mem_image_of_mem _ hj0, hji, ?_⟩
            have hgv' := ih (Fin.castLE hsz j0) (by change j0.val < m; exact Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi))
            simp only [Fin.val_castLE, j0.isLt, ↓reduceDIte] at hgv'
            rw [hgv']; exact hgv
      have hL : (pad5 C hsz).leftVars i = C.leftVars ⟨i.val, hlt⟩ := by dsimp [pad5]; exact dite_eq_left hlt
      have hLG : (pad5 C hsz).leftGates i = (C.leftGates ⟨i.val, hlt⟩).image (Fin.castLE hsz) := by dsimp [pad5]; exact dite_eq_left hlt
      have hR : (pad5 C hsz).rightVars i = C.rightVars ⟨i.val, hlt⟩ := by dsimp [pad5]; exact dite_eq_left hlt
      have hRG : (pad5 C hsz).rightGates i = (C.rightGates ⟨i.val, hlt⟩).image (Fin.castLE hsz) := by dsimp [pad5]; exact dite_eq_left hlt
      exact and_congr (by rw [hL, hLG]; exact hside _ _) (by rw [hR, hRG]; exact hside _ _)
    · simp only [hlt, ↓reduceDIte]
      rw [gateVal_unfold (pad5 C hsz) U i]
      have hL : (pad5 C hsz).leftVars i = ∅ := by dsimp [pad5]; exact dite_eq_right hlt
      have hLG : (pad5 C hsz).leftGates i = ∅ := by dsimp [pad5]; exact dite_eq_right hlt
      rw [hL, hLG]
      simp [sideTrue]

lemma pad5_eval {n : ℕ} (C : AndCountCircuit n) (hsz : C.size ≤ 5) (U : Finset (Fin n)) :
    (pad5 C hsz).eval U = C.eval U := by
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  constructor
  · rintro (h | ⟨j, hj, hgv⟩)
    · exact Or.inl h
    · change j ∈ C.outGates.image (Fin.castLE hsz) at hj
      obtain ⟨j0, hj0, rfl⟩ := Finset.mem_image.mp hj
      have hgv' := pad5_gateVal C hsz U 5 (Fin.castLE hsz j0) (Fin.is_lt _)
      simp only [Fin.val_castLE, j0.isLt, ↓reduceDIte] at hgv'
      rw [hgv'] at hgv
      exact Or.inr ⟨j0, hj0, hgv⟩
  · rintro (h | ⟨j0, hj0, hgv⟩)
    · exact Or.inl h
    · refine Or.inr ⟨Fin.castLE hsz j0, Finset.mem_image_of_mem _ hj0, ?_⟩
      have hgv' := pad5_gateVal C hsz U 5 (Fin.castLE hsz j0) (Fin.is_lt _)
      simp only [Fin.val_castLE, j0.isLt, ↓reduceDIte] at hgv'
      exact hgv'.trans hgv

/-! ### `proj_count`: information-theoretic lower bound on free gates -/

def sv {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) (s : Bool) : Bool :=
  sideTrue X (cond s (C.rightVars i) (C.leftVars i)) (cond s (C.rightGates i) (C.leftGates i)) i
    (C.gateVal X)

lemma gate_false_iff {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal X i = false ↔ (sv C X i false = false ∨ sv C X i true = false) := by
  rw [gateVal_unfold, Bool.and_eq_false_iff]; rfl

lemma sv_hit {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
    (i : Fin C.size) (s : Bool)
    (h : ¬ Disjoint (cond s (C.rightVars i) (C.leftVars i)) U) : sv C X i s = true := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨x, hx, hxU⟩ := h
  exact (sideTrue_iff _ _ _ _ _).2 (Or.inl ⟨x, hx, hU hxU⟩)

lemma sv_merge {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n)) (i : Fin C.size)
    (s : Bool) (hX : sv C X i s = false) (hY : sv C Y i s = false)
    (ih : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
      C.gateVal (X ∪ Y) j = false) : sv C (X ∪ Y) i s = false := by
  rw [← Bool.not_eq_true] at hX hY ⊢
  unfold sv at hX hY ⊢
  rw [sideTrue_iff] at hX hY ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact hX (Or.inl ⟨x, hx, h⟩)
    · exact hY (Or.inl ⟨x, hx, h⟩)
  · have h1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]; exact fun hh => hX (Or.inr ⟨j, hj, hji, hh⟩)
    have h2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]; exact fun hh => hY (Or.inr ⟨j, hj, hji, hh⟩)
    rw [ih j hji h1 h2] at hv
    exact Bool.noConfusion hv

def code {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (i : Fin C.size) : Bool :=
  if ¬ Disjoint (C.leftVars i) U then true
  else if ¬ Disjoint (C.rightVars i) U then false
  else sv C X i false

lemma code_ok {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
    (i : Fin C.size) (h : C.gateVal X i = false) : sv C X i (code C U X i) = false := by
  rw [gate_false_iff] at h
  unfold code
  by_cases hl : ¬ Disjoint (C.leftVars i) U
  · rw [ite_eq_left hl]
    have := sv_hit C U X hU i false hl
    rcases h with h | h
    · rw [this] at h; exact Bool.noConfusion h
    · exact h
  · rw [ite_eq_right hl]
    by_cases hr : ¬ Disjoint (C.rightVars i) U
    · rw [ite_eq_left hr]
      have := sv_hit C U X hU i true hr
      rcases h with h | h
      · exact h
      · rw [this] at h; exact Bool.noConfusion h
    · rw [ite_eq_right hr]
      cases hb : sv C X i false with
      | false => exact hb
      | true =>
        rcases h with h | h
        · rw [hb] at h; exact Bool.noConfusion h
        · exact h

lemma code_hit {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (i : Fin C.size)
    (h : ¬ Disjoint (C.leftVars i ∪ C.rightVars i) U) : code C U X i = code C U Y i := by
  unfold code
  by_cases hl : ¬ Disjoint (C.leftVars i) U
  · rw [ite_eq_left hl, ite_eq_left hl]
  · rw [ite_eq_right hl, ite_eq_right hl]
    by_cases hr : ¬ Disjoint (C.rightVars i) U
    · rw [ite_eq_left hr, ite_eq_left hr]
    · exfalso; apply h; rw [Finset.disjoint_union_left]; exact ⟨not_not.1 hl, not_not.1 hr⟩

lemma merge_gate {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
    (hY : U ⊆ Y) (hc : ∀ i, code C U X i = code C U Y i) :
    ∀ i : Fin C.size, C.gateVal X i = false → C.gateVal Y i = false →
      C.gateVal (X ∪ Y) i = false := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → C.gateVal X i = false →
      C.gateVal Y i = false → C.gateVal (X ∪ Y) i = false := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi h1 h2
      have ih' : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
          C.gateVal (X ∪ Y) j = false := fun j hji => ih j (by omega)
      have c1 := code_ok C U X hX i h1
      have c2 := code_ok C U Y hY i h2
      rw [← hc i] at c2
      have hm := sv_merge C X Y i _ c1 c2 ih'
      rw [gate_false_iff]
      cases hb : code C U X i with
      | false => rw [hb] at hm; exact Or.inl hm
      | true => rw [hb] at hm; exact Or.inr hm
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

lemma merge_eval {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
    (hY : U ⊆ Y) (hc : ∀ i, code C U X i = code C U Y i)
    (h1 : C.eval X = false) (h2 : C.eval Y = false) : C.eval (X ∪ Y) = false := by
  rw [← Bool.not_eq_true, eval_iff] at h1 h2 ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact h1 (Or.inl ⟨x, hx, h⟩)
    · exact h2 (Or.inl ⟨x, hx, h⟩)
  · have g1 : C.gateVal X j = false := by rw [← Bool.not_eq_true]; exact fun hh => h1 (Or.inr ⟨j, hj, hh⟩)
    have g2 : C.gateVal Y j = false := by rw [← Bool.not_eq_true]; exact fun hh => h2 (Or.inr ⟨j, hj, hh⟩)
    rw [merge_gate C U X Y hX hY hc j g1 g2] at hv
    exact Bool.noConfusion hv

lemma proj_count {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (m : ℕ)
    (M : Fin m → Finset (Fin n)) (hU : ∀ a, U ⊆ M a) (h0 : ∀ a, C.eval (M a) = false)
    (h1 : ∀ a b, a ≠ b → C.eval (M a ∪ M b) = true) :
    m ≤ 2 ^ (Finset.univ.filter
      (fun i : Fin C.size => Disjoint (C.leftVars i ∪ C.rightVars i) U)).card := by
  let f : Fin m → ({i : Fin C.size // Disjoint (C.leftVars i ∪ C.rightVars i) U} → Bool) :=
    fun a i => code C U (M a) i.1
  have hf : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hc : ∀ i, code C U (M a) i = code C U (M b) i := by
      intro i
      by_cases hi : Disjoint (C.leftVars i ∪ C.rightVars i) U
      · exact congrFun hab ⟨i, hi⟩
      · exact code_hit C U _ _ i hi
    have := merge_eval C U (M a) (M b) (hU a) (hU b) hc (h0 a) (h0 b)
    rw [h1 a b hne] at this
    exact Bool.noConfusion this
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype] at hcard
  exact hcard

/-! ### `litSet` and `mis_cover` -/

def litSet {n : ℕ} (C : AndCountCircuit n) (v : Fin n) : Finset (Fin C.size × Bool) :=
  Finset.univ.filter (fun p => if p.2 then v ∈ C.rightVars p.1 else v ∈ C.leftVars p.1)

lemma mem_litSet {n : ℕ} (C : AndCountCircuit n) (v : Fin n) (g : Fin C.size) (b : Bool) :
    (g, b) ∈ litSet C v ↔ (if b then v ∈ C.rightVars g else v ∈ C.leftVars g) := by
  simp [litSet]

lemma hitGates_card_eq_litSet_card {n : ℕ} (C : AndCountCircuit n)
    (hD : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (v : Fin n) :
    (litSet C v).card =
      (Finset.univ.filter (fun i : Fin C.size => ¬ Disjoint (C.leftVars i ∪ C.rightVars i) {v})).card := by
  have himg : (litSet C v).image Prod.fst =
      Finset.univ.filter (fun i : Fin C.size => ¬ Disjoint (C.leftVars i ∪ C.rightVars i) {v}) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.not_disjoint_iff, Finset.mem_singleton, Finset.mem_union, mem_litSet, Prod.exists]
    constructor
    · rintro ⟨_, b, hb, rfl⟩
      refine ⟨v, ?_, rfl⟩
      cases b <;> simp_all
    · rintro ⟨x, hx, rfl⟩
      rcases hx with hL | hR
      · exact ⟨g, false, by simpa using hL, rfl⟩
      · exact ⟨g, true, by simpa using hR, rfl⟩
  rw [← himg]
  symm
  apply Finset.card_image_of_injOn
  rintro ⟨g1, b1⟩ h1 ⟨g2, b2⟩ h2 hg
  dsimp only at hg; subst hg
  have h1' := (mem_litSet C v g1 b1).mp h1
  have h2' := (mem_litSet C v g1 b2).mp h2
  cases b1 <;> cases b2 <;> try rfl
  · exact (Finset.disjoint_left.mp (hD g1) (by simpa using h1') (by simpa using h2')).elim
  · exact (Finset.disjoint_left.mp (hD g1) (by simpa using h2') (by simpa using h1')).elim

def misChoice {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (g : Fin C.size) : Option Bool :=
  if sideL C I g = false then some false
  else if sideR C I g = false then some true
  else none

lemma mis_cover_gen {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n))
    (h0 : C.eval I = false) :
    (∀ v ∈ I, ∀ g b, (g, b) ∈ litSet C v → misChoice C I g ≠ some b) ∧
    (∀ w, w ∉ I → w ∉ C.outVars → C.eval (insert w I) = true →
      ∃ g b, (g, b) ∈ litSet C w ∧ misChoice C I g = some b) := by
  constructor
  · intro v hv g b hgb
    rw [mem_litSet] at hgb
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hgb
      have hL : sideL C I g = true := (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨v, hgb, hv⟩)
      unfold misChoice; rw [hL]; simp only [Bool.true_eq_false, ↓reduceIte]
      split_ifs <;> simp
    · simp only [↓reduceIte] at hgb
      have hR : sideR C I g = true := (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨v, hgb, hv⟩)
      unfold misChoice; rw [hR]; simp only [Bool.true_eq_false, ↓reduceIte]
      split_ifs <;> simp
  · intro w hw hwOut hev
    let S : Finset (Fin C.size) :=
      Finset.univ.filter (fun i => C.gateVal I i = false ∧ C.gateVal (insert w I) i = true)
    have hSne : S.Nonempty := by
      rw [eval_iff] at hev
      rcases hev with ⟨v, hvO, hvI⟩ | ⟨i, hiO, hit⟩
      · rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact (hwOut hvO).elim
        · have het : C.eval I = true := (eval_iff C I).mpr (Or.inl ⟨v, hvO, hvi⟩)
          rw [h0] at het; exact Bool.noConfusion het
      · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hit⟩⟩
        rw [Bool.eq_false_iff]
        intro hti
        have het : C.eval I = true := (eval_iff C I).mpr (Or.inr ⟨i, hiO, hti⟩)
        rw [h0] at het; exact Bool.noConfusion het
    let g := S.min' hSne
    have hgS : g ∈ S := S.min'_mem hSne
    have hgF : C.gateVal I g = false := (Finset.mem_filter.mp hgS).2.1
    have hgT : C.gateVal (insert w I) g = true := (Finset.mem_filter.mp hgS).2.2
    have hmin : ∀ j : Fin C.size, j < g → C.gateVal (insert w I) j = true → C.gateVal I j = true := by
      intro j hj hjt
      by_contra hnf
      have hjf : C.gateVal I j = false := Bool.eq_false_iff.mpr hnf
      exact (not_le_of_gt hj) (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjf, hjt⟩))
    rw [gateVal_unfold, Bool.and_eq_true] at hgT
    rw [gateVal_unfold] at hgF
    change (sideL C I g && sideR C I g) = false at hgF
    change sideL C (insert w I) g = true ∧ sideR C (insert w I) g = true at hgT
    by_cases hL : sideL C I g = false
    · refine ⟨g, false, ?_, by simp [misChoice, hL]⟩
      rw [mem_litSet]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hLT := (sideTrue_iff _ _ _ _ _).mp hgT.1
      rcases hLT with ⟨v, hv, hvI⟩ | ⟨j, hj, hji, hjt⟩
      · rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact hv
        · have ht : sideL C I g = true := (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨v, hv, hvi⟩)
          rw [hL] at ht; exact Bool.noConfusion ht
      · have ht : sideL C I g = true := (sideTrue_iff _ _ _ _ _).mpr (Or.inr ⟨j, hj, hji, hmin j hji hjt⟩)
        rw [hL] at ht; exact Bool.noConfusion ht
    · have hLt : sideL C I g = true := by cases h' : sideL C I g <;> simp_all
      have hR : sideR C I g = false := by simp [hLt] at hgF; exact hgF
      refine ⟨g, true, ?_, by simp [misChoice, hLt, hR]⟩
      rw [mem_litSet]; simp only [↓reduceIte]
      have hRT := (sideTrue_iff _ _ _ _ _).mp hgT.2
      rcases hRT with ⟨v, hv, hvI⟩ | ⟨j, hj, hji, hjt⟩
      · rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact hv
        · have ht : sideR C I g = true := (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨v, hv, hvi⟩)
          rw [hR] at ht; exact Bool.noConfusion ht
      · have ht : sideR C I g = true := (sideTrue_iff _ _ _ _ _).mpr (Or.inr ⟨j, hj, hji, hmin j hji hjt⟩)
        rw [hR] at ht; exact Bool.noConfusion ht

/-! ## Section 3: Inlining a `0`-gate and proving `hit(0) = 1`, `hit(v) ≤ 2`, and `a0` properties -/

def Separates (C : AndCountCircuit 9) : Prop :=
  ∀ k : Fin 16, C.eval (rows9 k) = false ∧ ∀ w : V, w ∉ rows9 k → C.eval (insert w (rows9 k)) = true

lemma sep_outVars_empty {C : AndCountCircuit 9} (hsep : Separates C) : ∀ v : V, v ∉ C.outVars := by
  intro v hvO
  obtain ⟨k, hvk⟩ := cover_all v
  have h1 : C.eval (rows9 k) = true := (eval_iff C _).mpr (Or.inl ⟨v, hvO, hvk⟩)
  rw [(hsep k).1] at h1
  exact Bool.noConfusion h1

lemma sep_union_true {C : AndCountCircuit 9} (hsep : Separates C) {k1 k2 : Fin 16}
    (hdiff : ∃ w ∈ rows9 k1, w ∉ rows9 k2) : C.eval (rows9 k1 ∪ rows9 k2) = true := by
  obtain ⟨w, hw1, hw2⟩ := hdiff
  apply eval_mono_U C (U := insert w (rows9 k2))
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx2
    · exact Finset.mem_union_left _ hw1
    · exact Finset.mem_union_right _ hx2
  · exact (hsep k2).2 w hw2

lemma hit_le_two (C : AndCountCircuit 9) (hsz : C.size = 5)
    (hD : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (hsep : Separates C) (v : V) :
    (litSet C v).card ≤ 2 := by
  have hp := proj_count C {v} 5 (fun i => rows9 (throughV v i))
    (fun i => Finset.singleton_subset_iff.mpr (throughV_mem v i))
    (fun i => (hsep (throughV v i)).1)
    (fun i j hij => sep_union_true hsep (throughV_diff v i j hij))
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin C.size)))
    (fun i : Fin C.size => Disjoint (C.leftVars i ∪ C.rightVars i) {v})
  have hcardU : (Finset.univ : Finset (Fin C.size)).card = 5 := by rw [Finset.card_univ, Fintype.card_fin, hsz]
  rw [hcardU] at hc
  rw [hitGates_card_eq_litSet_card C hD v]
  by_contra hgt
  have hfree : (Finset.univ.filter (fun i : Fin C.size => Disjoint (C.leftVars i ∪ C.rightVars i) {v})).card ≤ 2 := by
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hfree
  exact absurd (le_trans hp hpow) (by decide)

/-- Inline gate `a` (assuming `0 ∈ leftVars a`, so on any `U` with `0 ∈ U`, `gate a = sideR a`)
    producing a circuit of size `k` from a circuit of size `k + 1`. -/
def inlineLeft {k : ℕ} (C : AndCountCircuit 9) (hsz : C.size = k + 1) (a : Fin (k + 1)) :
    AndCountCircuit 9 :=
  let a' : Fin C.size := ⟨a.val, by omega⟩
  let lift (j : Fin k) : Fin C.size := ⟨(a.succAbove j).val, by omega⟩
  { size := k
    leftVars := fun i =>
      let p := lift i
      if a' ∈ C.leftGates p then C.leftVars p ∪ C.rightVars a' else C.leftVars p
    leftGates := fun i =>
      let p := lift i
      if a' ∈ C.leftGates p then
        Finset.univ.filter (fun j : Fin k => j < i ∧ (lift j ∈ C.leftGates p ∨ (lift j ∈ C.rightGates a' ∧ lift j < a')))
      else
        Finset.univ.filter (fun j : Fin k => j < i ∧ lift j ∈ C.leftGates p)
    rightVars := fun i =>
      let p := lift i
      if a' ∈ C.rightGates p then C.rightVars p ∪ C.rightVars a' else C.rightVars p
    rightGates := fun i =>
      let p := lift i
      if a' ∈ C.rightGates p then
        Finset.univ.filter (fun j : Fin k => j < i ∧ (lift j ∈ C.rightGates p ∨ (lift j ∈ C.rightGates a' ∧ lift j < a')))
      else
        Finset.univ.filter (fun j : Fin k => j < i ∧ lift j ∈ C.rightGates p)
    outVars := if a' ∈ C.outGates then C.outVars ∪ C.rightVars a' else C.outVars
    outGates :=
      if a' ∈ C.outGates then
        Finset.univ.filter (fun j : Fin k => lift j ∈ C.outGates ∨ (lift j ∈ C.rightGates a' ∧ lift j < a'))
      else
        Finset.univ.filter (fun j : Fin k => lift j ∈ C.outGates) }

lemma inlineLeft_wf {k : ℕ} (C : AndCountCircuit 9) (hsz : C.size = k + 1) (a : Fin (k + 1)) :
    (inlineLeft C hsz a).WellFormed := by
  intro i
  constructor
  · intro j hj
    dsimp only [inlineLeft] at hj
    split_ifs at hj <;> exact (Finset.mem_filter.mp hj).2.1
  · intro j hj
    dsimp only [inlineLeft] at hj
    split_ifs at hj <;> exact (Finset.mem_filter.mp hj).2.1

lemma exists_succAbove_of_ne {k : ℕ} (a x : Fin (k + 1)) (hne : x ≠ a) :
    ∃ j : Fin k, a.succAbove j = x :=
  Fin.exists_succAbove_eq hne

lemma inlineLeft_gateVal {k : ℕ} (C : AndCountCircuit 9) (hW : C.WellFormed)
    (hsz : C.size = k + 1) (a : Fin (k + 1))
    (h0a : (0 : V) ∈ C.leftVars ⟨a.val, by omega⟩) (U : Finset V) (h0U : (0 : V) ∈ U) :
    ∀ (m : ℕ) (i : Fin k), i.val < m →
      (inlineLeft C hsz a).gateVal U i = C.gateVal U ⟨(a.succAbove i).val, by omega⟩ := by
  let a' : Fin C.size := ⟨a.val, by omega⟩
  let lift (j : Fin k) : Fin C.size := ⟨(a.succAbove j).val, by omega⟩
  have hga : C.gateVal U a' = sideR C U a' := by
    rw [gateVal_unfold]
    have hLa : sideTrue U (C.leftVars a') (C.leftGates a') a' (C.gateVal U) = true :=
      (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨0, h0a, h0U⟩)
    rw [hLa, Bool.true_and]; rfl
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    have hlt_eq : ∀ j : Fin k, j < i → (inlineLeft C hsz a).gateVal U j = C.gateVal U (lift j) :=
      fun j hji => ih j (by omega)
    have hside : ∀ (B : Finset V) (F : Finset (Fin C.size)),
        (∀ j ∈ F, j < lift i) →
        let p := lift i
        let B' := if a' ∈ F then B ∪ C.rightVars a' else B
        let F' := if a' ∈ F then
          Finset.univ.filter (fun j : Fin k => j < i ∧ (lift j ∈ F ∨ (lift j ∈ C.rightGates a' ∧ lift j < a')))
        else
          Finset.univ.filter (fun j : Fin k => j < i ∧ lift j ∈ F)
        sideTrue U B' F' i ((inlineLeft C hsz a).gateVal U) = sideTrue U B F p (C.gateVal U) := by
      intro B F hF p B' F'
      rw [Bool.eq_iff_iff]
      simp only [sideTrue, decide_eq_true_eq]
      by_cases haF : a' ∈ F
      · have hap : a' < p := hF a' haF
        simp only [B', F', haF, ↓reduceIte, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (⟨x, hx | hx, hxU⟩ | ⟨j, ⟨hji, hjF | ⟨hjR, hja⟩⟩, _, hjv⟩)
          · exact Or.inl ⟨x, hx, hxU⟩
          · refine Or.inr ⟨a', haF, hap, ?_⟩
            rw [hga]; exact (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨x, hx, hxU⟩)
          · rw [hlt_eq j hji] at hjv
            have hjp : lift j < p := Fin.succAbove_lt_succAbove_iff.mpr hji
            exact Or.inr ⟨lift j, hjF, hjp, hjv⟩
          · rw [hlt_eq j hji] at hjv
            refine Or.inr ⟨a', haF, hap, ?_⟩
            rw [hga]; exact (sideTrue_iff _ _ _ _ _).mpr (Or.inr ⟨lift j, hjR, hja, hjv⟩)
        · rintro (⟨x, hx, hxU⟩ | ⟨j0, hj0, hjp, hgv⟩)
          · exact Or.inl ⟨x, Or.inl hx, hxU⟩
          · by_cases hj0a : j0 = a'
            · subst hj0a
              rw [hga] at hgv
              rcases (sideTrue_iff _ _ _ _ _).mp hgv with ⟨x, hx, hxU⟩ | ⟨j1, hj1R, hj1a, hj1v⟩
              · exact Or.inl ⟨x, Or.inr hx, hxU⟩
              · have hne1 : (⟨j1.val, by omega⟩ : Fin (k + 1)) ≠ a := fun h =>
                  (ne_of_lt hj1a) (Fin.ext (by simpa [a'] using congrArg Fin.val h))
                obtain ⟨j, hj⟩ := exists_succAbove_of_ne a ⟨j1.val, by omega⟩ hne1
                have hlj : lift j = j1 := Fin.ext (by simp [lift, hj])
                have hji : j < i := by
                  rw [← Fin.succAbove_lt_succAbove_iff (p := a)]
                  show a.succAbove j < a.succAbove i
                  rw [hj]; exact lt_trans hj1a hap
                refine Or.inr ⟨j, ⟨hji, Or.inr ⟨hlj.symm ▸ hj1R, hlj.symm ▸ hj1a⟩⟩, hji, ?_⟩
                rw [hlt_eq j hji, hlj]; exact hj1v
            · have hne : (⟨j0.val, by omega⟩ : Fin (k + 1)) ≠ a := fun h =>
                hj0a (Fin.ext (by simpa [a'] using congrArg Fin.val h))
              obtain ⟨j, hj⟩ := exists_succAbove_of_ne a ⟨j0.val, by omega⟩ hne
              have hlj : lift j = j0 := Fin.ext (by simp [lift, hj])
              have hji : j < i := by
                rw [← Fin.succAbove_lt_succAbove_iff (p := a)]
                show a.succAbove j < a.succAbove i
                rw [hj]; exact hjp
              refine Or.inr ⟨j, ⟨hji, Or.inl (hlj.symm ▸ hj0)⟩, hji, ?_⟩
              rw [hlt_eq j hji, hlj]; exact hgv
      · simp only [B', F', haF, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (h | ⟨j, ⟨hji, hjF⟩, _, hjv⟩)
          · exact Or.inl h
          · rw [hlt_eq j hji] at hjv
            have hjp : lift j < p := Fin.succAbove_lt_succAbove_iff.mpr hji
            exact Or.inr ⟨lift j, hjF, hjp, hjv⟩
        · rintro (h | ⟨j0, hj0, hjp, hgv⟩)
          · exact Or.inl h
          · have hne : (⟨j0.val, by omega⟩ : Fin (k + 1)) ≠ a := by
              intro heq; apply haF
              have : j0 = a' := Fin.ext (by simpa [a'] using congrArg Fin.val heq)
              rwa [← this]
            obtain ⟨j, hj⟩ := exists_succAbove_of_ne a ⟨j0.val, by omega⟩ hne
            have hlj : lift j = j0 := Fin.ext (by simp [lift, hj])
            have hji : j < i := by
              rw [← Fin.succAbove_lt_succAbove_iff (p := a)]
              show a.succAbove j < a.succAbove i
              rw [hj]; exact hjp
            refine Or.inr ⟨j, ⟨hji, hlj.symm ▸ hj0⟩, hji, ?_⟩
            rw [hlt_eq j hji, hlj]; exact hgv
    rw [gateVal_unfold (inlineLeft C hsz a) U i, gateVal_unfold C U (lift i)]
    exact congrArg₂ (· && ·)
      (hside (C.leftVars (lift i)) (C.leftGates (lift i)) (hW (lift i)).1)
      (hside (C.rightVars (lift i)) (C.rightGates (lift i)) (hW (lift i)).2)

lemma inlineLeft_eval {k : ℕ} (C : AndCountCircuit 9) (hW : C.WellFormed)
    (hsz : C.size = k + 1) (a : Fin (k + 1))
    (h0a : (0 : V) ∈ C.leftVars ⟨a.val, by omega⟩) (U : Finset V) (h0U : (0 : V) ∈ U) :
    (inlineLeft C hsz a).eval U = C.eval U := by
  let a' : Fin C.size := ⟨a.val, by omega⟩
  let lift (j : Fin k) : Fin C.size := ⟨(a.succAbove j).val, by omega⟩
  have hga : C.gateVal U a' = sideR C U a' := by
    rw [gateVal_unfold]
    have hLa : sideTrue U (C.leftVars a') (C.leftGates a') a' (C.gateVal U) = true :=
      (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨0, h0a, h0U⟩)
    rw [hLa, Bool.true_and]; rfl
  have hgv : ∀ j : Fin k, (inlineLeft C hsz a).gateVal U j = C.gateVal U (lift j) :=
    fun j => inlineLeft_gateVal C hW hsz a h0a U h0U k j j.isLt
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  by_cases haO : a' ∈ C.outGates
  · have hOV : (inlineLeft C hsz a).outVars = C.outVars ∪ C.rightVars a' := by
      dsimp only [inlineLeft]; exact ite_eq_left haO
    have hOG : (inlineLeft C hsz a).outGates =
        Finset.univ.filter (fun j : Fin k => lift j ∈ C.outGates ∨ (lift j ∈ C.rightGates a' ∧ lift j < a')) := by
      dsimp only [inlineLeft]; exact ite_eq_left haO
    rw [hOV, hOG]
    constructor
    · rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hjv⟩)
      · rcases Finset.mem_union.mp hx with hx1 | hx2
        · exact Or.inl ⟨x, hx1, hxU⟩
        · refine Or.inr ⟨a', haO, ?_⟩
          rw [hga]; exact (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨x, hx2, hxU⟩)
      · rw [hgv j] at hjv
        rcases (Finset.mem_filter.mp hj).2 with hjO | ⟨hjR, hja⟩
        · exact Or.inr ⟨lift j, hjO, hjv⟩
        · refine Or.inr ⟨a', haO, ?_⟩
          rw [hga]; exact (sideTrue_iff _ _ _ _ _).mpr (Or.inr ⟨lift j, hjR, hja, hjv⟩)
    · rintro (⟨x, hx, hxU⟩ | ⟨j0, hj0, hjv⟩)
      · exact Or.inl ⟨x, Finset.mem_union_left _ hx, hxU⟩
      · by_cases hj0a : j0 = a'
        · subst hj0a; rw [hga] at hjv
          rcases (sideTrue_iff _ _ _ _ _).mp hjv with ⟨x, hx, hxU⟩ | ⟨j1, hj1R, hj1a, hj1v⟩
          · exact Or.inl ⟨x, Finset.mem_union_right _ hx, hxU⟩
          · have hne1 : (⟨j1.val, by omega⟩ : Fin (k + 1)) ≠ a := fun h =>
              (ne_of_lt hj1a) (Fin.ext (by simpa [a'] using congrArg Fin.val h))
            obtain ⟨j, hj⟩ := exists_succAbove_of_ne a ⟨j1.val, by omega⟩ hne1
            have hlj : lift j = j1 := Fin.ext (by simp [lift, hj])
            refine Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hlj.symm ▸ hj1R, hlj.symm ▸ hj1a⟩⟩, ?_⟩
            rw [hgv j, hlj]; exact hj1v
        · have hne : (⟨j0.val, by omega⟩ : Fin (k + 1)) ≠ a := fun h =>
            hj0a (Fin.ext (by simpa [a'] using congrArg Fin.val h))
          obtain ⟨j, hj⟩ := exists_succAbove_of_ne a ⟨j0.val, by omega⟩ hne
          have hlj : lift j = j0 := Fin.ext (by simp [lift, hj])
          refine Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (hlj.symm ▸ hj0)⟩, ?_⟩
          rw [hgv j, hlj]; exact hjv
  · have hOV : (inlineLeft C hsz a).outVars = C.outVars := by
      dsimp only [inlineLeft]; exact ite_eq_right haO
    have hOG : (inlineLeft C hsz a).outGates = Finset.univ.filter (fun j : Fin k => lift j ∈ C.outGates) := by
      dsimp only [inlineLeft]; exact ite_eq_right haO
    rw [hOV, hOG]
    constructor
    · rintro (h | ⟨j, hj, hjv⟩)
      · exact Or.inl h
      · rw [hgv j] at hjv; exact Or.inr ⟨lift j, (Finset.mem_filter.mp hj).2, hjv⟩
    · rintro (h | ⟨j0, hj0, hjv⟩)
      · exact Or.inl h
      · have hne : (⟨j0.val, by omega⟩ : Fin (k + 1)) ≠ a := fun h =>
          haO (by have : j0 = a' := Fin.ext (by simpa [a'] using congrArg Fin.val h); rwa [← this])
        obtain ⟨j, hj⟩ := exists_succAbove_of_ne a ⟨j0.val, by omega⟩ hne
        have hlj : lift j = j0 := Fin.ext (by simp [lift, hj])
        refine Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlj.symm ▸ hj0⟩, ?_⟩
        rw [hgv j, hlj]; exact hjv

/-- G282 subproblem (`0 ∈ U` on G9) has no 3-gate `AndCountCircuit`! -/
lemma no_3and_G282 (E : AndCountCircuit 9) (hsz : E.size = 3)
    (hE : ∀ r : Fin 8, E.eval (rows9 (rows0 r)) = false ∧
      ∀ w : V, w ∉ rows9 (rows0 r) → E.eval (insert w (rows9 (rows0 r))) = true) : False := by
  let D := stripCircuit E
  have hDsz : D.size = 3 := hsz
  have hDd : ∀ i, Disjoint (D.leftVars i) (D.rightVars i) := strip_disjoint E
  have hDe : ∀ r : Fin 8, D.eval (rows9 (rows0 r)) = false ∧
      ∀ w : V, w ∉ rows9 (rows0 r) → D.eval (insert w (rows9 (rows0 r))) = true := by
    intro r
    simpa only [D, strip_eval_eq] using hE r
  have hOut : ∀ t : Fin 4, v36 t ∉ D.outVars := by
    intro t htO
    have hmem := through0_mem t 0
    have h1 : D.eval (rows9 (rows0 (through0 t 0))) = true := (eval_iff D _).mpr (Or.inl ⟨v36 t, htO, hmem⟩)
    rw [(hDe (through0 t 0)).1] at h1
    exact Bool.noConfusion h1
  have hcard1 : ∀ t : Fin 4, (litSet D (v36 t)).card = 1 := by
    intro t
    have hle : (litSet D (v36 t)).card ≤ 1 := by
      have hp := proj_count D {v36 t} 3 (fun i => rows9 (rows0 (through0 t i)))
        (fun i => Finset.singleton_subset_iff.mpr (through0_mem t i))
        (fun i => (hDe (through0 t i)).1)
        (fun i j hij => by
          obtain ⟨w, hw1, hw2⟩ := through0_diff t i j hij
          apply eval_mono_U D (U := insert w (rows9 (rows0 (through0 t j))))
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx2
            · exact Finset.mem_union_left _ hw1
            · exact Finset.mem_union_right _ hx2
          · exact (hDe (through0 t j)).2 w hw2)
      have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin D.size)))
        (fun i : Fin D.size => Disjoint (D.leftVars i ∪ D.rightVars i) {v36 t})
      have hcardU : (Finset.univ : Finset (Fin D.size)).card = 3 := by
        rw [Finset.card_univ, Fintype.card_fin, hDsz]
      rw [hcardU] at hc
      rw [hitGates_card_eq_litSet_card D hDd (v36 t)]
      by_contra hgt
      have hfree : (Finset.univ.filter (fun i : Fin D.size => Disjoint (D.leftVars i ∪ D.rightVars i) {v36 t})).card ≤ 1 := by
        omega
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hfree
      exact absurd (le_trans hp hpow) (by decide)
    have hge : 1 ≤ (litSet D (v36 t)).card := by
      obtain ⟨r, _, hnot⟩ := sep0_in t (if t = 0 then 1 else 0) (by fin_cases t <;> decide)
      obtain ⟨g, b, hgb, _⟩ := (mis_cover_gen D (rows9 (rows0 r)) (hDe r).1).2
        (v36 t) hnot (hOut t) ((hDe r).2 (v36 t) hnot)
      exact Finset.card_pos.mpr ⟨(g, b), hgb⟩
    omega
  have hex : ∀ t : Fin 4, ∃ p : Fin D.size × Bool, litSet D (v36 t) = {p} :=
    fun t => Finset.card_eq_one.mp (hcard1 t)
  let gfn : Fin 4 → Fin D.size := fun t => (hex t).choose.1
  let bfn : Fin 4 → Bool := fun t => (hex t).choose.2
  have hmem : ∀ t : Fin 4, (gfn t, bfn t) ∈ litSet D (v36 t) := fun t => by
    rw [(hex t).choose_spec]; exact Finset.mem_singleton_self _
  have huniq : ∀ t : Fin 4, ∀ p, p ∈ litSet D (v36 t) → p = (gfn t, bfn t) := fun t p hp => by
    rw [(hex t).choose_spec, Finset.mem_singleton] at hp; exact hp
  have hinj : Function.Injective gfn := by
    intro t1 t2 hgeq
    by_contra hne
    obtain ⟨r1, h2in, h1out⟩ := sep0_in t1 t2 hne
    have hcov1 := mis_cover_gen D (rows9 (rows0 r1)) (hDe r1).1
    obtain ⟨g1, b1, hgb1, hch1⟩ := hcov1.2 (v36 t1) h1out (hOut t1) ((hDe r1).2 (v36 t1) h1out)
    have hp1 := huniq t1 (g1, b1) hgb1
    have hch1' : misChoice D (rows9 (rows0 r1)) (gfn t1) = some (bfn t1) := by
      have := congrArg Prod.fst hp1; have := congrArg Prod.snd hp1
      dsimp only at *; subst_vars; exact hch1
    have hne_b : bfn t1 ≠ bfn t2 := by
      intro hbeq
      have hno := hcov1.1 (v36 t2) h2in (gfn t2) (bfn t2) (hmem t2)
      rw [← hgeq, ← hbeq] at hno
      exact hno hch1'
    obtain ⟨r2, h1out2, h2out2⟩ := sep0_out t1 t2 hne
    have hcov2 := mis_cover_gen D (rows9 (rows0 r2)) (hDe r2).1
    obtain ⟨g1', b1', hgb1', hch1''⟩ := hcov2.2 (v36 t1) h1out2 (hOut t1) ((hDe r2).2 (v36 t1) h1out2)
    obtain ⟨g2', b2', hgb2', hch2''⟩ := hcov2.2 (v36 t2) h2out2 (hOut t2) ((hDe r2).2 (v36 t2) h2out2)
    have e1 := huniq t1 (g1', b1') hgb1'
    have e2 := huniq t2 (g2', b2') hgb2'
    have hc1 : misChoice D (rows9 (rows0 r2)) (gfn t1) = some (bfn t1) := by
      cases e1; exact hch1''
    have hc2 : misChoice D (rows9 (rows0 r2)) (gfn t2) = some (bfn t2) := by
      cases e2; exact hch2''
    rw [hgeq] at hc1
    rw [hc1] at hc2
    exact hne_b (Option.some.inj hc2)
  have hle4 := Fintype.card_le_of_injective gfn hinj
  rw [Fintype.card_fin, Fintype.card_fin, hDsz] at hle4
  omega

/-- Vertex `0` appears bare in at most one gate of any 5-gate circuit separating G9. -/
lemma hit_zero_le_one (D : AndCountCircuit 9) (hW : D.WellFormed) (hsz : D.size = 5)
    (hD : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) (hsep : Separates D) :
    (litSet D 0).card ≤ 1 := by
  by_contra hgt
  have h2 : 2 ≤ (litSet D 0).card := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (litSet D 0).card)
  have hgpq : p.1 ≠ q.1 := by
    intro heq
    apply hpq
    ext
    · exact congrArg Fin.val heq
    · have hp' := (mem_litSet D 0 p.1 p.2).mp hp
      have hq' := (mem_litSet D 0 q.1 q.2).mp hq
      rw [← heq] at hq'
      cases hb1 : p.2 <;> cases hb2 : q.2 <;> try rfl
      · simp [hb1] at hp'; simp [hb2] at hq'
        exact (Finset.disjoint_left.mp (hD p.1) hp' hq').elim
      · simp [hb1] at hp'; simp [hb2] at hq'
        exact (Finset.disjoint_left.mp (hD p.1) hq' hp').elim
  let g1 : Fin 5 := ⟨p.1.val, by omega⟩
  let g2 : Fin 5 := ⟨q.1.val, by omega⟩
  have hg12 : g1 ≠ g2 := fun h => hgpq (Fin.ext (by simpa [g1, g2] using congrArg Fin.val h))
  let ε : Fin D.size → Bool := fun i => decide ((0 : V) ∈ D.rightVars i)
  let D1 := swapSide D ε
  have hD1W : D1.WellFormed := swapSide_wf D ε hW
  have hD1sz : D1.size = 5 := hsz
  have h0in : ∀ i : Fin D.size, (0 : V) ∈ D.leftVars i ∨ (0 : V) ∈ D.rightVars i → (0 : V) ∈ D1.leftVars i := by
    intro i hi
    by_cases hR : (0 : V) ∈ D.rightVars i
    · have hε : ε i = true := decide_eq_true hR
      simpa [D1, swapSide, hε] using hR
    · have hε : ε i = false := decide_eq_false hR
      have hL : (0 : V) ∈ D.leftVars i := hi.resolve_right hR
      simpa [D1, swapSide, hε] using hL
  have h0p : (0 : V) ∈ D1.leftVars p.1 := h0in p.1 (by
    have h1 := (mem_litSet D 0 p.1 p.2).mp hp
    cases hb : p.2 <;> simp [hb] at h1
    · exact Or.inl h1
    · exact Or.inr h1)
  have h0q : (0 : V) ∈ D1.leftVars q.1 := h0in q.1 (by
    have h1 := (mem_litSet D 0 q.1 q.2).mp hq
    cases hb : q.2 <;> simp [hb] at h1
    · exact Or.inl h1
    · exact Or.inr h1)
  have hab_ex : ∃ a b : Fin 5, a < b ∧ (0 : V) ∈ D1.leftVars ⟨a.val, by omega⟩ ∧
      (0 : V) ∈ D1.leftVars ⟨b.val, by omega⟩ := by
    rcases lt_or_gt_of_ne hg12 with hlt | hgt'
    · exact ⟨g1, g2, hlt, h0p, h0q⟩
    · exact ⟨g2, g1, hgt', h0q, h0p⟩
  obtain ⟨a, b, hab, h0a, h0b⟩ := hab_ex
  let D2 := inlineLeft D1 hD1sz b
  have hD2W : D2.WellFormed := inlineLeft_wf D1 hD1sz b
  have hD2sz : D2.size = 4 := rfl
  let a4 : Fin 4 := ⟨a.val, by omega⟩
  have hsucc : b.succAbove a4 = a := by
    apply Fin.ext
    show (Fin.succAbove b a4).val = a.val
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · exact hab
  have h0a4 : (0 : V) ∈ D2.leftVars a4 := by
    dsimp only [D2, inlineLeft]
    have hlift : (⟨(b.succAbove a4).val, by omega⟩ : Fin D1.size) = ⟨a.val, by omega⟩ :=
      Fin.ext (by simpa using congrArg Fin.val hsucc)
    rw [hlift]
    split_ifs
    · exact Finset.mem_union_left _ h0a
    · exact h0a
  let D3 := inlineLeft D2 hD2sz a4
  apply no_3and_G282 D3 rfl
  intro r
  have h0r : (0 : V) ∈ rows9 (rows0 r) := rows0_has0 r
  have hev : ∀ U : Finset V, (0 : V) ∈ U → D3.eval U = D.eval U := by
    intro U h0U
    rw [inlineLeft_eval D2 hD2W hD2sz a4 h0a4 U h0U,
        inlineLeft_eval D1 hD1W hD1sz b h0b U h0U,
        swapSide_eval D ε U]
  exact ⟨by rw [hev _ h0r]; exact (hsep (rows0 r)).1,
         fun w hw => by rw [hev _ (Finset.mem_insert_of_mem h0r)]; exact (hsep (rows0 r)).2 w hw⟩

/-- Existence and exact structure of the unique gate `a0` containing `0`. -/
lemma exists_unique_a0 (D : AndCountCircuit 9) (hW : D.WellFormed) (hsz : D.size = 5)
    (hD : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) (hsep : Separates D) :
    ∃ a0 : Fin 5, ∃ D' : AndCountCircuit 9, ∃ hsz' : D'.size = 5,
      D'.WellFormed ∧ (∀ i, Disjoint (D'.leftVars i) (D'.rightVars i)) ∧
      Separates D' ∧
      D'.leftVars ⟨a0.val, by omega⟩ = {0} ∧
      (0 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩ ∧
      (∀ i : Fin 5, i ≠ a0 → (0 : V) ∉ D'.leftVars ⟨i.val, by omega⟩ ∧ (0 : V) ∉ D'.rightVars ⟨i.val, by omega⟩) ∧
      (∀ k : Fin 16, (0 : V) ∉ rows9 k →
        sideL D' (rows9 k) ⟨a0.val, by omega⟩ = false ∧
        sideR D' (rows9 k) ⟨a0.val, by omega⟩ = true) := by
  have hle1 := hit_zero_le_one D hW hsz hD hsep
  obtain ⟨k0, hk0⟩ := avoid_all 0
  obtain ⟨g0, b0, hg0b0, _⟩ := (mis_cover_gen D (rows9 k0) (hsep k0).1).2
    0 hk0 (sep_outVars_empty hsep 0) ((hsep k0).2 0 hk0)
  have hcard1 : (litSet D 0).card = 1 := by
    have hpos : 1 ≤ (litSet D 0).card := Finset.card_pos.mpr ⟨(g0, b0), hg0b0⟩
    omega
  have hsing : litSet D 0 = {(g0, b0)} := by
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard1
    have : (g0, b0) = p := by rw [hp, Finset.mem_singleton] at hg0b0; exact hg0b0
    rwa [← this] at hp
  let ε : Fin D.size → Bool := fun i => if i = g0 then b0 else false
  let D' := swapSide D ε
  let a0 : Fin 5 := ⟨g0.val, by omega⟩
  have hD'sz : D'.size = 5 := hsz
  have hD'W : D'.WellFormed := swapSide_wf D ε hW
  have hD'd : ∀ i, Disjoint (D'.leftVars i) (D'.rightVars i) := swapSide_disjoint D ε hD
  have hD'sep : Separates D' := fun k => by simpa [D', swapSide_eval] using hsep k
  have h0inL : (0 : V) ∈ D'.leftVars ⟨a0.val, by omega⟩ := by
    have hmem := (mem_litSet D 0 g0 b0).mp hg0b0
    have ha0eq : (⟨a0.val, by omega⟩ : Fin D'.size) = g0 := Fin.ext rfl
    rw [ha0eq]
    cases hb : b0
    · simp [D', swapSide, ε, hb]; simpa [hb] using hmem
    · simp [D', swapSide, ε, hb]; simpa [hb] using hmem
  have h0notR : (0 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩ :=
    Finset.disjoint_left.mp (hD'd ⟨a0.val, by omega⟩) h0inL
  have h0other : ∀ i : Fin 5, i ≠ a0 →
      (0 : V) ∉ D'.leftVars ⟨i.val, by omega⟩ ∧ (0 : V) ∉ D'.rightVars ⟨i.val, by omega⟩ := by
    intro i hi
    have hig : (⟨i.val, by omega⟩ : Fin D.size) ≠ g0 := fun h =>
      hi (Fin.ext (by simpa [a0] using congrArg Fin.val h))
    have hε : ε ⟨i.val, by omega⟩ = false := by simp [ε, hig]
    constructor
    · intro hL
      have hL' : (0 : V) ∈ D.leftVars ⟨i.val, by omega⟩ := by simpa [D', swapSide, hε] using hL
      have hm : (⟨i.val, by omega⟩, false) ∈ litSet D 0 := (mem_litSet D 0 _ false).mpr (by simpa using hL')
      rw [hsing, Finset.mem_singleton] at hm
      exact hig (congrArg Prod.fst hm)
    · intro hR
      have hR' : (0 : V) ∈ D.rightVars ⟨i.val, by omega⟩ := by simpa [D', swapSide, hε] using hR
      have hm : (⟨i.val, by omega⟩, true) ∈ litSet D 0 := (mem_litSet D 0 _ true).mpr (by simpa using hR')
      rw [hsing, Finset.mem_singleton] at hm
      exact hig (congrArg Prod.fst hm)
  have hno0 : ∀ k : Fin 16, (0 : V) ∉ rows9 k →
      sideL D' (rows9 k) ⟨a0.val, by omega⟩ = false ∧
      sideR D' (rows9 k) ⟨a0.val, by omega⟩ = true := by
    intro k hk
    let I := rows9 k
    have hlt_eq : ∀ (m : ℕ) (j : Fin D'.size), j.val < m → j.val < a0.val →
        D'.gateVal (insert 0 I) j = D'.gateVal I j := by
      intro m
      induction m with
      | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
      | succ m ih =>
        intro j hjm hja
        have hjne : (⟨j.val, by omega⟩ : Fin 5) ≠ a0 := fun h => by
          have := congrArg Fin.val h; simp at this; omega
        have h0j := h0other ⟨j.val, by omega⟩ hjne
        have hsub : ∀ B : Finset V, (0 : V) ∉ B →
            ((∃ x ∈ B, x ∈ insert (0 : V) I) ↔ (∃ x ∈ B, x ∈ I)) := by
          intro B h0B
          constructor
          · rintro ⟨x, hxB, hxI⟩
            rcases Finset.mem_insert.mp hxI with rfl | hxi
            · exact (h0B hxB).elim
            · exact ⟨x, hxB, hxi⟩
          · rintro ⟨x, hxB, hxi⟩; exact ⟨x, hxB, Finset.mem_insert_of_mem hxi⟩
        have hltj : ∀ j' : Fin D'.size, j' < j → D'.gateVal (insert 0 I) j' = D'.gateVal I j' :=
          fun j' hj' => ih j' (by have : j'.val < j.val := hj'; omega) (lt_trans hj' hja)
        rw [gateVal_unfold, gateVal_unfold]
        congr 1
        · rw [Bool.eq_iff_iff, sideTrue_iff, sideTrue_iff]
          refine or_congr (hsub _ h0j.1) ⟨?_, ?_⟩
          · rintro ⟨j', hj'F, hj'j, hj'v⟩; exact ⟨j', hj'F, hj'j, by rwa [← hltj j' hj'j]⟩
          · rintro ⟨j', hj'F, hj'j, hj'v⟩; exact ⟨j', hj'F, hj'j, by rwa [hltj j' hj'j]⟩
        · rw [Bool.eq_iff_iff, sideTrue_iff, sideTrue_iff]
          refine or_congr (hsub _ h0j.2) ⟨?_, ?_⟩
          · rintro ⟨j', hj'F, hj'j, hj'v⟩; exact ⟨j', hj'F, hj'j, by rwa [← hltj j' hj'j]⟩
          · rintro ⟨j', hj'F, hj'j, hj'v⟩; exact ⟨j', hj'F, hj'j, by rwa [hltj j' hj'j]⟩
    have hfl : D'.eval I = false := (hD'sep k).1
    have hev : D'.eval (insert 0 I) = true := (hD'sep k).2 0 hk
    let S : Finset (Fin D'.size) :=
      Finset.univ.filter (fun i => D'.gateVal I i = false ∧ D'.gateVal (insert 0 I) i = true)
    have hSne : S.Nonempty := by
      rw [eval_iff] at hev
      rcases hev with ⟨v, hvO, _⟩ | ⟨i, hiO, hit⟩
      · exact (sep_outVars_empty hD'sep v hvO).elim
      · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hit⟩⟩
        rw [Bool.eq_false_iff]; intro hti
        have := (eval_iff D' I).mpr (Or.inr ⟨i, hiO, hti⟩); rw [hfl] at this; exact Bool.noConfusion this
    let g := S.min' hSne
    have hgS : g ∈ S := S.min'_mem hSne
    have hgF : D'.gateVal I g = false := (Finset.mem_filter.mp hgS).2.1
    have hgT : D'.gateVal (insert 0 I) g = true := (Finset.mem_filter.mp hgS).2.2
    have hmin : ∀ j : Fin D'.size, j < g → D'.gateVal (insert 0 I) j = true → D'.gateVal I j = true := by
      intro j hj hjt
      by_contra hnf
      exact (not_le_of_gt hj) (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_false_iff.mpr hnf, hjt⟩))
    have hga0 : g = ⟨a0.val, by omega⟩ := by
      by_contra hne
      have hne5 : (⟨g.val, by omega⟩ : Fin 5) ≠ a0 := fun h =>
        hne (Fin.ext (by simpa using congrArg Fin.val h))
      have h0g := h0other ⟨g.val, by omega⟩ hne5
      rw [gateVal_unfold, Bool.and_eq_true, sideTrue_iff, sideTrue_iff] at hgT
      have hgtI : D'.gateVal I g = true := by
        rw [gateVal_unfold, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]
        constructor
        · rcases hgT.1 with ⟨v, hvL, hvI⟩ | ⟨j, hjF, hjg, hjv⟩
          · rcases Finset.mem_insert.mp hvI with rfl | hvi
            · exact (h0g.1 hvL).elim
            · exact Or.inl ⟨v, hvL, hvi⟩
          · exact Or.inr ⟨j, hjF, hjg, hmin j hjg hjv⟩
        · rcases hgT.2 with ⟨v, hvR, hvI⟩ | ⟨j, hjF, hjg, hjv⟩
          · rcases Finset.mem_insert.mp hvI with rfl | hvi
            · exact (h0g.2 hvR).elim
            · exact Or.inl ⟨v, hvR, hvi⟩
          · exact Or.inr ⟨j, hjF, hjg, hmin j hjg hjv⟩
      rw [hgF] at hgtI; exact Bool.noConfusion hgtI
    rw [hga0] at hgF hgT
    rw [gateVal_unfold, Bool.and_eq_true] at hgT
    have hRtrue : sideR D' I ⟨a0.val, by omega⟩ = true := by
      have hRT := (sideTrue_iff _ _ _ _ _).mp hgT.2
      apply (sideTrue_iff _ _ _ _ _).mpr
      rcases hRT with ⟨v, hvR, hvI⟩ | ⟨j, hjF, hja, hjv⟩
      · rcases Finset.mem_insert.mp hvI with rfl | hvi
        · exact (h0notR hvR).elim
        · exact Or.inl ⟨v, hvR, hvi⟩
      · exact Or.inr ⟨j, hjF, hja, by rwa [← hlt_eq D'.size j j.isLt hja]⟩
    have hLfalse : sideL D' I ⟨a0.val, by omega⟩ = false := by
      rw [gateVal_unfold] at hgF
      change (sideL D' I ⟨a0.val, by omega⟩ && sideR D' I ⟨a0.val, by omega⟩) = false at hgF
      rw [hRtrue, Bool.and_true] at hgF; exact hgF
    exact ⟨hLfalse, hRtrue⟩
  have hLa0 : D'.leftVars ⟨a0.val, by omega⟩ = {0} := by
    ext v
    rw [Finset.mem_singleton]
    constructor
    · intro hvL
      by_contra hne
      obtain ⟨k, h0k, hvk⟩ := cover_no0 v hne
      have hLt : sideL D' (rows9 k) ⟨a0.val, by omega⟩ = true :=
        (sideTrue_iff _ _ _ _ _).mpr (Or.inl ⟨v, hvL, hvk⟩)
      rw [(hno0 k h0k).1] at hLt
      exact Bool.noConfusion hLt
    · rintro rfl; exact h0inL
  exact ⟨a0, D', hD'sz, hD'W, hD'd, hD'sep, hLa0, h0notR, h0other, hno0⟩

/-! ## Section 4: `Aut(G9)` variable permutations and gate canonicalization -/

def permuteVars (C : AndCountCircuit 9) (π : Equiv.Perm V) : AndCountCircuit 9 where
  size := C.size
  leftVars i := (C.leftVars i).map π.toEmbedding
  leftGates := C.leftGates
  rightVars i := (C.rightVars i).map π.toEmbedding
  rightGates := C.rightGates
  outVars := C.outVars.map π.toEmbedding
  outGates := C.outGates

lemma permuteVars_wf (C : AndCountCircuit 9) (π : Equiv.Perm V) (hW : C.WellFormed) :
    (permuteVars C π).WellFormed := hW

lemma permuteVars_disjoint (C : AndCountCircuit 9) (π : Equiv.Perm V)
    (hD : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (i : Fin C.size) :
    Disjoint ((permuteVars C π).leftVars i) ((permuteVars C π).rightVars i) := by
  rw [Finset.disjoint_left]
  intro x hL hR
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hL
  obtain ⟨b, hb, hab⟩ := Finset.mem_map.mp hR
  have : b = a := π.injective hab
  subst this
  exact Finset.disjoint_left.mp (hD i) ha hb

lemma permuteVars_sideTrue {k : ℕ} (U B : Finset V) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (π : Equiv.Perm V) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue (U.map π.toEmbedding) (B.map π.toEmbedding) F i v1 = sideTrue U B F i v2 := by
  rw [Bool.eq_iff_iff, sideTrue_iff, sideTrue_iff]
  constructor
  · rintro (⟨x, hxB, hxU⟩ | ⟨j, hjF, hji, hjv⟩)
    · obtain ⟨a, haB, rfl⟩ := Finset.mem_map.mp hxB
      obtain ⟨b, hbU, hab⟩ := Finset.mem_map.mp hxU
      have : b = a := π.injective hab
      subst this
      exact Or.inl ⟨b, haB, hbU⟩
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (⟨x, hxB, hxU⟩ | ⟨j, hjF, hji, hjv⟩)
    · exact Or.inl ⟨π x, Finset.mem_map_of_mem _ hxB, Finset.mem_map_of_mem _ hxU⟩
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

lemma permuteVars_gateVal (C : AndCountCircuit 9) (π : Equiv.Perm V) (U : Finset V) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (permuteVars C π).gateVal (U.map π.toEmbedding) i = C.gateVal U i := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [gateVal_unfold (permuteVars C π) (U.map π.toEmbedding) i, gateVal_unfold C U i]
    have hlt : ∀ j : Fin C.size, j < i →
        (permuteVars C π).gateVal (U.map π.toEmbedding) j = C.gateVal U j :=
      fun j hji => ih j (by omega)
    exact congrArg₂ (· && ·)
      (permuteVars_sideTrue U (C.leftVars i) (C.leftGates i) i _ _ π hlt)
      (permuteVars_sideTrue U (C.rightVars i) (C.rightGates i) i _ _ π hlt)

lemma permuteVars_sideL (C : AndCountCircuit 9) (π : Equiv.Perm V) (U : Finset V) (i : Fin C.size) :
    sideL (permuteVars C π) (U.map π.toEmbedding) i = sideL C U i :=
  permuteVars_sideTrue U (C.leftVars i) (C.leftGates i) i _ _ π
    (fun j _ => permuteVars_gateVal C π U C.size j j.isLt)

lemma permuteVars_sideR (C : AndCountCircuit 9) (π : Equiv.Perm V) (U : Finset V) (i : Fin C.size) :
    sideR (permuteVars C π) (U.map π.toEmbedding) i = sideR C U i :=
  permuteVars_sideTrue U (C.rightVars i) (C.rightGates i) i _ _ π
    (fun j _ => permuteVars_gateVal C π U C.size j j.isLt)

lemma permuteVars_eval (C : AndCountCircuit 9) (π : Equiv.Perm V) (U : Finset V) :
    (permuteVars C π).eval (U.map π.toEmbedding) = C.eval U := by
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  have hgv : ∀ j : Fin C.size, (permuteVars C π).gateVal (U.map π.toEmbedding) j = C.gateVal U j :=
    fun j => permuteVars_gateVal C π U C.size j j.isLt
  constructor
  · rintro (⟨x, hxO, hxU⟩ | ⟨j, hjO, hjv⟩)
    · obtain ⟨a, haO, rfl⟩ := Finset.mem_map.mp hxO
      obtain ⟨b, hbU, hab⟩ := Finset.mem_map.mp hxU
      have : b = a := π.injective hab; subst this
      exact Or.inl ⟨b, haO, hbU⟩
    · exact Or.inr ⟨j, hjO, by rwa [← hgv j]⟩
  · rintro (⟨x, hxO, hxU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨π x, Finset.mem_map_of_mem _ hxO, Finset.mem_map_of_mem _ hxU⟩
    · exact Or.inr ⟨j, hjO, by rwa [hgv j]⟩

def autFn : Fin 4 → V → V
  | 0 => fun v => v
  | 1 => ![0, 2, 1, 5, 6, 3, 4, 7, 8]
  | 2 => ![0, 1, 2, 4, 3, 6, 5, 8, 7]
  | 3 => ![0, 2, 1, 6, 5, 4, 3, 8, 7]

lemma autFn_invol (p : Fin 4) (v : V) : autFn p (autFn p v) = v := by
  revert p v; decide +kernel

def autPerm (p : Fin 4) : Equiv.Perm V where
  toFun := autFn p
  invFun := autFn p
  left_inv := autFn_invol p
  right_inv := autFn_invol p

lemma autPerm_zero (p : Fin 4) : autPerm p 0 = 0 := by
  fin_cases p <;> decide

lemma autPerm_rows9 (p : Fin 4) (k : Fin 16) :
    ∃ k' : Fin 16, (rows9 k').map (autPerm p).toEmbedding = rows9 k := by
  revert p k; decide +kernel

lemma permuteVars_separates (C : AndCountCircuit 9) (p : Fin 4) (hsep : Separates C) :
    Separates (permuteVars C (autPerm p)) := by
  intro k
  obtain ⟨k', hk'⟩ := autPerm_rows9 p k
  constructor
  · rw [← hk', permuteVars_eval]; exact (hsep k').1
  · intro w hw
    have hw' : autPerm p w ∉ rows9 k' := by
      intro hm
      apply hw
      rw [← hk']
      have : autPerm p (autPerm p w) = w := autFn_invol p w
      rw [← this]
      exact Finset.mem_map_of_mem _ hm
    have hins : insert w (rows9 k) = (insert (autPerm p w) (rows9 k')).map (autPerm p).toEmbedding := by
      rw [Finset.map_insert, hk']
      simp [autPerm, autFn_invol p w]
    rw [hins, permuteVars_eval]
    exact (hsep k').2 (autPerm p w) hw'

/-- Apply `σ₁` (`autPerm 1`) if needed so that `1 ∉ rightVars a0 → 2 ∉ rightVars a0`,
    preserving all `a0` structural invariants. -/
lemma exists_a0_with_sigma1 (D : AndCountCircuit 9) (hW : D.WellFormed) (hsz : D.size = 5)
    (hD : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) (hsep : Separates D) :
    ∃ a0 : Fin 5, ∃ D' : AndCountCircuit 9, ∃ hsz' : D'.size = 5,
      D'.WellFormed ∧ (∀ i, Disjoint (D'.leftVars i) (D'.rightVars i)) ∧
      Separates D' ∧
      D'.leftVars ⟨a0.val, by omega⟩ = {0} ∧
      (0 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩ ∧
      (∀ i : Fin 5, i ≠ a0 → (0 : V) ∉ D'.leftVars ⟨i.val, by omega⟩ ∧ (0 : V) ∉ D'.rightVars ⟨i.val, by omega⟩) ∧
      (∀ k : Fin 16, (0 : V) ∉ rows9 k →
        sideL D' (rows9 k) ⟨a0.val, by omega⟩ = false ∧
        sideR D' (rows9 k) ⟨a0.val, by omega⟩ = true) ∧
      ((1 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩ → (2 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩) := by
  obtain ⟨a0, D1, hsz1, hW1, hD1, hsep1, hLa0, h0R, h0oth, hno0⟩ := exists_unique_a0 D hW hsz hD hsep
  by_cases h12 : (1 : V) ∉ D1.rightVars ⟨a0.val, by omega⟩ ∧ (2 : V) ∈ D1.rightVars ⟨a0.val, by omega⟩
  · let D2 := permuteVars D1 (autPerm 1)
    refine ⟨a0, D2, hsz1, permuteVars_wf D1 _ hW1, permuteVars_disjoint D1 _ hD1,
      permuteVars_separates D1 1 hsep1, ?_, ?_, ?_, ?_, ?_⟩
    · change (D1.leftVars ⟨a0.val, by omega⟩).map (autPerm 1).toEmbedding = {0}
      rw [hLa0, Finset.map_singleton]; simp [autPerm, autFn]
    · intro hm
      obtain ⟨x, hx, hx0⟩ := Finset.mem_map.mp hm
      have : x = 0 := (autPerm 1).injective (hx0.trans (autPerm_zero 1).symm)
      subst this; exact h0R hx
    · intro i hi
      constructor
      · intro hm
        obtain ⟨x, hx, hx0⟩ := Finset.mem_map.mp hm
        have : x = 0 := (autPerm 1).injective (hx0.trans (autPerm_zero 1).symm)
        subst this; exact (h0oth i hi).1 hx
      · intro hm
        obtain ⟨x, hx, hx0⟩ := Finset.mem_map.mp hm
        have : x = 0 := (autPerm 1).injective (hx0.trans (autPerm_zero 1).symm)
        subst this; exact (h0oth i hi).2 hx
    · intro k hk
      obtain ⟨k', hk'⟩ := autPerm_rows9 1 k
      have hk0' : (0 : V) ∉ rows9 k' := by
        intro h0m; apply hk; rw [← hk']
        rw [← autPerm_zero 1]; exact Finset.mem_map_of_mem _ h0m
      have hL := permuteVars_sideL D1 (autPerm 1) (rows9 k') ⟨a0.val, by omega⟩
      have hR := permuteVars_sideR D1 (autPerm 1) (rows9 k') ⟨a0.val, by omega⟩
      rw [← hk']
      exact ⟨hL.trans (hno0 k' hk0').1, hR.trans (hno0 k' hk0').2⟩
    · intro h1not
      exfalso; apply h1not
      change (1 : V) ∈ (D1.rightVars ⟨a0.val, by omega⟩).map (autPerm 1).toEmbedding
      exact Finset.mem_map.mpr ⟨2, h12.2, by decide⟩
  · refine ⟨a0, D1, hsz1, hW1, hD1, hsep1, hLa0, h0R, h0oth, hno0, ?_⟩
    intro h1not h2in; exact h12 ⟨h1not, h2in⟩



/-! ## Section 4B: Phase 1 (`mis_cover` unit-propagation enumeration) and soundness -/

structure B10 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  b8 : Bool
  b9 : Bool
  deriving DecidableEq

def B10.get (x : B10) : Nat → Bool
  | 0 => x.b0 | 1 => x.b1 | 2 => x.b2 | 3 => x.b3 | 4 => x.b4
  | 5 => x.b5 | 6 => x.b6 | 7 => x.b7 | 8 => x.b8 | _ => x.b9

def B10.set (x : B10) : Nat → B10
  | 0 => {x with b0 := true} | 1 => {x with b1 := true}
  | 2 => {x with b2 := true} | 3 => {x with b3 := true}
  | 4 => {x with b4 := true} | 5 => {x with b5 := true}
  | 6 => {x with b6 := true} | 7 => {x with b7 := true}
  | 8 => {x with b8 := true} | _ => {x with b9 := true}

lemma B10.get_set_same (x : B10) (l : Fin 10) : (x.set l.val).get l.val = true := by
  fin_cases l <;> rfl

lemma B10.get_set_ne (x : B10) (l1 l2 : Fin 10) (hne : l1 ≠ l2) :
    (x.set l1.val).get l2.val = x.get l2.val := by
  fin_cases l1 <;> fin_cases l2 <;> simp_all [B10.set, B10.get]

structure F16 where
  f0 : B10
  f1 : B10
  f2 : B10
  f3 : B10
  f4 : B10
  f5 : B10
  f6 : B10
  f7 : B10
  f8 : B10
  f9 : B10
  f10 : B10
  f11 : B10
  f12 : B10
  f13 : B10
  f14 : B10
  f15 : B10

def F16.get (st : F16) (k : Fin 16) : B10 :=
  match k.val with
  | 0 => st.f0 | 1 => st.f1 | 2 => st.f2 | 3 => st.f3
  | 4 => st.f4 | 5 => st.f5 | 6 => st.f6 | 7 => st.f7
  | 8 => st.f8 | 9 => st.f9 | 10 => st.f10 | 11 => st.f11
  | 12 => st.f12 | 13 => st.f13 | 14 => st.f14 | _ => st.f15

structure Opt where
  id : Nat
  l1 : Nat
  l2 : Nat
  o1 : Nat
  o2 : Nat
  deriving DecidableEq

def subOpt (a b : Opt) : Bool :=
  (a.l1 == b.l1 || a.l1 == b.l2) && (a.l2 == b.l1 || a.l2 == b.l2)

def antiOk (w : Opt) : List Opt → Bool
  | [] => true
  | u :: us => !(subOpt w u) && !(subOpt u w) && antiOk w us

def upPass1 (f : B10) (chg : Bool) : List Opt → Option (B10 × Bool)
  | [] => some (f, chg)
  | w :: ws =>
    let f1 := f.get w.l1
    let f2 := f.get w.l2
    if f1 && f2 then none
    else if f1 then
      if f.get w.o2 then upPass1 f chg ws else upPass1 (f.set w.o2) true ws
    else if f2 then
      if f.get w.o1 then upPass1 f chg ws else upPass1 (f.set w.o1) true ws
    else if w.l1 == w.l2 then
      if f.get w.o1 then upPass1 f chg ws else upPass1 (f.set w.o1) true ws
    else upPass1 f chg ws

def upProp (f : B10) (outs : List Opt) : Option B10 :=
  match upPass1 f false outs with
  | none => none
  | some (f1, false) => some f1
  | some (f1, true) =>
    match upPass1 f1 false outs with
    | none => none
    | some (f2, _) => some f2

def stepIn (fk : B10) (wv : Opt) (outs : List Opt) : Option B10 :=
  let c1 := !(fk.get wv.l1)
  let c2 := !(fk.get wv.l2)
  if !c1 && !c2 then some fk
  else
    let fk1 := if c1 then fk.set wv.l1 else fk
    let fk2 := if c2 then fk1.set wv.l2 else fk1
    upProp fk2 outs

def stepOut (fk : B10) (wv : Opt) (outs : List Opt) : Option B10 :=
  let f1 := fk.get wv.l1
  let f2 := fk.get wv.l2
  if f1 && f2 then none
  else if f1 then
    if fk.get wv.o2 then some fk else upProp (fk.set wv.o2) outs
  else if f2 then
    if fk.get wv.o1 then some fk else upProp (fk.set wv.o1) outs
  else if wv.l1 == wv.l2 then
    if fk.get wv.o1 then some fk else upProp (fk.set wv.o1) outs
  else some fk

def forb0In  : B10 := ⟨true,false,false,false,false,false,false,false,false,false⟩
def forb0Out : B10 := ⟨false,true,false,false,false,false,false,false,false,false⟩

def initF16 : F16 := ⟨forb0In, forb0Out, forb0In, forb0In, forb0In, forb0Out, forb0Out, forb0In, forb0Out, forb0In, forb0Out, forb0Out, forb0In, forb0Out, forb0In, forb0Out⟩
def stepF16_1 (st : F16) (w1 : Opt) : Option F16 :=
  if (st.f0.get w1.l1 && st.f0.get w1.l2) || (st.f1.get w1.l1 && st.f1.get w1.l2) || (st.f2.get w1.l1 && st.f2.get w1.l2) || (st.f3.get w1.l1 && st.f3.get w1.l2) || (st.f4.get w1.l1 && st.f4.get w1.l2) || (st.f7.get w1.l1 && st.f7.get w1.l2) || (st.f8.get w1.l1 && st.f8.get w1.l2) || (st.f9.get w1.l1 && st.f9.get w1.l2) || (st.f12.get w1.l1 && st.f12.get w1.l2) || (st.f13.get w1.l1 && st.f13.get w1.l2) || (st.f14.get w1.l1 && st.f14.get w1.l2) then none else
  match stepIn st.f5 w1 [] with
  | none => none
  | some nf5 =>
  match stepIn st.f6 w1 [] with
  | none => none
  | some nf6 =>
  match stepIn st.f10 w1 [] with
  | none => none
  | some nf10 =>
  match stepIn st.f11 w1 [] with
  | none => none
  | some nf11 =>
  match stepIn st.f15 w1 [] with
  | none => none
  | some nf15 =>
  match stepOut st.f0 w1 [w1] with
  | none => none
  | some nf0 =>
  match stepOut st.f1 w1 [w1] with
  | none => none
  | some nf1 =>
  match stepOut st.f2 w1 [w1] with
  | none => none
  | some nf2 =>
  match stepOut st.f3 w1 [w1] with
  | none => none
  | some nf3 =>
  match stepOut st.f4 w1 [w1] with
  | none => none
  | some nf4 =>
  match stepOut st.f7 w1 [w1] with
  | none => none
  | some nf7 =>
  match stepOut st.f8 w1 [w1] with
  | none => none
  | some nf8 =>
  match stepOut st.f9 w1 [w1] with
  | none => none
  | some nf9 =>
  match stepOut st.f12 w1 [w1] with
  | none => none
  | some nf12 =>
  match stepOut st.f13 w1 [w1] with
  | none => none
  | some nf13 =>
  match stepOut st.f14 w1 [w1] with
  | none => none
  | some nf14 =>
  some ⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩
def stepF16_2 (st : F16) (w1 w2 : Opt) : Option F16 :=
  if (st.f0.get w2.l1 && st.f0.get w2.l2) || (st.f2.get w2.l1 && st.f2.get w2.l2) || (st.f3.get w2.l1 && st.f3.get w2.l2) || (st.f4.get w2.l1 && st.f4.get w2.l2) || (st.f5.get w2.l1 && st.f5.get w2.l2) || (st.f7.get w2.l1 && st.f7.get w2.l2) || (st.f9.get w2.l1 && st.f9.get w2.l2) || (st.f10.get w2.l1 && st.f10.get w2.l2) || (st.f12.get w2.l1 && st.f12.get w2.l2) || (st.f14.get w2.l1 && st.f14.get w2.l2) || (st.f15.get w2.l1 && st.f15.get w2.l2) then none else
  match stepIn st.f1 w2 [w1] with
  | none => none
  | some nf1 =>
  match stepIn st.f6 w2 [] with
  | none => none
  | some nf6 =>
  match stepIn st.f8 w2 [w1] with
  | none => none
  | some nf8 =>
  match stepIn st.f11 w2 [] with
  | none => none
  | some nf11 =>
  match stepIn st.f13 w2 [w1] with
  | none => none
  | some nf13 =>
  match stepOut st.f0 w2 [w2, w1] with
  | none => none
  | some nf0 =>
  match stepOut st.f2 w2 [w2, w1] with
  | none => none
  | some nf2 =>
  match stepOut st.f3 w2 [w2, w1] with
  | none => none
  | some nf3 =>
  match stepOut st.f4 w2 [w2, w1] with
  | none => none
  | some nf4 =>
  match stepOut st.f5 w2 [w2] with
  | none => none
  | some nf5 =>
  match stepOut st.f7 w2 [w2, w1] with
  | none => none
  | some nf7 =>
  match stepOut st.f9 w2 [w2, w1] with
  | none => none
  | some nf9 =>
  match stepOut st.f10 w2 [w2] with
  | none => none
  | some nf10 =>
  match stepOut st.f12 w2 [w2, w1] with
  | none => none
  | some nf12 =>
  match stepOut st.f14 w2 [w2, w1] with
  | none => none
  | some nf14 =>
  match stepOut st.f15 w2 [w2] with
  | none => none
  | some nf15 =>
  some ⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩
def stepF16_3 (st : F16) (w1 w2 w3 : Opt) : Option F16 :=
  if (st.f2.get w3.l1 && st.f2.get w3.l2) || (st.f4.get w3.l1 && st.f4.get w3.l2) || (st.f5.get w3.l1 && st.f5.get w3.l2) || (st.f6.get w3.l1 && st.f6.get w3.l2) || (st.f7.get w3.l1 && st.f7.get w3.l2) || (st.f8.get w3.l1 && st.f8.get w3.l2) || (st.f9.get w3.l1 && st.f9.get w3.l2) || (st.f10.get w3.l1 && st.f10.get w3.l2) || (st.f11.get w3.l1 && st.f11.get w3.l2) || (st.f14.get w3.l1 && st.f14.get w3.l2) || (st.f15.get w3.l1 && st.f15.get w3.l2) then none else
  match stepIn st.f0 w3 [w2, w1] with
  | none => none
  | some nf0 =>
  match stepIn st.f1 w3 [w1] with
  | none => none
  | some nf1 =>
  match stepIn st.f3 w3 [w2, w1] with
  | none => none
  | some nf3 =>
  match stepIn st.f12 w3 [w2, w1] with
  | none => none
  | some nf12 =>
  match stepIn st.f13 w3 [w1] with
  | none => none
  | some nf13 =>
  match stepOut st.f2 w3 [w3, w2, w1] with
  | none => none
  | some nf2 =>
  match stepOut st.f4 w3 [w3, w2, w1] with
  | none => none
  | some nf4 =>
  match stepOut st.f5 w3 [w3, w2] with
  | none => none
  | some nf5 =>
  match stepOut st.f6 w3 [w3] with
  | none => none
  | some nf6 =>
  match stepOut st.f7 w3 [w3, w2, w1] with
  | none => none
  | some nf7 =>
  match stepOut st.f8 w3 [w3, w1] with
  | none => none
  | some nf8 =>
  match stepOut st.f9 w3 [w3, w2, w1] with
  | none => none
  | some nf9 =>
  match stepOut st.f10 w3 [w3, w2] with
  | none => none
  | some nf10 =>
  match stepOut st.f11 w3 [w3] with
  | none => none
  | some nf11 =>
  match stepOut st.f14 w3 [w3, w2, w1] with
  | none => none
  | some nf14 =>
  match stepOut st.f15 w3 [w3, w2] with
  | none => none
  | some nf15 =>
  some ⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩
def stepF16_4 (st : F16) (w1 w2 w3 w4 : Opt) : Option F16 :=
  if (st.f3.get w4.l1 && st.f3.get w4.l2) || (st.f4.get w4.l1 && st.f4.get w4.l2) || (st.f5.get w4.l1 && st.f5.get w4.l2) || (st.f6.get w4.l1 && st.f6.get w4.l2) || (st.f9.get w4.l1 && st.f9.get w4.l2) || (st.f10.get w4.l1 && st.f10.get w4.l2) || (st.f11.get w4.l1 && st.f11.get w4.l2) || (st.f12.get w4.l1 && st.f12.get w4.l2) || (st.f13.get w4.l1 && st.f13.get w4.l2) || (st.f14.get w4.l1 && st.f14.get w4.l2) || (st.f15.get w4.l1 && st.f15.get w4.l2) then none else
  match stepIn st.f0 w4 [w2, w1] with
  | none => none
  | some nf0 =>
  match stepIn st.f1 w4 [w1] with
  | none => none
  | some nf1 =>
  match stepIn st.f2 w4 [w3, w2, w1] with
  | none => none
  | some nf2 =>
  match stepIn st.f7 w4 [w3, w2, w1] with
  | none => none
  | some nf7 =>
  match stepIn st.f8 w4 [w3, w1] with
  | none => none
  | some nf8 =>
  match stepOut st.f3 w4 [w4, w2, w1] with
  | none => none
  | some nf3 =>
  match stepOut st.f4 w4 [w4, w3, w2, w1] with
  | none => none
  | some nf4 =>
  match stepOut st.f5 w4 [w4, w3, w2] with
  | none => none
  | some nf5 =>
  match stepOut st.f6 w4 [w4, w3] with
  | none => none
  | some nf6 =>
  match stepOut st.f9 w4 [w4, w3, w2, w1] with
  | none => none
  | some nf9 =>
  match stepOut st.f10 w4 [w4, w3, w2] with
  | none => none
  | some nf10 =>
  match stepOut st.f11 w4 [w4, w3] with
  | none => none
  | some nf11 =>
  match stepOut st.f12 w4 [w4, w2, w1] with
  | none => none
  | some nf12 =>
  match stepOut st.f13 w4 [w4, w1] with
  | none => none
  | some nf13 =>
  match stepOut st.f14 w4 [w4, w3, w2, w1] with
  | none => none
  | some nf14 =>
  match stepOut st.f15 w4 [w4, w3, w2] with
  | none => none
  | some nf15 =>
  some ⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩
def stepF16_5 (st : F16) (w1 w2 w3 w4 w5 : Opt) : Option F16 :=
  if (st.f0.get w5.l1 && st.f0.get w5.l2) || (st.f1.get w5.l1 && st.f1.get w5.l2) || (st.f3.get w5.l1 && st.f3.get w5.l2) || (st.f6.get w5.l1 && st.f6.get w5.l2) || (st.f7.get w5.l1 && st.f7.get w5.l2) || (st.f8.get w5.l1 && st.f8.get w5.l2) || (st.f9.get w5.l1 && st.f9.get w5.l2) || (st.f10.get w5.l1 && st.f10.get w5.l2) || (st.f11.get w5.l1 && st.f11.get w5.l2) || (st.f12.get w5.l1 && st.f12.get w5.l2) || (st.f13.get w5.l1 && st.f13.get w5.l2) then none else
  match stepIn st.f2 w5 [w3, w2, w1] with
  | none => none
  | some nf2 =>
  match stepIn st.f4 w5 [w4, w3, w2, w1] with
  | none => none
  | some nf4 =>
  match stepIn st.f5 w5 [w4, w3, w2] with
  | none => none
  | some nf5 =>
  match stepIn st.f14 w5 [w4, w3, w2, w1] with
  | none => none
  | some nf14 =>
  match stepIn st.f15 w5 [w4, w3, w2] with
  | none => none
  | some nf15 =>
  match stepOut st.f0 w5 [w5, w2, w1] with
  | none => none
  | some nf0 =>
  match stepOut st.f1 w5 [w5, w1] with
  | none => none
  | some nf1 =>
  match stepOut st.f3 w5 [w5, w4, w2, w1] with
  | none => none
  | some nf3 =>
  match stepOut st.f6 w5 [w5, w4, w3] with
  | none => none
  | some nf6 =>
  match stepOut st.f7 w5 [w5, w3, w2, w1] with
  | none => none
  | some nf7 =>
  match stepOut st.f8 w5 [w5, w3, w1] with
  | none => none
  | some nf8 =>
  match stepOut st.f9 w5 [w5, w4, w3, w2, w1] with
  | none => none
  | some nf9 =>
  match stepOut st.f10 w5 [w5, w4, w3, w2] with
  | none => none
  | some nf10 =>
  match stepOut st.f11 w5 [w5, w4, w3] with
  | none => none
  | some nf11 =>
  match stepOut st.f12 w5 [w5, w4, w2, w1] with
  | none => none
  | some nf12 =>
  match stepOut st.f13 w5 [w5, w4, w1] with
  | none => none
  | some nf13 =>
  some ⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩
def stepF16_6 (st : F16) (w1 w2 w3 w4 w5 w6 : Opt) : Option F16 :=
  if (st.f0.get w6.l1 && st.f0.get w6.l2) || (st.f1.get w6.l1 && st.f1.get w6.l2) || (st.f2.get w6.l1 && st.f2.get w6.l2) || (st.f6.get w6.l1 && st.f6.get w6.l2) || (st.f7.get w6.l1 && st.f7.get w6.l2) || (st.f8.get w6.l1 && st.f8.get w6.l2) || (st.f11.get w6.l1 && st.f11.get w6.l2) || (st.f12.get w6.l1 && st.f12.get w6.l2) || (st.f13.get w6.l1 && st.f13.get w6.l2) || (st.f14.get w6.l1 && st.f14.get w6.l2) || (st.f15.get w6.l1 && st.f15.get w6.l2) then none else
  match stepIn st.f3 w6 [w5, w4, w2, w1] with
  | none => none
  | some nf3 =>
  match stepIn st.f4 w6 [w4, w3, w2, w1] with
  | none => none
  | some nf4 =>
  match stepIn st.f5 w6 [w4, w3, w2] with
  | none => none
  | some nf5 =>
  match stepIn st.f9 w6 [w5, w4, w3, w2, w1] with
  | none => none
  | some nf9 =>
  match stepIn st.f10 w6 [w5, w4, w3, w2] with
  | none => none
  | some nf10 =>
  match stepOut st.f0 w6 [w6, w5, w2, w1] with
  | none => none
  | some nf0 =>
  match stepOut st.f1 w6 [w6, w5, w1] with
  | none => none
  | some nf1 =>
  match stepOut st.f2 w6 [w6, w3, w2, w1] with
  | none => none
  | some nf2 =>
  match stepOut st.f6 w6 [w6, w5, w4, w3] with
  | none => none
  | some nf6 =>
  match stepOut st.f7 w6 [w6, w5, w3, w2, w1] with
  | none => none
  | some nf7 =>
  match stepOut st.f8 w6 [w6, w5, w3, w1] with
  | none => none
  | some nf8 =>
  match stepOut st.f11 w6 [w6, w5, w4, w3] with
  | none => none
  | some nf11 =>
  match stepOut st.f12 w6 [w6, w5, w4, w2, w1] with
  | none => none
  | some nf12 =>
  match stepOut st.f13 w6 [w6, w5, w4, w1] with
  | none => none
  | some nf13 =>
  match stepOut st.f14 w6 [w6, w4, w3, w2, w1] with
  | none => none
  | some nf14 =>
  match stepOut st.f15 w6 [w6, w4, w3, w2] with
  | none => none
  | some nf15 =>
  some ⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩
def stepF16_7 (st : F16) (w1 w2 w3 w4 w5 w6 w7 : Opt) : Option F16 :=
  if (st.f0.get w7.l1 && st.f0.get w7.l2) || (st.f1.get w7.l1 && st.f1.get w7.l2) || (st.f2.get w7.l1 && st.f2.get w7.l2) || (st.f3.get w7.l1 && st.f3.get w7.l2) || (st.f4.get w7.l1 && st.f4.get w7.l2) || (st.f5.get w7.l1 && st.f5.get w7.l2) || (st.f11.get w7.l1 && st.f11.get w7.l2) || (st.f12.get w7.l1 && st.f12.get w7.l2) || (st.f13.get w7.l1 && st.f13.get w7.l2) || (st.f14.get w7.l1 && st.f14.get w7.l2) || (st.f15.get w7.l1 && st.f15.get w7.l2) then none else
  match stepIn st.f6 w7 [w6, w5, w4, w3] with
  | none => none
  | some nf6 =>
  match stepIn st.f7 w7 [w6, w5, w3, w2, w1] with
  | none => none
  | some nf7 =>
  match stepIn st.f8 w7 [w6, w5, w3, w1] with
  | none => none
  | some nf8 =>
  match stepIn st.f9 w7 [w5, w4, w3, w2, w1] with
  | none => none
  | some nf9 =>
  match stepIn st.f10 w7 [w5, w4, w3, w2] with
  | none => none
  | some nf10 =>
  match stepOut st.f0 w7 [w7, w6, w5, w2, w1] with
  | none => none
  | some nf0 =>
  match stepOut st.f1 w7 [w7, w6, w5, w1] with
  | none => none
  | some nf1 =>
  match stepOut st.f2 w7 [w7, w6, w3, w2, w1] with
  | none => none
  | some nf2 =>
  match stepOut st.f3 w7 [w7, w5, w4, w2, w1] with
  | none => none
  | some nf3 =>
  match stepOut st.f4 w7 [w7, w4, w3, w2, w1] with
  | none => none
  | some nf4 =>
  match stepOut st.f5 w7 [w7, w4, w3, w2] with
  | none => none
  | some nf5 =>
  match stepOut st.f11 w7 [w7, w6, w5, w4, w3] with
  | none => none
  | some nf11 =>
  match stepOut st.f12 w7 [w7, w6, w5, w4, w2, w1] with
  | none => none
  | some nf12 =>
  match stepOut st.f13 w7 [w7, w6, w5, w4, w1] with
  | none => none
  | some nf13 =>
  match stepOut st.f14 w7 [w7, w6, w4, w3, w2, w1] with
  | none => none
  | some nf14 =>
  match stepOut st.f15 w7 [w7, w6, w4, w3, w2] with
  | none => none
  | some nf15 =>
  some ⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩
def stepF16_8 (st : F16) (w1 w2 w3 w4 w5 w6 w7 w8 : Opt) : Option F16 :=
  if (st.f0.get w8.l1 && st.f0.get w8.l2) || (st.f1.get w8.l1 && st.f1.get w8.l2) || (st.f2.get w8.l1 && st.f2.get w8.l2) || (st.f3.get w8.l1 && st.f3.get w8.l2) || (st.f4.get w8.l1 && st.f4.get w8.l2) || (st.f5.get w8.l1 && st.f5.get w8.l2) || (st.f6.get w8.l1 && st.f6.get w8.l2) || (st.f7.get w8.l1 && st.f7.get w8.l2) || (st.f8.get w8.l1 && st.f8.get w8.l2) || (st.f9.get w8.l1 && st.f9.get w8.l2) || (st.f10.get w8.l1 && st.f10.get w8.l2) then none else
  match stepIn st.f11 w8 [w7, w6, w5, w4, w3] with
  | none => none
  | some nf11 =>
  match stepIn st.f12 w8 [w7, w6, w5, w4, w2, w1] with
  | none => none
  | some nf12 =>
  match stepIn st.f13 w8 [w7, w6, w5, w4, w1] with
  | none => none
  | some nf13 =>
  match stepIn st.f14 w8 [w7, w6, w4, w3, w2, w1] with
  | none => none
  | some nf14 =>
  match stepIn st.f15 w8 [w7, w6, w4, w3, w2] with
  | none => none
  | some nf15 =>
  match stepOut st.f0 w8 [w8, w7, w6, w5, w2, w1] with
  | none => none
  | some nf0 =>
  match stepOut st.f1 w8 [w8, w7, w6, w5, w1] with
  | none => none
  | some nf1 =>
  match stepOut st.f2 w8 [w8, w7, w6, w3, w2, w1] with
  | none => none
  | some nf2 =>
  match stepOut st.f3 w8 [w8, w7, w5, w4, w2, w1] with
  | none => none
  | some nf3 =>
  match stepOut st.f4 w8 [w8, w7, w4, w3, w2, w1] with
  | none => none
  | some nf4 =>
  match stepOut st.f5 w8 [w8, w7, w4, w3, w2] with
  | none => none
  | some nf5 =>
  match stepOut st.f6 w8 [w8, w6, w5, w4, w3] with
  | none => none
  | some nf6 =>
  match stepOut st.f7 w8 [w8, w6, w5, w3, w2, w1] with
  | none => none
  | some nf7 =>
  match stepOut st.f8 w8 [w8, w6, w5, w3, w1] with
  | none => none
  | some nf8 =>
  match stepOut st.f9 w8 [w8, w5, w4, w3, w2, w1] with
  | none => none
  | some nf9 =>
  match stepOut st.f10 w8 [w8, w5, w4, w3, w2] with
  | none => none
  | some nf10 =>
  some ⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩
def fOutB10 : List B10 := [⟨true,false,false,false,false,false,false,false,false,false⟩, ⟨true,false,false,false,false,false,false,false,true,false⟩, ⟨true,false,false,false,false,false,false,false,false,true⟩, ⟨true,false,false,false,false,false,true,false,false,false⟩, ⟨true,false,false,false,false,false,true,false,true,false⟩, ⟨true,false,false,false,false,false,true,false,false,true⟩, ⟨true,false,false,false,false,false,false,true,false,false⟩, ⟨true,false,false,false,false,false,false,true,true,false⟩, ⟨true,false,false,false,false,false,false,true,false,true⟩, ⟨true,false,false,false,true,false,false,false,false,false⟩, ⟨true,false,false,false,true,false,false,false,true,false⟩, ⟨true,false,false,false,true,false,false,false,false,true⟩, ⟨true,false,false,false,true,false,true,false,false,false⟩, ⟨true,false,false,false,true,false,true,false,true,false⟩, ⟨true,false,false,false,true,false,true,false,false,true⟩, ⟨true,false,false,false,true,false,false,true,false,false⟩, ⟨true,false,false,false,true,false,false,true,true,false⟩, ⟨true,false,false,false,true,false,false,true,false,true⟩, ⟨true,false,false,false,false,true,false,false,false,false⟩, ⟨true,false,false,false,false,true,false,false,true,false⟩, ⟨true,false,false,false,false,true,false,false,false,true⟩, ⟨true,false,false,false,false,true,true,false,false,false⟩, ⟨true,false,false,false,false,true,true,false,true,false⟩, ⟨true,false,false,false,false,true,true,false,false,true⟩, ⟨true,false,false,false,false,true,false,true,false,false⟩, ⟨true,false,false,false,false,true,false,true,true,false⟩, ⟨true,false,false,false,false,true,false,true,false,true⟩, ⟨true,false,true,false,false,false,false,false,false,false⟩, ⟨true,false,true,false,false,false,false,false,true,false⟩, ⟨true,false,true,false,false,false,false,false,false,true⟩, ⟨true,false,true,false,false,false,true,false,false,false⟩, ⟨true,false,true,false,false,false,true,false,true,false⟩, ⟨true,false,true,false,false,false,true,false,false,true⟩, ⟨true,false,true,false,false,false,false,true,false,false⟩, ⟨true,false,true,false,false,false,false,true,true,false⟩, ⟨true,false,true,false,false,false,false,true,false,true⟩, ⟨true,false,true,false,true,false,false,false,false,false⟩, ⟨true,false,true,false,true,false,false,false,true,false⟩, ⟨true,false,true,false,true,false,false,false,false,true⟩, ⟨true,false,true,false,true,false,true,false,false,false⟩, ⟨true,false,true,false,true,false,true,false,true,false⟩, ⟨true,false,true,false,true,false,true,false,false,true⟩, ⟨true,false,true,false,true,false,false,true,false,false⟩, ⟨true,false,true,false,true,false,false,true,true,false⟩, ⟨true,false,true,false,true,false,false,true,false,true⟩, ⟨true,false,true,false,false,true,false,false,false,false⟩, ⟨true,false,true,false,false,true,false,false,true,false⟩, ⟨true,false,true,false,false,true,false,false,false,true⟩, ⟨true,false,true,false,false,true,true,false,false,false⟩, ⟨true,false,true,false,false,true,true,false,true,false⟩, ⟨true,false,true,false,false,true,true,false,false,true⟩, ⟨true,false,true,false,false,true,false,true,false,false⟩, ⟨true,false,true,false,false,true,false,true,true,false⟩, ⟨true,false,true,false,false,true,false,true,false,true⟩, ⟨true,false,false,true,false,false,false,false,false,false⟩, ⟨true,false,false,true,false,false,false,false,true,false⟩, ⟨true,false,false,true,false,false,false,false,false,true⟩, ⟨true,false,false,true,false,false,true,false,false,false⟩, ⟨true,false,false,true,false,false,true,false,true,false⟩, ⟨true,false,false,true,false,false,true,false,false,true⟩, ⟨true,false,false,true,false,false,false,true,false,false⟩, ⟨true,false,false,true,false,false,false,true,true,false⟩, ⟨true,false,false,true,false,false,false,true,false,true⟩, ⟨true,false,false,true,true,false,false,false,false,false⟩, ⟨true,false,false,true,true,false,false,false,true,false⟩, ⟨true,false,false,true,true,false,false,false,false,true⟩, ⟨true,false,false,true,true,false,true,false,false,false⟩, ⟨true,false,false,true,true,false,true,false,true,false⟩, ⟨true,false,false,true,true,false,true,false,false,true⟩, ⟨true,false,false,true,true,false,false,true,false,false⟩, ⟨true,false,false,true,true,false,false,true,true,false⟩, ⟨true,false,false,true,true,false,false,true,false,true⟩, ⟨true,false,false,true,false,true,false,false,false,false⟩, ⟨true,false,false,true,false,true,false,false,true,false⟩, ⟨true,false,false,true,false,true,false,false,false,true⟩, ⟨true,false,false,true,false,true,true,false,false,false⟩, ⟨true,false,false,true,false,true,true,false,true,false⟩, ⟨true,false,false,true,false,true,true,false,false,true⟩, ⟨true,false,false,true,false,true,false,true,false,false⟩, ⟨true,false,false,true,false,true,false,true,true,false⟩, ⟨true,false,false,true,false,true,false,true,false,true⟩]
def fInB10 : List B10 := [⟨false,false,false,false,false,false,false,false,false,false⟩, ⟨false,true,false,false,false,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,true,false⟩, ⟨false,true,false,false,false,false,false,false,true,false⟩, ⟨false,false,false,false,false,false,false,false,false,true⟩, ⟨false,true,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,false,false,false⟩, ⟨false,true,false,false,false,false,true,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,false,true,false,false,true⟩, ⟨false,true,false,false,false,false,true,false,false,true⟩, ⟨false,false,false,false,false,false,false,true,false,false⟩, ⟨false,true,false,false,false,false,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,true,true,false⟩, ⟨false,true,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,true,false,true⟩, ⟨false,true,false,false,false,false,false,true,false,true⟩, ⟨false,false,false,false,true,false,false,false,false,false⟩, ⟨false,true,false,false,true,false,false,false,false,false⟩, ⟨false,false,false,false,true,false,false,false,true,false⟩, ⟨false,true,false,false,true,false,false,false,true,false⟩, ⟨false,false,false,false,true,false,false,false,false,true⟩, ⟨false,true,false,false,true,false,false,false,false,true⟩, ⟨false,false,false,false,true,false,true,false,false,false⟩, ⟨false,true,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,true,false,true,false,true,false⟩, ⟨false,true,false,false,true,false,true,false,true,false⟩, ⟨false,false,false,false,true,false,true,false,false,true⟩, ⟨false,true,false,false,true,false,true,false,false,true⟩, ⟨false,false,false,false,true,false,false,true,false,false⟩, ⟨false,true,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,true,false,false,true,true,false⟩, ⟨false,true,false,false,true,false,false,true,true,false⟩, ⟨false,false,false,false,true,false,false,true,false,true⟩, ⟨false,true,false,false,true,false,false,true,false,true⟩, ⟨false,false,false,false,false,true,false,false,false,false⟩, ⟨false,true,false,false,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,true,false,false,true,false⟩, ⟨false,true,false,false,false,true,false,false,true,false⟩, ⟨false,false,false,false,false,true,false,false,false,true⟩, ⟨false,true,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,true,true,false,false,false⟩, ⟨false,true,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,true,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false⟩, ⟨false,false,false,false,false,true,true,false,false,true⟩, ⟨false,true,false,false,false,true,true,false,false,true⟩, ⟨false,false,false,false,false,true,false,true,false,false⟩, ⟨false,true,false,false,false,true,false,true,false,false⟩, ⟨false,false,false,false,false,true,false,true,true,false⟩, ⟨false,true,false,false,false,true,false,true,true,false⟩, ⟨false,false,false,false,false,true,false,true,false,true⟩, ⟨false,true,false,false,false,true,false,true,false,true⟩, ⟨false,false,true,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false,false⟩, ⟨false,false,true,false,false,false,false,false,true,false⟩, ⟨false,true,true,false,false,false,false,false,true,false⟩, ⟨false,false,true,false,false,false,false,false,false,true⟩, ⟨false,true,true,false,false,false,false,false,false,true⟩, ⟨false,false,true,false,false,false,true,false,false,false⟩, ⟨false,true,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,false,false,false,true,false,true,false⟩, ⟨false,true,true,false,false,false,true,false,true,false⟩, ⟨false,false,true,false,false,false,true,false,false,true⟩, ⟨false,true,true,false,false,false,true,false,false,true⟩, ⟨false,false,true,false,false,false,false,true,false,false⟩, ⟨false,true,true,false,false,false,false,true,false,false⟩, ⟨false,false,true,false,false,false,false,true,true,false⟩, ⟨false,true,true,false,false,false,false,true,true,false⟩, ⟨false,false,true,false,false,false,false,true,false,true⟩, ⟨false,true,true,false,false,false,false,true,false,true⟩, ⟨false,false,true,false,true,false,false,false,false,false⟩, ⟨false,true,true,false,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,false,false,false,true,false⟩, ⟨false,true,true,false,true,false,false,false,true,false⟩, ⟨false,false,true,false,true,false,false,false,false,true⟩, ⟨false,true,true,false,true,false,false,false,false,true⟩, ⟨false,false,true,false,true,false,true,false,false,false⟩, ⟨false,true,true,false,true,false,true,false,false,false⟩, ⟨false,false,true,false,true,false,true,false,true,false⟩, ⟨false,true,true,false,true,false,true,false,true,false⟩, ⟨false,false,true,false,true,false,true,false,false,true⟩, ⟨false,true,true,false,true,false,true,false,false,true⟩, ⟨false,false,true,false,true,false,false,true,false,false⟩, ⟨false,true,true,false,true,false,false,true,false,false⟩, ⟨false,false,true,false,true,false,false,true,true,false⟩, ⟨false,true,true,false,true,false,false,true,true,false⟩, ⟨false,false,true,false,true,false,false,true,false,true⟩, ⟨false,true,true,false,true,false,false,true,false,true⟩, ⟨false,false,true,false,false,true,false,false,false,false⟩, ⟨false,true,true,false,false,true,false,false,false,false⟩, ⟨false,false,true,false,false,true,false,false,true,false⟩, ⟨false,true,true,false,false,true,false,false,true,false⟩, ⟨false,false,true,false,false,true,false,false,false,true⟩, ⟨false,true,true,false,false,true,false,false,false,true⟩, ⟨false,false,true,false,false,true,true,false,false,false⟩, ⟨false,true,true,false,false,true,true,false,false,false⟩, ⟨false,false,true,false,false,true,true,false,true,false⟩, ⟨false,true,true,false,false,true,true,false,true,false⟩, ⟨false,false,true,false,false,true,true,false,false,true⟩, ⟨false,true,true,false,false,true,true,false,false,true⟩, ⟨false,false,true,false,false,true,false,true,false,false⟩, ⟨false,true,true,false,false,true,false,true,false,false⟩, ⟨false,false,true,false,false,true,false,true,true,false⟩, ⟨false,true,true,false,false,true,false,true,true,false⟩, ⟨false,false,true,false,false,true,false,true,false,true⟩, ⟨false,true,true,false,false,true,false,true,false,true⟩, ⟨false,false,false,true,false,false,false,false,false,false⟩, ⟨false,true,false,true,false,false,false,false,false,false⟩, ⟨false,false,false,true,false,false,false,false,true,false⟩, ⟨false,true,false,true,false,false,false,false,true,false⟩, ⟨false,false,false,true,false,false,false,false,false,true⟩, ⟨false,true,false,true,false,false,false,false,false,true⟩, ⟨false,false,false,true,false,false,true,false,false,false⟩, ⟨false,true,false,true,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,true,false,false,true,false,false,true⟩, ⟨false,true,false,true,false,false,true,false,false,true⟩, ⟨false,false,false,true,false,false,false,true,false,false⟩, ⟨false,true,false,true,false,false,false,true,false,false⟩, ⟨false,false,false,true,false,false,false,true,true,false⟩, ⟨false,true,false,true,false,false,false,true,true,false⟩, ⟨false,false,false,true,false,false,false,true,false,true⟩, ⟨false,true,false,true,false,false,false,true,false,true⟩, ⟨false,false,false,true,true,false,false,false,false,false⟩, ⟨false,true,false,true,true,false,false,false,false,false⟩, ⟨false,false,false,true,true,false,false,false,true,false⟩, ⟨false,true,false,true,true,false,false,false,true,false⟩, ⟨false,false,false,true,true,false,false,false,false,true⟩, ⟨false,true,false,true,true,false,false,false,false,true⟩, ⟨false,false,false,true,true,false,true,false,false,false⟩, ⟨false,true,false,true,true,false,true,false,false,false⟩, ⟨false,false,false,true,true,false,true,false,true,false⟩, ⟨false,true,false,true,true,false,true,false,true,false⟩, ⟨false,false,false,true,true,false,true,false,false,true⟩, ⟨false,true,false,true,true,false,true,false,false,true⟩, ⟨false,false,false,true,true,false,false,true,false,false⟩, ⟨false,true,false,true,true,false,false,true,false,false⟩, ⟨false,false,false,true,true,false,false,true,true,false⟩, ⟨false,true,false,true,true,false,false,true,true,false⟩, ⟨false,false,false,true,true,false,false,true,false,true⟩, ⟨false,true,false,true,true,false,false,true,false,true⟩, ⟨false,false,false,true,false,true,false,false,false,false⟩, ⟨false,true,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,true,false,true,false,false,true,false⟩, ⟨false,true,false,true,false,true,false,false,true,false⟩, ⟨false,false,false,true,false,true,false,false,false,true⟩, ⟨false,true,false,true,false,true,false,false,false,true⟩, ⟨false,false,false,true,false,true,true,false,false,false⟩, ⟨false,true,false,true,false,true,true,false,false,false⟩, ⟨false,false,false,true,false,true,true,false,true,false⟩, ⟨false,true,false,true,false,true,true,false,true,false⟩, ⟨false,false,false,true,false,true,true,false,false,true⟩, ⟨false,true,false,true,false,true,true,false,false,true⟩, ⟨false,false,false,true,false,true,false,true,false,false⟩, ⟨false,true,false,true,false,true,false,true,false,false⟩, ⟨false,false,false,true,false,true,false,true,true,false⟩, ⟨false,true,false,true,false,true,false,true,true,false⟩, ⟨false,false,false,true,false,true,false,true,false,true⟩, ⟨false,true,false,true,false,true,false,true,false,true⟩]
def hitB10 (f : B10) (w : Opt) : Bool := f.get w.l1 || f.get w.l2
def checkFull (w1 w2 w3 w4 w5 w6 w7 w8 : Opt) : Bool :=
  fInB10.any (fun f => hitB10 f w1 && hitB10 f w2 && !(hitB10 f w3) && !(hitB10 f w4) && hitB10 f w5 && hitB10 f w6 && hitB10 f w7 && hitB10 f w8) &&
  fOutB10.any (fun f => hitB10 f w1 && !(hitB10 f w2) && !(hitB10 f w3) && !(hitB10 f w4) && hitB10 f w5 && hitB10 f w6 && hitB10 f w7 && hitB10 f w8) &&
  fInB10.any (fun f => hitB10 f w1 && hitB10 f w2 && hitB10 f w3 && !(hitB10 f w4) && !(hitB10 f w5) && hitB10 f w6 && hitB10 f w7 && hitB10 f w8) &&
  fInB10.any (fun f => hitB10 f w1 && hitB10 f w2 && !(hitB10 f w3) && hitB10 f w4 && hitB10 f w5 && !(hitB10 f w6) && hitB10 f w7 && hitB10 f w8) &&
  fInB10.any (fun f => hitB10 f w1 && hitB10 f w2 && hitB10 f w3 && hitB10 f w4 && !(hitB10 f w5) && !(hitB10 f w6) && hitB10 f w7 && hitB10 f w8) &&
  fOutB10.any (fun f => !(hitB10 f w1) && hitB10 f w2 && hitB10 f w3 && hitB10 f w4 && !(hitB10 f w5) && !(hitB10 f w6) && hitB10 f w7 && hitB10 f w8) &&
  fOutB10.any (fun f => !(hitB10 f w1) && !(hitB10 f w2) && hitB10 f w3 && hitB10 f w4 && hitB10 f w5 && hitB10 f w6 && !(hitB10 f w7) && hitB10 f w8) &&
  fInB10.any (fun f => hitB10 f w1 && hitB10 f w2 && hitB10 f w3 && !(hitB10 f w4) && hitB10 f w5 && hitB10 f w6 && !(hitB10 f w7) && hitB10 f w8) &&
  fOutB10.any (fun f => hitB10 f w1 && !(hitB10 f w2) && hitB10 f w3 && !(hitB10 f w4) && hitB10 f w5 && hitB10 f w6 && !(hitB10 f w7) && hitB10 f w8) &&
  fInB10.any (fun f => hitB10 f w1 && hitB10 f w2 && hitB10 f w3 && hitB10 f w4 && hitB10 f w5 && !(hitB10 f w6) && !(hitB10 f w7) && hitB10 f w8) &&
  fOutB10.any (fun f => !(hitB10 f w1) && hitB10 f w2 && hitB10 f w3 && hitB10 f w4 && hitB10 f w5 && !(hitB10 f w6) && !(hitB10 f w7) && hitB10 f w8) &&
  fOutB10.any (fun f => !(hitB10 f w1) && !(hitB10 f w2) && hitB10 f w3 && hitB10 f w4 && hitB10 f w5 && hitB10 f w6 && hitB10 f w7 && !(hitB10 f w8)) &&
  fInB10.any (fun f => hitB10 f w1 && hitB10 f w2 && !(hitB10 f w3) && hitB10 f w4 && hitB10 f w5 && hitB10 f w6 && hitB10 f w7 && !(hitB10 f w8)) &&
  fOutB10.any (fun f => hitB10 f w1 && !(hitB10 f w2) && !(hitB10 f w3) && hitB10 f w4 && hitB10 f w5 && hitB10 f w6 && hitB10 f w7 && !(hitB10 f w8)) &&
  fInB10.any (fun f => hitB10 f w1 && hitB10 f w2 && hitB10 f w3 && hitB10 f w4 && !(hitB10 f w5) && hitB10 f w6 && hitB10 f w7 && !(hitB10 f w8)) &&
  fOutB10.any (fun f => !(hitB10 f w1) && hitB10 f w2 && hitB10 f w3 && hitB10 f w4 && !(hitB10 f w5) && hitB10 f w6 && hitB10 f w7 && !(hitB10 f w8))
def allOpts41 : List Opt := [⟨2, 1, 1, 0, 0⟩, ⟨4, 2, 2, 3, 3⟩, ⟨6, 1, 2, 0, 3⟩, ⟨8, 3, 3, 2, 2⟩, ⟨10, 1, 3, 0, 2⟩, ⟨16, 4, 4, 5, 5⟩, ⟨18, 1, 4, 0, 5⟩, ⟨20, 2, 4, 3, 5⟩, ⟨24, 3, 4, 2, 5⟩, ⟨32, 5, 5, 4, 4⟩, ⟨34, 1, 5, 0, 4⟩, ⟨36, 2, 5, 3, 4⟩, ⟨40, 3, 5, 2, 4⟩, ⟨64, 6, 6, 7, 7⟩, ⟨66, 1, 6, 0, 7⟩, ⟨68, 2, 6, 3, 7⟩, ⟨72, 3, 6, 2, 7⟩, ⟨80, 4, 6, 5, 7⟩, ⟨96, 5, 6, 4, 7⟩, ⟨128, 7, 7, 6, 6⟩, ⟨130, 1, 7, 0, 6⟩, ⟨132, 2, 7, 3, 6⟩, ⟨136, 3, 7, 2, 6⟩, ⟨144, 4, 7, 5, 6⟩, ⟨160, 5, 7, 4, 6⟩, ⟨256, 8, 8, 9, 9⟩, ⟨258, 1, 8, 0, 9⟩, ⟨260, 2, 8, 3, 9⟩, ⟨264, 3, 8, 2, 9⟩, ⟨272, 4, 8, 5, 9⟩, ⟨288, 5, 8, 4, 9⟩, ⟨320, 6, 8, 7, 9⟩, ⟨384, 7, 8, 6, 9⟩, ⟨512, 9, 9, 8, 8⟩, ⟨514, 1, 9, 0, 8⟩, ⟨516, 2, 9, 3, 8⟩, ⟨520, 3, 9, 2, 8⟩, ⟨528, 4, 9, 5, 8⟩, ⟨544, 5, 9, 4, 8⟩, ⟨576, 6, 9, 7, 8⟩, ⟨640, 7, 9, 6, 8⟩]
def optsFor : Nat → List (Opt × Nat)
  | 0 => [(⟨2, 1, 1, 0, 0⟩, 0), (⟨4, 2, 2, 3, 3⟩, 1), (⟨6, 1, 2, 0, 3⟩, 1), (⟨20, 2, 4, 3, 5⟩, 3)]
  | 1 => [(⟨2, 1, 1, 0, 0⟩, 1), (⟨4, 2, 2, 3, 3⟩, 1), (⟨6, 1, 2, 0, 3⟩, 1), (⟨8, 3, 3, 2, 2⟩, 1), (⟨10, 1, 3, 0, 2⟩, 1), (⟨16, 4, 4, 5, 5⟩, 3), (⟨18, 1, 4, 0, 5⟩, 3), (⟨20, 2, 4, 3, 5⟩, 3), (⟨24, 3, 4, 2, 5⟩, 3), (⟨80, 4, 6, 5, 7⟩, 7)]
  | 2 => [(⟨2, 1, 1, 0, 0⟩, 2), (⟨4, 2, 2, 3, 3⟩, 3), (⟨6, 1, 2, 0, 3⟩, 3), (⟨16, 4, 4, 5, 5⟩, 2), (⟨18, 1, 4, 0, 5⟩, 2), (⟨20, 2, 4, 3, 5⟩, 3), (⟨32, 5, 5, 4, 4⟩, 2), (⟨34, 1, 5, 0, 4⟩, 2), (⟨36, 2, 5, 3, 4⟩, 3), (⟨68, 2, 6, 3, 7⟩, 7)]
  | 3 => [(⟨2, 1, 1, 0, 0⟩, 3), (⟨4, 2, 2, 3, 3⟩, 3), (⟨6, 1, 2, 0, 3⟩, 3), (⟨8, 3, 3, 2, 2⟩, 3), (⟨10, 1, 3, 0, 2⟩, 3), (⟨16, 4, 4, 5, 5⟩, 3), (⟨18, 1, 4, 0, 5⟩, 3), (⟨20, 2, 4, 3, 5⟩, 3), (⟨24, 3, 4, 2, 5⟩, 3), (⟨32, 5, 5, 4, 4⟩, 3), (⟨34, 1, 5, 0, 4⟩, 3), (⟨36, 2, 5, 3, 4⟩, 3), (⟨40, 3, 5, 2, 4⟩, 3), (⟨64, 6, 6, 7, 7⟩, 7), (⟨66, 1, 6, 0, 7⟩, 7), (⟨68, 2, 6, 3, 7⟩, 7), (⟨72, 3, 6, 2, 7⟩, 7), (⟨80, 4, 6, 5, 7⟩, 7), (⟨96, 5, 6, 4, 7⟩, 7), (⟨320, 6, 8, 7, 9⟩, 15)]
  | 4 => [(⟨2, 1, 1, 0, 0⟩, 4), (⟨4, 2, 2, 3, 3⟩, 5), (⟨6, 1, 2, 0, 3⟩, 5), (⟨20, 2, 4, 3, 5⟩, 7), (⟨64, 6, 6, 7, 7⟩, 4), (⟨66, 1, 6, 0, 7⟩, 4), (⟨68, 2, 6, 3, 7⟩, 5), (⟨128, 7, 7, 6, 6⟩, 4), (⟨130, 1, 7, 0, 6⟩, 4), (⟨132, 2, 7, 3, 6⟩, 5)]
  | 5 => [(⟨2, 1, 1, 0, 0⟩, 5), (⟨4, 2, 2, 3, 3⟩, 5), (⟨6, 1, 2, 0, 3⟩, 5), (⟨8, 3, 3, 2, 2⟩, 5), (⟨10, 1, 3, 0, 2⟩, 5), (⟨16, 4, 4, 5, 5⟩, 7), (⟨18, 1, 4, 0, 5⟩, 7), (⟨20, 2, 4, 3, 5⟩, 7), (⟨24, 3, 4, 2, 5⟩, 7), (⟨64, 6, 6, 7, 7⟩, 5), (⟨66, 1, 6, 0, 7⟩, 5), (⟨68, 2, 6, 3, 7⟩, 5), (⟨72, 3, 6, 2, 7⟩, 5), (⟨80, 4, 6, 5, 7⟩, 7), (⟨128, 7, 7, 6, 6⟩, 5), (⟨130, 1, 7, 0, 6⟩, 5), (⟨132, 2, 7, 3, 6⟩, 5), (⟨136, 3, 7, 2, 6⟩, 5), (⟨144, 4, 7, 5, 6⟩, 7), (⟨272, 4, 8, 5, 9⟩, 15)]
  | 6 => [(⟨2, 1, 1, 0, 0⟩, 6), (⟨4, 2, 2, 3, 3⟩, 7), (⟨6, 1, 2, 0, 3⟩, 7), (⟨16, 4, 4, 5, 5⟩, 6), (⟨18, 1, 4, 0, 5⟩, 6), (⟨20, 2, 4, 3, 5⟩, 7), (⟨32, 5, 5, 4, 4⟩, 6), (⟨34, 1, 5, 0, 4⟩, 6), (⟨36, 2, 5, 3, 4⟩, 7), (⟨64, 6, 6, 7, 7⟩, 6), (⟨66, 1, 6, 0, 7⟩, 6), (⟨68, 2, 6, 3, 7⟩, 7), (⟨80, 4, 6, 5, 7⟩, 6), (⟨96, 5, 6, 4, 7⟩, 6), (⟨128, 7, 7, 6, 6⟩, 6), (⟨130, 1, 7, 0, 6⟩, 6), (⟨132, 2, 7, 3, 6⟩, 7), (⟨144, 4, 7, 5, 6⟩, 6), (⟨160, 5, 7, 4, 6⟩, 6), (⟨260, 2, 8, 3, 9⟩, 15)]
  | 7 => [(⟨2, 1, 1, 0, 0⟩, 7), (⟨4, 2, 2, 3, 3⟩, 7), (⟨6, 1, 2, 0, 3⟩, 7), (⟨8, 3, 3, 2, 2⟩, 7), (⟨10, 1, 3, 0, 2⟩, 7), (⟨16, 4, 4, 5, 5⟩, 7), (⟨18, 1, 4, 0, 5⟩, 7), (⟨20, 2, 4, 3, 5⟩, 7), (⟨24, 3, 4, 2, 5⟩, 7), (⟨32, 5, 5, 4, 4⟩, 7), (⟨34, 1, 5, 0, 4⟩, 7), (⟨36, 2, 5, 3, 4⟩, 7), (⟨40, 3, 5, 2, 4⟩, 7), (⟨64, 6, 6, 7, 7⟩, 7), (⟨66, 1, 6, 0, 7⟩, 7), (⟨68, 2, 6, 3, 7⟩, 7), (⟨72, 3, 6, 2, 7⟩, 7), (⟨80, 4, 6, 5, 7⟩, 7), (⟨96, 5, 6, 4, 7⟩, 7), (⟨128, 7, 7, 6, 6⟩, 7), (⟨130, 1, 7, 0, 6⟩, 7), (⟨132, 2, 7, 3, 6⟩, 7), (⟨136, 3, 7, 2, 6⟩, 7), (⟨144, 4, 7, 5, 6⟩, 7), (⟨160, 5, 7, 4, 6⟩, 7), (⟨256, 8, 8, 9, 9⟩, 15), (⟨258, 1, 8, 0, 9⟩, 15), (⟨260, 2, 8, 3, 9⟩, 15), (⟨264, 3, 8, 2, 9⟩, 15), (⟨272, 4, 8, 5, 9⟩, 15), (⟨288, 5, 8, 4, 9⟩, 15), (⟨320, 6, 8, 7, 9⟩, 15), (⟨384, 7, 8, 6, 9⟩, 15)]
  | 8 => [(⟨2, 1, 1, 0, 0⟩, 8), (⟨4, 2, 2, 3, 3⟩, 9), (⟨6, 1, 2, 0, 3⟩, 9), (⟨20, 2, 4, 3, 5⟩, 11), (⟨256, 8, 8, 9, 9⟩, 8), (⟨258, 1, 8, 0, 9⟩, 8), (⟨260, 2, 8, 3, 9⟩, 9), (⟨512, 9, 9, 8, 8⟩, 8), (⟨514, 1, 9, 0, 8⟩, 8), (⟨516, 2, 9, 3, 8⟩, 9)]
  | 9 => [(⟨2, 1, 1, 0, 0⟩, 9), (⟨4, 2, 2, 3, 3⟩, 9), (⟨6, 1, 2, 0, 3⟩, 9), (⟨8, 3, 3, 2, 2⟩, 9), (⟨10, 1, 3, 0, 2⟩, 9), (⟨16, 4, 4, 5, 5⟩, 11), (⟨18, 1, 4, 0, 5⟩, 11), (⟨20, 2, 4, 3, 5⟩, 11), (⟨24, 3, 4, 2, 5⟩, 11), (⟨80, 4, 6, 5, 7⟩, 15), (⟨256, 8, 8, 9, 9⟩, 9), (⟨258, 1, 8, 0, 9⟩, 9), (⟨260, 2, 8, 3, 9⟩, 9), (⟨264, 3, 8, 2, 9⟩, 9), (⟨272, 4, 8, 5, 9⟩, 11), (⟨512, 9, 9, 8, 8⟩, 9), (⟨514, 1, 9, 0, 8⟩, 9), (⟨516, 2, 9, 3, 8⟩, 9), (⟨520, 3, 9, 2, 8⟩, 9), (⟨528, 4, 9, 5, 8⟩, 11)]
  | 10 => [(⟨2, 1, 1, 0, 0⟩, 10), (⟨4, 2, 2, 3, 3⟩, 11), (⟨6, 1, 2, 0, 3⟩, 11), (⟨16, 4, 4, 5, 5⟩, 10), (⟨18, 1, 4, 0, 5⟩, 10), (⟨20, 2, 4, 3, 5⟩, 11), (⟨32, 5, 5, 4, 4⟩, 10), (⟨34, 1, 5, 0, 4⟩, 10), (⟨36, 2, 5, 3, 4⟩, 11), (⟨68, 2, 6, 3, 7⟩, 15), (⟨256, 8, 8, 9, 9⟩, 10), (⟨258, 1, 8, 0, 9⟩, 10), (⟨260, 2, 8, 3, 9⟩, 11), (⟨272, 4, 8, 5, 9⟩, 10), (⟨288, 5, 8, 4, 9⟩, 10), (⟨512, 9, 9, 8, 8⟩, 10), (⟨514, 1, 9, 0, 8⟩, 10), (⟨516, 2, 9, 3, 8⟩, 11), (⟨528, 4, 9, 5, 8⟩, 10), (⟨544, 5, 9, 4, 8⟩, 10)]
  | 11 => [(⟨2, 1, 1, 0, 0⟩, 11), (⟨4, 2, 2, 3, 3⟩, 11), (⟨6, 1, 2, 0, 3⟩, 11), (⟨8, 3, 3, 2, 2⟩, 11), (⟨10, 1, 3, 0, 2⟩, 11), (⟨16, 4, 4, 5, 5⟩, 11), (⟨18, 1, 4, 0, 5⟩, 11), (⟨20, 2, 4, 3, 5⟩, 11), (⟨24, 3, 4, 2, 5⟩, 11), (⟨32, 5, 5, 4, 4⟩, 11), (⟨34, 1, 5, 0, 4⟩, 11), (⟨36, 2, 5, 3, 4⟩, 11), (⟨40, 3, 5, 2, 4⟩, 11), (⟨64, 6, 6, 7, 7⟩, 15), (⟨66, 1, 6, 0, 7⟩, 15), (⟨68, 2, 6, 3, 7⟩, 15), (⟨72, 3, 6, 2, 7⟩, 15), (⟨80, 4, 6, 5, 7⟩, 15), (⟨96, 5, 6, 4, 7⟩, 15), (⟨256, 8, 8, 9, 9⟩, 11), (⟨258, 1, 8, 0, 9⟩, 11), (⟨260, 2, 8, 3, 9⟩, 11), (⟨264, 3, 8, 2, 9⟩, 11), (⟨272, 4, 8, 5, 9⟩, 11), (⟨288, 5, 8, 4, 9⟩, 11), (⟨320, 6, 8, 7, 9⟩, 15), (⟨512, 9, 9, 8, 8⟩, 11), (⟨514, 1, 9, 0, 8⟩, 11), (⟨516, 2, 9, 3, 8⟩, 11), (⟨520, 3, 9, 2, 8⟩, 11), (⟨528, 4, 9, 5, 8⟩, 11), (⟨544, 5, 9, 4, 8⟩, 11), (⟨576, 6, 9, 7, 8⟩, 15)]
  | 12 => [(⟨2, 1, 1, 0, 0⟩, 12), (⟨4, 2, 2, 3, 3⟩, 13), (⟨6, 1, 2, 0, 3⟩, 13), (⟨20, 2, 4, 3, 5⟩, 15), (⟨64, 6, 6, 7, 7⟩, 12), (⟨66, 1, 6, 0, 7⟩, 12), (⟨68, 2, 6, 3, 7⟩, 13), (⟨128, 7, 7, 6, 6⟩, 12), (⟨130, 1, 7, 0, 6⟩, 12), (⟨132, 2, 7, 3, 6⟩, 13), (⟨256, 8, 8, 9, 9⟩, 12), (⟨258, 1, 8, 0, 9⟩, 12), (⟨260, 2, 8, 3, 9⟩, 13), (⟨320, 6, 8, 7, 9⟩, 12), (⟨384, 7, 8, 6, 9⟩, 12), (⟨512, 9, 9, 8, 8⟩, 12), (⟨514, 1, 9, 0, 8⟩, 12), (⟨516, 2, 9, 3, 8⟩, 13), (⟨576, 6, 9, 7, 8⟩, 12), (⟨640, 7, 9, 6, 8⟩, 12)]
  | 13 => [(⟨2, 1, 1, 0, 0⟩, 13), (⟨4, 2, 2, 3, 3⟩, 13), (⟨6, 1, 2, 0, 3⟩, 13), (⟨8, 3, 3, 2, 2⟩, 13), (⟨10, 1, 3, 0, 2⟩, 13), (⟨16, 4, 4, 5, 5⟩, 15), (⟨18, 1, 4, 0, 5⟩, 15), (⟨20, 2, 4, 3, 5⟩, 15), (⟨24, 3, 4, 2, 5⟩, 15), (⟨64, 6, 6, 7, 7⟩, 13), (⟨66, 1, 6, 0, 7⟩, 13), (⟨68, 2, 6, 3, 7⟩, 13), (⟨72, 3, 6, 2, 7⟩, 13), (⟨80, 4, 6, 5, 7⟩, 15), (⟨128, 7, 7, 6, 6⟩, 13), (⟨130, 1, 7, 0, 6⟩, 13), (⟨132, 2, 7, 3, 6⟩, 13), (⟨136, 3, 7, 2, 6⟩, 13), (⟨144, 4, 7, 5, 6⟩, 15), (⟨256, 8, 8, 9, 9⟩, 13), (⟨258, 1, 8, 0, 9⟩, 13), (⟨260, 2, 8, 3, 9⟩, 13), (⟨264, 3, 8, 2, 9⟩, 13), (⟨272, 4, 8, 5, 9⟩, 15), (⟨320, 6, 8, 7, 9⟩, 13), (⟨384, 7, 8, 6, 9⟩, 13), (⟨512, 9, 9, 8, 8⟩, 13), (⟨514, 1, 9, 0, 8⟩, 13), (⟨516, 2, 9, 3, 8⟩, 13), (⟨520, 3, 9, 2, 8⟩, 13), (⟨528, 4, 9, 5, 8⟩, 15), (⟨576, 6, 9, 7, 8⟩, 13), (⟨640, 7, 9, 6, 8⟩, 13)]
  | 14 => [(⟨2, 1, 1, 0, 0⟩, 14), (⟨4, 2, 2, 3, 3⟩, 15), (⟨6, 1, 2, 0, 3⟩, 15), (⟨16, 4, 4, 5, 5⟩, 14), (⟨18, 1, 4, 0, 5⟩, 14), (⟨20, 2, 4, 3, 5⟩, 15), (⟨32, 5, 5, 4, 4⟩, 14), (⟨34, 1, 5, 0, 4⟩, 14), (⟨36, 2, 5, 3, 4⟩, 15), (⟨64, 6, 6, 7, 7⟩, 14), (⟨66, 1, 6, 0, 7⟩, 14), (⟨68, 2, 6, 3, 7⟩, 15), (⟨80, 4, 6, 5, 7⟩, 14), (⟨96, 5, 6, 4, 7⟩, 14), (⟨128, 7, 7, 6, 6⟩, 14), (⟨130, 1, 7, 0, 6⟩, 14), (⟨132, 2, 7, 3, 6⟩, 15), (⟨144, 4, 7, 5, 6⟩, 14), (⟨160, 5, 7, 4, 6⟩, 14), (⟨256, 8, 8, 9, 9⟩, 14), (⟨258, 1, 8, 0, 9⟩, 14), (⟨260, 2, 8, 3, 9⟩, 15), (⟨272, 4, 8, 5, 9⟩, 14), (⟨288, 5, 8, 4, 9⟩, 14), (⟨320, 6, 8, 7, 9⟩, 14), (⟨384, 7, 8, 6, 9⟩, 14), (⟨512, 9, 9, 8, 8⟩, 14), (⟨514, 1, 9, 0, 8⟩, 14), (⟨516, 2, 9, 3, 8⟩, 15), (⟨528, 4, 9, 5, 8⟩, 14), (⟨544, 5, 9, 4, 8⟩, 14), (⟨576, 6, 9, 7, 8⟩, 14), (⟨640, 7, 9, 6, 8⟩, 14)]
  | 15 => [(⟨2, 1, 1, 0, 0⟩, 15), (⟨4, 2, 2, 3, 3⟩, 15), (⟨6, 1, 2, 0, 3⟩, 15), (⟨8, 3, 3, 2, 2⟩, 15), (⟨10, 1, 3, 0, 2⟩, 15), (⟨16, 4, 4, 5, 5⟩, 15), (⟨18, 1, 4, 0, 5⟩, 15), (⟨20, 2, 4, 3, 5⟩, 15), (⟨24, 3, 4, 2, 5⟩, 15), (⟨32, 5, 5, 4, 4⟩, 15), (⟨34, 1, 5, 0, 4⟩, 15), (⟨36, 2, 5, 3, 4⟩, 15), (⟨40, 3, 5, 2, 4⟩, 15), (⟨64, 6, 6, 7, 7⟩, 15), (⟨66, 1, 6, 0, 7⟩, 15), (⟨68, 2, 6, 3, 7⟩, 15), (⟨72, 3, 6, 2, 7⟩, 15), (⟨80, 4, 6, 5, 7⟩, 15), (⟨96, 5, 6, 4, 7⟩, 15), (⟨128, 7, 7, 6, 6⟩, 15), (⟨130, 1, 7, 0, 6⟩, 15), (⟨132, 2, 7, 3, 6⟩, 15), (⟨136, 3, 7, 2, 6⟩, 15), (⟨144, 4, 7, 5, 6⟩, 15), (⟨160, 5, 7, 4, 6⟩, 15), (⟨256, 8, 8, 9, 9⟩, 15), (⟨258, 1, 8, 0, 9⟩, 15), (⟨260, 2, 8, 3, 9⟩, 15), (⟨264, 3, 8, 2, 9⟩, 15), (⟨272, 4, 8, 5, 9⟩, 15), (⟨288, 5, 8, 4, 9⟩, 15), (⟨320, 6, 8, 7, 9⟩, 15), (⟨384, 7, 8, 6, 9⟩, 15), (⟨512, 9, 9, 8, 8⟩, 15), (⟨514, 1, 9, 0, 8⟩, 15), (⟨516, 2, 9, 3, 8⟩, 15), (⟨520, 3, 9, 2, 8⟩, 15), (⟨528, 4, 9, 5, 8⟩, 15), (⟨544, 5, 9, 4, 8⟩, 15), (⟨576, 6, 9, 7, 8⟩, 15), (⟨640, 7, 9, 6, 8⟩, 15)]
  | _ => []

def run8 (ug : Nat) (st : F16) (w1 w2 w3 w4 w5 w6 w7 : Opt) : List (List Nat) :=
  (optsFor ug).flatMap fun (w8, _) =>
    if antiOk w8 [w1, w2, w3, w4, w5, w6, w7] then
      match stepF16_8 st w1 w2 w3 w4 w5 w6 w7 w8 with
      | none => []
      | some _ => if checkFull w1 w2 w3 w4 w5 w6 w7 w8 then [[w1.id, w2.id, w3.id, w4.id, w5.id, w6.id, w7.id, w8.id]] else []
    else []
def run7 (ug : Nat) (st : F16) (w1 w2 w3 w4 w5 w6 : Opt) : List (List Nat) :=
  (optsFor ug).flatMap fun (w7, nug) =>
    if antiOk w7 [w1, w2, w3, w4, w5, w6] then
      match stepF16_7 st w1 w2 w3 w4 w5 w6 w7 with
      | none => []
      | some st' => run8 nug st' w1 w2 w3 w4 w5 w6 w7
    else []
def run6 (ug : Nat) (st : F16) (w1 w2 w3 w4 w5 : Opt) : List (List Nat) :=
  (optsFor ug).flatMap fun (w6, nug) =>
    if antiOk w6 [w1, w2, w3, w4, w5] then
      match stepF16_6 st w1 w2 w3 w4 w5 w6 with
      | none => []
      | some st' => run7 nug st' w1 w2 w3 w4 w5 w6
    else []
def run5 (ug : Nat) (st : F16) (w1 w2 w3 w4 : Opt) : List (List Nat) :=
  (optsFor ug).flatMap fun (w5, nug) =>
    if antiOk w5 [w1, w2, w3, w4] then
      match stepF16_5 st w1 w2 w3 w4 w5 with
      | none => []
      | some st' => run6 nug st' w1 w2 w3 w4 w5
    else []
def run4 (ug : Nat) (st : F16) (w1 w2 w3 : Opt) : List (List Nat) :=
  (optsFor ug).flatMap fun (w4, nug) =>
    if antiOk w4 [w1, w2, w3] then
      match stepF16_4 st w1 w2 w3 w4 with
      | none => []
      | some st' => run5 nug st' w1 w2 w3 w4
    else []
def run3 (ug : Nat) (st : F16) (w1 w2 : Opt) : List (List Nat) :=
  (optsFor ug).flatMap fun (w3, nug) =>
    if antiOk w3 [w1, w2] then
      match stepF16_3 st w1 w2 w3 with
      | none => []
      | some st' => run4 nug st' w1 w2 w3
    else []
def runBranch (w1 w2 : Opt) (ug2 : Nat) : List (List Nat) :=
  match stepF16_1 initF16 w1 with
  | none => []
  | some st1 =>
    match stepF16_2 st1 w1 w2 with
    | none => []
    | some st2 => run3 ug2 st2 w1 w2



def litTrue (ch : Fin 5 → Option Bool) (l : Nat) : Prop :=
  ∃ g : Fin 5, ∃ b : Bool, ch g = some b ∧ 2 * g.val + (if b then 1 else 0) = l

def ForbValid (f : B10) (ch : Fin 5 → Option Bool) : Prop :=
  ∀ l : Nat, litTrue ch l → f.get l = false

abbrev OptOk (w : Opt) : Prop :=
  w.l1 < 10 ∧ w.l2 < 10 ∧
  w.o1 = (if w.l1 % 2 = 0 then w.l1 + 1 else w.l1 - 1) ∧
  w.o2 = (if w.l2 % 2 = 0 then w.l2 + 1 else w.l2 - 1)

def OutSat (w : Opt) (ch : Fin 5 → Option Bool) : Prop :=
  litTrue ch w.l1 ∨ litTrue ch w.l2

def InAvoid (w : Opt) (ch : Fin 5 → Option Bool) : Prop :=
  ¬ litTrue ch w.l1 ∧ ¬ litTrue ch w.l2

lemma litTrue_lt {ch : Fin 5 → Option Bool} {l : Nat} (h : litTrue ch l) : l < 10 := by
  obtain ⟨g, b, _, rfl⟩ := h
  cases b <;> simp <;> omega

lemma not_litTrue_opp {ch : Fin 5 → Option Bool} {l : Nat} (h : litTrue ch l) :
    ¬ litTrue ch (if l % 2 = 0 then l + 1 else l - 1) := by
  obtain ⟨g1, b1, h1, rfl⟩ := h
  rintro ⟨g2, b2, h2, heq⟩
  cases b1 <;> cases b2 <;> simp only [↓reduceIte, Bool.false_eq_true] at heq
  · have hm : (2 * g1.val + 0) % 2 = 0 := by omega
    rw [ite_eq_left hm] at heq; omega
  · have hm : (2 * g1.val + 0) % 2 = 0 := by omega
    rw [ite_eq_left hm] at heq
    have hg : g1 = g2 := Fin.ext (by omega)
    subst hg; rw [h1] at h2; cases h2
  · have hm : ¬ (2 * g1.val + 1) % 2 = 0 := by omega
    rw [ite_eq_right hm] at heq
    have hg : g1 = g2 := Fin.ext (by omega)
    subst hg; rw [h1] at h2; cases h2
  · have hm : ¬ (2 * g1.val + 1) % 2 = 0 := by omega
    rw [ite_eq_right hm] at heq; omega

lemma forbValid_set {f : B10} {ch : Fin 5 → Option Bool} (hf : ForbValid f ch)
    {l : Nat} (hl : l < 10) (hnot : ¬ litTrue ch l) : ForbValid (f.set l) ch := by
  intro l' hl'
  have hl'10 : l' < 10 := litTrue_lt hl'
  have hne : (⟨l, hl⟩ : Fin 10) ≠ ⟨l', hl'10⟩ := fun h => hnot (by
    have : l = l' := congrArg Fin.val h; rwa [this])
  rw [B10.get_set_ne f ⟨l, hl⟩ ⟨l', hl'10⟩ hne]
  exact hf l' hl'

lemma upPass1_sound (ch : Fin 5 → Option Bool) :
    ∀ (outs : List Opt) (f : B10) (chg : Bool),
      ForbValid f ch → (∀ w ∈ outs, OptOk w ∧ OutSat w ch) →
      ∃ f' chg', upPass1 f chg outs = some (f', chg') ∧ ForbValid f' ch := by
  intro outs
  induction outs with
  | nil => intro f chg hf _; exact ⟨f, chg, rfl, hf⟩
  | cons w ws ih =>
    intro f chg hf houts
    obtain ⟨⟨hl1, hl2, ho1, ho2⟩, hsat⟩ := houts w (List.mem_cons_self ..)
    have hrest : ∀ u ∈ ws, OptOk u ∧ OutSat u ch := fun u hu => houts u (List.mem_cons_of_mem _ hu)
    unfold upPass1
    dsimp only
    by_cases hf1 : f.get w.l1 = true
    · by_cases hf2 : f.get w.l2 = true
      · exfalso
        rcases hsat with h1 | h2
        · rw [hf w.l1 h1] at hf1; exact Bool.noConfusion hf1
        · rw [hf w.l2 h2] at hf2; exact Bool.noConfusion hf2
      · have hnot1 : ¬ litTrue ch w.l1 := fun h1 => by rw [hf w.l1 h1] at hf1; exact Bool.noConfusion hf1
        have hlit2 : litTrue ch w.l2 := hsat.resolve_left hnot1
        have ho2lt : w.o2 < 10 := by rw [ho2]; split_ifs <;> omega
        have hnot_o2 : ¬ litTrue ch w.o2 := by rw [ho2]; exact not_litTrue_opp hlit2
        simp only [hf1, hf2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · exact ih f chg hf hrest
        · exact ih (f.set w.o2) true (forbValid_set hf ho2lt hnot_o2) hrest
    · have hf1' : f.get w.l1 = false := Bool.eq_false_iff.mpr hf1
      by_cases hf2 : f.get w.l2 = true
      · have hnot2 : ¬ litTrue ch w.l2 := fun h2 => by rw [hf w.l2 h2] at hf2; exact Bool.noConfusion hf2
        have hlit1 : litTrue ch w.l1 := hsat.resolve_right hnot2
        have ho1lt : w.o1 < 10 := by rw [ho1]; split_ifs <;> omega
        have hnot_o1 : ¬ litTrue ch w.o1 := by rw [ho1]; exact not_litTrue_opp hlit1
        simp only [hf1', hf2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · exact ih f chg hf hrest
        · exact ih (f.set w.o1) true (forbValid_set hf ho1lt hnot_o1) hrest
      · have hf2' : f.get w.l2 = false := Bool.eq_false_iff.mpr hf2
        simp only [hf1', hf2', Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        by_cases heq : (w.l1 == w.l2) = true
        · have heq' : w.l1 = w.l2 := eq_of_beq heq
          have hlit1 : litTrue ch w.l1 := by rcases hsat with h1 | h2; exact h1; rwa [heq']
          have ho1lt : w.o1 < 10 := by rw [ho1]; split_ifs <;> omega
          have hnot_o1 : ¬ litTrue ch w.o1 := by rw [ho1]; exact not_litTrue_opp hlit1
          simp only [heq, ↓reduceIte]
          split_ifs
          · exact ih f chg hf hrest
          · exact ih (f.set w.o1) true (forbValid_set hf ho1lt hnot_o1) hrest
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          exact ih f chg hf hrest

lemma upProp_sound (ch : Fin 5 → Option Bool) (f : B10) (outs : List Opt)
    (hf : ForbValid f ch) (houts : ∀ w ∈ outs, OptOk w ∧ OutSat w ch) :
    ∃ f', upProp f outs = some f' ∧ ForbValid f' ch := by
  unfold upProp
  obtain ⟨f1, chg1, h1, hf1⟩ := upPass1_sound ch outs f false hf houts
  rw [h1]
  cases chg1
  · exact ⟨f1, rfl, hf1⟩
  · dsimp only
    obtain ⟨f2, chg2, h2, hf2⟩ := upPass1_sound ch outs f1 false hf1 houts
    rw [h2]; exact ⟨f2, rfl, hf2⟩

lemma stepIn_sound (ch : Fin 5 → Option Bool) (f : B10) (wv : Opt) (outs : List Opt)
    (hf : ForbValid f ch) (hwok : OptOk wv) (hav : InAvoid wv ch)
    (houts : ∀ w ∈ outs, OptOk w ∧ OutSat w ch) :
    ∃ f', stepIn f wv outs = some f' ∧ ForbValid f' ch := by
  unfold stepIn
  dsimp only
  split_ifs
  · exact ⟨f, rfl, hf⟩
  · exact upProp_sound ch _ outs (forbValid_set (forbValid_set hf hwok.1 hav.1) hwok.2.1 hav.2) houts
  · exact upProp_sound ch _ outs (forbValid_set hf hwok.2.1 hav.2) houts
  · exact upProp_sound ch _ outs (forbValid_set hf hwok.1 hav.1) houts
  · exact upProp_sound ch _ outs hf houts

lemma stepOut_sound (ch : Fin 5 → Option Bool) (f : B10) (wv : Opt) (outs : List Opt)
    (hf : ForbValid f ch) (hwok : OptOk wv) (hsat : OutSat wv ch)
    (houts : ∀ w ∈ outs, OptOk w ∧ OutSat w ch) :
    ∃ f', stepOut f wv outs = some f' ∧ ForbValid f' ch := by
  obtain ⟨hl1, hl2, ho1, ho2⟩ := hwok
  unfold stepOut; dsimp only
  by_cases hf1 : f.get wv.l1 = true
  · by_cases hf2 : f.get wv.l2 = true
    · exfalso; rcases hsat with h1 | h2
      · rw [hf wv.l1 h1] at hf1; exact Bool.noConfusion hf1
      · rw [hf wv.l2 h2] at hf2; exact Bool.noConfusion hf2
    · have hlit2 : litTrue ch wv.l2 := hsat.resolve_left (fun h1 => by rw [hf wv.l1 h1] at hf1; exact Bool.noConfusion hf1)
      have ho2lt : wv.o2 < 10 := by rw [ho2]; split_ifs <;> omega
      have hnot_o2 : ¬ litTrue ch wv.o2 := by rw [ho2]; exact not_litTrue_opp hlit2
      simp only [hf1, hf2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact ⟨f, rfl, hf⟩
      · exact upProp_sound ch (f.set wv.o2) outs (forbValid_set hf ho2lt hnot_o2) houts
  · have hf1' : f.get wv.l1 = false := Bool.eq_false_iff.mpr hf1
    by_cases hf2 : f.get wv.l2 = true
    · have hlit1 : litTrue ch wv.l1 := hsat.resolve_right (fun h2 => by rw [hf wv.l2 h2] at hf2; exact Bool.noConfusion hf2)
      have ho1lt : wv.o1 < 10 := by rw [ho1]; split_ifs <;> omega
      have hnot_o1 : ¬ litTrue ch wv.o1 := by rw [ho1]; exact not_litTrue_opp hlit1
      simp only [hf1', hf2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact ⟨f, rfl, hf⟩
      · exact upProp_sound ch (f.set wv.o1) outs (forbValid_set hf ho1lt hnot_o1) houts
    · have hf2' : f.get wv.l2 = false := Bool.eq_false_iff.mpr hf2
      simp only [hf1', hf2', Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      by_cases heq : (wv.l1 == wv.l2) = true
      · have heq' : wv.l1 = wv.l2 := eq_of_beq heq
        have hlit1 : litTrue ch wv.l1 := by rcases hsat with h1 | h2; exact h1; rwa [heq']
        have ho1lt : wv.o1 < 10 := by rw [ho1]; split_ifs <;> omega
        have hnot_o1 : ¬ litTrue ch wv.o1 := by rw [ho1]; exact not_litTrue_opp hlit1
        simp only [heq, ↓reduceIte]
        split_ifs
        · exact ⟨f, rfl, hf⟩
        · exact upProp_sound ch (f.set wv.o1) outs (forbValid_set hf ho1lt hnot_o1) houts
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        exact ⟨f, rfl, hf⟩

lemma not_both_forb {f : B10} {ch : Fin 5 → Option Bool} {w : Opt}
    (hf : ForbValid f ch) (hsat : OutSat w ch) : (f.get w.l1 && f.get w.l2) = false := by
  rcases hsat with h1 | h2
  · rw [hf w.l1 h1, Bool.false_and]
  · rw [hf w.l2 h2, Bool.and_false]

def StepValid (v : Nat) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool) : Prop :=
  (∀ u : V, u.val ≠ 0 → OptOk (W u)) ∧
  (∀ k : Fin 16, ∀ u : V, u.val ≠ 0 → u.val ≤ v →
    if u ∈ rows9 k then InAvoid (W u) (ch k) else OutSat (W u) (ch k))

lemma stepF16_1_sound (st : F16) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hst : ∀ k : Fin 16, ForbValid (st.get k) (ch k))
    (hsv : StepValid 1 W ch) :
    ∃ st', stepF16_1 st (W 1) = some st' ∧ ∀ k : Fin 16, ForbValid (st'.get k) (ch k) := by
  unfold stepF16_1
  have hfast0 : (st.f0.get (W 1).l1 && st.f0.get (W 1).l2) = false :=
    not_both_forb (hst 0) (by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast1 : (st.f1.get (W 1).l1 && st.f1.get (W 1).l2) = false :=
    not_both_forb (hst 1) (by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast2 : (st.f2.get (W 1).l1 && st.f2.get (W 1).l2) = false :=
    not_both_forb (hst 2) (by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast3 : (st.f3.get (W 1).l1 && st.f3.get (W 1).l2) = false :=
    not_both_forb (hst 3) (by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast4 : (st.f4.get (W 1).l1 && st.f4.get (W 1).l2) = false :=
    not_both_forb (hst 4) (by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast7 : (st.f7.get (W 1).l1 && st.f7.get (W 1).l2) = false :=
    not_both_forb (hst 7) (by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast8 : (st.f8.get (W 1).l1 && st.f8.get (W 1).l2) = false :=
    not_both_forb (hst 8) (by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast9 : (st.f9.get (W 1).l1 && st.f9.get (W 1).l2) = false :=
    not_both_forb (hst 9) (by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast12 : (st.f12.get (W 1).l1 && st.f12.get (W 1).l2) = false :=
    not_both_forb (hst 12) (by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast13 : (st.f13.get (W 1).l1 && st.f13.get (W 1).l2) = false :=
    not_both_forb (hst 13) (by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this)
  have hfast14 : (st.f14.get (W 1).l1 && st.f14.get (W 1).l2) = false :=
    not_both_forb (hst 14) (by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this)
  simp only [hfast0, hfast1, hfast2, hfast3, hfast4, hfast7, hfast8, hfast9, hfast12, hfast13, hfast14, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨nf5, hnf5, hfv5⟩ := stepIn_sound (ch 5) st.f5 (W 1) []
    (hst 5) (hsv.1 1 (by decide)) (by have := hsv.2 5 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; exact (List.not_mem_nil hu).elim)
  rw [hnf5]
  obtain ⟨nf6, hnf6, hfv6⟩ := stepIn_sound (ch 6) st.f6 (W 1) []
    (hst 6) (hsv.1 1 (by decide)) (by have := hsv.2 6 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; exact (List.not_mem_nil hu).elim)
  rw [hnf6]
  obtain ⟨nf10, hnf10, hfv10⟩ := stepIn_sound (ch 10) st.f10 (W 1) []
    (hst 10) (hsv.1 1 (by decide)) (by have := hsv.2 10 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; exact (List.not_mem_nil hu).elim)
  rw [hnf10]
  obtain ⟨nf11, hnf11, hfv11⟩ := stepIn_sound (ch 11) st.f11 (W 1) []
    (hst 11) (hsv.1 1 (by decide)) (by have := hsv.2 11 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; exact (List.not_mem_nil hu).elim)
  rw [hnf11]
  obtain ⟨nf15, hnf15, hfv15⟩ := stepIn_sound (ch 15) st.f15 (W 1) []
    (hst 15) (hsv.1 1 (by decide)) (by have := hsv.2 15 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; exact (List.not_mem_nil hu).elim)
  rw [hnf15]
  obtain ⟨nf0, hnf0, hfv0⟩ := stepOut_sound (ch 0) st.f0 (W 1) [W 1]
    (hst 0) (hsv.1 1 (by decide)) (by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf0]
  obtain ⟨nf1, hnf1, hfv1⟩ := stepOut_sound (ch 1) st.f1 (W 1) [W 1]
    (hst 1) (hsv.1 1 (by decide)) (by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf1]
  obtain ⟨nf2, hnf2, hfv2⟩ := stepOut_sound (ch 2) st.f2 (W 1) [W 1]
    (hst 2) (hsv.1 1 (by decide)) (by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf2]
  obtain ⟨nf3, hnf3, hfv3⟩ := stepOut_sound (ch 3) st.f3 (W 1) [W 1]
    (hst 3) (hsv.1 1 (by decide)) (by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf3]
  obtain ⟨nf4, hnf4, hfv4⟩ := stepOut_sound (ch 4) st.f4 (W 1) [W 1]
    (hst 4) (hsv.1 1 (by decide)) (by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf4]
  obtain ⟨nf7, hnf7, hfv7⟩ := stepOut_sound (ch 7) st.f7 (W 1) [W 1]
    (hst 7) (hsv.1 1 (by decide)) (by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf7]
  obtain ⟨nf8, hnf8, hfv8⟩ := stepOut_sound (ch 8) st.f8 (W 1) [W 1]
    (hst 8) (hsv.1 1 (by decide)) (by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf8]
  obtain ⟨nf9, hnf9, hfv9⟩ := stepOut_sound (ch 9) st.f9 (W 1) [W 1]
    (hst 9) (hsv.1 1 (by decide)) (by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf9]
  obtain ⟨nf12, hnf12, hfv12⟩ := stepOut_sound (ch 12) st.f12 (W 1) [W 1]
    (hst 12) (hsv.1 1 (by decide)) (by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf12]
  obtain ⟨nf13, hnf13, hfv13⟩ := stepOut_sound (ch 13) st.f13 (W 1) [W 1]
    (hst 13) (hsv.1 1 (by decide)) (by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf13]
  obtain ⟨nf14, hnf14, hfv14⟩ := stepOut_sound (ch 14) st.f14 (W 1) [W 1]
    (hst 14) (hsv.1 1 (by decide)) (by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf14]
  refine ⟨⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩, rfl, fun k => by fin_cases k <;> assumption⟩

lemma stepF16_2_sound (st : F16) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hst : ∀ k : Fin 16, ForbValid (st.get k) (ch k))
    (hsv : StepValid 2 W ch) :
    ∃ st', stepF16_2 st (W 1) (W 2) = some st' ∧ ∀ k : Fin 16, ForbValid (st'.get k) (ch k) := by
  unfold stepF16_2
  have hfast0 : (st.f0.get (W 2).l1 && st.f0.get (W 2).l2) = false :=
    not_both_forb (hst 0) (by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast2 : (st.f2.get (W 2).l1 && st.f2.get (W 2).l2) = false :=
    not_both_forb (hst 2) (by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast3 : (st.f3.get (W 2).l1 && st.f3.get (W 2).l2) = false :=
    not_both_forb (hst 3) (by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast4 : (st.f4.get (W 2).l1 && st.f4.get (W 2).l2) = false :=
    not_both_forb (hst 4) (by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast5 : (st.f5.get (W 2).l1 && st.f5.get (W 2).l2) = false :=
    not_both_forb (hst 5) (by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast7 : (st.f7.get (W 2).l1 && st.f7.get (W 2).l2) = false :=
    not_both_forb (hst 7) (by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast9 : (st.f9.get (W 2).l1 && st.f9.get (W 2).l2) = false :=
    not_both_forb (hst 9) (by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast10 : (st.f10.get (W 2).l1 && st.f10.get (W 2).l2) = false :=
    not_both_forb (hst 10) (by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast12 : (st.f12.get (W 2).l1 && st.f12.get (W 2).l2) = false :=
    not_both_forb (hst 12) (by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast14 : (st.f14.get (W 2).l1 && st.f14.get (W 2).l2) = false :=
    not_both_forb (hst 14) (by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this)
  have hfast15 : (st.f15.get (W 2).l1 && st.f15.get (W 2).l2) = false :=
    not_both_forb (hst 15) (by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this)
  simp only [hfast0, hfast2, hfast3, hfast4, hfast5, hfast7, hfast9, hfast10, hfast12, hfast14, hfast15, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨nf1, hnf1, hfv1⟩ := stepIn_sound (ch 1) st.f1 (W 2) [W 1]
    (hst 1) (hsv.1 2 (by decide)) (by have := hsv.2 1 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf1]
  obtain ⟨nf6, hnf6, hfv6⟩ := stepIn_sound (ch 6) st.f6 (W 2) []
    (hst 6) (hsv.1 2 (by decide)) (by have := hsv.2 6 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; exact (List.not_mem_nil hu).elim)
  rw [hnf6]
  obtain ⟨nf8, hnf8, hfv8⟩ := stepIn_sound (ch 8) st.f8 (W 2) [W 1]
    (hst 8) (hsv.1 2 (by decide)) (by have := hsv.2 8 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf8]
  obtain ⟨nf11, hnf11, hfv11⟩ := stepIn_sound (ch 11) st.f11 (W 2) []
    (hst 11) (hsv.1 2 (by decide)) (by have := hsv.2 11 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; exact (List.not_mem_nil hu).elim)
  rw [hnf11]
  obtain ⟨nf13, hnf13, hfv13⟩ := stepIn_sound (ch 13) st.f13 (W 2) [W 1]
    (hst 13) (hsv.1 2 (by decide)) (by have := hsv.2 13 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf13]
  obtain ⟨nf0, hnf0, hfv0⟩ := stepOut_sound (ch 0) st.f0 (W 2) [W 2, W 1]
    (hst 0) (hsv.1 2 (by decide)) (by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf0]
  obtain ⟨nf2, hnf2, hfv2⟩ := stepOut_sound (ch 2) st.f2 (W 2) [W 2, W 1]
    (hst 2) (hsv.1 2 (by decide)) (by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf2]
  obtain ⟨nf3, hnf3, hfv3⟩ := stepOut_sound (ch 3) st.f3 (W 2) [W 2, W 1]
    (hst 3) (hsv.1 2 (by decide)) (by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf3]
  obtain ⟨nf4, hnf4, hfv4⟩ := stepOut_sound (ch 4) st.f4 (W 2) [W 2, W 1]
    (hst 4) (hsv.1 2 (by decide)) (by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf4]
  obtain ⟨nf5, hnf5, hfv5⟩ := stepOut_sound (ch 5) st.f5 (W 2) [W 2]
    (hst 5) (hsv.1 2 (by decide)) (by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf5]
  obtain ⟨nf7, hnf7, hfv7⟩ := stepOut_sound (ch 7) st.f7 (W 2) [W 2, W 1]
    (hst 7) (hsv.1 2 (by decide)) (by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf7]
  obtain ⟨nf9, hnf9, hfv9⟩ := stepOut_sound (ch 9) st.f9 (W 2) [W 2, W 1]
    (hst 9) (hsv.1 2 (by decide)) (by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf9]
  obtain ⟨nf10, hnf10, hfv10⟩ := stepOut_sound (ch 10) st.f10 (W 2) [W 2]
    (hst 10) (hsv.1 2 (by decide)) (by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf10]
  obtain ⟨nf12, hnf12, hfv12⟩ := stepOut_sound (ch 12) st.f12 (W 2) [W 2, W 1]
    (hst 12) (hsv.1 2 (by decide)) (by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf12]
  obtain ⟨nf14, hnf14, hfv14⟩ := stepOut_sound (ch 14) st.f14 (W 2) [W 2, W 1]
    (hst 14) (hsv.1 2 (by decide)) (by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf14]
  obtain ⟨nf15, hnf15, hfv15⟩ := stepOut_sound (ch 15) st.f15 (W 2) [W 2]
    (hst 15) (hsv.1 2 (by decide)) (by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf15]
  refine ⟨⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩, rfl, fun k => by fin_cases k <;> assumption⟩

lemma stepF16_3_sound (st : F16) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hst : ∀ k : Fin 16, ForbValid (st.get k) (ch k))
    (hsv : StepValid 3 W ch) :
    ∃ st', stepF16_3 st (W 1) (W 2) (W 3) = some st' ∧ ∀ k : Fin 16, ForbValid (st'.get k) (ch k) := by
  unfold stepF16_3
  have hfast2 : (st.f2.get (W 3).l1 && st.f2.get (W 3).l2) = false :=
    not_both_forb (hst 2) (by have := hsv.2 2 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast4 : (st.f4.get (W 3).l1 && st.f4.get (W 3).l2) = false :=
    not_both_forb (hst 4) (by have := hsv.2 4 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast5 : (st.f5.get (W 3).l1 && st.f5.get (W 3).l2) = false :=
    not_both_forb (hst 5) (by have := hsv.2 5 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast6 : (st.f6.get (W 3).l1 && st.f6.get (W 3).l2) = false :=
    not_both_forb (hst 6) (by have := hsv.2 6 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast7 : (st.f7.get (W 3).l1 && st.f7.get (W 3).l2) = false :=
    not_both_forb (hst 7) (by have := hsv.2 7 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast8 : (st.f8.get (W 3).l1 && st.f8.get (W 3).l2) = false :=
    not_both_forb (hst 8) (by have := hsv.2 8 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast9 : (st.f9.get (W 3).l1 && st.f9.get (W 3).l2) = false :=
    not_both_forb (hst 9) (by have := hsv.2 9 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast10 : (st.f10.get (W 3).l1 && st.f10.get (W 3).l2) = false :=
    not_both_forb (hst 10) (by have := hsv.2 10 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast11 : (st.f11.get (W 3).l1 && st.f11.get (W 3).l2) = false :=
    not_both_forb (hst 11) (by have := hsv.2 11 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast14 : (st.f14.get (W 3).l1 && st.f14.get (W 3).l2) = false :=
    not_both_forb (hst 14) (by have := hsv.2 14 3 (by decide) (by decide); simpa [rows9] using this)
  have hfast15 : (st.f15.get (W 3).l1 && st.f15.get (W 3).l2) = false :=
    not_both_forb (hst 15) (by have := hsv.2 15 3 (by decide) (by decide); simpa [rows9] using this)
  simp only [hfast2, hfast4, hfast5, hfast6, hfast7, hfast8, hfast9, hfast10, hfast11, hfast14, hfast15, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨nf0, hnf0, hfv0⟩ := stepIn_sound (ch 0) st.f0 (W 3) [W 2, W 1]
    (hst 0) (hsv.1 3 (by decide)) (by have := hsv.2 0 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf0]
  obtain ⟨nf1, hnf1, hfv1⟩ := stepIn_sound (ch 1) st.f1 (W 3) [W 1]
    (hst 1) (hsv.1 3 (by decide)) (by have := hsv.2 1 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf1]
  obtain ⟨nf3, hnf3, hfv3⟩ := stepIn_sound (ch 3) st.f3 (W 3) [W 2, W 1]
    (hst 3) (hsv.1 3 (by decide)) (by have := hsv.2 3 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf3]
  obtain ⟨nf12, hnf12, hfv12⟩ := stepIn_sound (ch 12) st.f12 (W 3) [W 2, W 1]
    (hst 12) (hsv.1 3 (by decide)) (by have := hsv.2 12 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf12]
  obtain ⟨nf13, hnf13, hfv13⟩ := stepIn_sound (ch 13) st.f13 (W 3) [W 1]
    (hst 13) (hsv.1 3 (by decide)) (by have := hsv.2 13 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf13]
  obtain ⟨nf2, hnf2, hfv2⟩ := stepOut_sound (ch 2) st.f2 (W 3) [W 3, W 2, W 1]
    (hst 2) (hsv.1 3 (by decide)) (by have := hsv.2 2 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 2 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf2]
  obtain ⟨nf4, hnf4, hfv4⟩ := stepOut_sound (ch 4) st.f4 (W 3) [W 3, W 2, W 1]
    (hst 4) (hsv.1 3 (by decide)) (by have := hsv.2 4 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 4 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf4]
  obtain ⟨nf5, hnf5, hfv5⟩ := stepOut_sound (ch 5) st.f5 (W 3) [W 3, W 2]
    (hst 5) (hsv.1 3 (by decide)) (by have := hsv.2 5 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 5 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf5]
  obtain ⟨nf6, hnf6, hfv6⟩ := stepOut_sound (ch 6) st.f6 (W 3) [W 3]
    (hst 6) (hsv.1 3 (by decide)) (by have := hsv.2 6 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 6 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf6]
  obtain ⟨nf7, hnf7, hfv7⟩ := stepOut_sound (ch 7) st.f7 (W 3) [W 3, W 2, W 1]
    (hst 7) (hsv.1 3 (by decide)) (by have := hsv.2 7 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 7 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf7]
  obtain ⟨nf8, hnf8, hfv8⟩ := stepOut_sound (ch 8) st.f8 (W 3) [W 3, W 1]
    (hst 8) (hsv.1 3 (by decide)) (by have := hsv.2 8 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 8 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf8]
  obtain ⟨nf9, hnf9, hfv9⟩ := stepOut_sound (ch 9) st.f9 (W 3) [W 3, W 2, W 1]
    (hst 9) (hsv.1 3 (by decide)) (by have := hsv.2 9 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 9 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf9]
  obtain ⟨nf10, hnf10, hfv10⟩ := stepOut_sound (ch 10) st.f10 (W 3) [W 3, W 2]
    (hst 10) (hsv.1 3 (by decide)) (by have := hsv.2 10 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 10 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf10]
  obtain ⟨nf11, hnf11, hfv11⟩ := stepOut_sound (ch 11) st.f11 (W 3) [W 3]
    (hst 11) (hsv.1 3 (by decide)) (by have := hsv.2 11 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 11 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf11]
  obtain ⟨nf14, hnf14, hfv14⟩ := stepOut_sound (ch 14) st.f14 (W 3) [W 3, W 2, W 1]
    (hst 14) (hsv.1 3 (by decide)) (by have := hsv.2 14 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 14 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf14]
  obtain ⟨nf15, hnf15, hfv15⟩ := stepOut_sound (ch 15) st.f15 (W 3) [W 3, W 2]
    (hst 15) (hsv.1 3 (by decide)) (by have := hsv.2 15 3 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 15 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf15]
  refine ⟨⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩, rfl, fun k => by fin_cases k <;> assumption⟩

lemma stepF16_4_sound (st : F16) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hst : ∀ k : Fin 16, ForbValid (st.get k) (ch k))
    (hsv : StepValid 4 W ch) :
    ∃ st', stepF16_4 st (W 1) (W 2) (W 3) (W 4) = some st' ∧ ∀ k : Fin 16, ForbValid (st'.get k) (ch k) := by
  unfold stepF16_4
  have hfast3 : (st.f3.get (W 4).l1 && st.f3.get (W 4).l2) = false :=
    not_both_forb (hst 3) (by have := hsv.2 3 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast4 : (st.f4.get (W 4).l1 && st.f4.get (W 4).l2) = false :=
    not_both_forb (hst 4) (by have := hsv.2 4 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast5 : (st.f5.get (W 4).l1 && st.f5.get (W 4).l2) = false :=
    not_both_forb (hst 5) (by have := hsv.2 5 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast6 : (st.f6.get (W 4).l1 && st.f6.get (W 4).l2) = false :=
    not_both_forb (hst 6) (by have := hsv.2 6 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast9 : (st.f9.get (W 4).l1 && st.f9.get (W 4).l2) = false :=
    not_both_forb (hst 9) (by have := hsv.2 9 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast10 : (st.f10.get (W 4).l1 && st.f10.get (W 4).l2) = false :=
    not_both_forb (hst 10) (by have := hsv.2 10 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast11 : (st.f11.get (W 4).l1 && st.f11.get (W 4).l2) = false :=
    not_both_forb (hst 11) (by have := hsv.2 11 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast12 : (st.f12.get (W 4).l1 && st.f12.get (W 4).l2) = false :=
    not_both_forb (hst 12) (by have := hsv.2 12 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast13 : (st.f13.get (W 4).l1 && st.f13.get (W 4).l2) = false :=
    not_both_forb (hst 13) (by have := hsv.2 13 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast14 : (st.f14.get (W 4).l1 && st.f14.get (W 4).l2) = false :=
    not_both_forb (hst 14) (by have := hsv.2 14 4 (by decide) (by decide); simpa [rows9] using this)
  have hfast15 : (st.f15.get (W 4).l1 && st.f15.get (W 4).l2) = false :=
    not_both_forb (hst 15) (by have := hsv.2 15 4 (by decide) (by decide); simpa [rows9] using this)
  simp only [hfast3, hfast4, hfast5, hfast6, hfast9, hfast10, hfast11, hfast12, hfast13, hfast14, hfast15, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨nf0, hnf0, hfv0⟩ := stepIn_sound (ch 0) st.f0 (W 4) [W 2, W 1]
    (hst 0) (hsv.1 4 (by decide)) (by have := hsv.2 0 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf0]
  obtain ⟨nf1, hnf1, hfv1⟩ := stepIn_sound (ch 1) st.f1 (W 4) [W 1]
    (hst 1) (hsv.1 4 (by decide)) (by have := hsv.2 1 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf1]
  obtain ⟨nf2, hnf2, hfv2⟩ := stepIn_sound (ch 2) st.f2 (W 4) [W 3, W 2, W 1]
    (hst 2) (hsv.1 4 (by decide)) (by have := hsv.2 2 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 2 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf2]
  obtain ⟨nf7, hnf7, hfv7⟩ := stepIn_sound (ch 7) st.f7 (W 4) [W 3, W 2, W 1]
    (hst 7) (hsv.1 4 (by decide)) (by have := hsv.2 7 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 7 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf7]
  obtain ⟨nf8, hnf8, hfv8⟩ := stepIn_sound (ch 8) st.f8 (W 4) [W 3, W 1]
    (hst 8) (hsv.1 4 (by decide)) (by have := hsv.2 8 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 8 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf8]
  obtain ⟨nf3, hnf3, hfv3⟩ := stepOut_sound (ch 3) st.f3 (W 4) [W 4, W 2, W 1]
    (hst 3) (hsv.1 4 (by decide)) (by have := hsv.2 3 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 3 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf3]
  obtain ⟨nf4, hnf4, hfv4⟩ := stepOut_sound (ch 4) st.f4 (W 4) [W 4, W 3, W 2, W 1]
    (hst 4) (hsv.1 4 (by decide)) (by have := hsv.2 4 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 4 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 4 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf4]
  obtain ⟨nf5, hnf5, hfv5⟩ := stepOut_sound (ch 5) st.f5 (W 4) [W 4, W 3, W 2]
    (hst 5) (hsv.1 4 (by decide)) (by have := hsv.2 5 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 5 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 5 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf5]
  obtain ⟨nf6, hnf6, hfv6⟩ := stepOut_sound (ch 6) st.f6 (W 4) [W 4, W 3]
    (hst 6) (hsv.1 4 (by decide)) (by have := hsv.2 6 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 6 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 6 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf6]
  obtain ⟨nf9, hnf9, hfv9⟩ := stepOut_sound (ch 9) st.f9 (W 4) [W 4, W 3, W 2, W 1]
    (hst 9) (hsv.1 4 (by decide)) (by have := hsv.2 9 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 9 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 9 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf9]
  obtain ⟨nf10, hnf10, hfv10⟩ := stepOut_sound (ch 10) st.f10 (W 4) [W 4, W 3, W 2]
    (hst 10) (hsv.1 4 (by decide)) (by have := hsv.2 10 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 10 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 10 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf10]
  obtain ⟨nf11, hnf11, hfv11⟩ := stepOut_sound (ch 11) st.f11 (W 4) [W 4, W 3]
    (hst 11) (hsv.1 4 (by decide)) (by have := hsv.2 11 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 11 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 11 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf11]
  obtain ⟨nf12, hnf12, hfv12⟩ := stepOut_sound (ch 12) st.f12 (W 4) [W 4, W 2, W 1]
    (hst 12) (hsv.1 4 (by decide)) (by have := hsv.2 12 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 12 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf12]
  obtain ⟨nf13, hnf13, hfv13⟩ := stepOut_sound (ch 13) st.f13 (W 4) [W 4, W 1]
    (hst 13) (hsv.1 4 (by decide)) (by have := hsv.2 13 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 13 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf13]
  obtain ⟨nf14, hnf14, hfv14⟩ := stepOut_sound (ch 14) st.f14 (W 4) [W 4, W 3, W 2, W 1]
    (hst 14) (hsv.1 4 (by decide)) (by have := hsv.2 14 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 14 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 14 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf14]
  obtain ⟨nf15, hnf15, hfv15⟩ := stepOut_sound (ch 15) st.f15 (W 4) [W 4, W 3, W 2]
    (hst 15) (hsv.1 4 (by decide)) (by have := hsv.2 15 4 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 15 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 15 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf15]
  refine ⟨⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩, rfl, fun k => by fin_cases k <;> assumption⟩

lemma stepF16_5_sound (st : F16) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hst : ∀ k : Fin 16, ForbValid (st.get k) (ch k))
    (hsv : StepValid 5 W ch) :
    ∃ st', stepF16_5 st (W 1) (W 2) (W 3) (W 4) (W 5) = some st' ∧ ∀ k : Fin 16, ForbValid (st'.get k) (ch k) := by
  unfold stepF16_5
  have hfast0 : (st.f0.get (W 5).l1 && st.f0.get (W 5).l2) = false :=
    not_both_forb (hst 0) (by have := hsv.2 0 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast1 : (st.f1.get (W 5).l1 && st.f1.get (W 5).l2) = false :=
    not_both_forb (hst 1) (by have := hsv.2 1 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast3 : (st.f3.get (W 5).l1 && st.f3.get (W 5).l2) = false :=
    not_both_forb (hst 3) (by have := hsv.2 3 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast6 : (st.f6.get (W 5).l1 && st.f6.get (W 5).l2) = false :=
    not_both_forb (hst 6) (by have := hsv.2 6 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast7 : (st.f7.get (W 5).l1 && st.f7.get (W 5).l2) = false :=
    not_both_forb (hst 7) (by have := hsv.2 7 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast8 : (st.f8.get (W 5).l1 && st.f8.get (W 5).l2) = false :=
    not_both_forb (hst 8) (by have := hsv.2 8 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast9 : (st.f9.get (W 5).l1 && st.f9.get (W 5).l2) = false :=
    not_both_forb (hst 9) (by have := hsv.2 9 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast10 : (st.f10.get (W 5).l1 && st.f10.get (W 5).l2) = false :=
    not_both_forb (hst 10) (by have := hsv.2 10 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast11 : (st.f11.get (W 5).l1 && st.f11.get (W 5).l2) = false :=
    not_both_forb (hst 11) (by have := hsv.2 11 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast12 : (st.f12.get (W 5).l1 && st.f12.get (W 5).l2) = false :=
    not_both_forb (hst 12) (by have := hsv.2 12 5 (by decide) (by decide); simpa [rows9] using this)
  have hfast13 : (st.f13.get (W 5).l1 && st.f13.get (W 5).l2) = false :=
    not_both_forb (hst 13) (by have := hsv.2 13 5 (by decide) (by decide); simpa [rows9] using this)
  simp only [hfast0, hfast1, hfast3, hfast6, hfast7, hfast8, hfast9, hfast10, hfast11, hfast12, hfast13, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨nf2, hnf2, hfv2⟩ := stepIn_sound (ch 2) st.f2 (W 5) [W 3, W 2, W 1]
    (hst 2) (hsv.1 5 (by decide)) (by have := hsv.2 2 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 2 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf2]
  obtain ⟨nf4, hnf4, hfv4⟩ := stepIn_sound (ch 4) st.f4 (W 5) [W 4, W 3, W 2, W 1]
    (hst 4) (hsv.1 5 (by decide)) (by have := hsv.2 4 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 4 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 4 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf4]
  obtain ⟨nf5, hnf5, hfv5⟩ := stepIn_sound (ch 5) st.f5 (W 5) [W 4, W 3, W 2]
    (hst 5) (hsv.1 5 (by decide)) (by have := hsv.2 5 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 5 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 5 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf5]
  obtain ⟨nf14, hnf14, hfv14⟩ := stepIn_sound (ch 14) st.f14 (W 5) [W 4, W 3, W 2, W 1]
    (hst 14) (hsv.1 5 (by decide)) (by have := hsv.2 14 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 14 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 14 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf14]
  obtain ⟨nf15, hnf15, hfv15⟩ := stepIn_sound (ch 15) st.f15 (W 5) [W 4, W 3, W 2]
    (hst 15) (hsv.1 5 (by decide)) (by have := hsv.2 15 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 15 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 15 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf15]
  obtain ⟨nf0, hnf0, hfv0⟩ := stepOut_sound (ch 0) st.f0 (W 5) [W 5, W 2, W 1]
    (hst 0) (hsv.1 5 (by decide)) (by have := hsv.2 0 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 0 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf0]
  obtain ⟨nf1, hnf1, hfv1⟩ := stepOut_sound (ch 1) st.f1 (W 5) [W 5, W 1]
    (hst 1) (hsv.1 5 (by decide)) (by have := hsv.2 1 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 1 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf1]
  obtain ⟨nf3, hnf3, hfv3⟩ := stepOut_sound (ch 3) st.f3 (W 5) [W 5, W 4, W 2, W 1]
    (hst 3) (hsv.1 5 (by decide)) (by have := hsv.2 3 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 3 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 3 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf3]
  obtain ⟨nf6, hnf6, hfv6⟩ := stepOut_sound (ch 6) st.f6 (W 5) [W 5, W 4, W 3]
    (hst 6) (hsv.1 5 (by decide)) (by have := hsv.2 6 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 6 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 6 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 6 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf6]
  obtain ⟨nf7, hnf7, hfv7⟩ := stepOut_sound (ch 7) st.f7 (W 5) [W 5, W 3, W 2, W 1]
    (hst 7) (hsv.1 5 (by decide)) (by have := hsv.2 7 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 7 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 7 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf7]
  obtain ⟨nf8, hnf8, hfv8⟩ := stepOut_sound (ch 8) st.f8 (W 5) [W 5, W 3, W 1]
    (hst 8) (hsv.1 5 (by decide)) (by have := hsv.2 8 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 8 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 8 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf8]
  obtain ⟨nf9, hnf9, hfv9⟩ := stepOut_sound (ch 9) st.f9 (W 5) [W 5, W 4, W 3, W 2, W 1]
    (hst 9) (hsv.1 5 (by decide)) (by have := hsv.2 9 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 9 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 9 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 9 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf9]
  obtain ⟨nf10, hnf10, hfv10⟩ := stepOut_sound (ch 10) st.f10 (W 5) [W 5, W 4, W 3, W 2]
    (hst 10) (hsv.1 5 (by decide)) (by have := hsv.2 10 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 10 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 10 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 10 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf10]
  obtain ⟨nf11, hnf11, hfv11⟩ := stepOut_sound (ch 11) st.f11 (W 5) [W 5, W 4, W 3]
    (hst 11) (hsv.1 5 (by decide)) (by have := hsv.2 11 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 11 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 11 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 11 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf11]
  obtain ⟨nf12, hnf12, hfv12⟩ := stepOut_sound (ch 12) st.f12 (W 5) [W 5, W 4, W 2, W 1]
    (hst 12) (hsv.1 5 (by decide)) (by have := hsv.2 12 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 12 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 12 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf12]
  obtain ⟨nf13, hnf13, hfv13⟩ := stepOut_sound (ch 13) st.f13 (W 5) [W 5, W 4, W 1]
    (hst 13) (hsv.1 5 (by decide)) (by have := hsv.2 13 5 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 13 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 13 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf13]
  refine ⟨⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩, rfl, fun k => by fin_cases k <;> assumption⟩

lemma stepF16_6_sound (st : F16) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hst : ∀ k : Fin 16, ForbValid (st.get k) (ch k))
    (hsv : StepValid 6 W ch) :
    ∃ st', stepF16_6 st (W 1) (W 2) (W 3) (W 4) (W 5) (W 6) = some st' ∧ ∀ k : Fin 16, ForbValid (st'.get k) (ch k) := by
  unfold stepF16_6
  have hfast0 : (st.f0.get (W 6).l1 && st.f0.get (W 6).l2) = false :=
    not_both_forb (hst 0) (by have := hsv.2 0 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast1 : (st.f1.get (W 6).l1 && st.f1.get (W 6).l2) = false :=
    not_both_forb (hst 1) (by have := hsv.2 1 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast2 : (st.f2.get (W 6).l1 && st.f2.get (W 6).l2) = false :=
    not_both_forb (hst 2) (by have := hsv.2 2 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast6 : (st.f6.get (W 6).l1 && st.f6.get (W 6).l2) = false :=
    not_both_forb (hst 6) (by have := hsv.2 6 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast7 : (st.f7.get (W 6).l1 && st.f7.get (W 6).l2) = false :=
    not_both_forb (hst 7) (by have := hsv.2 7 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast8 : (st.f8.get (W 6).l1 && st.f8.get (W 6).l2) = false :=
    not_both_forb (hst 8) (by have := hsv.2 8 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast11 : (st.f11.get (W 6).l1 && st.f11.get (W 6).l2) = false :=
    not_both_forb (hst 11) (by have := hsv.2 11 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast12 : (st.f12.get (W 6).l1 && st.f12.get (W 6).l2) = false :=
    not_both_forb (hst 12) (by have := hsv.2 12 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast13 : (st.f13.get (W 6).l1 && st.f13.get (W 6).l2) = false :=
    not_both_forb (hst 13) (by have := hsv.2 13 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast14 : (st.f14.get (W 6).l1 && st.f14.get (W 6).l2) = false :=
    not_both_forb (hst 14) (by have := hsv.2 14 6 (by decide) (by decide); simpa [rows9] using this)
  have hfast15 : (st.f15.get (W 6).l1 && st.f15.get (W 6).l2) = false :=
    not_both_forb (hst 15) (by have := hsv.2 15 6 (by decide) (by decide); simpa [rows9] using this)
  simp only [hfast0, hfast1, hfast2, hfast6, hfast7, hfast8, hfast11, hfast12, hfast13, hfast14, hfast15, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨nf3, hnf3, hfv3⟩ := stepIn_sound (ch 3) st.f3 (W 6) [W 5, W 4, W 2, W 1]
    (hst 3) (hsv.1 6 (by decide)) (by have := hsv.2 3 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 3 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 3 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf3]
  obtain ⟨nf4, hnf4, hfv4⟩ := stepIn_sound (ch 4) st.f4 (W 6) [W 4, W 3, W 2, W 1]
    (hst 4) (hsv.1 6 (by decide)) (by have := hsv.2 4 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 4 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 4 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf4]
  obtain ⟨nf5, hnf5, hfv5⟩ := stepIn_sound (ch 5) st.f5 (W 6) [W 4, W 3, W 2]
    (hst 5) (hsv.1 6 (by decide)) (by have := hsv.2 5 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 5 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 5 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf5]
  obtain ⟨nf9, hnf9, hfv9⟩ := stepIn_sound (ch 9) st.f9 (W 6) [W 5, W 4, W 3, W 2, W 1]
    (hst 9) (hsv.1 6 (by decide)) (by have := hsv.2 9 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 9 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 9 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 9 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf9]
  obtain ⟨nf10, hnf10, hfv10⟩ := stepIn_sound (ch 10) st.f10 (W 6) [W 5, W 4, W 3, W 2]
    (hst 10) (hsv.1 6 (by decide)) (by have := hsv.2 10 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 10 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 10 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 10 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf10]
  obtain ⟨nf0, hnf0, hfv0⟩ := stepOut_sound (ch 0) st.f0 (W 6) [W 6, W 5, W 2, W 1]
    (hst 0) (hsv.1 6 (by decide)) (by have := hsv.2 0 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 0 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 0 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf0]
  obtain ⟨nf1, hnf1, hfv1⟩ := stepOut_sound (ch 1) st.f1 (W 6) [W 6, W 5, W 1]
    (hst 1) (hsv.1 6 (by decide)) (by have := hsv.2 1 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 1 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 1 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf1]
  obtain ⟨nf2, hnf2, hfv2⟩ := stepOut_sound (ch 2) st.f2 (W 6) [W 6, W 3, W 2, W 1]
    (hst 2) (hsv.1 6 (by decide)) (by have := hsv.2 2 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 2 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 2 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf2]
  obtain ⟨nf6, hnf6, hfv6⟩ := stepOut_sound (ch 6) st.f6 (W 6) [W 6, W 5, W 4, W 3]
    (hst 6) (hsv.1 6 (by decide)) (by have := hsv.2 6 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 6 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 6 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 6 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 6 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf6]
  obtain ⟨nf7, hnf7, hfv7⟩ := stepOut_sound (ch 7) st.f7 (W 6) [W 6, W 5, W 3, W 2, W 1]
    (hst 7) (hsv.1 6 (by decide)) (by have := hsv.2 7 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 7 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 7 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 7 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf7]
  obtain ⟨nf8, hnf8, hfv8⟩ := stepOut_sound (ch 8) st.f8 (W 6) [W 6, W 5, W 3, W 1]
    (hst 8) (hsv.1 6 (by decide)) (by have := hsv.2 8 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 8 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 8 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 8 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf8]
  obtain ⟨nf11, hnf11, hfv11⟩ := stepOut_sound (ch 11) st.f11 (W 6) [W 6, W 5, W 4, W 3]
    (hst 11) (hsv.1 6 (by decide)) (by have := hsv.2 11 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 11 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 11 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 11 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 11 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf11]
  obtain ⟨nf12, hnf12, hfv12⟩ := stepOut_sound (ch 12) st.f12 (W 6) [W 6, W 5, W 4, W 2, W 1]
    (hst 12) (hsv.1 6 (by decide)) (by have := hsv.2 12 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 12 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 12 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 12 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf12]
  obtain ⟨nf13, hnf13, hfv13⟩ := stepOut_sound (ch 13) st.f13 (W 6) [W 6, W 5, W 4, W 1]
    (hst 13) (hsv.1 6 (by decide)) (by have := hsv.2 13 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 13 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 13 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 13 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf13]
  obtain ⟨nf14, hnf14, hfv14⟩ := stepOut_sound (ch 14) st.f14 (W 6) [W 6, W 4, W 3, W 2, W 1]
    (hst 14) (hsv.1 6 (by decide)) (by have := hsv.2 14 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 14 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 14 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 14 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf14]
  obtain ⟨nf15, hnf15, hfv15⟩ := stepOut_sound (ch 15) st.f15 (W 6) [W 6, W 4, W 3, W 2]
    (hst 15) (hsv.1 6 (by decide)) (by have := hsv.2 15 6 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 15 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 15 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 15 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf15]
  refine ⟨⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩, rfl, fun k => by fin_cases k <;> assumption⟩

lemma stepF16_7_sound (st : F16) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hst : ∀ k : Fin 16, ForbValid (st.get k) (ch k))
    (hsv : StepValid 7 W ch) :
    ∃ st', stepF16_7 st (W 1) (W 2) (W 3) (W 4) (W 5) (W 6) (W 7) = some st' ∧ ∀ k : Fin 16, ForbValid (st'.get k) (ch k) := by
  unfold stepF16_7
  have hfast0 : (st.f0.get (W 7).l1 && st.f0.get (W 7).l2) = false :=
    not_both_forb (hst 0) (by have := hsv.2 0 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast1 : (st.f1.get (W 7).l1 && st.f1.get (W 7).l2) = false :=
    not_both_forb (hst 1) (by have := hsv.2 1 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast2 : (st.f2.get (W 7).l1 && st.f2.get (W 7).l2) = false :=
    not_both_forb (hst 2) (by have := hsv.2 2 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast3 : (st.f3.get (W 7).l1 && st.f3.get (W 7).l2) = false :=
    not_both_forb (hst 3) (by have := hsv.2 3 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast4 : (st.f4.get (W 7).l1 && st.f4.get (W 7).l2) = false :=
    not_both_forb (hst 4) (by have := hsv.2 4 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast5 : (st.f5.get (W 7).l1 && st.f5.get (W 7).l2) = false :=
    not_both_forb (hst 5) (by have := hsv.2 5 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast11 : (st.f11.get (W 7).l1 && st.f11.get (W 7).l2) = false :=
    not_both_forb (hst 11) (by have := hsv.2 11 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast12 : (st.f12.get (W 7).l1 && st.f12.get (W 7).l2) = false :=
    not_both_forb (hst 12) (by have := hsv.2 12 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast13 : (st.f13.get (W 7).l1 && st.f13.get (W 7).l2) = false :=
    not_both_forb (hst 13) (by have := hsv.2 13 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast14 : (st.f14.get (W 7).l1 && st.f14.get (W 7).l2) = false :=
    not_both_forb (hst 14) (by have := hsv.2 14 7 (by decide) (by decide); simpa [rows9] using this)
  have hfast15 : (st.f15.get (W 7).l1 && st.f15.get (W 7).l2) = false :=
    not_both_forb (hst 15) (by have := hsv.2 15 7 (by decide) (by decide); simpa [rows9] using this)
  simp only [hfast0, hfast1, hfast2, hfast3, hfast4, hfast5, hfast11, hfast12, hfast13, hfast14, hfast15, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨nf6, hnf6, hfv6⟩ := stepIn_sound (ch 6) st.f6 (W 7) [W 6, W 5, W 4, W 3]
    (hst 6) (hsv.1 7 (by decide)) (by have := hsv.2 6 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 6 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 6 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 6 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 6 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf6]
  obtain ⟨nf7, hnf7, hfv7⟩ := stepIn_sound (ch 7) st.f7 (W 7) [W 6, W 5, W 3, W 2, W 1]
    (hst 7) (hsv.1 7 (by decide)) (by have := hsv.2 7 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 7 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 7 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 7 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf7]
  obtain ⟨nf8, hnf8, hfv8⟩ := stepIn_sound (ch 8) st.f8 (W 7) [W 6, W 5, W 3, W 1]
    (hst 8) (hsv.1 7 (by decide)) (by have := hsv.2 8 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 8 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 8 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 8 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf8]
  obtain ⟨nf9, hnf9, hfv9⟩ := stepIn_sound (ch 9) st.f9 (W 7) [W 5, W 4, W 3, W 2, W 1]
    (hst 9) (hsv.1 7 (by decide)) (by have := hsv.2 9 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 9 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 9 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 9 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf9]
  obtain ⟨nf10, hnf10, hfv10⟩ := stepIn_sound (ch 10) st.f10 (W 7) [W 5, W 4, W 3, W 2]
    (hst 10) (hsv.1 7 (by decide)) (by have := hsv.2 10 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 10 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 10 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 10 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf10]
  obtain ⟨nf0, hnf0, hfv0⟩ := stepOut_sound (ch 0) st.f0 (W 7) [W 7, W 6, W 5, W 2, W 1]
    (hst 0) (hsv.1 7 (by decide)) (by have := hsv.2 0 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 0 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 0 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 0 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf0]
  obtain ⟨nf1, hnf1, hfv1⟩ := stepOut_sound (ch 1) st.f1 (W 7) [W 7, W 6, W 5, W 1]
    (hst 1) (hsv.1 7 (by decide)) (by have := hsv.2 1 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 1 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 1 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 1 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf1]
  obtain ⟨nf2, hnf2, hfv2⟩ := stepOut_sound (ch 2) st.f2 (W 7) [W 7, W 6, W 3, W 2, W 1]
    (hst 2) (hsv.1 7 (by decide)) (by have := hsv.2 2 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 2 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 2 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 2 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf2]
  obtain ⟨nf3, hnf3, hfv3⟩ := stepOut_sound (ch 3) st.f3 (W 7) [W 7, W 5, W 4, W 2, W 1]
    (hst 3) (hsv.1 7 (by decide)) (by have := hsv.2 3 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 3 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 3 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 3 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf3]
  obtain ⟨nf4, hnf4, hfv4⟩ := stepOut_sound (ch 4) st.f4 (W 7) [W 7, W 4, W 3, W 2, W 1]
    (hst 4) (hsv.1 7 (by decide)) (by have := hsv.2 4 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 4 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 4 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 4 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf4]
  obtain ⟨nf5, hnf5, hfv5⟩ := stepOut_sound (ch 5) st.f5 (W 7) [W 7, W 4, W 3, W 2]
    (hst 5) (hsv.1 7 (by decide)) (by have := hsv.2 5 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 5 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 5 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 5 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf5]
  obtain ⟨nf11, hnf11, hfv11⟩ := stepOut_sound (ch 11) st.f11 (W 7) [W 7, W 6, W 5, W 4, W 3]
    (hst 11) (hsv.1 7 (by decide)) (by have := hsv.2 11 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 11 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 11 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 11 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 11 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 11 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf11]
  obtain ⟨nf12, hnf12, hfv12⟩ := stepOut_sound (ch 12) st.f12 (W 7) [W 7, W 6, W 5, W 4, W 2, W 1]
    (hst 12) (hsv.1 7 (by decide)) (by have := hsv.2 12 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 12 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 12 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 12 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 12 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf12]
  obtain ⟨nf13, hnf13, hfv13⟩ := stepOut_sound (ch 13) st.f13 (W 7) [W 7, W 6, W 5, W 4, W 1]
    (hst 13) (hsv.1 7 (by decide)) (by have := hsv.2 13 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 13 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 13 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 13 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 13 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf13]
  obtain ⟨nf14, hnf14, hfv14⟩ := stepOut_sound (ch 14) st.f14 (W 7) [W 7, W 6, W 4, W 3, W 2, W 1]
    (hst 14) (hsv.1 7 (by decide)) (by have := hsv.2 14 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 14 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 14 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 14 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 14 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf14]
  obtain ⟨nf15, hnf15, hfv15⟩ := stepOut_sound (ch 15) st.f15 (W 7) [W 7, W 6, W 4, W 3, W 2]
    (hst 15) (hsv.1 7 (by decide)) (by have := hsv.2 15 7 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 15 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 15 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 15 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 15 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf15]
  refine ⟨⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩, rfl, fun k => by fin_cases k <;> assumption⟩

lemma stepF16_8_sound (st : F16) (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hst : ∀ k : Fin 16, ForbValid (st.get k) (ch k))
    (hsv : StepValid 8 W ch) :
    ∃ st', stepF16_8 st (W 1) (W 2) (W 3) (W 4) (W 5) (W 6) (W 7) (W 8) = some st' ∧ ∀ k : Fin 16, ForbValid (st'.get k) (ch k) := by
  unfold stepF16_8
  have hfast0 : (st.f0.get (W 8).l1 && st.f0.get (W 8).l2) = false :=
    not_both_forb (hst 0) (by have := hsv.2 0 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast1 : (st.f1.get (W 8).l1 && st.f1.get (W 8).l2) = false :=
    not_both_forb (hst 1) (by have := hsv.2 1 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast2 : (st.f2.get (W 8).l1 && st.f2.get (W 8).l2) = false :=
    not_both_forb (hst 2) (by have := hsv.2 2 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast3 : (st.f3.get (W 8).l1 && st.f3.get (W 8).l2) = false :=
    not_both_forb (hst 3) (by have := hsv.2 3 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast4 : (st.f4.get (W 8).l1 && st.f4.get (W 8).l2) = false :=
    not_both_forb (hst 4) (by have := hsv.2 4 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast5 : (st.f5.get (W 8).l1 && st.f5.get (W 8).l2) = false :=
    not_both_forb (hst 5) (by have := hsv.2 5 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast6 : (st.f6.get (W 8).l1 && st.f6.get (W 8).l2) = false :=
    not_both_forb (hst 6) (by have := hsv.2 6 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast7 : (st.f7.get (W 8).l1 && st.f7.get (W 8).l2) = false :=
    not_both_forb (hst 7) (by have := hsv.2 7 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast8 : (st.f8.get (W 8).l1 && st.f8.get (W 8).l2) = false :=
    not_both_forb (hst 8) (by have := hsv.2 8 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast9 : (st.f9.get (W 8).l1 && st.f9.get (W 8).l2) = false :=
    not_both_forb (hst 9) (by have := hsv.2 9 8 (by decide) (by decide); simpa [rows9] using this)
  have hfast10 : (st.f10.get (W 8).l1 && st.f10.get (W 8).l2) = false :=
    not_both_forb (hst 10) (by have := hsv.2 10 8 (by decide) (by decide); simpa [rows9] using this)
  simp only [hfast0, hfast1, hfast2, hfast3, hfast4, hfast5, hfast6, hfast7, hfast8, hfast9, hfast10, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨nf11, hnf11, hfv11⟩ := stepIn_sound (ch 11) st.f11 (W 8) [W 7, W 6, W 5, W 4, W 3]
    (hst 11) (hsv.1 8 (by decide)) (by have := hsv.2 11 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 11 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 11 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 11 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 11 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 11 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf11]
  obtain ⟨nf12, hnf12, hfv12⟩ := stepIn_sound (ch 12) st.f12 (W 8) [W 7, W 6, W 5, W 4, W 2, W 1]
    (hst 12) (hsv.1 8 (by decide)) (by have := hsv.2 12 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 12 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 12 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 12 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 12 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 12 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 12 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf12]
  obtain ⟨nf13, hnf13, hfv13⟩ := stepIn_sound (ch 13) st.f13 (W 8) [W 7, W 6, W 5, W 4, W 1]
    (hst 13) (hsv.1 8 (by decide)) (by have := hsv.2 13 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 13 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 13 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 13 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 13 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 13 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf13]
  obtain ⟨nf14, hnf14, hfv14⟩ := stepIn_sound (ch 14) st.f14 (W 8) [W 7, W 6, W 4, W 3, W 2, W 1]
    (hst 14) (hsv.1 8 (by decide)) (by have := hsv.2 14 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 14 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 14 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 14 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 14 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 14 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 14 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf14]
  obtain ⟨nf15, hnf15, hfv15⟩ := stepIn_sound (ch 15) st.f15 (W 8) [W 7, W 6, W 4, W 3, W 2]
    (hst 15) (hsv.1 8 (by decide)) (by have := hsv.2 15 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 15 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 15 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 15 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 15 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 15 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf15]
  obtain ⟨nf0, hnf0, hfv0⟩ := stepOut_sound (ch 0) st.f0 (W 8) [W 8, W 7, W 6, W 5, W 2, W 1]
    (hst 0) (hsv.1 8 (by decide)) (by have := hsv.2 0 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 0 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 0 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 0 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 0 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 0 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 0 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf0]
  obtain ⟨nf1, hnf1, hfv1⟩ := stepOut_sound (ch 1) st.f1 (W 8) [W 8, W 7, W 6, W 5, W 1]
    (hst 1) (hsv.1 8 (by decide)) (by have := hsv.2 1 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 1 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 1 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 1 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 1 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 1 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf1]
  obtain ⟨nf2, hnf2, hfv2⟩ := stepOut_sound (ch 2) st.f2 (W 8) [W 8, W 7, W 6, W 3, W 2, W 1]
    (hst 2) (hsv.1 8 (by decide)) (by have := hsv.2 2 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 2 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 2 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 2 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 2 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 2 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 2 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf2]
  obtain ⟨nf3, hnf3, hfv3⟩ := stepOut_sound (ch 3) st.f3 (W 8) [W 8, W 7, W 5, W 4, W 2, W 1]
    (hst 3) (hsv.1 8 (by decide)) (by have := hsv.2 3 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 3 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 3 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 3 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 3 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 3 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 3 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf3]
  obtain ⟨nf4, hnf4, hfv4⟩ := stepOut_sound (ch 4) st.f4 (W 8) [W 8, W 7, W 4, W 3, W 2, W 1]
    (hst 4) (hsv.1 8 (by decide)) (by have := hsv.2 4 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 4 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 4 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 4 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 4 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 4 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 4 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf4]
  obtain ⟨nf5, hnf5, hfv5⟩ := stepOut_sound (ch 5) st.f5 (W 8) [W 8, W 7, W 4, W 3, W 2]
    (hst 5) (hsv.1 8 (by decide)) (by have := hsv.2 5 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 5 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 7 (by decide), by have := hsv.2 5 7 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 5 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 5 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 5 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf5]
  obtain ⟨nf6, hnf6, hfv6⟩ := stepOut_sound (ch 6) st.f6 (W 8) [W 8, W 6, W 5, W 4, W 3]
    (hst 6) (hsv.1 8 (by decide)) (by have := hsv.2 6 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 6 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 6 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 6 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 6 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 6 3 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf6]
  obtain ⟨nf7, hnf7, hfv7⟩ := stepOut_sound (ch 7) st.f7 (W 8) [W 8, W 6, W 5, W 3, W 2, W 1]
    (hst 7) (hsv.1 8 (by decide)) (by have := hsv.2 7 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 7 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 7 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 7 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 7 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 7 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 7 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf7]
  obtain ⟨nf8, hnf8, hfv8⟩ := stepOut_sound (ch 8) st.f8 (W 8) [W 8, W 6, W 5, W 3, W 1]
    (hst 8) (hsv.1 8 (by decide)) (by have := hsv.2 8 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 8 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 6 (by decide), by have := hsv.2 8 6 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 8 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 8 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 8 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf8]
  obtain ⟨nf9, hnf9, hfv9⟩ := stepOut_sound (ch 9) st.f9 (W 8) [W 8, W 5, W 4, W 3, W 2, W 1]
    (hst 9) (hsv.1 8 (by decide)) (by have := hsv.2 9 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 9 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 9 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 9 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 9 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 9 2 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 1 (by decide), by have := hsv.2 9 1 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf9]
  obtain ⟨nf10, hnf10, hfv10⟩ := stepOut_sound (ch 10) st.f10 (W 8) [W 8, W 5, W 4, W 3, W 2]
    (hst 10) (hsv.1 8 (by decide)) (by have := hsv.2 10 8 (by decide) (by decide); simpa [rows9] using this)
    (by intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hsv.1 8 (by decide), by have := hsv.2 10 8 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 5 (by decide), by have := hsv.2 10 5 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 4 (by decide), by have := hsv.2 10 4 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 3 (by decide), by have := hsv.2 10 3 (by decide) (by decide); simpa [rows9] using this⟩
        · exact ⟨hsv.1 2 (by decide), by have := hsv.2 10 2 (by decide) (by decide); simpa [rows9] using this⟩)
  rw [hnf10]
  refine ⟨⟨nf0, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9, nf10, nf11, nf12, nf13, nf14, nf15⟩, rfl, fun k => by fin_cases k <;> assumption⟩




/-! ## Section 4C: Gate canonicalization and Phase 1 completeness (`exists_canon_in_runBranch`) -/

lemma sep_all : ∀ u v : V, u ≠ v → ∃ k : Fin 16, v ∈ rows9 k ∧ u ∉ rows9 k := by decide +kernel

def optHasLit (o : Opt) (l : Nat) : Bool := (o.l1 == l) || (o.l2 == l)

def optGm4 (o : Opt) : Nat :=
  (if o.l1 / 2 == 1 || o.l2 / 2 == 1 then 1 else 0) +
  (if o.l1 / 2 == 2 || o.l2 / 2 == 2 then 2 else 0) +
  (if o.l1 / 2 == 3 || o.l2 / 2 == 3 then 4 else 0) +
  (if o.l1 / 2 == 4 || o.l2 / 2 == 4 then 8 else 0)

def optCanonOk (o : Opt) (ug : Nat) : Bool :=
  let gm := optGm4 o
  (List.range 4).all fun g =>
    if ug.testBit g then true
    else if gm.testBit g then
      !(optHasLit o (2 * (g + 1) + 1)) &&
      ((List.range g).all fun g' => ug.testBit g' || gm.testBit g')
    else true

lemma allOpts41_spec : ∀ m : Fin 1024,
    (m.val % 2 = 0 ∧
     1 ≤ (Finset.univ.filter (fun l : Fin 10 => m.val.testBit l.val = true)).card ∧
     (Finset.univ.filter (fun l : Fin 10 => m.val.testBit l.val = true)).card ≤ 2 ∧
     ∀ g : Fin 5, ¬ (m.val.testBit (2 * g.val) = true ∧ m.val.testBit (2 * g.val + 1) = true)) →
    ∃ o ∈ allOpts41, o.id = m.val ∧ OptOk o ∧
      ∀ l : Fin 10, optHasLit o l.val = m.val.testBit l.val := by
  decide +kernel

lemma optsFor_complete : ∀ ug : Fin 16, ∀ o ∈ allOpts41,
    optCanonOk o ug.val = true → (o, ug.val ||| optGm4 o) ∈ optsFor ug.val := by
  decide +kernel

def validW12Pairs : List (Opt × Opt × Nat) := [
  (⟨4, 2, 2, 3, 3⟩, ⟨16, 4, 4, 5, 5⟩, 3),
  (⟨4, 2, 2, 3, 3⟩, ⟨24, 3, 4, 2, 5⟩, 3),
  (⟨4, 2, 2, 3, 3⟩, ⟨80, 4, 6, 5, 7⟩, 7),
  (⟨6, 1, 2, 0, 3⟩, ⟨8, 3, 3, 2, 2⟩, 1),
  (⟨6, 1, 2, 0, 3⟩, ⟨10, 1, 3, 0, 2⟩, 1),
  (⟨6, 1, 2, 0, 3⟩, ⟨16, 4, 4, 5, 5⟩, 3),
  (⟨6, 1, 2, 0, 3⟩, ⟨18, 1, 4, 0, 5⟩, 3),
  (⟨6, 1, 2, 0, 3⟩, ⟨24, 3, 4, 2, 5⟩, 3),
  (⟨6, 1, 2, 0, 3⟩, ⟨80, 4, 6, 5, 7⟩, 7),
  (⟨20, 2, 4, 3, 5⟩, ⟨8, 3, 3, 2, 2⟩, 3),
  (⟨20, 2, 4, 3, 5⟩, ⟨24, 3, 4, 2, 5⟩, 3),
  (⟨20, 2, 4, 3, 5⟩, ⟨32, 5, 5, 4, 4⟩, 3),
  (⟨20, 2, 4, 3, 5⟩, ⟨36, 2, 5, 3, 4⟩, 3),
  (⟨20, 2, 4, 3, 5⟩, ⟨40, 3, 5, 2, 4⟩, 3),
  (⟨20, 2, 4, 3, 5⟩, ⟨64, 6, 6, 7, 7⟩, 7),
  (⟨20, 2, 4, 3, 5⟩, ⟨68, 2, 6, 3, 7⟩, 7),
  (⟨20, 2, 4, 3, 5⟩, ⟨72, 3, 6, 2, 7⟩, 7),
  (⟨20, 2, 4, 3, 5⟩, ⟨80, 4, 6, 5, 7⟩, 7),
  (⟨20, 2, 4, 3, 5⟩, ⟨96, 5, 6, 4, 7⟩, 7),
  (⟨20, 2, 4, 3, 5⟩, ⟨320, 6, 8, 7, 9⟩, 15)
]

lemma w12_mem_valid : ∀ p1 ∈ optsFor 0, ∀ p2 ∈ optsFor p1.2,
    (optHasLit p1.1 1 = false → optHasLit p2.1 1 = false) →
    (stepF16_1 initF16 p1.1).isSome = true →
    (match stepF16_1 initF16 p1.1 with
     | some st1 => (stepF16_2 st1 p1.1 p2.1).isSome
     | none => false) = true →
    (p1.1, p2.1, p2.2) ∈ validW12Pairs := by
  decide +kernel

def classes62 : List (List Nat) := [
  [6, 10, 24, 72, 68, 20, 288, 640],
  [6, 10, 24, 72, 68, 20, 384, 544],
  [6, 10, 24, 72, 68, 272, 288, 640],
  [6, 10, 24, 72, 320, 20, 544, 384],
  [6, 10, 24, 96, 68, 272, 288, 640],
  [6, 10, 24, 96, 68, 272, 384, 640],
  [6, 10, 24, 320, 20, 640, 96, 384],
  [6, 10, 24, 320, 20, 640, 160, 576],
  [6, 10, 24, 320, 20, 640, 288, 576],
  [6, 10, 24, 320, 20, 640, 384, 576],
  [6, 10, 24, 320, 20, 640, 544, 384],
  [6, 10, 24, 320, 20, 640, 576, 384],
  [6, 10, 24, 320, 68, 20, 384, 544],
  [6, 10, 24, 320, 68, 144, 288, 544],
  [6, 10, 24, 320, 68, 144, 384, 544],
  [6, 10, 24, 320, 260, 20, 576, 160],
  [6, 10, 24, 320, 260, 528, 96, 160],
  [6, 10, 24, 320, 260, 528, 576, 160],
  [6, 10, 80, 40, 288, 68, 640, 272],
  [6, 10, 80, 40, 288, 68, 640, 384],
  [6, 10, 80, 136, 384, 20, 544, 288],
  [6, 10, 80, 136, 384, 20, 544, 320],
  [6, 10, 80, 264, 160, 260, 96, 144],
  [6, 10, 80, 264, 160, 260, 96, 528],
  [6, 10, 80, 264, 160, 260, 96, 640],
  [6, 10, 80, 264, 160, 260, 144, 96],
  [6, 10, 80, 264, 160, 260, 144, 544],
  [6, 10, 80, 264, 160, 260, 144, 576],
  [6, 10, 80, 264, 260, 20, 640, 96],
  [6, 10, 80, 264, 260, 68, 544, 144],
  [6, 10, 80, 264, 288, 20, 640, 96],
  [6, 10, 80, 264, 288, 20, 640, 576],
  [6, 10, 80, 264, 384, 68, 544, 144],
  [6, 10, 80, 264, 384, 68, 544, 528],
  [6, 18, 40, 80, 68, 288, 384, 640],
  [6, 18, 72, 272, 68, 288, 136, 544],
  [6, 18, 72, 272, 260, 40, 640, 576],
  [6, 18, 72, 272, 260, 160, 640, 576],
  [6, 18, 80, 40, 288, 68, 640, 384],
  [6, 18, 80, 264, 40, 68, 384, 640],
  [6, 18, 80, 264, 96, 260, 160, 520],
  [6, 18, 80, 264, 544, 68, 384, 640],
  [6, 24, 40, 320, 36, 640, 144, 576],
  [6, 24, 40, 320, 36, 640, 384, 576],
  [6, 24, 40, 320, 36, 640, 528, 384],
  [6, 24, 40, 320, 36, 640, 576, 384],
  [6, 24, 320, 40, 640, 36, 384, 528],
  [6, 24, 320, 40, 640, 36, 384, 576],
  [6, 24, 320, 40, 640, 36, 576, 144],
  [6, 24, 320, 40, 640, 36, 576, 384],
  [6, 80, 96, 264, 160, 260, 144, 520],
  [6, 80, 144, 264, 160, 260, 96, 520],
  [6, 80, 264, 96, 260, 160, 520, 144],
  [6, 80, 264, 144, 260, 160, 520, 96],
  [20, 320, 40, 384, 24, 640, 36, 576],
  [20, 320, 40, 384, 36, 640, 24, 576],
  [20, 320, 40, 576, 24, 640, 36, 384],
  [20, 320, 40, 576, 36, 640, 24, 384],
  [20, 320, 384, 40, 640, 24, 576, 36],
  [20, 320, 384, 40, 640, 36, 576, 24],
  [20, 320, 576, 40, 640, 24, 384, 36],
  [20, 320, 576, 40, 640, 36, 384, 24]
]

def chToB10 (ch : Fin 5 → Option Bool) : B10 :=
  ⟨ch 0 == some false, ch 0 == some true,
   ch 1 == some false, ch 1 == some true,
   ch 2 == some false, ch 2 == some true,
   ch 3 == some false, ch 3 == some true,
   ch 4 == some false, ch 4 == some true⟩

lemma chToB10_get (ch : Fin 5 → Option Bool) (l : Fin 10) :
    (chToB10 ch).get l.val = true ↔ litTrue ch l.val := by
  fin_cases l
  all_goals
    simp only [chToB10, B10.get, beq_iff_eq, litTrue]
    constructor
    · intro h; first
        | exact ⟨0, false, h, rfl⟩ | exact ⟨0, true, h, rfl⟩
        | exact ⟨1, false, h, rfl⟩ | exact ⟨1, true, h, rfl⟩
        | exact ⟨2, false, h, rfl⟩ | exact ⟨2, true, h, rfl⟩
        | exact ⟨3, false, h, rfl⟩ | exact ⟨3, true, h, rfl⟩
        | exact ⟨4, false, h, rfl⟩ | exact ⟨4, true, h, rfl⟩
    · rintro ⟨g, b, hg, heq⟩
      fin_cases g <;> cases b <;> simp_all

lemma chToB10_mem_fOut (ch : Fin 5 → Option Bool) (h0 : ch 0 = some false) :
    chToB10 ch ∈ fOutB10 := by
  have h : ∀ a b c d : Option Bool, chToB10 ![some false, a, b, c, d] ∈ fOutB10 := by decide +kernel
  have heq : ch = ![some false, ch 1, ch 2, ch 3, ch 4] := by
    ext i; fin_cases i <;> simp [h0]
  rw [heq]; exact h (ch 1) (ch 2) (ch 3) (ch 4)

lemma chToB10_mem_fIn (ch : Fin 5 → Option Bool) (h0 : ch 0 ≠ some false) :
    chToB10 ch ∈ fInB10 := by
  have h : ∀ z a b c d : Option Bool, z ≠ some false → chToB10 ![z, a, b, c, d] ∈ fInB10 := by
    decide +kernel
  have heq : ch = ![ch 0, ch 1, ch 2, ch 3, ch 4] := by
    ext i; fin_cases i <;> simp
  rw [heq]; exact h (ch 0) (ch 1) (ch 2) (ch 3) (ch 4) h0

lemma checkFull_sound (W : V → Opt) (ch : Fin 16 → Fin 5 → Option Bool)
    (hsv : StepValid 8 W ch)
    (h0in : ∀ k : Fin 16, (0 : V) ∈ rows9 k → ch k 0 ≠ some false)
    (h0out : ∀ k : Fin 16, (0 : V) ∉ rows9 k → ch k 0 = some false) :
    checkFull (W 1) (W 2) (W 3) (W 4) (W 5) (W 6) (W 7) (W 8) = true := by
  have hhit : ∀ k : Fin 16, ∀ u : V, u.val ≠ 0 →
      hitB10 (chToB10 (ch k)) (W u) = decide (u ∉ rows9 k) := by
    intro k u hu0
    have hok := hsv.1 u hu0
    have hst := hsv.2 k u hu0 (by omega)
    have h1 := chToB10_get (ch k) ⟨(W u).l1, hok.1⟩
    have h2 := chToB10_get (ch k) ⟨(W u).l2, hok.2.1⟩
    by_cases hum : u ∈ rows9 k
    · simp only [hum, not_true_eq_false, decide_false]
      simp only [hum, ↓reduceIte] at hst
      unfold hitB10
      rw [Bool.or_eq_false_iff]
      exact ⟨Bool.eq_false_iff.mpr (fun ht => hst.1 (h1.mp ht)),
             Bool.eq_false_iff.mpr (fun ht => hst.2 (h2.mp ht))⟩
    · simp only [hum, not_false_eq_true, decide_true]
      simp only [hum, ↓reduceIte] at hst
      unfold hitB10
      rw [Bool.or_eq_true]
      rcases hst with h | h
      · exact Or.inl (h1.mpr h)
      · exact Or.inr (h2.mpr h)
  have hall : ∀ k : Fin 16,
      (if (0 : V) ∈ rows9 k then fInB10 else fOutB10).any (fun f =>
        (if (1 : V) ∈ rows9 k then !(hitB10 f (W 1)) else hitB10 f (W 1)) &&
        (if (2 : V) ∈ rows9 k then !(hitB10 f (W 2)) else hitB10 f (W 2)) &&
        (if (3 : V) ∈ rows9 k then !(hitB10 f (W 3)) else hitB10 f (W 3)) &&
        (if (4 : V) ∈ rows9 k then !(hitB10 f (W 4)) else hitB10 f (W 4)) &&
        (if (5 : V) ∈ rows9 k then !(hitB10 f (W 5)) else hitB10 f (W 5)) &&
        (if (6 : V) ∈ rows9 k then !(hitB10 f (W 6)) else hitB10 f (W 6)) &&
        (if (7 : V) ∈ rows9 k then !(hitB10 f (W 7)) else hitB10 f (W 7)) &&
        (if (8 : V) ∈ rows9 k then !(hitB10 f (W 8)) else hitB10 f (W 8))) = true := by
    intro k
    rw [List.any_eq_true]
    refine ⟨chToB10 (ch k), ?_, ?_⟩
    · by_cases h0 : (0 : V) ∈ rows9 k
      · rw [ite_eq_left h0]; exact chToB10_mem_fIn (ch k) (h0in k h0)
      · rw [ite_eq_right h0]; exact chToB10_mem_fOut (ch k) (h0out k h0)
    · have h1 := hhit k 1 (by decide); have h2 := hhit k 2 (by decide)
      have h3 := hhit k 3 (by decide); have h4 := hhit k 4 (by decide)
      have h5 := hhit k 5 (by decide); have h6 := hhit k 6 (by decide)
      have h7 := hhit k 7 (by decide); have h8 := hhit k 8 (by decide)
      simp only [h1, h2, h3, h4, h5, h6, h7, h8]
      have hb : ∀ P : Prop, [Decidable P] → (if P then !(decide (¬ P)) else decide (¬ P)) = true := by
        intro P _; by_cases hP : P <;> simp [hP]
      simp only [hb, Bool.and_self]
  unfold checkFull
  have k0 := hall 0; have k1 := hall 1; have k2 := hall 2; have k3 := hall 3
  have k4 := hall 4; have k5 := hall 5; have k6 := hall 6; have k7 := hall 7
  have k8 := hall 8; have k9 := hall 9; have k10 := hall 10; have k11 := hall 11
  have k12 := hall 12; have k13 := hall 13; have k14 := hall 14; have k15 := hall 15
  simp only [rows9, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_false, or_true,
    ↓reduceIte] at k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15
  simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, Bool.and_self]

lemma testBit_sum_pow (P : Fin 10 → Bool) (l : Fin 10) :
    (∑ i : Fin 10, if P i = true then 2 ^ i.val else 0).testBit l.val = P l := by
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) (l : Fin 10),
      (∑ i : Fin 10, if (![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9] i) = true then 2 ^ i.val else 0).testBit l.val =
      ![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9] l := by decide +kernel
  have heq : P = ![P 0, P 1, P 2, P 3, P 4, P 5, P 6, P 7, P 8, P 9] := by
    ext i; fin_cases i <;> rfl
  rw [heq]; exact h (P 0) (P 1) (P 2) (P 3) (P 4) (P 5) (P 6) (P 7) (P 8) (P 9) l

lemma sum_pow_lt_1024 (P : Fin 10 → Bool) :
    (∑ i : Fin 10, if P i = true then 2 ^ i.val else 0) < 1024 := by
  calc (∑ i : Fin 10, if P i = true then 2 ^ i.val else 0)
      ≤ ∑ i : Fin 10, 2 ^ i.val := Finset.sum_le_sum (fun i _ => by split_ifs; exact le_refl _; exact Nat.zero_le _)
    _ < 1024 := by decide

def usedGOf (W : V → Opt) : Nat → Nat
  | 0 => 0
  | n + 1 => usedGOf W n ||| optGm4 (W ⟨(n + 1) % 9, Nat.mod_lt _ (by decide)⟩)

/-- Canonicalize gates `Fin 5 \ {a0}` and side-flips of `D'`, proving the resulting bare table
    belongs to `runBranch` for some `(w1, w2, ug2) ∈ validW12Pairs`! -/
lemma exists_canon_in_runBranch (D' : AndCountCircuit 9) (a0 : Fin 5) (hsz' : D'.size = 5)
    (hW' : D'.WellFormed) (hD' : ∀ i, Disjoint (D'.leftVars i) (D'.rightVars i))
    (hsep' : Separates D')
    (hLa0 : D'.leftVars ⟨a0.val, by omega⟩ = {0})
    (h0R : (0 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩)
    (h0oth : ∀ i : Fin 5, i ≠ a0 → (0 : V) ∉ D'.leftVars ⟨i.val, by omega⟩ ∧ (0 : V) ∉ D'.rightVars ⟨i.val, by omega⟩)
    (hno0 : ∀ k : Fin 16, (0 : V) ∉ rows9 k →
      sideL D' (rows9 k) ⟨a0.val, by omega⟩ = false ∧ sideR D' (rows9 k) ⟨a0.val, by omega⟩ = true)
    (h12 : (1 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩ → (2 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩) :
    ∃ D'' : AndCountCircuit 9, ∃ hsz'' : D''.size = 5, ∃ σ : Fin 5 ≃ Fin 5,
      D''.WellFormed ∧ (∀ i, Disjoint (D''.leftVars i) (D''.rightVars i)) ∧ Separates D'' ∧
      σ a0 = 0 ∧
      D''.leftVars ⟨a0.val, by omega⟩ = {0} ∧
      (0 : V) ∉ D''.rightVars ⟨a0.val, by omega⟩ ∧
      (∀ i : Fin 5, i ≠ a0 → (0 : V) ∉ D''.leftVars ⟨i.val, by omega⟩ ∧ (0 : V) ∉ D''.rightVars ⟨i.val, by omega⟩) ∧
      (∀ k : Fin 16, (0 : V) ∉ rows9 k →
        sideL D'' (rows9 k) ⟨a0.val, by omega⟩ = false ∧ sideR D'' (rows9 k) ⟨a0.val, by omega⟩ = true) ∧
      ∃ p ∈ validW12Pairs, ∃ c ∈ runBranch p.1 p.2.1 p.2.2,
        c.length = 8 ∧
        ∀ v : V, v.val ≠ 0 → ∀ g : Fin 5,
          (v ∈ D''.leftVars ⟨(σ.symm g).val, by omega⟩ ↔ (c.getD (v.val - 1) 0).testBit (2 * g.val) = true) ∧
          (v ∈ D''.rightVars ⟨(σ.symm g).val, by omega⟩ ↔ (c.getD (v.val - 1) 0).testBit (2 * g.val + 1) = true) := by
  classical
  let hitSet (g : Fin 5) : Finset Nat :=
    (Finset.Icc 1 8).filter (fun n => ∃ h : n < 9,
      (⟨n, h⟩ : V) ∈ D'.leftVars ⟨g.val, by omega⟩ ∨ (⟨n, h⟩ : V) ∈ D'.rightVars ⟨g.val, by omega⟩)
  let firstV (g : Fin 5) : Nat := if h : (hitSet g).Nonempty then (hitSet g).min' h else 9
  have hfirstV_le : ∀ g : Fin 5, firstV g ≤ 9 := by
    intro g; dsimp only [firstV]; split_ifs with h
    · have hm := Finset.mem_filter.mp ((hitSet g).min'_mem h)
      have := (Finset.mem_Icc.mp hm.1).2; omega
    · omega
  have hfirstV_spec : ∀ (g : Fin 5) (v : V), v.val ≠ 0 →
      (v ∈ D'.leftVars ⟨g.val, by omega⟩ ∨ v ∈ D'.rightVars ⟨g.val, by omega⟩) →
      firstV g ≤ v.val := by
    intro g v hv0 hv
    have hvmem : v.val ∈ hitSet g := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, v.isLt, hv⟩
    dsimp only [firstV]
    rw [dite_eq_left ⟨v.val, hvmem⟩]
    exact Finset.min'_le _ _ hvmem
  have hfirstV_hit : ∀ g : Fin 5, ∀ hlt : firstV g < 9,
      (⟨firstV g, hlt⟩ : V) ∈ D'.leftVars ⟨g.val, by omega⟩ ∨
      (⟨firstV g, hlt⟩ : V) ∈ D'.rightVars ⟨g.val, by omega⟩ := by
    intro g hlt
    dsimp only [firstV] at hlt ⊢
    by_cases hne : (hitSet g).Nonempty
    · have hm := (Finset.mem_filter.mp ((hitSet g).min'_mem hne)).2
      obtain ⟨_, hv⟩ := hm
      simpa [dite_eq_left hne] using hv
    · rw [dite_eq_right hne] at hlt; omega
  let key (g : Fin 5) : Nat := if g = a0 then 0 else 10 * firstV g + g.val + 1
  have hkey_inj : Function.Injective key := by
    intro g1 g2 heq
    dsimp only [key] at heq
    by_cases h1 : g1 = a0 <;> by_cases h2 : g2 = a0 <;> simp only [h1, h2, ↓reduceIte] at heq
    · rw [h1, h2]
    · omega
    · omega
    · exact Fin.ext (by omega)
  let S : Finset Nat := Finset.univ.image key
  have hScard : S.card = 5 := by
    rw [Finset.card_image_of_injective _ hkey_inj, Finset.card_univ, Fintype.card_fin]
  let emb : Fin 5 ↪o Nat := S.orderEmbOfFin hScard
  have hkey_mem : ∀ g : Fin 5, ∃ j : Fin 5, emb j = key g := by
    intro g
    have hm : key g ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ g)
    have hr : key g ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hm
    exact hr
  let σf : Fin 5 → Fin 5 := fun g => (hkey_mem g).choose
  have hσ_emb : ∀ g : Fin 5, emb (σf g) = key g := fun g => (hkey_mem g).choose_spec
  have hσ_inj : Function.Injective σf := fun g1 g2 h =>
    hkey_inj ((hσ_emb g1).symm.trans ((congrArg emb h).trans (hσ_emb g2)))
  let σ : Fin 5 ≃ Fin 5 := Equiv.ofBijective σf ((Finite.injective_iff_bijective).mp hσ_inj)
  have hσ_a0 : σ a0 = 0 := by
    by_contra hne
    have hgt : (0 : Fin 5) < σ a0 := Fin.pos_of_ne_zero hne
    have hlt : emb 0 < emb (σ a0) := emb.strictMono hgt
    have heq : emb (σ a0) = 0 := by simpa [σ, key] using hσ_emb a0
    omega
  have hσ_mono : ∀ g1 g2 : Fin 5, (σ g1).val < (σ g2).val → key g1 < key g2 := by
    intro g1 g2 hlt
    have : emb (σ g1) < emb (σ g2) := emb.strictMono hlt
    simpa [σ, hσ_emb] using this
  let ε : Fin D'.size → Bool := fun i =>
    let g : Fin 5 := ⟨i.val, by omega⟩
    if g = a0 then false
    else if h : firstV g < 9 then decide ((⟨firstV g, h⟩ : V) ∈ D'.rightVars i)
    else false
  let D'' := swapSide D' ε
  have hsz'' : D''.size = 5 := hsz'
  have hW'' : D''.WellFormed := swapSide_wf D' ε hW'
  have hD'' : ∀ i, Disjoint (D''.leftVars i) (D''.rightVars i) := swapSide_disjoint D' ε hD'
  have hsep'' : Separates D'' := fun k => by simpa [D'', swapSide_eval] using hsep' k
  have hε_a0 : ε ⟨a0.val, by omega⟩ = false := by simp [ε]
  have hLa0'' : D''.leftVars ⟨a0.val, by omega⟩ = {0} := by
    change cond (ε ⟨a0.val, by omega⟩) _ _ = {0}; rw [hε_a0]; exact hLa0
  have hRa0'' : D''.rightVars ⟨a0.val, by omega⟩ = D'.rightVars ⟨a0.val, by omega⟩ := by
    change cond (ε ⟨a0.val, by omega⟩) _ _ = _; rw [hε_a0]; rfl
  have h0R'' : (0 : V) ∉ D''.rightVars ⟨a0.val, by omega⟩ := by rw [hRa0'']; exact h0R
  have hno0'' : ∀ k : Fin 16, (0 : V) ∉ rows9 k →
      sideL D'' (rows9 k) ⟨a0.val, by omega⟩ = false ∧ sideR D'' (rows9 k) ⟨a0.val, by omega⟩ = true := by
    intro k hk
    have hgv : ∀ j : Fin D'.size, D''.gateVal (rows9 k) j = D'.gateVal (rows9 k) j :=
      fun j => swapSide_gateVal D' ε (rows9 k) D'.size j j.isLt
    have hL : sideL D'' (rows9 k) ⟨a0.val, by omega⟩ = sideL D' (rows9 k) ⟨a0.val, by omega⟩ := by
      unfold sideL
      have h1 : D''.leftVars ⟨a0.val, by omega⟩ = D'.leftVars ⟨a0.val, by omega⟩ := by
        change cond (ε ⟨a0.val, by omega⟩) _ _ = _; rw [hε_a0]; rfl
      have h2 : D''.leftGates ⟨a0.val, by omega⟩ = D'.leftGates ⟨a0.val, by omega⟩ := by
        change cond (ε ⟨a0.val, by omega⟩) _ _ = _; rw [hε_a0]; rfl
      rw [h1, h2]
      exact sideTrue_congr _ _ _ _ _ _ (fun j _ => hgv j)
    have hR : sideR D'' (rows9 k) ⟨a0.val, by omega⟩ = sideR D' (rows9 k) ⟨a0.val, by omega⟩ := by
      unfold sideR
      have h2 : D''.rightGates ⟨a0.val, by omega⟩ = D'.rightGates ⟨a0.val, by omega⟩ := by
        change cond (ε ⟨a0.val, by omega⟩) _ _ = _; rw [hε_a0]; rfl
      rw [hRa0'', h2]
      exact sideTrue_congr _ _ _ _ _ _ (fun j _ => hgv j)
    rw [hL, hR]; exact hno0 k hk
  have hfirst_notR : ∀ g : Fin 5, g ≠ a0 → ∀ hlt : firstV g < 9,
      (⟨firstV g, hlt⟩ : V) ∉ D''.rightVars ⟨g.val, by omega⟩ := by
    intro g hga hlt
    have hε : ε ⟨g.val, by omega⟩ = decide ((⟨firstV g, hlt⟩ : V) ∈ D'.rightVars ⟨g.val, by omega⟩) := by
      simp [ε, hga, hlt]
    change (⟨firstV g, hlt⟩ : V) ∉ cond (ε ⟨g.val, by omega⟩) (D'.leftVars ⟨g.val, by omega⟩) (D'.rightVars ⟨g.val, by omega⟩)
    rw [hε]
    by_cases hR : (⟨firstV g, hlt⟩ : V) ∈ D'.rightVars ⟨g.val, by omega⟩
    · rw [decide_eq_true hR, Bool.cond_true]
      exact Finset.disjoint_right.mp (hD' ⟨g.val, by omega⟩) hR
    · rw [decide_eq_false hR, Bool.cond_false]; exact hR
  have hhit_eq : ∀ (g : Fin 5) (v : V),
      (v ∈ D''.leftVars ⟨g.val, by omega⟩ ∨ v ∈ D''.rightVars ⟨g.val, by omega⟩) ↔
      (v ∈ D'.leftVars ⟨g.val, by omega⟩ ∨ v ∈ D'.rightVars ⟨g.val, by omega⟩) := by
    intro g v
    dsimp only [D'', swapSide]
    cases ε ⟨g.val, by omega⟩ <;> simp [or_comm]
  have h0oth'' : ∀ i : Fin 5, i ≠ a0 →
      (0 : V) ∉ D''.leftVars ⟨i.val, by omega⟩ ∧ (0 : V) ∉ D''.rightVars ⟨i.val, by omega⟩ := by
    intro i hi
    have h := h0oth i hi
    have he := hhit_eq i 0
    constructor <;> intro hm <;> rcases he.mp (by first | exact Or.inl hm | exact Or.inr hm) with h1 | h2
    · exact h.1 h1
    · exact h.2 h2
    · exact h.1 h1
    · exact h.2 h2
  let litP (v : V) (l : Fin 10) : Bool :=
    if l.val % 2 = 0 then
      decide (v ∈ D''.leftVars ⟨(σ.symm ⟨l.val / 2, by omega⟩).val, by omega⟩)
    else
      decide (v ∈ D''.rightVars ⟨(σ.symm ⟨l.val / 2, by omega⟩).val, by omega⟩)
  let mask (v : V) : Nat := ∑ l : Fin 10, if litP v l = true then 2 ^ l.val else 0
  have hmask_bit : ∀ (v : V) (l : Fin 10), (mask v).testBit l.val = litP v l :=
    fun v l => testBit_sum_pow (litP v) l
  have hopt_ex : ∀ v : V, v.val ≠ 0 → ∃ o ∈ allOpts41, o.id = mask v ∧ OptOk o ∧
      ∀ l : Fin 10, optHasLit o l.val = litP v l := by
    intro v hv0
    have hlt1024 : mask v < 1024 := sum_pow_lt_1024 (litP v)
    obtain ⟨o, ho, hid, hok, hbit⟩ := allOpts41_spec ⟨mask v, hlt1024⟩ (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (mask v) % 2 = 0
        have hb0 : (mask v).testBit 0 = false := by
          have hm0 := hmask_bit v 0
          simp only [Fin.val_zero] at hm0
          rw [hm0]
          have hsym0 : σ.symm 0 = a0 := by rw [← hσ_a0, Equiv.symm_apply_apply]
          have hvne0 : v ≠ 0 := fun h => hv0 (by rw [h]; rfl)
          simp only [litP, Fin.val_zero, Nat.zero_mod, ↓reduceIte, Nat.zero_div, Fin.mk_zero, hsym0, hLa0'',
            Finset.mem_singleton, hvne0, decide_false]
        have hz := Nat.testBit_zero (mask v)
        rw [hb0] at hz
        have hne1 : (mask v) % 2 ≠ 1 := by
          intro h1; rw [h1] at hz; simp at hz
        omega
      · obtain ⟨k, hvk⟩ := avoid_all v
        obtain ⟨g, b, hgb, _⟩ := (mis_cover_gen D'' (rows9 k) (hsep'' k).1).2
          v hvk (sep_outVars_empty hsep'' v) ((hsep'' k).2 v hvk)
        let g' : Fin 5 := σ ⟨g.val, by omega⟩
        let l : Fin 10 := ⟨2 * g'.val + (if b then 1 else 0), by cases b <;> (simp; omega)⟩
        apply Finset.card_pos.mpr
        refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        change (mask v).testBit l.val = true
        rw [hmask_bit v l]
        have hmem := (mem_litSet D'' v g b).mp hgb
        have hsym : σ.symm ⟨l.val / 2, by omega⟩ = ⟨g.val, by omega⟩ := by
          have : (⟨l.val / 2, by omega⟩ : Fin 5) = g' := Fin.ext (by dsimp [l]; cases b <;> (dsimp; omega))
          rw [this]; exact Equiv.symm_apply_apply σ _
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at hmem
          have hm0 : l.val % 2 = 0 := by dsimp [l]; omega
          simpa [litP, hm0, hsym] using hmem
        · simp only [↓reduceIte] at hmem
          have hm1 : l.val % 2 ≠ 0 := by dsimp [l]; omega
          simpa [litP, hm1, hsym] using hmem
      · have hcard_eq : (Finset.univ.filter (fun l : Fin 10 => (mask v).testBit l.val = true)).card =
            (litSet D'' v).card := by
          refine Finset.card_bij (fun (l : Fin 10) _ =>
            (⟨(σ.symm ⟨l.val / 2, by omega⟩).val, by omega⟩, decide (l.val % 2 = 1))) ?_ ?_ ?_
          · intro l hl
            have hb := (Finset.mem_filter.mp hl).2
            rw [hmask_bit v l] at hb
            rw [mem_litSet]
            by_cases hm : l.val % 2 = 0
            · have hm1 : decide (l.val % 2 = 1) = false := decide_eq_false (by omega)
              rw [hm1]; simp only [Bool.false_eq_true, ↓reduceIte]
              simpa [litP, hm] using hb
            · have hm1 : decide (l.val % 2 = 1) = true := decide_eq_true (by omega)
              rw [hm1]; simp only [↓reduceIte]
              simpa [litP, hm] using hb
          · intro l1 _ l2 _ heq
            have h1 := congrArg Prod.fst heq
            have h2 := congrArg Prod.snd heq
            dsimp only at h1 h2
            have hg : σ.symm ⟨l1.val / 2, by omega⟩ = σ.symm ⟨l2.val / 2, by omega⟩ :=
              Fin.ext (congrArg (Fin.val : Fin D''.size → Nat) h1)
            have hdiv : l1.val / 2 = l2.val / 2 := congrArg Fin.val (σ.symm.injective hg)
            have hmod : l1.val % 2 = l2.val % 2 := by
              have : (l1.val % 2 = 1) ↔ (l2.val % 2 = 1) := by simpa using h2
              omega
            exact Fin.ext (by omega)
          · rintro ⟨g, b⟩ hgb
            let g' : Fin 5 := σ ⟨g.val, by omega⟩
            let l : Fin 10 := ⟨2 * g'.val + (if b then 1 else 0), by cases b <;> (simp; omega)⟩
            have hsym : σ.symm ⟨l.val / 2, by omega⟩ = ⟨g.val, by omega⟩ := by
              have : (⟨l.val / 2, by omega⟩ : Fin 5) = g' := Fin.ext (by dsimp [l]; cases b <;> (dsimp; omega))
              rw [this]; exact Equiv.symm_apply_apply σ _
            refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [hmask_bit v l]
              have hmem := (mem_litSet D'' v g b).mp hgb
              cases b
              · simp only [Bool.false_eq_true, ↓reduceIte] at hmem
                have hm0 : l.val % 2 = 0 := by dsimp [l]; omega
                simpa [litP, hm0, hsym] using hmem
              · simp only [↓reduceIte] at hmem
                have hm1 : l.val % 2 ≠ 0 := by dsimp [l]; omega
                simpa [litP, hm1, hsym] using hmem
            · ext
              · dsimp only; exact congrArg (Fin.val : Fin 5 → Nat) hsym
              · dsimp only; cases b <;> simp [l]
        change (Finset.univ.filter (fun l : Fin 10 => (mask v).testBit l.val = true)).card ≤ 2
        rw [hcard_eq]
        exact hit_le_two D'' hsz'' hD'' hsep'' v
      · intro g ⟨hL, hR⟩
        change (mask v).testBit (2 * g.val) = true at hL
        change (mask v).testBit (2 * g.val + 1) = true at hR
        have hL' := hmask_bit v ⟨2 * g.val, by omega⟩ ▸ hL
        have hR' := hmask_bit v ⟨2 * g.val + 1, by omega⟩ ▸ hR
        have hm0 : (2 * g.val) % 2 = 0 := by omega
        have hm1 : (2 * g.val + 1) % 2 ≠ 0 := by omega
        have hd0 : (⟨(2 * g.val) / 2, by omega⟩ : Fin 5) = g := Fin.ext (by dsimp; omega)
        have hd1 : (⟨(2 * g.val + 1) / 2, by omega⟩ : Fin 5) = g := Fin.ext (by dsimp; omega)
        simp only [litP, hm0, ↓reduceIte, hd0, decide_eq_true_eq] at hL'
        simp only [litP, hm1, ↓reduceIte, hd1, decide_eq_true_eq] at hR'
        exact Finset.disjoint_left.mp (hD'' ⟨(σ.symm g).val, by omega⟩) hL' hR')
    refine ⟨o, ho, hid, hok, fun l => ?_⟩
    rw [hbit l, hmask_bit v l]
  let W : V → Opt := fun v => if h : v.val ≠ 0 then (hopt_ex v h).choose else ⟨1, 0, 0, 1, 1⟩
  have hW_mem : ∀ v : V, v.val ≠ 0 → W v ∈ allOpts41 := fun v hv => by simp only [W, dite_eq_left hv]; exact (hopt_ex v hv).choose_spec.1
  have hW_id : ∀ v : V, v.val ≠ 0 → (W v).id = mask v := fun v hv => by simp only [W, dite_eq_left hv]; exact (hopt_ex v hv).choose_spec.2.1
  have hW_ok : ∀ v : V, v.val ≠ 0 → OptOk (W v) := fun v hv => by simp only [W, dite_eq_left hv]; exact (hopt_ex v hv).choose_spec.2.2.1
  have hW_lit : ∀ v : V, v.val ≠ 0 → ∀ l : Fin 10, optHasLit (W v) l.val = litP v l := fun v hv => by
    simp only [W, dite_eq_left hv]; exact (hopt_ex v hv).choose_spec.2.2.2
  let ch : Fin 16 → Fin 5 → Option Bool := fun k g => misChoice D'' (rows9 k) ⟨(σ.symm g).val, by omega⟩
  have hlitTrue_iff : ∀ (k : Fin 16) (u : V), u.val ≠ 0 → ∀ l : Fin 10,
      litTrue (ch k) l.val ↔ ch k ⟨l.val / 2, by omega⟩ = some (decide (l.val % 2 = 1)) := by
    intro k u _ l
    constructor
    · rintro ⟨g, b, hgb, heq⟩
      have hg : (⟨l.val / 2, by omega⟩ : Fin 5) = g := Fin.ext (by dsimp; cases b <;> simp at heq <;> omega)
      have hb : decide (l.val % 2 = 1) = b := by cases b <;> simp at heq ⊢ <;> omega
      rw [hg, hb]; exact hgb
    · intro h
      refine ⟨⟨l.val / 2, by omega⟩, decide (l.val % 2 = 1), h, ?_⟩
      by_cases hm : l.val % 2 = 1 <;> simp [hm] <;> omega
  have hSV : StepValid 8 W ch := by
    refine ⟨hW_ok, fun k u hu0 _ => ?_⟩
    have hcov := mis_cover_gen D'' (rows9 k) (hsep'' k).1
    have hok := hW_ok u hu0
    have hl1 : (W u).l1 < 10 := hok.1
    have hl2 : (W u).l2 < 10 := hok.2.1
    by_cases hum : u ∈ rows9 k
    · simp only [hum, ↓reduceIte]
      constructor
      · intro h1
        have h1' := (hlitTrue_iff k u hu0 ⟨(W u).l1, hl1⟩).mp h1
        have hhas : optHasLit (W u) (W u).l1 = true := by simp [optHasLit]
        rw [hW_lit u hu0 ⟨(W u).l1, hl1⟩] at hhas
        have hmem : (⟨(σ.symm ⟨(W u).l1 / 2, by omega⟩).val, by omega⟩, decide ((W u).l1 % 2 = 1)) ∈ litSet D'' u := by
          rw [mem_litSet]
          by_cases hm : (W u).l1 % 2 = 0
          · have hm1 : decide ((W u).l1 % 2 = 1) = false := decide_eq_false (by omega)
            rw [hm1]; simp only [Bool.false_eq_true, ↓reduceIte]; simpa [litP, hm] using hhas
          · have hm1 : decide ((W u).l1 % 2 = 1) = true := decide_eq_true (by omega)
            rw [hm1]; simp only [↓reduceIte]; simpa [litP, hm] using hhas
        exact hcov.1 u hum _ _ hmem h1'
      · intro h2
        have h2' := (hlitTrue_iff k u hu0 ⟨(W u).l2, hl2⟩).mp h2
        have hhas : optHasLit (W u) (W u).l2 = true := by simp [optHasLit]
        rw [hW_lit u hu0 ⟨(W u).l2, hl2⟩] at hhas
        have hmem : (⟨(σ.symm ⟨(W u).l2 / 2, by omega⟩).val, by omega⟩, decide ((W u).l2 % 2 = 1)) ∈ litSet D'' u := by
          rw [mem_litSet]
          by_cases hm : (W u).l2 % 2 = 0
          · have hm1 : decide ((W u).l2 % 2 = 1) = false := decide_eq_false (by omega)
            rw [hm1]; simp only [Bool.false_eq_true, ↓reduceIte]; simpa [litP, hm] using hhas
          · have hm1 : decide ((W u).l2 % 2 = 1) = true := decide_eq_true (by omega)
            rw [hm1]; simp only [↓reduceIte]; simpa [litP, hm] using hhas
        exact hcov.1 u hum _ _ hmem h2'
    · simp only [hum, ↓reduceIte]
      obtain ⟨g, b, hgb, hch⟩ := hcov.2 u hum (sep_outVars_empty hsep'' u) ((hsep'' k).2 u hum)
      let g' : Fin 5 := σ ⟨g.val, by omega⟩
      let l : Fin 10 := ⟨2 * g'.val + (if b then 1 else 0), by cases b <;> (simp; omega)⟩
      have hsym : σ.symm ⟨l.val / 2, by omega⟩ = ⟨g.val, by omega⟩ := by
        have : (⟨l.val / 2, by omega⟩ : Fin 5) = g' := Fin.ext (by dsimp [l]; cases b <;> (dsimp; omega))
        rw [this]; exact Equiv.symm_apply_apply σ _
      have hhas : optHasLit (W u) l.val = true := by
        rw [hW_lit u hu0 l]
        have hmem := (mem_litSet D'' u g b).mp hgb
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at hmem
          have hm0 : l.val % 2 = 0 := by dsimp [l]; omega
          simpa [litP, hm0, hsym] using hmem
        · simp only [↓reduceIte] at hmem
          have hm1 : l.val % 2 ≠ 0 := by dsimp [l]; omega
          simpa [litP, hm1, hsym] using hmem
      have hlt : litTrue (ch k) l.val := by
        refine ⟨g', b, ?_, rfl⟩
        dsimp only [ch, g']
        have : (⟨(σ.symm (σ ⟨g.val, by omega⟩)).val, by omega⟩ : Fin D''.size) = g :=
          Fin.ext (by simp [Equiv.symm_apply_apply])
        rw [this]; exact hch
      unfold optHasLit at hhas
      rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hhas
      rcases hhas with heq | heq
      · exact Or.inl (heq ▸ hlt)
      · exact Or.inr (heq ▸ hlt)
  have h0in : ∀ k : Fin 16, (0 : V) ∈ rows9 k → ch k 0 ≠ some false := by
    intro k hk
    have hcov := mis_cover_gen D'' (rows9 k) (hsep'' k).1
    have hsym0 : σ.symm 0 = a0 := by rw [← hσ_a0, Equiv.symm_apply_apply]
    have h0mem : (⟨(σ.symm 0).val, by omega⟩, false) ∈ litSet D'' 0 := by
      rw [mem_litSet]; simp only [Bool.false_eq_true, ↓reduceIte, hsym0, hLa0'', Finset.mem_singleton]
    exact hcov.1 0 hk _ false h0mem
  have h0out : ∀ k : Fin 16, (0 : V) ∉ rows9 k → ch k 0 = some false := by
    intro k hk
    have hsym0 : σ.symm 0 = a0 := by rw [← hσ_a0, Equiv.symm_apply_apply]
    dsimp only [ch]
    have heq : (⟨(σ.symm 0).val, by omega⟩ : Fin D''.size) = ⟨a0.val, by omega⟩ :=
      Fin.ext (congrArg (Fin.val : Fin 5 → Nat) hsym0)
    rw [heq]; unfold misChoice; rw [(hno0'' k hk).1]; rfl
  have hinit : ∀ k : Fin 16, ForbValid (initF16.get k) (ch k) := by
    intro k l hl
    obtain ⟨g, b, hgb, rfl⟩ := hl
    have hcases : (initF16.get k) = if (0 : V) ∈ rows9 k then forb0In else forb0Out := by
      fin_cases k <;> decide
    rw [hcases]
    by_cases h0 : (0 : V) ∈ rows9 k
    · rw [ite_eq_left h0]
      fin_cases g <;> cases b <;> try rfl
      change ch k 0 = some false at hgb
      exact (h0in k h0 hgb).elim
    · rw [ite_eq_right h0]
      fin_cases g <;> cases b <;> try rfl
      change ch k 0 = some true at hgb
      rw [h0out k h0] at hgb; cases hgb
  have hnot_sub : ∀ u v : V, u.val ≠ 0 → v.val ≠ 0 → u ≠ v → subOpt (W u) (W v) = false := by
    intro u v hu0 hv0 huv
    rw [Bool.eq_false_iff]; intro hsub
    obtain ⟨k, hvin, huout⟩ := sep_all u v huv
    have h1 := hSV.2 k v hv0 (by omega); simp only [hvin, ↓reduceIte] at h1
    have h2 := hSV.2 k u hu0 (by omega); simp only [huout, ↓reduceIte] at h2
    unfold subOpt at hsub
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hsub
    rcases h2 with hl1 | hl2
    · rcases hsub.1 with e | e <;> (rw [e] at hl1; first | exact h1.1 hl1 | exact h1.2 hl1)
    · rcases hsub.2 with e | e <;> (rw [e] at hl2; first | exact h1.1 hl2 | exact h1.2 hl2)
  have hanti : ∀ (v : V) (us : List V), v.val ≠ 0 → (∀ u ∈ us, u.val ≠ 0 ∧ u ≠ v) →
      antiOk (W v) (us.map W) = true := by
    intro v us hv0 hus
    induction us with
    | nil => rfl
    | cons u rest ih =>
      obtain ⟨hu0, huv⟩ := hus u (List.mem_cons_self ..)
      simp only [List.map_cons, antiOk, hnot_sub v u hv0 hu0 huv.symm, hnot_sub u v hu0 hv0 huv,
        Bool.not_false, Bool.true_and]
      exact ih (fun x hx => hus x (List.mem_cons_of_mem _ hx))
  let usedG : Nat → Nat := usedGOf W
  have husedG_lt : ∀ n : Nat, n ≤ 8 → usedG n < 16 := by
    have hgm_lt : ∀ o ∈ allOpts41, optGm4 o < 16 := by decide +kernel
    have hor_lt : ∀ a b : Fin 16, (a.val ||| b.val) < 16 := by decide +kernel
    intro n hn
    induction n with
    | zero => dsimp only [usedG, usedGOf]; decide
    | succ m ih =>
      have hm16 : usedG m < 16 := ih (by omega)
      have hmod : (m + 1) % 9 = m + 1 := Nat.mod_eq_of_lt (by omega)
      have hgm16 : optGm4 (W ⟨(m + 1) % 9, Nat.mod_lt _ (by decide)⟩) < 16 :=
        hgm_lt _ (hW_mem _ (by dsimp; omega))
      exact hor_lt ⟨usedG m, hm16⟩ ⟨optGm4 (W ⟨(m + 1) % 9, Nat.mod_lt _ (by decide)⟩), hgm16⟩
  have hgm4_bit : ∀ (v : V) (hv0 : v.val ≠ 0) (g : Fin 4),
      (optGm4 (W v)).testBit g.val = true ↔
      (v ∈ D''.leftVars ⟨(σ.symm ⟨g.val + 1, by omega⟩).val, by omega⟩ ∨
       v ∈ D''.rightVars ⟨(σ.symm ⟨g.val + 1, by omega⟩).val, by omega⟩) := by
    intro v hv0 g
    have hgm_iff : ∀ o ∈ allOpts41, ∀ g : Fin 4,
        (optGm4 o).testBit g.val = true ↔
        (optHasLit o (2 * (g.val + 1)) = true ∨ optHasLit o (2 * (g.val + 1) + 1) = true) := by
      decide +kernel
    rw [hgm_iff (W v) (hW_mem v hv0) g]
    have hL := hW_lit v hv0 ⟨2 * (g.val + 1), by omega⟩
    have hR := hW_lit v hv0 ⟨2 * (g.val + 1) + 1, by omega⟩
    have hm0 : (2 * (g.val + 1)) % 2 = 0 := by omega
    have hm1 : (2 * (g.val + 1) + 1) % 2 ≠ 0 := by omega
    have hd0 : (⟨(2 * (g.val + 1)) / 2, by omega⟩ : Fin 5) = ⟨g.val + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    have hd1 : (⟨(2 * (g.val + 1) + 1) / 2, by omega⟩ : Fin 5) = ⟨g.val + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hL, hR]; simp only [litP, hm0, hm1, ↓reduceIte, hd0, hd1, decide_eq_true_eq]
  have husedG_bit : ∀ (n : Nat) (hn : n ≤ 8) (g : Fin 4),
      (usedG n).testBit g.val = true ↔
      ∃ u : V, u.val ≠ 0 ∧ u.val ≤ n ∧
        (u ∈ D''.leftVars ⟨(σ.symm ⟨g.val + 1, by omega⟩).val, by omega⟩ ∨
         u ∈ D''.rightVars ⟨(σ.symm ⟨g.val + 1, by omega⟩).val, by omega⟩) := by
    intro n
    induction n with
    | zero =>
      intro _ g; simp only [usedG, usedGOf, Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro u hu0 hle; omega
    | succ m ih =>
      intro hm g
      have hmod : (⟨(m + 1) % 9, Nat.mod_lt _ (by decide)⟩ : V) = ⟨m + 1, by omega⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      change (usedG m ||| optGm4 (W ⟨(m + 1) % 9, Nat.mod_lt _ (by decide)⟩)).testBit g.val = true ↔ _
      rw [hmod, Nat.testBit_lor, Bool.or_eq_true, ih (by omega) g, hgm4_bit ⟨m + 1, by omega⟩ (by dsimp; omega) g]
      constructor
      · rintro (⟨u, hu0, hle, hhit⟩ | hhit)
        · exact ⟨u, hu0, by omega, hhit⟩
        · exact ⟨⟨m + 1, by omega⟩, by dsimp; omega, le_refl _, hhit⟩
      · rintro ⟨u, hu0, hle, hhit⟩
        by_cases heq : u.val = m + 1
        · right; have : u = ⟨m + 1, by omega⟩ := Fin.ext heq; rwa [← this]
        · left; exact ⟨u, hu0, by omega, hhit⟩
  have hoptsFor_step : ∀ (n : Nat) (hn : 1 ≤ n) (hn8 : n ≤ 8),
      (W ⟨n, by omega⟩, usedG n) ∈ optsFor (usedG (n - 1)) := by
    intro n hn hn8
    have hnm : n - 1 + 1 = n := by omega
    have hused_eq : usedG n = usedG (n - 1) ||| optGm4 (W ⟨n, by omega⟩) := by
      have hmod : (⟨(n - 1 + 1) % 9, Nat.mod_lt _ (by decide)⟩ : V) = ⟨n, by omega⟩ :=
        Fin.ext (by dsimp; rw [hnm]; exact Nat.mod_eq_of_lt (by omega))
      conv_lhs => rw [← hnm]
      change usedG (n - 1) ||| optGm4 (W ⟨(n - 1 + 1) % 9, Nat.mod_lt _ (by decide)⟩) = _
      rw [hmod]
    rw [hused_eq]
    have hlt := husedG_lt (n - 1) (by omega)
    apply optsFor_complete ⟨usedG (n - 1), hlt⟩ (W ⟨n, by omega⟩) (hW_mem ⟨n, by omega⟩ (by dsimp; omega))
    unfold optCanonOk
    rw [List.all_eq_true]
    intro g hg
    have hg4 : g < 4 := List.mem_range.mp hg
    by_cases hug : (usedG (n - 1)).testBit g = true
    · simp [hug]
    · simp only [hug, Bool.false_eq_true, ↓reduceIte]
      by_cases hgm : (optGm4 (W ⟨n, by omega⟩)).testBit g = true
      · simp only [hgm, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
        let h : Fin 5 := σ.symm ⟨g + 1, by omega⟩
        have hha0 : h ≠ a0 := by
          intro heq
          have : (⟨g + 1, by omega⟩ : Fin 5) = σ h := (Equiv.apply_symm_apply σ _).symm
          rw [heq, hσ_a0] at this; have := congrArg Fin.val this; simp at this
        have hhit_n : (⟨n, by omega⟩ : V) ∈ D'.leftVars ⟨h.val, by omega⟩ ∨
            (⟨n, by omega⟩ : V) ∈ D'.rightVars ⟨h.val, by omega⟩ :=
          (hhit_eq h ⟨n, by omega⟩).mp ((hgm4_bit ⟨n, by omega⟩ (by dsimp; omega) ⟨g, hg4⟩).mp hgm)
        have hfirst_le_n : firstV h ≤ n := hfirstV_spec h ⟨n, by omega⟩ (by dsimp; omega) hhit_n
        have hfirst_eq : firstV h = n := by
          apply le_antisymm hfirst_le_n
          by_contra hlt'
          have hfl : firstV h < 9 := by omega
          have hfh := (hhit_eq h ⟨firstV h, hfl⟩).mpr (hfirstV_hit h hfl)
          have hpos : firstV h ≠ 0 := by
            dsimp only [firstV]
            split_ifs with hne
            · have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ((hitSet h).min'_mem hne)).1).1; omega
            · omega
          have := (husedG_bit (n - 1) (by omega) ⟨g, hg4⟩).mpr
            ⟨⟨firstV h, hfl⟩, by dsimp; omega, by dsimp; omega, hfh⟩
          exact hug this
        constructor
        · rw [hW_lit ⟨n, by omega⟩ (by dsimp; omega) ⟨2 * (g + 1) + 1, by omega⟩]
          have hm1 : (2 * (g + 1) + 1) % 2 ≠ 0 := by omega
          have hd1 : (⟨(2 * (g + 1) + 1) / 2, by omega⟩ : Fin 5) = ⟨g + 1, by omega⟩ := Fin.ext (by dsimp; omega)
          simp only [litP, hm1, ↓reduceIte, hd1, decide_eq_false_iff_not]
          have hfnR := hfirst_notR h hha0 (by omega : firstV h < 9)
          have heqv : (⟨n, by omega⟩ : V) = ⟨firstV h, by omega⟩ := Fin.ext hfirst_eq.symm
          rw [heqv]; exact hfnR
        · intro g' hg'
          have hg'g : g' < g := List.mem_range.mp hg'
          let h' : Fin 5 := σ.symm ⟨g' + 1, by omega⟩
          have hh'a0 : h' ≠ a0 := by
            intro heq
            have : (⟨g' + 1, by omega⟩ : Fin 5) = σ h' := (Equiv.apply_symm_apply σ _).symm
            rw [heq, hσ_a0] at this; have := congrArg Fin.val this; simp at this
          have hσlt : (σ h').val < (σ h).val := by
            simp only [h', h, Equiv.apply_symm_apply]; omega
          have hklt := hσ_mono h' h hσlt
          simp only [key, hh'a0, hha0, ↓reduceIte] at hklt
          have hfle : firstV h' ≤ n := by omega
          have hfl9 : firstV h' < 9 := by omega
          have hfh' := (hhit_eq h' ⟨firstV h', hfl9⟩).mpr (hfirstV_hit h' hfl9)
          have hpos' : firstV h' ≠ 0 := by
            dsimp only [firstV]
            split_ifs with hne
            · have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ((hitSet h').min'_mem hne)).1).1; omega
            · omega
          rw [Bool.or_eq_true]
          by_cases hlt_n : firstV h' < n
          · exact Or.inl ((husedG_bit (n - 1) (by omega) ⟨g', by omega⟩).mpr ⟨⟨firstV h', hfl9⟩, by dsimp; omega, by dsimp; omega, hfh'⟩)
          · have heqn : firstV h' = n := by omega
            have heqv : (⟨firstV h', hfl9⟩ : V) = ⟨n, by omega⟩ := Fin.ext heqn
            rw [heqv] at hfh'
            exact Or.inr ((hgm4_bit ⟨n, by omega⟩ (by dsimp; omega) ⟨g', by omega⟩).mpr hfh')
      · simp [hgm]
  have hSV_le : ∀ v : Nat, v ≤ 8 → StepValid v W ch :=
    fun v _ => ⟨hSV.1, fun k u hu0 hle => hSV.2 k u hu0 (by omega)⟩
  obtain ⟨st1, hst1, hfv1⟩ := stepF16_1_sound initF16 W ch hinit (hSV_le 1 (by decide))
  obtain ⟨st2, hst2, hfv2⟩ := stepF16_2_sound st1 W ch hfv1 (hSV_le 2 (by decide))
  obtain ⟨st3, hst3, hfv3⟩ := stepF16_3_sound st2 W ch hfv2 (hSV_le 3 (by decide))
  obtain ⟨st4, hst4, hfv4⟩ := stepF16_4_sound st3 W ch hfv3 (hSV_le 4 (by decide))
  obtain ⟨st5, hst5, hfv5⟩ := stepF16_5_sound st4 W ch hfv4 (hSV_le 5 (by decide))
  obtain ⟨st6, hst6, hfv6⟩ := stepF16_6_sound st5 W ch hfv5 (hSV_le 6 (by decide))
  obtain ⟨st7, hst7, hfv7⟩ := stepF16_7_sound st6 W ch hfv6 (hSV_le 7 (by decide))
  obtain ⟨st8, hst8, _⟩ := stepF16_8_sound st7 W ch hfv7 (hSV_le 8 (by decide))
  have hfull := checkFull_sound W ch hSV h0in h0out
  let c : List Nat := [(W 1).id, (W 2).id, (W 3).id, (W 4).id, (W 5).id, (W 6).id, (W 7).id, (W 8).id]
  have hc8 : c ∈ run8 (usedG 7) st7 (W 1) (W 2) (W 3) (W 4) (W 5) (W 6) (W 7) := by
    unfold run8; rw [List.mem_flatMap]
    refine ⟨(W 8, usedG 8), hoptsFor_step 8 (by decide) (by decide), ?_⟩
    have ha := hanti 8 [1,2,3,4,5,6,7] (by decide) (by decide)
    simp only [List.map_cons, List.map_nil] at ha
    dsimp only; rw [ha]; simp only [↓reduceIte, hst8, hfull, List.mem_singleton]; rfl
  have hc7 : c ∈ run7 (usedG 6) st6 (W 1) (W 2) (W 3) (W 4) (W 5) (W 6) := by
    unfold run7; rw [List.mem_flatMap]
    refine ⟨(W 7, usedG 7), hoptsFor_step 7 (by decide) (by decide), ?_⟩
    have ha := hanti 7 [1,2,3,4,5,6] (by decide) (by decide)
    simp only [List.map_cons, List.map_nil] at ha
    dsimp only; rw [ha]; simp only [↓reduceIte, hst7]; exact hc8
  have hc6 : c ∈ run6 (usedG 5) st5 (W 1) (W 2) (W 3) (W 4) (W 5) := by
    unfold run6; rw [List.mem_flatMap]
    refine ⟨(W 6, usedG 6), hoptsFor_step 6 (by decide) (by decide), ?_⟩
    have ha := hanti 6 [1,2,3,4,5] (by decide) (by decide)
    simp only [List.map_cons, List.map_nil] at ha
    dsimp only; rw [ha]; simp only [↓reduceIte, hst6]; exact hc7
  have hc5 : c ∈ run5 (usedG 4) st4 (W 1) (W 2) (W 3) (W 4) := by
    unfold run5; rw [List.mem_flatMap]
    refine ⟨(W 5, usedG 5), hoptsFor_step 5 (by decide) (by decide), ?_⟩
    have ha := hanti 5 [1,2,3,4] (by decide) (by decide)
    simp only [List.map_cons, List.map_nil] at ha
    dsimp only; rw [ha]; simp only [↓reduceIte, hst5]; exact hc6
  have hc4 : c ∈ run4 (usedG 3) st3 (W 1) (W 2) (W 3) := by
    unfold run4; rw [List.mem_flatMap]
    refine ⟨(W 4, usedG 4), hoptsFor_step 4 (by decide) (by decide), ?_⟩
    have ha := hanti 4 [1,2,3] (by decide) (by decide)
    simp only [List.map_cons, List.map_nil] at ha
    dsimp only; rw [ha]; simp only [↓reduceIte, hst4]; exact hc5
  have hc3 : c ∈ run3 (usedG 2) st2 (W 1) (W 2) := by
    unfold run3; rw [List.mem_flatMap]
    refine ⟨(W 3, usedG 3), hoptsFor_step 3 (by decide) (by decide), ?_⟩
    have ha := hanti 3 [1,2] (by decide) (by decide)
    simp only [List.map_cons, List.map_nil] at ha
    dsimp only; rw [ha]; simp only [↓reduceIte, hst3]; exact hc4
  have hcB : c ∈ runBranch (W 1) (W 2) (usedG 2) := by
    unfold runBranch; rw [hst1]; dsimp only; rw [hst2]; exact hc3
  have hsig1 : optHasLit (W 1) 1 = false → optHasLit (W 2) 1 = false := by
    intro h1f
    have hsym0 : σ.symm 0 = a0 := by rw [← hσ_a0, Equiv.symm_apply_apply]
    have h1n : (1 : V) ∉ D'.rightVars ⟨a0.val, by omega⟩ := by
      rw [← hRa0'']
      have hw1 := hW_lit 1 (by decide) 1
      simp only [Fin.val_one] at hw1
      rw [h1f] at hw1
      simpa [litP, hsym0] using hw1.symm
    have h2n : (2 : V) ∉ D''.rightVars ⟨a0.val, by omega⟩ := by rw [hRa0'']; exact h12 h1n
    have hw2 := hW_lit 2 (by decide) 1
    simp only [Fin.val_one] at hw2
    rw [hw2]
    simpa [litP, hsym0] using h2n
  have hpvalid : (W 1, W 2, usedG 2) ∈ validW12Pairs := by
    apply w12_mem_valid (W 1, usedG 1) (hoptsFor_step 1 (by decide) (by decide))
      (W 2, usedG 2) (hoptsFor_step 2 (by decide) (by decide)) hsig1
    · dsimp only; rw [hst1]; rfl
    · dsimp only; rw [hst1]; dsimp only; rw [hst2]; rfl
  refine ⟨D'', hsz'', σ, hW'', hD'', hsep'', hσ_a0, hLa0'', h0R'', h0oth'', hno0'',
    (W 1, W 2, usedG 2), hpvalid, c, hcB, rfl, ?_⟩
  intro v hv0 g
  have hcid : c.getD (v.val - 1) 0 = (W v).id := by
    fin_cases v <;> first | (exfalso; exact hv0 rfl) | rfl
  rw [hcid, hW_id v hv0]
  have hL := hmask_bit v ⟨2 * g.val, by omega⟩
  have hR := hmask_bit v ⟨2 * g.val + 1, by omega⟩
  have hm0 : (2 * g.val) % 2 = 0 := by omega
  have hm1 : (2 * g.val + 1) % 2 ≠ 0 := by omega
  have hd0 : (⟨(2 * g.val) / 2, by omega⟩ : Fin 5) = g := Fin.ext (by dsimp; omega)
  have hd1 : (⟨(2 * g.val + 1) / 2, by omega⟩ : Fin 5) = g := Fin.ext (by dsimp; omega)
  rw [hL, hR]; simp only [litP, hm0, hm1, ↓reduceIte, hd0, hd1, decide_eq_true_eq, and_self]


/-! ## Section 5: Phase 2 (`U16` topological completion search) and `maxCircuit` soundness -/

structure B5 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  deriving DecidableEq

def B5.anyAnd (x y : B5) : Bool :=
  (x.b0&&y.b0) || (x.b1&&y.b1) || (x.b2&&y.b2) || (x.b3&&y.b3) || (x.b4&&y.b4)
def B5.get (x : B5) : Nat → Bool
  | 0 => x.b0 | 1 => x.b1 | 2 => x.b2 | 3 => x.b3 | _ => x.b4
def B5.set (x : B5) : Nat → B5
  | 0 => {x with b0 := true} | 1 => {x with b1 := true}
  | 2 => {x with b2 := true} | 3 => {x with b3 := true}
  | _ => {x with b4 := true}
def B5.not (x : B5) : B5 := ⟨!x.b0, !x.b1, !x.b2, !x.b3, !x.b4⟩
def B5.ofFn (f : Fin 5 → Bool) : B5 := ⟨f 0, f 1, f 2, f 3, f 4⟩

lemma B5.get_ofFn (f : Fin 5 → Bool) (i : Fin 5) : (B5.ofFn f).get i.val = f i := by
  fin_cases i <;> rfl

lemma B5.anyAnd_eq_true (x y : B5) :
    B5.anyAnd x y = true ↔ ∃ i : Fin 5, x.get i.val = true ∧ y.get i.val = true := by
  constructor
  · cases x; cases y; unfold B5.anyAnd B5.get
    intro h; simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((h | h) | h) | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · rintro ⟨i, h1, h2⟩
    fin_cases i <;> simp_all [B5.anyAnd, B5.get]

lemma B5.get_set (x : B5) (i j : Fin 5) :
    (x.set i.val).get j.val = (if i = j then true else x.get j.val) := by
  fin_cases i <;> fin_cases j <;> rfl

lemma B5.get_not (x : B5) (i : Fin 5) : (B5.not x).get i.val = !(x.get i.val) := by
  fin_cases i <;> rfl

structure B9 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  b8 : Bool
  deriving DecidableEq

def B9.get (x : B9) : Nat → Bool
  | 0 => x.b0 | 1 => x.b1 | 2 => x.b2 | 3 => x.b3 | 4 => x.b4
  | 5 => x.b5 | 6 => x.b6 | 7 => x.b7 | _ => x.b8
def B9.ofFn (f : Fin 9 → Bool) : B9 := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8⟩
def B9.anyAnd (x y : B9) : Bool :=
  (x.b0&&y.b0)||(x.b1&&y.b1)||(x.b2&&y.b2)||(x.b3&&y.b3)||(x.b4&&y.b4)||
  (x.b5&&y.b5)||(x.b6&&y.b6)||(x.b7&&y.b7)||(x.b8&&y.b8)
def B9.diff (x y : B9) : B9 :=
  ⟨x.b0 && !y.b0, x.b1 && !y.b1, x.b2 && !y.b2, x.b3 && !y.b3, x.b4 && !y.b4,
   x.b5 && !y.b5, x.b6 && !y.b6, x.b7 && !y.b7, x.b8 && !y.b8⟩
def B9.sub (x y : B9) : Bool :=
  (!x.b0||y.b0)&&(!x.b1||y.b1)&&(!x.b2||y.b2)&&(!x.b3||y.b3)&&(!x.b4||y.b4)&&
  (!x.b5||y.b5)&&(!x.b6||y.b6)&&(!x.b7||y.b7)&&(!x.b8||y.b8)

lemma B9.get_ofFn (f : Fin 9 → Bool) (v : Fin 9) : (B9.ofFn f).get v.val = f v := by
  fin_cases v <;> rfl

lemma B9.anyAnd_eq_true (x y : B9) :
    B9.anyAnd x y = true ↔ ∃ v : Fin 9, x.get v.val = true ∧ y.get v.val = true := by
  constructor
  · cases x; cases y; unfold B9.anyAnd B9.get
    intro h; simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
    · exact ⟨7, h⟩
    · exact ⟨8, h⟩
  · rintro ⟨v, h1, h2⟩
    fin_cases v <;> simp_all [B9.anyAnd, B9.get]

lemma B9.get_diff (x y : B9) (v : Fin 9) :
    (B9.diff x y).get v.val = (x.get v.val && !(y.get v.val)) := by
  fin_cases v <;> rfl

lemma bool_imp_or (a b : Bool) (h : a = true → b = true) : (!a || b) = true := by
  cases a <;> simp_all

lemma B9.sub_eq_true (x y : B9) :
    B9.sub x y = true ↔ ∀ v : Fin 9, x.get v.val = true → y.get v.val = true := by
  cases x; cases y; unfold B9.sub
  constructor
  · intro h v hv
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    fin_cases v <;> simp_all [B9.get]
  · intro h
    have h0 := bool_imp_or _ _ (h ⟨0, by decide⟩); have h1 := bool_imp_or _ _ (h ⟨1, by decide⟩)
    have h2 := bool_imp_or _ _ (h ⟨2, by decide⟩); have h3 := bool_imp_or _ _ (h ⟨3, by decide⟩)
    have h4 := bool_imp_or _ _ (h ⟨4, by decide⟩); have h5 := bool_imp_or _ _ (h ⟨5, by decide⟩)
    have h6 := bool_imp_or _ _ (h ⟨6, by decide⟩); have h7 := bool_imp_or _ _ (h ⟨7, by decide⟩)
    have h8 := bool_imp_or _ _ (h ⟨8, by decide⟩)
    simp only [B9.get] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, Bool.and_self]

structure B16 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  b8 : Bool
  b9 : Bool
  b10 : Bool
  b11 : Bool
  b12 : Bool
  b13 : Bool
  b14 : Bool
  b15 : Bool
  deriving DecidableEq

def B16.get (x : B16) (k : Fin 16) : Bool :=
  match k.val with
  | 0 => x.b0 | 1 => x.b1 | 2 => x.b2 | 3 => x.b3
  | 4 => x.b4 | 5 => x.b5 | 6 => x.b6 | 7 => x.b7
  | 8 => x.b8 | 9 => x.b9 | 10 => x.b10 | 11 => x.b11
  | 12 => x.b12 | 13 => x.b13 | 14 => x.b14 | _ => x.b15
def B16.ofFn (f : Fin 16 → Bool) : B16 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15⟩
def B16.and (x y : B16) : B16 :=
  ⟨x.b0&&y.b0, x.b1&&y.b1, x.b2&&y.b2, x.b3&&y.b3, x.b4&&y.b4, x.b5&&y.b5, x.b6&&y.b6, x.b7&&y.b7,
   x.b8&&y.b8, x.b9&&y.b9, x.b10&&y.b10, x.b11&&y.b11, x.b12&&y.b12, x.b13&&y.b13, x.b14&&y.b14, x.b15&&y.b15⟩
def B16.or (x y : B16) : B16 :=
  ⟨x.b0||y.b0, x.b1||y.b1, x.b2||y.b2, x.b3||y.b3, x.b4||y.b4, x.b5||y.b5, x.b6||y.b6, x.b7||y.b7,
   x.b8||y.b8, x.b9||y.b9, x.b10||y.b10, x.b11||y.b11, x.b12||y.b12, x.b13||y.b13, x.b14||y.b14, x.b15||y.b15⟩
def B16.isZero (x : B16) : Bool :=
  !(x.b0||x.b1||x.b2||x.b3||x.b4||x.b5||x.b6||x.b7||x.b8||x.b9||x.b10||x.b11||x.b12||x.b13||x.b14||x.b15)
def B16.sub (x y : B16) : Bool :=
  (!x.b0||y.b0)&&(!x.b1||y.b1)&&(!x.b2||y.b2)&&(!x.b3||y.b3)&&(!x.b4||y.b4)&&(!x.b5||y.b5)&&(!x.b6||y.b6)&&(!x.b7||y.b7)&&
  (!x.b8||y.b8)&&(!x.b9||y.b9)&&(!x.b10||y.b10)&&(!x.b11||y.b11)&&(!x.b12||y.b12)&&(!x.b13||y.b13)&&(!x.b14||y.b14)&&(!x.b15||y.b15)

lemma B16.ext {x y : B16} (h : ∀ k : Fin 16, x.get k = y.get k) : x = y := by
  cases x; cases y
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  have h8 := h 8; have h9 := h 9; have h10 := h 10; have h11 := h 11
  have h12 := h 12; have h13 := h 13; have h14 := h 14; have h15 := h 15
  simp only [B16.get] at *
  subst_vars; rfl

lemma B16.get_ofFn (f : Fin 16 → Bool) (k : Fin 16) : (B16.ofFn f).get k = f k := by
  fin_cases k <;> rfl
lemma B16.get_and (x y : B16) (k : Fin 16) : (B16.and x y).get k = (x.get k && y.get k) := by
  fin_cases k <;> rfl
lemma B16.get_or (x y : B16) (k : Fin 16) : (B16.or x y).get k = (x.get k || y.get k) := by
  fin_cases k <;> rfl
lemma B16.isZero_eq_true (x : B16) : B16.isZero x = true ↔ ∀ k : Fin 16, x.get k = false := by
  cases x; unfold B16.isZero B16.get
  constructor
  · intro h k; fin_cases k <;> simp_all
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
    have h8 := h 8; have h9 := h 9; have h10 := h 10; have h11 := h 11
    have h12 := h 12; have h13 := h 13; have h14 := h 14; have h15 := h 15
    simp_all
lemma B16.sub_eq_true (x y : B16) :
    B16.sub x y = true ↔ ∀ k : Fin 16, x.get k = true → y.get k = true := by
  cases x; cases y; unfold B16.sub
  constructor
  · intro h k hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    fin_cases k <;> simp_all [B16.get]
  · intro h
    have h0 := bool_imp_or _ _ (h ⟨0, by decide⟩); have h1 := bool_imp_or _ _ (h ⟨1, by decide⟩)
    have h2 := bool_imp_or _ _ (h ⟨2, by decide⟩); have h3 := bool_imp_or _ _ (h ⟨3, by decide⟩)
    have h4 := bool_imp_or _ _ (h ⟨4, by decide⟩); have h5 := bool_imp_or _ _ (h ⟨5, by decide⟩)
    have h6 := bool_imp_or _ _ (h ⟨6, by decide⟩); have h7 := bool_imp_or _ _ (h ⟨7, by decide⟩)
    have h8 := bool_imp_or _ _ (h ⟨8, by decide⟩); have h9 := bool_imp_or _ _ (h ⟨9, by decide⟩)
    have h10 := bool_imp_or _ _ (h ⟨10, by decide⟩); have h11 := bool_imp_or _ _ (h ⟨11, by decide⟩)
    have h12 := bool_imp_or _ _ (h ⟨12, by decide⟩); have h13 := bool_imp_or _ _ (h ⟨13, by decide⟩)
    have h14 := bool_imp_or _ _ (h ⟨14, by decide⟩); have h15 := bool_imp_or _ _ (h ⟨15, by decide⟩)
    simp only [B16.get] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Bool.and_self]

structure U16 where
  u0 : B9
  u1 : B9
  u2 : B9
  u3 : B9
  u4 : B9
  u5 : B9
  u6 : B9
  u7 : B9
  u8 : B9
  u9 : B9
  u10 : B9
  u11 : B9
  u12 : B9
  u13 : B9
  u14 : B9
  u15 : B9

def U16.get (uc : U16) (k : Fin 16) : B9 :=
  match k.val with
  | 0 => uc.u0 | 1 => uc.u1 | 2 => uc.u2 | 3 => uc.u3
  | 4 => uc.u4 | 5 => uc.u5 | 6 => uc.u6 | 7 => uc.u7
  | 8 => uc.u8 | 9 => uc.u9 | 10 => uc.u10 | 11 => uc.u11
  | 12 => uc.u12 | 13 => uc.u13 | 14 => uc.u14 | _ => uc.u15

def onesB9 : List B9 := [⟨true,true,false,true,true,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,false,false⟩, ⟨false,true,true,true,true,false,false,false,false⟩, ⟨true,true,false,false,true,true,false,false,false⟩, ⟨true,false,true,false,true,true,false,false,false⟩, ⟨true,false,false,true,true,true,false,false,false⟩, ⟨false,false,true,true,true,true,false,false,false⟩, ⟨true,true,false,true,false,false,true,false,false⟩, ⟨true,false,true,true,false,false,true,false,false⟩, ⟨true,false,false,true,true,false,true,false,false⟩, ⟨false,false,true,true,true,false,true,false,false⟩, ⟨true,true,false,false,false,true,true,false,false⟩, ⟨true,false,true,false,false,true,true,false,false⟩, ⟨false,true,true,false,false,true,true,false,false⟩, ⟨true,false,false,true,false,true,true,false,false⟩, ⟨false,true,false,true,false,true,true,false,false⟩, ⟨true,false,false,false,true,true,true,false,false⟩, ⟨false,true,false,false,true,true,true,false,false⟩, ⟨true,true,true,false,false,false,false,true,false⟩, ⟨false,true,true,true,false,false,false,true,false⟩, ⟨true,true,false,false,true,false,false,true,false⟩, ⟨true,false,true,false,true,false,false,true,false⟩, ⟨false,true,true,false,true,false,false,true,false⟩, ⟨true,false,false,true,true,false,false,true,false⟩, ⟨false,false,true,true,true,false,false,true,false⟩, ⟨false,true,true,false,false,true,false,true,false⟩, ⟨true,false,false,false,true,true,false,true,false⟩, ⟨false,false,true,false,true,true,false,true,false⟩, ⟨true,true,false,false,false,false,true,true,false⟩, ⟨true,false,true,false,false,false,true,true,false⟩, ⟨false,true,true,false,false,false,true,true,false⟩, ⟨true,false,false,true,false,false,true,true,false⟩, ⟨false,true,false,true,false,false,true,true,false⟩, ⟨true,false,false,false,true,false,true,true,false⟩, ⟨false,true,false,false,true,false,true,true,false⟩, ⟨false,false,true,false,true,false,true,true,false⟩, ⟨true,false,false,false,false,true,true,true,false⟩, ⟨false,true,false,false,false,true,true,true,false⟩, ⟨true,true,true,false,false,false,false,false,true⟩, ⟨true,true,false,true,false,false,false,false,true⟩, ⟨true,false,true,true,false,false,false,false,true⟩, ⟨false,true,true,true,false,false,false,false,true⟩, ⟨false,true,true,false,true,false,false,false,true⟩, ⟨true,false,false,true,true,false,false,false,true⟩, ⟨false,false,true,true,true,false,false,false,true⟩, ⟨true,true,false,false,false,true,false,false,true⟩, ⟨true,false,true,false,false,true,false,false,true⟩, ⟨false,true,true,false,false,true,false,false,true⟩, ⟨true,false,false,true,false,true,false,false,true⟩, ⟨false,true,false,true,false,true,false,false,true⟩, ⟨false,false,true,true,false,true,false,false,true⟩, ⟨true,false,false,false,true,true,false,false,true⟩, ⟨false,true,false,false,true,true,false,false,true⟩, ⟨false,true,true,false,false,false,true,false,true⟩, ⟨true,false,false,true,false,false,true,false,true⟩, ⟨false,false,true,true,false,false,true,false,true⟩, ⟨true,false,false,false,false,true,true,false,true⟩, ⟨false,true,false,false,false,true,true,false,true⟩, ⟨false,true,true,false,false,false,false,true,true⟩, ⟨true,false,false,true,false,false,false,true,true⟩, ⟨false,false,true,true,false,false,false,true,true⟩, ⟨true,false,false,false,true,false,false,true,true⟩, ⟨false,false,true,false,true,false,false,true,true⟩, ⟨true,false,false,false,false,true,false,true,true⟩, ⟨false,true,false,false,false,true,false,true,true⟩, ⟨true,false,false,false,false,false,true,true,true⟩, ⟨false,true,false,false,false,false,true,true,true⟩]
def initU16 : U16 := ⟨⟨false,true,true,false,false,true,true,true,true⟩, ⟨true,true,false,false,false,true,true,true,true⟩, ⟨false,true,true,true,false,false,true,true,true⟩, ⟨false,true,true,false,true,true,false,true,true⟩, ⟨false,true,true,true,true,false,false,true,true⟩, ⟨true,false,true,true,true,false,false,true,true⟩, ⟨true,false,false,true,true,true,true,false,true⟩, ⟨false,true,true,true,false,true,true,false,true⟩, ⟨true,true,false,true,false,true,true,false,true⟩, ⟨false,true,true,true,true,true,false,false,true⟩, ⟨true,false,true,true,true,true,false,false,true⟩, ⟨true,false,false,true,true,true,true,true,false⟩, ⟨false,true,true,false,true,true,true,true,false⟩, ⟨true,true,false,false,true,true,true,true,false⟩, ⟨false,true,true,true,true,false,true,true,false⟩, ⟨true,false,true,true,true,false,true,true,false⟩⟩
def no0AllFalse (s : B16) : Bool := !(s.b1 || s.b5 || s.b6 || s.b8 || s.b10 || s.b11 || s.b13 || s.b15)
def no0AllTrue (s : B16) : Bool := s.b1 && s.b5 && s.b6 && s.b8 && s.b10 && s.b11 && s.b13 && s.b15

lemma no0AllFalse_of (s : B16) (h : ∀ k : Fin 16, (0 : V) ∉ rows9 k → s.get k = false) :
    no0AllFalse s = true := by
  have h1 := h 1 (by decide); have h5 := h 5 (by decide); have h6 := h 6 (by decide)
  have h8 := h 8 (by decide); have h10 := h 10 (by decide); have h11 := h 11 (by decide)
  have h13 := h 13 (by decide); have h15 := h 15 (by decide)
  simp [no0AllFalse, B16.get] at *; simp_all

lemma no0AllTrue_of (s : B16) (h : ∀ k : Fin 16, (0 : V) ∉ rows9 k → s.get k = true) :
    no0AllTrue s = true := by
  have h1 := h 1 (by decide); have h5 := h 5 (by decide); have h6 := h 6 (by decide)
  have h8 := h 8 (by decide); have h10 := h 10 (by decide); have h11 := h 11 (by decide)
  have h13 := h 13 (by decide); have h15 := h 15 (by decide)
  simp [no0AllTrue, B16.get] at *; simp_all

lemma onesB9_spec : ∀ x ∈ onesB9, ∃ k : Fin 16, ∃ w : V, w ∉ rows9 k ∧
    ∀ v : V, x.get v.val = decide (v ∈ insert w (rows9 k)) := by
  decide +kernel

lemma initU16_spec (k : Fin 16) (v : V) :
    (initU16.get k).get v.val = decide (v ∉ rows9 k) := by
  revert k v; decide +kernel

structure GInfo where
  gIdx : Nat
  Lg : B9
  Rg : B9
  bmL : B16
  bmR : B16
  deriving DecidableEq

structure PlacedG where
  Lg : B9
  Rg : B9
  lgM : B5
  rgM : B5
  isOut : Bool

def evalOneGo (x : B9) : List PlacedG → Nat → B5 → Bool
  | [], _, _ => false
  | pg :: rest, idx, tm =>
    let sL := B9.anyAnd pg.Lg x || B5.anyAnd pg.lgM tm
    let sR := B9.anyAnd pg.Rg x || B5.anyAnd pg.rgM tm
    let gv := sL && sR
    if gv && pg.isOut then true
    else evalOneGo x rest (idx + 1) (if gv then B5.set tm idx else tm)

def evalOne (pgs : List PlacedG) (x : B9) : Bool :=
  evalOneGo x pgs 0 ⟨false,false,false,false,false⟩

def evalAllOnes (pgs : List PlacedG) : Bool :=
  onesB9.all (evalOne pgs)

def orB16 : List B16 → List Bool → B16 → B16
  | [], _, acc => acc
  | g :: gs, true :: bs, acc => orB16 gs bs (B16.or acc g)
  | _ :: gs, false :: bs, acc => orB16 gs bs acc
  | _, _, acc => acc

def toB5 : List Bool → B5
  | [b0] => ⟨b0,false,false,false,false⟩
  | [b0,b1] => ⟨b0,b1,false,false,false⟩
  | [b0,b1,b2] => ⟨b0,b1,b2,false,false⟩
  | [b0,b1,b2,b3] => ⟨b0,b1,b2,b3,false⟩
  | _ => ⟨false,false,false,false,false⟩

def boolLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let prev := boolLists n
    prev.map (false :: ·) ++ prev.map (true :: ·)

def isMaxMask : List B16 → List Bool → B16 → Bool
  | [], [], _ => true
  | g :: gs, b :: bs, s => (B16.sub g s == b) && isMaxMask gs bs s
  | _, _, _ => false

def collectMaxSides (i : Nat) (bm : B16) (gvms : List B16) (isG0 isR : Bool) : List (B16 × B5) :=
  (boolLists i).filterMap fun bs =>
    let s := orB16 gvms bs bm
    let ok0 := if isG0 then (if isR then no0AllTrue s else no0AllFalse s) else true
    if ok0 && isMaxMask gvms bs s then some (s, toB5 bs) else none

def upd1 (u Lg Rg : B9) (bL bR : Bool) : B9 :=
  if !bL then B9.diff u Lg else if !bR then B9.diff u Rg else u

def updateU16 (uc : U16) (sL sR : B16) (Lg Rg remV : B9) : Option U16 :=
  let u0 := upd1 uc.u0 Lg Rg sL.b0 sR.b0; if !(B9.sub u0 remV) then none else
  let u1 := upd1 uc.u1 Lg Rg sL.b1 sR.b1; if !(B9.sub u1 remV) then none else
  let u2 := upd1 uc.u2 Lg Rg sL.b2 sR.b2; if !(B9.sub u2 remV) then none else
  let u3 := upd1 uc.u3 Lg Rg sL.b3 sR.b3; if !(B9.sub u3 remV) then none else
  let u4 := upd1 uc.u4 Lg Rg sL.b4 sR.b4; if !(B9.sub u4 remV) then none else
  let u5 := upd1 uc.u5 Lg Rg sL.b5 sR.b5; if !(B9.sub u5 remV) then none else
  let u6 := upd1 uc.u6 Lg Rg sL.b6 sR.b6; if !(B9.sub u6 remV) then none else
  let u7 := upd1 uc.u7 Lg Rg sL.b7 sR.b7; if !(B9.sub u7 remV) then none else
  let u8 := upd1 uc.u8 Lg Rg sL.b8 sR.b8; if !(B9.sub u8 remV) then none else
  let u9 := upd1 uc.u9 Lg Rg sL.b9 sR.b9; if !(B9.sub u9 remV) then none else
  let u10 := upd1 uc.u10 Lg Rg sL.b10 sR.b10; if !(B9.sub u10 remV) then none else
  let u11 := upd1 uc.u11 Lg Rg sL.b11 sR.b11; if !(B9.sub u11 remV) then none else
  let u12 := upd1 uc.u12 Lg Rg sL.b12 sR.b12; if !(B9.sub u12 remV) then none else
  let u13 := upd1 uc.u13 Lg Rg sL.b13 sR.b13; if !(B9.sub u13 remV) then none else
  let u14 := upd1 uc.u14 Lg Rg sL.b14 sR.b14; if !(B9.sub u14 remV) then none else
  let u15 := upd1 uc.u15 Lg Rg sL.b15 sR.b15; if !(B9.sub u15 remV) then none else
  some ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10,u11,u12,u13,u14,u15⟩

def searchTopo (gates : List GInfo) (v0 v1 v2 v3 v4 v5 v6 v7 v8 : B5) :
    Nat → Nat → B5 → List B16 → List PlacedG → U16 → Bool
  | 0, _, _, _, revPgs, _ => evalAllOnes revPgs.reverse
  | rem + 1, i, used, gvms, revPgs, uc =>
    if rem == 0 && evalAllOnes revPgs.reverse then true
    else
      gates.any fun gi =>
        if B5.get used gi.gIdx then false
        else
          let nused := B5.set used gi.gIdx
          let nrem := B5.not nused
          let remV : B9 := ⟨B5.anyAnd v0 nrem, B5.anyAnd v1 nrem, B5.anyAnd v2 nrem,
                            B5.anyAnd v3 nrem, B5.anyAnd v4 nrem, B5.anyAnd v5 nrem,
                            B5.anyAnd v6 nrem, B5.anyAnd v7 nrem, B5.anyAnd v8 nrem⟩
          let isG0 := gi.gIdx == 0
          let sLs := collectMaxSides i gi.bmL gvms isG0 false
          let sRs := collectMaxSides i gi.bmR gvms isG0 true
          sLs.any fun (sL, lg) =>
            sRs.any fun (sR, rg) =>
              let gm := B16.and sL sR
              let isZ := B16.isZero gm
              if rem == 0 && !isZ then false
              else
                match updateU16 uc sL sR gi.Lg gi.Rg remV with
                | none => false
                | some uc' =>
                  let pg : PlacedG := ⟨gi.Lg, gi.Rg, lg, rg, isZ⟩
                  searchTopo gates v0 v1 v2 v3 v4 v5 v6 v7 v8 rem (i + 1) nused (gvms ++ [gm]) (pg :: revPgs) uc'

/-! ### Section 5B: `maxCircuit` and `searchTopo_of_circuit` soundness -/

def maxCircuit (D : AndCountCircuit 9) : AndCountCircuit 9 where
  size := D.size
  leftVars := D.leftVars
  leftGates i := Finset.univ.filter (fun j : Fin D.size =>
    j < i ∧ ∀ k : Fin 16, D.gateVal (rows9 k) j = true → sideL D (rows9 k) i = true)
  rightVars := D.rightVars
  rightGates i := Finset.univ.filter (fun j : Fin D.size =>
    j < i ∧ ∀ k : Fin 16, D.gateVal (rows9 k) j = true → sideR D (rows9 k) i = true)
  outVars := ∅
  outGates := Finset.univ.filter (fun j : Fin D.size =>
    ∀ k : Fin 16, D.gateVal (rows9 k) j = false)

lemma maxCircuit_wf (D : AndCountCircuit 9) : (maxCircuit D).WellFormed := by
  intro i; constructor <;> intro j hj <;> exact (Finset.mem_filter.mp hj).2.1

lemma maxCircuit_leftGates_sub (D : AndCountCircuit 9) (hW : D.WellFormed) (i : Fin D.size) :
    D.leftGates i ⊆ (maxCircuit D).leftGates i := by
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hW i).1 j hj, fun k hgv => ?_⟩
  unfold sideL; rw [sideTrue_iff]; exact Or.inr ⟨j, hj, (hW i).1 j hj, hgv⟩

lemma maxCircuit_rightGates_sub (D : AndCountCircuit 9) (hW : D.WellFormed) (i : Fin D.size) :
    D.rightGates i ⊆ (maxCircuit D).rightGates i := by
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hW i).2 j hj, fun k hgv => ?_⟩
  unfold sideR; rw [sideTrue_iff]; exact Or.inr ⟨j, hj, (hW i).2 j hj, hgv⟩

lemma maxCircuit_outGates_sub (D : AndCountCircuit 9) (hsep : Separates D) :
    D.outGates ⊆ (maxCircuit D).outGates := by
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k => ?_⟩
  rw [Bool.eq_false_iff]; intro hgv
  have hev : D.eval (rows9 k) = true := (eval_iff D (rows9 k)).mpr (Or.inr ⟨j, hj, hgv⟩)
  rw [(hsep k).1] at hev; cases hev

lemma maxCircuit_mis_eq (D : AndCountCircuit 9) (hW : D.WellFormed) (k : Fin 16) :
    ∀ (m : ℕ) (i : Fin D.size), i.val < m →
      sideL (maxCircuit D) (rows9 k) i = sideL D (rows9 k) i ∧
      sideR (maxCircuit D) (rows9 k) i = sideR D (rows9 k) i ∧
      (maxCircuit D).gateVal (rows9 k) i = D.gateVal (rows9 k) i := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    have hL : sideL (maxCircuit D) (rows9 k) i = sideL D (rows9 k) i := by
      rw [Bool.eq_iff_iff]; unfold sideL; simp only [sideTrue, decide_eq_true_eq]
      constructor
      · rintro (h | ⟨j, hjM, hji, hgv⟩)
        · exact Or.inl h
        · have hjeq := (ih j (by omega)).2.2
          rw [hjeq] at hgv
          exact (sideTrue_iff _ _ _ _ _).mp ((Finset.mem_filter.mp hjM).2.2 k hgv)
      · rintro (h | ⟨j, hjD, hji, hgv⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, maxCircuit_leftGates_sub D hW i hjD, hji, (ih j (by omega)).2.2.symm ▸ hgv⟩
    have hR : sideR (maxCircuit D) (rows9 k) i = sideR D (rows9 k) i := by
      rw [Bool.eq_iff_iff]; unfold sideR; simp only [sideTrue, decide_eq_true_eq]
      constructor
      · rintro (h | ⟨j, hjM, hji, hgv⟩)
        · exact Or.inl h
        · have hjeq := (ih j (by omega)).2.2
          rw [hjeq] at hgv
          exact (sideTrue_iff _ _ _ _ _).mp ((Finset.mem_filter.mp hjM).2.2 k hgv)
      · rintro (h | ⟨j, hjD, hji, hgv⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, maxCircuit_rightGates_sub D hW i hjD, hji, (ih j (by omega)).2.2.symm ▸ hgv⟩
    refine ⟨hL, hR, ?_⟩
    rw [gateVal_unfold (maxCircuit D) (rows9 k) i, gateVal_unfold D (rows9 k) i]
    exact congrArg₂ (· && ·) hL hR

lemma maxCircuit_gateVal_mono (D : AndCountCircuit 9) (hW : D.WellFormed) (U : Finset V) :
    ∀ (m : ℕ) (i : Fin D.size), i.val < m →
      D.gateVal U i = true → (maxCircuit D).gateVal U i = true := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hv
    rw [gateVal_unfold D U i, Bool.and_eq_true] at hv
    simp only [sideTrue, decide_eq_true_eq] at hv
    rw [gateVal_unfold (maxCircuit D) U i, Bool.and_eq_true]
    simp only [sideTrue, decide_eq_true_eq]
    constructor
    · rcases hv.1 with h | ⟨j, hj, hji, hgv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, maxCircuit_leftGates_sub D hW i hj, hji, ih j (by omega) hgv⟩
    · rcases hv.2 with h | ⟨j, hj, hji, hgv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, maxCircuit_rightGates_sub D hW i hj, hji, ih j (by omega) hgv⟩

lemma maxCircuit_eval_mono (D : AndCountCircuit 9) (hW : D.WellFormed) (hsep : Separates D)
    (U : Finset V) (h : D.eval U = true) : (maxCircuit D).eval U = true := by
  rw [eval_iff] at h ⊢
  rcases h with ⟨v, hvO, _⟩ | ⟨j, hjO, hgv⟩
  · exact (sep_outVars_empty hsep v hvO).elim
  · exact Or.inr ⟨j, maxCircuit_outGates_sub D hsep hjO, maxCircuit_gateVal_mono D hW U D.size j j.isLt hgv⟩

lemma maxCircuit_separates (D : AndCountCircuit 9) (hW : D.WellFormed) (hsep : Separates D) :
    Separates (maxCircuit D) := by
  intro k
  constructor
  · rw [Bool.eq_false_iff]; intro hev
    rw [eval_iff] at hev
    rcases hev with ⟨v, hvO, _⟩ | ⟨j, hjO, hgv⟩
    · exact Finset.notMem_empty v hvO
    · have hfalse := (Finset.mem_filter.mp hjO).2 k
      rw [(maxCircuit_mis_eq D hW k D.size j j.isLt).2.2] at hgv
      rw [hfalse] at hgv; cases hgv
  · intro w hw
    exact maxCircuit_eval_mono D hW hsep (insert w (rows9 k)) ((hsep k).2 w hw)

lemma boolLists_mem : ∀ (n : Nat) (bs : List Bool), bs.length = n → bs ∈ boolLists n := by
  intro n
  induction n with
  | zero => intro bs h; cases bs with | nil => exact List.mem_singleton_self _ | cons _ _ => simp at h
  | succ m ih =>
    intro bs h
    cases bs with
    | nil => simp at h
    | cons b rest =>
      simp only [boolLists, List.mem_append, List.mem_map]
      have hrest : rest ∈ boolLists m := ih rest (by simpa using h)
      cases b
      · exact Or.inl ⟨rest, hrest, rfl⟩
      · exact Or.inr ⟨rest, hrest, rfl⟩

lemma orB16_get : ∀ (gs : List B16) (bs : List Bool) (acc : B16) (hlen : gs.length = bs.length) (k : Fin 16),
      (orB16 gs bs acc).get k = true ↔
        acc.get k = true ∨ ∃ j : Fin gs.length, bs.get ⟨j.val, by omega⟩ = true ∧ (gs.get j).get k = true := by
  intro gs
  induction gs with
  | nil =>
    intro bs acc _ k
    simp only [orB16, List.length_nil, IsEmpty.exists_iff, or_false]
  | cons g rest ih =>
    intro bs acc hlen k
    cases bs with
    | nil => simp at hlen
    | cons b bs' =>
      have hlen' : rest.length = bs'.length := by simpa using hlen
      cases b
      · simp only [orB16]
        rw [ih bs' acc hlen' k]
        constructor
        · rintro (h | ⟨j, hb, hg⟩)
          · exact Or.inl h
          · exact Or.inr ⟨⟨j.val + 1, by simp⟩, hb, hg⟩
        · rintro (h | ⟨j, hb, hg⟩)
          · exact Or.inl h
          · rcases j with ⟨jv, hjv⟩
            cases jv with
            | zero => simp at hb
            | succ j' => exact Or.inr ⟨⟨j', by simp at hjv; omega⟩, hb, hg⟩
      · simp only [orB16]
        rw [ih bs' (B16.or acc g) hlen' k, B16.get_or, Bool.or_eq_true]
        constructor
        · rintro ((ha | hg) | ⟨j, hb, hgj⟩)
          · exact Or.inl ha
          · exact Or.inr ⟨⟨0, by simp⟩, rfl, hg⟩
          · exact Or.inr ⟨⟨j.val + 1, by simp⟩, hb, hgj⟩
        · rintro (ha | ⟨j, hb, hgj⟩)
          · exact Or.inl (Or.inl ha)
          · rcases j with ⟨jv, hjv⟩
            cases jv with
            | zero => exact Or.inl (Or.inr hgj)
            | succ j' => exact Or.inr ⟨⟨j', by simp at hjv; omega⟩, hb, hgj⟩

lemma isMaxMask_true : ∀ (gs : List B16) (bs : List Bool) (s : B16) (hlen : gs.length = bs.length),
    (∀ j : Fin gs.length, B16.sub (gs.get j) s = bs.get ⟨j.val, by omega⟩) →
    isMaxMask gs bs s = true := by
  intro gs
  induction gs with
  | nil =>
    intro bs s hlen _
    cases bs with | nil => rfl | cons _ _ => simp at hlen
  | cons g rest ih =>
    intro bs s hlen hsub
    cases bs with
    | nil => simp at hlen
    | cons b bs' =>
      have hlen' : rest.length = bs'.length := by simpa using hlen
      simp only [isMaxMask, Bool.and_eq_true, beq_iff_eq]
      refine ⟨hsub ⟨0, by simp⟩, ih bs' s hlen' (fun j => hsub ⟨j.val + 1, by simp⟩)⟩

lemma toB5_get (bs : List Bool) (hlen : bs.length ≤ 4) (r : Fin 5) :
    (toB5 bs).get r.val = (if h : r.val < bs.length then bs.get ⟨r.val, h⟩ else false) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _⟩⟩⟩⟩⟩
  · fin_cases r <;> rfl
  · fin_cases r <;> rfl
  · fin_cases r <;> rfl
  · fin_cases r <;> rfl
  · fin_cases r <;> rfl
  · simp at hlen; omega

lemma evalOneGo_iff (Dstar : AndCountCircuit 9) (hsz : Dstar.size = 5)
    (U : Finset V) (x : B9) (hx : ∀ v : V, x.get v.val = decide (v ∈ U))
    (m : Nat) (hm : m ≤ 5) :
    ∀ (rest : List PlacedG) (idx : Nat) (tm : B5) (hlen : idx + rest.length = m),
      (∀ t : Fin rest.length,
        let j : Fin 5 := ⟨idx + t.val, by omega⟩
        let pg := rest.get t
        (∀ v : V, pg.Lg.get v.val = decide (v ∈ Dstar.leftVars ⟨j.val, by omega⟩)) ∧
        (∀ v : V, pg.Rg.get v.val = decide (v ∈ Dstar.rightVars ⟨j.val, by omega⟩)) ∧
        (∀ r : Fin 5, pg.lgM.get r.val = decide (r.val < j.val ∧ ⟨r.val, by omega⟩ ∈ Dstar.leftGates ⟨j.val, by omega⟩)) ∧
        (∀ r : Fin 5, pg.rgM.get r.val = decide (r.val < j.val ∧ ⟨r.val, by omega⟩ ∈ Dstar.rightGates ⟨j.val, by omega⟩)) ∧
        pg.isOut = decide (⟨j.val, by omega⟩ ∈ Dstar.outGates)) →
      (∀ r : Fin 5, tm.get r.val = decide (r.val < idx ∧ Dstar.gateVal U ⟨r.val, by omega⟩ = true)) →
      (evalOneGo x rest idx tm = true ↔
        ∃ j : Fin 5, idx ≤ j.val ∧ j.val < m ∧
          Dstar.gateVal U ⟨j.val, by omega⟩ = true ∧ ⟨j.val, by omega⟩ ∈ Dstar.outGates) := by
  intro rest
  induction rest with
  | nil =>
    intro idx tm hlen _ _
    simp only [evalOneGo, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro j hj1 hj2; simp at hlen; omega
  | cons pg tail ih =>
    intro idx tm hlen hpgs htm
    have h0 := hpgs ⟨0, by simp⟩
    dsimp only [List.get_eq_getElem, List.getElem_cons_zero, Nat.add_zero] at h0
    have hidx5 : idx < 5 := by simp at hlen; omega
    let j0 : Fin 5 := ⟨idx, hidx5⟩
    let j0D : Fin Dstar.size := ⟨idx, by omega⟩
    have hsL : (B9.anyAnd pg.Lg x || B5.anyAnd pg.lgM tm) = sideL Dstar U j0D := by
      rw [Bool.eq_iff_iff, Bool.or_eq_true, B9.anyAnd_eq_true, B5.anyAnd_eq_true]
      unfold sideL; rw [sideTrue_iff]
      constructor
      · rintro (⟨v, hv1, hv2⟩ | ⟨r, hr1, hr2⟩)
        · rw [h0.1 v, decide_eq_true_eq] at hv1
          rw [hx v, decide_eq_true_eq] at hv2
          exact Or.inl ⟨v, hv1, hv2⟩
        · rw [h0.2.2.1 r, decide_eq_true_eq] at hr1
          rw [htm r, decide_eq_true_eq] at hr2
          exact Or.inr ⟨⟨r.val, by omega⟩, hr1.2, hr1.1, hr2.2⟩
      · rintro (⟨v, hvL, hvU⟩ | ⟨r, hrG, hrlt, hrgv⟩)
        · left; exact ⟨v, (h0.1 v).trans (decide_eq_true hvL), (hx v).trans (decide_eq_true hvU)⟩
        · right; refine ⟨⟨r.val, by omega⟩, ?_, ?_⟩
          · rw [h0.2.2.1 ⟨r.val, by omega⟩]; exact decide_eq_true ⟨hrlt, hrG⟩
          · rw [htm ⟨r.val, by omega⟩]; exact decide_eq_true ⟨hrlt, hrgv⟩
    have hsR : (B9.anyAnd pg.Rg x || B5.anyAnd pg.rgM tm) = sideR Dstar U j0D := by
      rw [Bool.eq_iff_iff, Bool.or_eq_true, B9.anyAnd_eq_true, B5.anyAnd_eq_true]
      unfold sideR; rw [sideTrue_iff]
      constructor
      · rintro (⟨v, hv1, hv2⟩ | ⟨r, hr1, hr2⟩)
        · rw [h0.2.1 v, decide_eq_true_eq] at hv1
          rw [hx v, decide_eq_true_eq] at hv2
          exact Or.inl ⟨v, hv1, hv2⟩
        · rw [h0.2.2.2.1 r, decide_eq_true_eq] at hr1
          rw [htm r, decide_eq_true_eq] at hr2
          exact Or.inr ⟨⟨r.val, by omega⟩, hr1.2, hr1.1, hr2.2⟩
      · rintro (⟨v, hvR, hvU⟩ | ⟨r, hrG, hrlt, hrgv⟩)
        · left; exact ⟨v, (h0.2.1 v).trans (decide_eq_true hvR), (hx v).trans (decide_eq_true hvU)⟩
        · right; refine ⟨⟨r.val, by omega⟩, ?_, ?_⟩
          · rw [h0.2.2.2.1 ⟨r.val, by omega⟩]; exact decide_eq_true ⟨hrlt, hrG⟩
          · rw [htm ⟨r.val, by omega⟩]; exact decide_eq_true ⟨hrlt, hrgv⟩
    have hgv : ((B9.anyAnd pg.Lg x || B5.anyAnd pg.lgM tm) &&
                (B9.anyAnd pg.Rg x || B5.anyAnd pg.rgM tm)) = Dstar.gateVal U j0D := by
      rw [hsL, hsR, gateVal_unfold Dstar U j0D]; rfl
    have htm' : ∀ r : Fin 5,
        (if Dstar.gateVal U j0D then B5.set tm idx else tm).get r.val =
        decide (r.val < idx + 1 ∧ Dstar.gateVal U ⟨r.val, by omega⟩ = true) := by
      intro r
      by_cases hval : Dstar.gateVal U j0D = true
      · simp only [hval, ↓reduceIte]
        have hset := B5.get_set tm j0 r
        change (tm.set idx).get r.val = _
        rw [show idx = j0.val from rfl, hset]
        by_cases heq : j0 = r
        · subst heq; simp [j0, j0D, hval]
        · rw [ite_eq_right heq, htm r]
          have hne : r.val ≠ idx := fun h => heq (Fin.ext (by change idx = r.val; exact h.symm))
          have hj0v : j0.val = idx := rfl
          exact decide_eq_decide.mpr ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩
      · simp only [hval, Bool.false_eq_true, ↓reduceIte, htm r]
        refine decide_eq_decide.mpr ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ?_⟩
        by_cases heq : r.val = idx
        · have : (⟨r.val, by omega⟩ : Fin Dstar.size) = j0D := Fin.ext heq
          rw [this] at h2; exact absurd h2 hval
        · exact ⟨by omega, h2⟩
    have htail := ih (idx + 1) (if Dstar.gateVal U j0D then B5.set tm idx else tm)
      (by simp at hlen; omega)
      (fun t => by
        have ht := hpgs ⟨t.val + 1, by simp⟩
        have hidx : idx + (t.val + 1) = idx + 1 + t.val := by omega
        simpa [hidx] using ht)
      htm'
    simp only [evalOneGo, hgv]
    by_cases hout : (Dstar.gateVal U j0D && pg.isOut) = true
    · simp only [hout, ↓reduceIte, true_iff]
      rw [Bool.and_eq_true, h0.2.2.2.2, decide_eq_true_eq] at hout
      exact ⟨j0, le_refl _, by dsimp [j0]; simp at hlen; omega, hout.1, hout.2⟩
    · simp only [hout, Bool.false_eq_true, ↓reduceIte]
      rw [htail]
      constructor
      · rintro ⟨j, hj1, hj2, hgvj, houtj⟩
        exact ⟨j, by omega, hj2, hgvj, houtj⟩
      · rintro ⟨j, hj1, hj2, hgvj, houtj⟩
        by_cases heq : j.val = idx
        · exfalso; apply hout
          rw [Bool.and_eq_true, h0.2.2.2.2, decide_eq_true_eq]
          have hjeq : (⟨j.val, by omega⟩ : Fin Dstar.size) = j0D := Fin.ext heq
          rw [hjeq] at hgvj houtj
          exact ⟨hgvj, houtj⟩
        · exact ⟨j, by omega, hj2, hgvj, houtj⟩

lemma updateU16_some (uc : U16) (sL sR : B16) (Lg Rg remV : B9)
    (hsub : ∀ k : Fin 16, B9.sub (upd1 (uc.get k) Lg Rg (sL.get k) (sR.get k)) remV = true) :
    ∃ uc', updateU16 uc sL sR Lg Rg remV = some uc' ∧
      ∀ k : Fin 16, uc'.get k = upd1 (uc.get k) Lg Rg (sL.get k) (sR.get k) := by
  have h0 := hsub ⟨0, by decide⟩; have h1 := hsub ⟨1, by decide⟩
  have h2 := hsub ⟨2, by decide⟩; have h3 := hsub ⟨3, by decide⟩
  have h4 := hsub ⟨4, by decide⟩; have h5 := hsub ⟨5, by decide⟩
  have h6 := hsub ⟨6, by decide⟩; have h7 := hsub ⟨7, by decide⟩
  have h8 := hsub ⟨8, by decide⟩; have h9 := hsub ⟨9, by decide⟩
  have h10 := hsub ⟨10, by decide⟩; have h11 := hsub ⟨11, by decide⟩
  have h12 := hsub ⟨12, by decide⟩; have h13 := hsub ⟨13, by decide⟩
  have h14 := hsub ⟨14, by decide⟩; have h15 := hsub ⟨15, by decide⟩
  simp only [U16.get, B16.get] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  unfold updateU16
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl, fun k => by fin_cases k <;> rfl⟩

lemma searchTopo_sound_aux (D : AndCountCircuit 9) (hsz : D.size = 5)
    (hW : D.WellFormed) (hsep : Separates D)
    (σ : Fin 5 ≃ Fin 5) (a0 : Fin 5) (hσ_a0 : σ a0 = 0)
    (hno0 : ∀ k : Fin 16, (0 : V) ∉ rows9 k →
      sideL D (rows9 k) ⟨a0.val, by omega⟩ = false ∧ sideR D (rows9 k) ⟨a0.val, by omega⟩ = true)
    (gates : List GInfo) (vB5 : V → B5)
    (hgates : ∀ i : Fin 5, ∃ gi ∈ gates,
      gi.gIdx = (σ i).val ∧
      (∀ v : V, gi.Lg.get v.val = decide (v ∈ D.leftVars ⟨i.val, by omega⟩)) ∧
      (∀ v : V, gi.Rg.get v.val = decide (v ∈ D.rightVars ⟨i.val, by omega⟩)) ∧
      (∀ k : Fin 16, gi.bmL.get k = decide (∃ v ∈ rows9 k, v ∈ D.leftVars ⟨i.val, by omega⟩)) ∧
      (∀ k : Fin 16, gi.bmR.get k = decide (∃ v ∈ rows9 k, v ∈ D.rightVars ⟨i.val, by omega⟩)))
    (hvB5 : ∀ v : V, ∀ g : Fin 5,
      (vB5 v).get g.val = decide (v ∈ D.leftVars ⟨(σ.symm g).val, by omega⟩ ∨ v ∈ D.rightVars ⟨(σ.symm g).val, by omega⟩)) :
    ∀ (rem i : Nat) (hi : i + rem = 5)
      (used : B5) (gvms : List B16) (revPgs : List PlacedG) (uc : U16)
      (_ : ∀ g : Fin 5, used.get g.val = decide ((σ.symm g).val < i))
      (hgvLen : gvms.length = i)
      (_ : ∀ (j : Fin gvms.length) (k : Fin 16), (gvms.get j).get k = (maxCircuit D).gateVal (rows9 k) ⟨j.val, by change j.val < D.size; omega⟩)
      (hrevLen : revPgs.length = i)
      (_ : ∀ t : Fin revPgs.reverse.length,
        let j : Fin 5 := ⟨t.val, by
          have htl := t.isLt
          have hrl : revPgs.reverse.length = i := by rw [List.length_reverse, hrevLen]
          omega⟩
        let pg := revPgs.reverse.get t
        (∀ v : V, pg.Lg.get v.val = decide (v ∈ (maxCircuit D).leftVars ⟨j.val, by change j.val < D.size; omega⟩)) ∧
        (∀ v : V, pg.Rg.get v.val = decide (v ∈ (maxCircuit D).rightVars ⟨j.val, by change j.val < D.size; omega⟩)) ∧
        (∀ r : Fin 5, pg.lgM.get r.val = decide (r.val < j.val ∧ ⟨r.val, by change r.val < D.size; omega⟩ ∈ (maxCircuit D).leftGates ⟨j.val, by change j.val < D.size; omega⟩)) ∧
        (∀ r : Fin 5, pg.rgM.get r.val = decide (r.val < j.val ∧ ⟨r.val, by change r.val < D.size; omega⟩ ∈ (maxCircuit D).rightGates ⟨j.val, by change j.val < D.size; omega⟩)) ∧
        pg.isOut = decide (⟨j.val, by change j.val < D.size; omega⟩ ∈ (maxCircuit D).outGates))
      (_ : ∀ (k : Fin 16) (w : V), (uc.get k).get w.val = true →
        w ∉ rows9 k ∧ ∀ j : Fin 5, j.val < i → ∀ b : Bool,
          (⟨j.val, by change j.val < D.size; omega⟩, b) ∈ litSet (maxCircuit D) w →
          misChoice (maxCircuit D) (rows9 k) ⟨j.val, by change j.val < D.size; omega⟩ ≠ some b),
      searchTopo gates (vB5 0) (vB5 1) (vB5 2) (vB5 3) (vB5 4) (vB5 5) (vB5 6) (vB5 7) (vB5 8)
        rem i used gvms revPgs uc = true := by
  have hszS : (maxCircuit D).size = 5 := hsz
  have hsepS : Separates (maxCircuit D) := maxCircuit_separates D hW hsep
  have hmisL : ∀ (k : Fin 16) (idx : Fin (maxCircuit D).size),
      sideL (maxCircuit D) (rows9 k) idx = sideL D (rows9 k) idx :=
    fun k idx => (maxCircuit_mis_eq D hW k D.size idx idx.isLt).1
  have hmisR : ∀ (k : Fin 16) (idx : Fin (maxCircuit D).size),
      sideR (maxCircuit D) (rows9 k) idx = sideR D (rows9 k) idx :=
    fun k idx => (maxCircuit_mis_eq D hW k D.size idx idx.isLt).2.1
  have hmisG : ∀ (k : Fin 16) (idx : Fin (maxCircuit D).size),
      (maxCircuit D).gateVal (rows9 k) idx = D.gateVal (rows9 k) idx :=
    fun k idx => (maxCircuit_mis_eq D hW k D.size idx idx.isLt).2.2
  intro rem
  induction rem with
  | zero =>
    intro i hi used gvms revPgs uc _ _ _ hrevLen hrevSpec _
    unfold searchTopo evalAllOnes
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨k, w, hw, hxv⟩ := onesB9_spec x hx
    have hev : (maxCircuit D).eval (insert w (rows9 k)) = true := (hsepS k).2 w hw
    rw [eval_iff] at hev
    rcases hev with ⟨v, hvO, _⟩ | ⟨j, hjO, hjv⟩
    · exact (Finset.notMem_empty v hvO).elim
    · unfold evalOne
      rw [evalOneGo_iff (maxCircuit D) hszS (insert w (rows9 k)) x hxv 5 (le_refl 5)
        revPgs.reverse 0 ⟨false,false,false,false,false⟩ (by rw [List.length_reverse]; omega)
        (fun t => by simpa using hrevSpec t)
        (fun r => by fin_cases r <;> rfl)]
      exact ⟨⟨j.val, by omega⟩, Nat.zero_le _, by omega, hjv, hjO⟩
  | succ rem ih =>
    intro i hi used gvms revPgs uc hused hgvLen hgvSpec hrevLen hrevSpec huc
    unfold searchTopo
    by_cases hearly : (rem == 0 && evalAllOnes revPgs.reverse) = true
    · simp only [hearly, ↓reduceIte]
    · simp only [hearly, Bool.false_eq_true, ↓reduceIte]
      rw [List.any_eq_true]
      let ii : Fin 5 := ⟨i, by omega⟩
      obtain ⟨gi, hgi_mem, hgi_idx, hgi_L, hgi_R, hgi_bmL, hgi_bmR⟩ := hgates ii
      refine ⟨gi, hgi_mem, ?_⟩
      have hused_f : B5.get used gi.gIdx = false := by
        rw [hgi_idx, hused (σ ii), Equiv.symm_apply_apply]
        exact decide_eq_false (Nat.lt_irrefl i)
      simp only [hused_f, Bool.false_eq_true, ↓reduceIte]
      let nused := B5.set used gi.gIdx
      let nrem := B5.not nused
      let remV : B9 := ⟨B5.anyAnd (vB5 0) nrem, B5.anyAnd (vB5 1) nrem, B5.anyAnd (vB5 2) nrem,
                        B5.anyAnd (vB5 3) nrem, B5.anyAnd (vB5 4) nrem, B5.anyAnd (vB5 5) nrem,
                        B5.anyAnd (vB5 6) nrem, B5.anyAnd (vB5 7) nrem, B5.anyAnd (vB5 8) nrem⟩
      have hnused : ∀ g : Fin 5, nused.get g.val = decide ((σ.symm g).val < i + 1) := by
        intro g
        dsimp only [nused]
        rw [hgi_idx, B5.get_set used (σ ii) g]
        by_cases heq : σ ii = g
        · rw [ite_eq_left heq, ← heq, Equiv.symm_apply_apply]; exact (decide_eq_true (by dsimp [ii]; omega)).symm
        · rw [ite_eq_right heq, hused g]
          have hne : (σ.symm g).val ≠ i := fun h => heq (by
            have : σ.symm g = ii := Fin.ext h
            rw [← this, Equiv.apply_symm_apply])
          exact decide_eq_decide.mpr (by omega)
      let bsL : List Bool := (List.finRange i).map (fun j => decide (⟨j.val, by change j.val < D.size; omega⟩ ∈ (maxCircuit D).leftGates ⟨i, by change i < D.size; omega⟩))
      let bsR : List Bool := (List.finRange i).map (fun j => decide (⟨j.val, by change j.val < D.size; omega⟩ ∈ (maxCircuit D).rightGates ⟨i, by change i < D.size; omega⟩))
      have hbsL_len : bsL.length = i := by simp [bsL]
      have hbsR_len : bsR.length = i := by simp [bsR]
      let sL := orB16 gvms bsL gi.bmL
      let sR := orB16 gvms bsR gi.bmR
      have hsL_get : ∀ k : Fin 16, sL.get k = sideL (maxCircuit D) (rows9 k) ⟨i, by omega⟩ := by
        intro k
        rw [Bool.eq_iff_iff, orB16_get gvms bsL gi.bmL (by omega) k, hgi_bmL k, decide_eq_true_eq]
        unfold sideL; rw [sideTrue_iff]
        constructor
        · rintro (⟨v, hvk, hvL⟩ | ⟨j, hb, hgv⟩)
          · exact Or.inl ⟨v, hvL, hvk⟩
          · simp only [bsL, List.get_eq_getElem, List.getElem_map, List.getElem_finRange, decide_eq_true_eq] at hb
            rw [hgvSpec j k] at hgv
            exact Or.inr ⟨⟨j.val, by omega⟩, hb, show j.val < i from by omega, hgv⟩
        · rintro (⟨v, hvL, hvk⟩ | ⟨j, hjG, hji, hgv⟩)
          · exact Or.inl ⟨v, hvk, hvL⟩
          · have hjlt : j.val < i := hji
            right
            refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
            · simp only [bsL, List.get_eq_getElem, List.getElem_map, List.getElem_finRange, decide_eq_true_eq]; exact hjG
            · rw [hgvSpec ⟨j.val, by omega⟩ k]; exact hgv
      have hsR_get : ∀ k : Fin 16, sR.get k = sideR (maxCircuit D) (rows9 k) ⟨i, by omega⟩ := by
        intro k
        rw [Bool.eq_iff_iff, orB16_get gvms bsR gi.bmR (by omega) k, hgi_bmR k, decide_eq_true_eq]
        unfold sideR; rw [sideTrue_iff]
        constructor
        · rintro (⟨v, hvk, hvR⟩ | ⟨j, hb, hgv⟩)
          · exact Or.inl ⟨v, hvR, hvk⟩
          · simp only [bsR, List.get_eq_getElem, List.getElem_map, List.getElem_finRange, decide_eq_true_eq] at hb
            rw [hgvSpec j k] at hgv
            exact Or.inr ⟨⟨j.val, by omega⟩, hb, show j.val < i from by omega, hgv⟩
        · rintro (⟨v, hvR, hvk⟩ | ⟨j, hjG, hji, hgv⟩)
          · exact Or.inl ⟨v, hvk, hvR⟩
          · have hjlt : j.val < i := hji
            right
            refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
            · simp only [bsR, List.get_eq_getElem, List.getElem_map, List.getElem_finRange, decide_eq_true_eq]; exact hjG
            · rw [hgvSpec ⟨j.val, by omega⟩ k]; exact hgv
      have hmaxL : isMaxMask gvms bsL sL = true := by
        apply isMaxMask_true gvms bsL sL (by omega)
        intro j
        rw [Bool.eq_iff_iff, B16.sub_eq_true]
        simp only [bsL, List.get_eq_getElem, List.getElem_map, List.getElem_finRange, decide_eq_true_eq]
        change (∀ k : Fin 16, (gvms.get j).get k = true → sL.get k = true) ↔
          (⟨j.val, by omega⟩ : Fin D.size) ∈ Finset.univ.filter (fun j0 : Fin D.size =>
            j0 < ⟨i, by omega⟩ ∧ ∀ k : Fin 16, D.gateVal (rows9 k) j0 = true → sideL D (rows9 k) ⟨i, by omega⟩ = true)
        rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
        have hlt : (⟨j.val, by omega⟩ : Fin D.size) < ⟨i, by omega⟩ := show j.val < i from by omega
        simp only [hlt, true_and]
        constructor
        · intro h k hgv
          have h1 := h k ((hgvSpec j k).trans ((hmisG k ⟨j.val, by omega⟩).trans hgv))
          rw [hsL_get k, hmisL k ⟨i, by omega⟩] at h1
          exact h1
        · intro h k hgv
          rw [hgvSpec j k, hmisG k ⟨j.val, by omega⟩] at hgv
          rw [hsL_get k, hmisL k ⟨i, by omega⟩]
          exact h k hgv
      have hmaxR : isMaxMask gvms bsR sR = true := by
        apply isMaxMask_true gvms bsR sR (by omega)
        intro j
        rw [Bool.eq_iff_iff, B16.sub_eq_true]
        simp only [bsR, List.get_eq_getElem, List.getElem_map, List.getElem_finRange, decide_eq_true_eq]
        change (∀ k : Fin 16, (gvms.get j).get k = true → sR.get k = true) ↔
          (⟨j.val, by omega⟩ : Fin D.size) ∈ Finset.univ.filter (fun j0 : Fin D.size =>
            j0 < ⟨i, by omega⟩ ∧ ∀ k : Fin 16, D.gateVal (rows9 k) j0 = true → sideR D (rows9 k) ⟨i, by omega⟩ = true)
        rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
        have hlt : (⟨j.val, by omega⟩ : Fin D.size) < ⟨i, by omega⟩ := show j.val < i from by omega
        simp only [hlt, true_and]
        constructor
        · intro h k hgv
          have h1 := h k ((hgvSpec j k).trans ((hmisG k ⟨j.val, by omega⟩).trans hgv))
          rw [hsR_get k, hmisR k ⟨i, by omega⟩] at h1
          exact h1
        · intro h k hgv
          rw [hgvSpec j k, hmisG k ⟨j.val, by omega⟩] at hgv
          rw [hsR_get k, hmisR k ⟨i, by omega⟩]
          exact h k hgv
      have hok0L : (if (gi.gIdx == 0) = true then no0AllFalse sL else true) = true := by
        by_cases hg0 : (gi.gIdx == 0) = true
        · simp only [hg0, ↓reduceIte]
          have hia0 : ii = a0 := by
            have h0v : (σ ii).val = 0 := by rw [← hgi_idx]; exact beq_iff_eq.mp hg0
            exact σ.injective ((Fin.ext h0v).trans hσ_a0.symm)
          apply no0AllFalse_of
          intro k hk
          rw [hsL_get k, hmisL k ⟨i, by omega⟩]
          exact (congrArg (sideL D (rows9 k)) (Fin.ext (congrArg (Fin.val : Fin 5 → Nat) hia0))).trans (hno0 k hk).1
        · simp [hg0]
      have hok0R : (if (gi.gIdx == 0) = true then no0AllTrue sR else true) = true := by
        by_cases hg0 : (gi.gIdx == 0) = true
        · simp only [hg0, ↓reduceIte]
          have hia0 : ii = a0 := by
            have h0v : (σ ii).val = 0 := by rw [← hgi_idx]; exact beq_iff_eq.mp hg0
            exact σ.injective ((Fin.ext h0v).trans hσ_a0.symm)
          apply no0AllTrue_of
          intro k hk
          rw [hsR_get k, hmisR k ⟨i, by omega⟩]
          exact (congrArg (sideR D (rows9 k)) (Fin.ext (congrArg (Fin.val : Fin 5 → Nat) hia0))).trans (hno0 k hk).2
        · simp [hg0]
      have hsL_mem : (sL, toB5 bsL) ∈ collectMaxSides i gi.bmL gvms (gi.gIdx == 0) false := by
        unfold collectMaxSides; rw [List.mem_filterMap]
        refine ⟨bsL, boolLists_mem i bsL hbsL_len, ?_⟩
        change (if ((if (gi.gIdx == 0) = true then no0AllFalse sL else true) && isMaxMask gvms bsL sL) = true then some (sL, toB5 bsL) else none) = some (sL, toB5 bsL)
        rw [hok0L, hmaxL]; rfl
      have hsR_mem : (sR, toB5 bsR) ∈ collectMaxSides i gi.bmR gvms (gi.gIdx == 0) true := by
        unfold collectMaxSides; rw [List.mem_filterMap]
        refine ⟨bsR, boolLists_mem i bsR hbsR_len, ?_⟩
        change (if ((if (gi.gIdx == 0) = true then no0AllTrue sR else true) && isMaxMask gvms bsR sR) = true then some (sR, toB5 bsR) else none) = some (sR, toB5 bsR)
        rw [hok0R, hmaxR]; rfl
      rw [List.any_eq_true]; refine ⟨(sL, toB5 bsL), hsL_mem, ?_⟩
      rw [List.any_eq_true]; refine ⟨(sR, toB5 bsR), hsR_mem, ?_⟩
      dsimp only
      let gm := B16.and sL sR
      let isZ := B16.isZero gm
      have hgm_get : ∀ k : Fin 16, gm.get k = (maxCircuit D).gateVal (rows9 k) ⟨i, by omega⟩ := by
        intro k
        rw [B16.get_and, hsL_get k, hsR_get k, gateVal_unfold (maxCircuit D) (rows9 k) ⟨i, by omega⟩]; rfl
      have hisZ : isZ = decide ((⟨i, by omega⟩ : Fin (maxCircuit D).size) ∈ (maxCircuit D).outGates) := by
        rw [Bool.eq_iff_iff, B16.isZero_eq_true, decide_eq_true_eq]
        change (∀ k : Fin 16, gm.get k = false) ↔
          (⟨i, by omega⟩ : Fin D.size) ∈ Finset.univ.filter (fun j : Fin D.size => ∀ k : Fin 16, D.gateVal (rows9 k) j = false)
        rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
        constructor
        · intro h k
          have := h k; rw [hgm_get k, hmisG k ⟨i, by omega⟩] at this
          exact this
        · intro h k
          rw [hgm_get k, hmisG k ⟨i, by omega⟩]; exact h k
      have hnot_prune : (rem == 0 && !isZ) = false := by
        rw [Bool.eq_false_iff]; intro hp
        rw [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
        rcases hp with ⟨rfl, hisZ_f⟩
        apply hearly
        simp only [beq_self_eq_true, Bool.true_and]
        unfold evalAllOnes; rw [List.all_eq_true]
        intro x hx
        obtain ⟨k, w, hw, hxv⟩ := onesB9_spec x hx
        have hev : (maxCircuit D).eval (insert w (rows9 k)) = true := (hsepS k).2 w hw
        rw [eval_iff] at hev
        rcases hev with ⟨v, hvO, _⟩ | ⟨j, hjO, hjv⟩
        · exact (Finset.notMem_empty v hvO).elim
        · have hjlt4 : j.val < 4 := by
            by_contra hge
            have hj5 : j.val < 5 := by have := j.isLt; omega
            have hj4 : j = ⟨i, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [hj4] at hjO
            rw [hisZ, decide_eq_true hjO] at hisZ_f; cases hisZ_f
          unfold evalOne
          rw [evalOneGo_iff (maxCircuit D) hszS (insert w (rows9 k)) x hxv 4 (by omega)
            revPgs.reverse 0 ⟨false,false,false,false,false⟩ (by rw [List.length_reverse]; omega)
            (fun t => by simpa using hrevSpec t)
            (fun r => by fin_cases r <;> rfl)]
          exact ⟨⟨j.val, by omega⟩, Nat.zero_le _, hjlt4, hjv, hjO⟩
      change (if (rem == 0 && !isZ) = true then false else _) = true
      rw [hnot_prune]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hupd_inv : ∀ (k : Fin 16) (w : V),
          (upd1 (uc.get k) gi.Lg gi.Rg (sL.get k) (sR.get k)).get w.val = true →
          w ∉ rows9 k ∧ ∀ j : Fin 5, j.val < i + 1 → ∀ b : Bool,
            (⟨j.val, by omega⟩, b) ∈ litSet (maxCircuit D) w →
            misChoice (maxCircuit D) (rows9 k) ⟨j.val, by omega⟩ ≠ some b := by
        intro k w hw
        unfold upd1 at hw
        have hbase : (uc.get k).get w.val = true := by
          split_ifs at hw <;> first | exact hw | (rw [B9.get_diff, Bool.and_eq_true] at hw; exact hw.1)
        obtain ⟨hwout, hprev⟩ := huc k w hbase
        refine ⟨hwout, fun j hj b hmem hch => ?_⟩
        by_cases hjlt : j.val < i
        · exact hprev j hjlt b hmem hch
        · have hji : j.val = i := by omega
          have hj_eq : (⟨j.val, by omega⟩ : Fin (maxCircuit D).size) = ⟨i, by omega⟩ := Fin.ext hji
          rw [hj_eq] at hmem hch
          unfold misChoice at hch
          rw [mem_litSet] at hmem
          by_cases hL : sideL (maxCircuit D) (rows9 k) ⟨i, by omega⟩ = false
          · rw [ite_eq_left hL] at hch
            have hb : b = false := Option.some.inj hch.symm
            subst hb; simp only [Bool.false_eq_true, ↓reduceIte] at hmem
            rw [hsL_get k, hL] at hw
            simp only [Bool.not_false, ↓reduceIte, B9.get_diff, Bool.and_eq_true, Bool.not_eq_true'] at hw
            have hmemD : w ∈ D.leftVars ⟨ii.val, by omega⟩ := hmem
            rw [hgi_L w, decide_eq_true hmemD] at hw; cases hw.2
          · rw [ite_eq_right hL] at hch
            by_cases hR : sideR (maxCircuit D) (rows9 k) ⟨i, by omega⟩ = false
            · rw [ite_eq_left hR] at hch
              have hb : b = true := Option.some.inj hch.symm
              subst hb; simp only [↓reduceIte] at hmem
              have hLt : sideL (maxCircuit D) (rows9 k) ⟨i, by omega⟩ = true := Bool.eq_true_of_not_eq_false hL
              rw [hsL_get k, hsR_get k, hLt, hR] at hw
              simp only [Bool.not_true, Bool.false_eq_true, Bool.not_false, ↓reduceIte, B9.get_diff,
                Bool.and_eq_true, Bool.not_eq_true'] at hw
              have hmemD : w ∈ D.rightVars ⟨ii.val, by omega⟩ := hmem
              rw [hgi_R w, decide_eq_true hmemD] at hw; cases hw.2
            · rw [ite_eq_right hR] at hch; cases hch
      have hsub : ∀ k : Fin 16, B9.sub (upd1 (uc.get k) gi.Lg gi.Rg (sL.get k) (sR.get k)) remV = true := by
        intro k
        rw [B9.sub_eq_true]
        intro w hw
        obtain ⟨hwout, hno_cov⟩ := hupd_inv k w hw
        have hcov := mis_cover_gen (maxCircuit D) (rows9 k) (hsepS k).1
        obtain ⟨g, b, hgb, hch⟩ := hcov.2 w hwout (Finset.notMem_empty w) ((hsepS k).2 w hwout)
        have hg_ge : i + 1 ≤ g.val := by
          by_contra hlt
          exact hno_cov ⟨g.val, by omega⟩ (by dsimp; omega) b hgb hch
        have hrem_g : nrem.get (σ ⟨g.val, by omega⟩).val = true := by
          dsimp only [nrem]; rw [B5.get_not, hnused, Equiv.symm_apply_apply]
          have hnotlt : ¬ (⟨g.val, by omega⟩ : Fin 5).val < i + 1 := by dsimp; omega
          rw [decide_eq_false hnotlt]; rfl
        have hv_g : (vB5 w).get (σ ⟨g.val, by omega⟩).val = true := by
          have hsym_g : (⟨(σ.symm (σ ⟨g.val, by omega⟩)).val, by omega⟩ : Fin D.size) = g :=
            Fin.ext (by simp [Equiv.symm_apply_apply])
          rw [hvB5 w (σ ⟨g.val, by omega⟩), hsym_g, decide_eq_true_eq]
          rw [mem_litSet] at hgb
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte] at hgb; exact Or.inl hgb
          · simp only [↓reduceIte] at hgb; exact Or.inr hgb
        have hany : B5.anyAnd (vB5 w) nrem = true :=
          (B5.anyAnd_eq_true (vB5 w) nrem).mpr ⟨σ ⟨g.val, by omega⟩, hv_g, hrem_g⟩
        have hremV : remV.get w.val = B5.anyAnd (vB5 w) nrem := by fin_cases w <;> rfl
        rw [hremV]; exact hany
      obtain ⟨uc', huc'_eq, huc'_get⟩ := updateU16_some uc sL sR gi.Lg gi.Rg remV hsub
      rw [huc'_eq]
      let pg : PlacedG := ⟨gi.Lg, gi.Rg, toB5 bsL, toB5 bsR, isZ⟩
      apply ih (i + 1) (by omega) nused (gvms ++ [gm]) (pg :: revPgs) uc' hnused
        (by simp [hgvLen])
        (fun j k => by
          by_cases hj : j.val < i
          · have : (gvms ++ [gm]).get j = gvms.get ⟨j.val, by omega⟩ := by
              simp only [List.get_eq_getElem]; exact List.getElem_append_left (by omega)
            rw [this]; exact hgvSpec ⟨j.val, by omega⟩ k
          · have hjeq : j.val = i := by have := j.isLt; simp [hgvLen] at this; omega
            have : (gvms ++ [gm]).get j = gm := by
              simp only [List.get_eq_getElem]
              rw [List.getElem_append_right (by omega)]
              have hsub0 : j.val - gvms.length = 0 := by omega
              simp [hsub0]
            rw [this, hgm_get k]
            congr 1; exact Fin.ext hjeq.symm)
        (by simp [hrevLen])
        (fun t => by
          have hrev_eq : (pg :: revPgs).reverse = revPgs.reverse ++ [pg] := List.reverse_cons
          have hrl : revPgs.reverse.length = i := by rw [List.length_reverse, hrevLen]
          by_cases ht : t.val < i
          · have ht_get : (pg :: revPgs).reverse.get t = revPgs.reverse.get ⟨t.val, by omega⟩ := by
              simp only [List.get_eq_getElem, hrev_eq]
              exact List.getElem_append_left (by omega)
            rw [ht_get]; exact hrevSpec ⟨t.val, by omega⟩
          · have hteq : t.val = i := by
              have htl := t.isLt
              have hrl2 : (pg :: revPgs).reverse.length = i + 1 := by simp [hrevLen]
              omega
            have ht_get : (pg :: revPgs).reverse.get t = pg := by
              simp only [List.get_eq_getElem, hrev_eq]
              rw [List.getElem_append_right (by omega)]
              simp [hrl, hteq]
            rw [ht_get]
            have hji : (⟨t.val, by omega⟩ : Fin (maxCircuit D).size) = ⟨i, by omega⟩ := Fin.ext hteq
            refine ⟨fun v => by dsimp [pg]; rw [hgi_L v, hji]; rfl,
                    fun v => by dsimp [pg]; rw [hgi_R v, hji]; rfl,
                    fun r => ?_, fun r => ?_, ?_⟩
            · dsimp [pg]; rw [toB5_get bsL (by omega) r]
              by_cases hr : r.val < i
              · rw [dite_eq_left (by omega)]
                simp only [bsL, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
                rw [hji]; exact (decide_eq_decide.mpr (by simp [hr, hteq])).symm
              · rw [dite_eq_right (by omega)]
                exact (decide_eq_false (by omega)).symm
            · dsimp [pg]; rw [toB5_get bsR (by omega) r]
              by_cases hr : r.val < i
              · rw [dite_eq_left (by omega)]
                simp only [bsR, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
                rw [hji]; exact (decide_eq_decide.mpr (by simp [hr, hteq])).symm
              · rw [dite_eq_right (by omega)]
                exact (decide_eq_false (by omega)).symm
            · dsimp [pg]
              exact hisZ.trans (congrArg (fun x : Fin (maxCircuit D).size => decide (x ∈ (maxCircuit D).outGates)) hji.symm))
        (fun k w hw => by rw [huc'_get k] at hw; exact hupd_inv k w hw)

lemma searchTopo_of_circuit (D : AndCountCircuit 9) (hsz : D.size = 5)
    (hW : D.WellFormed) (hsep : Separates D)
    (σ : Fin 5 ≃ Fin 5) (a0 : Fin 5) (hσ_a0 : σ a0 = 0)
    (hno0 : ∀ k : Fin 16, (0 : V) ∉ rows9 k →
      sideL D (rows9 k) ⟨a0.val, by omega⟩ = false ∧ sideR D (rows9 k) ⟨a0.val, by omega⟩ = true)
    (gates : List GInfo) (vB5 : V → B5)
    (hgates : ∀ i : Fin 5, ∃ gi ∈ gates,
      gi.gIdx = (σ i).val ∧
      (∀ v : V, gi.Lg.get v.val = decide (v ∈ D.leftVars ⟨i.val, by omega⟩)) ∧
      (∀ v : V, gi.Rg.get v.val = decide (v ∈ D.rightVars ⟨i.val, by omega⟩)) ∧
      (∀ k : Fin 16, gi.bmL.get k = decide (∃ v ∈ rows9 k, v ∈ D.leftVars ⟨i.val, by omega⟩)) ∧
      (∀ k : Fin 16, gi.bmR.get k = decide (∃ v ∈ rows9 k, v ∈ D.rightVars ⟨i.val, by omega⟩)))
    (hvB5 : ∀ v : V, ∀ g : Fin 5,
      (vB5 v).get g.val = decide (v ∈ D.leftVars ⟨(σ.symm g).val, by omega⟩ ∨ v ∈ D.rightVars ⟨(σ.symm g).val, by omega⟩)) :
    searchTopo gates (vB5 0) (vB5 1) (vB5 2) (vB5 3) (vB5 4) (vB5 5) (vB5 6) (vB5 7) (vB5 8)
      5 0 ⟨false,false,false,false,false⟩ [] [] initU16 = true := by
  exact searchTopo_sound_aux D hsz hW hsep σ a0 hσ_a0 hno0 gates vB5 hgates hvB5
    5 0 rfl ⟨false,false,false,false,false⟩ [] [] initU16
    (fun g => by fin_cases g <;> rfl)
    rfl (fun j => Fin.elim0 j)
    rfl (fun t => Fin.elim0 t)
    (fun k w hw => by
      rw [initU16_spec k w, decide_eq_true_eq] at hw
      exact ⟨hw, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)


/-! ## Section 6: Computational certificates (20 Phase-1 branches + 62→13 orbit witnesses + 13 Phase-2 orbits) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_0 : runBranch ⟨4, 2, 2, 3, 3⟩ ⟨16, 4, 4, 5, 5⟩ 3 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_1 : runBranch ⟨4, 2, 2, 3, 3⟩ ⟨24, 3, 4, 2, 5⟩ 3 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_2 : runBranch ⟨4, 2, 2, 3, 3⟩ ⟨80, 4, 6, 5, 7⟩ 7 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_3 : runBranch ⟨6, 1, 2, 0, 3⟩ ⟨8, 3, 3, 2, 2⟩ 1 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_4 : runBranch ⟨6, 1, 2, 0, 3⟩ ⟨10, 1, 3, 0, 2⟩ 1 = [[6, 10, 24, 72, 68, 20, 288, 640], [6, 10, 24, 72, 68, 20, 384, 544], [6, 10, 24, 72, 68, 272, 288, 640], [6, 10, 24, 72, 320, 20, 544, 384], [6, 10, 24, 96, 68, 272, 288, 640], [6, 10, 24, 96, 68, 272, 384, 640], [6, 10, 24, 320, 20, 640, 96, 384], [6, 10, 24, 320, 20, 640, 160, 576], [6, 10, 24, 320, 20, 640, 288, 576], [6, 10, 24, 320, 20, 640, 384, 576], [6, 10, 24, 320, 20, 640, 544, 384], [6, 10, 24, 320, 20, 640, 576, 384], [6, 10, 24, 320, 68, 20, 384, 544], [6, 10, 24, 320, 68, 144, 288, 544], [6, 10, 24, 320, 68, 144, 384, 544], [6, 10, 24, 320, 260, 20, 576, 160], [6, 10, 24, 320, 260, 528, 96, 160], [6, 10, 24, 320, 260, 528, 576, 160], [6, 10, 80, 40, 288, 68, 640, 272], [6, 10, 80, 40, 288, 68, 640, 384], [6, 10, 80, 136, 384, 20, 544, 288], [6, 10, 80, 136, 384, 20, 544, 320], [6, 10, 80, 264, 160, 260, 96, 144], [6, 10, 80, 264, 160, 260, 96, 528], [6, 10, 80, 264, 160, 260, 96, 640], [6, 10, 80, 264, 160, 260, 144, 96], [6, 10, 80, 264, 160, 260, 144, 544], [6, 10, 80, 264, 160, 260, 144, 576], [6, 10, 80, 264, 260, 20, 640, 96], [6, 10, 80, 264, 260, 68, 544, 144], [6, 10, 80, 264, 288, 20, 640, 96], [6, 10, 80, 264, 288, 20, 640, 576], [6, 10, 80, 264, 384, 68, 544, 144], [6, 10, 80, 264, 384, 68, 544, 528]] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_5 : runBranch ⟨6, 1, 2, 0, 3⟩ ⟨16, 4, 4, 5, 5⟩ 3 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_6 : runBranch ⟨6, 1, 2, 0, 3⟩ ⟨18, 1, 4, 0, 5⟩ 3 = [[6, 18, 40, 80, 68, 288, 384, 640], [6, 18, 72, 272, 68, 288, 136, 544], [6, 18, 72, 272, 260, 40, 640, 576], [6, 18, 72, 272, 260, 160, 640, 576], [6, 18, 80, 40, 288, 68, 640, 384], [6, 18, 80, 264, 40, 68, 384, 640], [6, 18, 80, 264, 96, 260, 160, 520], [6, 18, 80, 264, 544, 68, 384, 640]] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_7 : runBranch ⟨6, 1, 2, 0, 3⟩ ⟨24, 3, 4, 2, 5⟩ 3 = [[6, 24, 40, 320, 36, 640, 144, 576], [6, 24, 40, 320, 36, 640, 384, 576], [6, 24, 40, 320, 36, 640, 528, 384], [6, 24, 40, 320, 36, 640, 576, 384], [6, 24, 320, 40, 640, 36, 384, 528], [6, 24, 320, 40, 640, 36, 384, 576], [6, 24, 320, 40, 640, 36, 576, 144], [6, 24, 320, 40, 640, 36, 576, 384]] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_8 : runBranch ⟨6, 1, 2, 0, 3⟩ ⟨80, 4, 6, 5, 7⟩ 7 = [[6, 80, 96, 264, 160, 260, 144, 520], [6, 80, 144, 264, 160, 260, 96, 520], [6, 80, 264, 96, 260, 160, 520, 144], [6, 80, 264, 144, 260, 160, 520, 96]] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_9 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨8, 3, 3, 2, 2⟩ 3 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_10 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨24, 3, 4, 2, 5⟩ 3 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_11 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨32, 5, 5, 4, 4⟩ 3 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_12 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨36, 2, 5, 3, 4⟩ 3 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_13 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨40, 3, 5, 2, 4⟩ 3 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_14 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨64, 6, 6, 7, 7⟩ 7 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_15 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨68, 2, 6, 3, 7⟩ 7 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_16 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨72, 3, 6, 2, 7⟩ 7 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_17 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨80, 4, 6, 5, 7⟩ 7 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_18 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨96, 5, 6, 4, 7⟩ 7 = [] := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p1_19 : runBranch ⟨20, 2, 4, 3, 5⟩ ⟨320, 6, 8, 7, 9⟩ 15 = [[20, 320, 40, 384, 24, 640, 36, 576], [20, 320, 40, 384, 36, 640, 24, 576], [20, 320, 40, 576, 24, 640, 36, 384], [20, 320, 40, 576, 36, 640, 24, 384], [20, 320, 384, 40, 640, 24, 576, 36], [20, 320, 384, 40, 640, 36, 576, 24], [20, 320, 576, 40, 640, 24, 384, 36], [20, 320, 576, 40, 640, 36, 384, 24]] := by decide +kernel

lemma runBranch_mem_classes62 : ∀ p ∈ validW12Pairs, ∀ c ∈ runBranch p.1 p.2.1 p.2.2, c ∈ classes62 := by
  have hsub4 : ∀ c ∈ ([ [6, 10, 24, 72, 68, 20, 288, 640], [6, 10, 24, 72, 68, 20, 384, 544], [6, 10, 24, 72, 68, 272, 288, 640], [6, 10, 24, 72, 320, 20, 544, 384], [6, 10, 24, 96, 68, 272, 288, 640], [6, 10, 24, 96, 68, 272, 384, 640], [6, 10, 24, 320, 20, 640, 96, 384], [6, 10, 24, 320, 20, 640, 160, 576], [6, 10, 24, 320, 20, 640, 288, 576], [6, 10, 24, 320, 20, 640, 384, 576], [6, 10, 24, 320, 20, 640, 544, 384], [6, 10, 24, 320, 20, 640, 576, 384], [6, 10, 24, 320, 68, 20, 384, 544], [6, 10, 24, 320, 68, 144, 288, 544], [6, 10, 24, 320, 68, 144, 384, 544], [6, 10, 24, 320, 260, 20, 576, 160], [6, 10, 24, 320, 260, 528, 96, 160], [6, 10, 24, 320, 260, 528, 576, 160], [6, 10, 80, 40, 288, 68, 640, 272], [6, 10, 80, 40, 288, 68, 640, 384], [6, 10, 80, 136, 384, 20, 544, 288], [6, 10, 80, 136, 384, 20, 544, 320], [6, 10, 80, 264, 160, 260, 96, 144], [6, 10, 80, 264, 160, 260, 96, 528], [6, 10, 80, 264, 160, 260, 96, 640], [6, 10, 80, 264, 160, 260, 144, 96], [6, 10, 80, 264, 160, 260, 144, 544], [6, 10, 80, 264, 160, 260, 144, 576], [6, 10, 80, 264, 260, 20, 640, 96], [6, 10, 80, 264, 260, 68, 544, 144], [6, 10, 80, 264, 288, 20, 640, 96], [6, 10, 80, 264, 288, 20, 640, 576], [6, 10, 80, 264, 384, 68, 544, 144], [6, 10, 80, 264, 384, 68, 544, 528] ] : List (List Nat)), c ∈ classes62 := by decide +kernel
  have hsub6 : ∀ c ∈ ([ [6, 18, 40, 80, 68, 288, 384, 640], [6, 18, 72, 272, 68, 288, 136, 544], [6, 18, 72, 272, 260, 40, 640, 576], [6, 18, 72, 272, 260, 160, 640, 576], [6, 18, 80, 40, 288, 68, 640, 384], [6, 18, 80, 264, 40, 68, 384, 640], [6, 18, 80, 264, 96, 260, 160, 520], [6, 18, 80, 264, 544, 68, 384, 640] ] : List (List Nat)), c ∈ classes62 := by decide +kernel
  have hsub7 : ∀ c ∈ ([ [6, 24, 40, 320, 36, 640, 144, 576], [6, 24, 40, 320, 36, 640, 384, 576], [6, 24, 40, 320, 36, 640, 528, 384], [6, 24, 40, 320, 36, 640, 576, 384], [6, 24, 320, 40, 640, 36, 384, 528], [6, 24, 320, 40, 640, 36, 384, 576], [6, 24, 320, 40, 640, 36, 576, 144], [6, 24, 320, 40, 640, 36, 576, 384] ] : List (List Nat)), c ∈ classes62 := by decide +kernel
  have hsub8 : ∀ c ∈ ([ [6, 80, 96, 264, 160, 260, 144, 520], [6, 80, 144, 264, 160, 260, 96, 520], [6, 80, 264, 96, 260, 160, 520, 144], [6, 80, 264, 144, 260, 160, 520, 96] ] : List (List Nat)), c ∈ classes62 := by decide +kernel
  have hsub19 : ∀ c ∈ ([ [20, 320, 40, 384, 24, 640, 36, 576], [20, 320, 40, 384, 36, 640, 24, 576], [20, 320, 40, 576, 24, 640, 36, 384], [20, 320, 40, 576, 36, 640, 24, 384], [20, 320, 384, 40, 640, 24, 576, 36], [20, 320, 384, 40, 640, 36, 576, 24], [20, 320, 576, 40, 640, 24, 384, 36], [20, 320, 576, 40, 640, 36, 384, 24] ] : List (List Nat)), c ∈ classes62 := by decide +kernel
  intro p hp c hc
  simp only [validW12Pairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [p1_0] at hc; cases hc
  · rw [p1_1] at hc; cases hc
  · rw [p1_2] at hc; cases hc
  · rw [p1_3] at hc; cases hc
  · rw [p1_4] at hc; exact hsub4 c hc
  · rw [p1_5] at hc; cases hc
  · rw [p1_6] at hc; exact hsub6 c hc
  · rw [p1_7] at hc; exact hsub7 c hc
  · rw [p1_8] at hc; exact hsub8 c hc
  · rw [p1_9] at hc; cases hc
  · rw [p1_10] at hc; cases hc
  · rw [p1_11] at hc; cases hc
  · rw [p1_12] at hc; cases hc
  · rw [p1_13] at hc; cases hc
  · rw [p1_14] at hc; cases hc
  · rw [p1_15] at hc; cases hc
  · rw [p1_16] at hc; cases hc
  · rw [p1_17] at hc; cases hc
  · rw [p1_18] at hc; cases hc
  · rw [p1_19] at hc; exact hsub19 c hc

def reps13 : Fin 13 → List Nat
  | ⟨0, _⟩ => [6, 10, 24, 72, 68, 20, 288, 640]
  | ⟨1, _⟩ => [6, 10, 24, 72, 68, 272, 288, 640]
  | ⟨2, _⟩ => [6, 10, 24, 96, 68, 272, 288, 640]
  | ⟨3, _⟩ => [6, 10, 24, 96, 68, 272, 384, 640]
  | ⟨4, _⟩ => [6, 10, 24, 320, 20, 640, 96, 384]
  | ⟨5, _⟩ => [6, 10, 24, 320, 20, 640, 384, 576]
  | ⟨6, _⟩ => [6, 18, 40, 80, 68, 288, 384, 640]
  | ⟨7, _⟩ => [6, 18, 72, 272, 68, 288, 136, 544]
  | ⟨8, _⟩ => [6, 18, 72, 272, 260, 160, 640, 576]
  | ⟨9, _⟩ => [6, 24, 40, 320, 36, 640, 144, 576]
  | ⟨10, _⟩ => [6, 24, 40, 320, 36, 640, 384, 576]
  | ⟨11, _⟩ => [6, 80, 96, 264, 160, 260, 144, 520]
  | ⟨12, _⟩ => [20, 320, 40, 384, 24, 640, 36, 576]

def gInfoOf (r : List Nat) (g : Fin 5) : GInfo :=
  let Lg := B9.ofFn (fun v => if v.val == 0 then g.val == 0 else (r.getD (v.val - 1) 0).testBit (2 * g.val))
  let Rg := B9.ofFn (fun v => if v.val == 0 then false else (r.getD (v.val - 1) 0).testBit (2 * g.val + 1))
  let bmL := B16.ofFn (fun k => (List.finRange 9).any fun v => (misMask k).testBit v.val && Lg.get v.val)
  let bmR := B16.ofFn (fun k => (List.finRange 9).any fun v => (misMask k).testBit v.val && Rg.get v.val)
  ⟨g.val, Lg, Rg, bmL, bmR⟩

def vB5Of (r : List Nat) (v : V) : B5 :=
  B5.ofFn (fun g =>
    if v.val == 0 then g.val == 0
    else (r.getD (v.val - 1) 0).testBit (2 * g.val) || (r.getD (v.val - 1) 0).testBit (2 * g.val + 1))

def orbitG : Fin 13 → List GInfo
  | ⟨0, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,true,false,false⟩, ⟨false,false,true,true,true,false,false,false,false⟩, ⟨false,false,true,true,true,true,true,false,false,true,true,true,false,false,true,true⟩, ⟨true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩]
  | ⟨1, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,true,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩]
  | ⟨2, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,true,false,false,true,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩, ⟨true,true,true,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩]
  | ⟨3, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,true,false,false,false,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩]
  | ⟨4, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,false,false,true,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,false,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,false,false,false,false,false⟩⟩]
  | ⟨5, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,false,false,true,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩]
  | ⟨6, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,false,false,false,false,false,false,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨true,true,true,false,false,false,true,true,true,false,false,true,false,true,false,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩]
  | ⟨7, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,false,true,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,true,true,true,true,false,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,false,false,true,false,true,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩, ⟨3, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,true,true,true,false,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩]
  | ⟨8, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,false,false,false,false,false,false,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,false⟩, ⟨true,true,true,false,false,false,true,true,true,false,false,true,false,true,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,true,false,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨true,true,false,true,false,false,false,false,false,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true⟩⟩]
  | ⟨9, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,false,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,true,true,false,false,false,true,true,false,false,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,false,false,false,true,false⟩, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,true,false,false,false,false,true,true,true,true,true,true,false,true,false,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩⟩, ⟨3, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,false,false,false,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩]
  | ⟨10, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,false,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,true,true,false,false,false,true,true,false,false,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,false,false,false,false,false⟩, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,true,false,false,false,false,true,false,true,false,false,true,false,true,false,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩⟩, ⟨3, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,false,false,true,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩]
  | ⟨11, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,false,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,true,true,false,false,false,true,true,false,false,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,false,true,false,false⟩, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩⟩, ⟨2, ⟨false,false,true,false,false,false,false,true,false⟩, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,true,false,false,false,false,true,true,true,true,true,true,false,true,false,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩⟩, ⟨3, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,true,false,true,false⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩, ⟨false,false,true,false,true,true,true,true,true,true,true,false,false,false,true,true⟩⟩, ⟨4, ⟨false,false,false,false,true,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,true,true,true,false,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩]
  | ⟨12, _⟩ => [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false⟩⟩, ⟨1, ⟨false,true,false,false,false,false,false,true,false⟩, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,false,true,true,true,true,true,true,true,false,false,false,true⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩⟩, ⟨2, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,false,true,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,true,true,true,true,false,true,true,false,false⟩⟩, ⟨3, ⟨false,false,true,false,false,false,false,false,true⟩, ⟨false,false,false,false,true,false,true,false,false⟩, ⟨false,true,false,false,false,false,true,false,true,false,false,true,true,true,true,true⟩, ⟨true,true,true,true,true,true,false,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,false,false,true,false,true,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩]

def orbitV : Fin 13 → V → B5
  | ⟨0, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,true,false,true,false⟩, ⟨false,true,false,true,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,true,false,true⟩, ⟨false,false,false,true,true⟩]
  | ⟨1, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,true,false,true,false⟩, ⟨false,true,false,true,false⟩, ⟨false,false,true,false,true⟩, ⟨false,false,true,false,true⟩, ⟨false,false,false,true,true⟩]
  | ⟨2, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,true,true,false⟩, ⟨false,true,false,true,false⟩, ⟨false,false,true,false,true⟩, ⟨false,false,true,false,true⟩, ⟨false,false,false,true,true⟩]
  | ⟨3, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,true,true,false⟩, ⟨false,true,false,true,false⟩, ⟨false,false,true,false,true⟩, ⟨false,false,false,true,true⟩, ⟨false,false,false,true,true⟩]
  | ⟨4, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,false,true,true,false⟩, ⟨false,false,false,true,true⟩]
  | ⟨5, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,false,false,true,true⟩, ⟨false,false,false,true,true⟩]
  | ⟨6, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,false,true,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,true,true,false⟩, ⟨false,true,false,true,false⟩, ⟨false,false,true,false,true⟩, ⟨false,false,false,true,true⟩, ⟨false,false,false,true,true⟩]
  | ⟨7, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,false,true,false,false⟩, ⟨false,true,false,true,false⟩, ⟨false,false,true,false,true⟩, ⟨false,true,false,true,false⟩, ⟨false,false,true,false,true⟩, ⟨false,true,false,true,false⟩, ⟨false,false,true,false,true⟩]
  | ⟨8, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨true,false,true,false,false⟩, ⟨false,true,false,true,false⟩, ⟨false,false,true,false,true⟩, ⟨false,true,false,false,true⟩, ⟨false,false,true,true,false⟩, ⟨false,false,false,true,true⟩, ⟨false,false,false,true,true⟩]
  | ⟨9, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,false,true,true,false⟩, ⟨false,false,false,true,true⟩]
  | ⟨10, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,false,false,true,true⟩, ⟨false,false,false,true,true⟩]
  | ⟨11, _⟩ => ![⟨true,false,false,false,false⟩, ⟨true,true,false,false,false⟩, ⟨false,false,true,true,false⟩, ⟨false,false,true,true,false⟩, ⟨false,true,false,false,true⟩, ⟨false,false,true,true,false⟩, ⟨false,true,false,false,true⟩, ⟨false,false,true,true,false⟩, ⟨false,true,false,false,true⟩]
  | ⟨12, _⟩ => ![⟨true,false,false,false,false⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩, ⟨false,true,true,false,false⟩, ⟨false,false,false,true,true⟩]

lemma orbit_lit_eq : ∀ o : Fin 13,
    (List.finRange 5).map (gInfoOf (reps13 o)) = orbitG o ∧
    ∀ v : V, vB5Of (reps13 o) v = orbitV o v := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_0 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,true,false,false⟩, ⟨false,false,true,true,true,false,false,false,false⟩, ⟨false,false,true,true,true,true,true,false,false,true,true,true,false,false,true,true⟩, ⟨true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,true,false,true,false⟩ ⟨false,true,false,true,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,true,false,true⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_1 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,true,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,true,false,true,false⟩ ⟨false,true,false,true,false⟩ ⟨false,false,true,false,true⟩ ⟨false,false,true,false,true⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_2 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,true,false,false,true,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩, ⟨true,true,true,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,true,true,false⟩ ⟨false,true,false,true,false⟩ ⟨false,false,true,false,true⟩ ⟨false,false,true,false,true⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_3 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨false,false,false,false,true,false,false,false,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,true,true,false⟩ ⟨false,true,false,true,false⟩ ⟨false,false,true,false,true⟩ ⟨false,false,false,true,true⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_4 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,false,false,true,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,false,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,false,false,false,false,false⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,false,true,true,false⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_5 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,false,false,true,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,false,false,true,true⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_6 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,false,false,false,false,false,false,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,true,false,false,true,false,false⟩, ⟨true,true,true,false,false,false,true,true,true,false,false,true,false,true,false,false⟩, ⟨true,true,false,true,true,true,false,false,false,true,true,false,true,true,false,false⟩⟩, ⟨3, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true⟩⟩, ⟨4, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,false,true,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,true,true,false⟩ ⟨false,true,false,true,false⟩ ⟨false,false,true,false,true⟩ ⟨false,false,false,true,true⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_7 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,false,true,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,true,true,true,true,false,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,false,false,true,false,true,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩, ⟨3, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,true,true,true,false,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,false,true,false,false⟩ ⟨false,true,false,true,false⟩ ⟨false,false,true,false,true⟩ ⟨false,true,false,true,false⟩ ⟨false,false,true,false,true⟩ ⟨false,true,false,true,false⟩ ⟨false,false,true,false,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_8 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,true,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,true,false,false,false,true,true,false,true,false,true,true,false,true,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,false,false,false,false,false,false,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,false⟩, ⟨true,true,true,false,false,false,true,true,true,false,false,true,false,true,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,false,false,false,false,false⟩⟩, ⟨3, ⟨false,false,false,true,false,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨true,true,false,true,false,false,false,false,false,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,true,false,false,false⟩, ⟨false,false,false,false,false,false,false,true,true⟩, ⟨true,true,true,false,true,true,false,true,true,false,false,false,false,false,true,true⟩, ⟨false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨true,false,true,false,false⟩ ⟨false,true,false,true,false⟩ ⟨false,false,true,false,true⟩ ⟨false,true,false,false,true⟩ ⟨false,false,true,true,false⟩ ⟨false,false,false,true,true⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_9 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,false,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,true,true,false,false,false,true,true,false,false,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,false,false,false,true,false⟩, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,true,false,false,false,false,true,true,true,true,true,true,false,true,false,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩⟩, ⟨3, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,false,false,false,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,false,true,true,false⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_10 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,false,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,true,true,false,false,false,true,true,false,false,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩⟩, ⟨2, ⟨false,false,true,false,false,false,false,false,false⟩, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,true,false,false,false,false,true,false,true,false,false,true,false,true,false,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩⟩, ⟨3, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,false,false,false,true,true,false⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩, ⟨false,false,false,true,true,true,true,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,false,false,true,false,false,true,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,false,false,true,true⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_11 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,true,false,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,true,true,false,false,false,true,true,false,false,false,true⟩⟩, ⟨1, ⟨false,true,false,false,false,false,true,false,false⟩, ⟨false,false,false,false,true,false,false,false,true⟩, ⟨false,false,false,true,true,true,true,false,false,true,true,true,false,false,false,true⟩, ⟨true,true,true,false,false,false,false,true,true,false,false,true,true,true,true,true⟩⟩, ⟨2, ⟨false,false,true,false,false,false,false,true,false⟩, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,true,false,false,false,false,true,true,true,true,true,true,false,true,false,false⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩⟩, ⟨3, ⟨false,false,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,true,false,true,false⟩, ⟨true,true,false,true,false,false,true,false,true,false,false,true,true,true,false,false⟩, ⟨false,false,true,false,true,true,true,true,true,true,true,false,false,false,true,true⟩⟩, ⟨4, ⟨false,false,false,false,true,false,true,false,false⟩, ⟨false,false,false,false,false,false,false,false,true⟩, ⟨true,true,true,true,true,true,false,true,true,true,true,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨true,true,false,false,false⟩ ⟨false,false,true,true,false⟩ ⟨false,false,true,true,false⟩ ⟨false,true,false,false,true⟩ ⟨false,false,true,true,false⟩ ⟨false,true,false,false,true⟩ ⟨false,false,true,true,false⟩ ⟨false,true,false,false,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem orbit_12 : (searchTopo [⟨0, ⟨true,false,false,false,false,false,false,false,false⟩, ⟨false,false,false,false,false,false,false,false,false⟩, ⟨true,false,true,true,true,false,false,true,false,true,false,false,true,false,true,false⟩, ⟨false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false⟩⟩, ⟨1, ⟨false,true,false,false,false,false,false,true,false⟩, ⟨false,false,false,true,false,true,false,false,false⟩, ⟨false,false,false,false,false,true,true,true,true,true,true,true,false,false,false,true⟩, ⟨true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true⟩⟩, ⟨2, ⟨false,true,false,false,false,true,false,false,false⟩, ⟨false,false,false,true,false,false,false,true,false⟩, ⟨false,false,true,false,true,true,true,false,false,false,true,true,false,false,true,true⟩, ⟨true,true,false,true,false,false,true,true,true,true,true,false,true,true,false,false⟩⟩, ⟨3, ⟨false,false,true,false,false,false,false,false,true⟩, ⟨false,false,false,false,true,false,true,false,false⟩, ⟨false,true,false,false,false,false,true,false,true,false,false,true,true,true,true,true⟩, ⟨true,true,true,true,true,true,false,true,true,true,true,false,false,false,false,false⟩⟩, ⟨4, ⟨false,false,true,false,true,false,false,false,false⟩, ⟨false,false,false,false,false,false,true,false,true⟩, ⟨true,true,true,false,false,false,true,true,true,false,false,true,false,true,false,false⟩, ⟨false,false,false,true,true,true,false,false,false,true,true,true,true,true,true,true⟩⟩] ⟨true,false,false,false,false⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ ⟨false,true,true,false,false⟩ ⟨false,false,false,true,true⟩ 5 0 ⟨false,false,false,false,false⟩ [] [] initU16) = false := by decide +kernel

lemma all_orbits_false (o : Fin 13) :
    searchTopo (orbitG o) (orbitV o 0) (orbitV o 1) (orbitV o 2) (orbitV o 3) (orbitV o 4)
      (orbitV o 5) (orbitV o 6) (orbitV o 7) (orbitV o 8)
      5 0 ⟨false,false,false,false,false⟩ [] [] initU16 = false := by
  fin_cases o
  · exact orbit_0
  · exact orbit_1
  · exact orbit_2
  · exact orbit_3
  · exact orbit_4
  · exact orbit_5
  · exact orbit_6
  · exact orbit_7
  · exact orbit_8
  · exact orbit_9
  · exact orbit_10
  · exact orbit_11
  · exact orbit_12

def wit62 : List (List Nat × Fin 4 × List (Fin 5) × List Bool × Fin 13) := [
  ([6, 10, 24, 72, 68, 20, 288, 640], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 0),
  ([6, 10, 24, 72, 68, 20, 384, 544], 1, [0, 1, 3, 2, 4], [false, true, false, false, false], 0),
  ([6, 10, 24, 72, 68, 272, 288, 640], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 1),
  ([6, 10, 24, 72, 320, 20, 544, 384], 2, [0, 1, 3, 2, 4], [false, false, false, false, false], 1),
  ([6, 10, 24, 96, 68, 272, 288, 640], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 2),
  ([6, 10, 24, 96, 68, 272, 384, 640], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 3),
  ([6, 10, 24, 320, 20, 640, 96, 384], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 4),
  ([6, 10, 24, 320, 20, 640, 160, 576], 1, [0, 1, 2, 3, 4], [false, true, false, true, true], 4),
  ([6, 10, 24, 320, 20, 640, 288, 576], 0, [0, 1, 2, 4, 3], [false, false, false, false, false], 4),
  ([6, 10, 24, 320, 20, 640, 384, 576], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 5),
  ([6, 10, 24, 320, 20, 640, 544, 384], 1, [0, 1, 2, 4, 3], [false, true, false, true, true], 4),
  ([6, 10, 24, 320, 20, 640, 576, 384], 0, [0, 1, 2, 4, 3], [false, false, false, false, false], 5),
  ([6, 10, 24, 320, 68, 20, 384, 544], 1, [0, 1, 3, 2, 4], [false, true, false, false, false], 1),
  ([6, 10, 24, 320, 68, 144, 288, 544], 1, [0, 1, 3, 2, 4], [false, true, false, false, false], 3),
  ([6, 10, 24, 320, 68, 144, 384, 544], 1, [0, 1, 3, 2, 4], [false, true, false, false, false], 2),
  ([6, 10, 24, 320, 260, 20, 576, 160], 1, [0, 1, 4, 2, 3], [false, true, false, false, false], 1),
  ([6, 10, 24, 320, 260, 528, 96, 160], 1, [0, 1, 4, 2, 3], [false, true, false, false, false], 3),
  ([6, 10, 24, 320, 260, 528, 576, 160], 1, [0, 1, 4, 2, 3], [false, true, false, false, false], 2),
  ([6, 10, 80, 40, 288, 68, 640, 272], 2, [0, 1, 2, 3, 4], [false, false, true, false, false], 2),
  ([6, 10, 80, 40, 288, 68, 640, 384], 2, [0, 1, 2, 3, 4], [false, false, true, false, false], 3),
  ([6, 10, 80, 136, 384, 20, 544, 288], 2, [0, 1, 3, 2, 4], [false, false, true, false, false], 3),
  ([6, 10, 80, 136, 384, 20, 544, 320], 2, [0, 1, 3, 2, 4], [false, false, true, false, false], 2),
  ([6, 10, 80, 264, 160, 260, 96, 144], 2, [0, 1, 4, 3, 2], [false, false, false, false, false], 5),
  ([6, 10, 80, 264, 160, 260, 96, 528], 2, [0, 1, 4, 2, 3], [false, false, false, false, false], 4),
  ([6, 10, 80, 264, 160, 260, 96, 640], 3, [0, 1, 4, 3, 2], [false, true, false, true, true], 4),
  ([6, 10, 80, 264, 160, 260, 144, 96], 2, [0, 1, 4, 2, 3], [false, false, false, false, false], 5),
  ([6, 10, 80, 264, 160, 260, 144, 544], 3, [0, 1, 4, 2, 3], [false, true, false, true, true], 4),
  ([6, 10, 80, 264, 160, 260, 144, 576], 2, [0, 1, 4, 3, 2], [false, false, false, false, false], 4),
  ([6, 10, 80, 264, 260, 20, 640, 96], 3, [0, 1, 2, 4, 3], [false, true, false, false, false], 1),
  ([6, 10, 80, 264, 260, 68, 544, 144], 3, [0, 1, 3, 4, 2], [false, true, false, false, false], 1),
  ([6, 10, 80, 264, 288, 20, 640, 96], 3, [0, 1, 2, 4, 3], [false, true, false, false, false], 2),
  ([6, 10, 80, 264, 288, 20, 640, 576], 3, [0, 1, 2, 4, 3], [false, true, false, false, false], 3),
  ([6, 10, 80, 264, 384, 68, 544, 144], 3, [0, 1, 3, 4, 2], [false, true, false, false, false], 2),
  ([6, 10, 80, 264, 384, 68, 544, 528], 3, [0, 1, 3, 4, 2], [false, true, false, false, false], 3),
  ([6, 18, 40, 80, 68, 288, 384, 640], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 6),
  ([6, 18, 72, 272, 68, 288, 136, 544], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 7),
  ([6, 18, 72, 272, 260, 40, 640, 576], 3, [0, 2, 1, 4, 3], [false, false, false, false, false], 6),
  ([6, 18, 72, 272, 260, 160, 640, 576], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 8),
  ([6, 18, 80, 40, 288, 68, 640, 384], 2, [0, 1, 2, 3, 4], [false, false, false, false, false], 6),
  ([6, 18, 80, 264, 40, 68, 384, 640], 1, [0, 2, 1, 3, 4], [false, false, false, false, false], 6),
  ([6, 18, 80, 264, 96, 260, 160, 520], 1, [0, 2, 1, 3, 4], [false, false, false, false, false], 7),
  ([6, 18, 80, 264, 544, 68, 384, 640], 1, [0, 2, 1, 4, 3], [false, false, false, true, false], 8),
  ([6, 24, 40, 320, 36, 640, 144, 576], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 9),
  ([6, 24, 40, 320, 36, 640, 384, 576], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 10),
  ([6, 24, 40, 320, 36, 640, 528, 384], 0, [0, 1, 2, 4, 3], [false, false, false, false, false], 9),
  ([6, 24, 40, 320, 36, 640, 576, 384], 0, [0, 1, 2, 4, 3], [false, false, false, false, false], 10),
  ([6, 24, 320, 40, 640, 36, 384, 528], 2, [0, 1, 2, 4, 3], [false, false, false, false, false], 9),
  ([6, 24, 320, 40, 640, 36, 384, 576], 2, [0, 1, 2, 4, 3], [false, false, false, false, false], 10),
  ([6, 24, 320, 40, 640, 36, 576, 144], 2, [0, 1, 2, 3, 4], [false, false, false, false, false], 9),
  ([6, 24, 320, 40, 640, 36, 576, 384], 2, [0, 1, 2, 3, 4], [false, false, false, false, false], 10),
  ([6, 80, 96, 264, 160, 260, 144, 520], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 11),
  ([6, 80, 144, 264, 160, 260, 96, 520], 0, [0, 1, 3, 2, 4], [false, false, false, false, false], 11),
  ([6, 80, 264, 96, 260, 160, 520, 144], 2, [0, 1, 2, 3, 4], [false, false, false, false, false], 11),
  ([6, 80, 264, 144, 260, 160, 520, 96], 2, [0, 1, 3, 2, 4], [false, false, false, false, false], 11),
  ([20, 320, 40, 384, 24, 640, 36, 576], 0, [0, 1, 2, 3, 4], [false, false, false, false, false], 12),
  ([20, 320, 40, 384, 36, 640, 24, 576], 0, [0, 2, 1, 3, 4], [false, false, false, false, false], 12),
  ([20, 320, 40, 576, 24, 640, 36, 384], 0, [0, 1, 2, 4, 3], [false, false, false, false, false], 12),
  ([20, 320, 40, 576, 36, 640, 24, 384], 0, [0, 2, 1, 4, 3], [false, false, false, false, false], 12),
  ([20, 320, 384, 40, 640, 24, 576, 36], 1, [0, 3, 4, 1, 2], [false, false, false, false, false], 12),
  ([20, 320, 384, 40, 640, 36, 576, 24], 1, [0, 3, 4, 2, 1], [false, false, false, false, false], 12),
  ([20, 320, 576, 40, 640, 24, 384, 36], 1, [0, 4, 3, 1, 2], [false, false, false, false, false], 12),
  ([20, 320, 576, 40, 640, 36, 384, 24], 1, [0, 4, 3, 2, 1], [false, false, false, false, false], 12)
]

lemma wit62_cover : ∀ c ∈ classes62, ∃ w ∈ wit62, w.1 = c := by decide +kernel

lemma wit62_ok : ∀ w ∈ wit62,
    w.2.2.1.getD 0 0 = 0 ∧
    w.2.2.2.1.getD 0 false = false ∧
    (∀ g1 g2 : Fin 5, w.2.2.1.getD g1.val 0 = w.2.2.1.getD g2.val 0 → g1 = g2) ∧
    (∀ v : V, v.val ≠ 0 → ∀ g : Fin 5,
      let ov := autFn w.2.1 v
      let og := w.2.2.1.getD g.val 0
      let m := w.1.getD (ov.val - 1) 0
      let bL := m.testBit (2 * og.val)
      let bR := m.testBit (2 * og.val + 1)
      let fl := w.2.2.2.1.getD g.val false
      (if fl then bR else bL) = ((reps13 w.2.2.2.2).getD (v.val - 1) 0).testBit (2 * g.val) ∧
      (if fl then bL else bR) = ((reps13 w.2.2.2.2).getD (v.val - 1) 0).testBit (2 * g.val + 1)) := by
  decide +kernel

lemma reduce_class62_to_false (D'' : AndCountCircuit 9) (a0 : Fin 5) (hsz'' : D''.size = 5)
    (hW'' : D''.WellFormed) (hsep'' : Separates D'')
    (σ : Fin 5 ≃ Fin 5) (hσ_a0 : σ a0 = 0)
    (hLa0'' : D''.leftVars ⟨a0.val, by omega⟩ = {0})
    (h0R'' : (0 : V) ∉ D''.rightVars ⟨a0.val, by omega⟩)
    (h0oth'' : ∀ i : Fin 5, i ≠ a0 → (0 : V) ∉ D''.leftVars ⟨i.val, by omega⟩ ∧ (0 : V) ∉ D''.rightVars ⟨i.val, by omega⟩)
    (hno0'' : ∀ k : Fin 16, (0 : V) ∉ rows9 k →
      sideL D'' (rows9 k) ⟨a0.val, by omega⟩ = false ∧ sideR D'' (rows9 k) ⟨a0.val, by omega⟩ = true)
    (c : List Nat) (hc_mem : c ∈ classes62)
    (hc_spec : ∀ v : V, v.val ≠ 0 → ∀ g : Fin 5,
      (v ∈ D''.leftVars ⟨(σ.symm g).val, by omega⟩ ↔ (c.getD (v.val - 1) 0).testBit (2 * g.val) = true) ∧
      (v ∈ D''.rightVars ⟨(σ.symm g).val, by omega⟩ ↔ (c.getD (v.val - 1) 0).testBit (2 * g.val + 1) = true)) :
    False := by
  obtain ⟨⟨c', pIdx, gp, fl, oIdx⟩, hw_mem, rfl⟩ := wit62_cover c hc_mem
  obtain ⟨hgp0, hfl0, hgp_inj, hw_bit⟩ := wit62_ok _ hw_mem
  dsimp only at hgp0 hfl0 hgp_inj hw_bit hc_spec
  let gpf : Fin 5 → Fin 5 := fun g => gp.getD g.val 0
  let gpE : Fin 5 ≃ Fin 5 := Equiv.ofBijective gpf ((Finite.injective_iff_bijective).mp hgp_inj)
  let σ' : Fin 5 ≃ Fin 5 := σ.trans gpE.symm
  have hσ'_a0 : σ' a0 = 0 := by
    dsimp only [σ', Equiv.trans_apply]
    rw [hσ_a0]
    exact gpE.symm_apply_eq.mpr hgp0.symm
  have hσ'_symm : ∀ g : Fin 5, σ'.symm g = σ.symm (gpf g) := fun g => rfl
  have haut0 : autFn pIdx 0 = 0 := autPerm_zero pIdx
  let D1 := permuteVars D'' (autPerm pIdx)
  have hsz1 : D1.size = 5 := hsz''
  have hW1 : D1.WellFormed := permuteVars_wf D'' _ hW''
  have hsep1 : Separates D1 := permuteVars_separates D'' pIdx hsep''
  have hD1_memL : ∀ (v : V) (i : Fin D1.size), v ∈ D1.leftVars i ↔ autFn pIdx v ∈ D''.leftVars ⟨i.val, by omega⟩ := by
    intro v i
    change v ∈ (D''.leftVars ⟨i.val, by omega⟩).map (autPerm pIdx).toEmbedding ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa [autPerm, autFn_invol] using ha
    · intro h; exact ⟨autFn pIdx v, h, autFn_invol pIdx v⟩
  have hD1_memR : ∀ (v : V) (i : Fin D1.size), v ∈ D1.rightVars i ↔ autFn pIdx v ∈ D''.rightVars ⟨i.val, by omega⟩ := by
    intro v i
    change v ∈ (D''.rightVars ⟨i.val, by omega⟩).map (autPerm pIdx).toEmbedding ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa [autPerm, autFn_invol] using ha
    · intro h; exact ⟨autFn pIdx v, h, autFn_invol pIdx v⟩
  have hno0_1 : ∀ k : Fin 16, (0 : V) ∉ rows9 k →
      sideL D1 (rows9 k) ⟨a0.val, by omega⟩ = false ∧ sideR D1 (rows9 k) ⟨a0.val, by omega⟩ = true := by
    intro k hk
    obtain ⟨k', hk'⟩ := autPerm_rows9 pIdx k
    have hk0' : (0 : V) ∉ rows9 k' := by
      intro h0m; apply hk; rw [← hk', ← autPerm_zero pIdx]; exact Finset.mem_map_of_mem _ h0m
    rw [← hk']
    exact ⟨(permuteVars_sideL D'' (autPerm pIdx) (rows9 k') ⟨a0.val, by omega⟩).trans (hno0'' k' hk0').1,
           (permuteVars_sideR D'' (autPerm pIdx) (rows9 k') ⟨a0.val, by omega⟩).trans (hno0'' k' hk0').2⟩
  let ε : Fin D1.size → Bool := fun i => fl.getD (σ' ⟨i.val, by omega⟩).val false
  let D2 := swapSide D1 ε
  have hsz2 : D2.size = 5 := hsz1
  have hW2 : D2.WellFormed := swapSide_wf D1 ε hW1
  have hsep2 : Separates D2 := fun k => by simpa [D2, swapSide_eval] using hsep1 k
  have hε_a0 : ε ⟨a0.val, by omega⟩ = false := by
    dsimp only [ε]; rw [hσ'_a0]; exact hfl0
  have hno0_2 : ∀ k : Fin 16, (0 : V) ∉ rows9 k →
      sideL D2 (rows9 k) ⟨a0.val, by omega⟩ = false ∧ sideR D2 (rows9 k) ⟨a0.val, by omega⟩ = true := by
    intro k hk
    have hgv : ∀ j : Fin D1.size, D2.gateVal (rows9 k) j = D1.gateVal (rows9 k) j :=
      fun j => swapSide_gateVal D1 ε (rows9 k) D1.size j j.isLt
    have hL : sideL D2 (rows9 k) ⟨a0.val, by omega⟩ = sideL D1 (rows9 k) ⟨a0.val, by omega⟩ := by
      unfold sideL
      have h1 : D2.leftVars ⟨a0.val, by omega⟩ = D1.leftVars ⟨a0.val, by omega⟩ := by
        change cond (ε ⟨a0.val, by omega⟩) _ _ = _; rw [hε_a0]; rfl
      have h2 : D2.leftGates ⟨a0.val, by omega⟩ = D1.leftGates ⟨a0.val, by omega⟩ := by
        change cond (ε ⟨a0.val, by omega⟩) _ _ = _; rw [hε_a0]; rfl
      rw [h1, h2]; exact sideTrue_congr _ _ _ _ _ _ (fun j _ => hgv j)
    have hR : sideR D2 (rows9 k) ⟨a0.val, by omega⟩ = sideR D1 (rows9 k) ⟨a0.val, by omega⟩ := by
      unfold sideR
      have h1 : D2.rightVars ⟨a0.val, by omega⟩ = D1.rightVars ⟨a0.val, by omega⟩ := by
        change cond (ε ⟨a0.val, by omega⟩) _ _ = _; rw [hε_a0]; rfl
      have h2 : D2.rightGates ⟨a0.val, by omega⟩ = D1.rightGates ⟨a0.val, by omega⟩ := by
        change cond (ε ⟨a0.val, by omega⟩) _ _ = _; rw [hε_a0]; rfl
      rw [h1, h2]; exact sideTrue_congr _ _ _ _ _ _ (fun j _ => hgv j)
    rw [hL, hR]; exact hno0_1 k hk
  let r := reps13 oIdx
  have hD2_L : ∀ (v : V) (g : Fin 5),
      decide (v ∈ D2.leftVars ⟨(σ'.symm g).val, by omega⟩) =
        (if v.val == 0 then g.val == 0 else (r.getD (v.val - 1) 0).testBit (2 * g.val)) := by
    intro v g
    have hεg : ε ⟨(σ'.symm g).val, by omega⟩ = fl.getD g.val false := by
      dsimp only [ε]; rw [Equiv.apply_symm_apply]
    change decide (v ∈ cond (ε ⟨(σ'.symm g).val, by omega⟩)
      (D1.rightVars ⟨(σ'.symm g).val, by omega⟩) (D1.leftVars ⟨(σ'.symm g).val, by omega⟩)) = _
    rw [hεg]
    by_cases hv0 : v.val = 0
    · have hv : v = 0 := Fin.ext hv0
      subst hv
      simp only [Fin.val_zero, beq_self_eq_true, ↓reduceIte]
      have ha0_eq : σ'.symm g = a0 ↔ g.val = 0 := by
        constructor
        · intro h; have : g = σ' a0 := (Equiv.symm_apply_eq σ').mp h; rw [this, hσ'_a0]; rfl
        · intro h; have hg0 : g = 0 := Fin.ext h; rw [hg0, ← hσ'_a0, Equiv.symm_apply_apply]
      by_cases hg : g.val = 0
      · have hg0 : g = 0 := Fin.ext hg
        subst hg0
        simp only [Fin.val_zero, beq_self_eq_true]
        rw [decide_eq_true_eq, hfl0, Bool.cond_false]
        have hsyma : σ'.symm 0 = a0 := ha0_eq.mpr rfl
        have hidx : (⟨(σ'.symm 0).val, by omega⟩ : Fin D''.size) = ⟨a0.val, by omega⟩ :=
          Fin.ext (congrArg (Fin.val : Fin 5 → Nat) hsyma)
        rw [hD1_memL 0 ⟨(σ'.symm 0).val, by omega⟩, hidx, haut0, hLa0'']; exact Finset.mem_singleton_self 0
      · have hne : σ'.symm g ≠ a0 := fun h => hg (ha0_eq.mp h)
        rw [beq_false_of_ne hg, decide_eq_false_iff_not]
        cases fl.getD g.val false
        · rw [Bool.cond_false, hD1_memL 0 ⟨(σ'.symm g).val, by omega⟩, haut0]; exact (h0oth'' _ hne).1
        · rw [Bool.cond_true, hD1_memR 0 ⟨(σ'.symm g).val, by omega⟩, haut0]; exact (h0oth'' _ hne).2
    · have hbeq : (v.val == 0) = false := beq_false_of_ne hv0
      rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hov0 : (autFn pIdx v).val ≠ 0 := by
        intro h
        have hv0' : autFn pIdx v = 0 := Fin.ext h
        have : v = 0 := by
          have := congrArg (autFn pIdx) hv0'
          rw [autFn_invol] at this; exact this.trans haut0
        exact hv0 (by rw [this]; rfl)
      have hbit := (hw_bit v hv0 g).1
      have hspec := hc_spec (autFn pIdx v) hov0 (gpf g)
      have hidx : (⟨(σ'.symm g).val, by omega⟩ : Fin D''.size) = ⟨(σ.symm (gpf g)).val, by omega⟩ :=
        Fin.ext (congrArg (Fin.val : Fin 5 → Nat) (hσ'_symm g))
      rw [← hbit]
      cases hfl : fl.getD g.val false
      · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
        rw [Bool.eq_iff_iff, decide_eq_true_eq, hD1_memL v ⟨(σ'.symm g).val, by omega⟩, hidx]; exact hspec.1
      · simp only [Bool.cond_true, ↓reduceIte]
        rw [Bool.eq_iff_iff, decide_eq_true_eq, hD1_memR v ⟨(σ'.symm g).val, by omega⟩, hidx]; exact hspec.2
  have hD2_R : ∀ (v : V) (g : Fin 5),
      decide (v ∈ D2.rightVars ⟨(σ'.symm g).val, by omega⟩) =
        (if v.val == 0 then false else (r.getD (v.val - 1) 0).testBit (2 * g.val + 1)) := by
    intro v g
    have hεg : ε ⟨(σ'.symm g).val, by omega⟩ = fl.getD g.val false := by
      dsimp only [ε]; rw [Equiv.apply_symm_apply]
    change decide (v ∈ cond (ε ⟨(σ'.symm g).val, by omega⟩)
      (D1.leftVars ⟨(σ'.symm g).val, by omega⟩) (D1.rightVars ⟨(σ'.symm g).val, by omega⟩)) = _
    rw [hεg]
    by_cases hv0 : v.val = 0
    · have hv : v = 0 := Fin.ext hv0
      subst hv
      simp only [Fin.val_zero, beq_self_eq_true, ↓reduceIte, decide_eq_false_iff_not]
      by_cases hg : g = 0
      · subst hg; simp only [Fin.val_zero]
        rw [hfl0, Bool.cond_false]
        have hsyma : σ'.symm 0 = a0 := by rw [← hσ'_a0, Equiv.symm_apply_apply]
        have hidx : (⟨(σ'.symm 0).val, by omega⟩ : Fin D''.size) = ⟨a0.val, by omega⟩ :=
          Fin.ext (congrArg (Fin.val : Fin 5 → Nat) hsyma)
        rw [hD1_memR 0 ⟨(σ'.symm 0).val, by omega⟩, hidx, haut0]; exact h0R''
      · have hne : σ'.symm g ≠ a0 := fun h => hg (by
          have : g = σ' a0 := (Equiv.symm_apply_eq σ').mp h; rwa [hσ'_a0] at this)
        cases fl.getD g.val false
        · rw [Bool.cond_false, hD1_memR 0 ⟨(σ'.symm g).val, by omega⟩, haut0]; exact (h0oth'' _ hne).2
        · rw [Bool.cond_true, hD1_memL 0 ⟨(σ'.symm g).val, by omega⟩, haut0]; exact (h0oth'' _ hne).1
    · have hbeq : (v.val == 0) = false := beq_false_of_ne hv0
      rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hov0 : (autFn pIdx v).val ≠ 0 := by
        intro h
        have hv0' : autFn pIdx v = 0 := Fin.ext h
        have : v = 0 := by
          have := congrArg (autFn pIdx) hv0'
          rw [autFn_invol] at this; exact this.trans haut0
        exact hv0 (by rw [this]; rfl)
      have hbit := (hw_bit v hv0 g).2
      have hspec := hc_spec (autFn pIdx v) hov0 (gpf g)
      have hidx : (⟨(σ'.symm g).val, by omega⟩ : Fin D''.size) = ⟨(σ.symm (gpf g)).val, by omega⟩ :=
        Fin.ext (congrArg (Fin.val : Fin 5 → Nat) (hσ'_symm g))
      rw [← hbit]
      cases hfl : fl.getD g.val false
      · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
        rw [Bool.eq_iff_iff, decide_eq_true_eq, hD1_memR v ⟨(σ'.symm g).val, by omega⟩, hidx]; exact hspec.2
      · simp only [Bool.cond_true, ↓reduceIte]
        rw [Bool.eq_iff_iff, decide_eq_true_eq, hD1_memL v ⟨(σ'.symm g).val, by omega⟩, hidx]; exact hspec.1
  have htrue : searchTopo (orbitG oIdx) (orbitV oIdx 0) (orbitV oIdx 1) (orbitV oIdx 2)
      (orbitV oIdx 3) (orbitV oIdx 4) (orbitV oIdx 5) (orbitV oIdx 6) (orbitV oIdx 7) (orbitV oIdx 8)
      5 0 ⟨false,false,false,false,false⟩ [] [] initU16 = true := by
    apply searchTopo_of_circuit D2 hsz2 hW2 hsep2 σ' a0 hσ'_a0 hno0_2 (orbitG oIdx) (orbitV oIdx)
    · intro i
      have hgi_mem : gInfoOf r (σ' i) ∈ orbitG oIdx := by
        rw [← (orbit_lit_eq oIdx).1]
        exact List.mem_map_of_mem (List.mem_finRange (σ' i))
      have hsym_i : (⟨(σ'.symm (σ' i)).val, by omega⟩ : Fin D2.size) = ⟨i.val, by omega⟩ :=
        Fin.ext (by simp [Equiv.symm_apply_apply])
      refine ⟨gInfoOf r (σ' i), hgi_mem, rfl, ?_, ?_, ?_, ?_⟩
      · intro v; dsimp only [gInfoOf]; rw [B9.get_ofFn, ← hD2_L v (σ' i), hsym_i]
      · intro v; dsimp only [gInfoOf]; rw [B9.get_ofFn, ← hD2_R v (σ' i), hsym_i]
      · intro k; dsimp only [gInfoOf]; rw [B16.get_ofFn, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨v, _, hv⟩
          rw [Bool.and_eq_true, B9.get_ofFn, ← hD2_L v (σ' i), hsym_i, decide_eq_true_eq] at hv
          exact ⟨v, (rows9_bit k v).mpr hv.1, hv.2⟩
        · rintro ⟨v, hvk, hvL⟩
          refine ⟨v, List.mem_finRange v, ?_⟩
          rw [Bool.and_eq_true, B9.get_ofFn, ← hD2_L v (σ' i), hsym_i, decide_eq_true_eq]
          exact ⟨(rows9_bit k v).mp hvk, hvL⟩
      · intro k; dsimp only [gInfoOf]; rw [B16.get_ofFn, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨v, _, hv⟩
          rw [Bool.and_eq_true, B9.get_ofFn, ← hD2_R v (σ' i), hsym_i, decide_eq_true_eq] at hv
          exact ⟨v, (rows9_bit k v).mpr hv.1, hv.2⟩
        · rintro ⟨v, hvk, hvR⟩
          refine ⟨v, List.mem_finRange v, ?_⟩
          rw [Bool.and_eq_true, B9.get_ofFn, ← hD2_R v (σ' i), hsym_i, decide_eq_true_eq]
          exact ⟨(rows9_bit k v).mp hvk, hvR⟩
    · intro v g
      rw [← (orbit_lit_eq oIdx).2 v]
      dsimp only [vB5Of]; rw [B5.get_ofFn]
      have hL := hD2_L v g
      have hR := hD2_R v g
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      by_cases hv0 : v.val = 0
      · have hbeq : (v.val == 0) = true := beq_iff_eq.mpr hv0
        simp only [hbeq, ↓reduceIte] at hL hR ⊢
        rw [← hL, decide_eq_true_eq]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | h)
          · exact h
          · rw [decide_eq_true h] at hR; cases hR
      · have hbeq : (v.val == 0) = false := beq_false_of_ne hv0
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hL hR ⊢
        rw [Bool.or_eq_true, ← hL, ← hR, decide_eq_true_eq, decide_eq_true_eq]
  rw [all_orbits_false oIdx] at htrue
  cases htrue

lemma g9Adj_iff (G : SimpleGraph (Fin 9))
    (hG : G = SimpleGraph.fromRel (fun a b : Fin 9 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)] : List (ℕ × ℕ))))
    (a b : Fin 9) : G.Adj a b ↔ g9Adj a b = true := by
  subst hG
  simp [SimpleGraph.fromRel_adj, g9Adj, E9]

end PEqualNP.Outside.L_meta_908_aux

theorem PEqualNP.Outside.L_meta_908 :
    ∀ G : SimpleGraph (Fin 9), G = SimpleGraph.fromRel (fun a b : Fin 9 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)] : List (ℕ × ℕ))) →
      ∀ C : PEqualNP.AndCount.AndCountCircuit 9, C.WellFormed →
        (∀ I : Finset (Fin 9), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 9, w ∉ I → ∃ a ∈ I, G.Adj a w) →
          C.eval I = false ∧ ∀ w : Fin 9, w ∉ I → C.eval (insert w I) = true) →
        6 ≤ C.size := by
  open PEqualNP.Outside.L_meta_908_aux in
  intro G hG C hW hMIS
  by_contra hlt
  have hle5 : C.size ≤ 5 := by omega
  have hsepC : Separates C := by
    intro k
    have hg := rows9_good k
    exact hMIS (rows9 k)
      (fun a ha c hc hadj => by
        have := (g9Adj_iff G hG a c).mp hadj
        rw [hg.1 a ha c hc] at this; cases this)
      (fun w hw => by
        obtain ⟨a, ha, hadj⟩ := hg.2 w hw
        exact ⟨a, ha, (g9Adj_iff G hG a w).mpr hadj⟩)
  let C1 := stripCircuit C
  have hW1 : C1.WellFormed := strip_wf C hW
  have hD1 : ∀ i, Disjoint (C1.leftVars i) (C1.rightVars i) := strip_disjoint C
  have hsep1 : Separates C1 := fun k => ⟨(strip_eval_eq C (rows9 k)).trans (hsepC k).1,
    fun w hw => (strip_eval_eq C (insert w (rows9 k))).trans ((hsepC k).2 w hw)⟩
  let D := pad5 C1 hle5
  have hW2 : D.WellFormed := pad5_wf C1 hle5 hW1
  have hD2 : ∀ i, Disjoint (D.leftVars i) (D.rightVars i) := pad5_disjoint C1 hle5 hD1
  have hsep2 : Separates D := fun k => ⟨(pad5_eval C1 hle5 (rows9 k)).trans (hsep1 k).1,
    fun w hw => (pad5_eval C1 hle5 (insert w (rows9 k))).trans ((hsep1 k).2 w hw)⟩
  obtain ⟨a0, D', hsz', hW', hD', hsep', hLa0, h0R, h0oth, hno0, h12⟩ :=
    exists_a0_with_sigma1 D hW2 rfl hD2 hsep2
  obtain ⟨D'', hsz'', σ, hW'', _, hsep'', hσ_a0, hLa0'', h0R'', h0oth'', hno0'', p, hp, c, hc, _, hc_spec⟩ :=
    exists_canon_in_runBranch D' a0 hsz' hW' hD' hsep' hLa0 h0R h0oth hno0 h12
  exact reduce_class62_to_false D'' a0 hsz'' hW'' hsep'' σ hσ_a0 hLa0'' h0R'' h0oth'' hno0''
    c (runBranch_mem_classes62 p hp c hc) hc_spec
