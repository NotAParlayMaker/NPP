import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- The gate recursion and union certificate are adapted from L-meta-634.
theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

theorem gateVal_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
  rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]

theorem gateVal_iff_wf {n : ℕ} (C : AndCountCircuit n) (hC : C.WellFormed) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, C.gateVal U j = true)) := by
  rw [gateVal_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases h2 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hC i).1 j hj, hv⟩
    · rcases h2 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hC i).2 j hj, hv⟩

theorem eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

theorem fuel_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U') :
    ∀ d : ℕ, ∀ i : Fin C.size, gateValFuel C U d i = true → gateValFuel C U' d i = true := by
  intro d
  induction d with
  | zero => intro i h; exact absurd h (by simp [gateValFuel])
  | succ d ih =>
    intro i h
    have h' : (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d)) = true := h
    show (sideTrue U' (C.leftVars i) (C.leftGates i) i (gateValFuel C U' d) &&
        sideTrue U' (C.rightVars i) (C.rightGates i) i (gateValFuel C U' d)) = true
    rw [Bool.and_eq_true] at h' ⊢
    exact ⟨sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.1,
      sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.2⟩

theorem gateVal_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal U' i = true :=
  fuel_mono C U U' hU C.size i h

theorem eval_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (h : C.eval U = true) : C.eval U' = true := by
  rw [eval_iff] at h ⊢
  rcases h with ⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩
  · exact Or.inl ⟨v, hv, hU hvU⟩
  · exact Or.inr ⟨j, hj, gateVal_mono C U U' hU j hg⟩

def sv {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) (s : Bool) : Bool :=
  sideTrue X (cond s (C.rightVars i) (C.leftVars i)) (cond s (C.rightGates i) (C.leftGates i)) i
    (C.gateVal X)

theorem gate_false_iff {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal X i = false ↔ (sv C X i false = false ∨ sv C X i true = false) := by
  rw [gateVal_rec, Bool.and_eq_false_iff]
  rfl

theorem sv_merge {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n)) (i : Fin C.size)
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
      rw [← Bool.not_eq_true]
      exact fun hh => hX (Or.inr ⟨j, hj, hji, hh⟩)
    have h2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hY (Or.inr ⟨j, hj, hji, hh⟩)
    rw [ih j hji h1 h2] at hv
    exact Bool.noConfusion hv

private def choice {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n))
    (i : Fin C.size) : Bool := sv C X i false

private theorem choice_ok {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n))
    (i : Fin C.size) (h : C.gateVal X i = false) : sv C X i (choice C X i) = false := by
  rw [gate_false_iff] at h
  unfold choice
  cases hb : sv C X i false with
  | false => exact hb
  | true =>
    rcases h with h | h
    · rw [hb] at h
      exact Bool.noConfusion h
    · exact h

theorem merge_gate {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n))
    (hc : ∀ i, choice C X i = choice C Y i) :
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
          C.gateVal (X ∪ Y) j = false := by
        intro j hji
        apply ih
        have : j.val < i.val := hji
        omega
      have c1 := choice_ok C X i h1
      have c2 := choice_ok C Y i h2
      rw [← hc i] at c2
      have hm := sv_merge C X Y i _ c1 c2 ih'
      rw [gate_false_iff]
      cases hb : choice C X i with
      | false => rw [hb] at hm; exact Or.inl hm
      | true => rw [hb] at hm; exact Or.inr hm
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

theorem merge_eval {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n))
    (hc : ∀ i, choice C X i = choice C Y i)
    (h1 : C.eval X = false) (h2 : C.eval Y = false) : C.eval (X ∪ Y) = false := by
  rw [← Bool.not_eq_true, eval_iff] at h1 h2 ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact h1 (Or.inl ⟨x, hx, h⟩)
    · exact h2 (Or.inl ⟨x, hx, h⟩)
  · have g1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h1 (Or.inr ⟨j, hj, hh⟩)
    have g2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h2 (Or.inr ⟨j, hj, hh⟩)
    rw [merge_gate C X Y hc j g1 g2] at hv
    exact Bool.noConfusion hv

private def IsMaximal {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ (∀ w, w ∉ I → ∃ a ∈ I, G.Adj a w)

private def Tests {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) : Prop :=
  ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
    (∀ w, w ∉ I → ∃ a ∈ I, G.Adj a w) →
    C.eval I = false ∧ ∀ w, w ∉ I → C.eval (insert w I) = true

private theorem count_maximal {n m : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (tests : Tests G C) (M : Fin m → Finset (Fin n))
    (maximal : ∀ a, IsMaximal G (M a)) (inj : Function.Injective M) : m ≤ 2 ^ C.size := by
  have opposite {X Y : Finset (Fin n)} (hx : IsMaximal G X) (h : ¬ Y ⊆ X) :
      C.eval (X ∪ Y) = true := by
    obtain ⟨w, hwY, hwX⟩ := Finset.not_subset.1 h
    apply eval_mono C (insert w X) (X ∪ Y) _ ((tests X hx.1 hx.2).2 w hwX)
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact Finset.mem_union_right _ hwY
    · exact Finset.mem_union_left _ hv
  let encode (a : Fin m) : Fin C.size → Bool := choice C (M a)
  have encode_inj : Function.Injective encode := by
    intro a b hab
    by_contra hne
    have hsets : M a ≠ M b := fun h => hne (inj h)
    have hfalse := merge_eval C (M a) (M b) (congrFun hab)
      (tests _ (maximal a).1 (maximal a).2).1 (tests _ (maximal b).1 (maximal b).2).1
    have htrue : C.eval (M a ∪ M b) = true := by
      by_cases hs : M b ⊆ M a
      · rw [Finset.union_comm]
        exact opposite (maximal b) (fun hh => hsets (Finset.Subset.antisymm hh hs))
      · exact opposite (maximal a) hs
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  have hc := Fintype.card_le_of_injective encode encode_inj
  simpa [Fintype.card_fun] using hc

private abbrev R6 (a b : Fin 6) : Prop :=
  (a.val,b.val) ∈ ([(0,1),(1,2),(0,2),(3,4),(4,5),(3,5)] : List (ℕ × ℕ))
private abbrev R5 (a b : Fin 5) : Prop :=
  (a.val,b.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0)] : List (ℕ × ℕ))
private abbrev R7 (a b : Fin 7) : Prop :=
  (a.val,b.val) ∈ ([(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6),
    (4,6),(4,0),(5,0),(5,1),(6,1),(6,2)] : List (ℕ × ℕ))

private def G6 := SimpleGraph.fromRel R6
private def G5 := SimpleGraph.fromRel R5
private def G7 := SimpleGraph.fromRel R7

private def decAdj {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    DecidableRel (SimpleGraph.fromRel R).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (R a b ∨ R b a)))

private def decMax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)) :
    Decidable (IsMaximal G I) := by unfold IsMaximal; infer_instance

private def C6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private def C5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  rightVars := ![{1, 4}, {1, 3}, {4}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private def C7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
  rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
  leftGates := ![∅, {0}, {1}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1, 2}

private def M6 : Fin 9 → Finset (Fin 6) :=
  ![{0,3},{0,4},{0,5},{1,3},{1,4},{1,5},{2,3},{2,4},{2,5}]
private def M5 : Fin 5 → Finset (Fin 5) := ![{0,2},{0,3},{1,3},{1,4},{2,4}]
private def M7 : Fin 7 → Finset (Fin 7) := ![{0,1},{1,2},{2,3},{3,4},{4,5},{5,6},{6,0}]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem upper6 : C6.WellFormed ∧ C6.size ≤ 4 ∧ Tests G6 C6 := by
  letI : DecidableRel G6.Adj := decAdj R6
  letI : ∀ I, Decidable (IsMaximal G6 I) := decMax G6
  refine ⟨by unfold WellFormed; decide, by decide, ?_⟩
  unfold Tests
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem lower6 (C : AndCountCircuit 6) (h : Tests G6 C) : 4 ≤ C.size := by
  letI : DecidableRel G6.Adj := decAdj R6
  letI : ∀ I, Decidable (IsMaximal G6 I) := decMax G6
  have count := count_maximal G6 C h M6 (by decide) (by decide)
  by_contra hle
  have := le_trans count (Nat.pow_le_pow_right (by decide : 0 < 2) (show C.size ≤ 3 by omega))
  norm_num at this

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem upper5 : C5.WellFormed ∧ C5.size ≤ 3 ∧ Tests G5 C5 := by
  letI : DecidableRel G5.Adj := decAdj R5
  letI : ∀ I, Decidable (IsMaximal G5 I) := decMax G5
  refine ⟨by unfold WellFormed; decide, by decide, ?_⟩
  unfold Tests
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem lower5 (C : AndCountCircuit 5) (h : Tests G5 C) : 3 ≤ C.size := by
  letI : DecidableRel G5.Adj := decAdj R5
  letI : ∀ I, Decidable (IsMaximal G5 I) := decMax G5
  have count := count_maximal G5 C h M5 (by decide) (by decide)
  by_contra hle
  have := le_trans count (Nat.pow_le_pow_right (by decide : 0 < 2) (show C.size ≤ 2 by omega))
  norm_num at this

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem upper7 : C7.WellFormed ∧ C7.size ≤ 3 ∧ Tests G7 C7 := by
  letI : DecidableRel G7.Adj := decAdj R7
  letI : ∀ I, Decidable (IsMaximal G7 I) := decMax G7
  refine ⟨by unfold WellFormed; decide, by decide, ?_⟩
  unfold Tests
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem lower7 (C : AndCountCircuit 7) (h : Tests G7 C) : 3 ≤ C.size := by
  letI : DecidableRel G7.Adj := decAdj R7
  letI : ∀ I, Decidable (IsMaximal G7 I) := decMax G7
  have count := count_maximal G7 C h M7 (by decide) (by decide)
  by_contra hle
  have := le_trans count (Nat.pow_le_pow_right (by decide : 0 < 2) (show C.size ≤ 2 by omega))
  norm_num at this

private theorem result :
    (∀ G : SimpleGraph (Fin 6), G = G6 →
      (∃ C, C.WellFormed ∧ C.size ≤ 4 ∧ Tests G C) ∧
        ∀ C, C.WellFormed → Tests G C → 4 ≤ C.size) ∧
    (∀ G : SimpleGraph (Fin 5), G = G5 →
      (∃ C, C.WellFormed ∧ C.size ≤ 3 ∧ Tests G C) ∧
        ∀ C, C.WellFormed → Tests G C → 3 ≤ C.size) ∧
    (∀ G : SimpleGraph (Fin 7), G = G7 →
      (∃ C, C.WellFormed ∧ C.size ≤ 3 ∧ Tests G C) ∧
        ∀ C, C.WellFormed → Tests G C → 3 ≤ C.size) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ rfl
    exact ⟨⟨C6, upper6⟩, fun C _ => lower6 C⟩
  · rintro _ rfl
    exact ⟨⟨C5, upper5⟩, fun C _ => lower5 C⟩
  · rintro _ rfl
    exact ⟨⟨C7, upper7⟩, fun C _ => lower7 C⟩

end PEqualNP.Outside.L_meta_906

theorem PEqualNP.Outside.L_meta_906 : (∀ G : SimpleGraph (Fin 6), G = SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed ∧ C.size ≤ 4 ∧
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed →
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true) →
    4 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 5), G = SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed →
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 7), G = SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed →
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) :=
  PEqualNP.Outside.L_meta_906.result
