import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- The evaluation lemmas adapt the AND-count evaluation facts in L-meta-634.

private theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
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

private theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

private theorem sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

private theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
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

private theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

private theorem eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

private theorem fuel_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U') :
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

private theorem gateVal_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal U' i = true :=
  fuel_mono C U U' hU C.size i h

private theorem eval_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (h : C.eval U = true) : C.eval U' = true := by
  rw [eval_iff] at h ⊢
  rcases h with ⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩
  · exact Or.inl ⟨v, hv, hU hvU⟩
  · exact Or.inr ⟨j, hj, gateVal_mono C U U' hU j hg⟩

def MaxIndependent {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧
    (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w)

def Boundary {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) : Prop :=
  ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
    (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
    C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true

-- A false gate has a false side. Its signature chooses the right side when the left is true.
private def signature {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U)

private theorem merge_side {n : ℕ} (C : AndCountCircuit n) (X Y B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size)
    (hx : sideTrue X B F i (C.gateVal X) = false)
    (hy : sideTrue Y B F i (C.gateVal Y) = false)
    (early : ∀ j : Fin C.size, j < i → C.gateVal X j = false →
      C.gateVal Y j = false → C.gateVal (X ∪ Y) j = false) :
    sideTrue (X ∪ Y) B F i (C.gateVal (X ∪ Y)) = false := by
  rw [← Bool.not_eq_true, sideTrue_iff] at hx hy ⊢
  rintro (⟨v, hv, hvxy⟩ | ⟨j, hj, hji, hval⟩)
  · rcases Finset.mem_union.mp hvxy with h | h
    · exact hx (.inl ⟨v, hv, h⟩)
    · exact hy (.inl ⟨v, hv, h⟩)
  · have hjx : C.gateVal X j = false := Bool.eq_false_iff.mpr fun h => hx (.inr ⟨j, hj, hji, h⟩)
    have hjy : C.gateVal Y j = false := Bool.eq_false_iff.mpr fun h => hy (.inr ⟨j, hj, hji, h⟩)
    rw [early j hji hjx hjy] at hval
    cases hval

private theorem merge_false {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n))
    (hsame : signature C X = signature C Y) (hx : C.eval X = false) (hy : C.eval Y = false) :
    C.eval (X ∪ Y) = false := by
  have gates (k : ℕ) : ∀ i : Fin C.size, i.val = k →
      C.gateVal X i = false → C.gateVal Y i = false → C.gateVal (X ∪ Y) i = false := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi hix hiy
      have early (j : Fin C.size) (hji : j < i) := ih j.val (show j.val < k by rw [← hi]; exact hji) j rfl
      have he := congrFun hsame i
      unfold signature at he
      generalize hl : sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X) = b
      cases b with
      | false =>
        have hm := merge_side C X Y (C.leftVars i) (C.leftGates i) i hl (he.symm.trans hl) early
        rw [gateVal_rec, hm, Bool.false_and]
      | true =>
        rw [gateVal_rec, hl, Bool.true_and] at hix
        rw [gateVal_rec, he.symm.trans hl, Bool.true_and] at hiy
        have hm := merge_side C X Y (C.rightVars i) (C.rightGates i) i hix hiy early
        rw [gateVal_rec, hm, Bool.and_false]
  rw [← Bool.not_eq_true, eval_iff] at hx hy ⊢
  rintro (⟨v, hv, hvxy⟩ | ⟨j, hj, hval⟩)
  · rcases Finset.mem_union.mp hvxy with h | h
    · exact hx (.inl ⟨v, hv, h⟩)
    · exact hy (.inl ⟨v, hv, h⟩)
  · have hjx : C.gateVal X j = false := Bool.eq_false_iff.mpr fun h => hx (.inr ⟨j, hj, h⟩)
    have hjy : C.gateVal Y j = false := Bool.eq_false_iff.mpr fun h => hy (.inr ⟨j, hj, h⟩)
    rw [gates j.val j rfl hjx hjy] at hval
    cases hval

theorem boundary_lower {n m : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (h : Boundary G C) (M : Fin m → Finset (Fin n)) (hinj : Function.Injective M)
    (hm : ∀ i, MaxIndependent G (M i)) : m ≤ 2 ^ C.size := by
  classical
  let f : Fin m → (Fin C.size → Bool) := fun a => signature C (M a)
  have inj : Function.Injective f := by
    intro a b he
    by_contra hne
    have hbna : ¬ M b ⊆ M a := by
      intro hba
      apply hne
      apply hinj
      refine Finset.Subset.antisymm ?_ hba
      intro u hu
      by_contra hnot
      obtain ⟨v, hv, hadj⟩ := (hm b).2 u hnot
      exact (hm a).1 v (hba hv) u hu hadj
    obtain ⟨u, hub, hua⟩ := Finset.not_subset.mp hbna
    have accepts : C.eval (M a ∪ M b) = true :=
      eval_mono C _ _ (Finset.insert_subset (Finset.mem_union_right _ hub) Finset.subset_union_left)
        ((h (M a) (hm a).1 (hm a).2).2 u hua)
    have rejects := merge_false C (M a) (M b) he
      (h (M a) (hm a).1 (hm a).2).1 (h (M b) (hm b).1 (hm b).2).1
    rw [rejects] at accepts
    cases accepts
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective f inj

end PEqualNP.Outside.L_meta_906

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount

abbrev edges6 : List (ℕ × ℕ) := [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)]

abbrev graph6 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun a b : Fin 6 => (a.val,b.val) ∈ edges6

private def witness6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  leftGates := fun _ => ∅
  rightVars := ![{1,2}, {2}, {4,5}, {5}]
  rightGates := fun _ => ∅
  outVars := ∅
  outGates := Finset.univ

set_option maxRecDepth 8192 in
theorem upper6 :
    ∃ C : AndCountCircuit 6, C.WellFormed ∧ C.size ≤ 4 ∧
      ∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ b ∈ I, ¬ graph6.Adj a b) →
        (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, graph6.Adj a w) →
        C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true := by
  refine ⟨witness6, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide
  · let _ : DecidableRel graph6.Adj := fun a b =>
      inferInstanceAs (Decidable (a ≠ b ∧ ((a.val,b.val) ∈ edges6 ∨ (b.val,a.val) ∈ edges6)))
    decide

abbrev edges5 : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

abbrev graph5 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun a b : Fin 5 => (a.val,b.val) ∈ edges5

private def witness5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  leftGates := fun _ => ∅
  rightVars := ![{1,4}, {1,3}, {4}]
  rightGates := fun _ => ∅
  outVars := ∅
  outGates := Finset.univ

set_option maxRecDepth 8192 in
theorem upper5 :
    ∃ C : AndCountCircuit 5, C.WellFormed ∧ C.size ≤ 3 ∧
      ∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ b ∈ I, ¬ graph5.Adj a b) →
        (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, graph5.Adj a w) →
        C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true := by
  refine ⟨witness5, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide
  · let _ : DecidableRel graph5.Adj := fun a b =>
      inferInstanceAs (Decidable (a ≠ b ∧ ((a.val,b.val) ∈ edges5 ∨ (b.val,a.val) ∈ edges5)))
    decide

abbrev edges7 : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)]

abbrev graph7 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun a b : Fin 7 => (a.val,b.val) ∈ edges7

private def witness7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0,4}, {0,1}, {1,2,3}]
  leftGates := ![∅, {0}, {1}]
  rightVars := ![{2,6}, {3,4,5}, {5,6}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1,2}

set_option maxRecDepth 8192 in
theorem upper7 :
    ∃ C : AndCountCircuit 7, C.WellFormed ∧ C.size ≤ 3 ∧
      ∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ b ∈ I, ¬ graph7.Adj a b) →
        (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, graph7.Adj a w) →
        C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true := by
  refine ⟨witness7, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide
  · let _ : DecidableRel graph7.Adj := fun a b =>
      inferInstanceAs (Decidable (a ≠ b ∧ ((a.val,b.val) ∈ edges7 ∨ (b.val,a.val) ∈ edges7)))
    decide

end PEqualNP.Outside.L_meta_906

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount

private def maximalFamily6 : Fin 9 → Finset (Fin 6) := ![{0, 3}, {0, 4}, {0, 5}, {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 4}, {2, 5}]

set_option maxRecDepth 8192 in
lemma lower6 (C : AndCountCircuit 6) (_ : C.WellFormed) (h : Boundary graph6 C) :
    4 ≤ C.size := by
  let _ : DecidableRel graph6.Adj := fun a b =>
    inferInstanceAs (Decidable (a ≠ b ∧ ((a.val,b.val) ∈ edges6 ∨ (b.val,a.val) ∈ edges6)))
  have hinj : Function.Injective maximalFamily6 := by
    change ∀ i j : Fin 9, maximalFamily6 i = maximalFamily6 j → i = j
    decide
  have hmax : ∀ i, MaxIndependent graph6 (maximalFamily6 i) := by
    unfold MaxIndependent
    decide
  have hcount := boundary_lower graph6 C h maximalFamily6 hinj hmax
  by_contra! hlt
  have hb : C.size ≤ 3 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hb
  omega

private def maximalFamily5 : Fin 5 → Finset (Fin 5) := ![{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}]

set_option maxRecDepth 8192 in
lemma lower5 (C : AndCountCircuit 5) (_ : C.WellFormed) (h : Boundary graph5 C) :
    3 ≤ C.size := by
  let _ : DecidableRel graph5.Adj := fun a b =>
    inferInstanceAs (Decidable (a ≠ b ∧ ((a.val,b.val) ∈ edges5 ∨ (b.val,a.val) ∈ edges5)))
  have hinj : Function.Injective maximalFamily5 := by
    change ∀ i j : Fin 5, maximalFamily5 i = maximalFamily5 j → i = j
    decide
  have hmax : ∀ i, MaxIndependent graph5 (maximalFamily5 i) := by
    unfold MaxIndependent
    decide
  have hcount := boundary_lower graph5 C h maximalFamily5 hinj hmax
  by_contra! hlt
  have hb : C.size ≤ 2 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hb
  omega

private def maximalFamily7 : Fin 7 → Finset (Fin 7) := ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {0, 6}]

set_option maxRecDepth 8192 in
lemma lower7 (C : AndCountCircuit 7) (_ : C.WellFormed) (h : Boundary graph7 C) :
    3 ≤ C.size := by
  let _ : DecidableRel graph7.Adj := fun a b =>
    inferInstanceAs (Decidable (a ≠ b ∧ ((a.val,b.val) ∈ edges7 ∨ (b.val,a.val) ∈ edges7)))
  have hinj : Function.Injective maximalFamily7 := by
    change ∀ i j : Fin 7, maximalFamily7 i = maximalFamily7 j → i = j
    decide
  have hmax : ∀ i, MaxIndependent graph7 (maximalFamily7 i) := by
    unfold MaxIndependent
    decide
  have hcount := boundary_lower graph7 C h maximalFamily7 hinj hmax
  by_contra! hlt
  have hb : C.size ≤ 2 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hb
  omega

end PEqualNP.Outside.L_meta_906

open PEqualNP.Outside.L_meta_906 in
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
    3 ≤ C.size) := by
  refine ⟨?_, ?_, ?_⟩
  · intro G h
    subst G
    exact ⟨upper6, lower6⟩
  · intro G h
    subst G
    exact ⟨upper5, lower5⟩
  · intro G h
    subst G
    exact ⟨upper7, lower7⟩
