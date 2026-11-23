import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- The evaluation and selector-merging lemmas are adapted from L_meta_634.
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

def code {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sv C X i false

theorem code_ok {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n))
    (i : Fin C.size) (h : C.gateVal X i = false) : sv C X i (code C X i) = false := by
  rw [gate_false_iff] at h
  unfold code
  cases hl : sv C X i false with
  | false => exact hl
  | true => exact h.resolve_left (by simp [hl])

theorem merge_gate {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n))
    (hc : ∀ i, code C X i = code C Y i) :
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
      have c1 := code_ok C X i h1
      have c2 := code_ok C Y i h2
      rw [← hc i] at c2
      have hm := sv_merge C X Y i _ c1 c2 ih'
      rw [gate_false_iff]
      cases hb : code C X i with
      | false => rw [hb] at hm; exact Or.inl hm
      | true => rw [hb] at hm; exact Or.inr hm
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

theorem merge_eval {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n))
    (hc : ∀ i, code C X i = code C Y i)
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

theorem negative_count {n : ℕ} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (_hwf : C.WellFormed)
    (hF : ∀ I ∈ F, C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true) :
    F.card ≤ 2 ^ C.size := by
  classical
  have eq_of_subset (I J : Finset (Fin n)) (hi : I ∈ F) (hs : I ⊆ J) (hj : C.eval J = false) :
      I = J := by
    apply Finset.Subset.antisymm hs
    intro w hw
    by_contra hn
    have h := eval_mono C (insert w I) J (Finset.insert_subset hw hs) ((hF I hi).2 w hn)
    simp [hj] at h
  let f : (↑F : Type _) → (Fin C.size → Bool) := fun I => code C I.1
  have hf : Function.Injective f := by
    intro I J h
    have hu := merge_eval C I.1 J.1 (fun i => congrFun h i) (hF _ I.2).1 (hF _ J.2).1
    exact Subtype.ext ((eq_of_subset _ _ I.2 Finset.subset_union_left hu).trans
      (eq_of_subset _ _ J.2 Finset.subset_union_right hu).symm)
  simpa using Fintype.card_le_of_injective f hf

end PEqualNP.Outside.L_meta_906_aux

namespace PEqualNP.Outside.L_meta_906_aux

open PEqualNP.AndCount

private def upperOn {n : ℕ} (edges : List (ℕ × ℕ)) (k : ℕ) : Prop :=
  let G := SimpleGraph.fromRel (fun a b : Fin n => (a.val, b.val) ∈ edges)
  ∃ C : AndCountCircuit n, C.WellFormed ∧ C.size ≤ k ∧
    ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) →
      (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true

private def trianglesCircuit : AndCountCircuit 6 where
  size := 4
  leftVars i := [{0}, {1}, {3}, {4}].getD i.val ∅
  rightVars i := [{1,2}, {2}, {4,5}, {5}].getD i.val ∅
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private def cycle5Circuit : AndCountCircuit 5 where
  size := 3
  leftVars i := [{0}, {2}, {3}].getD i.val ∅
  rightVars i := [{1,4}, {1,3}, {4}].getD i.val ∅
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private def complement7Circuit : AndCountCircuit 7 where
  size := 3
  leftVars i := [{0,4}, {0,1}, {1,2,3}].getD i.val ∅
  rightVars i := [{2,6}, {3,4,5}, {5,6}].getD i.val ∅
  leftGates i := [∅, {0}, {1}].getD i.val ∅
  rightGates i := [∅, ∅, {0}].getD i.val ∅
  outVars := ∅
  outGates := {1,2}

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem triangle_upper : upperOn (n := 6) [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5)] 4 := by
  refine ⟨trianglesCircuit, ?_, ?_, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide +kernel
  · decide
  · simp only [SimpleGraph.fromRel_adj]
    decide +kernel

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem cycle5_upper : upperOn (n := 5) [(0,1),(1,2),(2,3),(3,4),(4,0)] 3 := by
  refine ⟨cycle5Circuit, ?_, ?_, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide +kernel
  · decide
  · simp only [SimpleGraph.fromRel_adj]
    decide +kernel

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem complement7_upper : upperOn (n := 7)
    [(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6),(4,6),(4,0),(5,0),(5,1),(6,1),(6,2)] 3 := by
  refine ⟨complement7Circuit, ?_, ?_, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide +kernel
  · decide
  · simp only [SimpleGraph.fromRel_adj]
    decide +kernel

end PEqualNP.Outside.L_meta_906_aux

namespace PEqualNP.Outside.L_meta_906_aux

def maxFamily {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun I => (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) ∧
    ∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w)

private theorem force_count {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcard : 2 ^ k < (maxFamily G).card)
    (C : PEqualNP.AndCount.AndCountCircuit n) (hw : C.WellFormed)
    (heval : ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) →
      (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true) :
    k + 1 ≤ C.size := by
  have h := negative_count C (maxFamily G) hw (by
    intro I hI
    have hp := (Finset.mem_filter.mp hI).2
    exact heval I hp.1 hp.2)
  by_contra! hlt
  have hp : 2 ^ C.size ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  omega

set_option maxHeartbeats 1800000 in
private theorem triangle_count : (maxFamily (SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))))).card = 9 := by decide

set_option maxHeartbeats 1800000 in
private theorem cycle5_count : (maxFamily (SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ))))).card = 5 := by decide

set_option maxHeartbeats 1800000 in
private theorem complement7_count : (maxFamily (SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ))))).card = 7 := by decide

end PEqualNP.Outside.L_meta_906_aux

open PEqualNP.Outside.L_meta_906_aux

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
  · intro G hG
    subst G
    refine ⟨triangle_upper, ?_⟩
    apply force_count (k := 3)
    rw [triangle_count]
    decide
  · intro G hG
    subst G
    refine ⟨cycle5_upper, ?_⟩
    apply force_count (k := 2)
    rw [cycle5_count]
    decide
  · intro G hG
    subst G
    refine ⟨complement7_upper, ?_⟩
    apply force_count (k := 2)
    rw [complement7_count]
    decide
