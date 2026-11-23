import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
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

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
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

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
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

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C hUV C.size i h

private def choices {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U)

private lemma union_side {n : ℕ} (C : AndCountCircuit n) (U V B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size)
    (ih : ∀ j < i, C.gateVal U j = false → C.gateVal V j = false → C.gateVal (U ∪ V) j = false)
    (hU : sideTrue U B F i (C.gateVal U) = false)
    (hV : sideTrue V B F i (C.gateVal V) = false) :
    sideTrue (U ∪ V) B F i (C.gateVal (U ∪ V)) = false := by
  unfold sideTrue at hU hV ⊢
  rw [decide_eq_false_iff_not] at hU hV ⊢
  rintro (⟨p,hp,huv⟩ | ⟨j,hj,hji,hon⟩)
  · rcases Finset.mem_union.mp huv with hu | hv
    · exact hU (Or.inl ⟨p,hp,hu⟩)
    · exact hV (Or.inl ⟨p,hp,hv⟩)
  · have uj : C.gateVal U j = false := by
      cases h : C.gateVal U j
      · rfl
      · exact False.elim (hU (Or.inr ⟨j,hj,hji,h⟩))
    have vj : C.gateVal V j = false := by
      cases h : C.gateVal V j
      · rfl
      · exact False.elim (hV (Or.inr ⟨j,hj,hji,h⟩))
    rw [ih j hji uj vj] at hon
    contradiction

private lemma gate_union_false {n : ℕ} (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hab : choices C U = choices C V) (i : Fin C.size) :
    C.gateVal U i = false → C.gateVal V i = false → C.gateVal (U ∪ V) i = false := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    intro hu hv
    rw [gateVal_unfold] at hu hv ⊢
    have hs := congrFun hab i
    change sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) =
       sideTrue V (C.leftVars i) (C.leftGates i) i (C.gateVal V) at hs
    cases hl : sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) with
    | false =>
      have hh := union_side C U V _ _ i ih hl (hs.symm.trans hl)
      simp [hh]
    | true =>
      have hvl := hs.symm.trans hl
      simp [hl] at hu
      simp [hvl] at hv
      have hh := union_side C U V _ _ i ih hu hv
      simp [hh]

private lemma false_union {n : ℕ} (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hab : choices C U = choices C V) (hu : C.eval U = false) (hv : C.eval V = false) :
    C.eval (U ∪ V) = false := by
  unfold AndCountCircuit.eval at hu hv ⊢
  rw [decide_eq_false_iff_not] at hu hv ⊢
  rintro (⟨p,hp,huv⟩ | ⟨j,hj,hon⟩)
  · rcases Finset.mem_union.mp huv with u | v
    · exact hu (Or.inl ⟨p,hp,u⟩)
    · exact hv (Or.inl ⟨p,hp,v⟩)
  · have u : C.gateVal U j = false := by
      cases h : C.gateVal U j
      · rfl
      · exact False.elim (hu (Or.inr ⟨j,hj,h⟩))
    have v : C.gateVal V j = false := by
      cases h : C.gateVal V j
      · rfl
      · exact False.elim (hv (Or.inr ⟨j,hj,h⟩))
    rw [gate_union_false C U V hab j u v] at hon
    contradiction

private lemma eval_mono {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (h : C.eval U = true) : C.eval V = true := by
  unfold AndCountCircuit.eval at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  rcases h with h | ⟨j,hj,hg⟩
  · obtain ⟨v,hv,h⟩ := h
    exact Or.inl ⟨v,hv,hUV h⟩
  · exact Or.inr ⟨j,hj,gateVal_mono_U C hUV j hg⟩

theorem boundary_bound {n : ℕ} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (h : ∀ I ∈ F, C.eval I = false ∧ ∀ w ∉ I, C.eval (insert w I) = true) :
    F.card ≤ 2 ^ C.size := by
  classical
  have inj : Set.InjOn (choices C) F := by
    intro I hi J hj he
    have hu := false_union C I J he (h I hi).1 (h J hj).1
    apply Finset.Subset.antisymm
    · intro w hwi
      by_contra hwj
      have ht := (h J hj).2 w hwj
      have sub : insert w J ⊆ I ∪ J :=
        Finset.insert_subset (Finset.mem_union_left _ hwi) Finset.subset_union_right
      have heq := eval_mono C sub ht
      rw [hu] at heq
      contradiction
    · intro w hwj
      by_contra hwi
      have ht := (h I hi).2 w hwi
      have sub : insert w I ⊆ I ∪ J :=
        Finset.insert_subset (Finset.mem_union_right _ hwj) Finset.subset_union_left
      have heq := eval_mono C sub ht
      rw [hu] at heq
      contradiction
  calc
    F.card = (F.image (choices C)).card := (Finset.card_image_of_injOn inj).symm
    _ ≤ Fintype.card (Fin C.size → Bool) := Finset.card_le_univ _
    _ = 2 ^ C.size := by simp

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit


def graph6 := SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))

def circ6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  leftGates := ![∅, ∅, ∅, ∅]
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  rightGates := ![∅, ∅, ∅, ∅]
  outVars := ∅
  outGates := {0, 1, 2, 3}

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem upper6 : ∀ G : SimpleGraph (Fin 6), G = SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed ∧ C.size ≤ 4 ∧
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true) := by
  intro G rfl
  refine ⟨circ6, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide +revert
  · simp only [SimpleGraph.fromRel_adj]
    decide +revert

def graph5 := SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))

def circ5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  leftGates := ![∅, ∅, ∅]
  rightVars := ![{1, 4}, {1, 3}, {4}]
  rightGates := ![∅, ∅, ∅]
  outVars := ∅
  outGates := {0, 1, 2}

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem upper5 : ∀ G : SimpleGraph (Fin 5), G = SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ))) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true) := by
  intro G rfl
  refine ⟨circ5, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide +revert
  · simp only [SimpleGraph.fromRel_adj]
    decide +revert

def graph7 := SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))

def circ7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
  leftGates := ![∅, {0}, {1}]
  rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1, 2}

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem upper7 : ∀ G : SimpleGraph (Fin 7), G = SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ))) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true) := by
  intro G rfl
  refine ⟨circ7, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide +revert
  · simp only [SimpleGraph.fromRel_adj]
    decide +revert

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
def maxSets6 : Finset (Finset (Fin 6)) := by
  letI : DecidablePred (fun I : Finset (Fin 6) => (∀ a ∈ I, ∀ c ∈ I, ¬ (graph6).Adj a c) ∧ (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, (graph6).Adj a w)) := fun I => by
    unfold graph6
    simp only [SimpleGraph.fromRel_adj]
    infer_instance
  exact Finset.univ.filter (fun I : Finset (Fin 6) => (∀ a ∈ I, ∀ c ∈ I, ¬ (graph6).Adj a c) ∧ (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, (graph6).Adj a w))

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem maxSets6_card : maxSets6.card = 9 := by
  decide

theorem lower6 (C : AndCountCircuit 6)
    (h : ∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ graph6.Adj a c) →
      (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, graph6.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true) : 4 ≤ C.size := by
  classical
  have bound := boundary_bound C maxSets6 (by
    intro I hi
    have pair : (∀ a ∈ I, ∀ b ∈ I, ¬ graph6.Adj a b) ∧
        (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, graph6.Adj a w) := by
      simpa only [maxSets6, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact h I pair.1 pair.2)
  rw [maxSets6_card] at bound
  by_contra! hsmall
  have hle : C.size ≤ 3 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  omega

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
def maxSets5 : Finset (Finset (Fin 5)) := by
  letI : DecidablePred (fun I : Finset (Fin 5) => (∀ a ∈ I, ∀ c ∈ I, ¬ (graph5).Adj a c) ∧ (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, (graph5).Adj a w)) := fun I => by
    unfold graph5
    simp only [SimpleGraph.fromRel_adj]
    infer_instance
  exact Finset.univ.filter (fun I : Finset (Fin 5) => (∀ a ∈ I, ∀ c ∈ I, ¬ (graph5).Adj a c) ∧ (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, (graph5).Adj a w))

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem maxSets5_card : maxSets5.card = 5 := by
  decide

theorem lower5 (C : AndCountCircuit 5)
    (h : ∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ graph5.Adj a c) →
      (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, graph5.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true) : 3 ≤ C.size := by
  classical
  have bound := boundary_bound C maxSets5 (by
    intro I hi
    have pair : (∀ a ∈ I, ∀ b ∈ I, ¬ graph5.Adj a b) ∧
        (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, graph5.Adj a w) := by
      simpa only [maxSets5, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact h I pair.1 pair.2)
  rw [maxSets5_card] at bound
  by_contra! hsmall
  have hle : C.size ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  omega

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
def maxSets7 : Finset (Finset (Fin 7)) := by
  letI : DecidablePred (fun I : Finset (Fin 7) => (∀ a ∈ I, ∀ c ∈ I, ¬ (graph7).Adj a c) ∧ (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, (graph7).Adj a w)) := fun I => by
    unfold graph7
    simp only [SimpleGraph.fromRel_adj]
    infer_instance
  exact Finset.univ.filter (fun I : Finset (Fin 7) => (∀ a ∈ I, ∀ c ∈ I, ¬ (graph7).Adj a c) ∧ (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, (graph7).Adj a w))

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem maxSets7_card : maxSets7.card = 7 := by
  decide

theorem lower7 (C : AndCountCircuit 7)
    (h : ∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ graph7.Adj a c) →
      (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, graph7.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true) : 3 ≤ C.size := by
  classical
  have bound := boundary_bound C maxSets7 (by
    intro I hi
    have pair : (∀ a ∈ I, ∀ b ∈ I, ¬ graph7.Adj a b) ∧
        (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, graph7.Adj a w) := by
      simpa only [maxSets7, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact h I pair.1 pair.2)
  rw [maxSets7_card] at bound
  by_contra! hsmall
  have hle : C.size ≤ 2 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  omega

end PEqualNP.Outside.L_meta_906

open PEqualNP.Outside.L_meta_906

theorem PEqualNP.Outside.L_meta_906 :
  (∀ G : SimpleGraph (Fin 6), G = SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))) →
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
  · intro G rfl
    exact ⟨upper6 _ rfl, fun C _ h => lower6 C h⟩
  · intro G rfl
    exact ⟨upper5 _ rfl, fun C _ h => lower5 C h⟩
  · intro G rfl
    exact ⟨upper7 _ rfl, fun C _ h => lower7 C h⟩
