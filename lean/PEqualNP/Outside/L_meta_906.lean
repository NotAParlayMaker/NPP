import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

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

def sideL {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def sideR {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

theorem unionSide {n : ℕ} (C : AndCountCircuit n) (U I J B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size) (hU : U ⊆ I ∪ J)
    (ih : ∀ j < i, C.gateVal U j = true → C.gateVal I j = true ∨ C.gateVal J j = true) :
    sideTrue U B F i (C.gateVal U) = true →
    sideTrue I B F i (C.gateVal I) = true ∨ sideTrue J B F i (C.gateVal J) = true := by
  simp only [sideTrue, decide_eq_true_eq]
  rintro (⟨v, hv, hu⟩ | ⟨j, hj, hji, ht⟩)
  · rcases Finset.mem_union.mp (hU hu) with h | h
    · exact Or.inl (Or.inl ⟨v, hv, h⟩)
    · exact Or.inr (Or.inl ⟨v, hv, h⟩)
  · rcases ih j hji ht with h | h
    · exact Or.inl (Or.inr ⟨j, hj, hji, h⟩)
    · exact Or.inr (Or.inr ⟨j, hj, hji, h⟩)

theorem mergeInput {n : ℕ} (C : AndCountCircuit n) (I J U : Finset (Fin n))
    (hU : U ⊆ I ∪ J) (hs : ∀ i, sideL C I i = sideL C J i) :
    C.eval U = true → C.eval I = true ∨ C.eval J = true := by
  have gate (i : Fin C.size) : C.gateVal U i = true →
      C.gateVal I i = true ∨ C.gateVal J i = true := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h i ih =>
      intro ht
      rw [gateVal_rec, Bool.and_eq_true] at ht
      rw [gateVal_rec C I, gateVal_rec C J]
      change (sideL C I i && sideR C I i) = true ∨ (sideL C J i && sideR C J i) = true
      have hl : sideL C I i = true ∨ sideL C J i = true := unionSide C U I J _ _ i hU ih ht.1
      have hr : sideR C I i = true ∨ sideR C J i = true := unionSide C U I J _ _ i hU ih ht.2
      simp only [Bool.and_eq_true]
      rw [hs i] at hl ⊢
      tauto
  simp only [eval, decide_eq_true_eq]
  rintro (⟨w, hw, h⟩ | ⟨i, hi', h⟩)
  · rcases Finset.mem_union.mp (hU h) with h | h
    · exact Or.inl (Or.inl ⟨_, hw, h⟩)
    · exact Or.inr (Or.inl ⟨_, hw, h⟩)
  · rcases gate i h with h | h
    · exact Or.inl (Or.inr ⟨i, hi', h⟩)
    · exact Or.inr (Or.inr ⟨i, hi', h⟩)

abbrev Ind {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :=
  ∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c

abbrev Dom {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :=
  ∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w

def indB {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)) : Bool :=
  decide (Ind G I)

def domB {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)) : Bool :=
  decide (Dom G I)

theorem indSpec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)) :
    indB G I = true ↔ Ind G I := decide_eq_true_iff

theorem domSpec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)) :
    domB G I = true ↔ Dom G I := decide_eq_true_iff

abbrev Fits {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) :=
  ∀ I : Finset (Fin n), Ind G I → Dom G I →
    C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true

theorem lower {n m s : ℕ} (G : SimpleGraph (Fin n)) (rows : Fin m → Finset (Fin n))
    (good : ∀ a, Ind G (rows a) ∧ Dom G (rows a))
    (diff : ∀ a b, a ≠ b → ∃ w ∈ rows a, w ∉ rows b)
    (large : 2 ^ s < m) (C : AndCountCircuit n) (h : Fits G C) : s + 1 ≤ C.size := by
  let code (a : Fin m) := sideL C (rows a)
  have inj : Function.Injective code := by
    intro a b hab
    by_contra hne
    obtain ⟨w, hwa, hwb⟩ := diff a b hne
    have ha := h _ (good a).1 (good a).2
    have hb := h _ (good b).1 (good b).2
    have he := mergeInput C (rows a) (rows b) (insert w (rows b))
      (Finset.insert_subset (Finset.mem_union_left _ hwa) Finset.subset_union_right)
      (congrFun hab) (hb.2 w hwb)
    simp [ha.1, hb.1] at he
  have hc := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at hc
  by_contra! hlt
  have hp : 2 ^ C.size ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) (by omega)
  omega

abbrev graph6 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))

def circuit6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

def rows6 : Fin 9 → Finset (Fin 6) :=
  ![{0, 3}, {0, 4}, {0, 5}, {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 4}, {2, 5}]

theorem upper6 : Fits graph6 circuit6 := by
  simp only [Fits, ← indSpec graph6, ← domSpec graph6]
  decide +kernel

theorem lower6 (C : AndCountCircuit 6) (h : Fits graph6 C) : 4 ≤ C.size := by
  exact lower (s := 3) graph6 rows6
    (by simp only [← indSpec graph6, ← domSpec graph6]; decide +kernel)
    (by decide +kernel) (by decide) C h

abbrev graph5 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))

def circuit5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  rightVars := ![{1, 4}, {1, 3}, {4}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

def rows5 : Fin 5 → Finset (Fin 5) :=
  ![{0, 2}, {1, 3}, {2, 4}, {3, 0}, {4, 1}]

theorem upper5 : Fits graph5 circuit5 := by
  simp only [Fits, ← indSpec graph5, ← domSpec graph5]
  decide +kernel

theorem lower5 (C : AndCountCircuit 5) (h : Fits graph5 C) : 3 ≤ C.size := by
  exact lower (s := 2) graph5 rows5
    (by simp only [← indSpec graph5, ← domSpec graph5]; decide +kernel)
    (by decide +kernel) (by decide) C h

abbrev graph7 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))

def circuit7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
  rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
  leftGates := ![∅, {0}, {1}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1, 2}

def rows7 : Fin 7 → Finset (Fin 7) :=
  ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 0}]

theorem upper7 : Fits graph7 circuit7 := by
  simp only [Fits, ← indSpec graph7, ← domSpec graph7]
  decide +kernel

theorem lower7 (C : AndCountCircuit 7) (h : Fits graph7 C) : 3 ≤ C.size := by
  exact lower (s := 2) graph7 rows7
    (by simp only [← indSpec graph7, ← domSpec graph7]; decide +kernel)
    (by decide +kernel) (by decide) C h

end PEqualNP.Outside.L_meta_906

open PEqualNP.Outside.L_meta_906

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
  · intro G rfl
    refine ⟨⟨circuit6, ?_, by decide, upper6⟩, fun C _ h => lower6 C h⟩
    unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
    decide
  · intro G rfl
    refine ⟨⟨circuit5, ?_, by decide, upper5⟩, fun C _ h => lower5 C h⟩
    unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
    decide
  · intro G rfl
    refine ⟨⟨circuit7, ?_, by decide, upper7⟩, fun C _ h => lower7 C h⟩
    unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
    decide
