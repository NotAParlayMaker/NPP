import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906_aux

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

theorem mergeInput {n : ℕ} (C : AndCountCircuit n) (I J U : Finset (Fin n)) (hU : U ⊆ I ∪ J)
    (hs : ∀ i, sideL C I i = sideL C J i) :
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
      have hh := hs i
      rw [hh] at hl ⊢
      tauto
  simp only [eval, decide_eq_true_eq]
  rintro (⟨w, hw, h⟩ | ⟨i, hi', h⟩)
  · rcases Finset.mem_union.mp (hU h) with h | h
    · exact Or.inl (Or.inl ⟨_, hw, h⟩)
    · exact Or.inr (Or.inl ⟨_, hw, h⟩)
  · rcases gate i h with h | h
    · exact Or.inl (Or.inr ⟨i, hi', h⟩)
    · exact Or.inr (Or.inr ⟨i, hi', h⟩)


abbrev Good {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧
  (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w)

abbrev Matches {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) : Prop :=
  ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
    (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
    C.eval I = false ∧ ∀ w, w ∉ I → C.eval (insert w I) = true

theorem countRows {n m : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hmatch : Matches G C) (rows : Fin m → Finset (Fin n)) (hg : ∀ i, Good G (rows i))
    (hd : ∀ i j, i ≠ j → ∃ w ∈ rows i, w ∉ rows j) :
    m ≤ 2 ^ C.size := by
  let code (i : Fin m) := sideL C (rows i)
  have inject : Function.Injective code := by
    intro i j he
    by_contra hne
    obtain ⟨w, hi, hj⟩ := hd i j hne
    have hI := hmatch _ (hg i).1 (hg i).2
    have hJ := hmatch _ (hg j).1 (hg j).2
    have h := mergeInput C (rows i) (rows j) (insert w (rows j))
      (Finset.insert_subset (Finset.mem_union_left _ hi) Finset.subset_union_right)
      (fun k => congrFun he k) (hJ.2 w hj)
    simp [hI.1, hJ.1] at h
  simpa using Fintype.card_le_of_injective _ inject

def graph6 := SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))

def related6 (a b : Fin 6) : Bool := decide
  (a ≠ b ∧ (((a.val,b.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))) ∨ ((b.val,a.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))))

theorem rel6 (a b : Fin 6) : graph6.Adj a b ↔ related6 a b = true := by
  simp only [graph6, SimpleGraph.fromRel_adj, related6, decide_eq_true_eq]

def rows6 : Fin 9 → Finset (Fin 6) := ![{0, 3}, {1, 3}, {2, 3}, {0, 4}, {1, 4}, {2, 4}, {0, 5}, {1, 5}, {2, 5}]

def circuit6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  leftGates := ![∅, ∅, ∅, ∅]
  rightGates := ![∅, ∅, ∅, ∅]
  outVars := ∅
  outGates := {0, 1, 2, 3}

theorem good6 : ∀ i, Good graph6 (rows6 i) := by
  simp only [Good, rel6]
  decide +kernel

theorem diff6 : ∀ i j, i ≠ j → ∃ w ∈ rows6 i, w ∉ rows6 j := by decide +kernel

theorem well6 : circuit6.WellFormed := by
  unfold WellFormed
  decide +kernel

set_option maxRecDepth 10000 in
theorem match6 : Matches graph6 circuit6 := by
  simp only [Matches, rel6]
  decide +kernel

def graph5 := SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))

def related5 (a b : Fin 5) : Bool := decide
  (a ≠ b ∧ (((a.val,b.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ))) ∨ ((b.val,a.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))))

theorem rel5 (a b : Fin 5) : graph5.Adj a b ↔ related5 a b = true := by
  simp only [graph5, SimpleGraph.fromRel_adj, related5, decide_eq_true_eq]

def rows5 : Fin 5 → Finset (Fin 5) := ![{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}]

def circuit5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  rightVars := ![{1, 4}, {1, 3}, {4}]
  leftGates := ![∅, ∅, ∅]
  rightGates := ![∅, ∅, ∅]
  outVars := ∅
  outGates := {0, 1, 2}

theorem good5 : ∀ i, Good graph5 (rows5 i) := by
  simp only [Good, rel5]
  decide +kernel

theorem diff5 : ∀ i j, i ≠ j → ∃ w ∈ rows5 i, w ∉ rows5 j := by decide +kernel

theorem well5 : circuit5.WellFormed := by
  unfold WellFormed
  decide +kernel

set_option maxRecDepth 10000 in
theorem match5 : Matches graph5 circuit5 := by
  simp only [Matches, rel5]
  decide +kernel

def graph7 := SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))

def related7 (a b : Fin 7) : Bool := decide
  (a ≠ b ∧ (((a.val,b.val) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ))) ∨ ((b.val,a.val) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))))

theorem rel7 (a b : Fin 7) : graph7.Adj a b ↔ related7 a b = true := by
  simp only [graph7, SimpleGraph.fromRel_adj, related7, decide_eq_true_eq]

def rows7 : Fin 7 → Finset (Fin 7) := ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {0, 6}, {5, 6}]

def circuit7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
  rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
  leftGates := ![∅, {0}, {1}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1, 2}

theorem good7 : ∀ i, Good graph7 (rows7 i) := by
  simp only [Good, rel7]
  decide +kernel

theorem diff7 : ∀ i j, i ≠ j → ∃ w ∈ rows7 i, w ∉ rows7 j := by decide +kernel

theorem well7 : circuit7.WellFormed := by
  unfold WellFormed
  decide +kernel

set_option maxRecDepth 10000 in
theorem match7 : Matches graph7 circuit7 := by
  simp only [Matches, rel7]
  decide +kernel

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
  · rintro G rfl
    refine ⟨⟨circuit6, well6, by decide, match6⟩, ?_⟩
    intro C _ hm
    have hc := countRows graph6 C hm rows6 good6 diff6
    by_contra! h
    have hp : 2 ^ C.size ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · rintro G rfl
    refine ⟨⟨circuit5, well5, by decide, match5⟩, ?_⟩
    intro C _ hm
    have hc := countRows graph5 C hm rows5 good5 diff5
    by_contra! h
    have hp : 2 ^ C.size ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · rintro G rfl
    refine ⟨⟨circuit7, well7, by decide, match7⟩, ?_⟩
    intro C _ hm
    have hc := countRows graph7 C hm rows7 good7 diff7
    by_contra! h
    have hp : 2 ^ C.size ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
