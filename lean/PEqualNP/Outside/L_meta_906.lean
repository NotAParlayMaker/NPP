import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906_aux

open PEqualNP.AndCount

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

def leftSignature {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (j : Fin C.size) : Bool :=
  AndCountCircuit.sideTrue I (C.leftVars j) (C.leftGates j) j (C.gateVal I)

theorem splitGate {n : ℕ} (C : AndCountCircuit n) (I J U : Finset (Fin n))
    (sig : leftSignature C I = leftSignature C J)
    (sub : ∀ a ∈ U, a ∈ I ∨ a ∈ J) (k : Fin C.size) :
    C.gateVal U k = true → C.gateVal I k = true ∨ C.gateVal J k = true := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    have splitSide (V : Finset (Fin n)) (F : Finset (Fin C.size)) :
        AndCountCircuit.sideTrue U V F k (C.gateVal U) = true →
        AndCountCircuit.sideTrue I V F k (C.gateVal I) = true ∨
          AndCountCircuit.sideTrue J V F k (C.gateVal J) = true := by
      simp only [AndCountCircuit.sideTrue, decide_eq_true_eq]
      rintro (⟨a, ha, hu⟩ | ⟨j, hj, hjk, hv⟩)
      · rcases sub a hu with hi | hJ
        · exact Or.inl (Or.inl ⟨a, ha, hi⟩)
        · exact Or.inr (Or.inl ⟨a, ha, hJ⟩)
      · rcases ih j hjk hv with hi | hJ
        · exact Or.inl (Or.inr ⟨j, hj, hjk, hi⟩)
        · exact Or.inr (Or.inr ⟨j, hj, hjk, hJ⟩)
    rw [gateVal_eq C U k, gateVal_eq C I k, gateVal_eq C J k]
    simp only [Bool.and_eq_true]
    rintro ⟨hL, hR⟩
    have same := congrFun sig k
    unfold leftSignature at same
    have li := splitSide _ _ hL
    have ri := splitSide _ _ hR
    rw [same] at li ⊢
    rcases li with h | h <;> rcases ri with r | r
    · exact Or.inl ⟨h,r⟩
    · exact Or.inr ⟨h,r⟩
    · exact Or.inl ⟨h,r⟩
    · exact Or.inr ⟨h,r⟩

theorem splitOutput {n : ℕ} (C : AndCountCircuit n) (I J U : Finset (Fin n))
    (sig : leftSignature C I = leftSignature C J) (sub : ∀ a ∈ U, a ∈ I ∨ a ∈ J) :
    C.eval U = true → C.eval I = true ∨ C.eval J = true := by
  simp only [AndCountCircuit.eval, decide_eq_true_eq]
  rintro (⟨a, ha, hu⟩ | ⟨j, hj, hv⟩)
  · rcases sub a hu with hi | hJ
    · exact Or.inl (Or.inl ⟨a, ha, hi⟩)
    · exact Or.inr (Or.inl ⟨a, ha, hJ⟩)
  · rcases splitGate C I J U sig sub j hv with hi | hJ
    · exact Or.inl (Or.inr ⟨j, hj, hi⟩)
    · exact Or.inr (Or.inr ⟨j, hj, hJ⟩)

theorem count_false {n : ℕ} (C : AndCountCircuit n) (A : Finset (Finset (Fin n)))
    (h : ∀ I ∈ A, C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true) :
    A.card ≤ 2 ^ C.size := by
  classical
  have incl (I J : Finset (Fin n)) (hi : I ∈ A) (hj : J ∈ A)
      (same : leftSignature C I = leftSignature C J) : J ⊆ I := by
    intro w hw
    by_contra hn
    have sub : ∀ a ∈ insert w I, a ∈ I ∨ a ∈ J := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | h'
      · exact Or.inr hw
      · exact Or.inl h'
    have ht := splitOutput C I J (insert w I) same sub ((h I hi).2 w hn)
    simp only [(h I hi).1, (h J hj).1, Bool.false_eq_true, or_self] at ht
  have hinj : (↑A : Set (Finset (Fin n))).InjOn (leftSignature C) := by
    intro I hi J hj same
    exact Finset.Subset.antisymm (incl J I hj hi same.symm) (incl I J hi hj same)
  have bound : A.card ≤ (Finset.univ : Finset (Fin C.size → Bool)).card :=
    Finset.card_le_card_of_injOn (leftSignature C) (fun _ _ => Finset.mem_univ _) hinj
  simpa using bound



def graph6 := SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))
def circuit6 : AndCountCircuit 6 :=
  ⟨4, ![{0}, {1}, {3}, {4}], (fun _ => ∅), ![{1,2}, {2}, {4,5}, {5}], (fun _ => ∅), ∅, Finset.univ⟩

lemma wf6 : circuit6.WellFormed := by unfold AndCountCircuit.WellFormed; decide

def family6 : Finset (Finset (Fin 6)) := by
  letI : DecidableRel graph6.Adj := fun a b => by dsimp [graph6, SimpleGraph.fromRel]; infer_instance
  exact Finset.univ.filter (fun I => (∀ a ∈ I, ∀ c ∈ I, ¬ graph6.Adj a c) ∧ (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, graph6.Adj a w))

lemma member6 (I) : I ∈ family6 ↔ (∀ a ∈ I, ∀ c ∈ I, ¬ graph6.Adj a c) ∧ (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, graph6.Adj a w) := by simp [family6]

set_option maxRecDepth 8192 in
lemma count6 : family6.card = 9 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
lemma good6 : ∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ (graph6).Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, (graph6).Adj a w) → circuit6.eval I = false ∧ ∀ w : Fin 6, w ∉ I → circuit6.eval (insert w I) = true := by
  have check : ∀ I ∈ family6, circuit6.eval I = false ∧
      ∀ w : Fin 6, w ∉ I → circuit6.eval (insert w I) = true := by decide
  exact fun I hi hm => check I ((member6 I).mpr ⟨hi,hm⟩)



def graph5 := SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))
def circuit5 : AndCountCircuit 5 :=
  ⟨3, ![{0}, {2}, {3}], (fun _ => ∅), ![{1,4}, {1,3}, {4}], (fun _ => ∅), ∅, Finset.univ⟩

lemma wf5 : circuit5.WellFormed := by unfold AndCountCircuit.WellFormed; decide

def family5 : Finset (Finset (Fin 5)) := by
  letI : DecidableRel graph5.Adj := fun a b => by dsimp [graph5, SimpleGraph.fromRel]; infer_instance
  exact Finset.univ.filter (fun I => (∀ a ∈ I, ∀ c ∈ I, ¬ graph5.Adj a c) ∧ (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, graph5.Adj a w))

lemma member5 (I) : I ∈ family5 ↔ (∀ a ∈ I, ∀ c ∈ I, ¬ graph5.Adj a c) ∧ (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, graph5.Adj a w) := by simp [family5]

set_option maxRecDepth 8192 in
lemma count5 : family5.card = 5 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
lemma good5 : ∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ (graph5).Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, (graph5).Adj a w) → circuit5.eval I = false ∧ ∀ w : Fin 5, w ∉ I → circuit5.eval (insert w I) = true := by
  have check : ∀ I ∈ family5, circuit5.eval I = false ∧
      ∀ w : Fin 5, w ∉ I → circuit5.eval (insert w I) = true := by decide
  exact fun I hi hm => check I ((member5 I).mpr ⟨hi,hm⟩)



def graph7 := SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))
def circuit7 : AndCountCircuit 7 :=
  ⟨3, ![{0,4}, {0,1}, {1,2,3}], (![∅, {0}, {1}]), ![{2,6}, {3,4,5}, {5,6}], (![∅, ∅, {0}]), ∅, {1,2}⟩

lemma wf7 : circuit7.WellFormed := by unfold AndCountCircuit.WellFormed; decide

def family7 : Finset (Finset (Fin 7)) := by
  letI : DecidableRel graph7.Adj := fun a b => by dsimp [graph7, SimpleGraph.fromRel]; infer_instance
  exact Finset.univ.filter (fun I => (∀ a ∈ I, ∀ c ∈ I, ¬ graph7.Adj a c) ∧ (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, graph7.Adj a w))

lemma member7 (I) : I ∈ family7 ↔ (∀ a ∈ I, ∀ c ∈ I, ¬ graph7.Adj a c) ∧ (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, graph7.Adj a w) := by simp [family7]

set_option maxRecDepth 8192 in
lemma count7 : family7.card = 7 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
lemma good7 : ∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ (graph7).Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, (graph7).Adj a w) → circuit7.eval I = false ∧ ∀ w : Fin 7, w ∉ I → circuit7.eval (insert w I) = true := by
  have check : ∀ I ∈ family7, circuit7.eval I = false ∧
      ∀ w : Fin 7, w ∉ I → circuit7.eval (insert w I) = true := by decide
  exact fun I hi hm => check I ((member7 I).mpr ⟨hi,hm⟩)



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
    refine ⟨⟨circuit6, wf6, le_rfl, good6⟩, ?_⟩
    intro C _ h
    have hb := count_false C family6 (fun I hI =>
      h I ((member6 I).mp hI).1 ((member6 I).mp hI).2)
    rw [count6] at hb
    by_contra! small
    have hs : C.size ≤ 3 := by omega
    have hp : (2 : ℕ) ^ C.size ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hs
    omega
  · rintro G rfl
    refine ⟨⟨circuit5, wf5, le_rfl, good5⟩, ?_⟩
    intro C _ h
    have hb := count_false C family5 (fun I hI =>
      h I ((member5 I).mp hI).1 ((member5 I).mp hI).2)
    rw [count5] at hb
    by_contra! small
    have hs : C.size ≤ 2 := by omega
    have hp : (2 : ℕ) ^ C.size ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hs
    omega
  · rintro G rfl
    refine ⟨⟨circuit7, wf7, le_rfl, good7⟩, ?_⟩
    intro C _ h
    have hb := count_false C family7 (fun I hI =>
      h I ((member7 I).mp hI).1 ((member7 I).mp hI).2)
    rw [count7] at hb
    by_contra! small
    have hs : C.size ≤ 2 := by omega
    have hp : (2 : ℕ) ^ C.size ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hs
    omega
