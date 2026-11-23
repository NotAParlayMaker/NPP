import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

lemma side_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (v w : Fin k → Bool)
    (h : ∀ j ∈ F, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  apply Bool.eq_iff_iff.mpr
  simp only [sideTrue, decide_eq_true_eq]
  aesop

lemma fuel_stable {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    {d e : ℕ} (i : Fin C.size) (hd : i.val < d) (he : i.val < e) :
    C.gateValFuel U d i = C.gateValFuel U e i := by
  induction d generalizing e i with
  | zero => omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      simp only [gateValFuel]
      congr 1 <;> apply side_congr <;> intro j hj hji <;> apply ih <;> omega

lemma gate_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  calc
    C.gateVal U i = C.gateValFuel U (C.size + 1) i :=
      fuel_stable C U i i.isLt (by omega)
    _ = _ := rfl

lemma side_mono {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, v j = true → w j = true) :
    sideTrue U B F i v = true → sideTrue V B F i w = true := by
  simp only [sideTrue, decide_eq_true_eq]
  aesop

lemma fuel_mono {n : ℕ} (C : AndCountCircuit n)
    {U V : Finset (Fin n)} (hUV : U ⊆ V) (d : ℕ) :
    ∀ i, C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  induction d with
  | zero => simp [gateValFuel]
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨side_mono hUV _ _ _ _ _ ih hi.1, side_mono hUV _ _ _ _ _ ih hi.2⟩

lemma eval_mono {n : ℕ} (C : AndCountCircuit n)
    {U V : Finset (Fin n)} (hUV : U ⊆ V) :
    C.eval U = true → C.eval V = true := by
  simp only [eval, decide_eq_true_eq]
  have hg := fuel_mono C hUV C.size
  change (∃ v ∈ C.outVars, v ∈ U) ∨ (∃ j ∈ C.outGates, C.gateVal U j = true) → _
  simp only [gateVal] at *
  aesop

def signature {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    Fin C.size → Bool :=
  fun i => sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U)

lemma side_union {n : ℕ} (C : AndCountCircuit n) (U V B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size)
    (h : ∀ j ∈ F, j < i → C.gateVal (U ∪ V) j = (C.gateVal U j || C.gateVal V j)) :
    sideTrue (U ∪ V) B F i (C.gateVal (U ∪ V)) =
      (sideTrue U B F i (C.gateVal U) || sideTrue V B F i (C.gateVal V)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [sideTrue, decide_eq_true_eq, Bool.or_eq_true, Finset.mem_union]
  have hv (j) (hj : j ∈ F) (hji : j < i) :
      C.gateVal (U ∪ V) j = true ↔ C.gateVal U j = true ∨ C.gateVal V j = true := by
    rw [h j hj hji, Bool.or_eq_true]
  aesop

lemma gate_union {n : ℕ} (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hs : signature C U = signature C V) (i : Fin C.size) :
    C.gateVal (U ∪ V) i = (C.gateVal U i || C.gateVal V i) := by
  refine Fin.strong_induction_on ?_ i
  intro i ih
  rw [gate_eq C (U ∪ V) i, gate_eq C U i, gate_eq C V i]
  rw [side_union C U V _ _ i (fun j _ hj => ih j hj),
    side_union C U V _ _ i (fun j _ hj => ih j hj)]
  have hl := congrFun hs i
  change sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) =
    sideTrue V (C.leftVars i) (C.leftGates i) i (C.gateVal V) at hl
  rw [hl]
  cases sideTrue V (C.leftVars i) (C.leftGates i) i (C.gateVal V) <;> simp

lemma eval_union {n : ℕ} (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hs : signature C U = signature C V) :
    C.eval (U ∪ V) = (C.eval U || C.eval V) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval, decide_eq_true_eq, Bool.or_eq_true, Finset.mem_union,
    gate_union C U V hs]
  aesop

lemma maximal_false_eq {n : ℕ} (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hU : C.eval U = false) (hV : C.eval V = false)
    (hUm : ∀ w, w ∉ U → C.eval (insert w U) = true)
    (hVm : ∀ w, w ∉ V → C.eval (insert w V) = true)
    (hs : signature C U = signature C V) : U = V := by
  have hUV : C.eval (U ∪ V) = false := by rw [eval_union C U V hs, hU, hV]; rfl
  apply Finset.Subset.antisymm
  · intro w hw
    by_contra h
    have hi : insert w V ⊆ U ∪ V := by intro x hx; simp only [Finset.mem_insert] at hx; aesop
    have ht := eval_mono C hi (hVm w h)
    rw [hUV] at ht
    contradiction
  · intro w hw
    by_contra h
    have hi : insert w U ⊆ U ∪ V := by intro x hx; simp only [Finset.mem_insert] at hx; aesop
    have ht := eval_mono C hi (hUm w h)
    rw [hUV] at ht
    contradiction

lemma count_bound {n : ℕ} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (hF : ∀ I ∈ F, C.eval I = false ∧ ∀ w, w ∉ I → C.eval (insert w I) = true) :
    F.card ≤ 2 ^ C.size := by
  have hi : Function.Injective (fun I : {I // I ∈ F} => signature C I.val) := by
    intro I J h
    apply Subtype.ext
    exact maximal_false_eq C I.val J.val (hF _ I.property).1 (hF _ J.property).1
      (hF _ I.property).2 (hF _ J.property).2 h
  have hc := Fintype.card_le_of_injective _ hi
  simpa using hc

def family6 : Finset (Finset (Fin 6)) :=
  {{0, 3}, {0, 4}, {0, 5}, {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 4}, {2, 5}}

def family5 : Finset (Finset (Fin 5)) := {{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}}

def family7 : Finset (Finset (Fin 7)) :=
  {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 0}}

def circuit6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  leftGates := fun _ => ∅
  rightGates := fun _ => ∅
  outVars := ∅
  outGates := Finset.univ

def circuit5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  rightVars := ![{1, 4}, {1, 3}, {4}]
  leftGates := fun _ => ∅
  rightGates := fun _ => ∅
  outVars := ∅
  outGates := Finset.univ

def circuit7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
  rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
  leftGates := ![∅, {0}, {1}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1, 2}

lemma lower {n k : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Finset (Fin n)))
    (hcard : 2 ^ k < F.card)
    (hF : ∀ I ∈ F, (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧
      (∀ w, w ∉ I → ∃ a ∈ I, G.Adj a w))
    (C : AndCountCircuit n)
    (hC : ∀ I, (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w, w ∉ I → C.eval (insert w I) = true) :
    k + 1 ≤ C.size := by
  have hb := count_bound C F (fun I hI => hC I (hF I hI).1 (hF I hI).2)
  by_contra h
  have hs : C.size ≤ k := by omega
  have hp : 2 ^ C.size ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hs
  omega

end PEqualNP.Outside.L_meta_906

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
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
    constructor
    · refine ⟨PEqualNP.Outside.L_meta_906.circuit6, ?_, ?_, ?_⟩
      · unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
        decide
      · decide
      · simp only [SimpleGraph.fromRel_adj]
        decide
    · intro C _ hC
      exact PEqualNP.Outside.L_meta_906.lower _ PEqualNP.Outside.L_meta_906.family6
        (k := 3) (by decide) (by simp only [SimpleGraph.fromRel_adj]; decide) C hC
  · intro G hG
    subst G
    constructor
    · refine ⟨PEqualNP.Outside.L_meta_906.circuit5, ?_, ?_, ?_⟩
      · unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
        decide
      · decide
      · simp only [SimpleGraph.fromRel_adj]
        decide
    · intro C _ hC
      exact PEqualNP.Outside.L_meta_906.lower _ PEqualNP.Outside.L_meta_906.family5
        (k := 2) (by decide) (by simp only [SimpleGraph.fromRel_adj]; decide) C hC
  · intro G hG
    subst G
    constructor
    · refine ⟨PEqualNP.Outside.L_meta_906.circuit7, ?_, ?_, ?_⟩
      · unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
        decide
      · decide
      · simp only [SimpleGraph.fromRel_adj]
        decide
    · intro C _ hC
      exact PEqualNP.Outside.L_meta_906.lower _ PEqualNP.Outside.L_meta_906.family7
        (k := 2) (by decide) (by simp only [SimpleGraph.fromRel_adj]; decide) C hC
