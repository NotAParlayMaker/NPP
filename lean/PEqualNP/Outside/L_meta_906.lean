import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

variable {n : ℕ} (C : AndCountCircuit n)

private lemma fuel_stable (U : Finset (Fin n)) (d : ℕ) (i : Fin C.size) (hi : i.val < d) :
    C.gateValFuel U (d + 1) i = C.gateValFuel U d i := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    have side (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
        sideTrue U B F i (C.gateValFuel U (d + 1)) = sideTrue U B F i (C.gateValFuel U d) := by
      apply decide_eq_decide.mpr
      have stable (j : Fin C.size) (hj : j < i) := ih j (by omega)
      grind
    exact congrArg₂ Bool.and (side _ _) (side _ _)

private lemma gate_eq (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) :=
  (fuel_stable C U C.size i i.isLt).symm

private def cert (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  !(sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U))

private lemma eval_cover {I J S : Finset (Fin n)} (hS : S ⊆ I ∪ J)
    (hc : cert C I = cert C J) (hs : C.eval S = true) : C.eval I = true ∨ C.eval J = true := by
  have vertex (v : Fin n) (hv : v ∈ S) := Finset.mem_union.mp (hS hv)
  have gate (i : Fin C.size) : C.gateVal S i = true → C.gateVal I i = true ∨ C.gateVal J i = true := by
    apply (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction i
    intro i ih
    have side (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
        sideTrue S B F i (C.gateVal S) = true →
        sideTrue I B F i (C.gateVal I) = true ∨ sideTrue J B F i (C.gateVal J) = true := by
      simp only [sideTrue, decide_eq_true_eq]
      rintro (⟨v, hv, hs⟩ | ⟨j, hj, hji, hs⟩)
      · rcases vertex v hs with h | h
        · exact Or.inl (Or.inl ⟨v, hv, h⟩)
        · exact Or.inr (Or.inl ⟨v, hv, h⟩)
      · rcases ih j hji hs with h | h
        · exact Or.inl (Or.inr ⟨j, hj, hji, h⟩)
        · exact Or.inr (Or.inr ⟨j, hj, hji, h⟩)
    have hl := side (C.leftVars i) (C.leftGates i)
    have hr := side (C.rightVars i) (C.rightGates i)
    have he := congrFun hc i
    unfold cert at he
    rw [gate_eq C S i, gate_eq C I i, gate_eq C J i]
    simp only [Bool.and_eq_true]
    grind
  simp only [AndCountCircuit.eval, decide_eq_true_eq] at hs ⊢
  grind

private lemma count_bound (M : Finset (Finset (Fin n)))
    (h : ∀ I ∈ M, C.eval I = false ∧ ∀ w ∉ I, C.eval (insert w I) = true) :
    M.card ≤ 2 ^ C.size := by
  have subset {I J : Finset (Fin n)} (hI : I ∈ M) (hJ : J ∈ M) (hc : cert C I = cert C J) : I ⊆ J := by
    intro w hw
    by_contra hout
    have cover : insert w J ⊆ I ∪ J := Finset.insert_subset (Finset.mem_union_left _ hw) Finset.subset_union_right
    have either := eval_cover C cover hc ((h J hJ).2 w hout)
    rw [(h I hI).1, (h J hJ).1] at either
    simp at either
  have inj : Function.Injective (fun I : ↥M => cert C I.val) := by
    intro I J eq
    exact Subtype.ext (Finset.Subset.antisymm (subset I.prop J.prop eq) (subset J.prop I.prop eq.symm))
  simpa using Fintype.card_le_of_injective _ inj

private def triangles : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private def pentagon : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  rightVars := ![{1, 4}, {1, 3}, {4}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private def heptagonCompl : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
  rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
  leftGates := ![∅, {0}, {1}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1, 2}

private def triangleSets : Finset (Finset (Fin 6)) :=
  {{0, 3}, {0, 4}, {0, 5}, {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 4}, {2, 5}}

private def pentagonSets : Finset (Finset (Fin 5)) :=
  {{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}}

private def heptagonSets : Finset (Finset (Fin 7)) :=
  {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 0}}

private abbrev Promise (G : SimpleGraph (Fin n)) (D : AndCountCircuit n) :=
  ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) → (∀ w ∉ I, ∃ a ∈ I, G.Adj a w) →
    D.eval I = false ∧ ∀ w ∉ I, D.eval (insert w I) = true

private lemma exact_size (G : SimpleGraph (Fin n)) (k : ℕ) (W : AndCountCircuit n)
    (M : Finset (Finset (Fin n))) (hw : W.WellFormed) (hs : W.size ≤ k + 1) (hp : Promise G W)
    (hM : ∀ I ∈ M, (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) ∧ (∀ w ∉ I, ∃ a ∈ I, G.Adj a w))
    (hcard : 2 ^ k < M.card) :
    (∃ D : AndCountCircuit n, D.WellFormed ∧ D.size ≤ k + 1 ∧ Promise G D) ∧
      ∀ D : AndCountCircuit n, D.WellFormed → Promise G D → k + 1 ≤ D.size := by
  refine ⟨⟨W, hw, hs, hp⟩, ?_⟩
  intro D _ hD
  have bound := count_bound D M fun I hI => hD I (hM I hI).1 (hM I hI).2
  by_contra! hlt
  exact (Nat.not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) (show D.size ≤ k by omega)))
    (hcard.trans_le bound)

end PEqualNP.Outside.L_meta_906

open PEqualNP.Outside.L_meta_906

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in

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
  refine ⟨?_, ?_, ?_⟩ <;> rintro G rfl
  all_goals first
    | apply exact_size _ 3 triangles triangleSets
    | apply exact_size _ 2 pentagon pentagonSets
    | apply exact_size _ 2 heptagonCompl heptagonSets
  all_goals try unfold PEqualNP.AndCount.AndCountCircuit.WellFormed
  all_goals decide
