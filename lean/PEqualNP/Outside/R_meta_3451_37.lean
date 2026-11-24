import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_3451_37
    (mono : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ (x y : Fin n → Bool), (∀ k, x k = true → y k = true) →
    ∀ w, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true)
    (normal : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and → ∀ (x : Fin (N+N) → Bool),
        ((∃ p l, ¬ I p l ∧ ∀ k, x k = true ↔ k = Fin.castAdd N p ∨ k = Fin.natAdd N l) ∨
         (∃ p, (∀ l, I p l) ∧ ∀ k, x k = true ↔ k = Fin.castAdd N p) ∨
         (∃ l, (∀ p, I p l) ∧ ∀ k, x k = true ↔ k = Fin.natAdd N l)) →
        (D.wires (List.ofFn x)).getD (N+N+j) false = false) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  intro N I _ C four mc rb computes
  obtain ⟨D,md,rd,sz,ed,h⟩ := normal N I C four mc rb computes
  have pair (j) (hj : j < D.gates.length) (op : (NestedCover.gateAt D j).op = GateOp.and)
      (p l) (hn : ¬ I p l) := h j hj op (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
         (Or.inl ⟨p,l,hn,by simp⟩)
  refine ⟨D,md,rd,sz,ed,pair,?_⟩
  intro j hj op
  constructor
  · intro p
    by_cases hu : ∀ l, I p l
    · exact h j hj op _ (Or.inr (Or.inl ⟨p,hu,by simp⟩))
    push_neg at hu
    obtain ⟨l,hn⟩ := hu
    apply Bool.eq_false_iff.mpr
    intro hot
    have hp := mono _ D md _ (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
      (fun k hk => decide_eq_true (Or.inl (of_decide_eq_true hk))) _ hot
    rw [pair j hj op p l hn] at hp
    contradiction
  · intro l
    by_cases hu : ∀ p, I p l
    · exact h j hj op _ (Or.inr (Or.inr ⟨l,hu,by simp⟩))
    push_neg at hu
    obtain ⟨p,hn⟩ := hu
    apply Bool.eq_false_iff.mpr
    intro hot
    have hp := mono _ D md _ (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
      (fun k hk => decide_eq_true (Or.inr (of_decide_eq_true hk))) _ hot
    rw [pair j hj op p l hn] at hp
    contradiction
