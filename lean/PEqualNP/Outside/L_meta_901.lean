import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_901_aux

open PEqualNP.AndCount AndCountCircuit

def bic (n k : ℕ) (X Y : Fin k → Finset (Fin n)) : AndCountCircuit n where
  size := k
  leftVars := X
  leftGates _ := ∅
  rightVars := Y
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

theorem bic_gate (n k : ℕ) (X Y : Fin k → Finset (Fin n)) (U : Finset (Fin n)) (i : Fin k) :
    (bic n k X Y).gateVal U i = true ↔ (∃ v ∈ X i, v ∈ U) ∧ (∃ v ∈ Y i, v ∈ U) := by
  obtain ⟨m, h⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  unfold gateVal
  change gateValFuel (bic n k X Y) U k i = true ↔ _
  rw [congrArg (fun d => (bic n k X Y).gateValFuel U d i) h]
  simp only [gateValFuel, sideTrue, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ha | ⟨j, hj, _⟩, hb | ⟨l, hl, _⟩⟩
    · exact ⟨ha, hb⟩
    · exact (Finset.notMem_empty l hl).elim
    · exact (Finset.notMem_empty j hj).elim
    · exact (Finset.notMem_empty j hj).elim
  · exact fun ⟨ha, hb⟩ => ⟨Or.inl ha, Or.inl hb⟩

theorem bic_eval (n k : ℕ) (X Y : Fin k → Finset (Fin n)) (U : Finset (Fin n)) :
    (bic n k X Y).eval U = true ↔ ∃ i : Fin k, (∃ v ∈ X i, v ∈ U) ∧ (∃ v ∈ Y i, v ∈ U) := by
  unfold eval
  rw [decide_eq_true_eq]
  constructor
  · rintro (⟨v, hv, _⟩ | ⟨i, _, hi⟩)
    · exact (Finset.notMem_empty v hv).elim
    · exact ⟨i, (bic_gate n k X Y U i).mp hi⟩
  · rintro ⟨i, hi⟩
    exact Or.inr ⟨i, Finset.mem_univ _, (bic_gate n k X Y U i).mpr hi⟩

end PEqualNP.Outside.L_meta_901_aux

open PEqualNP.Outside.L_meta_901_aux

theorem PEqualNP.Outside.L_meta_901 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (X Y : Fin k → Finset (Fin n)),
  (∀ i : Fin k, ∀ x ∈ X i, ∀ y ∈ Y i, G.Adj x y) →
  (∀ a b : Fin n, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (a ∈ Y i ∧ b ∈ X i)) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed ∧ C.size ≤ k ∧
    ∀ I : Finset (Fin n),
      ((∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) ∧ (∀ u : Fin n, u ∉ I → ∃ a ∈ I, G.Adj u a)) →
      C.eval I = false ∧ ∀ u : Fin n, u ∉ I → C.eval (insert u I) = true := by
  intro n G k X Y hbi hcov
  refine ⟨bic n k X Y, ?_, le_refl _, ?_⟩
  · intro i
    constructor <;> intro j hj <;> exact (Finset.notMem_empty j hj).elim
  · rintro I ⟨hind, hmax⟩
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨i, ⟨x, hx, hxI⟩, ⟨y, hy, hyI⟩⟩ := (bic_eval n k X Y I).mp h
      exact hind x hxI y hyI (hbi i x hx y hy)
    · intro u hu
      obtain ⟨a, ha, hua⟩ := hmax u hu
      obtain ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hcov u a hua
      · exact (bic_eval n k X Y _).mpr
          ⟨i, ⟨u, h1, Finset.mem_insert_self _ _⟩, ⟨a, h2, Finset.mem_insert_of_mem ha⟩⟩
      · exact (bic_eval n k X Y _).mpr
          ⟨i, ⟨a, h2, Finset.mem_insert_of_mem ha⟩, ⟨u, h1, Finset.mem_insert_self _ _⟩⟩
