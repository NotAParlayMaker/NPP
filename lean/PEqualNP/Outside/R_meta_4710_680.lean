import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_4710_680
    (count : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {p : Fin N // z (Fin.castAdd N p) = true} ≤ 2 →
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      let bad := Finset.univ.filter fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ readsAtMost C (N+N) [e.1.val,N+e.2.val] 2 = false
      N * (q+1) ≤ 94*C.size + 2*N + bad.card)
    (remaining : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit) (F : Finset ℕ),
      300 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ j ∈ F, j < C.size ∧ (gateAt C j).op = .and) →
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
        ∃ j ∈ F, gateVal (N+N) C j z = true) →
      (∀ p l, I p l → ∃ j ∈ F, gateVal (N+N) C j
        (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true) →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        ∀ j ∈ F, gateVal (N+N) C j z = false) →
      let bad := Finset.univ.filter fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ readsAtMost C (N+N) [e.1.val,N+e.2.val] 2 = false
      N*q < 20*bad.card → N*q ≤ 100*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset ℕ), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x14 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x14 ∧ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ x16 ∈ x6, x16 < x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x17 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x17 = Bool.true ↔ ∃ x18 ∈ x6, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x18 x17 = Bool.true) → (∀ (x18 x19 : Fin x2), x3 x18 x19 → ∃ x21 ∈ x6, (PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x21 fun (x22 : Fin (x2 + x2)) => Decidable.decide (x22 = Fin.castAdd x2 x18 ∨ x22 = Fin.natAdd x2 x19)) = Bool.true) → (∀ (x19 : Fin (x2 + x2) → Bool), Fintype.card { x20 : Fin x2 // x19 (Fin.natAdd x2 x20) = Bool.true } ≤ x1 → (¬∃ (x21 : Fin x2) (x22 : Fin x2), x3 x21 x22 ∧ x19 (Fin.castAdd x2 x21) = Bool.true ∧ x19 (Fin.natAdd x2 x22) = Bool.true) → ∀ x22 ∈ x6, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x22 x19 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I _ C F hq hN hdegree hmeet hmono _ _ _ ordered hF hcover covered sound
  have hback : ReadsBack (N+N) C := by
    intro i hi k hk
    have hgate : gateAt C i = C.gates[i] := List.getD_eq_getElem _ _ hi
    obtain ⟨a,b,hab,hlt,hb⟩ := ordered i C.gates[i] (List.getElem?_eq_getElem hi)
    rw [hgate,hab] at hk
    simp at hk
    rcases hk with rfl | rfl <;> omega
  have hao : IsAO2 (N+N) C := by
    refine ⟨fun g hg => ?_,hback,fun g hg => ?_⟩
    · have h := (hmono g hg).1
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
    · obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨a,b,hab,_,_⟩ := ordered i g hi
      simp [hab]
  let bad := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ readsAtMost C (N+N) [e.1.val,N+e.2.val] 2 = false
  by_cases heavy : N*q < 20*bad.card
  · exact remaining q N I C F hq hN hdegree hmeet hao hF hcover covered sound heavy
  · have robust (z : Fin (N+N) → Bool)
        (_hp : Fintype.card {p : Fin N // z (Fin.castAdd N p) = true} ≤ 2)
        (hl : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2)
        (hfree : ¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
        circuitFun (N+N) C z = false := by
      have hlines : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q :=
        hl.trans (by omega)
      cases h : circuitFun (N+N) C z
      · rfl
      · obtain ⟨j,hj,hval⟩ := (hcover z).mp h
        have hbad := sound z hlines hfree j hj
        rw [hval] at hbad
        cases hbad
    have bound : N*(q+1) ≤ 94*C.size + 2*N + bad.card := count q N I C hdegree hmeet hao robust
    have hqN : 100*N ≤ N*q := by
      rw [Nat.mul_comm 100 N]
      exact Nat.mul_le_mul_left N (by omega)
    rw [Nat.mul_add,Nat.mul_one] at bound
    omega
