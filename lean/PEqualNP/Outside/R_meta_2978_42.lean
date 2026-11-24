import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2978_42
 (normal : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (R : List (List (Fin n) × List (Fin m))), (∀ r∈R, r.1≠[] ∧ r.2≠[]) → (∀ p l, I p l ↔ ∃ r∈R, p∈r.1 ∧ l∈r.2) →
 ∃ (D : Circuit) (P L : Finset ℕ), IsAO2 (n+m) D ∧ (∀ z, circuitFun (n+m) D z=(fun z : Fin (n+m) → Bool => decide (∃ p l, I p l ∧ z (Fin.castAdd m p)=true ∧ z (Fin.natAdd n l)=true)) z) ∧ D.size ≤ (R.map (fun r => r.1.length+r.2.length)).sum-1 ∧ (∀ w∈P, w<n ∨ ∃ j<D.gates.length, w=n+m+j ∧ (gateAt D j).op=GateOp.or ∧ ∀ a∈(gateAt D j).inputs, a∈P) ∧
 (∀ w∈L, (n≤w ∧ w<n+m) ∨ ∃ j<D.gates.length, w=n+m+j ∧ (gateAt D j).op=GateOp.or ∧ ∀ a∈(gateAt D j).inputs, a∈L) ∧
 (∀ j<D.gates.length, (gateAt D j).op=GateOp.and → ∃ a b, (gateAt D j).inputs=[a,b] ∧ a∈L ∧ b∈P))
 (stars : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I]
    (A : Finset (Fin n)) (B : Finset (Fin m)) (cover : ∀ p l, I p l → p∈A ∨ l∈B), ∃ R : List (List (Fin n) × List (Fin m)),
      (∀ r∈R, r.1≠[] ∧ r.2≠[]) ∧
      (∀ p l, I p l ↔ ∃ r∈R, p∈r.1 ∧ l∈r.2) ∧
      (R.map (fun r => r.1.length+r.2.length)).sum ≤
        Fintype.card {e : Fin n × Fin m // I e.1 e.2} + A.card + B.card)
 (safe : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
 (∀ a b l r, a≠b → l≠r → ¬(I a l ∧ I a r ∧ I b l ∧ I b r)) →
 IsAO2 (n+m) C → (∀ z, circuitFun (n+m) C z=(fun z : Fin (n+m) → Bool => decide (∃ p l, I p l ∧ z (Fin.castAdd m p)=true ∧ z (Fin.natAdd n l)=true)) z) → (∀ j < C.gates.length, (gateAt C j).op=GateOp.and → ∀ z : Fin (n+m) → Bool,
 PEqualNP.EdgeOwnership.gateVal (n+m) C j z=true → ∃ p l, I p l ∧ z (Fin.castAdd m p)=true ∧ z (Fin.natAdd n l)=true) → ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ p l, I p l → p∈A ∨ l∈B) ∧ Fintype.card {e : Fin n × Fin m // I e.1 e.2}+A.card+B.card≤C.size+1)
 (remaining : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
 (∀ a b l r, a≠b → l≠r → ¬(I a l ∧ I a r ∧ I b l ∧ I b r)) →
 IsAO2 (n+m) C → (∀ z, circuitFun (n+m) C z=(fun z : Fin (n+m) → Bool => decide (∃ p l, I p l ∧ z (Fin.castAdd m p)=true ∧ z (Fin.natAdd n l)=true)) z) → (∀ E : Circuit, IsAO2 (n+m) E → (∀ z, circuitFun (n+m) E z=circuitFun (n+m) C z) → C.size≤E.size) → (∃ j < C.gates.length, (gateAt C j).op=GateOp.and ∧ ∃ z : Fin (n+m) → Bool,
 PEqualNP.EdgeOwnership.gateVal (n+m) C j z=true ∧ ¬∃ p l, I p l ∧ z (Fin.castAdd m p)=true ∧ z (Fin.natAdd n l)=true) → ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ p l, I p l → p∈A ∨ l∈B) ∧ Fintype.card {e : Fin n × Fin m // I e.1 e.2}+A.card+B.card≤C.size+1) :
∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10 := by
  classical
  intro n m I inst C square ao correct
  let target := fun z : Fin (n+m) → Bool => decide (∃ p l, I p l ∧ z (Fin.castAdd m p)=true ∧ z (Fin.natAdd n l)=true)
  let existsOf := fun s : ℕ => ∃ D : Circuit, IsAO2 (n+m) D ∧ (∀ z, circuitFun (n+m) D z=target z) ∧ D.size=s
  have candidate : ∃ s, existsOf s := ⟨C.size,C,ao,correct,rfl⟩
  obtain ⟨K,ko,kf,ks⟩ := Nat.find_spec candidate
  have cheaper : K.size≤C.size := ks ▸ Nat.find_min' candidate (show existsOf C.size from ⟨C,ao,correct,rfl⟩)
  have least (E : Circuit) (ae : IsAO2 (n+m) E) (fe : ∀ z, circuitFun (n+m) E z=circuitFun (n+m) K z) :
      K.size≤E.size := by
    rw [ks]
    exact Nat.find_min' candidate (show existsOf E.size from ⟨E,ae,fun z => (fe z).trans (kf z),rfl⟩)
  have card : ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ p l, I p l → p∈A ∨ l∈B) ∧ Fintype.card {e : Fin n × Fin m // I e.1 e.2}+A.card+B.card≤K.size+1 := by
    by_cases ok : ∀ j < K.gates.length, (gateAt K j).op=GateOp.and → ∀ z : Fin (n+m) → Bool,
 PEqualNP.EdgeOwnership.gateVal (n+m) K j z=true → ∃ p l, I p l ∧ z (Fin.castAdd m p)=true ∧ z (Fin.natAdd n l)=true
    · exact safe n m I K square ko kf ok
    · apply remaining n m I K square ko kf least
      push Not at ok
      obtain ⟨j,hj,op,z,hz,fail⟩ := ok
      exact ⟨j,hj,op,z,hz,by simpa using fail⟩
  obtain ⟨A,B,cover,size⟩ := card
  obtain ⟨R,good,rep,price⟩ := stars n m I A B cover
  obtain ⟨D,P,L,ok,sem,small,rest⟩ := normal n m I R good rep
  exact ⟨D,P,L,ok,sem,by omega,rest⟩
