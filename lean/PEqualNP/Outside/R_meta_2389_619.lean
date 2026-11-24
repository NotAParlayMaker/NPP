import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2389_619
    (witness : ∀ C : Circuit, IsAO2 26 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      C.size < 64 → ∃ D : Circuit, IsAO2 26 D ∧ circuitFun 26 D = circuitFun 26 C ∧
        (∀ E : Circuit, IsAO2 26 E → circuitFun 26 E = circuitFun 26 D → D.size ≤ E.size) ∧
        ∃ t : Fin 26, (t = 1 ∨ t = 15) ∧ ∃ k < D.size,
          (gateAt D k).op = GateOp.and ∧ gateVal 26 D k (pairInput 0 t) = true)
    (points : ∀ D : Circuit, IsAO2 26 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∀ E : Circuit, IsAO2 26 E → circuitFun 26 E = circuitFun 26 D → D.size ≤ E.size) →
      ∀ k < D.size, (gateAt D k).op = GateOp.and → gateVal 26 D k (pairInput 0 1) = true →
        (∀ i < k, (gateAt D i).op = GateOp.and → gateVal 26 D i (pairInput 0 1) = false) →
        64 ≤ D.size)
    (pointLine : ∀ D : Circuit, IsAO2 26 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∀ E : Circuit, IsAO2 26 E → circuitFun 26 E = circuitFun 26 D → D.size ≤ E.size) →
      ∀ k < D.size, (gateAt D k).op = GateOp.and → gateVal 26 D k (pairInput 0 15) = true →
        (∀ i < k, (gateAt D i).op = GateOp.and → gateVal 26 D i (pairInput 0 15) = false) →
        64 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  classical
  intro C ao correct
  by_contra! small
  obtain ⟨D,da,eq,minimal,t,which,k,hk,op,on⟩ := witness C ao correct small
  have cap : D.size ≤ C.size := minimal C ao eq.symm
  have df (x : Fin 26 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    have h := congrFun eq x
    change D.eval (List.ofFn x) = C.eval (List.ofFn x) at h
    rw [h]
    exact correct x
  let fires := fun j => j < D.size ∧ (gateAt D j).op = GateOp.and ∧
    gateVal 26 D j (pairInput 0 t) = true
  have anyFire : ∃ j, fires j := ⟨k,hk,op,on⟩
  obtain ⟨hj,hand,yes⟩ : fires (Nat.find anyFire) := Nat.find_spec anyFire
  have before (i : ℕ) (hi : i < Nat.find anyFire) (h : (gateAt D i).op = GateOp.and) :
      gateVal 26 D i (pairInput 0 t) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun hon => Nat.find_min anyFire hi ⟨by omega,h,hon⟩
  have lower : 64 ≤ D.size := by
    rcases which with rfl|rfl
    · exact points D da df minimal _ hj hand yes before
    · exact pointLine D da df minimal _ hj hand yes before
  omega
