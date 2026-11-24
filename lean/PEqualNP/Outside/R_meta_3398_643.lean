import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3398_643
  (connectedCore : ∀ (n m : ℕ) (E F M : Finset (Fin n × Fin m)) (C : Circuit),
  let squareFree := fun E : Finset (Fin n × Fin m) =>
    ∀ p q : Fin n, ∀ l t : Fin m, p ≠ q → l ≠ t →
      ¬ ((p,l) ∈ E ∧ (p,t) ∈ E ∧ (q,l) ∈ E ∧ (q,t) ∈ E)
  let leaf := fun E (e : Fin n × Fin m) =>
    (∀ d ∈ E, d.1 = e.1 → d = e) ∨ (∀ d ∈ E, d.2 = e.2 → d = e)
  let connected := fun F : Finset (Fin n × Fin m) =>
    ∀ e ∈ F, ∀ d ∈ F, Relation.ReflTransGen
      (fun a b : Fin n × Fin m => a ∈ F ∧ b ∈ F ∧ (a.1 = b.1 ∨ a.2 = b.2)) e d
  let edgeFun := fun F (z : Fin (n+m) → Bool) =>
    decide (∃ p l, (p,l) ∈ F ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)
  squareFree E → F ⊆ E → connected F → M ⊆ F →
  (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) → (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
  (∀ e ∈ F, leaf E e → e ∈ M) → IsAO2 (n+m) C →
  (∀ z, circuitFun (n+m) C z = edgeFun F z) → F.card + M.card ≤ C.size + 1)
  (componentBridge : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
  let leaf := fun E (e : Fin n × Fin m) =>
    (∀ d ∈ E, d.1 = e.1 → d = e) ∨ (∀ d ∈ E, d.2 = e.2 → d = e)
  let connected := fun F : Finset (Fin n × Fin m) =>
    ∀ e ∈ F, ∀ d ∈ F, Relation.ReflTransGen
      (fun a b : Fin n × Fin m => a ∈ F ∧ b ∈ F ∧ (a.1 = b.1 ∨ a.2 = b.2)) e d
  let edgeFun := fun F (z : Fin (n+m) → Bool) =>
    decide (∃ p l, (p,l) ∈ F ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)
  (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) → (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) → M ⊆ E →
  (∀ e ∈ E, leaf E e → e ∈ M) → IsAO2 (n+m) C → (∀ z, circuitFun (n+m) C z = edgeFun E z) →
  ∃ (k : ℕ) (Es Ms : Fin k → Finset (Fin n × Fin m)) (Cs : Fin k → Circuit),
    (∀ i, Es i ⊆ E ∧ connected (Es i) ∧ Ms i ⊆ Es i ∧
      (∀ e ∈ Ms i, ∀ d ∈ Ms i, e.1 = d.1 → e = d) ∧
      (∀ e ∈ Ms i, ∀ d ∈ Ms i, e.2 = d.2 → e = d) ∧
      (∀ e ∈ Es i, leaf E e → e ∈ Ms i) ∧ IsAO2 (n+m) (Cs i) ∧
      (∀ z, circuitFun (n+m) (Cs i) z = edgeFun (Es i) z)) ∧
    E.card = ∑ i, (Es i).card ∧ M.card = ∑ i, (Ms i).card ∧
    (∑ i : Fin k, ((Cs i).size + 1)) ≤ C.size + 1)
 :
  ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →     PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →       (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →         x4 ⊆ x3 →           (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →             (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →               have x12 : Fin x1 × Fin x2 → Prop := fun (x12 : Fin x1 × Fin x2) => (∀ x13 ∈ x3, x13.1 = x12.1 → x13 = x12) ∨ ∀ x13 ∈ x3, x13.2 = x12.2 → x13 = x12;               (∀ x13 ∈ x3, x12 x13 → x13 ∈ x4) → (∃ x14 ∈ x4, x12 x14) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m E M C hsq hAO hEval hSub hMatchP hMatchL x12 hLeaf _hSome
  obtain ⟨k, Es, Ms, Cs, hparts, hEcard, hMcard, hcost⟩ :=
    componentBridge n m E M C hMatchP hMatchL hSub hLeaf hAO hEval
  have hlocal : ∀ i : Fin k, (Es i).card + (Ms i).card ≤ (Cs i).size + 1 := by
    intro i
    rcases hparts i with ⟨hEi, hconn, hMi, hmp, hml, hleaf, hAOi, hEvali⟩
    exact connectedCore n m E (Es i) (Ms i) (Cs i) hsq hEi hconn hMi hmp hml hleaf hAOi hEvali
  have hsum : (∑ i : Fin k, ((Es i).card + (Ms i).card)) ≤
      ∑ i : Fin k, ((Cs i).size + 1) :=
    Finset.sum_le_sum (fun i _ => hlocal i)
  calc
    E.card + M.card = ∑ i : Fin k, ((Es i).card + (Ms i).card) := by
      calc
        E.card + M.card = (∑ i : Fin k, (Es i).card) + (∑ i : Fin k, (Ms i).card) := by
          rw [hEcard, hMcard]
        _ = ∑ i : Fin k, ((Es i).card + (Ms i).card) := Finset.sum_add_distrib.symm
    _ ≤ ∑ i : Fin k, ((Cs i).size + 1) := hsum
    _ ≤ C.size + 1 := hcost
