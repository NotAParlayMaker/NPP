import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5066_677
    (layer : ∀ (m : ℕ) (C : Circuit), IsAO2 m C →
      let g := gateAt C
      (∀ i < C.size, ∀ j < C.size, (g i).op = .and → (g j).op = .and → ¬ InCone m C i j) →
      ∃ W : Finset ℕ,
        (∀ w ∈ W, w < m ∨ ∃ i < C.size, w = m+i ∧ (g i).op = .or ∧ ∀ u ∈ (g i).inputs, u ∈ W) ∧
        (∀ i < C.size, (g i).op = .and → ∀ u ∈ (g i).inputs, u ∈ W))
    (flat : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit) (W : Finset ℕ),
      let g := gateAt C
      (∀ p q l k, p ≠ q → l ≠ k → ¬ ((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) →
      (∀ p, (p,σ p) ∈ E) → IsAO2 (n+n) C →
      (∀ x, circuitFun (n+n) C x = decide (∃ p l, (p,l) ∈ E ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      (∀ w ∈ W, w < n+n ∨ ∃ i < C.size, w = n+n+i ∧
        (g i).op = .or ∧ ∀ u ∈ (g i).inputs, u ∈ W) →
      (∀ i < C.size, (g i).op = .and → ∀ u ∈ (g i).inputs, u ∈ W) →
      E.card + n ≤ C.size + 1)
    (nested : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit),
      let computes := fun D : Circuit =>
        ∀ x, circuitFun (n+n) D x = decide (∃ p l, (p,l) ∈ E ∧
          x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)
      n < E.card →
      (∀ p q l k, p ≠ q → l ≠ k → ¬ ((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) →
      (∀ p, (p,σ p) ∈ E) →
      ((∀ p, ∃ l, l ≠ σ p ∧ (p,l) ∈ E) ∧ ∀ l, ∃ p, σ p ≠ l ∧ (p,l) ∈ E) →
      IsAO2 (n+n) C → computes C →
      (∀ D, IsAO2 (n+n) D → computes D → C.size ≤ D.size) →
      (∃ i < C.size, ∃ j < C.size, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone (n+n) C i j) →
      E.card + n ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x12 ≠ x3 x11 ∧ (x11, x12) ∈ x2) ∧ ∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x3 x12 ≠ x11 ∧ (x12, x11) ∈ x2) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro n E σ C extra _ free matched model hcomp deg
  let computes (D : Circuit) : Prop :=
    ∀ x : Fin (n+n) → Bool, circuitFun (n+n) D x = decide (∃ p l, (p,l) ∈ E ∧
      x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)
  let admissible (s : ℕ) := ∃ D : Circuit, IsAO2 (n+n) D ∧ computes D ∧ D.size = s
  have existsSize : ∃ s, admissible s := ⟨C.size, C, model, hcomp, rfl⟩
  obtain ⟨D, hmodel, heval, leastSize⟩ := Nat.find_spec existsSize
  have least (B : Circuit) (hB : IsAO2 (n+n) B) (hE : computes B) : D.size ≤ B.size := by
    rw [leastSize]
    exact Nat.find_min' existsSize ⟨B, hB, hE, rfl⟩
  apply le_trans ?_ (Nat.add_le_add_right (least C model hcomp) 1)
  by_cases h : ∃ i < D.size, ∃ j < D.size, (gateAt D i).op = .and ∧
      (gateAt D j).op = .and ∧ InCone (n+n) D i j
  · exact nested n E σ D extra free matched deg hmodel heval least h
  · obtain ⟨W, closed, pins⟩ := layer (n+n) D hmodel
      (fun i hi j hj hgi hgj hc => h ⟨i,hi,j,hj,hgi,hgj,hc⟩)
    exact flat n E σ D W free matched hmodel heval closed pins
