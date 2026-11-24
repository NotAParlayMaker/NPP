import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4825_682
    (unroll : ∀ (m : ℕ) (C : Circuit), 0 < m → 0 < C.size → IsAO2 m C →
      C.output + 1 = m+C.size →
      (C.gates.flatMap Gate.inputs).toFinset = Finset.range (m+C.size-1) →
      (∀ j < C.size-1, (C.gates.flatMap Gate.inputs).count (m+j) = 1) →
      ∃ F : DMFormula m, F.leaves = C.size+1 ∧
        DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
          (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) F ∧
        ∀ x : Fin m → Bool, F.eval x = circuitFun m C x)
    (formulaSize : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (F : DMFormula (n+n)),
      (∀ p q l s, p ≠ q → l ≠ s →
         ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      (∀ p, (p,σ p) ∈ E) →
      DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
        (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) F →
      (∀ x, F.eval x = decide (∃ p l, (p,l) ∈ E ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      E.card + n ≤ F.leaves)
    (shared : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit),
      n < E.card → (∀ p q l s, p ≠ q → l ≠ s →
         ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      (∀ p, (p,σ p) ∈ E) → IsAO2 (n+n) C →
      (∀ x, circuitFun (n+n) C x = decide (∃ p l, (p,l) ∈ E ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      C.output + 1 = n+n+C.size →
      (C.gates.flatMap Gate.inputs).toFinset = Finset.range (n+n+C.size-1) →
      (∃ j < C.size-1, 1 < (C.gates.flatMap Gate.inputs).count (n+n+j)) →
      E.card-n ≤ (C.gates.flatMap Gate.inputs).length - (C.gates.flatMap Gate.inputs).toFinset.card) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x6 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x1), (x7, x8) ∈ x2 ∧ x6 (Fin.castAdd x1 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true);   x1 < x2.card → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → x5 x4 → x4.output + (1 : ℕ) = x1 + x1 + x4.size → (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).toFinset = Finset.range (x1 + x1 + x4.size - (1 : ℕ)) → x2.card - x1 ≤ (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).length - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates).toFinset.card := by
  classical
  intro n E σ C
  dsimp only
  intro hcard hrect hmatch hao hfun hlast hcover
  let L := C.gates.flatMap Gate.inputs
  have hL : L.toFinset = Finset.range (n+n+C.size-1) := hcover
  by_cases h : ∃ j < C.size-1, 1 < L.count (n+n+j)
  · exact shared n E σ C hcard hrect hmatch hao hfun hlast hcover h
  have hn : 0 < n := by
    by_contra! hn
    have hz : n = 0 := by omega
    subst n
    have he : E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun e _ => Fin.elim0 e.1)
    simp [he] at hcard
  have hs : 0 < C.size := by
    by_contra! hs
    have hg : C.gates = [] := List.length_eq_zero_iff.mp (show C.size = 0 by omega)
    have hmem : 0 ∈ L.toFinset := by
      rw [hL]
      exact Finset.mem_range.mpr (by omega)
    simp [L,hg] at hmem
  have linear (j : ℕ) (hj : j < C.size-1) : L.count (n+n+j) = 1 := by
    have hi : n+n+j ∈ L.toFinset := by
      rw [hL]
      exact Finset.mem_range.mpr (by omega)
    have positive := List.count_pos_iff.mpr (List.mem_toFinset.mp hi)
    have upper := Nat.not_lt.mp (fun hgt => h ⟨j,hj,hgt⟩)
    omega
  obtain ⟨F,hcost,hmono,hf⟩ := unroll (n+n) C (by omega) hs hao hlast hcover linear
  have bound := formulaSize n E σ F hrect hmatch hmono (fun x => (hf x).trans (hfun x))
  have hlen : L.length = 2*C.size := by
    change (C.gates.flatMap Gate.inputs).length = 2*C.gates.length
    rw [List.length_flatMap]
    have len : C.gates.map (fun g => g.inputs.length) = C.gates.map (fun _ => 2) :=
      List.map_congr_left (fun g hg => hao.2.2 g hg)
    rw [len]
    simp [Nat.mul_comm]
  change E.card-n ≤ L.length-L.toFinset.card
  rw [hlen,hL,Finset.card_range]
  omega
