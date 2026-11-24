import Mathlib
import PEqualNP.Defs

-- Count the output as one read and each live binary gate as two reads.
-- Every active endpoint and every live gate must occur among the distinct wires.
-- Only edges and matching pairs beyond the endpoint count require repeated reads.
theorem PEqualNP.Outside.R_meta_2872_624
    (distinctWires : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ x : Fin (n + m) → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) C x =
          decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)) →
      let live := PEqualNP.FactorSubst.liveGates (n + m) C
      let reads := C.output :: live.toList.flatMap (fun i =>
        [PEqualNP.TopForm.opnd C i 0, PEqualNP.TopForm.opnd C i 1])
      (E.image Prod.fst).card + (E.image Prod.snd).card + live.card ≤ reads.toFinset.card)
    (repeatedReads : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ x : Fin (n + m) → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) C x =
          decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      let live := PEqualNP.FactorSubst.liveGates (n + m) C
      let reads := C.output :: live.toList.flatMap (fun i =>
        [PEqualNP.TopForm.opnd C i 0, PEqualNP.TopForm.opnd C i 1])
      E.card + M.card - ((E.image Prod.fst).card + (E.image Prod.snd).card) ≤
        reads.length - reads.toFinset.card) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m E M C hcycle hbinary hfun hsub hrow hcol
  let live := PEqualNP.FactorSubst.liveGates (n + m) C
  let ports := fun i => [PEqualNP.TopForm.opnd C i 0, PEqualNP.TopForm.opnd C i 1]
  let reads := C.output :: live.toList.flatMap ports
  let vertices := (E.image Prod.fst).card + (E.image Prod.snd).card
  have distinct : vertices + live.card ≤ reads.toFinset.card :=
    distinctWires n m E C hbinary hfun
  have repeated : E.card + M.card - vertices ≤ reads.length - reads.toFinset.card :=
    repeatedReads n m E M C hcycle hbinary hfun hsub hrow hcol
  have countPorts (xs : List ℕ) : (xs.flatMap ports).length = 2 * xs.length := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
        simp [List.flatMap_cons, ports] at ih ⊢
        omega
  have lengthReads : reads.length = 2 * live.card + 1 := by
    simp only [reads, List.length_cons, countPorts, Finset.length_toList]
  have liveBound : live.card ≤ C.size := by
    exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))
  have distinctBound : reads.toFinset.card ≤ reads.length := List.toFinset_card_le _
  omega
