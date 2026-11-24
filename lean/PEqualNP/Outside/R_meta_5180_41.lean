import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.TopForm

-- Count the incident pairs that have no accepting proof tree with each input read at most twice.
theorem PEqualNP.Outside.R_meta_5180_41
    (counting : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)),
      let sparse := fun (D : Circuit) => ∀ T : Finset (Fin (N+N)),
        (List.finRange N).countP (fun l => decide (Fin.natAdd N l ∈ T)) ≤ q →
        (IsPrimeImplicant (N+N) D T ↔ ∃ p l : Fin N, p ∈ L l ∧ T = {Fin.castAdd N p, Fin.natAdd N l})
      let exceptions := fun (D : Circuit) => (((List.finRange N).toFinset ×ˢ (List.finRange N).toFinset).filter (fun e : Fin N × Fin N =>
        e.1 ∈ L e.2 ∧ readsAtMost D (N+N) [e.1.val,N+e.2.val] 2 = false)).card
      200 ≤ q → N=q^2+q+1 → (∀ l, (L l).card=q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, p ∈ L l ∧ r ∈ L l) →
      ∀ C : Circuit, IsAO2 (N+N) C → sparse C → N*q ≤ 95*C.size + exceptions C)
    (normalize : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)),
      let sparse := fun (D : Circuit) => ∀ T : Finset (Fin (N+N)),
        (List.finRange N).countP (fun l => decide (Fin.natAdd N l ∈ T)) ≤ q →
        (IsPrimeImplicant (N+N) D T ↔ ∃ p l : Fin N, p ∈ L l ∧ T = {Fin.castAdd N p, Fin.natAdd N l})
      let exceptions := fun (D : Circuit) => (((List.finRange N).toFinset ×ˢ (List.finRange N).toFinset).filter (fun e : Fin N × Fin N =>
        e.1 ∈ L e.2 ∧ readsAtMost D (N+N) [e.1.val,N+e.2.val] 2 = false)).card
      200 ≤ q → N=q^2+q+1 → (∀ l, (L l).card=q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, p ∈ L l ∧ r ∈ L l) →
      ∀ C : Circuit, IsAO2 (N+N) C → ¬ IsReadK (N+N) C 2 → C.output < N+N+C.size → sparse C →
      5*C.size < exceptions C →
      ∃ D : Circuit, IsAO2 (N+N) D ∧ sparse D ∧ D.size ≤ C.size ∧ exceptions D ≤ 5*D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N L C qbig order lines unique ao nonread out correct
  let exceptions := fun (D : Circuit) => (((List.finRange N).toFinset ×ˢ (List.finRange N).toFinset).filter (fun e : Fin N × Fin N =>
        e.1 ∈ L e.2 ∧ readsAtMost D (N+N) [e.1.val,N+e.2.val] 2 = false)).card
  have count := counting q N L qbig order lines unique C ao correct
  change N*q ≤ 95*C.size + exceptions C at count
  by_cases low : exceptions C ≤ 5*C.size
  · omega
  · obtain ⟨D,aod,sd,sz,lowD⟩ := normalize q N L qbig order lines unique C ao nonread out correct (Nat.lt_of_not_ge low)
    have countD := counting q N L qbig order lines unique D aod sd
    change N*q ≤ 95*D.size + exceptions D at countD
    change exceptions D ≤ 5*D.size at lowD
    omega
