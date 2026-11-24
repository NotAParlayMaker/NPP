import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection
theorem PEqualNP.Outside.R_meta_2984_317
    (leaves : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
        200 ≤ q → N=q^2+q+1 → (∀ l, (S l).card=q+1) →
        (∀ a b : Fin N, a≠b → ∃! l, a∈S l ∧ b∈S l) →
        IsAO2 (N+N) C → C.output<N+N+C.size → RightOnIncidentPairs S C →
        (∀ X Y : Finset (Fin N), Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) →
        N*q ≤ (C.gates.foldl (fun w g => w++[(g.inputs.map fun i => w.getD i 0).sum]) (List.replicate (N+N) 1)).getD C.output 0)
    (count : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → C.output<n+C.size →
         let L := (C.gates.foldl (fun w g => w++[(g.inputs.map fun i => w.getD i 0).sum]) (List.replicate n 1)).getD C.output 0
         1<L → 100*C.size<L → ∃ t : Fin C.size, 100 ≤ (C.gates.foldl (fun w g => w++[(g.inputs.map fun i => w.getD i 0).sum +
               if w.length=n+t.val then 1 else 0]) (List.replicate n 0)).getD C.output 0)
    (shared : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
        200 ≤ q → N=q^2+q+1 → (∀ l, (S l).card=q+1) →
        (∀ a b : Fin N, a≠b → ∃! l, a∈S l ∧ b∈S l) →
        IsAO2 (N+N) C → C.output<N+N+C.size → RightOnIncidentPairs S C →
        (∀ X Y : Finset (Fin N), Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) →
        100*C.size < (C.gates.foldl (fun w g => w++[(g.inputs.map fun i => w.getD i 0).sum]) (List.replicate (N+N) 1)).getD C.output 0 → (∃ t : Fin C.size, 100 ≤ (C.gates.foldl (fun w g => w++[(g.inputs.map fun i => w.getD i 0).sum +
               if w.length=(N+N)+t.val then 1 else 0]) (List.replicate (N+N) 0)).getD C.output 0) → N*q≤100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq hN hline uniq ok out good sparse
  have floor := leaves q N S C hq hN hline uniq ok out good sparse
  by_cases high : 100*C.size < (C.gates.foldl (fun w g => w++[(g.inputs.map fun i => w.getD i 0).sum]) (List.replicate (N+N) 1)).getD C.output 0
  · have nontrivial : 1<N*q := by
      have hp : 0<N := by omega
      have := Nat.le_mul_of_pos_left q hp
      omega
    exact shared q N S C hq hN hline uniq ok out good sparse high
      (count (N+N) C ok out (lt_of_lt_of_le nontrivial floor) high)
  · exact floor.trans (Nat.le_of_not_gt high)
