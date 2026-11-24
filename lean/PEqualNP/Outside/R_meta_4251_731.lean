import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4251_731
    (positiveRows : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : List (List ℕ) := [[(0 : ℕ)], [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)], [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)], [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]];
    ∀ (x6 x7 : Fin 13), x6.val < 3 → x2 x6 x7 →
      ∃ r ∈ ([2101257,843841,29557249,34605057,2101258,4202514,1212546,51119106,4202516,25219108,2818308,34605060] : List ℕ),
        ∀ i : Fin 26, (x3.getD i.val []).any (fun j => (fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) (Fin.ofNat 26 j)) = r.testBit i.val)
    (negativeRows : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : List (List ℕ) := [[(0 : ℕ)], [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)], [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)], [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]];
    ∀ x6 : Finset (Fin 3),
      ∃ r ∈ ([67108856,67106225,67107682,28037411,67106508,52331653,30401094,7] : List ℕ),
        ∀ i : Fin 26, (x3.getD i.val []).any (fun j => (fun (x7 : Fin (26 : ℕ)) => Fin.addCases (motive := fun _ => Bool) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide ((3 : ℕ) ≤ ↑x8 ∨ ∃ x9 ∈ x6, Fin.castAdd (10 : ℕ) x9 = x8)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (∀ x9 ∈ x6, ¬x2 (Fin.castAdd (10 : ℕ) x9) x8)) x7) (Fin.ofNat 26 j)) = r.testBit i.val)
    (search : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 13 ∧
      (∀ r ∈ ([2101257,843841,29557249,34605057,2101258,4202514,1212546,51119106,4202516,25219108,2818308,34605060] : List ℕ), C.eval (List.ofFn fun i : Fin 26 => r.testBit i.val) = true) ∧
      (∀ r ∈ ([67108856,67106225,67107682,28037411,67106508,52331653,30401094,7] : List ℕ), C.eval (List.ofFn fun i : Fin 26 => r.testBit i.val) = false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : List (List ℕ) := [[(0 : ℕ)], [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)], [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)], [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]]; have x4 : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (26 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x6 : Fin (26 : ℕ)) => (x3.getD ↑x6 []).any fun (x7 : ℕ) => x5 (Fin.ofNat (26 : ℕ) x7); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ (13 : ℕ) ∧ (∀ (x6 x7 : Fin (13 : ℕ)), ↑x6 < (3 : ℕ) → x2 x6 x7 → (x4 x5 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x6 ∨ x10 = Fin.natAdd (13 : ℕ) x7)) = Bool.true) ∧ ∀ (x6 : Finset (Fin (3 : ℕ))), (x4 x5 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide ((3 : ℕ) ≤ ↑x8 ∨ ∃ x9 ∈ x6, Fin.castAdd (10 : ℕ) x9 = x8)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (∀ x9 ∈ x6, ¬x2 (Fin.castAdd (10 : ℕ) x9) x8)) x7) = Bool.false := by
  dsimp only at positiveRows negativeRows ⊢
  obtain ⟨C, fan, budget, positive, negative⟩ := search
  refine ⟨C, fan, budget, ?_, ?_⟩
  · intro p l bound incidence
    obtain ⟨r, hr, row⟩ := positiveRows p l bound incidence
    change C.eval (List.ofFn _) = true
    rw [funext row]
    exact positive r hr
  · intro S
    obtain ⟨r, hr, row⟩ := negativeRows S
    change C.eval (List.ofFn _) = false
    rw [funext row]
    exact negative r hr
