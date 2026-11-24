import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.ReadTwo

-- A gate is required on an edge input if setting its value to false makes
-- the output false. A minimum-size circuit has such an input for each gate.
theorem PEqualNP.Outside.R_meta_3491_692
    (prune : ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (C : Circuit), ∀ j : Fin C.gates.length,
      let test := fun (j : ℕ) (p : Fin n) (l : Fin m) =>
        ((C.gates.zipIdx).foldl
          (fun w z => w ++ [if z.2 = j then false else z.1.op.eval (z.1.inputs.map fun k => w.getD k false)])
          (List.ofFn (pairInput (Fin.castAdd m p) (Fin.natAdd n l)))).getD C.output false
      IsAO2 (n+m) C → (∀ x : Fin (n+m) → Bool, circuitFun (n+m) C x =
        decide (∃ p l, R p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      (∀ p l, R p l → test j.val p l = true) →
      ∃ D : Circuit, IsAO2 (n+m) D ∧ D.size < C.size ∧ circuitFun (n+m) D = circuitFun (n+m) C)
    (count : ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (C : Circuit),
      let test := fun (j : ℕ) (p : Fin n) (l : Fin m) =>
        ((C.gates.zipIdx).foldl
          (fun w z => w ++ [if z.2 = j then false else z.1.op.eval (z.1.inputs.map fun k => w.getD k false)])
          (List.ofFn (pairInput (Fin.castAdd m p) (Fin.natAdd n l)))).getD C.output false
      (∀ p q l k, p ≠ q → l ≠ k → ¬ (R p l ∧ R p k ∧ R q l ∧ R q k)) →
      IsAO2 (n+m) C → (∀ x : Fin (n+m) → Bool, circuitFun (n+m) C x =
        decide (∃ p l, R p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      (∀ j : Fin C.gates.length, ∃ p l, R p l ∧ test j.val p l = false) →
      ∃ S : Finset (Fin (n+m)),
        (∀ p l, R p l → Fin.castAdd m p ∈ S ∨ Fin.natAdd n l ∈ S) ∧
        (incid R).card + S.card ≤ C.size + 1) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : Finset (Fin (x1 + x2))), (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 → Fin.castAdd x2 x10 ∈ x9 ∨ Fin.natAdd x1 x11 ∈ x9) ∧ (PEqualNP.ReadTwo.incid x3).card + x9.card ≤ x5.size + (1 : ℕ) := by
  intro n m R inst C noSquare model correct
  classical
  let P (k : ℕ) : Prop := ∃ D : Circuit, IsAO2 (n+m) D ∧
    circuitFun (n+m) D = circuitFun (n+m) C ∧ D.size = k
  have existsGood : ∃ k, P k := ⟨C.size,C,model,rfl,rfl⟩
  obtain ⟨D,hd,hdFun,hdSize⟩ := Nat.find_spec existsGood
  have minSize : D.size ≤ C.size := hdSize ▸ Nat.find_min' existsGood ⟨C,model,rfl,rfl⟩
  have funD (x : Fin (n+m) → Bool) : circuitFun (n+m) D x =
      decide (∃ p l, R p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) :=
    (congrFun hdFun x).trans (correct x)
  let test (j : ℕ) (p : Fin n) (l : Fin m) : Bool :=
    ((D.gates.zipIdx).foldl
      (fun w z => w ++ [if z.2 = j then false else z.1.op.eval (z.1.inputs.map fun k => w.getD k false)])
      (List.ofFn (pairInput (Fin.castAdd m p) (Fin.natAdd n l)))).getD D.output false
  have hasWitness (j : Fin D.gates.length) : ∃ p l, R p l ∧ test j.val p l = false := by
    by_contra missing
    have agrees (p : Fin n) (l : Fin m) (edge : R p l) : test j.val p l = true := by
      cases bit : test j.val p l with
      | true => rfl
      | false => exact (missing ⟨p,l,edge,bit⟩).elim
    obtain ⟨E,he,smaller,same⟩ := prune n m R D j hd funD agrees
    have optimal := Nat.find_min' existsGood (show P E.size from ⟨E,he,same.trans hdFun,rfl⟩)
    omega
  obtain ⟨S,covered,small⟩ := count n m R D noSquare hd funD hasWitness
  exact ⟨S,covered,by omega⟩
