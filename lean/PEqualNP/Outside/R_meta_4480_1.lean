import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Constant propagation removes every gate directly reading the fixed input.
-- This settles every leaf read by two gates; only single-use leaves remain.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4480_1
    (restrict : ∀ (n : ℕ) (C : Circuit) (v : Fin n), IsAO2 n C →
      (∃ x y : Fin n → Bool, circuitFun n C (Function.update x v false) ≠ circuitFun n C (Function.update y v false)) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size + (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length ≤ C.size ∧
        ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (Function.update x v false))
    (singleUse : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      let hit := fun (v : Fin (n+m)) (e : Fin n × Fin m) => Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
      let computes := fun (F : Finset (Fin n × Fin m)) (D : Circuit) => IsAO2 (n+m) D ∧ ∀ x, circuitFun (n+m) D x = decide (∃ e ∈ F, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)
      (∀ p q : Fin n, ∀ l k : Fin m, p ≠ q → l ≠ k → ¬ ((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) → computes E C → (∃ v, (E.filter (hit v)).card = 1) →
      (∀ v, (E.filter (hit v)).card = 1 → (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length ≤ 1) → ∃ t : Fin (n+m), let R := E.filter (fun e => ¬ hit t e); R.card < E.card ∧ (R = ∅ ∨ ∃ D : Circuit, computes R D ∧ D.size + (E.card-R.card)+1 ≤ C.size)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →     x6 x3 x4 →       (∃ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card = (1 : ℕ)) →         ∃ (x10 : Fin (x1 + x2)),           have x11 : Finset (Fin x1 × Fin x2) := {x11 ∈ x3 | ¬x5 x10 x11};           x11.card < x3.card ∧ (x11 = ∅ ∨ ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), x6 x11 x12 ∧ x12.size + (x3.card - x11.card) + (1 : ℕ) ≤ x4.size) := by
  classical
  intro n m E C
  let hit := fun (v : Fin (n+m)) (e : Fin n × Fin m) => Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
  let computes := fun (F : Finset (Fin n × Fin m)) (D : Circuit) => IsAO2 (n+m) D ∧ ∀ x, circuitFun (n+m) D x = decide (∃ e ∈ F, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)
  change (∀ p q : Fin n, ∀ l k : Fin m, p ≠ q → l ≠ k → ¬ ((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) → computes E C → (∃ v, (E.filter (hit v)).card = 1) → ∃ t : Fin (n+m), let R := E.filter (fun e => ¬ hit t e); R.card < E.card ∧ (R = ∅ ∨ ∃ D : Circuit, computes R D ∧ D.size + (E.card-R.card)+1 ≤ C.size)
  intro free correct leaf
  by_cases few : ∀ v, (E.filter (hit v)).card = 1 →
      (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length ≤ 1
  · exact singleUse n m E C free correct leaf few
  · push_neg at few
    obtain ⟨v,degree,reads⟩ := few
    let R := E.filter (fun e => ¬ hit v e)
    have partition : (E.filter (hit v)).card + R.card = E.card := by
      exact Finset.card_filter_add_card_filter_not (s := E) (p := hit v)
    refine ⟨v,?_,?_⟩
    · change R.card < E.card
      omega
    by_cases empty : R = ∅
    · exact Or.inl empty
    · right
      have restriction (x : Fin (n+m) → Bool) :
          circuitFun (n+m) C (Function.update x v false) =
          decide (∃ e ∈ R, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true) := by
        rw [correct.2]
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨e,he,hp,hl⟩
          have np : Fin.castAdd m e.1 ≠ v := by
            intro eq
            simp [eq] at hp
          have nl : Fin.natAdd n e.2 ≠ v := by
            intro eq
            simp [eq] at hl
          refine ⟨e,Finset.mem_filter.mpr ⟨he,?_⟩,?_,?_⟩
          · exact fun h => h.elim np nl
          · simpa only [Function.update_of_ne np] using hp
          · simpa only [Function.update_of_ne nl] using hl
        · rintro ⟨e,he,hp,hl⟩
          obtain ⟨he,miss⟩ := Finset.mem_filter.mp he
          have np : Fin.castAdd m e.1 ≠ v := fun h => miss (Or.inl h)
          have nl : Fin.natAdd n e.2 ≠ v := fun h => miss (Or.inr h)
          exact ⟨e,he,by simpa only [Function.update_of_ne np] using hp,
            by simpa only [Function.update_of_ne nl] using hl⟩
      have nonconstant : ∃ x y : Fin (n+m) → Bool,
          circuitFun (n+m) C (Function.update x v false) ≠
          circuitFun (n+m) C (Function.update y v false) := by
        refine ⟨fun _ => false,fun _ => true,?_⟩
        rw [restriction,restriction]
        have yes : (∃ e ∈ R, (fun _ : Fin (n+m) => true) (Fin.castAdd m e.1) = true ∧
            (fun _ : Fin (n+m) => true) (Fin.natAdd n e.2) = true) := by
          obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
          exact ⟨e,he,rfl,rfl⟩
        have trueEval : decide (∃ e ∈ R, (fun _ : Fin (n+m) => true) (Fin.castAdd m e.1) = true ∧
            (fun _ : Fin (n+m) => true) (Fin.natAdd n e.2) = true) = true := by
          simpa only [decide_eq_true_eq] using yes
        rw [trueEval]
        simp
      obtain ⟨D,valid,budget,eval⟩ := restrict (n+m) C v correct.1 nonconstant
      refine ⟨D,⟨valid,fun x => (eval x).trans (restriction x)⟩,?_⟩
      change D.size + (E.card-R.card)+1 ≤ C.size
      omega
