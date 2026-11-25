import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3451_77
    (closed : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C →
    (∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C x = true ↔ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
    (∀ p l : Fin N, I p l → ∃ j : ℕ, PEqualNP.CleanedNonEdge.OrReaches (N+N) C C.output j ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∃ b : Fin 2,
    Fin.castAdd N p ∈ PEqualNP.TopForm.side (n:=N+N) C j b ∧ Fin.natAdd N l ∈ PEqualNP.TopForm.side (n:=N+N) C j (1-b)) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) D ∧
    D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun (N+N) D = PEqualNP.MetaComplexity.circuitFun (N+N) C ∧
    ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = .and →
    ∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C x = false → (D.wires (List.ofFn x)).getD (N+N+j) false = false)
    (remaining : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p r l m : Fin N, p ≠ r → l ≠ m → ¬ (I p l ∧ I p m ∧ I r l ∧ I r m)) →
    PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C →
    (∀ x : Fin (N+N) → Bool, PEqualNP.MetaComplexity.circuitFun (N+N) C x = true ↔ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
    (∃ p l : Fin N, I p l ∧ ¬ (∃ j : ℕ, PEqualNP.CleanedNonEdge.OrReaches (N+N) C C.output j ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∃ b : Fin 2,
    Fin.castAdd N p ∈ PEqualNP.TopForm.side (n:=N+N) C j b ∧ Fin.natAdd N l ∈ PEqualNP.TopForm.side (n:=N+N) C j (1-b))) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) D ∧
    D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun (N+N) D = PEqualNP.MetaComplexity.circuitFun (N+N) C ∧
    ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = .and →
    ∀ p l : Fin N, ∀ x : Fin (N+N) → Bool, (∀ k, x k = true → k = Fin.castAdd N p ∨ k = Fin.natAdd N l) →
    PEqualNP.MetaComplexity.circuitFun (N+N) C x = false → (D.wires (List.ofFn x)).getD (N+N+j) false = false) :
  ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  intro N I inst C rect mon back spec
  let W : Prop := (∀ p l : Fin N, I p l → ∃ j : ℕ, PEqualNP.CleanedNonEdge.OrReaches (N+N) C C.output j ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∃ b : Fin 2,
    Fin.castAdd N p ∈ PEqualNP.TopForm.side (n:=N+N) C j b ∧ Fin.natAdd N l ∈ PEqualNP.TopForm.side (n:=N+N) C j (1-b))
  have candidate : ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) D ∧
    D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun (N+N) D = PEqualNP.MetaComplexity.circuitFun (N+N) C ∧
    ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = .and → ∀ p l : Fin N, ∀ x : Fin (N+N) → Bool, (∀ k, x k = true → k = Fin.castAdd N p ∨ k = Fin.natAdd N l) → PEqualNP.MetaComplexity.circuitFun (N+N) C x = false → (D.wires (List.ofFn x)).getD (N+N+j) false = false := by
    by_cases h : W
    · obtain ⟨D, m, r, size, fn, sound⟩ := closed N I C mon back spec h
      exact ⟨D,m,r,size,fn,fun j hj op _ _ x _ => sound j hj op x⟩
    · apply remaining N I C rect mon back spec
      simp only [W,not_forall,Classical.not_imp] at h
      obtain ⟨p,l,pl,miss⟩ := h
      exact ⟨p,l,pl,miss⟩
  obtain ⟨D, md, rd, size, eq, clean⟩ := candidate
  refine ⟨D,md,rd,size,?_,?_,?_⟩
  · intro x
    rw [eq]
    exact spec x
  all_goals
    have apart (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
      intro e
      have v := congrArg Fin.val e
      simp only [Fin.val_castAdd,Fin.val_natAdd] at v
      omega
    have neg (x : Fin (N+N) → Bool)
        (no : ¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) :
        PEqualNP.MetaComplexity.circuitFun (N+N) C x = false := by
      cases e : PEqualNP.MetaComplexity.circuitFun (N+N) C x with
      | false => rfl
      | true => exact (no ((spec x).mp e)).elim
  · intro j hj op p l non
    apply clean j hj op p l
    · intro k h; simpa only [decide_eq_true_eq] using h
    · apply neg
      rintro ⟨a,b,ab,ha,hb⟩
      simp only [decide_eq_true_eq] at ha hb
      rcases ha with h|h
      · have ap : a = p := by
          have v := congrArg Fin.val h
          exact Fin.ext v
        rcases hb with t|t
        · exact apart p b t.symm
        · have bl : b = l := by
            have v := congrArg Fin.val t
            exact Fin.ext (Nat.add_left_cancel v)
          exact non (ap ▸ bl ▸ ab)
      · exact apart a l h
  · intro j hj op
    constructor
    · intro p
      apply clean j hj op p p
      · intro k h; exact Or.inl (of_decide_eq_true h)
      · apply neg
        rintro ⟨a,b,ab,ha,hb⟩
        exact apart p b (of_decide_eq_true hb).symm
    · intro l
      apply clean j hj op l l
      · intro k h; exact Or.inr (of_decide_eq_true h)
      · apply neg
        rintro ⟨a,b,ab,ha,hb⟩
        exact apart a l (of_decide_eq_true ha)
