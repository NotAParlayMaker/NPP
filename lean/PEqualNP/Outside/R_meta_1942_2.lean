import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1942_2
    (single : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      PEqualNP.ReadK.IsReadK (N + N) C 2 →
      (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
        (PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true ∨
         PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true))).card ≤ 66 * C.size)
    (double : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      PEqualNP.ReadK.IsReadK (N + N) C 2 →
      (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false)).card ≤ 34 * C.size) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size := by
  classical
  intro q N I _inst C hq hN hline huniq hao hfun hread
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let S : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ (PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true ∨
                  PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true))
  let D : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false)
  have hE_eq : E = (Finset.univ : Finset (Fin N)).biUnion
      (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    ext ⟨p, l⟩
    simp [E]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
      (fun l : Fin N => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    intro l1 _ l2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨p2, _, heq⟩ := Finset.mem_image.mp hx2
    exact hne (Prod.mk.inj heq).2.symm
  have hE_card : E.card = N * (q + 1) := by
    rw [hE_eq, Finset.card_biUnion hdisj]
    have hach : ∀ l : Fin N, ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card = q + 1 := by
      intro l
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), hline l]
    simp [hach]
  have hcover : E ⊆ S ∪ D := by
    intro e he
    have ei : I e.1 e.2 := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_union, S, D, Finset.mem_filter, Finset.mem_univ, true_and]
    cases h1 : PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) with
    | false =>
      cases h2 : PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) with
      | false => exact Or.inr ⟨ei, rfl, rfl⟩
      | true => exact Or.inl ⟨ei, Or.inr rfl⟩
    | true => exact Or.inl ⟨ei, Or.inl rfl⟩
  have b1 := single q N I C hq hN hline huniq hao hfun hread
  have b2 := double q N I C hq hN hline huniq hao hfun hread
  change S.card ≤ 66 * C.size at b1
  change D.card ≤ 34 * C.size at b2
  have hle : E.card ≤ S.card + D.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le S D)
  have hqle : N * q ≤ N * (q + 1) :=
    Nat.mul_le_mul_left N (Nat.le_succ q)
  rw [hE_card] at hle
  omega
