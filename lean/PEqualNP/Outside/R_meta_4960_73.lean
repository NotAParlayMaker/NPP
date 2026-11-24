import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- An edge meeting at most one other edge lies at the end of a path or is isolated.
-- An unmatched leaf can also be removed. Each removal pays for the lost incidences and matches.
-- The square-root error is used only once, on the residual graph.
theorem PEqualNP.Outside.R_meta_4960_73
    (peel : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      (∃ e ∈ E,
        (E.filter (fun f => e.1 = f.1 ∨ e.2 = f.2)).card ≤ 2 ∨
        e ∉ M ∧ ((∀ f ∈ E, e.1 = f.1 → e = f) ∨ (∀ f ∈ E, e.2 = f.2 → e = f))) →
      (IsAO2 (n + m) C ∧ ∀ x, circuitFun (n + m) C x = decide
        (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) → (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      E.card + M.card ≤ C.size + 1 ∨
        ∃ (F : Finset (Fin n × Fin m)) (D : Circuit), F ⊂ E ∧
          (IsAO2 (n + m) D ∧ ∀ x, circuitFun (n + m) D x = decide
        (∃ p l, (p, l) ∈ F ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) ∧
          E.card + M.card + D.size ≤ F.card + (M ∩ F).card + C.size)
    (core : ∃ K : ℕ, ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ e ∈ E,
        3 ≤ (E.filter (fun f => e.1 = f.1 ∨ e.2 = f.2)).card ∧
        (((∀ f ∈ E, e.1 = f.1 → e = f) ∨ (∀ f ∈ E, e.2 = f.2 → e = f)) → e ∈ M)) →
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p, l) ∈ E ∧ (p, s) ∈ E ∧ (q, l) ∈ E ∧ (q, s) ∈ E)) →
      (IsAO2 (n + m) C ∧ ∀ x, circuitFun (n + m) C x = decide
        (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) → (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      E.card + M.card ≤ C.size + 1 + K * (n + m + 1).sqrt) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 x5 : Finset (Fin x2 × Fin x3)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x7 x8 : Fin x2) (x9 x10 : Fin x3), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x4 ∧ (x7, x10) ∈ x4 ∧ (x8, x9) ∈ x4 ∧ (x8, x10) ∈ x4)) → PEqualNP.TopForm.IsAO2 (x2 + x3) x6 → (∀ (x9 : Fin (x2 + x3) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x3) x6 x9 = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x3), (x10, x11) ∈ x4 ∧ x9 (Fin.castAdd x3 x10) = Bool.true ∧ x9 (Fin.natAdd x2 x11) = Bool.true)) → x5 ⊆ x4 → (∀ x11 ∈ x5, ∀ x13 ∈ x5, x11.1 = x13.1 → x11 = x13) → (∀ x12 ∈ x5, ∀ x14 ∈ x5, x12.2 = x14.2 → x12 = x14) → x4.card + x5.card ≤ x6.size + (1 : ℕ) + x1 * (x2 + x3 + (1 : ℕ)).sqrt := by
  classical
  obtain ⟨K, bound⟩ := core
  refine ⟨K, ?_⟩
  intro n m E M C square ao computes subset left right
  have go (k : ℕ) : ∀ (E M : Finset (Fin n × Fin m)) (C : Circuit),
    E.card = k → (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p, l) ∈ E ∧ (p, s) ∈ E ∧ (q, l) ∈ E ∧ (q, s) ∈ E)) →
    (IsAO2 (n + m) C ∧ ∀ x, circuitFun (n + m) C x = decide
        (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
    M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) → (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
    E.card + M.card ≤ C.size + 1 + K * (n + m + 1).sqrt := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro E M C size noSquare correct sub row col
      by_cases tip : ∃ e ∈ E,
          (E.filter (fun f => e.1 = f.1 ∨ e.2 = f.2)).card ≤ 2 ∨
          e ∉ M ∧ ((∀ f ∈ E, e.1 = f.1 → e = f) ∨ (∀ f ∈ E, e.2 = f.2 → e = f))
      · rcases peel n m E M C tip correct sub row col with done | ⟨F, D, strict, sem, cost⟩
        · omega
        have inside := Finset.ssubset_iff_subset_ne.mp strict |>.1
        have smaller : F.card < k := size ▸ Finset.card_lt_card strict
        have remain := ih F.card smaller F (M ∩ F) D rfl
          (fun p q l s pq ls four =>
            noSquare p q l s pq ls
              ⟨inside four.1, inside four.2.1, inside four.2.2.1, inside four.2.2.2⟩)
          sem Finset.inter_subset_right
          (fun e he f hf => row e (Finset.mem_inter.mp he).1 f (Finset.mem_inter.mp hf).1)
          (fun e he f hf => col e (Finset.mem_inter.mp he).1 f (Finset.mem_inter.mp hf).1)
        omega
      · apply bound n m E M C _ noSquare correct sub row col
        intro e he
        constructor
        · by_contra! h
          exact tip ⟨e, he, Or.inl (by omega)⟩
        · intro exclusive
          by_contra unmatched
          exact tip ⟨e, he, Or.inr ⟨unmatched, exclusive⟩⟩
  exact go _ E M C rfl square ⟨ao, computes⟩ subset left right
