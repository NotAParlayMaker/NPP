import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

-- Reduce L-meta-606 to four obligations:
-- (1) normalizing non-constant fan-in-two monotone circuits into strict fan-in-two DAGs,
-- (2) bounding girth-5 edges having a read-1 proof tree,
-- (3) bounding girth-5 edges whose minimum proof tree reads an endpoint twice, and
-- (4) bounding remaining girth-5 edges requiring at least three reads of an endpoint.
theorem PEqualNP.Outside.R_meta_606_5
    (normalize : ∀ (n : ℕ) (D : Circuit), Monotone2 D →
      (∃ x y : Fin n → Bool, circuitFun n D x ≠ circuitFun n D y) →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size ∧ circuitFun n C = circuitFun n D ∧
        C.output < n + C.size ∧
        ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j)
    (boundRead1 : ∃ c₁ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      C.output < n + C.size →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j) →
      circuitFun n C = (fun x : Fin n → Bool =>
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (G.edgeFinset.filter (fun e : Sym2 (Fin n) =>
        ∃ u v : Fin n, e = s(u, v) ∧ u < v ∧
          readsAtMost C n [u.val, v.val] 1 = true)).card ≤ c₁ * (C.size + 1))
    (boundRead2 : ∃ c₂ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      C.output < n + C.size →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j) →
      circuitFun n C = (fun x : Fin n → Bool =>
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (G.edgeFinset.filter (fun e : Sym2 (Fin n) =>
        ∃ u v : Fin n, e = s(u, v) ∧ u < v ∧
          readsAtMost C n [u.val, v.val] 1 = false ∧
          readsAtMost C n [u.val, v.val] 2 = true)).card ≤ c₂ * (C.size + 1))
    (boundRead3 : ∃ c₃ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      C.output < n + C.size →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j) →
      circuitFun n C = (fun x : Fin n → Bool =>
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (G.edgeFinset.filter (fun e : Sym2 (Fin n) =>
        ∃ u v : Fin n, e = s(u, v) ∧ u < v ∧
          readsAtMost C n [u.val, v.val] 2 = false)).card ≤ c₃ * (C.size + 1)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨c₁, h₁⟩ := boundRead1
  obtain ⟨c₂, h₂⟩ := boundRead2
  obtain ⟨c₃, h₃⟩ := boundRead3
  refine ⟨c₁ + c₂ + c₃, ?_⟩
  intro n G _ hG D hD hFun
  by_cases hEmpty : G.edgeFinset.Nonempty
  · obtain ⟨e0, he0⟩ := hEmpty
    induction e0 using Sym2.ind with
    | _ a0 b0 =>
      have hadj0 : G.Adj a0 b0 := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he0
      have hneq : ∃ x y : Fin n → Bool, circuitFun n D x ≠ circuitFun n D y := by
        refine ⟨fun _ => false, fun k => decide (k = a0 ∨ k = b0), ?_⟩
        rw [hFun]
        intro heq
        have h0 : decide (∃ i j : Fin n, G.Adj i j ∧ false = true ∧ false = true) = false := by
          simp
        have h1e : decide (∃ i j : Fin n, G.Adj i j ∧ decide (i = a0 ∨ i = b0) = true ∧
            decide (j = a0 ∨ j = b0) = true) = true := by
          simp only [decide_eq_true_eq]
          exact ⟨a0, b0, hadj0, Or.inl rfl, Or.inr rfl⟩
        dsimp only at heq
        rw [h0, h1e] at heq
        exact Bool.false_ne_true heq
      obtain ⟨C, hCmono, hCsize, hCfun, hCout, hCdag⟩ := normalize n D hD hneq
      have hCeq : circuitFun n C = (fun x : Fin n → Bool =>
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) :=
        hCfun.trans hFun
      let S₁ := G.edgeFinset.filter (fun e : Sym2 (Fin n) =>
        ∃ u v : Fin n, e = s(u, v) ∧ u < v ∧ readsAtMost C n [u.val, v.val] 1 = true)
      let S₂ := G.edgeFinset.filter (fun e : Sym2 (Fin n) =>
        ∃ u v : Fin n, e = s(u, v) ∧ u < v ∧
          readsAtMost C n [u.val, v.val] 1 = false ∧ readsAtMost C n [u.val, v.val] 2 = true)
      let S₃ := G.edgeFinset.filter (fun e : Sym2 (Fin n) =>
        ∃ u v : Fin n, e = s(u, v) ∧ u < v ∧ readsAtMost C n [u.val, v.val] 2 = false)
      have hb1 : S₁.card ≤ c₁ * (C.size + 1) := h₁ n G hG C hCmono hCout hCdag hCeq
      have hb2 : S₂.card ≤ c₂ * (C.size + 1) := h₂ n G hG C hCmono hCout hCdag hCeq
      have hb3 : S₃.card ≤ c₃ * (C.size + 1) := h₃ n G hG C hCmono hCout hCdag hCeq
      have hsub : G.edgeFinset ⊆ S₁ ∪ S₂ ∪ S₃ := by
        intro e he
        induction e using Sym2.ind with
        | _ a b =>
          have he' := he
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he'
          have hne : a ≠ b := G.ne_of_adj he'
          obtain ⟨u, v, huv, hlt⟩ : ∃ u v : Fin n, s(a, b) = s(u, v) ∧ u < v := by
            rcases lt_or_gt_of_ne hne with hlt | hlt
            · exact ⟨a, b, rfl, hlt⟩
            · exact ⟨b, a, Sym2.eq_swap, hlt⟩
          cases hr1 : readsAtMost C n [u.val, v.val] 1 with
          | true =>
            exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨he, u, v, huv, hlt, hr1⟩))
          | false =>
            cases hr2 : readsAtMost C n [u.val, v.val] 2 with
            | true =>
              exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_filter.mpr ⟨he, u, v, huv, hlt, hr1, hr2⟩))
            | false =>
              exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, v, huv, hlt, hr2⟩)
      have hcard : G.edgeFinset.card ≤ S₁.card + S₂.card + S₃.card :=
        (Finset.card_le_card hsub).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hsum : S₁.card + S₂.card + S₃.card ≤ (c₁ + c₂ + c₃) * (C.size + 1) := by
        rw [Nat.add_mul, Nat.add_mul]
        exact Nat.add_le_add (Nat.add_le_add hb1 hb2) hb3
      exact hcard.trans (hsum.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hCsize)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hEmpty, Finset.card_empty]
    exact Nat.zero_le _
