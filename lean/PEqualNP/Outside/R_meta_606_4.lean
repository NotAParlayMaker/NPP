import PEqualNP.Defs

/-!
# R_meta_606_4: 606 reduced to `(junk G C).card ≤ 1`

606 asks for `c` with `G.edgeFinset.card ≤ c * (D.size + 1)` for every AND/OR circuit `D` of
fan-in at most two deciding the edge function of a graph whose cycles all have length at least
five.  The reduction below feeds:

* `L_meta_1733`: a least AND/OR circuit `C'` in top form, no larger than `D`, whose edges outside
  `Ustar G C'` are at most `C'.size + 1`;
* `L_meta_1766` (through its corollary `ustar_empty_of_junk_empty_606`): every edge of `Ustar` is
  supported by a junk AND gate, hence an empty junk set forces `Ustar = empty`;
* `L_meta_1878`: a singleton junk set bounds `Ustar` by `k * (C.size + 1)`;
* the one remaining local statement, kept in the hypotheses on purpose:
  `junk G C` has at most one element for a least circuit in top form.

Conclusion: 606 with `c = k + 1`.  The empty-junk branch is proved here, not assumed.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

/-- 606, reduced to the junk-cardinality statement. -/
theorem PEqualNP.Outside.R_meta_606_4
    (h1733 : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, Monotone2 C →
      circuitFun n C = (fun x : Fin n → Bool => decide
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ C' : Circuit, IsLeastAO G C' ∧ TopForm G C' ∧ C'.size ≤ C.size ∧
        (G.edgeFinset \ Ustar G C').card ≤ C'.size + 1)
    -- The empty-junk branch, stated without any local `def`: this is the corollary of
    -- `L_meta_1766` proved in `Outside/Ustar_empty_of_junk_empty_606.lean`.
    (hustar : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → TopForm G C → junk G C = ∅ → Ustar G C = ∅)
    (h1878 : ∃ k : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit) (g : Nat), IsLeastAO G C → TopForm G C → junk G C = {g} →
      (Ustar G C).card ≤ k * (C.size + 1))
    (hjunk1 : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (junk G C).card ≤ 1) :
    ∃ c : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨k, h1878⟩ := h1878
  refine ⟨k + 1, ?_⟩
  intro n G _ hg D hM hF
  rcases G.edgeFinset.eq_empty_or_nonempty with hE | hE
  · rw [hE]
    simp
  · obtain ⟨C', hL, hT, hsz, hcov⟩ := h1733 n G hg hE D hM hF
    have hle : (Ustar G C').card ≤ k * (C'.size + 1) := by
      rcases (junk G C').eq_empty_or_nonempty with h0 | hne
      · rw [hustar n G C' hL hT h0]
        simp
      · have hc1 : (junk G C').card = 1 := by
          have h1 : 0 < (junk G C').card := Finset.card_pos.2 hne
          have h2 : (junk G C').card ≤ 1 := hjunk1 n G hg hE C' hL hT
          omega
        obtain ⟨g, hg'⟩ := Finset.card_eq_one.1 hc1
        exact h1878 n G hg hE C' g hL hT hg'
    have hsub : Ustar G C' ⊆ G.edgeFinset := Finset.sdiff_subset
    have hpart : G.edgeFinset.card = (G.edgeFinset \ Ustar G C').card + (Ustar G C').card := by
      have := Finset.card_sdiff_add_card_eq_card hsub
      omega
    have h2 : (C'.size + 1) + k * (C'.size + 1) = (k + 1) * (C'.size + 1) := by ring
    have h3 : (k + 1) * (C'.size + 1) ≤ (k + 1) * (D.size + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega