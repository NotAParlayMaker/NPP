import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Reduce the rung-0 target L-meta-1629 to two obligations:
  (1) a general linear sensitivity bound for monotone circuits
      (every coordinate sensitive implies `n ≤ C.size + 1`), which
      closes the case `q ≤ 100` for this circuit; and
  (2) the target itself restricted to `100 < q`.
  The `q ≤ 100` case is proved inline: every input coordinate of this
  circuit is sensitive (a 2-hot incident input versus the 1-hot input
  obtained by switching one of its two wires off), so the sensitivity
  bound gives `2N ≤ C.size + 1`, and `N * q ≤ 100 * C.size` follows
  for `q ≤ 100` by arithmetic. -/
theorem PEqualNP.Outside.R_meta_1629_4
    (h_sens : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∀ k : Fin n, ∃ x y : Fin n → Bool, (∀ j : Fin n, j ≠ k → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) →
      n ≤ C.size + 1)
    (h_large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      N * q ≤ 100 * C.size) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      N * q ≤ 100 * C.size := by
  intro q N I inst C hq hN hcard hline hmono hacc hsound
  by_cases hq100 : q ≤ 100
  · -- Sensitivity route for `q ≤ 100`.
    have hNpos : 7 ≤ N := by
      have hq2 : 4 ≤ q ^ 2 := by
        have h := Nat.mul_le_mul hq hq
        rw [pow_two]
        exact h
      omega
    have hpoint_line : ∀ p : Fin N, ∃ l : Fin N, I p l := by
      intro p
      obtain ⟨p', hp'⟩ : ∃ p' : Fin N, p' ≠ p :=
        Fintype.exists_ne_of_one_lt_card (by simp only [Fintype.card_fin]; omega) p
      obtain ⟨l, hl, -⟩ := (hline p p' hp'.symm).exists
      exact ⟨l, hl⟩
    have hline_point : ∀ l : Fin N, ∃ p : Fin N, I p l := by
      intro l
      have hpos : 0 < (Finset.univ.filter (fun p => I p l)).card := by
        rw [hcard l]; omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      exact ⟨p, (Finset.mem_filter.mp hp).2⟩
    have hsens : ∀ k : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
        (∀ j : Fin (N + N), j ≠ k → x j = y j) ∧
        circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
      intro k
      induction k using Fin.addCases with
      | left p =>
        obtain ⟨l, hl⟩ := hpoint_line p
        refine ⟨fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l),
          fun j => decide (j = Fin.natAdd N l), ?_, ?_⟩
        · intro j hj
          simp only [hj, false_or]
        · have hx := hacc p l hl
          have hy : circuitFun (N + N) C (fun j => decide (j = Fin.natAdd N l)) = false := by
            apply hsound
            · have hset : (Finset.univ.filter (fun l' : Fin N =>
                  decide (Fin.natAdd N l' = Fin.natAdd N l) = true)) = {l} := by
                ext l'
                simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                  Finset.mem_singleton]
                constructor
                · intro h
                  have hh := of_decide_eq_true h
                  have hv := congrArg Fin.val hh
                  simp only [Fin.val_natAdd] at hv
                  exact Fin.ext (by omega)
                · intro h; subst h; simp
              have hcard1 : (Finset.univ.filter (fun l' : Fin N =>
                  (fun j => decide (j = Fin.natAdd N l)) (Fin.natAdd N l') = true)).card ≤ q := by
                rw [hset, Finset.card_singleton]; omega
              exact hcard1
            · rintro ⟨p', l', -, hp', -⟩
              have hne : Fin.castAdd N p' ≠ Fin.natAdd N l := by
                intro hh
                have hv := congrArg Fin.val hh
                simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
                have := p'.isLt; omega
              exact hne (of_decide_eq_true hp')
          rw [hx, hy]
          decide
      | right l =>
        obtain ⟨p, hp⟩ := hline_point l
        refine ⟨fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l),
          fun j => decide (j = Fin.castAdd N p), ?_, ?_⟩
        · intro j hj
          simp only [hj, or_false]
        · have hx := hacc p l hp
          have hy : circuitFun (N + N) C (fun j => decide (j = Fin.castAdd N p)) = false := by
            apply hsound
            · have hne_all : ∀ l' : Fin N, Fin.natAdd N l' ≠ Fin.castAdd N p := by
                intro l' hh
                have hv := congrArg Fin.val hh
                simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
                have := p.isLt; omega
              have hset : (Finset.univ.filter (fun l' : Fin N =>
                  decide (Fin.natAdd N l' = Fin.castAdd N p) = true)) = ∅ := by
                apply Finset.filter_false_of_mem
                intro l' _
                show ¬ (decide (Fin.natAdd N l' = Fin.castAdd N p) = true)
                intro h
                exact hne_all l' (of_decide_eq_true h)
              have hcard0 : (Finset.univ.filter (fun l' : Fin N =>
                  (fun j => decide (j = Fin.castAdd N p)) (Fin.natAdd N l') = true)).card ≤ q := by
                rw [hset, Finset.card_empty]; omega
              exact hcard0
            · rintro ⟨p', l', -, -, hl'⟩
              have hne : Fin.natAdd N l' ≠ Fin.castAdd N p := by
                intro hh
                have hv := congrArg Fin.val hh
                simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
                have := p.isLt; omega
              exact hne (of_decide_eq_true hl')
          rw [hx, hy]
          decide
    have hle := h_sens (N + N) C hmono hsens
    have hq3 : q ^ 3 ≤ 100 * q ^ 2 := by
      calc q ^ 3 = q * q ^ 2 := by ring
      _ ≤ 100 * q ^ 2 := Nat.mul_le_mul_right _ hq100
    have hNq : N * q + 100 ≤ 200 * N := by
      rw [hN]
      nlinarith [hq3, hq]
    omega
  · exact h_large q N I C (Nat.lt_of_not_ge hq100) hN hcard hline hmono hacc hsound
