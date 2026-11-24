import Mathlib.Data.Finset.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1681_217
    (h_slp_search :
      let inc : Fin 13 → Fin 13 → Bool := fun p w =>
        let d := p - w
        d == 0 || d == 1 || d == 3 || d == 9
      let evalSLP : List (Bool × ℕ × ℕ) → (Fin 13 → Bool) → (Fin 13 → Bool) → Bool :=
        fun gs px wx =>
          let ws := gs.foldl (fun w g =>
            let a := w.getD g.2.1 false
            let b := w.getD g.2.2 false
            w ++ [cond g.1 (a && b) (a || b)]) (List.ofFn px ++ List.ofFn wx)
          ws.getD (26 + gs.length - 1) false
      ∃ gs : List (Bool × ℕ × ℕ),
        1 ≤ gs.length ∧ gs.length ≤ 63 ∧
        (∀ i : Fin gs.length,
          (gs.get i).2.1 < 26 + i.val ∧ (gs.get i).2.2 < 26 + i.val) ∧
        (∀ p w : Fin 13, inc p w = true →
          evalSLP gs (fun q => q == p) (fun z => z == w) = true) ∧
        (∀ a b c : Fin 13, (∀ w : Fin 13, ¬ (inc a w = true ∧ inc b w = true ∧ inc c w = true)) →
          evalSLP gs
            (fun q => q == a || q == b || q == c)
            (fun w => !(inc a w) && !(inc b w) && !(inc c w)) = false) ∧
        (∀ u v w : Fin 13, (∀ p : Fin 13, ¬ (inc p u = true ∧ inc p v = true ∧ inc p w = true)) →
          evalSLP gs
            (fun p => !(inc p u) && !(inc p v) && !(inc p w))
            (fun z => z == u || z == v || z == w) = false))
    (h_slp_to_circuit :
      let evalSLP : List (Bool × ℕ × ℕ) → (Fin 13 → Bool) → (Fin 13 → Bool) → Bool :=
        fun gs px wx =>
          let ws := gs.foldl (fun w g =>
            let a := w.getD g.2.1 false
            let b := w.getD g.2.2 false
            w ++ [cond g.1 (a && b) (a || b)]) (List.ofFn px ++ List.ofFn wx)
          ws.getD (26 + gs.length - 1) false
      ∀ gs : List (Bool × ℕ × ℕ),
        1 ≤ gs.length →
        (∀ i : Fin gs.length,
          (gs.get i).2.1 < 26 + i.val ∧ (gs.get i).2.2 < 26 + i.val) →
        ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C ∧
          C.size = gs.length ∧
          ∀ px wx : Fin 13 → Bool,
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C (Fin.append px wx) =
              evalSLP gs px wx) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  let inc : Fin 13 → Fin 13 → Bool := fun p w =>
    let d := p - w
    d == 0 || d == 1 || d == 3 || d == 9
  have h_inc_iff : ∀ p w : Fin 13,
      (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) ↔ inc p w = true := by
    intro p w
    constructor
    · intro h
      rcases h with ⟨dd, hdd, hp⟩
      have hsub : p - w = dd := by
        rw [hp, add_comm, add_sub_cancel_right]
      have hdd' : dd = 0 ∨ dd = 1 ∨ dd = 3 ∨ dd = 9 := by
        simpa using hdd
      change (((p - w == 0 || p - w == 1) || p - w == 3) || p - w == 9) = true
      rw [hsub]
      rcases hdd' with rfl | rfl | rfl | rfl <;> rfl
    · intro h
      have hsub : p - w = 0 ∨ p - w = 1 ∨ p - w = 3 ∨ p - w = 9 := by
        change (((p - w == 0 || p - w == 1) || p - w == 3) || p - w == 9) = true at h
        simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using h
      refine ⟨p - w, ?_, ?_⟩
      · rcases hsub with h0 | h1 | h3 | h9
        · rw [h0]; simp
        · rw [h1]; simp
        · rw [h3]; simp
        · rw [h9]; simp
      · rw [add_comm, sub_add_cancel]
  have h_inc_shift : ∀ p w t : Fin 13, inc (p + t) (w + t) = inc p w := by
    intro p w t
    change (((p + t - (w + t) == 0 || p + t - (w + t) == 1) || p + t - (w + t) == 3) ||
      p + t - (w + t) == 9) =
      (((p - w == 0 || p - w == 1) || p - w == 3) || p - w == 9)
    have hsub : p + t - (w + t) = p - w := add_sub_add_right_eq_sub p w t
    rw [hsub]
  have h_inc_refl : ∀ x : Fin 13, inc x x = true := by
    intro x
    have h1 := h_inc_shift 0 0 x
    rw [zero_add] at h1
    rw [h1]
    rfl
  have h_line_ex0 : ∀ b : Fin 13, ∃ w : Fin 13, inc 0 w = true ∧ inc b w = true := by
    decide
  have h_line_ex : ∀ a b : Fin 13, ∃ w : Fin 13, inc a w = true ∧ inc b w = true := by
    intro a b
    rcases h_line_ex0 (b - a) with ⟨w, hw0, hwb⟩
    refine ⟨w + a, ?_, ?_⟩
    · have h1 := h_inc_shift 0 w a
      rw [zero_add] at h1
      rw [h1]
      exact hw0
    · have h2 := h_inc_shift (b - a) w a
      rw [sub_add_cancel] at h2
      rw [h2]
      exact hwb
  have h_line_uniq0 : ∀ a b w : Fin 13,
      a ≠ b → inc a 0 = true → inc b 0 = true → inc a w = true → inc b w = true → w = 0 := by
    decide
  have h_line_uniq : ∀ a b w1 w2 : Fin 13,
      a ≠ b → inc a w1 = true → inc b w1 = true → inc a w2 = true → inc b w2 = true → w1 = w2 := by
    intro a b w1 w2 hab ha1 hb1 ha2 hb2
    have ha1' : inc (a - w1) 0 = true := by
      have h := h_inc_shift (a - w1) 0 w1
      rw [sub_add_cancel, zero_add] at h
      rw [← h]; exact ha1
    have hb1' : inc (b - w1) 0 = true := by
      have h := h_inc_shift (b - w1) 0 w1
      rw [sub_add_cancel, zero_add] at h
      rw [← h]; exact hb1
    have ha2' : inc (a - w1) (w2 - w1) = true := by
      have h := h_inc_shift (a - w1) (w2 - w1) w1
      rw [sub_add_cancel, sub_add_cancel] at h
      rw [← h]; exact ha2
    have hb2' : inc (b - w1) (w2 - w1) = true := by
      have h := h_inc_shift (b - w1) (w2 - w1) w1
      rw [sub_add_cancel, sub_add_cancel] at h
      rw [← h]; exact hb2
    have hab' : a - w1 ≠ b - w1 := by
      intro heq
      apply hab
      have := congrArg (· + w1) heq
      simpa using this
    have hz : w2 - w1 = 0 := h_line_uniq0 (a - w1) (b - w1) (w2 - w1) hab' ha1' hb1' ha2' hb2'
    exact (sub_eq_zero.mp hz).symm
  have h_pt_ex0 : ∀ v : Fin 13, ∃ p : Fin 13, inc p 0 = true ∧ inc p v = true := by
    decide
  have h_pt_ex : ∀ u v : Fin 13, ∃ p : Fin 13, inc p u = true ∧ inc p v = true := by
    intro u v
    rcases h_pt_ex0 (v - u) with ⟨p, hp0, hpv⟩
    refine ⟨p + u, ?_, ?_⟩
    · have h1 := h_inc_shift p 0 u
      rw [zero_add] at h1
      rw [h1]; exact hp0
    · have h2 := h_inc_shift p (v - u) u
      rw [sub_add_cancel] at h2
      rw [h2]; exact hpv
  have h_pt_uniq0 : ∀ p u v : Fin 13,
      u ≠ v → inc 0 u = true → inc 0 v = true → inc p u = true → inc p v = true → p = 0 := by
    decide
  have h_pt_uniq : ∀ p1 p2 u v : Fin 13,
      u ≠ v → inc p1 u = true → inc p1 v = true → inc p2 u = true → inc p2 v = true → p1 = p2 := by
    intro p1 p2 u v huv h1u h1v h2u h2v
    have h1u' : inc 0 (u - p1) = true := by
      have h := h_inc_shift 0 (u - p1) p1
      rw [zero_add, sub_add_cancel] at h
      rw [← h]; exact h1u
    have h1v' : inc 0 (v - p1) = true := by
      have h := h_inc_shift 0 (v - p1) p1
      rw [zero_add, sub_add_cancel] at h
      rw [← h]; exact h1v
    have h2u' : inc (p2 - p1) (u - p1) = true := by
      have h := h_inc_shift (p2 - p1) (u - p1) p1
      rw [sub_add_cancel, sub_add_cancel] at h
      rw [← h]; exact h2u
    have h2v' : inc (p2 - p1) (v - p1) = true := by
      have h := h_inc_shift (p2 - p1) (v - p1) p1
      rw [sub_add_cancel, sub_add_cancel] at h
      rw [← h]; exact h2v
    have huv' : u - p1 ≠ v - p1 := by
      intro heq
      apply huv
      have := congrArg (· + p1) heq
      simpa using this
    have hz : p2 - p1 = 0 := h_pt_uniq0 (p2 - p1) (u - p1) (v - p1) huv' h1u' h1v' h2u' h2v'
    exact (sub_eq_zero.mp hz).symm
  have h_tri_card0 : ∀ b c : Fin 13,
      (∀ w : Fin 13, ¬ (inc 0 w = true ∧ inc b w = true ∧ inc c w = true)) →
      (Finset.univ.filter (fun w : Fin 13 => !(inc 0 w) && !(inc b w) && !(inc c w))).card = 4 := by
    decide
  have h_tri_close0 : ∀ b c : Fin 13,
      (∀ w : Fin 13, ¬ (inc 0 w = true ∧ inc b w = true ∧ inc c w = true)) →
      ∀ v : Fin 13,
        (∀ w : Fin 13, inc 0 w = false → inc b w = false → inc c w = false → inc v w = false) →
        v = 0 ∨ v = b ∨ v = c := by
    decide
  rcases h_slp_search with ⟨gs, hlen1, hlen63, hwf, hpos, htri, hdual⟩
  rcases h_slp_to_circuit gs hlen1 hwf with ⟨C, hmono, hsize, heval⟩
  refine ⟨C, hmono, by omega, ?_, ?_⟩
  · intro p w hpw
    have hpw' : inc p w = true := (h_inc_iff p w).mp hpw
    have hfun : (fun k : Fin (13 + 13) => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) =
        Fin.append (fun q => q == p) (fun z => z == w) := by
      funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        rw [Fin.append_left]
        have hne : ∀ z : Fin 13, Fin.castAdd 13 i ≠ Fin.natAdd 13 z := by
          intro z heq
          have hv := congrArg Fin.val heq
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        by_cases hi : i = p
        · subst hi
          simp
        · have h1 : ¬ (Fin.castAdd 13 i = Fin.castAdd 13 p ∨ Fin.castAdd 13 i = Fin.natAdd 13 w) := by
            intro h
            rcases h with h1 | h2
            · exact hi (Fin.castAdd_injective 13 13 h1)
            · exact hne w h2
          rw [decide_eq_false h1]
          simp [hi]
      · intro j
        rw [Fin.append_right]
        have hne : ∀ q : Fin 13, Fin.natAdd 13 j ≠ Fin.castAdd 13 q := by
          intro q heq
          have hv := congrArg Fin.val heq
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
          omega
        by_cases hj : j = w
        · subst hj
          simp
        · have h1 : ¬ (Fin.natAdd 13 j = Fin.castAdd 13 p ∨ Fin.natAdd 13 j = Fin.natAdd 13 w) := by
            intro h
            rcases h with h1 | h2
            · exact hne p h1
            · exact hj (Fin.natAdd_injective 13 13 h2)
          rw [decide_eq_false h1]
          simp [hj]
    rw [hfun, heval]
    exact hpos p w hpw'
  · intro P hclosed hgen
    rcases hgen with ⟨hnotcol, hnotconc⟩
    let W : Finset (Fin 13) := Finset.univ.filter (fun w => ∀ p ∈ P, inc p w = false)
    have hmemW : ∀ w : Fin 13, w ∈ W ↔ ∀ p ∈ P, inc p w = false := by
      intro w
      simp [W]
    have hnotcol' : ∀ w : Fin 13, ∃ p ∈ P, inc p w = false := by
      intro w
      by_contra h
      push_neg at h
      apply hnotcol
      refine ⟨w, fun p hp => (h_inc_iff p w).mpr ?_⟩
      cases hpw : inc p w
      · exfalso; exact h p hp hpw
      · rfl
    have hnotconc' : ∀ p : Fin 13, ∃ w ∈ W, inc p w = false := by
      intro p
      by_contra h
      push_neg at h
      apply hnotconc
      refine ⟨p, fun w hw => (h_inc_iff p w).mpr ?_⟩
      have hwW : w ∈ W := (hmemW w).mpr (fun q hq => by
        cases hqw : inc q w
        · rfl
        · exfalso; exact hw q hq ((h_inc_iff q w).mpr hqw))
      cases hpw : inc p w
      · exfalso; exact h w hwW hpw
      · rfl
    -- Find non-collinear triple a, b, c ∈ P
    have hPne : P.Nonempty := by
      rcases hnotcol' 0 with ⟨a, ha, _⟩
      exact ⟨a, ha⟩
    rcases hPne with ⟨a, haP⟩
    have hPb : ∃ b ∈ P, b ≠ a := by
      rcases hnotcol' a with ⟨b, hbP, hba⟩
      refine ⟨b, hbP, ?_⟩
      intro heq
      rw [heq, h_inc_refl] at hba
      exact Bool.noConfusion hba
    rcases hPb with ⟨b, hbP, hba⟩
    rcases h_line_ex a b with ⟨w0, haw0, hbw0⟩
    rcases hnotcol' w0 with ⟨c, hcP, hcw0⟩
    have hnoncol : ∀ w : Fin 13, ¬ (inc a w = true ∧ inc b w = true ∧ inc c w = true) := by
      intro w h
      rcases h with ⟨haw, hbw, hcw⟩
      have heq : w0 = w := h_line_uniq a b w0 w hba.symm haw0 hbw0 haw hbw
      rw [← heq] at hcw
      rw [hcw0] at hcw
      exact Bool.noConfusion hcw
    -- Define the 4 lines missing {a, b, c}
    let M : Finset (Fin 13) :=
      Finset.univ.filter (fun w : Fin 13 => !(inc a w) && !(inc b w) && !(inc c w))
    have hmemM : ∀ w : Fin 13, w ∈ M ↔ inc a w = false ∧ inc b w = false ∧ inc c w = false := by
      intro w
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, Bool.not_eq_true', and_assoc]
    have hWsubM : W ⊆ M := by
      intro w hw
      have hw' := (hmemW w).mp hw
      exact (hmemM w).mpr ⟨hw' a haP, hw' b hbP, hw' c hcP⟩
    have hnoncol0 : ∀ w : Fin 13,
        ¬ (inc 0 w = true ∧ inc (b - a) w = true ∧ inc (c - a) w = true) := by
      intro w h
      rcases h with ⟨h0, hb, hc⟩
      apply hnoncol (w + a)
      have ha' := h_inc_shift 0 w a
      rw [zero_add] at ha'
      have hb' := h_inc_shift (b - a) w a
      rw [sub_add_cancel] at hb'
      have hc' := h_inc_shift (c - a) w a
      rw [sub_add_cancel] at hc'
      exact ⟨ha'.trans h0, hb'.trans hb, hc'.trans hc⟩
    have hMcard : M.card = 4 := by
      let M0 : Finset (Fin 13) :=
        Finset.univ.filter (fun w : Fin 13 => !(inc 0 w) && !(inc (b - a) w) && !(inc (c - a) w))
      have hM0card : M0.card = 4 := h_tri_card0 (b - a) (c - a) hnoncol0
      have hbij : M.card = M0.card := by
        refine Finset.card_bij (fun w _ => w - a) ?_ ?_ ?_
        · intro w hw
          have hw' := (hmemM w).mp hw
          simp only [M0, Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.and_eq_true, Bool.not_eq_true', and_assoc]
          have h1 := h_inc_shift 0 (w - a) a
          rw [zero_add, sub_add_cancel] at h1
          have h2 := h_inc_shift (b - a) (w - a) a
          rw [sub_add_cancel, sub_add_cancel] at h2
          have h3 := h_inc_shift (c - a) (w - a) a
          rw [sub_add_cancel, sub_add_cancel] at h3
          exact ⟨h1.symm.trans hw'.1, h2.symm.trans hw'.2.1, h3.symm.trans hw'.2.2⟩
        · intro w1 _ w2 _ heq
          have := congrArg (· + a) heq
          simpa using this
        · intro w0 hw0
          simp only [M0, Finset.mem_filter, Finset.mem_univ, true_and,
            Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hw0
          refine ⟨w0 + a, ?_, by simp⟩
          apply (hmemM (w0 + a)).mpr
          have h1 := h_inc_shift 0 w0 a
          rw [zero_add] at h1
          have h2 := h_inc_shift (b - a) w0 a
          rw [sub_add_cancel] at h2
          have h3 := h_inc_shift (c - a) w0 a
          rw [sub_add_cancel] at h3
          exact ⟨h1.trans hw0.1, h2.trans hw0.2.1, h3.trans hw0.2.2⟩
      exact hbij.trans hM0card
    -- Helper to match L-meta-1681 input function with Fin.append
    have h_app_eq : ∀ (px wx : Fin 13 → Bool),
        (∀ p : Fin 13, p ∈ P ↔ px p = true) →
        (∀ w : Fin 13, w ∈ W ↔ wx w = true) →
        (fun kk : Fin (13 + 13) => decide (
          (∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
          (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
            (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) =
        Fin.append px wx := by
      intro px wx hpx hwx
      funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        rw [Fin.append_left]
        have hiff : ((∃ pp ∈ P, Fin.castAdd 13 i = Fin.castAdd 13 pp) ∨
            (∃ ww : Fin 13, Fin.castAdd 13 i = Fin.natAdd 13 ww ∧
              (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd)))) ↔
            px i = true := by
          constructor
          · intro h
            rcases h with ⟨pp, hpp, heq⟩ | ⟨ww, heq, _⟩
            · have hi : i = pp := Fin.castAdd_injective 13 13 heq
              rw [hi]
              exact (hpx pp).mp hpp
            · exfalso
              have hv := congrArg Fin.val heq
              simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
              omega
          · intro hi
            exact Or.inl ⟨i, (hpx i).mpr hi, rfl⟩
        cases hval : px i
        · refine decide_eq_false ?_
          intro h
          have ht := hiff.mp h
          rw [hval] at ht
          exact Bool.noConfusion ht
        · exact decide_eq_true (hiff.mpr hval)
      · intro j
        rw [Fin.append_right]
        have hiff : ((∃ pp ∈ P, Fin.natAdd 13 j = Fin.castAdd 13 pp) ∨
            (∃ ww : Fin 13, Fin.natAdd 13 j = Fin.natAdd 13 ww ∧
              (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd)))) ↔
            wx j = true := by
          constructor
          · intro h
            rcases h with ⟨pp, _, heq⟩ | ⟨ww, heq, hww⟩
            · exfalso
              have hv := congrArg Fin.val heq
              simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
              omega
            · have hj : j = ww := Fin.natAdd_injective 13 13 heq
              rw [hj]
              apply (hwx ww).mp
              apply (hmemW ww).mpr
              intro pp hpp
              cases hpw : inc pp ww
              · rfl
              · exfalso; exact hww pp hpp ((h_inc_iff pp ww).mpr hpw)
          · intro hj
            refine Or.inr ⟨j, rfl, fun pp hpp hinc => ?_⟩
            have hjW : j ∈ W := (hwx j).mpr hj
            have hfalse := (hmemW j).mp hjW pp hpp
            have htrue := (h_inc_iff pp j).mp hinc
            rw [hfalse] at htrue
            exact Bool.noConfusion htrue
        cases hval : wx j
        · refine decide_eq_false ?_
          intro h
          have ht := hiff.mp h
          rw [hval] at ht
          exact Bool.noConfusion ht
        · exact decide_eq_true (hiff.mpr hval)
    by_cases hWM : W = M
    · -- Case 1: W = M (P is the triangle {a, b, c})
      have hPtri : ∀ p : Fin 13, p ∈ P ↔ (p == a || p == b || p == c) = true := by
        intro p
        constructor
        · intro hp
          have hcl : ∀ w0 : Fin 13, inc 0 w0 = false → inc (b - a) w0 = false →
              inc (c - a) w0 = false → inc (p - a) w0 = false := by
            intro w0 h0 hb hc
            have hwM : w0 + a ∈ M := by
              apply (hmemM (w0 + a)).mpr
              have h1 := h_inc_shift 0 w0 a; rw [zero_add] at h1
              have h2 := h_inc_shift (b - a) w0 a; rw [sub_add_cancel] at h2
              have h3 := h_inc_shift (c - a) w0 a; rw [sub_add_cancel] at h3
              exact ⟨h1.trans h0, h2.trans hb, h3.trans hc⟩
            have hwW : w0 + a ∈ W := by rw [hWM]; exact hwM
            have hpfalse := (hmemW (w0 + a)).mp hwW p hp
            have h4 := h_inc_shift (p - a) w0 a
            rw [sub_add_cancel] at h4
            exact h4.symm.trans hpfalse
          have hdisj := h_tri_close0 (b - a) (c - a) hnoncol0 (p - a) hcl
          have hdisj' : p = a ∨ p = b ∨ p = c := by
            rcases hdisj with h1 | h2 | h3
            · exact Or.inl (sub_eq_zero.mp h1)
            · right; left
              have := congrArg (· + a) h2
              simpa using this
            · right; right
              have := congrArg (· + a) h3
              simpa using this
          simp only [Bool.or_eq_true, beq_iff_eq]
          rcases hdisj' with rfl | rfl | rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr rfl
        · intro hp
          simp only [Bool.or_eq_true, beq_iff_eq] at hp
          rcases hp with (rfl | rfl) | rfl
          · exact haP
          · exact hbP
          · exact hcP
      have hWtri : ∀ w : Fin 13, w ∈ W ↔ (!(inc a w) && !(inc b w) && !(inc c w)) = true := by
        intro w
        rw [hWM]
        simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h_app_eq _ _ hPtri hWtri, heval]
      exact htri a b c hnoncol
    · -- Case 2: W ⊊ M, so W.card ≤ 3 and W is a non-concurrent triple {u, v, w}
      have hWlt : W.card < M.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hWsubM, hWM⟩)
      have hWle3 : W.card ≤ 3 := by omega
      rcases hnotconc' 0 with ⟨u, huW, _⟩
      have hWv : ∃ v ∈ W, v ≠ u := by
        rcases hnotconc' u with ⟨v, hvW, hvu⟩
        refine ⟨v, hvW, ?_⟩
        intro heq
        rw [heq, h_inc_refl] at hvu
        exact Bool.noConfusion hvu
      rcases hWv with ⟨v, hvW, hvu⟩
      rcases h_pt_ex u v with ⟨p0, hp0u, hp0v⟩
      rcases hnotconc' p0 with ⟨w, hwW, hp0w⟩
      have hnonconc : ∀ p : Fin 13, ¬ (inc p u = true ∧ inc p v = true ∧ inc p w = true) := by
        intro p h
        rcases h with ⟨hpu, hpv, hpw⟩
        have heq : p0 = p := h_pt_uniq p0 p u v hvu.symm hp0u hp0v hpu hpv
        rw [← heq] at hpw
        rw [hp0w] at hpw
        exact Bool.noConfusion hpw
      have hwu : w ≠ u := by
        intro heq; rw [heq, hp0u] at hp0w; exact Bool.noConfusion hp0w
      have hwv : w ≠ v := by
        intro heq; rw [heq, hp0v] at hp0w; exact Bool.noConfusion hp0w
      have hTsub : ({u, v, w} : Finset (Fin 13)) ⊆ W := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact huW
        · exact hvW
        · exact hwW
      have hTcard : ({u, v, w} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hwv.symm]
        · simp [hvu.symm, hwu.symm]
      have hWeq : W = {u, v, w} :=
        (Finset.eq_of_subset_of_card_le hTsub (by omega)).symm
      have hWdual : ∀ z : Fin 13, z ∈ W ↔ (z == u || z == v || z == w) = true := by
        intro z
        rw [hWeq]
        simp only [Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true, beq_iff_eq, or_assoc]
      have hPdual : ∀ p : Fin 13, p ∈ P ↔ (!(inc p u) && !(inc p v) && !(inc p w)) = true := by
        intro p
        simp only [Bool.and_eq_true, Bool.not_eq_true', and_assoc]
        constructor
        · intro hp
          exact ⟨(hmemW u).mp huW p hp, (hmemW v).mp hvW p hp, (hmemW w).mp hwW p hp⟩
        · intro h
          rcases h with ⟨hpu, hpv, hpw⟩
          by_contra hpP
          rcases hclosed p hpP with ⟨w2, hw2miss, hpw2⟩
          have hw2W : w2 ∈ W := (hmemW w2).mpr (fun q hq => by
            cases hqw : inc q w2
            · rfl
            · exfalso; exact hw2miss q hq ((h_inc_iff q w2).mpr hqw))
          rw [hWeq] at hw2W
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw2W
          have hpw2' : inc p w2 = true := (h_inc_iff p w2).mp hpw2
          rcases hw2W with rfl | rfl | rfl
          · rw [hpu] at hpw2'; exact Bool.noConfusion hpw2'
          · rw [hpv] at hpw2'; exact Bool.noConfusion hpw2'
          · rw [hpw] at hpw2'; exact Bool.noConfusion hpw2'
      rw [h_app_eq _ _ hPdual hWdual, heval]
      exact hdual u v w hnonconc
