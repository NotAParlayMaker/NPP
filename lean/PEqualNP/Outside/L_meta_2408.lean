import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2408

theorem card_le_four {M : ℕ} (Wl : Finset (Fin M)) (P Q : Fin M → Prop)
    (h : ∀ w ∈ Wl, ∀ w' ∈ Wl, (P w ↔ P w') → (Q w ↔ Q w') → w = w') : Wl.card ≤ 4 := by
  classical
  have h1 : Wl.card ≤ (Finset.univ : Finset (Bool × Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun w => (decide (P w), decide (Q w)))
    · intro w _
      simp
    · intro w hw w' hw' he
      simp only [Prod.mk.injEq, decide_eq_decide] at he
      exact h w (Finset.mem_coe.1 hw) w' (Finset.mem_coe.1 hw') he.1 he.2
  have h4 : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
  omega

theorem two_point {N M : ℕ} (I : Fin N → Fin M → Prop)
    (hI : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (p q : Fin N) (l l' : Fin M) (hpq : p ≠ q)
    (h1 : I p l) (h2 : I q l) (h3 : I p l') (h4 : I q l') : l = l' := by
  by_contra hne
  exact hI p q l l' hpq hne ⟨h1, h2, h3, h4⟩

end PEqualNP.Outside.L_meta_2408

theorem PEqualNP.Outside.L_meta_2408 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (Wl : Finset (Fin M)) (mk : Fin M → Finset (Fin N)) (z : Fin N → Fin N), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ w ∈ Wl, 3 ≤ (mk w).card ∧ ∀ a ∈ mk w, I a w ∧ ¬ I (z a) w ∧ z a ≠ a) → (∀ w ∈ Wl, ∀ a ∈ mk w, ∀ w' ∈ Wl, I a w' ∨ I (z a) w') → Wl.card ≤ 4 := by
  intro N M I Wl mk z hI hmk hall
  classical
  have hU := PEqualNP.Outside.L_meta_2408.two_point I hI
  by_cases hA : ∃ w ∈ Wl, ∃ a ∈ mk w, ∃ b ∈ mk w, a ≠ b ∧ z a ≠ z b
  · obtain ⟨w0, hw0, a, ha, b, hb, hab, hzab⟩ := hA
    obtain ⟨_, hm0⟩ := hmk w0 hw0
    obtain ⟨ha1, ha2, _⟩ := hm0 a ha
    obtain ⟨hb1, hb2, _⟩ := hm0 b hb
    have hazb : a ≠ z b := by
      intro h
      apply hb2
      rw [← h]
      exact ha1
    have hbza : b ≠ z a := by
      intro h
      apply ha2
      rw [← h]
      exact hb1
    apply PEqualNP.Outside.L_meta_2408.card_le_four Wl (fun w => I a w) (fun w => I b w)
    intro w hw w' hw' hP hQ
    have k1 := hall w0 hw0 a ha w hw
    have k1' := hall w0 hw0 a ha w' hw'
    have k2 := hall w0 hw0 b hb w hw
    have k2' := hall w0 hw0 b hb w' hw'
    by_cases pa : I a w
    · by_cases pb : I b w
      · exact hU a b w w' hab pa pb (hP.1 pa) (hQ.1 pb)
      · have pb' : ¬ I b w' := fun h => pb (hQ.2 h)
        exact hU a (z b) w w' hazb pa (k2.resolve_left pb) (hP.1 pa) (k2'.resolve_left pb')
    · have pa' : ¬ I a w' := fun h => pa (hP.2 h)
      by_cases pb : I b w
      · exact hU b (z a) w w' hbza pb (k1.resolve_left pa) (hQ.1 pb) (k1'.resolve_left pa')
      · have pb' : ¬ I b w' := fun h => pb (hQ.2 h)
        exact hU (z a) (z b) w w' hzab (k1.resolve_left pa) (k2.resolve_left pb)
          (k1'.resolve_left pa') (k2'.resolve_left pb')
  · have hA' : ∀ w ∈ Wl, ∀ a ∈ mk w, ∀ b ∈ mk w, a ≠ b → z a = z b := by
      intro w hw a ha b hb hab
      by_contra h
      exact hA ⟨w, hw, a, ha, b, hb, hab, h⟩
    rcases Wl.eq_empty_or_nonempty with h0 | ⟨w0, hw0⟩
    · simp [h0]
    obtain ⟨hc3, hm0⟩ := hmk w0 hw0
    obtain ⟨a1, ha1, a2, ha2, h12⟩ := Finset.one_lt_card.1 (by omega : 1 < (mk w0).card)
    have hz2 : z a2 = z a1 := (hA' w0 hw0 a1 ha1 a2 ha2 h12).symm
    by_cases hC : ∃ w1 ∈ Wl, I (z a1) w1
    · obtain ⟨w1, hw1, hcw1⟩ := hC
      obtain ⟨hc31, hm1⟩ := hmk w1 hw1
      obtain ⟨b, hb, hbc⟩ := Finset.exists_mem_ne (by omega : 1 < (mk w1).card) (z a1)
      obtain ⟨hb1, hb2, _⟩ := hm1 b hb
      have hcd : z a1 ≠ z b := by
        intro h
        apply hb2
        rw [← h]
        exact hcw1
      apply PEqualNP.Outside.L_meta_2408.card_le_four Wl (fun w => I (z a1) w) (fun w => I b w)
      intro w hw w' hw' hP hQ
      by_cases pc : I (z a1) w
      · by_cases pb : I b w
        · exact hU (z a1) b w w' (Ne.symm hbc) pc pb (hP.1 pc) (hQ.1 pb)
        · have pb' : ¬ I b w' := fun h => pb (hQ.2 h)
          exact hU (z a1) (z b) w w' hcd pc ((hall w1 hw1 b hb w hw).resolve_left pb)
            (hP.1 pc) ((hall w1 hw1 b hb w' hw').resolve_left pb')
      · have pc' : ¬ I (z a1) w' := fun h => pc (hP.2 h)
        have q1 : I a1 w := (hall w0 hw0 a1 ha1 w hw).resolve_right pc
        have q1' : I a1 w' := (hall w0 hw0 a1 ha1 w' hw').resolve_right pc'
        have q2 : I a2 w := (hall w0 hw0 a2 ha2 w hw).resolve_right (by rw [hz2]; exact pc)
        have q2' : I a2 w' := (hall w0 hw0 a2 ha2 w' hw').resolve_right (by rw [hz2]; exact pc')
        exact hU a1 a2 w w' h12 q1 q2 q1' q2'
    · have hC' : ∀ w ∈ Wl, ¬ I (z a1) w := by
        intro w hw h
        exact hC ⟨w, hw, h⟩
      have h1 : Wl.card ≤ 1 := by
        apply Finset.card_le_one.2
        intro w hw w' hw'
        have q1 : I a1 w := (hall w0 hw0 a1 ha1 w hw).resolve_right (hC' w hw)
        have q1' : I a1 w' := (hall w0 hw0 a1 ha1 w' hw').resolve_right (hC' w' hw')
        have q2 : I a2 w := (hall w0 hw0 a2 ha2 w hw).resolve_right (by rw [hz2]; exact hC' w hw)
        have q2' : I a2 w' :=
          (hall w0 hw0 a2 ha2 w' hw').resolve_right (by rw [hz2]; exact hC' w' hw')
        exact hU a1 a2 w w' h12 q1 q2 q1' q2'
      omega
