import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2407

theorem centre_eq {N M : ℕ} (I : Fin N → Fin M → Prop) (L : Set (Fin M))
    (h : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (p q z : Fin N) (hpq : p ≠ q) (hzq : z ≠ q)
    (hL : L ⊆ {l2 : Fin M | I p l2 ∨ I z l2})
    (h3 : 3 ≤ {l : Fin M | l ∈ L ∧ I q l}.ncard) : False := by
  have h3b : 2 < {l : Fin M | l ∈ L ∧ I q l}.ncard := h3
  obtain ⟨a, b, c, ⟨haL, haq⟩, ⟨hbL, hbq⟩, ⟨hcL, hcq⟩, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).1 h3b
  rcases hL haL with ha | ha <;> rcases hL hbL with hb | hb <;> rcases hL hcL with hc | hc <;>
    first
    | exact h p q a b hpq hab ⟨ha, haq, hb, hbq⟩
    | exact h p q a c hpq hac ⟨ha, haq, hc, hcq⟩
    | exact h p q b c hpq hbc ⟨hb, hbq, hc, hcq⟩
    | exact h z q a b hzq hab ⟨ha, haq, hb, hbq⟩
    | exact h z q a c hzq hac ⟨ha, haq, hc, hcq⟩
    | exact h z q b c hzq hbc ⟨hb, hbq, hc, hcq⟩

end PEqualNP.Outside.L_meta_2407

theorem PEqualNP.Outside.L_meta_2407 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M)), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → {p : Fin N | 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard ∧ ∃ z : Fin N, L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}}.ncard ≤ 2 := by
  intro N M I L h
  by_contra hcon
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).1 (not_le.1 hcon)
  obtain ⟨-, z, hz⟩ := hp
  have h1 : z = q := by
    by_contra hzq
    exact PEqualNP.Outside.L_meta_2407.centre_eq I L h p q z hpq hzq hz hq.1
  have h2 : z = r := by
    by_contra hzr
    exact PEqualNP.Outside.L_meta_2407.centre_eq I L h p r z hpr hzr hz hr.1
  exact hqr (h1.symm.trans h2)
