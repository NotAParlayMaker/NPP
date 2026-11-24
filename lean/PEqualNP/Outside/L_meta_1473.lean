import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1473

-- doubling is injective modulo an odd number
lemma dbl_inj (N : ℕ) (hN : N % 2 = 1) (c d : Fin N) (h : c + c = d + d) : c = d := by
  have h1 := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_add] at h1
  have key : ∀ x : ℕ, x < N → (x + x) % N = x + x ∨ (x + x) % N + N = x + x := by
    intro x hx
    rcases Nat.lt_or_ge (x + x) N with h2 | h2
    · left
      exact Nat.mod_eq_of_lt h2
    · right
      rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]
      omega
  have hc := key c.val c.isLt
  have hd := key d.val d.isLt
  apply Fin.ext
  omega

-- sums of two members of D are at most (q+2 choose 2) many, doubling is injective,
-- so some c has c + c outside D + D
lemma main (q : ℕ) (D : Finset (Fin (q ^ 2 + q + 1))) (hq : 2 ≤ q) (hD : D.card = q + 1) :
    ∃ c : Fin (q ^ 2 + q + 1), c ∉ D ∧
      ∀ t u : Fin (q ^ 2 + q + 1), ¬ (t + c - u ∈ D ∧ u + c - t ∈ D) := by
  classical
  let f : Sym2 (Fin (q ^ 2 + q + 1)) → Fin (q ^ 2 + q + 1) :=
    Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩
  have hBcard : (D.sym2.image f).card ≤ (q + 1 + 1).choose 2 := by
    calc (D.sym2.image f).card ≤ D.sym2.card := Finset.card_image_le
      _ = (q + 1 + 1).choose 2 := by rw [Finset.card_sym2, hD]
  have hmemB : ∀ a b : Fin (q ^ 2 + q + 1), a ∈ D → b ∈ D → a + b ∈ D.sym2.image f := by
    intro a b ha hb
    rw [Finset.mem_image]
    exact ⟨s(a, b), Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, rfl⟩
  have hodd : (q ^ 2 + q + 1) % 2 = 1 := by
    have h0 : (q ^ 2 + q) % 2 = 0 := by
      have h := Nat.even_mul_succ_self q
      have e : q ^ 2 + q = q * (q + 1) := by ring
      rw [e]
      exact Nat.even_iff.mp h
    omega
  have hBadcard : (Finset.univ.filter (fun c : Fin (q ^ 2 + q + 1) => c + c ∈ D.sym2.image f)).card
      ≤ (D.sym2.image f).card := by
    apply Finset.card_le_card_of_injOn (fun c => c + c)
    · intro c hc
      exact (Finset.mem_filter.mp hc).2
    · intro c _ d _ h
      exact dbl_inj _ hodd c d h
  have hlt : (q + 1 + 1).choose 2 < q ^ 2 + q + 1 := by
    rw [Nat.choose_two_right]
    apply Nat.div_lt_of_lt_mul
    have e : q + 1 + 1 - 1 = q + 1 := by omega
    rw [e]
    nlinarith
  have hex : ∃ c : Fin (q ^ 2 + q + 1), c + c ∉ D.sym2.image f := by
    by_contra hcon
    push_neg at hcon
    have h1 : Finset.univ.filter (fun c : Fin (q ^ 2 + q + 1) => c + c ∈ D.sym2.image f)
        = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro c
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon c⟩
    have h2 : (Finset.univ.filter (fun c : Fin (q ^ 2 + q + 1) => c + c ∈ D.sym2.image f)).card
        = q ^ 2 + q + 1 := by
      rw [h1, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, fun hcD => hc (hmemB c c hcD hcD), ?_⟩
  rintro t u ⟨h1, h2⟩
  apply hc
  have h3 := hmemB _ _ h1 h2
  have e : t + c - u + (u + c - t) = c + c := by abel
  rw [e] at h3
  exact h3

end PEqualNP.Outside.L_meta_1473

theorem PEqualNP.Outside.L_meta_1473 : ∀ (q : ℕ) (D : Finset (Fin (q ^ 2 + q + 1))),
    2 ≤ q → D.card = q + 1 →
    ∃ c : Fin (q ^ 2 + q + 1), c ∉ D ∧
      ∀ t u : Fin (q ^ 2 + q + 1), ¬ (t + c - u ∈ D ∧ u + c - t ∈ D) := by
  intro q D hq hD
  exact PEqualNP.Outside.L_meta_1473.main q D hq hD
