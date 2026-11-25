import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7850

lemma map_isDiag_iff {n : ℕ} {x : Sym2 (Fin n)} (hnd : ¬ x.IsDiag) (b : Fin n → Bool) :
    (Sym2.map b x).IsDiag ↔ b x.out.fst = b x.out.snd := by
  conv_lhs => rw [← Sym2.mk_fst_out_snd_out x]
  rw [Sym2.map_mk, Sym2.mk_isDiag_iff]

lemma out_ne {n : ℕ} {x : Sym2 (Fin n)} (hnd : ¬ x.IsDiag) : x.out.fst ≠ x.out.snd := by
  intro h
  apply hnd
  conv => rw [← Sym2.mk_fst_out_snd_out x]
  rw [Sym2.mk_isDiag_iff]
  exact h

lemma flip_cross {n : ℕ} (u v : Fin n) (huv : u ≠ v) (b : Fin n → Bool)
    (hb : ¬ (b u ≠ b v)) :
    Function.update b u (!b u) u ≠ Function.update b u (!b u) v := by
  rw [Function.update_self, Function.update_of_ne (Ne.symm huv)]
  simp only [ne_eq, not_not] at hb
  rw [hb]
  simp

lemma flip_noncross {n : ℕ} (u v : Fin n) (huv : u ≠ v) (b : Fin n → Bool)
    (hb : b u ≠ b v) :
    ¬ (Function.update b u (!b u) u ≠ Function.update b u (!b u) v) := by
  rw [Function.update_self, Function.update_of_ne (Ne.symm huv)]
  simp only [ne_eq, not_not]
  cases h1 : b u <;> cases h2 : b v <;> simp_all

lemma filter_dichotomy {n : ℕ} (u v : Fin n) :
    (Finset.univ.filter (fun b : Fin n → Bool => b u ≠ b v)).card
      + (Finset.univ.filter (fun b : Fin n → Bool => ¬ (b u ≠ b v))).card = 2 ^ n := by
  classical
  have hdisj : Disjoint (Finset.univ.filter (fun b : Fin n → Bool => b u ≠ b v))
      (Finset.univ.filter (fun b : Fin n → Bool => ¬ (b u ≠ b v))) := by
    rw [Finset.disjoint_left]
    intro b h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 h1
  have hunion : (Finset.univ.filter (fun b : Fin n → Bool => b u ≠ b v))
      ∪ (Finset.univ.filter (fun b : Fin n → Bool => ¬ (b u ≠ b v))) = Finset.univ := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact em _
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]

lemma half {n : ℕ} (hn : 1 ≤ n) (u v : Fin n) (huv : u ≠ v) :
    (Finset.univ.filter (fun b : Fin n → Bool => b u ≠ b v)).card = 2 ^ (n - 1) := by
  classical
  have hcompl : (Finset.univ.filter (fun b : Fin n → Bool => ¬ (b u ≠ b v))).card
      = (Finset.univ.filter (fun b : Fin n → Bool => b u ≠ b v)).card := by
    refine Finset.card_bij (fun b _ => Function.update b u (!b u)) ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact flip_cross u v huv b hb
    · intro b1 _ b2 _ hb
      funext w
      by_cases hwu : w = u
      · rw [hwu]
        have h1 := congrFun hb u
        simp only [Function.update_self] at h1
        simpa using h1
      · have h1 := congrFun hb w
        simpa only [Function.update_of_ne hwu] using h1
    · intro b hb
      refine ⟨Function.update b u (!b u), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact flip_noncross u v huv b hb
      · funext w
        by_cases hwu : w = u
        · rw [hwu]; simp
        · simp only [Function.update_of_ne hwu]
  have hd := filter_dichotomy u v
  rw [hcompl] at hd
  have hn1 : n = (n - 1) + 1 := by omega
  have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [hn1]
    rw [Nat.pow_succ]
  omega

lemma step_sum {n : ℕ} (E : Finset (Sym2 (Fin n))) (b : Fin n → Bool) :
    (E.filter (fun e => ¬(Sym2.map b e).IsDiag)).card
      = ∑ e ∈ E, if ¬(Sym2.map b e).IsDiag then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma swap_sum {n : ℕ} (E : Finset (Sym2 (Fin n))) :
    (∑ b : Fin n → Bool, (E.filter (fun e => ¬(Sym2.map b e).IsDiag)).card)
      = ∑ e ∈ E, (Finset.univ.filter (fun b : Fin n → Bool => ¬(Sym2.map b e).IsDiag)).card := by
  calc (∑ b : Fin n → Bool, (E.filter (fun e => ¬(Sym2.map b e).IsDiag)).card)
      = ∑ b : Fin n → Bool, ∑ e ∈ E, if ¬(Sym2.map b e).IsDiag then 1 else 0 := by
        exact Finset.sum_congr rfl (fun b _ => step_sum E b)
    _ = ∑ e ∈ E, ∑ b : Fin n → Bool, if ¬(Sym2.map b e).IsDiag then 1 else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ e ∈ E, (Finset.univ.filter (fun b : Fin n → Bool => ¬(Sym2.map b e).IsDiag)).card := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]

end PEqualNP.Outside.L_meta_7850

theorem PEqualNP.Outside.L_meta_7850 :
    ∀ (x1 : ℕ) (x2 : Finset (Sym2 (Fin x1))),
      (∀ x3 ∈ x2, ¬x3.IsDiag) →
      ∃ (x4 : Fin x1 → Bool), x2.card ≤ 2 * {x5 ∈ x2 | ¬(Sym2.map x4 x5).IsDiag}.card := by
  intro n E hnd
  classical
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have hcard0 : E.card = 0 := by
      have hle : E.card ≤ (Finset.univ : Finset (Sym2 (Fin 0))).card := Finset.card_le_univ E
      have hz : (Finset.univ : Finset (Sym2 (Fin 0))).card = 0 := by
        rw [Finset.card_univ, Sym2.card]
        norm_num
      omega
    exact ⟨fun _ => false, by rw [hcard0]; simp⟩
  · set cross : (Fin n → Bool) → ℕ :=
      fun b => (E.filter (fun e => ¬(Sym2.map b e).IsDiag)).card with hcross
    have hterm : ∀ e ∈ E,
        (Finset.univ.filter (fun b : Fin n → Bool => ¬(Sym2.map b e).IsDiag)).card = 2 ^ (n - 1) := by
      intro e he
      have hne := PEqualNP.Outside.L_meta_7850.out_ne (n := n) (x := e) (hnd e he)
      have hcongr : (Finset.univ.filter (fun b : Fin n → Bool => ¬(Sym2.map b e).IsDiag)).card
          = (Finset.univ.filter (fun b : Fin n → Bool => b e.out.fst ≠ b e.out.snd)).card := by
        congr 1
        ext b
        rw [Finset.mem_filter, Finset.mem_filter,
          PEqualNP.Outside.L_meta_7850.map_isDiag_iff (hnd e he)]
      rw [hcongr]
      exact PEqualNP.Outside.L_meta_7850.half hn e.out.fst e.out.snd hne
    have hsum : (∑ b : Fin n → Bool, cross b) = E.card * 2 ^ (n - 1) := by
      rw [hcross, PEqualNP.Outside.L_meta_7850.swap_sum E, Finset.sum_congr rfl hterm,
        Finset.sum_const, smul_eq_mul]
    have hnonempty : (Finset.univ : Finset (Fin n → Bool)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact ⟨fun _ => false⟩
    by_contra hcon
    push_neg at hcon
    have hstrict : (∑ b : Fin n → Bool, 2 * cross b) < (∑ _b : Fin n → Bool, E.card) := by
      apply Finset.sum_lt_sum_of_nonempty hnonempty
      intro b _
      exact hcon b
    rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, smul_eq_mul] at hstrict
    have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn1]
      rw [Nat.pow_succ]
    nlinarith
