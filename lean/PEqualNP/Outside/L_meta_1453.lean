import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1453_aux

open Finset

lemma geom_sum_lt (n w : ℕ) (hn : 2 ≤ n) :
    (∑ s ∈ Finset.range (w + 1), n ^ s) < 2 * n ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [Finset.sum_range_succ]
      have h1 : 2 * n ^ w ≤ n ^ (w + 1) := by
        calc 2 * n ^ w ≤ n * n ^ w := Nat.mul_le_mul_right _ hn
          _ = n ^ (w + 1) := by rw [pow_succ]; ring
      nlinarith

lemma card_sets_lt (n w : ℕ) (hn : 2 ≤ n) :
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ w)).card
      < 2 ^ (w * Nat.clog 2 n + 1) := by
  classical
  have hdisj : (Finset.range (w + 1) : Set ℕ).PairwiseDisjoint
      (fun s => (Finset.univ : Finset (Fin n)).powersetCard s) := by
    intro s hs t ht hst
    rw [Function.onFun]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_powersetCard] at hx hy
    omega
  have heq : (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ w))
      = (Finset.range (w + 1)).biUnion
          (fun s => (Finset.univ : Finset (Fin n)).powersetCard s) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro h
      exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      omega
  rw [heq, Finset.card_biUnion hdisj]
  calc ∑ s ∈ Finset.range (w + 1),
          ((Finset.univ : Finset (Fin n)).powersetCard s).card
      = ∑ s ∈ Finset.range (w + 1), n.choose s := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.card_powersetCard]
        simp
    _ ≤ ∑ s ∈ Finset.range (w + 1), n ^ s := by
        apply Finset.sum_le_sum
        intro s _
        exact Nat.choose_le_pow n s
    _ < 2 * n ^ w := geom_sum_lt n w hn
    _ ≤ 2 * (2 ^ Nat.clog 2 n) ^ w := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) n) w
    _ = 2 ^ (w * Nat.clog 2 n + 1) := by
        rw [← pow_mul]
        have h2 : 2 * 2 ^ (Nat.clog 2 n * w) = 2 ^ (Nat.clog 2 n * w + 1) := by
          rw [pow_succ]; ring
        rw [h2, Nat.mul_comm (Nat.clog 2 n) w]

noncomputable def pairEquiv {n Q : ℕ} {a b : Fin n} (hab : a ≠ b) :
    {f : Fin n → Fin Q // f a = f b} ≃ ({i : Fin n // i ≠ a} → Fin Q) where
  toFun f i := f.1 i.1
  invFun g := ⟨fun i => if h : i = a then g ⟨b, by simpa using hab.symm⟩ else g ⟨i, h⟩, by
    simp only [dif_pos rfl, dif_neg (hab.symm), dif_pos trivial]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    change (if h : i = a then f.1 b else f.1 i) = f.1 i
    by_cases h : i = a
    · rw [dif_pos h, h]
      exact f.2.symm
    · rw [dif_neg h]
  right_inv g := by
    funext i
    change (if h : (i : Fin n) = a then g ⟨b, by simpa using hab.symm⟩ else
      g ⟨(i : Fin n), h⟩) = g i
    rw [dif_neg i.2]

lemma card_pair (n Q : ℕ) (a b : Fin n) (hab : a ≠ b) :
    (Finset.univ.filter (fun f : Fin n → Fin Q => f a = f b)).card = Q ^ (n - 1) := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (pairEquiv (Q := Q) hab)]
  rw [Fintype.card_fun]
  have hcard : Fintype.card {i : Fin n // i ≠ a} = n - 1 := by
    have h := Fintype.card_subtype_compl (fun i : Fin n => i = a)
    rw [Fintype.card_fin, Fintype.card_subtype_eq] at h
    simpa using h
  rw [hcard]
  simp

def badf (n w : ℕ) (S : Finset (Fin n)) : Finset (Fin n → Fin (w ^ 2)) :=
  Finset.univ.filter (fun f => ¬ Set.InjOn f (S : Set (Fin n)))

def Bad (n w : ℕ) (S : Finset (Fin n)) :
    Finset (Fin (w * Nat.clog 2 n + 1) → Fin n → Fin (w ^ 2)) :=
  Finset.univ.filter (fun c => ∀ j, ¬ Set.InjOn (c j) (S : Set (Fin n)))

lemma card_badf (n w : ℕ) (hn : 2 ≤ n) (hw : 1 ≤ w) (S : Finset (Fin n))
    (hS : S.card ≤ w) : 2 * (badf n w S).card ≤ (w ^ 2) ^ n := by
  classical
  let Q := w ^ 2
  let B : Fin n × Fin n → Finset (Fin n → Fin Q) :=
    fun p => Finset.univ.filter (fun f => f p.1 = f p.2)
  have hQpos : 0 < Q := by positivity
  have hstep1 : 2 * (badf n w S).card
      ≤ ∑ f ∈ badf n w S, (S.offDiag.filter (fun p => f ∈ B p)).card := by
    rw [show 2 * (badf n w S).card = ∑ _f ∈ badf n w S, 2 by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]]
    apply Finset.sum_le_sum
    intro f hf
    have hnb : ¬ Set.InjOn f (S : Set (Fin n)) := (Finset.mem_filter.mp hf).2
    simp only [Set.InjOn] at hnb
    push_neg at hnb
    obtain ⟨a, ha, b, hb, hfab, hab⟩ := hnb
    have hp1 : (a, b) ∈ S.offDiag.filter (fun p => f ∈ B p) := by
      simp only [Finset.mem_filter, Finset.mem_offDiag, B, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨⟨ha, hb, hab⟩, hfab⟩
    have hp2 : (b, a) ∈ S.offDiag.filter (fun p => f ∈ B p) := by
      simp only [Finset.mem_filter, Finset.mem_offDiag, B, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨⟨hb, ha, hab.symm⟩, hfab.symm⟩
    have hne : (a, b) ≠ (b, a) := by
      intro h
      exact hab (congrArg Prod.fst h)
    have h2 := Finset.one_lt_card.mpr ⟨(a, b), hp1, (b, a), hp2, hne⟩
    omega
  have hstep2 : ∑ f ∈ badf n w S, (S.offDiag.filter (fun p => f ∈ B p)).card
      = ∑ p ∈ S.offDiag, ((badf n w S).filter (fun f => f ∈ B p)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hstep3 : ∑ p ∈ S.offDiag, ((badf n w S).filter (fun f => f ∈ B p)).card
      ≤ ∑ p ∈ S.offDiag, (B p).card := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.card_le_card
    intro f hf
    exact (Finset.mem_filter.mp hf).2
  have hBcard : ∀ p ∈ S.offDiag, (B p).card = Q ^ (n - 1) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    exact card_pair n Q p.1 p.2 hne
  have hPcard : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card S
  refine le_of_lt ?_
  calc 2 * (badf n w S).card
      ≤ ∑ p ∈ S.offDiag, (B p).card := le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
    _ = S.offDiag.card * Q ^ (n - 1) := by
        rw [Finset.sum_congr rfl hBcard, Finset.sum_const, smul_eq_mul]
    _ = (S.card * S.card - S.card) * Q ^ (n - 1) := by rw [hPcard]
    _ ≤ (w * w - w) * Q ^ (n - 1) := by
        apply Nat.mul_le_mul_right
        have hid : S.card * S.card - S.card = S.card * (S.card - 1) := by
          rw [Nat.mul_sub_left_distrib]; simp
        have hid2 : w * w - w = w * (w - 1) := by
          rw [Nat.mul_sub_left_distrib]; simp
        rw [hid, hid2]
        exact Nat.mul_le_mul hS (Nat.sub_le_sub_right hS 1)
    _ < (w * w) * Q ^ (n - 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ (pow_pos hQpos _)
        exact Nat.sub_lt (by positivity) (by omega)
    _ = Q * Q ^ (n - 1) := by simp [Q, pow_two]
    _ = Q ^ n := by
        rw [← pow_succ']
        congr 1
        omega


lemma card_Bad (n w : ℕ) (S : Finset (Fin n)) :
    (Bad n w S).card = (badf n w S).card ^ (w * Nat.clog 2 n + 1) := by
  have heq : Bad n w S
      = Fintype.piFinset (fun _ : Fin (w * Nat.clog 2 n + 1) => badf n w S) := by
    ext c
    simp [Bad, badf, Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset_const]

end PEqualNP.Outside.L_meta_1453_aux

open PEqualNP.Outside.L_meta_1453_aux

theorem PEqualNP.Outside.L_meta_1453 : ∀ (n w : ℕ), 2 ≤ n → 1 ≤ w →
    ∃ c : Fin (w * Nat.clog 2 n + 1) → Fin n → Fin (w ^ 2),
      ∀ S : Finset (Fin n), S.card ≤ w →
        ∃ j : Fin (w * Nat.clog 2 n + 1), Set.InjOn (c j) (S : Set (Fin n)) := by
  intro n w hn hw
  classical
  by_contra h
  push_neg at h
  let N := w * Nat.clog 2 n + 1
  let Q := w ^ 2
  let F0 : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => S.card ≤ w)
  have hcover : (Finset.univ : Finset (Fin N → Fin n → Fin Q)) ⊆
      F0.biUnion (fun S => Bad n w S) := by
    intro c _
    obtain ⟨S, hS, hbad⟩ := h c
    refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩, ?_⟩
    simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbad
  have hterm : ∀ S ∈ F0, 2 ^ N * (Bad n w S).card ≤ Q ^ (n * N) := by
    intro S hS
    have hScard : S.card ≤ w := (Finset.mem_filter.mp hS).2
    have hb : 2 * (badf n w S).card ≤ Q ^ n := by
      simpa [Q] using card_badf n w hn hw S hScard
    rw [card_Bad]
    calc 2 ^ N * (badf n w S).card ^ N = (2 * (badf n w S).card) ^ N := by rw [mul_pow]
      _ ≤ (Q ^ n) ^ N := Nat.pow_le_pow_left hb N
      _ = Q ^ (n * N) := by rw [← pow_mul]
  have hsum : 2 ^ N * (∑ S ∈ F0, (Bad n w S).card) ≤ F0.card * Q ^ (n * N) := by
    rw [Finset.mul_sum]
    calc ∑ S ∈ F0, 2 ^ N * (Bad n w S).card ≤ ∑ S ∈ F0, Q ^ (n * N) :=
          Finset.sum_le_sum hterm
      _ = F0.card * Q ^ (n * N) := by rw [Finset.sum_const, smul_eq_mul]
  have hF0 : F0.card < 2 ^ N := by
    simpa [F0, N] using card_sets_lt n w hn
  have hQpos : 0 < Q ^ (n * N) := by positivity
  have hlt : 2 ^ N * (∑ S ∈ F0, (Bad n w S).card) < 2 ^ N * Q ^ (n * N) :=
    lt_of_le_of_lt hsum (Nat.mul_lt_mul_of_pos_right hF0 hQpos)
  have hsumlt : (∑ S ∈ F0, (Bad n w S).card) < Q ^ (n * N) :=
    Nat.lt_of_mul_lt_mul_left hlt
  have hge : Q ^ (n * N) ≤ ∑ S ∈ F0, (Bad n w S).card := by
    calc Q ^ (n * N) = (Finset.univ : Finset (Fin N → Fin n → Fin Q)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun]
          simp [← pow_mul]
      _ ≤ (F0.biUnion (fun S => Bad n w S)).card := Finset.card_le_card hcover
      _ ≤ ∑ S ∈ F0, (Bad n w S).card := Finset.card_biUnion_le
  omega
