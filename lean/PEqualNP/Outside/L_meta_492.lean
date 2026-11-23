import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

namespace PEqualNP.Outside

private lemma subdiv492_div_mod {m k u v i : ℕ} (hk : 1 ≤ k) (hv : v < m) (hi : i < 2 * k) :
    ((m + 2 * k * (u * m + v) + i - m) / (2 * k) / m = u) ∧
    ((m + 2 * k * (u * m + v) + i - m) / (2 * k) % m = v) ∧
    ((m + 2 * k * (u * m + v) + i - m) % (2 * k) = i) := by
  have h1 : m + 2 * k * (u * m + v) + i - m = 2 * k * (u * m + v) + i := by omega
  rw [h1]
  have h2k : 0 < 2 * k := by omega
  have hdiv : (2 * k * (u * m + v) + i) / (2 * k) = u * m + v := by
    rw [Nat.mul_add_div h2k, Nat.div_eq_of_lt hi, Nat.add_zero]
  have hmod : (2 * k * (u * m + v) + i) % (2 * k) = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have hm : 0 < m := by omega
  rw [hdiv, hmod]
  refine ⟨?_, ?_, rfl⟩
  · rw [Nat.mul_comm u m, Nat.mul_add_div hm, Nat.div_eq_of_lt hv, Nat.add_zero]
  · rw [Nat.mul_comm u m, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]

private def subdiv492Phi (m k : ℕ) (x z : Fin (m + 2 * k * m * m)) : ℕ :=
  if z.val < m then
    if z.val = x.val then 0 else 2 * k + 1
  else
    let q := (z.val - m) / (2 * k)
    let r := (z.val - m) % (2 * k)
    if q / m = x.val then r + 1
    else if q % m = x.val then 2 * k - r
    else 2 * k + 1

private lemma ncard_le_two_of_subset_pair {α : Type*} [Finite α] (s : Set α) (a b : α)
    (h : s ⊆ {a, b}) : s.ncard ≤ 2 := by
  calc s.ncard ≤ ({a, b} : Set α).ncard := Set.ncard_le_ncard h (Set.toFinite _)
    _ ≤ ({b} : Set α).ncard + 1 := Set.ncard_insert_le a {b}
    _ = 2 := by simp

theorem L_meta_492 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k →
      ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
        S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
            ∃ i : Fin (2 * k),
              x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
              ((i.val = 0 ∧ y.val = u.val) ∨
                (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
                (i.val + 1 = 2 * k ∧ y.val = v.val))) →
        ∀ u v : Fin (m + 2 * k * m * m),
          u ≠ v → 3 ≤ (S.neighborSet u).ncard → 3 ≤ (S.neighborSet v).ncard →
          ∀ p : S.Walk u v, 2 * k + 1 ≤ p.length := by
  intro k m H hk S hS u v huv hu3 hv3 walk
  let R : Fin (m + 2 * k * m * m) → Fin (m + 2 * k * m * m) → Prop :=
    fun x y =>
      ∃ u0 v0 : Fin m, u0 < v0 ∧ H.Adj u0 v0 ∧
        ∃ i : Fin (2 * k),
          x.val = m + 2 * k * (u0.val * m + v0.val) + i.val ∧
          ((i.val = 0 ∧ y.val = u0.val) ∨
            (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u0.val * m + v0.val) + i.val + 1) ∨
            (i.val + 1 = 2 * k ∧ y.val = v0.val))
  have hS_adj : ∀ a b : Fin (m + 2 * k * m * m), S.Adj a b ↔ a ≠ b ∧ (R a b ∨ R b a) := by
    intro a b
    rw [hS, SimpleGraph.fromRel_adj]
  have hdeg_lt_m : ∀ w : Fin (m + 2 * k * m * m), 3 ≤ (S.neighborSet w).ncard → w.val < m := by
    intro w hw3
    by_contra hge
    have hwm : m ≤ w.val := by omega
    have hm_pos : 0 < m := by
      by_contra hm0
      have hm_eq : m = 0 := by omega
      have hwlt := w.isLt
      have h0 : m + 2 * k * m * m = 0 := by simp [hm_eq]
      omega
    have h2k : 0 < 2 * k := by omega
    let d := w.val - m
    let q := d / (2 * k)
    let r := d % (2 * k)
    let u0 := q / m
    let v0 := q % m
    have hd_lt : d < 2 * k * (m * m) := by
      have hwlt := w.isLt
      have hmul : 2 * k * m * m = 2 * k * (m * m) := Nat.mul_assoc _ _ _
      omega
    have hq_lt : q < m * m := Nat.div_lt_of_lt_mul hd_lt
    have hu0_lt : u0 < m := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hv0_lt : v0 < m := Nat.mod_lt q hm_pos
    have hr_lt : r < 2 * k := Nat.mod_lt d h2k
    have hw_decomp : w.val = m + 2 * k * (u0 * m + v0) + r := by
      have h1 : 2 * k * q + r = d := Nat.div_add_mod d (2 * k)
      have h2 : m * u0 + v0 = q := Nat.div_add_mod q m
      have h3 : u0 * m + v0 = q := by rw [Nat.mul_comm]; exact h2
      rw [h3]
      omega
    have hR_left : ∀ z : Fin (m + 2 * k * m * m), R w z →
        (r = 0 ∧ z.val = u0) ∨
        (r + 1 < 2 * k ∧ z.val = m + 2 * k * (u0 * m + v0) + r + 1) ∨
        (r + 1 = 2 * k ∧ z.val = v0) := by
      rintro z ⟨ua, va, _, _, i, hwx, hbr⟩
      have hdm := subdiv492_div_mod (u := ua.val) hk va.isLt i.isLt
      rw [← hwx] at hdm
      have hua : ua.val = u0 := hdm.1.symm
      have hva : va.val = v0 := hdm.2.1.symm
      have hi : i.val = r := hdm.2.2.symm
      rcases hbr with ⟨hi0, hzy⟩ | ⟨hi1, hzy⟩ | ⟨hi2, hzy⟩
      · left; exact ⟨by omega, by omega⟩
      · right; left; exact ⟨by omega, by omega⟩
      · right; right; exact ⟨by omega, by omega⟩
    have hR_right : ∀ z : Fin (m + 2 * k * m * m), R z w →
        0 < r ∧ z.val = m + 2 * k * (u0 * m + v0) + (r - 1) := by
      rintro z ⟨ua, va, _, _, i, hzx, hbr⟩
      rcases hbr with ⟨_, hwy⟩ | ⟨hi1, hwy⟩ | ⟨_, hwy⟩
      · have : w.val < m := by omega
        omega
      · have hdm := subdiv492_div_mod (u := ua.val) hk va.isLt hi1
        have hwy' : w.val = m + 2 * k * (ua.val * m + va.val) + (i.val + 1) := by omega
        rw [← hwy'] at hdm
        have hua : ua.val = u0 := hdm.1.symm
        have hva : va.val = v0 := hdm.2.1.symm
        have hi : i.val + 1 = r := hdm.2.2.symm
        exact ⟨by omega, by omega⟩
      · have : w.val < m := by omega
        omega
    have hle2 : (S.neighborSet w).ncard ≤ 2 := by
      by_cases hr0 : r = 0
      · have hlt_next : m + 2 * k * (u0 * m + v0) + 1 < m + 2 * k * m * m := by
          have : r + 1 < 2 * k := by omega
          have hmul : 2 * k * m * m = 2 * k * (m * m) := Nat.mul_assoc _ _ _
          have : u0 * m + v0 + 1 ≤ m * m := by
            have : u0 * m + v0 = q := by rw [Nat.mul_comm]; exact Nat.div_add_mod q m
            omega
          have hbound : 2 * k * (u0 * m + v0) + 2 * k ≤ 2 * k * (m * m) := by
            have := Nat.mul_le_mul_left (2 * k) this
            linarith
          omega
        let a : Fin (m + 2 * k * m * m) := ⟨u0, by omega⟩
        let b : Fin (m + 2 * k * m * m) := ⟨m + 2 * k * (u0 * m + v0) + 1, hlt_next⟩
        apply ncard_le_two_of_subset_pair _ a b
        intro z hz
        have hadj : S.Adj w z := hz
        rcases ((hS_adj w z).mp hadj).2 with h1 | h2
        · rcases hR_left z h1 with ⟨_, hzu⟩ | ⟨_, hzn⟩ | ⟨hbot, _⟩
          · left; exact Fin.ext hzu
          · right; exact Fin.ext (by dsimp [b]; omega)
          · omega
        · have := hR_right z h2
          omega
      · by_cases hrtop : r + 1 = 2 * k
        · let a : Fin (m + 2 * k * m * m) := ⟨m + 2 * k * (u0 * m + v0) + (r - 1), by omega⟩
          let b : Fin (m + 2 * k * m * m) := ⟨v0, by omega⟩
          apply ncard_le_two_of_subset_pair _ a b
          intro z hz
          have hadj : S.Adj w z := hz
          rcases ((hS_adj w z).mp hadj).2 with h1 | h2
          · rcases hR_left z h1 with ⟨h0, _⟩ | ⟨hlt, _⟩ | ⟨_, hzv⟩
            · omega
            · omega
            · right; exact Fin.ext hzv
          · have ⟨_, hzp⟩ := hR_right z h2
            left; exact Fin.ext hzp
        · have hlt_next : m + 2 * k * (u0 * m + v0) + r + 1 < m + 2 * k * m * m := by
            have : r + 1 < 2 * k := by omega
            have hmul : 2 * k * m * m = 2 * k * (m * m) := Nat.mul_assoc _ _ _
            have hq_le : u0 * m + v0 + 1 ≤ m * m := by
              have : u0 * m + v0 = q := by rw [Nat.mul_comm]; exact Nat.div_add_mod q m
              omega
            have hbound : 2 * k * (u0 * m + v0) + 2 * k ≤ 2 * k * (m * m) := by
              have := Nat.mul_le_mul_left (2 * k) hq_le
              linarith
            omega
          let a : Fin (m + 2 * k * m * m) := ⟨m + 2 * k * (u0 * m + v0) + (r - 1), by omega⟩
          let b : Fin (m + 2 * k * m * m) := ⟨m + 2 * k * (u0 * m + v0) + r + 1, hlt_next⟩
          apply ncard_le_two_of_subset_pair _ a b
          intro z hz
          have hadj : S.Adj w z := hz
          rcases ((hS_adj w z).mp hadj).2 with h1 | h2
          · rcases hR_left z h1 with ⟨h0, _⟩ | ⟨_, hzn⟩ | ⟨htop, _⟩
            · omega
            · right; exact Fin.ext hzn
            · omega
          · have ⟨_, hzp⟩ := hR_right z h2
            left; exact Fin.ext hzp
    omega
  have hum : u.val < m := hdeg_lt_m u hu3
  have hvm : v.val < m := hdeg_lt_m v hv3
  have hR_lip : ∀ a b : Fin (m + 2 * k * m * m), R a b →
      subdiv492Phi m k u b ≤ subdiv492Phi m k u a + 1 ∧
      subdiv492Phi m k u a ≤ subdiv492Phi m k u b + 1 := by
    rintro a b ⟨ua, va, huava, _, i, ha_eq, hbr⟩
    have huava_ne : ua.val ≠ va.val := by
      have : ua.val < va.val := huava
      omega
    have hdm_a := subdiv492_div_mod (u := ua.val) hk va.isLt i.isLt
    rw [← ha_eq] at hdm_a
    have hphi_a : subdiv492Phi m k u a =
        if ua.val = u.val then i.val + 1
        else if va.val = u.val then 2 * k - i.val
        else 2 * k + 1 := by
      unfold subdiv492Phi
      have ha_ge : ¬ a.val < m := by omega
      rw [if_neg ha_ge]
      simp only [hdm_a.1, hdm_a.2.1, hdm_a.2.2]
    rcases hbr with ⟨hi0, hb_eq⟩ | ⟨hi1, hb_eq⟩ | ⟨hi2, hb_eq⟩
    · have hphi_b : subdiv492Phi m k u b =
          if ua.val = u.val then 0 else 2 * k + 1 := by
        unfold subdiv492Phi
        have hb_lt : b.val < m := by omega
        rw [if_pos hb_lt, hb_eq]
      rw [hphi_a, hphi_b]
      split_ifs <;> omega
    · have hdm_b := subdiv492_div_mod (u := ua.val) hk va.isLt hi1
      have hb_eq' : b.val = m + 2 * k * (ua.val * m + va.val) + (i.val + 1) := by omega
      rw [← hb_eq'] at hdm_b
      have hphi_b : subdiv492Phi m k u b =
          if ua.val = u.val then i.val + 2
          else if va.val = u.val then 2 * k - (i.val + 1)
          else 2 * k + 1 := by
        unfold subdiv492Phi
        have hb_ge : ¬ b.val < m := by omega
        rw [if_neg hb_ge]
        simp only [hdm_b.1, hdm_b.2.1, hdm_b.2.2]
      rw [hphi_a, hphi_b]
      split_ifs <;> omega
    · have hphi_b : subdiv492Phi m k u b =
          if va.val = u.val then 0 else 2 * k + 1 := by
        unfold subdiv492Phi
        have hb_lt : b.val < m := by omega
        rw [if_pos hb_lt, hb_eq]
      rw [hphi_a, hphi_b]
      split_ifs <;> omega
  have hstep : ∀ a b : Fin (m + 2 * k * m * m), S.Adj a b →
      subdiv492Phi m k u b ≤ subdiv492Phi m k u a + 1 := by
    intro a b hab
    rcases ((hS_adj a b).mp hab).2 with h1 | h2
    · exact (hR_lip a b h1).1
    · exact (hR_lip b a h2).2
  have hwalk : ∀ {a b : Fin (m + 2 * k * m * m)} (w : S.Walk a b),
      subdiv492Phi m k u b ≤ subdiv492Phi m k u a + w.length := by
    intro a b w
    induction w with
    | nil => simp
    | @cons a c b hac w' ih =>
      have h1 := hstep a c hac
      simp only [SimpleGraph.Walk.length_cons]
      omega
  have hbound := hwalk walk
  have hphiu : subdiv492Phi m k u u = 0 := by
    unfold subdiv492Phi
    rw [if_pos hum, if_pos rfl]
  have hphiv : subdiv492Phi m k u v = 2 * k + 1 := by
    unfold subdiv492Phi
    have hne : v.val ≠ u.val := fun h => huv (Fin.ext h).symm
    rw [if_pos hvm, if_neg hne]
  omega

end PEqualNP.Outside
