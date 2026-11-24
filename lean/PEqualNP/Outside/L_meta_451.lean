import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_451_aux

lemma block_eq {k A A' p p' : ℕ} (hk : 1 ≤ k)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) (hp1' : 1 ≤ p') (hp2' : p' ≤ 2 * k)
    (h : 2 * k * A + p = 2 * k * A' + p') : A = A' ∧ p = p' := by
  have hkz : (0 : ℤ) < 2 * (k : ℤ) := by omega
  have hz : (2 * (k : ℤ)) * (A : ℤ) + (p : ℤ) = (2 * (k : ℤ)) * (A' : ℤ) + (p' : ℤ) := by
    exact_mod_cast h
  have hp1z : (1 : ℤ) ≤ p := by exact_mod_cast hp1
  have hp2z : (p : ℤ) ≤ 2 * (k : ℤ) := by exact_mod_cast hp2
  have hp1z' : (1 : ℤ) ≤ p' := by exact_mod_cast hp1'
  have hp2z' : (p' : ℤ) ≤ 2 * (k : ℤ) := by exact_mod_cast hp2'
  have hA : A = A' := by
    rcases le_total A A' with hle | hle
    · have hd : (2 * (k : ℤ)) * ((A' : ℤ) - A) = (p : ℤ) - p' := by nlinarith
      have hd0 : (A' : ℤ) - A = 0 := by
        by_contra hne
        have hpos : (1 : ℤ) ≤ (A' : ℤ) - A := by omega
        have hge : (2 * (k : ℤ)) ≤ (2 * (k : ℤ)) * ((A' : ℤ) - A) := by
          have := mul_le_mul_of_nonneg_left hpos (le_of_lt hkz)
          simpa using this
        have hlt : (p : ℤ) - p' < 2 * (k : ℤ) := by omega
        nlinarith
      omega
    · have hd : (2 * (k : ℤ)) * ((A : ℤ) - A') = (p' : ℤ) - p := by nlinarith
      have hd0 : (A : ℤ) - A' = 0 := by
        by_contra hne
        have hpos : (1 : ℤ) ≤ (A : ℤ) - A' := by omega
        have hge : (2 * (k : ℤ)) ≤ (2 * (k : ℤ)) * ((A : ℤ) - A') := by
          have := mul_le_mul_of_nonneg_left hpos (le_of_lt hkz)
          simpa using this
        have hlt : (p' : ℤ) - p < 2 * (k : ℤ) := by omega
        nlinarith
      omega
  subst hA
  exact ⟨rfl, by omega⟩

lemma base_inj {m : ℕ} {u v u' v' : Fin m}
    (h : u.val * m + v.val = u'.val * m + v'.val) : u = u' ∧ v = v' := by
  have hm : 0 < m := by omega
  have hq : u.val = u'.val := by
    have h1 : (u.val * m + v.val) / m = u.val := by
      rw [Nat.mul_comm u.val m, Nat.mul_add_div hm u.val v.val, Nat.div_eq_of_lt v.isLt,
        Nat.add_zero]
    have h2 : (u'.val * m + v'.val) / m = u'.val := by
      rw [Nat.mul_comm u'.val m, Nat.mul_add_div hm u'.val v'.val, Nat.div_eq_of_lt v'.isLt,
        Nat.add_zero]
    rw [← h1, h, h2]
  have hv : v.val = v'.val := by
    rw [hq] at h
    omega
  exact ⟨Fin.ext hq, Fin.ext hv⟩

end PEqualNP.Outside.L_meta_451_aux

open PEqualNP.Outside.L_meta_451_aux

theorem PEqualNP.Outside.L_meta_451 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
      (S : SimpleGraph (Fin (m + 2 * k * (m * m)))),
      1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        Q u v p x ↔
          (p = 0 ∧ x.val = u.val) ∨
          (p = 2 * k + 1 ∧ x.val = v.val) ∨
          (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      (∀ x y : Fin (m + 2 * k * (m * m)),
        S.Adj x y ↔
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
            ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) →
      ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x →
        (S.neighborSet x).ncard = 2 := by
  intro m k H Q S hk hQ hS u v p x huv hAdj hp1 hp2 hx
  let base : Fin m → Fin m → ℕ := fun a b => m + 2 * k * (a.val * m + b.val)
  have hxval : x.val + 1 = base u v + p := by
    rcases (hQ u v p x).1 hx with ⟨hp0, _⟩ | ⟨hpe, _⟩ | ⟨_, _, hval⟩
    · omega
    · omega
    · simpa [base] using hval
  have hbase : m ≤ base u v := by
    simp [base]
  have hxge : m ≤ x.val := by
    have := hxval
    omega
  have inner_unique : ∀ (a b a' b' : Fin m) (q q' : ℕ) (y : Fin (m + 2 * k * (m * m))),
      1 ≤ q → q ≤ 2 * k → 1 ≤ q' → q' ≤ 2 * k →
      Q a b q y → Q a' b' q' y → a = a' ∧ b = b' ∧ q = q' := by
    intro a b a' b' q q' y hq1 hq2 hq1' hq2' hqy hqy'
    have hyval : y.val + 1 = base a b + q := by
      rcases (hQ a b q y).1 hqy with ⟨hp0, _⟩ | ⟨hpe, _⟩ | ⟨_, _, hval⟩
      · omega
      · omega
      · simpa [base] using hval
    have hyval' : y.val + 1 = base a' b' + q' := by
      rcases (hQ a' b' q' y).1 hqy' with ⟨hp0, _⟩ | ⟨hpe, _⟩ | ⟨_, _, hval⟩
      · omega
      · omega
      · simpa [base] using hval
    have hblock : 2 * k * (a.val * m + b.val) + q = 2 * k * (a'.val * m + b'.val) + q' := by
      have h1 := hyval
      have h2 := hyval'
      simp [base] at h1 h2
      omega
    obtain ⟨hA, hq⟩ := block_eq hk hq1 hq2 hq1' hq2' hblock
    obtain ⟨ha, hb⟩ := base_inj hA
    exact ⟨ha, hb, hq⟩
  
  have hA_lt : u.val * m + v.val < m * m := by
    nlinarith [u.isLt, v.isLt]
  let left : Fin (m + 2 * k * (m * m)) :=
    if h : p = 1 then ⟨u.val, by omega⟩ else ⟨x.val - 1, by omega⟩
  let right : Fin (m + 2 * k * (m * m)) :=
    if h : p = 2 * k then ⟨v.val, by omega⟩
    else ⟨x.val + 1, by
      have hp_lt : p < 2 * k := by omega
      have hx := hxval
      simp [base] at hx
      nlinarith⟩
  have hQ_left : Q u v (p - 1) left := by
    by_cases hp1' : p = 1
    · have hleft : left = ⟨u.val, by omega⟩ := by apply Fin.ext; simp [left, dif_pos hp1']
      have hp0 : p - 1 = 0 := by omega
      rw [hp0, hleft, hQ u v 0 ⟨u.val, by omega⟩]
      exact Or.inl ⟨rfl, rfl⟩
    · have hleftval : left.val = x.val - 1 := by simp [left, dif_neg hp1']
      rw [hQ u v (p - 1) left]
      refine Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)
      have hx := hxval
      simp [base] at hx
      simp [hleftval, base]
      omega
  have hQ_right : Q u v (p + 1) right := by
    by_cases hpk : p = 2 * k
    · have hright : right = ⟨v.val, by omega⟩ := by apply Fin.ext; simp [right, dif_pos hpk]
      have hp1k : p + 1 = 2 * k + 1 := by omega
      rw [hright, hp1k, hQ u v (2 * k + 1) ⟨v.val, by omega⟩]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hrightval : right.val = x.val + 1 := by simp [right, dif_neg hpk]
      rw [hQ u v (p + 1) right]
      refine Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)
      have hx := hxval
      simp [base] at hx
      simp [hrightval, base]
      omega
  have hS_left : S.Adj x left := by
    refine (hS x left).2 ⟨u, v, huv, hAdj, p - 1, by omega, ?_⟩
    refine Or.inr ⟨hQ_left, ?_⟩
    have hp : (p - 1) + 1 = p := Nat.sub_add_cancel hp1
    simpa [hp] using hx
  have hS_right : S.Adj x right := by
    refine (hS x right).2 ⟨u, v, huv, hAdj, p, hp2, Or.inl ⟨hx, hQ_right⟩⟩
  have q_bounds : ∀ (a b : Fin m) (r : ℕ), Q a b r x → 1 ≤ r ∧ r ≤ 2 * k := by
    intro a b r hr
    rcases (hQ a b r x).1 hr with ⟨rfl, hzv⟩ | ⟨hpe, hzv⟩ | ⟨h1, h2, _⟩
    · omega
    · omega
    · exact ⟨h1, h2⟩
  have adj_iff : ∀ y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ y = left ∨ y = right := by
    intro y
    constructor
    · intro hxy
      obtain ⟨u', v', huv', hAdj', q, hq, hdisj⟩ := (hS x y).1 hxy
      rcases hdisj with ⟨hqx, hqy⟩ | ⟨hqy, hqx⟩
      · have hqb := q_bounds u' v' q hqx
        obtain ⟨rfl, rfl, hpq⟩ := inner_unique u v u' v' p q x hp1 hp2 hqb.1 hqb.2 hx hqx
        have hqyp : Q u v (p + 1) y := by simpa [← hpq] using hqy
        by_cases hpk : p = 2 * k
        · have hyv : y.val = v.val := by
            rcases (hQ u v (p + 1) y).1 hqyp with ⟨h0, _⟩ | ⟨hpe, hyv⟩ | ⟨h1, h2, _⟩
            · omega
            · exact hyv
            · omega
          have hyright : y = right := by
            simp [right, hpk]
            exact Fin.ext hyv
          exact Or.inr hyright
        · have hyval : y.val = x.val + 1 := by
            rcases (hQ u v (p + 1) y).1 hqyp with ⟨h0, _⟩ | ⟨hpe, _⟩ | ⟨h1, h2, hval⟩
            · omega
            · omega
            · have hx := hxval
              simp [base] at hval hx
              omega
          have hyright : y = right := by
            simp [right, hpk]
            exact Fin.ext hyval
          exact Or.inr hyright
      · have hqb := q_bounds u' v' (q + 1) hqx
        obtain ⟨rfl, rfl, hpq⟩ := inner_unique u v u' v' p (q + 1) x hp1 hp2 hqb.1 hqb.2 hx hqx
        have hq_eq : q = p - 1 := by omega
        have hqyp : Q u v (p - 1) y := by simpa [hq_eq] using hqy
        by_cases hp1' : p = 1
        · have hyu : y.val = u.val := by
            rcases (hQ u v (p - 1) y).1 hqyp with ⟨h0, hyu⟩ | ⟨hpe, _⟩ | ⟨h1, h2, _⟩
            · exact hyu
            · omega
            · omega
          have hyleft : y = left := by
            simp [left, hp1']
            exact Fin.ext hyu
          exact Or.inl hyleft
        · have hyval : y.val = x.val - 1 := by
            rcases (hQ u v (p - 1) y).1 hqyp with ⟨h0, _⟩ | ⟨hpe, _⟩ | ⟨h1, h2, hval⟩
            · omega
            · omega
            · have hx := hxval
              simp [base] at hval hx
              omega
          have hyleft : y = left := by
            simp [left, hp1']
            exact Fin.ext hyval
          exact Or.inl hyleft
    · intro hy
      rcases hy with rfl | rfl
      · exact hS_left
      · exact hS_right
  have hneigh : S.neighborSet x = {left, right} := by
    ext y
    rw [SimpleGraph.mem_neighborSet, adj_iff y]
    simp
  have hne : left ≠ right := by
    intro h
    by_cases hp1' : p = 1
    · have hl : left = ⟨u.val, by omega⟩ := by apply Fin.ext; simp [left, dif_pos hp1']
      by_cases hpk : p = 2 * k
      · omega
      · have hr : right = ⟨x.val + 1, by
            have hp_lt : p < 2 * k := by omega
            have hx := hxval
            simp [base] at hx
            nlinarith⟩ := by apply Fin.ext; simp [right, dif_neg hpk]
        have hv : u.val = x.val + 1 := by
          rw [hl, hr] at h
          exact congrArg Fin.val h
        omega
    · have hl : left = ⟨x.val - 1, by omega⟩ := by apply Fin.ext; simp [left, dif_neg hp1']
      by_cases hpk : p = 2 * k
      · have hr : right = ⟨v.val, by omega⟩ := by apply Fin.ext; simp [right, dif_pos hpk]
        have hv : x.val - 1 = v.val := by
          rw [hl, hr] at h
          exact congrArg Fin.val h
        omega
      · have hr : right = ⟨x.val + 1, by
            have hp_lt : p < 2 * k := by omega
            have hx := hxval
            simp [base] at hx
            nlinarith⟩ := by apply Fin.ext; simp [right, dif_neg hpk]
        have hv : x.val - 1 = x.val + 1 := by
          rw [hl, hr] at h
          exact congrArg Fin.val h
        omega
  rw [hneigh, Set.ncard_pair hne]
