import Mathlib
import PEqualNP.Defs

private lemma L_meta_451_encode_lt {m k : ℕ} {u v : Fin m} {q : ℕ}
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2 * k) :
    m + 2 * k * (u.val * m + v.val) + q - 1 < m + 2 * k * (m * m) := by
  have hmul : u.val * m + v.val + 1 ≤ m * m := by
    have hu : u.val + 1 ≤ m := u.isLt
    have hv : v.val + 1 ≤ m := v.isLt
    nlinarith
  have h2k : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
    Nat.mul_le_mul_left (2 * k) hmul
  have h2k' : 2 * k * (u.val * m + v.val) + 2 * k = 2 * k * (u.val * m + v.val + 1) := by ring
  omega

private lemma L_meta_451_div_eq {d a₁ b₁ a₂ b₂ : ℕ}
    (hb₁ : b₁ < d) (hb₂ : b₂ < d) (h : d * a₁ + b₁ = d * a₂ + b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have ha : a₁ = a₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : d * (a₁ + 1) ≤ d * a₂ := Nat.mul_le_mul_left d hlt
      nlinarith
    · have : d * (a₂ + 1) ≤ d * a₁ := Nat.mul_le_mul_left d hgt
      nlinarith
  subst ha
  exact ⟨rfl, by omega⟩

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
        u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x → (S.neighborSet x).ncard = 2 := by
  intro m k H Q S hk hQ hS u v p x huv hadj hp1 hp2 hQx
  have hx_eq : x.val + 1 = m + 2 * k * (u.val * m + v.val) + p := by
    rcases (hQ u v p x).mp hQx with ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨_, _, heq⟩
    · omega
    · omega
    · exact heq
  have hQ_exists : ∀ (q : ℕ), q ≤ 2 * k + 1 → ∃ y : Fin (m + 2 * k * (m * m)), Q u v q y := by
    intro q hq
    by_cases hq0 : q = 0
    · subst hq0
      refine ⟨⟨u.val, by omega⟩, (hQ u v 0 _).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · by_cases hqtop : q = 2 * k + 1
      · subst hqtop
        refine ⟨⟨v.val, by omega⟩, (hQ u v (2 * k + 1) _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · have hq1 : 1 ≤ q := by omega
        have hq2 : q ≤ 2 * k := by omega
        refine ⟨⟨m + 2 * k * (u.val * m + v.val) + q - 1, L_meta_451_encode_lt hq1 hq2⟩,
          (hQ u v q _).mpr (Or.inr (Or.inr ⟨hq1, hq2, by dsimp; omega⟩))⟩
  have hQ_uniq : ∀ {u' v' : Fin m} {q : ℕ} {y₁ y₂ : Fin (m + 2 * k * (m * m))},
      Q u' v' q y₁ → Q u' v' q y₂ → y₁ = y₂ := by
    intro u' v' q y₁ y₂ h₁ h₂
    apply Fin.ext
    rcases (hQ u' v' q y₁).mp h₁ with ⟨hq0, e₁⟩ | ⟨hqtop, e₁⟩ | ⟨hq1, hq2, e₁⟩ <;>
      rcases (hQ u' v' q y₂).mp h₂ with ⟨h0, e₂⟩ | ⟨h1, e₂⟩ | ⟨_, _, e₂⟩ <;> omega
  have hQ_decode : ∀ {u' v' : Fin m} {q : ℕ}, Q u' v' q x → u' = u ∧ v' = v ∧ q = p := by
    intro u' v' q hQ'
    have hq_inner : 1 ≤ q ∧ q ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u'.val * m + v'.val) + q := by
      rcases (hQ u' v' q x).mp hQ' with ⟨_, hx'⟩ | ⟨_, hx'⟩ | h
      · have := u'.isLt; omega
      · have := v'.isLt; omega
      · exact h
    obtain ⟨hq1, hq2, hx_eq'⟩ := hq_inner
    have heq1 : 2 * k * (u'.val * m + v'.val) + (q - 1) = 2 * k * (u.val * m + v.val) + (p - 1) := by
      omega
    obtain ⟨huv_eq, hq_sub⟩ := L_meta_451_div_eq (d := 2 * k) (by omega) (by omega) heq1
    have huv_eq' : m * u'.val + v'.val = m * u.val + v.val := by
      linarith [Nat.mul_comm u'.val m, Nat.mul_comm u.val m]
    obtain ⟨hu_eq, hv_eq⟩ := L_meta_451_div_eq (d := m) v'.isLt v.isLt huv_eq'
    exact ⟨Fin.ext hu_eq, Fin.ext hv_eq, by omega⟩
  obtain ⟨a, hQa⟩ := hQ_exists (p - 1) (by omega)
  obtain ⟨b, hQb⟩ := hQ_exists (p + 1) (by omega)
  have hab : a ≠ b := by
    intro h
    subst h
    rcases (hQ u v (p - 1) a).mp hQa with ⟨h1, ea⟩ | ⟨h1, _⟩ | ⟨h1, h2, ea⟩ <;>
      rcases (hQ u v (p + 1) a).mp hQb with ⟨h3, _⟩ | ⟨h3, eb⟩ | ⟨h3, h4, eb⟩
    · omega
    · omega
    · have := u.isLt; omega
    · omega
    · omega
    · omega
    · omega
    · have := v.isLt; omega
    · omega
  have hset : S.neighborSet x = {a, b} := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hxy
      rcases (hS x y).mp hxy with ⟨u', v', _, _, q, _, ⟨hQx', hQy'⟩ | ⟨hQy', hQx'⟩⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hQ_decode hQx'
        exact Or.inr (hQ_uniq hQy' hQb)
      · obtain ⟨rfl, rfl, hqp⟩ := hQ_decode hQx'
        have hq : q = p - 1 := by omega
        subst hq
        exact Or.inl (hQ_uniq hQy' hQa)
    · rintro (rfl | rfl)
      · refine (hS x y).mpr ⟨u, v, huv, hadj, p - 1, by omega, Or.inr ⟨hQa, ?_⟩⟩
        rwa [Nat.sub_add_cancel hp1]
      · exact (hS x y).mpr ⟨u, v, huv, hadj, p, hp2, Or.inl ⟨hQx, hQb⟩⟩
  rw [hset, Set.ncard_pair hab]
