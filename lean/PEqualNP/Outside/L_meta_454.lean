import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_454_aux

lemma dec (K m a b i a' b' i' : ℕ) (hb : b < m) (hb' : b' < m) (hi : i < K) (hi' : i' < K)
    (h : K * (a * m + b) + i = K * (a' * m + b') + i') : a = a' ∧ b = b' ∧ i = i' := by
  have hK : 0 < K := by omega
  have hm : 0 < m := by omega
  have e1 : (K * (a * m + b) + i) / K = a * m + b := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e2 : (K * (a' * m + b') + i') / K = a' * m + b' := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hi', Nat.add_zero]
  have e3 : (K * (a * m + b) + i) % K = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have e4 : (K * (a' * m + b') + i') % K = i' := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
  have hE : a * m + b = a' * m + b' := by rw [← e1, ← e2, h]
  have hI : i = i' := by rw [← e3, ← e4, h]
  have f1 : (a * m + b) / m = a := by
    rw [Nat.mul_comm a m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb, Nat.add_zero]
  have f2 : (a' * m + b') / m = a' := by
    rw [Nat.mul_comm a' m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb', Nat.add_zero]
  have f3 : (a * m + b) % m = b := by
    rw [Nat.mul_comm a m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have f4 : (a' * m + b') % m = b' := by
    rw [Nat.mul_comm a' m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
  refine ⟨?_, ?_, hI⟩
  · rw [← f1, ← f2, hE]
  · rw [← f3, ← f4, hE]

def enc (m k : ℕ) (w z : Fin m) : ℕ :=
  if w < z then m + 2 * k * (w.val * m + z.val)
  else m + 2 * k * (z.val * m + w.val) + (2 * k - 1)

lemma bound (m k a b i : ℕ) (ha : a < m) (hb : b < m) (hi : i < 2 * k) :
    m + 2 * k * (a * m + b) + i < m + 2 * k * (m * m) := by
  have h1 : (a + 1) * m ≤ m * m := Nat.mul_le_mul_right m ha
  have h1' : (a + 1) * m = a * m + m := by ring
  have h2 : 2 * k * (a * m + b + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ (by omega)
  have h3 : 2 * k * (a * m + b + 1) = 2 * k * (a * m + b) + 2 * k := by ring
  omega

lemma enc_lt (m k : ℕ) (hk : 1 ≤ k) (w z : Fin m) : enc m k w z < m + 2 * k * (m * m) := by
  unfold enc
  split_ifs
  · have := bound m k w.val z.val 0 w.isLt z.isLt (by omega)
    omega
  · exact bound m k z.val w.val (2 * k - 1) z.isLt w.isLt (by omega)

def f (m k : ℕ) (hk : 1 ≤ k) (w z : Fin m) : Fin (m + 2 * k * (m * m)) :=
  ⟨enc m k w z, enc_lt m k hk w z⟩

lemma f_inj (m k : ℕ) (hk : 1 ≤ k) (w : Fin m) : Function.Injective (f m k hk w) := by
  intro z z' h
  have h' : enc m k w z = enc m k w z' := congrArg Fin.val h
  unfold enc at h'
  have hw := w.isLt
  have hz := z.isLt
  have hz' := z'.isLt
  apply Fin.ext
  split_ifs at h' with h1 h2 h2
  · have := dec (2 * k) m w.val z.val 0 w.val z'.val 0 hz hz' (by omega) (by omega) (by omega)
    omega
  · have := dec (2 * k) m w.val z.val 0 z'.val w.val (2 * k - 1) hz hw (by omega) (by omega) (by omega)
    omega
  · have := dec (2 * k) m z.val w.val (2 * k - 1) w.val z'.val 0 hw hz' (by omega) (by omega) (by omega)
    omega
  · have := dec (2 * k) m z.val w.val (2 * k - 1) z'.val w.val (2 * k - 1) hw hw (by omega) (by omega) (by omega)
    omega

end PEqualNP.Outside.L_meta_454_aux

open PEqualNP.Outside.L_meta_454_aux in
theorem PEqualNP.Outside.L_meta_454 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ u : Fin m, (S.neighborSet (Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) u)).ncard = (H.neighborSet u).ncard := by
  intro m k H Q S hk hQ hS u
  have key : S.neighborSet (Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) u) =
      (f m k hk u) '' (H.neighborSet u) := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, Set.mem_image]
    have hW : (Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) u).val = u.val := rfl
    have hul := u.isLt
    constructor
    · intro hx
      rw [hS] at hx
      obtain ⟨a, b, hab, hadj, p, hp, hq⟩ := hx
      simp only [hQ] at hq
      rw [hW] at hq
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases h1 with ⟨hp0, hu⟩ | ⟨hp0, hu⟩ | ⟨hp1, hp2, hu⟩
        · have hua : u = a := Fin.ext hu
          subst hua
          refine ⟨b, hadj, Fin.ext ?_⟩
          show enc m k u b = x.val
          unfold enc
          simp only [hab, ite_true]
          rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩ <;> omega
        · omega
        · omega
      · rcases h2 with ⟨hp0, hu⟩ | ⟨hp0, hu⟩ | ⟨hp1, hp2, hu⟩
        · omega
        · have hub : u = b := Fin.ext hu
          subst hub
          refine ⟨a, hadj.symm, Fin.ext ?_⟩
          show enc m k u a = x.val
          unfold enc
          have hn : ¬ u < a := not_lt.mpr hab.le
          simp only [hn, ite_false]
          rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩ <;> omega
        · omega
    · rintro ⟨z, hz, rfl⟩
      rw [hS]
      have hval : (f m k hk u z).val = enc m k u z := rfl
      by_cases hlt : u < z
      · refine ⟨u, z, hlt, hz, 0, by omega, Or.inl ⟨?_, ?_⟩⟩
        · rw [hQ]
          left
          exact ⟨rfl, rfl⟩
        · rw [hQ]
          right
          right
          refine ⟨by omega, by omega, ?_⟩
          rw [hval]
          unfold enc
          simp only [hlt, ite_true]
      · have hne : u ≠ z := hz.ne
        have hzu : z < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
        refine ⟨z, u, hzu, hz.symm, 2 * k, le_refl _, Or.inr ⟨?_, ?_⟩⟩
        · rw [hQ]
          right
          right
          refine ⟨by omega, le_refl _, ?_⟩
          rw [hval]
          unfold enc
          simp only [hlt, ite_false]
          omega
        · rw [hQ]
          right
          left
          exact ⟨rfl, rfl⟩
  rw [key, Set.ncard_image_of_injective _ (f_inj m k hk u)]
