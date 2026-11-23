import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

theorem PEqualNP.Outside.L_meta_460 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x ≠ y → 3 ≤ (S.neighborSet x).ncard → 3 ≤ (S.neighborSet y).ncard → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hxy hdegx hdegy w
  have hQ_sub : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))),
      Q u v p z → m ≤ z.val →
      1 ≤ p ∧ p ≤ 2 * k ∧
      p = (z.val - m) % (2 * k) + 1 ∧
      u.val = ((z.val - m) / (2 * k)) / m ∧
      v.val = ((z.val - m) / (2 * k)) % m := by
    intro u v p z hQz hzm
    rcases (hQ u v p z).mp hQz with ⟨_, hzu⟩ | ⟨_, hzv⟩ | ⟨hp1, hp2, hzv⟩
    · have := u.isLt; omega
    · have := v.isLt; omega
    · have hd : z.val - m = (p - 1) + 2 * k * (u.val * m + v.val) := by omega
      have h2k : 0 < 2 * k := by omega
      have hlt : p - 1 < 2 * k := by omega
      have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
      have hmod1 : (z.val - m) % (2 * k) = p - 1 := by
        rw [hd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      have hdiv1 : (z.val - m) / (2 * k) = v.val + m * u.val := by
        rw [hd, Nat.add_mul_div_left _ _ h2k, Nat.div_eq_of_lt hlt, Nat.zero_add,
            Nat.mul_comm u.val m, Nat.add_comm]
      have hdiv2 : ((z.val - m) / (2 * k)) / m = u.val := by
        rw [hdiv1, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt v.isLt, Nat.zero_add]
      have hmod2 : ((z.val - m) / (2 * k)) % m = v.val := by
        rw [hdiv1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]
      refine ⟨hp1, hp2, ?_, hdiv2.symm, hmod2.symm⟩
      omega
  have hQ_unique_pt : ∀ (u v : Fin m) (p : ℕ) (z₁ z₂ : Fin (m + 2 * k * (m * m))),
      Q u v p z₁ → Q u v p z₂ → z₁ = z₂ := by
    intro u v p z₁ z₂ h1 h2
    apply Fin.ext
    rcases (hQ u v p z₁).mp h1 with ⟨hp1, hz1⟩ | ⟨hp1, hz1⟩ | ⟨hp1a, hp1b, hz1⟩ <;>
    rcases (hQ u v p z₂).mp h2 with ⟨hp2, hz2⟩ | ⟨hp2, hz2⟩ | ⟨hp2a, hp2b, hz2⟩ <;>
    omega
  have hsub_ncard : ∀ (s : Set (Fin (m + 2 * k * (m * m)))), s.Subsingleton → s.ncard ≤ 1 := by
    intro s hs
    rcases Set.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · simp
    · have : s = {a} := Set.Subset.antisymm (fun b hb => hs hb ha) (Set.singleton_subset_iff.mpr ha)
      rw [this, Set.ncard_singleton]
  have horig : ∀ z : Fin (m + 2 * k * (m * m)), 3 ≤ (S.neighborSet z).ncard → z.val < m := by
    intro z hdegz
    by_contra hge
    have hzm : m ≤ z.val := Nat.le_of_not_lt hge
    rcases Set.eq_empty_or_nonempty (S.neighborSet z) with hempty | ⟨y₀, hy₀⟩
    · rw [hempty, Set.ncard_empty] at hdegz
      omega
    · have hadj₀ : S.Adj z y₀ := hy₀
      rcases (hS z y₀).mp hadj₀ with ⟨u₀, v₀, _, _, p₀, _, ⟨hQz₀, _⟩ | ⟨_, hQz₀⟩⟩
      · have h0 := hQ_sub u₀ v₀ p₀ z hQz₀ hzm
        have hsub : S.neighborSet z ⊆ {t | Q u₀ v₀ (p₀ + 1) t} ∪ {t | Q u₀ v₀ (p₀ - 1) t} := by
          intro t ht
          rcases (hS z t).mp ht with ⟨u, v, _, _, p, _, ⟨hQz, hQt⟩ | ⟨hQt, hQz⟩⟩
          · have h1 := hQ_sub u v p z hQz hzm
            have hu : u = u₀ := Fin.ext (by omega)
            have hv : v = v₀ := Fin.ext (by omega)
            have hp : p = p₀ := by omega
            subst hu; subst hv; subst hp
            exact Or.inl hQt
          · have h1 := hQ_sub u v (p + 1) z hQz hzm
            have hu : u = u₀ := Fin.ext (by omega)
            have hv : v = v₀ := Fin.ext (by omega)
            have hp : p = p₀ - 1 := by omega
            subst hu; subst hv; subst hp
            exact Or.inr hQt
        have hle1 : ({t | Q u₀ v₀ (p₀ + 1) t} : Set _).ncard ≤ 1 :=
          hsub_ncard _ (fun a ha b hb => hQ_unique_pt u₀ v₀ (p₀ + 1) a b ha hb)
        have hle2 : ({t | Q u₀ v₀ (p₀ - 1) t} : Set _).ncard ≤ 1 :=
          hsub_ncard _ (fun a ha b hb => hQ_unique_pt u₀ v₀ (p₀ - 1) a b ha hb)
        have hle := le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (Set.ncard_union_le _ _)
        omega
      · have h0 := hQ_sub u₀ v₀ (p₀ + 1) z hQz₀ hzm
        have hsub : S.neighborSet z ⊆ {t | Q u₀ v₀ (p₀ + 1 + 1) t} ∪ {t | Q u₀ v₀ p₀ t} := by
          intro t ht
          rcases (hS z t).mp ht with ⟨u, v, _, _, p, _, ⟨hQz, hQt⟩ | ⟨hQt, hQz⟩⟩
          · have h1 := hQ_sub u v p z hQz hzm
            have hu : u = u₀ := Fin.ext (by omega)
            have hv : v = v₀ := Fin.ext (by omega)
            have hp : p = p₀ + 1 := by omega
            subst hu; subst hv; subst hp
            exact Or.inl hQt
          · have h1 := hQ_sub u v (p + 1) z hQz hzm
            have hu : u = u₀ := Fin.ext (by omega)
            have hv : v = v₀ := Fin.ext (by omega)
            have hp : p = p₀ := by omega
            subst hu; subst hv; subst hp
            exact Or.inr hQt
        have hle1 : ({t | Q u₀ v₀ (p₀ + 1 + 1) t} : Set _).ncard ≤ 1 :=
          hsub_ncard _ (fun a ha b hb => hQ_unique_pt u₀ v₀ (p₀ + 1 + 1) a b ha hb)
        have hle2 : ({t | Q u₀ v₀ p₀ t} : Set _).ncard ≤ 1 :=
          hsub_ncard _ (fun a ha b hb => hQ_unique_pt u₀ v₀ p₀ a b ha hb)
        have hle := le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (Set.ncard_union_le _ _)
        omega
  have hx_lt : x.val < m := horig x hdegx
  have hy_lt : y.val < m := horig y hdegy
  let f : Fin (m + 2 * k * (m * m)) → ℕ := fun z =>
    if z.val < m then
      if z.val = x.val then 0 else 2 * k + 1
    else
      let d := z.val - m
      let q := d % (2 * k) + 1
      let uv := d / (2 * k)
      let u := uv / m
      let v := uv % m
      if u = x.val ∧ v ≠ x.val then q
      else if v = x.val ∧ u ≠ x.val then 2 * k + 1 - q
      else 2 * k + 1
  have hf_Q : ∀ (u v : Fin m) (q : ℕ) (z : Fin (m + 2 * k * (m * m))),
      u < v → Q u v q z →
      (u.val = x.val → f z = q) ∧
      (v.val = x.val → f z = 2 * k + 1 - q) ∧
      (u.val ≠ x.val → v.val ≠ x.val → f z = 2 * k + 1) := by
    intro u v q z huv hQz
    have huvne : u.val ≠ v.val := ne_of_lt huv
    rcases (hQ u v q z).mp hQz with ⟨hq, hzu⟩ | ⟨hq, hzv⟩ | ⟨hq1, hq2, hzv⟩
    · have hfz : f z = if u.val = x.val then 0 else 2 * k + 1 := by
        simp only [f, hzu, u.isLt, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · intro hu; simp [hfz, hu, hq]
      · intro hv
        have hu : u.val ≠ x.val := by omega
        simp [hfz, hu, hq]
      · intro hu _; simp [hfz, hu]
    · have hfz : f z = if v.val = x.val then 0 else 2 * k + 1 := by
        simp only [f, hzv, v.isLt, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · intro hu
        have hv : v.val ≠ x.val := by omega
        simp [hfz, hv, hq]
      · intro hv; simp [hfz, hv, hq]
      · intro _ hv; simp [hfz, hv]
    · have hzm : m ≤ z.val := by omega
      have hnotlt : ¬ z.val < m := Nat.not_lt_of_ge hzm
      have hsub := hQ_sub u v q z hQz hzm
      have hfz : f z =
          if u.val = x.val ∧ v.val ≠ x.val then q
          else if v.val = x.val ∧ u.val ≠ x.val then 2 * k + 1 - q
          else 2 * k + 1 := by
        simp only [f, hnotlt, ↓reduceIte, ← hsub.2.2.1, ← hsub.2.2.2.1, ← hsub.2.2.2.2]
      refine ⟨?_, ?_, ?_⟩
      · intro hu
        have hv : v.val ≠ x.val := by omega
        simp [hfz, hu, hv]
      · intro hv
        have hu : u.val ≠ x.val := by omega
        simp [hfz, hu, hv]
      · intro hu hv
        simp [hfz, hu, hv]
  have hf_adj : ∀ a b : Fin (m + 2 * k * (m * m)), S.Adj a b → f b ≤ f a + 1 := by
    intro a b hab
    rcases (hS a b).mp hab with ⟨u, v, huv, _, p, hp, ⟨hQa, hQb⟩ | ⟨hQb, hQa⟩⟩
    · have ha := hf_Q u v p a huv hQa
      have hb := hf_Q u v (p + 1) b huv hQb
      by_cases hu : u.val = x.val
      · have := ha.1 hu; have := hb.1 hu; omega
      · by_cases hv : v.val = x.val
        · have := ha.2.1 hv; have := hb.2.1 hv; omega
        · have := ha.2.2 hu hv; have := hb.2.2 hu hv; omega
    · have hb := hf_Q u v p b huv hQb
      have ha := hf_Q u v (p + 1) a huv hQa
      by_cases hu : u.val = x.val
      · have := ha.1 hu; have := hb.1 hu; omega
      · by_cases hv : v.val = x.val
        · have := ha.2.1 hv; have := hb.2.1 hv; omega
        · have := ha.2.2 hu hv; have := hb.2.2 hu hv; omega
  have hf_walk : ∀ {a b : Fin (m + 2 * k * (m * m))} (q : S.Walk a b),
      f b ≤ f a + q.length := by
    intro a b q
    induction q with
    | nil => simp
    | cons hadj _ ih =>
      have hstep := hf_adj _ _ hadj
      simp only [SimpleGraph.Walk.length_cons]
      omega
  have hfx : f x = 0 := by simp [f, hx_lt]
  have hyx : y.val ≠ x.val := fun h => hxy (Fin.ext h.symm)
  have hfy : f y = 2 * k + 1 := by simp [f, hy_lt, hyx]
  have hw := hf_walk w
  omega
