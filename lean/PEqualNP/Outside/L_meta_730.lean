import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_730

lemma fin_two_eq : ∀ a b : Fin 2, a ≠ 0 → b ≠ 0 → a = b := by decide

lemma kernel_of_colorable {n : ℕ} (H : SimpleGraph (Fin n)) (hc : H.Colorable 2)
    (D : Fin n → Fin n → Prop) (hD : ∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) :
    ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  obtain ⟨c⟩ := hc
  let f : Set (Fin n) →o Set (Fin n) :=
    ⟨fun A => {x | c x = 0 ∧ ∀ y, D x y → ∃ a ∈ A, D y a}, by
      intro A B hAB x hx
      refine ⟨hx.1, fun y hy => ?_⟩
      obtain ⟨a, ha, hya⟩ := hx.2 y hy
      exact ⟨a, hAB ha, hya⟩⟩
  obtain ⟨A, hA⟩ : ∃ A : Set (Fin n),
      ∀ x, x ∈ A ↔ (c x = 0 ∧ ∀ y, D x y → ∃ a ∈ A, D y a) :=
    ⟨OrderHom.lfp f, fun x => (Set.ext_iff.mp f.map_lfp x).symm⟩
  have key : ∀ x y, x ∈ A → c y ≠ 0 → (∀ a ∈ A, ¬ D y a) → ¬ H.Adj x y := by
    intro x y hx hy1 hy2 hadj
    rcases (hD x y).mp hadj with h | h
    · obtain ⟨a, ha, hya⟩ := ((hA x).mp hx).2 y h
      exact hy2 a ha hya
    · exact hy2 x hx h
  refine ⟨A ∪ {y | c y ≠ 0 ∧ ∀ a ∈ A, ¬ D y a}, ?_, ?_⟩
  · rintro u (hu | hu) v (hv | hv) hadj
    · exact c.valid hadj ((((hA u).mp hu).1).trans (((hA v).mp hv).1).symm)
    · exact key u v hu hv.1 hv.2 hadj
    · exact key v u hv hu.1 hu.2 hadj.symm
    · exact c.valid hadj (fin_two_eq _ _ hu.1 hv.1)
  · intro v hv
    by_cases hcv : c v = 0
    · have hvA : v ∉ A := fun h => hv (Or.inl h)
      rw [hA v] at hvA
      push Not at hvA
      obtain ⟨y, hvy, hy⟩ := hvA hcv
      refine ⟨y, Or.inr ⟨?_, hy⟩, hvy⟩
      intro hcy
      exact c.valid ((hD v y).mpr (Or.inl hvy)) (hcv.trans hcy.symm)
    · have hvB : ¬ (c v ≠ 0 ∧ ∀ a ∈ A, ¬ D v a) := fun h => hv (Or.inr h)
      push Not at hvB
      obtain ⟨a, ha, hva⟩ := hvB hcv
      exact ⟨a, Or.inl ha, hva⟩

def OddClosed {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  Odd m ∧ ∃ p : ℕ → Fin n, (∀ k, k < m → H.Adj (p k) (p (k + 1))) ∧ p m = p 0

lemma core {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) (hm : Odd m) (P : ℕ → Fin n)
    (hadj : ∀ k, H.Adj (P k) (P (k + 1))) (hper : ∀ k, P (k + m) = P k)
    (hmin : ∀ m', OddClosed H m' → m ≤ m')
    (hK : ∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k) :
    False := by
  have hE : ∀ i d, Odd d → P (i + d) = P i → m ≤ d := by
    intro i d hd h
    refine hmin d ⟨hd, fun k => P (i + k), fun k _ => ?_, ?_⟩
    · simpa [add_assoc] using hadj (i + k)
    · simpa using h
  have hA : ∀ i d, Even d → H.Adj (P i) (P (i + d)) → m ≤ d + 1 := by
    intro i d hd h
    refine hmin (d + 1) ⟨hd.add_one, fun k => if k ≤ d then P (i + k) else P i, fun k hk => ?_, ?_⟩
    · by_cases hkd : k < d
      · have h1 : k ≤ d := by omega
        have h2 : k + 1 ≤ d := by omega
        simp only [h1, h2, ite_true]
        simpa [add_assoc] using hadj (i + k)
      · have h1 : k = d := by omega
        subst h1
        simp only [le_refl, ite_true, Nat.not_succ_le_self, ite_false]
        exact h.symm
    · simp
  have hm3 : 3 ≤ m := by
    obtain ⟨t, ht⟩ := hm
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      have h1 : m = 1 := by omega
      have h2 := hper 0
      rw [h1] at h2
      have h3 := hadj 0
      rw [zero_add] at h2 h3
      rw [h2] at h3
      exact H.irrefl h3
    · omega
  have hper' : ∀ t k, P (k + m * t) = P k := by
    intro t
    induction t with
    | zero => intro k; simp
    | succ t ih =>
      intro k
      have : k + m * (t + 1) = (k + m * t) + m := by ring
      rw [this, hper, ih]
  have hmod : ∀ k, P k = P (k % m) := by
    intro k
    have h := hper' (k / m) (k % m)
    rw [Nat.mod_add_div] at h
    exact h
  have hinj : ∀ a b, a < b → b < m → P a ≠ P b := by
    intro a b hab hb h
    rcases Nat.even_or_odd (b - a) with he | ho
    · have ho : Odd (m - (b - a)) := by
        obtain ⟨t, ht⟩ := hm
        obtain ⟨s, hs⟩ := he
        exact ⟨t - s, by omega⟩
      have h1 := hE b (m - (b - a)) ho (by
        have : b + (m - (b - a)) = a + m := by omega
        rw [this, hper, h])
      omega
    · have h1 := hE a (b - a) ho (by
        have : a + (b - a) = b := by omega
        rw [this, h])
      omega
  have hinj' : ∀ i j, P i = P j → i % m = j % m := by
    intro i j h
    rw [hmod i, hmod j] at h
    have hi : i % m < m := Nat.mod_lt _ (by omega)
    have hj : j % m < m := Nat.mod_lt _ (by omega)
    rcases Nat.lt_trichotomy (i % m) (j % m) with h1 | h1 | h1
    · exact absurd h (hinj _ _ h1 hj)
    · exact h1
    · exact absurd h.symm (hinj _ _ h1 hi)
  have hsucc : ∀ i j, P i = P j → P (i + 1) = P (j + 1) := by
    intro i j h
    have h1 : i ≡ j [MOD m] := hinj' i j h
    have h2 : (i + 1) % m = (j + 1) % m := h1.add_right 1
    rw [hmod (i + 1), hmod (j + 1), h2]
  have hchord : ∀ a b, a < b → b < m → H.Adj (P a) (P b) → b = a + 1 ∨ (a = 0 ∧ b + 1 = m) := by
    intro a b hab hb h
    rcases Nat.even_or_odd (b - a) with he | ho
    · have h1 := hA a (b - a) he (by
        have : a + (b - a) = b := by omega
        rw [this]
        exact h)
      right
      omega
    · have he : Even (m - (b - a)) := by
        obtain ⟨t, ht⟩ := hm
        obtain ⟨s, hs⟩ := ho
        exact ⟨t - s, by omega⟩
      have h1 := hA b (m - (b - a)) he (by
        have : b + (m - (b - a)) = a + m := by omega
        rw [this, hper]
        exact h.symm)
      left
      omega
  have harc : ∀ i j, H.Adj (P i) (P j) →
      ∃ k, (P i = P k ∧ P j = P (k + 1)) ∨ (P j = P k ∧ P i = P (k + 1)) := by
    intro i j h
    rw [hmod i, hmod j] at h ⊢
    have hi : i % m < m := Nat.mod_lt _ (by omega)
    have hj : j % m < m := Nat.mod_lt _ (by omega)
    have hwrap : ∀ b, b + 1 = m → P 0 = P (b + 1) := by
      intro b hb
      rw [hb]
      have := hper 0
      rw [zero_add] at this
      exact this.symm
    rcases Nat.lt_trichotomy (i % m) (j % m) with h1 | h1 | h1
    · rcases hchord _ _ h1 hj h with h2 | ⟨h2, h3⟩
      · exact ⟨i % m, Or.inl ⟨rfl, by rw [h2]⟩⟩
      · exact ⟨j % m, Or.inr ⟨rfl, by rw [h2]; exact hwrap _ h3⟩⟩
    · rw [h1] at h
      exact absurd h H.irrefl
    · rcases hchord _ _ h1 hi h.symm with h2 | ⟨h2, h3⟩
      · exact ⟨j % m, Or.inr ⟨rfl, by rw [h2]⟩⟩
      · exact ⟨i % m, Or.inl ⟨rfl, by rw [h2]; exact hwrap _ h3⟩⟩
  have hno2 : ∀ j, P j ≠ P (j + 2) := by
    intro j h
    have h1 : j + 0 ≡ j + 2 [MOD m] := hinj' j (j + 2) h
    have h2 : 0 ≡ 2 [MOD m] := Nat.ModEq.add_left_cancel' j h1
    have h3 : 0 % m = 2 % m := h2
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at h3
    omega
  let D : Fin n → Fin n → Prop := fun u v =>
    (∃ i, u = P i ∧ v = P (i + 1)) ∨
      (H.Adj u v ∧ (¬ ∃ i, u = P i) ∧ ((∃ i, v = P i) ∨ u < v))
  have hD1 : ∀ u v, H.Adj u v ↔ (D u v ∨ D v u) := by
    intro u v
    constructor
    · intro h
      by_cases hu : ∃ i, u = P i
      · by_cases hv : ∃ i, v = P i
        · obtain ⟨i, rfl⟩ := hu
          obtain ⟨j, rfl⟩ := hv
          obtain ⟨k, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := harc i j h
          · exact Or.inl (Or.inl ⟨k, h1, h2⟩)
          · exact Or.inr (Or.inl ⟨k, h1, h2⟩)
        · exact Or.inr (Or.inr ⟨h.symm, hv, Or.inl hu⟩)
      · by_cases hv : ∃ i, v = P i
        · exact Or.inl (Or.inr ⟨h, hu, Or.inl hv⟩)
        · rcases lt_trichotomy u v with h1 | h1 | h1
          · exact Or.inl (Or.inr ⟨h, hu, Or.inr h1⟩)
          · rw [h1] at h
            exact absurd h H.irrefl
          · exact Or.inr (Or.inr ⟨h.symm, hv, Or.inr h1⟩)
    · rintro ((⟨i, rfl, rfl⟩ | h) | (⟨i, rfl, rfl⟩ | h))
      · exact hadj i
      · exact h.1
      · exact (hadj i).symm
      · exact h.1.symm
  have hD2 : ∀ u v, D u v → ¬ D v u := by
    rintro u v (⟨i, rfl, rfl⟩ | ⟨_, hu, hv⟩) (⟨j, h1, h2⟩ | ⟨_, hv', hu'⟩)
    · have h3 := hsucc _ _ h1
      rw [← h2] at h3
      exact hno2 i h3.symm
    · exact hv' ⟨i + 1, rfl⟩
    · exact hu ⟨j + 1, h2⟩
    · rcases hv with hv | hv
      · exact hv' hv
      · rcases hu' with hu' | hu'
        · exact hu hu'
        · exact lt_asymm hv hu'
  obtain ⟨K, hK1, hK2⟩ := hK D hD1 hD2
  have hstep : ∀ i, P (i + 1) ∈ K ↔ P i ∉ K := by
    intro i
    constructor
    · intro h1 h2
      exact hK1 _ h2 _ h1 (hadj i)
    · intro h
      obtain ⟨k, hk, ⟨j, h1, rfl⟩ | ⟨_, h1, _⟩⟩ := hK2 _ h
      · rw [hsucc i j h1]
        exact hk
      · exact absurd ⟨i, rfl⟩ h1
  have hodd : ∀ t, P (2 * t + 1) ∈ K ↔ P 0 ∉ K := by
    intro t
    induction t with
    | zero => exact hstep 0
    | succ t ih =>
      have e : 2 * (t + 1) + 1 = (2 * t + 1 + 1) + 1 := by ring
      rw [e, hstep, hstep, not_not]
      exact ih
  obtain ⟨t, ht⟩ := hm
  have h1 := hodd t
  rw [← ht] at h1
  have h2 := hper 0
  rw [zero_add] at h2
  rw [h2] at h1
  by_cases h : P 0 ∈ K
  · exact (h1.mp h) h
  · exact h (h1.mpr h)

lemma colorable_of_kernels {n : ℕ} (H : SimpleGraph (Fin n))
    (hK : ∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k) :
    H.Colorable 2 := by
  classical
  by_contra hnc
  have h2 := mt SimpleGraph.isBipartite_iff_forall_walk_even_length.mpr hnc
  push Not at h2
  obtain ⟨v, w, hw⟩ := h2
  have hex : ∃ m, OddClosed H m :=
    ⟨w.length, hw, w.getVert,
      fun k hk => w.adj_getVert_succ hk, by simp⟩
  obtain ⟨hm, p, hp, hpm⟩ := Nat.find_spec hex
  have hmin : ∀ m', OddClosed H m' → Nat.find hex ≤ m' := fun m' h => Nat.find_min' hex h
  generalize Nat.find hex = m at hm hp hpm hmin
  have hpos : 0 < m := hm.pos
  refine core H m hm (fun k => p (k % m)) (fun k => ?_) (fun k => ?_) hmin hK
  · have hk : k % m < m := Nat.mod_lt _ hpos
    have e : (k + 1) % m = (k % m + 1) % m := (Nat.mod_add_mod k m 1).symm
    have h0 := hp (k % m) hk
    show H.Adj (p (k % m)) (p ((k + 1) % m))
    rw [e]
    by_cases h : k % m + 1 < m
    · rw [Nat.mod_eq_of_lt h]
      exact h0
    · have h1 : k % m + 1 = m := by omega
      rw [h1, Nat.mod_self, ← hpm]
      rw [h1] at h0
      exact h0
  · simp

end PEqualNP.Outside.L_meta_730

theorem PEqualNP.Outside.L_meta_730 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
  (∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k) ↔
  H.Colorable 2 := by
  intro n H
  constructor
  · exact PEqualNP.Outside.L_meta_730.colorable_of_kernels H
  · intro hc D hD _
    exact PEqualNP.Outside.L_meta_730.kernel_of_colorable H hc D hD
