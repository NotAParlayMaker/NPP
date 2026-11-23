import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta306

open Classical

abbrev V (m k : ℕ) : Type := Fin (m + 2 * k * (m * m))

theorem code_lt {m k : ℕ} (u v : Fin m) {i : ℕ} (hi : i < 2 * k) :
    m + 2 * k * (u.val * m + v.val) + i < m + 2 * k * (m * m) := by
  have hu : u.val + 1 ≤ m := u.isLt
  have hv := v.isLt
  have h1 : u.val * m + v.val + 1 ≤ m * m := by
    calc u.val * m + v.val + 1 ≤ u.val * m + m := by omega
      _ = (u.val + 1) * m := by ring
      _ ≤ m * m := Nat.mul_le_mul_right m hu
  have h2 : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h1
  have h3 : 2 * k * (u.val * m + v.val + 1) = 2 * k * (u.val * m + v.val) + 2 * k := by ring
  omega

def hub {m : ℕ} (k : ℕ) (u : Fin m) : V m k := ⟨u.val, Nat.lt_add_right _ u.isLt⟩

theorem hub_inj {m : ℕ} (k : ℕ) : Function.Injective (hub (m := m) k) := by
  intro a b hab
  have h := congrArg Fin.val hab
  exact Fin.ext h

def thF {m : ℕ} (k : ℕ) (u v : Fin m) (i : ℕ) : V m k :=
  if h : i < 2 * k then ⟨m + 2 * k * (u.val * m + v.val) + i, code_lt u v h⟩ else hub k u

theorem thF_val {m k : ℕ} (u v : Fin m) {i : ℕ} (hi : i < 2 * k) :
    (thF k u v i).val = m + 2 * k * (u.val * m + v.val) + i := by
  unfold thF
  rw [dif_pos hi]

theorem dec_aux {m k : ℕ} (x : V m k) (h : ¬ x.val < m) : (x.val - m) / (2 * k) < m * m :=
  Nat.div_lt_of_lt_mul (by have := x.isLt; omega)

theorem m_pos {m k : ℕ} (x : V m k) (h : ¬ x.val < m) : 0 < m := by
  have hq := dec_aux x h
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · have hz : m * m = 0 := by simp [h0]
    exact absurd (lt_of_lt_of_eq hq hz) (Nat.not_lt_zero _)
  · exact h0

def decF (m k : ℕ) (x : V m k) : Option (Fin m × Fin m) :=
  if h : x.val < m then none
  else some (⟨(x.val - m) / (2 * k) / m, Nat.div_lt_of_lt_mul (dec_aux x h)⟩,
    ⟨(x.val - m) / (2 * k) % m, Nat.mod_lt _ (m_pos x h)⟩)

theorem decF_hub {m k : ℕ} (x : V m k) (hx : x.val < m) : decF m k x = none := by
  unfold decF
  rw [dif_pos hx]

theorem decF_none {m k : ℕ} (x : V m k) (h : decF m k x = none) : x.val < m := by
  by_contra hn
  unfold decF at h
  rw [dif_neg hn] at h
  exact absurd h (by simp)

theorem decF_th {m k : ℕ} (hk : 1 ≤ k) (u v : Fin m) (i : ℕ) (hi : i < 2 * k) (x : V m k)
    (hx : x.val = m + 2 * k * (u.val * m + v.val) + i) : decF m k x = some (u, v) := by
  have hnm : ¬ x.val < m := by omega
  unfold decF
  rw [dif_neg hnm]
  have e1 : (x.val - m) / (2 * k) = u.val * m + v.val := by
    have hs : x.val - m = 2 * k * (u.val * m + v.val) + i := by omega
    rw [hs, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]
  have hmpos : 0 < m := by have := u.isLt; omega
  have e2 : (u.val * m + v.val) / m = u.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hmpos, Nat.div_eq_of_lt v.isLt, Nat.zero_add]
  have e3 : (u.val * m + v.val) % m = v.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]
  refine congrArg some (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · show (x.val - m) / (2 * k) / m = u.val
    rw [e1, e2]
  · show (x.val - m) / (2 * k) % m = v.val
    rw [e1, e3]

noncomputable def E {m : ℕ} (H : SimpleGraph (Fin m)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ H.Adj e.1 e.2)

theorem mem_E {m : ℕ} {H : SimpleGraph (Fin m)} {u v : Fin m} :
    (u, v) ∈ E H ↔ u < v ∧ H.Adj u v := by
  simp [E]

def Fw {m : ℕ} (H : SimpleGraph (Fin m)) (k : ℕ) (X : Finset (Fin m)) (x : V m k) : Prop :=
  (∃ u ∈ X, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧
    x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ X)

theorem card_ge_of_inj {α : Type} {n : ℕ} (A : Finset α) (f : Fin n → α)
    (hinj : Function.Injective f) (hmem : ∀ j, f j ∈ A) : n ≤ A.card := by
  calc n = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ A.card := Finset.card_le_card (by
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hx
        exact hmem j)

theorem fw_card {m k : ℕ} (hk : 1 ≤ k) (H : SimpleGraph (Fin m)) (X : Finset (Fin m))
    (X' : Finset (V m k)) (h : ∀ x, x ∈ X' ↔ Fw H k X x) :
    X'.card = X.card + k * (E H).card := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := decF m k) (s := X') (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)
  rw [hfib, Fintype.sum_option]
  have hnone : (X'.filter (fun x => decF m k x = none)).card = X.card := by
    symm
    refine Finset.card_bij (fun u _ => hub k u) ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_filter]
      exact ⟨(h _).2 (Or.inl ⟨u, hu, rfl⟩), decF_hub _ u.isLt⟩
    · intro a _ b _ hab
      exact hub_inj k hab
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hlt := decF_none x hx.2
      rcases (h x).1 hx.1 with ⟨u, hu, hxu⟩ | ⟨u, v, i, hi, _, _, hxv, _⟩
      · exact ⟨u, hu, Fin.ext hxu.symm⟩
      · omega
  have hsome : ∀ e : Fin m × Fin m,
      (X'.filter (fun x => decF m k x = some e)).card = if e ∈ E H then k else 0 := by
    rintro ⟨u, v⟩
    by_cases he : (u, v) ∈ E H
    · rw [if_pos he]
      obtain ⟨huv, hadj⟩ := mem_E.1 he
      obtain ⟨b, hb1, hb2⟩ : ∃ b : ℕ, b < 2 ∧ ∀ i : ℕ, (i % 2 = 1 ↔ u ∈ X) ↔ i % 2 = b := by
        by_cases hu : u ∈ X
        · exact ⟨1, by omega, fun i => by simp [hu]⟩
        · refine ⟨0, by omega, fun i => ?_⟩
          simp only [hu, iff_false]
          omega
      refine ((Finset.card_bij (s := (Finset.univ : Finset (Fin k)))
        (fun j _ => thF k u v (2 * j.val + b)) ?_ ?_ ?_).symm).trans (Finset.card_fin k)
      · intro j _
        have hj : 2 * j.val + b < 2 * k := by have := j.isLt; omega
        rw [Finset.mem_filter]
        exact ⟨(h _).2 (Or.inr ⟨u, v, 2 * j.val + b, hj, huv, hadj, thF_val u v hj,
          (hb2 _).2 (by omega)⟩), decF_th hk u v _ hj _ (thF_val u v hj)⟩
      · intro a _ c _ hac
        have ha : 2 * a.val + b < 2 * k := by have := a.isLt; omega
        have hc : 2 * c.val + b < 2 * k := by have := c.isLt; omega
        have hv := congrArg Fin.val hac
        rw [thF_val u v ha, thF_val u v hc] at hv
        exact Fin.ext (by omega)
      · intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hx1, hx2⟩ := hx
        rcases (h x).1 hx1 with ⟨u', hu', hxu⟩ | ⟨u', v', i, hi, huv', hadj', hxv, hpar⟩
        · rw [decF_hub x (by rw [hxu]; exact u'.isLt)] at hx2
          exact absurd hx2 (by simp)
        · rw [decF_th hk u' v' i hi x hxv] at hx2
          obtain ⟨rfl, rfl⟩ : u' = u ∧ v' = v := by simpa using hx2
          have hib := (hb2 i).1 hpar
          have hlt : 2 * (i / 2) + b < 2 * k := by omega
          refine ⟨⟨i / 2, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
          rw [thF_val u' v' hlt, hxv]
          omega
    · rw [if_neg he, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx hdx
      rcases (h x).1 hx with ⟨u', hu', hxu⟩ | ⟨u', v', i, hi, huv', hadj', hxv, hpar⟩
      · rw [decF_hub x (by rw [hxu]; exact u'.isLt)] at hdx
        exact absurd hdx (by simp)
      · rw [decF_th hk u' v' i hi x hxv] at hdx
        obtain ⟨rfl, rfl⟩ : u' = u ∧ v' = v := by simpa using hdx
        exact he (mem_E.2 ⟨huv', hadj'⟩)
  rw [hnone, Finset.sum_congr rfl (fun e _ => hsome e), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem fw_cover {m k : ℕ} (hk : 1 ≤ k) (H : SimpleGraph (Fin m))
    (Q : Fin m → Fin m → ℕ → V m k → Prop) (S : SimpleGraph (V m k))
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : V m k), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨
      (p = 2 * k + 1 ∧ x.val = v.val) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hS : ∀ x y : V m k, S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)))
    (X : Finset (Fin m)) (hX : ∀ u v : Fin m, H.Adj u v → u ∈ X ∨ v ∈ X)
    (X' : Finset (V m k)) (h : ∀ x, x ∈ X' ↔ Fw H k X x) :
    ∀ x y : V m k, S.Adj x y → x ∈ X' ∨ y ∈ X' := by
  have core : ∀ (u v : Fin m) (p : ℕ) (x y : V m k), u < v → H.Adj u v → p ≤ 2 * k →
      Q u v p x → Q u v (p + 1) y → x ∈ X' ∨ y ∈ X' := by
    intro u v p x y huv hadj hp hx hy
    rw [hQ] at hx hy
    have hc := hX u v hadj
    by_cases hu : u ∈ X
    · rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ((h x).2 (Or.inl ⟨u, hu, h2⟩))
      · omega
      · by_cases hodd : (p - 1) % 2 = 1
        · exact Or.inl ((h x).2 (Or.inr ⟨u, v, p - 1, by omega, huv, hadj, by omega,
            ⟨fun _ => hu, fun _ => hodd⟩⟩))
        · rcases hy with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
          · omega
          · omega
          · exact Or.inr ((h y).2 (Or.inr ⟨u, v, p, by omega, huv, hadj, by omega,
              ⟨fun _ => hu, fun _ => by omega⟩⟩))
    · have hv : v ∈ X := hc.resolve_left hu
      rcases hy with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
      · omega
      · exact Or.inr ((h y).2 (Or.inl ⟨v, hv, g2⟩))
      · by_cases hev : p % 2 = 0
        · exact Or.inr ((h y).2 (Or.inr ⟨u, v, p, by omega, huv, hadj, by omega,
            ⟨fun hh => absurd hh (by omega), fun hh => absurd hh hu⟩⟩))
        · rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
          · omega
          · omega
          · exact Or.inl ((h x).2 (Or.inr ⟨u, v, p - 1, by omega, huv, hadj, by omega,
              ⟨fun hh => absurd hh (by omega), fun hh => absurd hh hu⟩⟩))
  intro x y hxy
  obtain ⟨u, v, huv, hadj, p, hp, hpq | hpq⟩ := (hS x y).1 hxy
  · exact core u v p x y huv hadj hp hpq.1 hpq.2
  · exact (core u v p y x huv hadj hp hpq.1 hpq.2).symm

theorem bw {m k : ℕ} (hk : 1 ≤ k) (H : SimpleGraph (Fin m))
    (Q : Fin m → Fin m → ℕ → V m k → Prop) (S : SimpleGraph (V m k))
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : V m k), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨
      (p = 2 * k + 1 ∧ x.val = v.val) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hS : ∀ x y : V m k, S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)))
    (U : Finset (V m k)) (hU : ∀ x y : V m k, S.Adj x y → x ∈ U ∨ y ∈ U) :
    ∃ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧
      R.card + k * (E H).card ≤ U.card := by
  have Qth : ∀ (u v : Fin m) (p i : ℕ), p = i + 1 → i < 2 * k → Q u v p (thF k u v i) := by
    intro u v p i hp hi
    exact (hQ u v p _).2 (Or.inr (Or.inr ⟨by omega, by omega, by rw [thF_val u v hi]; omega⟩))
  have Qhub : ∀ u v : Fin m, Q u v 0 (hub k u) := fun u v =>
    (hQ u v 0 _).2 (Or.inl ⟨rfl, rfl⟩)
  have Qlast : ∀ u v : Fin m, Q u v (2 * k + 1) (hub k v) := fun u v =>
    (hQ u v (2 * k + 1) _).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have adj : ∀ (u v : Fin m) (p : ℕ) (x y : V m k), u < v → H.Adj u v → p ≤ 2 * k →
      Q u v p x → Q u v (p + 1) y → x ∈ U ∨ y ∈ U := by
    intro u v p x y huv hadj hp hx hy
    exact hU x y ((hS x y).2 ⟨u, v, huv, hadj, p, hp, Or.inl ⟨hx, hy⟩⟩)
  obtain ⟨R0, hR0⟩ : ∃ R0 : Finset (Fin m), ∀ u, u ∈ R0 ↔ hub k u ∈ U :=
    ⟨Finset.univ.filter (fun u => hub k u ∈ U), fun u => by simp⟩
  obtain ⟨Eb, hEb⟩ : ∃ Eb : Finset (Fin m × Fin m),
      Eb = (E H).filter (fun e => hub k e.1 ∉ U ∧ hub k e.2 ∉ U) := ⟨_, rfl⟩
  refine ⟨R0 ∪ Eb.image Prod.fst, ?_, ?_⟩
  · have key : ∀ u v : Fin m, u < v → H.Adj u v →
        u ∈ R0 ∪ Eb.image Prod.fst ∨ v ∈ R0 ∪ Eb.image Prod.fst := by
      intro u v huv hadj
      by_cases h1 : hub k u ∈ U
      · exact Or.inl (Finset.mem_union_left _ ((hR0 u).2 h1))
      · by_cases h2 : hub k v ∈ U
        · exact Or.inr (Finset.mem_union_left _ ((hR0 v).2 h2))
        · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(u, v), ?_, rfl⟩))
          rw [hEb, Finset.mem_filter]
          exact ⟨mem_E.2 ⟨huv, hadj⟩, h1, h2⟩
    intro a b hab
    rcases lt_or_gt_of_ne (H.ne_of_adj hab) with hlt | hgt
    · exact key a b hlt hab
    · exact (key b a hgt hab.symm).symm
  · have hfib := Finset.card_eq_sum_card_fiberwise (f := decF m k) (s := U) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)
    have hnone : R0.card ≤ (U.filter (fun x => decF m k x = none)).card := by
      calc R0.card = (R0.image (hub k)).card := by
            rw [Finset.card_image_of_injective _ (hub_inj k)]
        _ ≤ _ := Finset.card_le_card (by
            intro x hx
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
            rw [Finset.mem_filter]
            exact ⟨(hR0 u).1 hu, decF_hub _ u.isLt⟩)
    have hedge : ∀ e ∈ E H, k + (if hub k e.1 ∉ U ∧ hub k e.2 ∉ U then 1 else 0) ≤
        (U.filter (fun x => decF m k x = some e)).card := by
      rintro ⟨u, v⟩ he
      obtain ⟨huv, hadj⟩ := mem_E.1 he
      have hmid : ∀ i : ℕ, i + 1 < 2 * k → thF k u v i ∈ U ∨ thF k u v (i + 1) ∈ U :=
        fun i hi => adj u v (i + 1) _ _ huv hadj (by omega) (Qth u v (i + 1) i rfl (by omega))
          (Qth u v (i + 1 + 1) (i + 1) rfl hi)
      have hdec : ∀ i : ℕ, i < 2 * k → decF m k (thF k u v i) = some (u, v) :=
        fun i hi => decF_th hk u v i hi _ (thF_val u v hi)
      have hval : ∀ i j : ℕ, i < 2 * k → j < 2 * k → thF k u v i = thF k u v j → i = j := by
        intro i j hi hj hij
        have hv := congrArg Fin.val hij
        rw [thF_val u v hi, thF_val u v hj] at hv
        omega
      by_cases hbad : hub k u ∉ U ∧ hub k v ∉ U
      · rw [if_pos hbad]
        have hfirst : thF k u v 0 ∈ U :=
          (adj u v 0 _ _ huv hadj (by omega) (Qhub u v) (Qth u v (0 + 1) 0 rfl (by omega))).resolve_left
            hbad.1
        have hlast : thF k u v (2 * k - 1) ∈ U :=
          (adj u v (2 * k) _ _ huv hadj le_rfl (Qth u v (2 * k) (2 * k - 1) (by omega) (by omega))
            (Qlast u v)).resolve_right hbad.2
        have hex : ∀ j : Fin (k + 1), ∃ x : V m k, x ∈ U ∧ ∃ i : ℕ, i < 2 * k ∧
            x = thF k u v i ∧ (j.val = 0 → i = 0) ∧
            (0 < j.val → i = 2 * j.val - 1 ∨ i = 2 * j.val) := by
          intro j
          have hj := j.isLt
          by_cases h0 : j.val = 0
          · exact ⟨_, hfirst, 0, by omega, rfl, fun _ => rfl, fun hh => by omega⟩
          · by_cases h1 : thF k u v (2 * j.val - 1) ∈ U
            · exact ⟨_, h1, 2 * j.val - 1, by omega, rfl, fun hh => absurd hh h0,
                fun _ => Or.inl rfl⟩
            · have hjk : j.val < k := by
                by_contra hc
                have hjeq : j.val = k := by omega
                rw [hjeq] at h1
                exact h1 hlast
              have h2 : thF k u v (2 * j.val) ∈ U := by
                rcases hmid (2 * j.val - 1) (by omega) with hh | hh
                · exact absurd hh h1
                · have e : 2 * j.val - 1 + 1 = 2 * j.val := by omega
                  rwa [e] at hh
              exact ⟨_, h2, 2 * j.val, by omega, rfl, fun hh => absurd hh h0,
                fun _ => Or.inr rfl⟩
        choose g hgU gi hgi hgeq hg0 hg1 using hex
        refine card_ge_of_inj _ g ?_ ?_
        · intro a b hab
          have hi : gi a = gi b := by
            apply hval _ _ (hgi a) (hgi b)
            rw [← hgeq a, ← hgeq b, hab]
          have ha0 := hg0 a
          have ha1 := hg1 a
          have hb0 := hg0 b
          have hb1 := hg1 b
          exact Fin.ext (by omega)
        · intro j
          rw [Finset.mem_filter]
          exact ⟨hgU j, by rw [hgeq j]; exact hdec _ (hgi j)⟩
      · rw [if_neg hbad, Nat.add_zero]
        have hex : ∀ j : Fin k, ∃ x : V m k, x ∈ U ∧ ∃ i : ℕ, i < 2 * k ∧
            x = thF k u v i ∧ (i = 2 * j.val ∨ i = 2 * j.val + 1) := by
          intro j
          have hj := j.isLt
          rcases hmid (2 * j.val) (by omega) with hh | hh
          · exact ⟨_, hh, 2 * j.val, by omega, rfl, Or.inl rfl⟩
          · exact ⟨_, hh, 2 * j.val + 1, by omega, rfl, Or.inr rfl⟩
        choose g hgU gi hgi hgeq hg1 using hex
        refine card_ge_of_inj _ g ?_ ?_
        · intro a b hab
          have hi : gi a = gi b := by
            apply hval _ _ (hgi a) (hgi b)
            rw [← hgeq a, ← hgeq b, hab]
          have ha1 := hg1 a
          have hb1 := hg1 b
          exact Fin.ext (by omega)
        · intro j
          rw [Finset.mem_filter]
          exact ⟨hgU j, by rw [hgeq j]; exact hdec _ (hgi j)⟩
    have hu1 := Finset.card_union_le R0 (Eb.image Prod.fst)
    have hu2 := Finset.card_image_le (s := Eb) (f := Prod.fst)
    have hsum : ∑ e ∈ E H, (k + (if hub k e.1 ∉ U ∧ hub k e.2 ∉ U then 1 else 0)) =
        k * (E H).card + Eb.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hEb, Finset.card_filter,
        Nat.mul_comm]
    have h1 := Finset.sum_le_sum hedge
    have h2 : ∑ e ∈ E H, (U.filter (fun x => decF m k x = some e)).card ≤
        ∑ e : Fin m × Fin m, (U.filter (fun x => decF m k x = some e)).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Fintype.sum_option] at hfib
    omega

end PEqualNP.Outside.Meta306

theorem PEqualNP.Outside.L_meta_306 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → T.card ≤ R.card + 1) → (∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → T'.card ≤ U.card + 1) ∧ ((∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → T'.card ≤ U.card) ↔ (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → T.card ≤ R.card)) := by
  intro m k H Q S hk hQ hS T T' hT hT' hmin
  classical
  have hTc := PEqualNP.Outside.Meta306.fw_card hk H T T' hT'
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨R, hR, hRc⟩ := PEqualNP.Outside.Meta306.bw hk H Q S hQ hS U hU
    have h1 := hmin R hR
    omega
  · intro hall R hR
    obtain ⟨R', hR'⟩ : ∃ R' : Finset (Fin (m + 2 * k * (m * m))),
        ∀ x, x ∈ R' ↔ PEqualNP.Outside.Meta306.Fw H k R x :=
      ⟨Finset.univ.filter (fun x => PEqualNP.Outside.Meta306.Fw H k R x), fun x => by
        rw [Finset.mem_filter]
        exact ⟨fun hh => hh.2, fun hh => ⟨Finset.mem_univ _, hh⟩⟩⟩
    have hcov := PEqualNP.Outside.Meta306.fw_cover hk H Q S hQ hS R hR R' hR'
    have hc := PEqualNP.Outside.Meta306.fw_card hk H R R' hR'
    have h1 := hall R' hcov
    omega
  · intro hall U hU
    obtain ⟨R, hR, hRc⟩ := PEqualNP.Outside.Meta306.bw hk H Q S hQ hS U hU
    have h1 := hall R hR
    omega
