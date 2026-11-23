import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_729_aux

open Classical

inductive Wk {n : ℕ} (D : Fin n → Fin n → Prop) (R : Finset (Fin n)) : Fin n → Fin n → ℕ → Prop
  | nil (a : Fin n) : a ∈ R → Wk D R a a 0
  | cons (a b c : Fin n) (k : ℕ) : a ∈ R → D a b → Wk D R b c k → Wk D R a c (k + 1)

theorem wk_mem {n : ℕ} {D : Fin n → Fin n → Prop} {R : Finset (Fin n)} {a b : Fin n} {k : ℕ}
    (h : Wk D R a b k) : a ∈ R ∧ b ∈ R := by
  induction h with
  | nil a ha => exact ⟨ha, ha⟩
  | cons a b c k ha _ _ ih => exact ⟨ha, ih.2⟩

theorem wk_append {n : ℕ} {D : Fin n → Fin n → Prop} {R : Finset (Fin n)} {a b c : Fin n} {k m : ℕ}
    (h1 : Wk D R a b k) (h2 : Wk D R b c m) : Wk D R a c (k + m) := by
  induction h1 with
  | nil a _ => simpa using h2
  | cons a b' c' k ha hab _ ih =>
    have := Wk.cons a b' c (k + m) ha hab (ih h2)
    rw [show k + 1 + m = k + m + 1 by omega]
    exact this

theorem wk_snoc {n : ℕ} {D : Fin n → Fin n → Prop} {R : Finset (Fin n)} {a b c : Fin n} {k : ℕ}
    (h : Wk D R a b k) (hbc : D b c) (hc : c ∈ R) : Wk D R a c (k + 1) :=
  wk_append h (Wk.cons b c c 0 (wk_mem h).2 hbc (Wk.nil c hc))

theorem wk_first {n : ℕ} {D : Fin n → Fin n → Prop} {R : Finset (Fin n)} {a b : Fin n} {k : ℕ}
    (h : Wk D R a b k) : (k = 0 ∧ a = b) ∨ ∃ t k', k = k' + 1 ∧ D a t ∧ Wk D R t b k' := by
  cases h with
  | nil _ _ => exact Or.inl ⟨rfl, rfl⟩
  | cons _ t _ k' _ hat htb => exact Or.inr ⟨t, k', rfl, hat, htb⟩

theorem wk_fun {n : ℕ} {D : Fin n → Fin n → Prop} {R : Finset (Fin n)} {a b : Fin n} {k : ℕ}
    (h : Wk D R a b k) : ∃ f : ℕ → Fin n, f 0 = a ∧ f k = b ∧ ∀ i, i < k → D (f i) (f (i + 1)) := by
  induction h with
  | nil a _ => exact ⟨fun _ => a, rfl, rfl, by intro i hi; omega⟩
  | cons a b c k _ hab _ ih =>
    obtain ⟨f, h0, hk, hD⟩ := ih
    refine ⟨fun i => if i = 0 then a else f (i - 1), by simp, by simpa using hk, ?_⟩
    intro i hi
    rcases i with _ | i
    · simpa [h0] using hab
    · simpa using hD i (by omega)

theorem kernel {n : ℕ} (D : Fin n → Fin n → Prop)
    (hodd : ∀ (a : Fin n) (R : Finset (Fin n)) (k : ℕ), ¬ Wk D R a a (2 * k + 1)) :
    ∀ R : Finset (Fin n), ∃ K ⊆ R, (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧
      ∀ v ∈ R, v ∉ K → ∃ k ∈ K, D v k := by
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
  rcases R.eq_empty_or_nonempty with hR | hR
  · exact ⟨∅, by simp, by simp, by simp [hR]⟩
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image R
    (fun x => (R.filter (fun v => ∃ k, Wk D R x v k)).card) hR
  have back : ∀ w k, Wk D R r w k → ∃ m, Wk D R w r m := by
    intro w k hw
    have hsub : R.filter (fun v => ∃ k, Wk D R w v k) ⊆ R.filter (fun v => ∃ k, Wk D R r v k) := by
      intro v hv
      simp only [Finset.mem_filter] at hv ⊢
      obtain ⟨hvR, k', hk'⟩ := hv
      exact ⟨hvR, k + k', wk_append hw hk'⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (hmin w (wk_mem hw).2)
    have hrr : r ∈ R.filter (fun v => ∃ k, Wk D R r v k) := by
      simp only [Finset.mem_filter]
      exact ⟨hr, 0, Wk.nil r hr⟩
    rw [← heq] at hrr
    simp only [Finset.mem_filter] at hrr
    exact hrr.2
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), S = R.filter (fun v => ∃ j, Wk D R r v (2 * j)) := ⟨_, rfl⟩
  have hsemi : ∀ s ∈ S, ∀ w ∈ R, D s w → ∃ t ∈ S, D w t := by
    intro s hs w hw hsw
    simp only [hS, Finset.mem_filter] at hs
    obtain ⟨_, j, hj⟩ := hs
    have h1 : Wk D R r w (2 * j + 1) := wk_snoc hj hsw hw
    obtain ⟨m, hm⟩ := back w _ h1
    rcases wk_first hm with ⟨_, hwr⟩ | ⟨t, m', _, hwt, htr⟩
    · subst hwr
      exact absurd h1 (hodd _ R j)
    · refine ⟨t, ?_, hwt⟩
      simp only [hS, Finset.mem_filter]
      have h2 := wk_snoc h1 hwt (wk_mem htr).1
      exact ⟨(wk_mem htr).1, j + 1, by rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]; exact h2⟩
  have hind : ∀ u ∈ S, ∀ v ∈ S, ¬ D u v := by
    intro u hu v hv huv
    simp only [hS, Finset.mem_filter] at hu hv
    obtain ⟨_, j, hj⟩ := hu
    obtain ⟨hvR, i, hi⟩ := hv
    have h1 := wk_snoc hj huv hvR
    obtain ⟨m, hm⟩ := back v _ h1
    have c1 := wk_append h1 hm
    have c2 := wk_append hi hm
    rcases Nat.even_or_odd m with ⟨q, hq⟩ | ⟨q, hq⟩
    · subst hq
      exact hodd r R (j + q) (by rw [show 2 * (j + q) + 1 = 2 * j + 1 + (q + q) by ring]; exact c1)
    · subst hq
      exact hodd r R (i + q) (by rw [show 2 * (i + q) + 1 = 2 * i + (2 * q + 1) by ring]; exact c2)
  have hrS : r ∈ S := by
    simp only [hS, Finset.mem_filter]
    exact ⟨hr, 0, Wk.nil r hr⟩
  obtain ⟨R', hR'⟩ : ∃ R' : Finset (Fin n), R' = R.filter (fun v => v ∉ S ∧ ¬ ∃ t ∈ S, D v t) :=
    ⟨_, rfl⟩
  have hlt : R' ⊂ R := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨by rw [hR']; exact Finset.filter_subset _ _, fun h => ?_⟩
    have : r ∈ R' := by rw [h]; exact hr
    simp only [hR', Finset.mem_filter] at this
    exact this.2.1 hrS
  obtain ⟨K', hK'sub, hK'ind, hK'abs⟩ := ih R' hlt
  have hR'R : R' ⊆ R := by rw [hR']; exact Finset.filter_subset _ _
  refine ⟨S ∪ K', ?_, ?_, ?_⟩
  · exact Finset.union_subset (by rw [hS]; exact Finset.filter_subset _ _) (hK'sub.trans hR'R)
  · intro u hu v hv huv
    rw [Finset.mem_union] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hind u hu v hv huv
    · have hv' := hK'sub hv
      simp only [hR', Finset.mem_filter] at hv'
      exact hv'.2.2 (hsemi u hu v hv'.1 huv)
    · have hu' := hK'sub hu
      simp only [hR', Finset.mem_filter] at hu'
      exact hu'.2.2 ⟨v, hv, huv⟩
    · exact hK'ind u hu v hv huv
  · intro v hv hvK
    rw [Finset.mem_union, not_or] at hvK
    by_cases h : ∃ t ∈ S, D v t
    · obtain ⟨t, ht, hvt⟩ := h
      exact ⟨t, Finset.mem_union_left _ ht, hvt⟩
    · have hvR' : v ∈ R' := by
        simp only [hR', Finset.mem_filter]
        exact ⟨hv, hvK.1, h⟩
      obtain ⟨k, hk, hvk⟩ := hK'abs v hvR' hvK.2
      exact ⟨k, Finset.mem_union_right _ hk, hvk⟩

end PEqualNP.Outside.L_meta_729_aux

theorem PEqualNP.Outside.L_meta_729 : ∀ (n : ℕ) (D : Fin n → Fin n → Prop),
  (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
  (¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) →
  ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  intro n D _ _ hno
  have hodd : ∀ (a : Fin n) (R : Finset (Fin n)) (k : ℕ),
      ¬ PEqualNP.Outside.L_meta_729_aux.Wk D R a a (2 * k + 1) := by
    intro a R k h
    obtain ⟨f, h0, hk, hD⟩ := PEqualNP.Outside.L_meta_729_aux.wk_fun h
    exact hno ⟨k, f, by rw [hk, h0], hD⟩
  obtain ⟨K, -, hind, habs⟩ := PEqualNP.Outside.L_meta_729_aux.kernel D hodd Finset.univ
  exact ⟨↑K, fun u hu v hv => hind u hu v hv, fun v hv => habs v (Finset.mem_univ v) hv⟩
