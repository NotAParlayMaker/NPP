import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_729_aux

def WalkN {α : Type*} (D : α → α → Prop) (l : ℕ) (u v : α) : Prop :=
  ∃ c : ℕ → α, c 0 = u ∧ c l = v ∧ ∀ j, j < l → D (c j) (c (j+1))

def Reach {α : Type*} (D : α → α → Prop) (u v : α) : Prop :=
  ∃ l, WalkN D l u v

variable {α : Type*}

lemma walkN_zero (D : α → α → Prop) (u : α) : WalkN D 0 u u :=
  ⟨fun _ => u, rfl, rfl, fun j hj => (Nat.not_lt_zero j hj).elim⟩

lemma walkN_one {D : α → α → Prop} {u v : α} (h : D u v) : WalkN D 1 u v := by
  refine ⟨fun j => if j = 0 then u else v, by simp, by simp, ?_⟩
  intro j hj
  have : j = 0 := by omega
  simpa [this] using h

lemma walkN_add {D : α → α → Prop} {u v w : α} {l m : ℕ}
    (huv : WalkN D l u v) (hvw : WalkN D m v w) : WalkN D (l + m) u w := by
  obtain ⟨c, hc0, hcl, hc⟩ := huv
  obtain ⟨d, hd0, hdm, hd⟩ := hvw
  let f (j : ℕ) := if j < l then c j else d (j-l)
  refine ⟨f, ?_, ?_, ?_⟩
  · by_cases h : 0 < l
    · simpa [f, h] using hc0
    · have hl : l = 0 := by omega
      subst l
      simpa [f, hd0] using (hcl.symm.trans hc0)
  · simp [f, hdm]
  intro j hj
  by_cases h : j+1 < l
  · have hjl : j < l := by omega
    simpa [f,h,hjl] using hc j hjl
  by_cases hjl : j < l
  · have he : j+1 = l := by omega
    simpa [f,h,hjl,he,hd0,hcl] using hc j hjl
  · have hsub : j-l < m := by omega
    have hs : j+1-l = (j-l)+1 := by omega
    simpa [f,h,hjl,hs] using hd _ hsub

lemma reach_refl (D : α → α → Prop) (u : α) : Reach D u u := ⟨0, walkN_zero D u⟩

lemma reach_of_edge {D : α → α → Prop} {u v : α} (h : D u v) : Reach D u v :=
  ⟨1, walkN_one h⟩

lemma reach_trans {D : α → α → Prop} {u v w : α} (huv : Reach D u v)
    (hvw : Reach D v w) : Reach D u w := by
  obtain ⟨l,hl⟩ := huv
  obtain ⟨m,hm⟩ := hvw
  exact ⟨l+m, walkN_add hl hm⟩

lemma closed_even {D : α → α → Prop}
    (hodd : ∀ (v : α) (k : ℕ), ¬ WalkN D (2*k+1) v v)
    {u : α} {l : ℕ} (h : WalkN D l u u) : l % 2 = 0 := by
  by_contra hn
  have hl : 2*(l/2)+1 = l := by omega
  apply hodd u (l/2)
  rwa [hl]

-- Take vertices with an even-length return walk to the root.
lemma sink_parity {D : α → α → Prop} (r : α)
    (hodd : ∀ (v : α) (k : ℕ), ¬ WalkN D (2*k+1) v v)
    (hback : ∀ v, Reach D r v → Reach D v r) :
    ∃ S : Set α, r ∈ S ∧ (∀ v ∈ S, Reach D r v) ∧
      (∀ u ∈ S, ∀ v ∈ S, ¬ D u v) ∧
      ∀ v, Reach D r v → v ∉ S → ∃ w ∈ S, D v w := by
  let S : Set α := {v | Reach D r v ∧ ∃ k, WalkN D (2*k) v r}
  refine ⟨S, ⟨reach_refl D r, 0, walkN_zero D r⟩, fun _ h => h.1, ?_, ?_⟩
  · rintro u ⟨⟨l, hl⟩, k, hk⟩ v ⟨_, m, hm⟩ huv
    have h₁ := closed_even hodd (walkN_add hl hk)
    have h₂ := closed_even hodd (walkN_add (walkN_add hl (walkN_one huv)) hm)
    omega
  · intro v hrv hnot
    obtain ⟨l, hl⟩ := hback v hrv
    have hn : l % 2 ≠ 0 := by
      intro h
      apply hnot
      refine ⟨hrv, l/2, ?_⟩
      have he : 2*(l/2) = l := by omega
      rwa [he]
    obtain ⟨c, h0, he, hc⟩ := hl
    have hlen : 2*(l/2)+1 = l := by omega
    have hv : D v (c 1) := by simpa [h0] using hc 0 (by omega)
    refine ⟨c 1, ⟨reach_trans hrv (reach_of_edge hv), l/2, ?_⟩, hv⟩
    refine ⟨fun j => c (j+1), rfl, ?_, ?_⟩
    · simpa [hlen] using he
    · intro j hj
      exact hc (j+1) (by omega)

-- A smallest forward reachability set is a sink component.
lemma sink_in_set {α : Type*} [Fintype α] (R : α → α → Prop)
    (U : Finset α) (hne : U.Nonempty) (hrefl : ∀ v ∈ U, R v v)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hclosed : ∀ a ∈ U, ∀ b, R a b → b ∈ U) :
    ∃ r ∈ U, ∀ v, R r v → R v r := by
  classical
  let cone (a : α) := U.filter (R a)
  obtain ⟨r, hr, hmin⟩ := U.exists_min_image (fun a => (cone a).card) hne
  refine ⟨r, hr, ?_⟩
  intro v hrv
  have hsub : cone v ⊆ cone r := by
    intro w hw
    obtain ⟨hwU, hvw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwU, htrans r v w hrv hvw⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (hmin v (hclosed r hr v hrv))
  have hrSelf : r ∈ cone r := Finset.mem_filter.mpr ⟨hr, hrefl r hr⟩
  have hrInV : r ∈ cone v := heq.symm ▸ hrSelf
  exact (Finset.mem_filter.mp hrInV).2

-- Keep an independent piece and recurse after removing it and its predecessors.
lemma build_kernel {α : Type*} [Fintype α] (D : α → α → Prop)
    (hpiece : ∀ U : Finset α, U.Nonempty → ∃ S : Set α,
      (∃ r ∈ U, r ∈ S) ∧ (∀ v ∈ S, v ∈ U) ∧
      (∀ u ∈ S, ∀ v ∈ S, ¬ D u v) ∧
      (∀ u ∈ S, ∀ v ∈ U, D u v → v ∈ S ∨ ∃ k ∈ S, D v k)) :
    ∃ K : Set α, (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  classical
  have induced (U : Finset α) : ∃ K : Set α, (∀ k ∈ K, k ∈ U) ∧
      (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v ∈ U, v ∉ K → ∃ k ∈ K, D v k := by
    induction U using Finset.strongInductionOn with
    | _ U ih =>
      by_cases hU : U.Nonempty
      · obtain ⟨S, ⟨r, hrU, hrS⟩, hSU, hSS, hout⟩ := hpiece U hU
        let R := U.filter (fun v => v ∉ S ∧ ¬ ∃ k ∈ S, D v k)
        have hrR : r ∉ R := fun hr => (Finset.mem_filter.mp hr).2.1 hrS
        have hRU : R ⊆ U := Finset.filter_subset _ _
        obtain ⟨T, hTR, hTT, hTA⟩ :=
          ih R ((Finset.ssubset_iff_of_subset hRU).mpr ⟨r, hrU, hrR⟩)
        refine ⟨S ∪ T, ?_, ?_, ?_⟩
        · rintro k (hk | hk)
          · exact hSU _ hk
          · exact hRU (hTR _ hk)
        · rintro u (hu | hu) v (hv | hv)
          · exact hSS _ hu _ hv
          · intro hd
            obtain ⟨hvU, hvs, hn⟩ := Finset.mem_filter.mp (hTR _ hv)
            exact (hout _ hu _ hvU hd).elim hvs hn
          · intro hd
            exact (Finset.mem_filter.mp (hTR _ hu)).2.2 ⟨v, hv, hd⟩
          · exact hTT _ hu _ hv
        · intro v hvU hv
          by_cases hs : ∃ k ∈ S, D v k
          · obtain ⟨k, hk, hd⟩ := hs
            exact ⟨k, Or.inl hk, hd⟩
          · have hvR : v ∈ R :=
              Finset.mem_filter.mpr ⟨hvU, fun hvS => hv (Or.inl hvS), hs⟩
            obtain ⟨k, hk, hd⟩ := hTA v hvR (fun hvT => hv (Or.inr hvT))
            exact ⟨k, Or.inr hk, hd⟩
      · refine ⟨∅, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro v hv
          exact (hU ⟨v, hv⟩).elim
  obtain ⟨K, _, hi, ha⟩ := induced Finset.univ
  exact ⟨K, hi, fun v => ha v (Finset.mem_univ _)⟩

end PEqualNP.Outside.L_meta_729_aux

open PEqualNP.Outside.L_meta_729_aux in
theorem PEqualNP.Outside.L_meta_729 :
  ∀ (n : ℕ) (D : Fin n → Fin n → Prop),
  (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
  (¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) →
  ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  intro n D _ _ hodd
  classical
  apply build_kernel D
  intro U hU
  let E : Fin n → Fin n → Prop := fun a b => a ∈ U ∧ b ∈ U ∧ D a b
  have hclosed (a : Fin n) (ha : a ∈ U) (b : Fin n) (hab : Reach E a b) : b ∈ U := by
    obtain ⟨l, c, hc0, hcl, steps⟩ := hab
    cases l with
    | zero => simpa [← hcl, hc0] using ha
    | succ m => exact hcl ▸ (steps m (by omega)).2.1
  obtain ⟨r, hr, hback⟩ := sink_in_set (Reach E) U hU (fun a _ => reach_refl E a)
    (fun _ _ _ hab hbc => reach_trans hab hbc) hclosed
  have hoddE (a : Fin n) (k : ℕ) : ¬ WalkN E (2 * k + 1) a a := by
    rintro ⟨c, hc0, hcl, steps⟩
    exact hodd ⟨k, c, hcl.trans hc0.symm, fun j hj => (steps j hj).2.2⟩
  obtain ⟨S, hrs, hSr, hind, habs⟩ := sink_parity r hoddE hback
  have hSU : ∀ v ∈ S, v ∈ U := fun v hv => hclosed r hr v (hSr v hv)
  refine ⟨S, ⟨r, hr, hrs⟩, hSU, ?_, ?_⟩
  · intro u hu v hv huv
    exact hind u hu v hv ⟨hSU u hu, hSU v hv, huv⟩
  · intro u hu v hv huv
    by_cases h : v ∈ S
    · exact Or.inl h
    · have huv' : E u v := ⟨hSU u hu, hv, huv⟩
      obtain ⟨k, hk, hvk⟩ := habs v (reach_trans (hSr u hu) (reach_of_edge huv')) h
      exact Or.inr ⟨k, hk, hvk.2.2⟩
