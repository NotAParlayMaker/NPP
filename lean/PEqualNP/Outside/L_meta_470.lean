import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private abbrev OrderedEdge {m : ℕ} (H : SimpleGraph (Fin m)) :=
  {p : Fin m × Fin m // p.1 < p.2 ∧ H.Adj p.1 p.2}

private lemma edge_card {m : ℕ} (H : SimpleGraph (Fin m)) [Fintype (OrderedEdge H)] :
    H.edgeSet.ncard ≤ Fintype.card (OrderedEdge H) := by
  classical
  let f : OrderedEdge H → H.edgeSet := fun e => ⟨s(e.val.1, e.val.2), e.property.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf u v =>
      change H.Adj u v at he
      rcases lt_or_gt_of_ne he.ne with h | h
      · exact ⟨⟨(u,v), h, he⟩, rfl⟩
      · exact ⟨⟨(v,u), h, he.symm⟩, Subtype.ext (Sym2.eq_swap)⟩
  simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_le_of_surjective f hf

private def internal {m : ℕ} {H : SimpleGraph (Fin m)} (k : ℕ) (e : OrderedEdge H)
    (i : ℕ) := m + 2*k*(e.val.1.val*m + e.val.2.val) + i

private lemma digits {b a c i j : ℕ} (hi : i < b) (hj : j < b)
    (h : b*a+i = b*c+j) : a = c ∧ i = j := by
  have hdiv := congrArg (· / b) h
  have hb : 0 < b := by omega
  simp [Nat.mul_add_div hb, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj] at hdiv
  subst c
  exact ⟨rfl, by omega⟩

private lemma internal_inj {m k : ℕ} {H : SimpleGraph (Fin m)} {e f : OrderedEdge H}
    {i j : ℕ} (hi : i < 2*k) (hj : j < 2*k) (h : internal k e i = internal k f j) :
    e = f ∧ i = j := by
  unfold internal at h
  rw [Nat.add_assoc, Nat.add_assoc] at h
  obtain ⟨ha, hij⟩ := digits hi hj (Nat.add_left_cancel h)
  rw [Nat.mul_comm e.val.1.val m, Nat.mul_comm f.val.1.val m] at ha
  obtain ⟨hu,hv⟩ := digits e.val.2.isLt f.val.2.isLt ha
  exact ⟨Subtype.ext (Prod.ext (Fin.ext hu) (Fin.ext hv)), hij⟩

private lemma internal_ge {m : ℕ} {H : SimpleGraph (Fin m)} (k : ℕ) (e : OrderedEdge H)
    (i : ℕ) : m ≤ internal k e i := by unfold internal; omega

private lemma charge_count {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 0 < k)
    (U : Finset ℕ) (R : Finset (Fin m))
    (leftEnd : ∀ e : OrderedEdge H, e.val.1.val ∉ U → internal k e 0 ∈ U)
    (rightEnd : ∀ e : OrderedEdge H, e.val.2.val ∉ U → internal k e (2*k-1) ∈ U)
    (middle : ∀ (e : OrderedEdge H) (i : ℕ), i+1 < 2*k →
      internal k e i ∈ U ∨ internal k e (i+1) ∈ U)
    (restore : ∀ r ∈ R, r.val ∉ U →
      ∃ e : OrderedEdge H, e.val.1 = r ∧ e.val.2.val ∉ U) :
    R.card + k * H.edgeSet.ncard ≤ U.card := by
  classical
  let shift (e : OrderedEdge H) : ℕ := if e.val.2.val ∈ U then 0 else 1
  have positions (e : OrderedEdge H) (j : Fin k) :
      ∃ i : ℕ, i < 2*k ∧ 2*j.val+shift e ≤ i ∧ i ≤ 2*j.val+shift e+1 ∧
        internal k e i ∈ U := by
    have hj := j.isLt
    by_cases h : e.val.2.val ∈ U
    · simp only [shift, ite_eq_left h, Nat.add_zero]
      rcases middle e (2*j.val) (by omega) with h' | h'
      · exact ⟨_, by omega, by omega, by omega, h'⟩
      · exact ⟨_, by omega, by omega, by omega, h'⟩
    · simp only [shift, ite_eq_right h]
      by_cases hlast : j.val+1 = k
      · exact ⟨2*k-1, by omega, by omega, by omega, rightEnd e h⟩
      · rcases middle e (2*j.val+1) (by omega) with h' | h'
        · exact ⟨_, by omega, by omega, by omega, h'⟩
        · exact ⟨_, by omega, by omega, by omega, h'⟩
  choose pos hp hlo hhi hmem using positions
  have claims (r : ↥R) : ∃ n ∈ U,
      n = r.val.val ∨ ∃ e : OrderedEdge H, e.val.1 = r.val ∧ shift e = 1 ∧ n = internal k e 0 := by
    by_cases h : r.val.val ∈ U
    · exact ⟨_,h,Or.inl rfl⟩
    · obtain ⟨e,he,hn⟩ := restore r r.property h
      exact ⟨_,leftEnd e (he ▸ h), Or.inr ⟨e,he,by simp [shift,hn],rfl⟩⟩
  choose claim hc hclaim using claims
  let pay : Fin k × OrderedEdge H → ℕ := fun p => internal k p.2 (pos p.2 p.1)
  have pay_inj : Function.Injective pay := by
    rintro ⟨j,e⟩ ⟨l,f⟩ h
    change internal k e (pos e j) = internal k f (pos f l) at h
    obtain ⟨rfl,heq⟩ := internal_inj (hp e j) (hp f l) h
    have := hlo e j
    have := hhi e j
    have := hlo e l
    have := hhi e l
    have hjl : j.val = l.val := by omega
    exact Prod.ext (Fin.ext hjl) rfl
  have claim_inj : Function.Injective claim := by
    intro r s h
    rcases hclaim r with hr | ⟨e,he,_,hr⟩ <;>
      rcases hclaim s with hs | ⟨f,hf,_,hs⟩
    · exact Subtype.ext (Fin.ext (by omega))
    · have := internal_ge k f 0
      have := r.val.isLt
      omega
    · have := internal_ge k e 0
      have := s.val.isLt
      omega
    · have hef := (internal_inj (by omega) (by omega) (hr.symm.trans (h.trans hs))).1
      exact Subtype.ext (he.symm.trans (hef ▸ hf))
  have separate (r : ↥R) (p : Fin k × OrderedEdge H) : claim r ≠ pay p := by
    rintro h
    rcases hclaim r with hr | ⟨e,_,hs,hr⟩
    · have := internal_ge k p.2 (pos p.2 p.1)
      have := r.val.isLt
      change claim r = internal k p.2 (pos p.2 p.1) at h
      omega
    · obtain ⟨he,hi⟩ := internal_inj (by omega) (hp p.2 p.1) (hr.symm.trans h)
      have := hlo p.2 p.1
      rw [he] at hs
      omega
  let put : ↥R ⊕ (Fin k × OrderedEdge H) → ↥U :=
    Sum.elim (fun r => ⟨claim r,hc r⟩) (fun p => ⟨pay p,hmem p.2 p.1⟩)
  have inj : Function.Injective put := by
    rintro (r|p) (s|q) h
    · exact congrArg Sum.inl (claim_inj (congrArg Subtype.val h))
    · exact (separate r q (congrArg Subtype.val h)).elim
    · exact (separate s p (congrArg Subtype.val h.symm)).elim
    · exact congrArg Sum.inr (pay_inj (congrArg Subtype.val h))
  have bound := Fintype.card_le_of_injective put inj
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at bound
  exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left k (edge_card H)) _) bound

theorem L_meta_470 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ c : ℕ, (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → c ≤ R.card) → ∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro m k H Q S hk hQ hS c hc U hU
  let T := U.image Fin.val
  let R := Finset.univ.filter (fun u : Fin m => u.val ∈ T ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧ u.val ∉ T ∧ v.val ∉ T)
  have memT (n : ℕ) : n ∈ T ↔ ∃ x ∈ U, x.val = n := Finset.mem_image
  have miss (n : ℕ) : n ∉ T ↔ ∀ x ∈ U, x.val ≠ n := by simp [memT]
  have hR (r : Fin m) : r ∈ R ↔ (∃ x ∈ U, x.val = r.val) ∨ ∃ v : Fin m, r < v ∧ H.Adj r v ∧ (∀ x ∈ U, x.val ≠ r.val) ∧ (∀ x ∈ U, x.val ≠ v.val) := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, ← memT, ← miss]
  have cover (u v : Fin m) (huv : H.Adj u v) (hlt : u < v) : u ∈ R ∨ v ∈ R := by
    by_cases hu : u.val ∈ T
    · exact Or.inl ((hR u).2 (Or.inl ((memT _).1 hu)))
    by_cases hv : v.val ∈ T
    · exact Or.inr ((hR v).2 (Or.inl ((memT _).1 hv)))
    exact Or.inl ((hR u).2 (Or.inr ⟨v,hlt,huv,(miss _).1 hu,(miss _).1 hv⟩))
  have coverR : ∀ u v, H.Adj u v → u ∈ R ∨ v ∈ R := by
    intro u v huv
    rcases lt_or_gt_of_ne huv.ne with h | h
    · exact cover u v huv h
    · exact (cover v u huv.symm h).symm
  have inside (e : OrderedEdge H) (i : ℕ) (hi : i < 2*k) :
      internal k e i < m+2*k*(m*m) := by
    have h1 := Nat.mul_le_mul_right m (show e.val.1.val+1 ≤ m from e.val.1.isLt)
    rw [Nat.add_mul, one_mul] at h1
    have h2 := e.val.2.isLt
    have h3 := Nat.mul_le_mul_left (2*k)
      (show e.val.1.val*m+e.val.2.val+1 ≤ m*m by omega)
    rw [Nat.mul_add, Nat.mul_one] at h3
    simp only [internal, Nat.mul_assoc]
    simp only [Nat.mul_assoc] at h3
    omega
  let node (e : OrderedEdge H) (i : ℕ) (hi : i < 2*k) :
      Fin (m+2*k*(m*m)) := ⟨_,inside e i hi⟩
  let orig (v : Fin m) : Fin (m+2*k*(m*m)) := ⟨v.val,by have := v.isLt; omega⟩
  have flag (e : OrderedEdge H) (i : ℕ) (hi : i < 2*k) (y : Fin (m+2*k*(m*m)))
      (hne : internal k e i ≠ y.val)
      (hy : (i = 0 ∧ y.val = e.val.1.val) ∨
        (i+1 < 2*k ∧ y.val = internal k e i + 1) ∨
        (i+1 = 2*k ∧ y.val = e.val.2.val)) :
      internal k e i ∈ T ∨ y.val ∈ T := by
    have hadj : S.Adj (node e i hi) y := by
      apply (hS _ _).2
      refine ⟨e.val.1,e.val.2,e.property.1,e.property.2,?_⟩
      have qnode : Q e.val.1 e.val.2 (i+1) (node e i hi) :=
        (hQ _ _ _ _).2 (Or.inr (Or.inr ⟨by omega,by omega,by rfl⟩))
      rcases hy with ⟨rfl,hy⟩ | ⟨hj,hy⟩ | ⟨hj,hy⟩
      · exact ⟨0,by omega,Or.inr ⟨(hQ _ _ _ _).2 (Or.inl ⟨rfl,hy⟩),qnode⟩⟩
      · refine ⟨i+1,by omega,Or.inl ⟨qnode,(hQ _ _ _ _).2 (Or.inr (Or.inr ⟨by omega,by omega,?_⟩))⟩⟩
        unfold internal at hy
        omega
      · exact ⟨i+1,by omega,Or.inl ⟨qnode,(hQ _ _ _ _).2 (Or.inr (Or.inl ⟨by omega,hy⟩))⟩⟩
    rcases hU _ _ hadj with h | h
    · exact Or.inl ((memT _).2 ⟨_,h,rfl⟩)
    · exact Or.inr ((memT _).2 ⟨_,h,rfl⟩)
  have bound := charge_count (H := H) hk T R
    (fun e hn => (flag e 0 (by omega) (orig e.val.1)
      (by have := internal_ge k e 0; have := e.val.1.isLt; change _ ≠ e.val.1.val; omega)
      (Or.inl ⟨rfl,rfl⟩)).resolve_right hn)
    (fun e hn => (flag e (2*k-1) (by omega) (orig e.val.2)
      (by have := internal_ge k e (2*k-1); have := e.val.2.isLt; change _ ≠ e.val.2.val; omega)
      (Or.inr (Or.inr ⟨by omega,rfl⟩))).resolve_right hn)
    (fun e i hi => flag e i (by omega) (node e (i+1) hi)
      (by change internal k e i ≠ internal k e (i+1); unfold internal; omega)
      (Or.inr (Or.inl ⟨hi,by change internal k e (i+1) = _; unfold internal; omega⟩)))
    (by
      intro r hr hn
      rcases (hR r).1 hr with h | ⟨v,hlt,hadj,_,hv⟩
      · exact (hn ((memT _).2 h)).elim
      · exact ⟨⟨(r,v),hlt,hadj⟩,rfl,(miss _).2 hv⟩)
  exact (Nat.add_le_add_right (hc R coverR) _).trans (bound.trans Finset.card_image_le)

end PEqualNP.Outside
