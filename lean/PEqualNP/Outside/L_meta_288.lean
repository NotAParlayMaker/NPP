import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_288_aux

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

lemma bound (m k a b i : ℕ) (ha : a < m) (hb : b < m) (hi : i < 2 * k) :
    m + 2 * k * (a * m + b) + i < m + 2 * k * m * m := by
  have h1 : (a + 1) * m ≤ m * m := Nat.mul_le_mul_right m ha
  have h1' : (a + 1) * m = a * m + m := by ring
  have h2 : 2 * k * (a * m + b + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ (by omega)
  have h3 : 2 * k * (a * m + b + 1) = 2 * k * (a * m + b) + 2 * k := by ring
  have h4 : 2 * k * m * m = 2 * k * (m * m) := by ring
  omega

lemma cover_rel (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m))
    (hT : ∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T)
    (F : Finset (Fin (m + 2 * k * m * m)))
    (hF : ∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T))
    (x y : Fin (m + 2 * k * m * m)) (u v : Fin m) (huv : u < v) (hadj : H.Adj u v)
    (i : Fin (2 * k)) (hx : x.val = m + 2 * k * (u.val * m + v.val) + i.val)
    (hy : (i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val)) :
    x ∈ F ∨ y ∈ F := by
  rw [hF x, hF y]
  by_cases huT : u ∈ T
  · rcases hy with ⟨hi, hy⟩ | ⟨hi, hy⟩ | ⟨hi, hy⟩
    · right
      left
      exact ⟨u, huT, hy⟩
    · rcases Nat.mod_two_eq_zero_or_one i.val with hpar | hpar
      · right
        right
        refine ⟨u, v, ⟨i.val + 1, hi⟩, huv, hadj, ?_, ?_⟩
        · show y.val = m + 2 * k * (u.val * m + v.val) + (i.val + 1)
          rw [hy, Nat.add_assoc]
        · exact iff_of_true (show (i.val + 1) % 2 = 1 by omega) huT
      · left
        right
        exact ⟨u, v, i, huv, hadj, hx, iff_of_true hpar huT⟩
    · left
      right
      exact ⟨u, v, i, huv, hadj, hx, iff_of_true (by omega) huT⟩
  · rcases hy with ⟨hi, hy⟩ | ⟨hi, hy⟩ | ⟨hi, hy⟩
    · left
      right
      exact ⟨u, v, i, huv, hadj, hx, iff_of_false (by omega) huT⟩
    · rcases Nat.mod_two_eq_zero_or_one i.val with hpar | hpar
      · left
        right
        exact ⟨u, v, i, huv, hadj, hx, iff_of_false (by omega) huT⟩
      · right
        right
        refine ⟨u, v, ⟨i.val + 1, hi⟩, huv, hadj, ?_, ?_⟩
        · show y.val = m + 2 * k * (u.val * m + v.val) + (i.val + 1)
          rw [hy, Nat.add_assoc]
        · exact iff_of_false (show ¬ (i.val + 1) % 2 = 1 by omega) huT
    · right
      left
      exact ⟨v, (hT u v hadj).resolve_left huT, hy⟩

lemma edge_card (m : ℕ) (H : SimpleGraph (Fin m)) (E : Finset (Fin m × Fin m))
    (hE : ∀ p : Fin m × Fin m, p ∈ E ↔ p.1 < p.2 ∧ H.Adj p.1 p.2) :
    E.card = H.edgeSet.ncard := by
  have himg : H.edgeSet = (fun p : Fin m × Fin m => s(p.1, p.2)) '' (E : Set (Fin m × Fin m)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet, Set.mem_image, Finset.mem_coe, hE, Prod.exists,
        Sym2.eq_iff]
      constructor
      · intro h
        rcases lt_trichotomy a b with hlt | heq | hgt
        · exact ⟨a, b, ⟨hlt, h⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact absurd heq h.ne
        · exact ⟨b, a, ⟨hgt, h.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
      · rintro ⟨p, q, ⟨-, hpq⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · exact hpq
        · exact hpq.symm
  have hinj : Set.InjOn (fun p : Fin m × Fin m => s(p.1, p.2)) (E : Set (Fin m × Fin m)) := by
    intro p hp q hq hpq
    have hp' := (hE p).mp hp
    have hq' := (hE q).mp hq
    simp only [Sym2.eq_iff] at hpq
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have a1 := hp'.1
      have a2 := hq'.1
      rw [h1, h2] at a1
      exact lt_asymm a1 a2
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset]

def g (k m : ℕ) (T : Finset (Fin m)) (q : (Fin m × Fin m) × Fin k) : ℕ :=
  m + 2 * k * (q.1.1.val * m + q.1.2.val) + (2 * q.2.val + (if q.1.1 ∈ T then 1 else 0))

lemma g_inj (k m : ℕ) (T : Finset (Fin m)) : Function.Injective (g k m T) := by
  rintro ⟨⟨u, v⟩, t⟩ ⟨⟨u', v'⟩, t'⟩ h
  unfold g at h
  simp only at h
  have ht := t.isLt
  have ht' := t'.isLt
  have hd := dec (2 * k) m u.val v.val (2 * t.val + (if u ∈ T then 1 else 0)) u'.val v'.val
    (2 * t'.val + (if u' ∈ T then 1 else 0)) v.isLt v'.isLt (by split_ifs <;> omega)
    (by split_ifs <;> omega) (by omega)
  obtain ⟨hu, hv, hi⟩ := hd
  have hu' : u = u' := Fin.ext hu
  have hv' : v = v' := Fin.ext hv
  subst hu' hv'
  have htt : t = t' := by
    apply Fin.ext
    omega
  subst htt
  rfl

lemma count (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m))
    (F : Finset (Fin (m + 2 * k * m * m)))
    (hF : ∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T))
    (E : Finset (Fin m × Fin m))
    (hE : ∀ p : Fin m × Fin m, p ∈ E ↔ p.1 < p.2 ∧ H.Adj p.1 p.2) :
    F.card = T.card + E.card * k := by
  have hcardF : F.card = (F.image Fin.val).card :=
    (Finset.card_image_of_injective _ Fin.val_injective).symm
  have himg : F.image Fin.val = T.image Fin.val ∪ (E ×ˢ (Finset.univ : Finset (Fin k))).image (g k m T) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases (hF j).mp hj with ⟨u, huT, hju⟩ | ⟨u, v, i, huv, hadj, hjv, hpar⟩
      · left
        exact ⟨u, huT, hju.symm⟩
      · right
        have hil := i.isLt
        refine ⟨((u, v), ⟨i.val / 2, by omega⟩), (hE (u, v)).mpr ⟨huv, hadj⟩, ?_⟩
        unfold g
        simp only
        rw [hjv]
        by_cases huT : u ∈ T
        · have := hpar.mpr huT
          simp only [huT, ite_true]
          omega
        · have : ¬ i.val % 2 = 1 := fun h => huT (hpar.mp h)
          simp only [huT, ite_false]
          omega
    · rintro (⟨u, huT, rfl⟩ | ⟨⟨⟨u, v⟩, t⟩, hmem, rfl⟩)
      · have hul := u.isLt
        refine ⟨⟨u.val, by omega⟩, ?_, rfl⟩
        rw [hF]
        left
        exact ⟨u, huT, rfl⟩
      · have hmem' := (hE (u, v)).mp hmem
        have htl := t.isLt
        have hi : 2 * t.val + (if u ∈ T then 1 else 0) < 2 * k := by
          split_ifs <;> omega
        refine ⟨⟨g k m T ((u, v), t), bound m k u.val v.val _ u.isLt v.isLt hi⟩, ?_, rfl⟩
        rw [hF]
        right
        refine ⟨u, v, ⟨2 * t.val + (if u ∈ T then 1 else 0), hi⟩, hmem'.1, hmem'.2, rfl, ?_⟩
        by_cases huT : u ∈ T
        · simp only [huT, ite_true]
          exact iff_of_true (by omega) trivial
        · simp only [huT, ite_false]
          exact iff_of_false (by omega) (fun h => h)
  have hdisj : Disjoint (T.image Fin.val) ((E ×ˢ (Finset.univ : Finset (Fin k))).image (g k m T)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨u, -, rfl⟩ := h1
    obtain ⟨q, -, hq⟩ := h2
    unfold g at hq
    have := u.isLt
    omega
  rw [hcardF, himg, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (g_inj k m T), Finset.card_product, Finset.card_univ,
    Fintype.card_fin]

end PEqualNP.Outside.L_meta_288_aux

open PEqualNP.Outside.L_meta_288_aux in
theorem PEqualNP.Outside.L_meta_288 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k → (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ F : Finset (Fin (m + 2 * k * m * m)), (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T)) → (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ F ∨ y ∈ F) ∧ F.card = T.card + k * H.edgeSet.ncard := by
  intro k m H T hk hT S hS F hF
  subst hS
  constructor
  · intro x y hadj
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h | h
    · obtain ⟨u, v, huv, ha, i, hx, hy⟩ := h
      exact cover_rel k m H T hT F hF x y u v huv ha i hx hy
    · obtain ⟨u, v, huv, ha, i, hx, hy⟩ := h
      exact (cover_rel k m H T hT F hF y x u v huv ha i hx hy).symm
  · classical
    have hE : ∀ p : Fin m × Fin m,
        p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2) ↔
          p.1 < p.2 ∧ H.Adj p.1 p.2 := by
      intro p
      simp
    rw [count k m H T F hF _ hE, edge_card m H _ hE, Nat.mul_comm]
