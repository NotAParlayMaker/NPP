import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Subdivision290

lemma path_base (k : ℕ) (T : Finset (Fin (2 * k)))
    (h : ∀ (i : ℕ) (hi : i + 1 < 2 * k),
      (⟨i, by omega⟩ : Fin (2 * k)) ∈ T ∨ ⟨i + 1, hi⟩ ∈ T) : k ≤ T.card := by
  classical
  have hex : ∀ i : Fin k, ∃ j : T, j.val.val = 2 * i.val ∨ j.val.val = 2 * i.val + 1 := by
    intro i
    have hi : 2 * i.val + 1 < 2 * k := by omega
    rcases h (2 * i.val) hi with h0 | h1
    · exact ⟨⟨⟨2 * i.val, by omega⟩, h0⟩, Or.inl rfl⟩
    · exact ⟨⟨⟨2 * i.val + 1, hi⟩, h1⟩, Or.inr rfl⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have heq : (f i).val.val = (f j).val.val := congrArg (fun z : T => z.val.val) hij
    rcases hf i with hi | hi <;> rcases hf j with hj | hj <;> omega
  simpa using Fintype.card_le_of_injective f hinj

lemma path_extra (k : ℕ) (hk : 1 ≤ k) (T : Finset (Fin (2 * k)))
    (h : ∀ (i : ℕ) (hi : i + 1 < 2 * k),
      (⟨i, by omega⟩ : Fin (2 * k)) ∈ T ∨ ⟨i + 1, hi⟩ ∈ T)
    (h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ T)
    (hlast : (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) ∈ T) : k + 1 ≤ T.card := by
  classical
  have hex : ∀ i : Fin (k + 1), ∃ j : T, (j.val.val + 1) / 2 = i.val := by
    intro i
    by_cases hi0 : i.val = 0
    · exact ⟨⟨⟨0, by omega⟩, h0⟩, by simp [hi0]⟩
    by_cases hik : i.val = k
    · refine ⟨⟨⟨2 * k - 1, by omega⟩, hlast⟩, ?_⟩
      dsimp
      omega
    have hi : 2 * i.val - 1 + 1 < 2 * k := by omega
    rcases h (2 * i.val - 1) hi with h1 | h2
    · refine ⟨⟨⟨2 * i.val - 1, by omega⟩, h1⟩, ?_⟩
      dsimp
      omega
    · refine ⟨⟨⟨2 * i.val - 1 + 1, hi⟩, h2⟩, ?_⟩
      dsimp
      omega
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have heq : (f i).val.val = (f j).val.val := congrArg (fun z : T => z.val.val) hij
    rw [← hf i, ← hf j, heq]
  simpa using Fintype.card_le_of_injective f hinj

def old (k m : ℕ) (v : Fin m) : Fin (m + 2 * k * m * m) :=
  ⟨v.val, by have := v.isLt; omega⟩

def internal (k m : ℕ) (u v : Fin m) (i : Fin (2 * k)) :
    Fin (m + 2 * k * m * m) :=
  ⟨m + 2 * k * (u.val * m + v.val) + i.val, by
    have huv : u.val * m + v.val < m * m := by
      have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt u.isLt)
      have := v.isLt
      nlinarith
    have hb := Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt huv)
    calc
      m + 2 * k * (u.val * m + v.val) + i.val <
          m + (2 * k * (u.val * m + v.val) + 2 * k) := by have := i.isLt; omega
      _ = m + 2 * k * (u.val * m + v.val + 1) := by ring
      _ ≤ m + 2 * k * (m * m) := Nat.add_le_add_left hb m
      _ = m + 2 * k * m * m := by ring⟩

lemma block_quotient (b i j : ℕ) (hb : 0 < b) (hj : j < b) :
    (b * i + j) / b = i := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]

lemma internal_injective (k m : ℕ) (hk : 1 ≤ k) (u v u' v' : Fin m)
    (i i' : Fin (2 * k))
    (h : internal k m u v i = internal k m u' v' i') :
    u = u' ∧ v = v' ∧ i = i' := by
  have hv := congrArg Fin.val h
  change m + 2 * k * (u.val * m + v.val) + i.val =
    m + 2 * k * (u'.val * m + v'.val) + i'.val at hv
  have heq : 2 * k * (u.val * m + v.val) + i.val =
      2 * k * (u'.val * m + v'.val) + i'.val := by omega
  have hcode := congrArg (fun z : ℕ => z / (2 * k)) heq
  rw [block_quotient _ _ _ (by omega) i.isLt,
    block_quotient _ _ _ (by omega) i'.isLt] at hcode
  have hm : 0 < m := by have := u.isLt; omega
  have hu : u.val = u'.val := by
    calc
      u.val = (m * u.val + v.val) / m := (block_quotient _ _ _ hm v.isLt).symm
      _ = (m * u'.val + v'.val) / m := by congr 1; nlinarith only [hcode]
      _ = u'.val := block_quotient _ _ _ hm v'.isLt
  have hv' : v.val = v'.val := by rw [hu] at hcode; omega
  have hi : i.val = i'.val := by rw [hcode] at heq; omega
  exact ⟨Fin.ext hu, Fin.ext hv', Fin.ext hi⟩

lemma ordered_edges_card (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    (Finset.univ.filter (fun e : Fin m × Fin m => e.1 < e.2 ∧ H.Adj e.1 e.2)).card =
      H.edgeSet.ncard := by
  classical
  let E := Finset.univ.filter (fun e : Fin m × Fin m => e.1 < e.2 ∧ H.Adj e.1 e.2)
  have hc : E.card = H.edgeFinset.card := by
    apply Finset.card_bij (fun e _ => s(e.1, e.2))
    · intro e he
      have he' : e.1 < e.2 ∧ H.Adj e.1 e.2 := by simpa [E] using he
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he'.2
    · intro e he e' he' h
      have hlt : e.1 < e.2 := (show e.1 < e.2 ∧ H.Adj e.1 e.2 by simpa [E] using he).1
      have hlt' : e'.1 < e'.2 :=
        (show e'.1 < e'.2 ∧ H.Adj e'.1 e'.2 by simpa [E] using he').1
      rcases Sym2.eq_iff.mp h with h | h
      · exact Prod.ext h.1 h.2
      · rw [h.1, h.2] at hlt
        exact (lt_asymm hlt hlt').elim
    · intro e he
      induction e using Sym2.ind with
      | h u v =>
        have huv : H.Adj u v := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
        rcases lt_or_gt_of_ne huv.ne with hlt | hgt
        · exact ⟨(u, v), by simp [E, hlt, huv], rfl⟩
        · exact ⟨(v, u), by simp [E, hgt, huv.symm], Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩
  simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hc

lemma packing (k m : ℕ) (hk : 1 ≤ k) (R : Finset (Fin m))
    (E : Finset (Fin m × Fin m)) (T : Fin m × Fin m → Finset (Fin (2 * k)))
    (U : Finset (Fin (m + 2 * k * m * m)))
    (hR : ∀ v ∈ R, old k m v ∈ U)
    (hT : ∀ e ∈ E, ∀ i ∈ T e, internal k m e.1 e.2 i ∈ U) :
    R.card + ∑ e ∈ E, (T e).card ≤ U.card := by
  classical
  let O := R.image (old k m)
  let I := fun e : Fin m × Fin m => (T e).image (internal k m e.1 e.2)
  have hold : Function.Injective (old k m) := by
    intro u v h
    exact Fin.ext (congrArg (fun z : Fin (m + 2 * k * m * m) => z.val) h)
  have hO : O ⊆ U := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hR v hv
  have hI : E.biUnion I ⊆ U := by
    intro x hx
    obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hT e he i hi
  have hdis : (E : Set (Fin m × Fin m)).PairwiseDisjoint I := by
    intro e he e' he' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    obtain ⟨i', hi', hix'⟩ := Finset.mem_image.mp hx'
    have hp := internal_injective k m hk e.1 e.2 e'.1 e'.2 i i' (hix.trans hix'.symm)
    exact hne (Prod.ext hp.1 hp.2.1)
  have hdisO : Disjoint O (E.biUnion I) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, he, hx'⟩ := Finset.mem_biUnion.mp hx'
    obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hx'
    have hv := congrArg Fin.val hiv
    change m + 2 * k * (e.1.val * m + e.2.val) + i.val = v.val at hv
    have := v.isLt
    omega
  have hIcard : ∀ e : Fin m × Fin m, (I e).card = (T e).card := by
    intro e
    apply Finset.card_image_of_injective
    intro i j hij
    exact (internal_injective k m hk e.1 e.2 e.1 e.2 i j hij).2.2
  have hc := Finset.card_le_card (Finset.union_subset hO hI)
  rw [Finset.card_union_of_disjoint hdisO, Finset.card_biUnion hdis] at hc
  change (R.image (old k m)).card + _ ≤ _ at hc
  rw [Finset.card_image_of_injective R hold] at hc
  simpa only [hIcard] using hc

end PEqualNP.Outside.Subdivision290

open PEqualNP.Outside.Subdivision290

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_290 : ∀ (k m c : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → (∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → c ≤ T.card) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro k m c H hk hmin S hS U hU
  let E := Finset.univ.filter (fun e : Fin m × Fin m => e.1 < e.2 ∧ H.Adj e.1 e.2)
  let R := Finset.univ.filter (fun v : Fin m => old k m v ∈ U)
  let B := E.filter (fun e => e.1 ∉ R ∧ e.2 ∉ R)
  let T := fun e : Fin m × Fin m =>
    Finset.univ.filter (fun i : Fin (2 * k) => internal k m e.1 e.2 i ∈ U)
  have hpath : ∀ e ∈ E, ∀ (i : ℕ) (hi : i + 1 < 2 * k),
      (⟨i, by omega⟩ : Fin (2 * k)) ∈ T e ∨ ⟨i + 1, hi⟩ ∈ T e := by
    intro e he i hi
    have he' : e.1 < e.2 ∧ H.Adj e.1 e.2 := by simpa [E] using he
    have hadj : S.Adj (internal k m e.1 e.2 ⟨i, by omega⟩)
        (internal k m e.1 e.2 ⟨i + 1, hi⟩) := by
      rw [hS, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ?_⟩
      · intro h
        have hv := congrArg Fin.val h
        change m + 2 * k * (e.1.val * m + e.2.val) + i =
          m + 2 * k * (e.1.val * m + e.2.val) + (i + 1) at hv
        omega
      · refine ⟨e.1, e.2, he'.1, he'.2, ⟨i, by omega⟩, rfl,
          Or.inr (Or.inl ⟨hi, ?_⟩)⟩
        change m + 2 * k * (e.1.val * m + e.2.val) + (i + 1) =
          m + 2 * k * (e.1.val * m + e.2.val) + i + 1
        omega
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hU _ _ hadj
  have hlow : ∀ e ∈ E, k + (if e ∈ B then 1 else 0) ≤ (T e).card := by
    intro e he
    by_cases hb : e ∈ B
    · have he' : e.1 < e.2 ∧ H.Adj e.1 e.2 := by simpa [E] using he
      have hb' : e.1 ∉ R ∧ e.2 ∉ R := (Finset.mem_filter.mp hb).2
      have hnot0 : old k m e.1 ∉ U := by simpa [R] using hb'.1
      have hnot1 : old k m e.2 ∉ U := by simpa [R] using hb'.2
      have hfirst : S.Adj (internal k m e.1 e.2 ⟨0, by omega⟩) (old k m e.1) := by
        rw [hS, SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ?_⟩
        · intro h
          have hv := congrArg Fin.val h
          change m + 2 * k * (e.1.val * m + e.2.val) + 0 = e.1.val at hv
          have := e.1.isLt
          omega
        · exact ⟨e.1, e.2, he'.1, he'.2, ⟨0, by omega⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
      have hlast : S.Adj (internal k m e.1 e.2 ⟨2 * k - 1, by omega⟩)
          (old k m e.2) := by
        rw [hS, SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ?_⟩
        · intro h
          have hv := congrArg Fin.val h
          change m + 2 * k * (e.1.val * m + e.2.val) + (2 * k - 1) = e.2.val at hv
          have := e.2.isLt
          omega
        · exact ⟨e.1, e.2, he'.1, he'.2, ⟨2 * k - 1, by omega⟩, rfl,
            Or.inr (Or.inr ⟨by change (2 * k - 1) + 1 = 2 * k; omega, rfl⟩)⟩
      have hfmem : (⟨0, by omega⟩ : Fin (2 * k)) ∈ T e := by
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using
          (hU _ _ hfirst).resolve_right hnot0
      have hlmem : (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) ∈ T e := by
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using
          (hU _ _ hlast).resolve_right hnot1
      simpa only [if_pos hb] using path_extra k hk (T e) (hpath e he) hfmem hlmem
    · simpa only [if_neg hb, Nat.add_zero] using path_base k (T e) (hpath e he)
  let C0 := R ∪ B.image Prod.fst
  have hcover : ∀ u v : Fin m, H.Adj u v → u ∈ C0 ∨ v ∈ C0 := by
    intro u v huv
    by_cases hu : u ∈ R
    · exact Or.inl (Finset.mem_union_left _ hu)
    by_cases hv : v ∈ R
    · exact Or.inr (Finset.mem_union_left _ hv)
    rcases lt_or_gt_of_ne huv.ne with hlt | hgt
    · have he : (u, v) ∈ E := by simp [E, hlt, huv]
      have hb : (u, v) ∈ B := Finset.mem_filter.mpr ⟨he, hu, hv⟩
      exact Or.inl (Finset.mem_union_right R (Finset.mem_image.mpr ⟨(u, v), hb, rfl⟩))
    · have he : (v, u) ∈ E := by simp [E, hgt, huv.symm]
      have hb : (v, u) ∈ B := Finset.mem_filter.mpr ⟨he, hv, hu⟩
      exact Or.inr (Finset.mem_union_right R (Finset.mem_image.mpr ⟨(v, u), hb, rfl⟩))
  have hc : c ≤ R.card + B.card := by
    calc
      c ≤ C0.card := hmin C0 hcover
      _ ≤ R.card + (B.image Prod.fst).card := Finset.card_union_le _ _
      _ ≤ R.card + B.card := Nat.add_le_add_left Finset.card_image_le _
  have hEB : E.filter (fun e => e ∈ B) = B := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro h
      exact ⟨(Finset.mem_filter.mp h).1, h⟩
  have hBsum : (∑ e ∈ E, if e ∈ B then 1 else 0) = B.card := by
    rw [← Finset.sum_filter, hEB]
    simp
  have hsum : k * E.card + B.card ≤ ∑ e ∈ E, (T e).card := by
    have hs := Finset.sum_le_sum hlow
    rw [Finset.sum_add_distrib, Finset.sum_const, hBsum] at hs
    simpa [Nat.mul_comm] using hs
  have hpack := packing k m hk R E T U
    (by intro v hv; simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using hv)
    (by intro e he i hi; simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
  have hEcard : E.card = H.edgeSet.ncard := ordered_edges_card m H
  rw [← hEcard]
  omega
