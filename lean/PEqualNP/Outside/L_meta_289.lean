import Mathlib
import PEqualNP.Defs

open scoped Sym2 BigOperators

namespace Subdiv289

def orig (k : ℕ) {m : ℕ} (u : Fin m) : Fin (m + 2*k*m*m) :=
  ⟨u.val, by omega⟩

private lemma block_lt {a b n : ℕ} (ha : a < n) (hb : b < n) : a*n+b < n*n := by
  have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt ha)
  rw [Nat.succ_mul] at h
  omega

def inner (k : ℕ) {m : ℕ} (e : Fin m × Fin m) (i : Fin (2*k)) : Fin (m+2*k*m*m) :=
  ⟨m + 2*k*(e.1.val*m+e.2.val)+i.val, by
    have h := Nat.mul_le_mul_left (2*k)
      (Nat.succ_le_of_lt (block_lt e.1.isLt e.2.isLt))
    rw [Nat.mul_succ, ← Nat.mul_assoc (2*k) m m] at h
    have := i.isLt
    omega⟩

private lemma encode_inj {b q r i j : ℕ} (hi : i < b) (hj : j < b)
    (he : b*q+i = b*r+j) : q = r ∧ i = j := by
  have h := congrArg (fun x => x/b) he
  simp only [Nat.mul_add_div (by omega : 0 < b), Nat.div_eq_of_lt hi,
    Nat.div_eq_of_lt hj, Nat.add_zero] at h
  exact ⟨h, by simpa [h] using he⟩

lemma inner_inj {k m : ℕ} {e f : Fin m × Fin m} {i j : Fin (2*k)}
    (h : inner k e i = inner k f j) : e = f ∧ i = j := by
  have hv := congrArg Fin.val h
  change m + 2*k*(e.1.val*m+e.2.val)+i.val = m + 2*k*(f.1.val*m+f.2.val)+j.val at hv
  obtain ⟨he, hij⟩ := encode_inj i.isLt j.isLt (by omega :
    (2*k)*(e.1.val*m+e.2.val)+i.val = (2*k)*(f.1.val*m+f.2.val)+j.val)
  rw [Nat.mul_comm e.1.val m, Nat.mul_comm f.1.val m] at he
  obtain ⟨hx, hy⟩ := encode_inj e.2.isLt f.2.isLt he
  exact ⟨Prod.ext (Fin.ext hx) (Fin.ext hy), Fin.ext hij⟩

def fiber (k : ℕ) {m : ℕ} (U : Finset (Fin (m+2*k*m*m))) (e : Fin m × Fin m) :=
  (Finset.univ.image (inner k e)).filter (· ∈ U)

private lemma match_bound {k m t d : ℕ} {U : Finset (Fin (m+2*k*m*m))}
    {e : Fin m × Fin m}
    (h : ∀ a : Fin t, ∃ i : Fin (2*k), inner k e i ∈ U ∧
      2*a.val ≤ i.val+d ∧ i.val+d ≤ 2*a.val+1) :
    t ≤ (fiber k U e).card := by
  classical
  choose f hmem hlo hhi using h
  have hinj : Function.Injective (fun a => inner k e (f a)) := by
    intro a b hab
    have he := congrArg Fin.val (inner_inj hab).2
    have := hlo a
    have := hlo b
    have := hhi a
    have := hhi b
    apply Fin.ext
    omega
  let sel := Finset.univ.image (fun a => inner k e (f a))
  have hs : sel ⊆ fiber k U e := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨f a, Finset.mem_univ _, rfl⟩, hmem a⟩
  have hc := Finset.card_le_card hs
  simpa [sel, Finset.card_image_of_injective _ hinj] using hc

def SubRel (k m : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m+2*k*m*m)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2*k),
    x.val = m+2*k*(u.val*m+v.val)+i.val ∧
      ((i.val = 0 ∧ y.val = u.val) ∨
       (i.val+1 < 2*k ∧ y.val = m+2*k*(u.val*m+v.val)+i.val+1) ∨
       (i.val+1 = 2*k ∧ y.val = v.val))

lemma local_bound (k m : ℕ) (H : SimpleGraph (Fin m)) (hk : 1 ≤ k)
    (S : SimpleGraph (Fin (m+2*k*m*m))) (hS : S = SimpleGraph.fromRel (SubRel k m H))
    (U : Finset (Fin (m+2*k*m*m))) (hU : ∀ x y, S.Adj x y → x ∈ U ∨ y ∈ U)
    (e : Fin m × Fin m) (hlt : e.1 < e.2) (hadj : H.Adj e.1 e.2) :
    k + (if orig k e.1 ∉ U ∧ orig k e.2 ∉ U then 1 else 0) ≤ (fiber k U e).card := by
  have edge (i j : Fin (2*k)) (he : j.val = i.val+1) :
      inner k e i ∈ U ∨ inner k e j ∈ U := by
    apply hU
    rw [hS, SimpleGraph.fromRel_adj]
    refine ⟨fun eq => ?_, Or.inl ⟨e.1, e.2, hlt, hadj, i, rfl, Or.inr (Or.inl ⟨by omega, ?_⟩)⟩⟩
    · have := congrArg Fin.val (inner_inj eq).2
      omega
    · change m+2*k*(e.1.val*m+e.2.val)+j.val = _
      omega
  by_cases miss : orig k e.1 ∉ U ∧ orig k e.2 ∉ U
  · rw [ite_eq_left miss]
    apply match_bound (d := 1)
    intro a
    by_cases h0 : a.val = 0
    · let i : Fin (2*k) := ⟨0, by omega⟩
      have h : S.Adj (inner k e i) (orig k e.1) := by
        rw [hS, SimpleGraph.fromRel_adj]
        refine ⟨fun eq => ?_, Or.inl ⟨e.1, e.2, hlt, hadj, i, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
        have hv := congrArg Fin.val eq
        change m + _ + _ = e.1.val at hv
        have := e.1.isLt
        omega
      exact ⟨i, (hU _ _ h).resolve_right miss.1, by simp [i,h0], by simp [i,h0]⟩
    by_cases hk' : a.val = k
    · let i : Fin (2*k) := ⟨2*k-1, by omega⟩
      have h : S.Adj (inner k e i) (orig k e.2) := by
        rw [hS, SimpleGraph.fromRel_adj]
        refine ⟨fun eq => ?_, Or.inl ⟨e.1, e.2, hlt, hadj, i, rfl, Or.inr (Or.inr ⟨?_, rfl⟩)⟩⟩
        · have hv := congrArg Fin.val eq
          change m + _ + _ = e.2.val at hv
          have := e.2.isLt
          omega
        · dsimp [i]
          omega
      exact ⟨i, (hU _ _ h).resolve_right miss.2, by dsimp [i]; omega, by dsimp [i]; omega⟩
    · let i : Fin (2*k) := ⟨2*a.val-1, by have := a.isLt; omega⟩
      let j : Fin (2*k) := ⟨2*a.val, by have := a.isLt; omega⟩
      rcases edge i j (by dsimp [i,j]; omega) with hi | hj
      · exact ⟨i, hi, by dsimp [i]; omega, by dsimp [i]; omega⟩
      · exact ⟨j, hj, by dsimp [j]; omega, by dsimp [j]; omega⟩
  · rw [ite_eq_right miss, Nat.add_zero]
    apply match_bound (d := 0)
    intro a
    let i : Fin (2*k) := ⟨2*a.val, by have := a.isLt; omega⟩
    let j : Fin (2*k) := ⟨2*a.val+1, by have := a.isLt; omega⟩
    rcases edge i j rfl with hi | hj
    · exact ⟨i, hi, by simp [i], by dsimp [i]; omega⟩
    · exact ⟨j, hj, by dsimp [j]; omega, by simp [j]⟩

private noncomputable def edges {m : ℕ} (H : SimpleGraph (Fin m)) : Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter fun e => e.1 < e.2 ∧ H.Adj e.1 e.2

private theorem mem_edges {m : ℕ} (H : SimpleGraph (Fin m)) (p : Fin m × Fin m) :
    p ∈ edges H ↔ p.1 < p.2 ∧ H.Adj p.1 p.2 := by
  simp [edges]

private theorem card_edges {m : ℕ} (H : SimpleGraph (Fin m)) :
    (edges H).card = H.edgeSet.ncard := by
  classical
  have hinj : Set.InjOn (fun p : Fin m × Fin m => s(p.1, p.2)) (edges H : Set _) := by
    intro p hp q hq heq
    rcases Sym2.mk_eq_mk_iff.mp heq with h | h
    · exact h
    · have hp' := (mem_edges H p).mp hp
      have hq' := (mem_edges H q).mp hq
      subst p
      exact (lt_asymm hq'.1 hp'.1).elim
  have himage : (edges H).image (fun p => s(p.1, p.2)) = H.edgeFinset := by
    ext a
    obtain ⟨⟨u,v⟩, rfl⟩ := Sym2.mk_surjective a
    constructor
    · intro h
      obtain ⟨p,hp,hpeq⟩ := Finset.mem_image.mp h
      have ha := ((mem_edges H p).mp hp).2
      have he : s(p.1,p.2) ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.mpr ha
      exact hpeq ▸ he
    · intro h
      have ha : H.Adj u v := SimpleGraph.mem_edgeFinset.mp h
      rcases lt_or_gt_of_ne (SimpleGraph.Adj.ne ha) with hlt | hgt
      · exact Finset.mem_image.mpr ⟨(u,v), (mem_edges H _).mpr ⟨hlt,ha⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(v,u), (mem_edges H _).mpr ⟨hgt,ha.symm⟩, Sym2.eq_swap⟩
  rw [← Finset.card_image_of_injOn hinj, himage, SimpleGraph.edgeFinset_card, Set.ncard_eq_toFinset_card',
    Set.toFinset_card]

private theorem assemble {m k : ℕ} (H : SimpleGraph (Fin m)) {V : Type} [DecidableEq V]
    (U : Finset V) (original : Fin m ↪ V) (fibers : Fin m × Fin m → Finset V)
    (R : Finset (Fin m))
    (hr : ∀ u : Fin m, u ∈ R ↔ original u ∈ U ∨ ∃ v : Fin m,
      u < v ∧ H.Adj u v ∧ original u ∉ U ∧ original v ∉ U)
    (hsub : ∀ e ∈ edges H, fibers e ⊆ U)
    (hdis : (edges H : Set _).PairwiseDisjoint fibers)
    (horig : ∀ (e : Fin m × Fin m) (u : Fin m), original u ∉ fibers e)
    (hloc : ∀ e ∈ edges H,
      k + (if original e.1 ∉ U ∧ original e.2 ∉ U then 1 else 0) ≤ (fibers e).card) :
    (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧ R.card + k * H.edgeSet.ncard ≤ U.card := by
  classical
  constructor
  · intro u v ha
    by_cases hu : original u ∈ U
    · exact Or.inl ((hr u).mpr (.inl hu))
    by_cases hv : original v ∈ U
    · exact Or.inr ((hr v).mpr (.inl hv))
    rcases lt_or_gt_of_ne (SimpleGraph.Adj.ne ha) with hlt | hgt
    · exact Or.inl ((hr u).mpr (.inr ⟨v,hlt,ha,hu,hv⟩))
    · exact Or.inr ((hr v).mpr (.inr ⟨u,hgt,ha.symm,hv,hu⟩))
  · let A : Finset (Fin m) := Finset.univ.filter fun u => original u ∈ U
    let E := edges H
    let bad := E.filter fun e => original e.1 ∉ U ∧ original e.2 ∉ U
    let B := E.biUnion fibers
    have hR : R ⊆ A ∪ bad.image Prod.fst := by
      intro u hu
      rcases (hr u).mp hu with ho | ⟨v, hlt, ha, hnu, hnv⟩
      · exact Finset.mem_union_left _ (by simp [A, ho])
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨(u,v), Finset.mem_filter.mpr ⟨(mem_edges H _).mpr ⟨hlt,ha⟩,hnu,hnv⟩, rfl⟩
    have hRc : R.card ≤ A.card + bad.card :=
      (Finset.card_le_card hR).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left Finset.card_image_le _))
    have hB : B ⊆ U := by
      intro x hx
      obtain ⟨e,he,hx⟩ := Finset.mem_biUnion.mp hx
      exact hsub e he hx
    have hA : A.map original ⊆ U := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_filter.mp hu).2
    have hAB : Disjoint (A.map original) B := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨e,he,hy⟩ := Finset.mem_biUnion.mp hy
      exact horig e u hy
    have hUB : A.card + B.card ≤ U.card := by
      rw [← Finset.card_map original, ← Finset.card_union_of_disjoint hAB]
      exact Finset.card_le_card (Finset.union_subset hA hB)
    have hsum : k * E.card + bad.card ≤ B.card := by
      have hsum := Finset.sum_le_sum hloc
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_boole] at hsum
      change k * (edges H).card + bad.card ≤ ((edges H).biUnion fibers).card
      rw [Finset.card_biUnion hdis]
      simpa [E, bad, Nat.mul_comm] using hsum
    have hE : E.card = H.edgeSet.ncard := card_edges H
    rw [← hE]
    omega

end Subdiv289

open Subdiv289 in
theorem PEqualNP.Outside.L_meta_289 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → ∀ R : Finset (Fin m), (∀ u : Fin m, u ∈ R ↔ (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧ (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val)) → (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧ R.card + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro k m H hk S hS U hU R hR
  let original : Fin m ↪ Fin (m + 2 * k * m * m) :=
    ⟨orig k, fun u v h => Fin.ext (congrArg (fun x : Fin (m + 2 * k * m * m) => x.val) h)⟩
  apply assemble H U original (fiber k U) R
  · have chosen (u : Fin m) : (∃ x ∈ U, x.val = u.val) ↔ original u ∈ U := by
      constructor
      · rintro ⟨x, hx, he⟩
        have eq : x = original u := Fin.ext he
        exact eq ▸ hx
      · intro hu
        exact ⟨original u, hu, rfl⟩
    have missing (u : Fin m) : (∀ x ∈ U, x.val ≠ u.val) ↔ original u ∉ U := by
      constructor
      · intro h hu
        exact h (original u) hu rfl
      · intro hu x hx he
        exact hu ((chosen u).mp ⟨x, hx, he⟩)
    intro u
    simp only [hR, chosen, missing]
  · intro e he x hx
    exact (Finset.mem_filter.mp hx).2
  · intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi, ei⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).1
    obtain ⟨j, hj, ej⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
    exact hef (inner_inj (ei.trans ej.symm)).1
  · intro e u hu
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
    have hv := congrArg Fin.val he
    change m + 2 * k * (e.1.val * m + e.2.val) + i.val = u.val at hv
    have hlt := u.isLt
    omega
  · intro e he
    exact local_bound k m H hk S hS U hU e ((mem_edges H e).mp he).1 ((mem_edges H e).mp he).2
