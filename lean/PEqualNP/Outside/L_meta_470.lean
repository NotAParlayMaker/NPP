import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

namespace PEqualNP.Outside

private lemma path_cover_lb :
    ∀ (k : ℕ) (c : ℕ → Bool),
      (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) →
      k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤
        ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k
  induction k with
  | zero =>
    intro c hc
    have h0 := hc 0 (le_refl 0)
    have hnot : ¬ (c 0 = false ∧ c 1 = false) := by
      rintro ⟨h1, h2⟩
      rcases h0 with h | h <;> simp [h1, h2] at h
    simp [hnot]
  | succ k ih =>
    intro c hc
    have hc_prev : ∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true :=
      fun j hj => hc j (by omega)
    have hih := ih c hc_prev
    have hsplit : Finset.Icc 1 (2 * (k + 1)) =
        Finset.Icc 1 (2 * k) ∪ {2 * k + 1, 2 * k + 2} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hdisj : Disjoint (Finset.Icc 1 (2 * k)) {2 * k + 1, 2 * k + 2} := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      omega
    have hcard_eq :
        ((Finset.Icc 1 (2 * (k + 1))).filter (fun j => c j = true)).card =
          ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card +
          (({2 * k + 1, 2 * k + 2} : Finset ℕ).filter (fun j => c j = true)).card := by
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint]
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj
    have hpair_ge1 :
        1 ≤ (({2 * k + 1, 2 * k + 2} : Finset ℕ).filter (fun j => c j = true)).card := by
      rcases hc (2 * k + 1) (by omega) with h1 | h2
      · exact Finset.card_pos.mpr ⟨2 * k + 1, by simp [h1]⟩
      · exact Finset.card_pos.mpr ⟨2 * k + 2, by simp [h2]⟩
    rw [hcard_eq]
    by_cases hcond : c 0 = false ∧ c (2 * (k + 1) + 1) = false
    · rw [if_pos hcond]
      have hc_end : c (2 * k + 2) = true := by
        rcases hc (2 * k + 2) (by omega) with h | h
        · exact h
        · exfalso
          have h2 := hcond.2
          have : 2 * k + 2 + 1 = 2 * (k + 1) + 1 := by omega
          rw [this] at h
          simp [h2] at h
      cases hmid : c (2 * k + 1)
      · have hih' : k + 1 ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
          have : c 0 = false ∧ c (2 * k + 1) = false := ⟨hcond.1, hmid⟩
          simpa [this] using hih
        omega
      · have hpair_eq2 :
            (({2 * k + 1, 2 * k + 2} : Finset ℕ).filter (fun j => c j = true)).card = 2 := by
          have hfilt :
              ({2 * k + 1, 2 * k + 2} : Finset ℕ).filter (fun j => c j = true) =
                {2 * k + 1, 2 * k + 2} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
              and_iff_left_iff_imp]
            rintro (rfl | rfl)
            · exact hmid
            · exact hc_end
          rw [hfilt, Finset.card_pair (by omega)]
        omega
    · rw [if_neg hcond]
      omega

private lemma subdiv470_bound {m : ℕ} (k : ℕ) (u v : Fin m) (p : ℕ)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) :
    m + 2 * k * (u.val * m + v.val) + p - 1 < m + 2 * k * (m * m) := by
  have huv_lt : u.val * m + v.val + 1 ≤ m * m := by
    have h1 : u.val + 1 ≤ m := u.isLt
    have h2 : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m h1
    have h3 : (u.val + 1) * m = u.val * m + m := by ring
    omega
  have hmul : 2 * k * (u.val * m + v.val) + 2 * k ≤ 2 * k * (m * m) := by
    have := Nat.mul_le_mul_left (2 * k) huv_lt
    linarith
  omega

private def subdivVert470 {m : ℕ} (k : ℕ) (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    Fin (m + 2 * k * (m * m)) :=
  if h0 : p = 0 then ⟨u.val, by omega⟩
  else if htop : p = 2 * k + 1 then ⟨v.val, by omega⟩
  else ⟨m + 2 * k * (u.val * m + v.val) + p - 1, subdiv470_bound k u v p (by omega) (by omega)⟩

private lemma subdiv470_div_mod {m k : ℕ} (u : ℕ) {v p : ℕ} (hk : 1 ≤ k) (hv : v < m)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) :
    ((m + 2 * k * (u * m + v) + p - 1 - m) / (2 * k) / m = u) ∧
    ((m + 2 * k * (u * m + v) + p - 1 - m) / (2 * k) % m = v) ∧
    ((m + 2 * k * (u * m + v) + p - 1 - m) % (2 * k) = p - 1) := by
  have h1 : m + 2 * k * (u * m + v) + p - 1 - m = 2 * k * (u * m + v) + (p - 1) := by omega
  rw [h1]
  have h2k : 0 < 2 * k := by omega
  have hpm : p - 1 < 2 * k := by omega
  have hdiv : (2 * k * (u * m + v) + (p - 1)) / (2 * k) = u * m + v := by
    rw [Nat.mul_add_div h2k, Nat.div_eq_of_lt hpm, Nat.add_zero]
  have hmod : (2 * k * (u * m + v) + (p - 1)) % (2 * k) = p - 1 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hpm]
  have hm : 0 < m := by omega
  rw [hdiv, hmod]
  refine ⟨?_, ?_, rfl⟩
  · rw [Nat.mul_comm u m, Nat.mul_add_div hm, Nat.div_eq_of_lt hv, Nat.add_zero]
  · rw [Nat.mul_comm u m, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]

private lemma subdivVert470_Q {m k : ℕ}
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    Q u v p (subdivVert470 k u v p hp) := by
  rw [hQ]
  unfold subdivVert470
  by_cases h0 : p = 0
  · rw [dif_pos h0]
    exact Or.inl ⟨h0, rfl⟩
  · rw [dif_neg h0]
    by_cases htop : p = 2 * k + 1
    · rw [dif_pos htop]
      exact Or.inr (Or.inl ⟨htop, rfl⟩)
    · rw [dif_neg htop]
      exact Or.inr (Or.inr ⟨by omega, by omega, by dsimp; omega⟩)

theorem L_meta_470 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
      (S : SimpleGraph (Fin (m + 2 * k * (m * m)))),
      1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
          (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      (∀ x y : Fin (m + 2 * k * (m * m)),
        S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
          ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) →
      ∀ c : ℕ,
        (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → c ≤ R.card) →
        ∀ U : Finset (Fin (m + 2 * k * (m * m))),
          (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) →
          c + k * H.edgeSet.ncard ≤ U.card := by
  intro m k H Q S hk hQ hS c hc U hU
  classical
  let DirEdges : Finset (Fin m × Fin m) :=
    Finset.univ.filter fun e => e.1 < e.2 ∧ H.Adj e.1 e.2
  have hcardH : H.edgeSet.ncard = DirEdges.card := by
    let toH : {e : Fin m × Fin m // e ∈ DirEdges} → H.edgeSet :=
      fun e => ⟨s(e.1.1, e.1.2), (Finset.mem_filter.mp e.2).2.2⟩
    have hbij : Function.Bijective toH := by
      constructor
      · rintro ⟨⟨u1, v1⟩, h1⟩ ⟨⟨u2, v2⟩, h2⟩ heq
        have hlt1 : u1 < v1 := (Finset.mem_filter.mp h1).2.1
        have hlt2 : u2 < v2 := (Finset.mem_filter.mp h2).2.1
        have hsym : s(u1, v1) = s(u2, v2) := congrArg Subtype.val heq
        rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact False.elim (lt_asymm hlt1 hlt2)
      · rintro ⟨e, he⟩
        refine Sym2.ind (fun a b => ?_) e he
        intro hab
        have hne : a ≠ b := H.ne_of_adj hab
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ⟨⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hab⟩⟩, rfl⟩
        · refine ⟨⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, H.symm.symm _ _ hab⟩⟩, ?_⟩
          apply Subtype.ext
          exact Sym2.eq_swap
    rw [← Nat.card_coe_set_eq]
    have h1 := (Nat.card_congr (Equiv.ofBijective toH hbij)).symm
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe]
  let origEmb : Fin m → Fin (m + 2 * k * (m * m)) := fun u => ⟨u.val, by omega⟩
  let R0 : Finset (Fin m) := Finset.univ.filter fun u : Fin m => origEmb u ∈ U
  let BadEdges : Finset (Fin m × Fin m) := DirEdges.filter fun e => e.1 ∉ R0 ∧ e.2 ∉ R0
  let R : Finset (Fin m) := R0 ∪ BadEdges.image Prod.fst
  have hR_cover : ∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R := by
    intro u v huv
    by_cases hu : u ∈ R0
    · exact Or.inl (Finset.mem_union_left _ hu)
    · by_cases hv : v ∈ R0
      · exact Or.inr (Finset.mem_union_left _ hv)
      · have hne : u ≠ v := H.ne_of_adj huv
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · left
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨(u, v),
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, huv⟩, hu, hv⟩, rfl⟩
        · right
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨(v, u),
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, H.symm.symm _ _ huv⟩,
              hv, hu⟩, rfl⟩
  have hc_le : c ≤ R0.card + BadEdges.card := by
    calc c ≤ R.card := hc R hR_cover
      _ ≤ R0.card + (BadEdges.image Prod.fst).card := Finset.card_union_le _ _
      _ ≤ R0.card + BadEdges.card := Nat.add_le_add_left Finset.card_image_le _
  let Uorig : Finset (Fin (m + 2 * k * (m * m))) := R0.image origEmb
  have hUorig_card : Uorig.card = R0.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    have hval := congrArg Fin.val hab
    exact Fin.ext hval
  have hUorig_sub : Uorig ⊆ U := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    exact (Finset.mem_filter.mp hu).2
  let innerVert : Fin m × Fin m → Fin (2 * k) → Fin (m + 2 * k * (m * m)) :=
    fun e i => ⟨m + 2 * k * (e.1.val * m + e.2.val) + (i.val + 1) - 1,
      subdiv470_bound k e.1 e.2 (i.val + 1) (by omega) (by omega)⟩
  let Inner : Fin m × Fin m → Finset (Fin (m + 2 * k * (m * m))) :=
    fun e => Finset.univ.image (innerVert e)
  have hInner_ge_m : ∀ (e : Fin m × Fin m) (x : Fin (m + 2 * k * (m * m))),
      x ∈ Inner e → m ≤ x.val := by
    intro e x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    dsimp [innerVert]
    omega
  have hInner_disj : ∀ e1 e2 : Fin m × Fin m, e1 ≠ e2 → Disjoint (Inner e1) (Inner e2) := by
    intro e1 e2 hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨i1, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨i2, _, heq⟩
    have hval := congrArg Fin.val heq
    dsimp [innerVert] at hval
    have hval' :
        m + 2 * k * (e2.1.val * m + e2.2.val) + (i2.val + 1) - 1 =
          m + 2 * k * (e1.1.val * m + e1.2.val) + (i1.val + 1) - 1 := by omega
    have hdm1 := subdiv470_div_mod e1.1.val hk e1.2.isLt (p := i1.val + 1) (by omega) (by omega)
    have hdm2 := subdiv470_div_mod e2.1.val hk e2.2.isLt (p := i2.val + 1) (by omega) (by omega)
    rw [hval'] at hdm2
    apply hne
    exact Prod.ext (Fin.ext (hdm1.1.symm.trans hdm2.1)) (Fin.ext (hdm1.2.1.symm.trans hdm2.2.1))
  have hInner_lb : ∀ e ∈ DirEdges,
      k + (if e ∈ BadEdges then 1 else 0) ≤ (U ∩ Inner e).card := by
    intro e he
    have ⟨hlt, hadj⟩ := (Finset.mem_filter.mp he).2
    let ce : ℕ → Bool := fun p =>
      if hp : p ≤ 2 * k + 1 then decide (subdivVert470 k e.1 e.2 p hp ∈ U) else false
    have hce_cov : ∀ j : ℕ, j ≤ 2 * k → ce j = true ∨ ce (j + 1) = true := by
      intro j hj
      have hadjS : S.Adj (subdivVert470 k e.1 e.2 j (by omega))
          (subdivVert470 k e.1 e.2 (j + 1) (by omega)) := by
        rw [hS]
        exact ⟨e.1, e.2, hlt, hadj, j, hj,
          Or.inl ⟨subdivVert470_Q Q hQ e.1 e.2 j (by omega),
            subdivVert470_Q Q hQ e.1 e.2 (j + 1) (by omega)⟩⟩
      rcases hU _ _ hadjS with h1 | h2
      · left
        simp only [ce, dif_pos (by omega : j ≤ 2 * k + 1), decide_eq_true_eq]
        exact h1
      · right
        simp only [ce, dif_pos (by omega : j + 1 ≤ 2 * k + 1), decide_eq_true_eq]
        exact h2
    have hlb := path_cover_lb k ce hce_cov
    have hcond_eq : (ce 0 = false ∧ ce (2 * k + 1) = false) ↔ e ∈ BadEdges := by
      have h0v : subdivVert470 k e.1 e.2 0 (Nat.zero_le _) = origEmb e.1 := by
        apply Fin.ext
        simp [subdivVert470, origEmb]
      have htv : subdivVert470 k e.1 e.2 (2 * k + 1) (le_refl _) = origEmb e.2 := by
        apply Fin.ext
        simp [subdivVert470, origEmb]
      have h0 : ce 0 = false ↔ e.1 ∉ R0 := by
        simp only [ce, dif_pos (Nat.zero_le _), h0v, decide_eq_false_iff_not, R0, Finset.mem_filter,
          Finset.mem_univ, true_and]
      have htop : ce (2 * k + 1) = false ↔ e.2 ∉ R0 := by
        simp only [ce, dif_pos (le_refl _), htv, decide_eq_false_iff_not, R0, Finset.mem_filter,
          Finset.mem_univ, true_and]
      simp only [h0, htop, BadEdges, Finset.mem_filter, he, true_and]
    have hcard_le :
        ((Finset.Icc 1 (2 * k)).filter (fun j => ce j = true)).card ≤ (U ∩ Inner e).card := by
      let f : ℕ → Fin (m + 2 * k * (m * m)) := fun j =>
        if hj : 1 ≤ j ∧ j ≤ 2 * k then innerVert e ⟨j - 1, by omega⟩
        else ⟨0, by have := e.1.isLt; omega⟩
      have hmaps : ∀ j ∈ (Finset.Icc 1 (2 * k)).filter (fun j => ce j = true),
          f j ∈ U ∩ Inner e := by
        intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hj_icc, hj_ce⟩
        rcases Finset.mem_Icc.mp hj_icc with ⟨hj1, hj2⟩
        have hmemU : subdivVert470 k e.1 e.2 j (by omega) ∈ U := by
          simpa [ce, dif_pos (by omega : j ≤ 2 * k + 1)] using hj_ce
        have heq_vert : f j = subdivVert470 k e.1 e.2 j (by omega) := by
          apply Fin.ext
          simp only [f, dif_pos (And.intro hj1 hj2), innerVert, subdivVert470,
            dif_neg (by omega : j ≠ 0), dif_neg (by omega : j ≠ 2 * k + 1)]
          omega
        rw [Finset.mem_inter]
        refine ⟨heq_vert ▸ hmemU, ?_⟩
        simp only [f, dif_pos (And.intro hj1 hj2), Inner]
        exact Finset.mem_image.mpr ⟨⟨j - 1, by omega⟩, Finset.mem_univ _, rfl⟩
      have hinj : Set.InjOn f ↑((Finset.Icc 1 (2 * k)).filter (fun j => ce j = true)) := by
        intro j1 hj1 j2 hj2 hfeq
        rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hj1).1 with ⟨h1a, h1b⟩
        rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hj2).1 with ⟨h2a, h2b⟩
        have hval := congrArg Fin.val hfeq
        simp only [f, dif_pos (And.intro h1a h1b), dif_pos (And.intro h2a h2b), innerVert] at hval
        omega
      exact Finset.card_le_card_of_injOn f hmaps hinj
    have hif_eq :
        (if ce 0 = false ∧ ce (2 * k + 1) = false then 1 else 0) =
          (if e ∈ BadEdges then 1 else 0) := by
      by_cases hb : e ∈ BadEdges
      · rw [if_pos hb, if_pos (hcond_eq.mpr hb)]
      · rw [if_neg hb, if_neg (mt hcond_eq.mp hb)]
    omega
  let Uinner : Finset (Fin (m + 2 * k * (m * m))) := DirEdges.biUnion fun e => U ∩ Inner e
  have hUinner_sub : Uinner ⊆ U := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨e, _, hxe⟩
    exact (Finset.mem_inter.mp hxe).1
  have hdisj_orig_inner : Disjoint Uorig Uinner := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨u, _, rfl⟩
    rcases Finset.mem_biUnion.mp hx2 with ⟨e, _, hxe⟩
    have hge := hInner_ge_m e (origEmb u) (Finset.mem_inter.mp hxe).2
    have hlt := u.isLt
    dsimp [origEmb] at hge
    omega
  have hUinner_card : k * DirEdges.card + BadEdges.card ≤ Uinner.card := by
    have hbi : Uinner.card = ∑ e ∈ DirEdges, (U ∩ Inner e).card := by
      apply Finset.card_biUnion
      intro e1 _ e2 _ hne
      exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hInner_disj e1 e2 hne)
    rw [hbi]
    have hsum_le :
        (∑ e ∈ DirEdges, (k + if e ∈ BadEdges then 1 else 0)) ≤
          ∑ e ∈ DirEdges, (U ∩ Inner e).card :=
      Finset.sum_le_sum hInner_lb
    have hsum_eval :
        (∑ e ∈ DirEdges, (k + if e ∈ BadEdges then 1 else 0)) =
          k * DirEdges.card + BadEdges.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm,
        Finset.sum_boole, Nat.cast_id]
      have hfilt : DirEdges.filter (· ∈ BadEdges) = BadEdges := by
        ext e
        simp only [Finset.mem_filter, BadEdges, and_iff_right_iff_imp]
        intro h
        exact h.1
      rw [hfilt]
    omega
  have hunion_sub : Uorig ∪ Uinner ⊆ U := Finset.union_subset hUorig_sub hUinner_sub
  have hunion_card : Uorig.card + Uinner.card ≤ U.card := by
    rw [← Finset.card_union_of_disjoint hdisj_orig_inner]
    exact Finset.card_le_card hunion_sub
  rw [hcardH]
  omega

end PEqualNP.Outside
