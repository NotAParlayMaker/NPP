import Mathlib
import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_989_aux

private def pairing {F : Type} [Field F] :
    LinearMap.BilinForm F (Fin 3 → F) := dotProductBilin F F

private theorem dot_pairing {F : Type} [Field F] (x y : Fin 3 → F) :
    pairing x y = ∑ t : Fin 3, x t * y t := rfl

private theorem pairing_nondegenerate {F : Type} [Field F] :
    (pairing (F := F)).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have hi := hx (Pi.single i 1)
    simpa [dot_pairing, Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using hi
  · intro x hx
    funext i
    have hi := hx (Pi.single i 1)
    simpa [dot_pairing, Pi.single_apply, ite_mul, Finset.sum_ite_eq'] using hi

private theorem not_two_common {F : Type} [Field F] (a b c d : Fin 3 → F)
    (ha : a ≠ 0) (hb : ∀ t : F, b ≠ t • a)
    (hc : c ≠ 0) (hd : ∀ t : F, d ≠ t • c)
    (hac : pairing a c = 0) (hbc : pairing b c = 0) (had : pairing a d = 0) :
    pairing b d ≠ 0 := by
  intro hbd
  let W := Submodule.span F (Set.range (![a,b] : Fin 2 → Fin 3 → F))
  have hab : LinearIndependent F (![a,b] : Fin 2 → Fin 3 → F) :=
    (LinearIndependent.pair_iff' ha).2 fun t => (hb t).symm
  have hw : Module.finrank F W = 2 := by
    simpa [W] using finrank_span_eq_card hab
  have member (x : Fin 3 → F) (hax : pairing a x = 0) (hbx : pairing b x = 0) :
      x ∈ pairing.orthogonal W := by
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> assumption
    · simp
    · intro y z hy hz hy' hz'
      simp [hy', hz']
    · intro t y hy hy'
      simp [hy']
  let O := pairing.orthogonal W
  have hcd : LinearIndependent F (![c,d] : Fin 2 → Fin 3 → F) :=
    (LinearIndependent.pair_iff' hc).2 fun t => (hd t).symm
  let v : Fin 2 → O := ![⟨c, member c hac hbc⟩, ⟨d, member d had hbd⟩]
  have hv : LinearIndependent F v := by
    apply LinearIndependent.of_comp O.subtype
    convert hcd using 1
    funext i
    fin_cases i <;> rfl
  have hdim : 2 ≤ Module.finrank F O := by simpa using hv.fintype_card_le_finrank
  have hO : Module.finrank F O = 1 := by
    change Module.finrank F (pairing.orthogonal W) = 1
    rw [LinearMap.BilinForm.finrank_orthogonal pairing_nondegenerate, hw]
    simp
  omega

private noncomputable def linearPoly {F : Type} [Field F] (x : Fin 3 → F) : MvPolynomial (Fin 3) F :=
  ∑ t, MvPolynomial.C (x t) * MvPolynomial.X t

private theorem linearPoly_eval {F : Type} [Field F] (x y : Fin 3 → F) :
    MvPolynomial.eval y (linearPoly x) = pairing x y := by
  simp [linearPoly, dot_pairing]

private theorem linearPoly_homogeneous {F : Type} [Field F] (x : Fin 3 → F) :
    (linearPoly x).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro t _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

private theorem powerProduct_homogeneous {F : Type} [Field F] {α : Type}
    (s : Finset α) (x : α → Fin 3 → F) (i : Fin 3) (b : ℕ) (h : s.card ≤ b) :
    ((∏ p ∈ s, linearPoly (x p)) * (MvPolynomial.X i) ^ (b - s.card)).IsHomogeneous b := by
  have first : (∏ p ∈ s, linearPoly (x p)).IsHomogeneous s.card := by
    simpa using MvPolynomial.IsHomogeneous.prod s
      (fun p => linearPoly (x p)) (fun _ => 1)
      (fun p _ => linearPoly_homogeneous (x p))
  have last : ((MvPolynomial.X i : MvPolynomial (Fin 3) F) ^ (b - s.card)).IsHomogeneous
      (b - s.card) := by
    exact MvPolynomial.isHomogeneous_X_pow i _
  simpa [Nat.add_sub_of_le h] using first.mul last

private abbrev OrderedPair (r : ℕ) :=
  {a : Fin r × Fin r // a.1 < a.2}

private theorem orderedPair_card (r : ℕ) :
    Fintype.card (OrderedPair r) = r.choose 2 := by
  rw [Fintype.card_subtype]
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin r)))
  simpa using h

private theorem double_choose (b : ℕ) :
    2 * (b + 2).choose 2 = (b + 1) * (b + 2) := by
  rw [Nat.choose_two_right]
  have hd : 2 ∣ (b + 2) * (b + 2 - 1) := by
    rcases Nat.mod_two_eq_zero_or_one b with he | he
    · apply dvd_mul_of_dvd_left
      omega
    · apply dvd_mul_of_dvd_right
      omega
  rw [Nat.mul_div_cancel' hd]
  rw [show b + 2 - 1 = b + 1 by omega, Nat.mul_comm]

private noncomputable def decode (b : ℕ) (e : OrderedPair (b + 2)) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![e.val.1.val, e.val.2.val - e.val.1.val - 1, b + 1 - e.val.2.val]

private theorem represented (b : ℕ) (d : Fin 3 →₀ ℕ) (h : d.degree = b) :
    ∃ e, decode b e = d := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at h
  let e : OrderedPair (b + 2) :=
    ⟨(⟨d 0, by omega⟩, ⟨d 0 + d 1 + 1, by omega⟩), by
      change d 0 < d 0 + d 1 + 1
      omega⟩
  refine ⟨e, ?_⟩
  ext j
  fin_cases j <;> simp [decode, e] <;> omega

private noncomputable def coeffMap {F : Type} [Field F] (b : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) F b →ₗ[F] (OrderedPair (b + 2) → F) where
  toFun f e := f.val.coeff (decode b e)
  map_add' f g := by ext e; simp
  map_smul' r f := by ext e; simp

private theorem coeffMap_injective {F : Type} [Field F] (b : ℕ) :
    Function.Injective (coeffMap (F := F) b) := by
  intro p q hpq
  apply Subtype.ext
  ext d
  by_cases hd : d.degree = b
  · obtain ⟨e, rfl⟩ := represented b d hd
    exact congrFun hpq e
  · exact (MvPolynomial.IsHomogeneous.coeff_eq_zero p.property hd).trans
      (MvPolynomial.IsHomogeneous.coeff_eq_zero q.property hd).symm

private noncomputable def evalHom {F : Type} [Field F] (b : ℕ) (v : Fin 3 → F) :
    MvPolynomial.homogeneousSubmodule (Fin 3) F b →ₗ[F] F :=
  (MvPolynomial.aeval v).toLinearMap.comp (MvPolynomial.homogeneousSubmodule (Fin 3) F b).subtype

private theorem independent_evaluations {F : Type} [Field F] (b k : ℕ)
    (l : Fin k → Fin 3 → F) (p : Fin k → MvPolynomial.homogeneousSubmodule (Fin 3) F b)
    (diag : ∀ i, MvPolynomial.eval (l i) (p i).val ≠ 0)
    (off : ∀ i j, i ≠ j → MvPolynomial.eval (l j) (p i).val = 0) :
    k ≤ (b + 2).choose 2 := by
  classical
  have hp : LinearIndependent F p := by
    rw [Fintype.linearIndependent_iff]
    intro w hw i
    have h := congrArg (evalHom b (l i)) hw
    simp only [map_sum, map_smul, map_zero] at h
    change (∑ j, w j * MvPolynomial.eval (l i) (p j).val) = 0 at h
    rw [Finset.sum_eq_single i] at h
    · exact (mul_eq_zero.mp h).resolve_right (diag i)
    · intro j _ hj
      rw [off j i hj, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  have hi := hp.map' (coeffMap b) (LinearMap.ker_eq_bot.mpr (coeffMap_injective b))
  have h := hi.fintype_card_le_finrank
  simpa [orderedPair_card, Module.finrank_fintype_fun_eq_card] using h

theorem upper
    (F : Type) [Field F] (n k b : ℕ)
    (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n))
    (g : (Fin n → Bool) → Bool)
    (hpt : ∀ p, pt p ≠ 0) (hpdist : ∀ p p', p ≠ p' → ∀ c : F, pt p' ≠ c • pt p)
    (hl : ∀ i, l i ≠ 0) (hldist : ∀ i j, i ≠ j → ∀ c : F, l j ≠ c • l i)
    (hy : ∀ i, (y i).card ≤ b)
    (hyoff : ∀ i, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0)
    (hsafe : ∀ (i : Fin k) (x : Fin n → Bool), g x = true →
      ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0)
    (hwitness : ∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧
      (∑ t : Fin 3, pt p t * l i t) = 0 ∧ (∑ t : Fin 3, pt p' t * l i t) = 0 ∧
      g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧
      g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) :
    2 * k ≤ (b + 1) * (b + 2) := by
  classical
  have hhit : ∀ i j : Fin k, i ≠ j → ∃ p ∈ y i, pairing (pt p) (l j) = 0 := by
    intro i j hij
    obtain ⟨a, a', haa', hai, ha'i, hga, hga'⟩ := hwitness i
    obtain ⟨v, hv, hvj⟩ := hsafe j _ hga
    obtain ⟨w, hw, hwj⟩ := hsafe j _ hga'
    rcases of_decide_eq_true hv with hv | he
    · exact ⟨v, hv, hvj⟩
    subst v
    rcases of_decide_eq_true hw with hw | he'
    · exact ⟨w, hw, hwj⟩
    subst w
    exact (not_two_common (pt a) (pt a') (l i) (l j)
      (hpt a) (hpdist a a' haa') (hl i) (hldist i j hij) hai ha'i hvj hwj).elim
  have coord (i : Fin k) : ∃ t : Fin 3, l i t ≠ 0 := by
    by_contra! h
    exact hl i (funext h)
  choose c hc using coord
  let f : Fin k → MvPolynomial.homogeneousSubmodule (Fin 3) F b := fun i =>
    ⟨(∏ p ∈ y i, linearPoly (pt p)) * (MvPolynomial.X (c i)) ^ (b - (y i).card),
      powerProduct_homogeneous (y i) pt (c i) b (hy i)⟩
  have h := independent_evaluations b k l f (fun i => by
    simp only [f, map_mul, map_pow, MvPolynomial.eval_X, map_prod, linearPoly_eval]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun p hp => hyoff i p hp) (pow_ne_zero _ (hc i)))
    (fun i j hij => by
      obtain ⟨p, hp, hz⟩ := hhit i j hij
      simp only [f, map_mul, map_pow, MvPolynomial.eval_X, map_prod, linearPoly_eval]
      rw [Finset.prod_eq_zero hp hz, zero_mul])
  rw [← double_choose b]
  omega

private def arc {F : Type} [Field F] {b : ℕ} (a : Fin (b + 1) ↪ F)
    (i : Fin (b + 2)) : Fin 3 → F :=
  if hi : i.val < b + 1 then ![1, a ⟨i.val, hi⟩, (a ⟨i.val, hi⟩) ^ 2] else ![0,0,1]

private theorem arc_ne_zero {F : Type} [Field F] {b : ℕ} (a : Fin (b + 1) ↪ F)
    (i : Fin (b + 2)) : arc a i ≠ 0 := by
  intro h
  by_cases hi : i.val < b + 1
  · have h0 := congrFun h 0
    simp [arc, hi] at h0
  · have h2 := congrFun h 2
    simp [arc, hi] at h2

private theorem arc_distinct {F : Type} [Field F] {b : ℕ} (a : Fin (b + 1) ↪ F)
    {i j : Fin (b + 2)} (hij : i ≠ j) (t : F) : arc a j ≠ t • arc a i := by
  intro h
  by_cases hi : i.val < b + 1 <;> by_cases hj : j.val < b + 1
  · have ht : t = 1 := by
      have hh := congrFun h 0
      simpa [arc, hi, hj, Pi.smul_apply, smul_eq_mul, eq_comm] using hh
    have hh := congrFun h 1
    simp [arc, hi, hj, Pi.smul_apply, smul_eq_mul, ht, a.injective.eq_iff] at hh
    exact hij (Fin.ext hh.symm)
  · have ht : t = 0 := by
      have hh := congrFun h 0
      simpa [arc, hi, hj, Pi.smul_apply, smul_eq_mul, eq_comm] using hh
    exact arc_ne_zero a j (by simpa [ht] using h)
  · have hh := congrFun h 0
    simp [arc, hi, hj, Pi.smul_apply, smul_eq_mul] at hh
  · apply hij
    apply Fin.ext
    omega

private def secant {F : Type} [Field F] {b : ℕ} (a : Fin (b + 1) ↪ F)
    (e : OrderedPair (b + 2)) : Fin 3 → F :=
  let x := arc a e.val.1 1
  let y := arc a e.val.2 1
  if e.val.2.val < b + 1 then ![x * y, -(x + y), 1] else ![-x, 1, 0]

private theorem secant_ne_zero {F : Type} [Field F] {b : ℕ} (a : Fin (b + 1) ↪ F)
    (e : OrderedPair (b + 2)) : secant a e ≠ 0 := by
  intro h
  by_cases he : e.val.2.val < b + 1
  · have hh := congrFun h 2
    simp [secant, he] at hh
  · have hh := congrFun h 1
    simp [secant, he] at hh

private theorem secant_iff {F : Type} [Field F] {b : ℕ} (a : Fin (b + 1) ↪ F)
    (e : OrderedPair (b + 2)) (i : Fin (b + 2)) :
    pairing (arc a i) (secant a e) = 0 ↔ i = e.val.1 ∨ i = e.val.2 := by
  have he : e.val.1.val < b + 1 := by
    have h := e.property
    change e.val.1.val < e.val.2.val at h
    omega
  by_cases hf : e.val.2.val < b + 1 <;> by_cases hi : i.val < b + 1
  · simp only [secant, arc, dite_eq_left he, dite_eq_left hf, dite_eq_left hi, ite_eq_left hf,
      dot_pairing, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, one_mul]
    change a ⟨e.val.1.val, he⟩ * a ⟨e.val.2.val, hf⟩ +
      a ⟨i.val, hi⟩ * -(a ⟨e.val.1.val, he⟩ + a ⟨e.val.2.val, hf⟩) +
      a ⟨i.val, hi⟩ ^ 2 * 1 = 0 ↔ _
    rw [mul_one]
    rw [show a ⟨e.val.1.val, he⟩ * a ⟨e.val.2.val, hf⟩ +
          a ⟨i.val, hi⟩ * -(a ⟨e.val.1.val, he⟩ + a ⟨e.val.2.val, hf⟩) +
          a ⟨i.val, hi⟩ ^ 2 =
        (a ⟨i.val, hi⟩ - a ⟨e.val.1.val, he⟩) *
          (a ⟨i.val, hi⟩ - a ⟨e.val.2.val, hf⟩) by ring, mul_eq_zero]
    simp [sub_eq_zero, a.injective.eq_iff, Fin.ext_iff]
  · have hl : i ≠ e.val.1 := fun h => hi (h ▸ he)
    have hr : i ≠ e.val.2 := fun h => hi (h ▸ hf)
    simp [secant, arc, hf, he, hi, dot_pairing, Fin.sum_univ_three, hl, hr]
  · have hr : i ≠ e.val.2 := fun h => hf (h ▸ hi)
    have hs : -(a ⟨e.val.1.val, he⟩) + a ⟨i.val, hi⟩ =
        a ⟨i.val, hi⟩ - a ⟨e.val.1.val, he⟩ := by ring
    simp [secant, arc, hf, he, hi, dot_pairing, Fin.sum_univ_three, hr, hs,
      sub_eq_zero, a.injective.eq_iff, Fin.ext_iff]
  · have hr : i = e.val.2 := Fin.ext (by omega)
    simp [secant, arc, hf, he, dot_pairing, Fin.sum_univ_three, hr]

private theorem distinct_pair_endpoint {r : ℕ} {e f : OrderedPair r} (h : e ≠ f) :
    (e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2) ∨
    (e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2) := by
  by_cases first : e.val.1 = f.val.1 ∨ e.val.1 = f.val.2
  swap
  · exact Or.inl ⟨fun h => first (Or.inl h), fun h => first (Or.inr h)⟩
  by_cases second : e.val.2 = f.val.1 ∨ e.val.2 = f.val.2
  swap
  · exact Or.inr ⟨fun h => second (Or.inl h), fun h => second (Or.inr h)⟩
  exfalso
  have he := e.property
  have hf := f.property
  rcases first with ha | ha <;> rcases second with hb | hb
  · exact (ne_of_lt he) (ha.trans hb.symm)
  · exact h (Subtype.ext (Prod.ext ha hb))
  · rw [ha, hb] at he
    exact (asymm hf he)
  · exact (ne_of_lt he) (ha.trans hb.symm)

private theorem secant_distinct {F : Type} [Field F] {b : ℕ} (a : Fin (b + 1) ↪ F)
    {e f : OrderedPair (b + 2)} (hef : e ≠ f) (t : F) : secant a f ≠ t • secant a e := by
  intro h
  obtain ⟨i, hi, hif⟩ : ∃ i, (i = e.val.1 ∨ i = e.val.2) ∧
      (i ≠ f.val.1 ∧ i ≠ f.val.2) := by
    rcases distinct_pair_endpoint hef with h | h
    · exact ⟨e.val.1, Or.inl rfl, h⟩
    · exact ⟨e.val.2, Or.inr rfl, h⟩
  have z := (secant_iff a e i).2 hi
  have z' : pairing (arc a i) (secant a f) = 0 := by simp [h, z]
  exact ((secant_iff a f i).1 z').elim hif.1 hif.2


set_option maxHeartbeats 1500000 in
theorem lower : ∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2) := by
  intro F _ _ b hb
  classical
  obtain ⟨a⟩ : Nonempty (Fin (b + 1) ↪ F) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hb)
  let P := Projectivization F (Fin 3 → F)
  let : Fintype P := Fintype.ofFinite P
  let n := Fintype.card P
  let k := Fintype.card (OrderedPair (b + 2))
  let points : P ≃ Fin n := Fintype.equivFin _
  let pairs : OrderedPair (b + 2) ≃ Fin k := Fintype.equivFin _
  let pair (i : Fin k) : OrderedPair (b + 2) := pairs.symm i
  let pt (p : Fin n) : Fin 3 → F := (points.symm p).rep
  let l (i : Fin k) : Fin 3 → F := secant a (pair i)
  let wrap (r : Fin (b + 2)) : Fin n :=
    points (Projectivization.mk F (arc a r) (arc_ne_zero a r))
  have wrap_inj : Function.Injective wrap := by
    intro r s h
    have h' := points.injective h
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' F _ _
      (arc_ne_zero a r) (arc_ne_zero a s)).1 h'
    by_contra! hh
    exact arc_distinct a hh.symm t ht.symm
  have incident (i : Fin k) (r : Fin (b + 2)) :
      (∑ t : Fin 3, pt (wrap r) t * l i t) = 0 ↔
        r = (pair i).val.1 ∨ r = (pair i).val.2 := by
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep F (arc a r) (arc_ne_zero a r)
    have hu' : pt (wrap r) = (u : F) • arc a r := by
      simpa only [pt, wrap, Equiv.symm_apply_apply, Units.smul_def] using hu.symm
    rw [← dot_pairing, hu', map_smul, LinearMap.smul_apply, smul_eq_mul,
      mul_eq_zero, or_iff_right (Units.ne_zero u)]
    exact secant_iff a (pair i) r
  let inner (i : Fin k) : Finset (Fin (b + 2)) :=
    (Finset.univ.erase (pair i).val.1).erase (pair i).val.2
  let y (i : Fin k) : Finset (Fin n) := (inner i).image wrap
  have mem_inner (i : Fin k) (r : Fin (b + 2)) :
      r ∈ inner i ↔ r ≠ (pair i).val.1 ∧ r ≠ (pair i).val.2 := by
    change r ∈ (Finset.univ.erase (pair i).val.1).erase (pair i).val.2 ↔ _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  let g (x : Fin n → Bool) : Bool :=
    decide (∃ j : Fin k, (∀ p ∈ y j, x p = true) ∧
      (x (wrap (pair j).val.1) = true ∨ x (wrap (pair j).val.2) = true))
  refine ⟨n, k, pt, l, y, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (points.symm p).rep_ne_zero
  · intro p p' hpp c h
    apply hpp
    apply points.symm.injective
    have one := (Projectivization.mk_eq_mk_iff' F _ _ (points.symm p').rep_ne_zero
      (points.symm p).rep_ne_zero).2 ⟨c, h.symm⟩
    rw [Projectivization.mk_rep, Projectivization.mk_rep] at one
    exact one.symm
  · intro v hv
    let q := Projectivization.mk F v hv
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
    refine ⟨points q, ((a⁻¹ : Fˣ) : F), ?_⟩
    have eq' : (a : F) • v = pt (points q) := by
      simpa only [pt, Equiv.symm_apply_apply, q, Units.smul_def] using ha
    rw [← eq', smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero a), one_smul]
  · intro i
    exact secant_ne_zero a (pair i)
  · intro i j hij
    exact secant_distinct a (fun h => hij (pairs.symm.injective h))
  · intro i
    have hmem : (pair i).val.2 ∈ (Finset.univ : Finset (Fin (b + 2))).erase (pair i).val.1 :=
      Finset.mem_erase.mpr ⟨(ne_of_lt (pair i).property).symm, Finset.mem_univ _⟩
    have hc : (inner i).card = b := by
      change ((Finset.univ.erase (pair i).val.1).erase (pair i).val.2).card = b
      rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    exact (Finset.card_image_le).trans hc.le
  · intro i p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    intro hz
    exact ((incident i r).1 hz).elim ((mem_inner i r).1 hr).1 ((mem_inner i r).1 hr).2
  · intro x x' hxx hg
    obtain ⟨j, hy, hw⟩ := of_decide_eq_true hg
    exact decide_eq_true ⟨j, fun p hp => hxx p (hy p hp), hw.imp (hxx _) (hxx _)⟩
  · intro i x hx
    obtain ⟨j, hy, hw⟩ := of_decide_eq_true hx
    by_cases hij : i = j
    · subst j
      rcases hw with ha | ha
      · exact ⟨wrap (pair i).val.1, ha, (incident i _).2 (Or.inl rfl)⟩
      · exact ⟨wrap (pair i).val.2, ha, (incident i _).2 (Or.inr rfl)⟩
    · rcases distinct_pair_endpoint (fun h => hij (pairs.symm.injective h)) with hr | hr
      · refine ⟨wrap (pair i).val.1, hy _ ?_, (incident i _).2 (Or.inl rfl)⟩
        exact Finset.mem_image.mpr ⟨_, (mem_inner j _).2 hr, rfl⟩
      · refine ⟨wrap (pair i).val.2, hy _ ?_, (incident i _).2 (Or.inr rfl)⟩
        exact Finset.mem_image.mpr ⟨_, (mem_inner j _).2 hr, rfl⟩
  · intro i
    have gives (r : Fin (b + 2)) (hr : r = (pair i).val.1 ∨ r = (pair i).val.2) :
        g (fun v : Fin n => decide (v ∈ y i ∨ v = wrap r)) = true := by
      apply decide_eq_true
      refine ⟨i, fun p hp => decide_eq_true (Or.inl hp), ?_⟩
      rcases hr with rfl | rfl
      · exact Or.inl (decide_eq_true (Or.inr rfl))
      · exact Or.inr (decide_eq_true (Or.inr rfl))
    exact ⟨wrap (pair i).val.1, wrap (pair i).val.2,
      fun h => (ne_of_lt (pair i).property) (wrap_inj h),
      (incident i _).2 (Or.inl rfl), (incident i _).2 (Or.inr rfl),
      gives _ (Or.inl rfl), gives _ (Or.inr rfl)⟩
  · exact (congrArg (2 * ·) (orderedPair_card (b + 2))).trans (double_choose b)

end PEqualNP.Outside.L_meta_989_aux

theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) :=
  ⟨PEqualNP.Outside.L_meta_989_aux.upper, PEqualNP.Outside.L_meta_989_aux.lower⟩
