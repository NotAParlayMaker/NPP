import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_989_aux

open Matrix MvPolynomial

abbrev V (F : Type) := Fin 3 → F

lemma uniqueLine {F : Type} [Field F] {p q u v : V F}
    (hp : p ≠ 0) (hpq : ∀ c : F, q ≠ c • p) (hu : u ≠ 0)
    (hpu : p ⬝ᵥ u = 0) (hqu : q ⬝ᵥ u = 0)
    (hpv : p ⬝ᵥ v = 0) (hqv : q ⬝ᵥ v = 0) : ∃ c : F, v = c • u := by
  have hc : crossProduct p q ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.2
    ((LinearIndependent.pair_iff' hp).2 fun c => (hpq c).symm)
  have par (z : V F) (a : p ⬝ᵥ z = 0) (b : q ⬝ᵥ z = 0) :
      ∃ c : F, c • crossProduct p q = z := by
    by_contra! h
    have hn := crossProduct_ne_zero_iff_linearIndependent.2
      ((LinearIndependent.pair_iff' hc).2 h)
    apply hn
    simpa only [cross_cross_eq_smul_sub_smul, a, b, zero_smul, sub_zero]
  obtain ⟨c, ce⟩ := par u hpu hqu
  obtain ⟨d, de⟩ := par v hpv hqv
  have cn : c ≠ 0 := by rintro rfl; exact hu (by simpa using ce.symm)
  exact ⟨d / c, by rw [← ce, ← de, smul_smul, div_mul_cancel₀ _ cn]⟩

noncomputable def form {F : Type} [Field F] (p : V F) : MvPolynomial (Fin 3) F :=
  ∑ t, C (p t) * X t

lemma formHom {F : Type} [Field F] (p : V F) : (form p).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ _

lemma formEval {F : Type} [Field F] (p z : V F) : eval z (form p) = p ⬝ᵥ z := by
  simp [form, dotProduct]

lemma interpolation {F : Type} [Field F] {k b : ℕ} (l : Fin k → V F)
    (P : Fin k → MvPolynomial (Fin 3) F) (hom : ∀ i, (P i).IsHomogeneous b)
    (diag : ∀ i, eval (l i) (P i) ≠ 0)
    (off : ∀ i j, i ≠ j → eval (l j) (P i) = 0) : 2 * k ≤ (b + 1) * (b + 2) := by
  classical
  let D := (Finset.univ : Finset (Fin 3)).finsuppAntidiag b
  let A : Matrix (Fin k) D F := fun i d => (P i).coeff d.val
  let B : Matrix D (Fin k) F := fun d j => ∏ t, l j t ^ d.val t
  have he (i j : Fin k) : (A * B) i j = eval (l j) (P i) := by
    rw [Matrix.mul_apply, eval_eq']
    change (∑ d : D, (P i).coeff d.val * ∏ t, l j t ^ d.val t) = _
    rw [Finset.sum_coe_sort D (fun d : Fin 3 →₀ ℕ => (P i).coeff d * ∏ t, l j t ^ d t)]
    symm
    apply Finset.sum_subset
    · intro d hd
      have hsum := (hom i).degree_eq_sum_deg_support hd
      apply Finset.mem_finsuppAntidiag.mpr
      exact ⟨(Finset.sum_subset (Finset.subset_univ _) (by
        intro t _ ht
        simpa using ht)).symm.trans hsum.symm, Finset.subset_univ _⟩
    · intro d _ hd
      simp [notMem_support_iff.mp hd]
  have eqd : A * B = Matrix.diagonal (fun i => eval (l i) (P i)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [he]
    · simp [he, Matrix.diagonal_apply, hij, off i j hij]
  have hr := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  rw [eqd, Matrix.rank_diagonal] at hr
  have hc : Fintype.card {i : Fin k // eval (l i) (P i) ≠ 0} = k := by
    simp [Fintype.card_subtype, diag]
  rw [hc] at hr
  have hD : Fintype.card D = (b + 2).choose 2 := by
    change Fintype.card (↑((Finset.univ : Finset (Fin 3)).finsuppAntidiag b)) = _
    rw [Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show 3 + b - 1 = b + 2 by omega]
    exact Nat.choose_symm_of_eq_add rfl
  rw [hD, Nat.choose_two_right] at hr
  have hb : b + 2 - 1 = b + 1 := by omega
  rw [hb, Nat.mul_comm (b + 2)] at hr
  omega

lemma upper {F : Type} [Field F] {n k b : ℕ} (pt : Fin n → V F) (l : Fin k → V F)
    (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool)
    (hp : ∀ p, pt p ≠ 0) (hpp : ∀ p q, p ≠ q → ∀ c : F, pt q ≠ c • pt p)
    (hl : ∀ i, l i ≠ 0) (hll : ∀ i j, i ≠ j → ∀ c : F, l j ≠ c • l i)
    (hc : ∀ i, (y i).card ≤ b) (hn : ∀ i, ∀ p ∈ y i, pt p ⬝ᵥ l i ≠ 0)
    (safe : ∀ i x, g x = true → ∃ p, x p = true ∧ pt p ⬝ᵥ l i = 0)
    (two : ∀ i, ∃ p q, p ≠ q ∧ pt p ⬝ᵥ l i = 0 ∧ pt q ⬝ᵥ l i = 0 ∧
      g (fun v => decide (v ∈ y i ∨ v = p)) = true ∧
      g (fun v => decide (v ∈ y i ∨ v = q)) = true) : 2 * k ≤ (b + 1) * (b + 2) := by
  classical
  have crossHit (i j : Fin k) (ij : i ≠ j) : ∃ v ∈ y i, pt v ⬝ᵥ l j = 0 := by
    by_contra! miss
    obtain ⟨p, q, pq, pi, qi, gp, gq⟩ := two i
    have hit (a : Fin n) (ga : g (fun v => decide (v ∈ y i ∨ v = a)) = true) :
        pt a ⬝ᵥ l j = 0 := by
      obtain ⟨v, hv, zv⟩ := safe j _ ga
      rcases of_decide_eq_true hv with hv | rfl
      · exact (miss v hv zv).elim
      · exact zv
    obtain ⟨c, eq⟩ := uniqueLine (hp p) (hpp p q pq) (hl i) pi qi (hit p gp) (hit q gq)
    exact hll i j ij c eq
  have non (i : Fin k) : ∃ j, l i j ≠ 0 := by
    by_contra! h
    exact hl i (funext h)
  choose j hj using non
  let P (i : Fin k) : MvPolynomial (Fin 3) F :=
    (X (j i)) ^ (b - (y i).card) * ∏ p ∈ y i, form (pt p)
  apply interpolation l P
  · intro i
    have h := IsHomogeneous.prod (y i) (fun p => form (pt p)) (fun _ => 1) (fun p _ => formHom (pt p))
    have h' : (∏ p ∈ y i, form (pt p)).IsHomogeneous (y i).card := by simpa using h
    have hh := (isHomogeneous_X_pow (R := F) (j i) (b - (y i).card)).mul h'
    simpa [P, Nat.sub_add_cancel (hc i)] using hh
  · intro i
    simp only [P, map_mul, map_pow, eval_X, map_prod, formEval]
    exact mul_ne_zero (pow_ne_zero _ (hj _)) (Finset.prod_ne_zero_iff.mpr (hn i))
  · intro i r hir
    obtain ⟨v, hv, zv⟩ := crossHit i r hir
    simp only [P, map_mul, map_pow, eval_X, map_prod, formEval]
    rw [Finset.prod_eq_zero hv zv, mul_zero]

abbrev Chart (F : Type) := (F × F) ⊕ Option F

def point {F : Type} [Field F] : Chart F → V F
  | .inl (a, b) => ![1, a, b]
  | .inr (.some a) => ![0, 1, a]
  | .inr .none => ![0, 0, 1]

lemma pointNonzero {F : Type} [Field F] (a : Chart F) : point a ≠ 0 := by
  rcases a with ⟨x,y⟩ | (_ | z)
  · intro h; simpa [point] using congrFun h 0
  · intro h; simpa [point] using congrFun h 2
  · intro h; simpa [point] using congrFun h 1

lemma pointUnique {F : Type} [Field F] (a d : Chart F) (c : F)
    (h : point a = c • point d) : a = d := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rcases a with ⟨x,y⟩ | (_ | z) <;> rcases d with ⟨x',y'⟩ | (_ | z') <;>
    simp [point, Pi.smul_apply, smul_eq_mul] at h0 h1 h2 ⊢ <;> subst c <;> simp_all

lemma pointComplete {F : Type} [Field F] (v : V F) : ∃ p : Chart F, ∃ c : F, v = c • point p := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · refine ⟨.inr .none, v 2, ?_⟩
      funext t; fin_cases t <;> simp [point, h0, h1]
    · refine ⟨.inr (.some (v 2 / v 1)), v 1, ?_⟩
      funext t; fin_cases t <;> simp [point, h0, mul_div_cancel₀, h1]
  · refine ⟨.inl (v 1 / v 0, v 2 / v 0), v 0, ?_⟩
    funext t; fin_cases t <;> simp [point, mul_div_cancel₀, h0]

def arc {F : Type} [Field F] : Option F ↪ Chart F where
  toFun
    | .none => .inr .none
    | .some t => .inl (t, t^2)
  inj' := by rintro (_ | a) (_ | b) h <;> simp_all

lemma arcNone {F : Type} [Field F] : arc (none : Option F) = Sum.inr none := rfl
lemma arcSome {F : Type} [Field F] (t : F) : arc (some t) = Sum.inl (t, t^2) := rfl

def chord {F : Type} [Field F] : Option F → Option F → V F
  | .some a, .some d => ![a*d, -(a+d), 1]
  | .some a, .none => ![-a, 1, 0]
  | .none, .some a => ![-a, 1, 0]
  | .none, .none => 0

lemma chordNonzero {F : Type} [Field F] (a d : Option F) (hne : a ≠ d) :
    chord a d ≠ 0 := by
  cases a <;> cases d <;> try contradiction
  all_goals intro h
  all_goals first | simpa [chord] using congrFun h 1 | simpa [chord] using congrFun h 2

lemma onChord {F : Type} [Field F] (a d t : Option F) (hne : a ≠ d) :
    point (arc t) ⬝ᵥ chord a d = 0 ↔ t = a ∨ t = d := by
  cases a with
  | none =>
    cases d with
    | none => contradiction
    | some d => cases t <;> simp [arcNone, arcSome, point, chord, vec3_dotProduct, neg_add_eq_zero, eq_comm]
  | some a =>
    cases d with
    | none => cases t <;> simp [arcNone, arcSome, point, chord, vec3_dotProduct, neg_add_eq_zero, eq_comm]
    | some d =>
      cases t with
      | none => simp [arcNone, point, chord, vec3_dotProduct]
      | some t =>
        rw [arcSome, vec3_dotProduct]
        change 1 * (a*d) + t * -(a+d) + t^2 * 1 = 0 ↔ some t = some a ∨ some t = some d
        simp only [one_mul, mul_one, Option.some.injEq]
        rw [show a * d + t * -(a + d) + t ^ 2 = (t - a) * (t - d) by ring]
        simp [mul_eq_zero, sub_eq_zero]

end PEqualNP.Outside.L_meta_989_aux

open PEqualNP.Outside.L_meta_989_aux Matrix

theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) := by
  constructor
  · intro F _ n k b pt l y g
    exact upper pt l y g
  intro F _ _ b hb
  classical
  let J := Fin (b + 2)
  obtain ⟨e⟩ : Nonempty (J ↪ Option F) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [J, Nat.add_assoc] using Nat.succ_le_succ hb
  let C := Fintype.equivFin (Chart F)
  let s := (Finset.univ : Finset J).powersetCard 2
  let E := s.equivFin
  let pair (i : Fin s.card) : Finset J := (E.symm i).val
  have card (i) : (pair i).card = 2 := (Finset.mem_powersetCard.mp (E.symm i).property).2
  have pinj : Function.Injective pair := fun i j h => E.symm.injective (Subtype.ext h)
  choose u v uv pairs using fun i => Finset.card_eq_two.mp (card i)
  let pos : J ↪ Fin (Fintype.card (Chart F)) := (e.trans arc).trans C.toEmbedding
  let pt (z : Fin (Fintype.card (Chart F))) := point (C.symm z)
  let line (i : Fin s.card) := chord (e (u i)) (e (v i))
  let base (i : Fin s.card) := ((pair i)ᶜ).map pos
  let f (x : Fin (Fintype.card (Chart F)) → Bool) := decide (∀ i : Fin s.card,
    ∃ p, x p = true ∧ pt p ⬝ᵥ line i = 0)
  have uv' (i) : e (u i) ≠ e (v i) := fun h => uv i (e.injective h)
  have onLine (t : J) (i : Fin s.card) : pt (pos t) ⬝ᵥ line i = 0 ↔ t ∈ pair i := by
    change point (C.symm (C (arc (e t)))) ⬝ᵥ chord (e (u i)) (e (v i)) = 0 ↔ _
    rw [C.symm_apply_apply, onChord _ _ _ (uv' i), pairs i]
    simp
  have distinctLine (i j : Fin s.card) (ij : i ≠ j) (c : F) (he : line j = c • line i) : False := by
    apply ij
    apply pinj
    apply Finset.eq_of_subset_of_card_le _ (by simp [card])
    intro t ht
    apply (onLine t j).mp
    rw [he, dotProduct_smul, (onLine t i).mpr ht, smul_zero]
  have picked (i : Fin s.card) (t : J) (ht : t ∈ pair i) :
      f (fun z => decide (z ∈ base i ∨ z = pos t)) = true := by
    apply decide_eq_true
    intro j
    by_cases h : j = i
    · subst j
      exact ⟨pos t, by simp, (onLine t i).2 ht⟩
    · have hn : ¬ pair j ⊆ pair i := fun sub =>
        h (pinj (Finset.eq_of_subset_of_card_le sub (by simp [card])))
      obtain ⟨w, hw, hi⟩ := Finset.not_subset.mp hn
      refine ⟨pos w, ?_, (onLine w j).2 hw⟩
      exact decide_eq_true (Or.inl (Finset.mem_map.mpr ⟨w, Finset.mem_compl.mpr hi, rfl⟩))
  refine ⟨_, _, pt, line, base, f, (fun i => pointNonzero _), ?_, ?_,
    (fun i => chordNonzero _ _ (uv' i)), distinctLine, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q pq c he
    exact pq ((C.symm.injective (pointUnique _ _ c he)).symm)
  · intro w _
    obtain ⟨p, c, h⟩ := pointComplete w
    exact ⟨C p, c, by simpa [pt] using h⟩
  · intro i
    simp [base, Finset.card_compl, card, J]
  · intro i p hp hzero
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hp
    exact Finset.mem_compl.mp ht ((onLine t i).mp hzero)
  · intro x x' h hfx
    apply decide_eq_true
    intro i
    obtain ⟨p, hp, hz⟩ := of_decide_eq_true hfx i
    exact ⟨p, h p hp, hz⟩
  · intro i x hx
    exact of_decide_eq_true hx i
  · intro i
    have h₁ : u i ∈ pair i := by simp [pairs i]
    have h₂ : v i ∈ pair i := by simp [pairs i]
    exact ⟨pos (u i), pos (v i), fun h => uv i (pos.injective h), (onLine _ i).2 h₁,
      (onLine _ i).2 h₂, picked i _ h₁, picked i _ h₂⟩
  · change 2 * ((Finset.univ : Finset J).powersetCard 2).card = _
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_two_right]
    have h : b + 2 - 1 = b + 1 := by omega
    rw [h, Nat.mul_comm (b + 2)]
    have hd : 2 ∣ (b + 1) * (b + 2) := by
      rcases Nat.mod_two_eq_zero_or_one b with he | ho
      · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _
      · exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero (by omega)) _
    exact Nat.mul_div_cancel' hd
