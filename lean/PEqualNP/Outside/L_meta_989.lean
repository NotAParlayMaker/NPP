import Mathlib
import PEqualNP.Defs

open Matrix MvPolynomial

namespace PEqualNP.Outside.L_meta_989

lemma prop_of_cross {F : Type} [Field F] {a b : Fin 3 → F} (ha : a ≠ 0)
    (h : crossProduct a b = 0) : ∃ c : F, b = c • a := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [cross_apply] at h0 h1 h2
  by_cases a0 : a 0 = 0
  · by_cases a1 : a 1 = 0
    · have a2 : a 2 ≠ 0 := by
        intro a2
        apply ha
        funext i
        fin_cases i <;> simp [a0, a1, a2]
      refine ⟨b 2 / a 2, ?_⟩
      funext i
      fin_cases i
      · show b 0 = b 2 / a 2 * a 0
        rw [div_mul_eq_mul_div, eq_div_iff a2]
        linear_combination h1
      · show b 1 = b 2 / a 2 * a 1
        rw [div_mul_eq_mul_div, eq_div_iff a2]
        linear_combination (-1 : F) * h0
      · show b 2 = b 2 / a 2 * a 2
        rw [div_mul_eq_mul_div, eq_div_iff a2]
    · refine ⟨b 1 / a 1, ?_⟩
      funext i
      fin_cases i
      · show b 0 = b 1 / a 1 * a 0
        rw [div_mul_eq_mul_div, eq_div_iff a1]
        linear_combination (-1 : F) * h2
      · show b 1 = b 1 / a 1 * a 1
        rw [div_mul_eq_mul_div, eq_div_iff a1]
      · show b 2 = b 1 / a 1 * a 2
        rw [div_mul_eq_mul_div, eq_div_iff a1]
        linear_combination h0
  · refine ⟨b 0 / a 0, ?_⟩
    funext i
    fin_cases i
    · show b 0 = b 0 / a 0 * a 0
      rw [div_mul_eq_mul_div, eq_div_iff a0]
    · show b 1 = b 0 / a 0 * a 1
      rw [div_mul_eq_mul_div, eq_div_iff a0]
      linear_combination h2
    · show b 2 = b 0 / a 0 * a 2
      rw [div_mul_eq_mul_div, eq_div_iff a0]
      linear_combination (-1 : F) * h1

lemma line_prop {F : Type} [Field F] {p p' l l' : Fin 3 → F} (hp : p ≠ 0)
    (hpp : ∀ c : F, p' ≠ c • p) (hl : l ≠ 0)
    (h1 : p ⬝ᵥ l = 0) (h2 : p' ⬝ᵥ l = 0) (h3 : p ⬝ᵥ l' = 0) (h4 : p' ⬝ᵥ l' = 0) :
    ∃ c : F, l' = c • l := by
  rcases Configuration.ofField.crossProduct_eq_zero_of_dotProduct_eq_zero h1 h2 h3 h4 with h | h
  · obtain ⟨c, hc⟩ := prop_of_cross hp h
    exact absurd hc (hpp c)
  · exact prop_of_cross hl h

noncomputable def lin {F : Type} [Field F] (v : Fin 3 → F) : MvPolynomial (Fin 3) F :=
  ∑ t : Fin 3, C (v t) * X t

lemma eval_lin {F : Type} [Field F] (v w : Fin 3 → F) :
    eval w (lin v) = ∑ t : Fin 3, v t * w t := by
  simp [lin]

lemma lin_hom {F : Type} [Field F] (v : Fin 3 → F) : (lin v).IsHomogeneous 1 := by
  unfold lin
  apply IsHomogeneous.sum
  intro t _
  exact isHomogeneous_C_mul_X (v t) t

lemma finrank_hom (F : Type) [Field F] (b : ℕ) :
    Module.finrank F (homogeneousSubmodule (Fin 3) F b) = (b + 2).choose 2 := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have hs : {d : Fin 3 →₀ ℕ | d.degree = b} =
      (((Finset.univ : Finset (Fin 3)).finsuppAntidiag b : Finset (Fin 3 →₀ ℕ)) :
        Set (Fin 3 →₀ ℕ)) := by
    ext d
    simp [Finsupp.degree_eq_sum]
  rw [hs, LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp _),
    Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show 3 + b - 1 = b + 2 by omega]
  exact Nat.choose_symm_add

lemma part1 : ∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2) := by
  intro F _ n k b pt l y g hpt hpp hl hll hy hoff hsafe htwo
  classical
  have meet : ∀ i j : Fin k, i ≠ j → ∃ q ∈ y i, ∑ t : Fin 3, pt q t * l j t = 0 := by
    intro i j hij
    obtain ⟨p, p', hne, hp, hp', hg, hg'⟩ := htwo i
    by_contra hno
    push Not at hno
    obtain ⟨q, hq, hql⟩ := hsafe j _ hg
    obtain ⟨q', hq', hql'⟩ := hsafe j _ hg'
    simp only [decide_eq_true_eq] at hq hq'
    have eq1 : q = p := by
      rcases hq with h | h
      · exact absurd hql (hno q h)
      · exact h
    have eq2 : q' = p' := by
      rcases hq' with h | h
      · exact absurd hql' (hno q' h)
      · exact h
    subst eq1 eq2
    obtain ⟨c, hc⟩ := line_prop (hpt q) (hpp q q' hne) (hl i) hp hp' hql hql'
    exact hll i j hij c hc
  have hcoord : ∀ i : Fin k, ∃ t : Fin 3, l i t ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact hl i (funext h)
  choose tc htc using hcoord
  let f : Fin k → MvPolynomial (Fin 3) F := fun i =>
    (∏ q ∈ y i, lin (pt q)) * X (tc i) ^ (b - (y i).card)
  have fhom : ∀ i, (f i).IsHomogeneous b := by
    intro i
    have h1 : (∏ q ∈ y i, lin (pt q)).IsHomogeneous (∑ q ∈ y i, 1) :=
      IsHomogeneous.prod _ _ _ (fun q _ => lin_hom (pt q))
    have h2 := h1.mul (isHomogeneous_X_pow (R := F) (tc i) (b - (y i).card))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h2
    have : (y i).card + (b - (y i).card) = b := by have := hy i; omega
    rw [this] at h2
    exact h2
  have feval : ∀ i j, eval (l j) (f i) =
      (∏ q ∈ y i, ∑ t : Fin 3, pt q t * l j t) * l j (tc i) ^ (b - (y i).card) := by
    intro i j
    simp [f, eval_lin]
  have fzero : ∀ i j, i ≠ j → eval (l j) (f i) = 0 := by
    intro i j hij
    rw [feval]
    obtain ⟨q, hq, hq0⟩ := meet i j hij
    rw [Finset.prod_eq_zero hq hq0, zero_mul]
  have fne : ∀ i, eval (l i) (f i) ≠ 0 := by
    intro i
    rw [feval]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun q hq => hoff i q hq)
    · exact pow_ne_zero _ (htc i)
  let f' : Fin k → homogeneousSubmodule (Fin 3) F b := fun i => ⟨f i, fhom i⟩
  have hli : LinearIndependent F f' := by
    apply LinearIndependent.of_comp (homogeneousSubmodule (Fin 3) F b).subtype
    rw [linearIndependent_iff']
    intro s c hs j hj
    have := congrArg (eval (l j)) hs
    simp only [Function.comp_apply, Submodule.subtype_apply, map_sum, smul_eq_C_mul,
      map_mul, eval_C, map_zero] at this
    rw [Finset.sum_eq_single j] at this
    · exact (mul_eq_zero.mp this).resolve_right (fne j)
    · intro i _ hij
      simp [f', fzero i j hij]
    · intro h
      exact absurd hj h
  have : Module.Finite F (homogeneousSubmodule (Fin 3) F b) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 3) F b)
  have hk := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, finrank_hom] at hk
  have key : (b + 2) * (b + 1).choose 1 = (b + 2).choose 2 * 2 := Nat.add_one_mul_choose_eq (b + 1) 1
  simp only [Nat.choose_one_right] at key
  nlinarith

def A {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) : Option (Fin m) → Fin 3 → F
  | none => ![0, 0, 1]
  | some i => ![1, τ i, τ i ^ 2]

def lf {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) : Option (Fin m) → Option (Fin m) → Fin 3 → F
  | none, none => ![0, 0, 1]
  | none, some t => ![τ t, -1, 0]
  | some t, none => ![τ t, -1, 0]
  | some t, some s => ![τ t * τ s, -(τ t + τ s), 1]

lemma on_line {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) (hτ : Function.Injective τ)
    (a a' c : Option (Fin m)) (h : a ≠ a') :
    (∑ t : Fin 3, A τ c t * lf τ a a' t = 0) ↔ (c = a ∨ c = a') := by
  rcases c with _ | u <;> rcases a with _ | t <;> rcases a' with _ | s <;>
    simp [A, lf, Fin.sum_univ_three] at h ⊢
  · rw [← hτ.eq_iff]
    constructor <;> intro h' <;> linear_combination (-1 : F) * h'
  · rw [← hτ.eq_iff]
    constructor <;> intro h' <;> linear_combination (-1 : F) * h'
  · rw [← hτ.eq_iff, ← hτ.eq_iff]
    have e : τ t * τ s + τ u * (-τ s + -τ t) + τ u ^ 2 = (τ u - τ t) * (τ u - τ s) := by ring
    rw [e, mul_eq_zero, sub_eq_zero, sub_eq_zero]

lemma lf_symm {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) (a a' : Option (Fin m)) :
    lf τ a a' = lf τ a' a := by
  rcases a with _ | t <;> rcases a' with _ | s <;> funext i <;> fin_cases i <;>
    simp [lf] <;> ring

lemma lf_ne_zero {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) (a a' : Option (Fin m)) :
    lf τ a a' ≠ 0 := by
  intro h
  rcases a with _ | t <;> rcases a' with _ | s
  · have := congrFun h 2
    simp [lf] at this
  · have := congrFun h 1
    simp [lf] at this
  · have := congrFun h 1
    simp [lf] at this
  · have := congrFun h 2
    simp [lf] at this

def Lz {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) : Sym2 (Option (Fin m)) → Fin 3 → F :=
  Sym2.lift ⟨lf τ, lf_symm τ⟩

lemma sym2_rep {α : Type} (z : Sym2 α) (hz : ¬ z.IsDiag) :
    ∃ a a', a ≠ a' ∧ z = s(a, a') := by
  revert hz
  refine Sym2.inductionOn z ?_
  intro a a' hz
  exact ⟨a, a', by simpa using hz, rfl⟩

lemma on_line_z {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) (hτ : Function.Injective τ)
    (z : Sym2 (Option (Fin m))) (hz : ¬ z.IsDiag) (c : Option (Fin m)) :
    (∑ t : Fin 3, A τ c t * Lz τ z t = 0) ↔ c ∈ z := by
  obtain ⟨a, a', h, rfl⟩ := sym2_rep z hz
  rw [Sym2.mem_iff]
  exact on_line τ hτ a a' c h

lemma Lz_mk {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) (a a' : Option (Fin m)) :
    Lz τ s(a, a') = lf τ a a' := rfl

def Norm {F : Type} [Field F] (v : Fin 3 → F) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

lemma norm_ne_zero {F : Type} [Field F] {v : Fin 3 → F} (h : Norm v) : v ≠ 0 := by
  rintro rfl
  simp [Norm] at h

lemma norm_unique {F : Type} [Field F] {v w : Fin 3 → F} (hv : Norm v) (hw : Norm w) (c : F)
    (h : w = c • v) : w = v := by
  have e : ∀ i, w i = c * v i := fun i => by rw [h]; rfl
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have hc : c = 1 := by
    unfold Norm at hv hw
    rcases hv with h0 | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩ <;>
      rcases hw with k0 | ⟨k0, k1⟩ | ⟨k0, k1, k2⟩ <;> simp_all
  funext i
  rw [e i, hc, one_mul]

lemma norm_exists {F : Type} [Field F] {v : Fin 3 → F} (hv : v ≠ 0) :
    ∃ (w : Fin 3 → F) (c : F), Norm w ∧ v = c • w := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨(v 2)⁻¹ • v, v 2, Or.inr (Or.inr ⟨?_, ?_, ?_⟩), ?_⟩
      · simp [h0]
      · simp [h1]
      · simp [h2]
      · rw [smul_smul, mul_inv_cancel₀ h2, one_smul]
    · refine ⟨(v 1)⁻¹ • v, v 1, Or.inr (Or.inl ⟨?_, ?_⟩), ?_⟩
      · simp [h0]
      · simp [h1]
      · rw [smul_smul, mul_inv_cancel₀ h1, one_smul]
  · refine ⟨(v 0)⁻¹ • v, v 0, Or.inl ?_, ?_⟩
    · simp [h0]
    · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

lemma A_norm {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) (a : Option (Fin m)) :
    Norm (A τ a) := by
  rcases a with _ | t <;> simp [Norm, A]

lemma A_inj {F : Type} [Field F] {m : ℕ} (τ : Fin m → F) (hτ : Function.Injective τ) :
    Function.Injective (A τ) := by
  intro a a' h
  rcases a with _ | t <;> rcases a' with _ | s
  · rfl
  · have := congrFun h 0
    simp [A] at this
  · have := congrFun h 0
    simp [A] at this
  · have := congrFun h 1
    simp [A] at this
    rw [hτ this]

lemma part2 : ∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2) := by
  intro F _ _ b hb
  classical
  let τ : Fin (b + 1) → F := fun i => (Fintype.equivFin F).symm (Fin.castLE hb i)
  have hτ : Function.Injective τ := fun i j h =>
    Fin.castLE_injective hb ((Fintype.equivFin F).symm.injective h)
  let S : Finset (Fin 3 → F) := Finset.univ.filter Norm
  let n := S.card
  let eP : Fin n ≃ S := S.equivFin.symm
  let pt : Fin n → Fin 3 → F := fun p => (eP p).1
  have ptN : ∀ p, Norm (pt p) := fun p => (Finset.mem_filter.mp (eP p).2).2
  let Lt := {z : Sym2 (Option (Fin (b + 1))) // ¬ z.IsDiag}
  let k := Fintype.card Lt
  let eL : Fin k ≃ Lt := (Fintype.equivFin Lt).symm
  let l : Fin k → Fin 3 → F := fun i => Lz τ (eL i).1
  have AS : ∀ a, A τ a ∈ S := fun a => Finset.mem_filter.mpr ⟨Finset.mem_univ _, A_norm τ a⟩
  let idx : Option (Fin (b + 1)) → Fin n := fun a => eP.symm ⟨A τ a, AS a⟩
  have pt_idx : ∀ a, pt (idx a) = A τ a := fun a => by simp [pt, idx]
  have idx_inj : Function.Injective idx := by
    intro a a' h
    apply A_inj τ hτ
    rw [← pt_idx a, ← pt_idx a', h]
  let y : Fin k → Finset (Fin n) := fun i =>
    (Finset.univ.filter (fun a => a ∉ (eL i).1)).image idx
  let g : (Fin n → Bool) → Bool := fun x =>
    decide (b + 1 ≤ (Finset.univ.filter (fun a => x (idx a) = true)).card)
  have pair : ∀ i : Fin k, ∃ a a', a ≠ a' ∧ (eL i).1 = s(a, a') := fun i => sym2_rep _ (eL i).2
  have card_out : ∀ i : Fin k, (Finset.univ.filter (fun c => c ∉ (eL i).1)).card = b := by
    intro i
    obtain ⟨a, a', hne, he⟩ := pair i
    have hin : (Finset.univ.filter (fun c => c ∈ (eL i).1)) = {a, a'} := by
      ext c
      simp [he, Sym2.mem_iff]
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Option (Fin (b + 1))))) (fun c => c ∈ (eL i).1)
    rw [hin, Finset.card_pair hne, Finset.card_univ, Fintype.card_option, Fintype.card_fin] at h1
    omega
  have mem_y : ∀ i c, idx c ∈ y i ↔ c ∉ (eL i).1 := by
    intro i c
    simp only [y, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, he⟩
      rwa [← idx_inj he]
    · intro h
      exact ⟨c, h, rfl⟩
  have y_sub : ∀ i p, p ∈ y i → ∃ c, p = idx c ∧ c ∉ (eL i).1 := by
    intro i p hp
    simp only [y, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    exact ⟨c, rfl, hc⟩
  have online : ∀ i c, (∑ t : Fin 3, pt (idx c) t * l i t = 0) ↔ c ∈ (eL i).1 := by
    intro i c
    rw [pt_idx]
    exact on_line_z τ hτ _ (eL i).2 c
  refine ⟨n, k, pt, l, y, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact norm_ne_zero (ptN p)
  · intro p p' hne c hc
    apply hne
    have := norm_unique (ptN p) (ptN p') c hc
    exact eP.injective (Subtype.ext this.symm)
  · intro v hv
    obtain ⟨w, c, hw, rfl⟩ := norm_exists hv
    have wS : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
    refine ⟨eP.symm ⟨w, wS⟩, c, ?_⟩
    simp [pt]
  · intro i
    obtain ⟨a, a', _, he⟩ := pair i
    show Lz τ (eL i).1 ≠ 0
    rw [he, Lz_mk]
    exact lf_ne_zero τ a a'
  · intro i j hij c hc
    obtain ⟨a, a', hne, he⟩ := pair i
    obtain ⟨e1, e2, hne', he'⟩ := pair j
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply lf_ne_zero τ e1 e2
      rw [← Lz_mk, ← he']
      have : l j = 0 := by rw [hc, zero_smul]
      exact this
    have sub : ∀ e, e ∈ (eL j).1 → e ∈ (eL i).1 := by
      intro e he_mem
      rw [← online i e]
      have h2 := (online j e).mpr he_mem
      rw [hc] at h2
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      have h3 : ∑ t : Fin 3, pt (idx e) t * (c * l i t) =
          c * ∑ t : Fin 3, pt (idx e) t * l i t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        ring
      rw [h3] at h2
      exact (mul_eq_zero.mp h2).resolve_left hc0
    have m1 := sub e1 (by rw [he']; exact Sym2.mem_mk_left _ _)
    have m2 := sub e2 (by rw [he']; exact Sym2.mem_mk_right _ _)
    rw [he, Sym2.mem_iff] at m1 m2
    apply hij
    apply eL.injective
    apply Subtype.ext
    rw [he, he']
    rcases m1 with rfl | rfl <;> rcases m2 with rfl | rfl
    all_goals first
      | rfl
      | exact Sym2.eq_swap
      | exact absurd rfl hne'
  · intro i
    calc (y i).card ≤ (Finset.univ.filter (fun a => a ∉ (eL i).1)).card := Finset.card_image_le
      _ = b := card_out i
  · intro i p hp
    obtain ⟨c, rfl, hc⟩ := y_sub i p hp
    rw [Ne, online]
    exact hc
  · intro x x' hxx' hg
    simp only [g, decide_eq_true_eq] at hg ⊢
    refine le_trans hg (Finset.card_le_card ?_)
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact hxx' _ ha
  · intro i x hg
    simp only [g, decide_eq_true_eq] at hg
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ.filter (fun c => x (idx c) = true)) ⊆
        Finset.univ.filter (fun c => c ∉ (eL i).1) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      intro hmem
      exact hno _ hc ((online i c).mpr hmem)
    have := Finset.card_le_card hsub
    rw [card_out] at this
    omega
  · intro i
    obtain ⟨a, a', hne, he⟩ := pair i
    have ma : a ∈ (eL i).1 := by rw [he]; exact Sym2.mem_mk_left _ _
    have ma' : a' ∈ (eL i).1 := by rw [he]; exact Sym2.mem_mk_right _ _
    have gval : ∀ e, e ∈ (eL i).1 → g (fun v => decide (v ∈ y i ∨ v = idx e)) = true := by
      intro e he_mem
      simp only [g, decide_eq_true_eq]
      have hset : (Finset.univ.filter (fun c => idx c ∈ y i ∨ idx c = idx e)) =
          insert e (Finset.univ.filter (fun c => c ∉ (eL i).1)) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, mem_y, idx_inj.eq_iff]
        tauto
      rw [hset, Finset.card_insert_of_notMem, card_out]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact he_mem
    exact ⟨idx a, idx a', fun h => hne (idx_inj h), (online i a).mpr ma, (online i a').mpr ma',
      gval a ma, gval a' ma'⟩
  · show 2 * Fintype.card Lt = (b + 1) * (b + 2)
    rw [Sym2.card_subtype_not_diag, Fintype.card_option, Fintype.card_fin]
    have key : (b + 2) * (b + 1).choose 1 = (b + 2).choose 2 * 2 :=
      Nat.add_one_mul_choose_eq (b + 1) 1
    simp only [Nat.choose_one_right] at key
    nlinarith

end PEqualNP.Outside.L_meta_989

theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) := by
  exact ⟨PEqualNP.Outside.L_meta_989.part1, PEqualNP.Outside.L_meta_989.part2⟩
