import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_992_aux
open Matrix
open scoped Matrix

private theorem common_two {F : Type} [Field F] (P Q U V : Fin 3 → F)
    (hn : P ≠ 0) (hu : U ≠ 0) (hp : ∀ c : F, Q ≠ c • P)
    (hPU : P ⬝ᵥ U = 0) (hQU : Q ⬝ᵥ U = 0)
    (hPV : P ⬝ᵥ V = 0) (hQV : Q ⬝ᵥ V = 0) : ∃ c : F, V = c • U := by
  have hc : crossProduct P Q ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr
    ((LinearIndependent.pair_iff' hn).mpr (fun c => (hp c).symm))
  have multiple (W : Fin 3 → F) (hP : P ⬝ᵥ W = 0) (hQ : Q ⬝ᵥ W = 0) :
      ∃ c : F, W = c • crossProduct P Q := by
    by_contra! h
    have hi := crossProduct_ne_zero_iff_linearIndependent.mpr ((LinearIndependent.pair_iff' hc).mpr
      (fun c => (h c).symm))
    apply hi
    rw [cross_cross_eq_smul_sub_smul,hP,hQ,zero_smul,zero_smul,sub_self]
  obtain ⟨a,ha⟩ := multiple U hPU hQU
  obtain ⟨b,hb⟩ := multiple V hPV hQV
  have an : a ≠ 0 := by rintro rfl; simp_all
  exact ⟨b/a, by rw [ha,hb,smul_smul,div_mul_cancel₀ _ an]⟩

theorem forms {F : Type} [Field F] {n k b : ℕ}
    (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F)
    (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool)
    (hp : ∀ p, pt p ≠ 0) (hpn : ∀ p p', p ≠ p' → ∀ c : F, pt p' ≠ c • pt p)
    (hl : ∀ i, l i ≠ 0) (hln : ∀ i j, i ≠ j → ∀ c : F, l j ≠ c • l i)
    (hy : ∀ i, (y i).card ≤ b)
    (hdiag : ∀ i, ∀ p ∈ y i, ∑ t, pt p t * l i t ≠ 0)
    (hsound : ∀ i x, g x = true → ∃ p, x p = true ∧ ∑ t, pt p t * l i t = 0)
    (htrigger : ∀ i, ∃ p p', p ≠ p' ∧ ∑ t, pt p t * l i t = 0 ∧
      ∑ t, pt p' t * l i t = 0 ∧ g (fun v => decide (v ∈ y i ∨ v=p)) = true ∧
      g (fun v => decide (v ∈ y i ∨ v=p')) = true) :
    ∃ A : Fin k → Fin b → Fin 3 → F, ∀ i j, (∏ r, ∑ t, A i r t * l j t) ≠ 0 ↔ i = j := by
  classical
  have hit (i j : Fin k) (h : i ≠ j) : ∃ p ∈ y i, ∑ t, pt p t * l j t = 0 := by
    by_contra! no
    obtain ⟨p,q,pq,pi,qi,hp',hq'⟩ := htrigger i
    have force (u : Fin n) (hgu : g (fun v => decide (v ∈ y i ∨ v=u)) = true) :
        ∑ t, pt u t * l j t = 0 := by
      obtain ⟨r,hr,hrj⟩ := hsound j _ hgu
      rcases of_decide_eq_true hr with hr|rfl
      · exact (no r hr hrj).elim
      · exact hrj
    obtain ⟨c,hc⟩ := common_two _ _ _ _ (hp p) (hl i) (hpn p q pq) pi qi (force p hp') (force q hq')
    exact hln i j h c hc
  have pivot (i : Fin k) : ∃ z, l i z ≠ 0 := by
    by_contra! h; exact hl i (funext h)
  choose z hz using pivot
  let ix (i : Fin k) : Fin (y i).card ≃ (y i) := (y i).equivFin.symm
  let A (i : Fin k) (r : Fin b) (t : Fin 3) : F :=
    if h : r.val < (y i).card then pt (ix i ⟨r.val,h⟩).val t else if t=z i then 1 else 0
  refine ⟨A,fun i j => ?_⟩
  constructor
  · intro hn
    by_contra ne
    obtain ⟨p,hp,hzero⟩ := hit i j ne
    let rr := (ix i).symm ⟨p,hp⟩
    let r : Fin b := ⟨rr.val,lt_of_lt_of_le rr.isLt (hy i)⟩
    have eqp : (ix i rr).val = p := congrArg Subtype.val ((ix i).apply_symm_apply ⟨p,hp⟩)
    have eqr : (⟨r.val,rr.isLt⟩ : Fin (y i).card) = rr := rfl
    have hfac : ∑ t, A i r t * l j t = 0 := by
      simpa only [A,dite_eq_left (show r.val < (y i).card from rr.isLt),eqr,eqp] using hzero
    exact hn (Finset.prod_eq_zero (Finset.mem_univ r) hfac)
  · rintro rfl
    apply Finset.prod_ne_zero_iff.mpr
    intro r _
    by_cases hr : r.val < (y i).card
    · simp only [A,dite_eq_left hr]
      exact hdiag _ _ (ix i ⟨_,hr⟩).property
    · simpa [A,hr,ite_mul] using hz i

end PEqualNP.Outside.L_meta_992_aux

namespace PEqualNP.Outside.L_meta_992_aux

theorem dim_bound {F : Type} [Field F] {k b : ℕ}
    (l : Fin k → Fin 3 → F) (R : Fin k → Fin b → Fin 3 → F)
    (diag : ∀ i, (∏ a, ∑ t, R i a t * l i t) ≠ 0)
    (off : ∀ i j, i ≠ j → (∏ a, ∑ t, R i a t * l j t) = 0) :
    2*k ≤ (b+1)*(b+2) := by
  classical
  let mon (s : Sym (Fin 3) b) (j : Fin k) : F := (s.val.map (l j)).prod
  let V := Submodule.span F (Set.range mon)
  let poly (i j : Fin k) : F := ∏ a, ∑ t, R i a t * l j t
  have ins (i : Fin k) : poly i ∈ V := by
    let idx (f : Fin b → Fin 3) : Sym (Fin 3) b := ⟨Finset.univ.val.map f, by simp⟩
    have expand : poly i = ∑ f : Fin b → Fin 3, (∏ a, R i a (f a)) • mon (idx f) := by
      funext j
      simp only [poly, Fintype.prod_sum, Finset.sum_apply, Pi.smul_apply,smul_eq_mul]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.prod_mul_distrib]
      simp [mon,idx,Finset.prod,Function.comp_def]
    rw [expand]
    exact Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩)
  have whole : V = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun F (Fin k)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have e : (Pi.basisFun F (Fin k)) i = (poly i i)⁻¹ • poly i := by
      ext j
      by_cases hi : i=j
      · subst j; simp [Pi.basisFun_apply, diag, poly]
      · simp [Pi.basisFun_apply, Pi.single_eq_of_ne (Ne.symm hi), show poly i j=0 from off i j hi]
    rw [e]
    exact V.smul_mem _ (ins i)
  have cardBound := finrank_range_le_card (R := F) mon
  change Module.finrank F V ≤ _ at cardBound
  rw [whole,finrank_top,Module.finrank_pi, Fintype.card_fin,Sym.card_sym_eq_choose,Fintype.card_fin] at cardBound
  rw [show 3+b-1 = b+2 by omega, Nat.choose_symm_add, Nat.choose_two_right] at cardBound
  have eq : b+2-1 = b+1 := by omega
  rw [eq,Nat.mul_comm] at cardBound
  omega

end PEqualNP.Outside.L_meta_992_aux
theorem PEqualNP.Outside.L_meta_992 : ¬ (∃ (F : Type) (_ : Field F) (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ (b + 1) * (b + 2) < 2 * k) := by
  rintro ⟨F,hF,n,k,b,pt,l,y,g,hp,hpn,hl,hln,hy,hdiag,hsound,htrigger,strict⟩
  letI : Field F := hF
  obtain ⟨A,h⟩ := PEqualNP.Outside.L_meta_992_aux.forms pt l y g hp hpn hl hln hy hdiag hsound htrigger
  apply (Nat.not_lt_of_ge (PEqualNP.Outside.L_meta_992_aux.dim_bound l A (fun i => (h i i).2 rfl) ?_)) strict
  intro i j hij
  exact not_ne_iff.mp fun hn => hij ((h i j).1 hn)
