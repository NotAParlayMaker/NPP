import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_989_aux
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

end PEqualNP.Outside.L_meta_989_aux

namespace PEqualNP.Outside.L_meta_989_aux

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

end PEqualNP.Outside.L_meta_989_aux

namespace PEqualNP.Outside.L_meta_989_aux
variable {ι F : Type*} [Field F]

def arcVec (t : ι → F) : Option ι → Fin 3 → F
  | none => ![0,0,1]
  | some a => ![1,t a,(t a)^2]

def secVec (t : ι → F) : Option ι → Option ι → Fin 3 → F
  | some a, some b => ![t a * t b,-(t a+t b),1]
  | some a, none | none, some a => ![-t a,1,0]
  | none, none => ![1,0,0]

theorem arc_nonzero (t : ι → F) (a : Option ι) : arcVec t a ≠ 0 := by
  intro he
  cases a with
  | none => simpa [arcVec] using congrFun he 2
  | some a => simpa [arcVec] using congrFun he 0

theorem sec_nonzero (t : ι → F) (a b : Option ι) : secVec t a b ≠ 0 := by
  intro he
  cases a <;> cases b
  · simpa [secVec] using congrFun he 0
  · simpa [secVec] using congrFun he 1
  · simpa [secVec] using congrFun he 1
  · simpa [secVec] using congrFun he 2

theorem arc_not_smul {t : ι → F} (ht : Function.Injective t) {a b : Option ι} (hab : a ≠ b)
    (c : F) : arcVec t b ≠ c • arcVec t a := by
  intro he
  cases a with
  | none =>
    cases b with
    | none => exact hab rfl
    | some b => simpa [arcVec,Pi.smul_apply] using congrFun he 0
  | some a =>
    cases b with
    | none =>
      have h₀ := congrFun he 0
      have h₂ := congrFun he 2
      simp [arcVec,Pi.smul_apply] at h₀ h₂
      rw [← h₀] at h₂; simp at h₂
    | some b =>
      have h₀ := congrFun he 0
      have h₁ := congrFun he 1
      simp [arcVec,Pi.smul_apply] at h₀ h₁
      apply hab
      exact congrArg some (ht (by simpa [←h₀] using h₁.symm))

theorem sec_zero_iff {t : ι → F} (ht : Function.Injective t) {a b : Option ι}
    (hab : a ≠ b) (z : Option ι) :
    (∑ k, arcVec t z k * secVec t a b k) = 0 ↔ z=a ∨ z=b := by
  cases a <;> cases b <;> cases z <;>
    simp_all [arcVec,secVec,Fin.sum_univ_three]
  all_goals first
    | rw [show ∀ x y : F, -y + x = 0 ↔ x = y by intro x y; constructor <;> intro h <;> linear_combination h]
      exact ht.eq_iff
    | rename_i a b z
      convert (mul_eq_zero (a := t z - t a) (b := t z - t b)) using 1 <;>
        first | ring_nf | simp [sub_eq_zero,ht.eq_iff]
end PEqualNP.Outside.L_meta_989_aux
namespace PEqualNP.Outside.L_meta_989_aux
theorem all_points {F A : Type} [Field F] [Fintype F] (v : A → Fin 3 → F)
    (nz : ∀ a, v a ≠ 0) (sep : ∀ a a', a ≠ a' → ∀ c : F, v a' ≠ c • v a) :
    ∃ (n : ℕ) (p : Fin n → Fin 3 → F) (embed : A ↪ Fin n),
      (∀ i, p i ≠ 0) ∧ (∀ i j, i ≠ j → ∀ c : F, p j ≠ c • p i) ∧
      (∀ w : Fin 3 → F, w ≠ 0 → ∃ i, ∃ c : F, w = c • p i) ∧
      (∀ a, ∀ l : Fin 3 → F, (∑ t, p (embed a) t * l t) = 0 ↔ (∑ t, v a t * l t) = 0) := by
  classical
  let P := Projectivization F (Fin 3 → F)
  letI : Fintype P := Fintype.ofFinite P
  let e := Fintype.equivFin P
  let f (a : A) : P := Projectivization.mk F (v a) (nz a)
  have hf : Function.Injective f := by
    intro a b hab
    by_contra hne
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' F (v b) (v a) (nz b) (nz a)).mp hab.symm
    exact sep a b hne c hc.symm
  let p := fun i => (e.symm i).rep
  refine ⟨Fintype.card P,p,⟨e ∘ f,e.injective.comp hf⟩,fun i => (e.symm i).rep_ne_zero,?_,?_,?_⟩
  · intro i j h c hc
    apply h
    apply e.symm.injective
    rw [← Projectivization.mk_rep (e.symm i),← Projectivization.mk_rep (e.symm j)]
    exact ((Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨c,hc.symm⟩).symm
  · intro w hw
    let q := Projectivization.mk F w hw
    refine ⟨e q,?_⟩
    change ∃ c : F, w = c • (e.symm (e q)).rep
    rw [e.symm_apply_apply]
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' F w q.rep hw q.rep_ne_zero).mp q.mk_rep.symm
    exact ⟨c,hc.symm⟩
  · intro a l
    change (∑ t, (e.symm (e (f a))).rep t * l t) = 0 ↔ _
    rw [e.symm_apply_apply]
    obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep F (v a) (nz a)
    change _ = (f a).rep at hc
    rw [← hc]
    simp [Units.smul_def,Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
end PEqualNP.Outside.L_meta_989_aux
namespace PEqualNP.Outside.L_meta_989_aux
theorem sharp : ∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2) := by
  classical
  intro F _ _ b hF
  let A := Option (Fin (b+1))
  let t (i : Fin (b+1)) := (Fintype.equivFin F).symm (Fin.castLE hF i)
  have ht : Function.Injective t := (Fintype.equivFin F).symm.injective.comp
    (fun i j h => Fin.ext (congrArg (fun z : Fin (Fintype.card F) => z.val) h))
  obtain ⟨n,pt,embed,nz,sep,complete,he⟩ := all_points (arcVec t) (arc_nonzero t)
    (fun _ _ h => arc_not_smul ht h)
  let pairs := (Finset.univ : Finset A).powersetCard 2
  let k := Fintype.card ↥pairs
  let e : Fin k ≃ ↥pairs := (Fintype.equivFin ↥pairs).symm
  let S (i : Fin k) : Finset A := (e i).val
  have scard (i : Fin k) : (S i).card = 2 := (Finset.mem_powersetCard.mp (e i).property).2
  have endpoints (i : Fin k) : ∃ a z : A, a ≠ z ∧ S i = {a,z} := Finset.card_eq_two.mp (scard i)
  choose a z distinct hS using endpoints
  let l (i : Fin k) := secVec t (a i) (z i)
  have incident (i : Fin k) (v : A) : (∑ j, pt (embed v) j * l i j) = 0 ↔ v ∈ S i := by
    rw [he v (l i),hS]
    simpa [l] using sec_zero_iff ht (distinct i) v
  let y (i : Fin k) := (Finset.univ \ S i).map embed
  let g (x : Fin n → Bool) := decide (∃ w : A, ∀ v : A, v ≠ w → x (embed v) = true)
  have cardA : Fintype.card A = b+2 := by simp [A]
  refine ⟨n,k,pt,l,y,g,nz,sep,complete,fun i => sec_nonzero t _ _,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i j hij c hline
    have sub : S i ⊆ S j := by
      intro v hv
      apply (incident j v).mp
      rw [hline]
      simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm (pt (embed v) _ ) c,
        ←Finset.mul_sum,(incident i v).mpr hv,mul_zero]
    have hsets := Finset.eq_of_subset_of_card_le sub (by rw [scard,scard])
    exact hij (e.injective (Subtype.ext hsets))
  · intro i
    simp [y,Finset.card_sdiff_of_subset,scard]
  · intro i p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hp
    exact fun h => (Finset.mem_sdiff.mp hv).2 ((incident i v).mp h)
  · intro x x' hxx hg
    obtain ⟨w,hw⟩ := of_decide_eq_true hg
    exact decide_eq_true ⟨w,fun v hv => hxx _ (hw v hv)⟩
  · intro i x hg
    obtain ⟨w,hw⟩ := of_decide_eq_true hg
    by_cases h : a i = w
    · refine ⟨embed (z i),hw _ (by rw [←h]; exact (distinct i).symm),?_⟩
      exact (incident i _).mpr (by simp [hS])
    · exact ⟨embed (a i),hw _ h,(incident i _).mpr (by simp [hS])⟩
  · intro i
    have fire (v w : A) (hs : S i = {v,w}) :
        g (fun p => decide (p ∈ y i ∨ p=embed v)) = true := by
      apply decide_eq_true
      refine ⟨w,fun u hu => decide_eq_true ?_⟩
      by_cases huv : u=v
      · exact Or.inr (congrArg embed huv)
      · refine Or.inl (Finset.mem_map.mpr ⟨u,?_,rfl⟩)
        simp [hs,huv,hu]
    refine ⟨embed (a i),embed (z i),fun h => distinct i (embed.injective h),
      (incident i _).mpr (by simp [hS]),(incident i _).mpr (by simp [hS]),
      fire _ _ (hS i),fire _ _ (by rw [hS,Finset.pair_comm])⟩
  · change 2 * Fintype.card ↥pairs = _
    rw [Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ,cardA]
    simpa only [Nat.choose_one_right,Nat.mul_comm] using (Nat.add_one_mul_choose_eq (b+1) 1).symm
end PEqualNP.Outside.L_meta_989_aux
open PEqualNP.Outside.L_meta_989_aux
theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) := by
  constructor
  · intro F _ n k b pt l y g hp hpn hl hln hy hdiag hsound htrigger
    obtain ⟨A,h⟩ := forms pt l y g hp hpn hl hln hy hdiag hsound htrigger
    apply dim_bound l A (fun i => (h i i).2 rfl)
    intro i j hij
    exact not_ne_iff.mp fun hn => hij ((h i j).1 hn)
  · exact sharp
