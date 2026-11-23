import PEqualNP.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace PEqualNP.Outside

private def dot3 (u v : Fin 3 → ℂ) : ℂ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

private def sum0H : Submodule ℂ (Fin 3 → ℂ) :=
  LinearMap.ker
    ({ toFun := fun v : Fin 3 → ℂ => v 0 + v 1 + v 2
       map_add' := fun a b => by simp only [Pi.add_apply]; ring
       map_smul' := fun c a => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring } :
      (Fin 3 → ℂ) →ₗ[ℂ] ℂ)

private lemma finrank_sum0H : Module.finrank ℂ sum0H = 2 := by
  let f : (Fin 2 → ℂ) →ₗ[ℂ] sum0H :=
    { toFun := fun v =>
        ⟨![v 0, v 1, -(v 0 + v 1)], by
          change v 0 + v 1 + -(v 0 + v 1) = 0
          ring⟩
      map_add' := fun a b => by
        apply Subtype.ext
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := fun c a => by
        apply Subtype.ext
        funext i
        fin_cases i <;> simp <;> ring }
  have hbij : Function.Bijective f := by
    constructor
    · intro a b h
      have hval := congrArg Subtype.val h
      funext i
      fin_cases i
      · exact congrFun hval 0
      · exact congrFun hval 1
    · rintro ⟨v, hv⟩
      refine ⟨![v 0, v 1], ?_⟩
      apply Subtype.ext
      funext i
      fin_cases i
      · rfl
      · rfl
      · change -(v 0 + v 1) = v 2
        change v 0 + v 1 + v 2 = 0 at hv
        linear_combination -hv
  rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hbij), Module.finrank_fin_fun]

private lemma finrank_ortho_of_inj_dual {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (phi : V →ₗ[ℂ] Module.Dual ℂ V) (hphi : Function.Injective phi)
    (A B : Submodule ℂ V) (horth : ∀ a ∈ A, ∀ b ∈ B, phi b a = 0) :
    Module.finrank ℂ A + Module.finrank ℂ B ≤ Module.finrank ℂ V := by
  let resMap : V →ₗ[ℂ] Module.Dual ℂ A :=
    { toFun := fun b => (phi b).comp A.subtype
      map_add' := fun b1 b2 => by
        apply LinearMap.ext; intro a; simp
      map_smul' := fun c b => by
        apply LinearMap.ext; intro a; simp }
  have hker_le : B ≤ LinearMap.ker resMap := by
    intro b hb
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro a
    exact horth a.1 a.2 b hb
  have hphi_top : LinearMap.range phi = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hphi, Subspace.dual_finrank_eq]
  have hsurj : LinearMap.range resMap = ⊤ := by
    rw [eq_top_iff]
    intro f _
    rcases Submodule.exists_isCompl A with ⟨A', hcompl⟩
    let F : Module.Dual ℂ V := f.comp (A.projectionOnto A' hcompl)
    have hF_mem : F ∈ LinearMap.range phi := by rw [hphi_top]; trivial
    rcases hF_mem with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply LinearMap.ext
    intro a
    change phi b a.1 = f a
    rw [hb]
    change f (A.projectionOnto A' hcompl a.1) = f a
    rw [Submodule.projectionOnto_apply_left hcompl a]
  have hrn := LinearMap.finrank_range_add_finrank_ker resMap
  rw [hsurj, finrank_top, Subspace.dual_finrank_eq] at hrn
  have hBle := Submodule.finrank_mono hker_le
  omega

private lemma finrank_ortho_sum0H (A B : Submodule ℂ sum0H)
    (horth : ∀ a ∈ A, ∀ b ∈ B, dot3 a.1 b.1 = 0) :
    Module.finrank ℂ A + Module.finrank ℂ B ≤ 2 := by
  let phi : sum0H →ₗ[ℂ] Module.Dual ℂ sum0H :=
    { toFun := fun b =>
        { toFun := fun a => dot3 a.1 b.1
          map_add' := fun a1 a2 => by simp only [dot3, Submodule.coe_add, Pi.add_apply]; ring
          map_smul' := fun c a => by
            simp only [dot3, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            ring }
      map_add' := fun b1 b2 => by
        apply LinearMap.ext; intro a
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, dot3,
          Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun c b => by
        apply LinearMap.ext; intro a
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, dot3,
          Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        ring }
  have hphi_inj : Function.Injective phi := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hm1 : (![1, -1, 0] : Fin 3 → ℂ) ∈ sum0H := by change (1 : ℂ) + (-1) + 0 = 0; ring
    have hm2 : (![1, 0, -1] : Fin 3 → ℂ) ∈ sum0H := by change (1 : ℂ) + 0 + (-1) = 0; ring
    have h1 : dot3 (![1, -1, 0]) b.1 = 0 := congrArg (fun l => l ⟨![1, -1, 0], hm1⟩) hb
    have h2 : dot3 (![1, 0, -1]) b.1 = 0 := congrArg (fun l => l ⟨![1, 0, -1], hm2⟩) hb
    have h3 : b.1 0 + b.1 1 + b.1 2 = 0 := b.2
    simp only [dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 h2
    apply Subtype.ext
    funext i
    fin_cases i
    · change b.1 0 = 0; linear_combination (h1 + h2 + h3) / 3
    · change b.1 1 = 0; linear_combination (-2 * h1 + h2 + h3) / 3
    · change b.1 2 = 0; linear_combination (h1 - 2 * h2 + h3) / 3
  have hle := finrank_ortho_of_inj_dual phi hphi_inj A B horth
  rw [finrank_sum0H] at hle
  exact hle

private lemma finrank_iso_q3 (K : Submodule ℂ (Fin 3 → ℂ))
    (hK : ∀ a ∈ K, a 0 * a 1 + a 0 * a 2 + a 1 * a 2 = 0) :
    Module.finrank ℂ K ≤ 1 := by
  let phi : (Fin 3 → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin 3 → ℂ) :=
    { toFun := fun b =>
        { toFun := fun a => a 0 * (b 1 + b 2) + a 1 * (b 0 + b 2) + a 2 * (b 0 + b 1)
          map_add' := fun a1 a2 => by simp only [Pi.add_apply]; ring
          map_smul' := fun c a => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
      map_add' := fun b1 b2 => by
        apply LinearMap.ext; intro a
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply]; ring
      map_smul' := fun c b => by
        apply LinearMap.ext; intro a
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply,
          RingHom.id_apply]
        ring }
  have hphi_inj : Function.Injective phi := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have h0 : b 1 + b 2 = 0 := by
      have := congrArg (fun l => l ![1, 0, 0]) hb
      simpa [phi] using this
    have h1 : b 0 + b 2 = 0 := by
      have := congrArg (fun l => l ![0, 1, 0]) hb
      simpa [phi] using this
    have h2 : b 0 + b 1 = 0 := by
      have := congrArg (fun l => l ![0, 0, 1]) hb
      simpa [phi] using this
    funext i
    fin_cases i
    · change b 0 = 0; linear_combination (-h0 + h1 + h2) / 2
    · change b 1 = 0; linear_combination (h0 - h1 + h2) / 2
    · change b 2 = 0; linear_combination (h0 + h1 - h2) / 2
  have horth : ∀ a ∈ K, ∀ b ∈ K, phi b a = 0 := by
    intro a ha b hb
    have ha0 := hK a ha
    have hb0 := hK b hb
    have hab := hK (a + b) (K.add_mem ha hb)
    simp only [Pi.add_apply] at hab
    change a 0 * (b 1 + b 2) + a 1 * (b 0 + b 2) + a 2 * (b 0 + b 1) = 0
    linear_combination hab - ha0 - hb0
  have hle := finrank_ortho_of_inj_dual phi hphi_inj K K horth
  rw [Module.finrank_fin_fun] at hle
  omega

private lemma finrank_iso_HH (W : Submodule ℂ (sum0H × sum0H))
    (hW : ∀ p ∈ W, dot3 p.1.1 p.2.1 = 0) :
    Module.finrank ℂ W ≤ 2 := by
  let phi : (sum0H × sum0H) →ₗ[ℂ] Module.Dual ℂ (sum0H × sum0H) :=
    { toFun := fun q =>
        { toFun := fun p => dot3 p.1.1 q.2.1 + dot3 q.1.1 p.2.1
          map_add' := fun p1 p2 => by
            simp only [dot3, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
          map_smul' := fun c p => by
            simp only [dot3, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
              smul_eq_mul, RingHom.id_apply]; ring }
      map_add' := fun q1 q2 => by
        apply LinearMap.ext; intro p
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, dot3,
          Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
      map_smul' := fun c q => by
        apply LinearMap.ext; intro p
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, dot3,
          Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]; ring }
  have hphi_inj : Function.Injective phi := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    have hm1 : (![1, -1, 0] : Fin 3 → ℂ) ∈ sum0H := by change (1 : ℂ) + (-1) + 0 = 0; ring
    have hm2 : (![1, 0, -1] : Fin 3 → ℂ) ∈ sum0H := by change (1 : ℂ) + 0 + (-1) = 0; ring
    have ha1 : dot3 (![1, -1, 0]) q.2.1 = 0 := by
      have := congrArg (fun l => l (⟨![1, -1, 0], hm1⟩, 0)) hq
      simpa [phi, dot3] using this
    have ha2 : dot3 (![1, 0, -1]) q.2.1 = 0 := by
      have := congrArg (fun l => l (⟨![1, 0, -1], hm2⟩, 0)) hq
      simpa [phi, dot3] using this
    have hb1 : dot3 q.1.1 (![1, -1, 0]) = 0 := by
      have := congrArg (fun l => l (0, ⟨![1, -1, 0], hm1⟩)) hq
      simpa [phi, dot3] using this
    have hb2 : dot3 q.1.1 (![1, 0, -1]) = 0 := by
      have := congrArg (fun l => l (0, ⟨![1, 0, -1], hm2⟩)) hq
      simpa [phi, dot3] using this
    have hq1 : q.1.1 0 + q.1.1 1 + q.1.1 2 = 0 := q.1.2
    have hq2 : q.2.1 0 + q.2.1 1 + q.2.1 2 = 0 := q.2.2
    simp only [dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at ha1 ha2 hb1 hb2
    apply Prod.ext
    · apply Subtype.ext; funext i; fin_cases i
      · change q.1.1 0 = 0; linear_combination (hb1 + hb2 + hq1) / 3
      · change q.1.1 1 = 0; linear_combination (-2 * hb1 + hb2 + hq1) / 3
      · change q.1.1 2 = 0; linear_combination (hb1 - 2 * hb2 + hq1) / 3
    · apply Subtype.ext; funext i; fin_cases i
      · change q.2.1 0 = 0; linear_combination (ha1 + ha2 + hq2) / 3
      · change q.2.1 1 = 0; linear_combination (-2 * ha1 + ha2 + hq2) / 3
      · change q.2.1 2 = 0; linear_combination (ha1 - 2 * ha2 + hq2) / 3
  have horth : ∀ p ∈ W, ∀ q ∈ W, phi q p = 0 := by
    intro p hp q hq
    have hp0 := hW p hp
    have hq0 := hW q hq
    have hpq := hW (p + q) (W.add_mem hp hq)
    simp only [dot3, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply] at hp0 hq0 hpq ⊢
    change dot3 p.1.1 q.2.1 + dot3 q.1.1 p.2.1 = 0
    simp only [dot3]
    linear_combination hpq - hp0 - hq0
  have hle := finrank_ortho_of_inj_dual phi hphi_inj W W horth
  rw [Module.finrank_prod, finrank_sum0H] at hle
  omega

private lemma iso3_prop {a0 a1 a2 : ℂ} (hsum : a0 + a1 + a2 = 0)
    (hsq : a0 * a0 + a1 * a1 + a2 * a2 = 0) (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0) :
    a0 ≠ 0 ∧ a1 ≠ 0 ∧ a2 ≠ 0 ∧ a0 ≠ a1 ∧ a1 ≠ a2 ∧ a0 ≠ a2 ∧
      a0 * a0 = a1 * a2 ∧ a1 * a1 = a0 * a2 ∧ a2 * a2 = a0 * a1 := by
  have he2 : a0 * a1 + a0 * a2 + a1 * a2 = 0 := by
    linear_combination ((a0 + a1 + a2) * hsum - hsq) / 2
  have h00 : a0 * a0 = a1 * a2 := by linear_combination a0 * hsum - he2
  have h11 : a1 * a1 = a0 * a2 := by linear_combination a1 * hsum - he2
  have h22 : a2 * a2 = a0 * a1 := by linear_combination a2 * hsum - he2
  have ha0 : a0 ≠ 0 := by
    intro h0
    have h12 : a1 * a2 = 0 := by linear_combination -h00 + a0 * h0
    rcases mul_eq_zero.mp h12 with h1 | h2
    · have h2 : a2 = 0 := by linear_combination hsum - h0 - h1
      rcases hne with h | h | h <;> exact h (by assumption)
    · have h1 : a1 = 0 := by linear_combination hsum - h0 - h2
      rcases hne with h | h | h <;> exact h (by assumption)
  have ha1 : a1 ≠ 0 := by
    intro h1
    have h00' : a0 * a0 = 0 := by linear_combination h00 + a2 * h1
    exact ha0 (mul_self_eq_zero.mp h00')
  have ha2 : a2 ≠ 0 := by
    intro h2
    have h00' : a0 * a0 = 0 := by linear_combination h00 + a1 * h2
    exact ha0 (mul_self_eq_zero.mp h00')
  have h01 : a0 ≠ a1 := by
    intro heq
    have h2 : a2 = -2 * a0 := by linear_combination hsum + heq
    have hsq' : 6 * (a0 * a0) = 0 := by
      rw [← heq, h2] at hsq
      linear_combination hsq
    have hne6 : (6 : ℂ) ≠ 0 := by norm_num
    exact ha0 (mul_self_eq_zero.mp ((mul_eq_zero.mp hsq').resolve_left hne6))
  have h12 : a1 ≠ a2 := by
    intro heq
    have h0 : a0 = -2 * a1 := by linear_combination hsum + heq
    have hsq' : 6 * (a1 * a1) = 0 := by
      rw [← heq, h0] at hsq
      linear_combination hsq
    have hne6 : (6 : ℂ) ≠ 0 := by norm_num
    exact ha1 (mul_self_eq_zero.mp ((mul_eq_zero.mp hsq').resolve_left hne6))
  have h02 : a0 ≠ a2 := by
    intro heq
    have h1 : a1 = -2 * a0 := by linear_combination hsum + heq
    have hsq' : 6 * (a0 * a0) = 0 := by
      rw [← heq, h1] at hsq
      linear_combination hsq
    have hne6 : (6 : ℂ) ≠ 0 := by norm_num
    exact ha0 (mul_self_eq_zero.mp ((mul_eq_zero.mp hsq').resolve_left hne6))
  exact ⟨ha0, ha1, ha2, h01, h12, h02, h00, h11, h22⟩

private lemma iso3_inv_prop {a0 a1 a2 y0 y1 y2 : ℂ}
    (hsum : a0 + a1 + a2 = 0) (hsq : a0 * a0 + a1 * a1 + a2 * a2 = 0)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0)
    (hysum : y0 + y1 + y2 = 0)
    (hyorth : a1 * a2 * y0 + a0 * a2 * y1 + a0 * a1 * y2 = 0) :
    a0 * y0 = a1 * y1 ∧ a0 * y0 = a2 * y2 := by
  have ⟨ha0, ha1, ha2, h01, h12, h02, h00, h11, h22⟩ := iso3_prop hsum hsq hne
  have h1' : (a1 - a2) * (a1 + a2) * (a0 * y0 - a1 * y1) = 0 := by
    have hlin : (a0 * a0 - a2 * a2) * y0 + (a1 * a1 - a2 * a2) * y1 = 0 := by
      linear_combination hyorth - a2 * a2 * hysum + y0 * h00 + y1 * h11 + y2 * h22
    have hcoeff : a1 * (a0 * a0 - a2 * a2) + a0 * (a1 * a1 - a2 * a2) = 0 := by
      linear_combination -(a0 + a1) * h22
    linear_combination -a1 * hlin + y0 * hcoeff
  have h12_sum : a1 + a2 ≠ 0 := by
    intro h
    have : a0 = 0 := by linear_combination hsum - h
    exact ha0 this
  have hdiff1 : a0 * y0 - a1 * y1 = 0 := by
    have hne_prod : (a1 - a2) * (a1 + a2) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr h12) h12_sum
    exact (mul_eq_zero.mp h1').resolve_left hne_prod
  have h2' : (a2 - a1) * (a2 + a1) * (a0 * y0 - a2 * y2) = 0 := by
    have hlin : (a0 * a0 - a1 * a1) * y0 + (a2 * a2 - a1 * a1) * y2 = 0 := by
      linear_combination hyorth - a1 * a1 * hysum + y0 * h00 + y1 * h11 + y2 * h22
    have hcoeff : a2 * (a0 * a0 - a1 * a1) + a0 * (a2 * a2 - a1 * a1) = 0 := by
      linear_combination -(a0 + a2) * h11
    linear_combination -a2 * hlin + y0 * hcoeff
  have h21_sum : a2 + a1 ≠ 0 := by
    intro h
    have : a0 = 0 := by linear_combination hsum - h
    exact ha0 this
  have hdiff2 : a0 * y0 - a2 * y2 = 0 := by
    have hne_prod : (a2 - a1) * (a2 + a1) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm h12)) h21_sum
    exact (mul_eq_zero.mp h2').resolve_left hne_prod
  exact ⟨sub_eq_zero.mp hdiff1, sub_eq_zero.mp hdiff2⟩

private lemma iso3_dir_prop {a0 a1 a2 w0 w1 w2 : ℂ}
    (hsum : a0 + a1 + a2 = 0) (hsq : a0 * a0 + a1 * a1 + a2 * a2 = 0)
    (hne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0)
    (hwsum : w0 + w1 + w2 = 0) (hworth : a0 * w0 + a1 * w1 + a2 * w2 = 0) :
    a0 * w1 = a1 * w0 ∧ a0 * w2 = a2 * w0 := by
  have ⟨_, _, _, _, h12, _, _, _, _⟩ := iso3_prop hsum hsq hne
  have h1 : (a1 - a2) * (a0 * w1 - a1 * w0) = 0 := by
    have hlin : (a0 - a2) * w0 + (a1 - a2) * w1 = 0 := by
      linear_combination hworth - a2 * hwsum
    have hcoeff : a0 * (a0 - a2) + a1 * (a1 - a2) = 0 := by
      linear_combination hsq - a2 * hsum
    linear_combination a0 * hlin - w0 * hcoeff
  have h2 : (a2 - a1) * (a0 * w2 - a2 * w0) = 0 := by
    have hlin : (a0 - a1) * w0 + (a2 - a1) * w2 = 0 := by
      linear_combination hworth - a1 * hwsum
    have hcoeff : a0 * (a0 - a1) + a2 * (a2 - a1) = 0 := by
      linear_combination hsq - a1 * hsum
    linear_combination a0 * hlin - w0 * hcoeff
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr h12)),
    sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm h12)))⟩

theorem L_gct_213 :
    ∀ (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (X : Submodule ℂ (Fin 3 → ℂ))
      (Y : Submodule ℂ (Fin 2 → ℂ)),
      (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧
        (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) →
      (∀ t ∈ L, ∀ x ∈ X, (∑ j, (t (0, j) + t (1, j) + x j)) = 0 ∧
        (∑ j, ∑ l, if j = l then 0 else
          t (0, j) * t (1, l) + t (0, j) * x l + t (1, j) * x l) = 0 ∧
        (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
          t (0, j) * t (1, l) * x m) = 0) →
      (∀ t ∈ L, ∀ y ∈ Y, (∑ j, (t (0, j) + t (1, j))) + y 0 + y 1 = 0 ∧
        (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) +
          (∑ j, t (0, j)) * y 1 + y 0 * (∑ j, t (1, j)) = 0) →
      Module.finrank ℂ L + Module.finrank ℂ X + Module.finrank ℂ Y ≤ 3 := by
  intro L X Y hL hLX hLY
  have hL_exp : ∀ t ∈ L,
      (t (0, 0) + t (1, 0)) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2)) = 0 ∧
      t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) +
        t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) = 0 := by
    intro t ht
    have ⟨h1, h2⟩ := hL t ht
    simp (config := { decide := true }) [Fin.sum_univ_three] at h1 h2
    exact ⟨by linear_combination h1, by linear_combination h2⟩
  have hX_sum : ∀ x ∈ X, x 0 + x 1 + x 2 = 0 := by
    intro x hx
    have h1 := (hLX 0 L.zero_mem x hx).1
    simp only [Fin.sum_univ_three, Pi.zero_apply, zero_add] at h1
    exact h1
  have hY_sum : ∀ y ∈ Y, y 0 + y 1 = 0 := by
    intro y hy
    have h1 := (hLY 0 L.zero_mem y hy).1
    simp only [Fin.sum_univ_three, Pi.zero_apply, add_zero, zero_add] at h1
    exact h1
  have hLX_orth : ∀ t ∈ L, ∀ x ∈ X,
      (t (0, 0) + t (1, 0)) * x 0 + (t (0, 1) + t (1, 1)) * x 1 +
        (t (0, 2) + t (1, 2)) * x 2 = 0 := by
    intro t ht x hx
    have h2 := (hLX t ht x hx).2.1
    have ⟨hl1, hl2⟩ := hL_exp t ht
    have hxs := hX_sum x hx
    simp (config := { decide := true }) [Fin.sum_univ_three] at h2
    linear_combination -h2 + hl2 +
      ((t (0, 0) + t (1, 0)) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2))) * hxs
  have hLX_cub : ∀ t ∈ L, ∀ x ∈ X,
      t (0, 0) * t (1, 1) * x 2 + t (0, 0) * t (1, 2) * x 1 +
      t (0, 1) * t (1, 0) * x 2 + t (0, 1) * t (1, 2) * x 0 +
      t (0, 2) * t (1, 0) * x 1 + t (0, 2) * t (1, 1) * x 0 = 0 := by
    intro t ht x hx
    have h3 := (hLX t ht x hx).2.2
    simp (config := { decide := true }) [Fin.sum_univ_three] at h3
    linear_combination h3
  have hLY_row : ∀ t ∈ L, ∀ y ∈ Y,
      (t (0, 0) + t (0, 1) + t (0, 2)) * y 0 = 0 := by
    intro t ht y hy
    have h2 := (hLY t ht y hy).2
    have ⟨hl1, hl2⟩ := hL_exp t ht
    have hys := hY_sum y hy
    simp (config := { decide := true }) [Fin.sum_univ_three] at h2
    have htwo : -2 * ((t (0, 0) + t (0, 1) + t (0, 2)) * y 0) = 0 := by
      linear_combination h2 - hl2 - (t (0, 0) + t (0, 1) + t (0, 2)) * hys - y 0 * hl1
    have hne2 : (-2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp htwo).resolve_left hne2
  let colMap : L →ₗ[ℂ] sum0H :=
    { toFun := fun t =>
        ⟨fun j => t.1 (0, j) + t.1 (1, j), (hL_exp t.1 t.2).1⟩
      map_add' := fun t1 t2 => by
        apply Subtype.ext; funext j; simp only [Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun r t => by
        apply Subtype.ext; funext j
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let Xsub : Submodule ℂ sum0H := X.comap sum0H.subtype
  have hX_eq : Module.finrank ℂ Xsub = Module.finrank ℂ X := by
    let e : Xsub →ₗ[ℂ] X :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hbij : Function.Bijective e := by
      constructor
      · intro a b h
        have hv : a.1.1 = b.1.1 := congrArg (fun x : X => x.1) h
        exact Subtype.ext (Subtype.ext hv)
      · rintro ⟨x, hx⟩
        exact ⟨⟨⟨x, hX_sum x hx⟩, hx⟩, rfl⟩
    exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective e hbij)
  have hcol_X : Module.finrank ℂ (LinearMap.range colMap) + Module.finrank ℂ X ≤ 2 := by
    rw [← hX_eq]
    apply finrank_ortho_sum0H
    rintro _ ⟨t, rfl⟩ x hx
    exact hLX_orth t.1 t.2 x.1 hx
  have hker_le1 : Module.finrank ℂ (LinearMap.ker colMap) ≤ 1 := by
    let row0 : LinearMap.ker colMap →ₗ[ℂ] (Fin 3 → ℂ) :=
      { toFun := fun t j => t.1.1 (0, j)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hrow0_inj : Function.Injective row0 := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨⟨t, ht⟩, hker⟩ h0
      rw [LinearMap.mem_ker] at hker
      have hc0 : ∀ j : Fin 3, t (0, j) + t (1, j) = 0 := fun j =>
        congrFun (congrArg Subtype.val hker) j
      apply Subtype.ext; apply Subtype.ext
      funext ⟨i, j⟩
      have h0j : t (0, j) = 0 := congrFun h0 j
      fin_cases i
      · exact h0j
      · change t (1, j) = 0; have := hc0 j; linear_combination this - h0j
    rw [← LinearMap.finrank_range_of_inj hrow0_inj]
    apply finrank_iso_q3
    rintro _ ⟨⟨⟨t, ht⟩, hker⟩, rfl⟩
    rw [LinearMap.mem_ker] at hker
    have hc0 : ∀ j : Fin 3, t (0, j) + t (1, j) = 0 := fun j =>
      congrFun (congrArg Subtype.val hker) j
    have h2 := (hL_exp t ht).2
    have h0 := hc0 0; have h1 := hc0 1; have h2' := hc0 2
    change t (0, 0) * t (0, 1) + t (0, 0) * t (0, 2) + t (0, 1) * t (0, 2) = 0
    linear_combination (-h2 + t (0, 0) * (h1 + h2') + t (0, 1) * (h0 + h2') + t (0, 2) * (h0 + h1)) / 2
  have hrn_L : Module.finrank ℂ (LinearMap.range colMap) +
      Module.finrank ℂ (LinearMap.ker colMap) = Module.finrank ℂ L :=
    LinearMap.finrank_range_add_finrank_ker colMap
  have hY_le1 : Module.finrank ℂ Y ≤ 1 := by
    let eY : Y →ₗ[ℂ] ℂ :=
      { toFun := fun y => y.1 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hY_inj : Function.Injective eY := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      have hy0 : y.1 0 = 0 := hy
      have hys := hY_sum y.1 y.2
      apply Subtype.ext; funext i; fin_cases i
      · exact hy0
      · change y.1 1 = 0; linear_combination hys - hy0
    rw [← LinearMap.finrank_range_of_inj hY_inj]
    calc Module.finrank ℂ (LinearMap.range eY) ≤ Module.finrank ℂ ℂ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℂ
  by_cases hY0 : Module.finrank ℂ Y = 0
  · omega
  · have hY_pos : 0 < Module.finrank ℂ Y := by omega
    have hY_ne : ∃ y ∈ Y, y 0 ≠ 0 := by
      by_contra hall
      push Not at hall
      have hbot : Y = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro y hy
        funext i
        have hy0 := hall y hy
        have hys := hY_sum y hy
        fin_cases i
        · exact hy0
        · change y 1 = 0; linear_combination hys - hy0
      rw [hbot, finrank_bot] at hY_pos
      omega
    rcases hY_ne with ⟨y0, hy0_mem, hy0_ne⟩
    have hrow_zero : ∀ t ∈ L,
        t (0, 0) + t (0, 1) + t (0, 2) = 0 ∧ t (1, 0) + t (1, 1) + t (1, 2) = 0 := by
      intro t ht
      have h0 : t (0, 0) + t (0, 1) + t (0, 2) = 0 :=
        (mul_eq_zero.mp (hLY_row t ht y0 hy0_mem)).resolve_right hy0_ne
      have hs := (hL_exp t ht).1
      exact ⟨h0, by linear_combination hs - h0⟩
    have hdot_zero : ∀ t ∈ L,
        t (0, 0) * t (1, 0) + t (0, 1) * t (1, 1) + t (0, 2) * t (1, 2) = 0 := by
      intro t ht
      have ⟨hr0, hr1⟩ := hrow_zero t ht
      have h2 := (hL_exp t ht).2
      linear_combination (t (0, 0) + t (0, 1) + t (0, 2)) * hr1 - h2
    by_cases hX0 : Module.finrank ℂ X = 0
    · let toHH : L →ₗ[ℂ] (sum0H × sum0H) :=
        { toFun := fun t =>
            (⟨fun j => t.1 (0, j), (hrow_zero t.1 t.2).1⟩,
             ⟨fun j => t.1 (1, j), (hrow_zero t.1 t.2).2⟩)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have htoHH_inj : Function.Injective toHH := by
        rw [injective_iff_map_eq_zero]
        intro t ht
        apply Subtype.ext; funext ⟨i, j⟩
        fin_cases i
        · exact congrFun (congrArg Subtype.val (congrArg Prod.fst ht)) j
        · exact congrFun (congrArg Subtype.val (congrArg Prod.snd ht)) j
      have hL_le2 : Module.finrank ℂ L ≤ 2 := by
        rw [← LinearMap.finrank_range_of_inj htoHH_inj]
        apply finrank_iso_HH
        rintro _ ⟨t, rfl⟩
        exact hdot_zero t.1 t.2
      omega
    · by_cases hX2 : Module.finrank ℂ X = 2
      · have hXsub_top : Xsub = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          rw [hX_eq, hX2, finrank_sum0H]
        have hL_bot : L = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro t ht
          have hxm1 : (![1, -1, 0] : Fin 3 → ℂ) ∈ X := by
            have hm : (![1, -1, 0] : Fin 3 → ℂ) ∈ sum0H := by change (1 : ℂ) + (-1) + 0 = 0; ring
            have hmem : (⟨![1, -1, 0], hm⟩ : sum0H) ∈ Xsub := by rw [hXsub_top]; trivial
            exact hmem
          have hxm2 : (![1, 0, -1] : Fin 3 → ℂ) ∈ X := by
            have hm : (![1, 0, -1] : Fin 3 → ℂ) ∈ sum0H := by change (1 : ℂ) + 0 + (-1) = 0; ring
            have hmem : (⟨![1, 0, -1], hm⟩ : sum0H) ∈ Xsub := by rw [hXsub_top]; trivial
            exact hmem
          have ho1 := hLX_orth t ht _ hxm1
          have ho2 := hLX_orth t ht _ hxm2
          have hc1 := hLX_cub t ht _ hxm1
          have hc2 := hLX_cub t ht _ hxm2
          have ⟨hr0, hr1⟩ := hrow_zero t ht
          have hdot := hdot_zero t ht
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at ho1 ho2 hc1 hc2
          have hcs0 : t (0, 0) + t (1, 0) = 0 := by linear_combination (ho1 + ho2 + hr0 + hr1) / 3
          have hcs1 : t (0, 1) + t (1, 1) = 0 := by linear_combination (-2 * ho1 + ho2 + hr0 + hr1) / 3
          have hcs2 : t (0, 2) + t (1, 2) = 0 := by linear_combination (ho1 - 2 * ho2 + hr0 + hr1) / 3
          have hsq : t (0, 0) * t (0, 0) + t (0, 1) * t (0, 1) + t (0, 2) * t (0, 2) = 0 := by
            linear_combination -hdot + t (0, 0) * hcs0 + t (0, 1) * hcs1 + t (0, 2) * hcs2
          have ha_zero : t (0, 0) = 0 ∧ t (0, 1) = 0 ∧ t (0, 2) = 0 := by
            by_contra hne
            have hne' : t (0, 0) ≠ 0 ∨ t (0, 1) ≠ 0 ∨ t (0, 2) ≠ 0 := by tauto
            have hcub1' :
                t (0, 1) * t (0, 2) * 1 + t (0, 0) * t (0, 2) * (-1) + t (0, 0) * t (0, 1) * 0 = 0 := by
              linear_combination -hc1 / 2 +
                (t (0, 1) * hcs2 + t (0, 2) * hcs1 - t (0, 0) * hcs2 - t (0, 2) * hcs0) / 2
            have ⟨heq01, _⟩ := iso3_inv_prop hr0 hsq hne' (by ring : (1 : ℂ) + (-1) + 0 = 0) hcub1'
            have ⟨ha0, ha1, _, _, _, _, _, _, _⟩ := iso3_prop hr0 hsq hne'
            have h01_sum : t (0, 0) + t (0, 1) = 0 := by linear_combination heq01
            have h20 : t (0, 2) = 0 := by linear_combination hr0 - h01_sum
            have ⟨_, _, ha2, _, _, _, _, _, _⟩ := iso3_prop hr0 hsq hne'
            exact ha2 h20
          funext ⟨i, j⟩
          fin_cases i <;> fin_cases j
          · exact ha_zero.1
          · exact ha_zero.2.1
          · exact ha_zero.2.2
          · change t (1, 0) = 0; linear_combination hcs0 - ha_zero.1
          · change t (1, 1) = 0; linear_combination hcs1 - ha_zero.2.1
          · change t (1, 2) = 0; linear_combination hcs2 - ha_zero.2.2
        rw [hL_bot, finrank_bot]
        omega
      · have hX1 : Module.finrank ℂ X = 1 := by omega
        by_contra hgt
        have hker_pos : 0 < Module.finrank ℂ (LinearMap.ker colMap) := by omega
        have hrng_pos : 0 < Module.finrank ℂ (LinearMap.range colMap) := by omega
        have hX_ex : ∃ x ∈ X, x ≠ 0 := by
          by_contra hall
          push Not at hall
          have hbot : X = ⊥ := (Submodule.eq_bot_iff X).mpr hall
          rw [hbot, finrank_bot] at hX1
          omega
        rcases hX_ex with ⟨x, hx_mem, hx_ne⟩
        have hker_ex : ∃ t0 : Fin 2 × Fin 3 → ℂ, ∃ ht0 : t0 ∈ L, colMap ⟨t0, ht0⟩ = 0 ∧ t0 ≠ 0 := by
          have hne_bot : LinearMap.ker colMap ≠ ⊥ := by
            intro hb; rw [hb, finrank_bot] at hker_pos; omega
          rcases Submodule.exists_mem_ne_zero_of_ne_bot hne_bot with ⟨⟨t0, ht0⟩, hker0, hne0⟩
          refine ⟨t0, ht0, hker0, fun h => hne0 (Subtype.ext h)⟩
        rcases hker_ex with ⟨t0, ht0, hker0, ht0_ne⟩
        have hrng_ex : ∃ t1 : Fin 2 × Fin 3 → ℂ, ∃ ht1 : t1 ∈ L, colMap ⟨t1, ht1⟩ ≠ 0 := by
          have hne_bot : LinearMap.range colMap ≠ ⊥ := by
            intro hb; rw [hb, finrank_bot] at hrng_pos; omega
          rcases Submodule.exists_mem_ne_zero_of_ne_bot hne_bot with ⟨v, ⟨⟨t1, ht1⟩, hv⟩, hv_ne⟩
          exact ⟨t1, ht1, hv.symm ▸ hv_ne⟩
        rcases hrng_ex with ⟨t1, ht1, hcol1_ne⟩
        have hc0 : ∀ j : Fin 3, t0 (0, j) + t0 (1, j) = 0 := fun j =>
          congrFun (congrArg Subtype.val hker0) j
        have h0_0 := hc0 0; have h0_1 := hc0 1; have h0_2 := hc0 2
        have ⟨hr00, hr01⟩ := hrow_zero t0 ht0
        have ⟨hr10, hr11⟩ := hrow_zero t1 ht1
        have hd0 := hdot_zero t0 ht0
        have hd1 := hdot_zero t1 ht1
        have hd01 := hdot_zero (t0 + t1) (L.add_mem ht0 ht1)
        simp only [Pi.add_apply] at hd01
        have hxs := hX_sum x hx_mem
        have ho1 := hLX_orth t1 ht1 x hx_mem
        have hcub0 := hLX_cub t0 ht0 x hx_mem
        have hcub1 := hLX_cub t1 ht1 x hx_mem
        set a0 := t0 (0, 0); set a1 := t0 (0, 1); set a2 := t0 (0, 2)
        set u0 := t1 (0, 0); set u1 := t1 (0, 1); set u2 := t1 (0, 2)
        set v0 := t1 (1, 0); set v1 := t1 (1, 1); set v2 := t1 (1, 2)
        have ha_sq : a0 * a0 + a1 * a1 + a2 * a2 = 0 := by
          linear_combination -hd0 + a0 * h0_0 + a1 * h0_1 + a2 * h0_2
        have ha_ne : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 := by
          by_contra h
          push Not at h
          apply ht0_ne
          funext ⟨i, j⟩
          fin_cases i <;> fin_cases j
          · exact h.1
          · exact h.2.1
          · exact h.2.2
          · change t0 (1, 0) = 0; linear_combination h0_0 - h.1
          · change t0 (1, 1) = 0; linear_combination h0_1 - h.2.1
          · change t0 (1, 2) = 0; linear_combination h0_2 - h.2.2
        have ⟨ha0, ha1, ha2, _, _, _, h00, h11, h22⟩ := iso3_prop hr00 ha_sq ha_ne
        have hcub0' : a1 * a2 * x 0 + a0 * a2 * x 1 + a0 * a1 * x 2 = 0 := by
          linear_combination -hcub0 / 2 +
            (a0 * h0_1 * x 2 + a0 * h0_2 * x 1 + a1 * h0_0 * x 2 +
              a1 * h0_2 * x 0 + a2 * h0_0 * x 1 + a2 * h0_1 * x 0) / 2
        have ⟨hax01, hax02⟩ := iso3_inv_prop hr00 ha_sq ha_ne hxs hcub0'
        set c := a0 * x 0
        have hc_ne : c ≠ 0 := by
          intro hc0_eq
          have hx0 : x 0 = 0 := (mul_eq_zero.mp hc0_eq).resolve_left ha0
          have hx1 : x 1 = 0 := (mul_eq_zero.mp (hax01.symm.trans hc0_eq)).resolve_left ha1
          have hx2 : x 2 = 0 := (mul_eq_zero.mp (hax02.symm.trans hc0_eq)).resolve_left ha2
          apply hx_ne; funext j; fin_cases j <;> assumption
        have huv_sum : (u0 + v0) + (u1 + v1) + (u2 + v2) = 0 := by linear_combination hr10 + hr11
        have huv_orth : a1 * a2 * (u0 + v0) + a0 * a2 * (u1 + v1) + a0 * a1 * (u2 + v2) = 0 := by
          have hmul : c * (a1 * a2 * (u0 + v0) + a0 * a2 * (u1 + v1) + a0 * a1 * (u2 + v2)) = 0 := by
            linear_combination (a0 * a1 * a2) * ho1 +
              (u1 + v1) * a0 * a2 * hax01 + (u2 + v2) * a0 * a1 * hax02
          exact (mul_eq_zero.mp hmul).resolve_left hc_ne
        have ⟨has01, has02⟩ := iso3_inv_prop hr00 ha_sq ha_ne huv_sum huv_orth
        set s := a0 * (u0 + v0)
        have hs_ne : s ≠ 0 := by
          intro hs0
          have hs_0 : u0 + v0 = 0 := (mul_eq_zero.mp hs0).resolve_left ha0
          have hs_1 : u1 + v1 = 0 := (mul_eq_zero.mp (has01.symm.trans hs0)).resolve_left ha1
          have hs_2 : u2 + v2 = 0 := (mul_eq_zero.mp (has02.symm.trans hs0)).resolve_left ha2
          apply hcol1_ne
          apply Subtype.ext; funext j; fin_cases j <;> assumption
        have hvu_sum : (v0 - u0) + (v1 - u1) + (v2 - u2) = 0 := by linear_combination hr11 - hr10
        have hvu_orth : a0 * (v0 - u0) + a1 * (v1 - u1) + a2 * (v2 - u2) = 0 := by
          linear_combination hd01 - hd0 - hd1 - u0 * h0_0 - u1 * h0_1 - u2 * h0_2
        have ⟨hd01_eq, hd02_eq⟩ := iso3_dir_prop hr00 ha_sq ha_ne hvu_sum hvu_orth
        have h6 : 6 * c * s * s = 0 := by
          have hvu0 : a0 * (v0 - u0) = a0 * (v0 - u0) := rfl
          set d := (v0 - u0) / a0
          have hw0 : v0 - u0 = d * a0 := by dsimp [d]; field_simp [ha0]
          have hw1 : v1 - u1 = d * a1 := by
            have : a0 * (v1 - u1 - d * a1) = 0 := by linear_combination hd01_eq + a1 * hw0
            exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
          have hw2 : v2 - u2 = d * a2 := by
            have : a0 * (v2 - u2 - d * a2) = 0 := by linear_combination hd02_eq + a2 * hw0
            exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
          have h2u0 : 2 * a0 * u0 = s - d * a0 * a0 := by linear_combination -a0 * hw0
          have h2v0 : 2 * a0 * v0 = s + d * a0 * a0 := by linear_combination a0 * hw0
          have h2u1 : 2 * a1 * u1 = s - d * a1 * a1 := by linear_combination -has01 - a1 * hw1
          have h2v1 : 2 * a1 * v1 = s + d * a1 * a1 := by linear_combination -has01 + a1 * hw1
          have h2u2 : 2 * a2 * u2 = s - d * a2 * a2 := by linear_combination -has02 - a2 * hw2
          have h2v2 : 2 * a2 * v2 = s + d * a2 * a2 := by linear_combination -has02 + a2 * hw2
          have hx0_eq : a0 * x 0 = c := rfl
          have hx1_eq : a1 * x 1 = c := hax01.symm
          have hx2_eq : a2 * x 2 = c := hax02.symm
          have hcub_scaled : 4 * (a0 * a1 * a2) * (u0 * v1 * x 2 + u0 * v2 * x 1 +
              u1 * v0 * x 2 + u1 * v2 * x 0 + u2 * v0 * x 1 + u2 * v1 * x 0) = 0 := by
            linear_combination 4 * (a0 * a1 * a2) * hcub1
          have hexp :
              4 * (a0 * a1 * a2) * (u0 * v1 * x 2 + u0 * v2 * x 1 +
                u1 * v0 * x 2 + u1 * v2 * x 0 + u2 * v0 * x 1 + u2 * v1 * x 0) =
              6 * c * s * s - 2 * c * d * d * (a0 * a0 * a1 * a1 + a0 * a0 * a2 * a2 + a1 * a1 * a2 * a2) := by
            have hrearr :
                4 * (a0 * a1 * a2) * (u0 * v1 * x 2 + u0 * v2 * x 1 +
                  u1 * v0 * x 2 + u1 * v2 * x 0 + u2 * v0 * x 1 + u2 * v1 * x 0) =
                (2 * a0 * u0) * (2 * a1 * v1) * (a2 * x 2) +
                (2 * a0 * u0) * (2 * a2 * v2) * (a1 * x 1) +
                (2 * a1 * u1) * (2 * a0 * v0) * (a2 * x 2) +
                (2 * a1 * u1) * (2 * a2 * v2) * (a0 * x 0) +
                (2 * a2 * u2) * (2 * a0 * v0) * (a1 * x 1) +
                (2 * a2 * u2) * (2 * a1 * v1) * (a0 * x 0) := by ring
            rw [hrearr, h2u0, h2v0, h2u1, h2v1, h2u2, h2v2, hx0_eq, hx1_eq, hx2_eq]
            ring
          have hquart : a0 * a0 * a1 * a1 + a0 * a0 * a2 * a2 + a1 * a1 * a2 * a2 = 0 := by
            linear_combination (a0 * a1 * a2) * hr00 - a0 * a1 * h22 - a0 * a2 * h11 - a1 * a2 * h00
          rw [hcub_scaled, hquart] at hexp
          linear_combination -hexp
        have hne6 : (6 : ℂ) ≠ 0 := by norm_num
        have h6cs : 6 * c * s ≠ 0 := mul_ne_zero (mul_ne_zero hne6 hc_ne) hs_ne
        exact mul_ne_zero h6cs hs_ne h6

end PEqualNP.Outside
