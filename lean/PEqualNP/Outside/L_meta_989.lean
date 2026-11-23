import Mathlib
import PEqualNP.Defs

open Matrix

namespace PEqualNP.Outside.L_meta_989_aux

theorem cross_zero_prop {F : Type} [Field F] (u N : Fin 3 → F) (h : u ⨯₃ N = 0) (hN : N ≠ 0) :
    ∃ s : F, u = s • N := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [cross_apply] at h0 h1 h2
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hN
  refine ⟨u t / N t, ?_⟩
  funext r
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ht ⊢
  field_simp
  fin_cases t <;> fin_cases r <;> simp at ht ⊢ <;> first | linear_combination h0 | linear_combination -h0 | linear_combination h1 | linear_combination -h1 | linear_combination h2 | linear_combination -h2


theorem two_lines {F : Type} [Field F] (a c l l' : Fin 3 → F) (ha : a ≠ 0)
    (hac : ∀ s : F, c ≠ s • a) (hl : l ≠ 0)
    (hla : a ⬝ᵥ l = 0) (hlc : c ⬝ᵥ l = 0) (hl'a : a ⬝ᵥ l' = 0) (hl'c : c ⬝ᵥ l' = 0) :
    ∃ s : F, l' = s • l := by
  have hN : a ⨯₃ c ≠ 0 := by
    intro h0
    have : c ⨯₃ a = 0 := by rw [← cross_anticomm, h0, neg_zero]
    obtain ⟨s, hs⟩ := cross_zero_prop c a this ha
    exact hac s hs
  have key : ∀ m : Fin 3 → F, a ⬝ᵥ m = 0 → c ⬝ᵥ m = 0 → ∃ s : F, m = s • (a ⨯₃ c) := by
    intro m h1 h2
    apply cross_zero_prop m _ _ hN
    rw [← cross_anticomm, cross_cross_eq_smul_sub_smul, h1, h2]
    simp
  obtain ⟨s, hs⟩ := key l hla hlc
  obtain ⟨s', hs'⟩ := key l' hl'a hl'c
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hl (by simpa using hs)
  refine ⟨s' / s, ?_⟩
  rw [hs, hs', smul_smul, div_mul_cancel₀ _ hs0]

def mono {F : Type} [Field F] {k : ℕ} (l : Fin k → Fin 3 → F) (d a c : ℕ) : Fin k → F :=
  fun i => l i 0 ^ a * l i 1 ^ c * l i 2 ^ (d - a - c)

def W {F : Type} [Field F] {k : ℕ} (l : Fin k → Fin 3 → F) (d : ℕ) : Submodule F (Fin k → F) :=
  Submodule.span F {f | ∃ a c : ℕ, a + c ≤ d ∧ f = mono l d a c}

theorem coord_mem {F : Type} [Field F] {k : ℕ} (l : Fin k → Fin 3 → F) (d : ℕ) (t : Fin 3)
    (v : Fin k → F) (hv : v ∈ W l d) : (fun i => l i t) * v ∈ W l (d + 1) := by
  have hle : W l d ≤ (W l (d + 1)).comap (LinearMap.mulLeft F (fun i => l i t)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, c, hac, rfl⟩
    show (fun i => l i t) * mono l d a c ∈ W l (d + 1)
    apply Submodule.subset_span
    fin_cases t
    · refine ⟨a + 1, c, by omega, ?_⟩
      funext i
      have e : d + 1 - (a + 1) - c = d - a - c := by omega
      simp only [mono, Pi.mul_apply, e, Fin.zero_eta, Fin.isValue]
      ring
    · refine ⟨a, c + 1, by omega, ?_⟩
      funext i
      have e : d + 1 - a - (c + 1) = d - a - c := by omega
      simp only [mono, Pi.mul_apply, e, Fin.mk_one, Fin.isValue]
      ring
    · refine ⟨a, c, by omega, ?_⟩
      funext i
      have e : d + 1 - a - c = d - a - c + 1 := by omega
      simp only [mono, Pi.mul_apply, e, Fin.isValue, Fin.reduceFinMk]
      ring
  exact hle hv

theorem lin_mem {F : Type} [Field F] {k : ℕ} (l : Fin k → Fin 3 → F) (d : ℕ) (w : Fin 3 → F)
    (v : Fin k → F) (hv : v ∈ W l d) :
    (fun i => (∑ t : Fin 3, w t * l i t) * v i) ∈ W l (d + 1) := by
  have e : (fun i => (∑ t : Fin 3, w t * l i t) * v i) =
      ∑ t : Fin 3, w t • ((fun i => l i t) * v) := by
    funext i
    simp [Finset.sum_mul, Finset.sum_apply, mul_assoc]
  rw [e]
  exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (coord_mem l d t v hv))

theorem prod_mem {F : Type} [Field F] {n k : ℕ} (l : Fin k → Fin 3 → F) (pt : Fin n → Fin 3 → F)
    (s : Finset (Fin n)) :
    (fun i => ∏ q ∈ s, (∑ t : Fin 3, pt q t * l i t)) ∈ W l s.card := by
  induction s using Finset.induction_on with
  | empty =>
    apply Submodule.subset_span
    refine ⟨0, 0, by omega, ?_⟩
    funext i
    simp [mono]
  | insert q s hq ih =>
    rw [Finset.card_insert_of_notMem hq]
    have := lin_mem l s.card (pt q) _ ih
    simpa [Finset.prod_insert hq] using this

theorem pow_mem {F : Type} [Field F] {k : ℕ} (l : Fin k → Fin 3 → F) (d : ℕ) (t : Fin 3)
    (v : Fin k → F) (hv : v ∈ W l d) (e : ℕ) :
    (fun i => l i t ^ e * v i) ∈ W l (d + e) := by
  induction e with
  | zero => simpa using hv
  | succ e ih =>
    have := coord_mem l (d + e) t _ ih
    rw [← add_assoc]
    convert this using 1
    funext i
    simp [pow_succ]
    ring

theorem sum_aux (d : ℕ) : (∑ a ∈ Finset.range (d + 1), (d + 1 - a)) * 2 = (d + 1) * (d + 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have h1 : ∑ a ∈ Finset.range (d + 1), (d + 1 + 1 - a) = ∑ a ∈ Finset.range (d + 1), (d + 1 - a) + (d + 1) := by
      have hc : ∀ a ∈ Finset.range (d + 1), d + 1 + 1 - a = (d + 1 - a) + 1 := by
        intro a ha
        simp at ha
        omega
      rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib]
      simp
    have h2 : d + 1 + 1 - (d + 1) = 1 := by omega
    rw [h1, h2]
    nlinarith [ih]

theorem finrank_W {F : Type} [Field F] {k : ℕ} (l : Fin k → Fin 3 → F) (d : ℕ) :
    Module.finrank F (W l d) * 2 ≤ (d + 1) * (d + 2) := by
  classical
  let G : Finset ((_ : ℕ) × ℕ) := (Finset.range (d + 1)).sigma (fun a => Finset.range (d + 1 - a))
  have hle : W l d ≤ Submodule.span F ((G.image (fun x => mono l d x.1 x.2) : Finset (Fin k → F)) : Set (Fin k → F)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, c, hac, rfl⟩
    apply Submodule.subset_span
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    refine ⟨⟨a, c⟩, ?_, rfl⟩
    simp [G]
    omega
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_finset_le_card (R := F) (G.image (fun x => mono l d x.1 x.2))
  have h3 := Finset.card_image_le (s := G) (f := fun x => mono l d x.1 x.2)
  have h4 : G.card * 2 = (d + 1) * (d + 2) := by
    simp only [G, Finset.card_sigma, Finset.card_range]
    exact sum_aux d
  have h2' : Module.finrank F (Submodule.span F ((G.image (fun x => mono l d x.1 x.2) : Finset (Fin k → F)) : Set (Fin k → F))) ≤ (G.image (fun x => mono l d x.1 x.2)).card := h2
  rw [← h4]
  omega


theorem part1 : ∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2) := by
  intro F _ n k b pt l y g hpt hpp hl hll hy hyoff hsafe htwo
  classical
  have key : ∀ i j : Fin k, i ≠ j → ∃ q ∈ y j, ∑ t : Fin 3, pt q t * l i t = 0 := by
    intro i j hij
    by_contra hne
    push Not at hne
    obtain ⟨p, p', hpp', hp, hp', hg, hg'⟩ := htwo j
    have hon : ∀ r, g (fun v => decide (v ∈ y j ∨ v = r)) = true →
        ∑ t : Fin 3, pt r t * l i t = 0 := by
      intro r hr
      obtain ⟨q, hq, hqi⟩ := hsafe i _ hr
      simp only [decide_eq_true_eq] at hq
      rcases hq with hq | rfl
      · exact absurd hqi (hne q hq)
      · exact hqi
    obtain ⟨s, hs⟩ := two_lines (pt p) (pt p') (l j) (l i) (hpt p) (hpp p p' hpp') (hl j)
      hp hp' (hon p hg) (hon p' hg')
    exact hll j i (Ne.symm hij) s hs
  have ht : ∀ j : Fin k, ∃ t : Fin 3, l j t ≠ 0 := fun j => Function.ne_iff.mp (hl j)
  choose tt htt using ht
  let v : Fin k → Fin k → F := fun j i =>
    l i (tt j) ^ (b - (y j).card) * ∏ q ∈ y j, (∑ t : Fin 3, pt q t * l i t)
  have hvW : ∀ j, v j ∈ W l b := by
    intro j
    have := pow_mem l _ (tt j) _ (prod_mem l pt (y j)) (b - (y j).card)
    rw [Nat.add_sub_cancel' (hy j)] at this
    exact this
  have hdiag : ∀ j, v j j ≠ 0 := by
    intro j
    apply mul_ne_zero (pow_ne_zero _ (htt j))
    rw [Finset.prod_ne_zero_iff]
    exact hyoff j
  have hoff : ∀ i j, i ≠ j → v j i = 0 := by
    intro i j hij
    obtain ⟨q, hq, hqz⟩ := key i j hij
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero hq hqz)
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [Finset.sum_eq_single j (fun j' _ hj' => by rw [hoff j j' (Ne.symm hj'), mul_zero])
      (by simp)] at this
    exact (mul_eq_zero.mp this).resolve_right (hdiag j)
  have h1 := finrank_span_eq_card hli
  have h2 : Submodule.span F (Set.range v) ≤ W l b :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hvW j)
  have h3 := Submodule.finrank_mono h2
  have h4 := finrank_W l b
  simp only [Fintype.card_fin] at h1
  generalize (b + 1) * (b + 2) = M at h4 ⊢
  omega

def phi {F : Type} [Field F] : Option F → Fin 3 → F
  | none => ![0, 0, 1]
  | some t => ![1, t, t ^ 2]

theorem phi_ne_zero {F : Type} [Field F] (u : Option F) : phi u ≠ 0 := by
  intro h
  cases u with
  | none => have := congrFun h 2; simp [phi] at this
  | some t => have := congrFun h 0; simp [phi] at this

theorem phi_nonprop {F : Type} [Field F] (u v : Option F) (huv : u ≠ v) (c : F) :
    phi v ≠ c • phi u := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  cases u <;> cases v <;> simp [phi] at h0 h1 h2 huv
  all_goals subst h0
  all_goals simp_all

theorem phi_triple {F : Type} [Field F] (u v w : Option F) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) : phi w ⬝ᵥ (phi u ⨯₃ phi v) ≠ 0 := by
  cases u <;> cases v <;> cases w <;> simp_all [phi, cross_apply, dotProduct, Fin.sum_univ_three]
  all_goals intro h
  · exact hvw (by linear_combination -h)
  · exact huw (by linear_combination h)
  · exact huv (by linear_combination -h)
  · rename_i a b c
    have e : (a - b) * (a - c) * (b - c) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp e with e | e
    · rcases mul_eq_zero.mp e with e | e
      · exact huv (sub_eq_zero.mp e)
      · exact huw (sub_eq_zero.mp e)
    · exact hvw (sub_eq_zero.mp e)


theorem part2 : ∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2) := by
  intro F _ _ b hb
  classical
  let e := Finite.equivFin (Projectivization F (Fin 3 → F))
  let pt : Fin (Nat.card (Projectivization F (Fin 3 → F))) → Fin 3 → F := fun p => (e.symm p).rep
  obtain ⟨α⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (b + 2)) (β := Option F)
    (by simp; omega)
  let A : Fin (b + 2) → Fin 3 → F := fun a => phi (α a)
  have hA0 : ∀ a, A a ≠ 0 := fun a => phi_ne_zero _
  have hAnp : ∀ a a', a ≠ a' → ∀ c : F, A a' ≠ c • A a := by
    intro a a' h c
    exact phi_nonprop (α a) (α a') (fun h' => h (α.injective h')) c
  have hAtri : ∀ a c d, a ≠ c → a ≠ d → c ≠ d → A d ⬝ᵥ (A a ⨯₃ A c) ≠ 0 := by
    intro a c d h1 h2 h3
    exact phi_triple _ _ _ (fun h => h1 (α.injective h)) (fun h => h2 (α.injective h))
      (fun h => h3 (α.injective h))
  let idx : Fin (b + 2) → Fin (Nat.card (Projectivization F (Fin 3 → F))) :=
    fun a => e (Projectivization.mk F (A a) (hA0 a))
  have hidx : ∀ a, ∃ u : F, u ≠ 0 ∧ pt (idx a) = u • A a := by
    intro a
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep F (A a) (hA0 a)
    refine ⟨u, u.ne_zero, ?_⟩
    simp only [pt, idx, Equiv.symm_apply_apply, ← hu]
    rfl
  have hdot : ∀ a (w : Fin 3 → F), (∑ t : Fin 3, pt (idx a) t * w t = 0 ↔ A a ⬝ᵥ w = 0) := by
    intro a w
    obtain ⟨u, hu, h⟩ := hidx a
    have : ∑ t : Fin 3, pt (idx a) t * w t = u * (A a ⬝ᵥ w) := by
      rw [h]
      simp [dotProduct, Finset.mul_sum, mul_assoc]
    rw [this]
    simp [hu]
  have hidx_inj : Function.Injective idx := by
    intro a a' h
    by_contra hne
    simp only [idx, EmbeddingLike.apply_eq_iff_eq] at h
    rw [Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    exact hAnp a' a (Ne.symm hne) c hc.symm
  let T : Finset (Finset (Fin (b + 2))) := Finset.powersetCard 2 Finset.univ
  let eT : Fin T.card ≃ T := T.equivFin.symm
  have h2 : ∀ i : Fin T.card, ∃ x y : Fin (b + 2), x ≠ y ∧ ((eT i : Finset (Fin (b + 2)))) = {x, y} :=
    fun i => Finset.card_eq_two.mp (Finset.mem_powersetCard.mp (eT i).2).2
  choose f1 f2 hf12 hfs using h2
  have hmem : ∀ i d, d ∈ (eT i : Finset (Fin (b + 2))) ↔ d = f1 i ∨ d = f2 i := by
    intro i d
    rw [hfs i]
    simp
  let l : Fin T.card → Fin 3 → F := fun i => A (f1 i) ⨯₃ A (f2 i)
  have hl0 : ∀ i, l i ≠ 0 := by
    intro i h
    have h' : A (f2 i) ⨯₃ A (f1 i) = 0 := by
      rw [← cross_anticomm]
      simp only [l] at h
      rw [h, neg_zero]
    obtain ⟨s, hs⟩ := cross_zero_prop _ _ h' (hA0 _)
    exact hAnp (f1 i) (f2 i) (hf12 i) s hs
  have hon : ∀ i d, d ∈ (eT i : Finset (Fin (b + 2))) → A d ⬝ᵥ l i = 0 := by
    intro i d hd
    rcases (hmem i d).mp hd with rfl | rfl
    · exact dot_self_cross _ _
    · exact dot_cross_self _ _
  have hoff : ∀ i d, d ∉ (eT i : Finset (Fin (b + 2))) → A d ⬝ᵥ l i ≠ 0 := by
    intro i d hd
    rw [hmem] at hd
    push Not at hd
    exact hAtri _ _ _ (hf12 i) (Ne.symm hd.1) (Ne.symm hd.2)
  let y : Fin T.card → Finset (Fin (Nat.card (Projectivization F (Fin 3 → F)))) :=
    fun i => (Finset.univ \ (eT i : Finset (Fin (b + 2)))).image idx
  let g : (Fin (Nat.card (Projectivization F (Fin 3 → F))) → Bool) → Bool :=
    fun x => decide (b + 1 ≤ (Finset.univ.filter (fun a => x (idx a) = true)).card)
  have hcard2 : ∀ i, (eT i : Finset (Fin (b + 2))).card = 2 := fun i =>
    (Finset.mem_powersetCard.mp (eT i).2).2
  refine ⟨Nat.card (Projectivization F (Fin 3 → F)), T.card, pt, l, y, g, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact Projectivization.rep_ne_zero _
  · intro p p' hpp c h
    have := (Projectivization.mk_eq_mk_iff' F (pt p') (pt p) (Projectivization.rep_ne_zero _)
      (Projectivization.rep_ne_zero _)).mpr ⟨c, h.symm⟩
    simp only [pt, Projectivization.mk_rep] at this
    exact hpp (e.symm.injective this).symm
  · intro v hv
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
    refine ⟨e (Projectivization.mk F v hv), ((u⁻¹ : Fˣ) : F), ?_⟩
    simp only [pt, Equiv.symm_apply_apply, ← hu]
    rw [Units.smul_def, smul_smul]
    simp
  · exact hl0
  · intro i j hij c h
    have hne : (eT i : Finset (Fin (b + 2))) ≠ eT j := fun h' => hij (eT.injective (Subtype.ext h'))
    obtain ⟨d, hdj, hdi⟩ : ∃ d, d ∈ (eT j : Finset (Fin (b + 2))) ∧ d ∉ (eT i : Finset (Fin (b + 2))) := by
      by_contra hc
      push Not at hc
      apply hne
      exact (Finset.eq_of_subset_of_card_le hc (by rw [hcard2, hcard2])).symm
    have h1 := hon j d hdj
    rw [h, dotProduct_smul, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h1 | h1
    · subst h1
      exact hl0 j (by rw [h, zero_smul])
    · exact hoff i d hdi h1
  · intro i
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ_sdiff, hcard2, Fintype.card_fin]
    omega
  · intro i p hp
    simp only [y, Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    rw [Ne, hdot]
    exact hoff i d hd
  · intro x x' hxx' hg
    simp only [g, decide_eq_true_eq] at hg ⊢
    refine le_trans hg (Finset.card_le_card ?_)
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact hxx' _ ha
  · intro i x hgx
    by_contra hcon
    push Not at hcon
    have h1 : x (idx (f1 i)) ≠ true := fun h => hcon _ h ((hdot _ _).mpr (hon i _ ((hmem i _).mpr (Or.inl rfl))))
    have h2 : x (idx (f2 i)) ≠ true := fun h => hcon _ h ((hdot _ _).mpr (hon i _ ((hmem i _).mpr (Or.inr rfl))))
    have hsub : Finset.univ.filter (fun a => x (idx a) = true) ⊆ Finset.univ \ (eT i : Finset (Fin (b + 2))) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hai
      rcases (hmem i a).mp hai with rfl | rfl
      · exact h1 ha
      · exact h2 ha
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ_sdiff, hcard2, Fintype.card_fin] at hc
    simp only [g, decide_eq_true_eq] at hgx
    omega
  · intro i
    have key : ∀ r r' : Fin (b + 2), r ≠ r' → r ∈ (eT i : Finset (Fin (b + 2))) →
        r' ∈ (eT i : Finset (Fin (b + 2))) →
        g (fun v => decide (v ∈ y i ∨ v = idx r)) = true := by
      intro r r' hrr' hr hr'
      simp only [g, decide_eq_true_eq]
      have hsub : Finset.univ.erase r' ⊆ Finset.univ.filter
          (fun a => idx a ∈ y i ∨ idx a = idx r) := by
        intro a ha
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hai : a ∈ (eT i : Finset (Fin (b + 2)))
        · right
          have h3 : (eT i : Finset (Fin (b + 2))).card = 2 := hcard2 i
          rw [Finset.card_eq_two] at h3
          obtain ⟨u, w, huw, hs⟩ := h3
          rw [hs] at hr hr' hai
          simp at hr hr' hai
          congr 1
          rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> rcases hai with rfl | rfl <;>
            simp_all
        · left
          simp only [y, Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact ⟨a, hai, rfl⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hc
      omega
    have hm1 : f1 i ∈ (eT i : Finset (Fin (b + 2))) := (hmem i _).mpr (Or.inl rfl)
    have hm2 : f2 i ∈ (eT i : Finset (Fin (b + 2))) := (hmem i _).mpr (Or.inr rfl)
    refine ⟨idx (f1 i), idx (f2 i), hidx_inj.ne (hf12 i), (hdot _ _).mpr (hon i _ hm1),
      (hdot _ _).mpr (hon i _ hm2), key _ _ (hf12 i) hm1 hm2, key _ _ (Ne.symm (hf12 i)) hm2 hm1⟩
  · simp only [T, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have := Nat.add_one_mul_choose_eq (b + 1) 1
    simp only [Nat.choose_one_right] at this
    rw [mul_comm 2]
    linarith

end PEqualNP.Outside.L_meta_989_aux

theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) :=
  ⟨PEqualNP.Outside.L_meta_989_aux.part1, PEqualNP.Outside.L_meta_989_aux.part2⟩
