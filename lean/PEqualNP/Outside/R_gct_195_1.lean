import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_gct_195_1
    (h1 : ∀ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
      (∀ t ∈ L, (∑ e : Fin 4 ↪ Fin 6, ∏ r, (1 + t) (r, e r)) = 360) →
      Module.finrank ℂ L = 9 →
      ∀ i : Fin 4,
        4 ≤ Module.finrank ℂ ((L ⊓ ⨅ r : {r : Fin 4 // r ≠ i},
          LinearMap.ker (LinearMap.funLeft ℂ ℂ (fun j => (r.val, j)))) : Submodule ℂ (Fin 4 × Fin 6 → ℂ)) → False)
    (h2 : ∀ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
      (∀ t ∈ L, (∑ e : Fin 4 ↪ Fin 6, ∏ r, (1 + t) (r, e r)) = 360) →
      Module.finrank ℂ L = 9 →
      ∀ i : Fin 4,
        Module.finrank ℂ ((L ⊓ ⨅ r : {r : Fin 4 // r ≠ i},
          LinearMap.ker (LinearMap.funLeft ℂ ℂ (fun j => (r.val, j)))) : Submodule ℂ (Fin 4 × Fin 6 → ℂ)) = 3 → False)
    (h3 : ∀ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
      (∀ t ∈ L, (∑ e : Fin 4 ↪ Fin 6, ∏ r, (1 + t) (r, e r)) = 360) →
      Module.finrank ℂ L = 9 →
      (∀ i : Fin 4,
        Module.finrank ℂ ((L ⊓ ⨅ r : {r : Fin 4 // r ≠ i},
          LinearMap.ker (LinearMap.funLeft ℂ ℂ (fun j => (r.val, j)))) : Submodule ℂ (Fin 4 × Fin 6 → ℂ)) ≤ 2) → False) :
    ∀ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) → Module.finrank ℂ L ≤ 8 := by
  intro L h
  classical
  let aO : (Fin 4 × Fin 6 → ℂ) → ℂ := fun M => ∑ e : Fin 4 ↪ Fin 6, ∏ r, M (r, e r)
  let cW : (Fin 4 × Fin 6 → ℂ) → ℂ := fun t => ∑ i : Fin 4, ∑ j, t (i, j)
  let pQ : (Fin 4 × Fin 6 → ℂ) → ℂ := fun t =>
    (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then t (a, j) * t (b, l) else 0)
  let pR : (Fin 4 × Fin 6 → ℂ) → ℂ := fun t =>
    (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0)
  let yW : (Fin 4 × Fin 6 → ℂ) → ℂ := fun t =>
    (∑ j, ∑ l, ∑ m, ∑ n,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
      t (0, j) * t (1, l) * t (2, m) * t (3, n))
  have cK : ∀ M : Fin 4 × Fin 6 → ℂ,
      aO M = ∑ j, ∑ l, ∑ m, ∑ n,
        if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
        M (0, j) * M (1, l) * M (2, m) * M (3, n) := by
    intro M
    classical
    let u (z : Fin 4 → Fin 6) := ∏ r, M (r, z r)
    have A : aO M = ∑ z : Fin 4 → Fin 6, if Function.Injective z then u z else 0 := by
      let E := Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 6)
      change (∑ e : Fin 4 ↪ Fin 6, u e) = _
      rw [← E.sum_comp (fun e : Fin 4 ↪ Fin 6 => u e), ← Finset.sum_filter]
      exact (Finset.sum_subtype _ (by simp) u).symm
    let yH : (Fin 6 × Fin 6 × Fin 6 × Fin 6) ≃ (Fin 4 → Fin 6) :=
      { toFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
        invFun := fun z => (z 0, z 1, z 2, z 3)
        left_inv := fun _ => rfl
        right_inv := fun z => by ext i; fin_cases i <;> rfl }
    rw [A, ← yH.sum_comp (fun z => if Function.Injective z then u z else 0)]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    let z := yH (a, b, c, d)
    have p : z 0 = a := rfl
    have q : z 1 = b := rfl
    have s : z 2 = c := rfl
    have t : z 3 = d := rfl
    have f : Function.Injective z ↔ ¬(a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) := by
      constructor
      · intro o
        have h (i j : Fin 4) (g : i ≠ j) : z i ≠ z j := fun h => g (o h)
        exact not_or_intro (h 0 1 (by decide)) (not_or_intro (h 0 2 (by decide))
          (not_or_intro (h 0 3 (by decide)) (not_or_intro (h 1 2 (by decide))
            (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
      · intro g i j v
        simp only [not_or] at g
        fin_cases i <;> fin_cases j <;> first | rfl | grind
    change (if Function.Injective z then u z else 0) = _
    by_cases g : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d
    · have k : ¬Function.Injective z := fun h => f.mp h g
      rw [ite_eq_right k, ite_eq_left g]
    · rw [ite_eq_left (f.mpr g), ite_eq_right g]
      change (∏ r, M (r, z r)) = _
      simp [Fin.prod_univ_succ, p, q, s, t, mul_assoc]
  have aO_one : aO (1 : Fin 4 × Fin 6 → ℂ) = 360 := by
    have h' : aO (1 : Fin 4 × Fin 6 → ℂ) = (Fintype.card (Fin 4 ↪ Fin 6) : ℂ) := by
      simp [aO]
    have hc : Fintype.card (Fin 4 ↪ Fin 6) = 360 := by
      rw [Fintype.card_embedding_eq]
      decide
    rw [h', hc]
    norm_num
  have oD : ∀ t : Fin 4 × Fin 6 → ℂ,
      aO (1 + t) = 360 + 60 * cW t + 12 * pQ t + 3 * pR t + yW t := by
    intro t
    rw [cK]
    simp(config := {decide := true}) only [cW, pQ, pR, yW, Fin.sum_univ_six,
      Fin.sum_univ_four, Pi.add_apply, Pi.one_apply, ite_true, ite_false, add_zero,
      zero_add]
    ring
  have d : ∀ t ∈ L, aO (1 + t) = 360 := by
    intro t ht
    obtain ⟨k1, k2, k3, k4⟩ := h t ht
    rw [oD]
    simp only [cW, pQ, pR, yW] at k1 k2 k3 k4 ⊢
    rw [k1, k2, k3, k4]
    ring
  have aAl : ∀ (S : Submodule ℂ (Fin 4 × Fin 6 → ℂ)), 9 ≤ Module.finrank ℂ S →
      ∃ T : Submodule ℂ (Fin 4 × Fin 6 → ℂ), T ≤ S ∧ Module.finrank ℂ T = 9 := by
    intro S a
    obtain ⟨f, b⟩ := exists_linearIndependent_of_le_finrank (R := ℂ) (M := S) a
    have c : LinearIndependent ℂ (fun i => (S.subtype (f i) : Fin 4 × Fin 6 → ℂ)) :=
      b.map' S.subtype (Submodule.ker_subtype S)
    refine ⟨Submodule.span ℂ (Set.range fun i => (S.subtype (f i) : Fin 4 × Fin 6 → ℂ)), ?_, ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (f i).2
    · rw [finrank_span_eq_card c]
      simp
  have u_sum_le : ∀ (S : Submodule ℂ (Fin 4 × Fin 6 → ℂ)),
      ∑ i, Module.finrank ℂ ((S ⊓ ⨅ r : {r : Fin 4 // r ≠ i},
        LinearMap.ker (LinearMap.funLeft ℂ ℂ (fun j => (r.val, j)))) : Submodule ℂ (Fin 4 × Fin 6 → ℂ)) ≤
      Module.finrank ℂ S := by
    intro S
    classical
    let Z : Fin 4 → Submodule ℂ (Fin 4 × Fin 6 → ℂ) := fun i =>
      S ⊓ ⨅ r : {r : Fin 4 // r ≠ i},
        LinearMap.ker (LinearMap.funLeft ℂ ℂ (fun j => (r.val, j)))
    let u : Fin 4 → ℕ := fun i => Module.finrank ℂ (Z i)
    show ∑ i, u i ≤ Module.finrank ℂ S
    let Φ : (Π i : Fin 4, Z i) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) :=
      ∑ i : Fin 4, (Z i).subtype.comp (LinearMap.proj i)
    have hΦ (v : Π i : Fin 4, Z i) : Φ v = ∑ i, (v i : Fin 4 × Fin 6 → ℂ) := by
      simp [Φ]
    have hmem (v : Π i : Fin 4, Z i) : Φ v ∈ S := by
      rw [hΦ]
      exact Submodule.sum_mem S (fun i _ => (v i).2.1)
    let Ψ : (Π i : Fin 4, Z i) →ₗ[ℂ] S := Φ.codRestrict S hmem
    have hrow : ∀ (v : Π i : Fin 4, Z i) (k r : Fin 4) (c : Fin 6),
        r ≠ k → (v k : Fin 4 × Fin 6 → ℂ) (r, c) = 0 := by
      intro v k r c hrk
      have h1 : (v k : Fin 4 × Fin 6 → ℂ) ∈
          ⨅ s : {s : Fin 4 // s ≠ k},
            LinearMap.ker (LinearMap.funLeft ℂ ℂ (fun j => (s.val, j))) :=
        (Submodule.mem_inf.mp (v k).2).2
      have h2 : (v k : Fin 4 × Fin 6 → ℂ) ∈
          LinearMap.ker (LinearMap.funLeft ℂ ℂ (fun j => (r, j))) :=
        (Submodule.mem_iInf _).mp h1 ⟨r, hrk⟩
      have h3 : LinearMap.funLeft ℂ ℂ (fun j : Fin 6 => (r, j))
          (v k : Fin 4 × Fin 6 → ℂ) = 0 := by
        simpa only [LinearMap.mem_ker] using h2
      simpa only [LinearMap.funLeft_apply, Pi.zero_apply] using congrFun h3 c
    have hinj : Function.Injective Ψ := by
      intro v w h
      have h1 : Ψ v = Ψ w := h
      have h0 : Φ (v - w) = 0 := by
        have h3 : Ψ (v - w) = 0 := by rw [map_sub, h1, sub_self]
        have h4 := congrArg Subtype.val h3
        simpa [Ψ] using h4
      have hz : ∀ (i : Fin 4) (c : Fin 6),
          (v i : Fin 4 × Fin 6 → ℂ) (i, c) = (w i : Fin 4 × Fin 6 → ℂ) (i, c) := by
        intro i c
        have hs2 : (∑ k, ((v - w : Π i : Fin 4, Z i) k : Fin 4 × Fin 6 → ℂ)) = 0 := by
          rw [← hΦ]
          exact h0
        have hs3 : ∑ k, ((v - w : Π i : Fin 4, Z i) k : Fin 4 × Fin 6 → ℂ) (i, c) = 0 := by
          have h' := congrFun hs2 (i, c)
          simpa only [Finset.sum_apply, Pi.zero_apply] using h'
        have hsingle : ∑ k, ((v - w : Π i : Fin 4, Z i) k : Fin 4 × Fin 6 → ℂ) (i, c) =
            ((v - w : Π i : Fin 4, Z i) i : Fin 4 × Fin 6 → ℂ) (i, c) := by
          refine Finset.sum_eq_single i (fun k _ hk => ?_)
            (fun h => absurd (Finset.mem_univ i) h)
          exact hrow (v - w) k i c hk.symm
        rw [hsingle] at hs3
        have hsub : (v i : Fin 4 × Fin 6 → ℂ) (i, c) -
            (w i : Fin 4 × Fin 6 → ℂ) (i, c) = 0 := by
          simpa only [Pi.sub_apply, Submodule.coe_sub] using hs3
        exact sub_eq_zero.mp hsub
      funext i
      apply Subtype.ext
      funext ⟨r, c⟩
      by_cases hri : r = i
      · subst hri
        exact hz r c
      · have hv : (v i : Fin 4 × Fin 6 → ℂ) (r, c) = 0 := hrow v i r c hri
        have hw : (w i : Fin 4 × Fin 6 → ℂ) (r, c) = 0 := hrow w i r c hri
        rw [hv, hw]
    have hfin : Module.finrank ℂ (Π i : Fin 4, Z i) = ∑ i, u i := by
      rw [Module.finrank_pi_fintype]
    have hker : Module.finrank ℂ (LinearMap.ker Ψ) = 0 := by
      rw [LinearMap.ker_eq_bot.mpr hinj]
      simp
    have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
    have hle : Module.finrank ℂ (LinearMap.range Ψ) ≤ Module.finrank ℂ S := by
      have h := Submodule.finrank_mono (show LinearMap.range Ψ ≤ ⊤ from le_top)
      simpa using h
    have h1 : Module.finrank ℂ (LinearMap.range Ψ) = ∑ i, u i := by omega
    calc ∑ i, u i = Module.finrank ℂ (LinearMap.range Ψ) := h1.symm
      _ ≤ Module.finrank ℂ S := hle
  have aDe : ∀ (S : Submodule ℂ (Fin 4 × Fin 6 → ℂ)),
      (∀ t ∈ S, aO (1 + t) = 360) → Module.finrank ℂ S ≤ 8 := by
    intro S dS
    by_contra! l
    obtain ⟨T, z, e⟩ := aAl S (by omega : 9 ≤ Module.finrank ℂ S)
    have dT : ∀ t ∈ T, aO (1 + t) = 360 := fun x hx => dS x (z hx)
    let Z : Fin 4 → Submodule ℂ (Fin 4 × Fin 6 → ℂ) := fun i =>
      T ⊓ ⨅ r : {r : Fin 4 // r ≠ i},
        LinearMap.ker (LinearMap.funLeft ℂ ℂ (fun j => (r.val, j)))
    let u : Fin 4 → ℕ := fun i => Module.finrank ℂ (Z i)
    by_cases hh : ∃ i, 3 ≤ u i
    · obtain ⟨i, c⟩ := hh
      by_cases y : 4 ≤ u i
      · exact h1 T dT e i y
      · exact h2 T dT e i (by
          have h3' : u i = 3 := by omega
          exact h3')
    · exact h3 T dT e (fun i => by
        have hi : ¬ 3 ≤ u i := not_exists.mp hh i
        have h2' : u i ≤ 2 := by omega
        exact h2')
  exact aDe L d
