import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_7107_1
  (edgeFirst : let E : List (Fin 10 × Fin 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
    ∀ ws : List ((Fin 10 → Bool) → Bool), ws.length ≤ 18 →
    (∀ k : Fin ws.length,
      let p := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) x => x i)) ++
        [fun x => x 0 && x 1] ++ ws.take k.val
      ws.get k ∉ p ∧
        ∃ a ∈ p, ∃ b ∈ p, ws.get k = (fun x => a x && b x) ∨ ws.get k = (fun x => a x || b x)) →
    (∀ w ∈ ws, ∀ i j : Fin 10, i ≠ j →
      ((i, j) ∉ E ∧ (j, i) ∉ E → w ≠ fun x => x i && x j) ∧
      (w ≠ fun x => x i || x j)) →
    (∃ w ∈ ws, ∃ e ∈ E, ∀ z : Fin 10, w (fun i => decide (i = z)) = decide (z = e.1 ∨ z = e.2)) →
    (∃ h ∈ ws, ∃ u : Fin 10, ∀ z : Fin 10, h (fun i => decide (i = z)) = decide (z = u)) →
    (fun x => E.any fun e => x e.1 && x e.2) ∉ ws)
  (nonedgeFirst : let E : List (Fin 10 × Fin 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
    ∀ ws : List ((Fin 10 → Bool) → Bool), ws.length ≤ 18 →
    (∀ k : Fin ws.length,
      let p := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) x => x i)) ++
        [fun x => x 0 && x 1] ++ ws.take k.val
      ws.get k ∉ p ∧
        ∃ a ∈ p, ∃ b ∈ p, ws.get k = (fun x => a x && b x) ∨ ws.get k = (fun x => a x || b x)) →
    (∀ w ∈ ws, ∀ i j : Fin 10, i ≠ j →
      ((i, j) ∉ E ∧ (j, i) ∉ E → w ≠ fun x => x i && x j) ∧
      (w ≠ fun x => x i || x j)) →
    (∃ w ∈ ws, ∃ u v : Fin 10, u ≠ v ∧ (u, v) ∉ E ∧ (v, u) ∉ E ∧
      ∀ z : Fin 10, w (fun i => decide (i = z)) = decide (z = u ∨ z = v)) →
    (∃ h ∈ ws, ∃ u : Fin 10, ∀ z : Fin 10, h (fun i => decide (i = z)) = decide (z = u)) →
    (fun x => E.any fun e => x e.1 && x e.2) ∉ ws) :
  (have x1 : List (Fin (10 : ℕ) × Fin (10 : ℕ)) := [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))]; ∀ (x2 : List ((Fin (10 : ℕ) → Bool) → Bool)),   x2.length ≤ (18 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List ((Fin (10 : ℕ) → Bool) → Bool) := ((fun (x5 : Fin (10 : ℕ) → Bool) => Bool.false) :: (fun (x5 : Fin (10 : ℕ) → Bool) => Bool.true) :: List.ofFn fun (x5 : Fin (10 : ℕ)) (x6 : Fin (10 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ))] ++ List.take (↑x4) x2;         x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, (x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 && x7 x8) ∨ x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 || x7 x8) →       (∀ x5 ∈ x2, ∀ (x7 x8 : Fin (10 : ℕ)), x7 ≠ x8 → (¬(x1.any fun (x10 : Fin (10 : ℕ) × Fin (10 : ℕ)) => Decidable.decide ((x7, x8) = x10 ∨ (x8, x7) = x10)) = Bool.true → x5 ≠ fun (x11 : Fin (10 : ℕ) → Bool) => x11 x7 && x11 x8) ∧ x5 ≠ fun (x10 : Fin (10 : ℕ) → Bool) => x10 x7 || x10 x8) → (fun (x6 : Fin (10 : ℕ) → Bool) => x1.any fun (x7 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x6 x7.1 && x6 x7.2) ∉ x2) := by
  intro x1 ws hlen hstep hforb hP
  let P : (Fin 10 → Bool) → Bool := fun x => x1.any fun e => x e.1 && x e.2
  let unit (v : Fin 10) : Fin 10 → Bool := fun i => decide (i = v)
  let pair (u v : Fin 10) : Fin 10 → Bool := fun i => decide (i = u ∨ i = v)
  let A1 (f : (Fin 10 → Bool) → Bool) : Finset (Fin 10) :=
    Finset.univ.filter (fun v => f (unit v) = true)
  let Eset : Finset (Fin 10 × Fin 10) := x1.toFinset
  let M2 (f : (Fin 10 → Bool) → Bool) : Finset (Fin 10 × Fin 10) :=
    Eset.filter (fun e => f (pair e.1 e.2) = true ∧ f (unit e.1) = false ∧ f (unit e.2) = false)
  let c0 : (Fin 10 → Bool) → Bool := fun _ => false
  let c1 : (Fin 10 → Bool) → Bool := fun _ => true
  let S0nt : List ((Fin 10 → Bool) → Bool) :=
    (List.ofFn fun (i : Fin 10) x => x i) ++ [fun x => x 0 && x 1]
  let pref (k : ℕ) : List ((Fin 10 → Bool) → Bool) :=
    (c0 :: c1 :: List.ofFn fun (i : Fin 10) x => x i) ++ [fun x => x 0 && x 1] ++ ws.take k
  let prefnt (k : ℕ) : List ((Fin 10 → Bool) → Bool) := S0nt ++ ws.take k
  have pref_eq (k : ℕ) : pref k = c0 :: c1 :: prefnt k := by
    simp [pref, prefnt, S0nt, List.cons_append]
  have Eset_card : Eset.card = 15 := by decide
  have deg_bound (u : Fin 10) : (Eset.filter (fun e => e.1 = u ∨ e.2 = u)).card = 3 := by
    fin_cases u <;> decide
  have pair_bound (u v : Fin 10) :
      (Eset.filter (fun e => (e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u))).card ≤ 1 := by
    fin_cases u <;> fin_cases v <;> decide
  have A1_P : A1 P = ∅ := by
    ext v
    simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    fin_cases v <;> decide
  have M2_P : M2 P = Eset := by
    ext e
    simp only [M2, Finset.mem_filter, and_iff_left_iff_imp]
    intro he
    have he' : e ∈ x1 := List.mem_toFinset.mp he
    rcases e with ⟨a, b⟩
    have hp : P (pair a b) = true := by
      simp only [P, List.any_eq_true]
      exact ⟨(a, b), he', by simp [pair]⟩
    have hu1 : P (unit a) = false := by
      revert he'
      fin_cases a <;> fin_cases b <;> decide
    have hu2 : P (unit b) = false := by
      revert he'
      fin_cases a <;> fin_cases b <;> decide
    exact ⟨hp, hu1, hu2⟩
  have A1_and (a b : (Fin 10 → Bool) → Bool) :
      A1 (fun x => a x && b x) = A1 a ∩ A1 b := by
    ext v
    simp [A1, Bool.and_eq_true]
  have A1_or (a b : (Fin 10 → Bool) → Bool) :
      A1 (fun x => a x || b x) = A1 a ∪ A1 b := by
    ext v
    simp [A1, Bool.or_eq_true]
  have M2_or_sub (a b : (Fin 10 → Bool) → Bool) :
      M2 (fun x => a x || b x) ⊆ M2 a ∪ M2 b := by
    intro e he
    simp only [M2, Finset.mem_filter, Bool.or_eq_true, Bool.or_eq_false_iff] at he
    rcases he with ⟨heE, haorb, ⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩
    rcases haorb with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heE, ha, ha1, ha2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heE, hb, hb1, hb2⟩)
  have M2_and_mem (a b : (Fin 10 → Bool) → Bool) (e : Fin 10 × Fin 10)
      (he : e ∈ M2 (fun x => a x && b x)) :
      (e ∈ M2 a ∨ e.1 ∈ A1 a ∨ e.2 ∈ A1 a) ∧ (e ∈ M2 b ∨ e.1 ∈ A1 b ∨ e.2 ∈ A1 b) := by
    simp only [M2, Finset.mem_filter, Bool.and_eq_true] at he
    rcases he with ⟨heE, ⟨haP, hbP⟩, h1, h2⟩
    constructor
    · by_cases ha1 : a (unit e.1) = true
      · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha1⟩))
      · by_cases ha2 : a (unit e.2) = true
        · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha2⟩))
        · exact Or.inl (Finset.mem_filter.mpr ⟨heE, haP, Bool.eq_false_iff.mpr ha1, Bool.eq_false_iff.mpr ha2⟩)
    · by_cases hb1 : b (unit e.1) = true
      · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb1⟩))
      · by_cases hb2 : b (unit e.2) = true
        · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb2⟩))
        · exact Or.inl (Finset.mem_filter.mpr ⟨heE, hbP, Bool.eq_false_iff.mpr hb1, Bool.eq_false_iff.mpr hb2⟩)
  have M2_and_empty_left (a b : (Fin 10 → Bool) → Bool) (ha : A1 a = ∅) :
      M2 (fun x => a x && b x) ⊆ M2 a := by
    intro e he
    have hm := (M2_and_mem a b e he).1
    rcases hm with h | h | h
    · exact h
    · simp [ha] at h
    · simp [ha] at h
  have M2_and_empty_right (a b : (Fin 10 → Bool) → Bool) (hb : A1 b = ∅) :
      M2 (fun x => a x && b x) ⊆ M2 b := by
    intro e he
    have hm := (M2_and_mem a b e he).2
    rcases hm with h | h | h
    · exact h
    · simp [hb] at h
    · simp [hb] at h
  have M2_and_same (a b : (Fin 10 → Bool) → Bool) (u : Fin 10)
      (ha : A1 a = {u}) (hb : A1 b = {u}) :
      M2 (fun x => a x && b x) ⊆ M2 a := by
    intro e he
    have he' := he
    simp only [M2, Finset.mem_filter] at he'
    have hau : a (unit u) = true := by
      have hu : u ∈ A1 a := by rw [ha]; exact Finset.mem_singleton_self u
      exact (Finset.mem_filter.mp hu).2
    have hbu : b (unit u) = true := by
      have hu : u ∈ A1 b := by rw [hb]; exact Finset.mem_singleton_self u
      exact (Finset.mem_filter.mp hu).2
    have hne1 : e.1 ≠ u := by
      intro h
      rw [h, hau, hbu] at he'
      simp at he'
    have hne2 : e.2 ≠ u := by
      intro h
      rw [h, hau, hbu] at he'
      simp at he'
    rcases (M2_and_mem a b e he).1 with h | h | h
    · exact h
    · rw [ha, Finset.mem_singleton] at h; exact absurd h hne1
    · rw [ha, Finset.mem_singleton] at h; exact absurd h hne2
  have M2_and_deg (a b : (Fin 10 → Bool) → Bool) (u : Fin 10) (ha : A1 a = {u}) :
      M2 (fun x => a x && b x) ⊆ M2 a ∪ Eset.filter (fun e => e.1 = u ∨ e.2 = u) := by
    intro e he
    have heE : e ∈ Eset := (Finset.mem_filter.mp he).1
    rcases (M2_and_mem a b e he).1 with h | h | h
    · exact Finset.mem_union_left _ h
    · rw [ha, Finset.mem_singleton] at h
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heE, Or.inl h⟩)
    · rw [ha, Finset.mem_singleton] at h
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heE, Or.inr h⟩)
  have M2_and_pair (a b : (Fin 10 → Bool) → Bool) (u v : Fin 10) (huv : u ≠ v)
      (ha : A1 a = {u}) (hb : A1 b = {v}) :
      M2 (fun x => a x && b x) ⊆
        M2 a ∪ M2 b ∪ Eset.filter (fun e => (e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u)) := by
    intro e he
    have heE : e ∈ Eset := (Finset.mem_filter.mp he).1
    have hmem := M2_and_mem a b e he
    rcases hmem.1 with h1 | h1 | h1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
    · rw [ha, Finset.mem_singleton] at h1
      rcases hmem.2 with h2 | h2 | h2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
      · rw [hb, Finset.mem_singleton] at h2
        exact absurd (h1.symm.trans h2) huv
      · rw [hb, Finset.mem_singleton] at h2
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heE, Or.inl ⟨h1, h2⟩⟩)
    · rw [ha, Finset.mem_singleton] at h1
      rcases hmem.2 with h2 | h2 | h2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
      · rw [hb, Finset.mem_singleton] at h2
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heE, Or.inr ⟨h2, h1⟩⟩)
      · rw [hb, Finset.mem_singleton] at h2
        exact absurd (h1.symm.trans h2) huv
  have S0nt_props (f : (Fin 10 → Bool) → Bool) (hf : f ∈ S0nt) :
      ((A1 f = ∅ ∧ f = fun x => x 0 && x 1) ∨
       (∃ i : Fin 10, A1 f = {i} ∧ f = fun x => x i)) ∧
      (A1 f = ∅ → (M2 f).card = 1) ∧
      ((A1 f).card = 1 → (M2 f).card = 0) ∧
      (A1 f).card ≤ 1 := by
    simp only [S0nt, List.mem_append, List.mem_ofFn, List.mem_singleton] at hf
    rcases hf with ⟨i, rfl⟩ | rfl
    · have hAi : A1 (fun x => x i) = {i} := by
        ext v
        simp only [A1, unit, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          decide_eq_true_eq]
        exact eq_comm
      have hMi : M2 (fun x => x i) = ∅ := by
        ext e
        simp only [M2, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ hpair h1 h2
        simp only [pair, decide_eq_true_eq] at hpair
        simp only [unit, decide_eq_false_iff_not] at h1 h2
        rcases hpair with rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
      refine ⟨Or.inr ⟨i, hAi, rfl⟩, ?_, ?_, ?_⟩
      · intro h0; rw [hAi] at h0; exact absurd h0 (Finset.singleton_ne_empty i)
      · intro _; simp [hMi]
      · simp [hAi]
    · have hA0 : A1 (fun x => x 0 && x 1) = ∅ := by
        ext v
        simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        fin_cases v <;> decide
      have hM0 : M2 (fun x => x 0 && x 1) = {(0, 1)} := by
        ext e
        rcases e with ⟨a, b⟩
        simp only [M2, Eset, List.mem_toFinset, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
        fin_cases a <;> fin_cases b <;> decide
      refine ⟨Or.inl ⟨hA0, rfl⟩, ?_, ?_, ?_⟩
      · intro _; simp [hM0]
      · intro h1; simp [hA0] at h1
      · simp [hA0]
  have step_nontriv (k : ℕ) (hk : k < ws.length) :
      ∃ a ∈ prefnt k, ∃ b ∈ prefnt k, a ≠ b ∧
        (ws[k] = (fun x => a x && b x) ∨ ws[k] = (fun x => a x || b x)) := by
    have hs := hstep ⟨k, hk⟩
    have hp : ((fun (x5 : Fin 10 → Bool) => Bool.false) :: (fun (x5 : Fin 10 → Bool) => Bool.true) ::
        List.ofFn fun (x5 : Fin 10) (x6 : Fin 10 → Bool) => x6 x5) ++
        [fun (x5 : Fin 10 → Bool) => x5 0 && x5 1] ++ List.take k ws = pref k := rfl
    rw [hp, pref_eq] at hs
    rcases hs with ⟨hnot, a, ha, b, hb, hform⟩
    have hc0 : c0 ∈ c0 :: c1 :: prefnt k := List.mem_cons_self
    have hc1 : c1 ∈ c0 :: c1 :: prefnt k := List.mem_cons_of_mem _ List.mem_cons_self
    have gw : ws.get ⟨k, hk⟩ = ws[k] := rfl
    rw [gw] at hnot hform
    have ha_nt : a ∈ prefnt k := by
      rcases List.mem_cons.mp ha with rfl | ha'
      · exfalso
        rcases hform with hform | hform
        · have hEq : ws[k] = c0 := by funext x; rw [hform]; rfl
          exact hnot (hEq ▸ hc0)
        · have hEq : ws[k] = b := by funext x; rw [hform]; rfl
          exact hnot (hEq ▸ hb)
      · rcases List.mem_cons.mp ha' with rfl | ha''
        · exfalso
          rcases hform with hform | hform
          · have hEq : ws[k] = b := by funext x; rw [hform]; rfl
            exact hnot (hEq ▸ hb)
          · have hEq : ws[k] = c1 := by funext x; rw [hform]; rfl
            exact hnot (hEq ▸ hc1)
        · exact ha''
    have hb_nt : b ∈ prefnt k := by
      rcases List.mem_cons.mp hb with rfl | hb'
      · exfalso
        rcases hform with hform | hform
        · have hEq : ws[k] = c0 := by funext x; rw [hform]; simp [c0]
          exact hnot (hEq ▸ hc0)
        · have hEq : ws[k] = a := by funext x; rw [hform]; simp [c0]
          exact hnot (hEq ▸ ha)
      · rcases List.mem_cons.mp hb' with rfl | hb''
        · exfalso
          rcases hform with hform | hform
          · have hEq : ws[k] = a := by funext x; rw [hform]; simp [c1]
            exact hnot (hEq ▸ ha)
          · have hEq : ws[k] = c1 := by funext x; rw [hform]; simp [c1]
            exact hnot (hEq ▸ hc1)
        · exact hb''
    have hab : a ≠ b := by
      intro hab
      subst hab
      rcases hform with hform | hform
      · have hEq : ws[k] = a := by funext x; rw [hform]; exact Bool.and_self (a x)
        exact hnot (hEq ▸ ha)
      · have hEq : ws[k] = a := by funext x; rw [hform]; exact Bool.or_self (a x)
        exact hnot (hEq ▸ ha)
    exact ⟨a, ha_nt, b, hb_nt, hab, hform⟩
  by_cases hall : ∀ g ∈ ws, (A1 g).card ≤ 1
  · let Ecov (k : ℕ) : Finset (Fin 10 × Fin 10) := ((prefnt k).map M2).foldr (· ∪ ·) ∅
    have mem_foldr (L : List ((Fin 10 → Bool) → Bool)) (e : Fin 10 × Fin 10) :
        e ∈ (L.map M2).foldr (· ∪ ·) ∅ ↔ ∃ f ∈ L, e ∈ M2 f := by
      induction L with
      | nil => simp
      | cons f L ih =>
        simp only [List.map_cons, List.foldr_cons, Finset.mem_union, ih, List.mem_cons]
        constructor
        · rintro (h | ⟨g, hg, hmg⟩)
          · exact ⟨f, Or.inl rfl, h⟩
          · exact ⟨g, Or.inr hg, hmg⟩
        · rintro ⟨g, rfl | hg, hmg⟩
          · exact Or.inl hmg
          · exact Or.inr ⟨g, hg, hmg⟩
    have mem_Ecov (k : ℕ) (e : Fin 10 × Fin 10) :
        e ∈ Ecov k ↔ ∃ f ∈ prefnt k, e ∈ M2 f := mem_foldr (prefnt k) e
    have Ecov_zero : Ecov 0 = {(0, 1)} := by
      ext e
      rw [mem_Ecov]
      simp only [prefnt, List.take_zero, List.append_nil]
      constructor
      · rintro ⟨f, hf, hme⟩
        rcases (S0nt_props f hf).1 with ⟨_, rfl⟩ | ⟨i, hAi, _⟩
        · have hM0 : M2 (fun x => x 0 && x 1) = {(0, 1)} := by
            ext p
            rcases p with ⟨a, b⟩
            simp only [M2, Eset, List.mem_toFinset, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
            fin_cases a <;> fin_cases b <;> decide
          rwa [hM0] at hme
        · have hMi0 : (M2 f).card = 0 := (S0nt_props f hf).2.2.1 (by simp [hAi])
          rw [Finset.card_eq_zero.mp hMi0] at hme
          exact absurd hme (Finset.notMem_empty e)
      · intro he
        refine ⟨fun x => x 0 && x 1, by simp [S0nt], ?_⟩
        have hM0 : M2 (fun x => x 0 && x 1) = {(0, 1)} := by
          ext p
          rcases p with ⟨a, b⟩
          simp only [M2, Eset, List.mem_toFinset, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
          fin_cases a <;> fin_cases b <;> decide
        rwa [hM0]
    have Ecov_succ (k : ℕ) (hk : k < ws.length) : Ecov (k + 1) = Ecov k ∪ M2 (ws[k]) := by
      ext e
      simp only [mem_Ecov, Finset.mem_union]
      have htake : prefnt (k + 1) = prefnt k ++ [ws[k]] := by
        simp only [prefnt, List.take_succ_eq_append_getElem hk, List.append_assoc]
      rw [htake]
      constructor
      · rintro ⟨f, hf, hmf⟩
        rcases List.mem_append.mp hf with hf | hf
        · exact Or.inl ⟨f, hf, hmf⟩
        · rw [List.mem_singleton] at hf
          exact Or.inr (hf ▸ hmf)
      · rintro (⟨f, hf, hmf⟩ | hmf)
        · exact ⟨f, List.mem_append_left _ hf, hmf⟩
        · exact ⟨ws[k], List.mem_append_right _ (List.mem_singleton_self _), hmf⟩
    have prefnt_A1_le_one (k : ℕ) (f : (Fin 10 → Bool) → Bool) (hf : f ∈ prefnt k) :
        (A1 f).card ≤ 1 := by
      rcases List.mem_append.mp hf with hf0 | hfw
      · exact (S0nt_props f hf0).2.2.2
      · exact hall f (List.mem_of_mem_take hfw)
    let nonc (k : ℕ) : ℕ :=
      ((List.range k).filter (fun j => decide (Ecov (j + 1) = Ecov j))).length
    have nonc_zero : nonc 0 = 0 := by simp [nonc]
    have nonc_succ (k : ℕ) :
        nonc (k + 1) = nonc k + if Ecov (k + 1) = Ecov k then 1 else 0 := by
      simp only [nonc, List.range_succ, List.filter_append, List.length_append]
      by_cases h : Ecov (k + 1) = Ecov k
      · simp [h]
      · simp [h]
    have nonc_mono (k1 k2 : ℕ) (h : k1 ≤ k2) : nonc k1 ≤ nonc k2 := by
      induction h with
      | refl => exact le_rfl
      | step _ ih =>
        rw [nonc_succ]
        omega
    have cov_plus_nonc (k : ℕ) (hk : k ≤ ws.length) : (Ecov k).card + nonc k ≤ k + 1 := by
      induction k with
      | zero =>
        rw [Ecov_zero, nonc_zero]
        simp
      | succ k ih =>
        have hk' : k < ws.length := by omega
        have ih' := ih (by omega)
        by_cases heq : Ecov (k + 1) = Ecov k
        · rw [heq]; simp [nonc_succ, heq]
          omega
        · simp [nonc_succ, heq]
          have hEsub : ∃ u v : Fin 10, Ecov (k + 1) ⊆
              Ecov k ∪ Eset.filter (fun e => (e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u)) := by
            obtain ⟨a, ha, b, hb, _, hform⟩ := step_nontriv k hk'
            have hMa : M2 a ⊆ Ecov k := fun e he => (mem_Ecov k e).mpr ⟨a, ha, he⟩
            have hMb : M2 b ⊆ Ecov k := fun e he => (mem_Ecov k e).mpr ⟨b, hb, he⟩
            have hne : ∃ e, e ∈ M2 ws[k] ∧ e ∉ Ecov k := by
              by_contra hnone
              push Not at hnone
              apply heq
              rw [Ecov_succ k hk']
              ext e
              simp only [Finset.mem_union, or_iff_left_iff_imp]
              exact hnone e
            obtain ⟨e0, he0M, he0N⟩ := hne
            rcases hform with hform | hform
            · have ha1 : (A1 a).card = 1 := by
                have hle := prefnt_A1_le_one k a ha
                by_contra hne1
                have h0 : A1 a = ∅ := Finset.card_eq_zero.mp (by omega)
                exact he0N (hMa (M2_and_empty_left a b h0 (hform ▸ he0M)))
              have hb1 : (A1 b).card = 1 := by
                have hle := prefnt_A1_le_one k b hb
                by_contra hne1
                have h0 : A1 b = ∅ := Finset.card_eq_zero.mp (by omega)
                exact he0N (hMb (M2_and_empty_right a b h0 (hform ▸ he0M)))
              obtain ⟨u, hau⟩ := Finset.card_eq_one.mp ha1
              obtain ⟨v, hbv⟩ := Finset.card_eq_one.mp hb1
              have huv : u ≠ v := by
                intro huv
                subst huv
                exact he0N (hMa (M2_and_same a b u hau hbv (hform ▸ he0M)))
              refine ⟨u, v, ?_⟩
              rw [Ecov_succ k hk', hform]
              intro e he
              rcases Finset.mem_union.mp he with he | he
              · exact Finset.mem_union_left _ he
              · have hp := M2_and_pair a b u v huv hau hbv he
                rcases Finset.mem_union.mp hp with hp | hp
                · rcases Finset.mem_union.mp hp with hp | hp
                  · exact Finset.mem_union_left _ (hMa hp)
                  · exact Finset.mem_union_left _ (hMb hp)
                · exact Finset.mem_union_right _ hp
            · exfalso
              have hsub : M2 ws[k] ⊆ M2 a ∪ M2 b := hform ▸ M2_or_sub a b
              rcases Finset.mem_union.mp (hsub he0M) with h | h
              · exact he0N (hMa h)
              · exact he0N (hMb h)
          obtain ⟨u, v, hEsub⟩ := hEsub
          have hcard : (Ecov (k + 1)).card ≤ (Ecov k).card + 1 := by
            calc (Ecov (k + 1)).card
                ≤ (Ecov k ∪ Eset.filter (fun e => (e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u))).card :=
                  Finset.card_le_card hEsub
              _ ≤ (Ecov k).card + (Eset.filter (fun e => (e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u))).card :=
                  Finset.card_union_le _ _
              _ ≤ (Ecov k).card + 1 := Nat.add_le_add_left (pair_bound u v) _
          omega
    have hP_pref : P ∈ prefnt ws.length := by
      dsimp only [prefnt]
      rw [List.take_of_length_le le_rfl]
      exact List.mem_append_right _ hP
    have hPcov : Eset ⊆ Ecov ws.length := by
      intro e he
      rw [← M2_P] at he
      exact (mem_Ecov ws.length e).mpr ⟨P, hP_pref, he⟩
    have hnonc_le : nonc ws.length ≤ 4 := by
      have hc1 : 15 ≤ (Ecov ws.length).card := by
        rw [← Eset_card]
        exact Finset.card_le_card hPcov
      have hc2 := cov_plus_nonc ws.length le_rfl
      omega
    let Z1 : ℕ → ℕ := fun t => if t = 0 then 1 else if t = 1 then 2 else if t = 2 then 4 else if t = 3 then 8 else 14
    let Z2 : ℕ → ℕ := fun t => if t = 0 then 1 else if t = 1 then 2 else if t = 2 then 4 else if t = 3 then 6 else 10
    let U1 : ℕ → ℕ := fun t => if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 3 else if t = 3 then 7 else 15
    let U2 : ℕ → ℕ := fun t => if t = 0 then 0 else if t = 1 then 0 else if t = 2 then 1 else if t = 3 then 3 else 7
    have Z2_le_Z1 (t : ℕ) (ht : t ≤ 4) : Z2 t ≤ Z1 t := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) with rfl | rfl | rfl | rfl | rfl <;>
        simp [Z1, Z2]
    have Z1_le_14 (t : ℕ) (ht : t ≤ 4) : Z1 t ≤ 14 := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) with rfl | rfl | rfl | rfl | rfl <;>
        simp [Z1]
    have and_bound_arith (t : ℕ) (ht : t ≤ 4) :
        (t ≤ 1 → U2 t + U1 t + 1 ≤ Z2 t) ∧ (2 ≤ t → U2 t + 3 ≤ Z2 t) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) with rfl | rfl | rfl | rfl | rfl <;>
        simp [Z2, U1, U2]
    have Z1_le_Z2_succ (t : ℕ) (ht : t ≤ 3) : Z1 t ≤ Z2 (t + 1) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp [Z1, Z2]
    have Z2_le_Z1_succ (t : ℕ) (ht : t ≤ 3) : Z2 t ≤ Z1 (t + 1) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp [Z1, Z2]
    have Z1_mono (t : ℕ) (ht : t ≤ 3) : Z1 t ≤ Z1 (t + 1) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp [Z1]
    have U1_le_U2_succ (t : ℕ) (ht : t ≤ 3) : U1 t ≤ U2 (t + 1) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp [U1, U2]
    have U1_mono (t : ℕ) (ht : t ≤ 3) : U1 t ≤ U1 (t + 1) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp [U1]
    have Z1_add_Z2 (t : ℕ) (ht : t ≤ 3) : Z1 t + Z2 t ≤ Z1 (t + 1) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp [Z1, Z2]
    have U1_add_Z1 (t : ℕ) (ht : t ≤ 3) : U1 t + Z1 t ≤ U1 (t + 1) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp [U1, Z1]
    have U1_add_U2 (t : ℕ) (ht : t ≤ 3) : U1 t + U2 t ≤ U1 (t + 1) := by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
        simp [U1, U2]
    let Inv (t : ℕ) (L : List ((Fin 10 → Bool) → Bool)) : Prop :=
      (∀ f ∈ L, A1 f = ∅ → (M2 f).card ≤ Z1 t) ∧
      (∀ f ∈ L, ∀ g ∈ L, A1 f = ∅ → A1 g = ∅ → f ≠ g → (M2 f).card ≤ Z2 t ∨ (M2 g).card ≤ Z2 t) ∧
      (∀ f ∈ L, (A1 f).card = 1 → (M2 f).card ≤ U1 t) ∧
      (∀ f ∈ L, ∀ g ∈ L, (A1 f).card = 1 → (A1 g).card = 1 → f ≠ g → (M2 f).card ≤ U2 t ∨ (M2 g).card ≤ U2 t)
    have inv_k (k : ℕ) (hk : k ≤ ws.length) : Inv (nonc k) (prefnt k) := by
      induction k with
      | zero =>
        rw [nonc_zero]
        have hpref0 : prefnt 0 = S0nt := by simp [prefnt]
        rw [hpref0]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro f hf h0
          rw [(S0nt_props f hf).2.1 h0]
          simp [Z1]
        · intro f hf g hg h0f h0g hne
          rcases (S0nt_props f hf).1 with ⟨_, rfl⟩ | ⟨i, hAi, _⟩
          · rcases (S0nt_props g hg).1 with ⟨_, rfl⟩ | ⟨j, hAj, _⟩
            · exact absurd rfl hne
            · rw [hAj] at h0g; exact absurd h0g (Finset.singleton_ne_empty j)
          · rw [hAi] at h0f; exact absurd h0f (Finset.singleton_ne_empty i)
        · intro f hf h1
          rw [(S0nt_props f hf).2.2.1 h1]
          simp [U1]
        · intro f hf g hg h1f h1g _
          left
          rw [(S0nt_props f hf).2.2.1 h1f]
          simp [U2]
      | succ k ih =>
        have hk' : k < ws.length := by omega
        have ht_le : nonc (k + 1) ≤ 4 := le_trans (nonc_mono (k + 1) ws.length hk) hnonc_le
        have hinv := ih (by omega)
        rcases hinv with ⟨ihZ1, ihZ2, ihU1, ihU2⟩
        have htake : prefnt (k + 1) = prefnt k ++ [ws[k]] := by
          simp only [prefnt, List.take_succ_eq_append_getElem hk', List.append_assoc]
        obtain ⟨a, ha, b, hb, hab, hform⟩ := step_nontriv k hk'
        have ha_le : (A1 a).card ≤ 1 := prefnt_A1_le_one k a ha
        have hb_le : (A1 b).card ≤ 1 := prefnt_A1_le_one k b hb
        have hg_le : (A1 ws[k]).card ≤ 1 := hall ws[k] (List.getElem_mem hk')
        have hnot_pref : ws[k] ∉ prefnt k := by
          intro hmem
          have h0 := (hstep ⟨k, hk'⟩).1
          change ws[k] ∉ pref k at h0
          rw [pref_eq] at h0
          exact h0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem))
        have h_and_pair_bound (u v : Fin 10) (huv : u ≠ v) (hau : A1 a = {u}) (hbv : A1 b = {v}) :
            (M2 (fun x => a x && b x)).card ≤ Z2 (nonc k) := by
          have ht4 : nonc k ≤ 4 := le_trans (nonc_mono k ws.length (by omega)) hnonc_le
          have haU1 : (M2 a).card ≤ U1 (nonc k) := ihU1 a ha (by simp [hau])
          have hbU1 : (M2 b).card ≤ U1 (nonc k) := ihU1 b hb (by simp [hbv])
          have hU2 : (M2 a).card ≤ U2 (nonc k) ∨ (M2 b).card ≤ U2 (nonc k) :=
            ihU2 a ha b hb (by simp [hau]) (by simp [hbv]) hab
          have hpair : (M2 (fun x => a x && b x)).card ≤ (M2 a).card + (M2 b).card + 1 := by
            calc (M2 (fun x => a x && b x)).card
                ≤ (M2 a ∪ M2 b ∪ Eset.filter (fun e => (e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u))).card :=
                  Finset.card_le_card (M2_and_pair a b u v huv hau hbv)
              _ ≤ (M2 a ∪ M2 b).card + (Eset.filter (fun e => (e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u))).card :=
                  Finset.card_union_le _ _
              _ ≤ ((M2 a).card + (M2 b).card) + 1 :=
                  Nat.add_le_add (Finset.card_union_le _ _) (pair_bound u v)
          have hdegA : (M2 (fun x => a x && b x)).card ≤ (M2 a).card + 3 := by
            calc (M2 (fun x => a x && b x)).card
                ≤ (M2 a ∪ Eset.filter (fun e => e.1 = u ∨ e.2 = u)).card :=
                  Finset.card_le_card (M2_and_deg a b u hau)
              _ ≤ (M2 a).card + (Eset.filter (fun e => e.1 = u ∨ e.2 = u)).card :=
                  Finset.card_union_le _ _
              _ = (M2 a).card + 3 := by rw [deg_bound u]
          have hdegB : (M2 (fun x => a x && b x)).card ≤ (M2 b).card + 3 := by
            have hcomm : (fun x => a x && b x) = (fun x => b x && a x) := by
              funext x; exact Bool.and_comm (a x) (b x)
            rw [hcomm]
            calc (M2 (fun x => b x && a x)).card
                ≤ (M2 b ∪ Eset.filter (fun e => e.1 = v ∨ e.2 = v)).card :=
                  Finset.card_le_card (M2_and_deg b a v hbv)
              _ ≤ (M2 b).card + (Eset.filter (fun e => e.1 = v ∨ e.2 = v)).card :=
                  Finset.card_union_le _ _
              _ = (M2 b).card + 3 := by rw [deg_bound v]
          have h_ar := and_bound_arith (nonc k) ht4
          rcases (by omega : nonc k ≤ 1 ∨ 2 ≤ nonc k) with hle1 | hge2
          · have h_ar1 := h_ar.1 hle1
            rcases hU2 with haU2 | hbU2 <;> omega
          · have h_ar2 := h_ar.2 hge2
            rcases hU2 with haU2 | hbU2 <;> omega
        by_cases heq : Ecov (k + 1) = Ecov k
        · have hnc : nonc (k + 1) = nonc k + 1 := by simp [nonc_succ, heq]
          rw [hnc]
          have ht3 : nonc k ≤ 3 := by omega
          have hZ1_le_Z2 : Z1 (nonc k) ≤ Z2 (nonc k + 1) := Z1_le_Z2_succ (nonc k) ht3
          have hZ2_le_Z1 : Z2 (nonc k) ≤ Z1 (nonc k + 1) := Z2_le_Z1_succ (nonc k) ht3
          have hZ1_mono : Z1 (nonc k) ≤ Z1 (nonc k + 1) := Z1_mono (nonc k) ht3
          have hU1_le_U2 : U1 (nonc k) ≤ U2 (nonc k + 1) := U1_le_U2_succ (nonc k) ht3
          have hU1_mono : U1 (nonc k) ≤ U1 (nonc k + 1) := U1_mono (nonc k) ht3
          have hg_bounds : (A1 ws[k] = ∅ → (M2 ws[k]).card ≤ Z1 (nonc k + 1)) ∧
              ((A1 ws[k]).card = 1 → (M2 ws[k]).card ≤ U1 (nonc k + 1)) := by
            rcases hform with hform | hform
            · rw [hform]
              constructor
              · intro hA0
                by_cases ha0 : A1 a = ∅
                · exact le_trans (Finset.card_le_card (M2_and_empty_left a b ha0)) (le_trans (ihZ1 a ha ha0) hZ1_mono)
                · by_cases hb0 : A1 b = ∅
                  · exact le_trans (Finset.card_le_card (M2_and_empty_right a b hb0)) (le_trans (ihZ1 b hb hb0) hZ1_mono)
                  · have ha_nz : (A1 a).card ≠ 0 := fun h => ha0 (Finset.card_eq_zero.mp h)
                    have hb_nz : (A1 b).card ≠ 0 := fun h => hb0 (Finset.card_eq_zero.mp h)
                    obtain ⟨u, hau⟩ := Finset.card_eq_one.mp (by omega : (A1 a).card = 1)
                    obtain ⟨v, hbv⟩ := Finset.card_eq_one.mp (by omega : (A1 b).card = 1)
                    have huv : u ≠ v := by
                      intro huv; subst huv
                      have hAeq : A1 (fun x => a x && b x) = {u} := by rw [A1_and, hau, hbv, Finset.inter_self]
                      rw [hAeq] at hA0
                      exact absurd hA0 (Finset.singleton_ne_empty u)
                    exact le_trans (h_and_pair_bound u v huv hau hbv) hZ2_le_Z1
              · intro hA1
                have ha1 : (A1 a).card = 1 := by
                  have : A1 (fun x => a x && b x) ⊆ A1 a := by rw [A1_and]; exact Finset.inter_subset_left
                  have := Finset.card_le_card this
                  omega
                have hb1 : (A1 b).card = 1 := by
                  have : A1 (fun x => a x && b x) ⊆ A1 b := by rw [A1_and]; exact Finset.inter_subset_right
                  have := Finset.card_le_card this
                  omega
                obtain ⟨u, hau⟩ := Finset.card_eq_one.mp ha1
                obtain ⟨v, hbv⟩ := Finset.card_eq_one.mp hb1
                have huv : u = v := by
                  by_contra hne
                  have : A1 (fun x => a x && b x) = ∅ := by
                    rw [A1_and, hau, hbv]
                    ext z; simp [hne]
                  rw [this] at hA1; simp at hA1
                subst huv
                exact le_trans (Finset.card_le_card (M2_and_same a b u hau hbv)) (le_trans (ihU1 a ha ha1) hU1_mono)
            · rw [hform]
              have hM_or : (M2 (fun x => a x || b x)).card ≤ (M2 a).card + (M2 b).card :=
                le_trans (Finset.card_le_card (M2_or_sub a b)) (Finset.card_union_le _ _)
              constructor
              · intro hA0
                have ha0 : A1 a = ∅ := by
                  rw [A1_or, Finset.union_eq_empty] at hA0; exact hA0.1
                have hb0 : A1 b = ∅ := by
                  rw [A1_or, Finset.union_eq_empty] at hA0; exact hA0.2
                have haZ1 := ihZ1 a ha ha0
                have hbZ1 := ihZ1 b hb hb0
                have hZ2 := ihZ2 a ha b hb ha0 hb0 hab
                have h_add := Z1_add_Z2 (nonc k) ht3
                omega
              · intro hA1
                have hAu : A1 (fun x => a x || b x) = A1 a ∪ A1 b := A1_or a b
                by_cases ha0 : A1 a = ∅
                · have hb1 : (A1 b).card = 1 := by rw [hAu, ha0, Finset.empty_union] at hA1; exact hA1
                  have haZ1 := ihZ1 a ha ha0
                  have hbU1 := ihU1 b hb hb1
                  have h_add := U1_add_Z1 (nonc k) ht3
                  omega
                · by_cases hb0 : A1 b = ∅
                  · have ha1 : (A1 a).card = 1 := by rw [hAu, hb0, Finset.union_empty] at hA1; exact hA1
                    have haU1 := ihU1 a ha ha1
                    have hbZ1 := ihZ1 b hb hb0
                    have h_add := U1_add_Z1 (nonc k) ht3
                    omega
                  · have ha_nz : (A1 a).card ≠ 0 := fun h => ha0 (Finset.card_eq_zero.mp h)
                    have hb_nz : (A1 b).card ≠ 0 := fun h => hb0 (Finset.card_eq_zero.mp h)
                    have ha1 : (A1 a).card = 1 := by omega
                    have hb1 : (A1 b).card = 1 := by omega
                    have haU1 := ihU1 a ha ha1
                    have hbU1 := ihU1 b hb hb1
                    have hU2 := ihU2 a ha b hb ha1 hb1 hab
                    have h_add := U1_add_U2 (nonc k) ht3
                    omega
          rw [htake]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro f hf h0
            rcases List.mem_append.mp hf with hf | hf
            · exact le_trans (ihZ1 f hf h0) hZ1_mono
            · rcases List.mem_singleton.mp hf with rfl
              exact hg_bounds.1 h0
          · intro f hf g hg h0f h0g hne
            rcases List.mem_append.mp hf with hf | hf
            · left; exact le_trans (ihZ1 f hf h0f) hZ1_le_Z2
            · rcases List.mem_append.mp hg with hg | hg
              · right; exact le_trans (ihZ1 g hg h0g) hZ1_le_Z2
              · rw [List.mem_singleton] at hf hg; exact absurd (hf.trans hg.symm) hne
          · intro f hf h1
            rcases List.mem_append.mp hf with hf | hf
            · exact le_trans (ihU1 f hf h1) hU1_mono
            · rcases List.mem_singleton.mp hf with rfl
              exact hg_bounds.2 h1
          · intro f hf g hg h1f h1g hne
            rcases List.mem_append.mp hf with hf | hf
            · left; exact le_trans (ihU1 f hf h1f) hU1_le_U2
            · rcases List.mem_append.mp hg with hg | hg
              · right; exact le_trans (ihU1 g hg h1g) hU1_le_U2
              · rw [List.mem_singleton] at hf hg; exact absurd (hf.trans hg.symm) hne
        · have hnc : nonc (k + 1) = nonc k := by simp [nonc_succ, heq]
          rw [hnc]
          have hMa : M2 a ⊆ Ecov k := fun e he => (mem_Ecov k e).mpr ⟨a, ha, he⟩
          have hMb : M2 b ⊆ Ecov k := fun e he => (mem_Ecov k e).mpr ⟨b, hb, he⟩
          have hne : ∃ e, e ∈ M2 ws[k] ∧ e ∉ Ecov k := by
            by_contra hnone
            push Not at hnone
            apply heq
            rw [Ecov_succ k hk']
            ext e
            simp only [Finset.mem_union, or_iff_left_iff_imp]
            exact hnone e
          obtain ⟨e0, he0M, he0N⟩ := hne
          have hAnd : ws[k] = fun x => a x && b x := by
            rcases hform with hform | hform
            · exact hform
            · exfalso
              have hsub : M2 ws[k] ⊆ M2 a ∪ M2 b := hform ▸ M2_or_sub a b
              rcases Finset.mem_union.mp (hsub he0M) with h | h
              · exact he0N (hMa h)
              · exact he0N (hMb h)
          have ha1 : (A1 a).card = 1 := by
            by_contra hne1
            have h0 : A1 a = ∅ := Finset.card_eq_zero.mp (by omega)
            exact he0N (hMa (M2_and_empty_left a b h0 (hAnd ▸ he0M)))
          have hb1 : (A1 b).card = 1 := by
            by_contra hne1
            have h0 : A1 b = ∅ := Finset.card_eq_zero.mp (by omega)
            exact he0N (hMb (M2_and_empty_right a b h0 (hAnd ▸ he0M)))
          obtain ⟨u, hau⟩ := Finset.card_eq_one.mp ha1
          obtain ⟨v, hbv⟩ := Finset.card_eq_one.mp hb1
          have huv : u ≠ v := by
            intro huv; subst huv
            exact he0N (hMa (M2_and_same a b u hau hbv (hAnd ▸ he0M)))
          have hgA0 : A1 ws[k] = ∅ := by
            rw [hAnd, A1_and, hau, hbv]
            ext z; simp [huv]
          have hgM2_Z2 : (M2 ws[k]).card ≤ Z2 (nonc k) := by
            rw [hAnd]
            exact h_and_pair_bound u v huv hau hbv
          have ht4' : nonc k ≤ 4 := le_trans (nonc_mono k ws.length (by omega)) hnonc_le
          have hZ2_le_Z1 : Z2 (nonc k) ≤ Z1 (nonc k) := Z2_le_Z1 (nonc k) ht4'
          rw [htake]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro f hf h0
            rcases List.mem_append.mp hf with hf | hf
            · exact ihZ1 f hf h0
            · rw [List.mem_singleton] at hf; exact hf ▸ le_trans hgM2_Z2 hZ2_le_Z1
          · intro f hf g hg h0f h0g hne
            rcases List.mem_append.mp hf with hf | hf
            · rcases List.mem_append.mp hg with hg | hg
              · exact ihZ2 f hf g hg h0f h0g hne
              · rw [List.mem_singleton] at hg; right; exact hg ▸ hgM2_Z2
            · rw [List.mem_singleton] at hf; left; exact hf ▸ hgM2_Z2
          · intro f hf h1
            rcases List.mem_append.mp hf with hf | hf
            · exact ihU1 f hf h1
            · rw [List.mem_singleton] at hf; rw [hf, hgA0] at h1; simp at h1
          · intro f hf g hg h1f h1g hne
            rcases List.mem_append.mp hf with hf | hf
            · rcases List.mem_append.mp hg with hg | hg
              · exact ihU2 f hf g hg h1f h1g hne
              · rw [List.mem_singleton] at hg; rw [hg, hgA0] at h1g; simp at h1g
            · rw [List.mem_singleton] at hf; rw [hf, hgA0] at h1f; simp at h1f
    have hP_inv := (inv_k ws.length le_rfl).1 P hP_pref A1_P
    rw [M2_P, Eset_card] at hP_inv
    have hZ14 := Z1_le_14 (nonc ws.length) hnonc_le
    omega
  · push Not at hall
    have hex : ∃ k : ℕ, ∃ hk : k < ws.length, 2 ≤ (A1 ws[k]).card := by
      obtain ⟨w, hw, hgt⟩ := hall
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hw
      exact ⟨k, hk, hgt⟩
    classical
    let k := Nat.find hex
    have hspec := Nat.find_spec hex
    rcases hspec with ⟨hk, hk2⟩
    have hk2' : 2 ≤ (A1 ws[k]).card := hk2
    have hmin (j : ℕ) (hj : j < k) (hj_lt : j < ws.length) : (A1 ws[j]).card ≤ 1 := by
      by_contra hgt
      exact Nat.find_min hex hj ⟨hj_lt, by omega⟩
    have hpref_le : ∀ f ∈ prefnt k, (A1 f).card ≤ 1 := by
      intro f hf
      rcases List.mem_append.mp hf with hf0 | hfw
      · exact (S0nt_props f hf0).2.2.2
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfw
        have hlen_take : (ws.take k).length = k := List.length_take_of_le hk.le
        rw [hlen_take] at hj
        have hget_take : (ws.take k)[j] = ws[j] := List.getElem_take
        rw [hget_take]
        exact hmin j hj (lt_trans hj hk)
    obtain ⟨a, ha, b, hb, _, hform⟩ := step_nontriv k hk
    have hOr : ws[k] = fun x => a x || b x := by
      rcases hform with hform | hform
      · exfalso
        have : (A1 ws[k]).card ≤ (A1 a).card := by
          rw [hform, A1_and]
          exact Finset.card_le_card Finset.inter_subset_left
        have := hpref_le a ha
        omega
      · exact hform
    have ha1 : (A1 a).card = 1 := by
      have : (A1 ws[k]).card ≤ (A1 a).card + (A1 b).card := by
        rw [hOr, A1_or]
        exact Finset.card_union_le _ _
      have := hpref_le a ha
      have := hpref_le b hb
      omega
    have hb1 : (A1 b).card = 1 := by
      have : (A1 ws[k]).card ≤ (A1 a).card + (A1 b).card := by
        rw [hOr, A1_or]
        exact Finset.card_union_le _ _
      have := hpref_le a ha
      have := hpref_le b hb
      omega
    obtain ⟨u, hau⟩ := Finset.card_eq_one.mp ha1
    obtain ⟨v, hbv⟩ := Finset.card_eq_one.mp hb1
    have huv : u ≠ v := by
      intro huv; subst huv
      have : (A1 ws[k]).card = 1 := by
        rw [hOr, A1_or, hau, hbv, Finset.union_self, Finset.card_singleton]
      omega
    have hw_uv : ∀ z : Fin 10, ws[k] (unit z) = decide (z = u ∨ z = v) := by
      intro z
      apply Bool.eq_iff_iff.mpr
      have hz_mem : z ∈ A1 ws[k] ↔ ws[k] (unit z) = true := by
        simp [A1]
      rw [← hz_mem, hOr, A1_or, hau, hbv]
      simp [decide_eq_true_eq]
    have hab_ws : a ∈ ws ∨ b ∈ ws := by
      by_contra hneither
      push Not at hneither
      rcases hneither with ⟨ha_nws, hb_nws⟩
      have ha_S0 : a ∈ S0nt := by
        rcases List.mem_append.mp ha with h | h
        · exact h
        · exact absurd (List.mem_of_mem_take h) ha_nws
      have hb_S0 : b ∈ S0nt := by
        rcases List.mem_append.mp hb with h | h
        · exact h
        · exact absurd (List.mem_of_mem_take h) hb_nws
      have ha_proj : a = fun x => x u := by
        rcases (S0nt_props a ha_S0).1 with ⟨h0, _⟩ | ⟨i, hAi, hEq⟩
        · rw [h0] at hau; exact absurd hau.symm (Finset.singleton_ne_empty u)
        · have hiu : i = u := Finset.singleton_injective (hAi.symm.trans hau)
          rwa [← hiu]
      have hb_proj : b = fun x => x v := by
        rcases (S0nt_props b hb_S0).1 with ⟨h0, _⟩ | ⟨j, hAj, hEq⟩
        · rw [h0] at hbv; exact absurd hbv.symm (Finset.singleton_ne_empty v)
        · have hjv : j = v := Finset.singleton_injective (hAj.symm.trans hbv)
          rwa [← hjv]
      have hw_or : ws[k] = fun x => x u || x v := by
        rw [hOr, ha_proj, hb_proj]
      exact (hforb ws[k] (List.getElem_mem hk) u v huv).2 hw_or
    have h_single : ∃ h ∈ ws, ∃ c : Fin 10, ∀ z : Fin 10, h (unit z) = decide (z = c) := by
      rcases hab_ws with ha_ws | hb_ws
      · refine ⟨a, ha_ws, u, fun z => ?_⟩
        apply Bool.eq_iff_iff.mpr
        have : z ∈ A1 a ↔ a (unit z) = true := by simp [A1]
        rw [← this, hau]
        simp [decide_eq_true_eq]
      · refine ⟨b, hb_ws, v, fun z => ?_⟩
        apply Bool.eq_iff_iff.mpr
        have : z ∈ A1 b ↔ b (unit z) = true := by simp [A1]
        rw [← this, hbv]
        simp [decide_eq_true_eq]
    have hadj_iff (i j : Fin 10) :
        (x1.any fun e => decide ((i, j) = e ∨ (j, i) = e)) = true ↔ (i, j) ∈ x1 ∨ (j, i) ∈ x1 := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨e, he, hd⟩
        rcases of_decide_eq_true hd with h | h
        · exact Or.inl (h ▸ he)
        · exact Or.inr (h ▸ he)
      · rintro (h | h)
        · exact ⟨(i, j), h, decide_eq_true (Or.inl rfl)⟩
        · exact ⟨(j, i), h, decide_eq_true (Or.inr rfl)⟩
    have hforb' : ∀ w ∈ ws, ∀ i j : Fin 10, i ≠ j →
        ((i, j) ∉ x1 ∧ (j, i) ∉ x1 → w ≠ fun x => x i && x j) ∧ (w ≠ fun x => x i || x j) := by
      intro w hw i j hij
      refine ⟨fun hnot => (hforb w hw i j hij).1 ?_, (hforb w hw i j hij).2⟩
      rw [hadj_iff]
      rintro (h | h)
      · exact hnot.1 h
      · exact hnot.2 h
    dsimp only at edgeFirst nonedgeFirst
    by_cases hadj : (u, v) ∈ x1 ∨ (v, u) ∈ x1
    · rcases hadj with huvE | hvuE
      · exact edgeFirst ws hlen hstep hforb' ⟨ws[k], List.getElem_mem hk, (u, v), huvE, hw_uv⟩ h_single hP
      · exact edgeFirst ws hlen hstep hforb' ⟨ws[k], List.getElem_mem hk, (v, u), hvuE, fun z => by rw [hw_uv z]; simp only [or_comm]⟩ h_single hP
    · have hnot' : (u, v) ∉ x1 ∧ (v, u) ∉ x1 := ⟨fun h => hadj (Or.inl h), fun h => hadj (Or.inr h)⟩
      exact nonedgeFirst ws hlen hstep hforb' ⟨ws[k], List.getElem_mem hk, u, v, huv, hnot'.1, hnot'.2, hw_uv⟩ h_single hP
