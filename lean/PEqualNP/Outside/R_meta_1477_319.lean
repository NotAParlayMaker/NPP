import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Setting a point or line to true leaves five singleton terms. Removing those
-- five inputs leaves the incidence function of its affine complement.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1477_319
    (restrictVertex :
      let E := fun (u w : Fin 42) => decide (u.val < 21 ∧ 21 ≤ w.val ∧
      (w.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u w, E u w = true ∧ x u = true ∧ x w = true) →
        ∃ (v : Fin 42) (D : Circuit), Monotone2 D ∧ D.size + 25 ≤ C.size ∧
          ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) =
            C.eval (List.ofFn (Function.update x v true)))
    (stripSingletons : ∀ (n : ℕ) (S : Finset (Fin n)) (D : Circuit)
        (f : (Fin n → Bool) → Prop), Monotone2 D →
      (∃ x, f x) → ¬ f (fun _ => false) →
      (∀ x, f (fun i => if i ∈ S then false else x i) ↔ f x) →
      (∀ x, D.eval (List.ofFn x) = true ↔ (∃ i ∈ S, x i = true) ∨ f x) →
      ∃ A : Circuit, Monotone2 A ∧ A.size + S.card ≤ D.size ∧
        ∀ x, A.eval (List.ofFn x) = true ↔ f x)
    (affineBound :
      let E := fun (u w : Fin 42) => decide (u.val < 21 ∧ 21 ≤ w.val ∧
      (w.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
      ∀ (v : Fin 42) (A : Circuit), Monotone2 A →
        let S := Finset.univ.filter fun i => E v i || E i v
        let f := fun (x : Fin 42 → Bool) => ∃ u w : Fin 42, E u w = true ∧
      u ≠ v ∧ w ≠ v ∧ u ∉ S ∧ w ∉ S ∧ x u = true ∧ x w = true
        (∀ x, A.eval (List.ofFn x) = true ↔ f x) → 95 ≤ A.size) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, mono, bound, computes⟩
  let E := fun (u w : Fin 42) => decide (u.val < 21 ∧ 21 ≤ w.val ∧
      (w.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))
  have table : ∀ u w : Fin 42, (u.val, w.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ↔ E u w = true := by
    decide +kernel
  have spec (x : Fin 42 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ u w, E u w = true ∧ x u = true ∧ x w = true := by
    simpa only [table] using computes x
  obtain ⟨v, D, dmono, drop, heval⟩ := restrictVertex C mono spec
  let S := Finset.univ.filter fun i => E v i || E i v
  let f := fun (x : Fin 42 → Bool) => ∃ u w : Fin 42, E u w = true ∧
      u ≠ v ∧ w ≠ v ∧ u ∉ S ∧ w ∉ S ∧ x u = true ∧ x w = true
  have degree : ∀ j : Fin 42, (Finset.univ.filter fun i => E j i || E i j).card = 5 := by
    decide +kernel
  have neighbors (i) : i ∈ S ↔ E v i = true ∨ E i v = true := by simp [S]
  have loopless : ∀ i, E i i = false := by decide +kernel
  have survives : ∀ j : Fin 42, ∃ u w : Fin 42, E u w = true ∧ u ≠ j ∧ w ≠ j ∧
      (E j u || E u j) = false ∧ (E j w || E w j) = false := by decide +kernel
  have pos : ∃ x, f x := by
    obtain ⟨u, w, e, hu, hw, su, sw⟩ := survives v
    have outside (i : Fin 42) (h : (E v i || E i v) = false) : i ∉ S := by
      intro hi
      have ht := (Finset.mem_filter.mp hi).2
      rw [h] at ht
      contradiction
    exact ⟨fun _ => true, u, w, e, hu, hw, outside u su, outside w sw, rfl, rfl⟩
  have neg : ¬ f (fun _ => false) := by simp [f]
  have masked (x) : f (fun i => if i ∈ S then false else x i) ↔ f x := by
    unfold f
    constructor <;> rintro ⟨u, w, e, hu, hw, su, sw, xu, xw⟩ <;>
      exact ⟨u, w, e, hu, hw, su, sw, by simpa [su] using xu, by simpa [sw] using xw⟩
  have dspec (x) : D.eval (List.ofFn x) = true ↔ (∃ i ∈ S, x i = true) ∨ f x := by
    rw [heval, spec]
    constructor
    · rintro ⟨u, w, e, xu, xw⟩
      by_cases hu : u = v
      · subst u
        have hw : w ≠ v := fun h => by simp [h, loopless] at e
        exact Or.inl ⟨w, (neighbors w).2 (.inl e), by simpa [Function.update_of_ne hw] using xw⟩
      by_cases hw : w = v
      · subst w
        exact Or.inl ⟨u, (neighbors u).2 (.inr e), by simpa [Function.update_of_ne hu] using xu⟩
      rw [Function.update_of_ne hu] at xu
      rw [Function.update_of_ne hw] at xw
      by_cases su : u ∈ S
      · exact Or.inl ⟨u, su, xu⟩
      by_cases sw : w ∈ S
      · exact Or.inl ⟨w, sw, xw⟩
      exact Or.inr ⟨u, w, e, hu, hw, su, sw, xu, xw⟩
    · rintro (⟨i, hi, xi⟩ | ⟨u, w, e, hu, hw, _, _, xu, xw⟩)
      · have updated : Function.update x v true i = true := by
          by_cases h : i = v <;> simp [Function.update, h, xi]
        rcases (neighbors i).1 hi with e | e
        · exact ⟨v, i, e, Function.update_self .., updated⟩
        · exact ⟨i, v, e, updated, Function.update_self ..⟩
      · exact ⟨u, w, e, by simpa [Function.update_of_ne hu] using xu,
            by simpa [Function.update_of_ne hw] using xw⟩
  obtain ⟨A, amono, strip, ha⟩ := stripSingletons 42 S D f dmono pos neg masked dspec
  have lower := affineBound v A amono ha
  have five : S.card = 5 := degree v
  omega
