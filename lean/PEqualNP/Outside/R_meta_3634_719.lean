import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3634_719
    -- Each key is nine times the smaller endpoint plus the larger endpoint.
    (adjacent : ∀ (D : Circuit) (u v : Fin 9),
      9 * min u.val v.val + max u.val v.val ∈ ([11, 15, 21, 25] : List ℕ) →
      FanInTwo D → D.size = 13 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x u || x v]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False)
    (nonadjacent : ∀ (D : Circuit) (u v : Fin 9),
      9 * min u.val v.val + max u.val v.val ∈ ([12, 14, 16, 17, 24, 26, 33, 61] : List ℕ) →
      FanInTwo D → D.size = 13 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x u || x v]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  have representatives : ∀ (D : Circuit) (u v : Fin 9),
      9 * min u.val v.val + max u.val v.val ∈ ([11, 12, 14, 15, 16, 17, 21, 24, 25, 26, 33, 61] : List ℕ) →
      FanInTwo D → D.size = 13 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x u || x v]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → False := by
    intro D u v h
    by_cases e : 9 * min u.val v.val + max u.val v.val ∈ ([11, 15, 21, 25] : List ℕ)
    · exact adjacent D u v e
    · apply nonadjacent D u v
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h e ⊢
      tauto
  -- Rename the first nine input wires and preserve both supplied OR values.
  have rewire (C : Circuit) (p : Fin 9 → Fin 9) (basis : FanInTwo C) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
        ∀ (x : Fin 9 → Bool) (a b : Bool),
          D.eval (List.ofFn x ++ [a, b]) =
          C.eval (List.ofFn (fun i => x (p i)) ++ [a, b]) := by
    let r (i : ℕ) : ℕ := if h : i < 9 then (p ⟨i,h⟩).val else i
    let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩
    let D : Circuit := ⟨C.gates.map rename, r C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
      simpa [rename] using basis k hk
    · simp [Circuit.size, D]
    intro x a b
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have fold (gs : List Gate) (U V : List Bool)
        (low : 9 ≤ U.length) (len : V.length = U.length)
        (vals : ∀ i, V.getD (r i) false = U.getD i false) :
        ∀ i, ((gs.map rename).foldl step V).getD (r i) false =
          (gs.foldl step U).getD i false := by
      induction gs generalizing U V with
      | nil => exact vals
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        apply ih
        · simpa [step] using (show 9 ≤ U.length + 1 by omega)
        · simp [step, len]
        intro i
        have same : (rename g).op.eval ((rename g).inputs.map fun j => V.getD j false) =
            g.op.eval (g.inputs.map fun j => U.getD j false) := by
          simp only [rename, List.map_map, Function.comp_def, vals]
        simp only [step, same]
        by_cases hi : i < U.length
        · have hr : r i < V.length := by
            by_cases small : i < 9
            · have hp := (p ⟨i, small⟩).isLt
              simpa [r, small, len] using (show (p ⟨i, small⟩).val < U.length by omega)
            · simpa [r, small, len] using hi
          rw [List.getD_append _ _ _ _ hr, List.getD_append _ _ _ _ hi, vals]
        · have big : ¬ i < 9 := by omega
          simp only [r, dite_eq_right big]
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), len]
    apply fold C.gates
    · simp
    · simp
    intro i
    by_cases small : i < 9
    · have hp := (p ⟨i, small⟩).isLt
      simp only [r, dite_eq_left small]
      rw [List.getD_append _ _ _ _ (by simpa using hp),
        List.getD_append _ _ _ _ (by simpa using small)]
      rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getD_eq_getElem _ _ (by simpa using small)]
      simp only [List.getElem_ofFn]
    · simp only [r, dite_eq_right small]
      rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt small),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt small)]
      simp
  intro C S basis card _ disj size computes
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp card
  let p : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  let key (i j : Fin 9) := 9 * min i.val j.val + max i.val j.val
  have cover : ∀ i j : Fin 9, i ≠ j → i ≠ 0 → i ≠ 4 → j ≠ 0 → j ≠ 4 →
      key i j ∈ ([11, 12, 14, 15, 16, 17, 21, 24, 25, 26, 33, 61] : List ℕ) ∨ key (p i) (p j) ∈ ([11, 12, 14, 15, 16, 17, 21, 24, 25, 26, 33, 61] : List ℕ) := by decide
  have hdis := Finset.disjoint_left.mp disj
  have ha0 : a ≠ 0 := by rintro rfl; exact @hdis 0 (by simp) (by simp)
  have ha4 : a ≠ 4 := by rintro rfl; exact @hdis 4 (by simp) (by simp)
  have hb0 : b ≠ 0 := by rintro rfl; exact @hdis 0 (by simp) (by simp)
  have hb4 : b ≠ 4 := by rintro rfl; exact @hdis 4 (by simp) (by simp)
  have pair (x : Fin 9 → Bool) :
      decide (∃ i ∈ ({a, b} : Finset (Fin 9)), x i = true) = (x a || x b) := by
    simp
  rcases cover a b hab ha0 ha4 hb0 hb4 with h | h
  · apply representatives C a b h basis size
    intro x
    simpa only [pair] using computes x
  · obtain ⟨D, basisD, sizeD, evalD⟩ := rewire C p basis
    apply representatives D (p a) (p b) h basisD (sizeD.trans size)
    intro x
    rw [evalD]
    have hold := computes (fun i => x (p i))
    rw [pair] at hold
    change C.eval (List.ofFn (fun i => x (p i)) ++ [x (p 0) || x (p 4), x (p a) || x (p b)]) = _
    refine hold.trans ?_
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    change ((x 0 && x 5) || ((x 5 && x 8) || ((x 8 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 1) || ((x 5 && x 7) || ((x 8 && x 6) || ((x 3 && x 2) || ((x 1 && x 6) || ((x 7 && x 2) || (x 2 && x 1)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || (x 8 && x 5))))))))))))
    ac_rfl
