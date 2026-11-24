import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The eight-input bound is the checked statement of L-meta-2036.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3632_1
    (minorBound : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
    (drop : ∀ (C : Circuit) (r : Fin 9), FanInTwo C →
      (∃ g ∈ C.gates, (g.op = .not ∧ g.inputs.head? = some 4) ∨
        (g.op ≠ .not ∧ 4 ∈ g.inputs)) →
      let pre := fun y : Fin 8 → Bool =>
        let x := Fin.insertNth (α := fun _ => Bool) (4 : Fin 9) false y
        List.ofFn x ++ [x 0, x r]
      (∃ y, C.eval (pre y) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
        ∀ y, D.eval (List.ofFn y) = C.eval (pre y))
    (commonZero : ∀ (C : Circuit) (S : Finset (Fin 9)), FanInTwo C →
      S.card = 2 → S ≠ {0,4} → 0 ∈ S → C.size = 13 →
      (∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ j ∈ S, x j = true)]) = (fun x : Fin 9 → Bool =>
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
            List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) x) → False)
    (adjacentPartner : ∀ (C : Circuit) (r : Fin 9), FanInTwo C →
      (r = 1 ∨ r = 5) → C.size = 13 →
      (∀ g ∈ C.gates, ¬ ((g.op = .not ∧ g.inputs.head? = some 4) ∨
        (g.op ≠ .not ∧ 4 ∈ g.inputs))) →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x 4 || x r]) = (fun x : Fin 9 → Bool =>
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
            List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) x) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → ¬Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  intro C S fan card different overlap size computes
  by_cases zero : 0 ∈ S
  · exact commonZero C S fan card different zero size computes
  obtain ⟨j, hj, hj'⟩ := Finset.not_disjoint_iff.mp overlap
  have four : (4 : Fin 9) ∈ S := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    rcases hj' with rfl | rfl
    · exact (zero hj).elim
    · exact hj
  have one : (S.erase 4).card = 1 := by rw [Finset.card_erase_of_mem four, card]
  obtain ⟨r, he⟩ := Finset.card_eq_one.mp one
  have pair : S = {4,r} := by rw [← Finset.insert_erase four, he]
  have r4 : r ≠ 4 := by
    intro h
    subst r
    have hmem : (4 : Fin 9) ∈ S.erase 4 := by rw [he]; simp
    simp at hmem
  have pairSeed (x : Fin 9 → Bool) :
      decide (∃ j ∈ ({4,r} : Finset (Fin 9)), x j = true) = (x 4 || x r) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    constructor
    · rintro ⟨j, hj, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (h | h)
      · exact ⟨4, by simp, h⟩
      · exact ⟨r, by simp, h⟩
  let F := fun x : Fin 9 → Bool =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  let pre (p : Fin 9) (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4, x 4 || x p]
  have eval (x : Fin 9 → Bool) : C.eval (pre r x) = F x := by
    simpa only [pair, pairSeed, pre] using computes x
  let readsFour (g : Gate) : Prop :=
    (g.op = .not ∧ g.inputs.head? = some 4) ∨ (g.op ≠ .not ∧ 4 ∈ g.inputs)
  have unused : ∀ g ∈ C.gates, ¬ readsFour g := by
    intro g hg read
    let H : (Fin 8 → Bool) → Bool := fun y =>
      (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) ||
      (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) ||
      (y 5 && y 7) || (y 7 && y 4)
    have minorId : ∀ y : Fin 8 → Bool,
        F (Fin.insertNth (α := fun _ => Bool) (4 : Fin 9) false y) = H y :=
      by decide +kernel
    let mask (y : Fin 8 → Bool) := Fin.insertNth (α := fun _ => Bool) (4 : Fin 9) false y
    have slice (y : Fin 8 → Bool) :
        C.eval (List.ofFn (mask y) ++ [mask y 0, mask y r]) = H y := by
      have hv : mask y 4 = false := Fin.insertNth_apply_same _ _ _
      have h := eval (mask y)
      simp only [pre, hv, Bool.or_false, Bool.false_or] at h
      exact h.trans (minorId y)
    have low : ∃ y : Fin 8 → Bool,
        C.eval (List.ofFn (mask y) ++ [mask y 0, mask y r]) = false :=
      ⟨fun _ => false, (slice _).trans rfl⟩
    obtain ⟨D, fanD, boundD, evalD⟩ := drop C r fan ⟨g, hg, read⟩ low
    have tiny : D.size ≤ 12 := by omega
    exact minorBound ⟨D, fanD, tiny, fun y => (evalD y).trans (slice y)⟩
  by_cases adjacent : r = 1 ∨ r = 5
  · exact adjacentPartner C r fan adjacent size unused eval
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evalNot (l : List Bool) : GateOp.not.eval l = Bool.not (l.headD false) := rfl
  have keepWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have sameFold (gs : List Gate) (noRead : ∀ g ∈ gs, ¬ readsFour g)
      (a b : List Bool) (len : a.length = b.length)
      (agree : ∀ i : ℕ, i ≠ 4 → a.getD i false = b.getD i false) :
      ∀ i : ℕ, i ≠ 4 → (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
    induction gs generalizing a b with
    | nil => exact agree
    | cons g gs ih =>
      have no := noRead g List.mem_cons_self
      let va := g.op.eval (g.inputs.map fun i => a.getD i false)
      let vb := g.op.eval (g.inputs.map fun i => b.getD i false)
      have eq : va = vb := by
        dsimp only [va, vb]
        by_cases hn : g.op = .not
        · have head : g.inputs.head? ≠ some 4 := by simpa [readsFour, hn] using no
          simp only [hn, evalNot]
          cases h : g.inputs with
          | nil => rfl
          | cons j js =>
            have hj : j ≠ 4 := by simpa [h] using head
            exact congrArg Bool.not (agree j hj)
        · have none : 4 ∉ g.inputs := by simpa [readsFour, hn] using no
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro j hj
          exact agree j (fun e => none (e ▸ hj))
      change ∀ i : ℕ, i ≠ 4 →
        (gs.foldl step (a ++ [va])).getD i false = (gs.foldl step (b ++ [vb])).getD i false
      rw [eq]
      apply ih (fun g hg => noRead g (List.mem_cons_of_mem _ hg)) _ _ (by simp [len])
      intro i hi
      by_cases hin : i < a.length
      · rw [List.getD_append _ _ _ _ hin, List.getD_append _ _ _ _ (by omega)]
        exact agree i hi
      · rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), len]
  let onlyFour (i : Fin 9) : Bool := decide (i = 4)
  have output : C.output ≠ 4 := by
    intro h
    have v : C.eval (pre r onlyFour) = true := by
      change (C.gates.foldl step (pre r onlyFour)).getD C.output false = true
      rw [h, keepWire _ _ 4 (by simp [pre]), List.getD_append _ _ _ _ (by simp)]
      decide
    have f0 : F onlyFour = false := by decide
    exact Bool.false_ne_true (f0.symm.trans ((eval onlyFour).symm.trans v))
  let bits (p : Fin 9) (b : Bool) (i : Fin 9) : Bool :=
    decide (i = 0 ∨ i = p ∨ (b = true ∧ i = 4))
  have small : ∀ (p : Fin 9) (i : Fin 11), i.val ≠ 4 →
      (pre p (bits p false)).getD i.val false =
        (pre p (bits p true)).getD i.val false := by decide +kernel
  have init : ∀ i : ℕ, i ≠ 4 →
      (pre r (bits r false)).getD i false = (pre r (bits r true)).getD i false := by
    intro i hi
    by_cases bound : i < 11
    · exact small r ⟨i, bound⟩ hi
    · rw [List.getD_eq_default _ _ (by simpa [pre] using Nat.not_lt.mp bound),
          List.getD_eq_default _ _ (by simpa [pre] using Nat.not_lt.mp bound)]
  have same : C.eval (pre r (bits r false)) = C.eval (pre r (bits r true)) :=
    sameFold C.gates unused _ _ (by simp [pre]) init C.output output
  have left : ∀ p : Fin 9, p ≠ 1 → p ≠ 4 → p ≠ 5 → F (bits p false) = false :=
    by decide +kernel
  have right : ∀ p : Fin 9, F (bits p true) = true := by decide +kernel
  rw [eval, eval, left r (fun h => adjacent (Or.inl h)) r4 (fun h => adjacent (Or.inr h)), right r] at same
  contradiction
