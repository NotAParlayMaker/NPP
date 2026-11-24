import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

-- The first gate uses one of the two NOT gates permitted by the lower bound.
set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.R_meta_3178_634
    (binaryFloor : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ x1.size - PEqualNP.NotBracket.notCount x1)
    (zero :
      ∀ j : Fin 9, j ≠ 0 → ∀ C : Circuit, FanInTwo C → 12 ≤ C.size → C.size ≤ 13 →
        notCount C = 0 → ∃ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [!x 0, x 0 || x j]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5))
    (one :
      ∀ j : Fin 9, j ≠ 0 → ∀ C : Circuit, FanInTwo C → C.size = 13 →
        notCount C = 1 → ∃ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [!x 0, x 0 || x j]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5))
    : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (0 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro pins len bounded _ profile C fan small
  let row (j : Fin 9) (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0, x 0 || x j]
  let edge (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
  have inputRead (x : Fin 9 → Bool) (j : Fin 9) :
      (List.ofFn x ++ [!x 0]).getD j.val false = x j := by
    have h : j.val < (List.ofFn x).length := by simp
    rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]
  have readZero (x : Fin 9 → Bool) : (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := rfl
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp len
  have includesZero : a = 0 ∨ b = 0 := by simpa [eq_comm] using profile.2
  have notBothSpecial : ¬ ((a = 0 ∨ a = 9) ∧ (b = 0 ∨ b = 9)) := by simpa using profile.1
  have limitsA := bounded a (by simp)
  have limitsB := bounded b (by simp)
  obtain ⟨j,hj,hrow⟩ : ∃ j : Fin 9, j ≠ 0 ∧ ∀ x : Fin 9 → Bool,
      let v := List.ofFn x ++ [!x 0]
      v ++ [GateOp.or.eval ([a,b].map fun i => v.getD i false)] = row j x := by
    rcases includesZero with rfl | rfl
    · have hn : b ≠ 0 ∧ b ≠ 9 :=
        ⟨fun e => notBothSpecial ⟨Or.inl rfl, Or.inl e⟩, fun e => notBothSpecial ⟨Or.inl rfl, Or.inr e⟩⟩
      let j : Fin 9 := ⟨b,by omega⟩
      refine ⟨j,fun eq => hn.1 (congrArg Fin.val eq),?_⟩
      intro x
      change (List.ofFn x ++ [!x 0]) ++
        [((List.ofFn x ++ [!x 0]).getD 0 false || ((List.ofFn x ++ [!x 0]).getD b false || false))] = row j x
      have hread := inputRead x j
      change (List.ofFn x ++ [!x 0]).getD b false = x j at hread
      rw [Bool.or_false, readZero x, hread]
      rfl
    · have hn : a ≠ 0 ∧ a ≠ 9 :=
        ⟨fun e => notBothSpecial ⟨Or.inl e, Or.inl rfl⟩, fun e => notBothSpecial ⟨Or.inr e, Or.inl rfl⟩⟩
      let j : Fin 9 := ⟨a,by omega⟩
      refine ⟨j,fun eq => hn.1 (congrArg Fin.val eq),?_⟩
      intro x
      change (List.ofFn x ++ [!x 0]) ++
        [((List.ofFn x ++ [!x 0]).getD a false || ((List.ofFn x ++ [!x 0]).getD 0 false || false))] = row j x
      have hread := inputRead x j
      change (List.ofFn x ++ [!x 0]).getD a false = x j at hread
      rw [Bool.or_false, readZero x, hread, Bool.or_comm (x j) (x 0)]
      rfl
  change ∃ x : Fin 9 → Bool,
    C.eval ((List.ofFn x ++ [!x 0]) ++
      [GateOp.or.eval ([a,b].map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) ≠ edge x
  simp_rw [hrow]
  by_contra! computes
  let neg : Gate := ⟨.not,[0]⟩
  let disj : Gate := ⟨.or,[0,j.val]⟩
  let D : Circuit := ⟨neg :: disj :: C.gates,C.output⟩
  have legal : FanInTwo D := by
    intro g hg
    change g ∈ neg :: disj :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [neg]
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [disj]
    exact fan g hg
  have prepend (x : Fin 9 → Bool) : D.eval (List.ofFn x) = C.eval (row j x) := by
    have negVal : GateOp.not.eval ([0].map fun i => (List.ofFn x).getD i false) = !x 0 := rfl
    have orVal : GateOp.or.eval ([0,j.val].map fun i => (List.ofFn x ++ [!x 0]).getD i false) =
        (x 0 || x j) := by
      change ((List.ofFn x ++ [!x 0]).getD 0 false ||
        ((List.ofFn x ++ [!x 0]).getD j.val false || false)) = (x 0 || x j)
      rw [Bool.or_false, readZero x, inputRead x j]
    change ((neg :: disj :: C.gates).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD C.output false = _
    simp only [List.foldl_cons, neg, disj, negVal, orVal, List.append_assoc, List.cons_append, List.nil_append, row]
    rfl
  have correct (x : Fin 9 → Bool) : D.eval (List.ofFn x) = edge x := (prepend x).trans (computes x)
  have bound := binaryFloor D legal correct
  have sizeD : D.size = C.size + 2 := rfl
  have notD : notCount D = notCount C + 1 := rfl
  have sizeLower : 12 ≤ C.size := by omega
  have split : notCount C = 0 ∨ notCount C = 1 := by omega
  rcases split with hn | hn
  · obtain ⟨x,hx⟩ := zero j hj C fan sizeLower small hn
    exact hx (computes x)
  · have exactSize : C.size = 13 := by omega
    obtain ⟨x,hx⟩ := one j hj C fan exactSize hn
    exact hx (computes x)
