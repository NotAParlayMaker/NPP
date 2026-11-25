import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4817_617
    (rawCases : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)), x2 ∈ ([0, 1, 3, 6, 8] : List (Fin 12)) →   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5)
    (negatedFeature : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑(10 : Fin (12 : ℕ))) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5)
    (constantTrue : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑(11 : Fin (12 : ℕ))) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5) := by
  intro C j legal budget
  let base (x : Fin 10 → Bool) : List Bool :=
    List.ofFn x ++ [x 0 && x 2]
  let inputs (x : Fin 10 → Bool) (i : Fin 12) : List Bool :=
    base x ++ [!(base x).getD i.val false]
  let F (x : Fin 10 → Bool) : Bool := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  change ∃ x : Fin 10 → Bool, C.eval (inputs x j) ≠ F x
  by_cases jRaw : j.val < 10
  · let k : Fin 10 := ⟨j.val, jRaw⟩
    have orbits (i : Fin 10) : ∃ (r : Fin 12) (σ : Fin 10 → Fin 10),
        r ∈ ([0, 1, 3, 6, 8] : List (Fin 12)) ∧ (σ i).val = r.val ∧
        (∀ x : Fin 10 → Bool, (x (σ 0) && x (σ 2)) = (x 0 && x 2)) ∧
        (∀ x : Fin 10 → Bool, F (x ∘ σ) = F x) := by
      fin_cases i
      · exact ⟨0, id, by decide, rfl, fun _ => rfl, fun _ => rfl⟩
      · exact ⟨1, id, by decide, rfl, fun _ => rfl, fun _ => rfl⟩
      · refine ⟨0, ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8], by decide, rfl, ?_, ?_⟩
        · intro x
          change (x 2 && x 0) = (x 0 && x 2)
          exact Bool.and_comm _ _
        · intro x
          change (x 2 && x 1 || x 1 && x 0 || x 0 && x 4 || x 4 && x 3 || x 3 && x 2 || x 2 && x 7 || x 1 && x 6 || x 0 && x 5 || x 4 && x 9 || x 3 && x 8 || x 7 && x 5 || x 5 && x 8 || x 8 && x 6 || x 6 && x 9 || x 9 && x 7) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
          simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
      · exact ⟨3, id, by decide, rfl, fun _ => rfl, fun _ => rfl⟩
      · refine ⟨3, ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8], by decide, rfl, ?_, ?_⟩
        · intro x
          change (x 2 && x 0) = (x 0 && x 2)
          exact Bool.and_comm _ _
        · intro x
          change (x 2 && x 1 || x 1 && x 0 || x 0 && x 4 || x 4 && x 3 || x 3 && x 2 || x 2 && x 7 || x 1 && x 6 || x 0 && x 5 || x 4 && x 9 || x 3 && x 8 || x 7 && x 5 || x 5 && x 8 || x 8 && x 6 || x 6 && x 9 || x 9 && x 7) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
          simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
      · refine ⟨3, ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9], by decide, rfl, ?_, ?_⟩
        · intro x
          change (x 2 && x 0) = (x 0 && x 2)
          exact Bool.and_comm _ _
        · intro x
          change (x 2 && x 1 || x 1 && x 0 || x 0 && x 5 || x 5 && x 7 || x 7 && x 2 || x 2 && x 3 || x 1 && x 6 || x 0 && x 4 || x 5 && x 8 || x 7 && x 9 || x 3 && x 4 || x 4 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 3) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
          simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
      · exact ⟨6, id, by decide, rfl, fun _ => rfl, fun _ => rfl⟩
      · refine ⟨3, ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], by decide, rfl, ?_, ?_⟩
        · intro x
          change (x 0 && x 2) = (x 0 && x 2)
          rfl
        · intro x
          change (x 0 && x 1 || x 1 && x 2 || x 2 && x 7 || x 7 && x 5 || x 5 && x 0 || x 0 && x 4 || x 1 && x 6 || x 2 && x 3 || x 7 && x 9 || x 5 && x 8 || x 4 && x 3 || x 3 && x 8 || x 8 && x 6 || x 6 && x 9 || x 9 && x 4) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
          simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
      · exact ⟨8, id, by decide, rfl, fun _ => rfl, fun _ => rfl⟩
      · refine ⟨8, ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8], by decide, rfl, ?_, ?_⟩
        · intro x
          change (x 2 && x 0) = (x 0 && x 2)
          exact Bool.and_comm _ _
        · intro x
          change (x 2 && x 1 || x 1 && x 0 || x 0 && x 4 || x 4 && x 3 || x 3 && x 2 || x 2 && x 7 || x 1 && x 6 || x 0 && x 5 || x 4 && x 9 || x 3 && x 8 || x 7 && x 5 || x 5 && x 8 || x 8 && x 6 || x 6 && x 9 || x 9 && x 7) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
          simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    obtain ⟨r, σ, hr, toRep, feature, graph⟩ := orbits k
    let mapW (w : ℕ) : ℕ := if hw : w < 10 then (σ ⟨w, hw⟩).val else w
    have small {w : ℕ} (hw : w < 10) : mapW w < 10 := by
      simp [mapW, hw]
    have large {w : ℕ} (hw : 10 ≤ w) : mapW w = w := by
      simp [mapW, Nat.not_lt.mpr hw]
    let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map mapW⟩
    let D : Circuit := ⟨C.gates.map mapG, mapW C.output⟩
    have legalD : FanInTwo D := by
      intro g hg
      change g ∈ C.gates.map mapG at hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      simpa [mapG] using legal a ha
    have budgetD : D.size ≤ 17 := by
      change (C.gates.map mapG).length ≤ 17
      rw [List.length_map]
      exact budget
    obtain ⟨x, different⟩ := rawCases D r hr legalD budgetD
    change D.eval (inputs x r) ≠ F x at different
    have readRaw (z : Fin 10 → Bool) (rest : List Bool) (i : Fin 10) :
        ((List.ofFn z) ++ rest).getD i.val false = z i := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using i.isLt)]
      simp only [List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
    have readBase (z : Fin 10 → Bool) (i : Fin 10) : (base z).getD i.val false = z i :=
      readRaw z _ i
    have sign : (!(base x).getD r.val false) = (!(base (x ∘ σ)).getD j.val false) := by
      change (!(base x).getD r.val false) = (!(base (x ∘ σ)).getD k.val false)
      rw [← toRep, readBase x (σ k), readBase (x ∘ σ) k]
      simp only [Function.comp_apply]
    let rest : List Bool := [x 0 && x 2, !(base x).getD r.val false]
    have ref : inputs x r = List.ofFn x ++ rest := by
      simp [inputs, base, rest]
    have src : inputs (x ∘ σ) j = List.ofFn (x ∘ σ) ++ rest := by
      simpa [inputs, base, rest, List.append_assoc, Function.comp_apply] using
        (congrArg₂ (fun a b : Bool => List.ofFn (x ∘ σ) ++ [a,b]) (feature x) sign.symm)
    have start : ∀ w, (inputs x r).getD (mapW w) false =
        (inputs (x ∘ σ) j).getD w false := by
      rw [ref, src]
      intro w
      by_cases hw : w < 10
      · rw [show mapW w = (σ ⟨w, hw⟩).val by simp [mapW, hw]]
        exact (readRaw x rest (σ ⟨w, hw⟩)).trans
          (readRaw (x ∘ σ) rest ⟨w, hw⟩).symm
      · have h₁ : (List.ofFn x).length ≤ w := by simpa using Nat.le_of_not_lt hw
        have h₂ : (List.ofFn (x ∘ σ)).length ≤ w := by simpa using Nat.le_of_not_lt hw
        rw [large (Nat.le_of_not_lt hw), List.getD_eq_getElem?_getD,
          List.getD_eq_getElem?_getD, List.getElem?_append_right h₁, List.getElem?_append_right h₂]
        simp
    let step (acc : List Bool) (g : Gate) : List Bool :=
      acc ++ [g.op.eval (g.inputs.map (fun i => acc.getD i false))]
    have appendBefore (a : List Bool) (b : Bool) {w : ℕ} (h : w < a.length) :
        (a ++ [b]).getD w false = a.getD w false := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have appendAt (a : List Bool) (b : Bool) :
        (a ++ [b]).getD a.length false = b := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have appendAfter (a : List Bool) (b : Bool) {w : ℕ} (h : a.length < w) :
        (a ++ [b]).getD w false = false := by
      have hl : (a ++ [b]).length ≤ w := by simp; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]
      rfl
    have transport :
        ∀ (gs : List Gate) (a b : List Bool), a.length = b.length → 10 ≤ b.length →
          (∀ w, a.getD (mapW w) false = b.getD w false) →
          ∀ w, ((gs.map mapG).foldl step a).getD (mapW w) false =
            (gs.foldl step b).getD w false := by
      intro gs
      induction gs with
      | nil => intro a b heq hl hab; exact hab
      | cons g gs ih =>
        intro a b heq hl hab
        simp only [List.map_cons, List.foldl_cons]
        let v := g.op.eval (g.inputs.map (fun w => b.getD w false))
        have lhs : step a (mapG g) = a ++ [v] := by
          simp only [step, mapG, v, List.map_map, Function.comp_def, hab]
        have rhs : step b g = b ++ [v] := rfl
        rw [lhs, rhs]
        apply ih
        · simp [heq]
        · simp; omega
        · intro w
          rcases Nat.lt_trichotomy w b.length with before | rfl | after
          · have pw : mapW w < a.length := by
              by_cases h : w < 10
              · have s := small h
                omega
              · rw [large (Nat.le_of_not_lt h)]
                omega
            rw [appendBefore a v pw, appendBefore b v before, hab]
          · rw [large hl, ← heq, appendAt, heq, appendAt]
          · have lwm : 10 ≤ w := by omega
            have aw : a.length < w := by omega
            rw [large lwm, appendAfter a v aw, appendAfter b v after]
    have model : D.eval (inputs x r) = C.eval (inputs (x ∘ σ) j) := by
      change ((C.gates.map mapG).foldl step (inputs x r)).getD (mapW C.output) false =
        (C.gates.foldl step (inputs (x ∘ σ) j)).getD C.output false
      exact transport C.gates _ _ (by simp [ref, src]) (by simp [src]) start _
    refine ⟨x ∘ σ, ?_⟩
    rw [← model, graph x]
    exact different
  · have hj : j = 10 ∨ j = 11 := by
      have b := j.isLt
      have jv : j.val = 10 ∨ j.val = 11 := by omega
      rcases jv with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hj with rfl | rfl
    · exact negatedFeature C legal budget
    · exact constantTrue C legal budget
