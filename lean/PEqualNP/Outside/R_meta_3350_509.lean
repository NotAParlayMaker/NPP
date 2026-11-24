import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3350_509
    (raw : ∀ (C : Circuit) (i : Fin 9), i ∈ ([0, 2, 3, 4, 7] : List (Fin 9)) → FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6, !x i]) ≠ (
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (combined : ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6, !(x 4 || x 6)]) ≠ (
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (constant : ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6, true]) ≠ (
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C hFan hFirst hEdge hSecond
  by_contra hSize
  have hLimit : C.size ≤ 15 := by omega
  let edge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have prefix_get (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  obtain ⟨gates, out⟩ := C
  cases gates with
  | nil => simp at hSecond
  | cons first gates =>
    cases gates with
    | nil => simp at hSecond
    | cons second tail =>
      have hOp : second.op = GateOp.not := by simpa using hSecond
      let D : Circuit := ⟨tail, out⟩
      have hDFan : FanInTwo D := by
        intro g hg
        exact hFan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
      have hDSize : D.size ≤ 13 := by
        change tail.length + 1 + 1 ≤ 15 at hLimit
        change tail.length ≤ 13
        omega
      let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
      have seed_length (x : Fin 9 → Bool) : (seed x).length = 10 := by simp [seed]
      have first_step (x : Fin 9 → Bool) : step (List.ofFn x) first = seed x := by
        have hw := hFirst x
        change ((second :: tail).foldl step (step (List.ofFn x) first)).getD 9 false =
          (x 4 || x 6) at hw
        rw [prefix_get _ _ 9 (by simp [step])] at hw
        have hLen : (List.ofFn x).length ≤ 9 := by simp
        simp only [step, List.getD_eq_getElem?_getD,
          List.getElem?_append_right hLen, List.length_ofFn, Nat.sub_self] at hw
        have hValue : first.op.eval (first.inputs.map fun j => (List.ofFn x).getD j false) =
            (x 4 || x 6) := hw
        simp only [step, seed, hValue]
      let j := second.inputs.headD 10
      have second_step (x : Fin 9 → Bool) :
          step (seed x) second = seed x ++ [!((seed x).getD j false)] := by
        cases hInputs : second.inputs with
        | nil =>
          have hMissing : (seed x)[10]? = none := List.getElem?_eq_none (by rw [seed_length])
          simp [step, hOp, GateOp.eval, j, hInputs, List.getD_eq_getElem?_getD, hMissing]
        | cons a as => simp [step, hOp, GateOp.eval, j, hInputs]
      have correct (x : Fin 9 → Bool) :
          D.eval (seed x ++ [!((seed x).getD j false)]) = edge x := by
        have h := congrFun hEdge x
        change (tail.foldl step (step (step (List.ofFn x) first) second)).getD out false =
          edge x at h
        rw [first_step x, second_step x] at h
        exact h
      by_cases hRawInput : j < 9
      · let i : Fin 9 := ⟨j, hRawInput⟩
        have raw_read (x : Fin 9 → Bool) : (seed x).getD j false = x i := by
          have hLt : j < (List.ofFn x).length := by simpa using hRawInput
          simp only [seed, List.getD_eq_getElem?_getD, List.getElem?_append_left hLt,
            List.getElem?_ofFn, dite_eq_left hRawInput, Option.getD_some, i]
        have raw_correct (x : Fin 9 → Bool) :
            D.eval (List.ofFn x ++ [x 4 || x 6, !x i]) = edge x := by
          simpa only [raw_read x, seed, List.append_assoc, List.singleton_append] using correct x
        let swap : Fin 9 → Fin 9 := ![1, 0, 5, 8, 6, 2, 4, 7, 3]
        have representatives : ∀ a : Fin 9,
            a ∈ ([0, 2, 3, 4, 7] : List (Fin 9)) ∨ swap a ∈ ([0, 2, 3, 4, 7] : List (Fin 9)) := by
          decide
        rcases representatives i with hi | hi
        · obtain ⟨x, hx⟩ := raw D i hi hDFan hDSize
          exact hx (raw_correct x)
        · let rename (j : ℕ) := ([1, 0, 5, 8, 6, 2, 4, 7, 3] : List ℕ).getD j j
          let renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
          let D' : Circuit := ⟨tail.map renameGate, rename out⟩
          have hD'Fan : FanInTwo D' := by
            intro g hg
            obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp hg
            simpa [renameGate] using hDFan old hOld
          have hD'Size : D'.size ≤ 13 := by simpa [Circuit.size, D', D] using hDSize
          have edge_swap (x : Fin 9 → Bool) : edge (x ∘ swap) = edge x := by
            have h : ∀ a b c d e f g h i : Bool,
                (b && a || a && f || f && i || i && g || g && b || b && c ||
                 a && e || f && h || i && d || c && h || e && d || d && c) =
                (a && b || b && c || c && d || d && e || e && a || a && f ||
                 b && g || c && h || d && i || f && h || g && i || i && f) := by decide
            exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
          have read_rename (x : Fin 9 → Bool) (suffix : List Bool) (k : ℕ) :
              (List.ofFn x ++ suffix).getD (rename k) false =
                (List.ofFn (x ∘ swap) ++ suffix).getD k false := by
            by_cases hk : k < 9
            · interval_cases k <;> rfl
            · have hk' : 9 ≤ k := by omega
              have hIndex : ([1, 0, 5, 8, 6, 2, 4, 7, 3] : List ℕ).length ≤ k := by
                simpa using hk'
              have hn : rename k = k := by
                simp [rename, List.getD_eq_getElem?_getD, List.getElem?_eq_none hIndex]
              simp only [hn, List.getD_eq_getElem?_getD,
                List.getElem?_append_right (by simpa using hk' : (List.ofFn x).length ≤ k),
                List.getElem?_append_right (by simpa using hk' : (List.ofFn (x ∘ swap)).length ≤ k),
                List.length_ofFn]
          have fold_rename (x : Fin 9 → Bool) (gs : List Gate) (suffix : List Bool) :
              ∃ suffix',
                (gs.map renameGate).foldl step (List.ofFn x ++ suffix) = List.ofFn x ++ suffix' ∧
                gs.foldl step (List.ofFn (x ∘ swap) ++ suffix) = List.ofFn (x ∘ swap) ++ suffix' := by
            induction gs generalizing suffix with
            | nil => exact ⟨suffix, rfl, rfl⟩
            | cons g gs ih =>
              let b := g.op.eval (g.inputs.map fun k => (List.ofFn (x ∘ swap) ++ suffix).getD k false)
              have h :
                  g.op.eval ((g.inputs.map rename).map fun k => (List.ofFn x ++ suffix).getD k false) = b := by
                rw [List.map_map]
                congr 1
                apply List.map_congr_left
                intro k _
                exact read_rename x suffix k
              simpa only [List.map_cons, List.foldl_cons, step, renameGate, h,
                ← List.append_assoc] using ih (suffix ++ [b])
          have correct' (x : Fin 9 → Bool) :
              D'.eval (List.ofFn x ++ [x 4 || x 6, !x (swap i)]) = edge x := by
            let suffix := [x 4 || x 6, !x (swap i)]
            obtain ⟨suffix', hA, hB⟩ := fold_rename x tail suffix
            have h := raw_correct (x ∘ swap)
            have hOr : ((x ∘ swap) 4 || (x ∘ swap) 6) = (x 4 || x 6) := Bool.or_comm _ _
            change (tail.foldl step (List.ofFn (x ∘ swap) ++
              [(x ∘ swap) 4 || (x ∘ swap) 6, !x (swap i)])).getD out false = edge (x ∘ swap) at h
            rw [hOr] at h
            change (tail.foldl step (List.ofFn (x ∘ swap) ++ suffix)).getD out false =
              edge (x ∘ swap) at h
            change ((tail.map renameGate).foldl step (List.ofFn x ++ suffix)).getD (rename out) false =
              edge x
            rw [hA, read_rename, ← hB, h, edge_swap]
          obtain ⟨x, hx⟩ := raw D' (swap i) hi hD'Fan hD'Size
          exact hx (correct' x)
      · by_cases hAux : j = 9
        · obtain ⟨x, hx⟩ := combined D hDFan hDSize
          have hRead : (seed x).getD j false = (x 4 || x 6) := by
            simp [hAux, seed, List.getD_eq_getElem?_getD]
          exact hx (by simpa only [hRead, seed, List.append_assoc, List.singleton_append] using correct x)
        · obtain ⟨x, hx⟩ := constant D hDFan hDSize
          have hRead : (seed x).getD j false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [seed_length]; omega)]
            rfl
          exact hx (by simpa only [hRead, Bool.not_false, seed,
            List.append_assoc, List.singleton_append] using correct x)
