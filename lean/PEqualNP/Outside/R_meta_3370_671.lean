import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3370_671
    (binaryLower :
      let edge : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ B : Circuit, FanInTwo B →
        (∀ x, B.eval (List.ofFn x) = edge x) →
        13 ≤ B.gates.countP (fun g => GateOp.rec (motive := fun _ => Bool)
          true true false (fun _ => true) true g.op))
    (remaining :
      let edge : (Fin 9 → Bool) → Bool := fun x =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ (k : Fin 9), (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6) →
        ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
          (∀ x, C.eval (List.ofFn x ++ [false, x 0 || x 4 || x k]) = edge x) →
          11 ≤ C.gates.countP (fun g => GateOp.rec (motive := fun _ => Bool)
            true true false (fun _ => true) true g.op) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)), x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (2 : Fin (9 : ℕ)) ∨ x2 = (3 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [Bool.false, x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) || x7 x2]) = x1 x7) → False := by
  dsimp only
  intro k hk C fan small computes
  let countNonNot (gs : List Gate) : ℕ :=
    gs.countP (fun g => GateOp.rec (motive := fun _ => Bool)
      true true false (fun _ => true) true g.op)
  let seed (k : Fin 9) (x : Fin 9 → Bool) : List Bool :=
    List.ofFn x ++ [false, x 0 || x 4 || x k]

  let first : Gate := ⟨.or, [0, 4]⟩

  let second (k : Fin 9) : Gate := ⟨.or, [9, k.val]⟩

  let read (dead i : ℕ) : ℕ :=
    if i = 9 then dead else i

  let rename (dead : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (read dead)⟩

  let compile (k : Fin 9) (C : Circuit) : Circuit :=
    let dead := 11 + C.gates.length
    ⟨first :: second k :: C.gates.map (rename dead), read dead C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

  have read_set (w : List Bool) (dead : ℕ) (h₀ : 9 < w.length)
      (h₁ : w.length ≤ dead) (i : ℕ) :
      w.getD (read dead i) false = (w.set 9 false).getD i false := by
    by_cases h : i = 9
    · subst i
      simp only [read, ite_eq_left rfl]
      rw [List.getD_eq_default _ _ h₁, List.getD_eq_getElem?_getD,
        List.getElem?_set_self h₀]
      rfl
    · simp only [read, ite_eq_right h, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm h)]

  have step_set (w : List Bool) (dead : ℕ) (g : Gate) (h₀ : 9 < w.length)
      (h₁ : w.length ≤ dead) :
      (step w (rename dead g)).set 9 false = step (w.set 9 false) g := by
    simp only [step, rename, List.set_append_left _ _ h₀, List.map_map,
      Function.comp_def, read_set w dead h₀ h₁]

  have fold_set (gs : List Gate) (w : List Bool) (dead : ℕ)
      (h₀ : 9 < w.length) (h₁ : w.length + gs.length ≤ dead) :
      (List.foldl step w (gs.map (rename dead))).set 9 false =
        List.foldl step (w.set 9 false) gs := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have len : (step w (rename dead g)).length = w.length + 1 := by simp [step]
      rw [ih _ (by omega) (by simp only [List.length_cons] at h₁; omega)]
      rw [step_set _ _ _ h₀ (by omega)]

  have fold_length (gs : List Gate) (w : List Bool) :
      (List.foldl step w gs).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons,
        List.length_nil]
      omega

  have eval_prefix (k : Fin 9) (x : Fin 9 → Bool) :
      step (step (List.ofFn x) first) (second k) =
        List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x k] := by
    have value (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      simp only [List.getElem_ofFn]
    have zero : (List.ofFn x).getD 0 false = x 0 := value 0
    have four : (List.ofFn x).getD 4 false = x 4 := value 4
    have inList : k.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using k.isLt
    have atEnd : (List.ofFn x).length ≤ 9 := by simp
    have or_eval (l : List Bool) : GateOp.eval .or l = l.any id := rfl
    simp only [step, first, second, List.map_cons, List.map_nil, or_eval, List.any_cons,
      id_eq, List.any_nil, Bool.or_false, zero, four]
    rw [List.getD_append_right _ _ _ _ atEnd, List.getD_append _ _ _ _ inList,
      value k, List.append_assoc]
    rfl

  have eval_compile (k : Fin 9) (C : Circuit) (x : Fin 9 → Bool) :
      (compile k C).eval (List.ofFn x) = C.eval (seed k x) := by
    let dead := 11 + C.gates.length
    let w := List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x k]
    have len : w.length = 11 := by simp [w]
    have set : w.set 9 false = seed k x := by
      unfold w seed
      rw [List.set_append_right _ _ (by simp)]
      simp
    change (List.foldl step (step (step (List.ofFn x) first) (second k))
      (C.gates.map (rename dead))).getD (read dead C.output) false =
        (List.foldl step (seed k x) C.gates).getD C.output false
    rw [eval_prefix]
    change (List.foldl step w (C.gates.map (rename dead))).getD (read dead C.output) false = _
    rw [read_set _ _ (by rw [fold_length, List.length_map, len]; omega)
      (by rw [fold_length, List.length_map, len]) _]
    rw [fold_set _ _ _ (by omega) (by rw [len]), set]

  have fan_compile (k : Fin 9) (C : Circuit) (hfan : FanInTwo C) :
      FanInTwo (compile k C) := by
    intro g hg
    change g ∈ first :: second k :: C.gates.map _ at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [first]
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [second]
    obtain ⟨original, hmem, rfl⟩ := List.mem_map.mp hg
    simpa [rename] using hfan original hmem

  have count_compile (k : Fin 9) (C : Circuit) :
      countNonNot (compile k C).gates = countNonNot C.gates + 2 := by
    simp only [compile, countNonNot, List.countP_cons, first, second,
      ↓reduceIte, List.countP_map, Function.comp_def, rename]
  have lower := binaryLower (compile k C) (fan_compile k C fan) (fun x => by
    rw [eval_compile]
    exact computes x)
  change 13 ≤ countNonNot (compile k C).gates at lower
  rw [count_compile] at lower
  exact remaining k hk C fan small computes (by change 11 ≤ countNonNot C.gates; omega)
