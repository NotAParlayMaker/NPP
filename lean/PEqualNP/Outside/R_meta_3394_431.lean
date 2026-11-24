import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3394_431
    (lower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates)
    (remaining :
      let edge (x : Fin 9 → Bool) :=
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ j ∈ ([1,2,3,5,6,7,8] : List (Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        (if j = 6 then 13 else 12) ≤ C.gates.countP (fun g => !(g.op.eval [false])) →
        11 ≤ C.output → C.output < 11 + C.size →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x j]) ≠ edge x) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)),
      (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))],
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 →
        x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool),
          x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (6 : Fin (9 : ℕ)) || x6 x1]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
             x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
             x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
             x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
             x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
             x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
             x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
             x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
             x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
             x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
             x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
             x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro j hj C fan budget
  let edge (x : Fin 9 → Bool) :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  suffices h : ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x j]) ≠ edge x by
    simpa only [edge, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using h
  by_contra! correct
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let args (x : Fin 9 → Bool) := base x ++ [x 6 || x j]
  have baseLen (x) : (base x).length = 10 := by simp [base]
  have argsLen (x) : (args x).length = 11 := by simp [args, base]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g)]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step, List.length_append, List.length_singleton]
        omega
  have runLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step, Nat.add_comm, Nat.add_left_comm]
  have last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl
  have old (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    by_cases h : i < w.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have raw (x : Fin 9 → Bool) (i : Fin 9) : (base x).getD i.val false = x i := by
    unfold base
    rw [List.getD_append _ _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have argRaw (x : Fin 9 → Bool) (i : Fin 9) : (args x).getD i.val false = x i := by
    rw [show args x = base x ++ [x 6 || x j] by rfl,
      List.getD_append _ _ _ _ (by rw [baseLen]; have := i.isLt; omega), raw]
  have outValue (x : Fin 9 → Bool) (hi : C.output < 11) :
      (args x).getD C.output false = edge x := by
    have hx := correct x
    change (C.gates.foldl step (args x)).getD C.output false = edge x at hx
    rwa [keep C.gates (args x) C.output (by rwa [argsLen])] at hx
  have outLow : 11 ≤ C.output := by
    by_contra! below
    by_cases h : C.output < 9
    · let i : Fin 9 := ⟨C.output, h⟩
      let x : Fin 9 → Bool := fun k => decide (k = i)
      have hx := outValue x below
      change (args x).getD i.val false = edge x at hx
      rw [argRaw] at hx
      have off : edge x = false := by
        have all : ∀ k : Fin 9, edge (fun l => decide (l = k)) = false := by decide
        exact all i
      rw [off] at hx
      exact Bool.noConfusion (show true = false from by simpa only [x, decide_true] using hx)
    · rcases (show C.output = 9 ∨ C.output = 10 by omega) with eq | eq
      · let x : Fin 9 → Bool := fun _ => false
        have hx := outValue x below
        change (base x ++ [x 6 || x j]).getD C.output false = false at hx
        rw [eq, List.getD_append _ _ _ _ (by rw [baseLen]; decide)] at hx
        change (List.ofFn x ++ [!x 0]).getD 9 false = false at hx
        have idx : (List.ofFn x).length = 9 := List.length_ofFn
        have wire := last (List.ofFn x) (!x 0)
        rw [idx] at wire
        rw [wire] at hx
        exact Bool.noConfusion hx
      · let x : Fin 9 → Bool := fun i => decide (i = 6)
        have hx := outValue x below
        change (base x ++ [x 6 || x j]).getD C.output false = false at hx
        rw [eq, ← baseLen x, last] at hx
        have one : x 6 = true := rfl
        rw [one, Bool.true_or] at hx
        exact Bool.noConfusion hx
  have outHigh : C.output < 11 + C.size := by
    by_contra! beyond
    let x : Fin 9 → Bool := fun _ => true
    have hx := correct x
    change (C.gates.foldl step (args x)).getD C.output false = true at hx
    rw [List.getD_eq_default _ _ (by rw [runLen, argsLen]; exact beyond)] at hx
    exact Bool.noConfusion hx
  let binary (g : Gate) := !(g.op.eval [false])
  have lowerBound (D : Circuit) (fanD : FanInTwo D)
      (eval : ∀ x, D.eval (List.ofFn x) = edge x) : 13 ≤ D.gates.countP binary := by
    have bound := lower D fanD (fun x => by
      simpa only [edge, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using eval x)
    have same : D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) =
        D.gates.countP binary := by
      apply List.countP_congr
      intro g hg
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fanD g hg).1 :
        g.op = .and ∨ g.op = .or ∨ g.op = .not) with h | h | h <;> simp [binary, h, GateOp.eval]
    exact same ▸ bound
  have firstWire (x : Fin 9 → Bool) : step (List.ofFn x) ⟨.not, [0]⟩ = base x := by
    change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = base x
    rw [show (List.ofFn x).getD 0 false = x 0 by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl]
  have count : (if j = 6 then 13 else 12) ≤ C.gates.countP binary := by
    by_cases eq : j = 6
    · let ren (i : ℕ) := if i < 10 then i else if i = 10 then 6 else i - 1
      let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map ren⟩
      let D : Circuit := ⟨⟨.not, [0]⟩ :: C.gates.map rename, ren C.output⟩
      have sim (gs : List Gate) (w z : List Bool) (len : w.length = z.length + 1)
          (small : 11 ≤ w.length) (h : ∀ i, w.getD i false = z.getD (ren i) false) :
          ∀ i, (gs.foldl step w).getD i false =
            ((gs.map rename).foldl step z).getD (ren i) false := by
        induction gs generalizing w z with
        | nil => exact h
        | cons g gs ih =>
          simp only [List.map_cons, List.foldl_cons]
          apply ih
          · simp only [step, List.length_append, List.length_singleton, len]
          · simp only [step, List.length_append, List.length_singleton]
            omega
          · intro i
            have same : (g.inputs.map ren).map (fun k => z.getD k false) =
                g.inputs.map (fun k => w.getD k false) := by
              rw [List.map_map]
              exact List.map_congr_left (fun k _ => (h k).symm)
            have atLen : ren w.length = z.length := by
              unfold ren
              split_ifs <;> omega
            by_cases hi : i = w.length
            · rw [hi, atLen]
              simp only [step, rename, last, same]
            · have ne : ren i ≠ z.length := by
                unfold ren
                split_ifs <;> omega
              simp only [step, rename]
              rw [old _ _ _ hi, old _ _ _ ne, h]
      have rel (x : Fin 9 → Bool) (i : ℕ) :
          (args x).getD i false = (base x).getD (ren i) false := by
        by_cases hi : i < 10
        · rw [show ren i = i from ite_eq_left hi]
          exact List.getD_append _ _ _ _ (by rwa [baseLen])
        · by_cases h10 : i = 10
          · subst i
            have wire : (args x).getD 10 false = (x 6 || x j) := by
              change (base x ++ [x 6 || x j]).getD 10 false = _
              rw [← baseLen x, last]
            rw [wire, eq, Bool.or_self, show ren 10 = (6 : Fin 9).val by rfl, raw]
          · rw [List.getD_eq_default _ _ (by rw [argsLen]; omega),
                List.getD_eq_default _ _ (by
                  rw [baseLen]
                  unfold ren
                  rw [ite_eq_right hi, ite_eq_right h10]
                  omega)]
      have fanD : FanInTwo D := by
        intro g hg
        change g ∈ _ :: C.gates.map rename at hg
        rcases List.mem_cons.mp hg with rfl | hm
        · simp
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
          simpa only [rename, List.length_map] using fan k hk
      have evaluates (x : Fin 9 → Bool) : D.eval (List.ofFn x) = edge x := by
        change (((C.gates.map rename).foldl step (step (List.ofFn x) ⟨.not, [0]⟩))).getD
          (ren C.output) false = edge x
        rw [firstWire]
        exact (sim C.gates (args x) (base x) (by rw [argsLen, baseLen])
          (by rw [argsLen]) (rel x) C.output).symm.trans (correct x)
      have b := lowerBound D fanD evaluates
      rw [ite_eq_left eq]
      simpa [D, List.countP_cons, GateOp.eval, binary, List.countP_map, Function.comp_def,
        rename] using b
    · let D : Circuit := ⟨⟨.not, [0]⟩ :: ⟨.or, [6, j.val]⟩ :: C.gates, C.output⟩
      have suffix (x : Fin 9 → Bool) : step (base x) ⟨.or, [6, j.val]⟩ = args x := by
        change base x ++ [(base x).getD (6 : Fin 9).val false ||
          ((base x).getD j.val false || false)] = args x
        rw [raw, raw, Bool.or_false]
      have fanD : FanInTwo D := by
        intro g hg
        change g ∈ _ :: _ :: C.gates at hg
        rcases List.mem_cons.mp hg with rfl | rest
        · simp
        · rcases List.mem_cons.mp rest with rfl | rest
          · simp
          · exact fan g rest
      have evaluates (x : Fin 9 → Bool) : D.eval (List.ofFn x) = edge x := by
        change (C.gates.foldl step (step (step (List.ofFn x) ⟨.not, [0]⟩)
          ⟨.or, [6, j.val]⟩)).getD C.output false = edge x
        rw [firstWire, suffix]
        exact correct x
      have b := lowerBound D fanD evaluates
      change 13 ≤ (⟨.not, [0]⟩ :: ⟨.or, [6, j.val]⟩ :: C.gates).countP binary at b
      have counts : (⟨.not, [0]⟩ :: ⟨.or, [6, j.val]⟩ :: C.gates).countP binary =
          C.gates.countP binary + 1 := by
        simp [binary, GateOp.eval]
      rw [counts] at b
      rw [ite_eq_right eq]
      omega
  obtain ⟨x, bad⟩ := remaining j hj C fan budget count outLow outHigh
  exact bad (correct x)
