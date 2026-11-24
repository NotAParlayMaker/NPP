import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3174_713
    (expand : ∀ (n : ℕ) (C : Circuit) (_hc : FanInTwo C) (fs : List (DMFormula n)),
    let w := C.gates.foldl (fun (w : List ℕ) g =>
      let args := g.inputs.map fun i => w.getD i 0
      w ++ [ite (g.op.eval [false] = true) (args.headD 0) args.sum]) (fs.map DMFormula.leaves)
    (∃ b : Bool, ∀ x, C.eval (fs.map fun f => f.eval x) = b) ∨
    ∃ f : DMFormula n, f.leaves ≤ w.getD C.output 0 ∧
      ∀ x, f.eval x = C.eval (fs.map fun d => d.eval x))
    (small : ∀ (a b : Fin 9), a ∈ [1,5] → b ∈ [2,3,8] →
      ∀ f : DMFormula 10, f.leaves ≤ 15 → ∃ x : Fin 9 → Bool,
        f.eval (Fin.lastCases (x a || x b) x) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (cut : ∀ (a b : Fin 9), a ∈ [1,5] → b ∈ [2,3,8] →
      ∀ (S : DMFormula 10) (T : DMFormula 11), S.leaves ≤ 5 → S.leaves + T.leaves ≤ 15 →
      ∃ x : Fin 9 → Bool, let y : Fin 10 → Bool := Fin.lastCases (x a || x b) x
        T.eval (Fin.lastCases (S.eval y) y) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (shared : ∀ (a b : Fin 9), a ∈ [1,5] → b ∈ [2,3,8] →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → 16 ≤ (C.gates.foldl (fun (w : List ℕ) g =>
      let args := g.inputs.map fun i => w.getD i 0
      w ++ [ite (g.op.eval [false] = true) (args.headD 0) args.sum]) (List.replicate 11 1)).getD C.output 0 →
      let pins := fun x : Fin 9 → Bool => C.eval (List.ofFn x ++ [!x 0, x a || x b])
      (¬ ∃ (S : DMFormula 10) (T : DMFormula 11), S.leaves ≤ 5 ∧ S.leaves+T.leaves ≤ 15 ∧
        ∀ x : Fin 9 → Bool, let y : Fin 10 → Bool := Fin.lastCases (x a || x b) x
          T.eval (Fin.lastCases (S.eval y) y) = pins x) →
      ∃ x : Fin 9 → Bool, pins x ≠ ((x 0 && (x 1 || x 4 || x 5)) || (x 2 && (x 1 || x 3 || x 7)) || (x 3 && (x 4 || x 8)) || (x 5 && (x 7 || x 8)) || (x 6 && (x 1 || x 8)))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro ls len entries mixed C ops size
  obtain ⟨a,b,ha,hb,hval⟩ : ∃ a b : Fin 9, a ∈ [1,5] ∧ b ∈ [2,3,8] ∧
      ∀ x : Fin 9 → Bool,
        GateOp.or.eval (ls.map fun i => (List.ofFn x ++ [!x 0]).getD i false) = (x a || x b) := by
    cases ls with
    | nil => simp at len
    | cons p rest =>
      cases rest with
      | nil => simp at len
      | cons q rest =>
        have z : rest = [] := List.length_eq_zero_iff.mp (by simpa using len)
        subst rest
        have hp := entries p (by simp)
        have hq := entries q (by simp)
        have pair (a b : Fin 9) (ha : a ∈ [1,5]) (hb : b ∈ [2,3,8])
            (ord : [p,q] = [a.val,b.val] ∨ [p,q] = [b.val,a.val]) :
            ∃ m n : Fin 9, m ∈ [1,5] ∧ n ∈ [2,3,8] ∧ ∀ x : Fin 9 → Bool,
              GateOp.or.eval ([p,q].map fun i => (List.ofFn x ++ [!x 0]).getD i false) = (x m || x n) := by
          refine ⟨a,b,ha,hb,?_⟩
          have read (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x ++ [!x 0]).getD i.val false = x i := by
            have inRange : i.val < (List.ofFn x).length := by simp
            simp only [List.getD,List.getElem?_append_left inRange,List.getElem?_eq_getElem inRange,Option.getD_some,List.getElem_ofFn]
          rcases ord with eq | eq <;> rw [eq] <;> intro x <;>
            simp only [List.map_cons,List.map_nil,read] <;>
            change (_ || (_ || false)) = _ <;> simp [Bool.or_comm]
        rcases hp with h|h|h|h|h <;> subst p <;> rcases hq with h|h|h|h|h <;> subst q <;>
          simp at mixed <;> first
          | apply pair 1 2 (by decide) (by decide); decide
          | apply pair 1 3 (by decide) (by decide); decide
          | apply pair 1 8 (by decide) (by decide); decide
          | apply pair 5 2 (by decide) (by decide); decide
          | apply pair 5 3 (by decide) (by decide); decide
          | apply pair 5 8 (by decide) (by decide); decide
  let budget := (C.gates.foldl (fun (w : List ℕ) g =>
      let args := g.inputs.map fun i => w.getD i 0
      w ++ [ite (g.op.eval [false] = true) (args.headD 0) args.sum]) (List.replicate 11 1)).getD C.output 0
  let graph := fun x : Fin 9 → Bool => ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let pins := fun x : Fin 9 → Bool => List.ofFn x ++ [!x 0,x a || x b]
  suffices bad : ∃ x : Fin 9 → Bool, C.eval (pins x) ≠ graph x by
    obtain ⟨x,bad⟩ := bad
    exact ⟨x,by simpa only [hval,List.append_assoc,List.cons_append,List.nil_append] using bad⟩
  by_cases heavy : 16 ≤ budget
  · classical
    by_cases factors : ∃ (S : DMFormula 10) (T : DMFormula 11), S.leaves ≤ 5 ∧
        S.leaves+T.leaves ≤ 15 ∧ ∀ x : Fin 9 → Bool,
          let y : Fin 10 → Bool := Fin.lastCases (x a || x b) x
          T.eval (Fin.lastCases (S.eval y) y) = C.eval (pins x)
    · obtain ⟨S,T,hs,ht,representation⟩ := factors
      obtain ⟨x,miss⟩ := cut a b ha hb S T hs ht
      exact ⟨x,fun agrees => miss ((representation x).trans agrees)⟩
    · obtain ⟨x,miss⟩ := shared a b ha hb C ops size heavy factors
      refine ⟨x,fun agrees => miss (agrees.trans ?_)⟩
      dsimp only [graph]
      have identity : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool), ((b0 && b1) || (b1 && b2) || (b2 && b3) || (b3 && b4) || (b4 && b0) || (b0 && b5) || (b1 && b6) || (b2 && b7) || (b3 && b8) || (b5 && b7) || (b6 && b8) || (b8 && b5)) = ((b0 && (b1 || b4 || b5)) || (b2 && (b1 || b3 || b7)) || (b3 && (b4 || b8)) || (b5 && (b7 || b8)) || (b6 && (b1 || b8))) := by decide
      exact identity (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  let fs : List (DMFormula 10) :=
    List.ofFn (fun i : Fin 9 => DMFormula.lit i.castSucc true) ++ [.lit 0 false,.lit 9 true]
  have weight : fs.map DMFormula.leaves = List.replicate 11 1 := by decide
  let y : (Fin 9 → Bool) → Fin 10 → Bool := fun x => Fin.lastCases (x a || x b) x
  have inputs (x : Fin 9 → Bool) : fs.map (fun d => d.eval (y x)) = pins x := by
    have h0 : y x 0 = x 0 := Fin.lastCases_castSucc (0 : Fin 9)
    have h9 : y x 9 = (x a || x b) := Fin.lastCases_last
    have literal (i : Fin 10) (v : Bool) : (DMFormula.lit i v).eval (y x) = (if v then y x i else !(y x i)) := rfl
    simp only [fs,pins,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,
      literal,ite_true,Bool.false_eq_true,ite_false,h0,h9]
    congr 2
    funext i
    change Fin.lastCases (motive := fun _ : Fin 10 => Bool) (x a || x b) x i.castSucc = x i
    simp
  rcases expand 10 C ops fs with ⟨bval,constant⟩ | ⟨f,k,computed⟩
  · by_contra! agrees
    have same (x : Fin 9 → Bool) : graph x = bval := by rw [← agrees x,← inputs x]; exact constant (y x)
    have no := same (fun _ => false)
    have yes := same (fun _ => true)
    simp [graph] at no yes
    exact Bool.false_ne_true (no.symm.trans yes)
  · rw [weight] at k
    obtain ⟨x,h⟩ := small a b ha hb f (by change f.leaves ≤ budget at k; omega)
    exact ⟨x,fun eq => h ((computed (y x)).trans ((congrArg C.eval (inputs x)).trans eq))⟩
