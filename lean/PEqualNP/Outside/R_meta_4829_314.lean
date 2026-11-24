import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the sole gate reading vertex four and retain the circuits before and after it
-- for both cofactors. A NOT requires a later inversion. An AND requires its
-- other operand wherever activating vertex four introduces the first edge.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4829_314
    (splitReader : ∀ (C : Circuit) (j : Fin C.size), FanInTwo C → C.output ≠ 4 →
      (∀ k : Fin C.size, 4 ∈ (C.gates.get k).inputs → k = j) →
      ∃ P T : Circuit, FanInTwo P ∧ FanInTwo T ∧ P.size + T.size + 1 = C.size ∧
      ∀ (x : Fin 8 → Bool) (b : Bool),
        let w := P.wires ((List.ofFn x).insertIdx 4 false)
        let g := C.gates.get j
        T.eval (w ++ [g.op.eval (g.inputs.map fun i => if i = 4 then b else w.getD i false)]) =
          C.eval ((List.ofFn x).insertIdx 4 b))
    (singleUse :
      let lo := fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
        x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
      ∀ (P T : Circuit) (c : Bool), FanInTwo P → FanInTwo T → P.size + T.size ≤ 14 →
      (∀ x, T.eval (P.wires ((List.ofFn x).insertIdx 4 false) ++ [c]) = lo x) →
      T.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains (9+P.size)) ≤ 1)
    (notCase :
      let lo := fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
        x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
      let w := fun (P : Circuit) (x : Fin 8 → Bool) => P.wires ((List.ofFn x).insertIdx 4 false)
      ∀ P T : Circuit, FanInTwo P → FanInTwo T → P.size + T.size ≤ 14 →
        T.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains (9+P.size)) ≤ 1 →
        (∃ g ∈ T.gates, g.op = .not) →
        (∀ x, T.eval (w P x ++ [true]) = lo x) →
        ∃ x, T.eval (w P x ++ [false]) ≠ (lo x || x 0 || x 3))
    (andCase :
      let lo := fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
        x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
      let w := fun (P : Circuit) (x : Fin 8 → Bool) => P.wires ((List.ofFn x).insertIdx 4 false)
      ∀ (P T : Circuit) (s : Option ℕ), FanInTwo P → FanInTwo T → P.size + T.size ≤ 14 →
        T.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains (9+P.size)) ≤ 1 →
        let u := fun x => s.elim true (fun i => (w P x).getD i false)
        (∀ x, lo x = false → (x 0 || x 3) = true → u x = true) →
        (∀ x, T.eval (w P x ++ [false]) = lo x) →
        ∃ x, T.eval (w P x ++ [u x]) ≠ (lo x || x 0 || x 3)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin x1.size), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (x1.gates.get x2).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (x6 : Fin x1.size), (4 : ℕ) ∈ (x1.gates.get x6).inputs ↔ x6 = x2) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) := by
  intro C j fan cap nop unique eq
  let lo := fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
        x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  let hi := fun x : Fin 8 → Bool => lo x || x 0 || x 3
  let test : Fin 8 → Bool := fun i => decide (i = 0)
  have lowTest : lo test = false := by decide
  have highTest : hi test = true := by decide
  let ins := fun (x : Fin 8 → Bool) (b : Bool) => (List.ofFn x).insertIdx 4 b
  have spec (x : Fin 8 → Bool) (b : Bool) : C.eval (ins x b) = if b then hi x else lo x := by
    let y : Fin 9 → Bool := ![x 0,x 1,x 2,x 3,b,x 4,x 5,x 6,x 7]
    have ev := congrFun eq y
    change C.eval (List.ofFn y) = _ at ev
    have inp : ins x b = List.ofFn y := by rfl
    rw [inp,ev]
    change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && b || b && x 0 ||
      x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
      x 5 && x 7 || x 7 && x 4) = _
    cases b <;> simp only [hi,lo,Bool.and_false,Bool.false_and,Bool.and_true,Bool.true_and,
      Bool.or_false,Bool.false_or,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm,Bool.false_eq_true,ite_false,ite_true]
  have out : C.output ≠ 4 := by
    intro bad
    let x : Fin 8 → Bool := fun _ => true
    have preserve : ∀ (gs : List Gate) (z : List Bool), 4 < z.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) z).getD 4 false = z.getD 4 false := by
      intro gs
      induction gs with
      | nil => intro z h; rfl
      | cons g gs ih =>
        intro z h
        rw [List.foldl_cons,ih _ (by simp; omega),List.getD_append _ _ _ _ h]
    have h := spec x false
    change (C.gates.foldl _ (ins x false)).getD C.output false = _ at h
    rw [bad,preserve _ _ (by decide)] at h
    contradiction
  obtain ⟨P,T,pf,tf,len,run⟩ := splitReader C j fan out (fun k h => (unique k).mp h)
  let g := C.gates.get j
  let w := fun x : Fin 8 → Bool => P.wires (ins x false)
  let val := fun (x : Fin 8 → Bool) (b : Bool) => g.op.eval (g.inputs.map fun i => if i = 4 then b else (w x).getD i false)
  have both (x : Fin 8 → Bool) (b : Bool) : T.eval (w x ++ [val x b]) = if b then hi x else lo x :=
    (run x b).trans (spec x b)
  have live : val test false ≠ val test true := by
    intro h
    have e := (both test false).symm.trans ((congrArg (fun q => T.eval (w test ++ [q])) h).trans (both test true))
    change lo test = hi test at e
    rw [lowTest,highTest] at e
    contradiction
  have small : P.size + T.size ≤ 14 := by omega
  have hg : g ∈ C.gates := List.get_mem _ _
  have shape := fan g hg
  have marked : 4 ∈ g.inputs := (unique j).mpr rfl
  rcases shape.1 with isAnd | isOr | isNot
  · have side : ∃ s : Option ℕ, ∀ (x : Fin 8 → Bool) (b : Bool),
        val x b = (b && s.elim true (fun i => (w x).getD i false)) := by
      have hlen := shape.2
      generalize hlist : g.inputs = L at marked hlen
      rcases L with _ | ⟨a, _ | ⟨c, _ | ⟨e,tail⟩⟩⟩
      · simp at marked
      · have ha : a = 4 := (by simpa using marked : 4 = a).symm
        subst a
        exact ⟨none,fun x b => by change GateOp.eval _ _ = _; rw [isAnd,hlist]; cases b <;> rfl⟩
      · have hh : 4 = a ∨ 4 = c := by simpa using marked
        rcases hh with ha | hc
        · subst a
          by_cases ec : c = 4
          · subst c; exact ⟨none, fun x b => by dsimp only [val]; rw [isAnd,hlist]; cases b <;> rfl⟩
          · refine ⟨some c,fun x b => ?_⟩
            dsimp only [val]; rw [isAnd,hlist]
            simp only [List.map_cons,List.map_nil,ite_true,if_neg ec,Option.elim_some]
            cases b <;> cases (w x).getD c false <;> rfl
        · subst c
          by_cases ea : a = 4
          · subst a; exact ⟨none, fun x b => by dsimp only [val]; rw [isAnd,hlist]; cases b <;> rfl⟩
          · refine ⟨some a,fun x b => ?_⟩
            dsimp only [val]; rw [isAnd,hlist]
            simp only [List.map_cons,List.map_nil,ite_true,if_neg ea,Option.elim_some]
            cases b <;> cases (w x).getD a false <;> rfl
      · simp at hlen
    obtain ⟨s,sv⟩ := side
    let u := fun x => s.elim true (fun i => (w x).getD i false)
    have low (x : Fin 8 → Bool) : T.eval (w x ++ [false]) = lo x := by
      simpa only [sv,Bool.false_and, Bool.false_eq_true, ite_false] using both x false
    have high (x : Fin 8 → Bool) : T.eval (w x ++ [u x]) = hi x := by
      simpa only [u,sv,Bool.true_and,ite_true] using both x true
    have forced (x : Fin 8 → Bool) (hx : lo x = false) (hy : (x 0 || x 3) = true) : u x = true := by
      cases h : u x with
      | true => rfl
      | false =>
        have e := high x
        rw [h,low,hx] at e
        simp only [hi,hx,Bool.false_or,hy] at e
        contradiction
    obtain ⟨x,hx⟩ := andCase P T s pf tf small (singleUse P T false pf tf small low) forced low
    exact hx (high x)
  · exact nop isOr
  · have vs (x : Fin 8 → Bool) (b : Bool) : val x b = !b := by
      have hlen := shape.2
      generalize hlist : g.inputs = L at marked hlen
      cases L with
      | nil => simp at marked
      | cons a tail =>
        by_cases h : a = 4
        · subst a; dsimp only [val]; rw [isNot,hlist]; cases b <;> rfl
        · exfalso
          apply live
          dsimp only [val]; rw [isNot,hlist]
          simp only [List.map_cons,if_neg h]
          rfl
    have low (x : Fin 8 → Bool) : T.eval (w x ++ [true]) = lo x := by
      simpa only [vs,Bool.not_false,Bool.false_eq_true,ite_false] using both x false
    have high (x : Fin 8 → Bool) : T.eval (w x ++ [false]) = hi x := by
      simpa only [vs,Bool.not_true,ite_true] using both x true
    have gate : ∃ t ∈ T.gates, t.op = .not := by
      by_contra no
      have monot : ∀ t ∈ T.gates, t.op = .and ∨ t.op = .or := by
        intro t ht
        rcases (tf t ht).1 with a | o | n
        · exact Or.inl a
        · exact Or.inr o
        · exact False.elim (no ⟨t,ht,n⟩)
      let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
      let rel := fun (w v : List Bool) => w.length = v.length ∧ ∀ i, w.getD i false = true → v.getD i false = true
      have andEval (ys : List Bool) : GateOp.and.eval ys = ys.all id := rfl
      have orEval (ys : List Bool) : GateOp.or.eval ys = ys.any id := rfl
      have walk : ∀ (gs : List Gate) (w v : List Bool),
          (∀ g ∈ gs, g.op = .and ∨ g.op = .or) → rel w v → rel (gs.foldl step w) (gs.foldl step v) := by
        intro gs
        induction gs with
        | nil => intro w v _ h; exact h
        | cons g gs ih =>
          intro w v ok h
          obtain ⟨hlen,hval⟩ := h
          apply ih _ _ (fun g' hg' => ok g' (by simp [hg']))
          refine ⟨by simp [step,hlen], ?_⟩
          intro i on
          by_cases hi : i < w.length
          · rw [List.getD_append _ _ _ _ hi] at on
            rw [List.getD_append _ _ _ _ (by omega : i < v.length)]
            exact hval i on
          · by_cases eq : i = w.length
            · subst i
              simp only [step, List.getD_append_right _ _ _ _ (by omega : w.length ≤ w.length),
                Nat.sub_self, List.getD_cons_zero] at on
              rw [show w.length = v.length from hlen]
              simp only [step, List.getD_append_right _ _ _ _ (by omega : v.length ≤ v.length),
                Nat.sub_self, List.getD_cons_zero]
              rcases ok g (by simp) with op | op
              · simp [op,andEval] at on ⊢
                exact fun j hj => hval j (on j hj)
              · simp [op,orEval] at on ⊢
                obtain ⟨j,hj,jv⟩ := on
                exact ⟨j,hj,hval j jv⟩
            · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at on
              contradiction
      have inputs : rel (w test ++ [false]) (w test ++ [true]) := by
        refine ⟨by simp,?_⟩
        intro i on
        by_cases h : i < (w test).length
        · simpa only [List.getD_append _ _ _ _ h] using on
        · rw [List.getD_append_right _ _ _ _ (by omega)] at on ⊢
          cases i - (w test).length <;> simp [List.getD_eq_getElem?_getD] at on ⊢
      have up := (walk T.gates _ _ monot inputs).2 T.output
      have on : T.eval (w test ++ [false]) = true := (high test).trans highTest
      have off : T.eval (w test ++ [true]) = false := (low test).trans lowTest
      have clash : T.eval (w test ++ [true]) = true := up on
      rw [off] at clash
      contradiction
    obtain ⟨x,hx⟩ := notCase P T pf tf small (singleUse P T true pf tf small low) gate low
    exact hx (high x)
