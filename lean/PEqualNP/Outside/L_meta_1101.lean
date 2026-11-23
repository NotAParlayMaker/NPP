import PEqualNP.Defs
namespace PEqualNP.Outside.Threshold1101
open CircuitLowerBounds
private def pair (op : GateOp) (a b : Nat) : Gate := ⟨op,[a,b]⟩
private def anyIdx (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => n+3*k+3
private def twoIdx (n : Nat) : Nat → Nat
  | 0 => n
  | k+1 => n+3*k+2
private def gates (n : Nat) : Nat → List Gate
  | 0 => [⟨.or,[]⟩]
  | k+1 => gates n k ++ [pair .and (anyIdx n k) (k+1), pair .or (twoIdx n k) (n+3*k+1),
      pair .or (anyIdx n k) (k+1)]
private theorem len (n k : Nat) : (gates n k).length = 3*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [gates,ih]; omega
private theorem types (n k : Nat) : ∀ g ∈ gates n k, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => simp [gates]
  | succ k ih => intro g h
                 simp [gates] at h
                 rcases h with h|rfl|rfl|rfl
                 · exact ih _ h
                 all_goals simp [pair]
private def run (gs : List Gate) (x : List Bool) := (Circuit.mk gs 0).wires x
private def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private theorem lenRun (gs : List Gate) (x : List Bool) : (run gs x).length = x.length+gs.length := by
  change (gs.foldl step x).length = _
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [List.foldl,ih,step]; omega
private theorem readPair (w : List Bool) (op : GateOp) (i j : Nat) :
    step w (pair op i j) = w ++ [op.eval [w.getD i false,w.getD j false]] := by rfl
private theorem appendLast (w : List Bool) (b : Bool) :
    (w++[b]).getD w.length false = b := by simp [List.getD_append_right]
private theorem inputs (gs : List Gate) (x : List Bool) (i : Nat) (hi : i<x.length) :
    (run gs x).getD i false = x.getD i false := by
  change (gs.foldl step x).getD i false = _
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step x g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi
private theorem update (a b v : Bool) (z : Nat) (hi : (a=true ↔ 1≤z) ∧ (b=true ↔ 2≤z)) :
    ((a || v) = true ↔ 1 ≤ z + if (v == true) = true then 1 else 0) ∧
    ((b || a && v) = true ↔ 2 ≤ z + if (v == true) = true then 1 else 0) := by
  obtain ⟨h₁,h₂⟩ := hi
  cases v <;> simp [h₁,h₂] <;> omega
private theorem invariant (n k : Nat) (x : List Bool) (hx : x.length=n) (hk : k<n) :
    let w := run (gates n k) x
    (w.getD (anyIdx n k) false = true ↔ 1 ≤ (x.take (k+1)).count true) ∧
    (w.getD (twoIdx n k) false = true ↔ 2 ≤ (x.take (k+1)).count true) := by
  induction k with
  | zero =>
    cases x with
    | nil => simp_all
    | cons b bs =>
      subst n
      cases b <;> simp [anyIdx,twoIdx,run,gates,Circuit.wires,GateOp.eval,List.getD_append_right]
  | succ k ih =>
    let w := run (gates n k) x
    let a := w.getD (anyIdx n k) false
    let b := w.getD (twoIdx n k) false
    let v := x.getD (k+1) false
    have hw : w.length=n+3*k+1 := by simp [w,lenRun,len,hx]; omega
    have ha : anyIdx n k < w.length := by cases k <;> simp [anyIdx,hw] <;> omega
    have hb : twoIdx n k < w.length := by cases k <;> simp [twoIdx,hw] <;> omega
    have hv : k+1 < w.length := by omega
    have readv : w.getD (k+1) false = v := inputs _ _ _ (by omega)
    have hrun : run (gates n (k+1)) x = ((w ++ [a && v]) ++ [b || (a && v)]) ++ [a || v] := by
      change ((gates n k ++ _).foldl step x) = _
      rw [List.foldl_append]
      change step (step (step w _) _) _ = _
      simp only [readPair,GateOp.eval,List.all_cons,List.any_cons,List.all_nil,List.any_nil,id_eq,
        Bool.and_true,Bool.or_false]
      rw [readv]
      change ((w ++ [a && v]) ++ [_]) ++ [_] = _
      rw [List.getD_append _ _ _ _ hb,←hw,appendLast]
      rw [List.getD_append _ _ _ _ (by simp; omega : anyIdx n k < (w ++ [a && v]).length)]
      rw [List.getD_append _ _ _ _ ha]
      rw [List.getD_append _ _ _ _ (by simp; omega : k+1 < (w ++ [a && v]).length)]
      rw [List.getD_append _ _ _ _ hv,readv]
    have hi := ih (by omega)
    change (a = true ↔ _) ∧ (b = true ↔ _) at hi
    have take := List.take_concat_get' (l:=x) (i:=k+1) (by omega : k+1<x.length)
    change (_ ↔ _) ∧ (_ ↔ _)
    rw [hrun]
    have la : n+3*k+3 = (((w ++ [a && v]) ++ [b || (a && v)]).length) := by simp [hw]
    have lb : n+3*k+2 = ((w ++ [a && v]).length) := by simp [hw]
    simp only [anyIdx,twoIdx,la,lb,appendLast]
    rw [List.getD_append _ _ _ _ (by simp)]
    rw [appendLast,←take,List.count_append]
    have vx : x[k+1] = v := by simp [v,List.getD, List.getElem?_eq_getElem (by omega : k+1<x.length)]
    simp only [vx,List.count_singleton]
    exact update a b v _ hi
end PEqualNP.Outside.Threshold1101

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.Threshold1101 in
theorem PEqualNP.Outside.L_meta_1101 : ∀ n : ℕ, 2 ≤ n → ∃ C : Circuit, IsMonotoneCircuit C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.size ≤ 3*n ∧ ∀ x : List Bool, x.length = n →
    (C.eval x = true ↔ 2 ≤ x.count true) := by
  intro n hn
  let k := n-1
  refine ⟨⟨gates n k,twoIdx n k⟩,fun g h => (types n k g h).1,fun g h => (types n k g h).2,?_,?_⟩
  · change (gates n k).length ≤ _
    rw [len]; dsimp [k]; omega
  · intro x hx
    have hh := (invariant n k x hx (by dsimp [k]; omega)).2
    have eq : k+1=x.length := by dsimp [k]; omega
    change ((run (gates n k) x).getD (twoIdx n k) false = true ↔ _)
    simpa only [eq,List.take_length] using hh
