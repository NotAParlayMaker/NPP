import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Setting a vertex to zero removes every binary AND or OR that reads it.
-- All ten deleted-vertex graphs give the same nine-variable function up to renaming.
set_option maxRecDepth 25000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_4031_418
  (deleted : ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) (15 : ℕ))
  (sparse : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
    (∀ v : Fin 10, (C.gates.filter (fun g => (!g.op.eval [false]) && g.inputs.contains v.val)).length ≤ 2) →
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) :
  ¬PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ))) (18 : ℕ) := by
  classical
  let rename : Fin 10 → Fin 10 → ℕ := ![![40,4,0,1,6,7,3,5,2,8],
    ![4,40,6,1,0,3,7,8,2,5],
    ![0,4,40,6,1,5,3,7,8,2],
    ![0,1,6,40,4,5,2,8,7,3],
    ![4,0,1,6,40,3,5,2,8,7],
    ![4,0,1,2,3,40,5,6,7,8],
    ![0,4,3,2,1,5,40,8,7,6],
    ![0,1,6,8,5,4,2,40,3,7],
    ![0,1,2,7,5,4,6,3,40,8],
    ![0,1,2,3,4,5,6,7,8,40]]
  let graph (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let minor (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let encode (v : Fin 10) (x : Fin 9 → Bool) (i : Fin 10) := (List.ofFn x).getD (rename v i) false
  have safe : ∀ v i, rename v i<9 ∨ rename v i=40 := by decide
  have erased : ∀ v, rename v v=40 := by decide
  have iso : ∀ v x, graph (encode v x)=minor x := by
    intro v x
    fin_cases v
    · change ((false && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && false) || (false && x 7) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 4 && false) || (false && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (false && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 0 && x 5) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 0 && x 4) || (x 4 && false) || (false && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && x 3) || (false && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && false) || (false && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (false && x 7) || (x 4 && x 3) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && false) || (false && x 4) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (false && x 7) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 4 && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && false) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (false && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && false)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && false) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && false) || (false && x 7) || (x 7 && x 5)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 2) || (x 6 && false) || (x 8 && x 3) || (x 5 && x 7) || (x 4 && false) || (false && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && false) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && false) || (false && x 4)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && false) || (x 5 && x 7) || (x 7 && false) || (false && x 6) || (x 6 && x 8) || (x 8 && x 5)) = minor x
      unfold minor
      simp only [Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or] <;> ac_rfl
  let evalGate (g : Gate) (w : List Bool) :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  let run (gates : List Gate) (w : List Bool) :=
    gates.foldl (fun s g => s ++ [evalGate g s]) w

  have push (l : List Gate) (g : Gate) (w : List Bool) :
      run (l ++ [g]) w = run l w ++ [evalGate g (run l w)] := by
    simp [run, List.foldl_append]

  have width (l : List Gate) (w : List Bool) :
      (run l w).length = w.length + l.length := by
    induction l using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton l g ih => simp [push, ih, Nat.add_assoc]

  have read_push (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    rcases lt_trichotomy i w.length with h | h | h
    · rw [List.getD_append _ _ _ _ h, ite_eq_right (ne_of_lt h)]
    · subst i
      simp
    · rw [ite_eq_right (ne_of_gt h), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

  intro witness
  obtain ⟨C,fan,cap,correct⟩ := witness
  let drop (v : Fin 10) (g : Gate) := (!g.op.eval [false]) && g.inputs.contains v.val
  by_cases low : ∀ v : Fin 10, (C.gates.filter (drop v)).length≤2
  · obtain ⟨x,bad⟩ := sparse C fan cap low
    exact bad (correct x)
  push Not at low
  obtain ⟨v,high⟩ := low
  have simulate (gs : List Gate) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ g.inputs.length≤2)
      (small : gs.length≤18) :
      ∃ D : List Gate, (∀ g ∈ D, g.op ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ g.inputs.length≤2) ∧
        D.length + (gs.filter (drop v)).length = gs.length ∧
        ∃ r : ℕ → ℕ, (∀ j, r j<9+D.length ∨ r j=40) ∧
        (∀ i : Fin 10, r i.val=rename v i) ∧
        ∀ (x : Fin 9 → Bool) j, (run gs (List.ofFn (encode v x))).getD j false =
          (run D (List.ofFn x)).getD (r j) false := by
    induction gs using List.reverseRecOn with
    | nil =>
      let r (j : ℕ) := if h : j<10 then rename v ⟨j,h⟩ else 40
      refine ⟨[],by simp,rfl,r,?_,?_,?_⟩
      · intro j; dsimp [r];split <;> simp_all [safe]
      · intro i; simp [r,i.isLt]
      · intro x j
        by_cases hj : j<10
        · have idx {n} (f : Fin n → Bool) (i : Fin n) : (List.ofFn f).getD i.val false=f i := by
            simp [List.getD_eq_getElem?_getD,i.isLt]
          exact (idx (encode v x) ⟨j,hj⟩).trans (by simp [r,hj,encode,run])
        · change (List.ofFn _).getD j false=(List.ofFn x).getD (r j) false
          rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]
          simp only [r,dif_neg hj]
          exact (List.getD_eq_default _ _ (by simp)).symm
    | append_singleton pre g ih =>
      obtain ⟨D,good,budget,r,bound,inputs,agree⟩ := ih
        (fun a ha => legal a (by simp [ha])) (by simp at small;omega)
      obtain ⟨op,arity⟩ := legal g (by simp)
      let k := 10+pre.length
      have preSmall : D.length≤17 := by simp at small;omega
      have far (x : Fin 9 → Bool) : (run D (List.ofFn x)).getD 40 false=false :=
        List.getD_eq_default _ _ (by rw [width,List.length_ofFn];omega)
      have falsePort (x : Fin 9 → Bool) : (run pre (List.ofFn (encode v x))).getD v.val false=false := by
        rw [agree,inputs,erased,far]
      have before (i : Fin 10) : i.val ≠ k := by dsimp [k];have := i.isLt;omega
      by_cases skip : drop v g=true
      · have data : g.op.eval [false]=false ∧ v.val ∈ g.inputs := by simpa [drop] using skip
        obtain ⟨zeroOp,mem⟩ := data
        have notNot : g.op≠.not := by intro eq;rw [eq] at zeroOp;contradiction
        have bypass : ∃ j, (j < 9+D.length ∨ j=40) ∧ ∀ x : Fin 9 → Bool,
            evalGate g (run pre (List.ofFn (encode v x))) = (run D (List.ofFn x)).getD j false := by
          rcases op with op|op|op
          · refine ⟨40,Or.inr rfl,?_⟩
            intro x
            rw [far]
            change g.op.eval _ = false
            rw [op]
            apply Bool.eq_false_iff.mpr
            intro yes
            have all := List.all_eq_true.mp yes
            exact Bool.noConfusion ((falsePort x).symm.trans (all _ (List.mem_map.mpr ⟨_,mem,rfl⟩)))
          · let j := (g.inputs.erase v.val).headD v.val
            refine ⟨r j,bound j,?_⟩
            intro x
            rw [← agree x j]
            let val := fun i => (run pre (List.ofFn (encode v x))).getD i false
            change g.op.eval (g.inputs.map val)=val j
            rw [op]
            change (g.inputs.map val).any id=val j
            have zero : val v.val=false := falsePort x
            have eq := ((List.perm_cons_erase mem).map val).any_eq (f:=id)
            have count : (g.inputs.erase v.val).length≤1 := by rw [List.length_erase_of_mem mem];omega
            cases he : g.inputs.erase v.val with
            | nil => simpa [j,he,zero] using eq
            | cons a tail =>
              have empty : tail=[] := by simpa [he] using count
              simpa [j,he,empty,zero] using eq
          · exact False.elim (notNot op)
        obtain ⟨j,legalJ,reads⟩ := bypass
        refine ⟨D,good,?_,fun i => if i=k then j else r i,?_,?_,?_⟩
        · simp [List.filter_append,skip];omega
        · intro i;by_cases eq : i=k
          · simpa [eq] using legalJ
          · simpa [eq] using bound i
        · intro i; simpa [before i] using inputs i
        · intro x i
          rw [push,read_push,width,List.length_ofFn]
          change (if i=k then _ else _) = _
          split <;> rename_i h
          · simpa [h] using reads x
          · simpa [h] using agree x i
      · let next : Gate := ⟨g.op,g.inputs.map r⟩
        have out (x : Fin 9 → Bool) : evalGate g (run pre (List.ofFn (encode v x))) =
            evalGate next (run D (List.ofFn x)) := by
          dsimp [evalGate,next];rw [List.map_map]
          apply congrArg g.op.eval
          apply List.map_congr_left;intro i _;exact agree x i
        refine ⟨D++[next],?_,?_,fun i => if i=k then 9+D.length else r i,?_,?_,?_⟩
        · intro a ha
          rcases List.mem_append.mp ha with ha|ha
          · exact good a ha
          · obtain rfl := List.mem_singleton.mp ha
            exact ⟨op,by simpa [next] using arity⟩
        · have h : drop v g=false := Bool.eq_false_iff.mpr skip
          simp [List.filter_append,h];omega
        · intro i;have b := bound i;simp only [List.length_append,List.length_singleton]
          split <;> omega
        · intro i; simpa [before i] using inputs i
        · intro x i
          rw [push,push,read_push,read_push,width,width,List.length_ofFn,List.length_ofFn]
          by_cases h : i=k
          · simpa only [show 10+pre.length=k from rfl,h,ite_true,ite_self] using out x
          · have ne : r i ≠ 9+D.length := by have := bound i;omega
            simpa only [show 10+pre.length=k from rfl,if_neg h,if_neg ne] using agree x i
  obtain ⟨D,ok,size,r,_,_,agree⟩ := simulate C.gates fan cap
  apply deleted
  refine ⟨⟨D,r C.output⟩,ok,?_,?_⟩
  · change D.length≤15
    change C.gates.length≤18 at cap
    omega
  · intro x
    exact ((agree x C.output).symm.trans (correct (encode v x))).trans (iso v x)
