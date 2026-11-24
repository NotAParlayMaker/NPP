import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2159_3
    (edge01 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (edge04 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (manyEdges : let E : List ℕ := [3,6,12,24,17,33,66,132,264,160,320,288]; ∀ C : Circuit, FanInTwo C → (∀ g ∈ C.gates, g.op ≠ .not) → (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → (∀ (pre : List Gate) (g : Gate) (post : List Gate), C.gates = pre ++ g :: post → ∀ e ∈ E, ∃ j ∈ E, j ≠ e ∧ (C.wires (List.ofFn (fun k : Fin 9 => Nat.testBit j k.val))).getD (9+pre.length) false = true) → 16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
    simp [step]

  have step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
      (step w g).getD i false = w.getD i false := by
    simp [step, List.getD, List.getElem?_append_left hi]

  have step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
      (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    subst hk
    simp [step, List.getD]

  have all_true (l : List ℕ) (f : ℕ → Bool) :
      (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
    induction l with
    | nil => simp
    | cons a l ih => simp

  have any_true (l : List ℕ) (f : ℕ → Bool) :
      (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
    induction l with
    | nil => simp
    | cons a l ih => simp

  let Le (u v : List Bool) : Prop :=
    u.length = v.length ∧ ∀ t, u.getD t false = true → v.getD t false = true

  have step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (h : Le u v) : Le (step u g) (step v g) := by
    refine ⟨by rw [step_len, step_len, h.1], fun t ht => ?_⟩
    by_cases hlt : t < u.length
    · rw [step_lt _ _ _ hlt] at ht
      rw [step_lt _ _ _ (by rw [← h.1]; exact hlt)]
      exact h.2 t ht
    · by_cases heq : t = u.length
      · rw [step_last _ _ _ heq] at ht
        rw [step_last _ _ _ (heq.trans h.1)]
        rcases hop with hand | hor
        · rw [hand] at ht ⊢
          exact (all_true _ _).mpr (fun i hi => h.2 i ((all_true _ _).mp ht i hi))
        · rw [hor] at ht ⊢
          obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
          exact (any_true _ _).mpr ⟨i, hi, h.2 i hti⟩
      · rw [List.getD_eq_default _ _ (by rw [step_len]; omega)] at ht
        exact Bool.noConfusion ht

  have wires_mono (gs : List Gate)
      (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ u v : List Bool, Le u v → Le (gs.foldl step u) (gs.foldl step v) := by
    induction gs with
    | nil =>
      intro u v h
      exact h
    | cons g gs ih =>
      intro u v h
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
        (step_mono g (hg g (List.mem_cons.mpr (Or.inl rfl))) u v h)

  have eval_fold (gs : List Gate) (o : ℕ) (u : List Bool) :
      Circuit.eval ⟨gs, o⟩ u = (gs.foldl step u).getD o false := rfl

  have eval_mono (gs : List Gate) (o : ℕ)
      (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (u v : List Bool) (h : Le u v)
      (he : Circuit.eval ⟨gs, o⟩ u = true) : Circuit.eval ⟨gs, o⟩ v = true := by
    rw [eval_fold] at he ⊢
    exact (wires_mono gs hg u v h).2 o he

  have ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
      (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
    by_cases ht : t < n
    · refine ⟨ht, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
      simpa using h
    · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
      exact Bool.noConfusion h

  have ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
      (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp

  have le_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i = true → g i = true) :
      Le (List.ofFn f) (List.ofFn g) := by
    refine ⟨by simp, fun t ht => ?_⟩
    obtain ⟨hlt, hx⟩ := ofFn_getD_true f t ht
    exact (ofFn_getD_val g ⟨t, hlt⟩).trans (h _ hx)


  -- The minimal true inputs and maximal false inputs of the edge function.
  let positive : Fin 12 → ℕ := ![3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288]
  let negative : Fin 12 → ℕ := ![42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
  let row (m : ℕ) (i : Fin 9) := m.testBit i.val
  let target (x : Fin 9 → Bool) :=
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

  let gateAtRow (pre : List Gate) (g : Gate) (x : Fin 9 → Bool) :=
    let w := pre.foldl step (List.ofFn x)
    g.op.eval (g.inputs.map fun i => w.getD i false)

  have appendBit (w : List Bool) (a b : Bool) (h : a = true → b = true) :
      Le (w ++ [a]) (w ++ [b]) := by
    refine ⟨by simp, fun t ht => ?_⟩
    by_cases hl : t < w.length
    · simpa [List.getD, List.getElem?_append_left hl] using ht
    · by_cases he : t = w.length
      · subst t
        simpa [List.getD] using h (by simpa [List.getD] using ht)
      · rw [List.getD_eq_default _ _ (by simp; omega)] at ht
        contradiction

  have substituteRow (pre post : List Gate) (g h : Gate) (o : ℕ) (x : Fin 9 → Bool)
      (mono : ∀ t ∈ post, t.op = GateOp.and ∨ t.op = GateOp.or)
      (hv : gateAtRow pre g x = true → gateAtRow pre h x = true) :
      circuitFun 9 ⟨pre ++ g :: post, o⟩ x = true →
      circuitFun 9 ⟨pre ++ h :: post, o⟩ x = true := by
    change ((pre ++ g :: post).foldl step _).getD o false = true →
      ((pre ++ h :: post).foldl step _).getD o false = true
    simp only [List.foldl_append, List.foldl_cons]
    exact (wires_mono post mono _ _ (appendBit _ _ _ hv)).2 o

  -- Compare the replacement at the two boundaries and extend to every input.
  have substitute (pre post : List Gate) (g h : Gate) (o : ℕ)
      (mono : ∀ t ∈ pre ++ h :: post, t.op = GateOp.and ∨ t.op = GateOp.or)
      (correct : circuitFun 9 ⟨pre ++ g :: post, o⟩ = target)
      (hp : ∀ j, gateAtRow pre g (row (positive j)) = true → gateAtRow pre h (row (positive j)) = true)
      (hn : ∀ j, gateAtRow pre h (row (negative j)) = true → gateAtRow pre g (row (negative j)) = true) :
      circuitFun 9 ⟨pre ++ h :: post, o⟩ = target := by
    have mp := fun t (ht : t ∈ post) => mono t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
    have pos : ∀ x : Fin 9 → Bool, target x = true →
        ∃ j, ∀ k, row (positive j) k = true → x k = true := by decide
    have neg : ∀ x : Fin 9 → Bool, target x = false →
        ∃ j, ∀ k, x k = true → row (negative j) k = true := by decide
    have pt : ∀ j, target (row (positive j)) = true := by decide
    have nt : ∀ j, target (row (negative j)) = false := by decide
    funext x
    cases hx : target x with
    | true =>
      obtain ⟨j,hj⟩ := pos x hx
      exact eval_mono _ _ mono _ _ (le_ofFn _ _ hj)
        (substituteRow pre post g h o _ mp (hp j) (by rw [correct]; exact pt j))
    | false =>
      apply Bool.eq_false_iff.mpr
      intro hh
      obtain ⟨j,hj⟩ := neg x hx
      have hh' := eval_mono _ o mono _ _ (le_ofFn _ _ hj) hh
      have bad := substituteRow pre post h g o _ mp (hn j) hh'
      rw [correct, nt] at bad
      contradiction
  let value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let run (gs : List Gate) (w : List Bool) :=
    gs.foldl (fun v g => v ++ [value g v]) w
  let renamed (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩

  have transport (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
      (inside : ∀ i < w.length, f i < v.length)
      (future : ∀ i, w.length ≤ i → f i = v.length + (i - w.length))
      (same : ∀ i, w.getD i false = v.getD (f i) false) :
      ∀ i, (run gs w).getD i false = (run (gs.map (renamed f)) v).getD (f i) false := by
    induction gs generalizing w v with
    | nil => exact same
    | cons g gs ih =>
      have hv : value g w = value (renamed f g) v := by
        apply congrArg g.op.eval
        simp only [renamed,List.map_map,Function.comp_def]
        exact List.map_congr_left (fun i _ => same i)
      change ∀ i, (run gs (w ++ [value g w])).getD i false =
        (run (gs.map (renamed f)) (v ++ [value (renamed f g) v])).getD (f i) false
      apply ih
      · intro i hi
        simp only [List.length_append,List.length_cons,List.length_nil] at *
        by_cases h : i < w.length
        · have := inside i h
          omega
        · rw [future i (by omega)]
          omega
      · intro i hi
        simp only [List.length_append,List.length_cons,List.length_nil] at *
        rw [future i (by omega)]
        omega
      · intro i
        by_cases h : i < w.length
        · simpa only [List.getD_append _ _ false i h,List.getD_append _ _ false (f i) (inside i h)] using same i
        · rw [List.getD_append_right _ _ false i (by omega),
            List.getD_append_right _ _ false (f i) (by rw [future i (by omega)]; omega),future i (by omega),hv]
          simp

  have lenRun (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (w ++ [value g w])).length = _
      rw [ih]
      simp
      omega

  have keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w ++ [value g w])).getD i false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

  let insertIndex (i : ℕ) := if i < 9 then i else i+1
  let moveIndex (j i : ℕ) := if i < 9+j then insertIndex i else if i = 9+j then 9 else i

  -- Move an input-only gate to the front and relabel both sides of its old position.
  have moveToFront (pre post : List Gate) (g : Gate) (out : ℕ)
      (early : ∀ x : Fin 9 → Bool, value g (run pre (List.ofFn x)) = value g (List.ofFn x)) :
      let D : Circuit := ⟨g :: pre.map (renamed insertIndex) ++ post.map (renamed (moveIndex pre.length)),
        moveIndex pre.length out⟩
      circuitFun 9 D = circuitFun 9 ⟨pre ++ g :: post,out⟩ := by
    intro D
    funext x
    let u := List.ofFn x
    let z := value g u
    let w := run pre u
    let v := run (pre.map (renamed insertIndex)) (u ++ [z])
    have lu : u.length = 9 := by simp [u]
    have lw : w.length = 9+pre.length := by simp [w,lenRun,lu]
    have lv : v.length = 9+pre.length+1 := by simp [v,lenRun,lu]; omega
    have old : ∀ i, w.getD i false = v.getD (insertIndex i) false := by
      apply transport
      · intro i hi
        simp [insertIndex,show i<9 by omega,lu]
        omega
      · intro i hi
        simp [insertIndex,show ¬i<9 by omega,lu]
        omega
      · intro i
        by_cases h : i<9
        · simp only [insertIndex,ite_eq_left h,List.getD_append _ _ false i (by omega : i < u.length)]
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp [insertIndex,h,lu]; omega)]
    have newWire : v.getD 9 false = z := by
      rw [show v.getD 9 false = (u ++ [z]).getD 9 false from keeps _ _ _ (by simp [lu])]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [lu]
    have sim := transport (moveIndex pre.length) post (w ++ [value g w]) v
    have result : (run post (w ++ [value g w])).getD out false =
        (run (post.map (renamed (moveIndex pre.length))) v).getD (moveIndex pre.length out) false := by
      apply sim
      · simp only [List.length_append,List.length_cons,List.length_nil,lw,lv]
        intro i hi
        simp only [moveIndex,insertIndex]
        split_ifs <;> omega
      · simp only [List.length_append,List.length_cons,List.length_nil,lw,lv]
        intro i hi
        simp [moveIndex,show ¬i < 9+pre.length by omega,show i ≠ 9+pre.length by omega]
        omega
      · intro i
        by_cases h : i < 9+pre.length
        · simpa only [moveIndex,ite_eq_left h,List.getD_append _ _ false i (by omega : i<w.length)] using old i
        · by_cases he : i = 9+pre.length
          · subst i
            rw [List.getD_append_right _ _ _ _ (by omega)]
            simp only [moveIndex,lt_irrefl,ite_false,ite_true,newWire,lw,Nat.sub_self,List.getD_cons_zero]
            exact early x
          · rw [List.getD_eq_default _ _ (by simp [lw]; omega),
                List.getD_eq_default _ _ (by simp [moveIndex,h,he,lv]; omega)]
    dsimp [D,circuitFun,Circuit.eval,Circuit.wires] at *
    simpa only [run,List.foldl_append,List.foldl_cons,value,w,v,u,z] using result.symm
  -- Graph automorphisms take every edge to one of two representative edges.
  let maps : Fin 12 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],
  ![0,5,8,3,4,1,7,6,2],
  ![1,0,5,8,6,2,4,7,3],
  ![1,2,3,8,6,0,7,4,5],
  ![2,1,0,5,7,3,6,4,8],
  ![2,3,8,5,7,1,4,6,0],
  ![3,2,1,0,4,8,7,6,5],
  ![3,8,5,0,4,2,6,7,1],
  ![5,0,1,2,7,8,4,6,3],
  ![5,8,3,2,7,0,6,4,1],
  ![8,3,2,1,6,5,4,7,0],
  ![8,5,0,1,6,3,7,4,2]]
  let bound (a b : Fin 9) := ∀ C : Circuit, FanInTwo C →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x a && x b)) →
    circuitFun 9 C = target → 16 ≤ C.size

  have orbit (s : bound 0 1) (t : bound 0 4) (a b : Fin 9)
      (edge : target (fun i => decide (i=a ∨ i=b)) = true) : bound a b := by
    have pick : ∀ a b : Fin 9, target (fun i => decide (i=a ∨ i=b)) = true →
        ∃ p : Fin 12, (maps p a = 0 ∧ (maps p b = 1 ∨ maps p b = 4)) ∨
          (maps p b = 0 ∧ (maps p a = 1 ∨ maps p a = 4)) := by decide
    have invariant : ∀ p : Fin 12, ∀ x : Fin 9 → Bool, target (fun i => x (maps p i)) = target x := by decide
    obtain ⟨p,hp⟩ := pick a b edge
    intro C fan first correct
    let f (i : ℕ) := if hi : i<9 then (maps p ⟨i,hi⟩).val else i
    let D : Circuit := ⟨C.gates.map (renamed f),f C.output⟩
    have sim (x : Fin 9 → Bool) (i : ℕ) :
        (C.wires (List.ofFn fun k => x (maps p k))).getD i false = (D.wires (List.ofFn x)).getD (f i) false := by
      apply transport
      · intro j hj
        simp only [List.length_ofFn] at *
        simp [f,hj]
      · intro j hj
        simp only [List.length_ofFn] at *
        simp [f,show ¬j<9 by omega]
        omega
      · intro j
        by_cases hj : j<9
        · simp only [f,dite_eq_left hj]
          exact (ofFn_getD_val (fun k => x (maps p k)) ⟨j,hj⟩).trans (ofFn_getD_val x (maps p ⟨j,hj⟩)).symm
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [f,hj]; omega)]
    have df : FanInTwo D := by
      intro g hg
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
      simpa [renamed] using fan k hk
    have dc : circuitFun 9 D = target := by
      funext x
      exact (sim x C.output).symm.trans ((congrFun correct _).trans (invariant p x))
    have dg (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x (maps p a) && x (maps p b)) := by
      exact (sim x 9).symm.trans (first _)
    have bd : 16 ≤ D.size := by
      rcases hp with ⟨ha,hb|hb⟩|⟨hb,ha|ha⟩
      · exact s D df (by simpa [ha,hb] using dg) dc
      · exact t D df (by simpa [ha,hb] using dg) dc
      · exact s D df (by simpa [ha,hb,Bool.and_comm] using dg) dc
      · exact t D df (by simpa [ha,hb,Bool.and_comm] using dg) dc
    change 16 ≤ C.gates.length
    change 16 ≤ (C.gates.map (renamed f)).length at bd
    simpa using bd
  let E : List ℕ := [3,6,12,24,17,33,66,132,264,160,320,288]
  let A : Fin 12 → Fin 9 := ![0,1,2,3,4,0,1,2,3,5,6,8]
  let B : Fin 12 → Fin 9 := ![1,2,3,4,0,5,6,7,8,7,8,5]
  have indexed : ∀ m ∈ E, ∃ i, positive i = m := by decide
  have member : ∀ i, positive i ∈ E := by decide
  have adjacent : ∀ i, target (fun k => decide (k=A i ∨ k=B i)) = true := by decide
  have on : ∀ i j, positive i = positive j → row (positive j) (A i) && row (positive j) (B i) := by decide
  have off : ∀ i j, (row (negative j) (A i) && row (negative j) (B i)) = false := by decide
  intro C fan noNot first correct
  by_contra! small
  apply Nat.not_lt_of_ge (manyEdges C fan noNot first correct ?_) small
  intro pre g post splitG e he
  by_contra! single
  obtain ⟨i,rfl⟩ := indexed e he
  let h : Gate := ⟨.and,[(A i).val,(B i).val]⟩
  have raw (x : Fin 9 → Bool) : value h (List.ofFn x) = (x (A i) && x (B i)) := by
    change ((List.ofFn x).getD (A i).val false && ((List.ofFn x).getD (B i).val false && true)) = _
    rw [ofFn_getD_val,ofFn_getD_val]
    simp
  have early (x : Fin 9 → Bool) : value h (run pre (List.ofFn x)) = value h (List.ofFn x) := by
    simp only [value,h,List.map_cons,List.map_nil]
    rw [keeps _ _ _ (by simp), keeps _ _ _ (by simp)]
  have gateVal (x : Fin 9 → Bool) : gateAtRow pre h x = (x (A i) && x (B i)) := (early x).trans (raw x)
  have oldVal (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD (9+pre.length) false = gateAtRow pre g x := by
    change (run C.gates (List.ofFn x)).getD _ false = _
    rw [splitG]
    change ((pre ++ g :: post).foldl (fun v t => v ++ [value t v]) _).getD _ _ = _
    rw [List.foldl_append,List.foldl_cons]
    let w := run pre (List.ofFn x)
    have hl : w.length = 9+pre.length := by simp [w,lenRun]
    change (run post (w ++ [value g w])).getD _ false = _
    rw [keeps _ _ _ (by simp [hl]), ← hl]
    simp [List.getD]
    rfl
  have original : circuitFun 9 ⟨pre ++ g :: post,C.output⟩ = target := by
    rw [← splitG]; exact correct
  have fixed := substitute pre post g h C.output (by
    intro t ht
    rcases List.mem_append.mp ht with hp|ht
    · have hm := fan t (splitG ▸ List.mem_append_left _ hp)
      have nn := noNot t (splitG ▸ List.mem_append_left _ hp)
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm
      tauto
    · rcases List.mem_cons.mp ht with rfl|ht
      · exact Or.inl rfl
      · have hm := fan t (splitG ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ht))
        have nn := noNot t (splitG ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ht))
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm
        tauto) original (by
      intro j hj
      rw [gateVal]
      apply on
      by_contra hn
      have hh := single (positive j) (member j) (Ne.symm hn)
      rw [oldVal] at hh
      exact hh hj) (by
      intro j hj
      rw [gateVal,off] at hj
      contradiction)
  let D : Circuit := ⟨h :: pre.map (renamed insertIndex) ++ post.map (renamed (moveIndex pre.length)),moveIndex pre.length C.output⟩
  have dBound : 16 ≤ D.size := by
    apply orbit edge01 edge04 (A i) (B i) (adjacent i) D
    · intro t ht
      change t ∈ (h :: pre.map _ ++ post.map _) at ht
      simp only [List.mem_cons,List.mem_append,List.mem_map] at ht
      rcases ht with (rfl | ⟨t',ht',rfl⟩) | ⟨t',ht',rfl⟩
      · simp [h]
      · simpa [renamed] using fan t' (splitG ▸ List.mem_append_left _ ht')
      · simpa [renamed] using fan t' (splitG ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ht'))
    · intro x
      change (run (pre.map _ ++ post.map _) (List.ofFn x ++ [value h (List.ofFn x)])).getD 9 false = _
      rw [keeps _ _ _ (by simp)]
      simpa [List.getD] using raw x
    · exact (moveToFront pre post h C.output early).trans fixed
  have eqSize : D.size = C.size := by
    change (h :: pre.map _ ++ post.map _).length = C.gates.length
    rw [splitG]
    simp
    omega
  omega
