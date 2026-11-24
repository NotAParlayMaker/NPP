import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- L-meta-1672 excludes the graph circuit even if its required first gate is unused.
-- This forces every remaining counterexample to have exactly fifteen useful gates.
theorem PEqualNP.Outside.R_meta_3095_2 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) →
    (let E : List (Fin 9 × Fin 9) :=
       [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
     let f := fun x : Fin 9 → Bool => E.any fun p => x p.1 && x p.2
     ¬ ∃ C : Circuit, IsMinimalCircuit 9 C ∧ C.size = 15 ∧ C.output = 23 ∧
       (∃ tail : List Gate, C.gates = ⟨GateOp.or,[0,1]⟩ :: tail) ∧
       circuitFun 9 C = f ∧
       ∀ (v : Fin 9) (S : Finset ℕ),
         (∀ j ∈ S, j < C.size ∧
           ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
             (C.wires (List.ofFn x)).getD (9+j) false = b) ∨
            ∃ i < 9+j, ∀ x : Fin 9 → Bool, x v = false →
             (C.wires (List.ofFn x)).getD (9+j) false =
             (C.wires (List.ofFn x)).getD i false)) →
          (v ∈ [(0 : Fin 9),1,2,3,5,8] → S.card ≤ 3) ∧ (v ∈ [(4 : Fin 9),6,7] → S.card ≤ 2)) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin (9 : ℕ)) (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x1.size ∧ ((∃ (x9 : Bool), ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = x9) ∨ ∃ x9 < (9 : ℕ) + x7, ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = (x1.wires (List.ofFn x10)).getD x9 Bool.false)) → (x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] → x6.card ≤ (3 : ℕ)) ∧ (x5 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6.card ≤ (2 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro other normalized C hC hfirst htarget hbound
  let edges : List (Fin 9 × Fin 9) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let f := fun x : Fin 9 → Bool => edges.any fun p => x p.1 && x p.2
  change circuitFun 9 C = f at htarget
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have ext_wires (gs : List Gate) (w : List Bool) :
      ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t,ht,hlen⟩ := ih (w ++ [b])
      exact ⟨b :: t, by change gs.foldl step (w ++ [b]) = _; rw [ht]; simp,
        by simp [hlen]⟩
  have wires_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    obtain ⟨t,ht,hlen⟩ := ext_wires gs w
    simp [ht, hlen]
  have read_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    obtain ⟨t,ht,_⟩ := ext_wires gs w
    rw [ht, List.getD_append _ _ _ _ hi]
  have get_snoc (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    simp [List.getD_eq_getElem?_getD]
  have get_else (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    by_cases h : i < w.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have lower (B : Circuit) (hB : FanInTwo B) (hb : circuitFun 9 B = f) : 15 ≤ B.size := by
    let index := fun i : ℕ => if i < 9 then i else i+1
    let rewire := fun g : Gate => Gate.mk g.op (g.inputs.map index)
    let a : Gate := ⟨.and,[4,6]⟩
    let A : Circuit := ⟨a :: B.gates.map rewire, index B.output⟩
    have hA : FanInTwo A := by
      intro g hg
      change g ∈ a :: B.gates.map rewire at hg
      rcases List.mem_cons.mp hg with rfl | h
      · simp [a]
      · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp h
        simpa [rewire] using hB old hold
    have attach (gs : List Gate) (old new : List Bool)
        (hmin : 9 ≤ old.length) (hlen : new.length = old.length+1)
        (hr : ∀ i, old.getD i false = new.getD (index i) false) :
        ∀ i, (gs.foldl step old).getD i false =
          ((gs.map rewire).foldl step new).getD (index i) false := by
      induction gs generalizing old new with
      | nil => exact hr
      | cons g gs ih =>
        let b := g.op.eval (g.inputs.map fun i => old.getD i false)
        have eqstep : step new (rewire g) = new ++ [b] := by
          simp only [step, rewire, b, List.map_map, Function.comp_def, hr]
        change (∀ i, (gs.foldl step (old ++ [b])).getD i false =
          ((gs.map rewire).foldl step (step new (rewire g))).getD (index i) false)
        rw [eqstep]
        apply ih
        · simp; omega
        · simp [hlen]
        · intro i
          have hi : index old.length = new.length := by
            simp [index, hlen, show ¬ old.length < 9 by omega]
          by_cases h : i = old.length
          · rw [h, hi, get_snoc, get_snoc]
          · have hn : index i ≠ new.length := by
              unfold index
              split <;> omega
            rw [get_else _ _ _ h, get_else _ _ _ hn]
            exact hr i
    have prefix_eval (x : Fin 9 → Bool) :
        step (List.ofFn x) a = List.ofFn x ++ [x 4 && x 6] := by
      change List.ofFn x ++ [[(List.ofFn x).getD 4 false, (List.ofFn x).getD 6 false].all id] = _
      simp [List.ofFn_succ]
    have first_A (x : Fin 9 → Bool) :
        (A.wires (List.ofFn x)).getD 9 false = (x 4 && x 6) := by
      change ((B.gates.map rewire).foldl step (step (List.ofFn x) a)).getD 9 false = _
      rw [prefix_eval, read_prefix _ _ _ (by simp)]
      simp
    have sem_A : circuitFun 9 A = f := by
      funext x
      let w := List.ofFn x
      let v := w ++ [x 4 && x 6]
      have raw (i : ℕ) : w.getD i false = v.getD (index i) false := by
        by_cases hi : i < 9
        · have hix : index i = i := by simp [index, hi]
          rw [hix]
          exact (List.getD_append _ _ _ _ (by simpa [w] using hi)).symm
        · have hix : index i = i + 1 := by simp [index, hi]
          rw [hix]
          have hi' : w.length ≤ i := by simp [w]; omega
          have hv' : v.length ≤ i+1 := by simp [v,w]; omega
          rw [List.getD_eq_default _ _ hi', List.getD_eq_default _ _ hv']
      have e := attach B.gates w v (by simp [w]) (by simp [v]) raw B.output
      change ((B.gates.map rewire).foldl step (step (List.ofFn x) a)).getD (index B.output) false = _
      rw [prefix_eval]
      exact e.symm.trans (congrFun hb x)
    have ha := other A hA first_A (by simpa [f,edges,Bool.or_assoc] using sem_A)
    change 16 ≤ (a :: B.gates.map rewire).length at ha
    change 15 ≤ B.gates.length
    simp at ha
    omega
  by_contra hs
  have hCs : C.size = 15 := by have := lower C hC htarget; omega
  have hlen : C.gates.length = 15 := hCs
  have output_small : C.output < 24 := by
    by_contra! ho
    let y : Fin 9 → Bool := fun _ => true
    have hf := congrFun htarget y
    change (C.gates.foldl step (List.ofFn y)).getD C.output false = f y at hf
    rw [List.getD_eq_default _ _ (by rw [wires_len, hlen]; simp; omega)] at hf
    simp [f,edges,y] at hf
  have output_final : C.output = 23 := by
    by_contra ho
    let k := C.output + 1 - 9
    have hk : k ≤ 14 := by dsimp [k]; omega
    let T : Circuit := ⟨C.gates.take k,C.output⟩
    have hT : FanInTwo T := by
      intro g hg
      exact hC g (List.mem_of_mem_take hg)
    have htargetT : circuitFun 9 T = f := by
      funext x
      have hx := congrFun htarget x
      change ((C.gates.take k).foldl step (List.ofFn x)).getD C.output false = _
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _ at hx
      rw [← List.take_append_drop k C.gates, List.foldl_append,
        read_prefix _ _ _ (by rw [wires_len]; simp [hlen, Nat.min_eq_left (by omega : k ≤ 15)]; dsimp [k]; omega)] at hx
      exact hx
    have impossible := lower T hT htargetT
    change 15 ≤ (C.gates.take k).length at impossible
    simp [List.length_take, hlen, Nat.min_eq_left (by omega : k ≤ 15)] at impossible
    omega
  obtain ⟨g,gs,hgs⟩ : ∃ g gs, C.gates = g :: gs := by
    cases h : C.gates with
    | nil => simp [h] at hlen
    | cons g gs => exact ⟨g,gs,rfl⟩
  let first : Gate := ⟨.or,[0,1]⟩
  let D : Circuit := ⟨first :: gs,C.output⟩
  have dsize : D.size = 15 := by
    change (first :: gs).length = 15
    simpa only [List.length_cons, hgs] using hlen
  have dlegal : FanInTwo D := by
    intro b hb
    change b ∈ first :: gs at hb
    rcases List.mem_cons.mp hb with rfl | h
    · simp [first]
    · exact hC b (hgs.symm ▸ List.mem_cons_of_mem _ h)
  have dwires (x : Fin 9 → Bool) : D.wires (List.ofFn x) = C.wires (List.ofFn x) := by
    let w := List.ofFn x
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have e : C.wires w = gs.foldl step (w ++ [b]) := by
      change C.gates.foldl step w = _
      rw [hgs]
      rfl
    have first_C := hfirst x
    change (C.wires w).getD 9 false = _ at first_C
    rw [e, read_prefix _ _ _ (by simp [w])] at first_C
    have eqb : b = (x 0 || x 1) := by
      have hb : (w ++ [b]).getD 9 false = b := by simp [w]
      rw [hb] at first_C
      exact first_C
    have fb : step w first = w ++ [x 0 || x 1] := by
      change w ++ [[w.getD 0 false, w.getD 1 false].any id] = _
      simp [w, List.ofFn_succ]
    change gs.foldl step (step w first) = C.wires w
    rw [fb, e, eqb]
  have eval_D : circuitFun 9 D = f := by
    funext x
    have h := congrFun htarget x
    change (D.wires (List.ofFn x)).getD D.output false = _
    rw [dwires]
    exact h
  have dmin : IsMinimalCircuit 9 D := by
    refine ⟨dlegal,fun B hB hEq => ?_⟩
    rw [dsize]
    exact lower B hB (hEq.trans eval_D)
  apply normalized
  refine ⟨D,dmin,dsize,output_final,⟨gs,rfl⟩,eval_D,?_⟩
  intro i S h
  apply hbound i S
  intro j hj
  have p := h j hj
  simpa only [dsize, hCs, dwires] using p
