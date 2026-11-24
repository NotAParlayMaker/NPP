import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the terminal gate. An input port can survive there in just one useful role:
-- an OR with the auxiliary signal for vertex one. It supplies the two edges to its neighbors.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_3913_418
  (internal : ∀ t ∈ ([1,3,4,6,8] : List (Fin 9)),
    ∀ (D : Circuit), FanInTwo D → D.size ≤ 12 → ∀ (op : GateOp), op ∈ [GateOp.and,.or,.not] →
    ∀ (J : List ℕ), J.length ≤ 2 → ∃ x : Fin 9 → Bool,
      let w := D.wires (List.ofFn x ++ [x 0 || x 2, x t && (x 0 || x 2)])
      op.eval (J.map (fun j => w.getD (11+j) false)) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  (remaining : ∀ (D : Circuit), FanInTwo D → D.size ≤ 12 → ∃ x : Fin 9 → Bool,
    let t : Fin 9 := 1
    (x 1 && (x 0 || x 2)) = false ∧ D.eval (List.ofFn x ++ [x 0 || x 2, x t && (x 0 || x 2)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
  ∀ x1 ∈ [[(1 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))]],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let encode (t : Fin 9) (x : Fin 9 → Bool) := (List.ofFn x ++ [x 0 || x 2, x t && (x 0 || x 2)])
  let ports : List (Fin 9) := [1,3,4,6,8]
  let mask (m : ℕ) (j : Fin 9) := m.testBit j.val
  let pos : List (List ℕ) := [[6, 12, 3, 3, 3, 3, 3, 3, 3, 24, 12], [6, 12, 3, 3, 3, 3, 3, 3, 3, 24, 3], [6, 12, 3, 3, 3, 3, 3, 3, 3, 24, 3], [6, 12, 3, 3, 3, 3, 3, 3, 3, 24, 3], [6, 12, 3, 3, 3, 3, 3, 3, 3, 24, 3]]
  let neg : List (List ℕ) := [[1, 2, 4, 8, 16, 32, 64, 128, 256, 1, 0], [1, 2, 4, 8, 16, 32, 64, 128, 256, 1, 9], [1, 2, 4, 8, 16, 32, 64, 128, 256, 1, 20], [1, 2, 4, 8, 16, 32, 64, 128, 256, 1, 65], [1, 2, 4, 8, 16, 32, 64, 128, 256, 1, 257]]
  have census : ∀ k : Fin 5, ∀ i : Fin 11,
      let t := ports.getD k.val 0
      let x := mask ((pos.getD k.val []).getD i.val 0)
      let y := mask ((neg.getD k.val []).getD i.val 0)
      graph x = true ∧ (encode t x).getD i.val false = false ∧
        ((t=1 ∧ i=10) ∨ (graph y=false ∧ (encode t y).getD i.val false=true)) := by
    decide
  have portsIndex : ∀ t ∈ ports, ∃ k : Fin 5, ports.getD k.val 0=t := by decide
  have widthIn (t : Fin 9) (x : Fin 9 → Bool) : (encode t x).length=11 := by simp [encode]
  have zeroG : graph (fun _ => false)=false := rfl
  have zeroIn : ∀ (t : Fin 9) (i : Fin 11), (encode t (fun _ => false)).getD i.val false=false := by decide
  have posG : graph (mask 3)=true := rfl
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

  have early (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (run gs w).getD i false=w.getD i false := by
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      rw [push,read_push,width,ite_eq_right (by omega)]
      exact ih
  have all (t : Fin 9) (ht : t ∈ ports) (gs : List Gate) (out : ℕ)
      (fan : FanInTwo (⟨gs,out⟩ : Circuit)) (lim : gs.length≤13) :
      ∃ x, (run gs (encode t x)).getD out false ≠ graph x := by
    obtain ⟨k,hk⟩ := portsIndex t ht
    induction gs using List.reverseRecOn generalizing out with
    | nil =>
      by_cases h : out<11
      · let i : Fin 11 := ⟨out,h⟩
        obtain ⟨hG,hport,_⟩ := census k i
        rw [hk] at hport
        exact ⟨_,by change (encode t _).getD out false ≠ _; rw [show out=i.val from rfl,hport,hG];decide⟩
      · exact ⟨mask 3,by change (encode t _).getD out false ≠ _;rw [List.getD_eq_default _ _ (by rw [widthIn];omega),posG];decide⟩
    | append_singleton pre g ih =>
      have ok (o : ℕ) : FanInTwo (⟨pre,o⟩ : Circuit) := fun z hz => fan z (by simp [hz])
      have cap : pre.length≤12 := by simp at lim;omega
      by_cases last : out=11+pre.length
      · let D : Circuit := ⟨pre,0⟩
        let val (x : Fin 9 → Bool) (j : ℕ) := (run pre (encode t x)).getD j false
        have raw (x : Fin 9 → Bool) (i : Fin 11) : val x i.val=(encode t x).getD i.val false :=
          early _ _ _ (by rw [widthIn];exact i.isLt)
        have endval (x : Fin 9 → Bool) : (run (pre++[g]) (encode t x)).getD out false =
            g.op.eval (g.inputs.map (val x)) := by
          rw [push,read_push,width,widthIn,ite_eq_left last]
        by_contra! yes
        have exactG (x) : g.op.eval (g.inputs.map (val x))=graph x := (endval x).symm.trans (yes x)
        obtain ⟨legal,small⟩ := fan g (by simp)
        have opMem : g.op ∈ [GateOp.and,.or,.not] := by simpa using legal
        have tail (J : List ℕ) (bound : J.length≤2) (later : ∀ j ∈ J, 11 ≤ j)
            (same : ∀ x, g.op.eval (J.map (val x))=graph x) : False := by
          obtain ⟨x,bad⟩ := internal t ht D (ok 0) cap g.op opMem (J.map (fun a => a-11)) (by simpa)
          apply bad
          change g.op.eval (List.map (fun i => val x (11+i)) (J.map (fun a => a-11))) = graph x
          rw [List.map_map]
          convert same x using 2
          apply List.map_congr_left
          intro i hi
          have le := later i hi
          simp [Function.comp_def,Nat.add_sub_of_le le]
        by_cases more : ∀ j ∈ g.inputs, 11 ≤ j
        · exact tail _ small more exactG
        push Not at more
        obtain ⟨j,hj,short⟩ := more
        let i : Fin 11 := ⟨j,short⟩
        obtain ⟨positive,pOff,negative⟩ := census k i
        rw [hk] at pOff negative
        rcases legal with op | op | op
        · let x := mask ((pos.getD k.val []).getD i.val 0)
          have h := exactG x
          rw [op,positive] at h
          change (g.inputs.map (val x)).all id = true at h
          have hit := List.all_eq_true.mp h _ (List.mem_map.mpr ⟨j,hj,rfl⟩)
          have off : val x j = false := (raw x i).trans pOff
          change val x j = true at hit
          rw [off] at hit;contradiction
        · rcases negative with ⟨ht1,hi⟩ | ⟨hG,hwire⟩
          · clear hk
            subst t
            have ji : j=10 := congrArg Fin.val hi
            have hit : 10 ∈ g.inputs := ji ▸ hj
            have count : (g.inputs.erase 10).length ≤ 1 := by
              rw [List.length_erase_of_mem hit];omega
            let fallback := 11+pre.length
            let other := (g.inputs.erase 10).headD fallback
            obtain ⟨x,h10,wrong⟩ := remaining (⟨pre,other⟩ : Circuit) (ok other) cap
            have signal : val x 10=false := (raw x 10).trans (by exact h10)
            have missing : val x fallback=false := List.getD_eq_default _ _ (by dsimp [fallback];rw [width,widthIn])
            have v := exactG x
            rw [op] at v
            change (g.inputs.map (val x)).any id = graph x at v
            have reduce : (g.inputs.map (val x)).any id = val x other := by
              have perm := List.perm_cons_erase hit
              have eq := (perm.map (val x)).any_eq (f:=id)
              dsimp [other]
              cases he : g.inputs.erase 10 with
              | nil => simpa [he,signal,missing] using eq
              | cons a tail =>
                have empty : tail=[] := by simpa [he] using count
                simpa [he,empty,signal] using eq
            exact wrong (reduce.symm.trans v)
          · let x := mask ((neg.getD k.val []).getD i.val 0)
            have h := exactG x
            rw [op,hG] at h
            change (g.inputs.map (val x)).any id = false at h
            have on : val x j = true := (raw x i).trans hwire
            have any := List.any_eq_true.mpr (show ∃ a ∈ g.inputs.map (val x), id a = true from
              ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,on⟩)
            rw [h] at any;contradiction
        · have firstVal (x) : g.op.eval ((g.inputs.take 1).map (val x))=graph x := by
            have h := exactG x
            rw [op] at h ⊢
            cases e : g.inputs with
            | nil => simpa [e] using h
            | cons a l =>
              rw [e] at h
              have headNot (b : Bool) (bs : List Bool) : GateOp.not.eval (b::bs) = !b := by rfl
              simpa only [List.take_succ_cons,List.take_zero,List.map_cons,List.map_nil,headNot] using h
          by_cases earlier : ∀ a ∈ g.inputs.take 1, 11≤a
          · exact tail _ (by simp) earlier firstVal
          push Not at earlier
          obtain ⟨a,ha,low⟩ := earlier
          have on := firstVal (fun _ => false)
          rw [op,zeroG] at on
          have one : g.inputs.take 1=[a] := by
            cases e : g.inputs with
            | nil => simp [e] at ha
            | cons b bs =>
              have ab : a=b := by simpa [e] using ha
              simp [ab]
          rw [one] at on
          have off := (raw (fun _ => false) ⟨a,low⟩).trans (zeroIn t ⟨a,low⟩)
          change (!(val (fun _ => false) a)) = false at on
          rw [off] at on;contradiction
      · obtain ⟨x,bad⟩ := ih out (ok out) (by omega)
        exact ⟨x,by rw [push,read_push,width,widthIn,ite_eq_right last];exact bad⟩
  intro l hl C fan size
  have applyCase (t : Fin 9) (ht : t ∈ ports) :
      ∃ x : Fin 9 → Bool, C.eval (encode t x) ≠ graph x := all t ht C.gates C.output fan size
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  have and2 (a b : Bool) : GateOp.and.eval [a,b]= (a && b) := by cases a <;> cases b <;> rfl
  have lift (t : Fin 9) (ht : t ∈ ports) (a : Fin 11) (ha : a.val=t.val) :
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 2]
        C.eval (w ++ [GateOp.and.eval ([a,9].map (fun v : Fin 11 => w.getD v.val false))]) ≠ graph x := by
    obtain ⟨x,bad⟩ := applyCase t ht
    refine ⟨x,?_⟩
    dsimp only
    have first : (List.ofFn x ++ [x 0 || x 2]).getD a.val false = x t := by
      rw [List.getD_append _ _ _ _ (by simp [ha]),ha]
      have atIndex {n : Nat} (f : Fin n → Bool) (i : Fin n) :
          (List.ofFn f).getD i.val false = f i := by simp [List.getD_eq_getElem?_getD,i.isLt]
      exact atIndex x t
    have last : (List.ofFn x ++ [x 0 || x 2]).getD (9 : Fin 11).val false = (x 0 || x 2) := by rfl
    simpa only [List.map_cons,List.map_nil,first,last,and2,List.append_assoc,List.cons_append,
      List.nil_append,encode] using bad
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · exact lift 1 (by decide) 1 rfl
  · exact lift 3 (by decide) 3 rfl
  · exact lift 4 (by decide) 4 rfl
  · exact lift 6 (by decide) 6 rfl
  · exact lift 8 (by decide) 8 rfl
