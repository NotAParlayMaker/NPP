import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2159_1
    (andLower : ∀ (a b : Fin 9) (C : Circuit),
      ((a = 0 ∧ b ∈ ([1,2,3,4,6] : List (Fin 9))) ∨ (a = 4 ∧ b = 6)) → FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x a && x b)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) → 16 ≤ C.size)
    (product : ∀ (P N : List ℕ) (w : ℕ → List Bool),
      P = [3,6,12,17,24,33,66,132,160,264,288,320] →
      N = [42,50,69,104,116,138,201,208,261,276,385,402] → w = (fun r : ℕ =>
      List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 2]) →
      ∀ D : Circuit, Monotone2 D → D.size ≤ 14 → D.output < 24 →
      (∀ g ∈ D.gates, ∀ k ∈ g.inputs, k ≤ 24) →
      (∀ r ∈ P, D.eval (w r) = true) → (∀ r ∈ N, D.eval (w r) = false) →
      ∃ (j : Fin D.gates.length) (a b : Fin 9), a ≠ b ∧
        ∀ r ∈ P ++ N,
          (D.wires (w r)).getD (10+j.val) false = (r.testBit a.val && r.testBit b.val)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan noNot first correct
  let F := (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let P : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320]
  let N : List ℕ := [42,50,69,104,116,138,201,208,261,276,385,402]
  let row (r : ℕ) (i : Fin 9) := r.testBit i.val
  let w (r : ℕ) := List.ofFn (row r) ++ [r.testBit 0 || r.testBit 2]
  let step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
  let tr (m : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map m⟩
  have snoc (v : List Bool) (b : Bool) (i : ℕ) : (v ++ [b]).getD i false =
      if i < v.length then v.getD i false else if i = v.length then b else false := by
    by_cases h : i < v.length
    · rw [List.getD_append _ _ _ _ h,ite_eq_left h]
    · by_cases e : i = v.length
      · subst i; simp
      · rw [ite_eq_right h,ite_eq_right e,List.getD_eq_default _ _ (by simp; omega)]
  have len (gs : List Gate) (v : List Bool) : (gs.foldl step v).length = v.length + gs.length := by
    induction gs generalizing v with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]; omega
  have keep (gs : List Gate) (v : List Bool) (i : ℕ) (h : i < v.length) :
      (gs.foldl step v).getD i false = v.getD i false := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step v g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ h
  have sim (m : ℕ → ℕ) (gs : List Gate) (v z : List Bool)
      (old : ∀ i, v.getD i false = z.getD (m i) false)
      (lt : ∀ d i, i < v.length+d ↔ m i < z.length+d)
      (eq : ∀ d i, i = v.length+d ↔ m i = z.length+d) :
      ∀ i, (gs.foldl step v).getD i false = ((gs.map (tr m)).foldl step z).getD (m i) false := by
    induction gs generalizing v z with
    | nil => exact old
    | cons g gs ih =>
      apply ih (step v g) (step z (tr m g))
      · intro i
        have val : g.op.eval (g.inputs.map fun j => v.getD j false) =
            (tr m g).op.eval ((tr m g).inputs.map fun j => z.getD j false) := by
          simp only [tr,List.map_map,old]; rfl
        simp only [step,snoc,← val,← (show i < v.length ↔ m i < z.length by simpa using lt 0 i),
          ← (show i = v.length ↔ m i = z.length by simpa using eq 0 i),old]
      · intro d i; simpa [step,Nat.add_assoc,Nat.add_comm 1 d] using lt (d+1) i
      · intro d i; simpa [step,Nat.add_assoc,Nat.add_comm 1 d] using eq (d+1) i
  have monoC : Monotone2 C := by
    intro g hg
    obtain ⟨hop,hl⟩ := fan g hg
    exact ⟨by simpa [noNot g hg] using hop,hl⟩
  by_contra short
  have small : C.size ≤ 15 := by omega
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil =>
    have hh := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at hh
    simp at hh
  | cons g gs =>
    have sl : gs.length ≤ 14 := by change gs.length+1 ≤ 15 at small; omega
    have hval (x : Fin 9 → Bool) : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
      have h := first x
      change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at h
      rw [keep _ _ _ (by simp [step])] at h
      simpa only [step,snoc,List.length_ofFn,lt_self_iff_false,ite_false,ite_true] using h
    have agrees (r : ℕ) : (gs.foldl step (w r)).getD out false = F (row r) := by
      have h := congrFun correct (row r)
      change (gs.foldl step (step (List.ofFn (row r)) g)).getD out false = _ at h
      simpa only [step,hval,row,w,F,Fin.val_zero,show (2 : Fin 9).val = 2 from rfl] using h
    -- Every tape has length at most 24, so index 24 represents every larger, absent wire.
    let clip (i : ℕ) := min i 24
    let D : Circuit := ⟨gs.map (tr clip),clip out⟩
    have clipSim (xs : List Gate) (v z : List Bool) (hi : xs.length + v.length ≤ 24)
        (hl : z.length = v.length) (old : ∀ i, v.getD i false = z.getD (clip i) false) :
        ∀ i, (xs.foldl step v).getD i false = ((xs.map (tr clip)).foldl step z).getD (clip i) false := by
      induction xs generalizing v z with
      | nil => exact old
      | cons a xs ih =>
        have hh : v.length < 24 := by simp at hi; omega
        apply ih (step v a) (step z (tr clip a)) (by simp [step] at *; omega) (by simp [step,hl])
        intro i
        have val : a.op.eval (a.inputs.map fun j => v.getD j false) =
            (tr clip a).op.eval ((tr clip a).inputs.map fun j => z.getD j false) := by
          simp only [tr,List.map_map,old]; rfl
        have l : i < v.length ↔ clip i < z.length := by dsimp [clip]; omega
        have e : i = v.length ↔ clip i = z.length := by dsimp [clip]; omega
        simp only [step,snoc,← l,← e,← val,old]
    have tape (r i : ℕ) : (gs.foldl step (w r)).getD i false = (D.wires (w r)).getD (clip i) false := by
      apply clipSim gs _ _ (by simp [w]; omega) rfl
      intro t
      by_cases h : t ≤ 24
      · simp [clip,h]
      · rw [List.getD_eq_default _ _ (by simp [w]; omega),List.getD_eq_default _ _ (by simp [w,clip]; omega)]
    have dv (r : ℕ) : D.eval (w r) = F (row r) := (tape r out).symm.trans (agrees r)
    have pos : ∀ r ∈ P, F (row r) = true := by decide +kernel
    have neg : ∀ r ∈ N, F (row r) = false := by decide +kernel
    have dout : D.output < 24 := by
      by_contra large
      have hl : (D.wires (w 3)).length ≤ 24 := by
        change ((gs.map (tr clip)).foldl step (w 3)).length ≤ 24
        rw [len]; simp [w]; omega
      have hz : D.eval (w 3) = false := List.getD_eq_default _ _ (by omega)
      have hp := (dv 3).trans (pos 3 (by decide))
      exact Bool.false_ne_true (hz.symm.trans hp)
    have dm : Monotone2 D := by
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      simpa only [tr,List.length_map] using monoC b (List.mem_cons_of_mem g hb)
    have ds : D.size ≤ 14 := by change (gs.map (tr clip)).length ≤ 14; simpa using sl
    have di : ∀ a ∈ D.gates, ∀ k ∈ a.inputs, k ≤ 24 := by
      intro a ha k hk
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hk
      exact Nat.min_le_right _ _
    obtain ⟨j,a,b,ab,hit⟩ := product P N w rfl rfl rfl D dm ds dout di (fun r hr => (dv r).trans (pos r hr))
      (fun r hr => (dv r).trans (neg r hr))
    let left : Gate := ⟨.or,[0,2]⟩
    let head : Gate := ⟨.and,[a.val,b.val]⟩
    let pre := left :: D.gates.take j.val
    let mid := D.gates.get j
    let post := D.gates.drop (j.val+1)
    have shape : D.gates = D.gates.take j.val ++ mid :: post := by
      simp only [mid,post,List.get_eq_getElem,← List.drop_eq_getElem_cons j.isLt,List.take_append_drop]
    let k := 9+pre.length
    have kval : k = 10+j.val := by simp [k,pre,List.length_take]; omega
    -- Move wire k to position 9. Before k is computed, forward references must
    -- remain absent, so the prefix and suffix use different address maps.
    let lift (i : ℕ) := if i < 9 then i else i+1
    let perm (i : ℕ) := if i < k then lift i else if i=k then 9 else i
    let T : Circuit := ⟨head :: ((pre.map (tr lift)) ++ (post.map (tr perm))),perm D.output⟩
    have TM : Monotone2 T := by
      intro e he
      change e ∈ head :: _ at he
      rcases List.mem_cons.mp he with rfl | h
      · simp [head]
      rcases List.mem_append.mp h with h | h
      · obtain ⟨e',hm,rfl⟩ := List.mem_map.mp h
        rcases List.mem_cons.mp hm with rfl | htake
        · simp [left,tr]
        · simpa only [tr,List.length_map] using dm e' (List.mem_of_mem_take htake)
      · obtain ⟨e',hm,rfl⟩ := List.mem_map.mp h
        simpa only [tr,List.length_map] using dm e' (List.mem_of_mem_drop hm)
    have Tfan : FanInTwo T := by
      intro e he
      obtain ⟨o,l⟩ := TM e he
      refine ⟨?_,l⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at o ⊢
      tauto
    have dat (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    have hdval (x : Fin 9 → Bool) : step (List.ofFn x) head = List.ofFn x ++ [x a && x b] := by
      have ev (s t : Bool) : GateOp.and.eval [s,t] = (s && t) := by cases s <;> cases t <;> rfl
      simp only [step,head,List.map_cons,List.map_nil,dat,ev]
    have hfirst (x : Fin 9 → Bool) : (T.wires (List.ofFn x)).getD 9 false = (x a && x b) := by
      change (((pre.map (tr lift)) ++ (post.map (tr perm))).foldl step (step (List.ofFn x) head)).getD 9 false = _
      rw [hdval,keep _ _ _ (by simp),snoc]; simp
    have leftval (r : ℕ) : step (List.ofFn (row r)) left = w r := by
      have ev (s t : Bool) : GateOp.or.eval [s,t] = (s || t) := by cases s <;> cases t <;> rfl
      have h0 := dat (row r) 0
      have h2 := dat (row r) 2
      change (List.ofFn (row r)).getD 0 false = row r 0 at h0
      change (List.ofFn (row r)).getD 2 false = row r 2 at h2
      simp only [step,left,List.map_cons,List.map_nil,h0,h2,ev,w,row,Fin.val_zero,show (2 : Fin 9).val = 2 from rfl]
    have corner (r : ℕ) (hr : r ∈ P ++ N) : T.eval (List.ofFn (row r)) = F (row r) := by
      let v := List.ofFn (row r)
      let z := step v head
      let u := pre.foldl step v
      let m := (pre.map (tr lift)).foldl step z
      have vl : v.length = 9 := by simp [v]
      have zl : z.length = 10 := by simp [z,step,vl]
      have ul : u.length = k := by simp [u,len,vl,k]
      have ml : m.length = k+1 := by simp [m,len,zl,k]; omega
      have hstart (i : ℕ) : v.getD i false = z.getD (lift i) false := by
        change _ = (step v head).getD _ false
        rw [show step v head = v ++ [row r a && row r b] from hdval _,snoc]
        by_cases h : i < 9
        · simp [lift,h,vl]
        · rw [List.getD_eq_default _ _ (by omega)]
          simp only [lift,ite_eq_right h,vl,ite_eq_right (show ¬i+1<9 by omega),ite_eq_right (show i+1≠9 by omega)]
      have hpre : ∀ i, u.getD i false = m.getD (lift i) false := by
        apply sim lift pre v z hstart
        · intro d i; simp only [vl,zl,lift]; split <;> omega
        · intro d i; simp only [vl,zl,lift]; split <;> omega
      have mhead : m.getD 9 false = (row r a && row r b) := by
        rw [show m = (pre.map (tr lift)).foldl step z from rfl,keep _ _ _ (by omega)]
        change (step v head).getD _ false = _
        rw [show step v head = v ++ [row r a && row r b] from hdval _,snoc]; simp [vl]
      have decomp : D.wires (w r) = post.foldl step (step u mid) := by
        change D.gates.foldl step _ = _
        rw [shape,List.foldl_append,List.foldl_cons]
        change _ = post.foldl step (step ((D.gates.take j.val).foldl step (step v left)) mid)
        rw [show step v left = w r from leftval r]
      have prodval : (step u mid).getD k false = (row r a && row r b) := by
        have h := hit r hr
        rw [decomp,← kval,keep _ _ _ (by simp [step,ul])] at h
        exact h
      have hpost (i : ℕ) : (step u mid).getD i false = m.getD (perm i) false := by
        by_cases less : i < k
        · simp only [step,snoc,ul,less,ite_true,perm,hpre]
        · by_cases e : i = k
          · subst i; simpa [perm] using prodval.trans mhead.symm
          · rw [List.getD_eq_default _ _ (by simp [step,ul]; omega),List.getD_eq_default _ _ (by simp [perm,less,e,ml]; omega)]
      have hs := sim perm post (step u mid) m hpost
        (by intro d i; simp only [step,List.length_append,List.length_cons,List.length_nil,ul,ml,perm,lift]; split <;> split <;> omega)
        (by intro d i; simp only [step,List.length_append,List.length_cons,List.length_nil,ul,ml,perm,lift]; split <;> split <;> omega) D.output
      have tv : T.eval v = ((post.map (tr perm)).foldl step m).getD (perm D.output) false := by
        change (((pre.map (tr lift)) ++ (post.map (tr perm))).foldl step z).getD _ _ = _
        rw [List.foldl_append]
      exact tv.trans (hs.symm.trans ((congrArg (fun vs : List Bool => vs.getD D.output false) decomp.symm).trans (dv r)))
    have evalMon (x y : Fin 9 → Bool) (le : ∀ i, x i = true → y i = true) :
        T.eval (List.ofFn x) = true → T.eval (List.ofFn y) = true := by
      have run (ls : List Gate) (good : ∀ g ∈ ls, g.op = .and ∨ g.op = .or)
          (v z : List Bool) (hl : v.length = z.length)
          (rel : ∀ i, v.getD i false = true → z.getD i false = true) :
          ∀ i, (ls.foldl step v).getD i false = true → (ls.foldl step z).getD i false = true := by
        induction ls generalizing v z with
        | nil => exact rel
        | cons e ls ih =>
          apply ih (fun g hg => good g (List.mem_cons_of_mem _ hg)) (step v e) (step z e) (by simp [step,hl])
          intro i
          have va : e.op.eval (e.inputs.map fun j => v.getD j false) = true →
              e.op.eval (e.inputs.map fun j => z.getD j false) = true := by
            rcases good e (by simp) with hop | hop
            · have hand (l : List Bool) : GateOp.and.eval l = l.all id := rfl
              simp only [hop,hand,List.all_map,Function.comp_apply,id_eq,List.all_eq_true]
              exact fun h j hj => rel j (h j hj)
            · have hor (l : List Bool) : GateOp.or.eval l = l.any id := rfl
              simp only [hop,hor,List.any_map,Function.comp_apply,id_eq,List.any_eq_true]
              rintro ⟨j,hj,H⟩; exact ⟨j,hj,rel j H⟩
          simp only [step,snoc,hl]
          split
          · apply rel
          · split
            · exact va
            · exact id
      apply run T.gates (fun g hg => (TM g hg).1) _ _ (by simp) _ T.output
      intro i
      by_cases h : i < 9
      · simpa only [dat x ⟨i,h⟩,dat y ⟨i,h⟩] using le ⟨i,h⟩
      · rw [List.getD_eq_default _ _ (by simp; omega)]; simp
    -- Only the output must agree everywhere; the relocated gate need only agree on the frontier.
    have span : ∀ t : Fin 512,
        (F (row t.val) = true → ∃ r ∈ P, ∀ i, row r i = true → row t.val i = true) ∧
        (F (row t.val) = false → ∃ r ∈ N, ∀ i, row t.val i = true → row r i = true) := by decide +kernel
    have encode (x : Fin 9 → Bool) : ∃ t : Fin 512, row t.val = x := by
      let bits := BitVec.ofBoolListLE (List.ofFn x)
      have sz : bits.toNat < 512 := by simpa [bits] using bits.isLt
      have rx : row bits.toNat = x := by
        funext i
        simp only [row,bits,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
        simp [i.isLt]
      exact ⟨⟨bits.toNat,sz⟩,rx⟩
    have total : circuitFun 9 T = F := by
      funext x
      obtain ⟨t,rx⟩ := encode x
      obtain ⟨hp,hn⟩ := span t
      simp only [rx] at hp hn
      change T.eval (List.ofFn x) = F x
      cases h : F x with
      | true =>
        obtain ⟨r,hr,below⟩ := hp h
        exact evalMon _ _ below ((corner r (List.mem_append_left _ hr)).trans (pos r hr))
      | false =>
        obtain ⟨r,hr,above⟩ := hn h
        apply Bool.eq_false_iff.mpr
        intro bad
        have yes := evalMon _ _ above bad
        have no := (corner r (List.mem_append_right _ hr)).trans (neg r hr)
        exact Bool.false_ne_true (no.symm.trans yes)
    -- Send the unordered pair to one of the six AND-first statements L_meta_1667 through L_meta_1672.
    let perms : List (Fin 9 → Fin 9) := [
      ![0,1,2,3,4,5,6,7,8], ![0,5,8,3,4,1,7,6,2], ![1,0,5,8,6,2,4,7,3],
      ![1,2,3,8,6,0,7,4,5], ![2,1,0,5,7,3,6,4,8], ![2,3,8,5,7,1,4,6,0],
      ![3,2,1,0,4,8,7,6,5], ![3,8,5,0,4,2,6,7,1], ![5,0,1,2,7,8,4,6,3],
      ![5,8,3,2,7,0,6,4,1], ![8,3,2,1,6,5,4,7,0], ![8,5,0,1,6,3,7,4,2]]
    let rep (a b : Fin 9) := ((a == 0 && ([1,2,3,4,6] : List (Fin 9)).contains b) ||
      (a == 4 && b == 6))
    have covers : ∀ a b : Fin 9, a ≠ b → ∃ p ∈ perms, (rep (p a) (p b) || rep (p b) (p a)) = true := by
      decide +kernel
    have autos (p : Fin 9 → Fin 9) (hp : p ∈ perms) (x : Fin 9 → Bool) : F (x ∘ p) = F x := by
      simp only [perms,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;>
        simp only [F,Function.comp_apply,Matrix.cons_val] <;> ac_rfl
    obtain ⟨p,pm,repr⟩ := covers a b ab
    let reidx (i : ℕ) := if h : i < 9 then (p ⟨i,h⟩).val else i
    let U : Circuit := ⟨T.gates.map (tr reidx),reidx T.output⟩
    have Ufan : FanInTwo U := by
      intro g hg
      obtain ⟨g',hm,rfl⟩ := List.mem_map.mp hg
      simpa only [tr,List.length_map] using Tfan g' hm
    have rew (x : Fin 9 → Bool) : ∀ i, (T.wires (List.ofFn (x ∘ p))).getD i false =
        (U.wires (List.ofFn x)).getD (reidx i) false := by
      apply sim reidx T.gates (List.ofFn (x ∘ p)) (List.ofFn x)
      · intro i
        by_cases hi : i < 9
        · simp only [reidx,dite_eq_left hi,dat _ ⟨i,hi⟩,dat,Function.comp_apply]
        · simp only [reidx,dite_eq_right hi]; rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
      · intro d i; simp only [List.length_ofFn,reidx]; split <;> omega
      · intro d i; simp only [List.length_ofFn,reidx]; split <;> omega
    have Ufirst (x : Fin 9 → Bool) : (U.wires (List.ofFn x)).getD 9 false = (x (p a) && x (p b)) :=
      (rew x 9).symm.trans (hfirst (x ∘ p))
    have Uok : circuitFun 9 U = F := by
      funext x
      exact (rew x T.output).symm.trans ((congrFun total (x ∘ p)).trans (autos p pm x))
    have lo : 16 ≤ U.size := by
      rcases Bool.or_eq_true_iff.mp repr with h | h
      · exact andLower _ _ U (by simpa [rep] using h) Ufan Ufirst Uok
      · exact andLower _ _ U (by simpa [rep] using h) Ufan
          (fun x => (Ufirst x).trans (Bool.and_comm _ _)) Uok
    have same : U.size = T.size := List.length_map _
    have count : T.size = D.size+1 := by
      change (head :: ((pre.map (tr lift)) ++ (post.map (tr perm)))).length = D.gates.length+1
      have jj := j.isLt
      simp [pre,post,List.length_take]; omega
    omega
