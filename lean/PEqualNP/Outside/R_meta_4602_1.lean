import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4602_1
    (trace : have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (26 : ℕ) ∧ x2.Nodup ∧ (∀ x3 ∈ x2, x3 ∉ x1) ∧ (2097151 : ℕ) ∈ x2 ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5)
    (orbit : let S : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let N : List ℕ := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
      let D : List ℕ := [64, 256, 448, 1429, 1557, 2389, 3669, 1494, 1558, 1750, 1942, 2390, 2902, 1688, 1880, 2008]
      ∀ i j : Fin 58, i ≠ j → (i.val < 21 ↔ j.val < 21) →
        ∃ d ∈ D, ∃ p : ℕ → ℕ,
          ((p (d % 64) = i.val ∧ p (d / 64) = j.val) ∨
           (p (d % 64) = j.val ∧ p (d / 64) = i.val)) ∧
          (∀ r : Fin 59, p r.val < 21 ↔ r.val < 21) ∧
          ∀ x ∈ S, ∃ y ∈ N, ∀ r : Fin 59, x.testBit (p r.val) = y.testBit r.val) :
    have x1 : List (BitVec (59 : ℕ)) := [(95229015649944073 : BitVec (59 : ℕ)), (63038587928642 : BitVec (59 : ℕ)), (256463372304 : BitVec (59 : ℕ)), (4292497062825988 : BitVec (59 : ℕ)), (8521482511360 : BitVec (59 : ℕ)), (14003410187716736 : BitVec (59 : ℕ)), (55389823206179104 : BitVec (59 : ℕ)), (189297016294080519 : BitVec (59 : ℕ)), (155696362464215096 : BitVec (59 : ℕ)), (218994303131713984 : BitVec (59 : ℕ)), (183565875465424384 : BitVec (59 : ℕ)), (229736628136996864 : BitVec (59 : ℕ)), (270286071508729856 : BitVec (59 : ℕ)), (288160007409369088 : BitVec (59 : ℕ))]; have x2 : List ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)]; ∃ (x3 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))) (x4 : Fin (39 : ℕ)) (x5 : Fin (39 : ℕ)) (x6 : Fin (16 : ℕ)),   x3.length = (25 : ℕ) ∧     (14 : ℕ) ≤ ↑x4 ∧       x4 < x5 ∧         have x7 : ℕ := x2.getD ↑x6 (0 : ℕ);         have x8 : ℕ := x7 % (64 : ℕ);         have x9 : ℕ := x7 / (64 : ℕ);         have x10 : List (BitVec (59 : ℕ)) := List.foldl (fun (x10 : List (BitVec (59 : ℕ))) (x11 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x10 ++ [if x11.1 = Bool.true then x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) ||| x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ)) else x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) &&& x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ))]) x1 x3;         have x11 : BitVec (59 : ℕ) := x10.getD ↑x4 (0 : BitVec (59 : ℕ));         have x12 : BitVec (59 : ℕ) := x10.getD ↑x5 (0 : BitVec (59 : ℕ));         (if x8 < (21 : ℕ) then x11 ||| x12 else x11 &&& x12) = (2097151 : BitVec (59 : ℕ)) ∧ x11.getLsbD x8 ≠ x12.getLsbD x8 ∧ x11.getLsbD x8 = x12.getLsbD x9 ∧ x12.getLsbD x8 = x11.getLsbD x9 := by
  classical
  let S : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let N : List ℕ := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
  let D : List ℕ := [64, 256, 448, 1429, 1557, 2389, 3669, 1494, 1558, 1750, 1942, 2390, 2902, 1688, 1880, 2008]
  let T : ℕ := 2097151
  let B := N.map (BitVec.ofNat 59)
  let gate := fun (w : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) => w ++ [if g.1 = true then w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0 else w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0]
  have blen : B.length = 14 := rfl
  obtain ⟨ws,hlen,hnd,_,hm,hrule⟩ := trace
  change T ∈ ws at hm
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hm
  have rule (i : ℕ) (hi : i < ws.length) : ∃ a ∈ S ++ ws.take i, ∃ b ∈ S ++ ws.take i, ws[i] = a &&& b ∨ ws[i] = a ||| b := hrule ⟨i,hi⟩
  have bound (i : ℕ) (hi : i < ws.length) : ws[i] < 2^58 := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      obtain ⟨a,ha,b,hb,hop⟩ := rule i hi
      have good (v : ℕ) (hv : v ∈ S ++ ws.take i) : v < 2^58 := by
        rcases List.mem_append.mp hv with hs | hp
        · exact (show ∀ x ∈ S, x < 2^58 by decide +kernel) v hs
        · obtain ⟨j,hj,hv⟩ := List.mem_take_iff_getElem.mp hp
          exact hv ▸ ih j (by omega) (by omega)
      rcases hop with h | h
      · rw [h]; exact Nat.and_lt_two_pow _ (good b hb)
      · rw [h]; exact Nat.or_lt_two_pow (good a ha) (good b hb)
  have tb (r : ℕ) : T.testBit r = decide (r < 21) := Nat.testBit_two_pow_sub_one 21 r
  obtain ⟨a,ha,b,hb,hop⟩ := rule k hk
  rw [he] at hop
  obtain ⟨o,ho⟩ : ∃ o : Bool, T = (if o then a ||| b else a &&& b) := by
    rcases hop with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have bitop (r : ℕ) : decide (r < 21) = if o then a.testBit r || b.testBit r else a.testBit r && b.testBit r := by
    rw [← tb,ho]; cases o <;> simp [Nat.testBit_and,Nat.testBit_or]
  -- An OR operand cannot add a false positive; an AND operand cannot miss a positive.
  -- Every seed makes both kinds of error, so both operands are prior gate outputs.
  have seedbad : ∀ x ∈ S, (∃ i : Fin 21, x.testBit i.val = false) ∧ (∃ j : Fin 37, x.testBit (21+j.val) = true) := by decide +kernel
  have notseed (x : ℕ) (h : x = a ∨ x = b) : x ∉ S := by
    intro hs
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := seedbad x hs
    have ei := bitop i.val
    have ej := bitop (21+j.val)
    simp only [decide_eq_true i.isLt] at ei
    simp only [show ¬21+j.val < 21 by omega, decide_false] at ej
    rcases h with rfl | rfl <;> cases o <;> simp [hi,hj] at ei ej
  obtain ⟨ia,hia,ea⟩ := List.mem_take_iff_getElem.mp ((List.mem_append.mp ha).resolve_left (notseed a (.inl rfl)))
  obtain ⟨ib,hib,eb⟩ := List.mem_take_iff_getElem.mp ((List.mem_append.mp hb).resolve_left (notseed b (.inr rfl)))
  have aT : a ≠ T := by intro h; have := hnd.getElem_inj.mp (ea.trans (h.trans he.symm)); omega
  have bT : b ≠ T := by intro h; have := hnd.getElem_inj.mp (eb.trans (h.trans he.symm)); omega
  have abnd : a < 2^58 := ea ▸ bound ia (by omega)
  have bbnd : b < 2^58 := eb ▸ bound ib (by omega)
  have diff (x : ℕ) (hx : x ≠ T) (hbnd : x < 2^58) : ∃ r : Fin 58, x.testBit r.val ≠ decide (r.val < 21) := by
    obtain ⟨r,hr⟩ := Nat.exists_testBit_ne_of_ne hx
    have sm : r < 58 := by
      by_contra! hn
      have le : 2^58 ≤ 2^r := Nat.pow_le_pow_right (by decide) hn
      rw [Nat.testBit_lt_two_pow (by omega),tb,decide_eq_false (by omega)] at hr
      exact hr rfl
    exact ⟨⟨r,sm⟩,by simpa only [tb] using hr⟩
  -- Neither operand equals the target. Their errors witness opposite orientations
  -- on two rows of the same label: positive for OR and negative for AND.
  obtain ⟨i,hi⟩ := diff a aT abnd
  obtain ⟨j,hj⟩ := diff b bT bbnd
  have ei := bitop i.val
  have ej := bitop j.val
  have orient : decide (i.val < 21) = o ∧ decide (j.val < 21) = o ∧ a.testBit i.val = !o ∧ b.testBit i.val = o ∧ a.testBit j.val = o ∧ b.testBit j.val = !o := by
    revert ei ej hi hj
    generalize decide (i.val < 21) = u
    generalize decide (j.val < 21) = v
    generalize a.testBit i.val = ai
    generalize b.testBit i.val = bi
    generalize a.testBit j.val = aj
    generalize b.testBit j.val = bj
    cases o <;> cases u <;> cases v <;> cases ai <;> cases bi <;> cases aj <;> cases bj <;> decide
  obtain ⟨oi,oj,ai,bi,aj,bj⟩ := orient
  have ij : i ≠ j := by intro h; rw [h,aj] at ai; cases o <;> contradiction
  have same : i.val < 21 ↔ j.val < 21 := by simpa using (oi.trans oj.symm)
  -- Pull back all signals along the same row map, not just the two selected operands.
  obtain ⟨d,hd,p,hpair,hlabel,hcols⟩ := orbit i j ij same
  change d ∈ D at hd
  have small : ∀ c ∈ D, c % 64 < 59 ∧ c / 64 < 59 := by decide +kernel
  obtain ⟨su,sv⟩ := small d hd
  obtain ⟨s,hs,es⟩ := List.mem_iff_getElem.mp hd
  let idx : Fin 16 := ⟨s,hs⟩
  have ds : D.getD idx.val 0 = d := (List.getD_eq_getElem D 0 hs).trans es
  let F : ℕ → BitVec 59 := fun x => (BitVec.ofBoolListLE (List.ofFn (fun r : Fin 59 => x.testBit (p r.val)))).cast (by simp)
  have fb (x r : ℕ) (h : r < 59) : (F x : BitVec 59).getLsbD r = x.testBit (p r) := by
    simp only [F,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem _ false (by simpa only [List.length_ofFn] using h : r < (List.ofFn (fun t : Fin 59 => x.testBit (p t.val))).length),List.getElem_ofFn]
  have fs (x : ℕ) (hx : x ∈ S) : F x ∈ B := by
    obtain ⟨y,hy,hbits⟩ := hcols x hx
    refine List.mem_map.mpr ⟨y,hy,?_⟩
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [fb _ _ hr, hbits ⟨r,hr⟩]
    exact (BitVec.getLsbD_ofNat 59 y r).trans (by simp only [hr,decide_true,Bool.true_and])
  have fand (x y : ℕ) : F (x &&& y) = F x &&& F y := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr
    simp only [BitVec.getLsbD_and,fb _ _ hr,Nat.testBit_and]
  have forr (x y : ℕ) : F (x ||| y) = F x ||| F y := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr
    simp only [BitVec.getLsbD_or,fb _ _ hr,Nat.testBit_or]
  have ft : F T = 2097151 := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr
    rw [fb _ _ hr,tb]
    change decide (p r < 21) = T.testBit r
    rw [tb]; exact decide_eq_decide.mpr (hlabel ⟨r,hr⟩)
  have dk : decide (d%64 < 21) = o := by
    have h := hlabel ⟨d%64,su⟩
    change p (d%64) < 21 ↔ d%64 < 21 at h
    apply Eq.trans (decide_eq_decide.mpr h.symm); rcases hpair with h | h
    · exact (congrArg (fun z : ℕ => decide (z < 21)) h.1).trans oi
    · exact (congrArg (fun z : ℕ => decide (z < 21)) h.1).trans oj
  have goaleq : (if d%64 < 21 then F a ||| F b else F a &&& F b) = 2097151 := by
    rw [← ft,ho]
    cases o
    · simp only [of_decide_eq_false dk, ↓reduceIte, Bool.false_eq_true, fand]
    · simp only [of_decide_eq_true dk, ↓reduceIte, forr]
  have crosses : (F a).getLsbD (d%64) ≠ (F b).getLsbD (d%64) ∧ (F a).getLsbD (d%64) = (F b).getLsbD (d/64) ∧ (F b).getLsbD (d%64) = (F a).getLsbD (d/64) := by
    simp only [fb _ _ su,fb _ _ sv]; rcases hpair with ⟨u,v⟩ | ⟨u,v⟩ <;> rw [u,v] <;> simp only [ai,bi,aj,bj] <;> cases o <;> decide
  -- After n gates the wire list is exactly the new seeds followed by n transported values.
  have build (n : ℕ) (hn : n ≤ k) : ∃ gs : List (Bool × Fin 40 × Fin 40), gs.length = n ∧ gs.foldl gate B = B ++ (ws.take n).map F := by
    induction n with
    | zero => exact ⟨[],rfl,by simp⟩
    | succ n ih =>
      obtain ⟨gs,gl,gw⟩ := ih (by omega)
      obtain ⟨x,hx,y,hy,hop⟩ := rule n (by omega)
      let w := B ++ (ws.take n).map F
      have wire (v : ℕ) (hv : v ∈ S ++ ws.take n) : ∃ t : Fin 40, w.getD t.val 0 = F v := by
        have hmem : F v ∈ w := by
          rcases List.mem_append.mp hv with h | h
          · exact List.mem_append_left _ (fs v h)
          · exact List.mem_append_right _ (List.mem_map_of_mem h)
        obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp hmem
        have sz : w.length = 14+n := by simp [w,blen,List.length_take,Nat.min_eq_left (by omega : n ≤ ws.length)]
        exact ⟨⟨j,by omega⟩,(List.getD_eq_getElem w 0 hj).trans ej⟩
      obtain ⟨u,hu⟩ := wire x hx
      obtain ⟨v,hv⟩ := wire y hy
      obtain ⟨op,hv'⟩ : ∃ op : Bool, F ws[n] = (if op then F x ||| F y else F x &&& F y) := by
        rcases hop with h | h
        · exact ⟨false,by rw [h]; exact fand x y⟩
        · exact ⟨true,by rw [h]; exact forr x y⟩
      refine ⟨gs ++ [(op,u,v)],by simp [gl],?_⟩
      rw [List.foldl_append,gw,List.take_succ_eq_append_getElem (by omega : n < ws.length)]
      change w ++ [if op = true then w.getD u.val 0 ||| w.getD v.val 0 else w.getD u.val 0 &&& w.getD v.val 0] = _
      rw [hu,hv,←hv']; simp only [w,List.map_append,List.map_cons,List.map_nil,List.append_assoc]
  obtain ⟨gs,gl,gw⟩ := build k (by omega)
  let extras := List.replicate (25-k) ((false,0,0) : Bool × Fin 40 × Fin 40)
  have keep (w : List (BitVec 59)) (ls : List (Bool × Fin 40 × Fin 40)) : ∃ tail, ls.foldl gate w = w ++ tail := by
    induction ls generalizing w with
    | nil => exact ⟨[],by simp⟩
    | cons h t ih =>
      obtain ⟨tail,ht⟩ := ih (gate w h)
      refine ⟨(if h.1 = true then w.getD h.2.1.val 0 ||| w.getD h.2.2.val 0 else w.getD h.2.1.val 0 &&& w.getD h.2.2.val 0) :: tail,ht.trans ?_⟩
      exact List.append_assoc .. 
  obtain ⟨tail,ht⟩ := keep (B ++ (ws.take k).map F) extras
  let prog := gs ++ extras
  have plen : prog.length = 25 := by simp [prog,extras,gl]; omega
  have out (v : ℕ) (hv : v < k) : (prog.foldl gate B).getD (14+v) 0 = F ws[v] := by
    have lt : v < (ws.take k).length := by simp [List.length_take]; omega
    rw [show prog.foldl gate B = (B ++ (ws.take k).map F) ++ tail by dsimp only [prog]; rw [List.foldl_append,gw,ht]]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append,List.length_map,blen]; omega)]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [blen,Nat.add_sub_cancel_left,List.getD_eq_getElem _ 0 (by simpa using lt : v < ((ws.take k).map F).length),List.getElem_map,List.getElem_take]
  have la : ia < k := by omega
  have lb : ib < k := by omega
  let l : Fin 39 := ⟨14+ia,by omega⟩
  let r : Fin 39 := ⟨14+ib,by omega⟩
  have wa : (prog.foldl gate B).getD l.val 0 = F a := (out ia la).trans (congrArg F ea)
  have wb : (prog.foldl gate B).getD r.val 0 = F b := (out ib lb).trans (congrArg F eb)
  have lr : l ≠ r := by
    intro h; have hh := congrArg Fin.val h; change 14+ia=14+ib at hh
    have heq : ia = ib := by omega
    have hab : a = b := ea.symm.trans (heq ▸ eb)
    rw [hab,bi] at ai; cases o <;> contradiction
  let check := fun (code : ℕ) (x y : BitVec 59) =>
    (if code%64 < 21 then x ||| y else x &&& y) = 2097151 ∧
      x.getLsbD (code%64) ≠ y.getLsbD (code%64) ∧ x.getLsbD (code%64) = y.getLsbD (code/64) ∧ y.getLsbD (code%64) = x.getLsbD (code/64)
  rcases lt_or_gt_of_ne lr with h | h
  · refine ⟨prog,l,r,idx,plen,by dsimp [l]; omega,h,?_⟩
    change check (D.getD idx.val 0) ((prog.foldl gate B).getD l.val 0) ((prog.foldl gate B).getD r.val 0)
    rw [ds,wa,wb]; exact ⟨goaleq,crosses⟩
  · refine ⟨prog,r,l,idx,plen,by dsimp [r]; omega,h,?_⟩
    change check (D.getD idx.val 0) ((prog.foldl gate B).getD r.val 0) ((prog.foldl gate B).getD l.val 0)
    rw [ds,wa,wb]; dsimp only [check]
    rw [BitVec.or_comm (F b) (F a),BitVec.and_comm (F b) (F a)]
    exact ⟨goaleq,crosses.1.symm,crosses.2.2,crosses.2.1⟩
