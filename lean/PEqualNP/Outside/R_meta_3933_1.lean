import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_3933_1
    (binary : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ C.gates.countP (fun g => !(g.op.eval [false,false])))
    (fixed : ∀ (plain : Bool) (D : Circuit), FanInTwo D → D.size ≤ (if plain then 14 else 13) →
      ∃ r : ℕ, r < 512 ∧ D.eval (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++
        (if plain then [] else [r.testBit 0 || r.testBit 1, (r &&& 17) != 0])) ≠
        (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit r)
    (suffix : ∀ (m : ℕ) (D : Circuit),
      (31727032451024637546058449892380486774192680624387842336257748157603220582570656 : ℕ).testBit m = true →
      FanInTwo D → D.size = 13 → D.gates.countP (fun g => g.op.eval [false,false]) ≤ 2 →
      D.output = 23 → (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      let bank (r : ℕ) := List.ofFn (fun i : Fin 9 => r.testBit i.val) ++
        [r.testBit 0 || r.testBit 1, (r &&& m) != 0]
      let wire (r p : ℕ) := (D.wires (bank r)).getD p false
      (∀ (i : Fin 9) (E : Finset ℕ), (∀ j ∈ E, j < D.size+2 ∧
        ((∃ b : Bool, ∀ r : ℕ, r < 512 → r.testBit i.val = false → wire r (9+j) = b) ∨
         ∃ p < 9+j, ∀ r : ℕ, r < 512 → r.testBit i.val = false → wire r (9+j) = wire r p)) →
        E.card ≤ if i ∈ ([4,6,7] : List (Fin 9)) then 2 else 3) →
      ∃ r : ℕ, r < 512 ∧ D.eval (bank r) ≠
        (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit r) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin (9 : ℕ)) (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x1.size ∧ ((∃ (x9 : Bool), ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = x9) ∨ ∃ x9 < (9 : ℕ) + x7, ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = (x1.wires (List.ofFn x10)).getD x9 Bool.false)) → (x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] → x6.card ≤ (3 : ℕ)) ∧ (x5 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6.card ≤ (2 : ℕ))) → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (16 : ℕ) ≤ x1.size := by
  intro C fan first computes rigid second
  by_contra short
  have small : C.gates.length ≤ 15 := Nat.le_of_lt_succ (Nat.lt_of_not_ge short)
  let nt (g : Gate) := g.op.eval [false,false]
  have bin := binary C fan (fun x => congrFun computes x)
  have countSplit (l : List Gate) : l.countP nt + l.countP (fun g => !(nt g)) = l.length := by
    induction l with
    | nil => rfl
    | cons g l ih => cases h : nt g <;> simp [h] <;> clear * - ih <;> lia -abstractProof
  have allNot : C.gates.countP nt ≤ 2 := by
    change 13 ≤ C.gates.countP (fun g => !(nt g)) at bin
    have := countSplit C.gates
    clear * - this bin small
    lia -abstractProof
  obtain ⟨g,hg,hor⟩ := second
  obtain ⟨f,tail,split⟩ : ∃ f tail, C.gates = f :: g :: tail := by
    cases e : C.gates with
    | nil => simp [e] at hg
    | cons f l => cases l with
      | nil => simp [e] at hg
      | cons b bs => have eq : b = g := by simpa [e] using hg
                     exact ⟨f,bs,by rw [eq]⟩
  have ht : tail.length ≤ 13 := by rw [split] at small; simp at small; clear * - small; lia -abstractProof
  have hnot : tail.countP nt ≤ 2 := by
    rw [split] at allNot
    simp only [List.countP_cons] at allNot
    split at allNot <;> split at allNot <;> clear * - allNot <;> lia -abstractProof
  have arity := (fan g (by simp [split])).2
  let step (w : List Bool) (q : Gate) := w ++ [q.op.eval (q.inputs.map fun i => w.getD i false)]
  have stable (ls : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (ls.foldl step w).getD i false = w.getD i false := by
    induction ls generalizing w with
    | nil => rfl
    | cons q ls ih =>
      rw [List.foldl_cons,ih (step w q) (by simp [step]; exact h.le)]
      exact List.getD_append _ _ _ _ h
  let bank (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 1]
  have firstStep (x : Fin 9 → Bool) : step (List.ofFn x) f = bank x := by
    have e := first x
    change (C.gates.foldl step (List.ofFn x)).getD 9 false = _ at e
    rw [split,List.foldl_cons,stable _ _ _ (by simp [step])] at e
    simpa [step,bank] using congrArg (fun b => List.ofFn x ++ [b]) e
  let cap (n : ℕ) : Fin 11 := ⟨min n 10, Nat.lt_succ_of_le (Nat.min_le_right ..)⟩
  let a := cap (g.inputs.getD 0 10)
  let b := cap (g.inputs.getD 1 10)
  have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have padded (xs : List ℕ) (h : xs.length ≤ 2) (v : ℕ → Bool) (zero : v 10 = false) :
      (xs.map v).any id = (v (xs.getD 0 10) || v (xs.getD 1 10)) := by
    cases xs with
    | nil => simp [zero]
    | cons u us => cases us with
      | nil => simp [zero]
      | cons z zs => cases zs with
        | nil => simp
        | cons y ys => simp at h
  let pm (s : Bool) (i : ℕ) := if s then ([1,0,5,8,6,2,4,7,3,9,10] : List ℕ).getD i i else i
  let pin (i : ℕ) := ([1,2,4,8,16,32,64,128,256,3,0] : List ℕ).getD i 0
  let reps := ([5,9,17,33,65,129,257,12,20,36,68,132,260,7,24,72,136,264,11,80,144,19,131] : List ℕ)
  let ms (k : Fin 23) := reps.getD k.val 0
  have cover : ∀ u v : Fin 11, ∃ s : Bool, ∃ k : Fin 23, ∃ t : Fin 12,
      (pin (pm s u.val) ||| pin (pm s v.val)) = (if t.val = 10 then ms k else pin t.val) ∧ (t.val = 10 ∨ ms k = 17) := by decide
  obtain ⟨s,k,t,hmask,kind⟩ := cover a b
  have certified : ∀ k : Fin 23, ms k ≠ 17 →
      (31727032451024637546058449892380486774192680624387842336257748157603220582570656 : ℕ).testBit (ms k) = true := by decide
  let tr (i : ℕ) := if i < 9 then pm s i else if i = 10 then (if t.val = 11 then 24 else t.val) else min i 24
  let trans (q : Gate) : Gate := ⟨q.op,q.inputs.map tr⟩
  let D : Circuit := ⟨tail.map trans,tr C.output⟩
  have pmBound : ∀ s : Bool, ∀ i : Fin 9, pm s i.val < 9 := by decide
  have trBound (i : ℕ) : tr i ≤ 24 := by
    dsimp only [tr]; split_ifs with h h' h''
    · exact (pmBound s ⟨i,h⟩).le.trans (by decide)
    · decide
    · exact t.isLt.le.trans (by decide)
    · exact Nat.min_le_right .. 
  have fanD : FanInTwo D := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    have hz' := fan z (by simp [split,hz])
    exact ⟨hz'.1,by simpa [trans] using hz'.2⟩
  have sizeD : D.size ≤ 13 := by change (tail.map trans).length ≤ 13; simpa using ht
  have notD : D.gates.countP nt ≤ 2 := by
    change (tail.map trans).countP nt ≤ 2
    rw [List.countP_map]; exact hnot
  have pinsD : ∀ q ∈ D.gates, ∀ i ∈ q.inputs, i ≤ 24 := by
    intro q hq
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hq
    intro i hi
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    exact trBound j
  let hit (r m : ℕ) := (r &&& m) != 0
  let row (s : Bool) (r : Fin 512) (i : Fin 9) := r.val.testBit (pm s i.val)
  let base (r : Fin 512) := List.ofFn (fun i : Fin 9 => r.val.testBit i.val) ++
    [r.val.testBit 0 || r.val.testBit 1,hit r.val (ms k)]
  have hbank : ∀ s : Bool, ∀ r : Fin 512, ∀ i : Fin 11,
      (bank (row s r)).getD i.val false = hit r.val (pin (pm s i.val)) := by decide
  have hnew : ∀ r : Fin 512, ∀ i : Fin 10,
      (bank (row false r)).getD i.val false = hit r.val (pin i.val) := fun r i => hbank false r ⟨i.val,i.isLt.trans (by decide)⟩
  have edges : ∀ s : Bool, ∀ r : Fin 512,
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => row s r e.1 && row s r e.2) =
      (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit r.val := by decide
  have hraw (r : Fin 512) (i : Fin 10) : (base r).getD i.val false = hit r.val (pin i.val) := by
    change ((bank (row false r)) ++ [hit r.val (ms k)]).getD i.val false = _
    rw [List.getD_append _ _ _ _ (by simpa [bank] using i.isLt),hnew]
  have hinit (r : Fin 512) : ∀ i, (step (bank (row s r)) g).getD i false = (base r).getD (tr i) false := by
    let w := bank (row s r)
    have wl : w.length = 10 := by simp [w,bank]
    have bl : (base r).length = 11 := by simp [base]
    have rd (j : ℕ) : w.getD j false = hit r.val (pin (pm s (cap j).val)) := by
      by_cases h : j < 10
      · simpa only [cap,Nat.min_eq_left h.le] using hbank s r (cap j)
      · have cj : (cap j).val = 10 := Nat.min_eq_right (Nat.le_of_not_gt h)
        rw [List.getD_eq_default _ _ (wl ▸ Nat.le_of_not_gt h),cj]
        cases s <;> change false = ((r.val &&& 0) != 0) <;> simp
    have gval : g.op.eval (g.inputs.map fun j => w.getD j false) =
        hit r.val (if t.val = 10 then ms k else pin t.val) := by
      rw [hor,orEval,padded _ arity _ (List.getD_eq_default _ _ wl.le),rd,rd,← hmask]
      change (hit _ _ || hit _ _) = hit _ _
      rw [Bool.eq_iff_iff]
      simp only [hit,Nat.and_or_distrib_left,Bool.or_eq_true]
      exact (or_congr bne_iff_ne bne_iff_ne).trans ((not_and_or).symm.trans ((not_congr Nat.or_eq_zero_iff).symm.trans bne_iff_ne.symm))
    intro i
    change (w ++ [_]).getD i false = _
    by_cases h : i < 10
    · rw [List.getD_append _ _ _ _ (wl ▸ h),rd]
      have ci : (cap i).val = i := Nat.min_eq_left h.le
      rw [ci]
      have p9 : pm s 9 = 9 := by cases s <;> rfl
      have pb : pm s i < 10 := by
        by_cases u : i < 9
        · exact Nat.lt_trans (pmBound s ⟨i,u⟩) (by decide)
        · have : i = 9 := Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.le_of_not_gt u)
          rw [this,p9]; decide
      have rr : tr i = pm s i := by
        by_cases u : i < 9
        · simp [tr,u]
        · have : i = 9 := Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.le_of_not_gt u)
          rw [this,p9]; rfl
      rw [rr]; exact (hraw r ⟨_,pb⟩).symm
    · by_cases e : i = 10
      · subst i
        rw [List.getD_append_right _ _ _ _ wl.le,wl]; change _ = (base r).getD _ false
        rw [show (10:ℕ)-10=0 by decide,List.getD_cons_zero,gval]
        by_cases z : t.val = 11
        · simp only [tr,show ¬(10:ℕ)<9 by decide,ite_false,ite_true,z]
          rw [List.getD_eq_default _ _ (bl ▸ (by decide : 11 ≤ 24))]
          change ((r.val &&& 0) != 0) = false
          simp
        · by_cases y : t.val = 10
          · simp only [tr,show ¬(10:ℕ)<9 by decide,ite_false,ite_true,y]
            simp [base]
          · have tt : t.val < 10 := by have bound := t.isLt; clear * - bound z y; lia -abstractProof
            simp only [tr,show ¬(10:ℕ)<9 by decide,ite_false,ite_true,z,y]
            exact (hraw r ⟨_,tt⟩).symm
      · have lower := Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) (Ne.symm e)
        have ri : tr i = min i 24 := by simp [tr,show ¬ i < 9 from Nat.not_lt_of_ge ((by decide : 9 ≤ 10).trans lower.le),e]
        rw [ri,List.getD_eq_default _ _ (by simp [wl]; exact Nat.succ_le_of_lt lower),List.getD_eq_default _ _ (bl ▸ le_min (Nat.succ_le_of_lt lower) (by decide))]
  have unchanged (w : List Bool) (v : Bool) (i : ℕ) (hi : i ≠ w.length) :
      (w ++ [v]).getD i false = w.getD i false := by
    by_cases h : i < w.length
    · exact List.getD_append _ _ _ _ h
    · have above := Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) (Ne.symm hi)
      rw [List.getD_eq_default _ _ (by simpa using above),List.getD_eq_default _ _ above.le]
  have simulation (ls : List Gate) (u v : List Bool) (lens : u.length = v.length)
      (ok : ∀ i, u.getD i false = v.getD (tr i) false)
      (fresh : ∀ j < ls.length, ∀ i, i = u.length+j ↔ tr i = u.length+j) :
      ∀ i, (ls.foldl step u).getD i false = ((ls.map trans).foldl step v).getD (tr i) false := by
    induction ls generalizing u v with
    | nil => exact ok
    | cons q ls ih =>
      apply ih (step u q) (step v (trans q)) (by simp [step,lens])
      · intro i
        have eq : i = u.length ↔ tr i = v.length := by simpa [← lens] using fresh 0 (by simp) i
        have val : q.op.eval (q.inputs.map fun j => u.getD j false) =
            (trans q).op.eval ((trans q).inputs.map fun j => v.getD j false) := by
          simp only [trans,List.map_map,ok]; rfl
        by_cases e : i = u.length
        · have last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by simp
          change (u ++ [_]).getD i false = (v ++ [_]).getD (tr i) false
          rw [eq.mp e,e,last,last,val]
        · exact (unchanged _ _ _ e).trans ((ok i).trans (unchanged _ _ _ (mt eq.mpr e)).symm)
      · intro j hj i
        simpa [step,Nat.add_assoc,Nat.add_comm 1 j] using fresh (j+1) (by simpa using hj) i
  have wiresAgree (r : Fin 512) (p : ℕ) : (C.wires (List.ofFn (row s r))).getD p false =
      (D.wires (base r)).getD (tr p) false := by
    let u := step (bank (row s r)) g
    have ul : u.length = 11 := by simp [u,bank,step]
    have run := simulation tail u (base r) (by simp [ul,base]) (hinit r) (by
      intro j hj i; rw [ul]; dsimp only [tr]; split_ifs with h h' h''
      · have p : pm s i < 9 := pmBound s ⟨i,h⟩
        clear * - p h; lia -abstractProof
      · clear * - h' ht hj; lia -abstractProof
      · have lt : t.val < 11 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ t.isLt) h''
        clear * - lt h'; lia -abstractProof
      · by_cases bound : i ≤ 24
        · rw [Nat.min_eq_left bound]
        · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge bound))]
          clear * - hj ht bound; lia -abstractProof) p
    change (C.gates.foldl step (List.ofFn _)).getD p false = _
    rw [split,List.foldl_cons,List.foldl_cons,firstStep]
    exact run
  have agrees (r : Fin 512) : D.eval (base r) =
      (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit r.val :=
    (wiresAgree r C.output).symm.trans ((congrFun computes (row s r)).trans (edges s r))
  have rawMiss (Q : Circuit) (fq : FanInTwo Q) (sz : Q.size ≤ 14)
      (same : ∀ x : Fin 9 → Bool, Q.eval (List.ofFn x) = C.eval (List.ofFn x)) : False := by
    obtain ⟨r,hr,ne⟩ := fixed true Q fq sz
    apply ne
    simp only [if_true,List.append_nil]
    exact (same (row false ⟨r,hr⟩)).trans ((congrFun computes _).trans (edges false ⟨r,hr⟩))
  have full : C.gates.length = 15 := by
    by_contra e
    exact rawMiss C fan (by change C.gates.length ≤ 14; clear * - e small; lia -abstractProof) (fun _ => rfl)
  have exactSize : D.size = 13 := by
    rw [split] at full
    change (tail.map trans).length = 13
    rw [List.length_map]; change tail.length+1+1 = 15 at full
    clear * - full; lia -abstractProof
  have lengths (ls : List Gate) (v : List Bool) : (ls.foldl step v).length = v.length + ls.length := by
    induction ls generalizing v with
    | nil => simp
    | cons q ls ih => rw [List.foldl_cons,ih]; simp [step,Nat.add_assoc,Nat.add_comm 1]
  have late : 23 ≤ C.output := by
    by_contra! early
    let Q : Circuit := ⟨C.gates.take 14,C.output⟩
    apply rawMiss Q (fun g h => fan g (List.mem_of_mem_take h)) (by change (C.gates.take 14).length ≤ 14; simp) 
    intro x
    let v := (C.gates.take 14).foldl step (List.ofFn x)
    have vl : v.length = 23 := by simp [v,lengths,full]
    change v.getD C.output false = (C.gates.foldl step _).getD C.output false
    exact (stable (C.gates.drop 14) v _ (vl ▸ early)).symm.trans (by
      dsimp only [v]; rw [← List.foldl_append,List.take_append_drop])
  have out : D.output < 24 := by
    by_contra! large
    have len : (D.wires (base 3)).length ≤ 24 := by
      change (D.gates.foldl step _).length ≤ 24
      rw [lengths]; change (base 3).length + D.size ≤ 24; simpa [base] using Nat.add_le_add_left sizeD 11
    have h := agrees 3
    change (D.wires _).getD _ false = true at h
    rw [List.getD_eq_default _ _ (len.trans large)] at h; contradiction
  by_cases special : ms k = 17
  · obtain ⟨r,hr,ne⟩ := fixed false D fanD sizeD
    apply ne
    rw [if_neg Bool.false_ne_true]
    simpa only [base,hit,special] using agrees ⟨r,hr⟩
  have hten := kind.resolve_right special
  have lastPin : D.output = 23 := by
    have n : ¬ C.output < 9 := by clear * - late; lia -abstractProof
    have e : C.output ≠ 10 := by clear * - late; lia -abstractProof
    have eq : D.output = min C.output 24 := by change tr C.output = _; simp [tr,n,e]
    rw [eq] at out ⊢
    exact Nat.le_antisymm (Nat.le_of_lt_succ out) (le_min late (by decide))
  let perm (i : Fin 9) : Fin 9 := ⟨pm s i.val,pmBound s i⟩
  have invol : ∀ s : Bool, ∀ i : Fin 9, pm s (pm s i.val) = i.val := by decide
  have packing (n : ℕ) (x : Fin n → Bool) : ∃ r < 2^n, ∀ i : Fin n, r.testBit i.val = x i := by
    induction n with
    | zero => exact ⟨0,by decide,fun i => i.elim0⟩
    | succ n ih =>
      obtain ⟨a,ha,e⟩ := ih (fun i => x i.succ)
      exact ⟨Nat.bit (x 0) a,Nat.bit_lt_two_pow_succ_iff.mpr ha,
        Fin.cases (Nat.testBit_bit_zero ..) (fun i => (Nat.testBit_bit_succ ..).trans (e i))⟩
  have rows (x : Fin 9 → Bool) : ∃ r : Fin 512, row s r = x := by
    obtain ⟨n,hn,e⟩ := packing 9 (fun i => x (perm i))
    refine ⟨⟨n,hn⟩,funext fun i => (e (perm i)).trans (congrArg x (Fin.ext (invol s i)))⟩
  have stablePin (p : ℕ) (lo : 9 ≤ p) (hi : p ≤ 24) : tr p = p := by
    by_cases e : p = 10
    · subst p; simp [tr,hten]
    · simp [tr,Nat.not_lt_of_ge lo,e,Nat.min_eq_left hi]
  have groups : ∀ (s : Bool) (i : Fin 9),
      (i ∈ ([4,6,7] : List (Fin 9)) → pm s i.val ∈ ([4,6,7] : List ℕ)) ∧
      (i ∉ ([4,6,7] : List (Fin 9)) → pm s i.val ∈ ([0,1,2,3,5,8] : List ℕ)) := by
    intro s i; cases s <;> fin_cases i <;> decide
  have liftMem {i : Fin 9} {l : List (Fin 9)} (h : i.val ∈ l.map Fin.val) : i ∈ l := by
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    exact (Fin.ext e : j = i) ▸ hj
  obtain ⟨r,hr,ne⟩ := suffix (ms k) D (certified k special) fanD exactSize notD lastPin pinsD (by
    intro i E hyp
    have rr := rigid (perm i) E (by
      intro j hj
      obtain ⟨bound,loss⟩ := hyp j hj
      have lenC : C.size = D.size + 2 := by change C.gates.length = (tail.map trans).length + 2; rw [split]; simp
      refine ⟨lenC ▸ bound,?_⟩
      have jhi : 9+j ≤ 24 := by clear * - bound sizeD; lia -abstractProof
      have cur := stablePin (9+j) (Nat.le_add_right ..) jhi
      have off (r : Fin 512) (h : row s r (perm i) = false) : r.val.testBit i.val = false := by
        change r.val.testBit (pm s (pm s i.val)) = false at h
        rwa [invol] at h
      rcases loss with ⟨b,hb⟩ | ⟨p,hp,eq⟩
      · refine Or.inl ⟨b,?_⟩; intro x hx; obtain ⟨r,rfl⟩ := rows x
        rw [wiresAgree,cur]; exact hb r.val r.isLt (off r hx)
      · by_cases lt : p < 9
        · let p' := perm ⟨p,lt⟩
          have prior : tr p'.val = p := by change (if p'.val < 9 then _ else _) = _; rw [if_pos p'.isLt]; exact invol s ⟨p,lt⟩
          refine Or.inr ⟨p'.val,p'.isLt.trans_le (Nat.le_add_right ..),?_⟩
          intro x hx; obtain ⟨r,rfl⟩ := rows x
          rw [wiresAgree,wiresAgree,cur,prior]; exact eq r.val r.isLt (off r hx)
        · refine Or.inr ⟨p,hp,?_⟩; intro x hx; obtain ⟨r,rfl⟩ := rows x
          rw [wiresAgree,wiresAgree,cur,stablePin p (Nat.le_of_not_gt lt) (hp.le.trans jhi)]
          exact eq r.val r.isLt (off r hx))
    by_cases grp : i ∈ ([4,6,7] : List (Fin 9))
    · rw [if_pos grp]; apply rr.2; exact liftMem ((groups s i).1 grp)
    · rw [if_neg grp]; apply rr.1; exact liftMem ((groups s i).2 grp))
  exact ne (agrees ⟨r,hr⟩)
