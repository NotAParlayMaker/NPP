import PEqualNP.Defs

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_4415_641
    (global : ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → ↑x1 * (10 : ℕ) + ↑x2 ∉ [(12 : ℕ), (21 : ℕ), (23 : ℕ), (32 : ℕ), (16 : ℕ), (61 : ℕ), (27 : ℕ), (72 : ℕ), (38 : ℕ), (83 : ℕ), (57 : ℕ), (75 : ℕ), (68 : ℕ), (86 : ℕ), (58 : ℕ), (85 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x12 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)), x12 x1 || x12 x2]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) → False)
    (falsePositive : 
    ∀ (a b : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit),
    10 * min a.val b.val + max a.val b.val ∈ ([13,15,17,18,25,26,28,35,36,37,56,67,78] : List ℕ) →
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    (∀ i : Fin 9, ∃ g ∈ C.gates,
      i.val ∈ (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs)) →
    let bank := fun n : ℕ =>
      let x := fun i : Fin 9 => n.testBit i.val
      List.ofFn x ++ [x 0 || x 4, x a || x b]
    ∀ p q : ℕ, p ∈ ([52, 73, 84, 100, 112, 137, 146, 193, 200, 274, 386, 400] : List ℕ) → q ∈ ([116,201,402] : List ℕ) →
      p &&& q = p → C.eval (bank p) = true → C.eval (bank q) = false →
      (∃ k : Fin C.gates.length, (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.wires (bank p)).getD (11 + k.val) false = true ∧
        (C.wires (bank q)).getD (11 + k.val) false = false) →
      ∃ r : Fin 59, C.eval (bank ((7026623289660034915783320887927727366070090033330209655928152697067302462959165914419963795633307909346340554003670022409201926419659948381924108492039627735552 >>> (9 * r.val)) % 512)) ≠
        (316380210352264264 : ℕ).testBit r.val)
    (falseNegative : 
    ∀ (a b : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit),
    10 * min a.val b.val + max a.val b.val ∈ ([13,15,17,18,25,26,28,35,36,37,56,67,78] : List ℕ) →
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    (∀ i : Fin 9, ∃ g ∈ C.gates,
      i.val ∈ (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs)) →
    let bank := fun n : ℕ =>
      let x := fun i : Fin 9 => n.testBit i.val
      List.ofFn x ++ [x 0 || x 4, x a || x b]
    ∀ p q : ℕ, p ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ) → q < 511 →
      p &&& q = p → C.eval (bank p) = true → C.eval (bank q) = false →
      (∃ k : Fin C.gates.length, (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.wires (bank p)).getD (11 + k.val) false = true ∧
        (C.wires (bank q)).getD (11 + k.val) false = false) →
      ∃ r : Fin 59, C.eval (bank ((7026623289660034915783320887927727366070090033330209655928152697067302462959165914419963795633307909346340554003670022409201926419659948381924108492039627735552 >>> (9 * r.val)) % 512)) ≠
        (316380210352264264 : ℕ).testBit r.val) :
    have x1 : List (BitVec (59 : ℕ)) := [(360930119642124586 : BitVec (59 : ℕ)), (432486920269079116 : BitVec (59 : ℕ)), (293578547141297264 : BitVec (59 : ℕ)), (289365901620316032 : BitVec (59 : ℕ)), (439119665042618368 : BitVec (59 : ℕ)), (297239789478805504 : BitVec (59 : ℕ)), (306275578149863424 : BitVec (59 : ℕ)), (540467122476679168 : BitVec (59 : ℕ)), (576425567931334656 : BitVec (59 : ℕ))]; have x2 : List (BitVec (59 : ℕ)) → Fin (3 : ℕ) × List (Fin (25 : ℕ)) → List (BitVec (59 : ℕ)) := fun (x2 : List (BitVec (59 : ℕ))) (x3 : Fin (3 : ℕ) × List (Fin (25 : ℕ))) =>   have x4 : List (BitVec (59 : ℕ)) := List.map (fun (x4 : Fin (25 : ℕ)) => x2.getD ↑x4 (0 : BitVec (59 : ℕ))) x3.2;   x2 ++ [if x3.1 = (0 : Fin (3 : ℕ)) then List.foldr (fun (x5 x6 : BitVec (59 : ℕ)) => x5 &&& x6) (~~~(0 : BitVec (59 : ℕ))) x4 else if x3.1 = (1 : Fin (3 : ℕ)) then List.foldr (fun (x5 x6 : BitVec (59 : ℕ)) => x5 ||| x6) (0 : BitVec (59 : ℕ)) x4 else ~~~x4.headD (0 : BitVec (59 : ℕ))]; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : List (Fin (3 : ℕ) × List (Fin (25 : ℕ)))) (x6 : Fin (25 : ℕ)),   (10 : ℕ) * Min.min ↑x3 ↑x4 + Max.max ↑x3 ↑x4 ∈ [(13 : ℕ), (15 : ℕ), (17 : ℕ), (18 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (35 : ℕ), (36 : ℕ), (37 : ℕ), (56 : ℕ), (67 : ℕ), (78 : ℕ)] →     x5.length ≤ (13 : ℕ) →       (∀ x9 ∈ x5, x9.2.length ≤ (2 : ℕ)) →         (∀ (x10 : Fin (25 : ℕ)), ↑x10 < (9 : ℕ) → ∃ x12 ∈ x5, x10 ∈ if x12.1 = (2 : Fin (3 : ℕ)) then List.take (1 : ℕ) x12.2 else x12.2) →           have x11 : List (BitVec (59 : ℕ)) := x1 ++ [x1.getD (0 : ℕ) (0 : BitVec (59 : ℕ)) ||| x1.getD (4 : ℕ) (0 : BitVec (59 : ℕ)), x1.getD ↑x3 (0 : BitVec (59 : ℕ)) ||| x1.getD ↑x4 (0 : BitVec (59 : ℕ))];           have x12 : List (BitVec (59 : ℕ)) := List.foldl x2 x11 x5;           x12.getD ↑x6 (0 : BitVec (59 : ℕ)) ≠ (316380210352264264 : BitVec (59 : ℕ)) := by
  intro bank0 step0 a b gs out hp size arity used start0 final0 eqTarget
  let words : List (BitVec 59) := [360930119642124586, 432486920269079116, 293578547141297264, 289365901620316032, 439119665042618368, 297239789478805504, 306275578149863424, 540467122476679168, 576425567931334656]
  let initial := words ++ [words.getD 0 0 ||| words.getD 4 0, words.getD a.val 0 ||| words.getD b.val 0]
  let step := fun (w : List (BitVec 59)) (g : Fin 3 × List (Fin 25)) =>
    let args := g.2.map fun i => w.getD i.val 0
    w ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
      else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
  change (gs.foldl step initial).getD out.val 0 = 316380210352264264 at eqTarget
  let dec (g : Fin 3 × List (Fin 25)) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨if g.1 = 0 then .and else if g.1 = 1 then .or else .not, g.2.map Fin.val⟩
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs.map dec, out.val⟩
  have small : C.size ≤ 13 := by change (gs.map dec).length ≤ 13; simpa using size
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨g,hm,rfl⟩ := List.mem_map.mp hg
    obtain ⟨op,ins⟩ := g
    fin_cases op <;> simp [dec,arity _ hm]
  have readPins : ∀ i : Fin 9, ∃ g ∈ C.gates,
      i.val ∈ (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs) := by
    intro i
    let j : Fin 25 := ⟨i.val, by omega⟩
    obtain ⟨g,hg,hj⟩ := used j i.isLt
    refine ⟨dec g,List.mem_map.mpr ⟨g,hg,rfl⟩,?_⟩
    obtain ⟨op,ins⟩ := g
    have mapped := List.mem_map_of_mem (f := Fin.val) hj
    fin_cases op <;> first
      | change i.val ∈ ins.map Fin.val; exact mapped
      | change i.val ∈ (ins.map Fin.val).take 1; rw [← List.map_take]; exact mapped
  let row := fun (n : ℕ) (i : Fin 9) => n.testBit i.val
  let bank := fun n : ℕ => List.ofFn (row n) ++ [row n 0 || row n 4, row n a || row n b]
  let pt := fun r : Fin 59 => (7026623289660034915783320887927727366070090033330209655928152697067302462959165914419963795633307909346340554003670022409201926419659948381924108492039627735552 >>> (9*r.val)) % 512
  let scalar := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have indexed (w : List (BitVec 59)) (r : Fin 59) (i : ℕ) :
      (w.map fun v => v.getLsbD r.val).getD i false = (w.getD i 0).getLsbD r.val := by
    induction w generalizing i with
    | nil => exact BitVec.getLsbD_zero.symm
    | cons v vs ih => cases i with
      | zero => rfl
      | succ i => exact ih i
  have parts (r : Fin 59) (as : List (BitVec 59)) :
      let bs := as.map fun v => v.getLsbD r.val
      (as.foldr (· &&& ·) (~~~0)).getLsbD r.val = bs.all id ∧
      (as.foldr (· ||| ·) 0).getLsbD r.val = bs.any id ∧
      (~~~(as.headD 0)).getLsbD r.val = !(bs.headD false) := by
    have rb := r.isLt
    induction as with
    | nil =>
      have hz : (0 : BitVec 59).getLsbD r.val = false := BitVec.getLsbD_zero
      have ho : (~~~(0 : BitVec 59)).getLsbD r.val = true := by
        rw [BitVec.getLsbD_not, hz]; simp [rb]
      exact ⟨ho,hz,ho⟩
    | cons v rest ih =>
      obtain ⟨qa,qo,_⟩ := ih
      refine ⟨?_,?_,?_⟩
      · change (v &&& rest.foldr (· &&& ·) (~~~0)).getLsbD r.val = (_ && _)
        rw [BitVec.getLsbD_and,qa]; rfl
      · change (v ||| rest.foldr (· ||| ·) 0).getLsbD r.val = (_ || _)
        rw [BitVec.getLsbD_or,qo]; rfl
      · change (~~~v).getLsbD r.val = !(v.getLsbD r.val)
        rw [BitVec.getLsbD_not]; simp [rb]
  have run (ls : List (Fin 3 × List (Fin 25))) (w : List (BitVec 59)) (r : Fin 59) :
      (ls.foldl step w).map (fun v => v.getLsbD r.val) =
        (ls.map dec).foldl scalar (w.map fun v => v.getLsbD r.val) := by
    induction ls generalizing w with
    | nil => rfl
    | cons g ls ih =>
      rw [List.foldl_cons,ih]
      change _ = (ls.map dec).foldl scalar (scalar _ _)
      congr 1
      let as := g.2.map fun i => w.getD i.val 0
      have reads : (dec g).inputs.map (fun j => (w.map fun v => v.getLsbD r.val).getD j false) =
          as.map (fun v => v.getLsbD r.val) := by
        simp only [dec,as,List.map_map,Function.comp_def,indexed]
      simp only [step,scalar,List.map_append,List.map_cons,List.map_nil,reads]
      congr 2
      obtain ⟨op,ins⟩ := g
      fin_cases op
      · exact (parts r as).1
      · exact (parts r as).2.1
      · exact (parts r as).2.2
  have rawbits : ∀ r, words.map (fun v => v.getLsbD r.val) = List.ofFn (row (pt r)) := by
    decide +kernel
  have initialBits (r : Fin 59) : initial.map (fun v => v.getLsbD r.val) = bank (pt r) := by
    have atpin (i : Fin 9) : (words.getD i.val 0).getLsbD r.val = row (pt r) i := by
      rw [← indexed,rawbits,List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have at0 : (words.getD 0 0).getLsbD r.val = row (pt r) 0 := atpin 0
    have at4 : (words.getD 4 0).getLsbD r.val = row (pt r) 4 := atpin 4
    simp only [initial,bank,List.map_append,List.map_cons,List.map_nil,BitVec.getLsbD_or,
      rawbits,at0,at4,atpin]
  have sample (r : Fin 59) : C.eval (bank (pt r)) = (316380210352264264 : ℕ).testBit r.val := by
    change ((gs.map dec).foldl scalar (bank (pt r))).getD out.val false = _
    rw [← initialBits, ← run,indexed,eqTarget]
    rfl
  let target := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  have pairs : ∀ i j : Fin 9, 10 * min i.val j.val + max i.val j.val ∈ ([13,15,17,18,25,26,28,35,36,37,56,67,78] : List ℕ) →
      i ≠ 0 ∧ i ≠ 4 ∧ j ≠ 0 ∧ j ≠ 4 ∧ i ≠ j ∧
      i.val * 10 + j.val ∉ ([12,21,23,32,16,61,27,72,38,83,57,75,68,86,58,85] : List ℕ) := by
    decide +kernel
  obtain ⟨ha,ha',hb,hb',hab,hn⟩ := pairs a b hp
  apply global a b C ha ha' hb hb' hab hn fan small
  intro x
  let word := BitVec.ofBoolListLE (List.ofFn x)
  let n : Fin 512 := ⟨word.toNat, by have h := word.isLt; simpa [word] using h⟩
  have unpack : row n.val = x := by
    funext i
    change word.getLsbD i.val = x i
    rw [show word = BitVec.ofBoolListLE (List.ofFn x) from rfl,BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _
  change C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = target x
  rw [← unpack]
  change C.eval (bank n.val) = target (row n.val)
  let choose := fun z : Fin 512 => Fin.ofNat 59 ((5273690697528497123373243096163442877155431267574640661153405452483359018842879285903055174950520138857814131525052207019709674952391546999563549543533923144217511332424530667980278689458358746182134523268713677528032907163519276924033803577211313559344106194454571141936874536184082678191388481421152961939842823172370283037748999724479839553872972591662301286651169677151119196386120850944978330381764898025738252256320277749843069706869783872424355603328453224052932752054422347673654237618919728578312746176844593209197534666205189183914973897086634741388563011015129829892886400083555487434984079967135192461179028164952514209810550268494882446924932301392234509134445321333937180429795460775032654373122836025211208141448617995894714966616250174172848529271406254259650228748265984172394837706982880303121661799490594231392072584974065072518656318900800229121481120015592666576827264301719742361214491515304931557646400 >>> (6*z.val)) % 64)
  let tag := fun r : Fin 59 => (316380210352264264 : ℕ).testBit r.val
  have geometry : ∀ z : Fin 512,
      let r := choose z
      (z.val = pt r ∧ target (row z.val) = tag r) ∨
      (target (row z.val) = false ∧ z.val ∈ ([52, 73, 84, 100, 112, 137, 146, 193, 200, 274, 386, 400] : List ℕ) ∧
        pt r ∈ ([116,201,402] : List ℕ) ∧ z.val &&& pt r = z.val ∧ tag r = false) ∨
      (target (row z.val) = true ∧ pt r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ) ∧
        z.val < 511 ∧ pt r &&& z.val = pt r ∧ tag r = true) := by
    decide +kernel
  have early (ls : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length) : (ls.foldl scalar w).getD i false = w.getD i false := by
    induction ls generalizing w with
    | nil => rfl
    | cons g ls ih =>
      rw [List.foldl_cons,ih _ (by simp [scalar]; omega)]
      exact List.getD_append _ _ _ _ hi
  let ordered := fun (u v : List Bool) => ∀ i, u.getD i false = true → v.getD i false = true
  have joinOrder (u v : List Bool) (hu : u.length = v.length) (h : ordered u v)
      (s t : List Bool) (h' : ordered s t) : ordered (u ++ s) (v ++ t) := by
    intro i hi
    by_cases before : i < u.length
    · rw [List.getD_append _ _ _ _ before] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h i hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      rw [List.getD_append_right _ _ _ _ (by omega), ← hu]
      exact h' _ hi
  have descend (ls : List PEqualNP.CircuitLowerBounds.Gate)
      (legal : ∀ g ∈ ls, g.op = .and ∨ g.op = .or ∨ g.op = .not)
      (u v : List Bool) (len : u.length = v.length) (ord : ordered u v)
      (i : ℕ) (hi : (ls.foldl scalar u).getD i false = true)
      (hj : (ls.foldl scalar v).getD i false = false) :
      ∃ k : Fin ls.length, (ls.get k).op = .not ∧
        (ls.foldl scalar u).getD (u.length + k.val) false = true ∧
        (ls.foldl scalar v).getD (u.length + k.val) false = false := by
    induction ls generalizing u v with
    | nil =>
      have := ord i hi
      exact Bool.noConfusion (this.symm.trans hj)
    | cons g ls ih =>
      let eval := fun w : List Bool => g.op.eval (g.inputs.map fun j => w.getD j false)
      change (ls.foldl scalar (u ++ [eval u])).getD i false = true at hi
      change (ls.foldl scalar (v ++ [eval v])).getD i false = false at hj
      by_cases hit : eval u = true ∧ eval v = false
      · have hn : g.op = .not := by
          have andEval (xs : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := rfl
          have orEval (xs : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := rfl
          rcases legal g (by simp) with ha | ho | hn
          · have allu : (g.inputs.map fun j => u.getD j false).all id = true := by
              simpa only [eval,ha,andEval] using hit.1
            have allv : (g.inputs.map fun j => v.getD j false).all id = true := by
              simp only [List.all_eq_true,List.mem_map,forall_exists_index,and_imp,
                forall_apply_eq_imp_iff₂,id_eq] at allu ⊢
              exact fun j hj' => ord j (allu j hj')
            have eq : eval v = true := by simpa only [eval,ha,andEval] using allv
            exact Bool.noConfusion (eq.symm.trans hit.2)
          · have anyu : (g.inputs.map fun j => u.getD j false).any id = true := by
              simpa only [eval,ho,orEval] using hit.1
            have anyv : (g.inputs.map fun j => v.getD j false).any id = true := by
              simp only [List.any_eq_true,List.mem_map,exists_exists_and_eq_and,id_eq] at anyu ⊢
              obtain ⟨j,h0,h1⟩ := anyu
              exact ⟨j,h0,ord j h1⟩
            have eq : eval v = true := by simpa only [eval,ho,orEval] using anyv
            exact Bool.noConfusion (eq.symm.trans hit.2)
          · exact hn
        refine ⟨⟨0,by simp⟩,hn,?_,?_⟩
        · change (ls.foldl scalar (u ++ [eval u])).getD (u.length + 0) false = true
          rw [Nat.add_zero,early _ _ _ (by simp),List.getD_append_right _ _ _ _ (by omega)]
          simpa using hit.1
        · change (ls.foldl scalar (v ++ [eval v])).getD (u.length + 0) false = false
          rw [Nat.add_zero,len,early _ _ _ (by simp),List.getD_append_right _ _ _ _ (by omega)]
          simpa using hit.2
      · have o : ordered [eval u] [eval v] := by
          intro j hj'
          cases j with
          | zero =>
            change eval u = true at hj'
            change eval v = true
            cases h : eval v with
            | false => exact (hit ⟨hj',h⟩).elim
            | true => rfl
          | succ j =>
            change ([] : List Bool).getD j false = true at hj'
            simp at hj'
        obtain ⟨k,kop,ku,kv⟩ := ih (fun g h => legal g (by simp [h]))
          (u ++ [eval u]) (v ++ [eval v]) (by simp [len]) (joinOrder u v len ord _ _ o) hi hj
        refine ⟨k.succ,kop,?_,?_⟩
        · change (ls.foldl scalar (u ++ [eval u])).getD (u.length + (k.val + 1)) false = true
          rw [show u.length + (k.val + 1) = (u ++ [eval u]).length + k.val by simp; omega]
          exact ku
        · change (ls.foldl scalar (v ++ [eval v])).getD (u.length + (k.val + 1)) false = false
          rw [show u.length + (k.val + 1) = (u ++ [eval u]).length + k.val by simp; omega]
          exact kv
  have falling (p q : ℕ) (sub : p &&& q = p)
      (hp0 : C.eval (bank p) = true) (hq0 : C.eval (bank q) = false) :
      ∃ k : Fin C.gates.length, (C.gates.get k).op = .not ∧
        (C.wires (bank p)).getD (11 + k.val) false = true ∧
        (C.wires (bank q)).getD (11 + k.val) false = false := by
    have bits (i : Fin 9) (hp' : row p i = true) : row q i = true := by
      have h := congrArg (fun n : ℕ => n.testBit i.val) sub
      simp only [Nat.testBit_and] at h
      change p.testBit i.val = true at hp'
      simpa [row,hp'] using h
    have op (i j : Fin 9) (h : (row p i || row p j) = true) :
        (row q i || row q j) = true := by
      simp only [Bool.or_eq_true] at h ⊢
      exact h.imp (bits _) (bits _)
    have ord : ordered (bank p) (bank q) := by
      refine joinOrder _ _ (by simp) ?_ _ _ ?_
      · intro i hi
        by_cases h : i < 9
        · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),
              List.getElem_ofFn] at hi ⊢
          exact bits ⟨i,h⟩ hi
        · simp [List.getD,h] at hi
      · intro i hi
        rcases i with _ | _ | i
        · exact op 0 4 hi
        · exact op a b hi
        · change ([] : List Bool).getD i false = true at hi
          simp at hi
    have lg (g) (hg : g ∈ C.gates) : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan g hg).1
    have he := descend C.gates lg (bank p) (bank q) (by simp [bank]) ord C.output hp0 hq0
    rw [show (bank p).length = 11 by simp [bank]] at he
    exact he
  let r := choose n
  have samp : C.eval (bank (pt r)) = tag r := sample r
  rcases geometry n with ⟨he,ht⟩ | ⟨ht,hp',hq,hs,hf⟩ | ⟨ht,hp',hq,hs,ht'⟩
  · rw [ht,he]; exact sample _
  · rw [ht]
    by_contra wrong
    have ht0 : C.eval (bank n.val) = true := by simpa using wrong
    have hf1 := samp.trans hf
    obtain ⟨j,hj⟩ := falsePositive a b C hp fan small readPins n.val (pt r) hp' hq
      hs ht0 hf1 (falling n.val (pt r) hs ht0 hf1)
    exact hj (sample j)
  · rw [ht]
    by_contra wrong
    have hf1 : C.eval (bank n.val) = false := by simpa using wrong
    have ht0 := samp.trans ht'
    obtain ⟨j,hj⟩ := falseNegative a b C hp fan small readPins (pt r) n.val hp' hq
      hs ht0 hf1 (falling (pt r) n.val hs ht0 hf1)
    exact hj (sample j)
