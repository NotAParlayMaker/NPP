import Mathlib.Data.List.GetD
import Mathlib.Tactic.ByContra
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The normalized truth table treats the fixed bit as a constant, and
-- the free-negation argument of L-meta-2163 covers the smaller binary budget.
set_option maxRecDepth 3000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_5140_1
    (binaryCase : ∀ (b : Bool) (C : Circuit), FanInTwo C →
      (C.gates.countP fun g => !g.op.eval [false]) ≤ 12 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2] ++ [b]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (monotoneCase : ∀ (b : Bool) (C : Circuit), FanInTwo C → C.size = 13 → C.output = 23 →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 11 + j.val ∨ i = 24) →
      (∀ g ∈ C.gates, g.op ≠ .not) →
      let run := fun r : ℕ => C.eval ((List.ofFn fun i : Fin 9 => r.testBit i.val) ++
        [r.testBit 0 || r.testBit 2] ++ [b])
      (∃ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ), run r = false) ∨
      (∃ r ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ), run r = true)) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (13 : ℕ) →       ∃ (x5 : Fin (9 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ))];         x2.eval (x6 ++ [x1]) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  classical
  intro b C legal sizeBound
  let f (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let input (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2] ++ [b]
  by_cases notGate : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hg, hop⟩ := notGate
    have hit : g.op.eval [false] = true := by rw [hop]; rfl
    have positive : 0 < C.gates.countP (fun g => g.op.eval [false]) :=
      List.countP_pos_iff.mpr ⟨g,hg,hit⟩
    have total := List.length_eq_countP_add_countP (fun g : Gate => g.op.eval [false])
      (l := C.gates)
    have boolCompl (g : Gate) : decide (¬ g.op.eval [false] = true) =
        !g.op.eval [false] := by
      cases g.op.eval [false] <;> rfl
    simp_rw [boolCompl] at total
    change C.gates.length ≤ 13 at sizeBound
    exact binaryCase b C legal (by omega)
  have noNot (g : Gate) (hg : g ∈ C.gates) : g.op ≠ .not := fun h =>
    notGate ⟨g,hg,h⟩
  by_contra h
  have computes (x : Fin 9 → Bool) : C.eval (input x) = f x := by
    by_contra mismatch
    exact h ⟨x,mismatch⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have lenRun (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih,List.length_cons]
      simp [step]
      omega
  have retain (gs : List Gate) (w : List Bool) (i : ℕ) (good : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step w g) (by simpa [step] using Nat.lt_succ_of_lt good)]
      exact List.getD_append _ _ _ _ good
  have inLength (x : Fin 9 → Bool) : (input x).length = 11 := by simp [input]
  have outputExists : C.output < 11 + C.gates.length := by
    by_contra! bad
    have hfull : (C.gates.foldl step (input (fun _ => true))).getD C.output false = true := computes _
    rw [List.getD_eq_default _ _ (by rw [lenRun,inLength]; exact bad)] at hfull
    exact Bool.false_ne_true hfull
  have lengthC : C.gates.length ≤ 13 := sizeBound
  have padded : ∃ D : Circuit, FanInTwo D ∧ D.size = 13 ∧ D.output = 23 ∧
      (∀ g ∈ D.gates, g.op ≠ .not) ∧ ∀ ws : List Bool, ws.length = 11 → D.eval ws = C.eval ws := by
    by_cases h23 : C.output = 23
    · have size13 : C.size = 13 := by change C.gates.length = 13; omega
      exact ⟨C,legal,size13,h23,noNot,fun _ _ => rfl⟩
    let base := C.gates.take 12
    let copy : Gate := ⟨GateOp.or,[C.output,C.output]⟩
    let extra := 13 - base.length
    let tail := List.replicate extra copy
    let D : Circuit := ⟨base ++ tail,23⟩
    have baseSmall : base.length ≤ 12 := by simp [base,List.length_take]
    have positive : 0 < extra := by dsimp [extra]; omega
    have count : base.length + extra = 13 := by dsimp [extra]; omega
    have use : C.output < 11 + base.length := by
      have baseLen : base.length = min 12 C.gates.length := by simp [base,List.length_take]
      omega
    have legalCopy : ∀ g ∈ tail, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      have eq : g = copy := (List.mem_replicate.mp hg).2
      rw [eq]
      simp [copy]
    have legalD : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hg|hg
      · exact legal _ (List.mem_of_mem_take hg)
      · exact legalCopy _ hg
    have noNotD (g : Gate) (hg : g ∈ D.gates) : g.op ≠ .not := by
      rcases List.mem_append.mp hg with hg | hg
      · exact noNot g (List.mem_of_mem_take hg)
      · rw [(List.mem_replicate.mp hg).2]
        simp [copy]
    have sizeD : D.size = 13 := by
      change (base ++ tail).length = 13
      rw [List.length_append]
      simpa only [tail,List.length_replicate] using count
    have copyEval (ws : List Bool) : step ws copy = ws ++ [ws.getD C.output false] := by
      change ws ++ [GateOp.or.eval [ws.getD C.output false,ws.getD C.output false]] = _
      cases (ws.getD C.output false) <;> rfl
    have copies (k : ℕ) (ws : List Bool) (known : C.output < ws.length) :
        ((List.replicate k copy).foldl step ws) = ws ++ List.replicate k (ws.getD C.output false) := by
      induction k generalizing ws with
      | zero => simp
      | succ k ih =>
        rw [List.replicate_succ,List.foldl_cons,copyEval,ih _ (by simp; omega)]
        rw [List.getD_append _ _ _ _ known, List.replicate_succ]
        simp only [List.append_assoc,List.singleton_append]
    refine ⟨D,legalD,sizeD,rfl,noNotD,?_⟩
    intro ws hw
    let mid := base.foldl step ws
    have lm : mid.length = 11 + base.length := (lenRun base ws).trans (by rw [hw])
    have midKnown : C.output < mid.length := lm ▸ use
    have baseEval : mid.getD C.output false = C.eval ws := by
      have split : C.gates = base ++ C.gates.drop 12 := (List.take_append_drop _ _).symm
      change mid.getD C.output false = (C.gates.foldl step ws).getD C.output false
      rw [split,List.foldl_append]
      exact (retain _ _ _ midKnown).symm
    change ((base ++ tail).foldl step ws).getD 23 false = C.eval ws
    rw [List.foldl_append,copies extra mid midKnown,List.getD_append_right _ _ _ _ (by omega)]
    have less : 23 - mid.length < (List.replicate extra (mid.getD C.output false)).length := by simp; omega
    rw [List.getD_eq_getElem _ _ less,List.getElem_replicate]
    exact baseEval
  obtain ⟨D,dLegal,dSize,dOut,noNotD,evalD⟩ := padded
  have lengthD : D.gates.length = 13 := dSize
  let cap (j i : ℕ) := if i < 11 + j then i else 24
  let fix (j : ℕ) (g : Gate) := (⟨g.op,g.inputs.map (cap j)⟩ : Gate)
  let normal (gs : List Gate) (j : ℕ) := (gs.zipIdx j).map (fun p => fix p.2 p.1)
  let N : Circuit := ⟨normal D.gates 0,23⟩
  have hcap (j i : ℕ) : cap j i < 11 + j ∨ cap j i = 24 := by
    dsimp [cap]
    split <;> simp_all
  have fixStep (g : Gate) (w : List Bool) (j : ℕ) (hLen : w.length = 11 + j) (hJ : j < 13) :
      step w (fix j g) = step w g := by
    have equal (i : ℕ) : w.getD (cap j i) false = w.getD i false := by
      by_cases small : i < 11 + j
      · simp only [cap,ite_eq_left small]
      · rw [show cap j i = 24 from ite_eq_right small]
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    have mapEq : (g.inputs.map (cap j)).map (fun i => w.getD i false) = g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => equal i)
    change w ++ [g.op.eval ((g.inputs.map (cap j)).map (fun i => w.getD i false))] =
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    rw [mapEq]
  have sameRun (gs : List Gate) (j : ℕ) (ws : List Bool) (hLen : ws.length = 11 + j)
      (budget : j + gs.length ≤ 13) : (normal gs j).foldl step ws = gs.foldl step ws := by
    induction gs generalizing j ws with
    | nil => rfl
    | cons g gs ih =>
      change (normal gs (j+1)).foldl step (step ws (fix j g)) = gs.foldl step (step ws g)
      have hj : j < 13 := by simp only [List.length_cons] at budget; omega
      rw [fixStep g ws j hLen hj]
      apply ih
      · simp [step,hLen,Nat.add_assoc]
      · simp only [List.length_cons] at budget
        omega
  have evalN (ws : List Bool) (hw : ws.length = 11) : N.eval ws = D.eval ws := by
    change ((normal D.gates 0).foldl step ws).getD 23 false = (D.gates.foldl step ws).getD D.output false
    rw [dOut,sameRun D.gates 0 ws (by simpa using hw) (by omega)]
  have goodN (x : Fin 9 → Bool) : N.eval (input x) = f x :=
    (evalN _ (inLength x)).trans ((evalD _ (inLength x)).trans (computes x))
  have members (g : Gate) (hg : g ∈ N.gates) : ∃ j t, j < 13 ∧ t ∈ D.gates ∧ g = fix j t := by
    obtain ⟨⟨t,j⟩,ht,eq⟩ := List.mem_map.mp hg
    obtain ⟨bound,he⟩ := List.mem_zipIdx' ht
    exact ⟨j,t,by omega,he ▸ List.getElem_mem bound,eq.symm⟩
  have legalN : FanInTwo N := by
    intro g hg
    obtain ⟨j,t,_,ht,rfl⟩ := members g hg
    refine ⟨(dLegal _ ht).1,?_⟩
    simpa only [fix,List.length_map] using (dLegal t ht).2
  have sizeN : N.size = 13 := by
    change (normal D.gates 0).length = 13
    simpa only [normal,List.length_map,List.length_zipIdx] using lengthD
  have canonical (j : Fin N.gates.length) (i : ℕ) (hi : i ∈ (N.gates.get j).inputs) :
      i < 11 + j.val ∨ i = 24 := by
    have jl : j.val < (D.gates.zipIdx 0).length := by simpa only [N,normal,List.length_map] using j.isLt
    have orig : j.val < D.gates.length := by simpa using jl
    have access : N.gates.get j = fix j.val (D.gates.get ⟨j.val,orig⟩) := by
      change (normal D.gates 0)[j.val]'j.isLt = _
      simp only [normal,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
      rfl
    rw [access] at hi
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hi
    exact hcap j.val u
  have onlyAO (g : Gate) (hg : g ∈ N.gates) : g.op ≠ .not := by
    obtain ⟨j,t,_,ht,rfl⟩ := members g hg
    exact noNotD t ht
  rcases monotoneCase b N legalN sizeN rfl canonical onlyAO with ⟨r,hr,off⟩|⟨r,hr,off⟩
  · have positiveRows : ∀ r : ℕ, r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ) →
        f (fun i => r.testBit i.val) = true := by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have right := (goodN (fun i => r.testBit i.val)).trans (positiveRows r hr)
    change N.eval (input (fun i => r.testBit i.val)) = false at off
    rw [off] at right
    exact Bool.false_ne_true right
  · have negativeRows : ∀ r : ℕ, r ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ) →
        f (fun i => r.testBit i.val) = false := by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have right := (goodN (fun i => r.testBit i.val)).trans (negativeRows r hr)
    change N.eval (input (fun i => r.testBit i.val)) = true at off
    rw [off] at right
    exact Bool.noConfusion right
