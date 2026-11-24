import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 14000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4449_1
  (erase :
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let rows := fun (n : ℕ) (entries : List (Bool ⊕ ℕ)) (x : Fin n → Bool) => entries.map (Sum.elim id (fun i => (List.ofFn x).getD i false))
    ∀ (n : ℕ) (entries : List (Bool ⊕ ℕ)) (fixed : ℕ → Bool) (C : Circuit), FanInTwo C →
      (∀ i, fixed i = true → i < entries.length ∧ ∃ b : Bool, entries.getD i (.inl false) = .inl b) →
      (∃ x : Fin n → Bool, C.eval (rows n entries x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (fun g => (reads g).any fixed) ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (rows n entries x))
  (ordinary : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12)
  (negatedDegreeTwo :
    let H := fun x : Fin 8 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
    let minor := fun (k : Fin 8) (x : Fin 8 → Bool) => H (fun j => if j = k then !x j else x j)
    ∀ D : Circuit, FanInTwo D → D.size = 12 →
      ¬ (∀ x : Fin 8 → Bool, circuitFun 8 D x = minor 0 x))
  (negatedDegreeThree :
    let H := fun x : Fin 8 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
    let minor := fun (k : Fin 8) (x : Fin 8 → Bool) => H (fun j => if j = k then !x j else x j)
    ∀ D : Circuit, FanInTwo D → D.size = 12 →
      ¬ (∀ x : Fin 8 → Bool, circuitFun 8 D x = minor 4 x)) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (6 : Fin (9 : ℕ)) → x2 ≠ (7 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x10 : Fin (9 : ℕ) → Bool), x3.eval ((List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ))]).set ↑x2 !x10 x2) ≠ x1 x10 := by
  intro encoded r C hr0 hr4 hr6 hr7 fan budget
  let F := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let H := fun x : Fin 8 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  let minor := fun (k : Fin 8) (x : Fin 8 → Bool) => H (fun j => if j = k then !x j else x j)
  let inputs := fun (r : Fin 9) (x : Fin 9 → Bool) => (List.ofFn x ++ [x 0 || x 6]).set r.val (!x r)
  let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let rows := fun (n : ℕ) (entries : List (Bool ⊕ ℕ)) (x : Fin n → Bool) => entries.map (Sum.elim id (fun i => (List.ofFn x).getD i false))
  have boolAnd (l : List Bool) : GateOp.eval .and l = l.all id := rfl
  have boolOr (l : List Bool) : GateOp.eval .or l = l.any id := rfl
  have inputs_length (r : Fin 9) (x : Fin 9 → Bool) :
      (inputs r x).length = 10 := by simp [inputs]

  let baseRow (i : Fin 9) : Bool := decide (i = 0 ∨ i = 8)

  let plusSix (i : Fin 9) : Bool := decide (i = 6) || baseRow i

  let gateValue (w : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  have gate_kind {C : Circuit} (hC : FanInTwo C) {g : Gate} (hg : g ∈ C.gates) :
      g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

  have gateValue_congr {C : Circuit} (hC : FanInTwo C) {g : Gate}
      (hg : g ∈ C.gates) (w v : List Bool)
      (h : ∀ i ∈ reads g, w.getD i false = v.getD i false) :
      gateValue w g = gateValue v g := by
    have value (u : List Bool) :
        gateValue u g = g.op.eval ((reads g).map fun i => u.getD i false) := by
      rcases gate_kind hC hg with hop | hop | hop
      · simp [gateValue, reads, hop, boolAnd]
      · simp [gateValue, reads, hop, boolOr]
      · dsimp only [gateValue, reads]
        rw [hop]
        cases g.inputs <;> rfl
    rw [value w, value v, List.map_congr_left h]

  -- Equal appended values produce a common suffix of computed wires.
  have common_suffix (gs : List Gate) (w v : List Bool)
      (h : ∀ g ∈ gs, ∀ s, gateValue (w ++ s) g = gateValue (v ++ s) g) (s : List Bool) :
      ∃ t, gs.foldl (fun u g => u ++ [gateValue u g]) (w ++ s) = w ++ t ∧
        gs.foldl (fun u g => u ++ [gateValue u g]) (v ++ s) = v ++ t := by
    induction gs generalizing s with
    | nil => exact ⟨s, rfl, rfl⟩
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons, h g (by simp) s, List.append_assoc, List.append_assoc]
      exact ih (fun a ha => h a (by simp [ha])) _

  have append_agree {w v : List Bool} (hlen : w.length = v.length) (s : List Bool)
      (i : ℕ) (hi : w.getD i false = v.getD i false) :
      (w ++ s).getD i false = (v ++ s).getD i false := by
    by_cases hw : i < w.length
    · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (by omega), hi]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]

  have eval_eq_of_steps (C : Circuit) (w v : List Bool)
      (hlen : w.length = v.length) (hout : w.getD C.output false = v.getD C.output false)
      (h : ∀ g ∈ C.gates, ∀ s, gateValue (w ++ s) g = gateValue (v ++ s) g) :
      C.eval w = C.eval v := by
    obtain ⟨t, hw, hv⟩ := common_suffix C.gates w v h []
    simp only [List.append_nil] at hw hv
    change C.wires w = w ++ t at hw
    change C.wires v = v ++ t at hv
    change (C.wires w).getD C.output false = (C.wires v).getD C.output false
    rw [hw, hv]
    exact append_agree hlen t _ hout

  have eval_raw (C : Circuit) (w : List Bool) (hout : C.output < w.length) :
      C.eval w = w.getD C.output false := by
    obtain ⟨t, hw, _⟩ := common_suffix C.gates w w (fun _ _ _ => rfl) []
    simp only [List.append_nil] at hw
    change C.wires w = w ++ t at hw
    change (C.wires w).getD C.output false = w.getD C.output false
    rw [hw, List.getD_append _ _ _ _ hout]

  have has_reader {C : Circuit} (hC : FanInTwo C) (w v : List Bool)
      (hlen : w.length = v.length) (bad : ℕ → Prop) (hout : ¬bad C.output)
      (hraw : ∀ i, ¬bad i → w.getD i false = v.getD i false)
      (hne : C.eval w ≠ C.eval v) : ∃ g ∈ C.gates, ∃ i ∈ reads g, bad i := by
    by_contra! hnone
    refine hne (eval_eq_of_steps C w v hlen (hraw _ hout) ?_)
    intro g hg s
    apply gateValue_congr hC hg
    intro i hi
    exact append_agree hlen s i (hraw i (hnone g hg i hi))

  have getD_past (r : Fin 9) (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) :
      (inputs r x).getD i false = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr]
    · rfl
    · simpa only [inputs_length] using hi

  have output_not_six (r : Fin 9) (C : Circuit)
      (ev : ∀ x : Fin 9 → Bool, C.eval (inputs r x) = F x) : C.output ≠ 6 := by
    have check : ∀ r : Fin 9,
        let x : Fin 9 → Bool := fun j => decide (r ≠ 6 ∧ j = 6)
        (inputs r x).getD 6 false ≠ F x := by decide +kernel
    intro hout
    let x : Fin 9 → Bool := fun j => decide (r ≠ 6 ∧ j = 6)
    have bad := check r
    change (inputs r x).getD 6 false ≠ F x at bad
    have h : C.output < (inputs r x).length := by rw [hout, inputs_length]; decide
    have he := (eval_raw C (inputs r x) h).symm.trans (ev x)
    rw [hout] at he
    exact bad he

  have six_required (r : Fin 9) (C : Circuit) (fan : FanInTwo C)
      (ev : ∀ x : Fin 9 → Bool, C.eval (inputs r x) = F x) :
      1 ≤ C.gates.countP (fun g => (reads g).any (fun i => decide (i = 6))) := by
    have hout := output_not_six r C ev
    have checked : ∀ (r : Fin 9) (i : Fin 10), i.val ≠ 6 →
        (inputs r baseRow).getD i.val false = (inputs r plusSix).getD i.val false := by decide +kernel
    have agrees (i : ℕ) (hne : i ≠ 6) :
        (inputs r baseRow).getD i false = (inputs r plusSix).getD i false := by
      by_cases hi : i < 10
      · exact checked r ⟨i,hi⟩ hne
      · rw [getD_past _ _ _ (by omega),getD_past _ _ _ (by omega)]
    have different : C.eval (inputs r baseRow) ≠ C.eval (inputs r plusSix) := by
      rw [ev,ev]
      decide
    obtain ⟨g,hg,i,hi,eq⟩ := has_reader fan (inputs r baseRow) (inputs r plusSix) (by simp only [inputs_length])
      (fun i => i=6) hout agrees different
    have yes : (reads g).any (fun i => decide (i = 6)) = true :=
      List.any_eq_true.mpr ⟨i,hi,decide_eq_true eq⟩
    have mem : g ∈ C.gates.filter (fun g => (reads g).any (fun i => decide (i = 6))) :=
      List.mem_filter.mpr ⟨hg,yes⟩
    rw [List.countP_eq_length_filter]
    have p := List.length_pos_of_mem mem
    omega
  have prependSeed (D : Circuit) (fan : FanInTwo D) (g : Gate)
      (allowed : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) :
      let E : Circuit := ⟨g :: D.gates, D.output⟩
      FanInTwo E ∧ E.size = D.size + 1 ∧ ∀ w : List Bool,
        E.eval w = D.eval (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := by
    refine ⟨?_, rfl, fun _ => rfl⟩
    intro h hh
    change h ∈ g :: D.gates at hh
    rcases List.mem_cons.mp hh with rfl | hd
    · exact allowed
    · exact fan h hd

  have prependNot {n : ℕ} (D : Circuit) (fan : FanInTwo D) (j : Fin n) :
      let E : Circuit := ⟨⟨.not, [j.val]⟩ :: D.gates, D.output⟩
      FanInTwo E ∧ E.size = D.size + 1 ∧ ∀ y : Fin n → Bool,
        E.eval (List.ofFn y) = D.eval (List.ofFn y ++ [!(y j)]) := by
    let g : Gate := ⟨.not, [j.val]⟩
    have hs := prependSeed D fan g (by simp [g])
    refine ⟨hs.1, hs.2.1, fun y => ?_⟩
    have hread : (List.ofFn y).getD j.val false = y j := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt)]
      exact List.getElem_ofFn _
    change (⟨g :: D.gates, D.output⟩ : Circuit).eval (List.ofFn y) = _
    rw [hs.2.2]
    change D.eval (List.ofFn y ++ [!((List.ofFn y).getD j.val false)]) = _
    rw [hread]
  let rename (r : Fin 9) : Fin 9 → Fin 8 :=
    if r = 3 then ![1,5,7,4,0,2,0,3,6]
    else if r = 5 then ![7,3,2,1,5,4,0,6,0]
    else if r = 8 then ![2,3,7,4,6,1,0,5,0]
    else ![1,0,4,7,5,2,0,6,3]
  let cut (r : Fin 9) (x : Fin 8 → Bool) (i : Fin 9) : Bool :=
    if i = 6 then false else if i = r then !x (rename r i) else x (rename r i)
  let entries (r : Fin 9) : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin 9 => if i = 6 then Sum.inl false else Sum.inr (rename r i).val) ++
      [.inr (rename r 0).val]
  let fixed := fun i : ℕ => decide (i = 6)
  let target (r : Fin 9) := if r = 1 ∨ r = 8 then minor 0 else minor 4
  have accepted : ∀ r : Fin 9, r ≠ 0 → r ≠ 4 → r ≠ 6 → r ≠ 7 →
      r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 8 := by decide +kernel
  have hr := accepted r hr0 hr4 hr6 hr7
  have sameTarget : ∀ x : Fin 9 → Bool, encoded x = F x := by
    dsimp only [encoded,F]
    decide +kernel
  have sameInputs : ∀ x : Fin 8 → Bool, inputs r (cut r x) = rows 8 (entries r) x := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only [inputs,cut,rows,entries,rename]; decide +kernel)
  have sameMinor : ∀ x : Fin 8 → Bool, F (cut r x) = target r x := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only [F,cut,rename,target,H,minor]; decide +kernel)
  have hfalse : target r (fun _ => false) = false := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have frozenInputs (i : ℕ) (hf : fixed i = true) :
      i < (entries r).length ∧ ∃ b : Bool, (entries r).getD i (.inl false) = .inl b := by
    change decide (i = 6) = true at hf
    rcases of_decide_eq_true hf with rfl
    exact ⟨by simp [entries],false,rfl⟩
  by_contra failed
  have eval (x : Fin 9 → Bool) : C.eval (inputs r x) = F x := by
    have same : C.eval (inputs r x) = encoded x := by
      by_contra diff
      exact failed ⟨x,diff⟩
    exact same.trans (sameTarget x)
  have routed (x : Fin 8 → Bool) : C.eval (rows 8 (entries r) x) = target r x := by
    rw [← sameInputs,eval,sameMinor]
  obtain ⟨D,df,bound,semantics⟩ := erase 8 (entries r) fixed C fan frozenInputs
    ⟨fun _ => false, (routed (fun _ => false)).trans hfalse⟩
  have necessary := six_required r C fan eval
  change D.size + C.gates.countP (fun g => (reads g).any fixed) ≤ C.size at bound
  have small : D.size ≤ 12 := by
    change 1 ≤ C.gates.countP (fun g => (reads g).any fixed) at necessary
    omega
  have achieved (x : Fin 8 → Bool) : circuitFun 8 D x = target r x :=
    (semantics x).trans (routed x)
  have ofFnSnoc {n : ℕ} (x : Fin n → Bool) (b : Bool) :
      List.ofFn (Fin.snoc x b : Fin (n+1) → Bool) = List.ofFn x ++ [b] := by
    rw [List.ofFn_succ']
    simp
  have mustTwelve (k : Fin 8) (hk : k = 0 ∨ k = 4)
      (fits : ∀ x : Fin 8 → Bool, circuitFun 8 D x = minor k x) : D.size = 12 := by
    by_contra tooSmall
    have sub : D.size ≤ 11 := by omega
    let signed (x : Fin 8 → Bool) := fun i : Fin 8 => if i = k then !x i else x i
    let extended (x : Fin 8 → Bool) : Fin 9 → Bool := Fin.snoc x (!x k)
    let place : List (Bool ⊕ ℕ) :=
      List.ofFn (fun i : Fin 8 => Sum.inr (if i = k then 8 else i.val))
    have twice (x : Fin 8 → Bool) : minor k (signed x) = H x := by
      have same : (fun i : Fin 8 => if i = k then !(signed x i) else signed x i) = x := by
        funext i
        by_cases hi : i = k <;> simp [signed,hi]
      exact congrArg H same
    have slotRow : ∀ x : Fin 8 → Bool, rows 9 place (extended x) = List.ofFn (signed x) := by
      rcases hk with rfl | rfl <;>
        (dsimp only [rows,place,extended,signed]; decide +kernel)
    have restores (x : Fin 8 → Bool) : D.eval (rows 9 place (extended x)) = H x := by
      rw [slotRow]
      exact (fits (signed x)).trans (twice x)
    obtain ⟨D', df', rb, eq⟩ := erase 9 place (fun _ => false) D df
      (by intro _ hf; cases hf)
      ⟨extended (fun _ => false), (restores (fun _ => false)).trans rfl⟩
    let E : Circuit := ⟨⟨.not, [k.val]⟩ :: D'.gates,D'.output⟩
    have pre := prependNot D' df' k
    have pe : E.size = D'.size + 1 := pre.2.1
    have clipped : E.size ≤ 12 := by omega
    refine ordinary ⟨E,pre.1,clipped,?_⟩
    intro x
    have extendList : List.ofFn (extended x) = List.ofFn x ++ [!x k] := ofFnSnoc x (!x k)
    change E.eval (List.ofFn x) = H x
    have preEval : E.eval (List.ofFn x) = D'.eval (List.ofFn x ++ [!x k]) := pre.2.2 x
    rw [preEval, ← extendList, eq (extended x), restores x]
  by_cases kind : r = 1 ∨ r = 8
  · have fits (x : Fin 8 → Bool) : circuitFun 8 D x = minor 0 x := by
      exact (achieved x).trans (by dsimp only [target]; rw [ite_eq_left kind])
    apply negatedDegreeTwo D df (mustTwelve 0 (Or.inl rfl) fits)
    exact fits
  · have fits (x : Fin 8 → Bool) : circuitFun 8 D x = minor 4 x := by
      exact (achieved x).trans (by dsimp only [target]; rw [ite_eq_right kind])
    apply negatedDegreeThree D df (mustTwelve 4 (Or.inr rfl) fits)
    exact fits
