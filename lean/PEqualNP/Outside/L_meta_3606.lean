import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

def L_meta_3606_wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def L_meta_3606.WireLe (w w' : List Bool) : Prop :=
  ∀ i, w.getD i false ≤ w'.getD i false

theorem L_meta_3606.wiresFrom_length (gs : List Gate) (w : List Bool) :
    (L_meta_3606_wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [L_meta_3606_wiresFrom]
  | cons g gs ih =>
    change (L_meta_3606_wiresFrom gs
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length =
        w.length + (g :: gs).length
    rw [ih]
    simp
    omega

theorem L_meta_3606.wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    L_meta_3606_wiresFrom (gs ++ gs') w =
      L_meta_3606_wiresFrom gs' (L_meta_3606_wiresFrom gs w) := by
  simp [L_meta_3606_wiresFrom, List.foldl_append]

theorem L_meta_3606.WireLe_append (w w' : List Bool) (a b : Bool)
    (hlen : w.length = w'.length) (hle : L_meta_3606.WireLe w w') (hab : a ≤ b) :
    L_meta_3606.WireLe (w ++ [a]) (w' ++ [b]) := by
  intro i
  by_cases hi : i < w.length
  · have hi' : i < w'.length := by omega
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi']
    exact hle i
  · by_cases heq : i = w.length
    · subst i
      have hlen' : w'.length ≤ w.length := by omega
      rw [List.getD_append_right _ _ _ _ (by simp),
        List.getD_append_right _ _ _ _ (by simpa [hlen])]
      simpa [hlen] using hab
    · have hgt : w.length < i := by omega
      have hgt' : w'.length < i := by omega
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      have hidx : 1 ≤ i - w.length := by omega
      have hidx' : 1 ≤ i - w'.length := by omega
      rw [List.getD_eq_default _ _ hidx, List.getD_eq_default _ _ hidx']

theorem L_meta_3606.gateEval_mono (op : GateOp) (xs ys : List Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : xs.length = ys.length)
    (hxy : ∀ i, xs.getD i false ≤ ys.getD i false) :
    op.eval xs ≤ op.eval ys := by
  rcases hop with hop | hop
  · subst op
    induction xs generalizing ys with
    | nil =>
      cases ys <;> simp_all [GateOp.eval]
    | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
        simp only [List.length_cons] at hlen
        have hxy0 : x ≤ y := by simpa using hxy 0
        have hrest : ∀ i, xs.getD i false ≤ ys.getD i false := by
          intro i
          have := hxy (i + 1)
          simpa using this
        have hlen' : xs.length = ys.length := by omega
        have htail := ih ys hlen' hrest
        simp only [GateOp.eval, List.all_cons]
        cases x <;> cases y
        · simp [GateOp.eval]
        · simp [GateOp.eval]
        · have hfalse : False := by simpa [Bool.le_iff_imp] using hxy0
          exact False.elim hfalse
        · simpa [GateOp.eval] using htail
  · subst op
    induction xs generalizing ys with
    | nil =>
      cases ys <;> simp_all [GateOp.eval]
    | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
        simp only [List.length_cons] at hlen
        have hxy0 : x ≤ y := by simpa using hxy 0
        have hrest : ∀ i, xs.getD i false ≤ ys.getD i false := by
          intro i
          have := hxy (i + 1)
          simpa using this
        have hlen' : xs.length = ys.length := by omega
        have htail := ih ys hlen' hrest
        simp only [GateOp.eval, List.any_cons]
        cases x <;> cases y
        · simpa [GateOp.eval] using htail
        · simp [GateOp.eval]
        · have hfalse : False := by simpa [Bool.le_iff_imp] using hxy0
          exact False.elim hfalse
        · simp [GateOp.eval]

theorem L_meta_3606.wiresFrom_mono (gs : List Gate)
    (hok : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ w w', w.length = w'.length → L_meta_3606.WireLe w w' →
      L_meta_3606.WireLe (L_meta_3606_wiresFrom gs w)
        (L_meta_3606_wiresFrom gs w') := by
  induction gs with
  | nil =>
    intro w w' _ hle
    exact hle
  | cons g gs ih =>
    intro w w' hlen hle
    have hg := hok g (by simp)
    have hval : g.op.eval (g.inputs.map fun i => w.getD i false) ≤
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      apply L_meta_3606.gateEval_mono
      · exact hg.1
      · simp
      · intro i
        induction g.inputs generalizing i with
        | nil => simp
        | cons a inputs ih =>
          cases i with
          | zero => simpa using hle a
          | succ i => simpa using ih i
    have hstep : L_meta_3606.WireLe
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) :=
      L_meta_3606.WireLe_append w w' _ _ hlen hle hval
    change L_meta_3606.WireLe
      (L_meta_3606_wiresFrom gs
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]))
      (L_meta_3606_wiresFrom gs
        (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]))
    apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    · simp [hlen]
    · exact hstep

theorem L_meta_3606.take_split {α : Type} (l : List α) (i j : ℕ)
    (hij : i < j) (hj : j ≤ l.length) :
    l.take j = l.take i ++ [l[i]] ++ (l.take j).drop (i + 1) := by
  have htakej : (l.take j).take (i + 1) = l.take (i + 1) := by
    simp [List.take_take, Nat.min_eq_left (by omega : i + 1 ≤ j)]
  conv_lhs =>
    rw [← List.take_append_drop (i + 1) (l.take j), htakej,
      List.take_succ_eq_append_getElem (by omega : i < l.length)]

theorem PEqualNP.Outside.L_meta_3606
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (i j : Fin C.gates.length)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hij : i < j)
    (hjlast : ↑j + 1 = C.size)
    (hout : C.output = 9 + ↑j)
    (hiNot : (C.gates.get i).op = GateOp.not)
    (hjNot : (C.gates.get j).op = GateOp.not)
    (hNots : ∀ k : Fin C.gates.length,
      (C.gates.get k).op = GateOp.not → k = i ∨ k = j)
    (hzero : PEqualNP.MetaComplexity.circuitFun 9 C (fun _ => false) = false)
    (hone : PEqualNP.MetaComplexity.circuitFun 9 C (fun _ => true) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ ↑i ∧
        PEqualNP.MetaComplexity.circuitFun 9 D =
          PEqualNP.MetaComplexity.circuitFun 9 C := by
  classical
  let pre : List Gate := C.gates.take i.val
  let middle : List Gate := (C.gates.take j.val).drop (i.val + 1)
  let first : Gate := C.gates.get i
  let last : Gate := C.gates.get j
  have hilen : i.val < C.gates.length := i.isLt
  have hjlen : j.val < C.gates.length := j.isLt
  have hjlast' : j.val + 1 = C.gates.length := by
    simpa [Circuit.size] using hjlast
  have hpreLen : pre.length = i.val := by
    simp [pre, Nat.min_eq_left hilen.le]
  have hmidLen : middle.length = j.val - (i.val + 1) := by
    simp [middle, List.length_drop, List.length_take, Nat.min_eq_left hjlen.le]
  have hsplitI : C.gates.take j.val = pre ++ [first] ++ middle := by
    rw [L_meta_3606.take_split C.gates i.val j.val hij hjlen.le]
    simp [pre, middle, first]
  have hsplitJ' :
      C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val + 1) := by
    simp [List.take_append_drop]
  have hdrop : C.gates.drop (j.val + 1) = [] := by
    apply List.drop_eq_nil_of_le
    omega
  have hsplitJ : C.gates = C.gates.take j.val ++ [last] := by
    rw [hdrop] at hsplitJ'
    simpa [last] using hsplitJ'
  have hsplit : C.gates = pre ++ [first] ++ middle ++ [last] := by
    rw [hsplitJ, hsplitI]
  have hpreOK : ∀ g ∈ pre,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hg
    have hklt : k.val < i.val := by
      have hk := k.isLt
      simp [pre, List.length_take] at hk
      omega
    let kC : Fin C.gates.length := ⟨k.val, by omega⟩
    have hget : pre.get k = C.gates.get kC := by
      simp [pre, kC, List.getElem_take, hklt]
    have hmem : C.gates.get kC ∈ C.gates := List.get_mem C.gates kC
    have hgate := hfan (C.gates.get kC) hmem
    have hnot : (C.gates.get kC).op ≠ GateOp.not := by
      intro hn
      have hh := hNots kC hn
      rcases hh with hh | hh
      · have hv := congrArg Fin.val hh
        have hv' : k.val = i.val := by simpa [kC] using hv
        omega
      · have hv := congrArg Fin.val hh
        have hv' : k.val = j.val := by simpa [kC] using hv
        omega
    rw [hget]
    rcases hgate with ⟨hop, hlen⟩
    rcases hop with hop | hop | hop
    · exact ⟨Or.inl hop, hlen⟩
    · exact ⟨Or.inr hop, hlen⟩
    · exact False.elim (hnot hop)
  have hmiddleOK : ∀ g ∈ middle,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hg
    have hkbound : i.val + 1 + k.val < j.val := by
      have hk := k.isLt
      simp [middle, List.length_drop, List.length_take, Nat.min_eq_left hjlen.le] at hk
      omega
    let kC : Fin C.gates.length := ⟨i.val + 1 + k.val, by omega⟩
    have hget : middle.get k = C.gates.get kC := by
      simp [middle, kC, List.getElem_drop, List.getElem_take, hkbound]
    have hmem : C.gates.get kC ∈ C.gates := List.get_mem C.gates kC
    have hgate := hfan (C.gates.get kC) hmem
    have hnot : (C.gates.get kC).op ≠ GateOp.not := by
      intro hn
      have hh := hNots kC hn
      rcases hh with hh | hh
      · have hv := congrArg Fin.val hh
        have hv' : i.val + 1 + k.val = i.val := by simpa [kC] using hv
        omega
      · have hv := congrArg Fin.val hh
        have hv' : i.val + 1 + k.val = j.val := by simpa [kC] using hv
        omega
    rw [hget]
    rcases hgate with ⟨hop, hlen⟩
    rcases hop with hop | hop | hop
    · exact ⟨Or.inl hop, hlen⟩
    · exact ⟨Or.inr hop, hlen⟩
    · exact False.elim (hnot hop)
  let zero : Fin 9 → Bool := fun _ => false
  let one : Fin 9 → Bool := fun _ => true
  let w (x : Fin 9 → Bool) := L_meta_3606_wiresFrom pre (List.ofFn x)
  let a (x : Fin 9 → Bool) :=
    first.op.eval (first.inputs.map fun r => (w x).getD r false)
  let m (x : Fin 9 → Bool) := L_meta_3606_wiresFrom middle (w x ++ [a x])
  let lastIdx := last.inputs.headD 0
  let z (x : Fin 9 → Bool) := (m x).getD lastIdx false
  let firstIdx := first.inputs.headD 0
  let D : Circuit := ⟨pre, firstIdx⟩
  have hwLen (x : Fin 9 → Bool) : (w x).length = 9 + i.val := by
    simp [w, L_meta_3606.wiresFrom_length, pre, Nat.min_eq_left hilen.le]
  have hmLen (x : Fin 9 → Bool) : (m x).length = 9 + j.val := by
    simp [m, L_meta_3606.wiresFrom_length, List.length_append, List.length_singleton,
      w, hwLen, hmidLen]
    omega
  have hrun (x : Fin 9 → Bool) :
      C.wires (List.ofFn x) = L_meta_3606_wiresFrom [last] (m x) := by
    change L_meta_3606_wiresFrom C.gates (List.ofFn x) = _
    rw [hsplit]
    simp only [L_meta_3606.wiresFrom_append]
    simp [m, a, w, L_meta_3606_wiresFrom]
  have hfinal (x : Fin 9 → Bool) :
      C.eval (List.ofFn x) =
        last.op.eval (last.inputs.map fun r => (m x).getD r false) := by
    change (C.wires (List.ofFn x)).getD C.output false = _
    rw [hout, hrun x]
    simp [L_meta_3606_wiresFrom, hmLen]
  have hlastOp : last.op = GateOp.not := by
    simpa [last] using hjNot
  have hzero' : C.eval (List.ofFn zero) = false := by
    simpa [PEqualNP.MetaComplexity.circuitFun, zero] using hzero
  have hone' : C.eval (List.ofFn one) = true := by
    simpa [PEqualNP.MetaComplexity.circuitFun, one] using hone
  have hlastNe : last.inputs ≠ [] := by
    intro he
    have h := hfinal zero
    rw [hzero'] at h
    rw [hlastOp, he, GateOp.eval] at h
    simp at h
  have hfinalNot (x : Fin 9 → Bool) :
      C.eval (List.ofFn x) = !(z x) := by
    rw [hfinal x]
    cases he : last.inputs with
    | nil => exact False.elim (hlastNe he)
    | cons hd tl =>
      rw [hlastOp]
      have hidx : lastIdx = hd := by
        change last.inputs.headD 0 = hd
        rw [he]
        rfl
      simp [GateOp.eval, z, lastIdx, hidx, he]
  have hz0 : z zero = true := by
    have h : false = !(z zero) := by
      calc
        false = C.eval (List.ofFn zero) := hzero'.symm
        _ = !(z zero) := hfinalNot zero
    cases hz : z zero <;> simp [hz] at h ⊢
  have hz1 : z one = false := by
    have h : true = !(z one) := by
      calc
        true = C.eval (List.ofFn one) := hone'.symm
        _ = !(z one) := hfinalNot one
    cases hz : z one <;> simp [hz] at h ⊢
  have hinput0 (x : Fin 9 → Bool) :
      L_meta_3606.WireLe (List.ofFn zero) (List.ofFn x) := by
    intro r
    by_cases hr : r < 9
    · have hzero : (List.ofFn zero).getD r false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [hr, zero]
      have hx : (List.ofFn x).getD r false = x ⟨r, hr⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [hr]
      rw [hzero, hx]
      exact Bool.false_le _
    · simp [List.getD_eq_getElem?_getD, hr, zero]
  have hinput1 (x : Fin 9 → Bool) :
      L_meta_3606.WireLe (List.ofFn x) (List.ofFn one) := by
    intro r
    by_cases hr : r < 9
    · have hx : (List.ofFn x).getD r false = x ⟨r, hr⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [hr]
      have hone : (List.ofFn one).getD r false = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [hr, one]
      rw [hx, hone]
      exact Bool.le_true _
    · simp [List.getD_eq_getElem?_getD, hr, one]
  have hpre0 (x : Fin 9 → Bool) : L_meta_3606.WireLe (w zero) (w x) := by
    apply L_meta_3606.wiresFrom_mono pre hpreOK
    · simp [w]
    · exact hinput0 x
  have hpre1 (x : Fin 9 → Bool) : L_meta_3606.WireLe (w x) (w one) := by
    apply L_meta_3606.wiresFrom_mono pre hpreOK
    · simp [w]
    · exact hinput1 x
  have hmidLe (x y : Fin 9 → Bool) (ha : a x ≤ a y)
      (hw : L_meta_3606.WireLe (w x) (w y)) :
      L_meta_3606.WireLe (m x) (m y) := by
    apply L_meta_3606.wiresFrom_mono middle hmiddleOK
    · simp [List.length_append, List.length_singleton, hwLen]
    · exact L_meta_3606.WireLe_append (w x) (w y) (a x) (a y)
        (by rw [hwLen, hwLen]) hw ha
  have haEndpoints : a zero = true ∧ a one = false := by
    have hnot : ¬ a zero ≤ a one := by
      intro ha
      have hle := hmidLe zero one ha (hpre0 one)
      have hzle := hle lastIdx
      change z zero ≤ z one at hzle
      rw [hz0, hz1] at hzle
      simpa [Bool.le_iff_imp] using hzle
    cases hzeroA : a zero <;> cases honeA : a one
    · exact False.elim (hnot (by simp [hzeroA, honeA]))
    · exact False.elim (hnot (by simp [hzeroA, honeA]))
    · simpa [hzeroA, honeA]
    · exact False.elim (hnot (by simp [hzeroA, honeA]))
  have hza (x : Fin 9 → Bool) : z x = a x := by
    cases hx : a x
    · have hle := hmidLe x one (by simp [hx, haEndpoints.2]) (hpre1 x)
      have hzle := hle lastIdx
      change z x ≤ z one at hzle
      rw [hz1] at hzle
      cases hzx : z x
      · rfl
      · have hbad : (true : Bool) ≤ false := by simpa [hzx] using hzle
        have : False := by simpa [Bool.le_iff_imp] using hbad
        exact False.elim this
    · have hle := hmidLe zero x (by simp [hx, haEndpoints.1]) (hpre0 x)
      have hzle := hle lastIdx
      change z zero ≤ z x at hzle
      rw [hz0] at hzle
      cases hzx : z x
      · have hbad : (true : Bool) ≤ false := by simpa [hzx] using hzle
        have : False := by simpa [Bool.le_iff_imp] using hbad
        exact False.elim this
      · rfl
  have hfirstOp : first.op = GateOp.not := by
    simpa [first] using hiNot
  have hfirstNe : first.inputs ≠ [] := by
    intro he
    have hconst : a zero = a one := by
      change first.op.eval (first.inputs.map fun r => (w zero).getD r false) =
        first.op.eval (first.inputs.map fun r => (w one).getD r false)
      rw [he]
      rfl
    rw [haEndpoints.1, haEndpoints.2] at hconst
    cases hconst
  have haEval (x : Fin 9 → Bool) : a x = !((w x).getD firstIdx false) := by
    cases he : first.inputs with
    | nil => exact False.elim (hfirstNe he)
    | cons hd tl =>
      change first.op.eval (first.inputs.map fun r => (w x).getD r false) =
        !((w x).getD firstIdx false)
      rw [hfirstOp]
      simp [GateOp.eval, firstIdx, he]
  have hCfun (x : Fin 9 → Bool) :
      C.eval (List.ofFn x) = (w x).getD firstIdx false := by
    rw [hfinalNot x, hza x, haEval x]
    simp
  refine ⟨D, ?_, ?_, ?_⟩
  · change PEqualNP.MetaComplexity.FanInTwo D
    simp only [PEqualNP.MetaComplexity.FanInTwo, D]
    intro g hg
    rcases hpreOK g hg with ⟨hop, hlen⟩
    rcases hop with hop | hop
    · exact ⟨by simp [hop], hlen⟩
    · exact ⟨by simp [hop], hlen⟩
  · simp [D, Circuit.size, hpreLen]
  · funext x
    change D.eval (List.ofFn x) = C.eval (List.ofFn x)
    rw [hCfun x]
    rfl
