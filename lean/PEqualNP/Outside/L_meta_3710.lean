import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_3710 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (g a b : ℕ) (v : Fin n),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  g < C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [b, a]) →
  (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput v))).getD b false = true →
  (∀ w : Fin n, G.Adj v w → (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput w))).getD b false = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + g then a else i) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C g a b v hao hfun hg hop hinputs hunit hneighbors
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have foldl_step_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega

  have getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
      (w ++ t).getD i false = w.getD i false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_append_self (w : List Bool) (b : Bool) :
      (w ++ [b]).getD w.length false = b := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp

  have getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

  have foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hlt : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (step w g) hlt]
      exact getD_append_left_lt w _ i hi

  have foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
      (gs.foldl step w).getD i false = false := by
    apply getD_ge_len
    rw [foldl_step_len]
    exact hi

  have foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
      (gs.foldl step w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g0 gs ih =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : w.length < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
        have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
          getD_append_self w _
        rw [hself]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · have hilt : i < (step w g0).length := by
            simp only [step, List.length_append, List.length_cons, List.length_nil]
            omega
          simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
          exact (getD_append_left_lt w _ i hi).symm
        · simp only [hi, ↓reduceIte]
          exact getD_ge_len w i (Nat.le_of_not_lt hi)
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (step w g0) j' hj

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl step x := rfl


  have getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
      (w ++ [b]).getD m false = b := by
    subst hm
    simp [List.getD_eq_getElem?_getD]

  have getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
      (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    simp [List.getD_eq_getElem?_getD, hi]

  have monotone_foldl_step (gs : List Gate)
      (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (w1 w2 : List Bool) (hlen : w1.length = w2.length)
      (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
      ∀ k : ℕ, (gs.foldl step w1).getD k false = true →
        (gs.foldl step w2).getD k false = true := by
    induction gs generalizing w1 w2 with
    | nil => exact hle
    | cons g gs ih =>
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simpa using hM g List.mem_cons_self
      have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
        fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
      apply ih hM' (step w1 g) (step w2 g)
      · simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
      · intro k hk
        by_cases hlt : k < w1.length
        · have hlt2 : k < w2.length := hlen ▸ hlt
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
          exact hle k hk
        · by_cases heq : k = w1.length
          · subst heq
            have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
              simpa [step, getD_append_last_eq w1 _ w1.length rfl] using hk
            simp only [step]
            rw [getD_append_last_eq w2 _ w1.length hlen.symm]
            rcases hg with hand | hor
            · rw [hand] at hk1 ⊢
              change (g.inputs.map (fun i => w1.getD i false)).all id = true at hk1
              change (g.inputs.map (fun i => w2.getD i false)).all id = true
              simp only [List.all_eq_true, List.mem_map, id_eq,
                forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
              intro i hi
              exact hle i (hk1 i hi)
            · rw [hor] at hk1 ⊢
              change (g.inputs.map (fun i => w1.getD i false)).any id = true at hk1
              change (g.inputs.map (fun i => w2.getD i false)).any id = true
              simp only [List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
              obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
              exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
          · have hge : (step w1 g).length ≤ k := by
              simp only [step, List.length_append, List.length_cons, List.length_nil]
              omega
            rw [getD_ge_length _ k hge] at hk
            cases hk

  have append_bit_mono (x y : List Bool) (hxy : x.length = y.length)
      (hval : ∀ k : ℕ, x.getD k false = true → y.getD k false = true)
      (u v : Bool) (huv : u = true → v = true) :
      ∀ k : ℕ, (x ++ [u]).getD k false = true → (y ++ [v]).getD k false = true := by
    intro k hk
    by_cases hlt : k < x.length
    · rw [List.getD_append _ _ _ _ hlt] at hk
      rw [List.getD_append _ _ _ _ (hxy ▸ hlt)]
      exact hval k hk
    · by_cases heq : k = x.length
      · rw [getD_append_last_eq x u k heq.symm] at hk
        rw [getD_append_last_eq y v k (hxy.symm.trans heq.symm)]
        exact huv hk
      · have hge : (x ++ [u]).length ≤ k := by simp; omega
        rw [getD_ge_length _ _ hge] at hk
        cases hk

  have wireMono (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
      ∀ w, (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true := by
    intro w
    apply monotone_foldl_step C.gates (by
      intro q hq
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hao.1 q hq)
      (List.ofFn x) (List.ofFn y) (by simp)
    intro k hk
    by_cases hk' : k < n
    · rw [getD_ofFn x k hk'] at hk
      rw [getD_ofFn y k hk']
      exact hxy ⟨k,hk'⟩ hk
    · have hx : (List.ofFn x).getD k false = false := by
        exact getD_ge_length _ k (by simpa using hk')
      rw [hx] at hk
      cases hk
  have unitBelow (x : Fin n → Bool) (w : Fin n) (hw : x w = true) :
      PEqualNP.SplitCount.unitInput w ≤ x := by
    intro i
    by_cases hi : i = w
    · subst i
      simp [PEqualNP.SplitCount.unitInput, hw]
    · simp [PEqualNP.SplitCount.unitInput, hi]
  have bForced (x : Fin n → Bool) (w : Fin n) (hw : G.Adj v w)
      (hx : x w = true) :
      (C.wires (List.ofFn x)).getD b false = true := by
    have hmono := wireMono (PEqualNP.SplitCount.unitInput w) x
      (unitBelow x w hx) b
    have hone := hneighbors w hw
    exact hmono (by simpa [PEqualNP.BlindGate.wireValue] using hone)
  have noNeighbourWhenBFalse (x : Fin n → Bool)
      (hb0 : (C.wires (List.ofFn x)).getD b false = false) :
      ∀ w : Fin n, G.Adj v w → x w = false := by
    intro w hw
    cases hbit : x w with
    | false => rfl
    | true =>
      have := bForced x w hw hbit
      rw [hb0] at this
      cases this
  have vFalseWhenBFalse (x : Fin n → Bool)
      (hb0 : (C.wires (List.ofFn x)).getD b false = false) : x v = false := by
    cases hv : x v with
    | false => rfl
    | true =>
      have hm := wireMono (PEqualNP.SplitCount.unitInput v) x (unitBelow x v hv) b
        (by simpa [PEqualNP.BlindGate.wireValue] using hunit)
      rw [hb0] at hm
      cases hm
  let addV (x : Fin n → Bool) : Fin n → Bool := fun i => x i || decide (i = v)
  have xBelowAddV (x : Fin n → Bool) (i : Fin n) :
      x i = true → addV x i = true := by
    intro h; simp [addV,h]
  have graphAddV (x : Fin n → Bool)
      (hb0 : (C.wires (List.ofFn x)).getD b false = false) :
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (addV x) := by
    have hv := vFalseWhenBFalse x hb0
    have hn := noNeighbourWhenBFalse x hb0
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    apply Bool.eq_iff_iff.mpr
    simp
    constructor
    · rintro ⟨u,w,huw,hu,hw⟩
      exact ⟨u,w,huw,(xBelowAddV x u hu),(xBelowAddV x w hw)⟩
    · rintro ⟨u,w,huw,hu,hw⟩
      have hnot : u = v → False := by
        intro huv
        subst u
        have : addV x w = true := hw
        have hw' : x w = false := hn w huw
        have hne : w ≠ v := fun h => (G.ne_of_adj huw) h.symm
        simp [addV,hw',hne] at this
      have hnot' : w = v → False := by
        intro hwv
        subst w
        have : addV x u = true := hu
        have hu' : x u = false := hn u huw.symm
        have hne : u ≠ v := fun h => (G.ne_of_adj huw) h
        simp [addV,hu',hne] at this
      refine ⟨u,w,huw,?_,?_⟩
      · by_contra he
        have : u = v := by
          by_contra h
          simp [addV,h,he] at hu
        exact hnot this
      · by_contra he
        have : w = v := by
          by_contra h
          simp [addV,h,he] at hw
        exact hnot' this
  have bTrueAtAddV (x : Fin n → Bool) : (C.wires (List.ofFn (addV x))).getD b false = true := by
    have hmono := wireMono (PEqualNP.SplitCount.unitInput v) (addV x)
      (unitBelow (addV x) v (by simp [addV])) b
    exact hmono (by simpa [PEqualNP.BlindGate.wireValue] using hunit)
  have wires_gate_ofFn (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hj : C.gates[j]? = some g) :
      (C.wires (List.ofFn x)).getD (n + j) false =
        g.op.eval (g.inputs.map fun i => if i < n+j then (C.wires (List.ofFn x)).getD i false else false) := by
    have h := foldl_step_gate C.gates (List.ofFn x) j g hj
    simpa only [List.length_ofFn, ← wires_eq_foldl] using h
  have gateEqA (x : Fin n → Bool)
      (hb : (C.wires (List.ofFn x)).getD b false = true) :
      (C.wires (List.ofFn x)).getD (n+g) false =
        (C.wires (List.ofFn x)).getD a false := by
    have hg' : C.gates[g]? = some (C.gates[g]'hg) := List.getElem?_eq_getElem hg
    rw [wires_gate_ofFn C x g _ hg']
    have hread := hao.2.1 g hg
    have hgate : (C.gates[g]'hg).op = GateOp.and := by
      simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg] using hop
    have hinputs : (C.gates[g]'hg).inputs = [a,b] ∨ (C.gates[g]'hg).inputs = [b,a] := by
      simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg] using hinputs
    rcases hinputs with h | h
    · rw [h]
      have ha : a < n+g := hread a (by
        simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg,h] using (show a ∈ [a,b] by simp))
      have hb' : b < n+g := hread b (by
        simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg,h] using (show b ∈ [a,b] by simp))
      simp only [List.map_cons,List.map_nil,if_pos ha,if_pos hb',hgate,GateOp.eval,
        List.all_cons,List.all_nil, Bool.and_true]
      change ((C.wires (List.ofFn x)).getD a false &&
        (C.wires (List.ofFn x)).getD b false) = (C.wires (List.ofFn x)).getD a false
      rw [hb]
      simp
    · rw [h]
      have ha : a < n+g := hread a (by
        simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg,h] using (show a ∈ [b,a] by simp))
      have hb' : b < n+g := hread b (by
        simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg,h] using (show b ∈ [b,a] by simp))
      simp only [List.map_cons,List.map_nil,if_pos ha,if_pos hb',hgate,GateOp.eval,
        List.all_cons,List.all_nil, Bool.and_true]
      change ((C.wires (List.ofFn x)).getD b false &&
        (C.wires (List.ofFn x)).getD a false) = (C.wires (List.ofFn x)).getD a false
      rw [hb]
      simp
  have gateLeA (x : Fin n → Bool) :
      (C.wires (List.ofFn x)).getD (n+g) false = true →
        (C.wires (List.ofFn x)).getD a false = true := by
    have hg' : C.gates[g]? = some (C.gates[g]'hg) := List.getElem?_eq_getElem hg
    rw [wires_gate_ofFn C x g _ hg']
    have hread := hao.2.1 g hg
    have hin : (C.gates[g]'hg).inputs = [a,b] ∨ (C.gates[g]'hg).inputs = [b,a] := by
      simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg] using hinputs
    have hgate : (C.gates[g]'hg).op = GateOp.and := by
      simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg] using hop
    have hmemA : a ∈ (C.gates[g]'hg).inputs := by
      rcases hin with h | h <;> rw [h] <;> simp
    have hmemB : b ∈ (C.gates[g]'hg).inputs := by
      rcases hin with h | h <;> rw [h] <;> simp
    have ha : a < n+g := hread a (by
      simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg] using hmemA)
    have hb' : b < n+g := hread b (by
      simpa only [NestedCover.gateAt,List.getD_eq_getElem _ _ hg] using hmemB)
    rcases hin with h | h
    · rw [h]
      simp only [List.map_cons,List.map_nil,if_pos ha,if_pos hb',hgate,GateOp.eval,
        List.all_cons,List.all_nil,Bool.and_true]
      intro hval
      exact (Bool.and_eq_true_iff.mp hval).1
    · rw [h]
      simp only [List.map_cons,List.map_nil,if_pos ha,if_pos hb',hgate,GateOp.eval,
        List.all_cons,List.all_nil,Bool.and_true]
      intro hval
      exact (Bool.and_eq_true_iff.mp hval).2
  have evalInputsMono (op : GateOp) (ins : List ℕ) (u w : ℕ → Bool)
      (hop : op = GateOp.and ∨ op = GateOp.or)
      (hval : ∀ i ∈ ins, u i = true → w i = true) :
      op.eval (ins.map u) = true → op.eval (ins.map w) = true := by
    rcases hop with hand | hor
    · rw [hand]
      intro he
      have hall : ∀ z ∈ ins.map u, z = true := by
        simpa [GateOp.eval] using he
      apply List.all_eq_true.mpr
      intro z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
      exact hval i hi (hall (u i) (List.mem_map.mpr ⟨i,hi,rfl⟩))
    · rw [hor]
      intro he
      obtain ⟨z,hz,hztrue⟩ := List.any_eq_true.mp he
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
      apply List.any_eq_true.mpr
      exact ⟨w i,List.mem_map.mpr ⟨i,hi,rfl⟩,hval i hi hztrue⟩
  have aBelowGate : a < n+g := by
    have hread := hao.2.1 g hg
    have hmem : a ∈ (NestedCover.gateAt C g).inputs := by
      rcases hinputs with h | h
      · rw [h]; simp
      · rw [h]; simp
    exact hread a hmem
  let remapIndex (i : ℕ) : ℕ := if i = n+g then a else i
  let remapGate (q : Gate) : Gate := { q with inputs := q.inputs.map remapIndex }
  let remapGates := C.gates.map remapGate
  let dPrefix (x : Fin n → Bool) (j : ℕ) :=
    (remapGates.take j).foldl step (List.ofFn x)
  let cPrefix (y : Fin n → Bool) (j : ℕ) :=
    (C.gates.take j).foldl step (List.ofFn y)
  have prefixStable (y : Fin n → Bool) (j : ℕ) (hj : j ≤ C.gates.length)
      (k : ℕ) (hk : k < n+j) :
      (cPrefix y j).getD k false = (C.wires (List.ofFn y)).getD k false := by
    dsimp [cPrefix]
    have hlen : ((C.gates.take j).foldl step (List.ofFn y)).length = n+j := by
      rw [foldl_step_len]
      simp [List.length_take]
      omega
    have hsplit : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
    calc
      ((C.gates.take j).foldl step (List.ofFn y)).getD k false =
          ((C.gates.drop j).foldl step ((C.gates.take j).foldl step (List.ofFn y))).getD k false := by
            rw [← foldl_step_getD_lt (C.gates.drop j) _ k (by rw [hlen]; exact hk)]
      _ = (C.gates.foldl step (List.ofFn y)).getD k false := by
        rw [← List.foldl_append, hsplit]
      _ = (C.wires (List.ofFn y)).getD k false := by rw [← wires_eq_foldl]
  have prefixForward (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
      (C.wires (List.ofFn y)).getD (n+g) false = (C.wires (List.ofFn y)).getD a false →
      ∀ j ≤ C.gates.length, ∀ k < n+j,
        (dPrefix x j).getD k false = true → (cPrefix y j).getD k false = true := by
    intro hgateEq
    intro j
    induction j with
    | zero =>
      intro hj k hk hbit
      change (List.ofFn x).getD k false = true at hbit
      change (List.ofFn y).getD k false = true
      have hkin : k < n := hk
      have hbit' : x ⟨k,hkin⟩ = true := by rw [getD_ofFn x k hkin] at hbit; exact hbit
      have hout := hxy ⟨k,hkin⟩ hbit'
      rw [getD_ofFn y k hkin]
      exact hout
    | succ j ih =>
      intro hj k hk hbit
      have hjlt : j < C.gates.length := by omega
      have hremaplt : j < remapGates.length := by simpa [remapGates] using hjlt
      have hdTake := List.take_succ_eq_append_getElem (l := remapGates) (i := j) (by
        exact hremaplt)
      have hcTake := List.take_succ_eq_append_getElem (l := C.gates) (i := j) hjlt
      have hdgate : remapGates[j]'hremaplt = remapGate (C.gates[j]'hjlt) := by
        simp [remapGates]
      dsimp only [dPrefix,cPrefix] at hbit ⊢
      rw [hdTake] at hbit
      rw [hcTake] at ⊢
      rw [List.foldl_append] at hbit ⊢
      rw [hdgate] at hbit
      simp only [List.foldl_cons,List.foldl_nil,step] at hbit ⊢
      let dw := (remapGates.take j).foldl step (List.ofFn x)
      let cw := (C.gates.take j).foldl step (List.ofFn y)
      have hlenD : dw.length = n+j := by
        dsimp [dw]
        rw [foldl_step_len]
        simp [remapGates,List.length_take]
        omega
      have hlenC : cw.length = n+j := by
        dsimp [cw]
        rw [foldl_step_len]
        simp [List.length_take]
        omega
      have hboundGate : ∀ i ∈ C.gates[j].inputs, i < n+j := by
        intro i hi
        have hr := hao.2.1 j hjlt
        apply hr i
        simpa only [NestedCover.gateAt,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hjlt,Option.getD_some] using hi
      have hopGate : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
        have hmem := List.getElem_mem hjlt
        simpa using hao.1 C.gates[j] hmem
      have hinRel : ∀ i ∈ C.gates[j].inputs,
          dw.getD (remapIndex i) false = true → cw.getD i false = true := by
        intro i hi htrue
        have hibound := hboundGate i hi
        by_cases hspecial : i = n+g
        · subst i
          have hbelow : a < n+j := by omega
          have hprior := ih (by omega) a hbelow (by simpa [remapIndex] using htrue)
          have heq : cw.getD (n+g) false = cw.getD a false := by
            rw [prefixStable y j (by omega) (n+g) (by omega), hgateEq,
              ← prefixStable y j (by omega) a hbelow]
          rw [heq]
          exact hprior
        · have hprior := ih (by omega) i hibound
          apply hprior
          simpa [remapIndex,hspecial] using htrue
      have hEval := evalInputsMono (C.gates[j].op) (C.gates[j].inputs)
        (fun i => dw.getD (remapIndex i) false) (fun i => cw.getD i false)
        hopGate hinRel
      by_cases hklt : k < n+j
      · have hbit' : dw.getD k false = true := by
          rw [getD_append_left_lt dw _ k (by rw [hlenD]; exact hklt)] at hbit
          exact hbit
        have hout := ih (by omega) k hklt hbit'
        rw [getD_append_left_lt cw _ k (by rw [hlenC]; exact hklt)]
        exact hout
      · have heq : k = n+j := by omega
        subst k
        have hDout : (C.gates[j].op).eval
            (C.gates[j].inputs.map fun i => dw.getD (remapIndex i) false) = true := by
          have happend : (dw ++ [(C.gates[j].op).eval
              (C.gates[j].inputs.map fun i => dw.getD (remapIndex i) false)]).getD (n+j) false = true := by
            simpa [dw,remapGate,step,hdgate,Function.comp_def] using hbit
          rw [← hlenD,getD_append_self] at happend
          exact happend
        have hCout : (C.gates[j].op).eval
            (C.gates[j].inputs.map fun i => cw.getD i false) = true := hEval hDout
        change (cw ++ [(C.gates[j].op).eval
          (C.gates[j].inputs.map fun i => cw.getD i false)]).getD (n+j) false = true
        rw [← hlenC,getD_append_self]
        exact hCout
  have prefixBackward (x : Fin n → Bool) :
      ∀ j ≤ C.gates.length, ∀ k < n+j,
        (cPrefix x j).getD k false = true → (dPrefix x j).getD k false = true := by
    intro j
    induction j with
    | zero =>
      intro hj k hk hbit
      change (List.ofFn x).getD k false = true at hbit
      change (List.ofFn x).getD k false = true
      exact hbit
    | succ j ih =>
      intro hj k hk hbit
      have hjlt : j < C.gates.length := by omega
      have hremaplt : j < remapGates.length := by simpa [remapGates] using hjlt
      have hdTake := List.take_succ_eq_append_getElem (l := remapGates) (i := j) hremaplt
      have hcTake := List.take_succ_eq_append_getElem (l := C.gates) (i := j) hjlt
      have hdgate : remapGates[j]'hremaplt = remapGate (C.gates[j]'hjlt) := by simp [remapGates]
      dsimp only [dPrefix,cPrefix] at hbit ⊢
      rw [hdTake] at ⊢
      rw [hcTake] at hbit
      rw [List.foldl_append] at hbit ⊢
      rw [hdgate] at ⊢
      simp only [List.foldl_cons,List.foldl_nil,step] at hbit ⊢
      let dw := (remapGates.take j).foldl step (List.ofFn x)
      let cw := (C.gates.take j).foldl step (List.ofFn x)
      have hlenD : dw.length = n+j := by
        dsimp [dw]
        rw [foldl_step_len]
        simp [remapGates,List.length_take]
        omega
      have hlenC : cw.length = n+j := by
        dsimp [cw]
        rw [foldl_step_len]
        simp [List.length_take]
        omega
      have hboundGate : ∀ i ∈ C.gates[j].inputs, i < n+j := by
        intro i hi
        have hr := hao.2.1 j hjlt
        apply hr i
        simpa only [NestedCover.gateAt,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hjlt,Option.getD_some] using hi
      have hopGate : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
        have hmem := List.getElem_mem hjlt
        simpa using hao.1 C.gates[j] hmem
      have hinRel : ∀ i ∈ C.gates[j].inputs,
          cw.getD i false = true → dw.getD (remapIndex i) false = true := by
        intro i hi htrue
        have hibound := hboundGate i hi
        by_cases hspecial : i = n+g
        · subst i
          have hbelow : a < n+j := by omega
          have hfull : (C.wires (List.ofFn x)).getD (n+g) false = true := by
            rw [← prefixStable x j (by omega) (n+g) (by omega)]
            exact htrue
          have hfullA := gateLeA x hfull
          have hpreA : cw.getD a false = true := by
            rw [prefixStable x j (by omega) a hbelow]
            exact hfullA
          have hprior := ih (by omega) a hbelow hpreA
          simpa [remapIndex] using hprior
        · have hprior := ih (by omega) i hibound htrue
          simpa [remapIndex,hspecial] using hprior
      have hEval := evalInputsMono (C.gates[j].op) (C.gates[j].inputs)
        (fun i => cw.getD i false) (fun i => dw.getD (remapIndex i) false)
        hopGate hinRel
      by_cases hklt : k < n+j
      · have hbit' : cw.getD k false = true := by
          rw [getD_append_left_lt cw _ k (by rw [hlenC]; exact hklt)] at hbit
          exact hbit
        have hout := ih (by omega) k hklt hbit'
        rw [getD_append_left_lt dw _ k (by rw [hlenD]; exact hklt)]
        exact hout
      · have heq : k = n+j := by omega
        subst k
        have hCout : (C.gates[j].op).eval
            (C.gates[j].inputs.map fun i => cw.getD i false) = true := by
          have happend : (cw ++ [(C.gates[j].op).eval
              (C.gates[j].inputs.map fun i => cw.getD i false)]).getD (n+j) false = true := by
            simpa [cw,step] using hbit
          rw [← hlenC,getD_append_self] at happend
          exact happend
        have hDout : (C.gates[j].op).eval
            (C.gates[j].inputs.map fun i => dw.getD (remapIndex i) false) = true := hEval hCout
        have happendD : (dw ++ [(C.gates[j].op).eval
            (C.gates[j].inputs.map fun i => dw.getD (remapIndex i) false)]).getD (n+j) false = true := by
          rw [← hlenD,getD_append_self]
          exact hDout
        simpa [dw,remapGate,step,hdgate,Function.comp_def] using happendD
  let D : Circuit := { gates := remapGates, output := C.output }
  have wiresForward (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
      (heq : (C.wires (List.ofFn y)).getD (n+g) false =
        (C.wires (List.ofFn y)).getD a false) :
      ∀ k, (D.wires (List.ofFn x)).getD k false = true →
        (C.wires (List.ofFn y)).getD k false = true := by
    intro k hk
    have hlenC : (C.wires (List.ofFn y)).length = n+C.gates.length := by
      rw [wires_eq_foldl,foldl_step_len]
      simp
    have hlenD : (D.wires (List.ofFn x)).length = n+C.gates.length := by
      rw [wires_eq_foldl,foldl_step_len]
      simp [D,remapGates]
    by_cases hbound : k < n+C.gates.length
    · have hdFull : dPrefix x C.gates.length = D.wires (List.ofFn x) := by
        have ht : remapGates.take C.gates.length = remapGates :=
          List.take_of_length_le (by simp [remapGates])
        simp only [dPrefix,ht,D,Circuit.wires]
        rfl
      have hcFull : cPrefix y C.gates.length = C.wires (List.ofFn y) := by
        have ht : C.gates.take C.gates.length = C.gates := List.take_length
        simp only [cPrefix,ht,Circuit.wires]
        rfl
      have h := prefixForward x y hxy heq C.gates.length (le_refl _) k hbound
      rw [← hdFull] at hk
      rw [hcFull] at h
      exact h hk
    · have hfalse : (D.wires (List.ofFn x)).getD k false = false :=
        getD_ge_len _ k (by rw [hlenD]; omega)
      rw [hfalse] at hk
      cases hk
  have wiresBackward (x : Fin n → Bool) :
      ∀ k, (C.wires (List.ofFn x)).getD k false = true →
        (D.wires (List.ofFn x)).getD k false = true := by
    intro k hk
    have hlenC : (C.wires (List.ofFn x)).length = n+C.gates.length := by
      rw [wires_eq_foldl,foldl_step_len]
      simp
    have hlenD : (D.wires (List.ofFn x)).length = n+C.gates.length := by
      rw [wires_eq_foldl,foldl_step_len]
      simp [D,remapGates]
    by_cases hbound : k < n+C.gates.length
    · have hdFull : dPrefix x C.gates.length = D.wires (List.ofFn x) := by
        have ht : remapGates.take C.gates.length = remapGates :=
          List.take_of_length_le (by simp [remapGates])
        simp only [dPrefix,ht,D,Circuit.wires]
        rfl
      have hcFull : cPrefix x C.gates.length = C.wires (List.ofFn x) := by
        have ht : C.gates.take C.gates.length = C.gates := List.take_length
        simp only [cPrefix,ht,Circuit.wires]
        rfl
      have h := prefixBackward x C.gates.length (le_refl _) k hbound
      rw [← hcFull] at hk
      rw [hdFull] at h
      exact h hk
    · have hfalse : (C.wires (List.ofFn x)).getD k false = false :=
        getD_ge_len _ k (by rw [hlenC]; omega)
      rw [hfalse] at hk
      cases hk
  have transport (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
      (heq : (C.wires (List.ofFn y)).getD (n+g) false =
        (C.wires (List.ofFn y)).getD a false)
      (hgraph : NestedCover.graphFun G ∅ y = NestedCover.graphFun G ∅ x) :
      circuitFun n D x = NestedCover.graphFun G ∅ x := by
    have hCx := congrArg (fun F : (Fin n → Bool) → Bool => F x) hfun
    have hCy := congrArg (fun F : (Fin n → Bool) → Bool => F y) hfun
    have hforward := wiresForward x y hxy heq
    have hbackward := wiresBackward x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hDx
      have hCyOut : C.eval (List.ofFn y) = true := by
        apply hforward C.output
        simpa [Circuit.eval,circuitFun,D] using hDx
      have hCyEval : C.eval (List.ofFn y) = NestedCover.graphFun G ∅ y := by
        simpa [circuitFun] using hCy
      rw [hCyEval] at hCyOut
      rw [hgraph] at hCyOut
      exact hCyOut
    · intro hFx
      have hCxEval : C.eval (List.ofFn x) = NestedCover.graphFun G ∅ x := by
        simpa [circuitFun] using hCx
      have hCxOut : C.eval (List.ofFn x) = true := by
        rw [hCxEval]
        exact hFx
      have hDOut := hbackward C.output (by simpa [Circuit.eval] using hCxOut)
      simpa [circuitFun,Circuit.eval,D] using hDOut
  funext x
  change circuitFun n D x = NestedCover.graphFun G ∅ x
  cases hb : (C.wires (List.ofFn x)).getD b false with
  | true =>
      have heq := gateEqA x hb
      have h := transport x x (fun _ hi => hi) heq rfl
      simpa [D,remapGates,remapGate,remapIndex] using h
  | false =>
      let y := addV x
      have hxy : ∀ i, x i = true → y i = true := by
        intro i hi
        exact xBelowAddV x i hi
      have heq := gateEqA y (bTrueAtAddV x)
      have hgraph : NestedCover.graphFun G ∅ y = NestedCover.graphFun G ∅ x := by
        simpa [y] using (graphAddV x hb).symm
      exact transport x y hxy heq hgraph
