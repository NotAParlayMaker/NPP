import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4295_aux

namespace status

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

theorem belowOutput_iff_of_false_case
    (n : ℕ) (C C' : Circuit) (h w w' : ℕ)
    (hSub : WireBelowOutput n C h)
    (hEval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = C'.eval (List.ofFn x))
    (hNewTrue : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD h false = true → C'.eval (List.ofFn x) = true)
    (hWire : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD h false = false →
      (C.wires (List.ofFn x)).getD w false =
        (C'.wires (List.ofFn x)).getD w' false) :
    WireBelowOutput n C w ↔ WireBelowOutput n C' w' := by
  unfold WireBelowOutput
  constructor
  · intro hOld x hwNew
    by_cases hh : (C.wires (List.ofFn x)).getD h false = true
    · exact hNewTrue x hh
    · have hf : (C.wires (List.ofFn x)).getD h false = false := Bool.eq_false_of_not_eq_true hh
      have hwOld : (C.wires (List.ofFn x)).getD w false = true := by
        rw [hWire x hf]
        exact hwNew
      have hout := hOld x hwOld
      rw [hEval x] at hout
      exact hout
  · intro hNew x hwOld
    by_cases hh : (C.wires (List.ofFn x)).getD h false = true
    · exact hSub x hh
    · have hf : (C.wires (List.ofFn x)).getD h false = false := Bool.eq_false_of_not_eq_true hh
      have hwNew : (C'.wires (List.ofFn x)).getD w' false = true := by
        rw [← hWire x hf]
        exact hwOld
      have hout := hNew x hwNew
      rw [← hEval x] at hout
      exact hout

end status

namespace ao2

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def renameGate (n m p : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

private theorem eraseRedirect_lt {n m p len i : ℕ}
    (hm : m < len) (hp : p < n + m) (hi : i < n + len) :
    eraseRedirect n m p i < n + len - 1 := by
  unfold eraseRedirect
  by_cases h : i = n + m
  · simp [h]
    omega
  · by_cases h' : n + m < i
    · simp [h, h']
      omega
    · simp [h, h']
      omega

private theorem eraseRedirect_lt_gate {n m p j i : ℕ}
    (hmj : m ≤ j) (hp : p < n + m) (hi : i < n + (j + 1)) :
    eraseRedirect n m p i < n + j := by
  unfold eraseRedirect
  by_cases h : i = n + m
  · simp [h]
    omega
  · by_cases h' : n + m < i
    · simp [h, h']
      omega
    · simp [h, h']
      omega

theorem eraseRedirect_preserves_gate_index_test {n m p w len : ℕ}
    (hw : w < n + len) (hd : w ≠ n + m) :
    (n ≤ w ↔ n ≤ eraseRedirect n m p w) := by
  unfold eraseRedirect
  by_cases hgt : n + m < w
  · have hw' : n ≤ w - 1 := by omega
    simp [hd, hgt, hw']
    omega
  · have hlt : w < n + m := by omega
    simp [hd, hgt]

theorem eraseGate_len {n m p : ℕ} {C : Circuit} (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  simp [eraseGate, if_pos hm, List.length_append, List.length_take,
    List.length_drop, Nat.min_eq_left hm.le]
  omega

private theorem eraseGate_get_lt {n m p : ℕ} {C : Circuit} {j : ℕ}
    (hm : m < C.gates.length) (hj : j < m) :
    (eraseGate n C m p).gates[j]? = C.gates[j]? := by
  simp [eraseGate, if_pos hm, List.getElem?_append_left,
    List.length_take, Nat.min_eq_left hm.le, List.getElem?_take, hj]

private theorem eraseGate_get_ge {n m p : ℕ} {C : Circuit} {j : ℕ}
    (hm : m < C.gates.length) (hj : m ≤ j) (hjlen : j + 1 < C.gates.length) :
    (eraseGate n C m p).gates[j]? = (C.gates[j + 1]?).map (renameGate n m p) := by
  rw [eraseGate, if_pos hm]
  change (C.gates.take m ++
      (C.gates.drop (m + 1)).map (renameGate n m p))[j]? =
    (C.gates[j + 1]?).map (renameGate n m p)
  rw [List.getElem?_append_right (by
    simp [List.length_take, Nat.min_eq_left hm.le]
    omega)]
  have hidx : j - (C.gates.take m).length = j - m := by
    simp [List.length_take, Nat.min_eq_left hm.le]
  rw [hidx]
  simp only [List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

private theorem eraseGate_gateAt_lt {n m p : ℕ} {C : Circuit} {j : ℕ}
    (hm : m < C.gates.length) (hj : j < m) :
    PEqualNP.MetaComplexity.NestedCover.gateAt (eraseGate n C m p) j =
      PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, eraseGate_get_lt hm hj]

private theorem eraseGate_gateAt_ge {n m p : ℕ} {C : Circuit} {j : ℕ}
    (hm : m < C.gates.length) (hj : m ≤ j) (hjlen : j + 1 < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt (eraseGate n C m p) j =
      renameGate n m p (PEqualNP.MetaComplexity.NestedCover.gateAt C (j + 1)) := by
  have hopt := eraseGate_get_ge (n := n) (p := p) hm hj hjlen
  have hgate : C.gates[j + 1]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C (j + 1)) := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hjlen]
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  simp only [List.getD_eq_getElem?_getD, hopt, hgate, Option.map_some, Option.getD_some]

private theorem gateAt_mem {n : ℕ} (C : Circuit) {j : ℕ}
    (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
  apply List.mem_iff_getElem?.2
  refine ⟨j, ?_⟩
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]

private theorem gateAt_eq_of_get {C : Circuit} {j : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]

theorem eraseGate_out_lt {n m p : ℕ} {C : Circuit}
    (hm : m < C.gates.length) (hp : p < n + m)
    (ho : C.output < n + C.gates.length) :
    (eraseGate n C m p).output < n + C.gates.length - 1 := by
  simp only [eraseGate, if_pos hm]
  exact eraseRedirect_lt hm hp ho

theorem liftAt_len {n m p h : ℕ} {C : Circuit}
    (hm : m < C.gates.length) : (liftAt n C m p h).gates.length = C.gates.length := by
  simp [liftAt, eraseGate_len hm]
  omega

theorem liftAt_output_valid {n m p h : ℕ} {C : Circuit}
    (hm : m < C.gates.length) :
    (liftAt n C m p h).output < n + (liftAt n C m p h).gates.length := by
  simp [liftAt, eraseGate_len hm]

private theorem eraseGate_isAO2 {n m p : ℕ} {C : Circuit}
    (hC : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m) :
    IsAO2 n (eraseGate n C m p) := by
  rcases hC with ⟨hAO, hRB, hlen⟩
  have hlist : (eraseGate n C m p).gates =
      C.gates.take m ++ (C.gates.drop (m + 1)).map (renameGate n m p) := by
    simp only [eraseGate, if_pos hm]
    rfl
  have hlenE : (eraseGate n C m p).gates.length = C.gates.length - 1 := eraseGate_len hm
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [hlist] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hAO g (List.mem_of_mem_take hg)
    · rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
      have h0 := hAO g0 (List.mem_of_mem_drop hg0)
      simpa [renameGate] using h0
  · intro j hj i hi
    by_cases hjlt : j < m
    · have hjE : j < (eraseGate n C m p).gates.length := by rw [hlenE]; omega
      have hg : gateAt (eraseGate n C m p) j = gateAt C j :=
        eraseGate_gateAt_lt hm hjlt
      have hi0 : i ∈ (gateAt C j).inputs := by simpa [hg] using hi
      have hjC : j < C.gates.length := by omega
      have hb := hRB j hjC i hi0
      have hidx : eraseRedirect n m p i = i := by
        unfold eraseRedirect
        have hlt : i < n + m := by omega
        simp [ne_of_lt hlt, Nat.not_lt.mpr (Nat.le_of_lt hlt)]
      simpa [hidx] using hb
    · have hmj : m ≤ j := by omega
      have hjC : j + 1 < C.gates.length := by rw [hlenE] at hj; omega
      have hg := eraseGate_gateAt_ge (n := n) (p := p) hm hmj hjC
      have hiMap : i ∈ (gateAt C (j + 1)).inputs.map (eraseRedirect n m p) := by
        rw [hg] at hi
        simpa [renameGate] using hi
      rcases List.mem_map.mp hiMap with ⟨i0, hi0, rfl⟩
      have hb := hRB (j + 1) hjC i0 hi0
      exact eraseRedirect_lt_gate hmj hp hb
  · intro g hg
    rw [hlist] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hlen g (List.mem_of_mem_take hg)
    · rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
      have h0 := hlen g0 (List.mem_of_mem_drop hg0)
      simpa [renameGate] using h0

theorem liftAt_preserves_IsAO2 {n m p h : ℕ} {C : Circuit}
    (hC : IsAO2 n C)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hout : C.output < n + C.gates.length) :
    IsAO2 n (liftAt n C m p h) := by
  let E := eraseGate n C m p
  have hE : IsAO2 n E := by
    simpa [E] using eraseGate_isAO2 hC hm hp
  have hE_len : E.gates.length = C.gates.length - 1 := by
    simp [E, eraseGate_len hm]
  have hE_out : E.output < n + E.gates.length := by
    change (eraseGate n C m p).output < n + (eraseGate n C m p).gates.length
    have h := eraseGate_out_lt hm hp hout
    rw [eraseGate_len hm]
    omega
  rcases hE with ⟨hEAO, hERB, hElen⟩
  change AndOrOnly (liftAt n C m p h) ∧
    ReadsBack n (liftAt n C m p h) ∧
    (∀ g ∈ (liftAt n C m p h).gates, g.inputs.length = 2)
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [liftAt, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact hEAO g hg
    · rcases hg with rfl
      exact Or.inr rfl
  · intro j hj i hi
    have hjBound : j < E.gates.length + 1 := by
      simpa [liftAt, E, List.length_append, List.length_singleton] using hj
    by_cases hjE : j < E.gates.length
    · have hiE : i ∈ (gateAt E j).inputs := by
        have hgateE : gateAt (liftAt n C m p h) j = gateAt E j := by
          simp only [gateAt, liftAt, E, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hjE]
        rw [hgateE] at hi
        exact hi
      exact hERB j hjE i hiE
    · have hjeq : j = E.gates.length := by omega
      subst j
      have hlastGate : gateAt (liftAt n C m p h) E.gates.length =
          ⟨GateOp.or, [E.output, h]⟩ := by
        simp [gateAt, liftAt, E, List.getD_eq_getElem?_getD]
      have hiE : i ∈ [E.output, h] := by
        rw [hlastGate] at hi
        simpa using hi
      simp at hiE
      rcases hiE with rfl | rfl
      · exact hE_out
      · have hmle : m ≤ E.gates.length := by rw [hE_len]; omega
        omega
  · intro g hg
    simp only [liftAt, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact hElen g hg
    · rcases hg with rfl
      rfl

def erasedGateIndex (m j : ℕ) : ℕ := if j < m then j else j - 1

theorem liftAt_gate_mapping {n m p h j : ℕ} {C : Circuit}
    (hC : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hj : j < C.gates.length) (hjm : j ≠ m) :
    (liftAt n C m p h).gates[erasedGateIndex m j]? =
      (C.gates[j]?).map (renameGate n m p) := by
  have hlenE : (eraseGate n C m p).gates.length = C.gates.length - 1 :=
    eraseGate_len hm
  have hC_rb : ReadsBack n C := hC.2.1
  by_cases hjm' : j < m
  · have hjE : j < (eraseGate n C m p).gates.length := by rw [hlenE]; omega
    have hlift : (liftAt n C m p h).gates[j]? = (eraseGate n C m p).gates[j]? := by
      simp only [liftAt, List.getElem?_append_left hjE]
    have hE := eraseGate_get_lt (n := n) (p := p) hm hjm'
    have hmapSelf : (C.gates[j]?).map (renameGate n m p) = C.gates[j]? := by
      have hgate : C.gates[j]? = some (gateAt C j) := by
        simp [gateAt, hj]
      rw [hgate]
      have hinputs : (gateAt C j).inputs.map (eraseRedirect n m p) =
          (gateAt C j).inputs := by
        calc
          (gateAt C j).inputs.map (eraseRedirect n m p) =
              (gateAt C j).inputs.map id := by
            apply List.map_congr_left
            intro i hi
            have hbound := hC_rb j hj i hi
            have hlt : i < n + m := by omega
            unfold eraseRedirect
            simp [ne_of_lt hlt, Nat.not_lt.mpr (Nat.le_of_lt hlt)]
          _ = (gateAt C j).inputs := by simp
      cases hg : gateAt C j with
      | mk op inputs =>
        rw [hg] at hinputs
        simp [renameGate, hinputs]
    simp [erasedGateIndex, hjm', hlift, hE, hmapSelf]
  · have hmj : m < j := by omega
    let k := j - 1
    have hk : m ≤ k := by dsimp [k]; omega
    have hkE : k < (eraseGate n C m p).gates.length := by
      rw [hlenE]
      dsimp [k]
      omega
    have hlift : (liftAt n C m p h).gates[k]? = (eraseGate n C m p).gates[k]? := by
      simp only [liftAt, List.getElem?_append_left hkE]
    have hklen : k + 1 < C.gates.length := by dsimp [k]; omega
    have hE := eraseGate_get_ge (n := n) (p := p) hm hk hklen
    have hkj : k + 1 = j := by dsimp [k]; omega
    simpa [erasedGateIndex, hjm', k, hkj] using hlift.trans hE

end ao2

open PEqualNP.CircuitLowerBounds
open PEqualNP.CircuitMoves
open PEqualNP.TopForm

namespace eval

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl stepW w

private def redir (n m p i : ℕ) : ℕ := PEqualNP.CircuitMoves.eraseRedirect n m p i

private def changeGate (n m p : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redir n m p)⟩

private theorem runW_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    runW (g :: gs) w = runW gs (stepW w g) := by
  simp [runW, stepW]

private theorem runW_append (gs hs : List Gate) (w : List Bool) :
    runW (gs ++ hs) w = runW hs (runW gs w) := by
  simp [runW, List.foldl_append]

theorem runW_length (gs : List Gate) (w : List Bool) :
    (runW gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runW]
  | cons g gs ih =>
      rw [runW_cons]
      rw [ih]
      simp [stepW, List.length_append]
      omega

private theorem runW_getD (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (runW gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp [runW]
  | cons g gs ih =>
      rw [runW_cons]
      have hi' : i < (stepW w g).length := by simp [stepW, List.length_append]; omega
      rw [ih (stepW w g) hi']
      exact List.getD_append _ _ _ _ hi

private theorem runTailRel (n m p k : ℕ) (hp : p < n + m)
    (gs : List Gate) (newW oldW : List Bool)
    (hnew : newW.length = n + m + k)
    (hold : oldW.length = n + m + k + 1)
    (hrel : ∀ q < n + m + k + 1,
      newW.getD (redir n m p q) false = oldW.getD q false)
    (hread : ∀ j g, gs[j]? = some g → ∀ q ∈ g.inputs,
      q < n + m + k + j + 1) :
    ∀ q < n + m + k + gs.length + 1,
      (runW (gs.map (changeGate n m p)) newW).getD (redir n m p q) false =
        (runW gs oldW).getD q false := by
  induction gs generalizing k newW oldW with
  | nil =>
      intro q hq
      simpa [runW] using hrel q hq
  | cons g gs ih =>
      have hread0 : ∀ q ∈ g.inputs, q < n + m + k + 1 := by
        intro q hq
        exact hread 0 g (by simp) q hq
      have hbits : (g.inputs.map fun q => newW.getD (redir n m p q) false) =
          (g.inputs.map fun q => oldW.getD q false) := by
        apply List.map_congr_left
        intro q hq
        exact hrel q (hread0 q hq)
      let newW' := stepW newW (changeGate n m p g)
      let oldW' := stepW oldW g
      have hnew' : newW'.length = n + m + (k + 1) := by
        simp [newW', stepW, hnew]
        omega
      have hold' : oldW'.length = n + m + (k + 1) + 1 := by
        simp [oldW', stepW, hold]
        omega
      have hval : (changeGate n m p g).op.eval
          ((changeGate n m p g).inputs.map fun q => newW.getD q false) =
          g.op.eval (g.inputs.map fun q => oldW.getD q false) := by
        simpa [changeGate, Function.comp_def] using congrArg g.op.eval hbits
      have hrel' : ∀ q < n + m + (k + 1) + 1,
          newW'.getD (redir n m p q) false = oldW'.getD q false := by
        intro q hq
        have htop : q = n + m + k + 1 ∨ q < n + m + k + 1 := by omega
        rcases htop with heq | hlt
        · subst q
          have hred : redir n m p (n + m + k + 1) = n + m + k := by
            simp [redir, PEqualNP.CircuitMoves.eraseRedirect]
            omega
          rw [hred]
          have hleft : newW'.getD (n + m + k) false =
              (changeGate n m p g).op.eval
                ((changeGate n m p g).inputs.map fun q => newW.getD q false) := by
            simp [newW', oldW', stepW, hnew, List.getD_append_right]
          have hright : oldW'.getD (n + m + k + 1) false =
              g.op.eval (g.inputs.map fun q => oldW.getD q false) := by
            simp [newW', oldW', stepW, hold, List.getD_append_right]
          rw [hleft, hright]
          exact hval
        · have hredlt : redir n m p q < newW.length := by
            rw [hnew]
            unfold redir PEqualNP.CircuitMoves.eraseRedirect
            split_ifs <;> omega
          have hroldlt : q < oldW.length := by rw [hold]; omega
          rw [show newW'.getD (redir n m p q) false = newW.getD (redir n m p q) false by
                exact List.getD_append _ _ _ _ hredlt]
          rw [show oldW'.getD q false = oldW.getD q false by
                exact List.getD_append _ _ _ _ hroldlt]
          exact hrel q hlt
      have hread' : ∀ j g', gs[j]? = some g' → ∀ q ∈ g'.inputs,
          q < n + m + (k + 1) + j + 1 := by
        intro j g' hj q hq
        have hs : (g :: gs)[j + 1]? = some g' := by simpa using hj
        have hb := hread (j + 1) g' hs q hq
        omega
      have hfinal := ih (k + 1) newW' oldW' hnew' hold' hrel' hread'
      intro q hq
      simp only [List.length_cons] at hq
      have hq' : q < n + m + (k + 1) + gs.length + 1 := by omega
      have hf := hfinal q hq'
      simpa [runW_cons, newW', oldW'] using hf


theorem eraseEval_and_wireMap_hfalse (n : ℕ) (C : Circuit) (m p h : ℕ) (x : List Bool)
    (hao : PEqualNP.TopForm.IsAO2 n C) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hx : x.length = n)
    (hfalse : (C.wires x).getD h false = false) :
    ((PEqualNP.CircuitMoves.eraseGate n C m p).eval x = C.eval x) ∧
      (∀ i, ((PEqualNP.CircuitMoves.eraseGate n C m p).wires x).getD
        (redir n m p i) false = (C.wires x).getD i false) := by
  let pref := C.gates.take m
  let tail := C.gates.drop (m + 1)
  let newW := runW pref x
  let oldW := runW (C.gates.take (m + 1)) x
  have hgate' : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m] = ⟨GateOp.or, [h, p]⟩ := by
    rcases hgate with hgate | hgate
    · left
      exact (List.getElem?_eq_some_iff.mp (by simpa [List.getElem?_eq_getElem hm] using hgate)).2
    · right
      exact (List.getElem?_eq_some_iff.mp (by simpa [List.getElem?_eq_getElem hm] using hgate)).2
  have htakeSucc : C.gates.take (m + 1) = pref ++ [C.gates[m]] := by
    simpa [pref] using (List.take_succ_eq_append_getElem (l := C.gates) hm)
  have hbaseOld : oldW = stepW newW (C.gates[m]) := by
    simp only [oldW, newW]
    rw [htakeSucc, runW_append]
    rfl
  have hnewLen : newW.length = n + m := by
    dsimp [newW]
    rw [runW_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)]
  have holdBase : oldW.length = n + m + 1 := by
    rw [hbaseOld]
    simp [stepW, hnewLen]
  have htailDecomp : C.gates = C.gates.take (m + 1) ++ tail := by
    dsimp [tail]
    exact (List.take_append_drop (m + 1) C.gates).symm
  have hlenTake : (C.gates.take (m + 1)).length = m + 1 := by
    simp [List.length_take, Nat.min_eq_left (by omega : m + 1 ≤ C.gates.length)]
  have hlenAll : C.gates.length = m + 1 + tail.length := by
    have := congrArg List.length htailDecomp
    simp only [List.length_append, hlenTake, tail] at this
    omega
  have hCprefix : ∀ i < n + m, (C.wires x).getD i false = newW.getD i false := by
    intro i hi
    change (runW C.gates x).getD i false = newW.getD i false
    rw [← List.take_append_drop m C.gates, runW_append]
    exact runW_getD (C.gates.drop m) newW i (by rw [hnewLen]; exact hi)
  have hfalseBase : newW.getD h false = false := by
    rw [← hCprefix h hh]
    exact hfalse
  have hgateEval : (C.gates[m]).op.eval
      ((C.gates[m]).inputs.map fun i => newW.getD i false) = newW.getD p false := by
    rcases hgate' with hg | hg
    · rw [hg]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      rw [hfalseBase]
      simp
    · rw [hg]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      rw [hfalseBase]
      simp
  have hbaseRel : ∀ q < n + m + 1,
      newW.getD (redir n m p q) false = oldW.getD q false := by
    intro q hq
    by_cases heq : q = n + m
    · subst q
      rw [show redir n m p (n + m) = p by simp [redir, PEqualNP.CircuitMoves.eraseRedirect]]
      rw [hbaseOld]
      unfold stepW
      rw [List.getD_append_right]
      · simp [hnewLen]
        exact hgateEval.symm
      · rw [hnewLen]
    · have hq' : q < n + m := by omega
      have hred : redir n m p q = q := by
        simp [redir, PEqualNP.CircuitMoves.eraseRedirect, heq]
        omega
      rw [hred, hbaseOld]
      unfold stepW
      rw [List.getD_append _ _ _ _ (by rw [hnewLen]; exact hq')]
  have hread : ∀ j g, tail[j]? = some g → ∀ q ∈ g.inputs,
      q < n + m + 0 + j + 1 := by
    intro j g hj q hq
    have hidxOpt : C.gates[m + 1 + j]? = some g := by
      simpa [tail, List.getElem?_drop, Nat.add_assoc] using hj
    rcases List.getElem?_eq_some_iff.mp hidxOpt with ⟨hidx, hget⟩
    have hgateAt : PEqualNP.MetaComplexity.NestedCover.gateAt C (m + 1 + j) = g := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hidx, hget]
    have hread := hao.2.1 (m + 1 + j) hidx q (by simpa [hgateAt] using hq)
    omega
  have htailRel := runTailRel n m p 0 hp tail newW oldW hnewLen
    holdBase hbaseRel hread
  let E := PEqualNP.CircuitMoves.eraseGate n C m p
  have hE : E = ⟨pref ++ tail.map (changeGate n m p), redir n m p C.output⟩ := by
    dsimp [E, PEqualNP.CircuitMoves.eraseGate]
    rw [if_pos hm]
    rfl
  have hEw : E.wires x = runW (tail.map (changeGate n m p)) newW := by
    rw [hE]
    change runW (pref ++ tail.map (changeGate n m p)) x = _
    rw [runW_append]
  have hCw : C.wires x = runW tail oldW := by
    change runW C.gates x = _
    rw [htailDecomp, runW_append, htakeSucc, runW_append]
    have hgRun : runW [C.gates[m]] newW = oldW := by
      change stepW newW (C.gates[m]) = oldW
      exact hbaseOld.symm
    change runW tail (runW [C.gates[m]] newW) = runW tail oldW
    exact congrArg (runW tail) hgRun
  have hElen : (E.wires x).length = n + m + tail.length := by
    rw [hEw, runW_length, hnewLen, List.length_map]
  have hClen : (C.wires x).length = n + m + tail.length + 1 := by
    rw [hCw, runW_length, holdBase]
    omega
  have hEout : E.output = redir n m p C.output := by rw [hE]
  have hWireAll : ∀ q, (E.wires x).getD (redir n m p q) false =
      (C.wires x).getD q false := by
    intro q
    by_cases hout : q < n + m + tail.length + 1
    · rw [hEw, hCw]
      exact htailRel q hout
    · have hout' : n + m + tail.length + 1 ≤ q := by omega
      have hredge : n + m + tail.length ≤ redir n m p q := by
        unfold redir PEqualNP.CircuitMoves.eraseRedirect
        split_ifs <;> omega
      have hCsmall : (C.wires x).length ≤ q := by
        rw [hClen]
        exact hout'
      have hEsmall : (E.wires x).length ≤ redir n m p q := by
        rw [hElen]
        exact hredge
      rw [List.getD_eq_default _ _ hEsmall, List.getD_eq_default _ _ hCsmall]
  constructor
  · change (E.wires x).getD E.output false = (C.wires x).getD C.output false
    rw [hEout]
    exact hWireAll C.output
  · exact hWireAll


private theorem erasePrefix_wires (n : ℕ) (C : Circuit) (m p : ℕ)
    (x : List Bool) (hm : m < C.gates.length) (hx : x.length = n)
    (i : ℕ) (hi : i < n + m) :
    ((PEqualNP.CircuitMoves.eraseGate n C m p).wires x).getD i false =
      (C.wires x).getD i false := by
  let pref := C.gates.take m
  let tail := C.gates.drop (m + 1)
  let w := runW pref x
  let E := PEqualNP.CircuitMoves.eraseGate n C m p
  have hwlen : w.length = n + m := by
    dsimp [w, pref]
    rw [runW_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)]
  have hE : E = ⟨pref ++ tail.map (changeGate n m p), redir n m p C.output⟩ := by
    dsimp [E, PEqualNP.CircuitMoves.eraseGate]
    rw [if_pos hm]
    rfl
  have hEw : E.wires x = runW (tail.map (changeGate n m p)) w := by
    rw [hE]
    change runW (pref ++ tail.map (changeGate n m p)) x = _
    rw [runW_append]
  have hCdecomp : C.gates = pref ++ C.gates.drop m := by
    dsimp [pref]
    exact (List.take_append_drop m C.gates).symm
  have hCw : C.wires x = runW (C.gates.drop m) w := by
    calc
      C.wires x = runW C.gates x := rfl
      _ = runW (pref ++ C.gates.drop m) x := by
        exact congrArg (fun gs => runW gs x) hCdecomp
      _ = runW (C.gates.drop m) (runW pref x) := runW_append _ _ _
      _ = runW (C.gates.drop m) w := rfl
  rw [hEw, hCw]
  have hiw : i < w.length := by rw [hwlen]; exact hi
  rw [runW_getD _ _ _ hiw, runW_getD _ _ _ hiw]

private theorem getD_append_singleton (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]



theorem selectedOrWire_eval (n : ℕ) (C : Circuit) (m p h : ℕ) (x : List Bool)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩) (hx : x.length = n) :
    (C.wires x).getD (n + m) false =
      ((C.wires x).getD p false || (C.wires x).getD h false) := by
  let pref := C.gates.take m
  let tail := C.gates.drop (m + 1)
  let pre := runW pref x
  have hgate' : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m] = ⟨GateOp.or, [h, p]⟩ := by
    rcases hgate with hg | hg
    · left
      exact (List.getElem?_eq_some_iff.mp
        (by simpa [List.getElem?_eq_getElem hm] using hg)).2
    · right
      exact (List.getElem?_eq_some_iff.mp
        (by simpa [List.getElem?_eq_getElem hm] using hg)).2
  have hpreLen : pre.length = n + m := by
    dsimp [pre, pref]
    rw [runW_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)]
  have htakeSucc : C.gates.take (m + 1) = pref ++ [C.gates[m]] := by
    simpa [pref] using (List.take_succ_eq_append_getElem (l := C.gates) hm)
  have hbase : runW (C.gates.take (m + 1)) x = stepW pre (C.gates[m]) := by
    rw [htakeSucc, runW_append]
    rfl
  have htailDecomp : C.gates = C.gates.take (m + 1) ++ tail := by
    dsimp [tail]
    exact (List.take_append_drop (m + 1) C.gates).symm
  have hCw : C.wires x = runW tail (stepW pre (C.gates[m])) := by
    calc
      C.wires x = runW C.gates x := rfl
      _ = runW (C.gates.take (m + 1) ++ tail) x :=
        congrArg (fun gs => runW gs x) htailDecomp
      _ = runW tail (runW (C.gates.take (m + 1)) x) :=
        runW_append _ _ _
      _ = runW tail (stepW pre (C.gates[m])) :=
        congrArg (runW tail) hbase
  have hprefix : ∀ i < n + m,
      (C.wires x).getD i false = pre.getD i false := by
    intro i hi
    have hdecomp : C.gates = pref ++ C.gates.drop m := by
      dsimp [pref]
      exact (List.take_append_drop m C.gates).symm
    calc
      (C.wires x).getD i false = (runW C.gates x).getD i false := rfl
      _ = (runW (pref ++ C.gates.drop m) x).getD i false :=
        congrArg (fun gs => (runW gs x).getD i false) hdecomp
      _ = (runW (C.gates.drop m) (runW pref x)).getD i false :=
        congrArg (fun w => w.getD i false) (runW_append _ _ _)
      _ = pre.getD i false := by
        exact runW_getD (C.gates.drop m) pre i (by rw [hpreLen]; exact hi)
  have hbaseAt : (stepW pre (C.gates[m])).getD (n + m) false =
      (C.gates[m]).op.eval ((C.gates[m]).inputs.map fun i => pre.getD i false) := by
    change (pre ++ [((C.gates[m]).op.eval
      ((C.gates[m]).inputs.map fun i => pre.getD i false))]).getD (n + m) false = _
    rw [← hpreLen]
    exact getD_append_singleton pre _
  have hgateEval : (C.gates[m]).op.eval
      ((C.gates[m]).inputs.map fun i => pre.getD i false) =
      (pre.getD p false || pre.getD h false) := by
    rcases hgate' with hg | hg
    · rw [hg]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      simp [Bool.or_comm]
    · rw [hg]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      simp [Bool.or_comm]
  calc
    (C.wires x).getD (n + m) false =
        (runW tail (stepW pre (C.gates[m]))).getD (n + m) false :=
      congrArg (fun w => w.getD (n + m) false) hCw
    _ = (stepW pre (C.gates[m])).getD (n + m) false :=
      runW_getD tail (stepW pre (C.gates[m])) (n + m) (by
        simp [stepW, hpreLen])
    _ = (C.gates[m]).op.eval
        ((C.gates[m]).inputs.map fun i => pre.getD i false) := hbaseAt
    _ = (pre.getD p false || pre.getD h false) := hgateEval
    _ = ((C.wires x).getD p false || (C.wires x).getD h false) := by
      rw [← hprefix p hp, ← hprefix h hh]


theorem selectedWire_below_iff_operand (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hbelowH : PEqualNP.CircuitMoves.WireBelowOutput n C h) :
    PEqualNP.CircuitMoves.WireBelowOutput n C (n + m) ↔
      PEqualNP.CircuitMoves.WireBelowOutput n C p := by
  constructor
  · intro hbelowM x hpTrue
    have hgateTrue : (C.wires (List.ofFn x)).getD (n + m) false = true := by
      calc
        (C.wires (List.ofFn x)).getD (n + m) false =
            ((C.wires (List.ofFn x)).getD p false ||
              (C.wires (List.ofFn x)).getD h false) :=
          selectedOrWire_eval n C m p h (List.ofFn x) hm hp hh hgate (by simp)
        _ = true := by rw [hpTrue]; simp
    exact hbelowM x hgateTrue
  · intro hbelowP x hmTrue
    have heval := selectedOrWire_eval n C m p h (List.ofFn x) hm hp hh hgate (by simp)
    have hcases : (C.wires (List.ofFn x)).getD p false = true ∨
        (C.wires (List.ofFn x)).getD h false = true := by
      have hor : ((C.wires (List.ofFn x)).getD p false ||
          (C.wires (List.ofFn x)).getD h false) = true := by
        calc
          _ = (C.wires (List.ofFn x)).getD (n + m) false := heval.symm
          _ = true := hmTrue
      exact Bool.or_eq_true_iff.mp hor
    rcases hcases with hpTrue | hhTrue
    · exact hbelowP x (by simpa using hpTrue)
    · exact hbelowH x (by simpa using hhTrue)


theorem selectedWire_not_below (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hbelowH : PEqualNP.CircuitMoves.WireBelowOutput n C h)
    (hpNot : ¬ PEqualNP.CircuitMoves.WireBelowOutput n C p) :
    ¬ PEqualNP.CircuitMoves.WireBelowOutput n C (n + m) := by
  intro hbelowM
  exact hpNot ((selectedWire_below_iff_operand n C m p h hm hp hh hgate hbelowH).mp hbelowM)

theorem liftAt_wires_append (n : ℕ) (C : Circuit) (m p h : ℕ)
    (x : List Bool) :
    (PEqualNP.CircuitMoves.liftAt n C m p h).wires x =
      (PEqualNP.CircuitMoves.eraseGate n C m p).wires x ++
        [((PEqualNP.CircuitMoves.eraseGate n C m p).eval x ||
          ((PEqualNP.CircuitMoves.eraseGate n C m p).wires x).getD h false)] := by
  let E := PEqualNP.CircuitMoves.eraseGate n C m p
  have hRun : runW E.gates x = E.wires x := rfl
  unfold PEqualNP.CircuitMoves.liftAt
  change runW (E.gates ++ [⟨GateOp.or, [E.output, h]⟩]) x = _
  rw [runW_append, hRun]
  change stepW (E.wires x) ⟨GateOp.or, [E.output, h]⟩ = _
  unfold stepW
  congr 1
  simp [GateOp.eval, Circuit.eval, List.any_cons, List.any_nil]
  rfl


theorem liftAt_wires_prefix (n : ℕ) (C : Circuit) (m p h : ℕ) (x : List Bool)
    (hm : m < C.gates.length) (hx : x.length = n) (i : ℕ) (hi : i < n + m) :
    ((PEqualNP.CircuitMoves.liftAt n C m p h).wires x).getD i false =
      (C.wires x).getD i false := by
  let pref := C.gates.take m
  let tail := C.gates.drop (m + 1)
  let E := PEqualNP.CircuitMoves.eraseGate n C m p
  have hE : E = ⟨pref ++ tail.map (changeGate n m p), redir n m p C.output⟩ := by
    dsimp [E, pref, tail, PEqualNP.CircuitMoves.eraseGate]
    rw [if_pos hm]
    rfl
  have hElen : E.gates.length = m + tail.length := by
    rw [hE]
    simp [pref, tail, List.length_take, List.length_drop,
      Nat.min_eq_left (Nat.le_of_lt hm)]
  have hEwlen : (E.wires x).length = n + E.gates.length := by
    change (runW E.gates x).length = _
    rw [runW_length, hx]
  have hlen : (E.wires x).length = n + m + tail.length := by
    rw [hEwlen, hElen]
    omega
  rw [liftAt_wires_append]
  rw [List.getD_append _ _ _ _ (by rw [hlen]; omega)]
  exact erasePrefix_wires n C m p x hm hx i hi

theorem liftAt_eval_eq_or (n : ℕ) (C : Circuit) (m p h : ℕ)
    (x : List Bool) (hx : x.length = n) :
    (PEqualNP.CircuitMoves.liftAt n C m p h).eval x =
      ((PEqualNP.CircuitMoves.eraseGate n C m p).eval x ||
        ((PEqualNP.CircuitMoves.eraseGate n C m p).wires x).getD h false) := by
  let E := PEqualNP.CircuitMoves.eraseGate n C m p
  have hW := liftAt_wires_append n C m p h x
  have hlen : (E.wires x).length = n + E.gates.length := by
    change (runW E.gates x).length = n + E.gates.length
    rw [runW_length, hx]
  have hout : (PEqualNP.CircuitMoves.liftAt n C m p h).output = n + E.gates.length := by
    rfl
  have hout' : (PEqualNP.CircuitMoves.liftAt n C m p h).output =
      (E.wires x).length := by rw [hout, ← hlen]
  have hget : (E.wires x ++ [E.eval x || (E.wires x).getD h false]).getD
      (E.wires x).length false = (E.eval x || (E.wires x).getD h false) :=
    getD_append_singleton (E.wires x) _
  calc
    (PEqualNP.CircuitMoves.liftAt n C m p h).eval x =
        ((PEqualNP.CircuitMoves.liftAt n C m p h).wires x).getD
          (PEqualNP.CircuitMoves.liftAt n C m p h).output false := rfl
    _ = (E.wires x ++ [E.eval x || (E.wires x).getD h false]).getD
          (PEqualNP.CircuitMoves.liftAt n C m p h).output false :=
      congrArg (fun w : List Bool => w.getD
        (PEqualNP.CircuitMoves.liftAt n C m p h).output false) hW
    _ = (E.wires x ++ [E.eval x || (E.wires x).getD h false]).getD
          (E.wires x).length false :=
      congrArg (fun i =>
        (E.wires x ++ [E.eval x || (E.wires x).getD h false]).getD i false) hout'
    _ = (E.eval x || (E.wires x).getD h false) := hget


theorem liftAt_eval_true_of_h (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hm : m < C.gates.length) (hh : h < n + m)
    (x : Fin n → Bool)
    (htrue : (C.wires (List.ofFn x)).getD h false = true) :
    (PEqualNP.CircuitMoves.liftAt n C m p h).eval (List.ofFn x) = true := by
  have hx : (List.ofFn x).length = n := by simp
  rw [liftAt_eval_eq_or n C m p h (List.ofFn x) hx]
  rw [erasePrefix_wires n C m p (List.ofFn x) hm hx h hh, htrue]
  simp


theorem liftAt_eval_same (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hao : PEqualNP.TopForm.IsAO2 n C) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hbelow : PEqualNP.CircuitMoves.WireBelowOutput n C h)
    (x : Fin n → Bool) :
    (PEqualNP.CircuitMoves.liftAt n C m p h).eval (List.ofFn x) =
      C.eval (List.ofFn x) := by
  let xs := List.ofFn x
  have hxs : xs.length = n := by simp [xs]
  change (PEqualNP.CircuitMoves.liftAt n C m p h).eval xs = C.eval xs
  have hwire := erasePrefix_wires n C m p xs hm hxs h hh
  have hLift := liftAt_eval_eq_or n C m p h xs hxs
  by_cases htrue : (C.wires xs).getD h false = true
  · have hCtrue : C.eval xs = true := hbelow x htrue
    rw [hLift, hwire]
    change ((PEqualNP.CircuitMoves.eraseGate n C m p).eval xs ||
      (C.wires xs).getD h false) = C.eval xs
    rw [htrue, hCtrue]
    simp
  · have hfalse : (C.wires xs).getD h false = false := by
      cases hv : (C.wires xs).getD h false <;> simp_all
    have herase := eraseEval_and_wireMap_hfalse n C m p h xs hao hm hp hh hgate hxs hfalse
    rw [hLift, hwire, herase.1]
    change (C.eval xs || (C.wires xs).getD h false) = C.eval xs
    rw [hfalse]
    simp


theorem liftAt_wireMap_hfalse (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hao : PEqualNP.TopForm.IsAO2 n C) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : Fin n → Bool) (hfalse : (C.wires (List.ofFn x)).getD h false = false)
    (i : ℕ) (hi : i < n + C.gates.length) :
    ((liftAt n C m p h).wires (List.ofFn x)).getD
      (eraseRedirect n m p i) false = (C.wires (List.ofFn x)).getD i false := by
  let E := eraseGate n C m p
  have hElen : E.gates.length = C.gates.length - 1 := by
    dsimp [E]
    simp [eraseGate, hm, List.length_append, List.length_take,
      List.length_drop, Nat.min_eq_left hm.le]
    omega
  have hx : (List.ofFn x).length = n := by simp
  have hEwlen : (E.wires (List.ofFn x)).length = n + C.gates.length - 1 := by
    change (runW E.gates (List.ofFn x)).length = _
    rw [runW_length, hx, hElen]
    omega
  have hiR : eraseRedirect n m p i < n + C.gates.length - 1 := by
    unfold eraseRedirect
    by_cases heq : i = n + m
    · simp [heq]
      omega
    · by_cases hgt : n + m < i
      · simp [heq, hgt]
        omega
      · simp [heq, hgt]
        omega
  have hiE : eraseRedirect n m p i < (E.wires (List.ofFn x)).length := by
    rw [hEwlen]
    exact hiR
  have hErase := eraseEval_and_wireMap_hfalse n C m p h (List.ofFn x)
    hao hm hp hh hgate hx hfalse
  have hAppend := liftAt_wires_append n C m p h (List.ofFn x)
  change ((liftAt n C m p h).wires (List.ofFn x)).getD
      (eraseRedirect n m p i) false = _
  rw [hAppend, List.getD_append _ _ _ _ hiE]
  exact hErase.2 i

end eval

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves

namespace survivors


def badGate (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ ∃ a b,
    (C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ ∨
      C.gates[j]? = some ⟨GateOp.or, [b, a]⟩) ∧
    n ≤ b ∧ WireBelowOutput n C b ∧ ¬ WireBelowOutput n C a

def erasedGateIndex (m j : ℕ) : ℕ := if j < m then j else j - 1

def renameGate (n m p : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem list_length_two_eq_pair {α : Type} (xs : List α) (hlen : xs.length = 2) :
    ∃ a b, xs = [a, b] := by
  cases xs with
  | nil => simp at hlen
  | cons a xs =>
    cases xs with
    | nil => simp at hlen
    | cons b xs =>
      cases xs with
      | nil => exact ⟨a, b, rfl⟩
      | cons c xs => simp at hlen

theorem badGate_lift_iff
    (n m p : ℕ) (C C' : Circuit) (j : ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hC' : PEqualNP.TopForm.IsAO2 n C')
    (hRB : ReadsBack n C)
    (hj : j < C.gates.length)
    (hjm : j ≠ m)
    (hidx : erasedGateIndex m j < C'.gates.length)
    (hmap : gateAt C' (erasedGateIndex m j) = renameGate n m p (gateAt C j))
    (hwire : ∀ w, w < n + C.gates.length →
      (WireBelowOutput n C w ↔ WireBelowOutput n C' (eraseRedirect n m p w)))
    (hguard : ∀ w, w < n + C.gates.length → w ≠ n + m →
      (n ≤ w ↔ n ≤ eraseRedirect n m p w))
    (hdel : ¬ WireBelowOutput n C (n + m)) :
    badGate n C j ↔ badGate n C' (erasedGateIndex m j) := by
  have _hC' : PEqualNP.TopForm.IsAO2 n C' := hC'
  have _hjm : j ≠ m := hjm
  constructor
  · intro hbad
    rcases hbad with ⟨_, a, b, hgate | hgate, hnb, hbelow, hnot⟩
    · have hgateOld : gateAt C j = ⟨GateOp.or, [a, b]⟩ := by
        simpa [gateAt, hj] using hgate
      have hgateNew : gateAt C' (erasedGateIndex m j) =
          ⟨GateOp.or, [eraseRedirect n m p a, eraseRedirect n m p b]⟩ := by
        rw [hmap, hgateOld]
        simp [renameGate]
      have hnewOpt : C'.gates[erasedGateIndex m j]? =
          some ⟨GateOp.or, [eraseRedirect n m p a, eraseRedirect n m p b]⟩ := by
        simpa [gateAt, hidx] using hgateNew
      have haRead : a ∈ (gateAt C j).inputs := by rw [hgateOld]; simp
      have hbRead : b ∈ (gateAt C j).inputs := by rw [hgateOld]; simp
      have haBound : a < n + C.gates.length := by
        have h := hRB j hj a haRead
        omega
      have hbBound : b < n + C.gates.length := by
        have h := hRB j hj b hbRead
        omega
      have hbNotDel : b ≠ n + m := by
        intro heq
        subst b
        exact hdel hbelow
      have hnbNew : n ≤ eraseRedirect n m p b :=
        (hguard b hbBound hbNotDel).mp hnb
      have hwireB := hwire b hbBound
      have hbelowNew : WireBelowOutput n C' (eraseRedirect n m p b) :=
        hwireB.mp hbelow
      have hnotNew : ¬ WireBelowOutput n C' (eraseRedirect n m p a) := by
        intro h
        have hwireA := hwire a haBound
        exact hnot (hwireA.mpr h)
      exact ⟨hidx, eraseRedirect n m p a, eraseRedirect n m p b,
        Or.inl hnewOpt, hnbNew, hbelowNew, hnotNew⟩
    · have hgateOld : gateAt C j = ⟨GateOp.or, [b, a]⟩ := by
        simpa [gateAt, hj] using hgate
      have hgateNew : gateAt C' (erasedGateIndex m j) =
          ⟨GateOp.or, [eraseRedirect n m p b, eraseRedirect n m p a]⟩ := by
        rw [hmap, hgateOld]
        simp [renameGate]
      have hnewOpt : C'.gates[erasedGateIndex m j]? =
          some ⟨GateOp.or, [eraseRedirect n m p b, eraseRedirect n m p a]⟩ := by
        simpa [gateAt, hidx] using hgateNew
      have haRead : a ∈ (gateAt C j).inputs := by rw [hgateOld]; simp
      have hbRead : b ∈ (gateAt C j).inputs := by rw [hgateOld]; simp
      have haBound : a < n + C.gates.length := by
        have h := hRB j hj a haRead
        omega
      have hbBound : b < n + C.gates.length := by
        have h := hRB j hj b hbRead
        omega
      have hbNotDel : b ≠ n + m := by
        intro heq
        subst b
        exact hdel hbelow
      have hnbNew : n ≤ eraseRedirect n m p b :=
        (hguard b hbBound hbNotDel).mp hnb
      have hwireB := hwire b hbBound
      have hbelowNew : WireBelowOutput n C' (eraseRedirect n m p b) :=
        hwireB.mp hbelow
      have hnotNew : ¬ WireBelowOutput n C' (eraseRedirect n m p a) := by
        intro h
        have hwireA := hwire a haBound
        exact hnot (hwireA.mpr h)
      exact ⟨hidx, eraseRedirect n m p a, eraseRedirect n m p b,
        Or.inr hnewOpt, hnbNew, hbelowNew, hnotNew⟩
  · intro hbad
    rcases hbad with ⟨_, a', b', hgateNew | hgateNew, hnbNew, hbelowNew, hnotNew⟩
    · have hgateNew' : gateAt C' (erasedGateIndex m j) = ⟨GateOp.or, [a', b']⟩ := by
        simpa [gateAt, hidx] using hgateNew
      have hren : ⟨GateOp.or, [a', b']⟩ = renameGate n m p (gateAt C j) :=
        hgateNew'.symm.trans hmap
      have hmem : gateAt C j ∈ C.gates := by
        simpa [gateAt, hj] using (List.getElem_mem hj)
      have hlen : (gateAt C j).inputs.length = 2 := hC.2.2 _ hmem
      obtain ⟨u, v, huv⟩ := list_length_two_eq_pair _ hlen
      have hop : (gateAt C j).op = GateOp.or := by
        have he := congrArg Gate.op hren
        simpa [renameGate] using he.symm
      have hgateOld : gateAt C j = ⟨GateOp.or, [u, v]⟩ := by
        cases hg : gateAt C j with
        | mk op ins =>
          have hop' : op = GateOp.or := by simpa [hg] using hop
          have huv' : ins = [u, v] := by simpa [hg] using huv
          subst op
          rw [huv']
      have hgateOpt : C.gates[j]? = some ⟨GateOp.or, [u, v]⟩ := by
        simpa [gateAt, hj] using hgateOld
      have hmapInputs : [a', b'] = [eraseRedirect n m p u, eraseRedirect n m p v] := by
        have he := congrArg Gate.inputs hren
        simpa [renameGate, huv] using he
      have hparts : a' = eraseRedirect n m p u ∧ b' = eraseRedirect n m p v := by
        simpa using hmapInputs
      rcases hparts with ⟨haeq, hbeq⟩
      have huRead : u ∈ (gateAt C j).inputs := by rw [hgateOld]; simp
      have hvRead : v ∈ (gateAt C j).inputs := by rw [hgateOld]; simp
      have huBound : u < n + C.gates.length := by
        have h := hRB j hj u huRead
        omega
      have hvBound : v < n + C.gates.length := by
        have h := hRB j hj v hvRead
        omega
      have hwireV := hwire v hvBound
      have hvBelow : WireBelowOutput n C v := by
        apply hwireV.mpr
        simpa [hbeq] using hbelowNew
      have hvNotDel : v ≠ n + m := by
        intro heq
        subst v
        exact hdel hvBelow
      have hvGuard : n ≤ v := by
        apply (hguard v hvBound hvNotDel).mpr
        simpa [hbeq] using hnbNew
      have huNotBelow : ¬ WireBelowOutput n C u := by
        intro hbelowU
        apply hnotNew
        have hwireU := hwire u huBound
        have hbelowU' := hwireU.mp hbelowU
        simpa [haeq] using hbelowU'
      exact ⟨hj, u, v, Or.inl hgateOpt, hvGuard, hvBelow, huNotBelow⟩
    · have hgateNew' : gateAt C' (erasedGateIndex m j) = ⟨GateOp.or, [b', a']⟩ := by
        simpa [gateAt, hidx] using hgateNew
      have hren : ⟨GateOp.or, [b', a']⟩ = renameGate n m p (gateAt C j) :=
        hgateNew'.symm.trans hmap
      have hmem : gateAt C j ∈ C.gates := by
        simpa [gateAt, hj] using (List.getElem_mem hj)
      have hlen : (gateAt C j).inputs.length = 2 := hC.2.2 _ hmem
      obtain ⟨u, v, huv⟩ := list_length_two_eq_pair _ hlen
      have hop : (gateAt C j).op = GateOp.or := by
        have he := congrArg Gate.op hren
        simpa [renameGate] using he.symm
      have hgateOld : gateAt C j = ⟨GateOp.or, [u, v]⟩ := by
        cases hg : gateAt C j with
        | mk op ins =>
          have hop' : op = GateOp.or := by simpa [hg] using hop
          have huv' : ins = [u, v] := by simpa [hg] using huv
          subst op
          rw [huv']
      have hgateOpt : C.gates[j]? = some ⟨GateOp.or, [u, v]⟩ := by
        simpa [gateAt, hj] using hgateOld
      have hmapInputs : [b', a'] = [eraseRedirect n m p u, eraseRedirect n m p v] := by
        have he := congrArg Gate.inputs hren
        simpa [renameGate, huv] using he
      have hparts : b' = eraseRedirect n m p u ∧ a' = eraseRedirect n m p v := by
        simpa using hmapInputs
      rcases hparts with ⟨hbeq, haeq⟩
      have huRead : u ∈ (gateAt C j).inputs := by rw [hgateOld]; simp
      have hvRead : v ∈ (gateAt C j).inputs := by rw [hgateOld]; simp
      have huBound : u < n + C.gates.length := by
        have h := hRB j hj u huRead
        omega
      have hvBound : v < n + C.gates.length := by
        have h := hRB j hj v hvRead
        omega
      have huBelow : WireBelowOutput n C u := by
        have hwireU := hwire u huBound
        apply hwireU.mpr
        simpa [hbeq] using hbelowNew
      have huNotDel : u ≠ n + m := by
        intro heq
        subst u
        exact hdel huBelow
      have huGuard : n ≤ u := by
        apply (hguard u huBound huNotDel).mpr
        simpa [hbeq] using hnbNew
      have hvNotBelow : ¬ WireBelowOutput n C v := by
        intro hbelowV
        apply hnotNew
        have hwireV := hwire v hvBound
        have hbelowV' := hwireV.mp hbelowV
        simpa [haeq] using hbelowV'
      exact ⟨hj, v, u, Or.inr hgateOpt, huGuard, huBelow, hvNotBelow⟩

end survivors

namespace badcount

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm


def badGate (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧
    ∃ p h : ℕ,
      (C.gates[j]? = some ⟨GateOp.or, [p, h]⟩ ∨
       C.gates[j]? = some ⟨GateOp.or, [h, p]⟩) ∧
      n ≤ h ∧ WireBelowOutput n C h ∧ ¬ WireBelowOutput n C p


noncomputable def badGates (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact Finset.filter (badGate n C) (Finset.range C.gates.length)

noncomputable def badCount (n : ℕ) (C : Circuit) : ℕ := (badGates n C).card

def erasedGateIndex (m j : ℕ) : ℕ := if j < m then j else j - 1

private theorem erasedGateIndex_injOn (m : ℕ) (s : Finset ℕ)
    (hs : m ∉ s) : Set.InjOn (erasedGateIndex m) (s : Set ℕ) := by
  intro a ha b hb heq
  have ham : a ≠ m := by
    intro h; subst a; exact hs ha
  have hbm : b ≠ m := by
    intro h; subst b; exact hs hb
  by_cases ha' : a < m <;> by_cases hb' : b < m
  · simpa [erasedGateIndex, ha', hb'] using heq
  · have heq' : a = b - 1 := by simpa [erasedGateIndex, ha', hb'] using heq
    omega
  · have heq' : a - 1 = b := by simpa [erasedGateIndex, ha', hb'] using heq
    omega
  · have heq' : a - 1 = b - 1 := by simpa [erasedGateIndex, ha', hb'] using heq
    omega

theorem badGates_lift_eq_image
    (n : ℕ) (C C' : Circuit) (m : ℕ)
    (hlen : C'.gates.length = C.gates.length)
    (hm : m < C.gates.length)
    (hsurv : ∀ j, j < C.gates.length → j ≠ m →
      (badGate n C j ↔ badGate n C' (erasedGateIndex m j)))
    (hlast : ¬ badGate n C' (C.gates.length - 1)) :
    badGates n C' = (((badGates n C).erase m).image (erasedGateIndex m)) := by
  classical
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkr, hbk⟩
    have hkC : k < C.gates.length := by simpa [hlen] using hkr
    have hknlast : k ≠ C.gates.length - 1 := by
      intro heq
      subst k
      exact hlast hbk
    have hklt : k < C.gates.length - 1 := by omega
    by_cases hkm : k < m
    · refine Finset.mem_image.mpr ⟨k, ?_, ?_⟩
      · apply Finset.mem_erase.mpr
        refine ⟨by omega, ?_⟩
        have hbadold := (hsurv k hkC (by omega)).mpr
          (by simpa [erasedGateIndex, hkm] using hbk)
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkC,
          hbadold⟩
      · simp [erasedGateIndex, hkm]
    · have hmk : m ≤ k := by omega
      have hmj : m ≤ k + 1 := by omega
      have hnmj : ¬ k + 1 < m := by omega
      have hidx : erasedGateIndex m (k + 1) = k := by
        simp [erasedGateIndex, hnmj]
      refine Finset.mem_image.mpr ⟨k + 1, ?_, ?_⟩
      · apply Finset.mem_erase.mpr
        refine ⟨by omega, ?_⟩
        have hj : k + 1 < C.gates.length := by omega
        have hbk' : badGate n C' (erasedGateIndex m (k + 1)) := by
          simpa [hidx] using hbk
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,
          (hsurv (k + 1) hj (by omega)).mpr hbk'⟩
      · exact hidx
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    rcases Finset.mem_erase.mp hj with ⟨hjm, hjbad⟩
    rcases Finset.mem_filter.mp hjbad with ⟨hjr, hbj⟩
    have hjC : j < C.gates.length := by simpa using hjr
    have hbad := (hsurv j hjC hjm).mp hbj
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      simp [hlen]
      by_cases hjlt : j < m <;> simp [erasedGateIndex, hjlt] <;> omega
    · exact hbad

theorem badCount_lift_eq_erase_card
    (n : ℕ) (C C' : Circuit) (m : ℕ)
    (hlen : C'.gates.length = C.gates.length)
    (hm : m < C.gates.length)
    (hsurv : ∀ j, j < C.gates.length → j ≠ m →
      (badGate n C j ↔ badGate n C' (erasedGateIndex m j)))
    (hlast : ¬ badGate n C' (C.gates.length - 1)) :
    badCount n C' = ((badGates n C).erase m).card := by
  unfold badCount
  rw [badGates_lift_eq_image n C C' m hlen hm hsurv hlast]
  exact Finset.card_image_of_injOn (erasedGateIndex_injOn m
    ((badGates n C).erase m) (by simp))

end badcount

namespace stable
open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves


def badGate (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧
    ∃ p h : ℕ,
      (C.gates[j]? = some ⟨GateOp.or, [p, h]⟩ ∨
       C.gates[j]? = some ⟨GateOp.or, [h, p]⟩) ∧
      n ≤ h ∧ WireBelowOutput n C h ∧ ¬ WireBelowOutput n C p

def stable (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length → ∀ x8 x9,
    C.gates[j]? = some ⟨GateOp.or, [x8, x9]⟩ →
      (n ≤ x9 → WireBelowOutput n C x9 → WireBelowOutput n C x8) ∧
      (n ≤ x8 → WireBelowOutput n C x8 → WireBelowOutput n C x9)

theorem stable_iff_no_bad (n : ℕ) (C : Circuit) :
    stable n C ↔ ∀ j, ¬ badGate n C j := by
  classical
  constructor
  · intro hs j hb
    rcases hb with ⟨hj, p, h, hgate, hnh, hbh, hnop⟩
    rcases hgate with hgate | hgate
    · exact hnop ((hs j hj p h hgate).1 hnh hbh)
    · exact hnop ((hs j hj h p hgate).2 hnh hbh)
  · intro hno j hj x8 x9 hgate
    constructor
    · intro hn9 hb9
      by_contra hn8
      exact hno j ⟨hj, x8, x9, Or.inl hgate, hn9, hb9, hn8⟩
    · intro hn8 hb8
      by_contra hn9
      exact hno j ⟨hj, x9, x8, Or.inr hgate, hn8, hb8, hn9⟩

end stable

namespace wf


theorem normalize
    {α : Type} (Lift : α → α → Prop) (Stable Inv : α → Prop) (μ : α → Nat)
    (progress : ∀ C, Inv C → ¬ Stable C →
      ∃ C', Lift C C' ∧ μ C' < μ C ∧ Inv C')
    (C : α) (hC : Inv C) :
    ∃ D, Relation.ReflTransGen Lift C D ∧ Stable D ∧ Inv D := by
  suffices h : ∀ m, ∀ C, μ C = m → Inv C →
      ∃ D, Relation.ReflTransGen Lift C D ∧ Stable D ∧ Inv D by
    exact h (μ C) C rfl hC
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro C hμ hC
    by_cases hs : Stable C
    · exact ⟨C, Relation.ReflTransGen.refl, hs, hC⟩
    · obtain ⟨C', hLift, hμ', hC'⟩ := progress C hC hs
      have hlt : μ C' < m := by omega
      obtain ⟨D, hpath, hStable, hD⟩ := ih (μ C') hlt C' rfl hC'
      exact ⟨D, Relation.ReflTransGen.head hLift hpath, hStable, hD⟩


theorem normalize_preserving
    {α : Type} (Lift : α → α → Prop) (Stable Inv : α → Prop) (μ : α → Nat)
    (preserve : ∀ {C C'}, Lift C C' → ¬ Stable C → Inv C → Inv C')
    (decrease : ∀ C, Inv C → ¬ Stable C → ∃ C', Lift C C' ∧ μ C' < μ C)
    (C : α) (hC : Inv C) :
    ∃ D, Relation.ReflTransGen Lift C D ∧ Stable D ∧ Inv D := by
  apply normalize Lift Stable Inv μ ?_ C hC
  intro C hC hStable
  obtain ⟨C', hLift, hμ'⟩ := decrease C hC hStable
  exact ⟨C', hLift, hμ', preserve hLift hStable hC⟩

end wf

namespace progress

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover


private theorem liftAt_last_gate_not_bad (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hout : C.output < n + C.gates.length) :
    ¬ PEqualNP.Outside.L_meta_4295_aux.badcount.badGate n
      (liftAt n C m p h) ((liftAt n C m p h).gates.length - 1) := by
  let E := eraseGate n C m p
  let C' := liftAt n C m p h
  have hElen : E.gates.length = C.gates.length - 1 := by
    exact PEqualNP.Outside.L_meta_4295_aux.ao2.eraseGate_len hm
  have hLlen : C'.gates.length = C.gates.length := by
    exact PEqualNP.Outside.L_meta_4295_aux.ao2.liftAt_len hm
  have hlast : C'.gates.length - 1 = E.gates.length := by
    rw [hLlen, hElen]
  have hgateLast : C'.gates[E.gates.length]? =
      some ⟨GateOp.or, [E.output, h]⟩ := by
    dsimp [C', liftAt, E]
    simp
  have hEoutValid : E.output < n + E.gates.length := by
    have h := PEqualNP.Outside.L_meta_4295_aux.ao2.eraseGate_out_lt
      (n := n) (m := m) (p := p) (C := C) hm hp hout
    have h' : E.output < n + C.gates.length - 1 := by simpa [E] using h
    omega
  have hEoutBelow : WireBelowOutput n C' E.output := by
    intro x hEout
    have hx : (List.ofFn x).length = n := by simp
    have hEwlen : (E.wires (List.ofFn x)).length = n + E.gates.length := by
      change (PEqualNP.Outside.L_meta_4295_aux.eval.runW E.gates (List.ofFn x)).length = _
      rw [PEqualNP.Outside.L_meta_4295_aux.eval.runW_length, hx]
    have hAppend := PEqualNP.Outside.L_meta_4295_aux.eval.liftAt_wires_append n C m p h (List.ofFn x)
    have hprefix : (C'.wires (List.ofFn x)).getD E.output false =
        (E.wires (List.ofFn x)).getD E.output false := by
      rw [hAppend, List.getD_append _ _ _ _ (by rw [hEwlen]; exact hEoutValid)]
    have hEeval : E.eval (List.ofFn x) = true := by
      change (E.wires (List.ofFn x)).getD E.output false = true
      rw [← hprefix]
      exact hEout
    have hformula := PEqualNP.Outside.L_meta_4295_aux.eval.liftAt_eval_eq_or n C m p h (List.ofFn x) hx
    rw [hformula, hEeval]
    simp
  have hHbelow : WireBelowOutput n C' h := by
    intro x hhTrue
    have hx : (List.ofFn x).length = n := by simp
    have hprefix := PEqualNP.Outside.L_meta_4295_aux.eval.liftAt_wires_prefix n C m p h
      (List.ofFn x) hm hx h hh
    have hOldTrue : (C.wires (List.ofFn x)).getD h false = true := by
      rw [← hprefix]
      exact hhTrue
    simpa [C'] using PEqualNP.Outside.L_meta_4295_aux.eval.liftAt_eval_true_of_h n C m p h hm hh x hOldTrue
  intro hbad
  rcases hbad with ⟨_, a, b, hgate | hgate, _, _, hnot⟩
  · have heq : (⟨GateOp.or, [a, b]⟩ : Gate) = ⟨GateOp.or, [E.output, h]⟩ :=
      Option.some.inj (hgate.symm.trans (by simpa [C', hlast] using hgateLast))
    have hab : a = E.output ∧ b = h := by
      have hi := congrArg Gate.inputs heq
      simpa using hi
    rcases hab with ⟨rfl, rfl⟩
    exact hnot hEoutBelow
  · have heq : (⟨GateOp.or, [b, a]⟩ : Gate) = ⟨GateOp.or, [E.output, h]⟩ :=
      Option.some.inj (hgate.symm.trans (by simpa [C', hlast] using hgateLast))
    have hba : b = E.output ∧ a = h := by
      have hi := congrArg Gate.inputs heq
      simpa using hi
    rcases hba with ⟨rfl, rfl⟩
    exact hnot hHbelow

private theorem liftAt_decreases_badCount (n : ℕ) (C : Circuit)
    (hC : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (m p h : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m) (hnh : n ≤ h)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hbelow : WireBelowOutput n C h) (hnot : ¬ WireBelowOutput n C p) :
    PEqualNP.Outside.L_meta_4295_aux.badcount.badCount n
        (liftAt n C m p h) <
      PEqualNP.Outside.L_meta_4295_aux.badcount.badCount n C := by
  classical
  let C' := liftAt n C m p h
  have hC' : IsAO2 n C' := by
    simpa [C'] using PEqualNP.Outside.L_meta_4295_aux.ao2.liftAt_preserves_IsAO2
      hC hm hp hh hout
  have hlen : C'.gates.length = C.gates.length := by
    exact PEqualNP.Outside.L_meta_4295_aux.ao2.liftAt_len hm
  have hdel : ¬ WireBelowOutput n C (n + m) :=
    PEqualNP.Outside.L_meta_4295_aux.eval.selectedWire_not_below n C m p h hm hp hh hgate hbelow hnot
  have hEval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = C'.eval (List.ofFn x) := by
    intro x
    simpa [C'] using (PEqualNP.Outside.L_meta_4295_aux.eval.liftAt_eval_same n C m p h hC hm hp hh
      hgate hbelow x).symm
  have hNewTrue : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD h false = true → C'.eval (List.ofFn x) = true := by
    intro x hx
    simpa [C'] using PEqualNP.Outside.L_meta_4295_aux.eval.liftAt_eval_true_of_h n C m p h hm hh x hx
  have hwire : ∀ w, w < n + C.gates.length →
      (WireBelowOutput n C w ↔ WireBelowOutput n C' (eraseRedirect n m p w)) := by
    intro w hw
    exact PEqualNP.Outside.L_meta_4295_aux.status.belowOutput_iff_of_false_case
      n C C' h w (eraseRedirect n m p w) hbelow hEval hNewTrue (by
        intro x hfalse
        simpa [C'] using (PEqualNP.Outside.L_meta_4295_aux.eval.liftAt_wireMap_hfalse n C m p h
          hC hm hp hh hgate x hfalse w hw).symm)
  have hguard : ∀ w, w < n + C.gates.length → w ≠ n + m →
      (n ≤ w ↔ n ≤ eraseRedirect n m p w) := by
    intro w hw hwd
    exact PEqualNP.Outside.L_meta_4295_aux.ao2.eraseRedirect_preserves_gate_index_test hw hwd
  have hsurv : ∀ j, j < C.gates.length → j ≠ m →
      (PEqualNP.Outside.L_meta_4295_aux.badcount.badGate n C j ↔
        PEqualNP.Outside.L_meta_4295_aux.badcount.badGate n C'
          (PEqualNP.Outside.L_meta_4295_aux.badcount.erasedGateIndex m j)) := by
    intro j hj hjm
    have hidx : PEqualNP.Outside.L_meta_4295_aux.survivors.erasedGateIndex m j < C'.gates.length := by
      rw [hlen]
      by_cases hjlt : j < m <;>
        simp [PEqualNP.Outside.L_meta_4295_aux.survivors.erasedGateIndex, hjlt] <;> omega
    have hmap0 := PEqualNP.Outside.L_meta_4295_aux.ao2.liftAt_gate_mapping
      (n := n) (m := m) (p := p) (h := h) (j := j) (C := C)
      hC hm hp hj hjm
    have hOldGate : C.gates[j]? = some (gateAt C j) := by
      simp [gateAt, hj]
    rw [hOldGate] at hmap0
    have hmapOpt : C'.gates[PEqualNP.Outside.L_meta_4295_aux.survivors.erasedGateIndex m j]? =
        some (PEqualNP.Outside.L_meta_4295_aux.survivors.renameGate n m p (gateAt C j)) := by
      simpa [C', PEqualNP.Outside.L_meta_4295_aux.ao2.erasedGateIndex,
        PEqualNP.Outside.L_meta_4295_aux.survivors.erasedGateIndex, PEqualNP.Outside.L_meta_4295_aux.survivors.renameGate,
        PEqualNP.Outside.L_meta_4295_aux.ao2.renameGate] using hmap0
    have hmap : gateAt C' (PEqualNP.Outside.L_meta_4295_aux.survivors.erasedGateIndex m j) =
        PEqualNP.Outside.L_meta_4295_aux.survivors.renameGate n m p (gateAt C j) := by
      simpa [gateAt, hidx] using hmapOpt
    have hsurv0 := PEqualNP.Outside.L_meta_4295_aux.survivors.badGate_lift_iff n m p C C' j
      hC hC' hC.2.1 hj hjm hidx hmap hwire hguard hdel
    simpa [PEqualNP.Outside.L_meta_4295_aux.survivors.badGate,
      PEqualNP.Outside.L_meta_4295_aux.badcount.badGate,
      PEqualNP.Outside.L_meta_4295_aux.survivors.erasedGateIndex,
      PEqualNP.Outside.L_meta_4295_aux.badcount.erasedGateIndex] using hsurv0
  have hlast : ¬ PEqualNP.Outside.L_meta_4295_aux.badcount.badGate n C'
      (C.gates.length - 1) := by
    have hlast0 := liftAt_last_gate_not_bad n C m p h hm hp hh hout
    simpa [C', hlen, PEqualNP.Outside.L_meta_4295_aux.badcount.badGate] using hlast0
  have hmBad : PEqualNP.Outside.L_meta_4295_aux.badcount.badGate n C m := by
    refine ⟨hm, p, h, hgate, hnh, hbelow, hnot⟩
  have hmIn : m ∈ PEqualNP.Outside.L_meta_4295_aux.badcount.badGates n C := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hmBad⟩
  have hcount := PEqualNP.Outside.L_meta_4295_aux.badcount.badCount_lift_eq_erase_card
    n C C' m hlen hm hsurv hlast
  have hcountCard :
      (PEqualNP.Outside.L_meta_4295_aux.badcount.badGates n C').card =
        ((PEqualNP.Outside.L_meta_4295_aux.badcount.badGates n C).erase m).card := by
    simpa [PEqualNP.Outside.L_meta_4295_aux.badcount.badCount] using hcount
  have hcount' :
      (PEqualNP.Outside.L_meta_4295_aux.badcount.badGates n C').card =
        (PEqualNP.Outside.L_meta_4295_aux.badcount.badGates n C).card - 1 := by
    rw [hcountCard, Finset.card_erase_of_mem hmIn]
  have hpos : 0 <
      (PEqualNP.Outside.L_meta_4295_aux.badcount.badGates n C).card :=
    Finset.card_pos.mpr ⟨m, hmIn⟩
  change (PEqualNP.Outside.L_meta_4295_aux.badcount.badGates n C').card <
    (PEqualNP.Outside.L_meta_4295_aux.badcount.badGates n C).card
  rw [hcount']
  exact Nat.sub_lt hpos (by decide)

private theorem progress (n : ℕ) (C : Circuit)
    (hC : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hstable : ¬ PEqualNP.Outside.L_meta_4295_aux.stable.stable n C) :
    ∃ C', Lift n C C' ∧
      PEqualNP.Outside.L_meta_4295_aux.badcount.badCount n C' <
        PEqualNP.Outside.L_meta_4295_aux.badcount.badCount n C ∧
      IsAO2 n C' ∧ C'.output < n + C'.gates.length := by
  have hbad : ∃ m, PEqualNP.Outside.L_meta_4295_aux.stable.badGate n C m := by
    by_contra hn
    apply hstable
    apply (PEqualNP.Outside.L_meta_4295_aux.stable.stable_iff_no_bad n C).2
    intro j hj
    exact hn ⟨j, hj⟩
  rcases hbad with ⟨m, hmBad⟩
  have hmBad' : PEqualNP.Outside.L_meta_4295_aux.badcount.badGate n C m := by
    simpa [PEqualNP.Outside.L_meta_4295_aux.stable.badGate,
      PEqualNP.Outside.L_meta_4295_aux.badcount.badGate] using hmBad
  rcases hmBad' with ⟨hm, p, h, hgate, hnh, hbelow, hnot⟩
  have hpRead : p ∈ (gateAt C m).inputs := by
    rcases hgate with hg | hg
    · have heq : gateAt C m = ⟨GateOp.or, [p, h]⟩ := by
        simpa [gateAt, hm] using hg
      rw [heq]
      simp
    · have heq : gateAt C m = ⟨GateOp.or, [h, p]⟩ := by
        simpa [gateAt, hm] using hg
      rw [heq]
      simp
  have hhRead : h ∈ (gateAt C m).inputs := by
    rcases hgate with hg | hg
    · have heq : gateAt C m = ⟨GateOp.or, [p, h]⟩ := by
        simpa [gateAt, hm] using hg
      rw [heq]
      simp
    · have heq : gateAt C m = ⟨GateOp.or, [h, p]⟩ := by
        simpa [gateAt, hm] using hg
      rw [heq]
      simp
  have hp : p < n + m := by
    have hb := hC.2.1 m hm p hpRead
    omega
  have hh : h < n + m := by
    have hb := hC.2.1 m hm h hhRead
    omega
  let C' := liftAt n C m p h
  have hC' : IsAO2 n C' := by
    simpa [C'] using PEqualNP.Outside.L_meta_4295_aux.ao2.liftAt_preserves_IsAO2
      hC hm hp hh hout
  have hout' : C'.output < n + C'.gates.length := by
    simpa [C'] using PEqualNP.Outside.L_meta_4295_aux.ao2.liftAt_output_valid hm
  have hdecrease := liftAt_decreases_badCount n C hC hout m p h hm hp hh hnh
    hgate hbelow hnot
  exact ⟨C', ⟨m, hm, p, hp, h, hh, hnh, hgate, hbelow, rfl⟩,
    hdecrease, hC', hout'⟩


theorem normalizeCircuit (n : ℕ) (C : Circuit)
    (hC : IsAO2 n C) (hout : C.output < n + C.gates.length) :
    ∃ D, Relation.ReflTransGen (Lift n) C D ∧
      PEqualNP.Outside.L_meta_4295_aux.stable.stable n D := by
  let Inv : Circuit → Prop := fun X => IsAO2 n X ∧ X.output < n + X.gates.length
  let μ : Circuit → Nat := fun X =>
    PEqualNP.Outside.L_meta_4295_aux.badcount.badCount n X
  have hPreserve : ∀ {X Y}, Lift n X Y →
      ¬ PEqualNP.Outside.L_meta_4295_aux.stable.stable n X → Inv X → Inv Y := by
    intro X Y hXY _ hX
    rcases hXY with ⟨m, hm, p, hp, h, hh, _, _, _, rfl⟩
    exact ⟨PEqualNP.Outside.L_meta_4295_aux.ao2.liftAt_preserves_IsAO2
      hX.1 hm hp hh hX.2,
      PEqualNP.Outside.L_meta_4295_aux.ao2.liftAt_output_valid hm⟩
  have hDecrease : ∀ X, Inv X →
      ¬ PEqualNP.Outside.L_meta_4295_aux.stable.stable n X →
      ∃ Y, Lift n X Y ∧ μ Y < μ X := by
    intro X hX hns
    obtain ⟨Y, hXY, hdec, _, _⟩ := progress n X hX.1 hX.2 hns
    exact ⟨Y, hXY, hdec⟩
  obtain ⟨D, hpath, hstable, _⟩ :=
    PEqualNP.Outside.L_meta_4295_aux.wf.normalize_preserving
      (fun X Y => Lift n X Y)
      (fun X => PEqualNP.Outside.L_meta_4295_aux.stable.stable n X)
      Inv μ hPreserve hDecrease C ⟨hC, hout⟩
  exact ⟨D, hpath, hstable⟩

end progress


end PEqualNP.Outside.L_meta_4295_aux

theorem PEqualNP.Outside.L_meta_4295 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 x1 x2 →
      x2.output < x1 + x2.gates.length →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧
        ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ),
          x5.gates[x6]? = Option.some
            { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] } →
          (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 →
            PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧
          (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 →
            PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hC hout
  obtain ⟨D, hpath, hstable⟩ :=
    PEqualNP.Outside.L_meta_4295_aux.progress.normalizeCircuit n C hC hout
  exact ⟨D, hpath, by
    simpa [PEqualNP.Outside.L_meta_4295_aux.stable.stable] using hstable⟩
