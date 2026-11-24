import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The wire scan follows the recurrence used in L-meta-2227.
-- The formula case uses the rigidity of L-meta-2225 at the marked incidence.
theorem PEqualNP.Outside.R_meta_1967_2
    (unshare :
      let valid (C : Circuit) := C.size ≤ 27 ∧ IsAO2 14 C ∧
        (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) ∧
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
          p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
      let tree (C : Circuit) := ((C.output :: C.gates.flatMap Gate.inputs).filter
        (fun w => decide (14 ≤ w))).Nodup
      let reread (C : Circuit) (j : ℕ) (u : Fin 14) :=
        (gateAt C j).op = .and ∧ (14+j = C.output ∨ InCone 14 C j (C.output-14)) ∧
          gateVal 14 C j (pairInput 0 7) = true ∧
          ∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 14 C (opnd C j b) (pairInput u u) = false
      ∀ C : Circuit, valid C → ¬ tree C →
        (∃ i j, (InCone 14 C i j ∨ InCone 14 C j i) ∧ reread C i 0 ∧ reread C j 7) →
        2 ≤ C.lineDeg 14 {0} → 2 ≤ C.lineDeg 14 {7} →
        ∃ D : Circuit, valid D ∧ tree D ∧ 2 ≤ D.lineDeg 14 {0} ∧ 2 ≤ D.lineDeg 14 {7})
    (rigid : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup →
      HasLineDegree 14 {0} C 1 ∨ HasLineDegree 14 {7} C 1) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), (PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  rintro ⟨C, hsize, hgate, hfun, i, j, chain, iAnd, iOut, iYes, iOff, jAnd, jOut, jYes, jOff⟩
  have gateEq (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj
  have facts (j : ℕ) (hj : j < C.gates.length) :=
    hgate j (C.gates[j]'hj) (List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩)
  have ao : IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      exact (facts k hk).1
    · intro k hk w hw
      obtain ⟨a,b,inputs,_,ha,hb⟩ := (facts k hk).2
      rw [gateEq k hk, inputs] at hw
      rcases (show w = a ∨ w = b by simpa using hw) with rfl | rfl
      · exact ha
      · exact hb
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨_,_,eq,_,_,_⟩ := (facts k hk).2
      simp [eq]
  have distinct (k : ℕ) (hk : k < C.gates.length) : (gateAt C k).inputs.Nodup := by
    obtain ⟨a,b,eq,ne,_,_⟩ := (facts k hk).2
    rw [gateEq k hk, eq]
    simpa using ne
  have incidence : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l + 1 ∨ p = l + 3 := by
    decide +kernel
  have correct (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
      p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    simpa only [incidence] using hfun x
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  let scan {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :=
    gs.foldl (fun a g => a ++ [f a g]) w
  have scanCons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
      scan f (g :: gs) w = scan f gs (w ++ [f w g]) := rfl
  have scanLength {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
      (scan f gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [scan]
    | cons g gs ih => rw [scanCons, ih]; simp; omega
  have scanPrefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α)
      (d : α) (k : ℕ) (hk : k < w.length) : (scan f gs w).getD k d = w.getD k d := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [scanCons, ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hk
  have scanAppend {α : Type} (f : List α → Gate → α) (xs ys : List Gate) (w : List α) :
      scan f (xs ++ ys) w = scan f ys (scan f xs w) := by
    simp only [scan, List.foldl_append]
  have readStep {α : Type} (f : List α → Gate → α) (w : List α) (d : α)
      (k : ℕ) (hk : k < C.gates.length) (a b : ℕ) (ha : a < w.length+k) (hb : b < w.length+k)
      (op : α → α → α) (h : ∀ z, f z C.gates[k] = op (z.getD a d) (z.getD b d)) :
      (scan f C.gates w).getD (w.length+k) d =
        op ((scan f C.gates w).getD a d) ((scan f C.gates w).getD b d) := by
    let pre := scan f (C.gates.take k) w
    have hp : pre.length = w.length + k := by simp [pre, scanLength, Nat.min_eq_left hk.le]
    have hs : scan f C.gates w = scan f (C.gates[k] :: C.gates.drop (k+1)) pre := by
      have ht := List.take_append_drop k C.gates
      conv_lhs => rw [← ht, scanAppend, List.drop_eq_getElem_cons hk]
    have earlier (i : ℕ) (hi : i < w.length+k) : (scan f C.gates w).getD i d = pre.getD i d := by
      rw [hs]
      exact scanPrefix _ _ _ _ _ (by omega)
    rw [earlier a ha, earlier b hb, hs, scanCons,
      scanPrefix _ _ _ _ _ (by simp [hp]), List.getD_append_right _ _ _ _ (by omega)]
    simpa [hp] using h pre
  let B (x : Fin 14 → Bool) (w : ℕ) := (C.wires (List.ofFn x)).getD w false
  let N (v : Fin 14) (w : ℕ) := (C.lineDegrees 14 {v.val}).getD w 0
  let G (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let initial (v : Fin 14) := (List.range 14).map fun i => if i ∈ ({v.val} : Finset ℕ) then 1 else 0
  have nStart (v : Fin 14) : (initial v).length = 14 := by simp [initial]
  let boolOp (g : GateOp) (x y : Bool) := if g = .and then x && y else x || y
  let natOp (g : GateOp) (a b : ℕ) := if g = .and then a + b else max a b
  have bRaw (x : Fin 14 → Bool) (k : ℕ) (hk : k < 14) : B x k = x ⟨k, hk⟩ := by
    change (scan G C.gates (List.ofFn x)).getD k false = _
    rw [scanPrefix _ _ _ _ _ (by simpa using hk),
      List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
  have nRaw (v : Fin 14) (k : ℕ) (hk : k < 14) : N v k = if k = v.val then 1 else 0 := by
    change (scan (fun w g => g.lineDegree w) C.gates (initial v)).getD k 0 = _
    rw [scanPrefix _ _ _ _ _ (by simpa only [nStart] using hk),
      List.getD_eq_getElem _ _ (by simpa only [nStart] using hk)]
    simp [initial]
  have recurrence (k : ℕ) (hk : k < C.gates.length) (a b : ℕ)
      (inputs : C.gates[k].inputs = [a,b]) (ha : a < 14+k) (hb : b < 14+k) :
      (∀ x, B x (14+k) = boolOp C.gates[k].op (B x a) (B x b)) ∧
      (∀ v, N v (14+k) = natOp C.gates[k].op (N v a) (N v b)) := by
    constructor
    · intro x
      have ev (w : List Bool) :
          G w C.gates[k] = boolOp C.gates[k].op (w.getD a false) (w.getD b false) := by
        change C.gates[k].op.eval (C.gates[k].inputs.map (fun k => w.getD k false)) = _
        rw [inputs]
        simp only [List.map_cons, List.map_nil]
        rcases (facts k hk).1 with hop | hop
        · rw [hop]
          cases w.getD a false <;> cases w.getD b false <;> rfl
        · rw [hop]
          cases w.getD a false <;> cases w.getD b false <;> rfl
      change (scan G C.gates (List.ofFn x)).getD (14+k) false =
        boolOp C.gates[k].op ((scan G C.gates (List.ofFn x)).getD a false)
          ((scan G C.gates (List.ofFn x)).getD b false)
      simpa only [List.length_ofFn] using readStep G (List.ofFn x) false k hk a b
        (by simpa using ha) (by simpa using hb) (boolOp C.gates[k].op) ev
    · intro v
      let f (w : List ℕ) (g : Gate) := g.lineDegree w
      have ev (w : List ℕ) :
          f w C.gates[k] = natOp C.gates[k].op (w.getD a 0) (w.getD b 0) := by
        change (if C.gates[k].op = .and then (C.gates[k].inputs.map (fun i => w.getD i 0)).sum
          else (C.gates[k].inputs.map (fun i => w.getD i 0)).foldr max 0) = _
        rw [inputs]
        simp [natOp]
      change (scan f C.gates (initial v)).getD (14+k) 0 =
        natOp C.gates[k].op ((scan f C.gates (initial v)).getD a 0)
          ((scan f C.gates (initial v)).getD b 0)
      simpa only [nStart] using readStep f (initial v) 0 k hk a b
        (by simpa only [nStart] using ha) (by simpa only [nStart] using hb) (natOp C.gates[k].op) ev
  have numBound (g : GateOp) (a b : ℕ) : a ≤ natOp g a b ∧ b ≤ natOp g a b := by
    by_cases h : g = .and
    · simp [natOp, h]
    · simp only [natOp, h, if_false]
      exact ⟨le_max_left _ _, le_max_right _ _⟩
  have stable (u v : Fin 14) (w : ℕ) (hw : w < 14 + C.gates.length) (zero : N v w = 0) :
      B (pairInput u v) w = B (pairInput u u) w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases input : w < 14
      · rw [bRaw _ w input, bRaw _ w input]
        have nv : (⟨w,input⟩ : Fin 14) ≠ v := by
          intro eq
          have ew := congrArg Fin.val eq
          rw [nRaw v w input, if_pos ew] at zero
          contradiction
        change decide ((⟨w,input⟩ : Fin 14) = u ∨ (⟨w,input⟩ : Fin 14) = v) =
          decide ((⟨w,input⟩ : Fin 14) = u ∨ (⟨w,input⟩ : Fin 14) = u)
        simp [nv]
      · let k := w - 14
        have hk : k < C.gates.length := by omega
        have wi : w = 14 + k := by omega
        obtain ⟨a,b,ins,_,ha,hb⟩ := (facts k hk).2
        obtain ⟨bv,nv⟩ := recurrence k hk a b ins ha hb
        rw [wi, nv] at zero
        obtain ⟨la,lb⟩ := numBound C.gates[k].op (N v a) (N v b)
        rw [zero] at la lb
        rw [wi, bv, bv, ih a (by omega) (by omega) (by omega),
          ih b (by omega) (by omega) (by omega)]
  have flipCost (u v : Fin 14) (k : ℕ) (hop : (gateAt C k).op = .and)
      (hy : gateVal 14 C k (pairInput u v) = true)
      (hn : ∀ b : Fin 2,
        PEqualNP.CleanedNonEdge.wireVal 14 C (opnd C k b) (pairInput u u) = false) :
      2 ≤ N v (14+k) := by
    have hk : k < C.gates.length := by
      by_contra h
      change (scan G C.gates (List.ofFn (pairInput u v))).getD (14+k) false = true at hy
      rw [List.getD_eq_default _ _ (by rw [scanLength, List.length_ofFn]; omega)] at hy
      contradiction
    obtain ⟨a,b,ins,_,ha,hb⟩ := (facts k hk).2
    obtain ⟨bv,nv⟩ := recurrence k hk a b ins ha hb
    have sameOp : C.gates[k].op = .and := by simpa only [gateEq k hk] using hop
    have haOp : opnd C k 0 = a := by
      change (gateAt C k).inputs.getD 0 0 = a
      rw [gateEq k hk,ins]
      rfl
    have hbOp : opnd C k 1 = b := by
      change (gateAt C k).inputs.getD 1 0 = b
      rw [gateEq k hk,ins]
      rfl
    have oldA : B (pairInput u u) a = false := by
      have h := hn 0
      rw [haOp] at h
      exact h
    have oldB : B (pairInput u u) b = false := by
      have h := hn 1
      rw [hbOp] at h
      exact h
    change B (pairInput u v) (14+k) = true at hy
    rw [bv] at hy
    have vals : B (pairInput u v) a = true ∧ B (pairInput u v) b = true := by
      simpa only [boolOp, sameOp, if_pos rfl, Bool.and_eq_true] using hy
    have da : 0 < N v a := by
      by_contra h
      have ab := stable u v a (by omega) (by omega)
      rw [vals.1, oldA] at ab
      contradiction
    have db : 0 < N v b := by
      by_contra h
      have ab := stable u v b (by omega) (by omega)
      rw [vals.2, oldB] at ab
      contradiction
    rw [nv]
    simp only [natOp, sameOp, if_pos rfl]
    omega
  let coneF (cs : List (List ℕ)) (g : Gate) :=
    (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14+cs.length))).flatMap
      (fun w => (w-14) :: cs.getD (w-14) [])
  have coneSplit (i k : ℕ) (inside : InCone 14 C i k) :
      ∃ hk : k < C.gates.length, ∃ w ∈ C.gates[k].inputs,
        14 ≤ w ∧ w < 14 + k ∧ (i = w-14 ∨ InCone 14 C i (w-14)) := by
    change i ∈ (scan coneF C.gates []).getD k [] at inside
    have hk : k < C.gates.length := by
      by_contra beyond
      rw [List.getD_eq_default _ _ (by rw [scanLength]; simpa using Nat.le_of_not_gt beyond)] at inside
      contradiction
    let pre := scan coneF (C.gates.take k) []
    have preLen : pre.length = k := by simp [pre, scanLength, Nat.min_eq_left hk.le]
    have split : scan coneF C.gates [] = scan coneF (C.gates[k] :: C.gates.drop (k+1)) pre := by
      have ht := List.take_append_drop k C.gates
      conv_lhs => rw [← ht, scanAppend, List.drop_eq_getElem_cons hk]
    have current : (scan coneF C.gates []).getD k [] = coneF pre C.gates[k] := by
      have lt : k < (pre ++ [coneF pre C.gates[k]]).length := by simp [preLen]
      rw [split, scanCons, scanPrefix _ _ _ _ _ lt,
        List.getD_append_right _ _ _ _ (by omega), preLen, Nat.sub_self] <;> rfl
    rw [current] at inside
    change i ∈ ((C.gates[k].inputs.filter (fun w => decide (14 ≤ w ∧ w < 14+pre.length))).flatMap
      (fun w => (w-14) :: pre.getD (w-14) [])) at inside
    obtain ⟨w, sub, member⟩ := List.mem_flatMap.mp inside
    obtain ⟨read, hw⟩ := List.mem_filter.mp sub
    obtain ⟨lo, hi⟩ := of_decide_eq_true hw
    have hi' : w < 14+k := by simpa only [preLen] using hi
    refine ⟨hk, w, read, lo, hi', ?_⟩
    rcases List.mem_cons.mp member with eq | old
    · exact Or.inl eq
    · right
      change i ∈ (scan coneF C.gates []).getD (w-14) []
      rw [split, scanPrefix _ _ _ _ _ (by omega)]
      exact old
  have degreeAlong (v : Fin 14) (i k : ℕ) (path : InCone 14 C i k) :
      N v (14+i) ≤ N v (14+k) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      obtain ⟨hk,w,hmem,lo,hi,last⟩ := coneSplit i k path
      obtain ⟨a,b,ins,_,ha,hb⟩ := (facts k hk).2
      have parent : N v w ≤ N v (14+k) := by
        have degreeEq := (recurrence k hk a b ins ha hb).2 v
        have bound := numBound C.gates[k].op (N v a) (N v b)
        rw [← degreeEq] at bound
        rw [ins] at hmem
        rcases (show w = a ∨ w = b by simpa using hmem) with eq | eq
        · simpa only [eq] using bound.1
        · simpa only [eq] using bound.2
      have wire : 14 + (w-14) = w := by omega
      rcases last with eq | inside
      · simpa only [eq, wire] using parent
      · have sub := ih (w-14) (by omega) inside
        apply sub.trans
        simpa only [wire] using parent
  have outputBound : 14 ≤ C.output := by
    by_contra h
    have lt : C.output < 14 := by omega
    let t : Fin 14 := ⟨C.output, lt⟩
    have w : C.eval (List.ofFn (pairInput t t)) = true := by
      change B (pairInput t t) C.output = true
      rw [bRaw _ _ lt]
      change decide (t = t ∨ t = t) = true
      simp
    obtain ⟨p,l,_,haveP,haveL⟩ := (hfun _).mp w
    change decide (Fin.castAdd 7 p = t ∨ Fin.castAdd 7 p = t) = true at haveP
    change decide (Fin.natAdd 7 l = t ∨ Fin.natAdd 7 l = t) = true at haveL
    have eqP : Fin.castAdd 7 p = t := by simpa only [or_self, decide_eq_true_eq] using haveP
    have eqL : Fin.natAdd 7 l = t := by simpa only [or_self, decide_eq_true_eq] using haveL
    have apart : ∀ p l : Fin 7, Fin.castAdd 7 p ≠ Fin.natAdd 7 l := by decide +kernel
    exact apart p l (eqP.trans eqL.symm)
  have outputDegree (v : Fin 14) (w : ℕ) (hw : 14 + w = C.output ∨ InCone 14 C w (C.output-14))
      (low : 2 ≤ N v (14+w)) : 2 ≤ C.lineDeg 14 {v.val} := by
    change 2 ≤ N v C.output
    rcases hw with eq | cone
    · rwa [eq] at low
    · have h := degreeAlong v w (C.output-14) cone
      have eq : 14 + (C.output-14) = C.output := by omega
      exact low.trans (eq ▸ h)
  have dl : 2 ≤ C.lineDeg 14 {7} := outputDegree 7 i iOut (flipCost 0 7 i iAnd iYes iOff)
  have pairSwap : pairInput (7 : Fin 14) 0 = pairInput 0 7 := by
    funext x
    change decide (x = (7 : Fin 14) ∨ x = 0) = decide (x = 0 ∨ x = 7)
    by_cases h0 : x = 0 <;> by_cases h7 : x = 7 <;> simp [h0, h7]
  have dp : 2 ≤ C.lineDeg 14 {0} := by
    apply outputDegree 0 j jOut
    apply flipCost 7 0 j jAnd _ jOff
    exact pairSwap.symm ▸ jYes
  have noFormula (D : Circuit) (lowP : 2 ≤ D.lineDeg 14 {0}) (lowL : 2 ≤ D.lineDeg 14 {7})
      (form : HasLineDegree 14 {0} D 1 ∨ HasLineDegree 14 {7} D 1) : False := by
    rcases form with hp | hl
    · exact Nat.not_le_of_lt lowP hp
    · exact Nat.not_le_of_lt lowL hl
  by_cases ht : ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
  · exact noFormula C dp dl (rigid C hsize ao distinct correct ht)
  · obtain ⟨D, ⟨sizeD, aoD, nodupD, evalD⟩, treeD, loD, hiD⟩ :=
      unshare C ⟨hsize, ao, distinct, correct⟩ ht
        ⟨i, j, chain, ⟨iAnd, iOut, iYes, iOff⟩, ⟨jAnd, jOut, jYes, jOff⟩⟩ dp dl
    exact noFormula D loD hiD (rigid D sizeD aoD nodupD evalD treeD)
