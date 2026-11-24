import PEqualNP.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic

namespace PEqualNP.Outside.L_meta_4616.PathAccount

open PEqualNP.MetaComplexity

def Positive {n : ℕ} : DMFormula n → Prop
  | .lit _ sign => sign = true
  | .and a b => Positive a ∧ Positive b
  | .or a b => Positive a ∧ Positive b

end PEqualNP.Outside.L_meta_4616.PathAccount

namespace PEqualNP.Outside.L_meta_4616.PathAccount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

private def foldWires {α : Type} (step : List α → Gate → α)
    (gs : List Gate) (initial : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) initial

private theorem foldWires_length {α : Type} (step : List α → Gate → α)
    (gs : List Gate) (initial : List α) :
    (foldWires step gs initial).length = initial.length + gs.length := by
  induction gs generalizing initial with
  | nil => simp [foldWires]
  | cons g gs ih =>
      rw [show foldWires step (g :: gs) initial =
        foldWires step gs (initial ++ [step initial g]) from rfl, ih]
      simp only [List.length_append, List.length_nil, List.length_cons]
      omega

private theorem foldWires_append {α : Type} (step : List α → Gate → α)
    (first rest : List Gate) (initial : List α) :
    foldWires step (first ++ rest) initial =
      foldWires step rest (foldWires step first initial) := by
  simp [foldWires, List.foldl_append]

private theorem foldWires_getD_input {α : Type} (step : List α → Gate → α)
    (gs : List Gate) (initial : List α) (default : α) {i : ℕ} (hi : i < initial.length) :
    (foldWires step gs initial).getD i default = initial.getD i default := by
  induction gs generalizing initial with
  | nil => rfl
  | cons g gs ih =>
      change (foldWires step gs (initial ++ [step initial g])).getD i default = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private theorem foldWires_getD_take {α : Type} (step : List α → Gate → α)
    (gs : List Gate) (initial : List α) (default : α)
    {j i : ℕ} (hj : j ≤ gs.length) (hi : i < initial.length + j) :
    (foldWires step gs initial).getD i default =
      (foldWires step (gs.take j) initial).getD i default := by
  have he := List.take_append_drop j gs
  conv_lhs => rw [← he, foldWires_append]
  apply foldWires_getD_input
  simpa only [foldWires_length, List.length_take, Nat.min_eq_left hj] using hi

private theorem foldWires_getD_gate {α : Type} (step : List α → Gate → α)
    (gs : List Gate) (initial : List α) (default : α)
    {j : ℕ} {g : Gate} (hg : gs[j]? = some g) :
    (foldWires step gs initial).getD (initial.length+j) default =
      step (foldWires step (gs.take j) initial) g := by
  obtain ⟨hj, hjg⟩ := List.getElem?_eq_some_iff.mp hg
  rw [foldWires_getD_take step gs initial default
      (show j+1 ≤ gs.length by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hj, foldWires_append, hjg]
  let front := foldWires step (gs.take j) initial
  have hl : front.length = initial.length+j := by
    simp [front, foldWires_length, Nat.min_eq_left (Nat.le_of_lt hj)]
  change (front ++ [step front g]).getD (initial.length+j) default = step front g
  rw [← hl, List.getD_append_right _ _ _ _ (le_refl _)]
  simp

private def countStep (weight : ℕ → ℕ) (w : List ℕ) (g : Gate) : ℕ :=
  weight w.length + (g.inputs.map fun i => w.getD i 0).sum

def wireCount (n : ℕ) (C : Circuit) (weight : ℕ → ℕ) (wire : ℕ) : ℕ :=
  (foldWires (countStep weight) C.gates (List.replicate n 0)).getD wire 0

def postedPathCount (n : ℕ) (C : Circuit) (i : Fin C.size) : ℕ :=
  wireCount n C (fun w => if w = n + (i : ℕ) then 1 else 0) C.output

theorem postedPathCount_eq (n : ℕ) (C : Circuit) (i : Fin C.size) :
    postedPathCount n C i =
      (C.gates.foldl (fun w g => w ++
        [(if w.length = n + (i : ℕ) then 1 else 0) +
          (g.inputs.map fun j => w.getD j 0).sum]) (List.replicate n 0)).getD C.output 0 := rfl

private theorem wireCount_input {n : ℕ} {C : Circuit} {weight : ℕ → ℕ}
    {w : ℕ} (hw : w < n) : wireCount n C weight w = 0 := by
  unfold wireCount
  rw [foldWires_getD_input _ _ _ _ (by simpa using hw)]
  exact List.getD_replicate 0 hw

private theorem wireCount_gate {n : ℕ} {C : Circuit} (weight : ℕ → ℕ)
    {j : ℕ} {g : Gate} {a b : ℕ} (hg : C.gates[j]? = some g) (hin : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    wireCount n C weight (n+j) =
      weight (n+j) + (wireCount n C weight a + wireCount n C weight b) := by
  have hj : j ≤ C.gates.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hg).1
  have hlen : (List.replicate n (0 : ℕ)).length = n := by simp
  unfold wireCount
  have hgFold := foldWires_getD_gate (countStep weight) C.gates (List.replicate n 0) 0 hg
  rw [hlen] at hgFold
  rw [hgFold]
  have hA := foldWires_getD_take (countStep weight) C.gates (List.replicate n 0) 0 hj
    (i := a) (by simpa using ha)
  have hB := foldWires_getD_take (countStep weight) C.gates (List.replicate n 0) 0 hj
    (i := b) (by simpa using hb)
  simp only [countStep, hin, foldWires_length, List.length_replicate, List.length_take,
    Nat.min_eq_left hj, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [← hA, ← hB]

def BinarySorted (n : ℕ) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a,b] ∧ a < b ∧ b < n+j

private theorem countAll_eq_sum {n : ℕ} {C : Circuit} (wf : BinarySorted n C)
    (w : ℕ) (hw : w < n+C.size) :
    wireCount n C (fun _ => 1) w =
      ∑ i : Fin C.size, wireCount n C (fun k => if k = n+(i : ℕ) then 1 else 0) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · simp [wireCount_input hin]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by
        simpa only [Circuit.size, Nat.add_lt_add_iff_left] using hw
      obtain ⟨g, hg⟩ : ∃ g, C.gates[j]? = some g :=
        ⟨C.gates[j], List.getElem?_eq_getElem hj⟩
      obtain ⟨a,b,hab,ha,hb⟩ := wf j g hg
      have ha' : a < n+j := ha.trans hb
      rw [wireCount_gate _ hg hab ha' hb, ih a ha' (ha'.trans hw), ih b hb (hb.trans hw)]
      simp_rw [wireCount_gate _ hg hab ha' hb]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have eq : ∀ i : Fin C.size, n+j = n+(i : ℕ) ↔ i = ⟨j,hj⟩ := by
        intro i
        constructor
        · intro h
          exact Fin.ext (Nat.add_left_cancel h.symm)
        · rintro rfl
          rfl
      simp only [eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def formulaStep {n : ℕ} (fallback : Fin n) (w : List (DMFormula n))
    (g : Gate) : DMFormula n :=
  match g.inputs with
  | [a,b] =>
      let A := w.getD a (.lit fallback true)
      let B := w.getD b (.lit fallback true)
      match g.op with
      | .and => .and A B
      | .or => .or A B
      | _ => .lit fallback true
  | _ => .lit fallback true

private def formulaWire {n : ℕ} (fallback : Fin n) (C : Circuit) (w : ℕ) : DMFormula n :=
  (foldWires (formulaStep fallback) C.gates (List.ofFn fun i => .lit i true)).getD w
    (.lit fallback true)

private theorem formula_input {n : ℕ} (fallback : Fin n) (C : Circuit)
    {w : ℕ} (hw : w < n) : formulaWire fallback C w = .lit ⟨w,hw⟩ true := by
  unfold formulaWire
  have hget : w < (List.ofFn fun i : Fin n => DMFormula.lit i true).length := by simpa using hw
  rw [foldWires_getD_input _ _ _ _ hget, List.getD_eq_getElem _ _ hget]
  simp

private theorem formula_gate {n : ℕ} (fallback : Fin n) (C : Circuit)
    {j : ℕ} {g : Gate} {a b : ℕ} (hg : C.gates[j]? = some g) (hin : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    (g.op = .and → formulaWire fallback C (n+j) =
      .and (formulaWire fallback C a) (formulaWire fallback C b)) ∧
    (g.op = .or → formulaWire fallback C (n+j) =
      .or (formulaWire fallback C a) (formulaWire fallback C b)) := by
  let front : List (DMFormula n) := List.ofFn fun i => .lit i true
  let defval : DMFormula n := .lit fallback true
  have hj : j ≤ C.gates.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hg).1
  have hlen : front.length = n := by simp [front]
  change
    (g.op = .and → (foldWires (formulaStep fallback) C.gates front).getD (n+j) defval =
      .and ((foldWires (formulaStep fallback) C.gates front).getD a defval)
        ((foldWires (formulaStep fallback) C.gates front).getD b defval)) ∧
    (g.op = .or → (foldWires (formulaStep fallback) C.gates front).getD (n+j) defval =
      .or ((foldWires (formulaStep fallback) C.gates front).getD a defval)
        ((foldWires (formulaStep fallback) C.gates front).getD b defval))
  have hgFold := foldWires_getD_gate (formulaStep fallback) C.gates front defval hg
  rw [hlen] at hgFold
  have hA := foldWires_getD_take (formulaStep fallback) C.gates front defval hj
    (i := a) (by simpa [hlen] using ha)
  have hB := foldWires_getD_take (formulaStep fallback) C.gates front defval hj
    (i := b) (by simpa [hlen] using hb)
  dsimp only [defval] at hA hB
  constructor <;> intro hop <;> rw [hgFold] <;>
    simp only [formulaStep, hin, hop, defval, ← hA, ← hB]

private theorem bool_input {n : ℕ} (x : Fin n → Bool) (C : Circuit)
    {w : ℕ} (hw : w < n) : (C.wires (List.ofFn x)).getD w false = x ⟨w,hw⟩ := by
  change (foldWires (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x)).getD w false = _
  have hget : w < (List.ofFn x).length := by simpa using hw
  rw [foldWires_getD_input _ _ _ _ hget, List.getD_eq_getElem _ _ hget]
  simp

private theorem bool_gate {n : ℕ} (x : Fin n → Bool) (C : Circuit)
    {j : ℕ} {g : Gate} {a b : ℕ} (hg : C.gates[j]? = some g) (hin : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    (C.wires (List.ofFn x)).getD (n+j) false =
      g.op.eval [(C.wires (List.ofFn x)).getD a false, (C.wires (List.ofFn x)).getD b false] := by
  let eval (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
  let front := List.ofFn x
  have hj : j ≤ C.gates.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hg).1
  have hlen : front.length = n := by simp [front]
  change (foldWires eval C.gates front).getD (n+j) false =
    g.op.eval [(foldWires eval C.gates front).getD a false, (foldWires eval C.gates front).getD b false]
  have hgFold := foldWires_getD_gate eval C.gates front false hg
  rw [hlen] at hgFold
  have hA := foldWires_getD_take eval C.gates front false hj (i := a) (by simpa [hlen] using ha)
  have hB := foldWires_getD_take eval C.gates front false hj (i := b) (by simpa [hlen] using hb)
  rw [hgFold]
  simp only [eval, hin, List.map_cons, List.map_nil, ← hA, ← hB]

private theorem wireFormula_spec {n : ℕ} (fallback : Fin n) (C : Circuit)
    (hm : Monotone2 C) (wf : BinarySorted n C)
    (w : ℕ) (hw : w < n+C.size) :
    Positive (formulaWire fallback C w) ∧
      (formulaWire fallback C w).leaves = 1 + wireCount n C (fun _ => 1) w ∧
      ∀ x, (formulaWire fallback C w).eval x = (C.wires (List.ofFn x)).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · rw [formula_input fallback C hin, wireCount_input hin]
      exact ⟨rfl, rfl, fun x => (bool_input x C hin).symm⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by
        simpa only [Circuit.size, Nat.add_lt_add_iff_left] using hw
      obtain ⟨g, hg⟩ : ∃ g, C.gates[j]? = some g :=
        ⟨C.gates[j], List.getElem?_eq_getElem hj⟩
      obtain ⟨a,b,hab,ha,hb⟩ := wf j g hg
      have ha' : a < n+j := ha.trans hb
      obtain ⟨pa,la,ea⟩ := ih a ha' (ha'.trans hw)
      obtain ⟨pb,lb,eb⟩ := ih b hb (hb.trans hw)
      have hop : g.op = .and ∨ g.op = .or := by
        simpa using (hm g (List.mem_of_getElem? hg)).1
      have eq := formula_gate fallback C hg hab ha' hb
      rw [wireCount_gate _ hg hab ha' hb]
      rcases hop with andOp | orOp
      · rw [eq.1 andOp]
        refine ⟨⟨pa,pb⟩, ?_, fun x => ?_⟩
        · simp only [DMFormula.leaves, la, lb]
          omega
        · rw [DMFormula.eval, ea x, eb x, bool_gate x C hg hab ha' hb, andOp]
          simp [GateOp.eval]
      · rw [eq.2 orOp]
        refine ⟨⟨pa,pb⟩, ?_, fun x => ?_⟩
        · simp only [DMFormula.leaves, la, lb]
          omega
        · rw [DMFormula.eval, ea x, eb x, bool_gate x C hg hab ha' hb, orOp]
          simp [GateOp.eval]

theorem existsUnfoldedFormula {n : ℕ} (hn : 0 < n) (C : Circuit)
    (hm : Monotone2 C) (ho : C.output < n+C.size) (wf : BinarySorted n C) :
    ∃ F : DMFormula n, Positive F ∧
      (∀ x, F.eval x = circuitFun n C x) ∧
      F.leaves = 1 + ∑ i : Fin C.size, postedPathCount n C i := by
  let fallback : Fin n := ⟨0,hn⟩
  obtain ⟨pos, count, eval⟩ := wireFormula_spec fallback C hm wf C.output ho
  refine ⟨formulaWire fallback C C.output, pos, eval, ?_⟩
  rw [count, countAll_eq_sum wf C.output ho]
  rfl

end PEqualNP.Outside.L_meta_4616.PathAccount

namespace PEqualNP.Outside.L_meta_4616

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

abbrev IncEdge (inc : Fin N → Fin N → Prop) :=
  {e : Fin N × Fin N // inc e.1 e.2}

def positiveInput {inc : Fin N → Fin N → Prop} (e : IncEdge inc) (v : Fin (N+N)) : Bool :=
  decide (v = Fin.castAdd N e.1.1 ∨ v = Fin.natAdd N e.1.2)

def negativeInput (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (y : Option (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases
    (fun p => match y with
      | none => true
      | some l => decide (¬ inc p l))
    (fun l => decide (y = some l))

lemma negativePoint (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (y : Option (Fin N)) (p : Fin N) :
    negativeInput inc y (Fin.castAdd N p) =
      (match y with | none => true | some l => decide (¬ inc p l)) := by
  simp only [negativeInput, Fin.addCases_left]

lemma negativeLine (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (y : Option (Fin N)) (l : Fin N) :
    negativeInput inc y (Fin.natAdd N l) = decide (y = some l) := by
  simp only [negativeInput, Fin.addCases_right]

lemma negativeLineCard (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (y : Option (Fin N)) :
    Fintype.card {l : Fin N // negativeInput inc y (Fin.natAdd N l) = true} ≤ 1 := by
  apply Fintype.card_le_one_iff.mpr
  intro l m
  have hl : y = some l.val := of_decide_eq_true ((negativeLine inc y l.val).symm.trans l.property)
  have hm : y = some m.val := of_decide_eq_true ((negativeLine inc y m.val).symm.trans m.property)
  exact Subtype.ext (Option.some.inj (hl.symm.trans hm))

lemma negativeNoIncidence (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (y : Option (Fin N)) :
    ¬ ∃ p l : Fin N, inc p l ∧ negativeInput inc y (Fin.castAdd N p) = true ∧
      negativeInput inc y (Fin.natAdd N l) = true := by
  rintro ⟨p,l,hinc,hpoint,hline⟩
  have hy : y = some l := of_decide_eq_true ((negativeLine inc y l).symm.trans hline)
  subst y
  rw [negativePoint] at hpoint
  exact (of_decide_eq_true hpoint) hinc

lemma winningInput {inc : Fin N → Fin N → Prop} [DecidableRel inc]
    {e : IncEdge inc} {y : Option (Fin N)} {v : Fin (N+N)}
    (hpos : positiveInput e v = true) (hneg : negativeInput inc y v = false) :
    (v = Fin.castAdd N e.val.1 ∧ ∃ l : Fin N, y = some l ∧ inc e.val.1 l) ∨
    (v = Fin.natAdd N e.val.2 ∧ y ≠ some e.val.2) := by
  rcases of_decide_eq_true hpos with hv | hv
  · left
    refine ⟨hv, ?_⟩
    rw [hv,negativePoint] at hneg
    cases y with
    | none => contradiction
    | some l =>
      exact ⟨l,rfl,not_not.mp (of_decide_eq_false hneg)⟩
  · right
    refine ⟨hv, ?_⟩
    rw [hv,negativeLine] at hneg
    exact of_decide_eq_false hneg

noncomputable def edgesByLine (inc : Fin N → Fin N → Prop) :
    IncEdge inc ≃ (Σ l : Fin N, {p : Fin N // inc p l}) where
  toFun e := ⟨e.val.2,e.val.1,e.property⟩
  invFun e := ⟨(e.2.val,e.1),e.2.property⟩
  left_inv := by rintro ⟨⟨p,l⟩,hi⟩; rfl
  right_inv := by rintro ⟨l,⟨p,hi⟩⟩; rfl

lemma incidenceCard (inc : Fin N → Fin N → Prop) [DecidableRel inc] {q : ℕ}
    (hline : ∀ l : Fin N, Fintype.card {p : Fin N // inc p l} = q+1) :
    Fintype.card (IncEdge inc) = N*(q+1) := by
  rw [Fintype.card_congr (edgesByLine inc),Fintype.card_sigma]
  simp [hline]

lemma positiveCircuit {inc : Fin N → Fin N → Prop} {C : Circuit}
    (hpos : ∀ p l : Fin N, inc p l → circuitFun (N+N) C
      (fun v => decide (v = Fin.castAdd N p ∨ v = Fin.natAdd N l)) = true)
    (e : IncEdge inc) : circuitFun (N+N) C (positiveInput e) = true :=
  hpos e.val.1 e.val.2 e.property

lemma negativeCircuit {inc : Fin N → Fin N → Prop} [DecidableRel inc] {C : Circuit}
    {q : ℕ} (hq : 1 ≤ q)
    (hneg : ∀ x : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, inc p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N+N) C x = false)
    (y : Option (Fin N)) : circuitFun (N+N) C (negativeInput inc y) = false :=
  hneg _ ((negativeLineCard inc y).trans hq) (negativeNoIncidence inc y)

def inputTag (v : Fin (N+N)) : Fin N ⊕ Fin N :=
  Fin.addCases Sum.inl Sum.inr v

lemma positiveTag {inc : Fin N → Fin N → Prop} {e : IncEdge inc} {v : Fin (N+N)}
    (h : positiveInput e v = true) :
    inputTag v = .inl e.val.1 ∨ inputTag v = .inr e.val.2 := by
  rcases of_decide_eq_true h with rfl | rfl
  · left
    rw [inputTag, Fin.addCases_left]
  · right
    rw [inputTag, Fin.addCases_right]

lemma negativePointTag {inc : Fin N → Fin N → Prop} [DecidableRel inc]
    {y : Option (Fin N)} {v : Fin (N+N)} {p : Fin N}
    (hv : inputTag v = .inl p) (h : negativeInput inc y v = false) :
    ∃ l, y = some l ∧ inc p l := by
  have hv' : v = Fin.castAdd N p := by
    refine Fin.addCases ?_ ?_ v hv
    · intro p' he
      rw [inputTag,Fin.addCases_left,Sum.inl.injEq] at he
      exact congrArg (Fin.castAdd N) he
    · intro l he
      rw [inputTag,Fin.addCases_right] at he
      contradiction
  rw [hv',negativePoint] at h
  cases y with
  | none => contradiction
  | some l => exact ⟨l,rfl,not_not.mp (of_decide_eq_false h)⟩

lemma negativeLineTag {inc : Fin N → Fin N → Prop} [DecidableRel inc]
    {y : Option (Fin N)} {v : Fin (N+N)} {l : Fin N}
    (hv : inputTag v = .inr l) (h : negativeInput inc y v = false) : y ≠ some l := by
  have hv' : v = Fin.natAdd N l := by
    refine Fin.addCases ?_ ?_ v hv
    · intro p he
      rw [inputTag,Fin.addCases_left] at he
      contradiction
    · intro l' he
      rw [inputTag,Fin.addCases_right,Sum.inr.injEq] at he
      exact congrArg (Fin.natAdd N) he
  rw [hv',negativeLine] at h
  exact of_decide_eq_false h

lemma uniqueMeet {inc : Fin N → Fin N → Prop}
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, inc p l ∧ inc p' l)
    (l m : Fin N) (hlm : l ≠ m) (p p' : Fin N)
    (hpl : inc p l) (hpm : inc p m) (hp'l : inc p' l) (hp'm : inc p' m) : p = p' := by
  by_contra ne
  obtain ⟨k,_,hk⟩ := join p p' ne
  exact hlm ((hk l ⟨hpl,hp'l⟩).trans (hk m ⟨hpm,hp'm⟩).symm)

end PEqualNP.Outside.L_meta_4616

namespace PEqualNP.Outside.L_meta_4616.FormulaProtocol

open PEqualNP.MetaComplexity
open PathAccount (Positive)

variable {n : ℕ}

private def joined {a b : ℕ} {α : Type*} (f : Fin a → α) (g : Fin b → α)
    (i : Fin (a+b)) : α :=
  Fin.addCases (motive := fun _ => α) f g i

private theorem joinedLeft {a b : ℕ} {α : Type*}
    (f : Fin a → α) (g : Fin b → α) (i : Fin a) :
    joined f g (Fin.castAdd b i) = f i := Fin.addCases_left i

private theorem joinedRight {a b : ℕ} {α : Type*}
    (f : Fin a → α) (g : Fin b → α) (i : Fin b) :
    joined f g (Fin.natAdd a i) = g i := Fin.addCases_right i

def label : (F : DMFormula n) → Fin F.leaves → Fin n
  | .lit v _, _ => v
  | .and a b, i => joined (label a) (label b) i
  | .or a b, i => joined (label a) (label b) i

def row : (F : DMFormula n) → Fin F.leaves → (Fin n → Bool) → Prop
  | .lit v _, _, x => x v = true
  | .and a b, i, x => joined (fun j => row a j x) (fun j => row b j x) i
  | .or a b, i, x =>
      joined (fun j => a.eval x = true ∧ row a j x)
        (fun j => a.eval x = false ∧ row b j x) i

def column : (F : DMFormula n) → Fin F.leaves → (Fin n → Bool) → Prop
  | .lit v _, _, x => x v = false
  | .and a b, i, x =>
      joined (fun j => a.eval x = false ∧ column a j x)
        (fun j => a.eval x = true ∧ column b j x) i
  | .or a b, i, x => joined (fun j => column a j x) (fun j => column b j x) i

theorem rowLabel (F : DMFormula n) (x : Fin n → Bool) :
    ∀ i : Fin F.leaves, row F i x → x (label F i) = true := by
  induction F with
  | lit _ _ => exact fun _ h => h
  | and a b ih₀ ih₁ =>
    intro i
    refine Fin.addCases (motive := fun j => row (.and a b) j x →
      x (label (.and a b) j) = true) ?_ ?_ i
    · intro j
      simpa only [row,label,joinedLeft] using ih₀ j
    · intro j
      simpa only [row,label,joinedRight] using ih₁ j
  | or a b ih₀ ih₁ =>
    intro i
    refine Fin.addCases (motive := fun j => row (.or a b) j x →
      x (label (.or a b) j) = true) ?_ ?_ i
    · intro j h
      simp only [row,label,joinedLeft] at h ⊢
      exact ih₀ j h.2
    · intro j h
      simp only [row,label,joinedRight] at h ⊢
      exact ih₁ j h.2

theorem columnLabel (F : DMFormula n) (x : Fin n → Bool) :
    ∀ i : Fin F.leaves, column F i x → x (label F i) = false := by
  induction F with
  | lit _ _ => exact fun _ h => h
  | and a b ih₀ ih₁ =>
    intro i
    refine Fin.addCases (motive := fun j => column (.and a b) j x →
      x (label (.and a b) j) = false) ?_ ?_ i
    · intro j h
      simp only [column,label,joinedLeft] at h ⊢
      exact ih₀ j h.2
    · intro j h
      simp only [column,label,joinedRight] at h ⊢
      exact ih₁ j h.2
  | or a b ih₀ ih₁ =>
    intro i
    refine Fin.addCases (motive := fun j => column (.or a b) j x →
      x (label (.or a b) j) = false) ?_ ?_ i
    · intro j
      simpa only [column,label,joinedLeft] using ih₀ j
    · intro j
      simpa only [column,label,joinedRight] using ih₁ j

private theorem uniqueLeft {a b : ℕ} {P : Fin a → Prop} {Q : Fin (a+b) → Prop}
    (h : ∃! i, P i)
    (left : ∀ i, Q (Fin.castAdd b i) ↔ P i)
    (right : ∀ i, ¬ Q (Fin.natAdd a i)) : ∃! i, Q i := by
  obtain ⟨i,hi,unique⟩ := h
  refine ⟨Fin.castAdd b i,(left i).mpr hi,?_⟩
  intro j
  refine Fin.addCases (motive := fun w => Q w → w = Fin.castAdd b i) ?_ ?_ j
  · intro j hj
    exact congrArg (Fin.castAdd b) (unique j ((left j).mp hj))
  · intro j hj
    exact (right j hj).elim

private theorem uniqueRight {a b : ℕ} {P : Fin b → Prop} {Q : Fin (a+b) → Prop}
    (h : ∃! i, P i)
    (left : ∀ i, ¬ Q (Fin.castAdd b i))
    (right : ∀ i, Q (Fin.natAdd a i) ↔ P i) : ∃! i, Q i := by
  obtain ⟨i,hi,unique⟩ := h
  refine ⟨Fin.natAdd a i,(right i).mpr hi,?_⟩
  intro j
  refine Fin.addCases (motive := fun w => Q w → w = Fin.natAdd a i) ?_ ?_ j
  · intro j hj
    exact (left j hj).elim
  · intro j hj
    exact congrArg (Fin.natAdd a) (unique j ((right j).mp hj))

theorem partition (F : DMFormula n) (hF : Positive F) (x y : Fin n → Bool)
    (hx : F.eval x = true) (hy : F.eval y = false) :
    ∃! i : Fin F.leaves, row F i x ∧ column F i y := by
  induction F with
  | lit v sign =>
    have hsign : sign = true := hF
    subst sign
    change ∃! i : Fin 1, row (.lit v true) i x ∧ column (.lit v true) i y
    refine ⟨0,⟨?_,?_⟩,fun _ _ => Subsingleton.elim _ _⟩
    · change x v = true
      simpa [DMFormula.eval] using hx
    · change y v = false
      simpa [DMFormula.eval] using hy
  | and a b ih₀ ih₁ =>
    have hP : Positive a ∧ Positive b := hF
    have hX : a.eval x = true ∧ b.eval x = true := Bool.and_eq_true_iff.mp hx
    cases hA : a.eval y
    · apply uniqueLeft (ih₀ hP.1 hX.1 hA)
      · intro i
        simp [row,column,joinedLeft,hA]
      · intro i
        simp [row,column,joinedRight,hA]
    · have hB : b.eval y = false := by simpa [DMFormula.eval,hA] using hy
      apply uniqueRight (ih₁ hP.2 hX.2 hB)
      · intro i
        simp [row,column,joinedLeft,hA]
      · intro i
        simp [row,column,joinedRight,hA]
  | or a b ih₀ ih₁ =>
    have hP : Positive a ∧ Positive b := hF
    have hY : a.eval y = false ∧ b.eval y = false := Bool.or_eq_false_iff.mp hy
    cases hA : a.eval x
    · have hB : b.eval x = true := by simpa [DMFormula.eval,hA] using hx
      apply uniqueRight (ih₁ hP.2 hB hY.2)
      · intro i
        simp [row,column,joinedLeft,hA]
      · intro i
        simp [row,column,joinedRight,hA]
    · apply uniqueLeft (ih₀ hP.1 hA hY.1)
      · intro i
        simp [row,column,joinedLeft,hA]
      · intro i
        simp [row,column,joinedRight,hA]

end PEqualNP.Outside.L_meta_4616.FormulaProtocol

namespace PEqualNP.Outside.L_meta_4616.Rectangle

abbrev Edge {N : ℕ} (inc : Fin N → Fin N → Prop) :=
  {e : Fin N × Fin N // inc e.1 e.2}

private abbrev K := ZMod 2

theorem rectangleLeafBound {N k : ℕ}
    (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (meet : ∀ l m : Fin N, l ≠ m → ∀ p p' : Fin N,
      inc p l → inc p m → inc p' l → inc p' m → p = p')
    (A : Fin k → Edge inc → Prop) (B : Fin k → Option (Fin N) → Prop)
    (label : Fin k → Sum (Fin N) (Fin N))
    (hpos : ∀ i e, A i e → label i = .inl e.val.1 ∨ label i = .inr e.val.2)
    (hnegP : ∀ i t p, label i = .inl p → B i t → ∃ l, t = some l ∧ inc p l)
    (hnegL : ∀ i t l, label i = .inr l → B i t → t ≠ some l)
    (hpart : ∀ e t, ∃! i, A i e ∧ B i t) :
    Fintype.card (Edge inc) ≤ k := by
  classical
  let E := Edge inc
  let pick (e : E) (t : Option (Fin N)) := Classical.choose (hpart e t)
  have hPick (e : E) (t : Option (Fin N)) :
      (A (pick e t) e ∧ B (pick e t) t) ∧
        ∀ i, (A i e ∧ B i t) → i = pick e t :=
    Classical.choose_spec (hpart e t)
  let agg (a : E → K) (i : Fin k) := ∑ e : E, if A i e then a e else 0
  have eqSum (a : E → K) (t : Option (Fin N)) (v : Sum (Fin N) (Fin N)) :
      (∑ i : Fin k, if B i t ∧ label i = v then agg a i else 0) =
        ∑ e : E, if label (pick e t) = v then a e else 0 := by
    calc
      _ = ∑ i : Fin k, ∑ e : E,
          if (A i e ∧ B i t) ∧ label i = v then a e else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hb : B i t <;> by_cases hv : label i = v <;> simp [agg, hb, hv]
      _ = ∑ e : E, ∑ i : Fin k,
          if (A i e ∧ B i t) ∧ label i = v then a e else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_eq_single (pick e t)]
        · simp [(hPick e t).1]
        · intro i _ hi
          have neq : ¬ (A i e ∧ B i t) := fun h => hi ((hPick e t).2 i h)
          simp [neq]
        · simp
  have zeroKernel (a : E → K) (ha : ∀ i, agg a i = 0) : ∀ e, a e = 0 := by
    let f (e : E) (t : Option (Fin N)) : K :=
      if label (pick e t) = .inl e.val.1 then a e else 0
    let g (e : E) (t : Option (Fin N)) : K :=
      if label (pick e t) = .inr e.val.2 then a e else 0
    have choice (e : E) (t : Option (Fin N)) :
        label (pick e t) = .inl e.val.1 ∨ label (pick e t) = .inr e.val.2 :=
      hpos _ e (hPick e t).1.1
    have f_add_g (e : E) (t : Option (Fin N)) : f e t + g e t = a e := by
      rcases choice e t with h | h <;> simp [f, g, h]
    have f_zero (e : E) (t : Option (Fin N))
        (hn : ¬ ∃ l, t = some l ∧ inc e.val.1 l) : f e t = 0 := by
      have hn' : label (pick e t) ≠ .inl e.val.1 :=
        fun hh => hn (hnegP _ _ _ hh (hPick e t).1.2)
      simp [f, hn']
    have g_none (e : E) : g e none = a e := by
      have hz : f e none = 0 := f_zero e none (by simp)
      simpa [hz] using f_add_g e none
    have f_on (e : E) : f e (some e.val.2) = a e := by
      have hn : label (pick e (some e.val.2)) ≠ .inr e.val.2 :=
        fun he => hnegL _ _ _ he (hPick e _).1.2 rfl
      have hg : g e (some e.val.2) = 0 := by simp [g, hn]
      simpa [hg] using f_add_g e (some e.val.2)
    have total (t : Option (Fin N)) (v : Sum (Fin N) (Fin N)) :
        (∑ e : E, if label (pick e t) = v then a e else 0) = 0 := by
      rw [← eqSum a t v]
      simp [ha]
    have row (t : Option (Fin N)) (p : Fin N) :
        (∑ e : E, if e.val.1 = p then f e t else 0) = 0 := by
      calc
        _ = ∑ e : E, if label (pick e t) = .inl p then a e else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          rcases choice e t with h | h
          · simp [f, h]
          · simp [f, h]
        _ = 0 := total t (.inl p)
    have colG (t : Option (Fin N)) (l : Fin N) :
        (∑ e : E, if e.val.2 = l then g e t else 0) = 0 := by
      calc
        _ = ∑ e : E, if label (pick e t) = .inr l then a e else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          rcases choice e t with h | h
          · simp [g, h]
          · simp [g, h]
        _ = 0 := total t (.inr l)
    have colA (l : Fin N) :
        (∑ e : E, if e.val.2 = l then a e else 0) = 0 := by
      simpa only [g_none] using colG none l
    have colF (t : Option (Fin N)) (l : Fin N) :
        (∑ e : E, if e.val.2 = l then f e t else 0) = 0 := by
      have heq : (∑ e : E, if e.val.2 = l then a e else 0) =
          (∑ e : E, if e.val.2 = l then f e t else 0) +
            ∑ e : E, if e.val.2 = l then g e t else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : e.val.2 = l <;> simp [h, f_add_g]
      simpa [colG, colA] using heq.symm
    have offLine (e : E) (l : Fin N) (hd : e.val.2 ≠ l) (hi : inc e.val.1 l) :
        f e (some l) = 0 := by
      have hsum := colF (some l) e.val.2
      rw [Finset.sum_eq_single e] at hsum
      · simpa using hsum
      · intro e' _ hne
        by_cases hs : e'.val.2 = e.val.2
        · have hh : ¬ inc e'.val.1 l := by
            intro hie
            have hp : e'.val.1 = e.val.1 :=
              meet _ _ hd _ _ (hs ▸ e'.property) hie e.property hi
            apply hne
            exact Subtype.ext (Prod.ext hp hs)
          have hz : f e' (some l) = 0 := f_zero e' (some l) (by simpa using hh)
          simp [hs, hz]
        · simp [hs]
      · simp
    intro e
    have hsum := row (some e.val.2) e.val.1
    rw [Finset.sum_eq_single e] at hsum
    · simpa [f_on] using hsum
    · intro e' _ hne
      by_cases hp : e'.val.1 = e.val.1
      · have hl : e'.val.2 ≠ e.val.2 := fun hl => hne (Subtype.ext (Prod.ext hp hl))
        have hz : f e' (some e.val.2) = 0 := offLine e' e.val.2 hl (hp ▸ e.property)
        simp [hp, hz]
      · simp [hp]
    · simp
  have inj : Function.Injective agg := by
    intro a b hab
    have hz (i : Fin k) : agg (a - b) i = 0 := by
      have heq : agg (a - b) i = agg a i - agg b i := by
        simp only [agg, ← Finset.sum_sub_distrib, Pi.sub_apply]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : A i e <;> simp [h]
      rw [heq, hab, sub_self]
    funext e
    exact sub_eq_zero.mp (zeroKernel (a - b) hz e)
  have hcard := Fintype.card_le_of_injective agg inj
  have hpow : 2 ^ Fintype.card E ≤ 2 ^ k := by
    simpa [Fintype.card_fun, K, ZMod.card] using hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

end PEqualNP.Outside.L_meta_4616.Rectangle

namespace PEqualNP.Outside.L_meta_4616

open PEqualNP.MetaComplexity

theorem formulaIncidenceBound {N : ℕ}
    (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (meet : ∀ l m : Fin N, l ≠ m → ∀ p p' : Fin N,
      inc p l → inc p m → inc p' l → inc p' m → p = p')
    (F : DMFormula (N + N)) (hF : PathAccount.Positive F)
    (hyes : ∀ e : IncEdge inc, F.eval (positiveInput e) = true)
    (hno : ∀ t, F.eval (negativeInput inc t) = false) :
    Fintype.card (IncEdge inc) ≤ F.leaves := by
  let decode (v : Fin (N+N)) : Sum (Fin N) (Fin N) :=
    Fin.addCases (motive := fun _ => Sum (Fin N) (Fin N)) Sum.inl Sum.inr v
  have decodePoint (p : Fin N) : decode (Fin.castAdd N p) = .inl p := Fin.addCases_left p
  have decodeLine (l : Fin N) : decode (Fin.natAdd N l) = .inr l := Fin.addCases_right l
  have pointOfDecode (v : Fin (N+N)) (p : Fin N)
      (h : decode v = .inl p) : v = Fin.castAdd N p := by
    induction v using Fin.addCases with
    | left p' =>
      rw [decodePoint] at h
      exact congrArg (Fin.castAdd N) (Sum.inl.inj h)
    | right l =>
      rw [decodeLine] at h
      contradiction
  have lineOfDecode (v : Fin (N+N)) (l : Fin N)
      (h : decode v = .inr l) : v = Fin.natAdd N l := by
    induction v using Fin.addCases with
    | left p =>
      rw [decodePoint] at h
      contradiction
    | right l' =>
      rw [decodeLine] at h
      exact congrArg (Fin.natAdd N) (Sum.inr.inj h)
  refine Rectangle.rectangleLeafBound inc meet
    (fun i e => FormulaProtocol.row F i (positiveInput e))
    (fun i t => FormulaProtocol.column F i (negativeInput inc t))
    (fun i => decode (FormulaProtocol.label F i)) ?_ ?_ ?_ ?_
  · intro i e hi
    have hon := FormulaProtocol.rowLabel F (positiveInput e) i hi
    rcases of_decide_eq_true hon with h | h
    · exact Or.inl ((congrArg decode h).trans (decodePoint _))
    · exact Or.inr ((congrArg decode h).trans (decodeLine _))
  · intro i t p h hi
    have off := FormulaProtocol.columnLabel F (negativeInput inc t) i hi
    rw [pointOfDecode _ p h, negativePoint] at off
    cases t with
    | none => contradiction
    | some l => exact ⟨l, rfl, not_not.mp (of_decide_eq_false off)⟩
  · intro i t l h hi
    have off := FormulaProtocol.columnLabel F (negativeInput inc t) i hi
    rw [lineOfDecode _ l h, negativeLine] at off
    exact of_decide_eq_false off
  · intro e t
    exact FormulaProtocol.partition F hF _ _ (hyes e) (hno t)

end PEqualNP.Outside.L_meta_4616

open scoped BigOperators in
open PEqualNP.Outside.L_meta_4616 in
theorem PEqualNP.Outside.L_meta_4616 :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             x5.output < x2 + x2 + x5.size →               (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) →                 (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) →                   (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) →                     have x15 : Fin x5.size → ℕ := fun (x15 : Fin x5.size) => (List.foldl (fun (x16 : List ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) => x16 ++ [(if x16.length = x2 + x2 + ↑x15 then (1 : ℕ) else (0 : ℕ)) + (List.map (fun (x18 : ℕ) => x16.getD x18 (0 : ℕ)) x17.inputs).sum]) (List.replicate (x2 + x2) (0 : ℕ)) x5.gates).getD x5.output (0 : ℕ);                     x2 * (x1 + (1 : ℕ)) ≤ (1 : ℕ) + ∑ x16 : Fin x5.size, x15 x16 := by
  intro q N inc incDec C hq hN hline hmeet hM hOut hW hYes hNo
  dsimp only
  obtain ⟨F, hF, hEval, hLeaves⟩ :=
    PathAccount.existsUnfoldedFormula (show 0 < N+N by omega) C hM hOut hW
  have bound := formulaIncidenceBound inc (uniqueMeet hmeet) F hF
    (fun e => (hEval _).trans (positiveCircuit hYes e))
    (fun t => (hEval _).trans (negativeCircuit (show 1 ≤ q by omega) hNo t))
  rw [incidenceCard inc hline, hLeaves] at bound
  simpa only [PathAccount.postedPathCount_eq] using bound
