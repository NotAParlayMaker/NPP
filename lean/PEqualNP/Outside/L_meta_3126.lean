import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3126

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev Assignment := Fin 7 → Bool
-- The left case is a constant, and the right case refers to a rebuilt wire.
private abbrev Slot := Bool ⊕ ℕ

private def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def fits (length : ℕ) : Slot → Prop
  | .inl _ => True
  | .inr i => i < length

private def readSlot (wires : List Bool) : Slot → Bool
  | .inl b => b
  | .inr i => wires.getD i false

private def gateValue (wires : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => wires.getD i false)

private def stripAnd (left right : Slot) : Slot ⊕ Gate :=
  match left, right with
  | .inl false, _ | _, .inl false => .inl (.inl false)
  | .inl true, r | r, .inl true => .inl r
  | .inr i, .inr j => .inr ⟨.and, [i, j]⟩

private def stripOr (left right : Slot) : Slot ⊕ Gate :=
  match left, right with
  | .inl true, _ | _, .inl true => .inl (.inl true)
  | .inl false, r | r, .inl false => .inl r
  | .inr i, .inr j => .inr ⟨.or, [i, j]⟩

private def compile : GateOp → List Slot → Slot ⊕ Gate
  | .and, [] => .inl (.inl true)
  | .and, [r] => .inl r
  | .and, r :: s :: _ => stripAnd r s
  | .or, [] => .inl (.inl false)
  | .or, [r] => .inl r
  | .or, r :: s :: _ => stripOr r s
  | .not, [] => .inl (.inl true)
  | .not, .inl b :: _ => .inl (.inl (!b))
  | .not, .inr i :: _ => .inr ⟨.not, [i]⟩
  | _, _ => .inl (.inl false)

private def relevant {α : Type} : GateOp → List α → List α
  | .not, rs => rs.take 1
  | _, rs => rs

private def varies (f : Assignment → Bool) : Prop := ∃ x y, f x ≠ f y

private theorem compile_correct (w : List Bool) (op : GateOp) (rs : List Slot)
    (basis : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : rs.length ≤ 2) (bounded : ∀ r ∈ rs, fits w.length r) :
    ((compile op rs).elim (readSlot w) (gateValue w)
      = op.eval (rs.map (readSlot w))) ∧
    (compile op rs).elim (fits w.length)
      (fun g => allowed g ∧ ∀ r ∈ relevant op rs, r.isRight = true) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at basis
  rcases basis with rfl | rfl | rfl
  · rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨t, ts⟩⟩⟩
    · simp [compile, fits, readSlot, GateOp.eval]
    · simpa [compile, GateOp.eval] using bounded r (by simp)
    · have hr := bounded r (by simp)
      have hs := bounded s (by simp)
      rcases r with (b | i) <;> rcases s with (c | j)
      all_goals try cases b
      all_goals try cases c
      all_goals simp_all [compile, stripAnd, readSlot, gateValue, GateOp.eval, fits,
        allowed, relevant]
    · simp at arity
  · rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨t, ts⟩⟩⟩
    · simp [compile, fits, readSlot, GateOp.eval]
    · simpa [compile, GateOp.eval] using bounded r (by simp)
    · have hr := bounded r (by simp)
      have hs := bounded s (by simp)
      rcases r with (b | i) <;> rcases s with (c | j)
      all_goals try cases b
      all_goals try cases c
      all_goals simp_all [compile, stripOr, readSlot, gateValue, GateOp.eval, fits,
        allowed, relevant]
    · simp at arity
  · rcases rs with _ | ⟨r, rs⟩
    · simp [compile, fits, readSlot, GateOp.eval]
    · rcases r with (b | i) <;>
        simp [compile, fits, readSlot, gateValue, GateOp.eval, allowed, relevant]

private theorem mem_relevant {op : GateOp} {indices : List ℕ} {i : ℕ}
    (hi : i ∈ indices) (active : op ≠ .not ∨ indices[0]? = some i) :
    i ∈ relevant op indices := by
  cases op <;> try simpa [relevant] using hi
  rcases active with h | h
  · exact (h rfl).elim
  · cases indices with
    | nil => simp at h
    | cons a rest =>
      simp at h
      simp [relevant, h]

private theorem wires_add (gs : List Gate) (g : Gate) (inputs : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires inputs =
      (Circuit.mk gs 0).wires inputs ++ [gateValue ((Circuit.mk gs 0).wires inputs) g] := by
  simp [Circuit.wires, List.foldl_append, gateValue]

private theorem wire_length (gs : List Gate) (inputs : List Bool) :
    ((Circuit.mk gs 0).wires inputs).length = inputs.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => simp [wires_add, ih, Nat.add_assoc]

private theorem read_append {w suffix : List Bool} {r : Slot} (h : fits w.length r) :
    readSlot (w ++ suffix) r = readSlot w r := by
  cases r with
  | inl b => rfl
  | inr i => exact List.getD_append _ _ _ _ h

private def inputSlot : Option (Fin 7) → Slot
  | none => .inl false
  | some i => .inr i.val

private theorem input_agrees (l : List (Option (Fin 7))) (x : Assignment) (i : ℕ) :
    readSlot (List.ofFn x) (inputSlot (l.getD i none)) =
      (l.map fun p => p.elim false x).getD i false := by
  have h := List.getD_map l none (n := i) (fun p => p.elim false x)
  rw [show (none : Option (Fin 7)).elim false x = false from rfl] at h
  rw [h]
  cases hslot : l.getD i none with
  | none => rfl
  | some j =>
    change (List.ofFn x).getD j.val false = x j
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt)]
    rw [List.getElem_ofFn]

private theorem input_fits (l : List (Option (Fin 7))) (i : ℕ) :
    fits 7 (inputSlot (l.getD i none)) := by
  cases l.getD i none with
  | none => trivial
  | some j => exact j.isLt

private def canonicalWires (gs : List Gate) (x : Assignment) : List Bool :=
  (Circuit.mk gs 0).wires (List.ofFn x)

private theorem canonical_length (gs : List Gate) (x : Assignment) :
    (canonicalWires gs x).length = 7 + gs.length := by
  simp only [canonicalWires, wire_length, List.length_ofFn]

private theorem canonical_extension (gs extra : List Gate) (x : Assignment) :
    ∃ suffix, canonicalWires (gs ++ extra) x = canonicalWires gs x ++ suffix := by
  induction extra using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton extra g ih =>
    obtain ⟨tail, htail⟩ := ih
    refine ⟨tail ++ [gateValue (canonicalWires (gs ++ extra) x) g], ?_⟩
    rw [← List.append_assoc gs]
    simp only [canonicalWires, wires_add]
    change canonicalWires (gs ++ extra) x ++
      [gateValue (canonicalWires (gs ++ extra) x) g] =
        canonicalWires gs x ++ (tail ++ [gateValue (canonicalWires (gs ++ extra) x) g])
    simp only [htail, List.append_assoc]

private theorem relevant_map (op : GateOp) (indices : List ℕ) (f : ℕ → Slot) :
    relevant op (indices.map f) = (relevant op indices).map f := by
  cases op <;> simp [relevant]

private theorem simplifyGate (gs : List Gate) (refs : ℕ → Slot) (old : Assignment → List Bool)
    (g : Gate) (budget : ℕ) (hGate : allowed g)
    (hFits : ∀ i, fits (7 + gs.length) (refs i))
    (hRead : ∀ x i, readSlot (canonicalWires gs x) (refs i) = (old x).getD i false)
    (hBudget : (∀ i ∈ relevant g.op g.inputs, varies (fun x => (old x).getD i false)) →
      1 ≤ budget) :
    ∃ (extra : List Gate) (r : Slot),
      (∀ h ∈ extra, allowed h) ∧ extra.length ≤ budget ∧
      fits (7 + (gs ++ extra).length) r ∧
      ∀ x, readSlot (canonicalWires (gs ++ extra) x) r = gateValue (old x) g := by
  classical
  -- A wire can be semantically constant even if an earlier step kept its gate.
  let normalize (i : ℕ) : Slot :=
    if varies (fun x => (old x).getD i false) then refs i
    else .inl ((old (fun _ => false)).getD i false)
  have normFits (i : ℕ) : fits (7 + gs.length) (normalize i) := by
    unfold normalize
    split
    · exact hFits i
    · trivial
  have normRead (x : Assignment) (i : ℕ) :
      readSlot (canonicalWires gs x) (normalize i) = (old x).getD i false := by
    unfold normalize
    split
    · exact hRead x i
    · rename_i h
      exact not_not.mp fun hne => h ⟨(fun _ => false), x, hne⟩
  have normVaries (i : ℕ) (h : (normalize i).isRight = true) :
      varies (fun x => (old x).getD i false) := by
    by_contra hv
    simp only [normalize, ite_eq_right hv, Sum.isRight, Bool.false_eq_true] at h
  let slots := g.inputs.map normalize
  have hSpec (x : Assignment) :
      ((compile g.op slots).elim (readSlot (canonicalWires gs x))
        (gateValue (canonicalWires gs x)) = gateValue (old x) g) ∧
      (compile g.op slots).elim (fits (7 + gs.length))
        (fun h => allowed h ∧ ∀ r ∈ relevant g.op slots, r.isRight = true) := by
    have h := compile_correct (canonicalWires gs x) g.op slots hGate.1
      (by simpa [slots] using hGate.2) (by
        rw [canonical_length]
        intro r hr
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
        exact normFits i)
    have hMap : slots.map (readSlot (canonicalWires gs x)) =
        g.inputs.map (fun i => (old x).getD i false) := by
      change (g.inputs.map normalize).map (readSlot (canonicalWires gs x)) = _
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => normRead x i)
    rw [hMap, canonical_length] at h
    exact h
  cases hCompile : compile g.op slots with
  | inl r =>
    have hr := (hSpec (fun _ => false)).2
    rw [hCompile] at hr
    refine ⟨[], r, by simp, by simp, by simpa using hr, ?_⟩
    intro x
    have he := (hSpec x).1
    simpa [hCompile] using he
  | inr h =>
    have ha := (hSpec (fun _ => false)).2
    rw [hCompile] at ha
    change allowed h ∧ (∀ r ∈ relevant g.op slots, r.isRight = true) at ha
    have hb : 1 ≤ budget := hBudget fun i hi => normVaries i <|
      ha.2 (normalize i) (by
        change normalize i ∈ relevant g.op (g.inputs.map normalize)
        rw [relevant_map]
        exact List.mem_map.mpr ⟨i, hi, rfl⟩)
    refine ⟨[h], .inr (7 + gs.length), by simpa using ha.1, by simpa using hb, ?_, ?_⟩
    · simp [fits]
    · intro x
      have he := (hSpec x).1
      rw [hCompile] at he
      change (canonicalWires (gs ++ [h]) x).getD (7 + gs.length) false = _
      simp only [canonicalWires, wires_add]
      rw [List.getD_append_right _ _ _ _ (by rw [wire_length, List.length_ofFn])]
      rw [wire_length, List.length_ofFn, Nat.sub_self]
      exact he

private theorem fits_mono {small large : ℕ} (hle : small ≤ large) {r : Slot} (h : fits small r) :
    fits large r := by
  cases r with
  | inl b => trivial
  | inr i => exact Nat.lt_of_lt_of_le h hle

private theorem getD_push (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases lt_trichotomy i w.length with h | rfl | h
  · rw [ite_eq_right h.ne, List.getD_append _ _ _ _ h]
  · rw [ite_eq_left rfl, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  · rw [ite_eq_right h.ne', List.getD_eq_default w false h.le,
        List.getD_eq_default (w ++ [b]) false (by simp; omega)]

private theorem build (C : Circuit) (l : List (Option (Fin 7))) (hC : FanInTwo C) :
    let input (x : Assignment) := l.map (fun p => p.elim false x)
    let original (k : ℕ) (x : Assignment) :=
      (Circuit.mk (C.gates.take k) 0).wires (input x)
    let good (j : Fin C.gates.length) :=
      let g := C.gates.get j
      ∀ i ∈ g.inputs, g.op ≠ .not ∨ g.inputs[0]? = some i →
        varies (fun x => (original j.val x).getD i false)
    ∀ k ≤ C.gates.length, ∃ (gs : List Gate) (refs : ℕ → Slot) (S : Finset (Fin C.gates.length)),
      (∀ j ∈ S, j.val < k ∧ good j) ∧ (∀ g ∈ gs, allowed g) ∧ gs.length ≤ S.card ∧
      (∀ i, fits (7 + gs.length) (refs i)) ∧
      ∀ x i, readSlot (canonicalWires gs x) (refs i) = (original k x).getD i false := by
  classical
  intro input original good k
  induction k with
  | zero =>
    intro _
    refine ⟨[], fun i => inputSlot (l.getD i none), ∅, by simp, by simp, by simp, ?_, ?_⟩
    · exact input_fits l
    · exact input_agrees l
  | succ k ih =>
    intro hk
    have hk' : k < C.gates.length := hk
    obtain ⟨gs, refs, S, hChosen, hAllowed, hSize, hFits, hRead⟩ := ih (Nat.le_of_lt hk')
    let j : Fin C.gates.length := ⟨k, hk'⟩
    let g := C.gates.get j
    have hGate : allowed g := hC _ (List.getElem_mem hk')
    let budget : ℕ := if good j then 1 else 0
    have hBudget (hs : ∀ i ∈ relevant g.op g.inputs, varies fun x => (original k x).getD i false) :
        1 ≤ budget := by
      have hGood : good j := by
        intro i hi he
        exact hs i (mem_relevant hi he)
      simp [budget, hGood]
    obtain ⟨extra, r, hBasis, hBound, hrFits, hrRead⟩ :=
      simplifyGate gs refs (original k) g budget hGate hFits hRead hBudget
    -- Each new original gate sets exactly one original wire index.
    let nextRefs (i : ℕ) := if i = l.length + k then r else refs i
    let nextS := if good j then insert j S else S
    have hFresh : j ∉ S := by
      intro hj
      exact (Nat.lt_irrefl k) (hChosen j hj).1
    have hCard : nextS.card = S.card + budget := by
      by_cases hGood : good j
      · simp [nextS, budget, hGood, Finset.card_insert_of_notMem hFresh]
      · simp [nextS, budget, hGood]
    refine ⟨gs ++ extra, nextRefs, nextS, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      by_cases hGood : good j
      · have ht' : t = j ∨ t ∈ S := by simpa [nextS, hGood] using ht
        rcases ht' with rfl | ht'
        · exact ⟨Nat.lt_succ_self k, hGood⟩
        · exact ⟨Nat.lt_succ_of_lt (hChosen t ht').1, (hChosen t ht').2⟩
      · have ht' : t ∈ S := by simpa [nextS, hGood] using ht
        exact ⟨Nat.lt_succ_of_lt (hChosen t ht').1, (hChosen t ht').2⟩
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact hAllowed h hh
      · exact hBasis h hh
    · rw [hCard, List.length_append]
      exact Nat.add_le_add hSize hBound
    · intro i
      unfold nextRefs
      split
      · exact hrFits
      · exact fits_mono (by simp) (hFits i)
    · intro x i
      have hl : (original k x).length = l.length + k := by
        change ((Circuit.mk (C.gates.take k) 0).wires (l.map (fun p => p.elim false x))).length = _
        rw [wire_length, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk')]
      have hNext : original (k + 1) x = original k x ++ [gateValue (original k x) g] := by
        change (Circuit.mk (C.gates.take (k + 1)) 0).wires (input x) = _
        rw [List.take_succ_eq_append_getElem hk', wires_add]
        rfl
      rw [hNext, getD_push, hl]
      unfold nextRefs
      by_cases hi : i = l.length + k
      · simp only [ite_eq_left hi]
        exact hrRead x
      · simp only [ite_eq_right hi]
        obtain ⟨tail, htail⟩ := canonical_extension gs extra x
        rw [htail, read_append (by rw [canonical_length]; exact hFits i), hRead]

end PEqualNP.Outside.L_meta_3126

open PEqualNP.Outside.L_meta_3126 in
theorem PEqualNP.Outside.L_meta_3126 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Option (Fin (7 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x1 →     have x4 : (Fin (7 : ℕ) → Bool) → List Bool := fun (x4 : Fin (7 : ℕ) → Bool) => List.map (fun (x5 : Option (Fin (7 : ℕ))) => x5.elim Bool.false x4) x2;     have x5 : Fin x1.gates.length → Prop := fun (x5 : Fin x1.gates.length) =>       have x6 : PEqualNP.CircuitLowerBounds.Gate := x1.gates.get x5;       ∀ x7 ∈ x6.inputs, x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∨ x6.inputs[(0 : ℕ)]? = Option.some x7 → ∃ (x10 : Fin (7 : ℕ) → Bool) (x11 : Fin (7 : ℕ) → Bool), ({ gates := List.take (↑x5) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x4 x10)).getD x7 Bool.false ≠ ({ gates := List.take (↑x5) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x4 x11)).getD x7 Bool.false;     (∃ (x6 : Fin (7 : ℕ) → Bool) (x7 : Fin (7 : ℕ) → Bool), x1.eval (x4 x6) ≠ x1.eval (x4 x7)) → ∃ (x7 : Finset (Fin x1.gates.length)), (∀ x8 ∈ x7, x5 x8) ∧ PEqualNP.MetaComplexity.HasCircuitSize (7 : ℕ) (fun (x8 : Fin (7 : ℕ) → Bool) => x1.eval (x4 x8)) x7.card := by
  classical
  intro C l hC input good hVar
  obtain ⟨gs, refs, S, hGood, hAllowed, hSize, _, hRead⟩ :=
    build C l hC C.gates.length le_rfl
  refine ⟨S, fun j hj => (hGood j hj).2, ?_⟩
  have hOutput (x : Assignment) :
      readSlot (canonicalWires gs x) (refs C.output) = C.eval (input x) := by
    have h := hRead x C.output
    change readSlot (canonicalWires gs x) (refs C.output) =
      ((PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.take C.gates.length) 0).wires
        (input x)).getD C.output false at h
    simpa [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires] using h
  cases hout : refs C.output with
  | inl b =>
    obtain ⟨x, y, hxy⟩ := hVar
    have hx : b = C.eval (input x) := by simpa only [hout, readSlot] using hOutput x
    have hy : b = C.eval (input y) := by simpa only [hout, readSlot] using hOutput y
    exact (hxy (hx.symm.trans hy)).elim
  | inr i =>
    refine ⟨⟨gs, i⟩, hAllowed, hSize, fun x => ?_⟩
    simpa only [hout, readSlot, canonicalWires, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires] using hOutput x
