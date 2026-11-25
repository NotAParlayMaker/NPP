import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17241

open PEqualNP.CircuitLowerBounds

private def gateValue (R : List (Option Nat)) (g : Gate) : Option Nat :=
  let ins := g.inputs.map fun i => R.getD i none
  match g.op with
    | .or => ins.foldl (fun acc o => match acc, o with
        | none, o => o
        | some a, none => some a
        | some a, some b => some (min a b)) none
    | .and => ins.foldl (fun acc o => match acc, o with
        | some a, some b => some (a + b)
        | _, _ => none) (some 0)
    | _ => none

private def step (R : List (Option Nat)) (g : Gate) : List (Option Nat) :=
  R ++ [gateValue R g]

private theorem andPair (a b : Option Nat) :
    [a, b].foldl (fun acc o => match acc, o with
      | some x, some y => some (x + y)
      | _, _ => none) (some 0) = a.bind (fun x => b.map (fun y => x + y)) := by
  cases a <;> cases b <;> simp

private theorem orPair (a b : Option Nat) :
    [a, b].foldl (fun acc o => match acc, o with
      | none, o => o
      | some x, none => some x
      | some x, some y => some (min x y)) none =
      (a.map (fun x => min x (b.getD x))).orElse (fun _ => b) := by
  cases a <;> cases b <;> simp

private theorem foldShape (gs : List Gate) (R : List (Option Nat)) :
    ∃ tail, gs.foldl step R = R ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing R with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨tail, eq, len⟩ := ih (step R g)
    refine ⟨gateValue R g :: tail, ?_, by simp [len]⟩
    rw [List.foldl_cons, eq]
    simp [step]

private theorem oldWire (gs : List Gate) (R : List (Option Nat)) (i : Nat)
    (lt : i < R.length) : (gs.foldl step R).getD i none = R.getD i none := by
  obtain ⟨tail, eq, _⟩ := foldShape gs R
  rw [eq, List.getD_append _ _ _ _ lt]

private theorem split (gs : List Gate) (k : Nat) (g : Gate) (atGate : gs[k]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = k := by
  induction gs generalizing k with
  | nil => simp at atGate
  | cons a gs ih =>
    cases k with
    | zero =>
      simp at atGate
      subst g
      exact ⟨[], gs, rfl, rfl⟩
    | succ k =>
      simp at atGate
      obtain ⟨pre, post, rfl, rfl⟩ := ih k atGate
      exact ⟨a :: pre, post, rfl, rfl⟩

end PEqualNP.Outside.L_meta_17241

open PEqualNP.Outside.L_meta_17241 in
theorem PEqualNP.Outside.L_meta_17241 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List ℕ) (x4 : ℕ),   have x5 : ℕ → Option ℕ := fun (x5 : ℕ) => (PEqualNP.ReadK.scalarMults x2 x1 x3 x4).getD x5 Option.none;   (∀ (x6 : Fin x1), x5 ↑x6 = if ↑x6 = x4 then Option.some (1 : ℕ) else if ↑x6 ∈ x3 then Option.some (0 : ℕ) else Option.none) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x2.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → x8 < x1 + x6 → x9 < x1 + x6 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 (x1 + x6) = (x5 x8).bind fun (x15 : ℕ) => Option.map (fun (x16 : ℕ) => x15 + x16) (x5 x9)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 (x1 + x6) = (Option.map (fun (x15 : ℕ) => Min.min x15 ((x5 x9).getD x15)) (x5 x8)).orElse fun (x15 : Unit) => x5 x9) := by
  intro n C S v
  let initial := (List.range n).map fun i => if i = v then some 1 else if i ∈ S then some 0 else none
  have initialLength : initial.length = n := by simp [initial]
  change (∀ i : Fin n, (C.gates.foldl step initial).getD i.val none =
    if i.val = v then some 1 else if i.val ∈ S then some 0 else none) ∧ _
  constructor
  · intro i
    have lt : i.val < initial.length := initialLength.symm ▸ i.isLt
    rw [oldWire _ _ _ lt, List.getD_eq_getElem _ _ lt]
    simp [initial]
  · intro k g a b atGate inputs earlierA earlierB
    obtain ⟨pre, post, gates, preLength⟩ := split C.gates k g atGate
    let R := pre.foldl step initial
    obtain ⟨tail, shape, tailLength⟩ := foldShape pre initial
    have len : R.length = n + k := by
      change (pre.foldl step initial).length = _
      rw [shape, List.length_append, initialLength, tailLength, preLength]
    let out := post.foldl step (step R g)
    have wireA : out.getD a none = R.getD a none := by
      have h : a < R.length := by simpa [len] using earlierA
      rw [show out = post.foldl step (step R g) by rfl]
      rw [oldWire _ _ _ (by unfold step; simp; omega)]
      unfold step
      rw [List.getD_append _ _ _ _ h]
    have wireB : out.getD b none = R.getD b none := by
      have h : b < R.length := by simpa [len] using earlierB
      rw [show out = post.foldl step (step R g) by rfl]
      rw [oldWire _ _ _ (by unfold step; simp; omega)]
      unfold step
      rw [List.getD_append _ _ _ _ h]
    have newWire : out.getD (n + k) none = (step R g).getD R.length none := by
      rw [← len]
      exact oldWire _ _ _ (by unfold step; simp)
    let value := fun i => (C.gates.foldl step initial).getD i none
    change (g.op = .and → value (n + k) = (value a).bind (fun t => (value b).map fun u => t + u)) ∧
      (g.op = .or → value (n + k) = ((value a).map fun t => min t ((value b).getD t)).orElse fun _ => value b)
    dsimp only [value]
    rw [gates, List.foldl_append, List.foldl_cons]
    change (g.op = .and → out.getD (n + k) none = (out.getD a none).bind _) ∧
      (g.op = .or → out.getD (n + k) none = (Option.map _ (out.getD a none)).orElse _)
    rw [newWire, wireA, wireB]
    constructor <;> intro op <;> unfold step gateValue <;> rw [op, inputs] <;>
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    · exact andPair (R.getD a none) (R.getD b none)
    · exact orPair (R.getD a none) (R.getD b none)
