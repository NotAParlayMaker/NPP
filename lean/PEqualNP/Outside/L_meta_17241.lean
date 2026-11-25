import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17241

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def weights (n : ℕ) (S : List ℕ) (v : ℕ) : List (Option ℕ) :=
  (List.range n).map fun i => if i = v then some 1 else if i ∈ S then some 0 else none

def weight (R : List (Option ℕ)) (g : Gate) : Option ℕ :=
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

def appendWeight (R : List (Option ℕ)) (g : Gate) : List (Option ℕ) :=
  R ++ [weight R g]

theorem appendKeeps (R : List (Option ℕ)) (g : Gate) {i : ℕ} (hi : i < R.length) :
    (appendWeight R g).getD i none = R.getD i none := by
  simp [appendWeight, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldLength (gs : List Gate) (R : List (Option ℕ)) :
    (gs.foldl appendWeight R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, appendWeight, List.length_append,
      List.length_nil, List.length_cons]
    omega

theorem foldKeeps (gs : List Gate) (R : List (Option ℕ)) {i : ℕ} (hi : i < R.length) :
    (gs.foldl appendWeight R).getD i none = R.getD i none := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [appendWeight]; omega), appendKeeps _ _ hi]

theorem initialRead (n : ℕ) (C : Circuit) (S : List ℕ) (v : ℕ) (i : Fin n) :
    (scalarMults C n S v).getD i.val none =
      if i.val = v then some 1 else if i.val ∈ S then some 0 else none := by
  change (C.gates.foldl appendWeight (weights n S v)).getD i.val none = _
  rw [foldKeeps _ _ (by simp [weights, i.isLt])]
  simp [weights, List.getD_eq_getElem?_getD, i.isLt]

theorem gateRead (n : ℕ) (C : Circuit) (S : List ℕ) (v j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (a b : ℕ) (hins : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    let value := fun k => (scalarMults C n S v).getD k none
    (g.op = .and → value (n+j) = (value a).bind (fun x => (value b).map (fun y => x+y))) ∧
    (g.op = .or → value (n+j) = ((value a).map (fun x => min x ((value b).getD x))).orElse
      (fun _ => value b)) := by
  let R := (C.gates.take j).foldl appendWeight (weights n S v)
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hg
  have plen : R.length = n+j := by
    simp [R, foldLength, weights, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j+1) := by
    rw [← hget, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have run : scalarMults C n S v = (C.gates.drop (j+1)).foldl appendWeight (appendWeight R g) := by
    change C.gates.foldl appendWeight (weights n S v) = _
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  have prior (i : ℕ) (hi : i < n+j) :
      (scalarMults C n S v).getD i none = R.getD i none := by
    have hir : i < R.length := by simpa [plen] using hi
    rw [run, foldKeeps _ _ (by simp [appendWeight]; omega), appendKeeps _ _ hir]
  have gate : (scalarMults C n S v).getD (n+j) none = weight R g := by
    rw [run, foldKeeps _ _ (by simp [appendWeight, plen])]
    simp [appendWeight, List.getD_eq_getElem?_getD, ← plen]
  dsimp only
  rw [gate, prior a ha, prior b hb]
  constructor <;> intro hop <;>
    simp only [weight, hins, hop, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] <;>
    cases R.getD a none <;> cases R.getD b none <;> simp [Option.bind, Option.map, Option.orElse]

end PEqualNP.Outside.L_meta_17241

open PEqualNP.Outside.L_meta_17241 in
theorem PEqualNP.Outside.L_meta_17241 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List ℕ) (x4 : ℕ),   have x5 : ℕ → Option ℕ := fun (x5 : ℕ) => (PEqualNP.ReadK.scalarMults x2 x1 x3 x4).getD x5 Option.none;   (∀ (x6 : Fin x1), x5 ↑x6 = if ↑x6 = x4 then Option.some (1 : ℕ) else if ↑x6 ∈ x3 then Option.some (0 : ℕ) else Option.none) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x2.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → x8 < x1 + x6 → x9 < x1 + x6 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 (x1 + x6) = (x5 x8).bind fun (x15 : ℕ) => Option.map (fun (x16 : ℕ) => x15 + x16) (x5 x9)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 (x1 + x6) = (Option.map (fun (x15 : ℕ) => Min.min x15 ((x5 x9).getD x15)) (x5 x8)).orElse fun (x15 : Unit) => x5 x9) := by
  intro n C S v value
  exact ⟨initialRead n C S v, fun j g a b hg hin ha hb => gateRead n C S v j g hg a b hin ha hb⟩
