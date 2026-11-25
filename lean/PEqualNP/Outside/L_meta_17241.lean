import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17241_aux

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def base (n : ℕ) (S : List ℕ) (v : ℕ) : List (Option ℕ) :=
  (List.range n).map fun i => if i = v then some 1 else if i ∈ S then some 0 else none

def step (w : List (Option ℕ)) (g : Gate) : List (Option ℕ) :=
  let ins := g.inputs.map fun i => w.getD i none
  w ++ [match g.op with
    | GateOp.or => ins.foldl (fun acc o => match acc, o with
        | none, o => o
        | some a, none => some a
        | some a, some b => some (min a b)) none
    | GateOp.and => ins.foldl (fun acc o => match acc, o with
        | some a, some b => some (a + b)
        | _, _ => none) (some 0)
    | _ => none]

theorem length_run (gs : List Gate) (w : List (Option ℕ)) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_nil, List.length_cons]
    omega

theorem keep (gs : List Gate) (w : List (Option ℕ)) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i none = w.getD i none := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem gate (gs : List Gate) (w : List (Option ℕ)) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) none =
      (step ((gs.take j).foldl step w) g).getD (w.length+j) none := by
  obtain ⟨jlt, hget⟩ := List.getElem?_eq_some_iff.mp hj
  have h : gs = gs.take j ++ g :: gs.drop (j+1) := by
    rw [← hget, ← List.drop_eq_getElem_cons jlt, List.take_append_drop]
  conv_lhs => rw [h, List.foldl_append, List.foldl_cons]
  apply keep
  simp [step, length_run, List.length_take, min_eq_left jlt.le]

theorem previous (gs : List Gate) (w : List (Option ℕ)) (j i : ℕ)
    (hj : j ≤ gs.length) (hi : i < w.length+j) :
    (gs.foldl step w).getD i none = ((gs.take j).foldl step w).getD i none := by
  conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
  apply keep
  simpa [length_run, min_eq_left hj] using hi

end PEqualNP.Outside.L_meta_17241_aux

open PEqualNP.Outside.L_meta_17241_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_17241 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List ℕ) (x4 : ℕ),   have x5 : ℕ → Option ℕ := fun (x5 : ℕ) => (PEqualNP.ReadK.scalarMults x2 x1 x3 x4).getD x5 Option.none;   (∀ (x6 : Fin x1), x5 ↑x6 = if ↑x6 = x4 then Option.some (1 : ℕ) else if ↑x6 ∈ x3 then Option.some (0 : ℕ) else Option.none) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x2.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → x8 < x1 + x6 → x9 < x1 + x6 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 (x1 + x6) = (x5 x8).bind fun (x15 : ℕ) => Option.map (fun (x16 : ℕ) => x15 + x16) (x5 x9)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 (x1 + x6) = (Option.map (fun (x15 : ℕ) => Min.min x15 ((x5 x9).getD x15)) (x5 x8)).orElse fun (x15 : Unit) => x5 x9) := by
  intro n C S v
  change (∀ i : Fin n, (C.gates.foldl step (base n S v)).getD i none = _) ∧ _
  have bl : (base n S v).length = n := by simp [base]
  constructor
  · intro i
    rw [keep C.gates _ _ (by simp [bl])]
    simp [base, List.getD_eq_getElem?_getD, i.isLt]
  intro j g a b hj hab ha hb
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj
  let w := (C.gates.take j).foldl step (base n S v)
  have wl : w.length = n+j := by simp [w, length_run, bl, min_eq_left hlt.le]
  have eq := gate C.gates (base n S v) j g hj
  rw [bl] at eq
  have ea := previous C.gates (base n S v) j a hlt.le (by simpa only [bl] using ha)
  have eb := previous C.gates (base n S v) j b hlt.le (by simpa only [bl] using hb)
  change _ = w.getD a none at ea
  change _ = w.getD b none at eb
  change _ = (step w g).getD (n+j) none at eq
  have hlast : (step w g).getD (n+j) none = (step w g).getD w.length none := by rw [wl]
  change (_ → (C.gates.foldl step (base n S v)).getD (n+j) none = _) ∧
    (_ → (C.gates.foldl step (base n S v)).getD (n+j) none = _)
  rw [eq, hlast]
  have top (o : Option ℕ) : (w ++ [o]).getD w.length none = o := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  constructor <;> intro hop <;>
    simp only [PEqualNP.ReadK.scalarMults] <;>
    change (step w g).getD w.length none = _ <;>
    (first
      | change _ = ((C.gates.foldl step (base n S v)).getD a none).bind
          (fun x => ((C.gates.foldl step (base n S v)).getD b none).map (x + ·))
      | change _ = (((C.gates.foldl step (base n S v)).getD a none).map
          (fun x => min x (((C.gates.foldl step (base n S v)).getD b none).getD x))).orElse
          (fun _ => (C.gates.foldl step (base n S v)).getD b none)) <;>
    rw [ea, eb] <;> simp only [step, top, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] <;>
    (cases w.getD a none <;> cases w.getD b none <;> simp [Option.bind, Option.map, Option.orElse, Option.getD])
