import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.ReadK

namespace PEqualNP.Outside.L_meta_18191

abbrev Wire := Option ℕ

def gateVal (w : List Wire) (g : Gate) : Wire :=
  let ins := g.inputs.map fun i => w.getD i none
  match g.op with
  | .or => ins.foldl (fun acc o => match acc, o with
      | none, z => z | some x, none => some x | some x, some y => some (min x y)) none
  | .and => ins.foldl (fun acc o => match acc, o with
      | some x, some y => some (x+y) | _, _ => none) (some 0)
  | _ => none

def step (w : List Wire) (g : Gate) := w ++ [gateVal w g]

theorem fixed (gs : List Gate) (w : List Wire) {i : ℕ} (hi : i < w.length) :
    (gs.foldl step w).getD i none = w.getD i none := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step]; omega)]
    simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem traceGate (gs : List Gate) (w : List Wire) (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : gs[j]? = some g) (hab : g.inputs = [a,b]) (ha : a < w.length+j) (hb : b < w.length+j) :
    let r (i : ℕ) := (gs.foldl step w).getD i none
    (g.op = .and → r (w.length+j) = (r a).bind (fun x => (r b).map (fun y => x+y))) ∧
    (g.op = .or → r (w.length+j) = ((r a).map (fun x => min x ((r b).getD x))).orElse (fun _ => r b)) := by
  dsimp only
  induction gs generalizing w j with
  | nil => simp at hg
  | cons g0 gs ih =>
    cases j with
    | zero =>
      obtain rfl : g0 = g := by simpa using hg
      simp only [Nat.add_zero] at ha hb ⊢
      rw [fixed (g0 :: gs) w ha,fixed (g0 :: gs) w hb,List.foldl_cons,
        fixed gs (step w g0) (by simp [step])]
      have self : (step w g0).getD w.length none = gateVal w g0 := by
        simp [step,List.getD_eq_getElem?_getD]
      rw [self]
      constructor <;> intro hop <;>
        simp only [gateVal,hab,hop,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] <;>
        cases w.getD a none <;> cases w.getD b none <;> simp
    | succ j =>
      have len : (step w g0).length = w.length+1 := by simp [step]
      have eqn : w.length + (j+1) = (step w g0).length+j := by omega
      rw [eqn] at ha hb ⊢
      exact ih (step w g0) j (by simpa using hg) ha hb

theorem trace (n : ℕ) (C : Circuit) (S : List ℕ) (v : ℕ) :
    let r (i : ℕ) := (scalarMults C n S v).getD i none
    (∀ i : Fin n, r i.val = if i.val = v then some 1 else if i.val ∈ S then some 0 else none) ∧
    ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] → a < n+j → b < n+j →
      (g.op = .and → r (n+j) = (r a).bind (fun x => (r b).map (fun y => x+y))) ∧
      (g.op = .or → r (n+j) = ((r a).map (fun x => min x ((r b).getD x))).orElse (fun _ => r b)) := by
  let w : List Wire := (List.range n).map fun i => if i = v then some 1 else if i ∈ S then some 0 else none
  have len : w.length = n := by simp [w]
  have fold : scalarMults C n S v = C.gates.foldl step w := rfl
  dsimp only
  rw [fold]
  constructor
  · intro i
    rw [fixed C.gates w (by simpa [len] using i.isLt)]
    simp [w,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,i.isLt]
  · intro j g a b hg hab ha hb
    simpa only [len] using traceGate C.gates w j g a b hg hab (by simpa only [len] using ha)
      (by simpa only [len] using hb)


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem checked : ∀ (C : Circuit), (∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 25+j ∧ b < 25+j) → (∀ v ∈ ([0,7] : List ℕ), 2 ≤ ((scalarMults C 25 [0,7] v).getD C.output none).getD 2) → ∀ s : Bool, ∃ r : ℕ → ℕ, r (if s = true then 0 else 7) = 0 ∧ r (if s = true then 7 else 0) ≤ 1 ∧
      (∀ j < 25, j ≠ 0 → j ≠ 7 → r j = 2) ∧ 2 ≤ r C.output ∧
      ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → r (25+j) ≤ r a + r b) ∧ (g.op = .or → r (25+j) ≤ min (r a) (r b)) := by
  intro C hshape hcost
  intro s
  let v : ℕ := if s then 7 else 0
  let r (i : ℕ) := (scalarMults C 25 [0,7] v).getD i none
  let cap (z : Option ℕ) := min 2 (z.getD 2)
  obtain ⟨raw,gates⟩ := trace 25 C [0,7] v
  have raw0 := raw (0 : Fin 25)
  have raw7 := raw (7 : Fin 25)
  change r 0 = _ at raw0
  change r 7 = _ at raw7
  have good := hcost v (by cases s <;> simp [v])
  change 2 ≤ (r C.output).getD 2 at good
  refine ⟨fun i => cap (r i),?_,?_,?_,by simpa [cap] using good,?_⟩
  · cases s <;> simp_all [v,cap]
  · cases s <;> simp_all [v,cap]
  · intro j hj h0 h7
    have eq := raw (⟨j,hj⟩ : Fin 25)
    change r j = _ at eq
    cases s <;> simp_all [v,cap]
  · intro j g a b hg hab
    obtain ⟨_,u,w,uw,_,hu,hw⟩ := hshape j g hg
    rw [hab] at uw
    obtain ⟨rfl,rfl⟩ : a=u ∧ b=w := by simpa using uw
    obtain ⟨ha,ho⟩ := gates j g a b hg hab hu hw
    change (g.op = .and → cap (r (25+j)) ≤ cap (r a) + cap (r b)) ∧
      (g.op = .or → cap (r (25+j)) ≤ min (cap (r a)) (cap (r b)))
    constructor
    · intro hop
      rw [show r (25+j) = (r a).bind (fun x => (r b).map (fun y => x+y)) from ha hop]
      cases r a <;> cases r b <;> simp [cap] <;> omega
    · intro hop
      rw [show r (25+j) = ((r a).map (fun x => min x ((r b).getD x))).orElse (fun _ => r b) from ho hop]
      cases r a <;> cases r b <;> simp [cap] <;> omega
end PEqualNP.Outside.L_meta_18191

theorem PEqualNP.Outside.L_meta_18191 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) → (∀ x3 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (25 : ℕ) [(0 : ℕ), (7 : ℕ)] x3).getD x1.output Option.none).getD (2 : ℕ)) → ∀ (x4 : Bool), ∃ (x5 : ℕ → ℕ), x5 (if x4 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x5 (if x4 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x6 < (25 : ℕ), x6 ≠ (0 : ℕ) → x6 ≠ (7 : ℕ) → x5 x6 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x5 x1.output ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((25 : ℕ) + x6) ≤ x5 x8 + x5 x9) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((25 : ℕ) + x6) ≤ Min.min (x5 x8) (x5 x9)) := @PEqualNP.Outside.L_meta_18191.checked
