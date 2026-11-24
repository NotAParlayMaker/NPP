import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The cofactor calculation and removal of the first gate follow R_meta_2311_214.
-- A reader must pass the effect of the distinguished input to an ordinary gate.
theorem PEqualNP.Outside.R_meta_2311_697
    (exportsPin : ∀ D : Circuit,
      let read (g : Gate) := [0,9].any fun i => g.inputs.contains i
      let input (t : Bool) (y : Fin 8 → Bool) := t :: List.ofFn y ++ [!t]
      FanInTwo D →
      (∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1) →
      (∀ t : Bool, ∃ y y' : Fin 8 → Bool, D.eval (input t y) ≠ D.eval (input t y')) →
      ∀ y : Fin 8 → Bool, D.eval (input false y) ≠ D.eval (input true y) →
      ∃ P : List Gate, ∃ a : Gate, ∃ R : List Gate, D.gates = P ++ a :: R ∧ read a = true ∧
        (D.wires (input false y)).getD (10+P.length) false ≠
          (D.wires (input true y)).getD (10+P.length) false ∧
        ∃ b ∈ R, read b = false ∧ 10+P.length ∈ b.inputs)
    (remaining : ∀ D : Circuit,
      let read (g : Gate) := [0,9].any fun i => g.inputs.contains i
      let clamp (g : Gate) := g.op = .and ∧ 0 ∈ g.inputs ∨ g.op = .or ∧ 9 ∈ g.inputs
      let input (t : Bool) (y : Fin 8 → Bool) := t :: List.ofFn y ++ [!t]
      FanInTwo D →
      (∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1) →
      D.size ≤ 14 → (D.gates.filter read).length = 2 →
      (∀ (P : List Gate) (a : Gate) (R : List Gate), D.gates = P ++ a :: R →
        clamp a → ∀ b ∈ R, read b = false → 10+P.length ∉ b.inputs) →
      (∃ P : List Gate, ∃ a : Gate, ∃ R : List Gate, D.gates = P ++ a :: R ∧
        read a = true ∧ (D.wires (input false (fun i => decide (i = 0)))).getD (10+P.length) false ≠
          (D.wires (input true (fun i => decide (i = 0)))).getD (10+P.length) false ∧
        ∃ b ∈ R, read b = false ∧ 10+P.length ∈ b.inputs) →
      (∀ (t : Bool) (y : Fin 8 → Bool), D.eval (input t y) =
        ((t && (y 0 || y 3 || y 4)) || ([1,10,19,5,14,23,38,47,60] : List ℕ).any
          (fun e => y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8))))) → False) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   have x6 : Prop := ∃ (x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x3 = x6 ++ x7 :: x8 ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x7.inputs ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x7.inputs) ∧ ∃ x9 ∈ x8, x4 x9 = Bool.false ∧ (10 : ℕ) + x6.length ∈ x9.inputs;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x8 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x8)).getD (9 : ℕ) Bool.false = !x8 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 = (2 : ℕ) → ¬x6 → False := by
  dsimp only
  intro C fan head target size readers noBridge
  let norm (g : Gate) : Gate := ⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩
  let read (g : Gate) := [0,9].any (fun i => g.inputs.contains i)
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have normalized (g : Gate) (hg : g.op ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (norm g).op ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ (norm g).inputs.length ≤ 2 ∧
      ((norm g).op = .not → (norm g).inputs.length ≤ 1) ∧ ∀ w, step w (norm g) = step w g := by
    obtain ⟨op,ins⟩ := g
    rcases hg with ⟨ops,len⟩
    change op = .and ∨ op = .or ∨ op = .not at ops
    change ins.length ≤ 2 at len
    rcases ops with rfl | rfl | rfl
    · simp [norm,show GateOp.and.eval [false] = false from rfl,step,len]
    · simp [norm,show GateOp.or.eval [false] = false from rfl,step,len]
    · cases ins with
      | nil => simp [norm,show GateOp.not.eval [false] = true from rfl,step]
      | cons i tail =>
        simp [norm,show GateOp.not.eval [false] = true from rfl,step]
        intro w
        rfl
  have stable (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  cases cs : C.gates with
  | nil =>
    have r := readers
    simp [cs] at r
  | cons h gs =>
    let D : Circuit := ⟨gs.map norm, C.output⟩
    have ok (g) (mem : g ∈ gs) := normalized g (fan g (cs ▸ List.mem_cons_of_mem h mem))
    have fanD : FanInTwo D := by
      intro g hg
      obtain ⟨g,m,rfl⟩ := List.mem_map.mp hg
      exact ⟨(ok g m).1,(ok g m).2.1⟩
    have notD : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1 := by
      intro g hg
      obtain ⟨g,m,rfl⟩ := List.mem_map.mp hg
      exact (ok g m).2.2.1
    have agree (t : Bool) (y : Fin 8 → Bool) :
        D.eval (t :: List.ofFn y ++ [!t]) = circuitFun 9 C (Fin.cons t y) := by
      let x : Fin 9 → Bool := Fin.cons t y
      let w := List.ofFn x
      have len : w.length = 9 := List.length_ofFn
      have bit := head x
      change (C.gates.foldl step w).getD 9 false = !x 0 at bit
      rw [cs,List.foldl_cons,stable gs (step w h) 9 (by simp [step,len])] at bit
      have atEnd (v : Bool) : (w ++ [v]).getD 9 false = v := by rw [←len]; simp
      change (w ++ [_]).getD 9 false = !x 0 at bit
      rw [atEnd] at bit
      have appended : step w h = t :: List.ofFn y ++ [!t] := by
        change w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)] = _
        rw [bit]
        simp [w,x,List.ofFn_succ]
      have mapped (ls : List Gate) (hls : ∀ g∈ls, g ∈ gs) (z : List Bool) :
          (ls.map norm).foldl step z = ls.foldl step z := by
        induction ls generalizing z with
        | nil => rfl
        | cons g tail ih =>
          simp only [List.map_cons,List.foldl_cons,(ok g (hls g List.mem_cons_self)).2.2.2]
          exact ih (fun u m => hls u (List.mem_cons_of_mem g m)) _
      change ((gs.map norm).foldl step _).getD C.output false = (C.gates.foldl step w).getD C.output false
      rw [cs,List.foldl_cons,appended,mapped gs (fun _ m => m)]
    have rr : (D.gates.filter read).length = 2 := by simpa only [D,cs,List.drop_succ_cons,List.drop_zero,norm,read] using readers
    let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    have eq0 : ∀ y : Fin 8 → Bool, F (Fin.cons false y) = ([1,10,19,5,14,23,38,47,60] : List ℕ).any (fun e =>
          y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8))) := by
      intro y
      have truth : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, ((false && (v0)) || ((v0) && (v1)) || ((v1) && (v2)) || ((v2) && (v3)) || ((v3) && false) || (false && (v4)) || ((v0) && (v5)) || ((v1) && (v6)) || ((v2) && (v7)) || ((v4) && (v6)) || ((v5) && (v7)) || ((v7) && (v4))) = ((v0 && v1) || ((v1 && v2) || ((v2 && v3) || ((v0 && v5) || ((v1 && v6) || ((v2 && v7) || ((v4 && v6) || ((v5 && v7) || ((v7 && v4) || false))))))))) := by
        decide +kernel
      exact truth (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
    have eq1 : ∀ y : Fin 8 → Bool, F (Fin.cons true y) = (y 0 || y 3 || y 4 || (y 1 && y 2) || (y 1 && y 6) || (y 2 && y 7) || (y 5 && y 7)) := by
      intro y
      have truth : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, ((true && (v0)) || ((v0) && (v1)) || ((v1) && (v2)) || ((v2) && (v3)) || ((v3) && true) || (true && (v4)) || ((v0) && (v5)) || ((v1) && (v6)) || ((v2) && (v7)) || ((v4) && (v6)) || ((v5) && (v7)) || ((v7) && (v4))) = (v0 || v3 || v4 || (v1 && v2) || (v1 && v6) || (v2 && v7) || (v5 && v7)) := by
        decide +kernel
      exact truth (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
    have at0 (y : Fin 8 → Bool) : D.eval (false :: List.ofFn y ++ [true]) = ([1,10,19,5,14,23,38,47,60] : List ℕ).any (fun e =>
          y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8))) :=
      (agree false y).trans ((congrFun target _).trans (eq0 y))
    have at1 (y : Fin 8 → Bool) : D.eval (true :: List.ofFn y ++ [false]) = (y 0 || y 3 || y 4 || (y 1 && y 2) || (y 1 && y 6) || (y 2 && y 7) || (y 5 && y 7)) :=
      (agree true y).trans ((congrFun target _).trans (eq1 y))
    have budget : D.size ≤ 14 := by
      change (gs.map norm).length ≤ 14
      change C.gates.length ≤ 15 at size
      rw [cs] at size
      simp only [List.length_map, List.length_cons] at *
      omega
    have noDirect (P : List Gate) (a : Gate) (R : List Gate)
        (h : D.gates = P ++ a :: R)
        (clamp : a.op = .and ∧ 0 ∈ a.inputs ∨ a.op = .or ∧ 9 ∈ a.inputs)
        (b : Gate) (hb : b ∈ R) (ordinary : read b = false) : 10+P.length ∉ b.inputs := by
      intro edge
      apply noBridge
      refine ⟨P,a,R,?_,clamp,b,hb,ordinary,edge⟩
      simpa only [D,cs,List.drop_succ_cons,List.drop_zero,norm] using h
    let zero : Fin 8 → Bool := fun _ => false
    let single : Fin 8 → Bool := fun i => decide (i = 0)
    let pair : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have varies : ∀ t : Bool, ∃ y y' : Fin 8 → Bool,
        D.eval (t :: List.ofFn y ++ [!t]) ≠ D.eval (t :: List.ofFn y' ++ [!t]) := by
      intro t
      cases t
      · refine ⟨zero,pair,?_⟩
        change D.eval (false :: List.ofFn zero ++ [true]) ≠ D.eval (false :: List.ofFn pair ++ [true])
        rw [at0,at0]
        decide
      · refine ⟨zero,single,?_⟩
        change D.eval (true :: List.ofFn zero ++ [false]) ≠ D.eval (true :: List.ofFn single ++ [false])
        rw [at1,at1]
        decide
    have depends : D.eval (false :: List.ofFn single ++ [true]) ≠
        D.eval (true :: List.ofFn single ++ [false]) := by
      rw [at0,at1]
      decide
    obtain ⟨P,a,R,h,reader,differs,b,hb,ordinary,edge⟩ := exportsPin D fanD notD varies single depends
    apply remaining D fanD notD budget rr noDirect ⟨P,a,R,h,reader,differs,b,hb,ordinary,edge⟩
    intro t y
    cases t
    · exact at0 y
    · change D.eval (true :: List.ofFn y ++ [false]) =
        ((y 0 || y 3 || y 4) || ([1,10,19,5,14,23,38,47,60] : List ℕ).any
          (fun e => y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8))))
      rw [at1]
      have absorption : ∀ a b c d e f g h : Bool,
          (a || d || e || (b && c) || (b && g) || (c && h) || (f && h)) =
          ((a || d || e) || ((a && b) || ((b && c) || ((c && d) || ((a && f) || ((b && g) ||
            ((c && h) || ((e && g) || ((f && h) || ((h && e) || false)))))))))) := by decide +kernel
      exact absorption (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
