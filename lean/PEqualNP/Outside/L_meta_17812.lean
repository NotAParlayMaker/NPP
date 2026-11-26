import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17812

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step1 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def step2 (x8 : List Bool) (x9 : Bool × ℕ × ℕ) : List Bool :=
  have x10 : Bool := x8.getD x9.2.1 Bool.false
  have x11 : Bool := x8.getD x9.2.2 Bool.false
  x8 ++ [if x9.1 = Bool.true then x10 && x11 else x10 || x11]

def remap (k i : ℕ) : ℕ :=
  if i < 11 + k then i + 2 else 0

def compileGate (k : ℕ) (g : Gate) : Bool × ℕ × ℕ :=
  match g.op with
  | .and =>
    match g.inputs with
    | [] => (true, 1, 1)
    | [i0] => (true, remap k i0, 1)
    | [i0, i1] => (true, remap k i0, remap k i1)
    | _ => (true, 0, 0)
  | .or =>
    match g.inputs with
    | [] => (false, 0, 0)
    | [i0] => (false, remap k i0, 0)
    | [i0, i1] => (false, remap k i0, remap k i1)
    | _ => (false, 0, 0)
  | _ => (false, 0, 0)

def compileFrom : ℕ → List Gate → List (Bool × ℕ × ℕ)
  | _, [] => []
  | k, g :: gs => compileGate k g :: compileFrom (k + 1) gs

def gateMono2 (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem remap_lt (k i : ℕ) : remap k i < 13 + k := by
  unfold remap
  split_ifs <;> omega

theorem getD_remap (w : List Bool) (k i : ℕ) (hw : w.length = 11 + k) :
    (Bool.false :: Bool.true :: w).getD (remap k i) Bool.false = w.getD i Bool.false := by
  unfold remap
  split_ifs with h
  · rfl
  · symm
    exact List.getD_eq_default w Bool.false (by omega)

theorem compileGate_lt (k : ℕ) (g : Gate) :
    (compileGate k g).2.1 < 13 + k ∧ (compileGate k g).2.2 < 13 + k := by
  rcases g with ⟨op, inputs⟩
  cases op with
  | and =>
    cases inputs with
    | nil => simp [compileGate]; omega
    | cons i0 tl =>
      cases tl with
      | nil => exact ⟨remap_lt k i0, by simp [compileGate]; omega⟩
      | cons i1 tl2 =>
        cases tl2 with
        | nil => exact ⟨remap_lt k i0, remap_lt k i1⟩
        | cons _ _ => simp [compileGate]
  | or =>
    cases inputs with
    | nil => simp [compileGate]
    | cons i0 tl =>
      cases tl with
      | nil => exact ⟨remap_lt k i0, by simp [compileGate]⟩
      | cons i1 tl2 =>
        cases tl2 with
        | nil => exact ⟨remap_lt k i0, remap_lt k i1⟩
        | cons _ _ => simp [compileGate]
  | not => simp [compileGate]
  | mod _ => simp [compileGate]
  | maj => simp [compileGate]

theorem compileFrom_length (k : ℕ) (gs : List Gate) :
    (compileFrom k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [compileFrom, ih]

theorem compileFrom_lt (k : ℕ) (gs : List Gate) (idx : ℕ) (t : Bool × ℕ × ℕ)
    (h : (compileFrom k gs)[idx]? = Option.some t) :
    t.2.1 < 13 + (k + idx) ∧ t.2.2 < 13 + (k + idx) := by
  induction gs generalizing k idx with
  | nil => simp [compileFrom] at h
  | cons g gs ih =>
    cases idx with
    | zero =>
      simp only [compileFrom, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simpa using compileGate_lt k g
    | succ idx' =>
      simp only [compileFrom, List.getElem?_cons_succ] at h
      have hrec := ih (k + 1) idx' h
      have heq : k + 1 + idx' = k + (idx' + 1) := by omega
      rwa [heq] at hrec

theorem step2_compileGate (k : ℕ) (w : List Bool) (g : Gate)
    (hw : w.length = 11 + k) (hg : gateMono2 g) :
    step2 (Bool.false :: Bool.true :: w) (compileGate k g) =
      Bool.false :: Bool.true :: step1 w g := by
  rcases g with ⟨op, inputs⟩
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · cases inputs with
    | nil => rfl
    | cons i0 tl =>
      cases tl with
      | nil =>
        simp only [step2, step1, compileGate, GateOp.eval, List.map, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, ite_true, List.cons_append]
        rw [getD_remap w k i0 hw]
        simp
      | cons i1 tl2 =>
        cases tl2 with
        | nil =>
          simp only [step2, step1, compileGate, GateOp.eval, List.map, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, ite_true, List.cons_append]
          rw [getD_remap w k i0 hw, getD_remap w k i1 hw]
        | cons _ _ => simp at hlen
  · cases inputs with
    | nil => rfl
    | cons i0 tl =>
      cases tl with
      | nil =>
        simp only [step2, step1, compileGate, GateOp.eval, List.map, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, Bool.false_eq_true, ite_false, List.cons_append]
        rw [getD_remap w k i0 hw]
        simp
      | cons i1 tl2 =>
        cases tl2 with
        | nil =>
          simp only [step2, step1, compileGate, GateOp.eval, List.map, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.false_eq_true, ite_false, List.cons_append]
          rw [getD_remap w k i0 hw, getD_remap w k i1 hw]
        | cons _ _ => simp at hlen

theorem foldl_step1_length (gs : List Gate) (w : List Bool) :
    (List.foldl step1 w gs).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [step1]
    omega

theorem foldl_compileFrom (k : ℕ) (gs : List Gate) (w : List Bool)
    (hw : w.length = 11 + k) (hmono : ∀ g ∈ gs, gateMono2 g) :
    List.foldl step2 (Bool.false :: Bool.true :: w) (compileFrom k gs) =
      Bool.false :: Bool.true :: List.foldl step1 w gs := by
  induction gs generalizing k w with
  | nil => rfl
  | cons g gs ih =>
    simp only [compileFrom, List.foldl_cons]
    rw [step2_compileGate k w g hw (hmono g (List.mem_cons_self ..))]
    exact ih (k + 1) (step1 w g) (by simp [step1, hw]; omega)
      (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg'))

theorem main_proof (x1 : Circuit) (hmono : Monotone2 x1) (hsize : x1.size ≤ 18) :
    ∃ (x4 : List (Bool × ℕ × ℕ)) (x5 : ℕ),
      x4.length ≤ 18 ∧
      x5 < 13 + x4.length ∧
      (∀ (x6 : ℕ) (x7 : Bool × ℕ × ℕ), x4[x6]? = Option.some x7 →
        x7.2.1 < 13 + x6 ∧ x7.2.2 < 13 + x6) ∧
      ∀ (x6 : List Bool), x6.length = 11 →
        (List.foldl step2 (Bool.false :: Bool.true :: x6) x4).getD x5 Bool.false = x1.eval x6 := by
  refine ⟨compileFrom 0 x1.gates, remap x1.gates.length x1.output, ?_, ?_, ?_, ?_⟩
  · rw [compileFrom_length]
    exact hsize
  · rw [compileFrom_length]
    exact remap_lt x1.gates.length x1.output
  · intro idx t ht
    simpa using compileFrom_lt 0 x1.gates idx t ht
  · intro x6 hx6
    rw [foldl_compileFrom 0 x1.gates x6 hx6 hmono]
    have hlen : (List.foldl step1 x6 x1.gates).length = 11 + x1.gates.length := by
      rw [foldl_step1_length, hx6]
    exact getD_remap (List.foldl step1 x6 x1.gates) x1.gates.length x1.output hlen

end PEqualNP.Outside.L_meta_17812

theorem PEqualNP.Outside.L_meta_17812 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       ∃ (x4 : List (Bool × ℕ × ℕ)) (x5 : ℕ),         x4.length ≤ (18 : ℕ) ∧           x5 < (13 : ℕ) + x4.length ∧             (∀ (x6 : ℕ) (x7 : Bool × ℕ × ℕ), x4[x6]? = Option.some x7 → x7.2.1 < (13 : ℕ) + x6 ∧ x7.2.2 < (13 : ℕ) + x6) ∧               ∀ (x6 : List Bool),                 x6.length = (11 : ℕ) →                   (List.foldl                           (fun (x8 : List Bool) (x9 : Bool × ℕ × ℕ) =>                             have x10 : Bool := x8.getD x9.2.1 Bool.false;                             have x11 : Bool := x8.getD x9.2.2 Bool.false;                             x8 ++ [if x9.1 = Bool.true then x10 && x11 else x10 || x11])                           (Bool.false :: Bool.true :: x6) x4).getD                       x5 Bool.false =                     x1.eval x6) := by
  exact PEqualNP.Outside.L_meta_17812.main_proof
