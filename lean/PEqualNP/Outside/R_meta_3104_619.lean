import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3104_619
    (empty_prefix : let f := (fun x : Fin 8 → Bool =>
        ([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] :
          List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2))
      ∀ A B : Circuit, ∀ k : ℕ, FanInTwo A → FanInTwo B →
      A.size + B.size ≤ 13 → A.size = 0 → k ≤ 9 + A.size →
      10 + A.size ≤ B.output → B.output < 10 + A.size + B.size →
      let w (b : Bool) (x : Fin 8 → Bool) := A.wires (List.ofFn x ++ [x 1 || b])
      (∀ x, B.eval (w false x ++ [(w false x).getD k false]) = f x) →
      ∃ x, B.eval (w true x ++ [true]) ≠ (f x || x 0 || x 3))
    (nonempty_prefix : let f := (fun x : Fin 8 → Bool =>
        ([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] :
          List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2))
      ∀ A B : Circuit, ∀ k : ℕ, FanInTwo A → FanInTwo B →
      A.size + B.size ≤ 13 → 0 < A.size → k ≤ 9 + A.size →
      10 + A.size ≤ B.output → B.output < 10 + A.size + B.size →
      let w (b : Bool) (x : Fin 8 → Bool) := A.wires (List.ofFn x ++ [x 1 || b])
      (∀ x, B.eval (w false x ++ [(w false x).getD k false]) = f x) →
      ∃ x, B.eval (w true x ++ [true]) ≠ (f x || x 0 || x 3)) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         have x8 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x8 : Bool) (x9 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x9 ++ [x9 (1 : Fin (8 : ℕ)) || x8]);         (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.false x9 ++ [(x8 Bool.false x9).getD x4 Bool.false]) = x1 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.true x10 ++ [Bool.true]) ≠ (x1 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  intro f A B k fanA fanB budget w base



  let run (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have old_wire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi

  have run_length (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
      rw [ih]
      simp
      omega

  let target (x : Fin 8 → Bool) : Bool :=
    ([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] :
      List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2)

  let upperTarget (x : Fin 8 → Bool) : Bool := target x || x 0 || x 3

  let preWires (A : Circuit) (b : Bool) (x : Fin 8 → Bool) : List Bool :=
    A.wires (List.ofFn x ++ [x 1 || b])

  have preWires_length (A : Circuit) (b : Bool) (x : Fin 8 → Bool) :
      (preWires A b x).length = 9 + A.size := by
    change (run A.gates (List.ofFn x ++ [x 1 || b])).length = 9 + A.gates.length
    rw [run_length]
    simp only [List.length_append, List.length_ofFn, List.length_singleton]

  have output_bounds (A B : Circuit) (k : ℕ)
      (base : ∀ x, B.eval (preWires A false x ++ [(preWires A false x).getD k false]) = target x)
      (upper : ∀ x, B.eval (preWires A true x ++ [true]) = upperTarget x) :
      10 + A.size ≤ B.output ∧ B.output < 10 + A.size + B.size := by
    let witness : Fin 8 → Bool := ![false,true,false,true,false,false,false,false]
    have ht : target witness = false := by decide
    have hu : upperTarget witness = true := by decide
    have same : preWires A false witness = preWires A true witness := rfl
    have lo : 10 + A.size ≤ B.output := by
      by_contra h
      by_cases old : B.output < 9 + A.size
      · have lb := preWires_length A false witness
        have lu := preWires_length A true witness
        have eqb := old_wire B.gates
          (preWires A false witness ++ [(preWires A false witness).getD k false]) B.output (by simp; omega)
        have equ := old_wire B.gates (preWires A true witness ++ [true]) B.output (by simp; omega)
        rw [List.getD_append _ _ _ _ (by omega)] at eqb equ
        have hb := base witness
        have hh := upper witness
        change (run B.gates _).getD B.output false = _ at hb hh
        rw [eqb, ht, same] at hb
        rw [equ, hu, hb] at hh
        contradiction
      · have atMark : B.output = 9 + A.size := by omega
        let zero : Fin 8 → Bool := fun _ => false
        have lu := preWires_length A true zero
        have equ := old_wire B.gates (preWires A true zero ++ [true]) B.output (by simp; omega)
        rw [List.getD_append_right _ _ _ _ (by omega), atMark, lu] at equ
        have hh := upper zero
        change (run B.gates _).getD B.output false = _ at hh
        rw [atMark, equ] at hh
        have hz : upperTarget zero = false := by decide
        simp only [Nat.sub_self, List.getD_cons_zero, hz] at hh
        contradiction
    refine ⟨lo, ?_⟩
    by_contra h
    have hl : (run B.gates (preWires A true witness ++ [true])).length =
        10 + A.size + B.size := by
      rw [run_length]
      have lp := preWires_length A true witness
      change (preWires A true witness ++ [true]).length + B.gates.length = 10 + A.size + B.gates.length
      simp only [List.length_append, List.length_singleton, lp]
      omega
    have ho := List.getD_eq_default (run B.gates (preWires A true witness ++ [true])) false
      (n := B.output) (by omega)
    have hh := upper witness
    change (run B.gates _).getD B.output false = _ at hh
    rw [ho, hu] at hh
    contradiction

  have clamp_mark (A : Circuit) (k : ℕ) (x : Fin 8 → Bool) :
      (preWires A false x).getD (min k (9 + A.size)) false =
        (preWires A false x).getD k false := by
    by_cases h : k ≤ 9 + A.size
    · rw [Nat.min_eq_left h]
    · have hle : 9 + A.size ≤ k := by omega
      rw [Nat.min_eq_right hle]
      have hl := preWires_length A false x
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

  have baseCompact : ∀ x,
      B.eval (preWires A false x ++ [(preWires A false x).getD k false]) = target x := by
    intro x
    have h := base x
    change B.eval (preWires A false x ++ [(preWires A false x).getD k false]) = f x at h
    simpa only [f, target, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using h
  by_contra! agreement
  have upperCompact : ∀ x, B.eval (preWires A true x ++ [true]) = upperTarget x := by
    intro x
    have h := agreement x
    change B.eval (preWires A true x ++ [true]) = (f x || x 0 || x 3) at h
    simpa only [f, target, upperTarget, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc] using h
  have bounds := output_bounds A B k baseCompact upperCompact
  let mark := min k (9 + A.size)
  have markBound : mark ≤ 9 + A.size := Nat.min_le_right _ _
  have baseNormalized : ∀ x,
      B.eval (preWires A false x ++ [(preWires A false x).getD mark false]) = target x := by
    intro x
    change B.eval (preWires A false x ++ [(preWires A false x).getD (min k (9 + A.size)) false]) = _
    rw [clamp_mark]
    exact baseCompact x
  have failure : ∃ x, B.eval (preWires A true x ++ [true]) ≠ upperTarget x := by
    by_cases empty : A.size = 0
    · exact empty_prefix A B mark fanA fanB budget empty markBound bounds.1 bounds.2 baseNormalized
    · exact nonempty_prefix A B mark fanA fanB budget (by omega) markBound bounds.1 bounds.2 baseNormalized
  obtain ⟨x, hx⟩ := failure
  exact hx (upperCompact x)
