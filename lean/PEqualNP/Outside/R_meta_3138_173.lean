import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3138_173
    (lower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) →
      15 ≤ C.size)
    (tight :
      have F : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5));
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (p : ℕ), gs.length = 13 →
        PEqualNP.MetaComplexity.FanInTwo (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) →
        gs.countP (fun g => g.op.eval [false]) ≤ 1 →
        10 ≤ p → p < 22 →
        ∃ x : Fin 9 → Bool,
          have w : List Bool := (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3]);
          (w.getD p false || w.getD 22 false) ≠ F x) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false || x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  let Gate := PEqualNP.CircuitLowerBounds.Gate
  let Circuit := PEqualNP.CircuitLowerBounds.Circuit
  let FanInTwo := PEqualNP.MetaComplexity.FanInTwo
  let edge : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let prefixOr : Gate := ⟨.or, [0, 3]⟩
  let mergeOr (p q : ℕ) : Gate := ⟨.or, [p, q]⟩
  let withAux (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 3]
  let interim (gs : List Gate) (x : Fin 9 → Bool) : List Bool :=
    (⟨gs, 0⟩ : Circuit).wires (withAux x)
  let badOn (gs : List Gate) (p q : ℕ) (x : Fin 9 → Bool) : Prop :=
    ((interim gs x).getD p false || (interim gs x).getD q false) ≠ edge x
  let fanin (gs : List Gate) : Prop := FanInTwo ⟨gs, 0⟩
  let negations (gs : List Gate) : ℕ := gs.countP (fun g => g.op.eval [false])

  have step_length (w : List Bool) (g : Gate) :
      (step w g).length = w.length + 1 := by simp [step]

  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, step_length, List.length_cons]; omega

  have prefix_length (gs : List Gate) (x : Fin 9 → Bool) :
      (interim gs x).length = 10 + gs.length := by
    change (gs.foldl step (withAux x)).length = _
    rw [fold_length]
    simp [withAux]

  have fold_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by rw [step_length]; omega)]
      exact List.getD_append _ _ _ _ hi

  have prefix_eval (gs : List Gate) (x : Fin 9 → Bool) :
      (⟨prefixOr :: gs, 0⟩ : Circuit).wires (List.ofFn x) = interim gs x := by
    change gs.foldl step (step (List.ofFn x) prefixOr) = gs.foldl step (withAux x)
    simp [step, prefixOr, withAux, PEqualNP.CircuitLowerBounds.GateOp.eval]

  have single_fanin (gs : List Gate) (h : fanin gs) (o : ℕ) :
      FanInTwo ⟨prefixOr :: gs, o⟩ := by
    intro g hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp [prefixOr]
    · exact h _ hm

  have merged_fanin (gs : List Gate) (h : fanin gs) (p q o : ℕ) :
      FanInTwo ⟨prefixOr :: (gs ++ [mergeOr p q]), o⟩ := by
    apply single_fanin
    intro g hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h _ hm
    · simp [mergeOr]

  have append_eval (gs : List Gate) (g : Gate) (x : Fin 9 → Bool) :
      interim (gs ++ [g]) x = step (interim gs x) g := by
    simp [interim, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_append, step]

  have merged_eval (gs : List Gate) (p q : ℕ) (x : Fin 9 → Bool) :
      (⟨prefixOr :: (gs ++ [mergeOr p q]), 10 + gs.length⟩ : Circuit).eval (List.ofFn x) =
        ((interim gs x).getD p false || (interim gs x).getD q false) := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    change ((⟨prefixOr :: (gs ++ [mergeOr p q]), 0⟩ : Circuit).wires
      (List.ofFn x)).getD (10 + gs.length) false = _
    rw [prefix_eval, append_eval, ← prefix_length gs x]
    simp [step, mergeOr, PEqualNP.CircuitLowerBounds.GateOp.eval]

  have low_wire (gs : List Gate) (i : ℕ) (hi : i < 10) :
      ∃ x : Fin 9 → Bool, (interim gs x).getD i false = true ∧ edge x = false := by
    let seed (k : Fin 10) (j : Fin 9) := decide (j.val = if k.val = 9 then 0 else k.val)
    have seeds : ∀ k : Fin 10, (withAux (seed k)).getD k.val false = true ∧
        edge (seed k) = false := by dsimp [seed]; decide
    let x := seed ⟨i, hi⟩
    obtain ⟨hx, he⟩ := seeds ⟨i, hi⟩
    refine ⟨x, ?_, he⟩
    change ((gs.foldl step (withAux x)).getD i false) = true
    rw [fold_getD _ _ _ (by simpa [withAux] using hi)]
    exact hx

  change ∀ (gs : List Gate) (p q : ℕ), gs.length = 13 → fanin gs → negations gs ≤ 1 →
    p ≤ 24 → q ≤ 24 → ∃ x, badOn gs p q x
  intro gs p q len ok neg _ _
  by_contra! no
  have same : ∀ x : Fin 9 → Bool,
      ((interim gs x).getD p false || (interim gs x).getD q false) = edge x := by
    intro x
    simpa only [badOn, not_not] using no x
  have projected (o : ℕ) (he : ∀ x : Fin 9 → Bool, (interim gs x).getD o false = edge x) : False := by
    let C : Circuit := ⟨prefixOr :: gs, o⟩
    have large := lower C (single_fanin gs ok o) (fun x => by
      change ((⟨prefixOr :: gs, 0⟩ : Circuit).wires (List.ofFn x)).getD o false = edge x
      rw [prefix_eval]
      exact he x)
    have size : C.size = 14 := by simp [C, PEqualNP.CircuitLowerBounds.Circuit.size, len]
    omega
  have pLT : p < 23 := by
    by_contra! hp
    apply projected q
    intro x
    have h := same x
    rwa [List.getD_eq_default _ _ (n := p) (by rw [prefix_length, len]; exact hp), Bool.false_or] at h
  have qLT : q < 23 := by
    by_contra! hq
    apply projected p
    intro x
    have h := same x
    rwa [List.getD_eq_default _ _ (n := q) (by rw [prefix_length, len]; exact hq), Bool.or_false] at h
  have distinct : p ≠ q := by
    intro eq
    apply projected p
    intro x
    simpa only [← eq, Bool.or_self] using same x
  have pGe : 10 ≤ p := by
    by_contra! hp
    obtain ⟨x, hx, he⟩ := low_wire gs p hp
    have h := same x
    rw [hx, he, Bool.true_or] at h
    cases h
  have qGe : 10 ≤ q := by
    by_contra! hq
    obtain ⟨x, hx, he⟩ := low_wire gs q hq
    have h := same x
    rw [hx, he, Bool.or_true] at h
    cases h
  have last : p = 22 ∨ q = 22 := by
    by_contra! before
    have hp : p < 22 := by omega
    have hq : q < 22 := by omega
    obtain ⟨pre, g, hpre⟩ : ∃ pre : List Gate, ∃ g : Gate, gs = pre ++ [g] := by
      induction gs using List.reverseRecOn with
      | nil => simp at len
      | append_singleton pre g ih => exact ⟨pre, g, rfl⟩
    have preLen : pre.length = 12 := by simp [hpre] at len; omega
    have preOk : fanin pre := fun g hg => ok g (by rw [hpre]; exact List.mem_append_left _ hg)
    let C : Circuit := ⟨prefixOr :: (pre ++ [mergeOr p q]), 10 + pre.length⟩
    have large := lower C (merged_fanin pre preOk p q _) (fun x => by
      change (⟨prefixOr :: (pre ++ [mergeOr p q]), 10 + pre.length⟩ : Circuit).eval _ = _
      rw [merged_eval]
      have h := same x
      rw [hpre, append_eval] at h
      have wlen : (interim pre x).length = 22 := by rw [prefix_length, preLen]
      simpa only [step, List.getD_append _ _ _ _ (wlen ▸ hp),
        List.getD_append _ _ _ _ (wlen ▸ hq)] using h)
    have size : C.size = 14 := by simp [C, PEqualNP.CircuitLowerBounds.Circuit.size, preLen]
    omega
  rcases last with hp | hq
  · obtain ⟨x, hx⟩ := tight gs q len ok neg qGe (by omega)
    change badOn gs q 22 x at hx
    exact hx (by simpa only [badOn, hp, Bool.or_comm] using same x)
  · obtain ⟨x, hx⟩ := tight gs p len ok neg pGe (by omega)
    change badOn gs p 22 x at hx
    exact hx (by simpa only [badOn, hq] using same x)
