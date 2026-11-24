import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_4962_103
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → x1.gates[(1 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (9 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ k < (9 : ℕ), ∃ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), (2 : ℕ) ≤ i ∧ x1.gates[i]? = Option.some g ∧ k ∈ g.inputs) → (16 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → x1.gates[(1 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(2 : ℕ), (9 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ k < (9 : ℕ), ∃ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), (2 : ℕ) ≤ i ∧ x1.gates[i]? = Option.some g ∧ k ∈ g.inputs) → (16 : ℕ) ≤ x1.size)
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → x1.gates[(1 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(7 : ℕ), (9 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ k < (9 : ℕ), ∃ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), (2 : ℕ) ≤ i ∧ x1.gates[i]? = Option.some g ∧ k ∈ g.inputs) → (16 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ x5 < (9 : ℕ), x5 ≠ (4 : ℕ) → x5 ≠ (6 : ℕ) → x1.gates[(1 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, (9 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (16 : ℕ) ≤ x1.size := by
  obtain ⟨rho, hrho⟩ : ∃ rho : (Fin 9 → Fin 9) → ℕ → ℕ, ∀ p i, rho p i = if h : i < 9 then ((p ⟨i, h⟩ : Fin 9) : ℕ) else i :=
    ⟨fun p i => if h : i < 9 then ((p ⟨i, h⟩ : Fin 9) : ℕ) else i, fun _ _ => rfl⟩
  obtain ⟨rcirc, hrcirc⟩ : ∃ rcirc : (Fin 9 → Fin 9) → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Circuit,
      ∀ p C, rcirc p C = ⟨C.gates.map (fun g => (⟨g.op, g.inputs.map (rho p)⟩ : PEqualNP.CircuitLowerBounds.Gate)), rho p C.output⟩ :=
    ⟨fun p C => ⟨C.gates.map (fun g => (⟨g.op, g.inputs.map (rho p)⟩ : PEqualNP.CircuitLowerBounds.Gate)), rho p C.output⟩, fun _ _ => rfl⟩
  have sim : ∀ (ρ : ℕ → ℕ), (∀ i, 9 ≤ i → ρ i = i) → (∀ i, i < 9 → ρ i < 9) →
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w2 : List Bool),
      w2.length = w.length → 9 ≤ w.length → (∀ i, w2.getD (ρ i) false = w.getD i false) →
      ∀ i, ((gs.map (fun g => (⟨g.op, g.inputs.map ρ⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD (ρ i) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
    intro ρ hfix hlt gs
    induction gs with
    | nil => intro w w2 _ _ hw i; exact hw i
    | cons g gs ih =>
      intro w w2 hl h9 hw
      have hv : g.op.eval ((g.inputs.map ρ).map fun i => w2.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun a _ => hw a)
      have hext : ∀ k, (w2 ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (ρ k) false =
          (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD k false := by
        intro k
        simp only [List.getD_eq_getElem?_getD] at hw ⊢
        by_cases hk : k < 9
        · have hk1 : ρ k < w2.length := by have := hlt k hk; omega
          have hk2 : k < w.length := by omega
          rw [List.getElem?_append_left hk1, List.getElem?_append_left hk2]
          exact hw k
        · have hr : ρ k = k := hfix k (by omega)
          rw [hr]
          by_cases hk2 : k < w.length
          · have hk1 : k < w2.length := by omega
            rw [List.getElem?_append_left hk1, List.getElem?_append_left hk2]
            have := hw k
            rw [hr] at this
            exact this
          · have hk1 : w2.length ≤ k := by omega
            have hk3 : w.length ≤ k := by omega
            rw [List.getElem?_append_right hk1, List.getElem?_append_right hk3, hl]
      have hext2 : ∀ k, (w2 ++ [g.op.eval ((g.inputs.map ρ).map fun i => w2.getD i false)]).getD (ρ k) false =
          (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD k false := by
        intro k
        rw [hv]
        exact hext k
      intro i
      exact ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w2 ++ [g.op.eval ((g.inputs.map ρ).map fun i => w2.getD i false)])
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hext2 i
  have wires_rel : ∀ (p : Fin 9 → Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 9 → Bool) (i : ℕ),
      ((rcirc p C).wires (List.ofFn x)).getD (rho p i) false =
        (C.wires (List.ofFn (fun k => x (p k)))).getD i false := by
    intro p C x i
    have hfix : ∀ i, 9 ≤ i → rho p i = i := by
      intro i hi
      rw [hrho, dif_neg (by omega)]
    have hlt : ∀ i, i < 9 → rho p i < 9 := by
      intro i hi
      rw [hrho, dif_pos hi]
      exact (p ⟨i, hi⟩).isLt
    have base : ∀ i, (List.ofFn x).getD (rho p i) false = (List.ofFn (fun k => x (p k))).getD i false := by
      intro i
      by_cases hi : i < 9
      · rw [hrho, dif_pos hi, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_ofFn, List.getElem?_ofFn, dif_pos (p ⟨i, hi⟩).isLt, dif_pos hi]
      · rw [hfix i (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_ofFn, List.getElem?_ofFn, dif_neg hi, dif_neg hi]
    rw [hrcirc]
    exact sim (rho p) hfix hlt C.gates (List.ofFn (fun k => x (p k))) (List.ofFn x) (by simp) (by simp) base i
  have eta9 : ∀ x : Fin 9 → Bool, ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] = x := by
    intro x
    funext k
    fin_cases k <;> rfl
  have autCheck : ∀ p : Fin 9 → Fin 9,
      (∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
        (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) (fun k => ![b0, b1, b2, b3, b4, b5, b6, b7, b8] (p k)) =
        (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) ![b0, b1, b2, b3, b4, b5, b6, b7, b8]) →
      ∀ x : Fin 9 → Bool, (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) (fun k => x (p k)) = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x := by
    intro p h x
    have h1 := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    rw [eta9 x] at h1
    exact h1
  have preserved : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have hlt : i < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have e := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i hlt
      have e2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false = w.getD i false := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      exact e.trans e2
  have agree : ∀ (v : ℕ) (gs : List Gate) (wa wb : List Bool),
      (∀ g ∈ gs, v ∉ g.inputs) → wa.length = wb.length → v < wa.length →
      (∀ i, i ≠ v → wa.getD i false = wb.getD i false) →
      ∀ i, i ≠ v → (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wa).getD i false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wb).getD i false := by
    intro v gs
    induction gs with
    | nil => intro wa wb _ _ _ h; exact h
    | cons g gs ih =>
      intro wa wb hno hl hv h
      have hval : g.op.eval (g.inputs.map fun i => wa.getD i false) =
          g.op.eval (g.inputs.map fun i => wb.getD i false) := by
        congr 1
        apply List.map_congr_left
        intro a ha
        exact h a (fun e => hno g (List.mem_cons_self ..) (e ▸ ha))
      have hext : ∀ i, i ≠ v → (wa ++ [g.op.eval (g.inputs.map fun i => wa.getD i false)]).getD i false =
          (wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)]).getD i false := by
        intro i hi
        rw [hval]
        simp only [List.getD_eq_getElem?_getD] at h ⊢
        by_cases hi2 : i < wa.length
        · have hi3 : i < wb.length := by omega
          rw [List.getElem?_append_left hi2, List.getElem?_append_left hi3]
          exact h i hi
        · have hi3 : wa.length ≤ i := by omega
          have hi4 : wb.length ≤ i := by omega
          rw [List.getElem?_append_right hi3, List.getElem?_append_right hi4, hl]
      exact ih (wa ++ [g.op.eval (g.inputs.map fun i => wa.getD i false)])
        (wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)])
        (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hext
  have get11 : ∀ (x : Fin 9 → Bool) (a b : Bool) (i : ℕ),
      ((List.ofFn x ++ [a]) ++ [b]).getD i false =
        if h : i < 9 then x ⟨i, h⟩ else if i = 9 then a else if i = 10 then b else false := by
    intro x a b i
    simp only [List.getD_eq_getElem?_getD]
    by_cases hi9 : i < 9
    · have l1 : i < (List.ofFn x ++ [a]).length := by simp; omega
      have l3 : i < (List.ofFn x).length := by simp; omega
      rw [List.getElem?_append_left l1, List.getElem?_append_left l3, List.getElem?_ofFn, dif_pos hi9, dif_pos hi9]
      rfl
    · have l3 : (List.ofFn x).length ≤ i := by simp; omega
      rw [dif_neg hi9]
      by_cases hi10 : i < 10
      · have l1 : i < (List.ofFn x ++ [a]).length := by simp; omega
        have e9 : i = 9 := by omega
        subst e9
        rw [List.getElem?_append_left l1, List.getElem?_append_right l3]
        simp
      · have l1 : (List.ofFn x ++ [a]).length ≤ i := by simp; omega
        rw [List.getElem?_append_right l1, if_neg (by omega)]
        by_cases h10 : i = 10
        · subst h10
          simp
        · rw [if_neg h10]
          have l4 : [b].length ≤ i - (List.ofFn x ++ [a]).length := by simp; omega
          rw [List.getElem?_eq_none l4]
          rfl
  have getA : ∀ (x : Fin 9 → Bool) (a : Bool) (j : ℕ) (hj : j < 9), (List.ofFn x ++ [a]).getD j false = x ⟨j, hj⟩ := by
    intro x a j hj
    have l1 : j < (List.ofFn x).length := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left l1, List.getElem?_ofFn, dif_pos hj]
    try rfl
  have getB : ∀ (x : Fin 9 → Bool) (a : Bool), (List.ofFn x ++ [a]).getD 9 false = a := by
    intro x a
    have l1 : (List.ofFn x).length ≤ 9 := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right l1]
    simp
  have nodep : ∀ (C : Circuit) (j v : ℕ) (xa xb : Fin 9 → Bool),
      (∀ (x3 : Fin 9 → Bool), (C.wires (List.ofFn x3)).getD 9 false = (x3 4 || x3 6)) →
      C.gates[(1 : ℕ)]? = some { op := GateOp.or, inputs := [j, 9] } → (hj : j < 9) → v < 9 →
      (∀ (i : ℕ) (g : Gate), 2 ≤ i → C.gates[i]? = some g → v ∉ g.inputs) →
      (∀ k : Fin 9, (k : ℕ) ≠ v → xa k = xb k) →
      (xa 4 || xa 6) = (xb 4 || xb 6) →
      (xa ⟨j, hj⟩ || (xa 4 || xa 6)) = (xb ⟨j, hj⟩ || (xb 4 || xb 6)) →
      ∀ i, i ≠ v → (C.wires (List.ofFn xa)).getD i false = (C.wires (List.ofFn xb)).getD i false := by
    intro C j v xa xb hw9 hg1 hj hv hno hdiff h9 h10
    obtain ⟨gs, o⟩ := C
    rcases gs with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
    · simp at hg1
    · simp at hg1
    · have hg1' : g1 = { op := GateOp.or, inputs := [j, 9] } := by simpa using hg1
      subst hg1'
      have hno' : ∀ g ∈ rest, v ∉ g.inputs := by
        intro g hg
        obtain ⟨n, hn, hgn⟩ := List.getElem_of_mem hg
        apply hno (n + 2) g (by omega)
        show (g0 :: _ :: rest)[n + 2]? = some g
        rw [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_eq_getElem hn, hgn]
      have hv0 : ∀ x : Fin 9 → Bool, g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
        intro x
        have e : (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            ((List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]) ++
              [GateOp.or.eval ([j, 9].map fun i => (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).getD i false)])).getD 9 false = (x 4 || x 6) := hw9 x
        rw [preserved _ _ 9 (by simp), get11] at e
        simpa using e
      have hv1 : ∀ (x : Fin 9 → Bool) (a : Bool), GateOp.or.eval ([j, 9].map fun i => (List.ofFn x ++ [a]).getD i false) = (x ⟨j, hj⟩ || a) := by
        intro x a
        simp only [List.map_cons, List.map_nil, getA x a j hj, getB x a, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
      intro i hi
      show (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            ((List.ofFn xa ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn xa).getD i false)]) ++
              [GateOp.or.eval ([j, 9].map fun i => (List.ofFn xa ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn xa).getD i false)]).getD i false)])).getD i false =
          (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            ((List.ofFn xb ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn xb).getD i false)]) ++
              [GateOp.or.eval ([j, 9].map fun i => (List.ofFn xb ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn xb).getD i false)]).getD i false)])).getD i false
      apply agree v rest _ _ hno' (by simp) (by simp; omega) _ i hi
      intro k hk
      rw [get11, get11, hv1, hv1, hv0, hv0]
      by_cases hk9 : k < 9
      · rw [dif_pos hk9, dif_pos hk9]
        exact hdiff ⟨k, hk9⟩ hk
      · rw [dif_neg hk9, dif_neg hk9, h10, h9]
  have readers : ∀ (Ffun : (Fin 9 → Bool) → Bool) (C : Circuit),
      (∀ (x3 : Fin 9 → Bool), (C.wires (List.ofFn x3)).getD 9 false = (x3 4 || x3 6)) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD C.output false = Ffun x) →
      ∀ (j : ℕ) (hj : j < 9), C.gates[(1 : ℕ)]? = some { op := GateOp.or, inputs := [j, 9] } →
      ∀ (v : ℕ) (hv : v < 9) (xa xb xs : Fin 9 → Bool),
      (∀ k : Fin 9, (k : ℕ) ≠ v → xa k = xb k) →
      (xa 4 || xa 6) = (xb 4 || xb 6) →
      (xa ⟨j, hj⟩ || (xa 4 || xa 6)) = (xb ⟨j, hj⟩ || (xb 4 || xb 6)) →
      Ffun xa ≠ Ffun xb → xs ⟨v, hv⟩ ≠ Ffun xs →
      ∃ (i : ℕ) (g : Gate), 2 ≤ i ∧ C.gates[i]? = some g ∧ v ∈ g.inputs := by
    intro Ffun C hw9 hfun j hj hg1 v hv xa xb xs hd h9 h10 hne hxs
    by_contra hno
    push_neg at hno
    by_cases ho : C.output = v
    · have e := hfun xs
      rw [ho] at e
      have e2 : (C.wires (List.ofFn xs)).getD v false = (List.ofFn xs).getD v false :=
        preserved C.gates (List.ofFn xs) v (by simp; omega)
      rw [e2, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hv] at e
      exact hxs e
    · have e := nodep C j v xa xb hw9 hg1 hj hv hno hd h9 h10 C.output ho
      exact hne ((hfun xa).symm.trans (e.trans (hfun xb)))
  have readersR : ∀ (r : ℕ), (r = 0 ∨ r = 2 ∨ r = 7) → ∀ (C : Circuit),
      (∀ (x3 : Fin 9 → Bool), (C.wires (List.ofFn x3)).getD 9 false = (x3 4 || x3 6)) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD C.output false = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x) →
      C.gates[(1 : ℕ)]? = some { op := GateOp.or, inputs := [r, 9] } →
      (∀ k < (9 : ℕ), ∃ (i : ℕ) (g : Gate), 2 ≤ i ∧ C.gates[i]? = some g ∧ k ∈ g.inputs) := by
    intro r hr C hw9 hfun hg1 k hk
    interval_cases k
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 0 (by decide) ![true, true, false, false, true, false, false, false, false] ![false, true, false, false, true, false, false, false, false] ![true, false, false, false, false, false, false, false, false] (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 1 (by decide) ![false, true, true, false, true, false, false, false, false] ![false, false, true, false, true, false, false, false, false] ![false, true, false, false, false, false, false, false, false] (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 2 (by decide) ![false, true, true, false, true, false, false, false, false] ![false, true, false, false, true, false, false, false, false] ![false, false, true, false, false, false, false, false, false] (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 3 (by decide) ![false, false, true, true, true, false, false, false, false] ![false, false, true, false, true, false, false, false, false] ![false, false, false, true, false, false, false, false, false] (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 4 (by decide) ![true, false, false, false, true, false, true, false, false] ![true, false, false, false, false, false, true, false, false] ![false, false, false, false, true, false, false, false, false] (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 5 (by decide) ![false, false, false, false, true, true, false, true, false] ![false, false, false, false, true, false, false, true, false] ![false, false, false, false, false, true, false, false, false] (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 6 (by decide) ![false, true, false, false, true, false, true, false, false] ![false, true, false, false, true, false, false, false, false] ![false, false, false, false, false, false, true, false, false] (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 7 (by decide) ![false, false, true, false, true, false, false, true, false] ![false, false, true, false, true, false, false, false, false] ![false, false, false, false, false, false, false, true, false] (by decide) (by decide) (by decide) (by decide) (by decide)
    · rcases hr with rfl | rfl | rfl <;> exact readers _ C hw9 hfun _ (by decide) hg1 8 (by decide) ![false, false, false, false, true, true, false, false, true] ![false, false, false, false, true, true, false, false, false] ![false, false, false, false, false, false, false, false, true] (by decide) (by decide) (by decide) (by decide) (by decide)
  have main_case : ∀ (p : Fin 9 → Fin 9) (r : ℕ),
      (∀ x : Fin 9 → Bool, (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) (fun k => x (p k)) = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x) →
      (∀ x : Fin 9 → Bool, (x (p 4) || x (p 6)) = (x 4 || x 6)) →
      (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → x1.gates[(1 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [r, (9 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ k < (9 : ℕ), ∃ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), (2 : ℕ) ≤ i ∧ x1.gates[i]? = Option.some g ∧ k ∈ g.inputs) → (16 : ℕ) ≤ x1.size) →
      (∀ (C : Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ (x3 : Fin 9 → Bool), (C.wires (List.ofFn x3)).getD 9 false = (x3 4 || x3 6)) → (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD C.output false = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x) → C.gates[(1 : ℕ)]? = some { op := GateOp.or, inputs := [r, 9] } →
      (∀ k < (9 : ℕ), ∃ (i : ℕ) (g : Gate), 2 ≤ i ∧ C.gates[i]? = some g ∧ k ∈ g.inputs)) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ (x3 : Fin (9 : ℕ) → Bool), (C.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →
      (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) C = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →
      ∀ j : ℕ, rho p j = r →
      C.gates[(1 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [j, (9 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →
      (16 : ℕ) ≤ C.size := by
    intro p r haut hor H RR C hfan hw9 hfun j hj hg1
    have rho9 : rho p 9 = 9 := by rw [hrho, dif_neg (by omega)]
    have hsize : (rcirc p C).size = C.size := by
      rw [hrcirc]
      simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    have f1 : PEqualNP.MetaComplexity.FanInTwo (rcirc p C) := by
      intro g hg
      rw [hrcirc] at hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan a ha).1, by simpa using (hfan a ha).2⟩
    have f2 : ∀ (x3 : Fin (9 : ℕ) → Bool), ((rcirc p C).wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))) := by
      intro x
      have e := wires_rel p C x 9
      rw [rho9] at e
      exact e.trans ((hw9 (fun k => x (p k))).trans (hor x))
    have f3 : PEqualNP.MetaComplexity.circuitFun (9 : ℕ) (rcirc p C) = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
      funext x
      have e := wires_rel p C x C.output
      have ho : (rcirc p C).output = rho p C.output := by rw [hrcirc]
      have hc := congrFun hfun (fun k => x (p k))
      show ((rcirc p C).wires (List.ofFn x)).getD (rcirc p C).output false = _
      rw [ho, e]
      exact hc.trans (haut x)
    have f4 : (rcirc p C).gates[(1 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [r, (9 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } := by
      rw [hrcirc]
      show (C.gates.map (fun g => (⟨g.op, g.inputs.map (rho p)⟩ : PEqualNP.CircuitLowerBounds.Gate)))[1]? = _
      rw [List.getElem?_map, hg1]
      simp [hj, rho9]
    have rall := RR (rcirc p C) f1 f2 (fun x => congrFun f3 x) f4
    rw [← hsize]
    exact H (rcirc p C) f1 f2 f3 f4 rall
  intro C hfan hw9 hfun j hj9 hj4 hj6 hg1
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 C hfan hw9 hfun hg1 (readersR 0 (by decide) C hw9 (fun x => congrFun hfun x) hg1)
  · exact main_case ![1, 0, 5, 8, 6, 2, 4, 7, 3] 0 (autCheck _ (by decide +kernel)) (fun x => Bool.or_comm _ _) h1 (fun C2 _ f2 f3 f4 => readersR 0 (by decide) C2 f2 f3 f4) C hfan hw9 hfun 1 (by rw [hrho]; decide) hg1
  · exact h2 C hfan hw9 hfun hg1 (readersR 2 (by decide) C hw9 (fun x => congrFun hfun x) hg1)
  · exact main_case ![3, 8, 5, 0, 4, 2, 6, 7, 1] 0 (autCheck _ (by decide +kernel)) (fun x => rfl) h1 (fun C2 _ f2 f3 f4 => readersR 0 (by decide) C2 f2 f3 f4) C hfan hw9 hfun 3 (by rw [hrho]; decide) hg1
  · exact main_case ![1, 0, 5, 8, 6, 2, 4, 7, 3] 2 (autCheck _ (by decide +kernel)) (fun x => Bool.or_comm _ _) h2 (fun C2 _ f2 f3 f4 => readersR 2 (by decide) C2 f2 f3 f4) C hfan hw9 hfun 5 (by rw [hrho]; decide) hg1
  · exact h3 C hfan hw9 hfun hg1 (readersR 7 (by decide) C hw9 (fun x => congrFun hfun x) hg1)
  · exact main_case ![8, 3, 2, 1, 6, 5, 4, 7, 0] 0 (autCheck _ (by decide +kernel)) (fun x => Bool.or_comm _ _) h1 (fun C2 _ f2 f3 f4 => readersR 0 (by decide) C2 f2 f3 f4) C hfan hw9 hfun 8 (by rw [hrho]; decide) hg1
