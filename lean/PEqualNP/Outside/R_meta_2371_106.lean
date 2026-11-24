import Mathlib
import PEqualNP.Defs

-- Case split on the first gate up to the symmetries of the Petersen graph: the gate is unary
-- on input 0 and not a plain copy or constant false (so NOT or constant true), an AND or OR on
-- the edge (0, 1), an OR on the non-edge (0, 2), or an AND on it. A first gate that repeats an
-- input or is constant false is dropped and the shorter circuit is handled by induction.
-- Likewise a first gate that no later gate reads (and that is not the output) is dropped, so
-- the remaining gates read the first gate value (or output it).
-- After renaming the inputs by a graph symmetry, the remaining at most 17 gates read the
-- inputs followed by that canonical first gate value, and the output may be negated.
-- Each hypothesis is the step itself for one canonical first gate, so it is implied by the step.
set_option maxRecDepth 24000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2371_106 (unary : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (h : Bool → Bool) (b : Bool), h false = true → PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 → (D.output = 10 ∨ ∃ g ∈ D.gates, 10 ∈ g.inputs) → ∃ x : Fin 10 → Bool, (if b = true then !D.eval (List.ofFn x ++ [h (x 0)]) else D.eval (List.ofFn x ++ [h (x 0)])) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) (edge : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (c : Bool) (b : Bool), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 → (D.output = 10 ∨ ∃ g ∈ D.gates, 10 ∈ g.inputs) → ∃ x : Fin 10 → Bool, (if b = true then !D.eval (List.ofFn x ++ [if c = true then x 0 && x 1 else x 0 || x 1]) else D.eval (List.ofFn x ++ [if c = true then x 0 && x 1 else x 0 || x 1])) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) (nonedgeOr : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 → (D.output = 10 ∨ ∃ g ∈ D.gates, 10 ∈ g.inputs) → ∃ x : Fin 10 → Bool, (if b = true then !D.eval (List.ofFn x ++ [x 0 || x 2]) else D.eval (List.ofFn x ++ [x 0 || x 2])) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) (nonedgeAnd : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 → (D.output = 10 ∨ ∃ g ∈ D.gates, 10 ∈ g.inputs) → ∃ x : Fin 10 → Bool, (if b = true then !D.eval (List.ofFn x ++ [x 0 && x 2]) else D.eval (List.ofFn x ++ [x 0 && x 2])) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         ∃ (x10 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x9 x10 x3 else x9 x10 x3) ≠ x8 x10 := by
  intro x1 x2 x3 x4 h1 h2 h3
  dsimp only
  let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  have appGet : ∀ (w : List Bool) (v : Bool) (k : ℕ), (w ++ [v]).getD k false =
      if k < w.length then w.getD k false else if k = w.length then v else false := by
    intro w v k
    split_ifs with h1 h2
    · exact List.getD_append _ _ _ _ h1
    · subst h2
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (le_refl w.length)]
      simp
    · apply List.getD_eq_default
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have readValid (x : Fin 10 → Bool) (w : ℕ) (hw : w < 10) :
      (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa)]
    simp only [List.getElem_ofFn]
  have readMissing (x : Fin 10 → Bool) (w : ℕ) (hw : ¬ w < 10) :
      (List.ofFn x).getD w false = false := List.getD_eq_default _ _ (by simpa using hw)
  -- Renaming the input wires of a circuit through p (input k is read as input p k).
  have rename : ∀ (p : Fin 10 → Fin 10) (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 10 → Bool) (c : Bool),
      (⟨D.gates.map (fun g => (⟨g.op, g.inputs.map (fun k => if h : k < 10 then ((p ⟨k, h⟩ : Fin 10) : ℕ) else k)⟩ : PEqualNP.CircuitLowerBounds.Gate)),
        (fun k => if h : k < 10 then ((p ⟨k, h⟩ : Fin 10) : ℕ) else k) D.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x ++ [c]) =
        D.eval (List.ofFn (x ∘ p) ++ [c]) := by
    intro p D x c
    let ρ : ℕ → ℕ := fun k => if h : k < 10 then ((p ⟨k, h⟩ : Fin 10) : ℕ) else k
    let rg : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g => ⟨g.op, g.inputs.map ρ⟩
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have ρlt : ∀ k, k < 10 → ρ k < 10 := by
      intro k hk
      simp only [ρ, hk, dite_true]
      exact (p ⟨k, hk⟩).isLt
    have ρge : ∀ k, ¬ k < 10 → ρ k = k := by
      intro k hk
      simp only [ρ, hk, dite_false]
    have wiresRel : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
        10 ≤ w.length → w.length = w'.length → (∀ k, w.getD k false = w'.getD (ρ k) false) →
        ∀ k, (gs.foldl step w).getD k false = ((gs.map rg).foldl step w').getD (ρ k) false := by
      intro gs
      induction gs with
      | nil =>
        intro w w' _ _ h k
        exact h k
      | cons g gs ih =>
        intro w w' hl hlen h
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
            (rg g).op.eval ((rg g).inputs.map fun i => w'.getD i false) := by
          show g.op.eval (g.inputs.map fun i => w.getD i false) =
            g.op.eval ((g.inputs.map ρ).map fun i => w'.getD i false)
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact h i
        apply ih
        · show 10 ≤ (w ++ _).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · show (w ++ _).length = (w' ++ _).length
          simp only [List.length_append, List.length_cons, List.length_nil, hlen]
        · intro k
          show (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD k false =
            (w' ++ [(rg g).op.eval ((rg g).inputs.map fun i => w'.getD i false)]).getD (ρ k) false
          rw [appGet, appGet, ← hv]
          by_cases hk : k < 10
          · have h1 : k < w.length := by omega
            have h2 : ρ k < w'.length := by have := ρlt k hk; omega
            rw [if_pos h1, if_pos h2]
            exact h k
          · rw [ρge k hk]
            have hk' := h k
            rw [ρge k hk] at hk'
            by_cases h1 : k < w.length
            · have h1' : k < w'.length := by omega
              rw [if_pos h1, if_pos h1']
              exact hk'
            · have h1' : ¬ k < w'.length := by omega
              rw [if_neg h1, if_neg h1']
              by_cases h2 : k = w.length
              · have h2' : k = w'.length := by omega
                rw [if_pos h2, if_pos h2']
              · have h2' : ¬ k = w'.length := by omega
                rw [if_neg h2, if_neg h2']
    have base : ∀ k, (List.ofFn (x ∘ p) ++ [c]).getD k false = (List.ofFn x ++ [c]).getD (ρ k) false := by
      intro k
      rw [appGet, appGet]
      simp only [List.length_ofFn]
      by_cases hk : k < 10
      · have h2 : ρ k < 10 := ρlt k hk
        rw [if_pos hk, if_pos h2]
        rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using h2)]
        simp only [List.getElem_ofFn, Function.comp_apply, ρ, hk, dite_true]
      · rw [ρge k hk]
        simp [hk]
    have := wiresRel D.gates (List.ofFn (x ∘ p) ++ [c]) (List.ofFn x ++ [c])
      (by simp) (by simp) base D.output
    exact this.symm
  -- Dropping the extra wire 10 when it repeats wire t (an input, or a wire that never exists).
  have drop : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (t : ℕ) (x : Fin 10 → Bool), (t < 10 ∨ 10 + D.gates.length ≤ t) →
      (⟨D.gates.map (fun g => (⟨g.op, g.inputs.map (fun k => if k < 10 then k else if k = 10 then t else k - 1)⟩ : PEqualNP.CircuitLowerBounds.Gate)),
        (fun k => if k < 10 then k else if k = 10 then t else k - 1) D.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) =
        D.eval (List.ofFn x ++ [(List.ofFn x).getD t false]) := by
    intro D t x ht
    let σ : ℕ → ℕ := fun k => if k < 10 then k else if k = 10 then t else k - 1
    let rn : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g => ⟨g.op, g.inputs.map σ⟩
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have σlt : ∀ k, k < 10 → σ k = k := by
      intro k hk
      simp [σ, hk]
    have σten : σ 10 = t := by
      simp [σ]
    have σgt : ∀ k, 10 < k → σ k = k - 1 := by
      intro k hk
      have a1 : ¬ k < 10 := by omega
      have a2 : ¬ k = 10 := by omega
      simp [σ, a1, a2]
    have inv : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
        w.length = w'.length + 1 → 10 < w.length → (t < 10 ∨ w'.length + gs.length ≤ t) →
        (∀ k, w.getD k false = w'.getD (σ k) false) →
        ∀ k, (gs.foldl step w).getD k false = ((gs.map rn).foldl step w').getD (σ k) false := by
      intro gs
      induction gs with
      | nil =>
        intro w w' _ _ _ h k
        exact h k
      | cons g gs ih =>
        intro w w' hlen hl ht' h
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
            (rn g).op.eval ((rn g).inputs.map fun i => w'.getD i false) := by
          show g.op.eval (g.inputs.map fun i => w.getD i false) =
            g.op.eval ((g.inputs.map σ).map fun i => w'.getD i false)
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact h i
        simp only [List.length_cons] at ht'
        apply ih
        · show (w ++ _).length = (w' ++ _).length + 1
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · show 10 < (w ++ _).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · show t < 10 ∨ (w' ++ _).length + gs.length ≤ t
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · intro k
          show (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD k false =
            (w' ++ [(rn g).op.eval ((rn g).inputs.map fun i => w'.getD i false)]).getD (σ k) false
          rw [appGet, appGet, ← hv]
          have hk' := h k
          by_cases hk : k < 10
          · rw [σlt k hk] at hk' ⊢
            have h1 : k < w.length := by omega
            have h2 : k < w'.length := by omega
            rw [if_pos h1, if_pos h2]
            exact hk'
          · by_cases hk10 : k = 10
            · subst hk10
              rw [σten] at hk' ⊢
              have h1 : 10 < w.length := hl
              rw [if_pos h1, hk']
              rcases ht' with ht1 | ht1
              · have h2 : t < w'.length := by omega
                rw [if_pos h2]
              · have h2 : ¬ t < w'.length := by omega
                have h3 : ¬ t = w'.length := by omega
                rw [if_neg h2, if_neg h3]
                exact List.getD_eq_default _ _ (by omega)
            · have hgt : 10 < k := by omega
              rw [σgt k hgt] at hk' ⊢
              by_cases h1 : k < w.length
              · have h1' : k - 1 < w'.length := by omega
                rw [if_pos h1, if_pos h1']
                exact hk'
              · have h1' : ¬ k - 1 < w'.length := by omega
                rw [if_neg h1, if_neg h1']
                by_cases h2 : k = w.length
                · have h2' : k - 1 = w'.length := by omega
                  rw [if_pos h2, if_pos h2']
                · have h2' : ¬ k - 1 = w'.length := by omega
                  rw [if_neg h2, if_neg h2']
    have base : ∀ k, (List.ofFn x ++ [(List.ofFn x).getD t false]).getD k false = (List.ofFn x).getD (σ k) false := by
      intro k
      rw [appGet]
      simp only [List.length_ofFn]
      by_cases hk : k < 10
      · rw [if_pos hk, σlt k hk]
      · by_cases hk10 : k = 10
        · subst hk10
          rw [σten]
          simp
        · have hgt : 10 < k := by omega
          rw [if_neg hk, if_neg hk10, σgt k hgt]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm
    have := inv D.gates (List.ofFn x ++ [(List.ofFn x).getD t false]) (List.ofFn x)
      (by simp) (by simp) (by simpa using ht) base D.output
    exact this.symm
  have fOne : F (fun _ => true) = true := by decide
  have fZero : F (fun _ => false) = false := by decide
  have fSingle : ∀ j : Fin 10, F (fun k => decide (k = j)) = false := by decide
  -- Wires other than 10 do not depend on wire 10 when no gate reads wire 10.
  have indepWires : ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool), w.length = w'.length →
      (∀ g ∈ gl, 10 ∉ g.inputs) → (∀ k, k ≠ 10 → w.getD k false = w'.getD k false) →
      ∀ k, k ≠ 10 →
        (gl.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD k false =
        (gl.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD k false := by
    intro gl
    induction gl with
    | nil =>
      intro w w' _ _ h k hk
      exact h k hk
    | cons g gl ih =>
      intro w w' hlen hnr h
      rw [List.foldl_cons, List.foldl_cons]
      have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => w'.getD i false) := by
        congr 1
        apply List.map_congr_left
        intro i hi
        apply h i
        intro hi10
        rw [hi10] at hi
        exact hnr g List.mem_cons_self hi
      apply ih
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
      · intro g' hg'
        exact hnr g' (List.mem_cons_of_mem _ hg')
      · intro k hk
        show (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD k false =
          (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).getD k false
        rw [appGet, appGet, hv, hlen]
        by_cases h1 : k < w'.length
        · rw [if_pos h1, if_pos h1]
          exact h k hk
        · rw [if_neg h1, if_neg h1]
  have main : ∀ m : ℕ, ∀ (g0 : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (pol : Bool),
      PEqualNP.MetaComplexity.FanInTwo ⟨[g0], 0⟩ → PEqualNP.MetaComplexity.FanInTwo ⟨gs, o⟩ → gs.length ≤ m → m ≤ 17 →
      ∃ x : Fin 10 → Bool, (if pol = true then
          !(PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]))
        else PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)])) ≠ F x := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih x1 gs x3 x4 h1 h2 hlen hm
    by_contra hall
    push_neg at hall
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, x3⟩
    have hD : PEqualNP.MetaComplexity.FanInTwo D := h2
    have sz : D.size ≤ 17 := by
      show gs.length ≤ 17
      omega
    -- A circuit on the ten inputs alone, with fewer gates, is handled by the induction.
    have viaIH : ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ),
        PEqualNP.MetaComplexity.FanInTwo ⟨gl, o'⟩ → gl.length ≤ m →
        (∀ x : Fin 10 → Bool, (if x4 = true then !(PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, o'⟩ (List.ofFn x))
          else PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, o'⟩ (List.ofFn x)) = F x) → False := by
      intro gl o' hf hl hc
      cases gl with
      | nil =>
        have ev : ∀ x : Fin 10 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨[], o'⟩ (List.ofFn x) =
            (List.ofFn x).getD o' false := fun x => rfl
        by_cases hj : o' < 10
        · cases x4 with
          | false =>
            have e := hc (fun k => decide (k = ⟨o', hj⟩))
            rw [if_neg (by decide), ev, readValid _ _ hj, fSingle] at e
            simp at e
          | true =>
            have e := hc (fun _ => false)
            rw [if_pos rfl, ev, readValid _ _ hj, fZero] at e
            simp at e
        · cases x4 with
          | false =>
            have e := hc (fun _ => true)
            rw [if_neg (by decide), ev, readMissing _ _ hj, fOne] at e
            simp at e
          | true =>
            have e := hc (fun _ => false)
            rw [if_pos rfl, ev, readMissing _ _ hj, fZero] at e
            simp at e
      | cons g rest =>
        have hm' : rest.length < m := by
          simp only [List.length_cons] at hl
          omega
        obtain ⟨x, hx⟩ := ih rest.length hm' g rest o' x4
          (fun g' hg' => hf g' (by
            have : g' = g := List.mem_singleton.mp hg'
            subst this
            exact List.mem_cons_self))
          (fun g' hg' => hf g' (List.mem_cons_of_mem _ hg')) le_rfl (by omega)
        exact hx (hc x)
    let V := fun x : Fin 10 → Bool =>
      x1.op.eval (x1.inputs.map (fun i => (List.ofFn x).getD i false))
    have computes : ∀ x : Fin 10 → Bool,
        (if x4 = true then !D.eval (List.ofFn x ++ [V x]) else D.eval (List.ofFn x ++ [V x])) = F x :=
      fun x => hall x
    -- If no gate reads the first gate and it is not the output, drop it.
    have hread : D.output = 10 ∨ ∃ g ∈ gs, 10 ∈ g.inputs := by
      by_contra hnot
      push_neg at hnot
      obtain ⟨hout, hnr⟩ := hnot
      have indep : ∀ (x : Fin 10 → Bool) (c : Bool),
          D.eval (List.ofFn x ++ [false]) = D.eval (List.ofFn x ++ [c]) := by
        intro x c
        apply indepWires D.gates (List.ofFn x ++ [false]) (List.ofFn x ++ [c]) (by simp) hnr
        · intro k hk
          rw [appGet, appGet]
          simp only [List.length_ofFn]
          by_cases h1 : k < 10
          · rw [if_pos h1, if_pos h1]
          · rw [if_neg h1, if_neg h1, if_neg hk, if_neg hk]
        · exact hout
      apply viaIH (D.gates.map (fun g => (⟨g.op, g.inputs.map (fun k => if k < 10 then k else if k = 10 then 10 + gs.length else k - 1)⟩ : PEqualNP.CircuitLowerBounds.Gate)))
        ((fun k => if k < 10 then k else if k = 10 then 10 + gs.length else k - 1) D.output)
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        obtain ⟨hop, hl⟩ := hD g0 hg0
        exact ⟨hop, by simpa using hl⟩
      · rw [List.length_map]
        exact hlen
      · intro x
        rw [drop D (10 + gs.length) x (Or.inr le_rfl), readMissing x (10 + gs.length) (by omega), indep x (V x)]
        exact computes x
    -- If the first gate only repeats an input or reads constant false, drop it.
    have shrink : ∀ t : ℕ, (t < 10 ∨ 10 + gs.length ≤ t) → (∀ x, V x = (List.ofFn x).getD t false) → False := by
      intro t ht htv
      apply viaIH (D.gates.map (fun g => (⟨g.op, g.inputs.map (fun k => if k < 10 then k else if k = 10 then t else k - 1)⟩ : PEqualNP.CircuitLowerBounds.Gate)))
        ((fun k => if k < 10 then k else if k = 10 then t else k - 1) D.output)
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        obtain ⟨hop, hl⟩ := hD g0 hg0
        exact ⟨hop, by simpa using hl⟩
      · rw [List.length_map]
        exact hlen
      · intro x
        rw [drop D t x ht, ← htv x]
        exact computes x
    let a : Fin 10 → Fin 10 := ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5]
    have aInv : ∀ x, F (x ∘ a) = F x := by
      intro x
      dsimp [F, a, Function.comp_def]
      ac_rfl
    let b : Fin 10 → Fin 10 := ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7]
    have bInv : ∀ x, F (x ∘ b) = F x := by
      intro x
      dsimp [F, b, Function.comp_def]
      ac_rfl
    let move : List Bool → Fin 10 → Fin 10 := fun word i =>
      word.foldl (fun j bit => if bit then b j else a j) i
    have moveInv : ∀ word x, F (x ∘ move word) = F x := by
      intro word
      induction word with
      | nil => intro x; rfl
      | cons bit rest ih =>
        intro x
        cases bit
        · exact (aInv (x ∘ move rest)).trans (ih x)
        · exact (bInv (x ∘ move rest)).trans (ih x)
    -- Words in the two graph symmetries cover the three orbits of ordered pairs.
    let routes := (List.range 7).flatMap fun n =>
      (List.range (2 ^ n)).map fun m => (List.range n).map m.testBit
    have cover : ∀ i j : Fin 10, routes.any (fun w =>
        decide (move w i = 0 ∧ (move w j = 0 ∨ move w j = 1 ∨ move w j = 2))) = true := by decide
    have aInj : ∀ u v : Fin 10, a u = a v → u = v := by decide
    have bInj : ∀ u v : Fin 10, b u = b v → u = v := by decide
    have moveInj : ∀ (word : List Bool) (u v : Fin 10), move word u = move word v → u = v := by
      intro word
      induction word with
      | nil => intro u v h; exact h
      | cons bit rest ih =>
        intro u v h
        cases bit
        · exact aInj u v (ih (a u) (a v) h)
        · exact bInj u v (ih (b u) (b v) h)
    have orbit (i j : Fin 10) : ∃ p : Fin 10 → Fin 10, p i = 0 ∧
        (p j = 0 ∨ p j = 1 ∨ p j = 2) ∧ (∀ x, F (x ∘ p) = F x) ∧ ∀ u v, p u = p v → u = v := by
      obtain ⟨w, _, hw⟩ := List.any_eq_true.mp (cover i j)
      have h := of_decide_eq_true hw
      exact ⟨move w, h.1, h.2, moveInv w, moveInj w⟩
    let rl : (Fin 10 → Fin 10) → PEqualNP.CircuitLowerBounds.Circuit := fun p =>
      ⟨D.gates.map (fun g => (⟨g.op, g.inputs.map (fun k => if h : k < 10 then ((p ⟨k, h⟩ : Fin 10) : ℕ) else k)⟩ : PEqualNP.CircuitLowerBounds.Gate)),
        (fun k => if h : k < 10 then ((p ⟨k, h⟩ : Fin 10) : ℕ) else k) D.output⟩
    have rlEval : ∀ (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) (c : Bool),
        (rl p).eval (List.ofFn x ++ [c]) = D.eval (List.ofFn (x ∘ p) ++ [c]) :=
      fun p x c => rename p D x c
    have rlFan : ∀ p, PEqualNP.MetaComplexity.FanInTwo (rl p) := by
      intro p g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hop, hl⟩ := hD g0 hg0
      exact ⟨hop, by simpa using hl⟩
    have rlSize : ∀ p, (rl p).size ≤ 17 := by
      intro p
      show (D.gates.map _).length ≤ 17
      rw [List.length_map]
      exact sz
    have rlRead : ∀ p, (rl p).output = 10 ∨ ∃ g ∈ (rl p).gates, 10 ∈ g.inputs := by
      intro p
      rcases hread with h | ⟨g, hg, h10⟩
      · left
        show (fun k => if h : k < 10 then ((p ⟨k, h⟩ : Fin 10) : ℕ) else k) D.output = 10
        simp [h]
      · right
        refine ⟨_, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
        show 10 ∈ g.inputs.map _
        exact List.mem_map.mpr ⟨10, h10, by simp⟩
    have run (p : Fin 10 → Fin 10) (hp : ∀ x, F (x ∘ p) = F x) (x : Fin 10 → Bool) :
        (if x4 = true then !D.eval (List.ofFn (x ∘ p) ++ [V (x ∘ p)])
          else D.eval (List.ofFn (x ∘ p) ++ [V (x ∘ p)])) = F x :=
      (computes (x ∘ p)).trans (hp x)
    have noUnary (i : Fin 10) (h : Bool → Bool) (hv : ∀ x, V x = h (x i)) : False := by
      by_cases hf : h false = true
      · obtain ⟨p, hi, _, hp, _⟩ := orbit i i
        obtain ⟨x, hx⟩ := unary (rl p) h x4 hf (rlFan p) (rlSize p) (rlRead p)
        apply hx
        rw [rlEval p x (h (x 0))]
        simpa only [hv, Function.comp_apply, hi] using run p hp x
      · have hf' : h false = false := by simpa using hf
        by_cases ht : h true = true
        · apply shrink i (Or.inl i.isLt)
          intro x
          rw [hv x, readValid x i i.isLt]
          show h (x i) = x i
          generalize x i = z
          cases z
          · exact hf'
          · exact ht
        · have ht' : h true = false := by simpa using ht
          apply shrink (10 + gs.length) (Or.inr le_rfl)
          intro x
          rw [hv x, readMissing x _ (by omega)]
          generalize x i = z
          cases z
          · exact hf'
          · exact ht'
    have noBinary (i j : Fin 10) (c : Bool)
        (hv : ∀ x, V x = if c = true then x i && x j else x i || x j) : False := by
      obtain ⟨p, hi, hj, hp, hpinj⟩ := orbit i j
      rcases hj with hj | hj | hj
      · have hij : i = j := hpinj i j (hi.trans hj.symm)
        subst hij
        apply noUnary i id
        intro x
        rw [hv x]
        cases c <;> simp
      · obtain ⟨x, hx⟩ := edge (rl p) c x4 (rlFan p) (rlSize p) (rlRead p)
        apply hx
        rw [rlEval p x _]
        simpa only [hv, Function.comp_apply, hi, hj] using run p hp x
      · cases c with
        | false =>
          obtain ⟨x, hx⟩ := nonedgeOr (rl p) x4 (rlFan p) (rlSize p) (rlRead p)
          apply hx
          rw [rlEval p x _]
          simpa only [hv, Function.comp_apply, hi, hj, Bool.false_eq_true, ite_false] using run p hp x
        | true =>
          obtain ⟨x, hx⟩ := nonedgeAnd (rl p) x4 (rlFan p) (rlSize p) (rlRead p)
          apply hx
          rw [rlEval p x _]
          simpa only [hv, Function.comp_apply, hi, hj, ite_true] using run p hp x
    obtain ⟨op, bound⟩ := h1 x1 (List.mem_singleton_self _)
    change x1.inputs.length ≤ 2 at bound
    rcases he : x1.inputs with _ | ⟨u, tail⟩
    · exact noUnary 0 (fun _ => x1.op.eval []) (by intro x; simp [V, he])
    rcases ht : tail with _ | ⟨v, tail'⟩
    · by_cases hu : u < 10
      · exact noUnary ⟨u, hu⟩ (fun bit => x1.op.eval [bit]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readValid _ _ hu])
      · exact noUnary 0 (fun _ => x1.op.eval [false]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readMissing _ _ hu])
    have empty : tail' = [] := by simpa [he, ht] using bound
    subst tail'
    by_cases hu : u < 10
    · by_cases hv : v < 10
      · have op' : x1.op = .and ∨ x1.op = .or ∨ x1.op = .not := op
        rcases op' with hop | hop | hop
        · apply noBinary ⟨u, hu⟩ ⟨v, hv⟩ true
          intro x
          simp only [V, he, ht, List.map_cons, List.map_nil, hop, readValid _ _ hu, readValid _ _ hv]
          change [x ⟨u, hu⟩, x ⟨v, hv⟩].all id = _
          simp
        · apply noBinary ⟨u, hu⟩ ⟨v, hv⟩ false
          intro x
          simp only [V, he, ht, List.map_cons, List.map_nil, hop, readValid _ _ hu, readValid _ _ hv]
          change [x ⟨u, hu⟩, x ⟨v, hv⟩].any id = _
          simp
        · apply noUnary ⟨u, hu⟩ (! ·)
          intro x
          simp only [V, he, ht, List.map_cons, List.map_nil, hop, readValid _ _ hu]
          rfl
      · exact noUnary ⟨u, hu⟩ (fun s => x1.op.eval [s, false]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readValid _ _ hu, readMissing _ _ hv])
    · by_cases hv : v < 10
      · exact noUnary ⟨v, hv⟩ (fun s => x1.op.eval [false, s]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readMissing _ _ hu, readValid _ _ hv])
      · exact noUnary 0 (fun _ => x1.op.eval [false, false]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readMissing _ _ hu, readMissing _ _ hv])
  exact main 17 x1 x2.gates x3 x4 h1 (fun g hg => h2 g hg) h3 le_rfl
