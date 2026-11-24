import Mathlib
import PEqualNP.Defs

-- Cut by which wires the later gates read. Wire nine is the first gate, input four OR input six.
-- If input four is read by no later gate and by no output pin, the inputs with (3, 4, 6) true
-- and with (3, 6) true get the same output, and the edge function is true on the first and
-- false on the second. Input six is the same with (4, 6, 8) and (4, 8). That side is proved
-- below. Left open: wire nine unread, which is a circuit of fourteen gates on the nine inputs,
-- and the case where input four, input six and wire nine are all read.
theorem PEqualNP.Outside.R_meta_3064_1
    (hUnread : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (pins : List (Fin 24)),
      gs.length ≤ 13 →
      PEqualNP.MetaComplexity.FanInTwo { gates := gs, output := 0 } →
      (∀ g ∈ gs, ∀ i ∈ g.inputs, i ≤ 23) →
      pins.length ≤ 2 →
      (∀ g ∈ gs, 9 ∉ g.inputs) → (∀ p ∈ pins, p.val ≠ 9) →
      ∃ x : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.and.eval (pins.map fun p =>
          (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires
            (List.ofFn x ++ [x 4 || x 6])).getD p.val false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hRead : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (pins : List (Fin 24)),
      gs.length ≤ 13 →
      PEqualNP.MetaComplexity.FanInTwo { gates := gs, output := 0 } →
      (∀ g ∈ gs, ∀ i ∈ g.inputs, i ≤ 23) →
      pins.length ≤ 2 →
      ((∃ g ∈ gs, 4 ∈ g.inputs) ∨ ∃ p ∈ pins, p.val = 4) →
      ((∃ g ∈ gs, 6 ∈ g.inputs) ∨ ∃ p ∈ pins, p.val = 6) →
      ((∃ g ∈ gs, 9 ∈ g.inputs) ∨ ∃ p ∈ pins, p.val = 9) →
      ∃ x : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.and.eval (pins.map fun p =>
          (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires
            (List.ofFn x ++ [x 4 || x 6])).getD p.val false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro gs pins hlen hfan hbound hpins
  have agree : ∀ (v : ℕ) (l : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ l, v ∉ g.inputs) →
      ∀ (w w' : List Bool), w.length = w'.length → (∀ i, i ≠ v → w[i]? = w'[i]?) →
      ∀ i, i ≠ v → (({ gates := l, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires w)[i]? =
        (({ gates := l, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires w')[i]? := by
    intro v l
    induction l with
    | nil =>
      intro _ w w' _ h
      exact h
    | cons g tl ih =>
      intro hread w w' hl h
      have hg : v ∉ g.inputs := hread g List.mem_cons_self
      have hval : g.op.eval (g.inputs.map fun j => w.getD j false) =
          g.op.eval (g.inputs.map fun j => w'.getD j false) := by
        congr 1
        apply List.map_congr_left
        intro j hj
        have hjv : j ≠ v := fun e => hg (e ▸ hj)
        simp only [List.getD_eq_getElem?_getD, h j hjv]
      change ∀ i, i ≠ v →
        (({ gates := tl, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires
          (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]))[i]? =
        (({ gates := tl, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires
          (w' ++ [g.op.eval (g.inputs.map fun j => w'.getD j false)]))[i]?
      apply ih (fun g' hg' => hread g' (List.mem_cons_of_mem _ hg'))
      · simp [hl]
      · intro i hi
        rw [hval]
        simp only [List.getElem?_append, hl]
        split
        · exact h i hi
        · rfl
  have pair : ∀ (v : ℕ) (xp xn : Fin 9 → Bool), (∀ g ∈ gs, v ∉ g.inputs) →
      (∀ p ∈ pins, p.val ≠ v) →
      (∀ i, i ≠ v → (List.ofFn xp ++ [xp 4 || xp 6])[i]? = (List.ofFn xn ++ [xn 4 || xn 6])[i]?) →
      (xp 0 && xp 1 || xp 1 && xp 2 || xp 2 && xp 3 || xp 3 && xp 4 || xp 4 && xp 0 || xp 0 && xp 5 || xp 1 && xp 6 || xp 2 && xp 7 || xp 3 && xp 8 || xp 5 && xp 7 || xp 6 && xp 8 || xp 8 && xp 5) = true →
      (xn 0 && xn 1 || xn 1 && xn 2 || xn 2 && xn 3 || xn 3 && xn 4 || xn 4 && xn 0 || xn 0 && xn 5 || xn 1 && xn 6 || xn 2 && xn 7 || xn 3 && xn 8 || xn 5 && xn 7 || xn 6 && xn 8 || xn 8 && xn 5) = false →
      ∃ x : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.and.eval (pins.map fun p =>
          (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires
            (List.ofFn x ++ [x 4 || x 6])).getD p.val false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro v xp xn hg hp hi hfp hfn
    have hw := agree v gs hg (List.ofFn xp ++ [xp 4 || xp 6]) (List.ofFn xn ++ [xn 4 || xn 6])
      (by simp) hi
    have hout : PEqualNP.CircuitLowerBounds.GateOp.and.eval (pins.map fun p =>
          (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires
            (List.ofFn xp ++ [xp 4 || xp 6])).getD p.val false) =
        PEqualNP.CircuitLowerBounds.GateOp.and.eval (pins.map fun p =>
          (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires
            (List.ofFn xn ++ [xn 4 || xn 6])).getD p.val false) := by
      congr 1
      apply List.map_congr_left
      intro p hpm
      simp only [List.getD_eq_getElem?_getD, hw p.val (hp p hpm)]
    by_cases hb : PEqualNP.CircuitLowerBounds.GateOp.and.eval (pins.map fun p =>
          (({ gates := gs, output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires
            (List.ofFn xn ++ [xn 4 || xn 6])).getD p.val false) = true
    · refine ⟨xn, ?_⟩
      rw [hb, hfn]
      decide
    · refine ⟨xp, ?_⟩
      rw [hout, hfp]
      exact hb
  by_cases h9 : ((∃ g ∈ gs, 9 ∈ g.inputs) ∨ ∃ p ∈ pins, p.val = 9)
  swap
  · exact hUnread gs pins hlen hfan hbound hpins (fun g hg hv => h9 (Or.inl ⟨g, hg, hv⟩))
      (fun p hp hv => h9 (Or.inr ⟨p, hp, hv⟩))
  by_cases h4 : ((∃ g ∈ gs, 4 ∈ g.inputs) ∨ ∃ p ∈ pins, p.val = 4)
  swap
  · have hg : ∀ g ∈ gs, 4 ∉ g.inputs := fun g hg hv => h4 (Or.inl ⟨g, hg, hv⟩)
    have hp : ∀ p ∈ pins, p.val ≠ 4 := fun p hp hv => h4 (Or.inr ⟨p, hp, hv⟩)
    obtain ⟨xp, hxp⟩ : ∃ xp : Fin 9 → Bool, xp = fun i => decide (i.val = 3 ∨ i.val = 4 ∨ i.val = 6) := ⟨_, rfl⟩
    obtain ⟨xn, hxn⟩ : ∃ xn : Fin 9 → Bool, xn = fun i => decide (i.val = 3 ∨ i.val = 6) := ⟨_, rfl⟩
    have e1 : List.ofFn xp ++ [xp 4 || xp 6] = [false, false, false, true, true, false, true, false, false, true] := by
      subst hxp
      decide
    have e2 : List.ofFn xn ++ [xn 4 || xn 6] = [false, false, false, true, false, false, true, false, false, true] := by
      subst hxn
      decide
    refine pair 4 xp xn hg hp ?_ (by subst hxp; decide) (by subst hxn; decide)
    intro i hi
    rw [e1, e2]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      first | rfl | exact absurd rfl hi
  by_cases h6 : ((∃ g ∈ gs, 6 ∈ g.inputs) ∨ ∃ p ∈ pins, p.val = 6)
  swap
  · have hg : ∀ g ∈ gs, 6 ∉ g.inputs := fun g hg hv => h6 (Or.inl ⟨g, hg, hv⟩)
    have hp : ∀ p ∈ pins, p.val ≠ 6 := fun p hp hv => h6 (Or.inr ⟨p, hp, hv⟩)
    obtain ⟨xp, hxp⟩ : ∃ xp : Fin 9 → Bool, xp = fun i => decide (i.val = 4 ∨ i.val = 6 ∨ i.val = 8) := ⟨_, rfl⟩
    obtain ⟨xn, hxn⟩ : ∃ xn : Fin 9 → Bool, xn = fun i => decide (i.val = 4 ∨ i.val = 8) := ⟨_, rfl⟩
    have e1 : List.ofFn xp ++ [xp 4 || xp 6] = [false, false, false, false, true, false, true, false, true, true] := by
      subst hxp
      decide
    have e2 : List.ofFn xn ++ [xn 4 || xn 6] = [false, false, false, false, true, false, false, false, true, true] := by
      subst hxn
      decide
    refine pair 6 xp xn hg hp ?_ (by subst hxp; decide) (by subst hxn; decide)
    intro i hi
    rw [e1, e2]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      first | rfl | exact absurd rfl hi
  exact hRead gs pins hlen hfan hbound hpins h4 h6 h9
