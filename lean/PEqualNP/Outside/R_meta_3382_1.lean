import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first child proves that indices beyond all allocated wires can be renamed.
-- The second child restricts the paired circuits to finite sets of wire names.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3382_1
    (preserve :
      ∀ (w : List Bool) (gs : List Gate) (k : ℕ) (f : ℕ → ℕ),
        w.length + gs.length ≤ k → (∀ i < k, f i = i) → (∀ i, k ≤ i → k ≤ f i) →
          ∀ o : ℕ,
            ({gates := gs.map (fun g => {g with inputs := g.inputs.map f}), output := f o} : Circuit).eval w =
              ({gates := gs, output := o} : Circuit).eval w)
    (bounded :
      have x1 : (Fin (7 : ℕ) → Bool) → Bool :=
        fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ)));
        ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
          x4 < 21 → x5 < 21 → x2.output < 21 →
          (∀ g ∈ x2.gates, ∀ i ∈ g.inputs, i < 21) →
          PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 →
          List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates →
          (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) →
          (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ)
    ) :
      have x1 : (Fin (7 : ℕ) → Bool) → Bool :=
        fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ)));
        ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
          PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 →
          List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates →
          (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) →
          (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ) := by
  intro graph c d a b hfan hsize hbase halign haug
  let norm (i : ℕ) : ℕ :=
    if i < 18 then i else if i = a then 18 else if i = b then 19 else 20
  let shifted (i : ℕ) : ℕ := if i = 0 then 0 else norm (i - 1) + 1
  let remap (f : ℕ → ℕ) (g : Gate) : Gate := {g with inputs := g.inputs.map f}
  let C : Circuit := ⟨c.gates.map (remap norm), norm c.output⟩
  let D : Circuit := ⟨d.gates.map (remap shifted), 0⟩
  have norm_lt (i : ℕ) : norm i < 21 := by
    unfold norm
    split_ifs <;> omega
  have norm_small (i : ℕ) (hi : i < 18) : norm i = i := by
    simp [norm, hi]
  have norm_large (i : ℕ) (hi : 18 ≤ i) : 18 ≤ norm i := by
    unfold norm
    split_ifs <;> omega
  have norm_two (i : ℕ) : norm i = 2 ↔ i = 2 := by
    by_cases hi : i < 18
    · rw [norm_small i hi]
    · have := norm_large i (by omega)
      omega
  have shifted_succ (i : ℕ) : shifted (i + 1) = norm i + 1 := by
    simp [shifted]
  have shifted_small (i : ℕ) (hi : i < 19) : shifted i = i := by
    by_cases hz : i = 0
    · simp [shifted, hz]
    · rw [show shifted i = norm (i - 1) + 1 by simp [shifted, hz],
        norm_small _ (by omega)]
      omega
  have shifted_large (i : ℕ) (hi : 19 ≤ i) : 19 ≤ shifted i := by
    have hz : i ≠ 0 := by omega
    have h := norm_large (i - 1) (by omega)
    simp [shifted, hz]
    omega
  have lenC : c.gates.length = 11 := hsize
  have lenD : d.gates.length = 11 := halign.length_eq.symm.trans lenC
  have hCfan : FanInTwo C := by
    intro g hg
    obtain ⟨g', h', rfl⟩ := List.mem_map.mp hg
    simpa [remap] using hfan g' h'
  have hCsize : C.size = 11 := by simp [C, Circuit.size, lenC]
  have hCinputs : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i < 21 := by
    intro g hg i hi
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact norm_lt j
  have hCbase : circuitFun 7 C = graph := by
    funext x
    rw [← congrFun hbase x]
    exact preserve (List.ofFn x) c.gates 18 norm (by simp [lenC])
      norm_small norm_large c.output
  have alignPins {is js : List ℕ}
      (h : List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) is js) :
      List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = norm a ∨ i = norm b))
        (is.map norm) (js.map shifted) := by
    induction h with
    | nil => exact .nil
    | @cons i j _ _ h _ ih =>
      refine .cons ?_ ih
      rcases h with h | ⟨hz, ha | hb⟩
      · left
        rw [h, shifted_succ]
      · right
        simp [shifted, hz, ha]
      · right
        simp [shifted, hz, hb]
  have alignGates {gs hs : List Gate}
      (h : List.Forall₂ (fun (g h : Gate) => g.op = h.op ∧
        List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs) gs hs) :
      List.Forall₂ (fun (g h : Gate) => g.op = h.op ∧
        List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = norm a ∨ i = norm b)) g.inputs h.inputs)
        (gs.map (remap norm)) (hs.map (remap shifted)) := by
    induction h with
    | nil => exact .nil
    | @cons g h _ _ hmatch _ ih =>
      exact .cons ⟨hmatch.1, alignPins hmatch.2⟩ ih
  have hDaug : ∀ x : Fin 7 → Bool,
      (D.wires (true :: List.ofFn x)).getD (C.output + 1) false = (graph x || x 2) := by
    intro x
    have he := preserve (true :: List.ofFn x) d.gates 19 shifted (by simp [lenD])
      shifted_small shifted_large (c.output + 1)
    change (D.wires (true :: List.ofFn x)).getD (shifted (c.output + 1)) false =
      (d.wires (true :: List.ofFn x)).getD (c.output + 1) false at he
    rw [shifted_succ] at he
    exact he.trans (haug x)
  let counted (g : Gate) := g.op.eval [true, false] && g.inputs.contains 2
  have hp : counted ∘ remap norm = counted := by
    funext g
    have hmem : (g.inputs.map norm).contains 2 = g.inputs.contains 2 := by
      simp [List.contains_eq_mem, List.mem_map, norm_two]
    change (g.op.eval [true, false] && (g.inputs.map norm).contains 2) =
      (g.op.eval [true, false] && g.inputs.contains 2)
    rw [hmem]
  have hCount : (C.gates.filter counted).length = (c.gates.filter counted).length := by
    change ((c.gates.map (remap norm)).filter counted).length = _
    rw [List.filter_map, List.length_map, hp]
  have h := bounded C D (norm a) (norm b) (norm_lt a) (norm_lt b) (norm_lt c.output)
    hCinputs hCfan hCsize hCbase (alignGates halign) hDaug
  change (C.gates.filter counted).length < 2 at h
  exact hCount ▸ h
