import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4938_412
    (padding : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size ∧ D.output ≤ 29 ∧ (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 29) ∧ ∀ (x : Fin 10 → Bool) (v : Bool), D.eval (List.ofFn x ++ [v]) = C.eval (List.ofFn x))
    (lower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (16 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro gate C u v hg hC hs
  dsimp only
  intro _ _ clean
  let E : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨gate :: (C.gates ++ [⟨.or, [u,v]⟩]), 11 + C.gates.length⟩
  have fe : PEqualNP.MetaComplexity.FanInTwo E := by
    intro g hm
    change g ∈ gate :: (C.gates ++ [⟨.or,[u,v]⟩]) at hm
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | hc | rfl
    · exact hg _ (by simp)
    · exact hC _ hc
    · simp
  have es : E.size ≤ 18 := by
    change C.gates.length ≤ 16 at hs
    simp [E,PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  obtain ⟨D,df,dsize,dout,dreads,deval⟩ := padding E fe es
  obtain ⟨x,ne⟩ := lower D true df (dsize ▸ es) dout dreads
  let inBits := List.ofFn x
  let first := ({ gates := [gate], output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires inBits
  let ws := C.wires first
  have all_len (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) :
      (gs.foldl (fun w (g : PEqualNP.CircuitLowerBounds.Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).length = l.length + gs.length := by
    induction gs generalizing l with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp
      omega
  have firstlen : first.length = 11 := by
    simp [first,inBits,PEqualNP.CircuitLowerBounds.Circuit.wires]
  have wlen : ws.length = 11 + C.gates.length := by
    unfold ws PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [all_len,firstlen]
  have eout : E.eval inBits = (ws.getD u false || ws.getD v false) := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval E PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [List.foldl_cons,List.foldl_append,List.foldl_nil]
    change (ws ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval ([u,v].map fun k => ws.getD k false)]).getD
      (11 + C.gates.length) false = (ws.getD u false || ws.getD v false)
    rw [← wlen]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have mismatch := ne
  rw [deval] at mismatch
  change E.eval inBits ≠ _ at mismatch
  rw [eout] at mismatch
  refine ⟨x,?_⟩
  change _ = true ∧ ws.getD u false = false ∧ ws.getD v false = false
  generalize ht : (fun z : Fin 10 → Bool => z (0 : Fin (10 : ℕ)) && z (1 : Fin (10 : ℕ)) || z (1 : Fin (10 : ℕ)) && z (2 : Fin (10 : ℕ)) || z (2 : Fin (10 : ℕ)) && z (3 : Fin (10 : ℕ)) || z (3 : Fin (10 : ℕ)) && z (4 : Fin (10 : ℕ)) || z (4 : Fin (10 : ℕ)) && z (0 : Fin (10 : ℕ)) || z (0 : Fin (10 : ℕ)) && z (5 : Fin (10 : ℕ)) || z (1 : Fin (10 : ℕ)) && z (6 : Fin (10 : ℕ)) || z (2 : Fin (10 : ℕ)) && z (7 : Fin (10 : ℕ)) || z (3 : Fin (10 : ℕ)) && z (8 : Fin (10 : ℕ)) || z (4 : Fin (10 : ℕ)) && z (9 : Fin (10 : ℕ)) || z (5 : Fin (10 : ℕ)) && z (7 : Fin (10 : ℕ)) || z (7 : Fin (10 : ℕ)) && z (9 : Fin (10 : ℕ)) || z (9 : Fin (10 : ℕ)) && z (6 : Fin (10 : ℕ)) || z (6 : Fin (10 : ℕ)) && z (8 : Fin (10 : ℕ)) || z (8 : Fin (10 : ℕ)) && z (5 : Fin (10 : ℕ))) x = t at *
  cases t
  · have hf := clean x ht
    change ws.getD u false = false ∧ ws.getD v false = false at hf
    rw [hf.1,hf.2] at mismatch
    contradiction
  · cases hu : ws.getD u false <;> cases hv : ws.getD v false
    · exact ⟨ht,rfl,rfl⟩
    all_goals rw [hu,hv] at mismatch; exact False.elim (mismatch rfl)
