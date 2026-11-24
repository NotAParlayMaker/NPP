import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2114_487
    (short :
      let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 k))
      ∀ C : Circuit, FanInTwo C → C.size ≤ 14 → circuitFun 9 C ≠ f)
    (partners :
      let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 k))
      ∀ C : Circuit, circuitFun 9 C = f → ∀ u ∈ ([4,6,7] : List (Fin 9)), ∀ a b : Fin 9,
        a ≠ u → b ≠ u →
        (∀ g ∈ C.gates, u.val ∈ g.inputs → g.op = .or ∧ (a.val ∈ g.inputs ∨ b.val ∈ g.inputs)) →
        let k := min a.val b.val + 9 * max a.val b.val
        (f (fun i => i == a || i == b) || (k == 27 && u != 4) ||
          (k == 73 && u != 6) || (k == 47 && u != 7)) = true)
    (primary :
      let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 k))
      let lows := ([4,6,7] : List (Fin 9))
      ∀ C : Circuit, IsMinimalCircuit 9 C → C.size = 15 → circuitFun 9 C = f →
        let r := fun u : Fin 9 => ({i : Fin C.size | u.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size))
        (∀ i : Fin C.size, let g := C.gates.get i
          g.inputs.Nodup ∧ g.inputs.length = 2 - (g.op.eval [false]).toNat ∧
          ∀ w ∈ g.inputs, w < 9 + i.val) →
        (∀ u ∈ lows, (r u).Nonempty ∧ (r u).card ≤ 2 ∧ ∀ i ∈ r u, (C.gates.get i).op = .or) →
        (∃ u ∈ lows, (r u).card = 2) →
        (∀ u ∈ lows, ∀ a b : Fin 9, a ≠ u → b ≠ u →
          (∀ g ∈ C.gates, u.val ∈ g.inputs → a.val ∈ g.inputs ∨ b.val ∈ g.inputs) →
          let k := min a.val b.val + 9 * max a.val b.val
          (f (fun i => i == a || i == b) || (k == 27 && u != 4) ||
            (k == 73 && u != 6) || (k == 47 && u != 7)) = true) →
        (∀ g ∈ C.gates, ∀ u ∈ lows, u.val ∈ g.inputs → ∀ w ∈ g.inputs, w < 9) → False)
    (computed :
      let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 k))
      let lows := ([4,6,7] : List (Fin 9))
      ∀ C : Circuit, IsMinimalCircuit 9 C → C.size = 15 → circuitFun 9 C = f →
        let r := fun u : Fin 9 => ({i : Fin C.size | u.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size))
        (∀ i : Fin C.size, let g := C.gates.get i
          g.inputs.Nodup ∧ g.inputs.length = 2 - (g.op.eval [false]).toNat ∧
          ∀ w ∈ g.inputs, w < 9 + i.val) →
        (∀ u ∈ lows, (r u).Nonempty ∧ (r u).card ≤ 2 ∧ ∀ i ∈ r u, (C.gates.get i).op = .or) →
        (∃ u ∈ lows, (r u).card = 2) →
        (∀ u ∈ lows, ∀ a b : Fin 9, a ≠ u → b ≠ u →
          (∀ g ∈ C.gates, u.val ∈ g.inputs → a.val ∈ g.inputs ∨ b.val ∈ g.inputs) →
          let k := min a.val b.val + 9 * max a.val b.val
          (f (fun i => i == a || i == b) || (k == 27 && u != 4) ||
            (k == 73 && u != 6) || (k == 47 && u != 7)) = true) →
        (∃ g ∈ C.gates, (∃ u ∈ lows, u.val ∈ g.inputs) ∧ ∃ w ∈ g.inputs, 9 ≤ w) → False) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x7 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x7).card = (2 : ℕ)) → False := by
  dsimp only
  intro C hC hall hdouble
  obtain ⟨hmin, hsize, hfun, hclean, hcount⟩ := hC
  let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
    (fun k => x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 k))
  have fn : circuitFun 9 C = f := by
    rw [hfun]
    funext x
    simp only [f,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  have full : C.size = 15 := by
    by_contra ne
    exact short C hmin.1 (by omega) fn
  have cleaned (i : Fin C.size) :
      let g := C.gates.get i
      g.inputs.Nodup ∧ g.inputs.length = 2 - (g.op.eval [false]).toNat ∧
      ∀ w ∈ g.inputs, w < 9 + i.val := by
    obtain ⟨earlier, unique, arity⟩ := hclean i
    refine ⟨unique, ?_, earlier⟩
    rcases arity with ⟨op,len⟩ | ⟨op,len⟩
    · simp only [len, op] <;> rfl
    · have operations := (hmin.1 (C.gates.get i) (List.get_mem _ _)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at operations
      rcases operations with andOp | orOp | notOp
      · simp only [len, andOp] <;> rfl
      · simp only [len, orOp] <;> rfl
      · exact (op notOp).elim
  let lows := ([4,6,7] : List (Fin 9))
  let r := fun u : Fin 9 => ({i : Fin C.size | u.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size))
  have counts (u : Fin 9) (hu : u ∈ lows) :
      (r u).Nonempty ∧ (r u).card ≤ 2 ∧ ∀ i ∈ r u, (C.gates.get i).op = .or := by
    exact ⟨(hcount u hu).1, (hcount u hu).2.1, hall u hu⟩
  have allowed (u : Fin 9) (hu : u ∈ lows) (a b : Fin 9) (ha : a ≠ u) (hb : b ≠ u)
      (masked : ∀ g ∈ C.gates, u.val ∈ g.inputs → a.val ∈ g.inputs ∨ b.val ∈ g.inputs) :
      let k := min a.val b.val + 9 * max a.val b.val
      (f (fun i => i == a || i == b) || (k == 27 && u != 4) ||
        (k == 73 && u != 6) || (k == 47 && u != 7)) = true := by
    apply partners C fn u hu a b ha hb
    intro g hg reads
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    let j : Fin C.size := ⟨i, hi⟩
    have inside : j ∈ ({k : Fin C.size | u.val ∈ (C.gates.get k).inputs} : Finset (Fin C.size)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, reads⟩
    exact ⟨hall u hu j inside, masked _ hg reads⟩
  classical
  by_cases all : ∀ g ∈ C.gates, ∀ u ∈ lows, u.val ∈ g.inputs → ∀ w ∈ g.inputs, w < 9
  · exact primary C hmin full fn cleaned counts hdouble allowed all
  · apply computed C hmin full fn cleaned counts hdouble allowed
    by_contra absent
    apply all
    intro g hg u hu read w hw
    exact Nat.lt_of_not_ge (fun late => absent ⟨g, hg, ⟨u, hu, read⟩, w, hw, late⟩)
