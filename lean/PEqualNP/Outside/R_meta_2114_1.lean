import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
set_option synthInstance.maxSize 512 in
theorem PEqualNP.Outside.R_meta_2114_1
    (atFour :
      let readers : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
        fun C v => Finset.univ.filter (fun j : Fin C.size => v.val ∈ (C.gates.get j).inputs)
      let clean (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
        ∀ j : Fin C.size, let g := C.gates.get j
        (∀ w ∈ g.inputs, w < 9 + j.val) ∧ g.inputs.Nodup ∧
          ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
            (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))
      let f (x : Fin 9 → Bool) : Bool :=
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = f → clean C →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)), (readers C v).Nonempty ∧
          (readers C v).card ≤ 2 ∧
          ∀ j ∈ readers C v, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (readers C 4).card = 2 → False)
    (relabel :
      let readers : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
        fun C v => Finset.univ.filter (fun j : Fin C.size => v.val ∈ (C.gates.get j).inputs)
      let clean (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
        ∀ j : Fin C.size, let g := C.gates.get j
        (∀ w ∈ g.inputs, w < 9 + j.val) ∧ g.inputs.Nodup ∧
          ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
            (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (e : Fin 9 ≃ Fin 9),
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → clean C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.IsMinimalCircuit 9 D ∧ D.size = C.size ∧ clean D ∧
          (∀ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 D x =
            PEqualNP.MetaComplexity.circuitFun 9 C (fun i => x (e i))) ∧
          ∀ v : Fin 9, (readers D (e v)).card = (readers C v).card ∧
            ((∀ j ∈ readers C v, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
              ∀ j ∈ readers D (e v), (D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x7 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x7).card = (2 : ℕ)) → False := by
  dsimp only
  intro C hc hor
  rintro ⟨v, hv, hdup⟩
  let readers : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
    fun C v => Finset.univ.filter (fun j : Fin C.size => v.val ∈ (C.gates.get j).inputs)
  let f (x : Fin 9 → Bool) : Bool :=
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have hfn : PEqualNP.MetaComplexity.circuitFun 9 C = f := by
    rw [hc.2.2.1]
    funext x
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] <;> rfl
  let e6 : Fin 9 ≃ Fin 9 :=
    ⟨fun i => ([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0,
      fun i => ([1, 0, 5, 8, 6, 2, 4, 7, 3] : List (Fin 9)).getD i.val 0,
      by decide +kernel, by decide +kernel⟩
  let e7 : Fin 9 ≃ Fin 9 :=
    ⟨fun i => ([1, 2, 3, 8, 6, 0, 7, 4, 5] : List (Fin 9)).getD i.val 0,
      fun i => ([5, 0, 1, 2, 7, 8, 4, 6, 3] : List (Fin 9)).getD i.val 0,
      by decide +kernel, by decide +kernel⟩
  have hv' : v = 4 ∨ v = 6 ∨ v = 7 := by simpa using hv
  have choice : ∃ e : Fin 9 ≃ Fin 9, e v = 4 ∧
      (∀ i ∈ ([4, 6, 7] : List (Fin 9)), e.symm i ∈ ([4, 6, 7] : List (Fin 9))) ∧
      (∀ x : Fin 9 → Bool, f (fun i => x (e i)) = f x) := by
    rcases hv' with rfl | rfl | rfl
    · exact ⟨Equiv.refl _, rfl, fun i hi => hi, fun x => rfl⟩
    · exact ⟨e6, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨e7, by decide +kernel, by decide +kernel, by decide +kernel⟩
  obtain ⟨e, he, fromSpecial, hinv⟩ := choice
  obtain ⟨D, hMin, hSize, hClean, hEval, hReaders⟩ := relabel C e hc.1 hc.2.2.2.1
  have hDsmall : D.size ≤ 15 := by rw [hSize]; exact hc.2.1
  have hDfun : PEqualNP.MetaComplexity.circuitFun 9 D = f := by
    funext x
    exact (hEval x).trans ((congrFun hfn _).trans (hinv x))
  have hDspecial : ∀ i ∈ ([4, 6, 7] : List (Fin 9)), (readers D i).Nonempty ∧
      (readers D i).card ≤ 2 ∧
      ∀ j ∈ readers D i, (D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro i hi
    have hj := fromSpecial i hi
    obtain ⟨hcount, hor'⟩ := hReaders (e.symm i)
    simp only [Equiv.apply_symm_apply] at hcount hor'
    change (readers D i).card = (readers C (e.symm i)).card at hcount
    obtain ⟨hnon, hle, _⟩ := hc.2.2.2.2 (e.symm i) hj
    refine ⟨Finset.card_pos.mp ?_, ?_, hor' (hor (e.symm i) hj)⟩
    · rw [hcount]
      exact Finset.card_pos.mpr hnon
    · rw [hcount]
      exact hle
  have hDdup := (hReaders v).1
  rw [he, hdup] at hDdup
  exact atFour D hMin hDsmall hDfun hClean hDspecial hDdup
