import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4041_733
    (orbits :
      let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ (Y : Finset (Fin 42)), Y.card ≤ 2 →
        (∀ u ∈ Y, u.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) →
        ∃ p : Fin 42 → Fin 42, Function.Bijective p ∧
          (∀ u v, (E (p u) (p v) ∨ E (p v) (p u)) ↔ (E u v ∨ E v u)) ∧
          (Y.image p = ∅ ∨ Y.image p = {0} ∨ Y.image p = {0, 1} ∨ Y.image p = {0, 22}))
    (base :
      let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let A := fun (D : Circuit) (S : Finset (Fin 42)) => ∃ j g,
        D.gates[j]? = some g ∧ g.op = GateOp.and ∧
        (D.wires (List.ofFn fun v => decide (v ∈ S))).getD (42 + j) false = true
      ∀ D : Circuit, Monotone2 D → D.size ≤ 124 →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v, E u v ∧ x u = true ∧ x v = true) → ¬ A D ∅ ∧ ¬ A D {0})
    (sameSide :
      let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ D : Circuit, Monotone2 D → D.size ≤ 124 →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v, E u v ∧ x u = true ∧ x v = true) →
        ¬ ∃ j g, D.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (D.wires (List.ofFn fun v : Fin 42 => decide (v ∈ ({0, 1} : Finset (Fin 42))))).getD
            (42 + j) false = true)
    (opposite :
      let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ D : Circuit, Monotone2 D → D.size ≤ 124 →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v, E u v ∧ x u = true ∧ x v = true) →
        ¬ ∃ j g, D.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (D.wires (List.ofFn fun v : Fin 42 => decide (v ∈ ({0, 22} : Finset (Fin 42))))).getD
            (42 + j) false = true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (42 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → x2.card ≤ (2 : ℕ) → (∀ x6 ∈ x2, ↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → (∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x9 : Fin (42 : ℕ)) => Decidable.decide (x9 ∈ x2))).getD ((42 : ℕ) + x7) Bool.false = Bool.true) → ∃ (x8 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (42 : ℕ)) (x10 : Fin (42 : ℕ)), (↑x9 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x10 ∧ (↑x10 + (21 : ℕ) - ↑x9) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) := by
  intro C Y hMono hSize hCard hAllowed hActive
  let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  by_contra hNoWitness
  have agree (x : Fin 42 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true := by
    by_contra hBad
    exact hNoWitness ⟨x, hBad⟩
  obtain ⟨p, hBij, hEdges, hImage⟩ := orbits Y hCard hAllowed

  -- Rename the inputs and keep the indices of all gate wires.
  let renameIndex (i : ℕ) : ℕ := if hi : i < 42 then (p ⟨i, hi⟩).val else i
  let renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map renameIndex⟩
  let D : Circuit := ⟨C.gates.map renameGate, renameIndex C.output⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have late (i : ℕ) (hi : 42 ≤ i) : renameIndex i = i := dif_neg (Nat.not_lt.mpr hi)
  have indexBound (i k : ℕ) (hk : 42 ≤ k) (hi : i < k) : renameIndex i < k := by
    by_cases hInput : i < 42
    · rw [show renameIndex i = (p ⟨i, hInput⟩).val from dif_pos hInput]
      exact (p ⟨i, hInput⟩).isLt.trans_le hk
    · rwa [late i (Nat.le_of_not_gt hInput)]
  have startReads (x : Fin 42 → Bool) (i : ℕ) :
      (List.ofFn x).getD (renameIndex i) false =
        (List.ofFn fun v : Fin 42 => x (p v)).getD i false := by
    by_cases hi : i < 42
    · have hi' : renameIndex i < 42 := indexBound i 42 le_rfl hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi'),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      simp [renameIndex, hi]
    · have oldMissing : (List.ofFn fun v : Fin 42 => x (p v)).getD i false = false :=
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
      have newMissing : (List.ofFn x).getD i false = false :=
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
      rw [late i (Nat.le_of_not_gt hi), oldMissing, newMissing]

  have scans (gs : List Gate) (old new : List Bool) (hlen : old.length = new.length)
      (hstart : 42 ≤ old.length) (read : ∀ i, new.getD (renameIndex i) false = old.getD i false) :
      ∀ i, ((gs.map renameGate).foldl step new).getD (renameIndex i) false =
        (gs.foldl step old).getD i false := by
    induction gs generalizing old new with
    | nil => exact read
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have sameValue :
          (renameGate g).op.eval ((renameGate g).inputs.map fun i => new.getD i false) =
            g.op.eval (g.inputs.map fun i => old.getD i false) := by
        change g.op.eval ((g.inputs.map renameIndex).map fun i => new.getD i false) = _
        rw [List.map_map]
        congr 1
        exact List.map_congr_left fun i _ => read i
      apply ih
      · simp [step, hlen]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      · intro i
        simp only [step]
        by_cases hi : i < old.length
        · rw [List.getD_append _ _ _ _ (indexBound i new.length (hlen ▸ hstart) (hlen ▸ hi)),
            List.getD_append _ _ _ _ hi]
          exact read i
        · have hi' : old.length ≤ i := Nat.le_of_not_gt hi
          rw [late i (hstart.trans hi'), List.getD_append_right _ _ _ _ (hlen ▸ hi'),
            List.getD_append_right _ _ _ _ hi', ← hlen, sameValue]
  have relabelWires (x : Fin 42 → Bool) (i : ℕ) :
      (D.wires (List.ofFn x)).getD (renameIndex i) false =
        (C.wires (List.ofFn fun v : Fin 42 => x (p v))).getD i false :=
    scans C.gates _ _ (by simp) (by simp) (startReads x) i

  have hDM : Monotone2 D := by
    intro g hg
    change g ∈ C.gates.map renameGate at hg
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg
    simpa [renameGate] using hMono g hg
  have hDS : D.size ≤ 124 := by simpa [D, Circuit.size] using hSize

  -- Use the undirected incidence relation because the permutation may exchange the two sides.
  have hImageEdges (x : Fin 42 → Bool) :
      (∃ u v, E u v ∧ x (p u) = true ∧ x (p v) = true) ↔
        (∃ u v, E u v ∧ x u = true ∧ x v = true) := by
    constructor
    · rintro ⟨u, v, he, hu, hv⟩
      rcases (hEdges u v).mpr (Or.inl he) with e | e
      · exact ⟨p u, p v, e, hu, hv⟩
      · exact ⟨p v, p u, e, hv, hu⟩
    · rintro ⟨u, v, he, hu, hv⟩
      obtain ⟨a, rfl⟩ := hBij.2 u
      obtain ⟨b, rfl⟩ := hBij.2 v
      rcases (hEdges a b).mp (Or.inl he) with e | e
      · exact ⟨a, b, e, hu, hv⟩
      · exact ⟨b, a, e, hv, hu⟩
  have hDAgree (x : Fin 42 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true := by
    have he : D.eval (List.ofFn x) = C.eval (List.ofFn fun v : Fin 42 => x (p v)) :=
      relabelWires x C.output
    rw [he]
    exact (agree _).trans (hImageEdges x)

  obtain ⟨j, g, hj, hAnd, hOn⟩ := hActive
  have hSameInput :
      (fun v : Fin 42 => decide (p v ∈ Y.image p)) =
        (fun v : Fin 42 => decide (v ∈ Y)) := by
    funext v
    simp [Finset.mem_image, hBij.1.eq_iff]
  have hOnD : ∃ j g, D.gates[j]? = some g ∧ g.op = GateOp.and ∧
      (D.wires (List.ofFn fun v : Fin 42 => decide (v ∈ Y.image p))).getD (42 + j) false = true := by
    refine ⟨j, renameGate g, ?_, hAnd, ?_⟩
    · change (C.gates.map renameGate)[j]? = some (renameGate g)
      simp [hj]
    · have hr := relabelWires (fun v : Fin 42 => decide (v ∈ Y.image p)) (42 + j)
      rw [late (42 + j) (by omega), hSameInput] at hr
      exact hr.trans hOn
  rcases hImage with hEmpty | hSingleton | hSame | hOpposite
  · rw [hEmpty] at hOnD
    exact (base D hDM hDS hDAgree).1 hOnD
  · rw [hSingleton] at hOnD
    exact (base D hDM hDS hDAgree).2 hOnD
  · rw [hSame] at hOnD
    exact sameSide D hDM hDS hDAgree hOnD
  · rw [hOpposite] at hOnD
    exact opposite D hDM hDS hDAgree hOnD
