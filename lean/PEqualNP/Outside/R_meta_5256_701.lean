import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5256_701
    (hOutAnd : let D : Finset (Fin 13) := {0, 1, 3, 9};
      let P : Bool → List Bool → Prop := fun b xs =>
        if b = true then ∃ p l : Fin 13, p - l ∈ D ∧
          xs = (List.ofFn fun q : Fin 13 => decide (q = p)) ++ List.ofFn fun q : Fin 13 => decide (q = l)
        else ∃ Q : Finset (Fin 13), Q.card = 4 ∧ (∀ l : Fin 13, {q ∈ Q | q - l ∈ D}.card ≤ 2) ∧
          xs = (List.ofFn fun q : Fin 13 => decide (q ∈ Q)) ++ List.ofFn fun l : Fin 13 => decide (∀ q ∈ Q, q - l ∉ D);
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        26 ≤ C.output → C.output < 26 + C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ b xs, P b xs → C.eval xs = b) →
        2 ≤ C.lineDeg 26 (Finset.Ico 13 26) →
        (∀ j < C.size, ∀ w ≤ 26 + j, ∃ b xs, P b xs ∧ (C.wires xs).getD (26 + j) false = b ∧
          (if w = 26 + j then false else (C.wires xs).getD w false) = !b) →
        (∃ i j, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone 26 C i j) →
        64 ≤ C.size)
    (hOutOr : let D : Finset (Fin 13) := {0, 1, 3, 9};
      let P : Bool → List Bool → Prop := fun b xs =>
        if b = true then ∃ p l : Fin 13, p - l ∈ D ∧
          xs = (List.ofFn fun q : Fin 13 => decide (q = p)) ++ List.ofFn fun q : Fin 13 => decide (q = l)
        else ∃ Q : Finset (Fin 13), Q.card = 4 ∧ (∀ l : Fin 13, {q ∈ Q | q - l ∈ D}.card ≤ 2) ∧
          xs = (List.ofFn fun q : Fin 13 => decide (q ∈ Q)) ++ List.ofFn fun l : Fin 13 => decide (∀ q ∈ Q, q - l ∉ D);
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        26 ≤ C.output → C.output < 26 + C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ b xs, P b xs → C.eval xs = b) →
        2 ≤ C.lineDeg 26 (Finset.Ico 13 26) →
        (∀ j < C.size, ∀ w ≤ 26 + j, ∃ b xs, P b xs ∧ (C.wires xs).getD (26 + j) false = b ∧
          (if w = 26 + j then false else (C.wires xs).getD w false) = !b) →
        (∃ i j, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone 26 C i j) →
        64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) → (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) → (64 : ℕ) ≤ x3.size := by
  intro D P C hm hr hcomp hdeg hdist hcone
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      simp only [List.foldl_cons, ht, List.append_assoc, List.singleton_append]
  have hQp : ∀ p : Fin 13,
      ({p, p + 1, p + 2, p + 5} : Finset (Fin 13)).card = 4 ∧
      ∀ l : Fin 13, {q ∈ ({p, p + 1, p + 2, p + 5} : Finset (Fin 13)) | q - l ∈ D}.card ≤ 2 := by
    decide
  have hQl : ∀ l : Fin 13,
      ({l - 3, l - 2, l - 1, l + 2} : Finset (Fin 13)).card = 4 ∧
      (∀ c : Fin 13, {q ∈ ({l - 3, l - 2, l - 1, l + 2} : Finset (Fin 13)) | q - c ∈ D}.card ≤ 2) ∧
      ∀ q ∈ ({l - 3, l - 2, l - 1, l + 2} : Finset (Fin 13)), q - l ∉ D := by
    decide
  have hge26 : 26 ≤ C.output := by
    by_contra hlt
    push_neg at hlt
    by_cases hp : C.output < 13
    · let p : Fin 13 := ⟨C.output, hp⟩
      let Q : Finset (Fin 13) := {p, p + 1, p + 2, p + 5}
      let xs := (List.ofFn fun q : Fin 13 => decide (q ∈ Q)) ++ List.ofFn fun l : Fin 13 => decide (∀ q ∈ Q, q - l ∉ D)
      have hP : P false xs := ⟨Q, (hQp p).1, (hQp p).2, rfl⟩
      have hev := hcomp false xs hP
      obtain ⟨t, ht, _⟩ := hpre C.gates xs
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at hev
      rw [ht, List.getD_append _ _ _ _ (by simp [xs]; omega)] at hev
      have h1 : xs.getD C.output false = true := by
        simp only [xs]
        rw [List.getD_append _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        exact decide_eq_true (by simp [Q, p])
      rw [h1] at hev
      exact Bool.noConfusion hev
    · let l : Fin 13 := ⟨C.output - 13, by omega⟩
      let Q : Finset (Fin 13) := {l - 3, l - 2, l - 1, l + 2}
      let xs := (List.ofFn fun q : Fin 13 => decide (q ∈ Q)) ++ List.ofFn fun c : Fin 13 => decide (∀ q ∈ Q, q - c ∉ D)
      have hP : P false xs := ⟨Q, (hQl l).1, (hQl l).2.1, rfl⟩
      have hev := hcomp false xs hP
      obtain ⟨t, ht, _⟩ := hpre C.gates xs
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at hev
      rw [ht, List.getD_append _ _ _ _ (by simp [xs]; omega)] at hev
      have h1 : xs.getD C.output false = true := by
        simp only [xs]
        rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        have hidx : (⟨C.output - (List.ofFn fun q : Fin 13 => decide (q ∈ Q)).length, by simp; omega⟩ : Fin 13) = l := by
          ext; simp [l]
        rw [hidx]
        exact decide_eq_true (hQl l).2.2
      rw [h1] at hev
      exact Bool.noConfusion hev
  have hlt26 : C.output < 26 + C.size := by
    by_contra hge
    push_neg at hge
    let xs := (List.ofFn fun q : Fin 13 => decide (q = (0 : Fin 13))) ++ List.ofFn fun q : Fin 13 => decide (q = (0 : Fin 13))
    have hP : P true xs := ⟨0, 0, by decide, rfl⟩
    have hev := hcomp true xs hP
    obtain ⟨t, ht, hl⟩ := hpre C.gates xs
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at hev
    have hsz : C.size = C.gates.length := rfl
    rw [ht, List.getD_eq_default _ _ (by simp [xs, hl]; omega)] at hev
    exact Bool.noConfusion hev
  have hidx : C.output - 26 < C.gates.length := by
    have : C.size = C.gates.length := rfl
    omega
  have hmem := (hm _ (List.getElem_mem hidx)).1
  have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - 26) = C.gates[C.output - 26] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    simp [List.getD_eq_getElem?_getD, hidx]
  rw [← hgat] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hop | hop
  · exact hOutAnd C hm hr hge26 hlt26 hop hcomp hdeg hdist hcone
  · exact hOutOr C hm hr hge26 hlt26 hop hcomp hdeg hdist hcone
