import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership PEqualNP.SplitCount in
theorem PEqualNP.Outside.R_meta_4147_512
    (lowAnd :
      let S := singerLines3
      let row := fun Q => incidenceInput Q (missLines S Q)
      let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
      let inner := fun (C : Circuit) i => PEqualNP.ReadTwo.isAnd C i ∧
        ∃ j, PEqualNP.ReadTwo.isAnd C j ∧ InCone 26 C i j
      let hard := fun C : Circuit => (∃ i, inner C i) ∧ ∀ i, inner C i →
        (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26 + i) false = true) ∧
        2 ≤ ((incidences S).filter fun e =>
          ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false).card
      ∀ C, valid C → hard C →
        26 ≤ C.output ∧ C.output < 26 + C.gates.length →
        (∀ j, PEqualNP.ReadTwo.isAnd C j → ¬ inner C j →
          InConeOrSelf 26 C j (C.output - 26) →
          ∀ Q, IsQuadrangle S Q → (C.wires (row Q)).getD (26 + j) false = false) →
        PEqualNP.ReadTwo.nAnd C ≤ 13 →
        64 ≤ C.size)
    (highAnd :
      let S := singerLines3
      let row := fun Q => incidenceInput Q (missLines S Q)
      let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
      let inner := fun (C : Circuit) i => PEqualNP.ReadTwo.isAnd C i ∧
        ∃ j, PEqualNP.ReadTwo.isAnd C j ∧ InCone 26 C i j
      let hard := fun C : Circuit => (∃ i, inner C i) ∧ ∀ i, inner C i →
        (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26 + i) false = true) ∧
        2 ≤ ((incidences S).filter fun e =>
          ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false).card
      ∀ C, valid C → hard C →
        26 ≤ C.output ∧ C.output < 26 + C.gates.length →
        (∀ j, PEqualNP.ReadTwo.isAnd C j → ¬ inner C j →
          InConeOrSelf 26 C j (C.output - 26) →
          ∀ Q, IsQuadrangle S Q → (C.wires (row Q)).getD (26 + j) false = false) →
        14 ≤ PEqualNP.ReadTwo.nAnd C →
        64 ≤ C.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x4 → x3.eval (x2 x4) = Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ (x6 : ℕ), x4 x5 x6) ∧ ∀ (x6 : ℕ), x4 x5 x6 → (∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x8 ∧ (x5.wires (x2 x8)).getD ((26 : ℕ) + x6) Bool.false = Bool.true) ∧ (2 : ℕ) ≤ {x8 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x8.1} {x8.2}) = Bool.false}.card; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x5 x6 → (64 : ℕ) ≤ x6.size := by
  dsimp only
  intro C hvalid hhard
  obtain ⟨hmono, hback, hpos, hneg⟩ := hvalid
  have singerEq (l : Fin 13) : singerLines3 l =
      (Finset.univ.filter fun p : Fin 13 => (p.val + 13 - l.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ)) := rfl
  have missEq (Q : Finset (Fin 13)) : missLines singerLines3 Q =
      (Finset.univ.filter fun l : Fin 13 => Disjoint (singerLines3 l) Q) := rfl
  have inputEq (X Y : Finset (Fin 13)) : incidenceInput X Y =
      List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) := rfl
  have coneEq (cs : List (List ℕ)) (g : Gate) : coneStep 26 cs g =
      cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => (w - 26) :: cs.getD (w - 26) [])] := rfl
  have orEval (values : List Bool) : GateOp.or.eval values = values.any id := rfl
  have hwires_len : ∀ (gs : List Gate) (acc : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
        acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g r ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  have hwires_prefix : ∀ (gs : List Gate) (acc : List Bool) (w : ℕ), w < acc.length →
      (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) acc).getD w false =
        acc.getD w false := by
    intro gs
    induction gs with
    | nil => intro acc w _; rfl
    | cons g r ih =>
      intro acc w hw
      simp only [List.foldl_cons]
      have hlen : w < (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]).length := by
        simp; omega
      rw [ih _ w hlen]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  have hwires_gate : ∀ (x : List Bool), x.length = 26 → ∀ (m : ℕ) (hm : m < C.gates.length),
      (C.wires x).getD (26 + m) false =
        C.gates[m].op.eval (C.gates[m].inputs.map fun i =>
          if i < 26 + m then (C.wires x).getD i false else false) := by
    intro x hxlen m hm
    let step : List Bool → Gate → List Bool :=
      fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    have hsplit : C.gates = C.gates.take m ++ [C.gates[m]] ++ C.gates.drop (m + 1) := by
      have h1 : C.gates.take m ++ C.gates.drop m = C.gates := List.take_append_drop m C.gates
      have h2 : C.gates.drop m = C.gates[m] :: C.gates.drop (m + 1) := List.drop_eq_getElem_cons hm
      calc C.gates = C.gates.take m ++ C.gates.drop m := h1.symm
        _ = C.gates.take m ++ (C.gates[m] :: C.gates.drop (m + 1)) := by rw [h2]
        _ = C.gates.take m ++ [C.gates[m]] ++ C.gates.drop (m + 1) := by simp
    set acc := (C.gates.take m).foldl step x
    have haccLen : acc.length = 26 + m := by
      dsimp only [acc]
      rw [hwires_len, hxlen, List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)]
    have haccAt : ∀ u < 26 + m, (C.wires x).getD u false = acc.getD u false := by
      intro u hu
      unfold Circuit.wires
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hu2 : u < (step acc C.gates[m]).length := by simp [step]; omega
      rw [hwires_prefix (C.gates.drop (m + 1)) _ u hu2]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < acc.length)]
    have hmain : (C.wires x).getD (26 + m) false =
        C.gates[m].op.eval (C.gates[m].inputs.map fun i => acc.getD i false) := by
      unfold Circuit.wires
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hjlt : 26 + m < (step acc C.gates[m]).length := by simp [step, haccLen]
      rw [hwires_prefix (C.gates.drop (m + 1)) _ (26 + m) hjlt]
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    rw [hmain]
    congr 1
    apply List.map_congr_left
    intro i _
    split_ifs with hlt
    · exact (haccAt i hlt).symm
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : acc.length ≤ i)]
  have hQ0 : IsQuadrangle singerLines3 ({0, 1, 2, 5} : Finset (Fin 13)) := by
    refine ⟨by decide, fun l => ?_⟩
    have heq : (({0, 1, 2, 5} : Finset (Fin 13)) ∩ singerLines3 l) =
        ({0, 1, 2, 5} : Finset (Fin 13)).filter (fun p => (p.val + 13 - l.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ)) := by
      ext p; simp [singerEq]
    rw [heq]
    fin_cases l <;> decide
  have hQ0_miss7 : (7 : Fin 13) ∈ missLines singerLines3 ({0, 1, 2, 5} : Finset (Fin 13)) := by
    rw [missEq, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Finset.disjoint_left.mpr fun x hx1 hx2 => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    rcases hx2 with rfl | rfl | rfl | rfl <;> simp [singerEq] at hx1
  have hshift : ∀ (s p l : Fin 13), p + s ∈ singerLines3 (l + s) ↔ p ∈ singerLines3 l := by
    intro s p l
    simp only [singerEq, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_add]
    have hmod : ((p.val + s.val) % 13 + 13 - (l.val + s.val) % 13) % 13 = (p.val + 13 - l.val) % 13 := by omega
    rw [hmod]
  have hQshift : ∀ (s : Fin 13), IsQuadrangle singerLines3 (({0, 1, 2, 5} : Finset (Fin 13)).image (· + s)) := by
    intro s
    have hinj : Function.Injective (fun x : Fin 13 => x + s) := add_left_injective s
    constructor
    · rw [Finset.card_image_of_injective _ hinj]; exact hQ0.1
    · intro l
      have hsub : (({0, 1, 2, 5} : Finset (Fin 13)).image (· + s) ∩ singerLines3 l) =
          (({0, 1, 2, 5} : Finset (Fin 13)) ∩ singerLines3 (l - s)).image (· + s) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hxl⟩
          refine ⟨a, ⟨ha, ?_⟩, rfl⟩
          have := (hshift s a (l - s)).mp (by simpa using hxl)
          exact this
        · rintro ⟨a, ⟨ha, hal⟩, rfl⟩
          refine ⟨⟨a, ha, rfl⟩, ?_⟩
          have := (hshift s a (l - s)).mpr hal
          simpa using this
      rw [hsub, Finset.card_image_of_injective _ hinj]
      exact hQ0.2 (l - s)
  have hPointInQ : ∀ p : Fin 13, ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧ p ∈ Q := by
    intro p
    refine ⟨({0, 1, 2, 5} : Finset (Fin 13)).image (· + p), hQshift p, ?_⟩
    exact Finset.mem_image.mpr ⟨0, by simp, zero_add p⟩
  have hLineInMiss : ∀ l : Fin 13, ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧ l ∈ missLines singerLines3 Q := by
    intro l
    refine ⟨({0, 1, 2, 5} : Finset (Fin 13)).image (· + (l - 7)), hQshift (l - 7), ?_⟩
    rw [missEq, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Finset.disjoint_left.mpr ?_⟩
    intro x hxl hxQ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxQ
    have h7 : a ∈ singerLines3 (7 : Fin 13) := by
      have := (hshift (l - 7) a 7).mp (by simpa using hxl)
      exact this
    have hdisj := (Finset.mem_filter.mp hQ0_miss7).2
    exact (Finset.disjoint_left.mp hdisj) h7 ha
  have houtBounds : 26 ≤ C.output ∧ C.output < 26 + C.gates.length := by
    constructor
    · by_contra hlt26
      push Not at hlt26
      by_cases hlt13 : C.output < 13
      · obtain ⟨Q, hQ, hpQ⟩ := hPointInQ ⟨C.output, hlt13⟩
        have hfalse := hneg Q hQ
        unfold Circuit.eval Circuit.wires at hfalse
        have hlenIn : (incidenceInput Q (missLines singerLines3 Q)).length = 26 := by
          simp [inputEq]
        rw [hwires_prefix C.gates _ C.output (by omega)] at hfalse
        have htrue : (incidenceInput Q (missLines singerLines3 Q)).getD C.output false = true := by
          rw [inputEq]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt13]), List.getElem?_ofFn]
          simp [hlt13, hpQ]
        rw [htrue] at hfalse; cases hfalse
      · have hl13 : C.output - 13 < 13 := by omega
        obtain ⟨Q, hQ, hlQ⟩ := hLineInMiss ⟨C.output - 13, hl13⟩
        have hfalse := hneg Q hQ
        unfold Circuit.eval Circuit.wires at hfalse
        have hlenIn : (incidenceInput Q (missLines singerLines3 Q)).length = 26 := by
          simp [inputEq]
        rw [hwires_prefix C.gates _ C.output (by omega)] at hfalse
        have htrue : (incidenceInput Q (missLines singerLines3 Q)).getD C.output false = true := by
          rw [inputEq]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), List.length_ofFn, List.getElem?_ofFn]
          simp [hl13, hlQ]
        rw [htrue] at hfalse; cases hfalse
    · by_contra hge
      push Not at hge
      have h00 : (0 : Fin 13) ∈ singerLines3 (0 : Fin 13) := by simp [singerEq]
      have htrue := hpos 0 0 h00
      unfold Circuit.eval Circuit.wires at htrue
      have hlenW : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13)))).length = 26 + C.gates.length := by
        rw [hwires_len]; simp [inputEq]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at htrue
      cases htrue
  have hcones_len : ∀ (gs : List Gate) (acc : List (List ℕ)),
      (gs.foldl (coneStep 26) acc).length = acc.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g r ih =>
      intro acc
      simp only [List.foldl_cons, ih, coneEq, List.length_append, List.length_cons, List.length_nil]
      omega
  have hcones_prefix : ∀ (gs : List Gate) (acc : List (List ℕ)) (m : ℕ), m < acc.length →
      (gs.foldl (coneStep 26) acc).getD m [] = acc.getD m [] := by
    intro gs
    induction gs with
    | nil => intro acc m _; rfl
    | cons g r ih =>
      intro acc m hm
      simp only [List.foldl_cons]
      have hlt : m < (coneStep 26 acc g).length := by simp [coneEq]; omega
      rw [ih _ m hlt]
      simp only [coneEq, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
  have hcones_at : ∀ (m : ℕ) (hm : m < C.gates.length) (i : ℕ),
      InCone 26 C i m ↔
        ∃ w ∈ C.gates[m].inputs, 26 ≤ w ∧ w < 26 + m ∧ (w - 26 = i ∨ InCone 26 C i (w - 26)) := by
    intro m hm i
    have hsplit : C.gates = C.gates.take m ++ [C.gates[m]] ++ C.gates.drop (m + 1) := by
      have h1 : C.gates.take m ++ C.gates.drop m = C.gates := List.take_append_drop m C.gates
      have h2 : C.gates.drop m = C.gates[m] :: C.gates.drop (m + 1) := List.drop_eq_getElem_cons hm
      calc C.gates = C.gates.take m ++ C.gates.drop m := h1.symm
        _ = C.gates.take m ++ (C.gates[m] :: C.gates.drop (m + 1)) := by rw [h2]
        _ = C.gates.take m ++ [C.gates[m]] ++ C.gates.drop (m + 1) := by simp
    set acc := (C.gates.take m).foldl (coneStep 26) []
    have haccLen : acc.length = m := by
      dsimp only [acc]; rw [hcones_len, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)]
    have haccAt : ∀ u < m, (cones 26 C).getD u [] = acc.getD u [] := by
      intro u hu
      unfold cones
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hu2 : u < (coneStep 26 acc C.gates[m]).length := by simp [coneEq]; omega
      rw [hcones_prefix (C.gates.drop (m + 1)) _ u hu2]
      simp only [coneEq, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < acc.length)]
    have hcm : (cones 26 C).getD m [] =
        (C.gates[m].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + m))).flatMap
          (fun w => (w - 26) :: acc.getD (w - 26) []) := by
      unfold cones
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hmlt : m < (coneStep 26 acc C.gates[m]).length := by simp [coneEq, haccLen]
      rw [hcones_prefix (C.gates.drop (m + 1)) _ m hmlt]
      simp only [coneEq, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    unfold InCone
    rw [hcm, List.mem_flatMap]
    constructor
    · rintro ⟨w, hwF, hwi⟩
      rw [List.mem_filter, decide_eq_true_eq] at hwF
      obtain ⟨hwIn, h26, hlt⟩ := hwF
      refine ⟨w, hwIn, h26, hlt, ?_⟩
      simp only [List.mem_cons] at hwi
      rcases hwi with rfl | hmem
      · exact Or.inl rfl
      · right; rw [haccAt (w - 26) (by omega)]; exact hmem
    · rintro ⟨w, hwIn, h26, hlt, hwi⟩
      refine ⟨w, List.mem_filter.mpr ⟨hwIn, decide_eq_true ⟨h26, hlt⟩⟩, ?_⟩
      simp only [List.mem_cons]
      rcases hwi with rfl | hmem
      · exact Or.inl rfl
      · right; rw [← haccAt (w - 26) (by omega)]; exact hmem
  have htopRejects : ∀ j < C.gates.length, (gateAt C j).op = .and →
      ¬ ((gateAt C j).op = .and ∧ ∃ k, (gateAt C k).op = .and ∧ InCone 26 C j k) →
      InConeOrSelf 26 C j (C.output - 26) →
      ∀ Q, IsQuadrangle singerLines3 Q →
        (C.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + j) false = false := by
    intro j hj hjAnd hjTop hReach Q hQ
    have hprop : ∀ m < C.gates.length, InConeOrSelf 26 C j m →
        (C.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + j) false = true →
        (C.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + m) false = true := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro hm hjm hjT
        rcases hjm with rfl | hcone
        · exact hjT
        · have hmNotAnd : C.gates[m].op ≠ .and := by
            intro hAnd
            apply hjTop
            refine ⟨hjAnd, m, ?_, hcone⟩
            unfold gateAt
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
            exact hAnd
          have hmOr : C.gates[m].op = .or := by
            have hM := hmono C.gates[m] (List.getElem_mem hm)
            rcases hM.1 with h | h
            · exact False.elim (hmNotAnd h)
            · exact h
          obtain ⟨w, hwIn, h26, hlt, hwi⟩ := (hcones_at m hm j).mp hcone
          have hwTrue : (C.wires (incidenceInput Q (missLines singerLines3 Q))).getD w false = true := by
            have hsub := ih (w - 26) (by omega) (by omega) (by
              rcases hwi with h | h
              · exact Or.inl h.symm
              · exact Or.inr h) hjT
            rw [show 26 + (w - 26) = w by omega] at hsub
            exact hsub
          rw [hwires_gate (incidenceInput Q (missLines singerLines3 Q)) (by simp [inputEq]) m hm, hmOr]
          simp only [orEval, List.any_eq_true, id_eq]
          refine ⟨true, ?_, rfl⟩
          rw [List.mem_map]
          refine ⟨w, hwIn, ?_⟩
          rw [ite_eq_left hlt, hwTrue]
    cases hv : (C.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + j) false
    · rfl
    · exfalso
      have hOutT := hprop (C.output - 26) (by omega) hReach hv
      rw [show 26 + (C.output - 26) = C.output by omega] at hOutT
      have hOutF := hneg Q hQ
      unfold Circuit.eval at hOutF
      rw [hOutT] at hOutF
      cases hOutF
  have andIff (i : ℕ) : PEqualNP.ReadTwo.isAnd C i ↔ (gateAt C i).op = .and := by
    constructor
    · exact fun hi => hi.2
    · intro hi
      refine ⟨?_, hi⟩
      by_contra! outside
      change (C.gates.getD i ⟨.or, []⟩).op = .and at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none outside] at hi
      cases hi
  have top' (j : ℕ) (hj : PEqualNP.ReadTwo.isAnd C j)
      (hjTop : ¬ (PEqualNP.ReadTwo.isAnd C j ∧ ∃ k, PEqualNP.ReadTwo.isAnd C k ∧ InCone 26 C j k))
      (hReach : InConeOrSelf 26 C j (C.output - 26))
      (Q : Finset (Fin 13)) (hQ : IsQuadrangle singerLines3 Q) :
      (C.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26 + j) false = false := by
    apply htopRejects j hj.1 hj.2 _ hReach Q hQ
    simpa only [andIff] using hjTop
  by_cases hlow : PEqualNP.ReadTwo.nAnd C ≤ 13
  · refine lowAnd C ⟨hmono, hback, hpos, hneg⟩ ?_ houtBounds top' hlow
    simpa only [andIff] using hhard
  · refine highAnd C ⟨hmono, hback, hpos, hneg⟩ ?_ houtBounds top' (by omega)
    simpa only [andIff] using hhard
