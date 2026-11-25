import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1969_1
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      27 ≤ C.size)
    (h2 : ∀ (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b : Fin 14, G.Adj a b ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        ((a = Fin.castAdd 7 u ∧ b = Fin.natAdd 7 t) ∨ (b = Fin.castAdd 7 u ∧ a = Fin.natAdd 7 t))) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.junk G C = ∅)
    (h3 : ∀ (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b : Fin 14, G.Adj a b ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        ((a = Fin.castAdd 7 u ∧ b = Fin.natAdd 7 t) ∨ (b = Fin.castAdd 7 u ∧ a = Fin.natAdd 7 t))) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.junk G C = ∅ →
      PEqualNP.TopForm.andPairs 14 C = 0) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 ≠ x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  intro hex
  obtain ⟨C, hsz, hwf, heval, j1, j2, _, _, _, hj1_op, _, hj1_07, hj1_00, _⟩ := hex
  let adj2 : Fin 14 → Fin 14 → Prop := fun a b =>
    ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
      ((a = Fin.castAdd 7 u ∧ b = Fin.natAdd 7 t) ∨
       (b = Fin.castAdd 7 u ∧ a = Fin.natAdd 7 t))
  let G2 : SimpleGraph (Fin 14) :=
    { Adj := adj2
      symm := ⟨by
        intro a b hab
        obtain ⟨u, t, hinc, hor⟩ := hab
        exact ⟨u, t, hinc, hor.symm⟩⟩
      loopless := ⟨by
        intro a haa
        obtain ⟨u, t, _, hor⟩ := haa
        rcases hor with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · have hv := congrArg Fin.val (h1'.symm.trans h2')
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        · have hv := congrArg Fin.val (h1'.symm.trans h2')
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega⟩ }
  let _ : DecidableRel G2.Adj := fun a b => inferInstanceAs (Decidable (adj2 a b))
  have hG2 : ∀ a b : Fin 14, G2.Adj a b ↔
      ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        ((a = Fin.castAdd 7 u ∧ b = Fin.natAdd 7 t) ∨
         (b = Fin.castAdd 7 u ∧ a = Fin.natAdd 7 t)) := fun _ _ => Iff.rfl
  have hAO2 : PEqualNP.TopForm.IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      exact (hwf j _ hget).1
    · intro j hj w hw
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
        simp [List.getD_eq_getElem?_getD, hget]
      rw [hga] at hw
      obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hwf j _ hget
      rw [hinp] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨_, a, b, hinp, _⟩ := hwf j _ hget
      rw [hinp]
      rfl
  have hgraph_iff : ∀ x : Fin 14 → Bool,
      PEqualNP.MetaComplexity.NestedCover.graphFun G2 ∅ x = true ↔
      ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
    intro x
    change (decide (∃ a ∈ (∅ : Finset (Fin 14)), x a = true) ||
      decide (∃ u v, G2.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp only [Finset.notMem_empty, false_and,
      exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨a, b, ⟨u, t, hinc, hor⟩, ha, hb⟩ := h
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, t, hinc, ha, hb⟩
      · exact ⟨u, t, hinc, hb, ha⟩
    · intro h
      obtain ⟨u, t, hinc, hu, ht⟩ := h
      exact ⟨Fin.castAdd 7 u, Fin.natAdd 7 t, ⟨u, t, hinc, Or.inl ⟨rfl, rfl⟩⟩, hu, ht⟩
  have hfun : PEqualNP.MetaComplexity.circuitFun 14 C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G2 ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    exact (heval x).trans (hgraph_iff x).symm
  have hleast : PEqualNP.TopForm.IsLeastAO G2 C := by
    refine ⟨hAO2, hfun, ?_⟩
    intro C' hAO2' hfun'
    have heval' : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
      intro x
      have hx : C'.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun G2 ∅ x :=
        congrFun hfun' x
      rw [hx]
      exact hgraph_iff x
    exact le_trans hsz (h1 C' hAO2' heval')
  have hjunk : PEqualNP.TopForm.junk G2 C = ∅ := h2 G2 C hG2 hleast
  have hand : PEqualNP.TopForm.andPairs 14 C = 0 := h3 G2 C hG2 hleast hjunk
  have hno_and_cone : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ¬ PEqualNP.EdgeOwnership.InCone 14 C i j := by
    intro i hi j hj hopi hopj hcone
    let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp :=
      PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    unfold PEqualNP.TopForm.andPairs at hand
    have hemp := Finset.eq_empty_iff_forall_notMem.mp (Finset.card_eq_zero.mp hand) (i, j)
    apply hemp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨hi, hj⟩, hopi, hopj, hcone⟩
  -- Wire and cone helpers
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have hstep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g gs ih =>
      intro ws
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hstep_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons]
      have hlt : i < (step ws g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step ws g) i hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hstep_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool)
      (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      gs[j]? = some g →
      (gs.foldl step ws).getD (ws.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < ws.length + j then (gs.foldl step ws).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro ws j g hj; simp at hj
    | cons g0 gs ih =>
      intro ws j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : ws.length < (step ws g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hstep_lt gs (step ws g0) ws.length hlt]
        have hself : (step ws g0).getD ws.length false =
            g0.op.eval (g0.inputs.map fun i => ws.getD i false) := by
          simp only [step, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl ws.length)]
          simp
        rw [hself]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < ws.length
        · have hilt : i < (step ws g0).length := by
            simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          simp only [hi, ↓reduceIte]
          rw [hstep_lt gs (step ws g0) i hilt]
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · simp only [hi, ↓reduceIte]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
            Option.getD_none]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (step ws g0).length = ws.length + 1 := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
        have hidx : ws.length + (j + 1) = (step ws g0).length + j := by omega
        rw [hidx]
        exact ih (step ws g0) j g hj
  let cstep : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (List ℕ) :=
    fun cs g => cs ++ [(g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + cs.length))).flatMap
      (fun w => (w - 14) :: cs.getD (w - 14) [])]
  have hcone_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)) (i : ℕ),
      i < cs.length → (gs.foldl cstep cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons]
      have hlt : i < (cstep cs g).length := by
        simp only [cstep, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (cstep cs g) i hlt]
      simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hcone_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ))
      (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      gs[j]? = some g →
      (gs.foldl cstep cs).getD (cs.length + j) [] =
        (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + (cs.length + j)))).flatMap
          (fun w => (w - 14) :: (gs.foldl cstep cs).getD (w - 14) []) := by
    intro gs
    induction gs with
    | nil => intro cs j g hj; simp at hj
    | cons g0 gs ih =>
      intro cs j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : cs.length < (cstep cs g0).length := by
          simp only [cstep, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hcone_lt gs (cstep cs g0) cs.length hlt]
        have hself : (cstep cs g0).getD cs.length [] =
            (g0.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + cs.length))).flatMap
              (fun w => (w - 14) :: cs.getD (w - 14) []) := by
          simp only [cstep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl cs.length)]
          simp
        rw [hself]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwlt : w - 14 < cs.length := by omega
        have hwlt1 : w - 14 < (cstep cs g0).length := by
          simp only [cstep, List.length_append, List.length_cons, List.length_nil]; omega
        rw [hcone_lt gs (cstep cs g0) (w - 14) hwlt1]
        simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hlen1 : (cstep cs g0).length = cs.length + 1 := by
          simp only [cstep, List.length_append, List.length_cons, List.length_nil]
        have hidx : cs.length + (j + 1) = (cstep cs g0).length + j := by omega
        rw [hidx]
        exact ih (cstep cs g0) j g hj
  have hin_cone_self : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
      C.gates[j]? = some g → u ∈ g.inputs → 14 ≤ u → u < 14 + j →
      PEqualNP.EdgeOwnership.InCone 14 C (u - 14) j := by
    intro j g u hj hu h14 hlt
    change u - 14 ∈ (C.gates.foldl cstep []).getD j []
    have hcg := hcone_gate C.gates [] j g hj
    simp only [List.length_nil, Nat.zero_add] at hcg
    rw [hcg, List.mem_flatMap]
    refine ⟨u, ?_, List.mem_cons_self⟩
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hu, h14, hlt⟩
  have hin_cone_trans : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (u k : ℕ),
      C.gates[j]? = some g → u ∈ g.inputs → 14 ≤ u → u < 14 + j →
      PEqualNP.EdgeOwnership.InCone 14 C k (u - 14) →
      PEqualNP.EdgeOwnership.InCone 14 C k j := by
    intro j g u k hj hu h14 hlt hk
    change k ∈ (C.gates.foldl cstep []).getD (u - 14) [] at hk
    change k ∈ (C.gates.foldl cstep []).getD j []
    have hcg := hcone_gate C.gates [] j g hj
    simp only [List.length_nil, Nat.zero_add] at hcg
    rw [hcg, List.mem_flatMap]
    refine ⟨u, ?_, List.mem_cons_of_mem _ hk⟩
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hu, h14, hlt⟩
  have hwire_in : ∀ (x : Fin 14 → Bool) (u : ℕ) (hu : u < 14),
      PEqualNP.CleanedNonEdge.wireVal 14 C u x = x ⟨u, hu⟩ := by
    intro x u hu
    change (C.gates.foldl step (List.ofFn x)).getD u false = x ⟨u, hu⟩
    have hlen : (List.ofFn x).length = 14 := List.length_ofFn
    have hlt : u < (List.ofFn x).length := by omega
    rw [hstep_lt C.gates (List.ofFn x) u hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  have hwire_gate : ∀ (x : Fin 14 → Bool) (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
      C.gates[j]? = some g → g.inputs = [a, b] → a < 14 + j → b < 14 + j →
      PEqualNP.CleanedNonEdge.wireVal 14 C (14 + j) x =
        g.op.eval [PEqualNP.CleanedNonEdge.wireVal 14 C a x,
                   PEqualNP.CleanedNonEdge.wireVal 14 C b x] := by
    intro x j g a b hj hinp ha hb
    change (C.gates.foldl step (List.ofFn x)).getD (14 + j) false = _
    have hlen : (List.ofFn x).length = 14 := List.length_ofFn
    have hg := hstep_gate C.gates (List.ofFn x) j g hj
    rw [hlen] at hg
    rw [hg, hinp]
    simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceIte]
    rfl
  have hand_ev : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) :=
    fun a b => by cases a <;> cases b <;> rfl
  have hor_ev : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) :=
    fun a b => by cases a <;> cases b <;> rfl
  have hj1_lt : j1 < C.gates.length := by
    by_contra hge
    have hlen : (C.gates.foldl step (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7))).length =
        14 + C.gates.length := by rw [hstep_len, List.length_ofFn]
    have hf : PEqualNP.EdgeOwnership.gateVal 14 C j1
        (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) = false := by
      change (C.gates.foldl step (List.ofFn _)).getD (14 + j1) false = false
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega : (C.gates.foldl step _).length ≤ 14 + j1)]
      rfl
    rw [hj1_07] at hf
    cases hf
  -- Any wire with no AND gate in its closed cone distributes over pointwise OR
  let hasAnd : ℕ → Prop := fun u =>
    14 ≤ u ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C (u - 14)).op =
          PEqualNP.CircuitLowerBounds.GateOp.and ∨
        ∃ k, PEqualNP.EdgeOwnership.InCone 14 C k (u - 14) ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
            PEqualNP.CircuitLowerBounds.GateOp.and)
  have hpure_or : ∀ u : ℕ, u < 14 + C.gates.length → ¬ hasAnd u →
      ∀ x y : Fin 14 → Bool,
        PEqualNP.CleanedNonEdge.wireVal 14 C u (fun i => x i || y i) =
          (PEqualNP.CleanedNonEdge.wireVal 14 C u x || PEqualNP.CleanedNonEdge.wireVal 14 C u y) := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro hu hno x y
      by_cases h14 : u < 14
      · rw [hwire_in _ u h14, hwire_in _ u h14, hwire_in _ u h14]
      · have hge14 : 14 ≤ u := Nat.le_of_not_lt h14
        let gidx := u - 14
        have hg_lt : gidx < C.gates.length := by omega
        have hug : u = 14 + gidx := by omega
        have hget : C.gates[gidx]? = some C.gates[gidx] := List.getElem?_eq_getElem hg_lt
        obtain ⟨hop, a, b, hinp, _, ha, hb⟩ := hwf gidx C.gates[gidx] hget
        have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C gidx = C.gates[gidx] := by
          change C.gates.getD gidx ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[gidx]
          simp [List.getD_eq_getElem?_getD, hget]
        have hor : C.gates[gidx].op = PEqualNP.CircuitLowerBounds.GateOp.or := by
          rcases hop with hand_op | hor_op
          · exfalso; exact hno ⟨hge14, Or.inl (by rw [hga]; exact hand_op)⟩
          · exact hor_op
        have hmem_a : a ∈ C.gates[gidx].inputs := by rw [hinp]; simp
        have hmem_b : b ∈ C.gates[gidx].inputs := by rw [hinp]; simp
        have hno_a : ¬ hasAnd a := by
          intro hha
          obtain ⟨ha14, ha_op | ⟨k, hk_cone, hk_op⟩⟩ := hha
          · exact hno ⟨hge14, Or.inr ⟨a - 14, hin_cone_self gidx C.gates[gidx] a hget hmem_a ha14 ha, ha_op⟩⟩
          · exact hno ⟨hge14, Or.inr ⟨k, hin_cone_trans gidx C.gates[gidx] a k hget hmem_a ha14 ha hk_cone, hk_op⟩⟩
        have hno_b : ¬ hasAnd b := by
          intro hhb
          obtain ⟨hb14, hb_op | ⟨k, hk_cone, hk_op⟩⟩ := hhb
          · exact hno ⟨hge14, Or.inr ⟨b - 14, hin_cone_self gidx C.gates[gidx] b hget hmem_b hb14 hb, hb_op⟩⟩
          · exact hno ⟨hge14, Or.inr ⟨k, hin_cone_trans gidx C.gates[gidx] b k hget hmem_b hb14 hb hk_cone, hk_op⟩⟩
        have iha := ih a (by omega) (by omega) hno_a x y
        have ihb := ih b (by omega) (by omega) hno_b x y
        rw [hug, hwire_gate _ gidx C.gates[gidx] a b hget hinp ha hb,
          hwire_gate _ gidx C.gates[gidx] a b hget hinp ha hb,
          hwire_gate _ gidx C.gates[gidx] a b hget hinp ha hb,
          hor, hor_ev, hor_ev, hor_ev, iha, ihb]
        exact (show ∀ p1 q1 p2 q2 : Bool,
          ((p1 || q1) || (p2 || q2)) = ((p1 || p2) || (q1 || q2)) by decide) _ _ _ _
  -- Apply to both operands of j1
  have hget1 : C.gates[j1]? = some C.gates[j1] := List.getElem?_eq_getElem hj1_lt
  obtain ⟨_, a1, b1, hinp1, _, ha1, hb1⟩ := hwf j1 C.gates[j1] hget1
  have hga1 : PEqualNP.MetaComplexity.NestedCover.gateAt C j1 = C.gates[j1] := by
    change C.gates.getD j1 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j1]
    simp [List.getD_eq_getElem?_getD, hget1]
  have hopnd0 : PEqualNP.TopForm.opnd C j1 0 = a1 := by
    change (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).inputs.getD 0 0 = a1
    rw [hga1, hinp1]; rfl
  have hopnd1 : PEqualNP.TopForm.opnd C j1 1 = b1 := by
    change (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).inputs.getD 1 0 = b1
    rw [hga1, hinp1]; rfl
  have hno_child : ∀ u : ℕ, u ∈ C.gates[j1].inputs → u < 14 + j1 → ¬ hasAnd u := by
    intro u hu_in hu_lt hhu
    obtain ⟨hu14, hu_op | ⟨k, hk_cone, hk_op⟩⟩ := hhu
    · exact hno_and_cone (u - 14) (by omega) j1 hj1_lt hu_op hj1_op
        (hin_cone_self j1 C.gates[j1] u hget1 hu_in hu14 hu_lt)
    · have hk_lt : k < C.gates.length := by
        by_contra hge
        have hno : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
            PEqualNP.CircuitLowerBounds.GateOp.or := by
          change (C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
            PEqualNP.CircuitLowerBounds.GateOp.or
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hge)]
        rw [hno] at hk_op
        cases hk_op
      exact hno_and_cone k hk_lt j1 hj1_lt hk_op hj1_op
        (hin_cone_trans j1 C.gates[j1] u k hget1 hu_in hu14 hu_lt hk_cone)
  have hno_a1 : ¬ hasAnd a1 := hno_child a1 (by rw [hinp1]; simp) ha1
  have hno_b1 : ¬ hasAnd b1 := hno_child b1 (by rw [hinp1]; simp) hb1
  have hpair_or : (fun i : Fin 14 =>
      PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0 i ||
      PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7 i) =
      PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 := by
    funext i
    change (decide (i = 0 ∨ i = 0) || decide (i = 7 ∨ i = 7)) = decide (i = 0 ∨ i = 7)
    by_cases h0 : i = 0 <;> by_cases h7 : i = 7 <;> simp [h0, h7]
  have hj1_07_eval : PEqualNP.CleanedNonEdge.wireVal 14 C a1
      (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) = true ∧
      PEqualNP.CleanedNonEdge.wireVal 14 C b1
      (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7) = true := by
    have hv := hj1_07
    change PEqualNP.CleanedNonEdge.wireVal 14 C (14 + j1) _ = true at hv
    rw [hwire_gate _ j1 C.gates[j1] a1 b1 hget1 hinp1 ha1 hb1] at hv
    have hop1 : C.gates[j1].op = PEqualNP.CircuitLowerBounds.GateOp.and := by rw [← hga1]; exact hj1_op
    rw [hop1, hand_ev, Bool.and_eq_true] at hv
    exact hv
  have ha1_00 : PEqualNP.CleanedNonEdge.wireVal 14 C a1
      (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0) = false := by
    rw [← hopnd0]; exact hj1_00 0
  have hb1_00 : PEqualNP.CleanedNonEdge.wireVal 14 C b1
      (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0) = false := by
    rw [← hopnd1]; exact hj1_00 1
  have ha1_77 : PEqualNP.CleanedNonEdge.wireVal 14 C a1
      (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7) = true := by
    have hd := hpure_or a1 (by omega) hno_a1
      (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0)
      (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7)
    rw [hpair_or, hj1_07_eval.1, ha1_00, Bool.false_or] at hd
    exact hd.symm
  have hb1_77 : PEqualNP.CleanedNonEdge.wireVal 14 C b1
      (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7) = true := by
    have hd := hpure_or b1 (by omega) hno_b1
      (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 0)
      (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7)
    rw [hpair_or, hj1_07_eval.2, hb1_00, Bool.false_or] at hd
    exact hd.symm
  have hj1_77 : PEqualNP.EdgeOwnership.gateVal 14 C j1
      (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7) = true := by
    change PEqualNP.CleanedNonEdge.wireVal 14 C (14 + j1) _ = true
    rw [hwire_gate _ j1 C.gates[j1] a1 b1 hget1 hinp1 ha1 hb1]
    have hop1 : C.gates[j1].op = PEqualNP.CircuitLowerBounds.GateOp.and := by rw [← hga1]; exact hj1_op
    rw [hop1, hand_ev, ha1_77, hb1_77]; rfl
  have hgraph_77 : PEqualNP.MetaComplexity.NestedCover.graphFun G2 ∅
      (PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7) = false := by
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨u, t, _, hu, _⟩ := (hgraph_iff _).mp ht
    change decide (Fin.castAdd 7 u = (7 : Fin 14) ∨ Fin.castAdd 7 u = (7 : Fin 14)) = true at hu
    rw [decide_eq_true_iff] at hu
    rcases hu with heq | heq <;>
    · have hv : u.val = 7 := by
        have := congrArg Fin.val heq
        simpa [Fin.val_castAdd] using this
      have hult := u.isLt
      omega
  have hj1_mem : j1 ∈ PEqualNP.TopForm.junk G2 C := by
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hj1_lt, hj1_op, hj1_lt, PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 7, hj1_77, hgraph_77⟩
  rw [hjunk] at hj1_mem
  exact Finset.notMem_empty j1 hj1_mem
