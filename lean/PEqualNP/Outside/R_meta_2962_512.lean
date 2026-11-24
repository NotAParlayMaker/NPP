import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

/-- Reduction of L-meta-2962:
    Internally proves every maximal core is an AND gate, vertex-cover transfer, and the entire
    pairwise-disjoint-cones case (including `M = ∅` and `|M| = 1`) from `single_core_bound`.
    Splits the remaining overlapping-cones case into all-live vs has-dead maximal cores. -/
theorem PEqualNP.Outside.R_meta_2962_512
    (single_core_bound :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : Circuit) (s : Fin n → Bool),
        (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
        NoFourCycle G →
        IsAO2 n C →
        circuitFun n C = graphFun G ∅ →
        IsLiftFixedPoint G C →
        ∀ c ∈ maximalCores G C,
          (gateAt C c).op = GateOp.and →
          ∃ S : Finset (Fin n),
            (∀ e ∈ gammaE G C c, ∃ v ∈ S, v ∈ e) ∧
            (gammaE G C c).card + S.card ≤ (coneSet n C c).card + 1)
    (shared_cones_live :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
        (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
        NoFourCycle G →
        IsAO2 n C →
        circuitFun n C = graphFun G ∅ →
        IsLiftFixedPoint G C →
        IsMinCover G T →
        IsMinCover (G.deleteEdges (((maximalCores G C).biUnion (gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
        (∀ c ∈ maximalCores G C, (gateAt C c).op = GateOp.and) →
        (∃ c₁ ∈ maximalCores G C, ∃ c₂ ∈ maximalCores G C,
          c₁ ≠ c₂ ∧ (coneSet n C c₁ ∩ coneSet n C c₂).Nonempty) →
        (∀ c ∈ maximalCores G C, InOutputCone n C c) →
        ((maximalCores G C).biUnion (gammaE G C)).card + T.card ≤
          ((maximalCores G C).biUnion (coneSet n C)).card + (maximalCores G C).card + T'.card)
    (shared_cones_has_dead :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
        (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
        NoFourCycle G →
        IsAO2 n C →
        circuitFun n C = graphFun G ∅ →
        IsLiftFixedPoint G C →
        IsMinCover G T →
        IsMinCover (G.deleteEdges (((maximalCores G C).biUnion (gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
        (∀ c ∈ maximalCores G C, (gateAt C c).op = GateOp.and) →
        (∃ c₁ ∈ maximalCores G C, ∃ c₂ ∈ maximalCores G C,
          c₁ ≠ c₂ ∧ (coneSet n C c₁ ∩ coneSet n C c₂).Nonempty) →
        (∃ c ∈ maximalCores G C, ¬ InOutputCone n C c) →
        ((maximalCores G C).biUnion (gammaE G C)).card + T.card ≤
          ((maximalCores G C).biUnion (coneSet n C)).card + (maximalCores G C).card + T'.card) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover
        (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card +
          (PEqualNP.Core.maximalCores G C).card + T'.card := by
  intro n G _ C s T T' hbip hno4 hao2 hfun hlift hminT hminT'
  rcases hao2 with ⟨hao, hrb, hlen2⟩
  let wireStep : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]
  have hfold_len : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl wireStep ws).length = ws.length + gs.length := by
    intro gs; induction gs with
    | nil => intro ws; simp
    | cons g r ih =>
      intro ws; simp only [List.foldl_cons, List.length_cons]
      rw [ih]; simp [wireStep]; omega
  have hfold_prev : ∀ (gs : List Gate) (ws : List Bool) (w : ℕ),
      w < ws.length → (gs.foldl wireStep ws).getD w false = ws.getD w false := by
    intro gs; induction gs with
    | nil => intro ws w _; rfl
    | cons g r ih =>
      intro ws w hw
      simp only [List.foldl_cons]
      rw [ih (wireStep ws g) w (by simp [wireStep]; omega)]
      dsimp only [wireStep]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw, ← List.getD_eq_getElem?_getD]
  have hwval_allTrue : ∀ w < n + C.gates.length, wval (n := n) C (fun _ : Fin n => true) w = true := by
    have hfold_true : ∀ (gs : List Gate) (ws : List Bool),
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
        (∀ (k : ℕ) (hk : k < gs.length), ∀ i ∈ (gs[k]).inputs, i < ws.length + k) →
        (∀ w < ws.length, ws.getD w false = true) →
        ∀ w < ws.length + gs.length, (gs.foldl wireStep ws).getD w false = true := by
      intro gs; induction gs with
      | nil => intro ws _ _ hws w hw; exact hws w (by simpa using hw)
      | cons g r ih =>
        intro ws hgs hrb_g hws w hw
        simp only [List.foldl_cons]
        have hg_prop := hgs g (by simp)
        have hg_rb : ∀ i ∈ g.inputs, i < ws.length := by
          intro i hi; simpa using hrb_g 0 (by simp) i hi
        have hg_eval : g.op.eval (g.inputs.map (fun i => ws.getD i false)) = true := by
          rcases List.length_eq_two.mp hg_prop.2 with ⟨a, b, hab⟩
          rw [hab] at hg_rb ⊢
          have ha : ws.getD a false = true := hws a (hg_rb a (by simp))
          have hb : ws.getD b false = true := hws b (hg_rb b (by simp))
          simp only [List.map_cons, List.map_nil, ha, hb]
          rcases hg_prop.1 with hop | hop <;> simp [hop, GateOp.eval]
        have hws' : ∀ u < (wireStep ws g).length, (wireStep ws g).getD u false = true := by
          intro u hu
          dsimp only [wireStep] at hu ⊢
          simp only [List.length_append, List.length_singleton] at hu
          by_cases hlt : u < ws.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
            exact hws u hlt
          · have heq : u = ws.length := by omega
            rw [heq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            exact hg_eval
        apply ih (wireStep ws g) (fun g' hg' => hgs g' (by simp [hg']))
        · intro k hk i hi
          have := hrb_g (k + 1) (by simp; omega) i (by simpa using hi)
          simp only [wireStep, List.length_append, List.length_singleton]; omega
        · exact hws'
        · simp only [wireStep, List.length_append, List.length_singleton]
          simp only [List.length_cons] at hw; omega
    intro w hw
    unfold wval Circuit.wires
    have hinit_true : ∀ u < (List.ofFn (fun _ : Fin n => true)).length,
        (List.ofFn (fun _ : Fin n => true)).getD u false = true := by
      intro u hu
      simp only [List.length_ofFn] at hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hu])]
      simp
    apply hfold_true C.gates (List.ofFn (fun _ : Fin n => true))
    · intro g hg; exact ⟨hao g hg, hlen2 g hg⟩
    · intro k hk i hi
      simp only [List.length_ofFn]
      have hrbk := hrb k hk i
      have hget : gateAt C k = C.gates[k] := by
        unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
      rw [← hget] at hi
      exact hrbk hi
    · exact hinit_true
    · simp only [List.length_ofFn]; exact hw
  have hgate_eval : ∀ (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool),
      gateVal n C j x =
        (gateAt C j).op.eval ((gateAt C j).inputs.map (fun i => wval C x i)) := by
    intro j hj x
    unfold gateVal wval Circuit.wires
    have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop j C.gates]
      congr 1
      rw [List.drop_eq_getElem_cons hj]
    have hgat : gateAt C j = C.gates[j] := by
      unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [hgat]
    let ws0 := List.ofFn x
    let wsj := (C.gates.take j).foldl wireStep ws0
    have hwsj_len : wsj.length = n + j := by
      dsimp only [wsj, ws0]; rw [hfold_len]; simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hfull : C.gates.foldl wireStep ws0 =
        (C.gates.drop (j + 1)).foldl wireStep (wireStep wsj C.gates[j]) := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    change (C.gates.foldl wireStep ws0).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map (fun i => (C.gates.foldl wireStep ws0).getD i false))
    rw [hfull]
    have hlhs : ((C.gates.drop (j + 1)).foldl wireStep (wireStep wsj C.gates[j])).getD (n + j) false =
        (C.gates[j]).op.eval ((C.gates[j]).inputs.map (fun i => wsj.getD i false)) := by
      rw [hfold_prev _ _ (n + j) (by simp [wireStep, hwsj_len])]
      dsimp only [wireStep]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hwsj_len]
      simp
    rw [hlhs]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < n + j := by
      have hrbj := hrb j hj i
      rw [← hgat] at hi
      exact hrbj hi
    symm
    rw [hfold_prev _ _ i (by simp [wireStep, hwsj_len]; omega)]
    dsimp only [wireStep]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  have hcore_and : ∀ c ∈ maximalCores G C, (gateAt C c).op = GateOp.and := by
    intro c hc
    have hc' : c < C.gates.length ∧ IsMaximalCore G C c := by
      unfold maximalCores gatesWhere at hc
      rw [Finset.mem_filter, Finset.mem_range] at hc
      exact hc
    rcases hc'.2.1 with ⟨hc_lt, ⟨hbelow, _⟩, hnotboth, _⟩
    have hc_mem : gateAt C c ∈ C.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc_lt]
      exact List.getElem_mem hc_lt
    rcases hao (gateAt C c) hc_mem with hand | hor
    · exact hand
    · exfalso
      have hlen_c : (gateAt C c).inputs.length = 2 := hlen2 (gateAt C c) hc_mem
      rcases List.length_eq_two.mp hlen_c with ⟨w0, w1, hw01⟩
      have hop0 : opnd C c 0 = w0 := by simp [opnd, hw01]
      have hop1 : opnd C c 1 = w1 := by simp [opnd, hw01]
      have hw0_lt : w0 < n + c := hrb c hc_lt w0 (by simp [hw01])
      have hw1_lt : w1 < n + c := hrb c hc_lt w1 (by simp [hw01])
      have hbelow_wire : ∀ w, (w = w0 ∨ w = w1) →
          ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
        intro w hw x hwx
        apply hbelow x
        rw [hgate_eval c hc_lt x, hor, hw01]
        rcases hw with rfl | rfl <;> simp [GateOp.eval, hwx]
      have hge_n : ∀ w, (w = w0 ∨ w = w1) → n ≤ w := by
        intro w hw
        by_contra hlt
        push Not at hlt
        let i : Fin n := ⟨w, hlt⟩
        let x : Fin n → Bool := fun k => decide (k = i)
        have hwx : wval C x w = true := by
          unfold wval Circuit.wires
          change (C.gates.foldl wireStep (List.ofFn x)).getD w false = true
          rw [hfold_prev _ _ w (by simp [hlt])]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlt])]
          simp [x, i]
        have hgf := hbelow_wire w hw x hwx
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
          Bool.false_or, decide_eq_true_eq] at hgf
        rcases hgf with ⟨u, v, huv, hu, hv⟩
        have hu' : u = i := by simpa [x] using hu
        have hv' : v = i := by simpa [x] using hv
        subst hu'; subst hv'
        exact G.ne_of_adj huv rfl
      have himp_wire : ∀ w, (w = w0 ∨ w = w1) → w < n + c → IsImpOperand G C w := by
        intro w hw hwlt
        have hwn := hge_n w hw
        refine ⟨hwn, ?_, ?_⟩
        · intro x hx
          apply hbelow_wire w hw x
          unfold gateVal at hx
          unfold wval
          rwa [Nat.add_sub_cancel' hwn] at hx
        · refine ⟨fun _ => true, ?_⟩
          unfold gateVal
          rw [Nat.add_sub_cancel' hwn]
          exact hwval_allTrue w (by omega)
      apply hnotboth
      rw [hop0, hop1]
      exact ⟨himp_wire w0 (Or.inl rfl) hw0_lt, himp_wire w1 (Or.inr rfl) hw1_lt⟩
  let M := maximalCores G C
  let D := M.biUnion (gammaE G C)
  let U := M.biUnion (coneSet n C)
  have hcover_transfer : ∀ S : Finset (Fin n),
      (∀ e ∈ D, ∃ v ∈ S, v ∈ e) → T.card ≤ T'.card + S.card := by
    intro S hS
    have hvc : G.IsVertexCover ((T' ∪ S : Finset (Fin n)) : Set (Fin n)) := by
      intro u v huv
      by_cases heD : s(u, v) ∈ D
      · rcases hS s(u, v) heD with ⟨w, hwS, hwe⟩
        rw [Sym2.mem_iff] at hwe
        rcases hwe with rfl | rfl
        · exact Or.inl (by simp [hwS])
        · exact Or.inr (by simp [hwS])
      · have huv' : (G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj u v := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨huv, heD⟩
        rcases hminT'.1 huv' with hu | hv
        · exact Or.inl (by simp [hu])
        · exact Or.inr (by simp [hv])
    have hle := hminT.2 (T' ∪ S) hvc
    have hunion : (T' ∪ S).card ≤ T'.card + S.card := Finset.card_union_le T' S
    omega
  by_cases hdisj : ∀ c₁ ∈ M, ∀ c₂ ∈ M, c₁ ≠ c₂ → Disjoint (coneSet n C c₁) (coneSet n C c₂)
  · have hsingle : ∀ c ∈ M,
        ∃ S : Finset (Fin n),
          (∀ e ∈ gammaE G C c, ∃ v ∈ S, v ∈ e) ∧
          (gammaE G C c).card + S.card ≤ (coneSet n C c).card + 1 := by
      intro c hc
      exact single_core_bound n G C s hbip hno4 ⟨hao, hrb, hlen2⟩ hfun hlift c hc (hcore_and c hc)
    let Sc : ℕ → Finset (Fin n) := fun c =>
      if hc : c ∈ M then Classical.choose (hsingle c hc) else ∅
    have hSc_cov : ∀ c ∈ M, ∀ e ∈ gammaE G C c, ∃ v ∈ Sc c, v ∈ e := by
      intro c hc
      simp only [Sc, hc, ↓reduceDIte]
      exact (Classical.choose_spec (hsingle c hc)).1
    have hSc_bound : ∀ c ∈ M, (gammaE G C c).card + (Sc c).card ≤ (coneSet n C c).card + 1 := by
      intro c hc
      simp only [Sc, hc, ↓reduceDIte]
      exact (Classical.choose_spec (hsingle c hc)).2
    let S := M.biUnion Sc
    have hS_cov : ∀ e ∈ D, ∃ v ∈ S, v ∈ e := by
      intro e he
      rcases Finset.mem_biUnion.mp he with ⟨c, hcM, hec⟩
      rcases hSc_cov c hcM e hec with ⟨v, hvSc, hve⟩
      exact ⟨v, Finset.mem_biUnion.mpr ⟨c, hcM, hvSc⟩, hve⟩
    have hT_le : T.card ≤ T'.card + S.card := hcover_transfer S hS_cov
    have hD_le : D.card ≤ ∑ c ∈ M, (gammaE G C c).card := Finset.card_biUnion_le
    have hS_le : S.card ≤ ∑ c ∈ M, (Sc c).card := Finset.card_biUnion_le
    have hU_eq : U.card = ∑ c ∈ M, (coneSet n C c).card :=
      Finset.card_biUnion (fun c₁ hc₁ c₂ hc₂ hne => hdisj c₁ hc₁ c₂ hc₂ hne)
    have hsum_le : ∑ c ∈ M, ((gammaE G C c).card + (Sc c).card) ≤
        ∑ c ∈ M, ((coneSet n C c).card + 1) :=
      Finset.sum_le_sum (fun c hc => hSc_bound c hc)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum_le
    change D.card + T.card ≤ U.card + M.card + T'.card
    omega
  · have hover : ∃ c₁ ∈ M, ∃ c₂ ∈ M, c₁ ≠ c₂ ∧ (coneSet n C c₁ ∩ coneSet n C c₂).Nonempty := by
      push Not at hdisj
      rcases hdisj with ⟨c₁, hc₁, c₂, hc₂, hne, hnd⟩
      rw [Finset.not_disjoint_iff] at hnd
      rcases hnd with ⟨g, hg₁, hg₂⟩
      exact ⟨c₁, hc₁, c₂, hc₂, hne, g, Finset.mem_inter.mpr ⟨hg₁, hg₂⟩⟩
    by_cases hlive : ∀ c ∈ M, InOutputCone n C c
    · exact shared_cones_live n G C s T T' hbip hno4 ⟨hao, hrb, hlen2⟩ hfun hlift hminT hminT'
        hcore_and hover hlive
    · push Not at hlive
      exact shared_cones_has_dead n G C s T T' hbip hno4 ⟨hao, hrb, hlen2⟩ hfun hlift hminT hminT'
        hcore_and hover hlive
