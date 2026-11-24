import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_4213_aux

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

theorem drun_single (g : Gate) (x : List Bool) :
    drun [g] x = x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)] :=
  rfl

theorem drun_append (A B : List Gate) (x : List Bool) : drun (A ++ B) x = drun B (drun A x) := by
  simp [drun, List.foldl_append]

theorem drun_length (gs : List Gate) (x : List Bool) :
    (drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [drun]
  | cons g gs ih => rw [drun_cons, ih]; simp; omega

theorem drun_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (drun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [drun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

theorem drun_at (gs : List Gate) (x : List Bool) (j w : ℕ) (g : Gate) (hg : gs[j]? = some g)
    (hw : w = x.length + j) (hback : ∀ i ∈ g.inputs, i < w) :
    (drun gs x).getD w false = g.op.eval (g.inputs.map fun i => (drun gs x).getD i false) := by
  have hj : j < gs.length := by
    rcases Nat.lt_or_ge j gs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hg
      exact absurd hg (by simp)
  have hgj : gs[j] = g := by
    rw [List.getElem?_eq_getElem hj] at hg
    exact Option.some.inj hg
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
  have htl : (drun (gs.take j) x).length = x.length + j := by
    rw [drun_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have e1 : drun gs x = drun (gs.drop (j + 1)) (drun [g] (drun (gs.take j) x)) := by
    conv_lhs => rw [hsplit]
    rw [show gs.take j ++ gs[j] :: gs.drop (j + 1) = gs.take j ++ ([gs[j]] ++ gs.drop (j + 1)) from rfl,
      drun_append, drun_append, hgj]
  have hlen1 : w < (drun [g] (drun (gs.take j) x)).length := by
    rw [drun_single, List.length_append, htl, List.length_singleton]
    omega
  have hpre : ∀ i, i < w → (drun gs x).getD i false = (drun (gs.take j) x).getD i false := by
    intro i hi
    rw [e1, drun_getD _ _ _ (Nat.lt_trans hi hlen1), drun_single,
      List.getD_append _ _ _ _ (by rw [htl]; omega)]
  have hval : (drun gs x).getD w false =
      g.op.eval (g.inputs.map fun i => (drun (gs.take j) x).getD i false) := by
    rw [e1, drun_getD _ _ _ hlen1, drun_single, List.getD_append_right _ _ _ _ (by rw [htl]; omega),
      htl, hw, Nat.sub_self, List.getD_cons_zero]
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hpre i (hback i hi)).symm

def V (C : Circuit) (w : ℕ) (a b : Fin 14) : Bool :=
  PEqualNP.CleanedNonEdge.wireVal 14 C w (PEqualNP.EdgeOwnership.pairInput a b)

def X3 (C : Circuit) (w x4 : ℕ) : Prop :=
  ((14 : ℕ) + x4 = w ∨ PEqualNP.EdgeOwnership.InCone 14 C x4 (w - 14)) ∧
    (gateAt C x4).op = GateOp.and ∧ V C (14 + x4) 0 0 = false ∧ V C (14 + x4) 7 7 = false ∧
    ∃ x5 : Fin 2, V C (PEqualNP.TopForm.opnd C x4 x5) 0 0 = true ∧
      V C (PEqualNP.TopForm.opnd C x4 (1 - x5)) 7 7 = true

theorem gate_val (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (c d : ℕ)
    (hin : (gateAt C j).inputs = [c, d]) (hc : c < 14 + j) (hd : d < 14 + j) (x : Fin 14 → Bool) :
    PEqualNP.CleanedNonEdge.wireVal 14 C (14 + j) x =
      (gateAt C j).op.eval [PEqualNP.CleanedNonEdge.wireVal 14 C c x, PEqualNP.CleanedNonEdge.wireVal 14 C d x] := by
  have hga : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hg : C.gates[j]? = some (gateAt C j) := by rw [hga]; exact List.getElem?_eq_getElem hj
  have h := drun_at C.gates (List.ofFn x) j (14 + j) (gateAt C j) hg (by simp)
    (by rw [hin]; intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> assumption)
  show (drun C.gates (List.ofFn x)).getD (14 + j) false = _
  rw [h, hin]
  rfl

theorem input_val (C : Circuit) (w : ℕ) (hw : w < 14) (x : Fin 14 → Bool) :
    PEqualNP.CleanedNonEdge.wireVal 14 C w x = x ⟨w, hw⟩ := by
  show (drun C.gates (List.ofFn x)).getD w false = _
  rw [drun_getD _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]

theorem beyond_val (C : Circuit) (w : ℕ) (hw : 14 + C.gates.length ≤ w) (x : Fin 14 → Bool) :
    PEqualNP.CleanedNonEdge.wireVal 14 C w x = false := by
  show (drun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by rw [drun_length]; simpa using hw)

theorem not_input (C : Circuit) (w : ℕ) (hw : w < 14) (h1 : V C w 0 7 = true) (h2 : V C w 0 0 = false)
    (h3 : V C w 7 7 = false) : False := by
  unfold V at h1 h2 h3
  rw [input_val C w hw] at h1 h2 h3
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq, decide_eq_false_iff_not, or_self] at h1 h2 h3
  rcases h1 with h | h
  · exact h2 h
  · exact h3 h

def cfold (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs

theorem cfold_cons (g : Gate) (gs : List Gate) (cs : List (List ℕ)) :
    cfold (g :: gs) cs = cfold gs (PEqualNP.EdgeOwnership.coneStep 14 cs g) := rfl

theorem cfold_append (A B : List Gate) (cs : List (List ℕ)) : cfold (A ++ B) cs = cfold B (cfold A cs) := by
  simp [cfold, List.foldl_append]

theorem cfold_length (gs : List Gate) (cs : List (List ℕ)) : (cfold gs cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp [cfold]
  | cons g gs ih => rw [cfold_cons, ih]; simp [PEqualNP.EdgeOwnership.coneStep]; omega

theorem cfold_getD (gs : List Gate) (cs : List (List ℕ)) (i : ℕ) (hi : i < cs.length) :
    (cfold gs cs).getD i [] = cs.getD i [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    rw [cfold_cons, ih _ (by simp [PEqualNP.EdgeOwnership.coneStep]; omega)]
    simp only [PEqualNP.EdgeOwnership.coneStep]
    exact List.getD_append _ _ _ _ hi

theorem cfold_at (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (cfold gs []).getD j [] = (gs[j].inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + j))).flatMap
      (fun w => (w - 14) :: (cfold (gs.take j) []).getD (w - 14) []) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
  have htl : (cfold (gs.take j) []).length = j := by
    rw [cfold_length, List.length_take]
    simp only [List.length_nil, Nat.zero_add]
    omega
  have e1 : cfold gs [] = cfold (gs.drop (j + 1)) (PEqualNP.EdgeOwnership.coneStep 14 (cfold (gs.take j) []) gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [cfold_append, cfold_cons]
  rw [e1, cfold_getD _ _ _ (by simp [PEqualNP.EdgeOwnership.coneStep, htl])]
  simp only [PEqualNP.EdgeOwnership.coneStep]
  rw [List.getD_append_right _ _ _ _ (le_of_eq htl), htl, Nat.sub_self, List.getD_cons_zero]

theorem cone_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (u : ℕ) (hu : u ∈ (gateAt C j).inputs)
    (hu14 : 14 ≤ u) (huj : u < 14 + j) :
    PEqualNP.EdgeOwnership.InCone 14 C (u - 14) j ∧
      ∀ i, PEqualNP.EdgeOwnership.InCone 14 C i (u - 14) → PEqualNP.EdgeOwnership.InCone 14 C i j := by
  have hga : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hcone : (PEqualNP.EdgeOwnership.cones 14 C).getD j [] =
      (C.gates[j].inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + j))).flatMap
        (fun w => (w - 14) :: (cfold (C.gates.take j) []).getD (w - 14) []) := cfold_at C.gates j hj
  have hpre : (cfold (C.gates.take j) []).getD (u - 14) [] = (PEqualNP.EdgeOwnership.cones 14 C).getD (u - 14) [] := by
    have e : PEqualNP.EdgeOwnership.cones 14 C = cfold (C.gates.drop j) (cfold (C.gates.take j) []) := by
      show cfold C.gates [] = _
      rw [← cfold_append, List.take_append_drop]
    rw [e, cfold_getD (C.gates.drop j) (cfold (C.gates.take j) []) (u - 14)
      (by rw [cfold_length, List.length_take]; simp only [List.length_nil, Nat.zero_add]; omega)]
  have hmemf : u ∈ C.gates[j].inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + j)) := by
    rw [List.mem_filter]
    exact ⟨by rw [← hga]; exact hu, by simp only [decide_eq_true_eq]; omega⟩
  constructor
  · show (u - 14) ∈ (PEqualNP.EdgeOwnership.cones 14 C).getD j []
    rw [hcone, List.mem_flatMap]
    exact ⟨u, hmemf, List.mem_cons.2 (Or.inl rfl)⟩
  · intro i hi
    show i ∈ (PEqualNP.EdgeOwnership.cones 14 C).getD j []
    rw [hcone, List.mem_flatMap]
    refine ⟨u, hmemf, List.mem_cons.2 (Or.inr ?_)⟩
    rw [hpre]
    exact hi

theorem gate_shape (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 14 C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ c d : ℕ, (gateAt C j).inputs = [c, d] ∧ c < 14 + j ∧ d < 14 + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  obtain ⟨hao, hrb, hlen⟩ := hC
  have hga : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hmem : gateAt C j ∈ C.gates := by rw [hga]; exact List.getElem_mem hj
  have h2 := hlen _ hmem
  rcases hl : (gateAt C j).inputs with _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩
  · rw [hl] at h2; simp at h2
  · rw [hl] at h2; simp at h2
  · exact ⟨c, d, rfl, hrb j hj c (by rw [hl]; simp), hrb j hj d (by rw [hl]; simp), hao _ hmem⟩
  · rw [hl] at h2; simp at h2

theorem main_ind (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 14 C) : ∀ w : ℕ,
    V C w 0 7 = true → V C w 0 0 = false → V C w 7 7 = false → ∃ x10 : ℕ, X3 C w x10 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro h1 h2 h3
  by_cases hw14 : w < 14
  · exact absurd (not_input C w hw14 h1 h2 h3) id
  by_cases hwb : 14 + C.gates.length ≤ w
  · unfold V at h1
    rw [beyond_val C w hwb] at h1
    exact absurd h1 Bool.false_ne_true
  obtain ⟨j, rfl⟩ : ∃ j, w = 14 + j := ⟨w - 14, by omega⟩
  have hj : j < C.gates.length := by omega
  obtain ⟨c, d, hin, hc, hd, hop⟩ := gate_shape C hC j hj
  have hv : ∀ a b : Fin 14, V C (14 + j) a b = (gateAt C j).op.eval [V C c a b, V C d a b] := by
    intro a b
    unfold V
    exact gate_val C j hj c d hin hc hd _
  have lift : ∀ u, u ∈ (gateAt C j).inputs → u < 14 + j → V C u 0 7 = true → V C u 0 0 = false →
      V C u 7 7 = false → ∃ x10, X3 C (14 + j) x10 := by
    intro u hu huw g1 g2 g3
    have hu14 : 14 ≤ u := by
      by_contra hlt
      exact not_input C u (by omega) g1 g2 g3
    obtain ⟨x10, hx10⟩ := ih u huw g1 g2 g3
    refine ⟨x10, Or.inr ?_, hx10.2⟩
    rw [show 14 + j - 14 = j by omega]
    obtain ⟨ha, hb⟩ := cone_mem C j hj u hu hu14 huw
    rcases hx10.1 with he | hcone
    · rw [show x10 = u - 14 by omega]
      exact ha
    · exact hb x10 hcone
  have hcm : c ∈ (gateAt C j).inputs := by rw [hin]; simp
  have hdm : d ∈ (gateAt C j).inputs := by rw [hin]; simp
  have e07 := hv 0 7
  have e00 := hv 0 0
  have e77 := hv 7 7
  rcases hop with hop | hop
  · rw [hop] at e07 e00 e77
    simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] at e07 e00 e77
    rw [h1] at e07
    rw [h2] at e00
    rw [h3] at e77
    have k07 := e07.symm
    rw [Bool.and_eq_true] at k07
    obtain ⟨hc07, hd07⟩ := k07
    have hop0 : PEqualNP.TopForm.opnd C j 0 = c := by simp [PEqualNP.TopForm.opnd, hin]
    have hop1 : PEqualNP.TopForm.opnd C j 1 = d := by simp [PEqualNP.TopForm.opnd, hin]
    have wit : ∀ x5 : Fin 2, V C (PEqualNP.TopForm.opnd C j x5) 0 0 = true →
        V C (PEqualNP.TopForm.opnd C j (1 - x5)) 7 7 = true → ∃ x10, X3 C (14 + j) x10 := by
      intro x5 k1 k2
      exact ⟨j, Or.inl rfl, hop, h2, h3, x5, k1, k2⟩
    cases hc00 : V C c 0 0 <;> cases hd00 : V C d 0 0 <;> cases hc77 : V C c 7 7 <;>
      cases hd77 : V C d 7 7 <;> simp only [hc00, hd00, hc77, hd77, Bool.and_self, Bool.and_false,
        Bool.and_true] at e00 e77
    all_goals first
      | exact absurd e00 (by decide)
      | exact absurd e77 (by decide)
      | exact lift c hcm hc hc07 hc00 hc77
      | exact lift d hdm hd hd07 hd00 hd77
      | exact wit 0 (by rw [hop0]; exact hc00) (by rw [show (1 : Fin 2) - 0 = 1 from rfl, hop1]; exact hd77)
      | exact wit 1 (by rw [hop1]; exact hd00) (by rw [show (1 : Fin 2) - 1 = 0 from rfl, hop0]; exact hc77)
  · rw [hop] at e07 e00 e77
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] at e07 e00 e77
    rw [h1] at e07
    rw [h2] at e00
    rw [h3] at e77
    have k00 := e00.symm
    rw [Bool.or_eq_false_iff] at k00
    have k77 := e77.symm
    rw [Bool.or_eq_false_iff] at k77
    cases hc07 : V C c 0 7
    · have hd07 : V C d 0 7 = true := by
        rw [hc07, Bool.false_or] at e07
        exact e07.symm
      exact lift d hdm hd hd07 k00.2 k77.2
    · exact lift c hcm hc hc07 k00.1 k77.1

theorem final (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 14 C) (x5 : ℕ)
    (hand : (gateAt C x5).op = GateOp.and) (h07 : V C (14 + x5) 0 7 = true)
    (hops : ∀ x8 : Fin 2, V C (PEqualNP.TopForm.opnd C x5 x8) 0 0 = false ∧
      V C (PEqualNP.TopForm.opnd C x5 x8) 7 7 = false) (x9 : Fin 2) :
    ∃ x10 : ℕ, X3 C (PEqualNP.TopForm.opnd C x5 x9) x10 := by
  have hx5 : x5 < C.gates.length := by
    by_contra h
    have e : gateAt C x5 = ⟨GateOp.or, []⟩ := List.getD_eq_default _ _ (by omega)
    rw [e] at hand
    cases hand
  obtain ⟨c, d, hin, hc, hd, -⟩ := gate_shape C hC x5 hx5
  have hval := gate_val C x5 hx5 c d hin hc hd (PEqualNP.EdgeOwnership.pairInput 0 7)
  have h07' : PEqualNP.CleanedNonEdge.wireVal 14 C (14 + x5) (PEqualNP.EdgeOwnership.pairInput 0 7) = true := h07
  rw [hval, hand] at h07'
  simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true] at h07'
  obtain ⟨hc07, hd07⟩ := h07'
  have hval_op : ∀ i : Fin 2, V C (PEqualNP.TopForm.opnd C x5 i) 0 7 = true := by
    intro i
    match i with
    | ⟨0, _⟩ =>
      show V C ((gateAt C x5).inputs.getD 0 0) 0 7 = true
      rw [hin]
      exact hc07
    | ⟨1, _⟩ =>
      show V C ((gateAt C x5).inputs.getD 1 0) 0 7 = true
      rw [hin]
      exact hd07
  exact main_ind C hC _ (hval_op x9) (hops x9).1 (hops x9).2

end PEqualNP.Outside.L_meta_4213_aux

theorem PEqualNP.Outside.L_meta_4213 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → ∀ (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((14 : ℕ) + x5) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x8 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x5 x8) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x5 x8) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → ∀ (x9 : Fin (2 : ℕ)), ∃ (x10 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x5 x9) x10 := by
  intro C
  dsimp only
  intro hC x5 hand h07 hops x9
  exact PEqualNP.Outside.L_meta_4213_aux.final C hC x5 hand h07 hops x9
