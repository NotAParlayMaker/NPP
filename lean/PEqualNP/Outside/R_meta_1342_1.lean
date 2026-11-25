import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1342_1
    (compile_40bit :
      ∀ (B : List (Bool × ℕ × ℕ)) (T : List (ℕ × ℕ)),
        let cols : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
        let W := B.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]) cols
        T ≠ [] →
        (∀ j : ℕ, j < B.length → (B.getD j (false, 0, 0)).2.1 < 11 + j ∧ (B.getD j (false, 0, 0)).2.2 < 11 + j) →
        (∀ e : ℕ × ℕ, e ∈ T → e.1 < 11 + B.length ∧ e.2 < 11 + B.length) →
        T.foldl (fun (acc : ℕ) (e : ℕ × ℕ) => acc ||| (W.getD e.1 0 &&& W.getD e.2 0)) 0 = 65535 →
        ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C ∧
          C.size + 1 = B.length + 2 * T.length ∧
          ∀ k : Fin 40, C.eval (cols.map fun z => z.testBit k.val) = (65535 : ℕ).testBit k.val)
    (shard1_search :
      ∃ (B : List (Bool × ℕ × ℕ)) (T : List (ℕ × ℕ)),
        let cols : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
        let W := B.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]) cols
        T ≠ [] ∧
        B.length + 2 * T.length ≤ 22 ∧
        (∀ j : ℕ, j < B.length → (B.getD j (false, 0, 0)).2.1 < 11 + j ∧ (B.getD j (false, 0, 0)).2.2 < 11 + j) ∧
        (∀ e : ℕ × ℕ, e ∈ T → e.1 < 11 + B.length ∧ e.2 < 11 + B.length) ∧
        3 ≤ (List.range B.length).countP (fun j : ℕ => (B.getD j (false, 0, 0)).1 && decide (W.getD (11 + j) 0 &&& 1099511562240 ≠ 0) && decide (W.getD (11 + j) 0 &&& 65535 ≠ 0)) ∧
        (∀ j : ℕ, j < B.length → W.getD (11 + j) 0 &&& 65535 ≠ 0 ∧ W.getD (11 + j) 0 &&& 1099511562240 ≠ 0) ∧
        (∀ e : ℕ × ℕ, e ∈ T → (W.getD e.1 0 &&& W.getD e.2 0) &&& 1099511562240 = 0 ∧ (W.getD e.1 0 &&& W.getD e.2 0) &&& 65535 ≠ 0) ∧
        T.foldl (fun (acc : ℕ) (e : ℕ × ℕ) => acc ||| (W.getD e.1 0 &&& W.getD e.2 0)) 0 = 65535) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  let cols : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let E : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let row (r : ℕ) (i : Fin 11) : Bool := r.testBit i.val
  let edge (x : Fin 11 → Bool) : Bool :=
    E.any fun e => x (Fin.ofNat 11 e.1) && x (Fin.ofNat 11 e.2)
  let leRow (x y : Fin 11 → Bool) : Bool :=
    (List.finRange 11).all (fun i => !x i || y i)
  have leRow_imp (x y : Fin 11 → Bool) (h : leRow x y = true) :
      ∀ i : Fin 11, x i = true → y i = true := by
    intro i hxi
    have hi := List.all_eq_true.mp h i (List.mem_finRange i)
    simpa [hxi] using hi
  have cover : ∀ x : Fin 11 → Bool,
      ((List.finRange 16).any (fun k => leRow (row (P.getD k.val 0)) x) = edge x) ∧
      ((List.finRange 24).any (fun k => leRow x (row (Q.getD k.val 0))) = !edge x) := by
    decide +kernel
  have cols_P : ∀ k : Fin 16,
      cols.map (fun z => z.testBit k.val) = List.ofFn (row (P.getD k.val 0)) := by
    decide +kernel
  have cols_Q : ∀ k : Fin 24,
      cols.map (fun z => z.testBit (16 + k.val)) = List.ofFn (row (Q.getD k.val 0)) := by
    decide +kernel
  have mask_P : ∀ k : Fin 16, (65535 : ℕ).testBit k.val = true := by decide +kernel
  have mask_Q : ∀ k : Fin 24, (65535 : ℕ).testBit (16 + k.val) = false := by decide +kernel
  have edge_spec (x : Fin 11 → Bool) :
      edge x = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true := by
    dsimp only [edge]
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · intro z
      rcases z with ⟨e, hab, ha, hb⟩
      have bounds : ∀ p ∈ E, p.1 < 11 ∧ p.2 < 11 := by decide
      have hbd := bounds e hab
      refine ⟨Fin.ofNat 11 e.1, Fin.ofNat 11 e.2, ?_, ha, hb⟩
      change (e.1 % 11, e.2 % 11) ∈ E
      rw [Nat.mod_eq_of_lt hbd.1, Nat.mod_eq_of_lt hbd.2]
      exact hab
    · intro z
      rcases z with ⟨u, v, hm, hu, hv⟩
      refine ⟨(u.val, v.val), hm, ?_, ?_⟩
      · convert hu using 2
        exact Fin.ext (Nat.mod_eq_of_lt u.isLt)
      · convert hv using 2
        exact Fin.ext (Nat.mod_eq_of_lt v.isLt)
  obtain ⟨B, T, hTne, hbud, hBread, hTread, _, _, _, hcov⟩ := shard1_search
  obtain ⟨C, hmonoC, hszC, heval40⟩ := compile_40bit B T hTne hBread hTread hcov
  have hCmono : ∀ x y : Fin 11 → Bool, (∀ i : Fin 11, x i = true → y i = true) →
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    intro x y hle hx
    let step : List Bool → Gate → List Bool := fun w g =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have op_mono : ∀ {op : GateOp} {l1 l2 : List Bool},
        (op = GateOp.and ∨ op = GateOp.or) →
        l1.length = l2.length →
        (∀ i < l1.length, l1.getD i false = true → l2.getD i false = true) →
        op.eval l1 = true → op.eval l2 = true := by
      intro op l1 l2 hop hlen hli h1
      rcases hop with rfl | rfl
      · change l1.all id = true at h1
        change l2.all id = true
        simp only [List.all_eq_true, id_eq] at h1 ⊢
        intro b hb
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
        have hi1 : i < l1.length := hlen.symm ▸ hi
        have h1i : l1.getD i false = true := by
          rw [List.getD_eq_getElem _ _ hi1]
          exact h1 l1[i] (List.getElem_mem hi1)
        have h2i := hli i hi1 h1i
        rwa [List.getD_eq_getElem _ _ hi] at h2i
      · change l1.any id = true at h1
        change l2.any id = true
        simp only [List.any_eq_true, id_eq] at h1 ⊢
        obtain ⟨a, ha, rfl⟩ := h1
        obtain ⟨i, hi1, hia⟩ := List.getElem_of_mem ha
        have hi2 : i < l2.length := hlen ▸ hi1
        have h1i : l1.getD i false = true := by
          rw [List.getD_eq_getElem _ _ hi1]; exact hia
        have h2i := hli i hi1 h1i
        rw [List.getD_eq_getElem _ _ hi2] at h2i
        exact ⟨l2[i], List.getElem_mem hi2, h2i⟩
    have fold_mono : ∀ (gs : List Gate) (w1 w2 : List Bool),
        (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        w1.length = w2.length →
        (∀ i, w1.getD i false = true → w2.getD i false = true) →
        ∀ i, (gs.foldl step w1).getD i false = true → (gs.foldl step w2).getD i false = true := by
      intro gs
      induction gs with
      | nil =>
        intro w1 w2 _ _ hle_w i hi
        exact hle_w i hi
      | cons g rest ih =>
        intro w1 w2 hgs hlen_w hle_w
        have hg := hgs g (List.mem_cons_self ..)
        have hrest : ∀ g' ∈ rest, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
          fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
        have hstep_len : (step w1 g).length = (step w2 g).length := by
          simp [step, hlen_w]
        have hstep_le : ∀ i, (step w1 g).getD i false = true → (step w2 g).getD i false = true := by
          intro i hi
          by_cases hilt : i < w1.length
          · have hi2 : i < w2.length := hlen_w ▸ hilt
            have hg1 : (step w1 g).getD i false = w1.getD i false := by
              simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
            have hg2 : (step w2 g).getD i false = w2.getD i false := by
              simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi2]
            rw [hg1] at hi
            rw [hg2]
            exact hle_w i hi
          · by_cases hieq : i = w1.length
            · have hieq2 : i = w2.length := hlen_w ▸ hieq
              have hg1 : (step w1 g).getD i false = g.op.eval (g.inputs.map fun k => w1.getD k false) := by
                simp [step, List.getD_eq_getElem?_getD, hieq]
              have hg2 : (step w2 g).getD i false = g.op.eval (g.inputs.map fun k => w2.getD k false) := by
                simp [step, List.getD_eq_getElem?_getD, hieq2]
              rw [hg1] at hi
              rw [hg2]
              refine op_mono hg (by simp) ?_ hi
              intro j hj hji
              simp only [List.length_map] at hj
              simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hji ⊢
              rw [List.getElem?_eq_getElem hj] at hji ⊢
              simp only [Option.map_some, Option.getD_some] at hji ⊢
              exact hle_w _ hji
            · have hge1 : w1.length + 1 ≤ i := by omega
              have hg1 : (step w1 g).getD i false = false := by
                have hlen1 : (step w1 g).length ≤ i := by simp [step]; omega
                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen1]
              rw [hg1] at hi
              cases hi
        exact ih (step w1 g) (step w2 g) hrest hstep_len hstep_le
    have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have hm := hmonoC g hg
      exact hm.1
    have hinit_le : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
      intro i hi
      by_cases hilt : i < 11
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hilt, ↓reduceDIte,
          Option.getD_some] at hi ⊢
        exact hle ⟨i, hilt⟩ hi
      · have hlenx : (List.ofFn x).length ≤ i := by simp; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlenx] at hi
        simp at hi
    exact fold_mono C.gates (List.ofFn x) (List.ofFn y) hgs (by simp) hinit_le C.output hx
  refine ⟨C, hmonoC, ?_, by omega⟩
  intro x
  rw [← edge_spec]
  constructor
  · intro hx
    by_cases he : edge x = true
    · exact he
    · have he0 : edge x = false := Bool.eq_false_of_not_eq_true he
      have nq : (List.finRange 24).any (fun k => leRow x (row (Q.getD k.val 0))) = true := by
        rw [(cover x).2, he0]; rfl
      obtain ⟨k, _, hle⟩ := List.any_eq_true.mp nq
      have hneg : C.eval (List.ofFn (row (Q.getD k.val 0))) = false := by
        rw [← cols_Q k, heval40 ⟨16 + k.val, by omega⟩, mask_Q k]
      have hpos : C.eval (List.ofFn (row (Q.getD k.val 0))) = true :=
        hCmono x (row (Q.getD k.val 0)) (leRow_imp _ _ hle) hx
      rw [hneg] at hpos
      cases hpos
  · intro hx
    have np : (List.finRange 16).any (fun k => leRow (row (P.getD k.val 0)) x) = true :=
      (cover x).1.trans hx
    obtain ⟨k, _, hle⟩ := List.any_eq_true.mp np
    have hpos : C.eval (List.ofFn (row (P.getD k.val 0))) = true := by
      rw [← cols_P k, heval40 ⟨k.val, by omega⟩, mask_P k]
    exact hCmono (row (P.getD k.val 0)) x (leRow_imp _ _ hle) hpos
