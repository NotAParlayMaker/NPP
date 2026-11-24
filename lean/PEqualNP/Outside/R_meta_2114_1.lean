import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2114_1
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∃ i j k : Fin C.gates.length,
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool =>
          x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      16 ≤ C.size)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      C.size ≤ 15 →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool =>
          x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      False)
    (h3 :
      let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      let r : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
        fun C v => {i : Fin C.size | (v : ℕ) ∈ (C.gates.get i).inputs}
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C →
        C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = f →
        (∀ i : Fin C.size,
          let g := C.gates.get i
          (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
          ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
           (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)),
          (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
          ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (r C 4).card = 2 →
        (∃ n0 : Fin C.size, ∀ i : Fin C.size,
          (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ i = n0) →
        False)
    (h4 :
      let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      let r : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
        fun C v => {i : Fin C.size | (v : ℕ) ∈ (C.gates.get i).inputs}
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C →
        C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = f →
        (∀ i : Fin C.size,
          let g := C.gates.get i
          (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
          ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
           (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)),
          (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
          ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (r C 4).card = 2 →
        (∃ n1 n2 : Fin C.size, n1 < n2 ∧ ∀ i : Fin C.size,
          (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ i = n1 ∨ i = n2) →
        False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))
    have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}
    have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧ x3.size ≤ (15 : ℕ) ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧ (∀ (x4 : Fin x3.size), have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4; (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧ ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or)
    ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x7 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x7).card = (2 : ℕ)) → False := by
  classical
  let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let r : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
    fun C v => {i : Fin C.size | (v : ℕ) ∈ (C.gates.get i).inputs}
  let rwW (σ : Fin 9 → Fin 9) (w : ℕ) : ℕ :=
    if h : w < 9 then (σ ⟨w, h⟩).val else w
  let mapG (σ : Fin 9 → Fin 9) (g : PEqualNP.CircuitLowerBounds.Gate) :
      PEqualNP.CircuitLowerBounds.Gate :=
    ⟨g.op, g.inputs.map (rwW σ)⟩
  let relabel (σ : Fin 9 → Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) :
      PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (mapG σ), rwW σ C.output⟩
  have rwW_inj (σ : Fin 9 → Fin 9) (hσ : Function.Injective σ) :
      Function.Injective (rwW σ) := by
    intro a b hab
    dsimp only [rwW] at hab
    by_cases ha : a < 9
    · rw [dif_pos ha] at hab
      by_cases hb : b < 9
      · rw [dif_pos hb] at hab
        have hfin : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := Fin.ext hab
        exact congrArg Fin.val (hσ hfin)
      · rw [dif_neg hb] at hab
        have hlt := (σ ⟨a, ha⟩).isLt
        omega
    · rw [dif_neg ha] at hab
      by_cases hb : b < 9
      · rw [dif_pos hb] at hab
        have hlt := (σ ⟨b, hb⟩).isLt
        omega
      · rw [dif_neg hb] at hab
        exact hab
  have rwW_lt (σ : Fin 9 → Fin 9) (w k : ℕ) :
      rwW σ w < 9 + k ↔ w < 9 + k := by
    dsimp only [rwW]
    by_cases hw : w < 9
    · rw [dif_pos hw]
      have hlt := (σ ⟨w, hw⟩).isLt
      omega
    · rw [dif_neg hw]
  let stepW (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have fold_sim (σ : Fin 9 → Fin 9) (gs : List PEqualNP.CircuitLowerBounds.Gate) :
      ∀ (w1 w2 : List Bool),
        w1.length = w2.length → 9 ≤ w1.length →
        (∀ u : ℕ, w1.getD (rwW σ u) false = w2.getD u false) →
        ∀ u : ℕ,
          ((gs.map (mapG σ)).foldl stepW w1).getD (rwW σ u) false =
          (gs.foldl stepW w2).getD u false := by
    induction gs with
    | nil =>
      intro w1 w2 _ _ hsim u
      exact hsim u
    | cons g gs ih =>
      intro w1 w2 hlen h9 hsim u
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hinp : ((mapG σ g).inputs.map fun i => w1.getD i false) =
          (g.inputs.map fun v => w2.getD v false) := by
        dsimp only [mapG]
        rw [List.map_map]
        apply List.map_congr_left
        intro v _
        exact hsim v
      let b : Bool := g.op.eval (g.inputs.map fun v => w2.getD v false)
      have hs1 : stepW w1 (mapG σ g) = w1 ++ [b] := by
        dsimp only [stepW, mapG, b]
        rw [hinp]
      have hs2 : stepW w2 g = w2 ++ [b] := rfl
      rw [hs1, hs2]
      apply ih (w1 ++ [b]) (w2 ++ [b])
      · simp only [List.length_append, hlen]
      · simp only [List.length_append]
        omega
      · intro v
        by_cases hv : v < 9
        · have hrw : rwW σ v < w1.length := by
            dsimp only [rwW]
            rw [dif_pos hv]
            have hlt := (σ ⟨v, hv⟩).isLt
            omega
          have hv2 : v < w2.length := by omega
          rw [List.getD_append w1 [b] false (rwW σ v) hrw,
              List.getD_append w2 [b] false v hv2]
          exact hsim v
        · have hrw : rwW σ v = v := by
            dsimp only [rwW]
            exact dif_neg hv
          rw [hrw]
          by_cases hlt2 : v < w2.length
          · have hlt1 : v < w1.length := by omega
            rw [List.getD_append w1 [b] false v hlt1,
                List.getD_append w2 [b] false v hlt2]
            have hs := hsim v
            rwa [hrw] at hs
          · by_cases heq : v = w2.length
            · subst heq
              have h1 : (w1 ++ [b]).getD w2.length false = b := by
                rw [← hlen]
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
                  Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              have h2' : (w2 ++ [b]).getD w2.length false = b := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
                  Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              rw [h1, h2']
            · have hge1 : (w1 ++ [b]).length ≤ v := by
                simp only [List.length_append, List.length_singleton]
                omega
              have hge2 : (w2 ++ [b]).length ≤ v := by
                simp only [List.length_append, List.length_singleton]
                omega
              rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
  have eval_relabel (σ : Fin 9 → Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (y : Fin 9 → Bool) :
      (relabel σ C).eval (List.ofFn y) = C.eval (List.ofFn (y ∘ σ)) := by
    change ((C.gates.map (mapG σ)).foldl stepW (List.ofFn y)).getD (rwW σ C.output) false =
      (C.gates.foldl stepW (List.ofFn (y ∘ σ))).getD C.output false
    apply fold_sim σ C.gates (List.ofFn y) (List.ofFn (y ∘ σ))
    · simp only [List.length_ofFn]
    · simp only [List.length_ofFn, le_rfl]
    · intro u
      by_cases hu : u < 9
      · dsimp only [rwW]
        rw [dif_pos hu]
        have h1 : (List.ofFn y).getD (σ ⟨u, hu⟩).val false = y (σ ⟨u, hu⟩) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
            dif_pos (σ ⟨u, hu⟩).isLt, Option.getD_some, Fin.eta]
        have h2' : (List.ofFn (y ∘ σ)).getD u false = y (σ ⟨u, hu⟩) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
            dif_pos hu, Option.getD_some, Function.comp_apply]
        rw [h1, h2']
      · dsimp only [rwW]
        rw [dif_neg hu]
        have h1 : (List.ofFn y).length ≤ u := by
          simp only [List.length_ofFn]
          omega
        have h2' : (List.ofFn (y ∘ σ)).length ≤ u := by
          simp only [List.length_ofFn]
          omega
        rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2']
  have transport (σ : Fin 9 → Fin 9)
      (hσ : Function.Injective σ)
      (hfσ : ∀ y : Fin 9 → Bool, f (y ∘ σ) = f y)
      (hset : ∀ u ∈ ([4, 6, 7] : List (Fin 9)), ∃ v ∈ ([4, 6, 7] : List (Fin 9)), σ v = u)
      (C : PEqualNP.CircuitLowerBounds.Circuit)
      (hmin : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
      (hsz : C.size ≤ 15)
      (hfun : PEqualNP.MetaComplexity.circuitFun 9 C = f)
      (hcln : ∀ i : Fin C.size,
        let g := C.gates.get i
        (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
         (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)))
      (h467 : ∀ v ∈ ([4, 6, 7] : List (Fin 9)),
        (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
        ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (v0 : Fin 9) (hv0 : (r C v0).card = 2) (hσv0 : σ v0 = 4) :
      let C' := relabel σ C
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C' ∧
      C'.size ≤ 15 ∧
      PEqualNP.MetaComplexity.circuitFun 9 C' = f ∧
      (∀ i : Fin C'.size,
        let g := C'.gates.get i
        (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
         (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))) ∧
      (∀ u ∈ ([4, 6, 7] : List (Fin 9)),
        (r C' u).Nonempty ∧ (r C' u).card ≤ 2 ∧
        ∀ i ∈ r C' u, (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (r C' 4).card = 2 := by
    let C' := relabel σ C
    have hlen : C'.size = C.size := by
      change (C.gates.map (mapG σ)).length = C.gates.length
      exact List.length_map (mapG σ)
    have hfun' : PEqualNP.MetaComplexity.circuitFun 9 C' = f := by
      funext y
      change C'.eval (List.ofFn y) = f y
      rw [eval_relabel σ C y]
      have hc : C.eval (List.ofFn (y ∘ σ)) = f (y ∘ σ) := congrFun hfun (y ∘ σ)
      exact hc.trans (hfσ y)
    have hmin_pair : PEqualNP.MetaComplexity.FanInTwo C ∧
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D →
          PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.MetaComplexity.circuitFun 9 C →
          C.size ≤ D.size := hmin
    have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := by
      change ∀ g' ∈ C'.gates,
        g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
          PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
        g'.inputs.length ≤ 2
      intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      have hfg : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
          PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
          g.inputs.length ≤ 2 := hmin_pair.1 g hg
      dsimp only [mapG]
      rw [List.length_map]
      exact hfg
    have hmin' : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C' := by
      refine ⟨hfan', ?_⟩
      intro D hD hDfun
      rw [hlen]
      exact hmin_pair.2 D hD (hDfun.trans (hfun'.trans hfun.symm))
    let toOrig (j : Fin C'.size) : Fin C.size :=
      ⟨j.val, by have hlt := j.isLt; omega⟩
    let toRel (i : Fin C.size) : Fin C'.size :=
      ⟨i.val, by have hlt := i.isLt; omega⟩
    have hget (j : Fin C'.size) :
        C'.gates.get j = mapG σ (C.gates.get (toOrig j)) := by
      have hj1 : j.val < (C.gates.map (mapG σ)).length := j.isLt
      have hj2 : j.val < C.gates.length := (toOrig j).isLt
      change (C.gates.map (mapG σ))[j.val]'hj1 = mapG σ (C.gates[j.val]'hj2)
      exact List.getElem_map (mapG σ)
    have hcln' : ∀ j : Fin C'.size,
        let g := C'.gates.get j
        (∀ w ∈ g.inputs, w < 9 + (j : ℕ)) ∧ g.inputs.Nodup ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
         (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) := by
      intro j
      dsimp only
      rw [hget j]
      have hi := hcln (toOrig j)
      dsimp only at hi
      dsimp only [mapG]
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
        exact (rwW_lt σ u j.val).mpr (hi.1 u hu)
      · exact hi.2.1.map (rwW_inj σ hσ)
      · rw [List.length_map]
        exact hi.2.2
    have hrcard (v : Fin 9) : (r C' (σ v)).card = (r C v).card := by
      symm
      refine Finset.card_bij (fun (i : Fin C.size) _ => toRel i) ?_ ?_ ?_
      · intro i hi
        simp only [r, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        change (σ v : ℕ) ∈ (C'.gates.get (toRel i)).inputs
        rw [hget (toRel i)]
        have heq_i : toOrig (toRel i) = i := Fin.ext rfl
        rw [heq_i]
        dsimp only [mapG]
        refine List.mem_map.mpr ⟨(v : ℕ), hi, ?_⟩
        dsimp only [rwW]
        rw [dif_pos v.isLt]
      · intro i1 _ i2 _ heq
        exact Fin.ext (Fin.mk.inj heq)
      · intro j hj
        refine ⟨toOrig j, ?_, Fin.ext rfl⟩
        simp only [r, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        rw [hget j] at hj
        dsimp only [mapG] at hj
        obtain ⟨w, hw, hrw⟩ := List.mem_map.mp hj
        have hv_rw : rwW σ (v : ℕ) = (σ v : ℕ) := by
          dsimp only [rwW]
          rw [dif_pos v.isLt]
        have hweq : w = (v : ℕ) := rwW_inj σ hσ (hrw.trans hv_rw.symm)
        rwa [← hweq]
    have h467' : ∀ u ∈ ([4, 6, 7] : List (Fin 9)),
        (r C' u).Nonempty ∧ (r C' u).card ≤ 2 ∧
        ∀ j ∈ r C' u, (C'.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := hset u hu
      have hv_info := h467 v hv
      have hc := hrcard v
      refine ⟨Finset.card_pos.mp (by rw [hc]; exact Finset.card_pos.mpr hv_info.1),
        by rw [hc]; exact hv_info.2.1, ?_⟩
      intro j hj
      simp only [r, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [hget j] at hj ⊢
      dsimp only [mapG] at hj ⊢
      obtain ⟨w, hw, hrw⟩ := List.mem_map.mp hj
      have hv_rw : rwW σ (v : ℕ) = (σ v : ℕ) := by
        dsimp only [rwW]
        rw [dif_pos v.isLt]
      have hweq : w = (v : ℕ) := rwW_inj σ hσ (hrw.trans hv_rw.symm)
      have hi_mem : toOrig j ∈ r C v := by
        simp only [r, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [← hweq]
      exact hv_info.2.2 (toOrig j) hi_mem
    have hr4 : (r C' 4).card = 2 := by
      rw [← hσv0, hrcard v0, hv0]
    exact ⟨hmin', by rw [hlen]; exact hsz, hfun', hcln', h467', hr4⟩
  intro _ _ _ C hP hor htwo
  have hmin : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C := hP.1
  have hsz : C.size ≤ 15 := hP.2.1
  have hfun : PEqualNP.MetaComplexity.circuitFun 9 C = f := hP.2.2.1
  have hcln := hP.2.2.2.1
  have h467 : ∀ v ∈ ([4, 6, 7] : List (Fin 9)),
      (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
      ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro v hv
    exact ⟨(hP.2.2.2.2 v hv).1, (hP.2.2.2.2 v hv).2.1, hor v hv⟩
  have hexC' : ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C' ∧
      C'.size ≤ 15 ∧
      PEqualNP.MetaComplexity.circuitFun 9 C' = f ∧
      (∀ i : Fin C'.size,
        let g := C'.gates.get i
        (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
         (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))) ∧
      (∀ u ∈ ([4, 6, 7] : List (Fin 9)),
        (r C' u).Nonempty ∧ (r C' u).card ≤ 2 ∧
        ∀ i ∈ r C' u, (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (r C' 4).card = 2 := by
    obtain ⟨v0, hv0_mem, hv0_card⟩ := htwo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv0_mem
    rcases hv0_mem with rfl | rfl | rfl
    · exact ⟨C, hmin, hsz, hfun, hcln, h467, hv0_card⟩
    · let π2 : Fin 9 → Fin 9 := ![2, 3, 8, 5, 7, 1, 4, 6, 0]
      have hπ2_inj : Function.Injective π2 := by decide
      have hπ2_f : ∀ y : Fin 9 → Bool, f (y ∘ π2) = f y := by decide +kernel
      have hπ2_set : ∀ u ∈ ([4, 6, 7] : List (Fin 9)),
          ∃ v ∈ ([4, 6, 7] : List (Fin 9)), π2 v = u := by decide
      exact ⟨relabel π2 C,
        transport π2 hπ2_inj hπ2_f hπ2_set C hmin hsz hfun hcln h467 6 hv0_card rfl⟩
    · let π1 : Fin 9 → Fin 9 := ![1, 2, 3, 8, 6, 0, 7, 4, 5]
      have hπ1_inj : Function.Injective π1 := by decide
      have hπ1_f : ∀ y : Fin 9 → Bool, f (y ∘ π1) = f y := by decide +kernel
      have hπ1_set : ∀ u ∈ ([4, 6, 7] : List (Fin 9)),
          ∃ v ∈ ([4, 6, 7] : List (Fin 9)), π1 v = u := by decide
      exact ⟨relabel π1 C,
        transport π1 hπ1_inj hπ1_f hπ1_set C hmin hsz hfun hcln h467 7 hv0_card rfl⟩
  obtain ⟨C', hmin', hsz', hfun', hcln', h467', hr4'⟩ := hexC'
  let N : Finset (Fin C'.size) :=
    Finset.univ.filter (fun i : Fin C'.size =>
      (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not)
  by_cases hN3 : 3 ≤ N.card
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
    let N1 := N.erase i
    have hc1 : N1.card = N.card - 1 := Finset.card_erase_of_mem hi
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < N1.card)
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hjN : j ∈ N := (Finset.mem_erase.mp hj).2
    let N2 := N1.erase j
    have hc2 : N2.card = N1.card - 1 := Finset.card_erase_of_mem hj
    obtain ⟨k, hk⟩ := Finset.card_pos.mp (by omega : 0 < N2.card)
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hkN1 : k ∈ N1 := (Finset.mem_erase.mp hk).2
    have hki : k ≠ i := (Finset.mem_erase.mp hkN1).1
    have hkN : k ∈ N := (Finset.mem_erase.mp hkN1).2
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hi hjN hkN
    have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := hmin'.1
    have hge16 : 16 ≤ C'.size :=
      h1 C' hfan' ⟨i, j, k, hji.symm, hki.symm, hkj.symm, hi, hjN, hkN⟩ hfun'
    omega
  · have hNle2 : N.card = 0 ∨ N.card = 1 ∨ N.card = 2 := by omega
    rcases hNle2 with hN0 | hN1 | hN2
    · have hNemp : N = ∅ := Finset.card_eq_zero.mp hN0
      have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := hmin'.1
      have hmono : PEqualNP.MetaComplexity.Monotone2 C' := by
        change ∀ g ∈ C'.gates,
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
           g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2
        intro g hg
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
        have hfg : (C'.gates.get i).op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
            PEqualNP.CircuitLowerBounds.GateOp.or,
            PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
            (C'.gates.get i).inputs.length ≤ 2 := hfan' (C'.gates.get i) hg
        have hnot : (C'.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
          intro heq
          let i' : Fin C'.size := i
          have hmem : i' ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ i', heq⟩
          rw [hNemp] at hmem
          exact Finset.notMem_empty i' hmem
        have hop : (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not := hfg.1
        rcases hop with ha | hb | hc
        · exact ⟨Or.inl ha, hfg.2⟩
        · exact ⟨Or.inr hb, hfg.2⟩
        · exact absurd hc hnot
      exact h2 C' hmono hsz' hfun'
    · obtain ⟨n0, hn0⟩ := Finset.card_eq_one.mp hN1
      refine h3 C' hmin' hsz' hfun' hcln' h467' hr4' ⟨n0, ?_⟩
      intro i
      have hm : (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ i ∈ N := by
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hm, hn0, Finset.mem_singleton]
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
      let N1 := N.erase a
      have hc1 : N1.card = 1 := by
        rw [Finset.card_erase_of_mem ha, hN2]
      obtain ⟨b, hb1⟩ := Finset.card_eq_one.mp hc1
      have hba_mem : b ∈ N1 := by rw [hb1]; exact Finset.mem_singleton_self b
      have hba : b ≠ a := (Finset.mem_erase.mp hba_mem).1
      have hiff : ∀ i : Fin C'.size,
          (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ i = a ∨ i = b := by
        intro i
        have hm : (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ i ∈ N := by
          simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hm]
        by_cases hia : i = a
        · subst hia
          exact ⟨fun _ => Or.inl rfl, fun _ => ha⟩
        · constructor
          · intro hiN
            have hiN1 : i ∈ N1 := Finset.mem_erase.mpr ⟨hia, hiN⟩
            rw [hb1, Finset.mem_singleton] at hiN1
            exact Or.inr hiN1
          · rintro (rfl | rfl)
            · exact absurd rfl hia
            · exact (Finset.mem_erase.mp hba_mem).2
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exact h4 C' hmin' hsz' hfun' hcln' h467' hr4' ⟨a, b, hlt, hiff⟩
      · exact absurd heq.symm hba
      · refine h4 C' hmin' hsz' hfun' hcln' h467' hr4' ⟨b, a, hgt, ?_⟩
        intro i
        rw [hiff i, or_comm]
