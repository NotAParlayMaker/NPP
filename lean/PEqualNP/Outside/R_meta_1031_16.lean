import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves PEqualNP.TopForm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_1031_16
    (twoColor : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G → ((∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v)) →
      ∃ C : Circuit, (Monotone2 C ∧ C.eval (List.ofFn (fun _ : Fin n => false)) = false ∧
        (∀ u v : Fin n, C.eval (List.ofFn (pairInput u v)) = decide (G.Adj u v)) ∧
        (∀ j < C.gates.length, (gateAt C j).op = .and →
          gateVal n C j (fun _ => false) = false ∧
          ∀ u v : Fin n, ¬ G.Adj u v → gateVal n C j (pairInput u v) = false)) ∧
        ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (other : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G → (¬ (∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v)) →
      ∃ C : Circuit, (Monotone2 C ∧ C.eval (List.ofFn (fun _ : Fin n => false)) = false ∧
        (∀ u v : Fin n, C.eval (List.ofFn (pairInput u v)) = decide (G.Adj u v)) ∧
        (∀ j < C.gates.length, (gateAt C j).op = .and →
          gateVal n C j (fun _ => false) = false ∧
          ∀ u v : Fin n, ¬ G.Adj u v → gateVal n C j (pairInput u v) = false)) ∧
        ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  classical
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have sample_getD_app_lt : ∀ (w t : List Bool) (i : ℕ), i < w.length →
      (w ++ t).getD i false = w.getD i false := by
    intro w t i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_app_self : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  have sample_getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g0 gs ih =>
      intro w i hi
      rw [List.foldl_cons]
      have hlt : i < (stepW w g0).length := by
        change i < (w ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (stepW w g0) i hlt]
      exact sample_getD_app_lt w _ i hi
  have foldl_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl stepW w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; simp at h
    | cons g0 gs ih =>
      intro w j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : w.length < (stepW w g0).length := by
          change w.length < (w ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [foldl_getD_lt gs (stepW w g0) w.length hlt]
        change (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]).getD w.length false = _
        rw [getD_app_self w _]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · have hilt : i < (stepW w g0).length := by
            change i < (w ++ [_]).length
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          simp only [hi, ↓reduceIte, foldl_getD_lt gs (stepW w g0) i hilt]
          exact (sample_getD_app_lt w _ i hi).symm
        · simp only [hi, ↓reduceIte]
          exact sample_getD_ge w i (Nat.le_of_not_lt hi)
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen : (stepW w g0).length + j' = w.length + (j' + 1) := by
          change (w ++ [_]).length + j' = w.length + (j' + 1)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (stepW w g0) j' g hj
  have wires_gate (n : ℕ) (C : Circuit) : ∀ (x : Fin n → Bool) (j : ℕ) (g : Gate),
      C.gates[j]? = some g →
      (C.wires (List.ofFn x)).getD (n + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
    intro x j g hj
    have h := foldl_gate C.gates (List.ofFn x) j g hj
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    rw [hlen] at h
    exact h
  have wires_inp (n : ℕ) (C : Circuit) : ∀ (x : Fin n → Bool) (w : ℕ) (hw : w < n),
      (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro x w hw
    have h := foldl_getD_lt C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw)
    change (C.gates.foldl stepW (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]
  have cone_getD_lt (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
      (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
    intro gs
    induction gs with
    | nil => intro cs j _; rfl
    | cons g0 gs ih =>
      intro cs j hj
      rw [List.foldl_cons]
      have hlt : j < (coneStep n cs g0).length := by
        change j < (cs ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (coneStep n cs g0) j hlt]
      change (cs ++ [_]).getD j [] = cs.getD j []
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have cone_gate (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ) (h : Gate),
      gs[k]? = some h →
      (gs.foldl (coneStep n) cs).getD (cs.length + k) [] =
        (h.inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + k)))).flatMap
          (fun w => (w - n) :: (gs.foldl (coneStep n) cs).getD (w - n) []) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; simp at h
    | cons g0 gs ih =>
      intro cs k h hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : cs.length < (coneStep n cs g0).length := by
          change cs.length < (cs ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [cone_getD_lt n gs (coneStep n cs g0) cs.length hlt]
        have hself : (coneStep n cs g0).getD cs.length [] =
            (g0.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) []) := by
          change (cs ++ [_]).getD cs.length [] = _
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl cs.length)]
          simp
        rw [hself]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwlt : w - n < cs.length := by omega
        have hwlt2 : w - n < (coneStep n cs g0).length := by
          change w - n < (cs ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [cone_getD_lt n gs (coneStep n cs g0) (w - n) hwlt2]
        change (w - n) :: cs.getD (w - n) [] = (w - n) :: (cs ++ [_]).getD (w - n) []
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        have hlen : (coneStep n cs g0).length + k' = cs.length + (k' + 1) := by
          change (cs ++ [_]).length + k' = cs.length + (k' + 1)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (coneStep n cs g0) k' h hk
  have inCone_iff_rec (n : ℕ) (C : Circuit) : ∀ (k : ℕ) (h : Gate) (i : ℕ), C.gates[k]? = some h →
      (InCone n C i k ↔ ∃ w ∈ h.inputs, n ≤ w ∧ w < n + k ∧ (i = w - n ∨ InCone n C i (w - n))) := by
    intro k h i hk
    change i ∈ (C.gates.foldl (coneStep n) []).getD k [] ↔ _
    have hcg := cone_gate n C.gates [] k h hk
    simp only [List.length_nil, Nat.zero_add] at hcg
    rw [hcg, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hi⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      simp only [List.mem_cons] at hi
      exact ⟨w, hw.1, hw.2.1, hw.2.2, hi⟩
    · rintro ⟨w, hwin, hle, hlt, hi⟩
      refine ⟨w, ?_, ?_⟩
      · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hwin, hle, hlt⟩
      · rw [List.mem_cons]; exact hi

  have wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
      (C.wires (List.ofFn x)).length = n + C.gates.length := by
    have hfold (gs : List Gate) : ∀ w, (gs.foldl stepW w).length = w.length + gs.length := by
      induction gs with
      | nil => intro; simp
      | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp only [stepW,List.length_append,List.length_cons,List.length_nil]
        omega
    change (C.gates.foldl stepW (List.ofFn x)).length = _
    rw [hfold, List.length_ofFn]

  have gate_read (C : Circuit) (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
      gateAt C j = g := by
    change C.gates.getD j ⟨.or,[]⟩ = g
    rw [List.getD_eq_getElem?_getD,h]
    rfl

  have and_inputs (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hg : C.gates[j]? = some g) (hop : g.op = .and) :
      gateVal n C j x = true ↔
        ∀ w ∈ g.inputs, w < n+j ∧ (C.wires (List.ofFn x)).getD w false = true := by
    unfold gateVal
    rw [wires_gate n C _ _ _ hg, hop]
    change (g.inputs.map _).all id = true ↔ _
    simp only [List.all_eq_true,List.mem_map]
    constructor
    · intro h k hk
      by_cases e : k < n+j
      · exact ⟨e, by simpa only [e, ↓reduceIte,id_eq] using h _ ⟨k,hk,rfl⟩⟩
      · have bad := h _ ⟨k,hk,rfl⟩
        simp [e] at bad
    · rintro h _ ⟨k, hk, rfl⟩
      rcases h k hk with ⟨e,he⟩
      simpa only [e, ↓reduceIte,id_eq] using he

  have or_inputs (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hg : C.gates[j]? = some g) (hop : g.op = .or) :
      gateVal n C j x = true ↔
        ∃ w ∈ g.inputs, w < n+j ∧ (C.wires (List.ofFn x)).getD w false = true := by
    unfold gateVal
    rw [wires_gate n C _ _ _ hg, hop]
    change (g.inputs.map _).any id = true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨_, h, hp⟩
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
      by_cases e : k < n+j
      · exact ⟨k,hk,e,by simpa only [e, ↓reduceIte,id_eq] using hp⟩
      · simp [e] at hp
    · rintro ⟨k,hk,e,he⟩
      refine ⟨_,List.mem_map.mpr ⟨k,hk,rfl⟩,?_⟩
      simpa only [e, ↓reduceIte,id_eq] using he

  let noNest (n : ℕ) (C : Circuit) : Prop :=
    ∀ j k, (gateAt C j).op = .and → (gateAt C k).op = .and → ¬ InCone n C j k

  have first_reader (n : ℕ) (C : Circuit) (h t : ℕ)
      (ht : t < C.gates.length) (hc : InCone n C h t) :
      ∃ r ≤ t, h < r ∧ ∃ rg, C.gates[r]? = some rg ∧ n+h ∈ rg.inputs := by
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      let g := C.gates[t]
      have hg : C.gates[t]? = some g := List.getElem?_eq_getElem ht
      obtain ⟨w,hw,wn,wt,route⟩ := (inCone_iff_rec n C t g h hg).mp hc
      rcases route with eq | prior
      · refine ⟨t, le_rfl, by omega, g, hg, ?_⟩
        rwa [show n+h=w by omega]
      · have tlt : w - n < t := by omega
        obtain ⟨r,rt,hr,rg,he,read⟩ := ih (w-n) tlt (tlt.trans ht) prior
        exact ⟨r,rt.trans tlt.le,hr,rg,he,read⟩

  have active_bound (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
      (ht : (C.wires (List.ofFn x)).getD w false = true) : w < n + C.gates.length := by
    by_contra! he
    have hge : (C.wires (List.ofFn x)).length ≤ w := by rwa [wires_len n C x]
    rw [List.getD_eq_default _ _ hge] at ht
    contradiction

  have wire_mono (n : ℕ) (C : Circuit) (mono : Monotone2 C) (x y : Fin n → Bool)
      (inc : ∀ a, x a = true → y a = true) :
      ∀ w, (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ht
      by_cases hw : w < n
      · rw [wires_inp n C y w hw]
        apply inc
        simpa only [wires_inp n C x w hw] using ht
      · have bound := active_bound n C x w ht
        let j := w-n
        have jlt : j < C.gates.length := by dsimp [j]; omega
        have row : w = n+j := by dsimp [j]; omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem jlt
        have mem : g ∈ C.gates := List.getElem_mem jlt
        rw [row] at ht ⊢
        change gateVal n C j x = true at ht
        change gateVal n C j y = true
        rcases (mono g mem).1 with e | e
        · apply (and_inputs n C y j g hg e).mpr
          intro a ha
          obtain ⟨early,hit⟩ := (and_inputs n C x j g hg e).mp ht a ha
          exact ⟨early,ih a (row ▸ early) hit⟩
        · obtain ⟨a,ha,early,hit⟩ := (or_inputs n C x j g hg e).mp ht
          exact (or_inputs n C y j g hg e).mpr ⟨a,ha,early,ih a (row ▸ early) hit⟩

  have or_witness (n : ℕ) (C : Circuit) (mono : Monotone2 C) (x : Fin n → Bool) :
      ∀ w, (∀ j, w = n+j → (gateAt C j).op ≠ .and ∧
        ∀ i, InCone n C i j → (gateAt C i).op ≠ .and) →
        (C.wires (List.ofFn x)).getD w false = true →
        ∃ a : Fin n, x a = true ∧ ∀ y : Fin n → Bool, y a = true →
          (C.wires (List.ofFn y)).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ors active
      by_cases raw : w < n
      · refine ⟨⟨w,raw⟩,(wires_inp n C x w raw).symm ▸ active,?_⟩
        intro y hy
        rwa [wires_inp n C y w raw]
      · have bound := active_bound n C x w active
        let j := w-n
        have hj : j < C.gates.length := by dsimp [j]; omega
        have row : w = n+j := by dsimp [j]; omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
        have mem : g ∈ C.gates := List.getElem_mem hj
        have gnot : g.op ≠ .and := by simpa only [gate_read C j g hg] using (ors j row).1
        have hop := ((mono g mem).1).resolve_left gnot
        have hit : gateVal n C j x = true := by unfold gateVal; rwa [← row]
        obtain ⟨k,hk,klt,hkHit⟩ := (or_inputs n C x j g hg hop).mp hit
        have below : ∀ j', k = n+j' → (gateAt C j').op ≠ .and ∧
            ∀ i, InCone n C i j' → (gateAt C i).op ≠ .and := by
          intro j' eq
          have nk : n ≤ k := by omega
          have diff : k-n=j' := by omega
          refine ⟨(ors j row).2 _ ((inCone_iff_rec n C j g j' hg).mpr
            ⟨k,hk,nk,klt,Or.inl diff.symm⟩),?_⟩
          intro i hi
          exact (ors j row).2 _ ((inCone_iff_rec n C j g i hg).mpr
            ⟨k,hk,nk,klt,Or.inr (diff ▸ hi)⟩)
        obtain ⟨a,ha,path⟩ := ih k (row ▸ klt) below hkHit
        refine ⟨a,ha,?_⟩
        intro y yes
        rw [row]
        exact (or_inputs n C y j g hg hop).mpr ⟨k,hk,klt,path y yes⟩




  have and_parent_witness (n : ℕ) (C : Circuit) (mono : Monotone2 C) (flat : noNest n C)
      (x : Fin n → Bool) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (hop : g.op = .and)
      (w : ℕ) (hw : w ∈ g.inputs) (hit : gateVal n C j x = true) :
      ∃ a : Fin n, x a = true ∧ ∀ y : Fin n → Bool, y a = true →
        (C.wires (List.ofFn y)).getD w false = true := by
    obtain ⟨early,active⟩ := (and_inputs n C x j g hg hop).mp hit w hw
    have hj : (gateAt C j).op = .and := (congrArg Gate.op (gate_read C j g hg)).trans hop
    apply or_witness n C mono x w _ active
    intro k eq
    have wn : n ≤ w := by omega
    have eq' : w-n = k := by omega
    constructor
    · intro han
      exact flat k j han hj ((inCone_iff_rec n C j g k hg).mpr
        ⟨w,hw,wn,early,Or.inl eq'.symm⟩)
    · intro i path han
      exact flat i j han hj ((inCone_iff_rec n C j g i hg).mpr
        ⟨w,hw,wn,early,Or.inr (eq' ▸ path)⟩)

  have small_hit (n : ℕ) (C : Circuit) (mono : Monotone2 C) (flat : noNest n C)
      (x : Fin n → Bool) :
      ∀ w, (C.wires (List.ofFn x)).getD w false = true →
        ∃ L : List (Fin n), L.length ≤ 2 ∧ (∀ a ∈ L, x a = true) ∧
          ∀ y : Fin n → Bool, (∀ a ∈ L, y a = true) →
            (C.wires (List.ofFn y)).getD w false = true := by
    classical
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hit
      by_cases raw : w < n
      · refine ⟨[⟨w,raw⟩],by simp,?_,?_⟩
        · intro a ha
          rw [List.mem_singleton.mp ha]
          rwa [wires_inp n C x w raw] at hit
        · intro y yes
          rw [wires_inp n C y w raw]
          exact yes _ (by simp)
      · have bound := active_bound n C x w hit
        let j := w-n
        have hj : j < C.gates.length := by dsimp [j]; omega
        have row : w = n+j := by dsimp [j]; omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
        have mem : g ∈ C.gates := List.getElem_mem hj
        have ht : gateVal n C j x = true := by unfold gateVal; rwa [← row]
        rcases (mono g mem).1 with had | hor
        · let opts (a : {k // k ∈ g.inputs}) :=
            and_parent_witness n C mono flat x j g hg had a.val a.property ht
          let pick (a : {k // k ∈ g.inputs}) := Classical.choose (opts a)
          let L := g.inputs.attach.map pick
          refine ⟨L,by simpa [L] using (mono g mem).2,?_,?_⟩
          · intro p hp
            obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
            exact (Classical.choose_spec (opts v)).1
          · intro y yes
            rw [row]
            apply (and_inputs n C y j g hg had).mpr
            intro a ha
            let chosen : {k // k ∈ g.inputs} := ⟨a,ha⟩
            have selected : pick chosen ∈ L :=
              List.mem_map.mpr ⟨chosen, List.mem_attach _ _, rfl⟩
            exact ⟨((and_inputs n C x j g hg had).mp ht a ha).1,
              (Classical.choose_spec (opts chosen)).2 y (yes _ selected)⟩
        · obtain ⟨a,ha,early,ah⟩ := (or_inputs n C x j g hg hor).mp ht
          obtain ⟨L,cap,sel,lifts⟩ := ih a (row ▸ early) ah
          refine ⟨L,cap,sel,?_⟩
          intro y hy
          rw [row]
          exact (or_inputs n C y j g hg hor).mpr ⟨a,ha,early,lifts y hy⟩

  let sampleFit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
    Monotone2 C ∧ C.eval (List.ofFn (fun _ : Fin n => false)) = false ∧
      (∀ u v : Fin n, C.eval (List.ofFn (pairInput u v)) = decide (G.Adj u v)) ∧
      ∀ j < C.gates.length, (gateAt C j).op = .and →
        gateVal n C j (fun _ => false) = false ∧
        ∀ u v : Fin n, ¬ G.Adj u v → gateVal n C j (pairInput u v) = false

  have full_fit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (fit : sampleFit G C) (flat : noNest n C) :
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    constructor
    · intro yes
      obtain ⟨L, cap, pins, sufficient⟩ := small_hit n C fit.1 flat x C.output yes
      cases L with
      | nil =>
        have hit : C.eval (List.ofFn fun _ : Fin n => false) = true :=
          sufficient _ (by intro _ h; simp at h)
        rw [fit.2.1] at hit
        contradiction
      | cons a tail =>
        cases tail with
        | nil =>
          have hit : C.eval (List.ofFn (pairInput a a)) = true :=
            sufficient _ (by
              intro b bmem
              change decide (b = a ∨ b = a) = true
              rw [decide_eq_true_eq]
              exact Or.inl (List.mem_singleton.mp bmem))
          rw [fit.2.2.1 a a] at hit
          exact False.elim (G.ne_of_adj (of_decide_eq_true hit) rfl)
        | cons b tail =>
          have empty : tail = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_cons] at cap
            omega
          subst tail
          have hit : C.eval (List.ofFn (pairInput a b)) = true := sufficient _ (by
            intro i hi
            change decide (i = a ∨ i = b) = true
            rw [decide_eq_true_eq]
            simpa using hi)
          rw [fit.2.2.1 a b] at hit
          exact ⟨a,b,of_decide_eq_true hit,pins _ (by simp),pins _ (by simp)⟩
    · rintro ⟨a,b,adj,ha,hb⟩
      change (C.wires (List.ofFn x)).getD C.output false = true
      refine wire_mono n C fit.1 (pairInput a b) x ?_ C.output ?_
      · intro i hi
        have h : i = a ∨ i = b := of_decide_eq_true hi
        rcases h with rfl | rfl <;> assumption
      · change C.eval (List.ofFn (pairInput a b)) = true
        rw [fit.2.2.1 a b, decide_eq_true_eq]
        exact adj

  let andCost (C : Circuit) : ℕ :=
    letI := gateOpDecEq
    ((List.range C.gates.length).map fun j => if (gateAt C j).op = .and then j + 1 else 0).sum

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

  have W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      W (g :: gs) w = W gs (step w g) := rfl

  have W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
    simp [W, List.foldl_append]

  have W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
    rw [W_append]; rfl

  have W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
      W gs w = W (gs.drop j) (W (gs.take j) w) := by
    rw [← W_append, List.take_append_drop]

  have step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
    simp [step]

  have W_length (gs : List Gate) :
      ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
    induction gs with
    | nil => intro w; simp [W]
    | cons g gs ih =>
      intro w
      rw [W_cons, ih, step_len, List.length_cons]
      omega

  have getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
      (l ++ l2).getD i false = l.getD i false := by
    simp [List.getD, List.getElem?_append_left h]

  have getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
    simp [List.getD]

  have getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

  have step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
      (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

  have step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
      (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    subst hk; exact getD_app_len w _

  have W_prefix (gs : List Gate) :
      ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
      exact getD_app_lt w _ i hi

  have W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
      (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

  have W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
      (h : gs = pre ++ g :: post) :
      (W gs w).getD (w.length + pre.length) false =
        g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
    subst h
    rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
    exact step_last _ _ _ (by rw [W_length])

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨.or, []⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

  have eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    cases a <;> cases b <;> rfl

  let erase_rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

  have erase_redirect_lt (n m p i : ℕ) (h : i < n + m) : eraseRedirect n m p i = i := by
    unfold eraseRedirect
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have erase_redirect_self (n m p : ℕ) : eraseRedirect n m p (n + m) = p := by
    unfold eraseRedirect
    rw [ite_eq_left rfl]

  have erase_redirect_gt (n m p i : ℕ) (h : n + m < i) : eraseRedirect n m p i = i - 1 := by
    unfold eraseRedirect
    rw [ite_eq_right (by omega), ite_eq_left h]

  have erase_redirect_succ (n m p k : ℕ) (h : n + m ≤ k) : eraseRedirect n m p (k + 1) = k := by
    rw [erase_redirect_gt n m p (k + 1) (by omega), Nat.add_sub_cancel]

  have erase_hop_eq (r : ℕ → ℕ) (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool)
      (h : ∀ i, f i = f' (r i)) :
      op.eval (l.map f) = op.eval ((l.map r).map f') := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h i

  have erase_snoc_eq (a : List Bool) (v : Bool) (i : ℕ) (h : i = a.length) :
      (a ++ [v]).getD i false = v := by
    subst h
    exact getD_app_len a v

  have erase_snoc_gt (a : List Bool) (v : Bool) (i : ℕ) (h : a.length < i) :
      (a ++ [v]).getD i false = false :=
    getD_ge _ _ (by rw [List.length_append, List.length_singleton]; omega)

  have erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
      eraseGate n C m p = Circuit.mk
        (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
        (eraseRedirect n m p C.output) := ite_eq_left hm

  have erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
      (eraseGate n C m p).gates
        = C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)) :=
    congrArg Circuit.gates (erase_eq n C m p hm)

  have erase_output (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
      (eraseGate n C m p).output = eraseRedirect n m p C.output :=
    congrArg Circuit.output (erase_eq n C m p hm)

  have erase_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
      (eraseGate n C m p).gates.length + 1 = C.gates.length := by
    rw [erase_gates n C m p hm, List.length_append, List.length_take, List.length_map,
      List.length_drop]
    omega

  have erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
      (eraseGate n C m p).size + 1 = C.size := by
    show (eraseGate n C m p).gates.length + 1 = C.gates.length
    exact erase_length n C m p hm

  have erase_getD (l : List Gate) (f : Gate → Gate) (d : Gate) (m j : ℕ) (hm : m < l.length)
      (hj : j + 1 < l.length) :
      (l.take m ++ (l.drop (m + 1)).map f).getD j d
        = if j < m then l.getD j d else f (l.getD (j + 1) d) := by
    have hlt : (l.take m).length = m := by
      rw [List.length_take]
      omega
    by_cases h : j < m
    · rw [ite_eq_left h, List.getD_append _ _ _ _ (by omega)]
      rw [List.getD_eq_getElem (l.take m) d (by omega), List.getD_eq_getElem l d (by omega),
        List.getElem_take]
    · rw [ite_eq_right h, List.getD_append_right _ _ _ _ (by omega), hlt]
      have e : m + 1 + (j - m) = j + 1 := by omega
      rw [List.getD_eq_getElem (List.map f (l.drop (m + 1))) d
          (by rw [List.length_map, List.length_drop]; omega),
        List.getD_eq_getElem l d hj, List.getElem_map, List.getElem_drop]
      simp only [e]

  have erase_gateAt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
      (hj : j + 1 < C.gates.length) :
      gateAt (eraseGate n C m p) j
        = if j < m then gateAt C j else erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
    have h0 : gateAt (eraseGate n C m p) j
        = (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))).getD j
          (Gate.mk GateOp.or []) :=
      congrArg (fun gs : List Gate => gs.getD j (Gate.mk GateOp.or [])) (erase_gates n C m p hm)
    rw [h0]
    exact erase_getD C.gates (erase_rg (eraseRedirect n m p)) (Gate.mk GateOp.or []) m j hm hj

  have erase_gateAt_lt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
      (hj : j < m) : gateAt (eraseGate n C m p) j = gateAt C j := by
    rw [erase_gateAt n C m p j hm (by omega), ite_eq_left hj]

  have erase_gateAt_ge (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
      (hj : m ≤ j) (hj1 : j + 1 < C.gates.length) :
      gateAt (eraseGate n C m p) j = erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
    rw [erase_gateAt n C m p j hm hj1, ite_eq_right (Nat.not_lt.mpr hj)]

  have erase_monotone2 (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
      (hM : Monotone2 C) : Monotone2 (eraseGate n C m p) := by
    intro g hg
    rw [erase_gates n C m p hm] at hg
    rcases List.mem_append.1 hg with h | h
    · exact hM g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have h0 := hM g0 (List.mem_of_mem_drop hg0)
      refine ⟨h0.1, ?_⟩
      show (g0.inputs.map (eraseRedirect n m p)).length ≤ 2
      rw [List.length_map]
      exact h0.2

  have erase_val_lt {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length)
      {x : List Bool} (hx : x.length = n) {i : ℕ} (hi : i < n + m) :
      val (eraseGate n C m p) x i = val C x i := by
    have hpre : (C.gates.take m).length = m := by
      rw [List.length_take]
      omega
    have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
    have e1 : val (eraseGate n C m p) x i
        = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
          i false :=
      congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
    have e2 : val C x i = (W (C.gates.take m ++ C.gates.drop m) x).getD i false :=
      congrArg (fun gs : List Gate => (W gs x).getD i false) (List.take_append_drop m C.gates).symm
    rw [e1, e2, W_append, W_append,
      W_prefix ((C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
        (W (C.gates.take m) x) i (by omega),
      W_prefix (C.gates.drop m) (W (C.gates.take m) x) i (by omega)]

  have lift_gates (n : ℕ) (C : Circuit) (m p h : ℕ) :
      (liftAt n C m p h).gates = (eraseGate n C m p).gates ++
        [Gate.mk GateOp.or [(eraseGate n C m p).output, h]] := rfl

  have lift_length (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
      (liftAt n C m p h).gates.length = C.gates.length := by
    rw [lift_gates, List.length_append, List.length_singleton]
    exact erase_length n C m p hm

  have lift_size (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
      (liftAt n C m p h).size = C.size := lift_length n C m p h hm

  have lift_gateAt_lt (n : ℕ) (C : Circuit) (m p h j : ℕ)
      (hj : j < (eraseGate n C m p).gates.length) :
      gateAt (liftAt n C m p h) j = gateAt (eraseGate n C m p) j := by
    change (liftAt n C m p h).gates.getD j ⟨.or, []⟩ =
      (eraseGate n C m p).gates.getD j ⟨.or, []⟩
    rw [lift_gates]
    exact List.getD_append _ _ _ _ hj

  have lift_gateAt_last (n : ℕ) (C : Circuit) (m p h : ℕ) :
      gateAt (liftAt n C m p h) (eraseGate n C m p).gates.length
        = Gate.mk GateOp.or [(eraseGate n C m p).output, h] := by
    change (liftAt n C m p h).gates.getD (eraseGate n C m p).gates.length ⟨.or, []⟩ = _
    rw [lift_gates, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    rfl

  have lift_monotone2 (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length)
      (hM : Monotone2 C) : Monotone2 (liftAt n C m p h) := by
    intro g hg
    rw [lift_gates] at hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact erase_monotone2 n C m p hm hM g h1
    · rw [List.mem_singleton] at h1
      subst h1
      exact ⟨by simp, by simp⟩

  have lift_val_lt {n : ℕ} {C : Circuit} {m p h : ℕ} {x : List Bool} (hx : x.length = n)
      {k : ℕ} (hk : k < n + (eraseGate n C m p).gates.length) :
      val (liftAt n C m p h) x k = val (eraseGate n C m p) x k := by
    show (W (liftAt n C m p h).gates x).getD k false = (W (eraseGate n C m p).gates x).getD k false
    rw [lift_gates, W_append]
    exact W_prefix _ _ _ (by rw [W_length]; omega)

  have lift_or_eval2 (f : ℕ → Bool) (a b : ℕ) :
      GateOp.eval (Gate.mk GateOp.or [a, b]).op ((Gate.mk GateOp.or [a, b]).inputs.map f)
        = (f a || f b) := by
    show (f a || (f b || false)) = (f a || f b)
    cases f a <;> cases f b <;> rfl

  have lift_eval_or {n : ℕ} {C : Circuit} {m p h : ℕ} {x : List Bool} (hx : x.length = n) :
      (liftAt n C m p h).eval x = ((eraseGate n C m p).eval x || val (eraseGate n C m p) x h) := by
    have hEl : (W (eraseGate n C m p).gates x).length = n + (eraseGate n C m p).gates.length := by
      rw [W_length, hx]
    show (W ((eraseGate n C m p).gates ++
      [Gate.mk GateOp.or [(eraseGate n C m p).output, h]]) x).getD
        (n + (eraseGate n C m p).gates.length) false = _
    rw [W_snoc, step_last _ _ _ hEl.symm]
    exact lift_or_eval2 _ _ _

  have erase_step_rel (rel : Bool → Bool → Prop) (h00 : rel false false) (n m p : ℕ)
      (a b : List Bool) (hp : p ≠ b.length) (va vb : Bool) (hl : a.length = b.length + 1)
      (hn : n + m < a.length)
      (h : ∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) (hv : rel va vb) :
      ∀ i, rel ((a ++ [va]).getD i false) ((b ++ [vb]).getD (eraseRedirect n m p i) false) := by
    intro i
    by_cases hi : i < a.length
    · rw [getD_app_lt a [va] i hi]
      by_cases he : i = n + m
      · subst i
        rw [erase_redirect_self]
        have hr : (b ++ [vb]).getD p false = b.getD p false := by
          by_cases hlt : p < b.length
          · exact getD_app_lt b [vb] p hlt
          · rw [erase_snoc_gt b vb p (by omega), getD_ge b p (by omega)]
        rw [hr]
        simpa only [erase_redirect_self] using h (n + m)
      · have hri : eraseRedirect n m p i < b.length := by
          unfold eraseRedirect
          rw [ite_eq_right he]
          split_ifs <;> omega
        rw [getD_app_lt b [vb] _ hri]
        exact h i
    · rw [erase_redirect_gt n m p i (by omega)]
      by_cases hi2 : i = a.length
      · rw [erase_snoc_eq a va i hi2, erase_snoc_eq b vb (i - 1) (by omega)]
        exact hv
      · rw [erase_snoc_gt a va i (by omega), erase_snoc_gt b vb (i - 1) (by omega)]
        exact h00

  have erase_W_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (h00 : rel false false)
      (n m p : ℕ)
      (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
        (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
        rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
      (gs : List Gate) : ∀ (a b : List Bool), (∀ g ∈ gs, Q g.op) →
        a.length = b.length + 1 → n + m < a.length →
        (p < n + m ∨ b.length + gs.length ≤ p) →
        (∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) →
        ∀ i, rel ((W gs a).getD i false)
          ((W (gs.map (erase_rg (eraseRedirect n m p))) b).getD (eraseRedirect n m p i) false) := by
    induction gs with
    | nil => intro a b _ _ _ _ h i; exact h i
    | cons g gs ih =>
      intro a b hg hl hn safe h i
      rw [List.map_cons, W_cons, W_cons]
      refine ih (step a g) (step b (erase_rg (eraseRedirect n m p) g)) ?_ ?_ ?_ ?_ ?_ i
      · intro g' hg'
        exact hg g' (List.mem_cons_of_mem _ hg')
      · rw [step_len, step_len, hl]
      · rw [step_len]
        omega
      · rcases safe with near | far
        · exact Or.inl near
        · apply Or.inr
          rw [step_len]
          simp only [List.length_cons] at far
          omega
      · have hp : p ≠ b.length := by
          rcases safe with near | far
          · omega
          · simp only [List.length_cons] at far
            omega
        exact erase_step_rel rel h00 n m p a b hp
          (g.op.eval (g.inputs.map fun i => a.getD i false))
          (g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => b.getD i false))
          hl hn h
          (hop g.op g.inputs (fun i => a.getD i false) (fun i => b.getD i false)
            (hg g (by simp)) h)

  have erase_sem (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
      (n m p : ℕ)
      (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
        (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
        rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
      (pre post : List Gate) (gm : Gate) (x : List Bool) (hx : x.length = n)
      (hpre : pre.length = m)
      (safe : p < n + m ∨ n + m + post.length ≤ p)
      (hpost : ∀ g ∈ post, Q g.op)
      (hbase : rel (gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false))
        ((W pre x).getD p false)) :
      ∀ i, rel ((W (pre ++ gm :: post) x).getD i false)
        ((W (pre ++ post.map (erase_rg (eraseRedirect n m p))) x).getD
          (eraseRedirect n m p i) false) := by
    have hA : (W pre x).length = n + m := by rw [W_length, hx, hpre]
    rw [W_append, W_append, W_cons]
    refine erase_W_rel Q rel (hrefl false) n m p hop post (step (W pre x) gm) (W pre x)
      hpost ?_ ?_ ?_ ?_
    · exact step_len _ _
    · rw [step_len, hA]
      omega
    · rwa [hA]
    · intro i
      show rel ((W pre x ++ [gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false)]).getD i
        false) ((W pre x).getD (eraseRedirect n m p i) false)
      by_cases hi : i < n + m
      · rw [erase_redirect_lt n m p i hi, getD_app_lt (W pre x) _ i (by omega)]
        exact hrefl _
      · by_cases hi2 : i = n + m
        · rw [hi2, erase_redirect_self n m p, erase_snoc_eq (W pre x) _ (n + m) hA.symm]
          exact hbase
        · rw [erase_redirect_gt n m p i (by omega), erase_snoc_gt (W pre x) _ i (by omega),
            getD_ge (W pre x) (i - 1) (by omega)]
          exact hrefl false

  have erase_val_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
      {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (safe : p < n + m ∨ n + C.gates.length ≤ p)
      (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
        (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
        rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
      (hQ : ∀ g ∈ C.gates.drop (m + 1), Q g.op)
      {x : List Bool} (hx : x.length = n) (hv : rel (val C x (n + m)) (val C x p)) :
      ∀ i, rel (val C x i) (val (eraseGate n C m p) x (eraseRedirect n m p i)) := by
    have hsplit : C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1) = C.gates := by
      rw [gateAt_eq hm, ← List.drop_eq_getElem_cons hm, List.take_append_drop]
    have hpre : (C.gates.take m).length = m := by
      rw [List.length_take]
      omega
    have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
    have e1 : val C x (n + m) = (gateAt C m).op.eval
        ((gateAt C m).inputs.map fun i => (W (C.gates.take m) x).getD i false) := by
      have h1 := W_gate_pre C.gates (C.gates.take m) (C.gates.drop (m + 1)) (gateAt C m) x
        hsplit.symm
      rw [hx, hpre] at h1
      exact h1
    have e2 : val C x p = (W (C.gates.take m) x).getD p false := by
      rcases safe with near | far
      · show (W C.gates x).getD p false = _
        rw [W_split C.gates x m]
        exact W_prefix _ _ _ (by omega)
      · rw [val_ge hx far, getD_ge _ _ (by omega)]
    have safe' : p < n + m ∨ n + m + (C.gates.drop (m + 1)).length ≤ p := by
      rcases safe with near | far
      · exact Or.inl near
      · right
        rw [List.length_drop]
        omega
    rw [e1, e2] at hv
    have key := erase_sem Q rel hrefl n m p hop (C.gates.take m) (C.gates.drop (m + 1))
      (gateAt C m) x hx hpre safe' hQ hv
    have hW : ∀ i, val C x i
        = (W (C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1)) x).getD i false :=
      fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) hsplit.symm
    have hWD : ∀ i, val (eraseGate n C m p) x i
        = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
          i false :=
      fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
    intro i
    rw [hW i, hWD (eraseRedirect n m p i)]
    exact key i

  have erase_val {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (safe : p < n + m ∨ n + C.gates.length ≤ p)
      {x : List Bool} (hx : x.length = n) (hv : val C x p = val C x (n + m)) :
      ∀ i, val (eraseGate n C m p) x (eraseRedirect n m p i) = val C x i := by
    intro i
    exact (erase_val_rel (fun _ => True) (@Eq Bool) (fun _ => rfl) hm safe
      (fun op l f f' _ h => erase_hop_eq (eraseRedirect n m p) op l f f' h)
      (fun _ _ => trivial) hx hv.symm i).symm

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_imp : OpMono (fun a b => a = true → b = true) := by
    intro op hop l f g h
    rcases hop with rfl | rfl
    · change (l.map f).all id = true → (l.map g).all id = true
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro h1 i hi; exact h i hi (h1 i hi)
    · change (l.map f).any id = true → (l.map g).any id = true
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩


  have erase_val_le {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length)
      (safe : p < n + m ∨ n + C.gates.length ≤ p) (mono : Monotone2 C)
      {x : List Bool} (hx : x.length = n)
      (hv : val C x p = true → val C x (n + m) = true) :
      ∀ i, val (eraseGate n C m p) x (eraseRedirect n m p i) = true → val C x i = true := by
    refine erase_val_rel (fun op => op = .and ∨ op = .or) (fun a b => b = true → a = true)
      (fun _ h => h) hm safe ?_ ?_ hx hv
    · intro op l f f' hop h
      rw [List.map_map]
      exact opMono_imp op hop l (fun i => f' (eraseRedirect n m p i)) f (fun i _ => h i)
    · intro g hg
      exact (mono g (List.mem_of_mem_drop hg)).1

  have always_false (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length)
      (mono : Monotone2 C) :
      let p := n + C.size + 1
      let E := eraseGate n C m p
      Monotone2 E ∧ E.size + 1 = C.size ∧
        ∀ x : List Bool, x.length = n → val C x (n + m) = false →
          E.eval x = C.eval x ∧
          (∀ i, val E x (eraseRedirect n m p i) = val C x i) ∧
          ∀ j, val E x (n + j) = val C x (n + (if j < m then j else j + 1)) := by
    intro p E
    refine ⟨erase_monotone2 n C m p hm mono, erase_size n C m p hm, ?_⟩
    intro x hx zero
    have beyond : n + C.gates.length ≤ p := by
      change n + C.gates.length ≤ n + C.gates.length + 1
      omega
    have vals := erase_val hm (Or.inr beyond) hx ((val_ge hx beyond).trans zero.symm)
    refine ⟨?_, vals, ?_⟩
    · show val E x E.output = val C x C.output
      rw [show E.output = eraseRedirect n m p C.output from erase_output n C m p hm]
      exact vals C.output
    · intro j
      by_cases early : j < m
      · rw [ite_eq_left early]
        exact erase_val_lt hm hx (by omega)
      · rw [ite_eq_right early]
        have v := vals (n + j + 1)
        rw [erase_redirect_succ n m p (n + j) (by omega)] at v
        simpa only [Nat.add_assoc] using v

  have W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (W gs w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (W gs w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [W_cons]
      cases j with
      | zero =>
        have h1 : w.length < (step w g).length := by simp [step]
        rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
        simp only [List.getElem_cons_zero]
        rw [step_last w g w.length rfl]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, W_prefix gs (step w g) i (by simp [step]; omega)]
          exact (step_lt w g i hi).symm
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (step w g) j hj'
        have hl : (step w g).length = w.length + 1 := step_len w g
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact W_gate C.gates x j hj


  have readerShape (ins : List ℕ) (w : ℕ) (small : ins.length ≤ 2)
      (occur : w ∈ ins) : ins = [w] ∨ ∃ u, ins = [w, u] ∨ ins = [u, w] := by
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · cases occur
    · have e := List.mem_singleton.mp occur
      subst a
      exact Or.inl rfl
    · rcases List.mem_pair.mp occur with rfl | rfl
      · exact Or.inr ⟨b, Or.inl rfl⟩
      · exact Or.inr ⟨a, Or.inr rfl⟩
    · simp at small

  have orReaderRedirect (n : ℕ) (C : Circuit) (h r : ℕ)
      (hr : r < C.gates.length) (earlier : h < r)
      (read : n + h ∈ (gateAt C r).inputs) (small : (gateAt C r).inputs.length ≤ 2)
      (hop : (gateAt C r).op = .or) :
      ∃ p, (p < n + r ∨ n + C.gates.length ≤ p) ∧
        ∀ x : List Bool, x.length = n →
          val C x (n + r) = (val C x (n + h) || val C x p) := by
    let dead := n + C.gates.length + 1
    let readAt (x : List Bool) (u : ℕ) := if u < n + r then val C x u else false
    have hdead {x : List Bool} (hx : x.length = n) : val C x dead = false :=
      val_ge hx (by dsimp [dead]; omega)
    have hread (x : List Bool) : readAt x (n + h) = val C x (n + h) := by
      change (if n + h < n + r then val C x (n + h) else false) = _
      rw [ite_eq_left (by omega)]
    have old (x : List Bool) (hx : x.length = n) :
        val C x (n + r) = GateOp.or.eval ((gateAt C r).inputs.map (readAt x)) := by
      rw [val_gate hx hr, hop]
    have pairVal (u : ℕ)
        (shape : (gateAt C r).inputs = [n + h, u] ∨ (gateAt C r).inputs = [u, n + h])
        (x : List Bool) (hx : x.length = n) :
        val C x (n + r) = (val C x (n + h) || readAt x u) := by
      rw [old x hx]
      rcases shape with e | e
      · rw [e]
        change GateOp.or.eval [readAt x (n + h), readAt x u] = _
        rw [eval_or2, hread x]
      · rw [e]
        change GateOp.or.eval [readAt x u, readAt x (n + h)] = _
        rw [eval_or2, hread x, Bool.or_comm]
    rcases readerShape (gateAt C r).inputs (n + h) small read with one | ⟨u, pair⟩
    · refine ⟨dead, Or.inr (by dsimp [dead]; omega), fun x hx => ?_⟩
      rw [old x hx, one, hdead hx, Bool.or_false]
      change (readAt x (n + h) || false) = _
      rw [Bool.or_false, hread x]
    · by_cases valid : u < n + r ∧ u ≠ n + h
      · refine ⟨u, Or.inl valid.1, fun x hx => ?_⟩
        rw [pairVal u pair x hx]
        change (val C x (n + h) || (if u < n + r then val C x u else false)) = _
        rw [ite_eq_left valid.1]
      · refine ⟨dead, Or.inr (by dsimp [dead]; omega), fun x hx => ?_⟩
        rw [pairVal u pair x hx, hdead hx]
        by_cases same : u = n + h
        · rw [same, hread x, Bool.or_self, Bool.or_false]
        · have hlate : ¬ u < n + r := fun hu => valid ⟨hu, same⟩
          change (val C x (n + h) || (if u < n + r then val C x u else false)) = _
          rw [ite_eq_right hlate]

  have readerRedirect (n : ℕ) (C : Circuit) (h r : ℕ)
      (hr : r < C.gates.length) (earlier : h < r)
      (read : n + h ∈ (gateAt C r).inputs) (mono : Monotone2 C) :
      ∃ p, (p < n + r ∨ n + C.gates.length ≤ p) ∧
        ∀ x : List Bool, x.length = n →
          (val C x p = true → val C x (n + r) = true) ∧
          (val C x (n + h) = false → val C x p = val C x (n + r)) := by
    have model := mono (gateAt C r) (gateAt_mem hr)
    have op : (gateAt C r).op = .and ∨ (gateAt C r).op = .or := model.1
    rcases op with ha | ho
    · let dead := n + C.gates.length + 1
      have far : n + C.gates.length ≤ dead := by dsimp [dead]; omega
      refine ⟨dead, Or.inr far, fun x hx => ?_⟩
      rw [val_ge hx far]
      constructor
      · intro impossible
        cases impossible
      · intro hf
        cases ht : val C x (n + r)
        · rfl
        rw [val_gate hx hr, ha] at ht
        change ((gateAt C r).inputs.map (fun i =>
          if i < n + r then val C x i else false)).all id = true at ht
        simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at ht
        have hand := ht (n + h) read
        rw [ite_eq_left (by omega), hf] at hand
        cases hand
    · obtain ⟨p, safe, hp⟩ := orReaderRedirect n C h r hr earlier read model.2 ho
      refine ⟨p, safe, fun x hx => ?_⟩
      rw [hp x hx]
      constructor
      · intro ht
        rw [ht, Bool.or_true]
      · intro hf
        rw [hf, Bool.false_or]

  have lift_reader_semantic (n : ℕ) (C : Circuit) (h r : ℕ)
      (hr : r < C.gates.length) (earlier : h < r)
      (read : n + h ∈ (gateAt C r).inputs) (mono : Monotone2 C) :
      ∃ p : ℕ,
        let D := liftAt n C r p (n + h)
        Monotone2 D ∧ D.size = C.size ∧
        (∀ x : List Bool, x.length = n → D.eval x = (C.eval x || val C x (n + h))) ∧
        ∀ j < D.gates.length, (gateAt D j).op = .and →
          let old := if j < r then j else j + 1
          (gateAt C old).op = .and ∧
            ∀ x : List Bool, x.length = n → val D x (n + j) = true → val C x (n + old) = true := by
    obtain ⟨p, safe, redirect⟩ := readerRedirect n C h r hr earlier read mono
    let E := eraseGate n C r p
    let D := liftAt n C r p (n + h)
    have ELength : E.gates.length + 1 = C.gates.length := erase_length n C r p hr
    have DLength : D.gates.length = C.gates.length := lift_length n C r p (n + h) hr
    refine ⟨p, lift_monotone2 n C r p (n + h) hr mono, lift_size n C r p (n + h) hr, ?_, ?_⟩
    · intro x hx
      rw [lift_eval_or hx, erase_val_lt hr hx (by omega : n+h < n+r)]
      cases hh : val C x (n + h)
      · simp only [Bool.or_false]
        change val E x E.output = val C x C.output
        rw [show E.output = eraseRedirect n r p C.output from erase_output n C r p hr]
        exact erase_val hr safe hx ((redirect x hx).2 hh) C.output
      · simp only [Bool.or_true]
    · intro j hj hop
      have jE : j < E.gates.length := by
        by_contra bad
        have eq : j = E.gates.length := by
          change j < D.gates.length at hj
          omega
        subst j
        change (gateAt D E.gates.length).op = .and at hop
        rw [lift_gateAt_last] at hop
        cases hop
      change (gateAt D j).op = .and at hop
      rw [lift_gateAt_lt n C r p (n + h) j jE] at hop
      dsimp only
      by_cases ej : j < r
      · rw [ite_eq_left ej]
        rw [erase_gateAt_lt n C r p j hr ej] at hop
        refine ⟨hop, fun x hx hv => ?_⟩
        change val D x (n + j) = true at hv
        rw [lift_val_lt hx (by omega : n + j < n + E.gates.length),
          erase_val_lt hr hx (by omega : n + j < n + r)] at hv
        exact hv
      · rw [ite_eq_right ej]
        rw [erase_gateAt_ge n C r p j hr (Nat.le_of_not_gt ej) (by omega)] at hop
        refine ⟨hop, fun x hx hv => ?_⟩
        change val D x (n + j) = true at hv
        rw [lift_val_lt hx (by omega : n + j < n + E.gates.length)] at hv
        have vind := erase_val_le hr safe mono hx ((redirect x hx).1) (n + j + 1)
        rw [erase_redirect_succ n r p (n + j) (by omega)] at vind
        simpa only [Nat.add_assoc] using vind hv


  have lift_cost_lt (n : ℕ) (C : Circuit) (r p w : ℕ) (hr : r < C.gates.length)
      (later : ∃ j, r ≤ j ∧ j < C.gates.length ∧ (gateAt C j).op = .and) :
      andCost (liftAt n C r p w) < andCost C := by
    let _ := gateOpDecEq
    let E := eraseGate n C r p
    let D := liftAt n C r p w
    let f (A : Circuit) (j : ℕ) : ℕ := if (gateAt A j).op = .and then j + 1 else 0
    let count := C.gates.length - (r + 1)
    have elen : E.gates.length + 1 = C.gates.length := erase_length n C r p hr
    have dlen : D.gates.length = E.gates.length + 1 := by
      exact (lift_length n C r p w hr).trans elen.symm
    have splitOld : C.gates.length = r + 1 + count := by dsimp [count]; omega
    have splitNew : E.gates.length = r + count := by dsimp [count]; omega
    have samePrefix : (List.range r).map (f D) = (List.range r).map (f C) := by
      apply List.map_congr_left
      intro j hj
      have hjr := List.mem_range.mp hj
      have jE : j < E.gates.length := by omega
      change (if (gateAt D j).op = .and then j + 1 else 0) =
        (if (gateAt C j).op = .and then j + 1 else 0)
      rw [lift_gateAt_lt n C r p w j jE, erase_gateAt_lt n C r p j hr hjr]
    have endZero : f D E.gates.length = 0 := by
      change (if (gateAt D E.gates.length).op = .and then E.gates.length + 1 else 0) = 0
      rw [lift_gateAt_last]
      rfl
    have oldCost : andCost C =
        ((List.range r).map (f C)).sum + f C r +
          ((List.range count).map (fun i => f C (r + 1 + i))).sum := by
      change ((List.range C.gates.length).map (f C)).sum = _
      rw [splitOld, List.range_add, List.map_append, List.sum_append, List.map_map,
        List.sum_range_succ]
      rfl
    have newCost : andCost D =
        ((List.range r).map (f C)).sum +
          ((List.range count).map (fun i => f D (r + i))).sum := by
      change ((List.range D.gates.length).map (f D)).sum = _
      rw [dlen, List.sum_range_succ, endZero, Nat.add_zero, splitNew, List.range_add,
        List.map_append, List.sum_append, samePrefix, List.map_map]
      rfl
    have tailOp (i : ℕ) (hi : i ∈ List.range count) :
        (gateAt D (r + i)).op = (gateAt C (r + 1 + i)).op := by
      have lt := List.mem_range.mp hi
      have eq : r + i + 1 = r + 1 + i := by omega
      have inE : r + i < E.gates.length := by omega
      have inC : r + i + 1 < C.gates.length := by omega
      calc
        (gateAt D (r + i)).op = (gateAt E (r + i)).op :=
          congrArg Gate.op (lift_gateAt_lt n C r p w (r + i) inE)
        _ = (gateAt C (r + i + 1)).op := by
          have gate := erase_gateAt_ge n C r p (r + i) hr (by omega) inC
          have op := congrArg Gate.op gate
          exact op
        _ = (gateAt C (r + 1 + i)).op := congrArg (fun j => (gateAt C j).op) eq
    have tailBound (i : ℕ) (hi : i ∈ List.range count) : f D (r + i) ≤ f C (r + 1 + i) := by
      change (if (gateAt D (r + i)).op = .and then r + i + 1 else 0) ≤
        (if (gateAt C (r + 1 + i)).op = .and then r + 1 + i + 1 else 0)
      rw [tailOp i hi]
      split_ifs <;> omega
    obtain ⟨j, hrj, hj, andJ⟩ := later
    change andCost D < andCost C
    rw [newCost, oldCost]
    by_cases eq : j = r
    · subst j
      have removed : 0 < f C r := by
        change 0 < (if (gateAt C r).op = .and then r + 1 else 0)
        rw [ite_eq_left andJ]
        omega
      have bound := List.sum_le_sum tailBound
      omega
    · let i := j - (r + 1)
      have hi : i ∈ List.range count := by
        apply List.mem_range.mpr
        dsimp [i, count]
        omega
      have shifted : r + 1 + i = j := by dsimp [i]; omega
      have strict : f D (r + i) < f C (r + 1 + i) := by
        change (if (gateAt D (r + i)).op = .and then r + i + 1 else 0) <
          (if (gateAt C (r + 1 + i)).op = .and then r + 1 + i + 1 else 0)
        rw [tailOp i hi, shifted, ite_eq_left andJ, ite_eq_left andJ]
        omega
      have bound := List.sum_lt_sum (fun i => f D (r + i)) (fun i => f C (r + 1 + i))
        tailBound ⟨i, hi, strict⟩
      omega

  have lift_reader (n : ℕ) (C : Circuit) (h r : ℕ)
      (hr : r < C.gates.length) (earlier : h < r)
      (read : n + h ∈ (gateAt C r).inputs) (mono : Monotone2 C)
      (later : ∃ j, r ≤ j ∧ j < C.gates.length ∧ (gateAt C j).op = .and) :
      ∃ D : Circuit,
        Monotone2 D ∧ D.size = C.size ∧ andCost D < andCost C ∧
        (∀ x : List Bool, x.length = n → D.eval x = (C.eval x || val C x (n + h))) ∧
        ∀ j < D.gates.length, (gateAt D j).op = .and →
          let old := if j < r then j else j + 1
          (gateAt C old).op = .and ∧
            ∀ x : List Bool, x.length = n → val D x (n + j) = true → val C x (n + old) = true := by
    obtain ⟨p, trans⟩ := lift_reader_semantic n C h r hr earlier read mono
    exact ⟨liftAt n C r p (n + h), trans.1, trans.2.1, lift_cost_lt n C r p (n + h) hr later,
      trans.2.2.1, trans.2.2.2⟩

  have accepts_only_with_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (fourFree : NoFourCycle G) (C : Circuit) (j : ℕ) (g : Gate)
      (small : g.inputs.length ≤ 2)
      (andEval : ∀ x : Fin n → Bool, gateVal n C j x = true ↔
        ∀ w ∈ g.inputs, w < n+j ∧ (C.wires (List.ofFn x)).getD w false = true)
      (lift : ∀ (x : Fin n → Bool) (w : ℕ), w ∈ g.inputs → gateVal n C j x = true →
        ∃ a : Fin n, x a = true ∧ ∀ y : Fin n → Bool, y a = true →
          (C.wires (List.ofFn y)).getD w false = true)
      (empty : gateVal n C j (fun _ => false) = false)
      (nonedge : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
      (edge : ∃ a b : Fin n, G.Adj a b ∧ gateVal n C j (pairInput a b) = true) :
      ∃ c : Fin n, ∀ x : Fin n → Bool, gateVal n C j x = true → x c = true := by
    classical
    obtain ⟨p,q,_,hot⟩ := edge
    have bound (w : ℕ) (seen : w ∈ g.inputs) : w < n+j :=
      ((andEval (pairInput p q)).mp hot w seen).1
    have leftTrue (a b : Fin n) : pairInput a b a = true := decide_eq_true (Or.inl rfl)
    have rightTrue (a b : Fin n) : pairInput a b b = true := decide_eq_true (Or.inr rfl)
    obtain ⟨wa,wb,inputs⟩ : ∃ a b : ℕ, g.inputs = [a,b] := by
      rcases ins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,rest⟩⟩⟩
      · have onEmpty := (andEval (fun _ => false)).mpr (by
          intro w hw
          rw [ins] at hw
          cases hw)
        rw [empty] at onEmpty
        cases onEmpty
      · have mem : a ∈ g.inputs := by
          rw [ins]
          exact List.mem_cons_self
        obtain ⟨c,_,source⟩ := lift (pairInput p q) a mem hot
        have onSingle := (andEval (pairInput c c)).mpr (by
          intro w hw
          rw [ins] at hw
          have same := List.mem_singleton.mp hw
          subst w
          exact ⟨bound a mem,source (pairInput c c) (leftTrue c c)⟩)
        rw [nonedge c c (fun e => e.ne rfl)] at onSingle
        cases onSingle
      · exact ⟨a,b,rfl⟩
      · rw [ins] at small
        simp only [List.length_cons] at small
        omega
    have waMem : wa ∈ g.inputs := by
      rw [inputs]
      exact List.mem_cons_self
    have wbMem : wb ∈ g.inputs := by
      rw [inputs]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    let A : Set (Fin n) := {a | ∀ y : Fin n → Bool, y a = true →
      (C.wires (List.ofFn y)).getD wa false = true}
    let B : Set (Fin n) := {b | ∀ y : Fin n → Bool, y b = true →
      (C.wires (List.ofFn y)).getD wb false = true}
    have cross (a b : Fin n) (ha : a ∈ A) (hb : b ∈ B) : G.Adj a b := by
      by_contra off
      have active := (andEval (pairInput a b)).mpr (by
        intro w hw
        rw [inputs] at hw
        rcases List.mem_pair.mp hw with eq | eq
        · subst w
          exact ⟨bound wa waMem,ha _ (leftTrue a b)⟩
        · subst w
          exact ⟨bound wb wbMem,hb _ (rightTrue a b)⟩)
      rw [nonedge a b off] at active
      cases active
    obtain ⟨a0,_,a0A⟩ := lift (pairInput p q) wa waMem hot
    by_cases onlyA : ∀ a ∈ A, a = a0
    · refine ⟨a0,?_⟩
      intro x hx
      obtain ⟨a,hit,ha⟩ := lift x wa waMem hx
      exact (onlyA a ha) ▸ hit
    · push Not at onlyA
      obtain ⟨a1,a1A,ne⟩ := onlyA
      obtain ⟨b0,_,b0B⟩ := lift (pairInput p q) wb wbMem hot
      have neighbor (b : Fin n) (hb : b ∈ B) :
          b ∈ (Finset.univ.filter fun w => G.Adj a0 w ∧ G.Adj a1 w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ b,cross a0 b a0A hb,cross a1 b a1A hb⟩
      have unique := Finset.card_le_one.mp (fourFree a0 a1 ne.symm)
      refine ⟨b0,?_⟩
      intro x hx
      obtain ⟨b,hit,hb⟩ := lift x wb wbMem hx
      have eq : b = b0 := unique b (neighbor b hb) b0 (neighbor b0 b0B)
      exact eq ▸ hit

  have accepted_edges_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (fourFree : NoFourCycle G) (C : Circuit) (j : ℕ) (g : Gate)
      (small : g.inputs.length ≤ 2)
      (andEval : ∀ x : Fin n → Bool, gateVal n C j x = true ↔
        ∀ w ∈ g.inputs, w < n+j ∧ (C.wires (List.ofFn x)).getD w false = true)
      (lift : ∀ (x : Fin n → Bool) (w : ℕ), w ∈ g.inputs → gateVal n C j x = true →
        ∃ a : Fin n, x a = true ∧ ∀ y : Fin n → Bool, y a = true →
          (C.wires (List.ofFn y)).getD w false = true)
      (empty : gateVal n C j (fun _ => false) = false)
      (nonedge : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
      (edge : ∃ a b : Fin n, G.Adj a b ∧ gateVal n C j (pairInput a b) = true) :
      ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v →
        gateVal n C j (pairInput u v) = true → u = c ∨ v = c := by
    obtain ⟨c,center⟩ := accepts_only_with_center G fourFree C j g small andEval lift empty nonedge edge
    refine ⟨c,?_⟩
    intro u v _ hv
    have active := center (pairInput u v) hv
    have same : c = u ∨ c = v := of_decide_eq_true active
    exact same.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

  let pathRel (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
    a < b ∧ ∃ k : ℕ, ∃ h : Gate, b = n+k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs

  have path_strict (n : ℕ) (C : Circuit) :
      ∀ {a b : ℕ}, Relation.TransGen (pathRel n C) a b → a < b := by
    intro a b ab
    induction ab with
    | single direct => exact direct.1
    | tail _ next ih => exact lt_trans ih next.1

  have path_inCone (n : ℕ) (C : Circuit) :
      ∀ {a b : ℕ}, Relation.TransGen (pathRel n C) a b →
        ∀ i j : ℕ, a = n+i → b = n+j → InCone n C i j := by
    intro a b ab
    induction ab with
    | single h =>
      intro i j ha hb
      rcases h with ⟨hlt,k,g,hbk,hgk,hain⟩
      have hjk : j = k := by omega
      subst hjk
      rw [inCone_iff_rec n C j g i hgk]
      exact ⟨n+i,ha ▸ hain,by omega,by omega,Or.inl (by omega)⟩
    | tail hab hbc ih =>
      rename_i b' c'
      intro i j ha hc
      have hlt_a : a < b' := path_strict n C hab
      have hnb : n ≤ b' := by omega
      rcases hbc with ⟨hlt_b,k,g,hck,hgk,hbin⟩
      have hjk : j = k := by omega
      subst hjk
      have hib : InCone n C i (b'-n) := ih i (b'-n) ha (by omega)
      rw [inCone_iff_rec n C j g i hgk]
      exact ⟨b',hbin,hnb,by omega,Or.inr hib⟩

  intro n G inst triangle quadrilateral
  have four : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hap,hbp⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨haq,hbq⟩ := (Finset.mem_filter.mp hq).2
    exact (quadrilateral a p b q hap hbp.symm hbq haq.symm).resolve_left hab
  have initial : ∃ C : Circuit, sampleFit G C ∧
      ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size := by
    by_cases sided : ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v
    · exact twoColor n G triangle four sided
    · exact other n G triangle four sided
  obtain ⟨original,fitOriginal,lowerOriginal⟩ := initial
  let atSize (k : ℕ) := ∃ C : Circuit, sampleFit G C ∧ C.size = k
  have sizes : ∃ k, atSize k := ⟨original.size,original,fitOriginal,rfl⟩
  let s := Nat.find sizes
  obtain ⟨base,fitBase,sizeBase⟩ : atSize s := Nat.find_spec sizes
  let byWeight (a : ℕ) := ∃ C : Circuit, sampleFit G C ∧ C.size = s ∧ andCost C = a
  have weights : ∃ a, byWeight a := ⟨andCost base,base,fitBase,sizeBase,rfl⟩
  obtain ⟨C,fit,sizeC,weightC⟩ : byWeight (Nat.find weights) := Nat.find_spec weights
  have minimum (E : Circuit) (fitE : sampleFit G E) : C.size ≤ E.size :=
    sizeC.trans_le (Nat.find_min' sizes ⟨E,fitE,rfl⟩)
  have atGate (j : ℕ) (andOp : (gateAt C j).op = .and) : j < C.gates.length := by
    by_contra! high
    have fallback : gateAt C j = ⟨.or,[]⟩ := List.getD_eq_default _ _ high
    rw [fallback] at andOp
    cases andOp
  have flat : noNest n C := by
    intro h t ah targetAnd hc
    obtain ⟨r,rt,hr,g,hg,read⟩ := first_reader n C h t (atGate t targetAnd) hc
    have rlt := rt.trans_lt (atGate t targetAnd)
    have rh : n+h ∈ (gateAt C r).inputs := by rwa [gate_read C r g hg]
    obtain ⟨D,legal,lengthD,lowering,out,andD⟩ := lift_reader n C h r rlt hr rh fit.1
      ⟨t,rt,atGate t targetAnd,targetAnd⟩
    have cold := fit.2.2.2 h (atGate h ah) ah
    have fitD : sampleFit G D := by
      refine ⟨legal,?_,?_,?_⟩
      · rw [out _ List.length_ofFn, fit.2.1]
        exact cold.1
      · intro a b
        rw [out _ List.length_ofFn,fit.2.2.1]
        by_cases adj : G.Adj a b
        · simp [adj]
        · simpa only [decide_eq_false adj,Bool.false_or] using (show val C (List.ofFn (pairInput a b)) (n+h) = false from cold.2 a b adj)
      · intro j hj hop
        obtain ⟨oldOp,below⟩ := andD j hj hop
        let old := if j < r then j else j+1
        have oldCold := fit.2.2.2 old (atGate old oldOp) oldOp
        constructor
        · apply Bool.eq_false_iff.mpr
          intro hit
          have hhit := below (List.ofFn fun _ : Fin n => false) List.length_ofFn hit
          change gateVal n C old (fun _ => false) = true at hhit
          rw [oldCold.1] at hhit
          contradiction
        · intro a b adj
          apply Bool.eq_false_iff.mpr
          intro hit
          have hhit := below (List.ofFn (pairInput a b)) List.length_ofFn hit
          change gateVal n C old (pairInput a b) = true at hhit
          rw [oldCold.2 a b adj] at hhit
          contradiction
    have contrary : Nat.find weights ≤ andCost D :=
      Nat.find_min' weights ⟨D,fitD,lengthD.trans sizeC,rfl⟩
    exact (not_lt_of_ge (weightC.symm ▸ contrary)) lowering
  have active (m : ℕ) (hor : (gateAt C m).op = .and) :
      ∃ u v : Fin n, G.Adj u v ∧ gateVal n C m (pairInput u v) = true := by
    by_contra! missing
    have bound := atGate m hor
    let e := n + C.size + 1
    let E := PEqualNP.CircuitMoves.eraseGate n C m e
    have data := always_false n C m bound fit.1
    have monoE : Monotone2 E := data.1
    have sizeE : E.size + 1 = C.size := data.2.1
    have sem := data.2.2
    have cold := fit.2.2.2 m bound hor
    have pairZero (a b : Fin n) : gateVal n C m (pairInput a b) = false := by
      by_cases adj : G.Adj a b
      · exact Bool.eq_false_iff.mpr (missing a b adj)
      · exact cold.2 a b adj
    have equalsZero := sem (List.ofFn (fun _ : Fin n => false)) List.length_ofFn cold.1
    have equalsPair (a b : Fin n) :=
      sem (List.ofFn (pairInput a b)) List.length_ofFn (pairZero a b)
    have fitE : sampleFit G E := by
      refine ⟨monoE,equalsZero.1.trans fit.2.1,fun a b => (equalsPair a b).1.trans (fit.2.2.1 a b),?_⟩
      intro j hj hop
      let k := if j < m then j else j + 1
      have oldOp : (gateAt C k).op = .and := by
        by_cases before : j < m
        · simpa only [k,ite_eq_left before] using (congrArg Gate.op
            (erase_gateAt_lt n C m e j bound before)).symm.trans hop
        · have j' : j + 1 < C.gates.length := by
            change j < E.size at hj
            change E.size + 1 = C.gates.length at sizeE
            omega
          have eq := erase_gateAt_ge n C m e j bound (Nat.le_of_not_gt before) (by omega)
          have ops := congrArg Gate.op eq
          change (gateAt E j).op = (gateAt C (j+1)).op at ops
          simpa only [k,ite_eq_right before] using ops.symm.trans hop
      have oldCold := fit.2.2.2 k (atGate k oldOp) oldOp
      exact ⟨(equalsZero.2.2 j).trans oldCold.1,
        fun a b adj => ((equalsPair a b).2.2 j).trans (oldCold.2 a b adj)⟩
    exact (not_lt_of_ge (minimum E fitE)) (by omega)
  have exactFit := full_fit G C fit flat
  have graphRow (x : Fin n → Bool) :
      graphFun G ∅ x = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = _
    simp
  have optimum (D : Circuit) (mono : Monotone2 D)
      (exactD : ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) : C.size ≤ D.size := by
    have exactFunction : circuitFun n D = graphFun G ∅ :=
      funext (fun x => (exactD x).trans (graphRow x).symm)
    exact (minimum original fitOriginal).trans (lowerOriginal D mono exactFunction)
  refine ⟨C,fit.1,exactFit,optimum,?_⟩
  intro j g hg hop
  have ha : (gateAt C j).op = .and := (congrArg Gate.op (gate_read C j g hg)).trans hop
  have bound := atGate j ha
  have nz := active j ha
  have cold := fit.2.2.2 j bound ha
  have star := accepted_edges_star G four C j g (fit.1 g (List.mem_of_getElem? hg)).2
    (fun x => and_inputs n C x j g hg hop)
    (fun x w hw ht => and_parent_witness n C fit.1 flat x j g hg hop w hw ht)
    cold.1 cold.2 nz
  obtain ⟨center,allEdges⟩ := star
  refine ⟨center,?_,?_⟩
  · obtain ⟨a,b,adj,hit⟩ := nz
    refine ⟨a,b,adj,hit,?_⟩
    intro i h hi op route
    have ai : (gateAt C i).op = .and := (congrArg Gate.op (gate_read C i h hi)).trans op
    exact False.elim (flat i j ai ha (path_inCone n C route i j rfl rfl))
  · intro a b adj hit
    exact allEdges a b adj hit.1
