import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1031_401
    (hSound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∀ x y : Fin n, x ≠ y → gateVal n C j (pairInput x y) = true → G.Adj x y)
    (hAlive : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v : Fin n, G.Adj u v ∧ gateVal n C j (pairInput u v) = true)
    (hOwn : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∀ x y : Fin n, x ≠ y → gateVal n C j (pairInput x y) = true → G.Adj x y) →
        (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v : Fin n, G.Adj u v ∧ gateVal n C j (pairInput u v) = true) →
        ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
          (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
            ∀ x y : Fin n, x ≠ y → gateVal n D j (pairInput x y) = true → G.Adj x y) ∧
          ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
            ∃ u v : Fin n, G.Adj u v ∧ Owns n D j u v) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  classical
  intro n G _ htri hcycle
  obtain ⟨C₀, hmin₀, hfun₀, hps₀⟩ := hSound n G htri hcycle
  have hal₀ := hAlive n G htri hcycle C₀ hmin₀ hfun₀
  obtain ⟨C, hmin, hfun, hps, huse⟩ := hOwn n G htri hcycle C₀ hmin₀ hfun₀ hps₀ hal₀
  have coneUnfold (cs : List (List ℕ)) (g : Gate) :
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
  have coneLength (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [coneUnfold]
      omega
  have coneCharacter (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
          n ≤ w ∧ w < n + j ∧ (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by simp [coneLength]
      have old (k : ℕ) (hk : k < gs.length) :
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        simp only [coneUnfold, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have hold : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [old j h, ih i j, hold]
        constructor
        · rintro ⟨_, w, hw, h1, h2, hi⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rwa [old (w - n) (by omega)]
        · rintro ⟨_, w, hw, h1, h2, hi⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rwa [old (w - n) (by omega)] at hi
      · subst h
        have hgate : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have hnew : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp only [coneUnfold, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [hnew, hgate]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, hi⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rwa [old (w - n) (by omega)]
        · rintro ⟨_, w, hw, h1, h2, hi⟩
          rw [old (w - n) (by omega)] at hi
          exact ⟨w, ⟨hw, h1, h2⟩, hi⟩
      · have hnone : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          simp only [coneUnfold, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [hnone]
        constructor
        · intro hfalse; simp at hfalse
        · rintro ⟨hout, _⟩
          simp at hout
          omega
  have coneRec (i j : ℕ) : InCone n C i j ↔ j < C.gates.length ∧
      ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ InCone n C i k) := by
    delta InCone cones gateAt
    rw [coneCharacter]
    constructor
    · rintro ⟨hj, w, hw, hn, hwj, hi⟩
      refine ⟨hj, w - n, by omega, ?_, hi⟩
      rwa [show n + (w - n) = w by omega]
    · rintro ⟨hj, k, hk, hw, hi⟩
      refine ⟨hj, n + k, hw, by omega, by omega, ?_⟩
      rwa [show n + k - n = k by omega]
  have someBound (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) : j < C.gates.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hg
    contradiction
  have gateEq (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) : gateAt C j = g := by
    delta gateAt
    simp [List.getD_eq_getElem?_getD, hg]
  have gateSome (j : ℕ) (hj : j < C.gates.length) : C.gates[j]? = some (gateAt C j) := by
    delta gateAt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  let step (a b : ℕ) : Prop :=
    a < b ∧ ∃ (k : ℕ) (g : Gate), b = n + k ∧ C.gates[k]? = some g ∧ a ∈ g.inputs
  have increasing {a b : ℕ} (hpath : Relation.TransGen step a b) : a < b := by
    induction hpath with
    | single h => exact h.1
    | tail _ h ih => exact ih.trans h.1
  have conePath (j : ℕ) : ∀ i, InCone n C i j → Relation.TransGen step (n + i) (n + j) := by
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i hi
      obtain ⟨hj, k, hkj, hmem, hk⟩ := (coneRec i j).1 hi
      have hstep : step (n + k) (n + j) := ⟨by omega, j, gateAt C j, rfl, gateSome j hj, hmem⟩
      rcases hk with h | h
      · subst i
        exact Relation.TransGen.single hstep
      · exact Relation.TransGen.tail (ih k hkj i h) hstep
  have pathHasCone {b : ℕ} {i : ℕ} (hpath : Relation.TransGen step (n + i) b) :
      ∃ j, b = n + j ∧ InCone n C i j := by
    induction hpath with
    | single hs =>
      obtain ⟨hlt, j, g, hindex, hg, hmem⟩ := hs
      rw [hindex] at hlt
      refine ⟨j, hindex, (coneRec i j).2 ⟨someBound j g hg, i, by omega, ?_, Or.inl rfl⟩⟩
      simpa only [gateEq j g hg] using hmem
    | tail _ hs ih =>
      obtain ⟨k, hbefore, hc⟩ := ih
      obtain ⟨hlt, j, g, hindex, hg, hmem⟩ := hs
      rw [hbefore, hindex] at hlt
      refine ⟨j, hindex, (coneRec i j).2 ⟨someBound j g hg, k, by omega, ?_, Or.inr hc⟩⟩
      rwa [gateEq j g hg, ← hbefore]
  have pathCone {i j : ℕ} (hpath : Relation.TransGen step (n + i) (n + j)) :
      InCone n C i j := by
    obtain ⟨k, hk, hc⟩ := pathHasCone hpath
    have : k = j := by omega
    rwa [this] at hc
  have ownExact (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
      (u v : Fin n) : Owns n C j u v ↔
      (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + j) false = true ∧
        ∀ (i : ℕ) (g' : Gate), C.gates[i]? = some g' → g'.op = GateOp.and →
          Relation.TransGen step (n + i) (n + j) →
            (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + i) false = false := by
    have hj := someBound j g hg
    constructor
    · rintro ⟨_, _, hval, hprev⟩
      refine ⟨hval, ?_⟩
      intro i g' hi ho hpath
      have hlt := increasing hpath
      exact hprev i (by omega) (pathCone hpath) (by rwa [gateEq i g' hi])
    · rintro ⟨hval, hprev⟩
      refine ⟨hj, by rwa [gateEq j g hg], hval, ?_⟩
      intro i hi hc hgate
      exact hprev i (gateAt C i) (gateSome i (hi.trans hj)) hgate (conePath j i hc)
  have model (D : Circuit) : Monotone2 D ↔
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) := by
    delta Monotone2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have computes (D : Circuit) : circuitFun n D = graphFun G ∅ ↔
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) := by
    rw [funext_iff]
    delta circuitFun graphFun
    simp
  have hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    (model C).1 hmin.1
  let stepWire : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wiresEq (x : List Bool) : C.wires x = C.gates.foldl stepWire x := rfl
  have foldlLength (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega
  have foldlGetLt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getDGe (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldlGetGate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldlGetLt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldlGetLt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]; exact getDGe w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  have gateAtEq (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have gateAtMem (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAtEq j hj]; exact List.getElem_mem hj
  have valGate (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
      (C.wires x).getD (n + j) false = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then (C.wires x).getD i false else false) := by
    rw [← hx, gateAtEq j hj]
    exact foldlGetGate C.gates x j hj
  have valOr (x : List Bool) (hx : x.length = n) (r : ℕ) (hr : r < C.gates.length)
      (hop : (gateAt C r).op = GateOp.or) :
      (C.wires x).getD (n + r) false = true ↔
        ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ (C.wires x).getD i false = true := by
    rw [valGate x hx r hr, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [if_neg hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
  have valAnd (x : List Bool) (hx : x.length = n) (r : ℕ) (hr : r < C.gates.length)
      (hop : (gateAt C r).op = GateOp.and) :
      (C.wires x).getD (n + r) false = true ↔
        ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ (C.wires x).getD i false = true := by
    rw [valGate x hx r hr, hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
      · rw [if_neg hlt] at h'; cases h'
    · intro h i hi
      rw [if_pos (h i hi).1]; exact (h i hi).2
  have inputWire (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
      (C.wires (List.ofFn z)).getD i false = z ⟨i, hi⟩ := by
    rw [wiresEq, foldlGetLt _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  have coneTrans (j k k' : ℕ) (hkj : InCone n C k j) (hk' : k' < k)
      (hin : n + k' ∈ (gateAt C k).inputs) : InCone n C k' j := by
    have hkj' : k < j := by have := increasing (conePath j k hkj); omega
    have hjlen : j < C.gates.length := ((coneRec k j).1 hkj).1
    have hk : k < C.gates.length := by omega
    have hstep : step (n + k') (n + k) :=
      ⟨by omega, k, gateAt C k, rfl, gateSome k hk, hin⟩
    exact pathCone (Relation.TransGen.trans (Relation.TransGen.single hstep) (conePath j k hkj))
  have dom (j : ℕ) (u v : Fin n) (hown : Owns n C j u v) :
      ∀ i : ℕ, i < n + j → (i < n ∨ InCone n C (i - n) j) →
        (C.wires (List.ofFn (pairInput u v))).getD i false = true →
        ∃ s : Fin n, (s = u ∨ s = v) ∧ ∀ z : Fin n → Bool, z s = true →
          (C.wires (List.ofFn z)).getD i false = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hij hcone hval
      by_cases hin : i < n
      · rw [inputWire _ i hin] at hval
        refine ⟨⟨i, hin⟩, ?_, fun z hz => by rw [inputWire z i hin]; exact hz⟩
        simpa [pairInput] using hval
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hkj : k < j := by omega
        have hcone' : InCone n C k j := by
          rcases hcone with h | h
          · omega
          · simpa using h
        have hklen : k < C.gates.length := by
          have := ((coneRec k j).1 hcone').1
          omega
        rcases (hmono _ (gateAtMem k hklen)).1 with hop | hop
        · exfalso
          have h0 : (C.wires (List.ofFn (pairInput u v))).getD (n + k) false = false :=
            hown.2.2.2 k hkj hcone' hop
          rw [h0] at hval
          exact absurd hval (by simp)
        · obtain ⟨i', hi'in, hi'lt, hi'val⟩ :=
            (valOr (List.ofFn (pairInput u v)) (by simp) k hklen hop).1 hval
          have hcn : i' < n ∨ InCone n C (i' - n) j := by
            by_cases h : i' < n
            · exact Or.inl h
            · right
              obtain ⟨k', rfl⟩ : ∃ k', i' = n + k' := ⟨i' - n, by omega⟩
              have : n + k' - n = k' := by omega
              rw [this]
              exact coneTrans j k k' hcone' (by omega) hi'in
          obtain ⟨s, hs, hsd⟩ := ih i' (by omega) (by omega) hcn hi'val
          refine ⟨s, hs, fun z hz => ?_⟩
          exact (valOr (List.ofFn z) (by simp) k hklen hop).2 ⟨i', hi'in, hi'lt, hsd z hz⟩
  have leak (j : ℕ) (u v p q : Fin n) (hown1 : Owns n C j u v) (hown2 : Owns n C j p q)
      (huv : G.Adj u v) (hpq : G.Adj p q)
      (hup : u ≠ p) (huq : u ≠ q) (hvp : v ≠ p) (hvq : v ≠ q) :
      ∃ x y : Fin n, x ≠ y ∧ ¬ G.Adj x y ∧ gateVal n C j (pairInput x y) = true := by
    obtain ⟨hj, hgop, hval1, hprev1⟩ := hown1
    obtain ⟨_, _, hval2, hprev2⟩ := hown2
    have A1 := (valAnd _ (by simp) j hj hgop).1 hval1
    have A2 := (valAnd _ (by simp) j hj hgop).1 hval2
    have hinp : ∀ i ∈ (gateAt C j).inputs, ∃ s s' : Fin n, (s = u ∨ s = v) ∧ (s' = p ∨ s' = q) ∧
        ∀ x y : Fin n, (x = s ∨ y = s') →
          (C.wires (List.ofFn (pairInput x y))).getD i false = true := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := A1 i hi
      obtain ⟨hi1', hi2'⟩ := A2 i hi
      have hcn : i < n ∨ InCone n C (i - n) j := by
        by_cases h : i < n
        · exact Or.inl h
        · right
          obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
          have : n + k - n = k := by omega
          rw [this]
          exact (coneRec k j).2 ⟨hj, k, by omega, hi, Or.inl rfl⟩
      obtain ⟨s, hs, hsd⟩ := dom j u v ⟨hj, hgop, hval1, hprev1⟩ i hi1 hcn hi2
      obtain ⟨s', hs', hsd'⟩ := dom j p q ⟨hj, hgop, hval2, hprev2⟩ i hi1' hcn hi2'
      refine ⟨s, s', hs, hs', ?_⟩
      intro x y hxy
      rcases hxy with rfl | rfl
      · exact hsd _ (by simp [pairInput])
      · exact hsd' _ (by simp [pairInput])
    have dis : ∀ s s' : Fin n, (s = u ∨ s = v) → (s' = p ∨ s' = q) → s ≠ s' := by
      intro s s' hs hs' h
      rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;>
        first | exact hup h | exact huq h | exact hvp h | exact hvq h
    have adjL : ∀ a b : Fin n, (a = u ∨ a = v) → (b = u ∨ b = v) → a ≠ b → G.Adj a b := by
      intro a b ha hb hab
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact huv
      · exact huv.symm
      · exact (hab rfl).elim
    have adjR : ∀ a b : Fin n, (a = p ∨ a = q) → (b = p ∨ b = q) → a ≠ b → G.Adj a b := by
      intro a b ha hb hab
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hpq
      · exact hpq.symm
      · exact (hab rfl).elim
    have hlen := (hmono _ (gateAtMem j hj)).2
    by_contra hcon
    have hAdj : ∀ x y : Fin n, x ≠ y →
        (∀ i ∈ (gateAt C j).inputs, (C.wires (List.ofFn (pairInput x y))).getD i false = true) →
        G.Adj x y := by
      intro x y hne hQ
      by_contra hna
      apply hcon
      refine ⟨x, y, hne, hna, ?_⟩
      exact (valAnd _ (by simp) j hj hgop).2 (fun i hi => ⟨(A1 i hi).1, hQ i hi⟩)
    have tri1 : ∀ s : Fin n, (s = u ∨ s = v) →
        (∀ i ∈ (gateAt C j).inputs, ∀ y : Fin n,
          (C.wires (List.ofFn (pairInput s y))).getD i false = true) → False := by
      intro s hs hQ
      have h1 := hAdj s p (dis s p hs (Or.inl rfl)) (fun i hi => hQ i hi p)
      have h2 := hAdj s q (dis s q hs (Or.inr rfl)) (fun i hi => hQ i hi q)
      exact htri p q s hpq h2.symm h1
    generalize (gateAt C j).inputs = l at hinp hAdj tri1 hlen
    match l, hlen with
    | [], _ =>
      exact tri1 u (Or.inl rfl) (fun i hi => by simp at hi)
    | [i], _ =>
      obtain ⟨s, s', hs, hs', hsd⟩ := hinp i (by simp)
      refine tri1 s hs (fun i' hi' y => ?_)
      have : i' = i := by simpa using hi'
      subst this
      exact hsd s y (Or.inl rfl)
    | [i1, i2], _ =>
      obtain ⟨s1, t1, hs1, ht1, hsd1⟩ := hinp i1 (by simp)
      obtain ⟨s2, t2, hs2, ht2, hsd2⟩ := hinp i2 (by simp)
      by_cases e1 : s1 = s2
      · subst e1
        refine tri1 s1 hs1 (fun i' hi' y => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
        rcases hi' with rfl | rfl
        · exact hsd1 s1 y (Or.inl rfl)
        · exact hsd2 s1 y (Or.inl rfl)
      · by_cases e2 : t1 = t2
        · subst e2
          have hmem : ∀ i' ∈ [i1, i2], ∀ w : Fin n,
              (C.wires (List.ofFn (pairInput w t1))).getD i' false = true := by
            intro i' hi' w
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
            rcases hi' with rfl | rfl
            · exact hsd1 w t1 (Or.inr rfl)
            · exact hsd2 w t1 (Or.inr rfl)
          have a1 := hAdj u t1 (dis u t1 (Or.inl rfl) ht1) (fun i' hi' => hmem i' hi' u)
          have a2 := hAdj v t1 (dis v t1 (Or.inr rfl) ht1) (fun i' hi' => hmem i' hi' v)
          exact htri u v t1 huv a2 a1.symm
        · have b1 := hAdj s1 t2 (dis s1 t2 hs1 ht2) (by
            intro i' hi'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
            rcases hi' with rfl | rfl
            · exact hsd1 s1 t2 (Or.inl rfl)
            · exact hsd2 s1 t2 (Or.inr rfl))
          have b2 := hAdj s2 t1 (dis s2 t1 hs2 ht1) (by
            intro i' hi'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
            rcases hi' with rfl | rfl
            · exact hsd1 s2 t1 (Or.inr rfl)
            · exact hsd2 s2 t1 (Or.inl rfl))
          have c1 : G.Adj t2 t1 := adjR t2 t1 ht2 ht1 (Ne.symm e2)
          have c2 : G.Adj s2 s1 := adjL s2 s1 hs2 hs1 (Ne.symm e1)
          rcases hcycle s1 t2 t1 s2 b1 c1 b2.symm c2 with h | h
          · exact dis s1 t1 hs1 ht1 h
          · exact dis s2 t2 hs2 ht2 h.symm
    | _ :: _ :: _ :: _, h => simp at h
  have common (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
      ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = c ∨ v = c := by
    have hmeet (u v p q : Fin n) (huv : G.Adj u v) (hpq : G.Adj p q)
        (h1 : Owns n C j u v) (h2 : Owns n C j p q) : u = p ∨ u = q ∨ v = p ∨ v = q := by
      by_contra hn
      push Not at hn
      obtain ⟨x, y, hxy, hna, hT⟩ := leak j u v p q h1 h2 huv hpq hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
      exact hna (hps j hj hop x y hxy hT)
    obtain ⟨a, b, hab, hoab⟩ := huse j hj hop
    by_cases ha : ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = a ∨ v = a
    · exact ⟨a, ha⟩
    · push Not at ha
      obtain ⟨p, q, hpq, hopq, hpa, hqa⟩ := ha
      have hbpq : p = b ∨ q = b := by
        have h := hmeet p q a b hpq hab hopq hoab
        tauto
      have hext : ∃ w : Fin n, w ≠ a ∧ G.Adj b w ∧
          ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
        rcases hbpq with rfl | rfl
        · refine ⟨q, hqa, hpq, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
        · refine ⟨p, hpa, hpq.symm, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
      obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
      refine ⟨b, ?_⟩
      intro u v huv hov
      by_contra hn
      push Not at hn
      have huva : u = a ∨ v = a := by
        have h := hmeet u v a b huv hab hov hoab
        tauto
      have huvw : u = w ∨ v = w := by
        have h := hmeetw u v huv hov
        tauto
      have hwaAdj : G.Adj w a := by
        rcases huva with h | h
        · subst u
          have hvw : v = w := huvw.resolve_left (Ne.symm hwa)
          simpa [hvw] using huv.symm
        · subst v
          have huw : u = w := huvw.resolve_right (Ne.symm hwa)
          simpa [huw] using huv
      exact htri a b w hab hbw hwaAdj
  refine ⟨C, (model C).1 hmin.1, (computes C).1 hfun, ?_, ?_⟩
  · intro D hD hDf
    exact hmin.2 D ((model D).2 hD) (((computes D).2 hDf).trans hfun.symm)
  · intro j g hj hop
    have hgate : (gateAt C j).op = GateOp.and := by rwa [gateEq j g hj]
    have hbound := someBound j g hj
    obtain ⟨u, v, huv, hown⟩ := huse j hbound hgate
    obtain ⟨c, hc⟩ := common j hbound hgate
    refine ⟨c, ⟨u, v, huv, (ownExact j g hj hop u v).1 hown⟩, ?_⟩
    intro p q hpq h
    exact hc p q hpq ((ownExact j g hj hop p q).2 h)
