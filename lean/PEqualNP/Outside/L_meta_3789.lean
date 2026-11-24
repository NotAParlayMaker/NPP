import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3789_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover


def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

/-- The value of the wire of gate `k` is the operation applied to the wire values it reads,
taking `false` for wires that do not exist when the gate is evaluated. -/
lemma gate_wire_getD (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (n + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
        if i < n + k then (C.wires x).getD i false else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire x
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len, hx]
  have hCj : (C.wires x).getD (n + k) false =
      gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w, (w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
  · simp [orStep, List.getD_eq_getElem?_getD, hop]

lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

/-- The OR closure of the wire of gate `k`, read gate by gate: either `g` is gate `k` itself, or
`k` is an OR gate reading an earlier wire whose OR closure contains `g`. -/
lemma orReaches_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : ∀ x, x ∈ (orSets n C).getD k [] ↔ x = k ∨ (gk.op = GateOp.or ∧
      ∃ w, (w ∈ gk.inputs ∧ n ≤ w ∧ w < n + k) ∧
        x ∈ (pre.foldl (orStep n) []).getD (w - n) []) := by
    intro x
    rw [hc, orFold_getD_lt n post _ k (by omega)]
    have h := orStep_mem_last n (pre.foldl (orStep n) []) gk x
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have e : n + k - n = k := by omega
  unfold OrReaches
  rw [e, h1 g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, ⟨hw, hn, hlt⟩, h⟩⟩
    · exact Or.inl h
    · right
      refine ⟨hop, w, hw, hn, hlt, hn, ?_⟩
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro (h | ⟨hop, w, hw, hn, hlt, _, h⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨hop, w, ⟨hw, hn, hlt⟩, ?_⟩⟩
      rw [← h2 (w - n) (by omega)]
      exact h

lemma orReaches_length {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) :
    w - n < C.gates.length := by
  have hn : n ≤ w := h.1
  by_contra hk
  have hlen : (orSets n C).length = C.gates.length := by
    simp [orSets, orFold_length]
  have hge : (orSets n C).length ≤ w - n := by
    rw [hlen]
    omega
  have hempty : (orSets n C).getD (w - n) [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl
  have hmem := h.2
  rw [hempty] at hmem
  exact absurd hmem (by simp)

/-- OR closure propagates truth: if gate `g` is true, every gate wire whose OR closure contains
`g` is true. -/
lemma orReaches_true (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
    ∀ k, k < C.gates.length → ∀ g, OrReaches n C (n + k) g →
      (C.wires x).getD (n + g) false = true →
      (C.wires x).getD (n + k) false = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk g hr htrue
    rcases (orReaches_iff n C g k hk).mp hr with rfl | ⟨hop, i, hi, hn, hlt, hri⟩
    · exact htrue
    · have hine : n + (i - n) = i := by omega
      have hri' : OrReaches n C (n + (i - n)) g := by rwa [hine]
      have hik : i - n < k := by omega
      have htrue_i : (C.wires x).getD i false = true := by
        rw [← hine]
        exact ih (i - n) hik (by omega) g hri' htrue
      have hval := gate_wire_getD n C x hx k hk
      rw [hval, hop]
      have hmem : (if i < n + k then (C.wires x).getD i false else false) ∈
          (gateAt C k).inputs.map
            (fun i => if i < n + k then (C.wires x).getD i false else false) :=
        List.mem_map.mpr ⟨i, hi, rfl⟩
      have hone : (if i < n + k then (C.wires x).getD i false else false) = true := by
        simp only [hlt, ↓reduceIte]
        exact htrue_i
      have hany : ((gateAt C k).inputs.map
          (fun i => if i < n + k then (C.wires x).getD i false else false)).any id = true := by
        rw [List.any_eq_true]
        exact ⟨_, hmem, hone⟩
      simpa [GateOp.eval] using hany

end PEqualNP.Outside.L_meta_3789_aux

theorem PEqualNP.Outside.L_meta_3789 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : List Bool),
      x5.length = x1 →
      PEqualNP.CleanedNonEdge.OrReaches x1 x2 x4 x3 →
      (x2.wires x5).getD (x1 + x3) Bool.false = Bool.true →
      (x2.wires x5).getD x4 Bool.false = Bool.true := by
  intro n C g w x hx hr htrue
  have hn : n ≤ w := hr.1
  have hw : n + (w - n) = w := by omega
  have hk : w - n < C.gates.length :=
    PEqualNP.Outside.L_meta_3789_aux.orReaches_length hr
  have hr' : PEqualNP.CleanedNonEdge.OrReaches n C (n + (w - n)) g := by rwa [hw]
  have hres := PEqualNP.Outside.L_meta_3789_aux.orReaches_true n C x hx
    (w - n) hk g hr' htrue
  rwa [hw] at hres
