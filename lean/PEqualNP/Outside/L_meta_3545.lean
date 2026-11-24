import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3545

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
  PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

theorem foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

theorem foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem wv_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    wireVal n C (n + k) x = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then wireVal n C i x else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : wireVal n C (n + k) x = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [wireVal]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [wireVal]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

theorem wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    wireVal n C u x = x ⟨u, hu⟩ := by
  simp only [wireVal]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

theorem wv_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wireVal n C w x = false := by
  simp only [wireVal]
  apply getD_ge_length
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]
  exact hw

/-! Cones. -/

theorem coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

theorem coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (j : ℕ) (hj : j < cs.length) :
    (coneStep n cs g).getD j [] = cs.getD j [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

theorem coneStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (coneStep n cs g).getD cs.length [] ↔
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ (x = w - n ∨ x ∈ cs.getD (w - n) []) := by
  simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_flatMap, List.mem_filter,
    decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, hx⟩
    exact ⟨w, hw, hn, hlt, hx⟩
  · rintro ⟨w, hw, hn, hlt, hx⟩
    exact ⟨w, ⟨hw, hn, hlt⟩, hx⟩

theorem cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  simp [cones, coneFold_length]

theorem cones_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (cones n C).getD k [] ↔
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        (x = w - n ∨ x ∈ (cones n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have h1 : (cones n C).getD k [] = (coneStep n (pre.foldl (coneStep n) []) gk).getD k [] := by
    rw [hc, coneFold_getD_lt n post _ k (by simp [coneStep, hl0])]
  have h2 : ∀ j, j < k → (cones n C).getD j [] = (pre.foldl (coneStep n) []).getD j [] := by
    intro j hj
    rw [hc, coneFold_getD_lt n post _ j (by simp [coneStep, hl0]; omega)]
    exact coneStep_getD_lt n _ gk j (by omega)
  have h3 := coneStep_mem_last n (pre.foldl (coneStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro ⟨w, hw, hn, hlt, hx⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by rw [h2 (w - n) (by omega)]; exact hx)
  · rintro ⟨w, hw, hn, hlt, hx⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by rw [← h2 (w - n) (by omega)]; exact hx)

theorem inCone_lt (n : ℕ) (C : Circuit) (a b : ℕ) (h : InCone n C a b) : b < C.gates.length := by
  by_contra hb
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

theorem inCone_iff (n : ℕ) (C : Circuit) (a b : ℕ) (hb : b < C.gates.length) :
    InCone n C a b ↔ ∃ w ∈ (gateAt C b).inputs, n ≤ w ∧ w < n + b ∧
      (a = w - n ∨ InCone n C a (w - n)) := by
  unfold InCone
  exact cones_mem_iff n C b a hb

theorem inCone_read (n : ℕ) (C : Circuit) (g r : ℕ) (hr : r < C.gates.length)
    (hw : n + g ∈ (gateAt C r).inputs) (hg : g < r) : InCone n C g r := by
  rw [inCone_iff n C g r hr]
  exact ⟨n + g, hw, by omega, by omega, Or.inl (by omega)⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (a b : ℕ) :
    ∀ c, InCone n C a b → InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hab hbc
    have hc := inCone_lt n C b c hbc
    rw [inCone_iff n C b c hc] at hbc
    obtain ⟨w, hw, hn, hlt, hx⟩ := hbc
    rw [inCone_iff n C a c hc]
    refine ⟨w, hw, hn, hlt, Or.inr ?_⟩
    rcases hx with hx | hx
    · rw [← hx]; exact hab
    · exact ih (w - n) (by omega) hab hx

/-! OR closures. -/

theorem orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

theorem orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

theorem orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (j : ℕ) (hj : j < cs.length) :
    (orStep n cs g).getD j [] = cs.getD j [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

theorem orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp [orSets, orFold_length]

theorem orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
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
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ j, j < k → (orSets n C).getD j [] = (pre.foldl (orStep n) []).getD j [] := by
    intro j hj
    rw [hc, orFold_getD_lt n post _ j (by omega)]
    exact orStep_getD_lt n _ gk j (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

theorem orReaches_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ) :
    ∀ w, OrReaches n C w g → wireVal n C (n + g) x = true → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr hg
    obtain ⟨hnw, hmem⟩ := hr
    have hk : w - n < C.gates.length := by
      by_contra hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)]
        at hmem
      simp at hmem
    rw [orSets_mem_iff n C (w - n) g hk] at hmem
    rcases hmem with h | ⟨hop, w', hw', hn', hlt', hx⟩
    · rw [h] at hg; rwa [show n + (w - n) = w by omega] at hg
    · have hv : wireVal n C w' x = true := ih w' (by omega) ⟨hn', hx⟩ hg
      have := wv_gate n C x (w - n) hk
      rw [show n + (w - n) = w by omega] at this
      rw [this, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true]
      exact ⟨w', hw', by simp [show w' < w by omega, hv]⟩

/-! The rewired circuit `D`. -/

def mapG (rho : ℕ → ℕ → ℕ) (r : ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (fun i => rho r i) }

def Dc (G0 : List Gate) (C : Circuit) (rho : ℕ → ℕ → ℕ) (o : ℕ) : Circuit :=
  Circuit.mk (G0 ++ C.gates.mapIdx (mapG rho)) o

theorem D_gateAt (G0 : List Gate) (C : Circuit) (rho : ℕ → ℕ → ℕ) (o : ℕ) (r : ℕ)
    (hr : r < C.gates.length) :
    gateAt (Dc G0 C rho o) (G0.length + r) = mapG rho r (gateAt C r) := by
  simp only [Dc, gateAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp [hr]

theorem D_prefix (n : ℕ) (G0 : List Gate) (C : Circuit) (rho : ℕ → ℕ → ℕ) (o : ℕ)
    (x : Fin n → Bool) (j : ℕ) (hj : j < n + G0.length) :
    wireVal n (Dc G0 C rho o) j x = wireVal n (Circuit.mk G0 0) j x := by
  simp only [wireVal, Dc]
  rw [wires_eq_foldl, wires_eq_foldl]
  simp only [List.foldl_append]
  apply foldl_stepWire_getD_lt
  rw [foldl_stepWire_length, List.length_ofFn]
  exact hj

def drd (n : ℕ) (G0 : List Gate) (C : Circuit) (rho : ℕ → ℕ → ℕ) (o : ℕ) (x : Fin n → Bool)
    (r i : ℕ) : Bool :=
  if rho r i < n + (G0.length + r) then wireVal n (Dc G0 C rho o) (rho r i) x else false

theorem D_val2 (n : ℕ) (G0 : List Gate) (C : Circuit) (rho : ℕ → ℕ → ℕ) (o : ℕ)
    (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length) (a b : ℕ)
    (hab : (gateAt C r).inputs = [a, b]) :
    wireVal n (Dc G0 C rho o) (n + G0.length + r) x =
      (gateAt C r).op.eval [drd n G0 C rho o x r a, drd n G0 C rho o x r b] := by
  have hk : G0.length + r < (Dc G0 C rho o).gates.length := by simp [Dc]; omega
  rw [show n + G0.length + r = n + (G0.length + r) by omega, wv_gate n _ x _ hk,
    D_gateAt G0 C rho o r hr]
  simp only [mapG, hab, List.map_cons, List.map_nil, drd]

abbrev Tr (n : ℕ) (C : Circuit) (W u : ℕ → ℕ) (k g : ℕ) : Prop :=
  g < C.gates.length ∧ OrReaches n C (W k) g ∧ (gateAt C g).op = GateOp.or ∧
    InCone n C (u k) g

theorem core : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H qH C m u T W z NR P G0 rho D hq hAO hC hNR hP h6 h7 h8 hG0 hD hr1 hr2 y
  have hmem : ∀ r, r < C.gates.length → gateAt C r ∈ C.gates := fun r hr => by
    rw [gateAt_eq C r hr]; exact List.getElem_mem hr
  have hop : ∀ r, r < C.gates.length →
      (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or :=
    fun r hr => hAO.1 _ (hmem r hr)
  have hback : ∀ r, r < C.gates.length → ∀ i ∈ (gateAt C r).inputs, i < n + r :=
    fun r hr => hAO.2.1 r hr
  have htwo : ∀ r, r < C.gates.length → ∃ a b, (gateAt C r).inputs = [a, b] :=
    fun r hr => List.length_eq_two.mp (hAO.2.2 _ (hmem r hr))
  have hne : GateOp.and ≠ GateOp.or := by intro h; cases h
  set o := (if C.output < n then C.output else C.output + G0.length) with ho
  have hDD : D = Dc G0 C rho o := hD
  subst hDD
  have Cv : ∀ (x : Fin n → Bool) r, r < C.gates.length → ∀ a b,
      (gateAt C r).inputs = [a, b] →
      wireVal n C (n + r) x = (gateAt C r).op.eval [wireVal n C a x, wireVal n C b x] := by
    intro x r hr a b hab
    have ha := hback r hr a (by rw [hab]; simp)
    have hb := hback r hr b (by rw [hab]; simp)
    rw [wv_gate n C x r hr, hab]
    simp [ha, hb]
  -- reads of the rewired gates
  have rd_in : ∀ (x : Fin n → Bool) r, r < C.gates.length → ∀ i ∈ (gateAt C r).inputs,
      (∀ k < m, ¬ (NR k r ∧ i = n + u k)) → i < n →
      drd n G0 C rho o x r i = wireVal n C i x := by
    intro x r hr i hi hnn hin
    have hrho := hr1 r hr i hi hnn
    simp only [hin, ↓reduceIte] at hrho
    simp only [drd, hrho, show i < n + (G0.length + r) by omega, ↓reduceIte]
    rw [wv_input n _ x i hin, wv_input n C x i hin]
  have rd_gate : ∀ (x : Fin n → Bool) r, r < C.gates.length → ∀ i ∈ (gateAt C r).inputs,
      (∀ k < m, ¬ (NR k r ∧ i = n + u k)) → n ≤ i →
      drd n G0 C rho o x r i = wireVal n (Dc G0 C rho o) (n + G0.length + (i - n)) x := by
    intro x r hr i hi hnn hin
    have hrho := hr1 r hr i hi hnn
    have hlt := hback r hr i hi
    simp only [show ¬ i < n by omega, ↓reduceIte] at hrho
    simp only [drd, hrho, show i + G0.length < n + (G0.length + r) by omega, ↓reduceIte]
    congr 1
    omega
  have UA : ∀ (x : Fin n → Bool) r, r < C.gates.length →
      (∀ k < m, ∀ r', NR k r' → r' ≠ r ∧ ¬ InCone n C r' r) →
      wireVal n (Dc G0 C rho o) (n + G0.length + r) x = wireVal n C (n + r) x := by
    intro x r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr hU
      obtain ⟨a, b, hab⟩ := htwo r hr
      have hnn : ∀ i, ∀ k < m, ¬ (NR k r ∧ i = n + u k) := by
        intro i k hk h
        exact (hU k hk r h.1).1 rfl
      have key : ∀ i ∈ (gateAt C r).inputs, drd n G0 C rho o x r i = wireVal n C i x := by
        intro i hi
        by_cases hin : i < n
        · exact rd_in x r hr i hi (hnn i) hin
        · rw [rd_gate x r hr i hi (hnn i) (by omega)]
          have hlt := hback r hr i hi
          have hc : InCone n C (i - n) r :=
            inCone_read n C (i - n) r hr (by rw [show n + (i - n) = i by omega]; exact hi)
              (by omega)
          have := ih (i - n) (by omega) (by omega) (by
            intro k hk r' hr'
            obtain ⟨_, h2⟩ := hU k hk r' hr'
            refine ⟨?_, ?_⟩
            · intro h3
              rw [h3] at h2
              exact h2 hc
            · intro h3
              exact h2 (inCone_trans n C r' (i - n) r h3 hc))
          rw [this, show n + (i - n) = i by omega]
      rw [D_val2 n G0 C rho o x r hr a b hab, Cv x r hr a b hab,
        key a (by rw [hab]; simp), key b (by rw [hab]; simp)]
  have rd_nr : ∀ (x : Fin n → Bool) r k, k < m → NR k r →
      drd n G0 C rho o x r (n + u k) = P k x := by
    intro x r k hk hnr
    have hr : r < C.gates.length := ((hNR k r).mp hnr).1
    rcases hr2 r k hk hnr with ⟨hlt, hval⟩ | ⟨g9, hg9, hrho, hval, hU⟩ | ⟨hP0, hge⟩
    · simp only [drd, show rho r (n + u k) < n + (G0.length + r) by omega, ↓reduceIte]
      rw [D_prefix n G0 C rho o x _ hlt]
      exact hval x
    · simp only [drd, hrho, show n + G0.length + g9 < n + (G0.length + r) by omega,
        ↓reduceIte]
      rw [UA x g9 (by omega) hU]
      exact hval x
    · simp only [drd, show ¬ rho r (n + u k) < n + (G0.length + r) by omega, ↓reduceIte]
      exact (hP0 x).symm
  have cls : ∀ (x : Fin n → Bool) r, r < C.gates.length → ∀ i ∈ (gateAt C r).inputs,
      (∃ k < m, NR k r ∧ i = n + u k ∧ drd n G0 C rho o x r i = P k x) ∨
      (i < n ∧ drd n G0 C rho o x r i = wireVal n C i x) ∨
      (n ≤ i ∧ i - n < r ∧
        drd n G0 C rho o x r i = wireVal n (Dc G0 C rho o) (n + G0.length + (i - n)) x) := by
    intro x r hr i hi
    by_cases hN : ∃ k < m, NR k r ∧ i = n + u k
    · obtain ⟨k, hk, hnr, hik⟩ := hN
      refine Or.inl ⟨k, hk, hnr, hik, ?_⟩
      rw [hik]
      exact rd_nr x r k hk hnr
    · have hnn : ∀ k < m, ¬ (NR k r ∧ i = n + u k) := fun k hk h => hN ⟨k, hk, h.1, h.2⟩
      by_cases hin : i < n
      · exact Or.inr (Or.inl ⟨hin, rd_in x r hr i hi hnn hin⟩)
      · have hlt := hback r hr i hi
        exact Or.inr (Or.inr ⟨by omega, by omega, rd_gate x r hr i hi hnn (by omega)⟩)
  -- the OR trees
  have RL : ∀ k < m, ∀ g, Tr n C W u k g → ∀ r, r < C.gates.length →
      n + g ∈ (gateAt C r).inputs → r = T k ∨ Tr n C W u k r := by
    intro k hk g hg r hr hin
    rcases (h7 k hk g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).2 r hr hin with h | ⟨h1, h2⟩
    · exact Or.inl h
    · have hlt := hback r hr (n + g) hin
      exact Or.inr ⟨hr, h1, h2,
        inCone_trans n C (u k) g r hg.2.2.2 (inCone_read n C g r hr hin (by omega))⟩
  have NRor : ∀ k < m, ∀ r, NR k r → (gateAt C r).op = GateOp.or → Tr n C W u k r := by
    intro k hk r hnr hor
    obtain ⟨hr, hin, h⟩ := (hNR k r).mp hnr
    rcases h with h | ⟨h1, _⟩
    · rw [h] at hor
      exact absurd ((h6 k hk).2.2.1.symm.trans hor) hne
    · have hlt := hback r hr (n + u k) hin
      exact ⟨hr, h1, hor, inCone_read n C (u k) r hr hin (by omega)⟩
  have NRand : ∀ k < m, ∀ r, NR k r → (gateAt C r).op = GateOp.and → r = T k := by
    intro k hk r hnr hand
    obtain ⟨_, _, h⟩ := (hNR k r).mp hnr
    rcases h with h | ⟨_, h2⟩
    · exact h
    · exact absurd (hand.symm.trans h2) hne
  have other : ∀ k < m, ∀ a b, (gateAt C (T k)).inputs = [a, b] →
      (n ≤ a → b = z k) ∧ (n ≤ b → a = z k) := by
    intro k hk a b hab
    obtain ⟨_, _, _, hz, hT, _⟩ := h6 k hk
    rw [hab] at hT
    rcases hT with h | h
    · simp only [List.cons.injEq, and_true] at h
      obtain ⟨h1, h2⟩ := h
      exact ⟨fun _ => h2, fun h' => by omega⟩
    · simp only [List.cons.injEq, and_true] at h
      obtain ⟨h1, h2⟩ := h
      exact ⟨fun h' => by omega, fun _ => h1⟩
  -- a read of `u k` made true by `P k` together with `z k` gives an edge
  have Bad_q : ∀ x : Fin n → Bool, (∃ k < m, (∃ r, NR k r) ∧ P k x = true ∧
      wireVal n C (z k) x = true) → qH x = true := by
    rintro x ⟨k, hk, ⟨r, hnr⟩, hPk, hzk⟩
    obtain ⟨huk, hTk, hTand, hz, hT, hTq, _⟩ := h6 k hk
    rw [hP] at hPk
    obtain ⟨w1, hw1, hu⟩ := of_decide_eq_true hPk
    set e : Fin n → Bool := fun j1 => decide (j1 = w1 ∨ (j1 : ℕ) = z k) with he
    have hWe : wireVal n C (W k) e = true := by
      obtain ⟨hr, hin, h⟩ := (hNR k r).mp hnr
      rcases h with h | ⟨h1, h2⟩
      · rw [h] at hin
        rcases hT with h' | h' <;> rw [h'] at hin <;> simp only [List.mem_cons,
          List.not_mem_nil, or_false] at hin
        · rcases hin with h'' | h''
          · rw [← h'']; exact hu
          · omega
        · rcases hin with h'' | h''
          · omega
          · rw [← h'']; exact hu
      · apply orReaches_val n C e r (W k) h1
        have hlt := hback r hr (n + u k) hin
        rw [wv_gate n C e r hr, h2]
        simp only [GateOp.eval, List.any_map, List.any_eq_true]
        exact ⟨n + u k, hin, by simp [show n + u k < n + r by omega, hu]⟩
    have hze : wireVal n C (z k) e = true := by
      rw [wv_input n C e (z k) hz]
      simp [he]
    have hTe : wireVal n C (n + T k) e = true := by
      obtain ⟨a, b, hab⟩ := htwo (T k) hTk
      rw [Cv e (T k) hTk a b hab, hTand]
      rcases hT with h | h <;> rw [hab] at h <;> simp only [List.cons.injEq, and_true] at h <;>
        obtain ⟨h1, h2⟩ := h <;> rw [h1, h2] <;> simp [GateOp.eval, hWe, hze]
    obtain ⟨a0, b0, hadj, ha0, hb0⟩ := (hq e).mp (hTq e hTe)
    simp only [he, decide_eq_true_eq] at ha0 hb0
    have hxz : x ⟨z k, hz⟩ = true := by rw [← wv_input n C x (z k) hz]; exact hzk
    rw [hq]
    rcases ha0 with ha0 | ha0 <;> rcases hb0 with hb0 | hb0
    · rw [ha0, hb0] at hadj
      exact absurd hadj (H.irrefl)
    · have : b0 = ⟨z k, hz⟩ := Fin.ext hb0
      rw [ha0, this] at hadj
      exact ⟨w1, ⟨z k, hz⟩, hadj, hw1, hxz⟩
    · have : a0 = ⟨z k, hz⟩ := Fin.ext ha0
      rw [hb0, this] at hadj
      exact ⟨⟨z k, hz⟩, w1, hadj, hxz, hw1⟩
    · have : a0 = b0 := Fin.ext (ha0.trans hb0.symm)
      rw [this] at hadj
      exact absurd hadj (H.irrefl)
  -- D below the edge function, away from the bad inputs
  have Inv1 : ∀ x : Fin n → Bool, ¬ (∃ k < m, (∃ r, NR k r) ∧ P k x = true ∧
      wireVal n C (z k) x = true) → ∀ r, r < C.gates.length →
      wireVal n (Dc G0 C rho o) (n + G0.length + r) x = true →
      wireVal n C (n + r) x = true ∨
        ∃ k < m, (∃ r', NR k r') ∧ Tr n C W u k r ∧ P k x = true := by
    intro x hB r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr hd
      obtain ⟨a, b, hab⟩ := htwo r hr
      have hai : a ∈ (gateAt C r).inputs := by rw [hab]; simp
      have hbi : b ∈ (gateAt C r).inputs := by rw [hab]; simp
      rw [D_val2 n G0 C rho o x r hr a b hab] at hd
      rcases hop r hr with hand | hor
      · left
        rw [hand] at hd
        simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
          Bool.and_eq_true] at hd
        obtain ⟨hda, hdb⟩ := hd
        have key : ∀ i j, (i = a ∧ j = b ∨ i = b ∧ j = a) →
            drd n G0 C rho o x r i = true → drd n G0 C rho o x r j = true →
            wireVal n C i x = true := by
          intro i j hij hdi hdj
          have hii : i ∈ (gateAt C r).inputs := by
            rcases hij with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> assumption
          have hji : j ∈ (gateAt C r).inputs := by
            rcases hij with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> assumption
          have hoth : ∀ k < m, r = T k → n ≤ i → j = z k := by
            intro k hk hrT hni
            have hab' : (gateAt C (T k)).inputs = [a, b] := by rw [← hrT]; exact hab
            obtain ⟨o1, o2⟩ := other k hk a b hab'
            rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h2]; rw [h1] at hni; exact o1 hni
            · rw [h2]; rw [h1] at hni; exact o2 hni
          have hzj : ∀ k < m, j = z k → wireVal n C (z k) x = true := by
            intro k hk hj
            have hz := (h6 k hk).2.2.2.1
            rcases cls x r hr j hji with ⟨k', _, _, hj', _⟩ | ⟨_, h⟩ | ⟨hnj, _, _⟩
            · omega
            · rw [← hj, ← h]; exact hdj
            · omega
          rcases cls x r hr i hii with ⟨k, hk, hnr, hik, hv⟩ | ⟨_, hv⟩ | ⟨hni, hlt, hv⟩
          · exfalso
            have hrT := NRand k hk r hnr hand
            have hjz := hoth k hk hrT (by omega)
            exact hB ⟨k, hk, ⟨r, hnr⟩, by rw [← hv]; exact hdi, hzj k hk hjz⟩
          · rw [← hv]; exact hdi
          · rw [hv] at hdi
            rcases ih (i - n) hlt (by omega) hdi with h | ⟨k, hk, hex, hTr, hPk⟩
            · rwa [show n + (i - n) = i by omega] at h
            · exfalso
              rcases RL k hk (i - n) hTr r hr
                  (by rw [show n + (i - n) = i by omega]; exact hii) with hrT | hTr'
              · exact hB ⟨k, hk, hex, hPk, hzj k hk (hoth k hk hrT hni)⟩
              · exact hne (hand.symm.trans hTr'.2.2.1)
        rw [Cv x r hr a b hab, hand]
        simp [GateOp.eval, key a b (Or.inl ⟨rfl, rfl⟩) hda hdb,
          key b a (Or.inr ⟨rfl, rfl⟩) hdb hda]
      · rw [hor] at hd
        simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false,
          Bool.or_eq_true] at hd
        have key : ∀ i ∈ (gateAt C r).inputs, drd n G0 C rho o x r i = true →
            wireVal n C i x = true ∨
              ∃ k < m, (∃ r', NR k r') ∧ Tr n C W u k r ∧ P k x = true := by
          intro i hii hdi
          rcases cls x r hr i hii with ⟨k, hk, hnr, hik, hv⟩ | ⟨_, hv⟩ | ⟨hni, hlt, hv⟩
          · exact Or.inr ⟨k, hk, ⟨r, hnr⟩, NRor k hk r hnr hor, by rw [← hv]; exact hdi⟩
          · left; rw [← hv]; exact hdi
          · rw [hv] at hdi
            rcases ih (i - n) hlt (by omega) hdi with h | ⟨k, hk, hex, hTr, hPk⟩
            · left; rwa [show n + (i - n) = i by omega] at h
            · rcases RL k hk (i - n) hTr r hr
                  (by rw [show n + (i - n) = i by omega]; exact hii) with hrT | hTr'
              · rw [hrT] at hor
                exact absurd ((h6 k hk).2.2.1.symm.trans hor) hne
              · exact Or.inr ⟨k, hk, hex, hTr', hPk⟩
        have hC2 : ∀ i ∈ (gateAt C r).inputs, wireVal n C i x = true →
            wireVal n C (n + r) x = true := by
          intro i hii hci
          rw [Cv x r hr a b hab, hor]
          rw [hab] at hii
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
          rcases hii with h | h <;> rw [h] at hci <;> simp [GateOp.eval, hci]
        rcases hd with hda | hdb
        · rcases key a hai hda with h | h
          · exact Or.inl (hC2 a hai h)
          · exact Or.inr h
        · rcases key b hbi hdb with h | h
          · exact Or.inl (hC2 b hbi h)
          · exact Or.inr h
  -- D above the edge function at the inputs where each `P k` sees `u k`
  have Inv2 : ∀ x : Fin n → Bool, (∀ k < m, wireVal n C (z k) x = true →
      wireVal n C (n + u k) x = true → P k x = true) →
      ∀ r, r < C.gates.length → wireVal n C (n + r) x = true →
      wireVal n (Dc G0 C rho o) (n + G0.length + r) x = true ∨
        ∃ k < m, Tr n C W u k r ∧ wireVal n C (z k) x = false := by
    intro x hTP r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr hc
      obtain ⟨a, b, hab⟩ := htwo r hr
      have hai : a ∈ (gateAt C r).inputs := by rw [hab]; simp
      have hbi : b ∈ (gateAt C r).inputs := by rw [hab]; simp
      rw [Cv x r hr a b hab] at hc
      rcases hop r hr with hand | hor
      · left
        rw [hand] at hc
        simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
          Bool.and_eq_true] at hc
        obtain ⟨hca, hcb⟩ := hc
        have key : ∀ i j, (i = a ∧ j = b ∨ i = b ∧ j = a) →
            wireVal n C i x = true → wireVal n C j x = true →
            drd n G0 C rho o x r i = true := by
          intro i j hij hci hcj
          have hii : i ∈ (gateAt C r).inputs := by
            rcases hij with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> assumption
          have hoth : ∀ k < m, r = T k → n ≤ i → j = z k := by
            intro k hk hrT hni
            have hab' : (gateAt C (T k)).inputs = [a, b] := by rw [← hrT]; exact hab
            obtain ⟨o1, o2⟩ := other k hk a b hab'
            rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h2]; rw [h1] at hni; exact o1 hni
            · rw [h2]; rw [h1] at hni; exact o2 hni
          rcases cls x r hr i hii with ⟨k, hk, hnr, hik, hv⟩ | ⟨_, hv⟩ | ⟨hni, hlt, hv⟩
          · have hrT := NRand k hk r hnr hand
            have hjz := hoth k hk hrT (by omega)
            rw [hv]
            rw [hjz] at hcj
            rw [hik] at hci
            exact hTP k hk hcj hci
          · rw [hv]; exact hci
          · rw [hv]
            rcases ih (i - n) hlt (by omega) (by rwa [show n + (i - n) = i by omega])
              with h | ⟨k, hk, hTr, hzf⟩
            · exact h
            · exfalso
              rcases RL k hk (i - n) hTr r hr
                  (by rw [show n + (i - n) = i by omega]; exact hii) with hrT | hTr'
              · have hjz := hoth k hk hrT hni
                rw [hjz] at hcj
                rw [hcj] at hzf
                exact absurd hzf (by simp)
              · exact hne (hand.symm.trans hTr'.2.2.1)
        rw [D_val2 n G0 C rho o x r hr a b hab, hand]
        simp [GateOp.eval, key a b (Or.inl ⟨rfl, rfl⟩) hca hcb,
          key b a (Or.inr ⟨rfl, rfl⟩) hcb hca]
      · rw [hor] at hc
        simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false,
          Bool.or_eq_true] at hc
        have key : ∀ i ∈ (gateAt C r).inputs, wireVal n C i x = true →
            drd n G0 C rho o x r i = true ∨
              ∃ k < m, Tr n C W u k r ∧ wireVal n C (z k) x = false := by
          intro i hii hci
          rcases cls x r hr i hii with ⟨k, hk, hnr, hik, hv⟩ | ⟨_, hv⟩ | ⟨hni, hlt, hv⟩
          · have hTr := NRor k hk r hnr hor
            cases hzk : wireVal n C (z k) x
            · exact Or.inr ⟨k, hk, hTr, hzk⟩
            · left
              rw [hv]
              rw [hik] at hci
              exact hTP k hk hzk hci
          · left; rw [hv]; exact hci
          · rcases ih (i - n) hlt (by omega) (by rwa [show n + (i - n) = i by omega])
              with h | ⟨k, hk, hTr, hzf⟩
            · left; rw [hv]; exact h
            · rcases RL k hk (i - n) hTr r hr
                  (by rw [show n + (i - n) = i by omega]; exact hii) with hrT | hTr'
              · rw [hrT] at hor
                exact absurd ((h6 k hk).2.2.1.symm.trans hor) hne
              · exact Or.inr ⟨k, hk, hTr', hzf⟩
        have hD2 : ∀ i ∈ (gateAt C r).inputs, drd n G0 C rho o x r i = true →
            wireVal n (Dc G0 C rho o) (n + G0.length + r) x = true := by
          intro i hii hdi
          rw [D_val2 n G0 C rho o x r hr a b hab, hor]
          rw [hab] at hii
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
          rcases hii with h | h <;> rw [h] at hdi <;> simp [GateOp.eval, hdi]
        rcases hc with hca | hcb
        · rcases key a hai hca with h | h
          · exact Or.inl (hD2 a hai h)
          · exact Or.inr h
        · rcases key b hbi hcb with h | h
          · exact Or.inl (hD2 b hbi h)
          · exact Or.inr h
  -- the rewired gates are monotone
  have Mono : ∀ x x' : Fin n → Bool, (∀ j, x j = true → x' j = true) →
      ∀ r, r < C.gates.length →
      wireVal n (Dc G0 C rho o) (n + G0.length + r) x = true →
      wireVal n (Dc G0 C rho o) (n + G0.length + r) x' = true := by
    intro x x' hxx r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr hd
      obtain ⟨a, b, hab⟩ := htwo r hr
      have hai : a ∈ (gateAt C r).inputs := by rw [hab]; simp
      have hbi : b ∈ (gateAt C r).inputs := by rw [hab]; simp
      have key : ∀ i ∈ (gateAt C r).inputs, drd n G0 C rho o x r i = true →
          drd n G0 C rho o x' r i = true := by
        intro i hii hdi
        by_cases hN : ∃ k < m, NR k r ∧ i = n + u k
        · obtain ⟨k, hk, hnr, hik⟩ := hN
          rw [hik] at hdi ⊢
          rw [rd_nr x r k hk hnr, hP] at hdi
          rw [rd_nr x' r k hk hnr, hP]
          obtain ⟨w1, hw1, hu⟩ := of_decide_eq_true hdi
          exact decide_eq_true ⟨w1, hxx w1 hw1, hu⟩
        · have hnn : ∀ k < m, ¬ (NR k r ∧ i = n + u k) :=
            fun k hk h => hN ⟨k, hk, h.1, h.2⟩
          by_cases hin : i < n
          · rw [rd_in x r hr i hii hnn hin, wv_input n C x i hin] at hdi
            rw [rd_in x' r hr i hii hnn hin, wv_input n C x' i hin]
            exact hxx _ hdi
          · have hlt := hback r hr i hii
            rw [rd_gate x r hr i hii hnn (by omega)] at hdi
            rw [rd_gate x' r hr i hii hnn (by omega)]
            exact ih (i - n) (by omega) (by omega) hdi
      rw [D_val2 n G0 C rho o x r hr a b hab] at hd
      rw [D_val2 n G0 C rho o x' r hr a b hab]
      rcases hop r hr with h | h <;> rw [h] at hd ⊢ <;> simp [GateOp.eval] at hd ⊢
      · exact ⟨key a hai hd.1, key b hbi hd.2⟩
      · rcases hd with hd | hd
        · exact Or.inl (key a hai hd)
        · exact Or.inr (key b hbi hd)
  -- the output
  have Ceval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = wireVal n C C.output x :=
    fun x => rfl
  show (Dc G0 C rho o).eval (List.ofFn y) = qH y
  show wireVal n (Dc G0 C rho o) o y = qH y
  rcases Nat.lt_or_ge C.output n with hlt | hge
  · have hoeq : o = C.output := by simp [ho, hlt]
    rw [hoeq, wv_input n _ y _ hlt, ← hC y, Ceval, wv_input n C y _ hlt]
  · have hoeq : o = n + G0.length + (C.output - n) := by
      simp only [ho, show ¬ C.output < n by omega, ↓reduceIte]
      omega
    rw [hoeq]
    rcases Nat.lt_or_ge (C.output - n) C.gates.length with hlo | hgo
    · apply Bool.eq_iff_iff.mpr
      constructor
      · intro hd
        by_cases hB : ∃ k < m, (∃ r, NR k r) ∧ P k y = true ∧ wireVal n C (z k) y = true
        · exact Bad_q y hB
        · rcases Inv1 y hB (C.output - n) hlo hd with h | ⟨k, hk, _, hTr, _⟩
          · rw [← hC y, Ceval, show C.output = n + (C.output - n) by omega]
            exact h
          · exact absurd (show C.output = n + (C.output - n) by omega)
              ((h7 k hk _ hTr.1 hTr.2.1 hTr.2.2.1 hTr.2.2.2).1)
      · intro hqy
        obtain ⟨a0, b0, hadj, ha0, hb0⟩ := (hq y).mp hqy
        set e : Fin n → Bool := fun j => decide (j = a0 ∨ j = b0) with he
        have hqe : qH e = true := (hq e).mpr ⟨a0, b0, hadj, by simp [he], by simp [he]⟩
        have hce : wireVal n C (n + (C.output - n)) e = true := by
          rw [show n + (C.output - n) = C.output by omega, ← Ceval, hC e]
          exact hqe
        have hTP : ∀ k < m, wireVal n C (z k) e = true → wireVal n C (n + u k) e = true →
            P k e = true := by
          intro k hk hze hue
          have hz := (h6 k hk).2.2.2.1
          rw [wv_input n C e (z k) hz] at hze
          simp only [he, decide_eq_true_eq] at hze
          rw [hP]
          apply decide_eq_true
          rcases hze with h | h
          · refine ⟨b0, by simp [he], ?_⟩
            have hfe : (fun j1 : Fin n => decide (j1 = b0 ∨ (j1 : ℕ) = z k)) = e := by
              funext j
              simp only [he]
              rw [← h]
              simp only [Fin.ext_iff]
              try simp only [decide_eq_decide]
              try tauto
            rw [hfe]
            exact hue
          · refine ⟨a0, by simp [he], ?_⟩
            have hfe : (fun j1 : Fin n => decide (j1 = a0 ∨ (j1 : ℕ) = z k)) = e := by
              funext j
              simp only [he]
              rw [← h]
              simp only [Fin.ext_iff]
              try simp only [decide_eq_decide]
              try tauto
            rw [hfe]
            exact hue
        rcases Inv2 e hTP (C.output - n) hlo hce with h | ⟨k, hk, hTr, _⟩
        · refine Mono e y ?_ (C.output - n) hlo h
          intro j hj
          simp only [he, decide_eq_true_eq] at hj
          rcases hj with hj | hj <;> rw [hj] <;> assumption
        · exact absurd (show C.output = n + (C.output - n) by omega)
            ((h7 k hk _ hTr.1 hTr.2.1 hTr.2.2.1 hTr.2.2.2).1)
    · rw [wv_ge n _ y _ (by simp [Dc]; omega), ← hC y, Ceval, wv_ge n C y _ (by omega)]

end PEqualNP.Outside.L_meta_3545

theorem PEqualNP.Outside.L_meta_3545 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 :=
  PEqualNP.Outside.L_meta_3545.core
