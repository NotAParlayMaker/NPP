import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

namespace L3543_prefix

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_gate (gs : List Gate) (w : List Bool) (r : ℕ) (hr : r < gs.length) :
    (gs.foldl step w).getD (w.length + r) false =
      (gateAt ⟨gs, 0⟩ r).op.eval ((gateAt ⟨gs, 0⟩ r).inputs.map fun i =>
        if i < w.length + r then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w r with
  | nil => simp at hr
  | cons g gs ih =>
    cases r with
    | zero =>
      rw [List.foldl_cons]
      rw [show w.length + 0 = w.length by rfl,
        foldl_getD_lt gs (step w g) w.length (by simp [step])]
      have hv : (step w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by simp [step]
      rw [hv]
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        Option.getD_some]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · simp only [hi, ↓reduceIte]
        have h2 : (step w g).getD i false = w.getD i false := by
          simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        exact h2.symm.trans (foldl_getD_lt gs (step w g) i (by simp [step]; omega)).symm
      · simp only [hi, ↓reduceIte]
        simp [List.getElem?_eq_none (Nat.le_of_not_lt hi)]
    | succ r =>
      rw [List.foldl_cons]
      have hr' : r < gs.length := by simpa using hr
      have h := ih (step w g) r hr'
      have he : w.length + (r + 1) = (step w g).length + r := by simp [step]; omega
      rw [he]
      simpa only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        Option.getD_some] using h

lemma wireVal_length (n : ℕ) (C : Circuit) (y : Fin n → Bool) :
    (C.wires (List.ofFn y)).length = n + C.gates.length := by
  change (C.gates.foldl step (List.ofFn y)).length = _
  rw [foldl_length, List.length_ofFn]

lemma wireVal_input (n : ℕ) (C : Circuit) (y : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i y = y ⟨i, hi⟩ := by
  unfold wireVal
  change (C.gates.foldl step (List.ofFn y)).getD i false = _
  rw [foldl_getD_lt _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma wireVal_gate (n : ℕ) (C : Circuit) (y : Fin n → Bool) (r : ℕ)
    (hr : r < C.gates.length) :
    wireVal n C (n + r) y = (gateAt C r).op.eval ((gateAt C r).inputs.map fun i =>
      if i < n + r then wireVal n C i y else false) := by
  have h := foldl_gate C.gates (List.ofFn y) r hr
  change (C.gates.foldl step (List.ofFn y)).getD (n + r) false =
    (gateAt C r).op.eval ((gateAt C r).inputs.map fun i =>
      if i < n + r then (C.gates.foldl step (List.ofFn y)).getD i false else false)
  simpa only [List.length_ofFn, gateAt] using h

lemma gateAt_append_mapIdx (pre gs : List Gate) (f : ℕ → Gate → Gate)
    (r : ℕ) (hr : r < gs.length) :
    gateAt ⟨pre ++ gs.mapIdx f, 0⟩ (pre.length + r) = f r (gateAt ⟨gs, 0⟩ r) := by
  have hlen : pre.length + r < (pre ++ gs.mapIdx f).length := by
    simp only [List.length_append, List.length_mapIdx]
    omega
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ (by simpa using hr)]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, List.getElem_mapIdx]

lemma wireVal_eq_false (n : ℕ) (C : Circuit) (y : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : wireVal n C i y = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn y)).length ≤ i := by
    simpa only [wireVal_length] using hi
  rw [List.getElem?_eq_none hlen]
  rfl

lemma prepend_mapIdx_gate (n : ℕ) (y : Fin n → Bool) (G0 : List Gate)
    (C : Circuit) (rho : ℕ → ℕ → ℕ) (r : ℕ) (hr : r < C.gates.length)
    (hback : ∀ i ∈ (gateAt C r).inputs, i < n + r)
    (hsafe : ∀ i ∈ (gateAt C r).inputs,
      rho r i < n + G0.length + r ∨
        (wireVal n C i y = false ∧ wireVal n ⟨G0 ++ C.gates.mapIdx
          (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)), 0⟩
          (rho r i) y = false))
    (hval : ∀ i ∈ (gateAt C r).inputs,
      wireVal n C i y = wireVal n ⟨G0 ++ C.gates.mapIdx
        (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)), 0⟩
        (rho r i) y) :
    wireVal n ⟨G0 ++ C.gates.mapIdx
      (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)), 0⟩
      (n + G0.length + r) y = wireVal n C (n + r) y := by
  let D : Circuit := ⟨G0 ++ C.gates.mapIdx
    (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)), 0⟩
  change wireVal n D (n + G0.length + r) y = wireVal n C (n + r) y
  have hDr : G0.length + r < D.gates.length := by
    simp only [D, List.length_append, List.length_mapIdx]
    omega
  rw [show n + G0.length + r = n + (G0.length + r) by omega,
    wireVal_gate n D y (G0.length + r) hDr,
    gateAt_append_mapIdx G0 C.gates
      (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)) r hr,
    wireVal_gate n C y r hr]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  change (if rho r i < n + (G0.length + r) then wireVal n D (rho r i) y else false) =
    if i < n + r then wireVal n C i y else false
  have hb : i < n + r := hback i hi
  by_cases ht : rho r i < n + (G0.length + r)
  · simp only [ht, hb, ↓reduceIte]
    simpa only [Nat.add_assoc, D] using (hval i hi).symm
  · have hf := (hsafe i hi).resolve_left (by simpa only [Nat.add_assoc] using ht)
    simp only [ht, hb, ↓reduceIte, hf.1]

/-- Prepending gates and remapping each old gate preserves the circuit semantics.
The safety condition either keeps redirected reads before their gate or makes both reads false. -/
lemma prepend_mapIdx_eval_aux
    (n : ℕ) (y : Fin n → Bool) (G0 : List Gate)
    (C D : Circuit) (rho : ℕ → ℕ → ℕ)
    (_hG0 : ∀ i < G0.length,
      ∀ w ∈ (G0.getD i ⟨GateOp.or, []⟩).inputs, w < n + i)
    (hD : D = ⟨G0 ++ C.gates.mapIdx
      (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)),
      if C.output < n then C.output else C.output + G0.length⟩)
    (hback : ∀ r < C.gates.length,
      ∀ i ∈ (gateAt C r).inputs, i < n + r)
    (hsafe : ∀ r < C.gates.length,
      ∀ i ∈ (gateAt C r).inputs,
        rho r i < n + G0.length + r ∨
          (wireVal n C i y = false ∧ wireVal n D (rho r i) y = false))
    (hval : ∀ r < C.gates.length,
      ∀ i ∈ (gateAt C r).inputs,
        wireVal n C i y = wireVal n D (rho r i) y) :
    D.eval (List.ofFn y) = C.eval (List.ofFn y) := by
  subst D
  let D0 : Circuit := ⟨G0 ++ C.gates.mapIdx
    (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)),
    if C.output < n then C.output else C.output + G0.length⟩
  change D0.eval (List.ofFn y) = C.eval (List.ofFn y)
  unfold Circuit.eval
  change (D0.wires (List.ofFn y)).getD
    (if C.output < n then C.output else C.output + G0.length) false =
    (C.wires (List.ofFn y)).getD C.output false
  by_cases ho : C.output < n
  · simp only [ho, ↓reduceIte]
    change wireVal n D0 C.output y = wireVal n C C.output y
    rw [wireVal_input n D0 y C.output ho, wireVal_input n C y C.output ho]
  · simp only [ho, ↓reduceIte]
    change wireVal n D0 (C.output + G0.length) y = wireVal n C C.output y
    by_cases hr : C.output - n < C.gates.length
    · have he : C.output = n + (C.output - n) := by omega
      rw [he]
      have hg := prepend_mapIdx_gate n y G0 C rho (C.output - n) hr
        (hback (C.output - n) hr) (hsafe (C.output - n) hr)
        (hval (C.output - n) hr)
      change wireVal n ⟨G0 ++ C.gates.mapIdx
        (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)), 0⟩
        (n + G0.length + (C.output - n)) y = wireVal n C (n + (C.output - n)) y at hg
      have he2 : n + (C.output - n) + G0.length =
          n + G0.length + (C.output - n) := by omega
      rw [he2]
      simpa only [D0, wireVal, Circuit.wires] using hg
    · have hC : n + C.gates.length ≤ C.output := by omega
      have hD0 : n + D0.gates.length ≤ C.output + G0.length := by
        simp only [D0, List.length_append, List.length_mapIdx]
        omega
      rw [wireVal_eq_false n C y C.output hC,
        wireVal_eq_false n D0 y (C.output + G0.length) hD0]

/-- Prepending gates and remapping each old gate preserves the circuit semantics.
The safety condition either keeps redirected reads before their gate or makes both reads false. -/
theorem prepend_mapIdx_eval
    (n : ℕ) (y : Fin n → Bool) (G0 : List Gate)
    (C D : Circuit) (rho : ℕ → ℕ → ℕ)
    (_hG0 : ∀ i < G0.length,
      ∀ w ∈ (G0.getD i ⟨GateOp.or, []⟩).inputs, w < n + i)
    (hD : D = ⟨G0 ++ C.gates.mapIdx
      (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)),
      if C.output < n then C.output else C.output + G0.length⟩)
    (hback : ∀ r < C.gates.length,
      ∀ i ∈ (gateAt C r).inputs, i < n + r)
    (hsafe : ∀ r < C.gates.length,
      ∀ i ∈ (gateAt C r).inputs,
        rho r i < n + G0.length + r ∨
          (wireVal n C i y = false ∧ wireVal n D (rho r i) y = false))
    (hval : ∀ r < C.gates.length,
      ∀ i ∈ (gateAt C r).inputs,
        wireVal n C i y = wireVal n D (rho r i) y) :
    D.eval (List.ofFn y) = C.eval (List.ofFn y) := by
  exact prepend_mapIdx_eval_aux n y G0 C D rho _hG0 hD hback hsafe hval

open PEqualNP.EdgeOwnership

lemma cones_append_singleton (n : ℕ) (gs : List Gate) (g : Gate) (out : ℕ) :
    cones n ⟨gs ++ [g], out⟩ = coneStep n (cones n ⟨gs, out⟩) g := by
  simp [cones, List.foldl_append]

lemma conesFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma inCone_of_direct_input_list (n : ℕ) (gs : List Gate) (out r i : ℕ)
    (hr : r < gs.length) (hi : i ∈ (gateAt ⟨gs, out⟩ r).inputs)
    (hn : n ≤ i) (hb : i < n + r) : InCone n ⟨gs, out⟩ (i - n) r := by
  unfold InCone
  induction gs using List.reverseRecOn generalizing r i with
  | nil => simp at hr
  | append_singleton gs g ih =>
    rcases Nat.lt_or_ge r gs.length with h | h
    · have hi' : i ∈ (gateAt ⟨gs, out⟩ r).inputs := by
        simpa only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left h] using hi
      have hc : r < (cones n ⟨gs, out⟩).length := by
        change r < (gs.foldl (coneStep n) []).length
        rw [conesFold_length]
        simpa using h
      simpa only [cones_append_singleton, coneStep, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hc] using ih r i h hi' hn hb
    · have hr' : r = gs.length := by simp only [List.length_append, List.length_singleton] at hr; omega
      subst r
      have hg : gateAt ⟨gs ++ [g], out⟩ gs.length = g := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      rw [hg] at hi
      change (i - n) ∈ (cones n ⟨gs ++ [g], out⟩).getD gs.length []
      simp only [cones, List.foldl_append, List.foldl_cons, List.foldl_nil,
        coneStep, List.getD_eq_getElem?_getD]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
        rw [conesFold_length]; simp
      rw [List.getElem?_append_right (by omega)]
      rw [hlen]
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
        List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
      refine ⟨i, ?_, ?_⟩
      · exact ⟨hi, hn, hb⟩
      · simp

lemma inCone_of_direct_input {n : ℕ} {C : Circuit} {r i : ℕ}
    (hr : r < C.gates.length) (hi : i ∈ (gateAt C r).inputs)
    (hn : n ≤ i) (hb : i < n + r) : InCone n C (i - n) r :=
  inCone_of_direct_input_list n C.gates C.output r i hr hi hn hb

lemma prepend_wireVal_lt (n : ℕ) (y : Fin n → Bool) (G0 gs : List Gate) (i : ℕ)
    (hi : i < n + G0.length) :
    wireVal n ⟨G0 ++ gs, 0⟩ i y = wireVal n ⟨G0, 0⟩ i y := by
  unfold wireVal Circuit.wires
  rw [List.foldl_append]
  exact foldl_getD_lt gs ((⟨G0, 0⟩ : Circuit).wires (List.ofFn y)) i
    (by simpa only [L3543_prefix.wireVal_length] using hi)

lemma inCone_of_cone_of_direct_list (n : ℕ) (gs : List Gate) (out i j r : ℕ)
    (hcone : InCone n ⟨gs, out⟩ i j) (hr : r < gs.length)
    (hj : n + j ∈ (gateAt ⟨gs, out⟩ r).inputs) (hb : n + j < n + r) :
    InCone n ⟨gs, out⟩ i r := by
  unfold InCone at hcone ⊢
  induction gs using List.reverseRecOn generalizing i j r with
  | nil => simp at hr
  | append_singleton gs g ih =>
    have hjlen : j < gs.length := by
      simp only [List.length_append, List.length_singleton] at hr
      omega
    have hjcones : j < (cones n ⟨gs, out⟩).length := by
      change j < (gs.foldl (coneStep n) []).length
      rw [conesFold_length]
      simpa using hjlen
    have hcone' : i ∈ (cones n ⟨gs, out⟩).getD j [] := by
      simpa only [cones_append_singleton, coneStep, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hjcones] using hcone
    rcases Nat.lt_or_ge r gs.length with h | h
    · have hj' : n + j ∈ (gateAt ⟨gs, out⟩ r).inputs := by
        simpa only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left h] using hj
      have hc : r < (cones n ⟨gs, out⟩).length := by
        change r < (gs.foldl (coneStep n) []).length
        rw [conesFold_length]
        simpa using h
      simpa only [cones_append_singleton, coneStep, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hc] using ih i j r hcone' h hj' hb
    · have hr' : r = gs.length := by simp only [List.length_append, List.length_singleton] at hr; omega
      subst r
      have hg : gateAt ⟨gs ++ [g], out⟩ gs.length = g := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      rw [hg] at hj
      change i ∈ (cones n ⟨gs ++ [g], out⟩).getD gs.length []
      simp only [cones_append_singleton, coneStep, List.getD_eq_getElem?_getD]
      have hlen : (cones n ⟨gs, out⟩).length = gs.length := by
        change (gs.foldl (coneStep n) []).length = gs.length
        rw [conesFold_length]; simp
      rw [List.getElem?_append_right (by omega), hlen]
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
        List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
      refine ⟨n + j, ?_, ?_⟩
      · exact ⟨hj, by omega, hb⟩
      · simp only [Nat.add_sub_cancel_left, List.mem_cons]
        exact Or.inr hcone'

lemma inCone_of_cone_of_direct {n : ℕ} {C : Circuit} {i j r : ℕ}
    (hcone : InCone n C i j) (hr : r < C.gates.length)
    (hj : n + j ∈ (gateAt C r).inputs) (hb : n + j < n + r) : InCone n C i r :=
  inCone_of_cone_of_direct_list n C.gates C.output i j r hcone hr hj hb

end L3543_prefix

namespace L3543NarrowDirect

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma ao2_of_isAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  intro j hj
  have hg := gateAt_mem C j hj
  refine ⟨h.1 _ hg, ?_, h.2.1 j hj⟩
  obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C j).inputs = [a, b] :=
    List.length_eq_two.mp (h.2.2 _ hg)
  exact ⟨a, b, hab⟩

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    wireVal n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (wireVal n C · x)) := by
  have h := L3543_prefix.foldl_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  change (C.gates.foldl L3543_prefix.step (List.ofFn x)).getD (n + j) false = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [(hC j hj).2.2 i hi, ↓reduceIte]
  rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := L3543_prefix.wireVal_input n C x w hw

lemma wv_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wireVal n C w x = false :=
  L3543_prefix.wireVal_eq_false n C x w hw

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma wv_mono (n : ℕ) (C : Circuit) (hC : AO2 n C) (x y : Fin n → Bool)
    (hxy : x ≤ y) : ∀ w, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn] at hw
      rw [wv_input n C y w hwn]
      exact hxy _ hw
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k < C.gates.length
      · rw [wv_rec n C x hC k hk] at hw
        rw [wv_rec n C y hC k hk]
        obtain ⟨hop, hab, hlt⟩ := hC k hk
        obtain ⟨a, b, hab⟩ := hab
        rw [hab] at hw ⊢ hlt
        have ha_lt : a < n + k := hlt a (by simp)
        have hb_lt : b < n + k := hlt b (by simp)
        rcases hop with hop | hop
        · rw [hop] at hw ⊢
          rw [eval_and_pair] at hw ⊢
          rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hw
          rcases hw with ⟨ha, hb⟩
          have hia := ih a (by omega) ha
          have hib := ih b (by omega) hb
          simp [hia, hib]
        · rw [hop] at hw ⊢
          rw [eval_or_pair] at hw ⊢
          rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hw
          rcases hw with ha | hb
          · have hia := ih a (by omega) ha
            simp [hia]
          · have hib := ih b (by omega) hb
            simp [hib]
      · rw [wv_ge n C x (n + k) (by omega)] at hw
        cases hw

def star (n : ℕ) (C : Circuit) (u z : ℕ) (x : Fin n → Bool) : Bool :=
  decide (∃ w : Fin n, x w = true ∧
    wireVal n C (n + u) (fun j : Fin n => decide (j = w ∨ (j : ℕ) = z)) = true)

lemma star_mono (n : ℕ) (C : Circuit) (u z : ℕ) (x y : Fin n → Bool)
    (hxy : x ≤ y) : star n C u z x = true → star n C u z y = true := by
  simp only [star, decide_eq_true_eq]
  rintro ⟨w, hw, hu⟩
  exact ⟨w, hxy w hw, hu⟩

lemma pair_le (n z : ℕ) (hz : z < n) (w : Fin n) (x : Fin n → Bool)
    (hw : x w = true) (hxz : x ⟨z, hz⟩ = true) :
    (fun j : Fin n => decide (j = w ∨ (j : ℕ) = z)) ≤ x := by
  intro j
  by_cases hjw : j = w
  · subst j; intro _; exact hw
  · by_cases hjz : (j : ℕ) = z
    · have hje : j = ⟨z, hz⟩ := Fin.ext hjz
      subst j; intro _; exact hxz
    · simp [hjw, hjz]

lemma star_le (n : ℕ) (C : Circuit) (hC : AO2 n C) (u z : ℕ) (hz : z < n)
    (x : Fin n → Bool) (hxz : x ⟨z, hz⟩ = true) :
    star n C u z x = true → wireVal n C (n + u) x = true := by
  simp only [star, decide_eq_true_eq]
  rintro ⟨w, hw, hu⟩
  exact wv_mono n C hC _ x (pair_le n z hz w x hw hxz) (n + u) hu

lemma star_pair_right (n : ℕ) (C : Circuit) (hC : AO2 n C) (u : ℕ) (a b : Fin n) :
    star n C u b.val (pairInput a b) = true ↔ wireVal n C (n + u) (pairInput a b) = true := by
  constructor
  · intro h
    exact star_le n C hC u b.val b.isLt (pairInput a b) (by simp [pairInput]) h
  · intro hu
    simp only [star, decide_eq_true_eq]
    refine ⟨a, by simp [pairInput], ?_⟩
    have heq : (fun j : Fin n => decide (j = a ∨ (j : ℕ) = b.val)) = pairInput a b := by
      funext j
      simp only [pairInput]
      tauto
    rw [heq]
    exact hu

end L3543NarrowDirect

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_3543 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → m = 1 → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H qH C m u T W z NR P G0 rho D hq hAO hC hNR hP hspec
    hclosure hpair hG0 hD hrho hmap hm y
  subst m
  have hback : ∀ r < C.gates.length,
      ∀ i ∈ (gateAt C r).inputs, i < n + r := hAO.2.1
  have hAO2 : L3543NarrowDirect.AO2 n C := L3543NarrowDirect.ao2_of_isAO2 n C hAO
  have hs0 := hspec 0 (by omega)
  have hTlen : T 0 < C.gates.length := hs0.2.1
  have hTin : (gateAt C (T 0)).inputs = [W 0, z 0] ∨
      (gateAt C (T 0)).inputs = [z 0, W 0] := hs0.2.2.2.2.1
  have hz : z 0 < n := hs0.2.2.2.1
  have hTop : (gateAt C (T 0)).op = GateOp.and := hs0.2.2.1
  let D0 : Circuit := ⟨G0 ++ C.gates.mapIdx
    (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)), 0⟩
  have hDg : D.gates = D0.gates := by rw [hD]
  have hDw : ∀ (x : Fin n → Bool) (w : ℕ),
      wireVal n D w x = wireVal n D0 w x := by
    intro x w
    unfold wireVal Circuit.wires
    rw [hDg]
  have hDlen : D0.gates.length = G0.length + C.gates.length := by
    simp [D0]
  have hDout : D.output = if C.output < n then C.output else C.output + G0.length := by rw [hD]
  let dread (x : Fin n → Bool) (r i : ℕ) : Bool :=
    if rho r i < n + (G0.length + r) then wireVal n D (rho r i) x else false
  have hDrec (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length) :
      wireVal n D (n + G0.length + r) x =
        (gateAt C r).op.eval ((gateAt C r).inputs.map (dread x r)) := by
    have hdr : G0.length + r < D.gates.length := by rw [hDg, hDlen]; omega
    have hgateD : gateAt D (G0.length + r) = gateAt D0 (G0.length + r) := by
      unfold gateAt
      rw [hDg]
    rw [show n + G0.length + r = n + (G0.length + r) by omega,
      L3543_prefix.wireVal_gate n D x (G0.length + r) hdr, hgateD,
      L3543_prefix.gateAt_append_mapIdx G0 C.gates
        (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)) r hr]
    simp only [List.map_map]
    rfl
  have hrhoOrd (r : ℕ) (hr : r < C.gates.length) (i : ℕ)
      (hi : i ∈ (gateAt C r).inputs) (hno : ∀ k < 1, ¬ (NR k r ∧ i = n + u k)) :
      rho r i = if i < n then i else i + G0.length :=
    hrho r hr i hi hno
  have hord (r : ℕ) (hr : r < C.gates.length) (i : ℕ)
      (hi : i ∈ (gateAt C r).inputs) (hno : ¬ (NR 0 r ∧ i = n + u 0)) :
      rho r i = if i < n then i else i + G0.length := by
    apply hrhoOrd r hr i hi
    intro k hk h
    have hk0 : k = 0 := by omega
    subst k
    exact hno h
  have hP0 (x : Fin n → Bool) : P 0 x = L3543NarrowDirect.star n C (u 0) (z 0) x := hP 0 x
  let Branch : ℕ → Prop := fun r =>
    r = T 0 ∨ (OrReaches n C (W 0) r ∧ (gateAt C r).op = GateOp.or ∧ InCone n C (u 0) r)
  have hreaderBranch (r : ℕ) (hr : r < C.gates.length) (i : ℕ)
      (hi : i ∈ (gateAt C r).inputs) (hnr : NR 0 r ∧ i = n + u 0) : Branch r := by
    rcases (hNR 0 r).mp hnr.1 with ⟨_, _, hc⟩
    rcases hc with ht | ⟨hreach, hop⟩
    · exact Or.inl ht
    · refine Or.inr ⟨hreach, hop, ?_⟩
      have hc := L3543_prefix.inCone_of_direct_input hr hi (by omega) (hback r hr i hi)
      rwa [hnr.2, Nat.add_sub_cancel_left] at hc
  have hbranchStep (r j : ℕ) (hr : r < C.gates.length) (hj : j < C.gates.length)
      (hread : n + j ∈ (gateAt C r).inputs)
      (hbj : OrReaches n C (W 0) j ∧ (gateAt C j).op = GateOp.or ∧ InCone n C (u 0) j) :
      Branch r := by
    have hc := hclosure 0 (by omega) j hj hbj.1 hbj.2.1 hbj.2.2
    rcases hc.2 r hr hread with ht | ⟨hreach, hop⟩
    · exact Or.inl ht
    · refine Or.inr ⟨hreach, hop, ?_⟩
      exact L3543_prefix.inCone_of_cone_of_direct hbj.2.2 hr hread (hback r hr _ hread)
  have hCTfalse (x : Fin n → Bool) (hx : x ⟨z 0, hz⟩ = false) :
      wireVal n C (n + T 0) x = false := by
    rw [L3543NarrowDirect.wv_rec n C x hAO2 (T 0) hTlen, hTop]
    rcases hTin with hin | hin <;> rw [hin] <;>
      simp [GateOp.eval, L3543NarrowDirect.wv_input n C x (z 0) hz, hx]
  have hDTfalse (x : Fin n → Bool) (hx : x ⟨z 0, hz⟩ = false) :
      wireVal n D (n + G0.length + T 0) x = false := by
    rw [hDrec x (T 0) hTlen, hTop]
    have hzrho : rho (T 0) (z 0) = z 0 := by
      rw [hord (T 0) hTlen (z 0)
        (by rcases hTin with h | h <;> simp [h]) (by intro hs; omega)]
      simp [hz]
    rcases hTin with hin | hin <;> rw [hin] <;>
      simp [GateOp.eval, dread, hzrho,
        L3543NarrowDirect.wv_input n D x (z 0) hz, hx]
  have heq_noz (x : Fin n → Bool) (hx : x ⟨z 0, hz⟩ = false) : D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    have hgood : ∀ r, r < C.gates.length →
        wireVal n D (n + G0.length + r) x = true →
          wireVal n C (n + r) x = true ∨ Branch r := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro hr hdr
        have hdout : wireVal n D (n + G0.length + r) x = true := hdr
        obtain ⟨hop, hab, _⟩ := hAO2 r hr
        obtain ⟨a, b, hab⟩ := hab
        rw [hDrec x r hr, hab] at hdr
        rcases hop with hop | hop
        · have hdrp : dread x r a = true ∧ dread x r b = true := by
            simpa only [hop, L3543NarrowDirect.eval_and_pair, Bool.and_eq_true] using hdr
          have hinput : ∀ i ∈ (gateAt C r).inputs,
              dread x r i = true → wireVal n C i x = true := by
            intro i hi hdi
            by_cases hs : NR 0 r ∧ i = n + u 0
            · have hb := hreaderBranch r hr i hi hs
              rcases hb with ht | ⟨_, hor, _⟩
              · subst r
                exact False.elim (Bool.false_ne_true ((hDTfalse x hx).symm.trans hdout))
              · exact GateOp.noConfusion (hor.symm.trans hop)
            · have hguard : rho r i < n + (G0.length + r) := by
                by_contra hg
                simp [dread, hg] at hdi
              have hdiw : wireVal n D (rho r i) x = true := by
                simpa only [dread, hguard, ↓reduceIte] using hdi
              rw [hord r hr i hi hs] at hdiw
              by_cases hin : i < n
              · simp only [hin, ↓reduceIte] at hdiw
                rw [L3543NarrowDirect.wv_input n C x i hin]
                simpa only [L3543NarrowDirect.wv_input n D x i hin] using hdiw
              · simp only [hin, ↓reduceIte] at hdiw
                have hb := hback r hr i hi
                have hj : i - n < r := by omega
                have hjlen : i - n < C.gates.length := by omega
                have he : i + G0.length = n + G0.length + (i - n) := by omega
                have hdi' : wireVal n D (n + G0.length + (i - n)) x = true := by
                  simpa only [he] using hdiw
                rcases ih (i - n) hj hjlen hdi' with hcj | hbj
                · rwa [show i = n + (i - n) by omega]
                · rcases hbj with ht | hbj
                  · rw [ht] at hdi'
                    exact False.elim (Bool.false_ne_true ((hDTfalse x hx).symm.trans hdi'))
                  · have hb' := hbranchStep r (i - n) hr hjlen
                      (by
                        have heq : n + (i - n) = i := by omega
                        rwa [heq]) hbj
                    rcases hb' with ht | ⟨_, hor, _⟩
                    · subst r
                      exact False.elim (Bool.false_ne_true ((hDTfalse x hx).symm.trans hdout))
                    · exact GateOp.noConfusion (hor.symm.trans hop)
          rw [L3543NarrowDirect.wv_rec n C x hAO2 r hr, hop, hab,
            L3543NarrowDirect.eval_and_pair, Bool.and_eq_true]
          exact Or.inl ⟨hinput a (by simp [hab]) hdrp.1,
            hinput b (by simp [hab]) hdrp.2⟩
        · have hdro : dread x r a = true ∨ dread x r b = true := by
            simpa only [hop, L3543NarrowDirect.eval_or_pair, Bool.or_eq_true] using hdr
          have horInput : ∀ i ∈ (gateAt C r).inputs,
              dread x r i = true →
                wireVal n C (n + r) x = true ∨ Branch r := by
            intro i hi hdi
            by_cases hs : NR 0 r ∧ i = n + u 0
            · exact Or.inr (hreaderBranch r hr i hi hs)
            · have hguard : rho r i < n + (G0.length + r) := by
                by_contra hg
                simp [dread, hg] at hdi
              have hdiw : wireVal n D (rho r i) x = true := by
                simpa only [dread, hguard, ↓reduceIte] using hdi
              rw [hord r hr i hi hs] at hdiw
              by_cases hin : i < n
              · simp only [hin, ↓reduceIte] at hdiw
                have hci : wireVal n C i x = true := by
                  rw [L3543NarrowDirect.wv_input n C x i hin]
                  simpa only [L3543NarrowDirect.wv_input n D x i hin] using hdiw
                left
                rw [L3543NarrowDirect.wv_rec n C x hAO2 r hr, hop, hab,
                  L3543NarrowDirect.eval_or_pair, Bool.or_eq_true]
                have hiab : i = a ∨ i = b := by simpa [hab] using hi
                rcases hiab with rfl | rfl
                · exact Or.inl hci
                · exact Or.inr hci
              · simp only [hin, ↓reduceIte] at hdiw
                have hb := hback r hr i hi
                have hj : i - n < r := by omega
                have hjlen : i - n < C.gates.length := by omega
                have he : i + G0.length = n + G0.length + (i - n) := by omega
                have hdi' : wireVal n D (n + G0.length + (i - n)) x = true := by
                  simpa only [he] using hdiw
                rcases ih (i - n) hj hjlen hdi' with hcj | hbj
                · have hci : wireVal n C i x = true := by
                    rwa [show i = n + (i - n) by omega]
                  left
                  rw [L3543NarrowDirect.wv_rec n C x hAO2 r hr, hop, hab,
                    L3543NarrowDirect.eval_or_pair, Bool.or_eq_true]
                  have hiab : i = a ∨ i = b := by simpa [hab] using hi
                  rcases hiab with rfl | rfl
                  · exact Or.inl hci
                  · exact Or.inr hci
                · rcases hbj with ht | hbj
                  · rw [ht] at hdi'
                    exact False.elim (Bool.false_ne_true ((hDTfalse x hx).symm.trans hdi'))
                  · exact Or.inr (hbranchStep r (i - n) hr hjlen
                      (by
                        have heq : n + (i - n) = i := by omega
                        rwa [heq]) hbj)
          rcases hdro with hdi | hdi
          · exact horInput a (by simp [hab]) hdi
          · exact horInput b (by simp [hab]) hdi
    have hrev : ∀ r, r < C.gates.length →
        wireVal n C (n + r) x = true →
          wireVal n D (n + G0.length + r) x = true ∨ Branch r := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro hr hcr
        have hcout : wireVal n C (n + r) x = true := hcr
        obtain ⟨hop, hab, _⟩ := hAO2 r hr
        obtain ⟨a, b, hab⟩ := hab
        rw [L3543NarrowDirect.wv_rec n C x hAO2 r hr, hab] at hcr
        rcases hop with hop | hop
        · have hcrp : wireVal n C a x = true ∧ wireVal n C b x = true := by
            simpa only [hop, L3543NarrowDirect.eval_and_pair, Bool.and_eq_true] using hcr
          have hinput : ∀ i ∈ (gateAt C r).inputs,
              wireVal n C i x = true → dread x r i = true := by
            intro i hi hci
            by_cases hs : NR 0 r ∧ i = n + u 0
            · have hb := hreaderBranch r hr i hi hs
              rcases hb with ht | ⟨_, hor, _⟩
              · subst r
                exact False.elim (Bool.false_ne_true ((hCTfalse x hx).symm.trans hcout))
              · exact GateOp.noConfusion (hor.symm.trans hop)
            · by_cases hin : i < n
              · simpa [dread, hord r hr i hi hs, hin,
                  show i < n + (G0.length + r) by omega,
                  L3543NarrowDirect.wv_input n C x i hin,
                  L3543NarrowDirect.wv_input n D x i hin] using hci
              · have hb := hback r hr i hi
                have hj : i - n < r := by omega
                have hjlen : i - n < C.gates.length := by omega
                have he : i + G0.length = n + G0.length + (i - n) := by omega
                have hcj : wireVal n C (n + (i - n)) x = true := by
                  rw [show n + (i - n) = i by omega]
                  exact hci
                rcases ih (i - n) hj hjlen hcj with hdj | hbj
                · have hguard : rho r i < n + (G0.length + r) := by
                    rw [hord r hr i hi hs]
                    simp only [hin, ↓reduceIte]
                    omega
                  have hdiw : wireVal n D (rho r i) x = true := by
                    rw [hord r hr i hi hs]
                    simp only [hin, ↓reduceIte, he]
                    exact hdj
                  simpa only [dread, hguard, ↓reduceIte] using hdiw
                · rcases hbj with ht | hbj
                  · rw [ht] at hcj
                    exact False.elim (Bool.false_ne_true ((hCTfalse x hx).symm.trans hcj))
                  · have hb' := hbranchStep r (i - n) hr hjlen
                      (by
                        have heq : n + (i - n) = i := by omega
                        rwa [heq]) hbj
                    rcases hb' with ht | ⟨_, hor, _⟩
                    · subst r
                      exact False.elim (Bool.false_ne_true ((hCTfalse x hx).symm.trans hcout))
                    · exact GateOp.noConfusion (hor.symm.trans hop)
          rw [hDrec x r hr, hop, hab, L3543NarrowDirect.eval_and_pair, Bool.and_eq_true]
          exact Or.inl ⟨hinput a (by simp [hab]) hcrp.1,
            hinput b (by simp [hab]) hcrp.2⟩
        · have hcro : wireVal n C a x = true ∨ wireVal n C b x = true := by
            simpa only [hop, L3543NarrowDirect.eval_or_pair, Bool.or_eq_true] using hcr
          have horInput : ∀ i ∈ (gateAt C r).inputs,
              wireVal n C i x = true →
                wireVal n D (n + G0.length + r) x = true ∨ Branch r := by
            intro i hi hci
            by_cases hs : NR 0 r ∧ i = n + u 0
            · exact Or.inr (hreaderBranch r hr i hi hs)
            · by_cases hin : i < n
              · have hdi : dread x r i = true := by
                  simpa [dread, hord r hr i hi hs, hin,
                    show i < n + (G0.length + r) by omega,
                    L3543NarrowDirect.wv_input n C x i hin,
                    L3543NarrowDirect.wv_input n D x i hin] using hci
                left
                rw [hDrec x r hr, hop, hab, L3543NarrowDirect.eval_or_pair, Bool.or_eq_true]
                have hiab : i = a ∨ i = b := by simpa [hab] using hi
                rcases hiab with rfl | rfl
                · exact Or.inl hdi
                · exact Or.inr hdi
              · have hb := hback r hr i hi
                have hj : i - n < r := by omega
                have hjlen : i - n < C.gates.length := by omega
                have he : i + G0.length = n + G0.length + (i - n) := by omega
                have hcj : wireVal n C (n + (i - n)) x = true := by
                  rw [show n + (i - n) = i by omega]
                  exact hci
                rcases ih (i - n) hj hjlen hcj with hdj | hbj
                · have hguard : rho r i < n + (G0.length + r) := by
                    rw [hord r hr i hi hs]
                    simp only [hin, ↓reduceIte]
                    omega
                  have hdiw : wireVal n D (rho r i) x = true := by
                    rw [hord r hr i hi hs]
                    simp only [hin, ↓reduceIte, he]
                    exact hdj
                  have hdi : dread x r i = true := by
                    simpa only [dread, hguard, ↓reduceIte] using hdiw
                  left
                  rw [hDrec x r hr, hop, hab, L3543NarrowDirect.eval_or_pair, Bool.or_eq_true]
                  have hiab : i = a ∨ i = b := by simpa [hab] using hi
                  rcases hiab with rfl | rfl
                  · exact Or.inl hdi
                  · exact Or.inr hdi
                · rcases hbj with ht | hbj
                  · rw [ht] at hcj
                    exact False.elim (Bool.false_ne_true ((hCTfalse x hx).symm.trans hcj))
                  · exact Or.inr (hbranchStep r (i - n) hr hjlen
                      (by
                        have heq : n + (i - n) = i := by omega
                        rwa [heq]) hbj)
          rcases hcro with hci | hci
          · exact horInput a (by simp [hab]) hci
          · exact horInput b (by simp [hab]) hci
    by_cases ho : C.output < n
    · unfold Circuit.eval
      rw [hDout]
      simp only [ho, ↓reduceIte]
      change wireVal n D C.output x = wireVal n C C.output x
      rw [L3543NarrowDirect.wv_input n D x C.output ho,
        L3543NarrowDirect.wv_input n C x C.output ho]
    · let r := C.output - n
      by_cases hr : r < C.gates.length
      · have hout : C.output = n + r := by omega
        have hboutD (hd : wireVal n D (n + G0.length + r) x = true) : ¬ Branch r := by
          intro hb
          rcases hb with ht | ⟨hreach, hop, hcone⟩
          · rw [ht] at hd
            exact Bool.false_ne_true ((hDTfalse x hx).symm.trans hd)
          · exact (hclosure 0 (by omega) r hr hreach hop hcone).1 (by omega)
        have hboutC (hc : wireVal n C (n + r) x = true) : ¬ Branch r := by
          intro hb
          rcases hb with ht | ⟨hreach, hop, hcone⟩
          · rw [ht] at hc
            exact Bool.false_ne_true ((hCTfalse x hx).symm.trans hc)
          · exact (hclosure 0 (by omega) r hr hreach hop hcone).1 (by omega)
        unfold Circuit.eval
        rw [hDout]
        simp only [ho, ↓reduceIte]
        change wireVal n D (C.output + G0.length) x = wireVal n C C.output x
        rw [hout, show n + r + G0.length = n + G0.length + r by omega]
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro hd
          by_contra hc
          have hcf : wireVal n C (n + r) x = false := by
            cases hval : wireVal n C (n + r) x with
            | false => rfl
            | true => exact False.elim (hc hval)
          have hn : ¬ wireVal n C (n + r) x = true := by simp [hcf]
          exact hboutD hd ((hgood r hr hd).resolve_left hn)
        · intro hc
          by_contra hd
          have hdf : wireVal n D (n + G0.length + r) x = false := by
            cases hval : wireVal n D (n + G0.length + r) x with
            | false => rfl
            | true => exact False.elim (hd hval)
          have hn : ¬ wireVal n D (n + G0.length + r) x = true := by simp [hdf]
          exact hboutC hc ((hrev r hr hc).resolve_left hn)
      · have hge : n + C.gates.length ≤ C.output := by omega
        have hdge : n + D.gates.length ≤ C.output + G0.length := by
          rw [hDg, hDlen]
          omega
        unfold Circuit.eval
        rw [hDout]
        simp only [ho, ↓reduceIte]
        change wireVal n D (C.output + G0.length) x = wireVal n C C.output x
        rw [L3543_prefix.wireVal_eq_false n D x (C.output + G0.length) hdge,
          L3543_prefix.wireVal_eq_false n C x C.output hge]
  let zread (x : Fin n → Bool) (r i : ℕ) : Bool :=
    if rho r i < n + (G0.length + r) then wireVal n D (rho r i) x else false

  have hDrec_z (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length) :
      wireVal n D (n + G0.length + r) x =
        (gateAt C r).op.eval ((gateAt C r).inputs.map (zread x r)) := by
    have hdr : G0.length + r < D.gates.length := by rw [hDg, hDlen]; omega
    have hgateD : gateAt D (G0.length + r) = gateAt D0 (G0.length + r) := by
      unfold gateAt
      rw [hDg]
    rw [show n + G0.length + r = n + (G0.length + r) by omega,
      L3543_prefix.wireVal_gate n D x (G0.length + r) hdr, hgateD,
      L3543_prefix.gateAt_append_mapIdx G0 C.gates
        (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)) r hr]
    simp only [List.map_map, zread, Function.comp_def]
    rfl

  have hprefix_value (r i : ℕ) (hi : rho r i < n + G0.length)
      (hp : ∀ x : Fin n → Bool,
        wireVal n (⟨G0, 0⟩ : Circuit) (rho r i) x = P 0 x)
      (x : Fin n → Bool) : wireVal n D (rho r i) x = P 0 x := by
    rw [hDw x (rho r i)]
    unfold D0
    rw [L3543_prefix.prepend_wireVal_lt n x G0
      (C.gates.mapIdx (fun r g => ({ op := g.op, inputs := g.inputs.map (rho r) } : Gate)))
      (rho r i) hi]
    exact hp x

  have hstar_pair (a : Fin n) :
      P 0 (pairInput a ⟨z 0, hz⟩) =
        wireVal n C (n + u 0) (pairInput a ⟨z 0, hz⟩) := by
    rw [hP0]
    exact Bool.eq_iff_iff.mpr
      (L3543NarrowDirect.star_pair_right n C hAO2 (u 0) a ⟨z 0, hz⟩)

  have hchanged_le (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
      (hprev : ∀ g < r, wireVal n D (n + G0.length + g) x = true →
        wireVal n C (n + g) x = true)
      (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
      (hs : NR 0 r ∧ i = n + u 0) (hxz : x ⟨z 0, hz⟩ = true)
      (hdi : zread x r i = true) : wireVal n C i x = true := by
    have htime : rho r i < n + (G0.length + r) := by
      by_contra ht
      simp [zread, ht] at hdi
    have hdi' : wireVal n D (rho r i) x = true := by
      simpa [zread, htime] using hdi
    have hiu := hs.2
    subst i
    rcases hmap r 0 (by omega) hs.1 with hp | ⟨g, hg, hrg, hval, _⟩ | ⟨hpf, hge⟩
    · have hpv : P 0 x = true := by
        rw [← hprefix_value r (n + u 0) hp.1 hp.2 x]
        exact hdi'
      rw [hP0] at hpv
      exact L3543NarrowDirect.star_le n C hAO2 (u 0) (z 0) hz x hxz hpv
    · have hcg : wireVal n C (n + g) x = true := hprev g hg (by simpa [hrg] using hdi')
      rw [hval x] at hcg
      rw [hP0] at hcg
      exact L3543NarrowDirect.star_le n C hAO2 (u 0) (z 0) hz x hxz hcg
    · omega

  have hforward (x : Fin n → Bool) (hxz : x ⟨z 0, hz⟩ = true) :
      ∀ r, r < C.gates.length →
        wireVal n D (n + G0.length + r) x = true →
          wireVal n C (n + r) x = true := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr hdr
      obtain ⟨hop, hab, _⟩ := hAO2 r hr
      obtain ⟨a, b, hab⟩ := hab
      rw [hDrec_z x r hr, hab] at hdr
      have hinput : ∀ i ∈ (gateAt C r).inputs,
          zread x r i = true → wireVal n C i x = true := by
        intro i hi hdi
        by_cases hs : NR 0 r ∧ i = n + u 0
        · exact hchanged_le x r hr (fun g hg hd => ih g hg (by omega) hd) i hi hs hxz hdi
        · have hrw := hord r hr i hi hs
          by_cases hin : i < n
          · have ht : i < n + (G0.length + r) := by omega
            simp only [zread, hrw, hin, ite_eq_left ht, ↓reduceIte,
              L3543NarrowDirect.wv_input n D x i hin,
              L3543NarrowDirect.wv_input n C x i hin] at hdi ⊢
            exact hdi
          · have hb := hback r hr i hi
            have hj : i - n < r := by omega
            have he : i + G0.length = n + G0.length + (i - n) := by omega
            have ht : n + G0.length + (i - n) < n + (G0.length + r) := by omega
            have hdi' : wireVal n D (n + G0.length + (i - n)) x = true := by
              simpa only [zread, hrw, ite_eq_right hin, he, ite_eq_left ht] using hdi
            have hcg := ih (i - n) hj (by omega) hdi'
            rw [show i = n + (i - n) by omega]
            exact hcg
      rw [L3543NarrowDirect.wv_rec n C x hAO2 r hr, hab]
      rcases hop with hop | hop
      · rw [hop] at hdr ⊢
        simp only [L3543NarrowDirect.eval_and_pair, Bool.and_eq_true_eq_eq_true_and_eq_true] at hdr ⊢
        exact ⟨hinput a (by simp [hab]) hdr.1, hinput b (by simp [hab]) hdr.2⟩
      · rw [hop] at hdr ⊢
        simp only [L3543NarrowDirect.eval_or_pair, Bool.or_eq_true_eq_eq_true_or_eq_true] at hdr ⊢
        rcases hdr with hda | hdb
        · exact Or.inl (hinput a (by simp [hab]) hda)
        · exact Or.inr (hinput b (by simp [hab]) hdb)

  have hD_le_C (x : Fin n → Bool) (hxz : x ⟨z 0, hz⟩ = true) :
      D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true := by
    intro hd
    unfold Circuit.eval at hd ⊢
    by_cases ho : C.output < n
    · rw [hDout, ite_eq_left ho] at hd
      change wireVal n D C.output x = true at hd
      change wireVal n C C.output x = true
      simpa only [L3543NarrowDirect.wv_input n D x C.output ho,
        L3543NarrowDirect.wv_input n C x C.output ho] using hd
    · let r := C.output - n
      by_cases hr : r < C.gates.length
      · have hout : C.output = n + r := by omega
        rw [hDout, ite_eq_right ho] at hd
        change wireVal n D (C.output + G0.length) x = true at hd
        change wireVal n C C.output x = true
        rw [show C.output + G0.length = n + G0.length + r by omega] at hd
        have hc := hforward x hxz r hr hd
        simpa only [hout] using hc
      · have hge : n + C.gates.length ≤ C.output := by omega
        have hdge : n + D.gates.length ≤ C.output + G0.length := by rw [hDg, hDlen]; omega
        rw [hDout, ite_eq_right ho] at hd
        change wireVal n D (C.output + G0.length) x = true at hd
        rw [L3543_prefix.wireVal_eq_false n D x (C.output + G0.length) hdge] at hd
        cases hd

  have hchanged_pair (a : Fin n) (r : ℕ) (hr : r < C.gates.length)
      (hprev : ∀ g < r,
        wireVal n D (n + G0.length + g) (pairInput a ⟨z 0, hz⟩) =
          wireVal n C (n + g) (pairInput a ⟨z 0, hz⟩))
      (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
      (hs : NR 0 r ∧ i = n + u 0) :
      zread (pairInput a ⟨z 0, hz⟩) r i =
        wireVal n C i (pairInput a ⟨z 0, hz⟩) := by
    have hiu := hs.2
    subst i
    rcases hmap r 0 (by omega) hs.1 with hp | ⟨g, hg, hrg, hval, _⟩ | ⟨hpf, hge⟩
    · have ht : rho r (n + u 0) < n + (G0.length + r) := by omega
      simp only [zread, ite_eq_left ht, hprefix_value r (n + u 0) hp.1 hp.2, hstar_pair]
    · have ht : n + G0.length + g < n + (G0.length + r) := by omega
      simp only [zread, hrg, ite_eq_left ht, hprev g hg, hval, hstar_pair]
    · have ht : ¬ rho r (n + u 0) < n + (G0.length + r) := by omega
      simp only [zread, ite_eq_right ht]
      have hpfalse : P 0 (pairInput a ⟨z 0, hz⟩) = false := hpf _
      rw [← hstar_pair]
      exact hpfalse.symm

  have heq_pair (a : Fin n) :
      D.eval (List.ofFn (pairInput a ⟨z 0, hz⟩)) =
        C.eval (List.ofFn (pairInput a ⟨z 0, hz⟩)) := by
    have hg : ∀ r, r < C.gates.length →
        wireVal n D (n + G0.length + r) (pairInput a ⟨z 0, hz⟩) =
          wireVal n C (n + r) (pairInput a ⟨z 0, hz⟩) := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro hr
        obtain ⟨hop, hab, _⟩ := hAO2 r hr
        obtain ⟨b, c, hab⟩ := hab
        have hinput : ∀ i ∈ (gateAt C r).inputs,
            zread (pairInput a ⟨z 0, hz⟩) r i =
              wireVal n C i (pairInput a ⟨z 0, hz⟩) := by
          intro i hi
          by_cases hs : NR 0 r ∧ i = n + u 0
          · exact hchanged_pair a r hr (fun g hg => ih g hg (by omega)) i hi hs
          · have hrw := hord r hr i hi hs
            by_cases hin : i < n
            · have ht : i < n + (G0.length + r) := by omega
              simp only [zread, hrw, hin, ite_eq_left ht, ↓reduceIte,
                L3543NarrowDirect.wv_input]
            · have hb := hback r hr i hi
              have hj : i - n < r := by omega
              have he : i + G0.length = n + G0.length + (i - n) := by omega
              have ht : n + G0.length + (i - n) < n + (G0.length + r) := by omega
              simp only [zread, hrw, ite_eq_right hin, ite_eq_left ht, he]
              have hh := ih (i - n) hj (by omega)
              conv_rhs => rw [show i = n + (i - n) by omega]
              exact hh
        rw [hDrec_z (pairInput a ⟨z 0, hz⟩) r hr,
          L3543NarrowDirect.wv_rec n C (pairInput a ⟨z 0, hz⟩) hAO2 r hr, hab]
        rcases hop with hop | hop
        · rw [hop]
          simp only [L3543NarrowDirect.eval_and_pair,
            hinput b (by simp [hab]), hinput c (by simp [hab])]
        · rw [hop]
          simp only [L3543NarrowDirect.eval_or_pair,
            hinput b (by simp [hab]), hinput c (by simp [hab])]
    unfold Circuit.eval
    change wireVal n D D.output (pairInput a ⟨z 0, hz⟩) =
      wireVal n C C.output (pairInput a ⟨z 0, hz⟩)
    by_cases ho : C.output < n
    · rw [hDout, ite_eq_left ho]
      rw [L3543NarrowDirect.wv_input n D _ C.output ho,
        L3543NarrowDirect.wv_input n C _ C.output ho]
    · let r := C.output - n
      by_cases hr : r < C.gates.length
      · have hout : C.output = n + r := by omega
        rw [hDout, ite_eq_right ho, show C.output + G0.length = n + G0.length + r by omega]
        simpa only [hout] using hg r hr
      · have hge : n + C.gates.length ≤ C.output := by omega
        have hdge : n + D.gates.length ≤ C.output + G0.length := by rw [hDg, hDlen]; omega
        rw [hDout, ite_eq_right ho]
        change wireVal n D (C.output + G0.length) (pairInput a ⟨z 0, hz⟩) =
          wireVal n C C.output (pairInput a ⟨z 0, hz⟩)
        rw [L3543_prefix.wireVal_eq_false n D _ (C.output + G0.length) hdge,
          L3543_prefix.wireVal_eq_false n C _ C.output hge]

  have hsuffix_mono : ∀ r, r < C.gates.length →
      ∀ x y : Fin n → Bool, x ≤ y →
        wireVal n D (n + G0.length + r) x = true →
          wireVal n D (n + G0.length + r) y = true := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr x y hxy hdx
      obtain ⟨hop, hab, _⟩ := hAO2 r hr
      obtain ⟨b, c, hab⟩ := hab
      rw [hDrec_z x r hr, hab] at hdx
      have hinput : ∀ i ∈ (gateAt C r).inputs,
          zread x r i = true → zread y r i = true := by
        intro i hi hdi
        by_cases hs : NR 0 r ∧ i = n + u 0
        · have hiu := hs.2
          subst i
          have htime : rho r (n + u 0) < n + (G0.length + r) := by
            by_contra ht
            simp [zread, ht] at hdi
          have hdi' : wireVal n D (rho r (n + u 0)) x = true := by
            simpa [zread, htime] using hdi
          rcases hmap r 0 (by omega) hs.1 with hp | ⟨g, hg, hrg, hval, _⟩ | ⟨hpf, hge⟩
          · have hpv : P 0 x = true := by
              rw [← hprefix_value r (n + u 0) hp.1 hp.2 x]
              exact hdi'
            rw [hP0] at hpv
            have hpy := L3543NarrowDirect.star_mono n C (u 0) (z 0) x y hxy hpv
            have ht : rho r (n + u 0) < n + (G0.length + r) := by omega
            simpa only [zread, ite_eq_left ht, hprefix_value r (n + u 0) hp.1 hp.2 y,
              hP0] using hpy
          · have hdg : wireVal n D (n + G0.length + g) x = true := by
              simpa [zread, hrg, show n + G0.length + g < n + (G0.length + r) by omega] using hdi
            have hdy := ih g hg (by omega) x y hxy hdg
            have ht : n + G0.length + g < n + (G0.length + r) := by omega
            simpa only [zread, hrg, ite_eq_left ht] using hdy
          · omega
        · have hrw := hord r hr i hi hs
          by_cases hin : i < n
          · have ht : i < n + (G0.length + r) := by omega
            simp only [zread, hrw, hin, ite_eq_left ht, ↓reduceIte,
              L3543NarrowDirect.wv_input n D x i hin,
              L3543NarrowDirect.wv_input n D y i hin] at hdi ⊢
            exact hxy ⟨i, hin⟩ hdi
          · have hb := hback r hr i hi
            have hj : i - n < r := by omega
            have he : i + G0.length = n + G0.length + (i - n) := by omega
            have ht : n + G0.length + (i - n) < n + (G0.length + r) := by omega
            have hdi' : wireVal n D (n + G0.length + (i - n)) x = true := by
              simpa only [zread, hrw, ite_eq_right hin, he, ite_eq_left ht] using hdi
            have hdy := ih (i - n) hj (by omega) x y hxy hdi'
            simp only [zread, hrw, ite_eq_right hin, ite_eq_left ht, he]
            exact hdy
      rw [hDrec_z y r hr, hab]
      rcases hop with hop | hop
      · rw [hop] at hdx ⊢
        simp only [L3543NarrowDirect.eval_and_pair, Bool.and_eq_true_eq_eq_true_and_eq_true] at hdx ⊢
        exact ⟨hinput b (by simp [hab]) hdx.1, hinput c (by simp [hab]) hdx.2⟩
      · rw [hop] at hdx ⊢
        simp only [L3543NarrowDirect.eval_or_pair, Bool.or_eq_true_eq_eq_true_or_eq_true] at hdx ⊢
        rcases hdx with hdb | hdc
        · exact Or.inl (hinput b (by simp [hab]) hdb)
        · exact Or.inr (hinput c (by simp [hab]) hdc)

  have hD_mono (x y : Fin n → Bool) (hxy : x ≤ y) :
      D.eval (List.ofFn x) = true → D.eval (List.ofFn y) = true := by
    intro hd
    unfold Circuit.eval at hd ⊢
    by_cases ho : C.output < n
    · rw [hDout, ite_eq_left ho] at hd ⊢
      change wireVal n D C.output x = true at hd
      change wireVal n D C.output y = true
      have hdx : x ⟨C.output, ho⟩ = true := by
        simpa only [L3543NarrowDirect.wv_input n D x C.output ho] using hd
      simpa only [L3543NarrowDirect.wv_input n D y C.output ho] using hxy ⟨C.output, ho⟩ hdx
    · let r := C.output - n
      by_cases hr : r < C.gates.length
      · rw [hDout, ite_eq_right ho] at hd ⊢
        change wireVal n D (C.output + G0.length) x = true at hd
        change wireVal n D (C.output + G0.length) y = true
        rw [show C.output + G0.length = n + G0.length + r by omega] at hd ⊢
        exact hsuffix_mono r hr x y hxy hd
      · have hdge : n + D.gates.length ≤ C.output + G0.length := by rw [hDg, hDlen]; omega
        rw [hDout, ite_eq_right ho] at hd
        change wireVal n D (C.output + G0.length) x = true at hd
        rw [L3543_prefix.wireVal_eq_false n D x (C.output + G0.length) hdge] at hd
        cases hd

  have hC_pair (a b : Fin n) (hab : H.Adj a b) :
      C.eval (List.ofFn (pairInput a b)) = true := by
    rw [hC]
    exact (hq _).2 ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩

  have hpair_le (x : Fin n → Bool) (a b : Fin n)
      (ha : x a = true) (hb : x b = true) : pairInput a b ≤ x := by
    intro j hj
    by_cases hja : j = a
    · subst j; exact ha
    · by_cases hjb : j = b
      · subst j; exact hb
      · simp [pairInput, hja, hjb] at hj

  have hq_le_D : ∀ x : Fin n → Bool, qH x = true → D.eval (List.ofFn x) = true := by
    intro x hx
    obtain ⟨a, b, hab, ha, hb⟩ := (hq x).1 hx
    have habne : a ≠ b := by
      intro he
      subst b
      exact H.irrefl hab
    by_cases hza : (⟨z 0, hz⟩ : Fin n) = a
    · have hzb : (⟨z 0, hz⟩ : Fin n) ≠ b := by
        intro hzb
        exact habne (hza.symm.trans hzb)
      have hdp : D.eval (List.ofFn (pairInput b ⟨z 0, hz⟩)) = true := by
        rw [heq_pair b]
        exact hC_pair b ⟨z 0, hz⟩ (by simpa [hza, H.adj_comm] using hab)
      exact hD_mono _ x (hpair_le x b ⟨z 0, hz⟩ hb (by simpa [hza] using ha)) hdp
    · by_cases hzb : (⟨z 0, hz⟩ : Fin n) = b
      · have hdp : D.eval (List.ofFn (pairInput a ⟨z 0, hz⟩)) = true := by
          rw [heq_pair a]
          exact hC_pair a ⟨z 0, hz⟩ (by simpa [hzb] using hab)
        exact hD_mono _ x (hpair_le x a ⟨z 0, hz⟩ ha (by simpa [hzb] using hb)) hdp
      · have hzfalse : pairInput a b ⟨z 0, hz⟩ = false := by
          simp [pairInput, show (⟨z 0, hz⟩ : Fin n) ≠ a from hza,
            show (⟨z 0, hz⟩ : Fin n) ≠ b from hzb]
        have hdp : D.eval (List.ofFn (pairInput a b)) = true := by
          rw [heq_noz _ hzfalse]
          exact hC_pair a b hab
        exact hD_mono _ x (hpair_le x a b ha hb) hdp

  by_cases hzy : y ⟨z 0, hz⟩ = true
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hd
      rw [← hC y]
      exact hD_le_C y hzy hd
    · exact hq_le_D y
  · have hyf : y ⟨z 0, hz⟩ = false := by
      cases h : y ⟨z 0, hz⟩ <;> simp_all
    rw [heq_noz y hyf, hC]
