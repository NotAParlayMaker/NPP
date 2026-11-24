import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4145_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership PEqualNP.CircuitMoves

-- Section 1: Basic wire evaluation and monotonicity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc, ite_eq_left rfl]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma legal_of_mono2 (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma lt_length_of_gateAt_and (C : Circuit) (k : ℕ) (h : (gateAt C k).op = GateOp.and) :
    k < C.gates.length := by
  by_contra hge
  have hle : C.gates.length ≤ k := Nat.le_of_not_lt hge
  have heq : gateAt C k = ⟨GateOp.or, []⟩ := by
    unfold gateAt; exact List.getD_eq_default _ _ hle
  rw [heq] at h
  cases h

lemma ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]; simp [GateOp.eval]

lemma ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]; simp [GateOp.eval]

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil => intro w₁ w₂ _ hle i hi; exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    rw [wiresFrom_cons] at hi ⊢
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen]) _ i hi
    intro j
    simp only [getD_snoc, hlen]
    split_ifs
    · rcases hmono g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk; exact hle k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩; exact ⟨k, hk, hle k h⟩
    · exact hle j

lemma circuit_wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma getD_wires_gate_rb (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length)
    (hrb : ReadsBack x.length C) :
    (C.wires x).getD (x.length + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x).getD i false) := by
  rw [circuit_wires_eq, getD_wiresFrom_gate C.gates x k hk, gateAt_eq C k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt := hrb k hk i (by rw [gateAt_eq C k hk]; exact hi)
  simp [hlt]

lemma wires_set_mono (C : Circuit) (hmono : Monotone2 C) (i : ℕ) (hi : i < C.gates.length)
    (g₁ g₂ : Gate) (x : List Bool)
    (C₁ C₂ : Circuit)
    (hC₁ : C₁ = { gates := C.gates.set i g₁, output := C.output })
    (hC₂ : C₂ = { gates := C.gates.set i g₂, output := C.output })
    (hle : (C₁.wires x).getD (x.length + i) false = true →
      (C₂.wires x).getD (x.length + i) false = true) :
    ∀ w, (C₁.wires x).getD w false = true → (C₂.wires x).getD w false = true := by
  subst hC₁ hC₂
  have hsplit : C.gates = C.gates.take i ++ C.gates[i] :: C.gates.drop (i + 1) := by
    have h1 := (List.take_append_drop i C.gates).symm
    rw [List.drop_eq_getElem_cons hi] at h1
    exact h1
  have hset (g : Gate) : C.gates.set i g = C.gates.take i ++ g :: C.gates.drop (i + 1) := by
    apply List.ext_getElem?
    intro k
    by_cases hki : k = i
    · subst hki
      rw [List.getElem?_set_self hi, List.getElem?_append_right (by simp [Nat.le_of_lt hi])]
      simp [Nat.le_of_lt hi]
    · rw [List.getElem?_set_ne (Ne.symm hki)]
      by_cases hlt : k < i
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hlt]
      · rw [List.getElem?_append_right (by simp; omega)]
        have hlen : (C.gates.take i).length = i := by simp [Nat.le_of_lt hi]
        rw [hlen, show k - i = (k - i - 1) + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop]
        congr 1; omega
  let pre := C.gates.take i
  let post := C.gates.drop (i + 1)
  have hpre_len : (wiresFrom pre x).length = x.length + i := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hi)]
  have hpost_mono : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg =>
    (legal_of_mono2 C hmono g (List.mem_of_mem_drop hg)).1
  have hval (g : Gate) :
      (wiresFrom (C.gates.set i g) x).getD (x.length + i) false =
        g.op.eval (g.inputs.map fun k => (wiresFrom pre x).getD k false) := by
    rw [hset g, wiresFrom_append, wiresFrom_cons]
    change (wiresFrom post (wiresFrom pre x ++
      [g.op.eval (g.inputs.map fun k => (wiresFrom pre x).getD k false)])).getD (x.length + i) false = _
    rw [getD_wiresFrom_lt _ _ _ (by rw [List.length_append, List.length_singleton, hpre_len]; omega)]
    rw [← hpre_len, getD_snoc, ite_eq_left rfl]
  rw [circuit_wires_eq, circuit_wires_eq, hval g₁, hval g₂] at hle
  intro w hw
  rw [circuit_wires_eq, hset g₁, wiresFrom_append, wiresFrom_cons] at hw
  rw [circuit_wires_eq, hset g₂, wiresFrom_append, wiresFrom_cons]
  refine wiresFrom_mono post hpost_mono _ _ (by simp) ?_ w hw
  intro j
  simp only [getD_snoc]
  split_ifs
  · exact hle
  · exact id

lemma set_self_eq (C : Circuit) (i : ℕ) (hi : i < C.gates.length) :
    { gates := C.gates.set i C.gates[i], output := C.output : Circuit } = C := by
  cases C; simp

-- Section 2: InCone characterization and properties

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma cones_take (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < cs.length) :
    (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : j < (coneStep n cs g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma cones_char (n : ℕ) (gs : List Gate) (i j : ℕ) :
    i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
        n ≤ w ∧ w < n + j ∧ (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      simpa using cones_len n gs []
    have hprev : ∀ k < gs.length,
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    by_cases hlt : j < gs.length
    · rw [hprev j hlt, ih]
      have hgate : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hgate]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rcases h3 with rfl | h3
        · exact Or.inl rfl
        · exact Or.inr (by rw [hprev (w - n) (by omega)]; exact h3)
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨hlt, w, hw, h1, h2, ?_⟩
        rcases h3 with rfl | h3
        · exact Or.inl rfl
        · exact Or.inr (by rw [← hprev (w - n) (by omega)]; exact h3)
    · by_cases heq : j = gs.length
      · subst heq
        have hstep : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp only [coneStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        have hgate : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [hstep, hgate]
        simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · exact Or.inr (by rw [hprev (w - n) (by omega)]; exact h3)
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨w, ⟨hw, h1, h2⟩, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · exact Or.inr (by rw [← hprev (w - n) (by omega)]; exact h3)
      · have hge : (coneStep n (gs.foldl (coneStep n) []) g).length ≤ j := by
          simp only [coneStep, List.length_append, List.length_singleton, hlen]; omega
        rw [List.getD_eq_default _ _ hge]
        simp only [List.not_mem_nil, false_iff, not_and]
        intro hlt'
        simp only [List.length_append, List.length_singleton] at hlt'
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧
      ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]; exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]; exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (h : InCone n C i j) :
    i < j ∧ j < C.gates.length := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨hj, k, hkj, _, hrest⟩ := (inCone_iff n C i j).mp h
    rcases hrest with rfl | hc
    · exact ⟨hkj, hj⟩
    · have := ih k hkj hc
      exact ⟨by omega, hj⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (i k j : ℕ)
    (h1 : InCone n C i k) (h2 : InCone n C k j) : InCone n C i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨hj, c, hcj, hcin, hrest⟩ := (inCone_iff n C k j).mp h2
    rw [inCone_iff]
    refine ⟨hj, c, hcj, hcin, ?_⟩
    rcases hrest with rfl | hc
    · exact Or.inr h1
    · exact Or.inr (ih c hcj hc)

lemma inCone_first_step (n : ℕ) (C : Circuit) (i j : ℕ) (h : InCone n C i j) :
    ∃ k < C.gates.length, n + i ∈ (gateAt C k).inputs ∧ (k = j ∨ InCone n C k j) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨hj, c, hcj, hcin, hrest⟩ := (inCone_iff n C i j).mp h
    rcases hrest with rfl | hc
    · exact ⟨j, hj, hcin, Or.inl rfl⟩
    · obtain ⟨k, hk, hkin, hkj⟩ := ih c hcj hc
      refine ⟨k, hk, hkin, Or.inr ?_⟩
      rw [inCone_iff]
      exact ⟨hj, c, hcj, hcin, hkj⟩

lemma inCone_set_ge (n : ℕ) (C : Circuit) (i : ℕ) (g : Gate) (u v : ℕ) (hu : i ≤ u) :
    InCone n { gates := C.gates.set i g, output := C.output } u v ↔ InCone n C u v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases hvi : v ≤ i
    · constructor <;> intro h
      · have := (inCone_lt n _ u v h).1; omega
      · have := (inCone_lt n _ u v h).1; omega
    · have hne : v ≠ i := by omega
      have hgate : gateAt { gates := C.gates.set i g, output := C.output } v = gateAt C v := by
        simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
      rw [inCone_iff, inCone_iff, List.length_set, hgate]
      constructor
      · rintro ⟨hv, c, hcv, hcin, hrest⟩
        refine ⟨hv, c, hcv, hcin, ?_⟩
        rcases hrest with rfl | hc
        · exact Or.inl rfl
        · exact Or.inr ((ih c hcv).mp hc)
      · rintro ⟨hv, c, hcv, hcin, hrest⟩
        refine ⟨hv, c, hcv, hcin, ?_⟩
        rcases hrest with rfl | hc
        · exact Or.inl rfl
        · exact Or.inr ((ih c hcv).mpr hc)

lemma inCone_set_input_only (n : ℕ) (C : Circuit) (i : ℕ) (g : Gate)
    (hg : ∀ w ∈ g.inputs, w < n) (u v : ℕ) :
    InCone n { gates := C.gates.set i g, output := C.output } u v → InCone n C u v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro h
    obtain ⟨hv, c, hcv, hcin, hrest⟩ := (inCone_iff n _ u v).mp h
    rw [List.length_set] at hv
    by_cases hvi : v = i
    · subst hvi
      have hgate : gateAt { gates := C.gates.set v g, output := C.output } v = g := by
        simp [gateAt, List.getD_eq_getElem?_getD, hv]
      rw [hgate] at hcin
      have := hg (n + c) hcin
      omega
    · have hgate : gateAt { gates := C.gates.set i g, output := C.output } v = gateAt C v := by
        simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hvi)]
      rw [hgate] at hcin
      rw [inCone_iff]
      refine ⟨hv, c, hcv, hcin, ?_⟩
      rcases hrest with rfl | hc
      · exact Or.inl rfl
      · exact Or.inr (ih c hcv hc)

-- Section 3: Gate erasure and LIFT

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

lemma er_eq (n m a : ℕ) : eraseRedirect n m a = rn (n + m) a := by
  funext i; unfold eraseRedirect rn; split_ifs <;> omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold rn
  by_cases hlt : i < A.length
  · rw [ite_eq_left hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  · by_cases heq : i = A.length
    · subst heq
      rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [getD_mid A E b A.length rfl, ← hb]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha]
    · rw [ite_eq_right hlt, ite_eq_right heq]
      have h1 : A.length ≤ i - 1 := by omega
      have h2 : A.length ≤ i := by omega
      have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
        List.getElem?_append_right h2]
      rw [h3, List.getElem?_cons_succ]

lemma surg_rn (A : List Bool) (N a : ℕ) (hN : A.length = N) (ha : a < N) (post : List Gate) :
    ∀ E : List Bool, ∃ E2 : List Bool,
      wiresFrom post (A ++ A.getD a false :: E) = A ++ A.getD a false :: E2 ∧
      wiresFrom (post.map (Tc N a)) (A ++ E) = A ++ E2 := by
  induction post with
  | nil => intro E; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E
    have he : (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) =
        h.op.eval (h.inputs.map fun i => (A ++ A.getD a false :: E).getD i false) := by
      show h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_rn A E (A.getD a false) N hN a ha rfl i
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ A.getD a false :: E).getD i false)])
    refine ⟨E2, ?_, ?_⟩
    · rw [wiresFrom_cons, List.append_assoc, List.cons_append]; exact h1
    · rw [List.map_cons, wiresFrom_cons, he, List.append_assoc]; exact h2

lemma eraseGate_bridge (n : ℕ) (C : Circuit) (pre post : List Gate) (gj : Gate)
    (hC : C.gates = pre ++ gj :: post) (a : ℕ) :
    eraseGate n C pre.length a =
      ⟨pre ++ post.map (Tc (n + pre.length) a), rn (n + pre.length) a C.output⟩ := by
  have hk : pre.length < C.gates.length := by rw [hC]; simp
  have h1 : C.gates.take pre.length = pre := by rw [hC]; simp
  have h2 : C.gates.drop (pre.length + 1) = post := by rw [hC]; simp
  unfold eraseGate
  rw [ite_eq_left hk, h1, h2, er_eq]
  rfl

lemma eraseGate_struct (n : ℕ) (C : Circuit) (m a : ℕ) (hm : m < C.gates.length)
    (ha : a < n + m) (hmono : Monotone2 C) (hrb : ReadsBack n C) :
    Monotone2 (eraseGate n C m a) ∧ ReadsBack n (eraseGate n C m a) ∧
      (eraseGate n C m a).size + 1 = C.size := by
  obtain ⟨pre, post, gj, hC, hpl, _⟩ := split_gates C.gates m hm
  subst hpl
  rw [eraseGate_bridge n C pre post gj hC a]
  have legal := legal_of_mono2 C hmono
  refine ⟨?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := legal h (by rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hh)))
      refine ⟨?_, by show (h.inputs.map (rn _ _)).length ≤ 2; simp [hl.2]⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map (Tc (n + pre.length) a), rn (n + pre.length) a C.output⟩ j =
          gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map (Tc (n + pre.length) a), rn (n + pre.length) a C.output⟩ j =
          Tc (n + pre.length) a (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
      have hlt := hrb (j + 1) (by rw [hC]; simp; omega) w (by rw [e2]; exact hw)
      unfold rn; split_ifs <;> omega
  · show (pre ++ post.map (Tc (n + pre.length) a)).length + 1 = C.gates.length
    rw [hC]; simp; omega

lemma eraseGate_eval_eq (n : ℕ) (C : Circuit) (m a : ℕ) (hm : m < C.gates.length)
    (ha : a < n + m) (x : List Bool) (hx : x.length = n) :
    (eraseGate n C m a).eval x =
      (wiresFrom (C.gates.drop (m + 1))
        (wiresFrom (C.gates.take m) x ++ [(C.wires x).getD a false])).getD C.output false := by
  obtain ⟨pre, post, gj, hC, hpl, _⟩ := split_gates C.gates m hm
  have ht : C.gates.take m = pre := by rw [hC, ← hpl]; simp
  have hd : C.gates.drop (m + 1) = post := by rw [hC, ← hpl]; simp
  rw [ht, hd]
  subst hpl
  rw [eraseGate_bridge n C pre post gj hC a]
  have hlen : (wiresFrom pre x).length = n + pre.length := by rw [length_wiresFrom, hx]
  have hwa : (C.wires x).getD a false = (wiresFrom pre x).getD a false := by
    rw [circuit_wires_eq, hC, wiresFrom_append]
    exact getD_wiresFrom_lt _ _ a (by omega)
  rw [hwa]
  obtain ⟨E2, h1, h2⟩ := surg_rn (wiresFrom pre x) (n + pre.length) a hlen ha post []
  rw [List.append_nil] at h2
  show (wiresFrom (pre ++ post.map (Tc (n + pre.length) a)) x).getD
    (rn (n + pre.length) a C.output) false = _
  rw [wiresFrom_append, h2, h1]
  exact getD_rn (wiresFrom pre x) E2 _ (n + pre.length) hlen a ha rfl C.output

lemma eraseGate_eval_cmp (n : ℕ) (C : Circuit) (m a : ℕ) (hm : m < C.gates.length)
    (ha : a < n + m) (hmono : Monotone2 C) (x : List Bool) (hx : x.length = n) :
    (((C.wires x).getD (n + m) false = true → (C.wires x).getD a false = true) →
      C.eval x = true → (eraseGate n C m a).eval x = true) ∧
    ((C.wires x).getD (n + m) false = (C.wires x).getD a false →
      (eraseGate n C m a).eval x = C.eval x) := by
  obtain ⟨pre, post, gj, hC, hpl, _⟩ := split_gates C.gates m hm
  have ht : C.gates.take m = pre := by rw [hC, ← hpl]; simp
  have hd : C.gates.drop (m + 1) = post := by rw [hC, ← hpl]; simp
  have hpre_len : (wiresFrom pre x).length = n + m := by
    rw [length_wiresFrom, hx, hpl]
  have hpost_mono : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg =>
    (legal_of_mono2 C hmono g (by rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hg)))).1
  have hgm : (C.wires x).getD (n + m) false =
      gj.op.eval (gj.inputs.map fun i => (wiresFrom pre x).getD i false) := by
    rw [circuit_wires_eq, hC, wiresFrom_append, wiresFrom_cons,
      getD_wiresFrom_lt _ _ _ (by rw [List.length_append, List.length_singleton, hpre_len]; omega),
      ← hpre_len, getD_snoc, ite_eq_left rfl]
  have hold : C.eval x = (wiresFrom post (wiresFrom pre x ++ [(C.wires x).getD (n + m) false])).getD
      C.output false := by
    conv_lhs => rw [Circuit.eval, circuit_wires_eq, hC, wiresFrom_append, wiresFrom_cons, ← hgm]
  rw [eraseGate_eval_eq n C m a hm ha x hx, ht, hd, hold]
  refine ⟨fun hle hev => ?_, fun heq => by rw [heq]⟩
  refine wiresFrom_mono post hpost_mono _ _ (by simp) ?_ C.output hev
  intro i
  simp only [getD_snoc]
  split_ifs
  · exact hle
  · exact id

lemma eraseGate_wires_lt (n : ℕ) (C : Circuit) (m a : ℕ) (hm : m < C.gates.length)
    (x : List Bool) (w : ℕ) (hw : w < x.length + m) :
    ((eraseGate n C m a).wires x).getD w false = (C.wires x).getD w false := by
  obtain ⟨pre, post, gj, hC, hpl, _⟩ := split_gates C.gates m hm
  subst hpl
  rw [eraseGate_bridge n C pre post gj hC a, circuit_wires_eq, circuit_wires_eq,
    hC, wiresFrom_append, wiresFrom_append]
  have hlen : (wiresFrom pre x).length = x.length + pre.length := by rw [length_wiresFrom]
  rw [getD_wiresFrom_lt (post.map _) (wiresFrom pre x) w (by omega),
    getD_wiresFrom_lt (gj :: post) (wiresFrom pre x) w (by omega)]

lemma eraseGate_dead_eval (n : ℕ) (hn : 0 < n) (C : Circuit) (m : ℕ) (hm : m < C.gates.length)
    (hrb : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    (v : ℕ) (hv : v < C.gates.length) (hne : v ≠ m) (hnc : ¬ InCone n C m v) :
    ((eraseGate n C m 0).wires x).getD (eraseRedirect n m 0 (n + v)) false =
      (C.wires x).getD (n + v) false := by
  subst hx
  obtain ⟨pre, post, gj, hC, hpl, _⟩ := split_gates C.gates m hm
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    have hD_rb : ReadsBack x.length (eraseGate x.length C m 0) := by
      have hm0 : 0 < x.length + m := by omega
      intro j hj i hi
      have hlen : (eraseGate x.length C m 0).gates.length = pre.length + post.length := by
        rw [← hpl, eraseGate_bridge x.length C pre post gj hC 0]; simp
      rw [hlen] at hj
      rw [← hpl, eraseGate_bridge x.length C pre post gj hC 0] at hi
      by_cases hjp : j < pre.length
      · have e : gateAt ⟨pre ++ post.map (Tc (x.length + pre.length) 0),
            rn (x.length + pre.length) 0 C.output⟩ j = gateAt C j := by
          simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
        rw [e] at hi
        exact hrb j (by rw [hC]; simp; omega) i hi
      · have hjk : j - pre.length < post.length := by omega
        have e1 : gateAt ⟨pre ++ post.map (Tc (x.length + pre.length) 0),
            rn (x.length + pre.length) 0 C.output⟩ j =
            Tc (x.length + pre.length) 0 (post[j - pre.length]) := by
          simp [gateAt, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
        have e2 : gateAt C (j + 1) = post[j - pre.length] := by
          have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
          simp [gateAt, hC, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
        rw [e1] at hi
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
        have hlt := hrb (j + 1) (by rw [hC]; simp; omega) w (by rw [e2]; exact hw)
        unfold rn; split_ifs <;> omega
    by_cases hvlt : v < m
    · have her : eraseRedirect x.length m 0 (x.length + v) = x.length + v := by
        unfold eraseRedirect; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [her]
      exact eraseGate_wires_lt x.length C m 0 hm x (x.length + v) (by omega)
    · have hvgt : m < v := by omega
      have her : eraseRedirect x.length m 0 (x.length + v) = x.length + (v - 1) := by
        unfold eraseRedirect; rw [ite_eq_right (by omega), ite_eq_left (by omega)]; omega
      have hv1_lt : v - 1 < (eraseGate x.length C m 0).gates.length := by
        rw [← hpl, eraseGate_bridge x.length C pre post gj hC 0]
        simp only [List.length_append, List.length_map]
        rw [hC] at hv; simp only [List.length_append, List.length_cons] at hv; omega
      rw [her, getD_wires_gate_rb (eraseGate x.length C m 0) x (v - 1) hv1_lt hD_rb,
        getD_wires_gate_rb C x v hv hrb]
      have hgate : gateAt (eraseGate x.length C m 0) (v - 1) =
          ⟨(gateAt C v).op, (gateAt C v).inputs.map (eraseRedirect x.length m 0)⟩ := by
        rw [← hpl, eraseGate_bridge x.length C pre post gj hC 0]
        have hjk : v - 1 - pre.length < post.length := by
          rw [hC] at hv; simp only [List.length_append, List.length_cons] at hv; omega
        have e1 : gateAt ⟨pre ++ post.map (Tc (x.length + pre.length) 0),
            rn (x.length + pre.length) 0 C.output⟩ (v - 1) =
            Tc (x.length + pre.length) 0 (post[v - 1 - pre.length]) := by
          simp [gateAt, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (show pre.length ≤ v - 1 by omega), hjk]
        have e2 : gateAt C v = post[v - 1 - pre.length] := by
          have h3 : v - pre.length = (v - 1 - pre.length) + 1 := by omega
          simp [gateAt, hC, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (show pre.length ≤ v by omega), h3, hjk]
        rw [e1, e2, Tc, ← er_eq]
      rw [hgate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hwlt := hrb v hv w hw
      by_cases hwn : w < x.length
      · have herw : eraseRedirect x.length m 0 w = w := by
          unfold eraseRedirect; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [Function.comp_apply, herw, circuit_wires_eq, circuit_wires_eq,
          getD_wiresFrom_lt _ x w (by omega), getD_wiresFrom_lt _ x w (by omega)]
      · let c := w - x.length
        have hwc : w = x.length + c := by omega
        have hcv : c < v := by omega
        have hcm : c ≠ m := by
          intro heq
          apply hnc
          rw [inCone_iff]
          exact ⟨hv, c, hcv, hwc ▸ hw, Or.inl heq.symm⟩
        have hnc_c : ¬ InCone x.length C m c := by
          intro hc
          apply hnc
          rw [inCone_iff]
          exact ⟨hv, c, hcv, hwc ▸ hw, Or.inr hc⟩
        rw [Function.comp_apply, hwc]
        exact ih c hcv (by omega) hcm hnc_c

lemma liftAt_struct (n : ℕ) (C : Circuit) (k p h : ℕ) (hk : k < C.gates.length)
    (hp : p < n + k) (hh : h < n + k) (hout : C.output < n + C.gates.length)
    (hmono : Monotone2 C) (hrb : ReadsBack n C) :
    Monotone2 (liftAt n C k p h) ∧ ReadsBack n (liftAt n C k p h) ∧
      (liftAt n C k p h).size = C.size := by
  obtain ⟨hmE, hrbE, hszE⟩ := eraseGate_struct n C k p hk hp hmono hrb
  let E := eraseGate n C k p
  have hElen : E.gates.length + 1 = C.gates.length := hszE
  have houtE : E.output < n + E.gates.length := by
    have : E.output = eraseRedirect n k p C.output := by
      simp [E, eraseGate, hk]
    rw [this, er_eq]
    unfold rn
    split_ifs <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    unfold liftAt at hg
    rcases List.mem_append.mp hg with h1 | h2
    · exact hmE g h1
    · rw [List.mem_singleton.mp h2]
      exact ⟨Or.inr rfl, by simp⟩
  · intro j hj w hw
    have hj' : j < E.gates.length + 1 := by
      simpa [E, liftAt] using hj
    by_cases hlt : j < E.gates.length
    · have hg : gateAt (liftAt n C k p h) j = gateAt E j := by
        simp only [E, liftAt, gateAt, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left hlt]
      rw [hg] at hw
      exact hrbE j hlt w hw
    · have heq : j = E.gates.length := by omega
      subst heq
      have hg : gateAt (liftAt n C k p h) E.gates.length = ⟨GateOp.or, [E.output, h]⟩ := by
        simp only [E, liftAt, gateAt, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right le_rfl]
        simp
      rw [hg] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact houtE
      · omega
  · show (E.gates ++ [{ op := GateOp.or, inputs := [E.output, h] : Gate }]).length = C.gates.length
    simp [hElen]

lemma liftAt_eval (n : ℕ) (C : Circuit) (k p i : ℕ) (hk : k < C.gates.length)
    (hp : p < n + k) (hi : i < k)
    (hg : (gateAt C k).op = GateOp.or ∧
      ((gateAt C k).inputs = [p, n + i] ∨ (gateAt C k).inputs = [n + i, p]))
    (hmono : Monotone2 C) (hrb : ReadsBack n C) (x : List Bool) (hx : x.length = n) :
    (C.eval x = true → (liftAt n C k p (n + i)).eval x = true) ∧
    ((C.wires x).getD (n + i) false = false → (liftAt n C k p (n + i)).eval x = C.eval x) := by
  subst hx
  let E := eraseGate x.length C k p
  have hElen : (E.wires x).length = x.length + E.gates.length := by
    rw [circuit_wires_eq, length_wiresFrom]
  have hleval : (liftAt x.length C k p (x.length + i)).eval x =
      (E.eval x || (E.wires x).getD (x.length + i) false) := by
    show (wiresFrom (E.gates ++ [{ op := GateOp.or, inputs := [E.output, x.length + i] : Gate }]) x).getD
      (x.length + E.gates.length) false = _
    rw [wiresFrom_append, wiresFrom_cons]
    show (E.wires x ++ [GateOp.or.eval [(E.wires x).getD E.output false,
      (E.wires x).getD (x.length + i) false]]).getD (x.length + E.gates.length) false = _
    rw [← hElen, getD_snoc, ite_eq_left rfl]
    simp [GateOp.eval, Circuit.eval]
  have hwi : (E.wires x).getD (x.length + i) false = (C.wires x).getD (x.length + i) false :=
    eraseGate_wires_lt x.length C k p hk x (x.length + i) (by omega)
  have hwk : (C.wires x).getD (x.length + k) false =
      ((C.wires x).getD p false || (C.wires x).getD (x.length + i) false) := by
    rw [getD_wires_gate_rb C x k hk hrb, hg.1]
    rcases hg.2 with h2 | h2
    · rw [h2]; simp [GateOp.eval]
    · rw [h2]; simp [GateOp.eval, Bool.or_comm]
  rw [hleval, hwi]
  constructor
  · intro hev
    cases hbi : (C.wires x).getD (x.length + i) false
    · have heq : (C.wires x).getD (x.length + k) false = (C.wires x).getD p false := by
        rw [hwk, hbi]; simp
      have hEeq := (eraseGate_eval_cmp x.length C k p hk hp hmono x rfl).2 heq
      rw [hEeq, hev]; rfl
    · simp
  · intro hbi
    have heq : (C.wires x).getD (x.length + k) false = (C.wires x).getD p false := by
      rw [hwk, hbi]; simp
    have hEeq := (eraseGate_eval_cmp x.length C k p hk hp hmono x rfl).2 heq
    rw [hEeq, hbi]; simp

def shiftIdx (k a : ℕ) : ℕ := if a < k then a else a + 1

lemma shiftIdx_inj (k : ℕ) : Function.Injective (shiftIdx k) := by
  intro a b hab
  unfold shiftIdx at hab
  split_ifs at hab <;> omega

lemma shiftIdx_ne (k a : ℕ) : shiftIdx k a ≠ k := by
  unfold shiftIdx; split_ifs <;> omega

lemma liftAt_inCone_imp (n : ℕ) (C : Circuit) (k p h : ℕ) (hk : k < C.gates.length)
    (hp : p < n + k) (hpin : p ∈ (gateAt C k).inputs) (hrb : ReadsBack n C) :
    ∀ a b, b < C.gates.length - 1 →
      InCone n (liftAt n C k p h) a b → InCone n C (shiftIdx k a) (shiftIdx k b) := by
  obtain ⟨pre, post, gj, hC, hpl, _⟩ := split_gates C.gates k hk
  subst hpl
  have hElen : (eraseGate n C pre.length p).gates.length = C.gates.length - 1 := by
    rw [eraseGate_bridge n C pre post gj hC p, hC]; simp
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | ind b ih =>
    intro hb hcone
    obtain ⟨_, c, hcb, hcin, hrest⟩ := (inCone_iff n _ a b).mp hcone
    have hab : a < b := (inCone_lt n _ a b hcone).1
    have hbc : b < (eraseGate n C pre.length p).gates.length := by omega
    have hgate_eq : gateAt (liftAt n C pre.length p h) b = gateAt (eraseGate n C pre.length p) b := by
      simp only [liftAt, gateAt, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hbc]
    rw [hgate_eq] at hcin
    by_cases hbk : b < pre.length
    · have hsb : shiftIdx pre.length b = b := ite_eq_left hbk
      have hsc : shiftIdx pre.length c = c := ite_eq_left (by omega)
      have hsa : shiftIdx pre.length a = a := ite_eq_left (by omega)
      have hge : gateAt (eraseGate n C pre.length p) b = gateAt C b := by
        rw [eraseGate_bridge n C pre post gj hC p]
        simp [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hbk]
      rw [hge] at hcin
      rw [hsb, hsa, inCone_iff]
      refine ⟨by omega, c, hcb, hcin, ?_⟩
      rcases hrest with rfl | hc
      · exact Or.inl rfl
      · have := ih c hcb a (by omega) hc
        rw [hsa, hsc] at this
        exact Or.inr this
    · have hsb : shiftIdx pre.length b = b + 1 := ite_eq_right hbk
      have hjk : b - pre.length < post.length := by
        rw [hC] at hb; simp only [List.length_append, List.length_cons] at hb; omega
      have hge : gateAt (eraseGate n C pre.length p) b =
          Tc (n + pre.length) p (post[b - pre.length]) := by
        rw [eraseGate_bridge n C pre post gj hC p]
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ b by omega), hjk]
      have hgc : gateAt C (b + 1) = post[b - pre.length] := by
        have h3 : b + 1 - pre.length = (b - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ b + 1 by omega), h3, hjk]
      rw [hge] at hcin
      obtain ⟨w, hw, hwrn⟩ := List.mem_map.mp hcin
      have hw' : w ∈ (gateAt C (b + 1)).inputs := by rw [hgc]; exact hw
      have hwlt := hrb (b + 1) (by omega) w hw'
      have ih_ac : shiftIdx pre.length a = shiftIdx pre.length c ∨
          InCone n C (shiftIdx pre.length a) (shiftIdx pre.length c) := by
        rcases hrest with rfl | hc
        · exact Or.inl rfl
        · exact Or.inr (ih c hcb a (by omega) hc)
      rw [hsb]
      unfold rn at hwrn
      by_cases hw1 : w < n + pre.length
      · rw [ite_eq_left hw1] at hwrn
        have hsc : shiftIdx pre.length c = c := ite_eq_left (by omega)
        rw [inCone_iff]
        refine ⟨by omega, c, by omega, hwrn ▸ hw', ?_⟩
        rwa [hsc] at ih_ac
      · by_cases hw2 : w = n + pre.length
        · rw [ite_eq_right hw1, ite_eq_left hw2] at hwrn
          have hsc : shiftIdx pre.length c = c := ite_eq_left (by omega)
          have hin_k : InCone n C (shiftIdx pre.length a) pre.length := by
            rw [inCone_iff]
            refine ⟨hk, c, by omega, hwrn ▸ hpin, ?_⟩
            rwa [hsc] at ih_ac
          rw [inCone_iff]
          exact ⟨by omega, pre.length, by omega, (by omega : n + pre.length = w) ▸ hw', Or.inr hin_k⟩
        · rw [ite_eq_right hw1, ite_eq_right hw2] at hwrn
          have hsc : shiftIdx pre.length c = c + 1 := ite_eq_right (by omega)
          rw [inCone_iff]
          refine ⟨by omega, c + 1, by omega, (by omega : n + (c + 1) = w) ▸ hw', ?_⟩
          rwa [hsc] at ih_ac

-- Section 4: The lexicographic measure mu

def isAndOp (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def andConePairs (C : Circuit) : Finset (ℕ × ℕ) :=
  (Finset.range C.size ×ˢ Finset.range C.size).filter fun p =>
    isAndOp (gateAt C p.2).op = true ∧ InCone 26 C p.1 p.2

def mu (C : Circuit) : ℕ := (andConePairs C).card

lemma mu_liftAt_lt (C : Circuit) (k p h j : ℕ) (hk : k < C.gates.length)
    (hp : p < 26 + k) (hpin : p ∈ (gateAt C k).inputs) (hrb : ReadsBack 26 C)
    (hj_and : (gateAt C j).op = GateOp.and) (hkj : InCone 26 C k j) :
    mu (liftAt 26 C k p h) < mu C := by
  let D := liftAt 26 C k p h
  have hDlen : D.size = C.size := by
    unfold D liftAt Circuit.size eraseGate
    rw [ite_eq_left hk]; simp; omega
  have hElen : (eraseGate 26 C k p).gates.length = C.gates.length - 1 := by
    unfold eraseGate; rw [ite_eq_left hk]; simp; omega
  have hlast_or : (gateAt D (C.gates.length - 1)).op = GateOp.or := by
    have h1 : gateAt D (eraseGate 26 C k p).gates.length =
        ⟨GateOp.or, [(eraseGate 26 C k p).output, h]⟩ := by
      simp [D, liftAt, gateAt, List.getD_eq_getElem?_getD]
    rw [← hElen, h1]
  have hop_shift : ∀ v < C.gates.length - 1, (gateAt D v).op = (gateAt C (shiftIdx k v)).op := by
    intro v hv
    obtain ⟨pre, post, gj, hC, hpl, _⟩ := split_gates C.gates k hk
    have hvE : v < (eraseGate 26 C k p).gates.length := by omega
    have h1 : gateAt D v = gateAt (eraseGate 26 C k p) v := by
      simp only [D, liftAt, gateAt, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hvE]
    rw [h1]
    have hvk_eq : shiftIdx k v = shiftIdx pre.length v := by rw [hpl]
    rw [hvk_eq, ← hpl, eraseGate_bridge 26 C pre post gj hC p]
    by_cases hvk : v < pre.length
    · rw [show shiftIdx pre.length v = v from ite_eq_left hvk]
      simp [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hvk]
    · rw [show shiftIdx pre.length v = v + 1 from ite_eq_right hvk]
      have hjk : v - pre.length < post.length := by
        rw [hC] at hv; simp only [List.length_append, List.length_cons] at hv; omega
      have e1 : gateAt ⟨pre ++ post.map (Tc (26 + pre.length) p), rn (26 + pre.length) p C.output⟩ v =
          Tc (26 + pre.length) p (post[v - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ v by omega), hjk]
      have e2 : gateAt C (v + 1) = post[v - pre.length] := by
        have h3 : v + 1 - pre.length = (v - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ v + 1 by omega), h3, hjk]
      rw [e1, e2]; rfl
  let f : ℕ × ℕ → ℕ × ℕ := fun q => (shiftIdx k q.1, shiftIdx k q.2)
  have hsub : (andConePairs D).image f ⊆ andConePairs C := by
    intro q hq
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hq
    simp only [andConePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab ⊢
    obtain ⟨⟨haD, hbD⟩, hband, hcone⟩ := hab
    have hb_ne : b ≠ C.gates.length - 1 := by
      intro heq
      rw [heq, hlast_or] at hband
      simp [isAndOp] at hband
    have hb_lt : b < C.gates.length - 1 := by
      change b < D.gates.length at hbD
      change D.gates.length = C.gates.length at hDlen
      omega
    have ha_lt : a < b := (inCone_lt 26 D a b hcone).1
    have hcone' := liftAt_inCone_imp 26 C k p h hk hp hpin hrb a b hb_lt hcone
    refine ⟨⟨?_, ?_⟩, ?_, hcone'⟩
    · show shiftIdx k a < C.gates.length; unfold shiftIdx; split_ifs <;> omega
    · show shiftIdx k b < C.gates.length; unfold shiftIdx; split_ifs <;> omega
    · rwa [← hop_shift b hb_lt]
  have hmem_kj : (k, j) ∈ andConePairs C := by
    have hjlt := (inCone_lt 26 C k j hkj).2
    simp only [andConePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      isAndOp_eq_true]
    exact ⟨⟨hk, hjlt⟩, hj_and, hkj⟩
  have hnot_mem : (k, j) ∉ (andConePairs D).image f := by
    intro hmem
    obtain ⟨⟨a, b⟩, _, heq⟩ := Finset.mem_image.mp hmem
    have : shiftIdx k a = k := congrArg Prod.fst heq
    exact shiftIdx_ne k a this
  have hss : (andConePairs D).image f ⊂ andConePairs C :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hnot_mem (h ▸ hmem_kj)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Prod.ext (shiftIdx_inj k (congrArg Prod.fst hxy)) (shiftIdx_inj k (congrArg Prod.snd hxy))
  unfold mu
  rw [← Finset.card_image_of_injective (andConePairs D) hinj]
  exact Finset.card_lt_card hss

lemma mu_set_input_only_le (C : Circuit) (i : ℕ) (hi : i < C.gates.length)
    (hi_and : (gateAt C i).op = GateOp.and) (g : Gate)
    (hg_op : g.op = GateOp.and) (hg_in : ∀ w ∈ g.inputs, w < 26) :
    mu { gates := C.gates.set i g, output := C.output } ≤ mu C := by
  let D : Circuit := { gates := C.gates.set i g, output := C.output }
  have hlen : D.size = C.size := List.length_set
  have hop : ∀ v, (gateAt D v).op = (gateAt C v).op := by
    intro v
    by_cases hvi : v = i
    · subst hvi
      have h1 : gateAt D v = g := by simp [D, gateAt, List.getD_eq_getElem?_getD, hi]
      rw [h1, hg_op, hi_and]
    · have h1 : gateAt D v = gateAt C v := by
        simp [D, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hvi)]
      rw [h1]
  apply Finset.card_le_card
  intro p hp
  simp only [andConePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
  refine ⟨⟨hlen ▸ hp.1.1, hlen ▸ hp.1.2⟩, ?_, ?_⟩
  · rw [← hop p.2]; exact hp.2.1
  · exact inCone_set_input_only 26 C i g hg_in p.1 p.2 hp.2.2

-- Section 5: PG(2, 3) finite geometry facts

def inc3 (p l : Fin 13) : Bool :=
  let d := (p.val + 13 - l.val) % 13
  d == 0 || d == 1 || d == 3 || d == 9

lemma mem_singerLines3_iff (p l : Fin 13) : p ∈ singerLines3 l ↔ inc3 p l = true := by
  revert p l; decide +kernel

lemma inc3_shift (p l c : Fin 13) : inc3 (p + c) (l + c) = inc3 p l := by
  revert p l c; decide +kernel

lemma singerLines3_shift (p l c : Fin 13) :
    p + c ∈ singerLines3 (l + c) ↔ p ∈ singerLines3 l := by
  rw [mem_singerLines3_iff, mem_singerLines3_iff, inc3_shift]

def shiftSet (c : Fin 13) (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Q.image (fun x => x + c)

lemma isQuadrangle_shift (c : Fin 13) (Q : Finset (Fin 13)) (hQ : IsQuadrangle singerLines3 Q) :
    IsQuadrangle singerLines3 (shiftSet c Q) := by
  have hinj : Function.Injective (fun x : Fin 13 => x + c) := fun a b h => add_right_cancel h
  refine ⟨?_, ?_⟩
  · rw [shiftSet, Finset.card_image_of_injective Q hinj]; exact hQ.1
  · intro l
    have hcard : (shiftSet c Q ∩ singerLines3 l).card = (Q ∩ singerLines3 (l - c)).card := by
      have heq : shiftSet c Q ∩ singerLines3 l = (Q ∩ singerLines3 (l - c)).image (fun x => x + c) := by
        ext x
        simp only [Finset.mem_inter, shiftSet, Finset.mem_image]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hx⟩
          refine ⟨a, ⟨ha, ?_⟩, rfl⟩
          have := (singerLines3_shift a (l - c) c).mp (by simpa using hx)
          exact this
        · rintro ⟨a, ⟨ha, hal⟩, rfl⟩
          refine ⟨⟨a, ha, rfl⟩, ?_⟩
          have := (singerLines3_shift a (l - c) c).mpr hal
          simpa using this
      rw [heq, Finset.card_image_of_injective _ hinj]
    rw [hcard]
    exact hQ.2 (l - c)

lemma mem_missLines_shift (c : Fin 13) (Q : Finset (Fin 13)) (l : Fin 13) :
    l + c ∈ missLines singerLines3 (shiftSet c Q) ↔ l ∈ missLines singerLines3 Q := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left,
    shiftSet, Finset.mem_image]
  constructor
  · intro h p hp hpQ
    exact h ((singerLines3_shift p l c).mpr hp) ⟨p, hpQ, rfl⟩
  · rintro h x hx ⟨p, hpQ, rfl⟩
    exact h ((singerLines3_shift p l c).mp hx) hpQ

def qBase1 : Finset (Fin 13) := {0, 1, 4, 6}
def qBase2 : Finset (Fin 13) := {0, 1, 5, 11}
def mBase1 : Finset (Fin 13) := {2, 7, 9}
def mBase2 : Finset (Fin 13) := {3, 6, 7}

lemma qBase1_quad : IsQuadrangle singerLines3 qBase1 := by decide +kernel
lemma qBase2_quad : IsQuadrangle singerLines3 qBase2 := by decide +kernel
lemma mBase1_sub : ∀ l ∈ mBase1, l ∈ missLines singerLines3 qBase1 := by decide +kernel
lemma mBase2_sub : ∀ l ∈ mBase2, l ∈ missLines singerLines3 qBase2 := by decide +kernel

lemma diff_pp_cover : ∀ d : Fin 13,
    (∃ a ∈ qBase1, ∃ b ∈ qBase1, a - b = d) ∨ (∃ a ∈ qBase2, ∃ b ∈ qBase2, a - b = d) := by
  decide +kernel

lemma diff_ll_cover : ∀ d : Fin 13,
    (∃ a ∈ mBase1, ∃ b ∈ mBase1, a - b = d) ∨ (∃ a ∈ mBase2, ∃ b ∈ mBase2, a - b = d) := by
  decide +kernel

lemma diff_pl_cover : ∀ d : Fin 13, inc3 d 0 = false →
    (∃ a ∈ qBase1, ∃ b ∈ mBase1, a - b = d) ∨ (∃ a ∈ qBase2, ∃ b ∈ mBase2, a - b = d) := by
  decide +kernel

def pgAdj (u v : Fin 26) : Prop :=
  (∃ (hu : u.val < 13) (hv : 13 ≤ v.val), inc3 ⟨u.val, hu⟩ ⟨v.val - 13, by omega⟩ = true) ∨
  (∃ (hv : v.val < 13) (hu : 13 ≤ u.val), inc3 ⟨v.val, hv⟩ ⟨u.val - 13, by omega⟩ = true)

def pgGraph : SimpleGraph (Fin 26) where
  Adj := pgAdj
  symm := ⟨by
    intro u v h
    rcases h with ⟨hu, hv, h⟩ | ⟨hv, hu, h⟩
    · exact Or.inr ⟨hu, hv, h⟩
    · exact Or.inl ⟨hv, hu, h⟩⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega⟩

def pgGraphAdjDec : DecidableRel pgGraph.Adj := fun u v => by
  unfold pgGraph pgAdj; dsimp only; infer_instance

lemma pg_no_c4_points : ∀ (p₁ p₂ l₁ l₂ : Fin 13), p₁ ≠ p₂ → l₁ ≠ l₂ →
    ¬ (inc3 p₁ l₁ = true ∧ inc3 p₁ l₂ = true ∧ inc3 p₂ l₁ = true ∧ inc3 p₂ l₂ = true) := by
  decide +kernel

lemma pg_c4_free : ∀ a b c d : Fin 26, a ≠ c → b ≠ d →
    ¬ (pgGraph.Adj a b ∧ pgGraph.Adj b c ∧ pgGraph.Adj c d ∧ pgGraph.Adj d a) := by
  intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
  by_cases ha : a.val < 13
  · rcases hab with ⟨_, hb, h1⟩ | ⟨_, ha', _⟩
    · rcases hbc with ⟨hb', _, _⟩ | ⟨hc, _, h2⟩
      · omega
      · rcases hcd with ⟨_, hd, h3⟩ | ⟨_, hc', _⟩
        · rcases hda with ⟨hd', _, _⟩ | ⟨_, _, h4⟩
          · omega
          · apply pg_no_c4_points ⟨a.val, ha⟩ ⟨c.val, hc⟩ ⟨b.val - 13, by omega⟩ ⟨d.val - 13, by omega⟩
            · intro heq; have hval : a.val = c.val := congrArg (Fin.val : Fin 13 → ℕ) heq
              exact hac (Fin.ext hval)
            · intro heq; have hval : b.val - 13 = d.val - 13 := congrArg (Fin.val : Fin 13 → ℕ) heq
              exact hbd (Fin.ext (by omega))
            · exact ⟨h1, h4, h2, h3⟩
        · omega
    · omega
  · have ha' : 13 ≤ a.val := by omega
    rcases hab with ⟨ha1, _, _⟩ | ⟨hb, _, h1⟩
    · omega
    · rcases hbc with ⟨_, hc, h2⟩ | ⟨_, hb', _⟩
      · rcases hcd with ⟨hc', _, _⟩ | ⟨hd, _, h3⟩
        · omega
        · rcases hda with ⟨_, _, h4⟩ | ⟨_, hd', _⟩
          · apply pg_no_c4_points ⟨b.val, hb⟩ ⟨d.val, hd⟩ ⟨a.val - 13, by omega⟩ ⟨c.val - 13, by omega⟩
            · intro heq; have hval : b.val = d.val := congrArg (Fin.val : Fin 13 → ℕ) heq
              exact hbd (Fin.ext hval)
            · intro heq; have hval : a.val - 13 = c.val - 13 := congrArg (Fin.val : Fin 13 → ℕ) heq
              exact hac (Fin.ext (by omega))
            · exact ⟨h1, h2, h4, h3⟩
          · omega
      · omega

lemma incidenceInput_getD (X Y : Finset (Fin 13)) (w : Fin 26) :
    (incidenceInput X Y).getD w.val false =
      if h : w.val < 13 then decide (⟨w.val, h⟩ ∈ X) else decide (⟨w.val - 13, by omega⟩ ∈ Y) := by
  unfold incidenceInput
  by_cases h : w.val < 13
  · rw [dite_eq_left h, List.getD_append _ _ _ _ (by simp [h]),
      List.getD_eq_getElem _ _ (by simp [h]), List.getElem_ofFn]
  · rw [dite_eq_right h]
    have hge : (List.ofFn fun p : Fin 13 => decide (p ∈ X)).length ≤ w.val := by simp; omega
    have hlt : w.val - 13 < (List.ofFn fun l : Fin 13 => decide (l ∈ Y)).length := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, List.length_ofFn,
      List.getElem?_ofFn, show w.val - 13 < 13 by omega, ↓reduceDIte, Option.getD_some]

lemma incidenceInput_len (X Y : Finset (Fin 13)) : (incidenceInput X Y).length = 26 := by
  simp [incidenceInput]

lemma fin_shift_eq {a b x y : Fin 13} (h : a - b = x - y) : b + (x - a) = y := by
  have h1 : a = b + (x - y) := eq_add_of_sub_eq' h
  rw [h1]; abel

lemma inc3_sub_zero (p l : Fin 13) : inc3 (p - l) 0 = inc3 p l := by
  have h1 : p - l + l = p := by abel
  have h2 : (0 : Fin 13) + l = l := by abel
  rw [← inc3_shift (p - l) 0 l, h1, h2]

lemma pg_nonedge_in_quad (u v : Fin 26) (hnuv : ¬ pgGraph.Adj u v) :
    ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧
      (incidenceInput Q (missLines singerLines3 Q)).getD u.val false = true ∧
      (incidenceInput Q (missLines singerLines3 Q)).getD v.val false = true := by
  by_cases hu : u.val < 13
  · by_cases hv : v.val < 13
    · let pu : Fin 13 := ⟨u.val, hu⟩
      let pv : Fin 13 := ⟨v.val, hv⟩
      rcases diff_pp_cover (pu - pv) with ⟨a, ha, b, hb, hab⟩ | ⟨a, ha, b, hb, hab⟩
      · refine ⟨shiftSet (pu - a) qBase1, isQuadrangle_shift _ _ qBase1_quad, ?_, ?_⟩
        · rw [incidenceInput_getD, dite_eq_left hu, decide_eq_true_eq]
          exact Finset.mem_image.mpr ⟨a, ha, by change a + (pu - a) = pu; abel⟩
        · rw [incidenceInput_getD, dite_eq_left hv, decide_eq_true_eq]
          exact Finset.mem_image.mpr ⟨b, hb, fin_shift_eq hab⟩
      · refine ⟨shiftSet (pu - a) qBase2, isQuadrangle_shift _ _ qBase2_quad, ?_, ?_⟩
        · rw [incidenceInput_getD, dite_eq_left hu, decide_eq_true_eq]
          exact Finset.mem_image.mpr ⟨a, ha, by change a + (pu - a) = pu; abel⟩
        · rw [incidenceInput_getD, dite_eq_left hv, decide_eq_true_eq]
          exact Finset.mem_image.mpr ⟨b, hb, fin_shift_eq hab⟩
    · let pu : Fin 13 := ⟨u.val, hu⟩
      let lv : Fin 13 := ⟨v.val - 13, by omega⟩
      have hni : inc3 pu lv = false := by
        cases h : inc3 pu lv
        · rfl
        · exfalso; exact hnuv (Or.inl ⟨hu, by omega, h⟩)
      have hni0 : inc3 (pu - lv) 0 = false := (inc3_sub_zero pu lv).trans hni
      rcases diff_pl_cover (pu - lv) hni0 with ⟨a, ha, b, hb, hab⟩ | ⟨a, ha, b, hb, hab⟩
      · refine ⟨shiftSet (pu - a) qBase1, isQuadrangle_shift _ _ qBase1_quad, ?_, ?_⟩
        · rw [incidenceInput_getD, dite_eq_left hu, decide_eq_true_eq]
          exact Finset.mem_image.mpr ⟨a, ha, by change a + (pu - a) = pu; abel⟩
        · rw [incidenceInput_getD, dite_eq_right hv, decide_eq_true_eq]
          have hbl : b + (pu - a) = lv := fin_shift_eq hab
          change lv ∈ missLines singerLines3 (shiftSet (pu - a) qBase1)
          rw [← hbl, mem_missLines_shift]
          exact mBase1_sub b hb
      · refine ⟨shiftSet (pu - a) qBase2, isQuadrangle_shift _ _ qBase2_quad, ?_, ?_⟩
        · rw [incidenceInput_getD, dite_eq_left hu, decide_eq_true_eq]
          exact Finset.mem_image.mpr ⟨a, ha, by change a + (pu - a) = pu; abel⟩
        · rw [incidenceInput_getD, dite_eq_right hv, decide_eq_true_eq]
          have hbl : b + (pu - a) = lv := fin_shift_eq hab
          change lv ∈ missLines singerLines3 (shiftSet (pu - a) qBase2)
          rw [← hbl, mem_missLines_shift]
          exact mBase2_sub b hb
  · by_cases hv : v.val < 13
    · let pv : Fin 13 := ⟨v.val, hv⟩
      let lu : Fin 13 := ⟨u.val - 13, by omega⟩
      have hni : inc3 pv lu = false := by
        cases h : inc3 pv lu
        · rfl
        · exfalso; exact hnuv (Or.inr ⟨hv, by omega, h⟩)
      have hni0 : inc3 (pv - lu) 0 = false := (inc3_sub_zero pv lu).trans hni
      rcases diff_pl_cover (pv - lu) hni0 with ⟨a, ha, b, hb, hab⟩ | ⟨a, ha, b, hb, hab⟩
      · refine ⟨shiftSet (pv - a) qBase1, isQuadrangle_shift _ _ qBase1_quad, ?_, ?_⟩
        · rw [incidenceInput_getD, dite_eq_right hu, decide_eq_true_eq]
          have hbl : b + (pv - a) = lu := fin_shift_eq hab
          change lu ∈ missLines singerLines3 (shiftSet (pv - a) qBase1)
          rw [← hbl, mem_missLines_shift]
          exact mBase1_sub b hb
        · rw [incidenceInput_getD, dite_eq_left hv, decide_eq_true_eq]
          exact Finset.mem_image.mpr ⟨a, ha, by change a + (pv - a) = pv; abel⟩
      · refine ⟨shiftSet (pv - a) qBase2, isQuadrangle_shift _ _ qBase2_quad, ?_, ?_⟩
        · rw [incidenceInput_getD, dite_eq_right hu, decide_eq_true_eq]
          have hbl : b + (pv - a) = lu := fin_shift_eq hab
          change lu ∈ missLines singerLines3 (shiftSet (pv - a) qBase2)
          rw [← hbl, mem_missLines_shift]
          exact mBase2_sub b hb
        · rw [incidenceInput_getD, dite_eq_left hv, decide_eq_true_eq]
          exact Finset.mem_image.mpr ⟨a, ha, by change a + (pv - a) = pv; abel⟩
    · let lu : Fin 13 := ⟨u.val - 13, by omega⟩
      let lv : Fin 13 := ⟨v.val - 13, by omega⟩
      rcases diff_ll_cover (lu - lv) with ⟨a, ha, b, hb, hab⟩ | ⟨a, ha, b, hb, hab⟩
      · refine ⟨shiftSet (lu - a) qBase1, isQuadrangle_shift _ _ qBase1_quad, ?_, ?_⟩
        · rw [incidenceInput_getD, dite_eq_right hu, decide_eq_true_eq]
          have hal : a + (lu - a) = lu := by abel
          have hmem : a + (lu - a) ∈ missLines singerLines3 (shiftSet (lu - a) qBase1) :=
            (mem_missLines_shift (lu - a) qBase1 a).mpr (mBase1_sub a ha)
          simpa only [hal] using hmem
        · rw [incidenceInput_getD, dite_eq_right hv, decide_eq_true_eq]
          have hbl : b + (lu - a) = lv := fin_shift_eq hab
          change lv ∈ missLines singerLines3 (shiftSet (lu - a) qBase1)
          rw [← hbl, mem_missLines_shift]
          exact mBase1_sub b hb
      · refine ⟨shiftSet (lu - a) qBase2, isQuadrangle_shift _ _ qBase2_quad, ?_, ?_⟩
        · rw [incidenceInput_getD, dite_eq_right hu, decide_eq_true_eq]
          have hal : a + (lu - a) = lu := by abel
          have hmem : a + (lu - a) ∈ missLines singerLines3 (shiftSet (lu - a) qBase2) :=
            (mem_missLines_shift (lu - a) qBase2 a).mpr (mBase2_sub a ha)
          simpa only [hal] using hmem
        · rw [incidenceInput_getD, dite_eq_right hv, decide_eq_true_eq]
          have hbl : b + (lu - a) = lv := fin_shift_eq hab
          change lv ∈ missLines singerLines3 (shiftSet (lu - a) qBase2)
          rw [← hbl, mem_missLines_shift]
          exact mBase2_sub b hb

lemma pg_inc_card : (incidences singerLines3).card = 52 := by decide +kernel

lemma pg_deg_pt : ∀ p : Fin 13, ((incidences singerLines3).filter fun e => e.1 = p).card = 4 := by
  decide +kernel

lemma pg_deg_ln : ∀ l : Fin 13, ((incidences singerLines3).filter fun e => e.2 = l).card = 4 := by
  decide +kernel

lemma pg_edge_card [DecidableRel pgGraph.Adj] : pgGraph.edgeFinset.card = 52 := by
  let f : Fin 13 × Fin 13 → Sym2 (Fin 26) := fun e => s(⟨e.1.val, by omega⟩, ⟨13 + e.2.val, by omega⟩)
  have heq : pgGraph.edgeFinset = (incidences singerLines3).image f := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image, incidences,
        Finset.mem_filter, Finset.mem_univ, true_and]
      change pgAdj u v ↔ _
      constructor
      · intro hadj
        rcases hadj with ⟨hu, hv, h⟩ | ⟨hv, hu, h⟩
        · refine ⟨(⟨u.val, hu⟩, ⟨v.val - 13, by omega⟩), (mem_singerLines3_iff _ _).mpr h, ?_⟩
          have h1 : (⟨u.val, by omega⟩ : Fin 26) = u := Fin.ext rfl
          have h2 : (⟨13 + (v.val - 13), by omega⟩ : Fin 26) = v := Fin.ext (by dsimp; omega)
          change s(⟨u.val, by omega⟩, ⟨13 + (v.val - 13), by omega⟩) = s(u, v)
          rw [h1, h2]
        · refine ⟨(⟨v.val, hv⟩, ⟨u.val - 13, by omega⟩), (mem_singerLines3_iff _ _).mpr h, ?_⟩
          have h1 : (⟨v.val, by omega⟩ : Fin 26) = v := Fin.ext rfl
          have h2 : (⟨13 + (u.val - 13), by omega⟩ : Fin 26) = u := Fin.ext (by dsimp; omega)
          change s(⟨v.val, by omega⟩, ⟨13 + (u.val - 13), by omega⟩) = s(u, v)
          rw [h1, h2, Sym2.eq_swap]
      · rintro ⟨⟨p, l⟩, hp, hfeq⟩
        rw [Sym2.eq_iff] at hfeq
        rcases hfeq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hu : u.val = p.val := (congrArg (Fin.val : Fin 26 → ℕ) h1).symm
          have hv : v.val = 13 + l.val := (congrArg (Fin.val : Fin 26 → ℕ) h2).symm
          have hp_eq : (⟨u.val, by omega⟩ : Fin 13) = p := Fin.ext hu
          have hl_eq : (⟨v.val - 13, by omega⟩ : Fin 13) = l := Fin.ext (by dsimp; omega)
          exact Or.inl ⟨by omega, by omega, by rw [hp_eq, hl_eq]; exact (mem_singerLines3_iff p l).mp hp⟩
        · have hv : v.val = p.val := (congrArg (Fin.val : Fin 26 → ℕ) h1).symm
          have hu : u.val = 13 + l.val := (congrArg (Fin.val : Fin 26 → ℕ) h2).symm
          have hp_eq : (⟨v.val, by omega⟩ : Fin 13) = p := Fin.ext hv
          have hl_eq : (⟨u.val - 13, by omega⟩ : Fin 13) = l := Fin.ext (by dsimp; omega)
          exact Or.inr ⟨by omega, by omega, by rw [hp_eq, hl_eq]; exact (mem_singerLines3_iff p l).mp hp⟩
  have hinj : Function.Injective f := by
    intro e₁ e₂ heq
    simp only [f, Sym2.eq_iff, Fin.ext_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (Fin.ext h1) (Fin.ext (by omega))
    · omega
  rw [heq, Finset.card_image_of_injective _ hinj, pg_inc_card]

lemma pg_vertex_cover_ge (T : Finset (Fin 26))
    (hT : ∀ u v : Fin 26, pgGraph.Adj u v → u ∈ T ∨ v ∈ T) : 13 ≤ T.card := by
  let TP : Finset (Fin 13) := Finset.univ.filter fun p => (⟨p.val, by omega⟩ : Fin 26) ∈ T
  let TL : Finset (Fin 13) := Finset.univ.filter fun l => (⟨13 + l.val, by omega⟩ : Fin 26) ∈ T
  have hTcard : TP.card + TL.card = T.card := by
    let T1 := T.filter fun u : Fin 26 => u.val < 13
    let T2 := T.filter fun u : Fin 26 => ¬ (u.val < 13)
    have h1 : T1.card + T2.card = T.card := by
      have hun : T1 ∪ T2 = T := by
        ext u; simp only [T1, T2, Finset.mem_union, Finset.mem_filter]
        by_cases h : u.val < 13 <;> simp [h]
      have hdis : Disjoint T1 T2 := by
        rw [Finset.disjoint_left]
        intro u hu1 hu2
        exact (Finset.mem_filter.mp hu2).2 (Finset.mem_filter.mp hu1).2
      rw [← Finset.card_union_of_disjoint hdis, hun]
    have hTP : TP.card = T1.card := by
      refine Finset.card_bij (fun p _ => (⟨p.val, by omega⟩ : Fin 26)) ?_ ?_ ?_
      · intro p hp
        simp only [TP, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact Finset.mem_filter.mpr ⟨hp, p.isLt⟩
      · intro a _ b _ h
        have hval : a.val = b.val := congrArg (Fin.val : Fin 26 → ℕ) h
        exact Fin.ext hval
      · intro u hu
        obtain ⟨huT, hult⟩ := Finset.mem_filter.mp hu
        exact ⟨⟨u.val, hult⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huT⟩, by ext; rfl⟩
    have hTL : TL.card = T2.card := by
      refine Finset.card_bij (fun l _ => (⟨13 + l.val, by omega⟩ : Fin 26)) ?_ ?_ ?_
      · intro l hl
        simp only [TL, Finset.mem_filter, Finset.mem_univ, true_and] at hl
        exact Finset.mem_filter.mpr ⟨hl, by dsimp; omega⟩
      · intro a _ b _ h
        have hval : 13 + a.val = 13 + b.val := congrArg (Fin.val : Fin 26 → ℕ) h
        exact Fin.ext (by omega)
      · intro u hu
        obtain ⟨huT, huge⟩ := Finset.mem_filter.mp hu
        refine ⟨⟨u.val - 13, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · convert huT using 1; ext; dsimp; omega
        · ext; dsimp; omega
    omega
  have hcov : incidences singerLines3 ⊆
      (TP.biUnion fun p => (incidences singerLines3).filter fun e => e.1 = p) ∪
      (TL.biUnion fun l => (incidences singerLines3).filter fun e => e.2 = l) := by
    intro e he
    have hadj : pgGraph.Adj ⟨e.1.val, by omega⟩ ⟨13 + e.2.val, by omega⟩ := by
      refine Or.inl ⟨e.1.isLt, by dsimp; omega, ?_⟩
      have hmem := (Finset.mem_filter.mp he).2
      have hinc : inc3 e.1 e.2 = true := (mem_singerLines3_iff e.1 e.2).mp hmem
      convert hinc using 2
      ext; dsimp; omega
    rcases hT _ _ hadj with hp | hl
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, Finset.mem_filter.mpr ⟨he, rfl⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨e.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, Finset.mem_filter.mpr ⟨he, rfl⟩⟩)
  have h52 : 52 ≤ 4 * (TP.card + TL.card) := by
    calc 52 = (incidences singerLines3).card := pg_inc_card.symm
      _ ≤ ((TP.biUnion fun p => (incidences singerLines3).filter fun e => e.1 = p) ∪
            (TL.biUnion fun l => (incidences singerLines3).filter fun e => e.2 = l)).card :=
          Finset.card_le_card hcov
      _ ≤ (TP.biUnion fun p => (incidences singerLines3).filter fun e => e.1 = p).card +
          (TL.biUnion fun l => (incidences singerLines3).filter fun e => e.2 = l).card :=
          Finset.card_union_le _ _
      _ ≤ (∑ p ∈ TP, ((incidences singerLines3).filter fun e => e.1 = p).card) +
          (∑ l ∈ TL, ((incidences singerLines3).filter fun e => e.2 = l).card) :=
          Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ = (∑ _p ∈ TP, 4) + (∑ _l ∈ TL, 4) := by
          congr 1 <;> apply Finset.sum_congr rfl <;> intro x _
          · exact pg_deg_pt x
          · exact pg_deg_ln x
      _ = 4 * (TP.card + TL.card) := by simp; ring
  omega

-- Section 6: Single-level lower bound (no AND in cone of AND implies size >= 64)

def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w - 1) ((gateAtPos n gs w).inputs.getD 0 (w - 1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w - 1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w - 1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  isAndOp (gateAtPos n gs w).op

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w - 1) i < w := by
  unfold clampWire; split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
      (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]; split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i + 1) x = x ⟨i, hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi),
    List.getD_eq_getElem (List.ofFn x) false (by simpa using hi), List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if isAndOp op then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval, isAndOp, vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval, isAndOp]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval, isAndOp]

lemma gateAtPos_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n + j + 1) = gs[j] := by
  unfold gateAtPos
  rw [show n + j + 1 - (n + 1) = j by omega, List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hne : ∀ j : Fin gs.length, (gs[j.val]).op = GateOp.and → (gs[j.val]).inputs ≠ [])
    (w : ℕ) (lo : n + 1 ≤ w) (hi : w < n + 1 + gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w - (n + 1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n + j + 1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAtPos_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n + j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 (hne ⟨j, hj⟩)
    (fun i => if i < n + j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n + j) (by simp)

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w; by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w; by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card := Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, by simpa using ha, by simpa using hsub, by simp⟩
    · refine ⟨{a, b}, ?_, by simpa using hsub, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]; exact Finset.mem_range.mpr hb
      · simp only [hiB, ite_true]; exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

lemma gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2; simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2; exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n + 1) (n + 1 + len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

lemma cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true → (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v → H (a w) u v ∧ H (b w) u v) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 → ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 :=
            (Finset.card_le_card (heq ▸ Finset.subset_union_left)).trans ht
          have htb : (S (b w)).card ≤ 1 :=
            (Finset.card_le_card (heq ▸ Finset.subset_union_right)).trans ht
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]; tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]; tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨ (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht; rw [feq, ite_eq_right ht] at hw; simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h; rw [feq, ite_eq_left ht, ite_eq_right h] at hw; omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]; simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using dag_union_bound f {r} B hstep

lemma edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v → H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

lemma edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true → ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true → (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w), (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha, hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c, hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u, hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c, hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v, hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c, h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha, hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf, hfa, hfb, hu]
      · simp [F, hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c, x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w, hk, hN, hA, how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS, hN, hk, hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w, t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w, hj, ht⟩)⟩
        rcases how with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · rcases spec w hw u hu v hv with ⟨he, ht⟩ | ⟨he, ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he, ht⟩ | ⟨he, ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

lemma total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v → H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v → H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true → ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T, hT, hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH
  exact ⟨T, hT, by omega⟩

-- Section 7: Problem-specific definitions and main proof

def rowQ (Q : Finset (Fin 13)) : List Bool :=
  incidenceInput Q (missLines singerLines3 Q)

def validC (C : Circuit) : Prop :=
  Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs singerLines3 C ∧
    ∀ Q, IsQuadrangle singerLines3 Q → C.eval (rowQ Q) = false

def innerC (C : Circuit) (i : ℕ) : Prop :=
  (gateAt C i).op = GateOp.and ∧
    ∃ j, (gateAt C j).op = GateOp.and ∧ InCone 26 C i j

def hardC (C : Circuit) : Prop :=
  (∃ i, innerC C i) ∧ ∀ i, innerC C i →
    (∃ Q, IsQuadrangle singerLines3 Q ∧ (C.wires (rowQ Q)).getD (26 + i) false = true) ∧
    2 ≤ ((incidences singerLines3).filter fun e =>
      ({ gates := C.gates.set i ⟨GateOp.or, []⟩, output := C.output : Circuit }).eval
        (incidenceInput {e.1} {e.2}) = false).card

lemma mem_set_or {α : Type*} (l : List α) (i : ℕ) (a x : α) (hx : x ∈ l.set i a) :
    x ∈ l ∨ x = a := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [List.getElem_set]
  by_cases hki : i = k
  · exact Or.inr (ite_eq_left hki)
  · rw [ite_eq_right hki]
    exact Or.inl (List.getElem_mem (by simpa using hk))

lemma valid_output_bounds (C : Circuit) (hC : validC C) :
    26 ≤ C.output ∧ C.output < 26 + C.size := by
  have h00 : (0 : Fin 13) ∈ singerLines3 0 := by decide +kernel
  have hpos : C.eval (incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}) = true :=
    hC.2.2.1 0 0 h00
  have hlt : C.output < 26 + C.size := by
    by_contra hge
    have hlen : (C.wires (incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)})).length =
        26 + C.size := by
      rw [circuit_wires_eq, length_wiresFrom, incidenceInput_len]; rfl
    have hev : C.eval (incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) {(0 : Fin 13)}) = false := by
      unfold Circuit.eval
      exact List.getD_eq_default _ _ (by omega)
    rw [hev] at hpos; cases hpos
  have hge26 : 26 ≤ C.output := by
    by_contra hlt26
    let u : Fin 26 := ⟨C.output, by omega⟩
    obtain ⟨Q, hQ, hu, _⟩ := pg_nonedge_in_quad u u (pgGraph.loopless.irrefl u)
    have hev : C.eval (rowQ Q) = true := by
      unfold Circuit.eval rowQ
      rw [circuit_wires_eq, getD_wiresFrom_lt _ _ C.output (by rw [incidenceInput_len]; omega)]
      exact hu
    have hneg := hC.2.2.2 Q hQ
    rw [hev] at hneg; cases hneg
  exact ⟨hge26, hlt⟩

lemma valid_eval_nonedge_false (C : Circuit) (hC : validC C) (u v : Fin 26)
    (hnuv : ¬ pgGraph.Adj u v) : C.eval (List.ofFn (pairBits u v)) = false := by
  obtain ⟨Q, hQ, hu, hv⟩ := pg_nonedge_in_quad u v hnuv
  cases h : C.eval (List.ofFn (pairBits u v))
  · rfl
  · exfalso
    have htrue : C.eval (rowQ Q) = true := by
      unfold Circuit.eval at h ⊢
      refine wiresFrom_mono C.gates (fun g hg => (legal_of_mono2 C hC.1 g hg).1)
        (List.ofFn (pairBits u v)) (rowQ Q) (by simp [rowQ, incidenceInput_len]) ?_ C.output h
      intro i hi
      by_cases hi26 : i < 26
      · rw [List.getD_eq_getElem _ _ (by simpa using hi26), List.getElem_ofFn] at hi
        simp only [pairBits, decide_eq_true_eq] at hi
        rcases hi with hiu | hiv
        · have : i = u.val := congrArg Fin.val hiu; subst this; exact hu
        · have : i = v.val := congrArg Fin.val hiv; subst this; exact hv
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi
    have hneg := hC.2.2.2 Q hQ
    rw [htrue] at hneg; cases hneg

lemma valid_eval_edge_true (C : Circuit) (hC : validC C) (u v : Fin 26)
    (huv : pgGraph.Adj u v) : C.eval (List.ofFn (pairBits u v)) = true := by
  have heq_input (p l : Fin 13) (hp : u = ⟨p.val, by omega⟩) (hl : v = ⟨13 + l.val, by omega⟩) :
      List.ofFn (pairBits u v) = incidenceInput {p} {l} := by
    apply List.ext_getElem
    · simp [incidenceInput_len]
    · intro i hi1 hi2
      have hi26 : i < 26 := by simpa using hi1
      have h1 : (List.ofFn (pairBits u v))[i]'hi1 = pairBits u v ⟨i, hi26⟩ := List.getElem_ofFn hi1
      have h2 : (incidenceInput {p} {l})[i]'hi2 = (incidenceInput {p} {l}).getD i false :=
        (List.getD_eq_getElem _ _ hi2).symm
      rw [h1, h2, incidenceInput_getD {p} {l} ⟨i, hi26⟩]
      simp only [pairBits, hp, hl, Fin.ext_iff, Finset.mem_singleton]
      by_cases hi13 : i < 13
      · rw [dite_eq_left hi13]
        simp only [decide_eq_decide]
        omega
      · rw [dite_eq_right hi13]
        simp only [decide_eq_decide]
        omega
  have hsymm : pairBits u v = pairBits v u := by
    funext z; simp [pairBits, or_comm]
  rcases huv with ⟨hu, hv, h⟩ | ⟨hv, hu, h⟩
  · let p : Fin 13 := ⟨u.val, hu⟩
    let l : Fin 13 := ⟨v.val - 13, by omega⟩
    rw [heq_input p l rfl (by ext; dsimp [l]; omega)]
    exact hC.2.2.1 l p ((mem_singerLines3_iff p l).mpr h)
  · let p : Fin 13 := ⟨v.val, hv⟩
    let l : Fin 13 := ⟨u.val - 13, by omega⟩
    have heq2 : List.ofFn (pairBits v u) = incidenceInput {p} {l} := by
      apply List.ext_getElem
      · simp [incidenceInput_len]
      · intro i hi1 hi2
        have hi26 : i < 26 := by simpa using hi1
        have h1 : (List.ofFn (pairBits v u))[i]'hi1 = pairBits v u ⟨i, hi26⟩ := List.getElem_ofFn hi1
        have h2 : (incidenceInput {p} {l})[i]'hi2 = (incidenceInput {p} {l}).getD i false :=
          (List.getD_eq_getElem _ _ hi2).symm
        rw [h1, h2, incidenceInput_getD {p} {l} ⟨i, hi26⟩]
        simp only [pairBits, Fin.ext_iff, Finset.mem_singleton, p, l]
        by_cases hi13 : i < 13
        · rw [dite_eq_left hi13]; simp only [decide_eq_decide]; omega
        · rw [dite_eq_right hi13]; simp only [decide_eq_decide]; omega
    rw [hsymm, heq2]
    exact hC.2.2.1 l p ((mem_singerLines3_iff p l).mpr h)

lemma exists_inner_of_min_size (D : Circuit) (hD : validC D) (hsz : D.size < 64)
    (hmin : ∀ E, validC E → D.size ≤ E.size) : ∃ i, innerC D i := by
  by_contra hNoInner
  have hNo : ∀ i j, (gateAt D i).op = GateOp.and → (gateAt D j).op = GateOp.and →
      ¬ InCone 26 D i j := fun i j hi hj h => hNoInner ⟨i, hi, j, hj, h⟩
  obtain ⟨hout_ge, hout_lt⟩ := valid_output_bounds D hD
  let outG := D.output - 26
  have houtG_lt : outG < D.gates.length := by change D.output < 26 + D.gates.length at hout_lt; omega
  have hout_eq : D.output = 26 + outG := by omega
  have hlive : ∀ g < D.gates.length, g = outG ∨ InCone 26 D g outG := by
    intro g hg
    by_contra hdead
    have hdead' : g ≠ outG ∧ ¬ InCone 26 D g outG := not_or.mp hdead
    let E := eraseGate 26 D g 0
    obtain ⟨hmE, hrbE, hszE⟩ := eraseGate_struct 26 D g 0 hg (by omega) hD.1 hD.2.1
    have heval : ∀ x : List Bool, x.length = 26 → E.eval x = D.eval x := by
      intro x hx
      have h1 := eraseGate_dead_eval 26 (by omega) D g hg hD.2.1 x hx outG houtG_lt hdead'.1.symm hdead'.2
      have hEout : E.output = eraseRedirect 26 g 0 D.output := by simp [E, eraseGate, hg]
      unfold Circuit.eval
      rw [hEout, hout_eq]
      exact h1
    have hEv : validC E := by
      refine ⟨hmE, hrbE, ?_, ?_⟩
      · intro l p hp
        rw [heval _ (incidenceInput_len _ _)]
        exact hD.2.2.1 l p hp
      · intro Q hQ
        rw [heval (rowQ Q) (incidenceInput_len _ _)]
        exact hD.2.2.2 Q hQ
    have hEsz : E.size + 1 = D.size := hszE
    have := hmin E hEv
    omega
  have hand_below : ∀ g < D.gates.length, (gateAt D g).op = GateOp.and →
      ∀ x : List Bool, x.length = 26 →
        (D.wires x).getD (26 + g) false = true → D.eval x = true := by
    intro g hg hg_and x hx hgt
    have hreach : ∀ v < D.gates.length, (g = v ∨ InCone 26 D g v) →
        (D.wires x).getD (26 + v) false = true := by
      intro v
      induction v using Nat.strong_induction_on with
      | ind v ih =>
        intro hv hvg
        rcases hvg with rfl | hc
        · exact hgt
        · have hv_or : (gateAt D v).op = GateOp.or := by
            have hleg := (legal_of_mono2 D hD.1 _ (List.getElem_mem hv)).1
            rw [← gateAt_eq D v hv] at hleg
            rcases hleg with hand | hor
            · exact (hNo g v hg_and hand hc).elim
            · exact hor
          obtain ⟨_, c, hcv, hcin, hrest⟩ := (inCone_iff 26 D g v).mp hc
          have hct : (D.wires x).getD (26 + c) false = true :=
            ih c hcv (by omega) hrest
          rw [← hx, getD_wires_gate_rb D x v hv (hx ▸ hD.2.1), ev_or _ _ hv_or]
          exact ⟨26 + c, hcin, hct⟩
    unfold Circuit.eval
    rw [hout_eq]
    exact hreach outG houtG_lt (hlive g hg)
  have hne : ∀ j : Fin D.gates.length, (D.gates[j.val]).op = GateOp.and →
      (D.gates[j.val]).inputs ≠ [] := by
    intro j hj hempty
    have hgt : (D.wires (rowQ qBase1)).getD (26 + j.val) false = true := by
      have hlen : (rowQ qBase1).length = 26 := incidenceInput_len _ _
      rw [← hlen, getD_wires_gate_rb D (rowQ qBase1) j.val j.isLt (hlen ▸ hD.2.1),
        gateAt_eq D j.val j.isLt, hempty, hj]
      rfl
    have hev := hand_below j.val j.isLt (by rw [gateAt_eq D j.val j.isLt]; exact hj)
      (rowQ qBase1) (incidenceInput_len _ _) hgt
    have hneg := hD.2.2.2 qBase1 qBase1_quad
    rw [hev] at hneg; cases hneg
  have hroot_read (x : Fin 26 → Bool) :
      posRead D.gates (clampWire (26 + D.gates.length) D.output) x = D.eval (List.ofFn x) := by
    rw [pos_clamp]
    have hlt : D.output < 26 + D.gates.length := hout_lt
    rw [ite_eq_left hlt]; rfl
  have hsingle_false (u : Fin 26) : D.eval (List.ofFn (singletonBits u)) = false := by
    have heq : singletonBits u = pairBits u u := by funext z; simp [singletonBits, pairBits]
    rw [heq]
    exact valid_eval_nonedge_false D hD u u (pgGraph.loopless.irrefl u)
  have hops := legal_of_mono2 D hD.1
  letI : DecidableRel pgGraph.Adj := pgGraphAdjDec
  obtain ⟨T, hT, hcard⟩ := total_from_model 26 27 (27 + D.gates.length)
    (clampWire (26 + D.gates.length) D.output) D.gates.length pgGraph
    (supports D.gates) (fun w u v => posRead D.gates w (pairBits u v) = true)
    (firstWire 26 D.gates) (secondWire 26 D.gates) (andPos 26 D.gates)
    pg_c4_free
    (by unfold clampWire; split <;> omega)
    (by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and, hroot_read] at hu
      rw [hsingle_false u] at hu; cases hu)
    (fun u v huv => by rw [hroot_read]; exact valid_eval_edge_true D hD u v huv)
    (fun w hw => by
      cases w with
      | zero => simp [supports, posRead]
      | succ i =>
        have hi : i < 26 := by omega
        have hs : supports D.gates (i + 1) = {⟨i, hi⟩} := by
          ext u; simp [supports, pos_input D.gates i hi, singletonBits, eq_comm]
        simp [hs])
    (fun w u v hw h => by
      cases w with
      | zero => simp [posRead] at h
      | succ i =>
        have hi : i < 26 := by omega
        simp [supports, pos_input D.gates i hi, pairBits, singletonBits] at h ⊢
        exact h)
    (fun w lo _ => clamp_lt w _ (by omega))
    (fun w lo _ => clamp_lt w _ (by omega))
    (fun w lo hi ha => by
      ext u
      simp only [Finset.mem_union, supports, Finset.mem_filter, Finset.mem_univ, true_and,
        pos_gate D.gates hops hne w lo hi, ha, Bool.false_eq_true, ite_false, Bool.or_eq_true])
    (fun w u v lo hi ha h => by
      simpa only [pos_gate D.gates hops hne w lo hi, ha, Bool.false_eq_true, ite_false,
        Bool.or_eq_true] using h)
    (fun w u v lo hi ha h => by
      simpa only [pos_gate D.gates hops hne w lo hi, ha, ite_true, Bool.and_eq_true] using h)
    (fun w lo hi ha => by
      let j := w - 27
      have hj : j < D.gates.length := by omega
      have hw : w = 26 + j + 1 := by omega
      have hj_and : (gateAt D j).op = GateOp.and := by
        rw [hw] at ha
        simp only [andPos, gateAtPos_index D.gates j hj, isAndOp_eq_true] at ha
        rw [gateAt_eq D j hj]; exact ha
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      simp only [supports, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [hw] at hu
      have hgt : (D.wires (List.ofFn (singletonBits u))).getD (26 + j) false = true := hu
      have hev := hand_below j hj hj_and (List.ofFn (singletonBits u)) (by simp) hgt
      rw [hsingle_false u] at hev; cases hev)
    (fun w lo hi ha u hu v hv => by
      let j := w - 27
      have hj : j < D.gates.length := by omega
      have hw : w = 26 + j + 1 := by omega
      have hj_and : (gateAt D j).op = GateOp.and := by
        rw [hw] at ha
        simp only [andPos, gateAtPos_index D.gates j hj, isAndOp_eq_true] at ha
        rw [gateAt_eq D j hj]; exact ha
      have hpos_t : posRead D.gates w (pairBits u v) = true := by
        simp only [pos_gate D.gates hops hne w lo hi, ha, ite_true, Bool.and_eq_true]
        have hm := pos_mono (n := 26) D.gates (fun g hg => (hops g hg).1)
        refine ⟨?_, ?_⟩
        · apply hm _ (singletonBits u) (pairBits u v) _ (Finset.mem_filter.mp hu).2
          intro z hz; simp only [singletonBits, decide_eq_true_eq] at hz; simp [pairBits, hz]
        · apply hm _ (singletonBits v) (pairBits u v) _ (Finset.mem_filter.mp hv).2
          intro z hz; simp only [singletonBits, decide_eq_true_eq] at hz; simp [pairBits, hz]
      rw [hw] at hpos_t
      have hev := hand_below j hj hj_and (List.ofFn (pairBits u v)) (by simp) hpos_t
      by_contra hnuv
      have hnf := valid_eval_nonedge_false D hD u v hnuv
      rw [hev] at hnf; cases hnf)
    (gate_partition_count 26 D.gates.length (andPos 26 D.gates) (supports D.gates))
  have h52 := pg_edge_card
  have h13 := pg_vertex_cover_ge T hT
  change D.gates.length < 64 at hsz
  omega

lemma shrink_clean_inner (E : Circuit) (hE : validC E) (i : ℕ) (hinn : innerC E i)
    (hclean : ∀ Q, IsQuadrangle singerLines3 Q → (E.wires (rowQ Q)).getD (26 + i) false = false) :
    ∃ E', validC E' ∧ (E'.size < E.size ∨ (E'.size = E.size ∧ mu E' < mu E)) := by
  obtain ⟨hi_and, j, hj_and, hij⟩ := hinn
  obtain ⟨k, hk, hkin, hkj⟩ := inCone_first_step 26 E i j hij
  have hik : 26 + i < 26 + k := hE.2.1 k hk (26 + i) hkin
  have hk_leg := legal_of_mono2 E hE.1 _ (List.getElem_mem hk)
  rw [← gateAt_eq E k hk] at hk_leg
  rcases hk_leg.1 with hk_and | hk_or
  · let E' := eraseGate 26 E k (26 + i)
    obtain ⟨hm', hrb', hsz'⟩ := eraseGate_struct 26 E k (26 + i) hk hik hE.1 hE.2.1
    have hE'v : validC E' := by
      refine ⟨hm', hrb', ?_, ?_⟩
      · intro l p hp
        have hcmp := (eraseGate_eval_cmp 26 E k (26 + i) hk hik hE.1
          (incidenceInput {p} {l}) (incidenceInput_len _ _)).1
        refine hcmp ?_ (hE.2.2.1 l p hp)
        intro hkt
        have hlen : (incidenceInput {p} {l}).length = 26 := incidenceInput_len _ _
        rw [← hlen, getD_wires_gate_rb E _ k hk (hlen ▸ hE.2.1), ev_and _ _ hk_and] at hkt
        exact hkt (26 + i) hkin
      · intro Q hQ
        have hbi : (E.wires (rowQ Q)).getD (26 + i) false = false := hclean Q hQ
        have hbk : (E.wires (rowQ Q)).getD (26 + k) false = false := by
          cases h : (E.wires (rowQ Q)).getD (26 + k) false
          · rfl
          · exfalso
            have hlen : (rowQ Q).length = 26 := incidenceInput_len _ _
            rw [← hlen, getD_wires_gate_rb E _ k hk (hlen ▸ hE.2.1), ev_and _ _ hk_and] at h
            have := h (26 + i) hkin
            rw [hbi] at this; cases this
        have hcmp := (eraseGate_eval_cmp 26 E k (26 + i) hk hik hE.1
          (rowQ Q) (incidenceInput_len _ _)).2 (by rw [hbk, hbi])
        rw [hcmp]
        exact hE.2.2.2 Q hQ
    have hE'sz : E'.size + 1 = E.size := hsz'
    exact ⟨E', hE'v, Or.inl (by omega)⟩
  · have hkj_cone : InCone 26 E k j := by
      rcases hkj with rfl | hc
      · rw [hk_or] at hj_and; cases hj_and
      · exact hc
    have hlen_in : (gateAt E k).inputs.length ≤ 2 := hk_leg.2
    cases hin_eq : (gateAt E k).inputs with
    | nil => rw [hin_eq] at hkin; simp at hkin
    | cons a rest =>
      cases rest with
      | nil =>
        have ha : a = 26 + i := (List.mem_singleton.mp (hin_eq ▸ hkin)).symm
        subst ha
        let E' := eraseGate 26 E k (26 + i)
        obtain ⟨hm', hrb', hsz'⟩ := eraseGate_struct 26 E k (26 + i) hk hik hE.1 hE.2.1
        have heq_all : ∀ x : List Bool, x.length = 26 → E'.eval x = E.eval x := by
          intro x hx
          apply (eraseGate_eval_cmp 26 E k (26 + i) hk hik hE.1 x hx).2
          have hrb_x : ReadsBack x.length E := hx ▸ hE.2.1
          have hgx := getD_wires_gate_rb E x k hk hrb_x
          rw [hx] at hgx
          rw [hgx, hk_or, hin_eq]
          simp [GateOp.eval]
        have hE'v : validC E' := by
          refine ⟨hm', hrb', ?_, ?_⟩
          · intro l p hp; rw [heq_all _ (incidenceInput_len _ _)]; exact hE.2.2.1 l p hp
          · intro Q hQ; rw [heq_all (rowQ Q) (incidenceInput_len _ _)]; exact hE.2.2.2 Q hQ
        have hE'sz : E'.size + 1 = E.size := hsz'
        exact ⟨E', hE'v, Or.inl (by omega)⟩
      | cons b rest2 =>
        have hr2 : rest2 = [] := List.length_eq_zero_iff.mp (by rw [hin_eq] at hlen_in; simpa using hlen_in)
        subst hr2
        have hmem_ab : 26 + i = a ∨ 26 + i = b := by
          rw [hin_eq] at hkin; simpa using hkin
        have hpair : ∃ p, p < 26 + k ∧ p ∈ (gateAt E k).inputs ∧
            ((gateAt E k).inputs = [p, 26 + i] ∨ (gateAt E k).inputs = [26 + i, p]) := by
          rcases hmem_ab with rfl | rfl
          · refine ⟨b, hE.2.1 k hk b (by rw [hin_eq]; simp), by rw [hin_eq]; simp, Or.inr hin_eq⟩
          · refine ⟨a, hE.2.1 k hk a (by rw [hin_eq]; simp), by rw [hin_eq]; simp, Or.inl hin_eq⟩
        obtain ⟨p, hp, hpin, hgs⟩ := hpair
        have hout := (valid_output_bounds E hE).2
        let E' := liftAt 26 E k p (26 + i)
        obtain ⟨hm', hrb', hsz'⟩ := liftAt_struct 26 E k p (26 + i) hk hp hik hout hE.1 hE.2.1
        have hE'v : validC E' := by
          refine ⟨hm', hrb', ?_, ?_⟩
          · intro l pt hpt
            exact (liftAt_eval 26 E k p i hk hp (by omega) ⟨hk_or, hgs⟩ hE.1 hE.2.1
              (incidenceInput {pt} {l}) (incidenceInput_len _ _)).1 (hE.2.2.1 l pt hpt)
          · intro Q hQ
            rw [(liftAt_eval 26 E k p i hk hp (by omega) ⟨hk_or, hgs⟩ hE.1 hE.2.1
              (rowQ Q) (incidenceInput_len _ _)).2 (hclean Q hQ)]
            exact hE.2.2.2 Q hQ
        have hmu : mu E' < mu E := mu_liftAt_lt E k p (26 + i) j hk hp hpin hE.2.1 hj_and hkj_cone
        exact ⟨E', hE'v, Or.inr ⟨hsz', hmu⟩⟩

lemma hard_of_min (D : Circuit) (hD : validC D) (hsz : D.size < 64)
    (hminSize : ∀ E, validC E → D.size ≤ E.size)
    (hminMu : ∀ E, validC E → E.size = D.size → mu D ≤ mu E) : hardC D := by
  refine ⟨exists_inner_of_min_size D hD hsz hminSize, ?_⟩
  intro i hinn
  refine ⟨?_, ?_⟩
  · by_contra hnoQ
    have hclean : ∀ Q, IsQuadrangle singerLines3 Q →
        (D.wires (rowQ Q)).getD (26 + i) false = false := by
      intro Q hQ
      cases h : (D.wires (rowQ Q)).getD (26 + i) false
      · rfl
      · exact (hnoQ ⟨Q, hQ, h⟩).elim
    obtain ⟨E', hE'v, hred⟩ := shrink_clean_inner D hD i hinn hclean
    rcases hred with hlt | ⟨heq, hmu⟩
    · exact Nat.not_lt_of_ge (hminSize E' hE'v) hlt
    · exact Nat.not_lt_of_ge (hminMu E' hE'v heq) hmu
  · by_contra hlt2
    obtain ⟨hi_and, j, hj_and, hij⟩ := hinn
    have hi_lt : i < D.gates.length := lt_length_of_gateAt_and D i hi_and
    let D₀ : Circuit := { gates := D.gates.set i ⟨GateOp.or, []⟩, output := D.output }
    let Bad := (incidences singerLines3).filter fun e =>
      D₀.eval (incidenceInput {e.1} {e.2}) = false
    have hcard_le1 : Bad.card ≤ 1 := by
      change ¬ 2 ≤ Bad.card at hlt2; omega
    have hD₀_i_false : ∀ x : List Bool, x.length = 26 → (D₀.wires x).getD (26 + i) false = false := by
      intro x hx
      have hiD₀ : i < D₀.gates.length := by simp [D₀, hi_lt]
      rw [← hx, circuit_wires_eq, getD_wiresFrom_gate D₀.gates x i hiD₀]
      have hg : D₀.gates[i]'hiD₀ = ⟨GateOp.or, []⟩ := by simp [D₀]
      rw [hg]; rfl
    have hD₀_quad : ∀ Q, IsQuadrangle singerLines3 Q → D₀.eval (rowQ Q) = false := by
      intro Q hQ
      cases h : D₀.eval (rowQ Q)
      · rfl
      · exfalso
        have hDtrue : D.eval (rowQ Q) = true := by
          have hself := set_self_eq D i hi_lt
          have hlenQ : (rowQ Q).length = 26 := incidenceInput_len _ _
          have hmono_cmp := wires_set_mono D hD.1 i hi_lt ⟨GateOp.or, []⟩ D.gates[i]
            (rowQ Q) D₀ D rfl hself.symm (fun ht => by
              rw [hlenQ] at ht
              rw [hD₀_i_false (rowQ Q) hlenQ] at ht; cases ht)
          exact hmono_cmp D.output h
        have hneg := hD.2.2.2 Q hQ
        rw [hDtrue] at hneg; cases hneg
    have hD₀_mono : Monotone2 D₀ := by
      intro g hg
      rcases mem_set_or D.gates i ⟨GateOp.or, []⟩ g hg with h1 | h2
      · exact hD.1 g h1
      · rw [h2]; exact ⟨Or.inr rfl, by simp⟩
    have hD₀_rb : ReadsBack 26 D₀ := by
      intro m hm w hw
      rw [List.length_set] at hm
      by_cases hmi : m = i
      · subst hmi
        have hg : gateAt D₀ m = ⟨GateOp.or, []⟩ := by
          simp [D₀, gateAt, List.getD_eq_getElem?_getD, hi_lt]
        rw [hg] at hw; simp at hw
      · have hg : gateAt D₀ m = gateAt D m := by
          simp [D₀, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hmi)]
        rw [hg] at hw
        exact hD.2.1 m hm w hw
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard_le1 with h0 | h1
    · have hD₀_pos : RightOnIncidentPairs singerLines3 D₀ := by
        intro l p hp
        have hmem : (p, l) ∈ incidences singerLines3 :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
        cases h : D₀.eval (incidenceInput {p} {l})
        · exfalso
          have hbad : (p, l) ∈ Bad := Finset.mem_filter.mpr ⟨hmem, h⟩
          have : Bad.card ≠ 0 := Finset.card_ne_zero.mpr ⟨(p, l), hbad⟩
          omega
        · rfl
      have hD₀_v : validC D₀ := ⟨hD₀_mono, hD₀_rb, hD₀_pos, hD₀_quad⟩
      have hij₀ : InCone 26 D₀ i j := (inCone_set_ge 26 D i ⟨GateOp.or, []⟩ i j le_rfl).mpr hij
      obtain ⟨k, hk, hkin, _⟩ := inCone_first_step 26 D₀ i j hij₀
      have hik : 26 + i < 26 + k := hD₀_rb k hk (26 + i) hkin
      have hk_leg := legal_of_mono2 D₀ hD₀_mono _ (List.getElem_mem hk)
      rw [← gateAt_eq D₀ k hk] at hk_leg
      have hshrink (a : ℕ) (ha : a < 26 + k)
          (heq : ∀ x : List Bool, x.length = 26 →
            (D₀.wires x).getD (26 + k) false = (D₀.wires x).getD a false) : False := by
        let E' := eraseGate 26 D₀ k a
        obtain ⟨hm', hrb', hsz'⟩ := eraseGate_struct 26 D₀ k a hk ha hD₀_mono hD₀_rb
        have hEv : validC E' := by
          refine ⟨hm', hrb', ?_, ?_⟩
          · intro l p hp
            rw [(eraseGate_eval_cmp 26 D₀ k a hk ha hD₀_mono _ (incidenceInput_len _ _)).2
              (heq _ (incidenceInput_len _ _))]
            exact hD₀_pos l p hp
          · intro Q hQ
            rw [(eraseGate_eval_cmp 26 D₀ k a hk ha hD₀_mono (rowQ Q) (incidenceInput_len _ _)).2
              (heq (rowQ Q) (incidenceInput_len _ _))]
            exact hD₀_quad Q hQ
        have hE'sz : E'.size + 1 = D₀.size := hsz'
        have hD₀_sz : D₀.size = D.size := List.length_set
        have := hminSize E' hEv
        omega
      rcases hk_leg.1 with hk_and | hk_or
      · apply hshrink (26 + i) hik
        intro x hx
        rw [hD₀_i_false x hx]
        cases h : (D₀.wires x).getD (26 + k) false
        · rfl
        · exfalso
          rw [← hx, getD_wires_gate_rb D₀ x k hk (hx ▸ hD₀_rb), ev_and _ _ hk_and] at h
          have := h (26 + i) hkin
          rw [hD₀_i_false x hx] at this; cases this
      · have hlen_in : (gateAt D₀ k).inputs.length ≤ 2 := hk_leg.2
        cases hin_eq : (gateAt D₀ k).inputs with
        | nil => rw [hin_eq] at hkin; simp at hkin
        | cons a rest =>
          cases rest with
          | nil =>
            have ha : a = 26 + i := (List.mem_singleton.mp (hin_eq ▸ hkin)).symm
            subst ha
            apply hshrink (26 + i) hik
            intro x hx
            have hgx := getD_wires_gate_rb D₀ x k hk (hx ▸ hD₀_rb)
            rw [hx] at hgx
            rw [hgx, hk_or, hin_eq]
            simp [GateOp.eval]
          | cons b rest2 =>
            have hr2 : rest2 = [] :=
              List.length_eq_zero_iff.mp (by rw [hin_eq] at hlen_in; simpa using hlen_in)
            subst hr2
            have hmem_ab : 26 + i = a ∨ 26 + i = b := by rw [hin_eq] at hkin; simpa using hkin
            rcases hmem_ab with rfl | rfl
            · apply hshrink b (hD₀_rb k hk b (by rw [hin_eq]; simp))
              intro x hx
              have hgx := getD_wires_gate_rb D₀ x k hk (hx ▸ hD₀_rb)
              rw [hx] at hgx
              rw [hgx, hk_or, hin_eq]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false]
              rw [hD₀_i_false x hx]; simp
            · apply hshrink a (hD₀_rb k hk a (by rw [hin_eq]; simp))
              intro x hx
              have hgx := getD_wires_gate_rb D₀ x k hk (hx ▸ hD₀_rb)
              rw [hx] at hgx
              rw [hgx, hk_or, hin_eq]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false]
              rw [hD₀_i_false x hx]; simp
    · obtain ⟨⟨p, l⟩, hBad⟩ := Finset.card_eq_one.mp h1
      have hpl_mem : (p, l) ∈ incidences singerLines3 :=
        (Finset.mem_filter.mp (hBad ▸ Finset.mem_singleton_self (p, l))).1
      have hpl_inc : p ∈ singerLines3 l := (Finset.mem_filter.mp hpl_mem).2
      let g₁ : Gate := ⟨GateOp.and, [p.val, 13 + l.val]⟩
      let D₁ : Circuit := { gates := D.gates.set i g₁, output := D.output }
      have hD₁_sz : D₁.size = D.size := List.length_set
      have hD₁_mono : Monotone2 D₁ := by
        intro g hg
        rcases mem_set_or D.gates i g₁ g hg with hmem | rfl
        · exact hD.1 g hmem
        · exact ⟨Or.inl rfl, by simp [g₁]⟩
      have hD₁_rb : ReadsBack 26 D₁ := by
        intro m hm w hw
        rw [List.length_set] at hm
        by_cases hmi : m = i
        · subst hmi
          have hg : gateAt D₁ m = g₁ := by
            simp [D₁, gateAt, List.getD_eq_getElem?_getD, hi_lt]
          rw [hg] at hw
          simp only [g₁, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;> omega
        · have hg : gateAt D₁ m = gateAt D m := by
            simp [D₁, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hmi)]
          rw [hg] at hw
          exact hD.2.1 m hm w hw
      have hD₁_i_val (x : List Bool) (hx : x.length = 26) :
          (D₁.wires x).getD (26 + i) false = (x.getD p.val false && x.getD (13 + l.val) false) := by
        have hi1 : i < D₁.gates.length := by simp [D₁, hi_lt]
        rw [← hx, getD_wires_gate_rb D₁ x i hi1 (hx ▸ hD₁_rb)]
        have hg : gateAt D₁ i = g₁ := by
          simp [D₁, gateAt, List.getD_eq_getElem?_getD, hi_lt]
        rw [hg]
        simp only [g₁, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true]
        rw [circuit_wires_eq, getD_wiresFrom_lt _ _ p.val (by omega),
          getD_wiresFrom_lt _ _ (13 + l.val) (by omega)]
      have hD₁_i_quad (Q : Finset (Fin 13)) : (D₁.wires (rowQ Q)).getD (26 + i) false = false := by
        rw [hD₁_i_val (rowQ Q) (incidenceInput_len _ _)]
        have hp_bit : (rowQ Q).getD p.val false = decide (p ∈ Q) := by
          have := incidenceInput_getD Q (missLines singerLines3 Q) ⟨p.val, by omega⟩
          simpa [rowQ, p.isLt] using this
        have hl_bit : (rowQ Q).getD (13 + l.val) false = decide (l ∈ missLines singerLines3 Q) := by
          have := incidenceInput_getD Q (missLines singerLines3 Q) ⟨13 + l.val, by omega⟩
          have h13 : ¬ (13 + l.val < 13) := by omega
          rw [dite_eq_right h13] at this
          simpa [rowQ] using this
        rw [hp_bit, hl_bit]
        by_cases hpQ : p ∈ Q
        · have hlM : l ∉ missLines singerLines3 Q := by
            intro hlm
            have hdisj := (Finset.mem_filter.mp hlm).2
            exact Finset.disjoint_left.mp hdisj hpl_inc hpQ
          simp [hpQ, hlM]
        · simp [hpQ]
      have hD₁_pos : RightOnIncidentPairs singerLines3 D₁ := by
        intro l' p' hp'
        by_cases heq : (p', l') = (p, l)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          have h1 : (D₁.wires (incidenceInput {p'} {l'})).getD (26 + i) false = true := by
            rw [hD₁_i_val _ (incidenceInput_len _ _)]
            have hp_bit : (incidenceInput {p'} {l'}).getD p'.val false = true := by
              have := incidenceInput_getD {p'} {l'} ⟨p'.val, by omega⟩
              simpa [p'.isLt] using this
            have hl_bit : (incidenceInput {p'} {l'}).getD (13 + l'.val) false = true := by
              have := incidenceInput_getD {p'} {l'} ⟨13 + l'.val, by omega⟩
              have h13 : ¬ (13 + l'.val < 13) := by omega
              rw [dite_eq_right h13] at this
              simpa using this
            rw [hp_bit, hl_bit]; rfl
          have hself := set_self_eq D i hi_lt
          have hcmp := wires_set_mono D hD.1 i hi_lt D.gates[i] g₁
            (incidenceInput {p'} {l'}) D D₁ hself.symm rfl
            (fun _ => by rw [incidenceInput_len]; exact h1)
          exact hcmp D.output (hD.2.2.1 l' p' hp')
        · have hD₀_true : D₀.eval (incidenceInput {p'} {l'}) = true := by
            cases h : D₀.eval (incidenceInput {p'} {l'})
            · exfalso
              have hmem : (p', l') ∈ Bad :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'⟩, h⟩
              rw [hBad, Finset.mem_singleton] at hmem
              exact heq hmem
            · rfl
          have hcmp := wires_set_mono D hD.1 i hi_lt ⟨GateOp.or, []⟩ g₁
            (incidenceInput {p'} {l'}) D₀ D₁ rfl rfl (fun ht => by
              rw [incidenceInput_len] at ht
              rw [hD₀_i_false _ (incidenceInput_len _ _)] at ht; cases ht)
          exact hcmp D.output hD₀_true
      have hD₁_quad : ∀ Q, IsQuadrangle singerLines3 Q → D₁.eval (rowQ Q) = false := by
        intro Q hQ
        cases h : D₁.eval (rowQ Q)
        · rfl
        · exfalso
          have hself := set_self_eq D i hi_lt
          have hlenQ : (rowQ Q).length = 26 := incidenceInput_len _ _
          have hcmp := wires_set_mono D hD.1 i hi_lt g₁ D.gates[i]
            (rowQ Q) D₁ D rfl hself.symm (fun ht => by
              rw [hlenQ] at ht
              rw [hD₁_i_quad Q] at ht; cases ht)
          have hDtrue : D.eval (rowQ Q) = true := hcmp D.output h
          have hneg := hD.2.2.2 Q hQ
          rw [hDtrue] at hneg; cases hneg
      have hD₁_v : validC D₁ := ⟨hD₁_mono, hD₁_rb, hD₁_pos, hD₁_quad⟩
      have hD₁_inner : innerC D₁ i := by
        have hij1 : InCone 26 D₁ i j := (inCone_set_ge 26 D i g₁ i j le_rfl).mpr hij
        have hji : j ≠ i := by have := (inCone_lt 26 D i j hij).1; omega
        have hj1 : (gateAt D₁ j).op = GateOp.and := by
          have hg : gateAt D₁ j = gateAt D j := by
            simp [D₁, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hji)]
          rw [hg]; exact hj_and
        have hi1 : (gateAt D₁ i).op = GateOp.and := by
          have hg : gateAt D₁ i = g₁ := by
            simp [D₁, gateAt, List.getD_eq_getElem?_getD, hi_lt]
          rw [hg]
        exact ⟨hi1, j, hj1, hij1⟩
      have hD₁_mu : mu D₁ ≤ mu D :=
        mu_set_input_only_le D i hi_lt hi_and g₁ rfl (fun w hw => by
          simp only [g₁, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;> omega)
      obtain ⟨D₂, hD₂v, hred⟩ := shrink_clean_inner D₁ hD₁_v i hD₁_inner (fun Q _ => hD₁_i_quad Q)
      rcases hred with hlt | ⟨heq, hmu⟩
      · exact Nat.not_lt_of_ge (hminSize D₂ hD₂v) (by omega)
      · exact Nat.not_lt_of_ge (hminMu D₂ hD₂v (by omega)) (by omega)

end PEqualNP.Outside.L_meta_4145_aux

theorem PEqualNP.Outside.L_meta_4145 : have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x4 → x3.eval (x2 x4) = Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ (x6 : ℕ), x4 x5 x6) ∧ ∀ (x6 : ℕ), x4 x5 x6 → (∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x8 ∧ (x5.wires (x2 x8)).getD ((26 : ℕ) + x6) Bool.false = Bool.true) ∧ (2 : ℕ) ≤ {x8 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x8.1} {x8.2}) = Bool.false}.card; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x6.size < (64 : ℕ) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x3 x9 ∧ x9.size ≤ x6.size ∧ x5 x9 := by
  classical
  intro x1 x2 x3 x4 x5 C hC hsz
  have hC' : PEqualNP.Outside.L_meta_4145_aux.validC C := hC
  have hexS : ∃ s : ℕ, ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.Outside.L_meta_4145_aux.validC E ∧ E.size = s := ⟨C.size, C, hC', rfl⟩
  let s₀ := Nat.find hexS
  have hs₀_le : s₀ ≤ C.size := Nat.find_min' hexS ⟨C, hC', rfl⟩
  obtain ⟨E₀, hE₀, hE₀s⟩ := Nat.find_spec hexS
  have hexM : ∃ m : ℕ, ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.Outside.L_meta_4145_aux.validC E ∧ E.size = s₀ ∧
      PEqualNP.Outside.L_meta_4145_aux.mu E = m :=
    ⟨PEqualNP.Outside.L_meta_4145_aux.mu E₀, E₀, hE₀, hE₀s, rfl⟩
  let m₀ := Nat.find hexM
  obtain ⟨D, hD, hDs, hDm⟩ := Nat.find_spec hexM
  have hminSize : ∀ E, PEqualNP.Outside.L_meta_4145_aux.validC E → D.size ≤ E.size := by
    intro E hE
    rw [hDs]
    exact Nat.find_min' hexS ⟨E, hE, rfl⟩
  have hminMu : ∀ E, PEqualNP.Outside.L_meta_4145_aux.validC E → E.size = D.size →
      PEqualNP.Outside.L_meta_4145_aux.mu D ≤ PEqualNP.Outside.L_meta_4145_aux.mu E := by
    intro E hE hEs
    rw [hDm]
    exact Nat.find_min' hexM ⟨E, hE, hEs.trans hDs, rfl⟩
  have hhard := PEqualNP.Outside.L_meta_4145_aux.hard_of_min D hD (by omega) hminSize hminMu
  exact ⟨D, hD, by omega, hhard⟩
