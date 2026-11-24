import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3026

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4
lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  unfold gateAt; simp [List.getD_eq_getElem?_getD, hk]

lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hlen _ hmem)
  exact ⟨hao _ hmem, ⟨a, b, hab⟩, hrb k hk⟩

lemma wv_big (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wv n C x w = false := by
  unfold wv
  rw [wires_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [foldl_len]; simp; omega

lemma wv_mono (n : ℕ) (C : Circuit) (hC : AO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : ∀ w, wv n C x w = true → wv n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    rcases Nat.lt_or_ge w n with h1 | h1
    · rw [wv_input n C x w h1] at h; rw [wv_input n C y w h1]; exact hxy _ h
    rcases Nat.lt_or_ge w (n + C.gates.length) with h2 | h2
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨hop, ⟨a, b, hab⟩, hrb⟩ := hC j hj
      have ha : a < n + j := hrb a (by simp [hab])
      have hb : b < n + j := hrb b (by simp [hab])
      rw [wv_rec n C x (aob hC) j hj, hab] at h
      rw [wv_rec n C y (aob hC) j hj, hab]
      rcases hop with hop | hop <;> rw [hop] at h ⊢
      · rw [eval_and_pair] at h ⊢
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨ih a ha h.1, ih b hb h.2⟩
      · rw [eval_or_pair] at h ⊢
        simp only [Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · exact Or.inl (ih a ha h)
        · exact Or.inr (ih b hb h)
    · rw [wv_big n C x w h2] at h; exact absurd h (by simp)

def RV (n : ℕ) (C : Circuit) (w : ℕ) (v : Fin n) : Prop :=
  (v : ℕ) = w ∨ (n ≤ w ∧ ∃ k, k < C.gates.length ∧ (k = w - n ∨ InCone n C k (w - n)) ∧
    (v : ℕ) ∈ (gateAt C k).inputs)

lemma RV_gate (n : ℕ) (C : Circuit) (hC : AO2 n C) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : (gateAt C j).inputs = [a, b]) (v : Fin n) :
    RV n C (n + j) v ↔ RV n C a v ∨ RV n C b v := by
  have ha : a < n + j := (hC j hj).2.2 a (by simp [hab])
  have hb : b < n + j := (hC j hj).2.2 b (by simp [hab])
  have hv := v.isLt
  constructor
  · rintro (h | ⟨_, k, hk, hk2, hin⟩)
    · omega
    · rw [Nat.add_sub_cancel_left] at hk2
      rcases hk2 with rfl | hk2
      · rw [hab] at hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · rw [inCone_iff] at hk2
        obtain ⟨_, k', hk', hin', h3⟩ := hk2
        rw [hab] at hin'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin'
        have hR : RV n C (n + k') v := by
          refine Or.inr ⟨by omega, k, hk, ?_, hin⟩
          rw [Nat.add_sub_cancel_left]; exact h3
        rcases hin' with h | h
        · rw [h] at hR; exact Or.inl hR
        · rw [h] at hR; exact Or.inr hR
  · have key : ∀ c, c ∈ (gateAt C j).inputs → c < n + j → RV n C c v → RV n C (n + j) v := by
      intro c hc hcj h
      rcases h with h | ⟨hnc, k, hk, hk2, hin⟩
      · refine Or.inr ⟨by omega, j, hj, Or.inl (by omega), ?_⟩
        rw [h]; exact hc
      · refine Or.inr ⟨by omega, k, hk, Or.inr ?_, hin⟩
        rw [Nat.add_sub_cancel_left, inCone_iff]
        refine ⟨hj, c - n, by omega, ?_, hk2⟩
        rw [show n + (c - n) = c by omega]; exact hc
    rintro (h | h)
    · exact key a (by simp [hab]) ha h
    · exact key b (by simp [hab]) hb h

lemma wv_local (n : ℕ) (C : Circuit) (hC : AO2 n C) (x y : Fin n → Bool) :
    ∀ w, (∀ v, RV n C w v → x v = y v) → wv n C x w = wv n C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    rcases Nat.lt_or_ge w n with h1 | h1
    · rw [wv_input n C x w h1, wv_input n C y w h1]; exact h ⟨w, h1⟩ (Or.inl rfl)
    rcases Nat.lt_or_ge w (n + C.gates.length) with h2 | h2
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨hop, ⟨a, b, hab⟩, hrb⟩ := hC j hj
      have ha : a < n + j := hrb a (by simp [hab])
      have hb : b < n + j := hrb b (by simp [hab])
      rw [wv_rec n C x (aob hC) j hj, wv_rec n C y (aob hC) j hj, hab]
      have e1 := ih a ha (fun v hv => h v ((RV_gate n C hC j a b hj hab v).2 (Or.inl hv)))
      have e2 := ih b hb (fun v hv => h v ((RV_gate n C hC j a b hj hab v).2 (Or.inr hv)))
      simp only [List.map_cons, List.map_nil, e1, e2]
    · rw [wv_big n C x w h2, wv_big n C y w h2]

lemma wv_zero (n : ℕ) (C : Circuit) (hC : AO2 n C) : ∀ w, wv n C (fun _ => false) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with h1 | h1
    · rw [wv_input n C _ w h1]
    rcases Nat.lt_or_ge w (n + C.gates.length) with h2 | h2
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨hop, ⟨a, b, hab⟩, hrb⟩ := hC j hj
      have ha : a < n + j := hrb a (by simp [hab])
      have hb : b < n + j := hrb b (by simp [hab])
      rw [wv_rec n C _ (aob hC) j hj, hab]
      rcases hop with hop | hop <;> rw [hop]
      · rw [eval_and_pair, ih a ha]; rfl
      · rw [eval_or_pair, ih a ha, ih b hb]; rfl
    · rw [wv_big n C _ w h2]

lemma wv_out (n : ℕ) (C : Circuit) (hC : AO2 n C) (y : Fin n → Bool) (w : ℕ)
    (h : ∀ v, RV n C w v → y v = false) : wv n C y w = false := by
  rw [wv_local n C hC y (fun _ => false) w h]; exact wv_zero n C hC w

lemma wv_true_var (n : ℕ) (C : Circuit) (hC : AO2 n C) (y : Fin n → Bool) (w : ℕ)
    (h : wv n C y w = true) : ∃ v, RV n C w v ∧ y v = true := by
  by_contra hne
  push_neg at hne
  rw [wv_out n C hC y w (fun v hv => by simpa using hne v hv)] at h
  exact absurd h (by simp)

abbrev IOS (n : ℕ) (C : Circuit) (g h : ℕ) : Prop := g = h ∨ InCone n C g h

lemma ios_trans (n : ℕ) (C : Circuit) (a b c : ℕ) (h1 : IOS n C a b) (h2 : IOS n C b c) :
    IOS n C a c := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  · exact Or.inr (inCone_trans n C a b h1 c h2)

lemma ios_le (n : ℕ) (C : Circuit) (a b : ℕ) (h : IOS n C a b) : a ≤ b := by
  rcases h with rfl | h
  · exact le_refl _
  · exact (inCone_lt n C a b h).1.le

lemma RV_mono (n : ℕ) (C : Circuit) (g h : ℕ) (hgh : IOS n C g h) (v : Fin n)
    (hv : RV n C (n + g) v) : RV n C (n + h) v := by
  have hvl := v.isLt
  rcases hv with hv | ⟨_, k, hk, hk2, hin⟩
  · omega
  refine Or.inr ⟨by omega, k, hk, ?_, hin⟩
  rw [Nat.add_sub_cancel_left] at hk2 ⊢
  exact ios_trans n C k g h hk2 hgh

def unit {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def pr {n : ℕ} (u v : Fin n) : Fin n → Bool := fun i => decide (i = u ∨ i = v)

lemma pr_comm {n : ℕ} (u v : Fin n) : pr u v = pr v u := by
  funext i; simp [pr, or_comm]

lemma unit_le_pr1 {n : ℕ} (u v : Fin n) : ∀ i, unit u i = true → pr u v i = true := by
  intro i h; simp [unit, pr] at h ⊢; exact Or.inl h

lemma unit_le_pr2 {n : ℕ} (u v : Fin n) : ∀ i, unit v i = true → pr u v i = true := by
  intro i h; simp [unit, pr] at h ⊢; exact Or.inr h

lemma bool3 (a b c : Bool) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) : False := by
  cases a <;> cases b <;> cases c <;> simp_all

def RO (n : ℕ) (C : Circuit) (c : ℕ) : Prop :=
  (∀ x j1 j2, IOS n C j1 c → IOS n C j2 c → x ∈ (gateAt C j1).inputs →
    x ∈ (gateAt C j2).inputs → j1 = j2) ∧
  (∀ j a, IOS n C j c → (gateAt C j).inputs ≠ [a, a])

lemma par (n : ℕ) (C : Circuit) (c : ℕ) (hR : RO n C c) (g h q : ℕ) (hgh : InCone n C g h)
    (hh : IOS n C h c) (hq : IOS n C q c) (hin : n + g ∈ (gateAt C q).inputs) : IOS n C q h := by
  obtain ⟨r, _, _, hrin, hr⟩ := inCone_reader n C g h hgh
  have hrc : IOS n C r c := ios_trans n C r h c hr hh
  have := hR.1 _ _ _ hq hrc hin hrin
  rw [this]; exact hr

lemma chain (n : ℕ) (C : Circuit) (c : ℕ) (hR : RO n C c) :
    ∀ g g' k, IOS n C g c → IOS n C g' c → IOS n C k g → IOS n C k g' →
      IOS n C g g' ∨ IOS n C g' g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro g' k hg hg' hkg hkg'
    rcases hkg with rfl | hkg
    · exact Or.inl hkg'
    rw [inCone_iff] at hkg
    obtain ⟨hglen, j, hjg, hjin, hkj⟩ := hkg
    have hjg' : InCone n C j g := by rw [inCone_iff]; exact ⟨hglen, j, hjg, hjin, Or.inl rfl⟩
    have hjc : IOS n C j c := ios_trans n C j g c (Or.inr hjg') hg
    rcases ih j hjg g' k hjc hg' hkj hkg' with h | h
    · rcases h with rfl | h
      · exact Or.inr (Or.inr hjg')
      · exact Or.inl (par n C c hR j g' g h hg' hg hjin)
    · exact Or.inr (ios_trans n C g' j g h (Or.inr hjg'))

lemma disj (n : ℕ) (C : Circuit) (hC : AO2 n C) (c : ℕ) (hR : RO n C c) (g a b : ℕ)
    (hg : IOS n C g c) (hglen : g < C.gates.length) (hab : (gateAt C g).inputs = [a, b])
    (v : Fin n) (hva : RV n C a v) (hvb : RV n C b v) : False := by
  have ha : a < n + g := (hC g hglen).2.2 a (by simp [hab])
  have hb : b < n + g := (hC g hglen).2.2 b (by simp [hab])
  have hne : a ≠ b := fun h => hR.2 g a hg (by rw [hab, h])
  have gin : ∀ x, x ∈ (gateAt C g).inputs → n ≤ x → IOS n C (x - n) c ∧ InCone n C (x - n) g := by
    intro x hx hnx
    have hxg := (hC g hglen).2.2 x hx
    have : InCone n C (x - n) g := by
      rw [inCone_iff]
      exact ⟨hglen, x - n, by omega, by rw [show n + (x - n) = x by omega]; exact hx, Or.inl rfl⟩
    exact ⟨ios_trans n C _ g c (Or.inr this) hg, this⟩
  have rd : ∀ x, x ∈ (gateAt C g).inputs → RV n C x v →
      ∃ k, IOS n C k c ∧ (v : ℕ) ∈ (gateAt C k).inputs ∧
        ((k = g ∧ (v : ℕ) = x) ∨ (n ≤ x ∧ IOS n C k (x - n))) := by
    intro x hx h
    rcases h with h | ⟨hnx, k, _, hk2, hin⟩
    · exact ⟨g, hg, by rw [h]; exact hx, Or.inl ⟨rfl, h⟩⟩
    · obtain ⟨h1, _⟩ := gin x hx hnx
      exact ⟨k, ios_trans n C k (x - n) c hk2 h1, hin, Or.inr ⟨hnx, hk2⟩⟩
  obtain ⟨ka, hka, hvka, hca⟩ := rd a (by simp [hab]) hva
  obtain ⟨kb, hkb, hvkb, hcb⟩ := rd b (by simp [hab]) hvb
  have hk := hR.1 _ _ _ hka hkb hvka hvkb
  subst hk
  rcases hca with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hcb with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact hne (h2.symm.trans h4)
  · have := ios_le n C _ _ h4; omega
  · have := ios_le n C _ _ h2; omega
  · obtain ⟨hac, _⟩ := gin a (by simp [hab]) h1
    obtain ⟨hbc, _⟩ := gin b (by simp [hab]) h3
    rcases chain n C c hR (a - n) (b - n) ka hac hbc h2 h4 with h | h
    · rcases h with h | h
      · exact hne (by omega)
      · have := par n C c hR (a - n) (b - n) g h hbc hg
          (by rw [show n + (a - n) = a by omega]; simp [hab])
        have := ios_le n C _ _ this; omega
    · rcases h with h | h
      · exact hne (by omega)
      · have := par n C c hR (b - n) (a - n) g h hac hg
          (by rw [show n + (b - n) = b by omega]; simp [hab])
        have := ios_le n C _ _ this; omega

lemma comparable (n : ℕ) (C : Circuit) (c : ℕ) (hR : RO n C c) (g g' : ℕ) (v : Fin n)
    (hg : IOS n C g c) (hg' : IOS n C g' c) (h1 : RV n C (n + g) v) (h2 : RV n C (n + g') v) :
    IOS n C g g' ∨ IOS n C g' g := by
  have hv := v.isLt
  rcases h1 with h1 | ⟨_, k, _, hk, hin⟩
  · omega
  rcases h2 with h2 | ⟨_, k', _, hk', hin'⟩
  · omega
  rw [Nat.add_sub_cancel_left] at hk hk'
  have hkc := ios_trans n C k g c hk hg
  have hkc' := ios_trans n C k' g' c hk' hg'
  have := hR.1 _ _ _ hkc hkc' hin hin'
  subst this
  exact chain n C c hR g g' k hg hg' hk hk'

lemma pass (n : ℕ) (C : Circuit) (hC : AO2 n C) (c : ℕ) (hR : RO n C c) (g : ℕ) :
    ∀ h, IOS n C g h → IOS n C h c → ∃ e : Bool, ∀ y : Fin n → Bool,
      (∀ v, ¬ RV n C (n + g) v → y v = false) → wv n C y (n + h) = (e && wv n C y (n + g)) := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hgh hhc
    rcases hgh with rfl | hgh
    · exact ⟨true, fun y _ => by simp⟩
    rw [inCone_iff] at hgh
    obtain ⟨hhlen, j, hjh, hjin, hgj⟩ := hgh
    have hjh' : InCone n C j h := by rw [inCone_iff]; exact ⟨hhlen, j, hjh, hjin, Or.inl rfl⟩
    have hjc : IOS n C j c := ios_trans n C j h c (Or.inr hjh') hhc
    obtain ⟨e, he⟩ := ih j hjh hgj hjc
    obtain ⟨hop, ⟨a, b, hab⟩, _⟩ := hC h hhlen
    have other : ∀ o, ((gateAt C h).inputs = [n + j, o] ∨ (gateAt C h).inputs = [o, n + j]) →
        ∀ y : Fin n → Bool, (∀ v, ¬ RV n C (n + g) v → y v = false) → wv n C y o = false := by
      intro o ho y hy
      apply wv_out n C hC y o
      intro v hv
      apply hy v
      intro hg
      have hj := RV_mono n C g j hgj v hg
      rcases ho with ho | ho
      · exact disj n C hC c hR h (n + j) o hhc hhlen ho v hj hv
      · exact disj n C hC c hR h o (n + j) hhc hhlen ho v hv hj
    rw [hab] at hjin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjin
    rcases hjin with hj | hj
    · have ho := other b (Or.inl (by rw [hab, hj]))
      rcases hop with hop | hop
      · refine ⟨false, fun y hy => ?_⟩
        rw [wv_rec n C y (aob hC) h hhlen, hab, hop, eval_and_pair, ho y hy]; simp
      · refine ⟨e, fun y hy => ?_⟩
        rw [wv_rec n C y (aob hC) h hhlen, hab, hop, eval_or_pair, ho y hy, ← hj, he y hy]; simp
    · have ho := other a (Or.inr (by rw [hab, hj]))
      rcases hop with hop | hop
      · refine ⟨false, fun y hy => ?_⟩
        rw [wv_rec n C y (aob hC) h hhlen, hab, hop, eval_and_pair, ho y hy]; simp
      · refine ⟨e, fun y hy => ?_⟩
        rw [wv_rec n C y (aob hC) h hhlen, hab, hop, eval_or_pair, ho y hy, ← hj, he y hy]; simp

lemma join (n : ℕ) (C : Circuit) (hC : AO2 n C) (c : ℕ) (hc : c < C.gates.length)
    (hR : RO n C c) (p l : Fin n) (h1 : wv n C (pr p l) (n + c) = true)
    (h2 : wv n C (unit p) (n + c) = false) (h3 : wv n C (unit l) (n + c) = false) :
    ∃ a, IOS n C a c ∧ a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      (∀ y : Fin n → Bool, (∀ v, ¬ RV n C (n + a) v → y v = false) →
        wv n C y (n + c) = wv n C y (n + a)) ∧
      ∃ hA hB, ((gateAt C a).inputs = [hA, hB] ∨ (gateAt C a).inputs = [hB, hA]) ∧
        RV n C hA p ∧ RV n C hB l ∧ wv n C (unit p) hA = true ∧ wv n C (unit l) hB = true := by
  classical
  let P : ℕ → Prop := fun k => IOS n C k c ∧ wv n C (pr p l) (n + k) = true ∧
    wv n C (unit p) (n + k) = false ∧ wv n C (unit l) (n + k) = false
  have hex : ∃ k, P k := ⟨c, Or.inl rfl, h1, h2, h3⟩
  have ha : P (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, ¬ P k := fun k hk => Nat.find_min hex hk
  generalize Nat.find hex = a at ha hmin
  obtain ⟨hac, ha1, ha2, ha3⟩ := ha
  have halen : a < C.gates.length := lt_of_le_of_lt (ios_le n C a c hac) hc
  obtain ⟨hop, ⟨x1, x2, hx⟩, hrb⟩ := hC a halen
  have split : ∀ x ∈ (gateAt C a).inputs, wv n C (pr p l) x = true →
      wv n C (unit p) x = true ∨ wv n C (unit l) x = true := by
    intro x hx hxt
    have hxa := hrb x hx
    rcases Nat.lt_or_ge x n with hxn | hxn
    · rw [wv_input n C _ x hxn] at hxt
      rw [wv_input n C _ x hxn, wv_input n C _ x hxn]
      simp only [pr, unit, decide_eq_true_eq] at hxt ⊢
      exact hxt
    · obtain ⟨j, rfl⟩ : ∃ j, x = n + j := ⟨x - n, by omega⟩
      have hP : ¬ P j := hmin j (by omega)
      have hxc : IOS n C j c := by
        refine ios_trans n C j a c (Or.inr ?_) hac
        rw [inCone_iff]; exact ⟨halen, j, by omega, hx, Or.inl rfl⟩
      by_contra hne
      push_neg at hne
      exact hP ⟨hxc, hxt, by simpa using hne.1, by simpa using hne.2⟩
  rw [hx] at split
  have sx1 := split x1 (by simp)
  have sx2 := split x2 (by simp)
  have ev : ∀ y, wv n C y (n + a) = (gateAt C a).op.eval ([x1, x2].map (wv n C y)) := by
    intro y; rw [wv_rec n C y (aob hC) a halen, hx]
  have rvp : ∀ (h : ℕ) (q : Fin n), wv n C (unit q) h = true → RV n C h q := by
    intro h q hq
    obtain ⟨v, hv, hv2⟩ := wv_true_var n C hC _ h hq
    simp [unit] at hv2
    rw [← hv2]; exact hv
  rcases hop with hop | hop
  swap
  · exfalso
    rw [ev, hop, eval_or_pair] at ha1 ha2 ha3
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at ha1 ha2 ha3
    rcases ha1 with h | h
    · rcases sx1 h with h' | h'
      · simp [h'] at ha2
      · simp [h'] at ha3
    · rcases sx2 h with h' | h'
      · simp [h'] at ha2
      · simp [h'] at ha3
  have hpass := pass n C hC c hR a c hac (Or.inl rfl)
  obtain ⟨e, he⟩ := hpass
  rw [ev, hop, eval_and_pair] at ha1 ha2 ha3
  simp only [Bool.and_eq_true] at ha1
  have tr : (∀ v, RV n C (n + a) v → ∀ v' : Fin n, ¬ RV n C (n + a) v' → v' ≠ v) := by
    intro v hv v' hv' h; rw [h] at hv'; exact hv' hv
  have finish : ∀ hA hB, ((gateAt C a).inputs = [hA, hB] ∨ (gateAt C a).inputs = [hB, hA]) →
      wv n C (unit p) hA = true → wv n C (unit l) hB = true → False ∨ (∃ a, IOS n C a c ∧
      a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      (∀ y : Fin n → Bool, (∀ v, ¬ RV n C (n + a) v → y v = false) →
        wv n C y (n + c) = wv n C y (n + a)) ∧
      ∃ hA hB, ((gateAt C a).inputs = [hA, hB] ∨ (gateAt C a).inputs = [hB, hA]) ∧
        RV n C hA p ∧ RV n C hB l ∧ wv n C (unit p) hA = true ∧ wv n C (unit l) hB = true) := by
    intro hA hB hin hpA hlB
    right
    have hRA := rvp hA p hpA
    have hRB := rvp hB l hlB
    have hRap : RV n C (n + a) p := by
      rcases hin with h | h
      · exact (RV_gate n C hC a hA hB halen h p).2 (Or.inl hRA)
      · exact (RV_gate n C hC a hB hA halen h p).2 (Or.inr hRA)
    have hRal : RV n C (n + a) l := by
      rcases hin with h | h
      · exact (RV_gate n C hC a hA hB halen h l).2 (Or.inr hRB)
      · exact (RV_gate n C hC a hB hA halen h l).2 (Or.inl hRB)
    have hsupp : ∀ v, ¬ RV n C (n + a) v → pr p l v = false := by
      intro v hv
      have e1 := tr p hRap v hv
      have e2 := tr l hRal v hv
      simp [pr, e1, e2]
    have he1 := he (pr p l) hsupp
    have hat : wv n C (pr p l) (n + a) = true := by
      rw [ev, hop, eval_and_pair]; simp [ha1.1, ha1.2]
    have hetrue : e = true := by
      rw [h1, hat] at he1; simpa using he1.symm
    refine ⟨a, hac, halen, hop, fun y hy => ?_, hA, hB, hin, hRA, hRB, hpA, hlB⟩
    rw [he y hy, hetrue]; simp
  rcases sx1 ha1.1 with s1 | s1 <;> rcases sx2 ha1.2 with s2 | s2
  · simp [s1, s2] at ha2
  · rcases finish x1 x2 (Or.inl hx) s1 s2 with h | h
    · exact h.elim
    · exact h
  · rcases finish x2 x1 (Or.inr hx) s2 s1 with h | h
    · exact h.elim
    · exact h
  · simp [s1, s2] at ha3

lemma set_foldl (gs : List Gate) (g0 : Gate)
    (hg0 : ∀ w : List Bool, g0.op.eval (g0.inputs.map fun i => w.getD i false) = false) :
    ∀ (c : ℕ) (w : List Bool), c < gs.length →
      (gs.foldl stepW w).getD (w.length + c) false = false →
      (gs.set c g0).foldl stepW w = gs.foldl stepW w := by
  induction gs with
  | nil => intro c w hc; simp at hc
  | cons g gs ih =>
    intro c w hc h
    cases c with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      rw [List.foldl_cons, foldl_getD_lt gs (stepW w g) (w.length + 0) (by simp [stepW])] at h
      have e : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
        simpa [stepW, List.getD_eq_getElem?_getD] using h
      simp only [stepW, e, hg0]
    | succ c =>
      simp only [List.set_cons_succ, List.foldl_cons]
      apply ih c (stepW w g) (by simp at hc; omega)
      rw [List.foldl_cons] at h
      have : (stepW w g).length = w.length + 1 := by simp [stepW]
      rw [this, show w.length + 1 + c = w.length + (c + 1) by omega]
      exact h

lemma lost_true (n : ℕ) (C : Circuit) (c : ℕ) (hc : c < C.gates.length) (x : Fin n → Bool)
    (h1 : PEqualNP.MetaComplexity.circuitFun n C x = true)
    (h2 : PEqualNP.MetaComplexity.circuitFun n
      (Circuit.mk (C.gates.set c (Gate.mk GateOp.or [])) C.output) x = false) :
    wv n C x (n + c) = true := by
  by_contra hne
  have hf : wv n C x (n + c) = false := by simpa using hne
  have key : (C.gates.set c (Gate.mk GateOp.or [])).foldl stepW (List.ofFn x) =
      C.gates.foldl stepW (List.ofFn x) := by
    apply set_foldl C.gates _ (fun w => by simp [GateOp.eval]) c (List.ofFn x) hc
    rw [List.length_ofFn]; exact hf
  change ((C.gates.set c (Gate.mk GateOp.or [])).foldl stepW (List.ofFn x)).getD C.output false
    = false at h2
  change (C.gates.foldl stepW (List.ofFn x)).getD C.output false = true at h1
  rw [key, h1] at h2
  exact absurd h2 (by simp)

lemma notBF_cone (n : ℕ) (C : Circuit) (BF : ℕ → Prop)
    (H5 : ∀ j < C.gates.length, ((gateAt C j).op = GateOp.and ∨ ¬ BF (n + j)) →
      ∀ w ∈ (gateAt C j).inputs, ¬ BF w) :
    ∀ c, ¬ BF (n + c) → ∀ k, InCone n C k c → ¬ BF (n + k) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc k hk
    rw [inCone_iff] at hk
    obtain ⟨hclen, j, hjc, hjin, hkj⟩ := hk
    have hj : ¬ BF (n + j) := H5 c hclen (Or.inr hc) (n + j) hjin
    rcases hkj with rfl | hkj
    · exact hj
    · exact ih j hjc hj k hkj

lemma inputs_facts (n : ℕ) (C : Circuit) (hC : AO2 n C) (c : ℕ) (hR : RO n C c) (a : ℕ)
    (hac : IOS n C a c) (halen : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hA hB : ℕ) (hin : (gateAt C a).inputs = [hA, hB] ∨ (gateAt C a).inputs = [hB, hA]) :
    (∀ v, RV n C hA v → RV n C hB v → False) ∧
    (∀ v, RV n C (n + a) v ↔ RV n C hA v ∨ RV n C hB v) ∧
    (∀ y, wv n C y (n + a) = (wv n C y hA && wv n C y hB)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v h1 h2
    rcases hin with h | h
    · exact disj n C hC c hR a hA hB hac halen h v h1 h2
    · exact disj n C hC c hR a hB hA hac halen h v h2 h1
  · intro v
    rcases hin with h | h
    · exact RV_gate n C hC a hA hB halen h v
    · exact (RV_gate n C hC a hB hA halen h v).trans or_comm
  · intro y
    rcases hin with h | h
    · rw [wv_rec n C y (aob hC) a halen, h, hand, eval_and_pair]
    · rw [wv_rec n C y (aob hC) a halen, h, hand, eval_and_pair, Bool.and_comm]

def LostData (n : ℕ) (C : Circuit) (c : ℕ) (FT : (Fin n → Bool) → Prop) (v : Fin n) : Prop :=
  ∃ y1, wv n C (pr v y1) (n + c) = true ∧ wv n C (unit y1) (n + c) = false ∧
    ∃ w1 : ℕ, (∀ z, wv n C z (n + c) = true → wv n C z w1 = true → FT z) ∧
      (wv n C (unit v) w1 = true ∨ wv n C (unit y1) w1 = true)

lemma side (n : ℕ) (C : Circuit) (hC : AO2 n C) (c : ℕ) (hc : c < C.gates.length)
    (hR : RO n C c) (FT : (Fin n → Bool) → Prop)
    (hU : ∀ v : Fin n, RV n C (n + c) v → wv n C (unit v) (n + c) = true ∨ LostData n C c FT v)
    (a : ℕ) (hac : IOS n C a c) (halen : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and)
    (htr : ∀ y : Fin n → Bool, (∀ v, ¬ RV n C (n + a) v → y v = false) →
        wv n C y (n + c) = wv n C y (n + a))
    (hA hB : ℕ) (hin : (gateAt C a).inputs = [hA, hB] ∨ (gateAt C a).inputs = [hB, hA])
    (p l : Fin n) (hRA : RV n C hA p) (hRB : RV n C hB l)
    (hpl : wv n C (pr p l) (n + c) = true)
    (z : Fin n → Bool) (hFz : ¬ FT z) (hcz : wv n C z (n + c) = true)
    (x0 : Fin n) (hx0 : RV n C hA x0) (hzx0 : z x0 = true) :
    ∃ y1 : Fin n, ∃ w1 : ℕ, (∀ z, wv n C z (n + c) = true → wv n C z w1 = true → FT z) ∧
      wv n C (unit y1) w1 = true ∧ RV n C hB y1 ∧ wv n C (unit y1) hB = true := by
  obtain ⟨hdis, hRVa, hev⟩ := inputs_facts n C hC c hR a hac halen hand hA hB hin
  have hx0a : RV n C (n + a) x0 := (hRVa x0).2 (Or.inl hx0)
  have suppunit : ∀ q : Fin n, RV n C (n + a) q → ∀ v, ¬ RV n C (n + a) v → unit q v = false := by
    intro q hq v hv
    have : v ≠ q := fun e => hv (by rw [e]; exact hq)
    simp [unit, this]
  have suppr : ∀ q q' : Fin n, RV n C (n + a) q → RV n C (n + a) q' →
      ∀ v, ¬ RV n C (n + a) v → pr q q' v = false := by
    intro q q' hq hq' v hv
    have h1 : v ≠ q := fun e => hv (by rw [e]; exact hq)
    have h2 : v ≠ q' := fun e => hv (by rw [e]; exact hq')
    simp [pr, h1, h2]
  have hcx0 : wv n C (unit x0) (n + c) = false := by
    rw [htr _ (suppunit x0 hx0a), hev]
    have : wv n C (unit x0) hB = false := by
      apply wv_out n C hC
      intro v hv
      have : v ≠ x0 := fun e => hdis x0 hx0 (by rw [← e]; exact hv)
      simp [unit, this]
    rw [this]; simp
  rcases hU x0 (RV_mono n C a c hac x0 hx0a) with h | ⟨y1, hcy, hy1, w1, hw1, hwor⟩
  · rw [hcx0] at h; exact absurd h (by simp)
  have hwy1 : wv n C (unit y1) w1 = true := by
    rcases hwor with h | h
    · exfalso
      apply hFz
      apply hw1 z hcz
      apply wv_mono n C hC (unit x0) z _ w1 h
      intro i hi; simp [unit] at hi; rw [hi]; exact hzx0
    · exact h
  refine ⟨y1, w1, hw1, hwy1, ?_⟩
  by_cases hy : RV n C (n + a) y1
  · have hat : wv n C (pr x0 y1) (n + a) = true := by
      rw [← htr _ (suppr x0 y1 hx0a hy)]; exact hcy
    rw [hev] at hat
    simp only [Bool.and_eq_true] at hat
    have hyB : RV n C hB y1 := by
      rcases (hRVa y1).1 hy with h | h
      · exfalso
        have : wv n C (pr x0 y1) hB = false := by
          apply wv_out n C hC
          intro v hv
          have e1 : v ≠ x0 := fun e => hdis x0 hx0 (by rw [← e]; exact hv)
          have e2 : v ≠ y1 := fun e => hdis y1 h (by rw [← e]; exact hv)
          simp [pr, e1, e2]
        rw [this] at hat; exact absurd hat.2 (by simp)
      · exact h
    refine ⟨hyB, ?_⟩
    rw [← hat.2]
    apply wv_local n C hC
    intro v hv
    have e1 : v ≠ x0 := fun e => hdis x0 hx0 (by rw [← e]; exact hv)
    simp [unit, pr, e1]
  · exfalso
    obtain ⟨a', ha'c, ha'len, hand', htr', hA', hB', hin', hRA', hRB', _, _⟩ :=
      join n C hC c hc hR x0 y1 hcy hcx0 hy1
    obtain ⟨_, hRVa', _⟩ := inputs_facts n C hC c hR a' ha'c ha'len hand' hA' hB' hin'
    have hx0a' : RV n C (n + a') x0 := (hRVa' x0).2 (Or.inl hRA')
    have hy1a' : RV n C (n + a') y1 := (hRVa' y1).2 (Or.inr hRB')
    rcases comparable n C c hR a a' x0 hac ha'c hx0a hx0a' with h | h
    · rcases h with rfl | h
      · exact hy hy1a'
      have hpa : RV n C (n + a) p := (hRVa p).2 (Or.inl hRA)
      have hla : RV n C (n + a) l := (hRVa l).2 (Or.inr hRB)
      have hpa' := RV_mono n C a a' (Or.inr h) p hpa
      have hla' := RV_mono n C a a' (Or.inr h) l hla
      rw [inCone_iff] at h
      obtain ⟨_, j, _, hjin, haj⟩ := h
      obtain ⟨_, ⟨u1, u2, hu⟩, _⟩ := hC a' ha'len
      have hpj := RV_mono n C a j haj p hpa
      have hlj := RV_mono n C a j haj l hla
      have j1 : ∀ o, ((gateAt C a').inputs = [n + j, o] ∨ (gateAt C a').inputs = [o, n + j]) →
          wv n C (pr p l) o = false := by
        intro o ho
        apply wv_out n C hC
        intro v hv
        have e1 : v ≠ p := by
          intro e; rw [e] at hv
          rcases ho with ho | ho
          · exact disj n C hC c hR a' (n + j) o ha'c ha'len ho p hpj hv
          · exact disj n C hC c hR a' o (n + j) ha'c ha'len ho p hv hpj
        have e2 : v ≠ l := by
          intro e; rw [e] at hv
          rcases ho with ho | ho
          · exact disj n C hC c hR a' (n + j) o ha'c ha'len ho l hlj hv
          · exact disj n C hC c hR a' o (n + j) ha'c ha'len ho l hv hlj
        simp [pr, e1, e2]
      have hval : wv n C (pr p l) (n + a') = false := by
        rw [wv_rec n C _ (aob hC) a' ha'len, hu, hand', eval_and_pair]
        rw [hu] at hjin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hjin
        rcases hjin with e | e
        · rw [j1 u2 (Or.inl (by rw [hu, e]))]; simp
        · rw [j1 u1 (Or.inr (by rw [hu, e]))]; simp
      have hsup : ∀ v, ¬ RV n C (n + a') v → pr p l v = false := by
        intro v hv
        have e1 : v ≠ p := fun e => hv (by rw [e]; exact hpa')
        have e2 : v ≠ l := fun e => hv (by rw [e]; exact hla')
        simp [pr, e1, e2]
      rw [htr' _ hsup, hval] at hpl
      exact absurd hpl (by simp)
    · exact hy (RV_mono n C a' a h y1 hy1a')

theorem tight_false (n : ℕ) (C : Circuit) (hC : AO2 n C) (c : ℕ) (hc : c < C.gates.length)
    (hR : RO n C c) (FT : (Fin n → Bool) → Prop) (s : Fin n → Bool)
    (hNB : ∀ k, IOS n C k c → ∃ z, wv n C z (n + k) = true ∧ ¬ FT z)
    (hTri : ∀ a b, FT (pr a b) → s a ≠ s b)
    (hU : ∀ v : Fin n, RV n C (n + c) v → wv n C (unit v) (n + c) = true ∨ LostData n C c FT v)
    (hL : ∃ p l, wv n C (pr p l) (n + c) = true ∧ wv n C (unit p) (n + c) = false ∧
      wv n C (unit l) (n + c) = false)
    (hlin : ∃ u, wv n C (unit u) (n + c) = true) : False := by
  classical
  obtain ⟨p, l, hpl, hp, hl⟩ := hL
  obtain ⟨a, hac, halen, hand, htr, hA, hB, hin, hRA, hRB, _, _⟩ :=
    join n C hC c hc hR p l hpl hp hl
  obtain ⟨_, hRVa, hev⟩ := inputs_facts n C hC c hR a hac halen hand hA hB hin
  obtain ⟨z, hz, hFz⟩ := hNB a hac
  have hz2 := hz
  rw [hev] at hz2
  simp only [Bool.and_eq_true] at hz2
  have hcz : wv n C z (n + c) = true := by
    let z' : Fin n → Bool := fun v => z v && decide (RV n C (n + a) v)
    have h1 : wv n C z' (n + c) = wv n C z' (n + a) := htr z' (by intro v hv; simp [z', hv])
    have h2 : wv n C z' (n + a) = wv n C z (n + a) := by
      apply wv_local n C hC; intro v hv; simp [z', hv]
    apply wv_mono n C hC z' z (by intro i hi; simp [z'] at hi; exact hi.1)
    rw [h1, h2]; exact hz
  obtain ⟨x0, hx0, hzx0⟩ := wv_true_var n C hC z hA hz2.1
  obtain ⟨y0, hy0, hzy0⟩ := wv_true_var n C hC z hB hz2.2
  obtain ⟨y1, w1, hw1, hwy1, hRy1, hBy1⟩ := side n C hC c hc hR FT hU a hac halen hand htr
    hA hB hin p l hRA hRB hpl z hFz hcz x0 hx0 hzx0
  obtain ⟨x1, w2, hw2, hwx1, hRx1, hAx1⟩ := side n C hC c hc hR FT hU a hac halen hand htr
    hB hA hin.symm l p hRB hRA (by rw [pr_comm]; exact hpl) z hFz hcz y0 hy0 hzy0
  obtain ⟨u, hu⟩ := hlin
  have hx1a : RV n C (n + a) x1 := (hRVa x1).2 (Or.inl hRx1)
  have hy1a : RV n C (n + a) y1 := (hRVa y1).2 (Or.inr hRy1)
  have hc11 : wv n C (pr x1 y1) (n + c) = true := by
    have hsup : ∀ v, ¬ RV n C (n + a) v → pr x1 y1 v = false := by
      intro v hv
      have e1 : v ≠ x1 := fun e => hv (by rw [e]; exact hx1a)
      have e2 : v ≠ y1 := fun e => hv (by rw [e]; exact hy1a)
      simp [pr, e1, e2]
    rw [htr _ hsup, hev]
    simp only [Bool.and_eq_true]
    exact ⟨wv_mono n C hC _ _ (unit_le_pr1 x1 y1) hA hAx1,
      wv_mono n C hC _ _ (unit_le_pr2 x1 y1) hB hBy1⟩
  have f1 : FT (pr x1 y1) := hw1 _ hc11 (wv_mono n C hC _ _ (unit_le_pr2 x1 y1) w1 hwy1)
  have f2 : FT (pr u y1) := hw1 _ (wv_mono n C hC _ _ (unit_le_pr1 u y1) _ hu)
    (wv_mono n C hC _ _ (unit_le_pr2 u y1) w1 hwy1)
  have f3 : FT (pr u x1) := hw2 _ (wv_mono n C hC _ _ (unit_le_pr1 u x1) _ hu)
    (wv_mono n C hC _ _ (unit_le_pr2 u x1) w2 hwx1)
  exact bool3 (s u) (s x1) (s y1) (hTri _ _ f3) (hTri _ _ f2) (hTri _ _ f1)

lemma final_count (n : ℕ) (C : Circuit) (hC : AO2 n C) (c : ℕ) (hc : c < C.gates.length)
    (U : Finset (Fin n)) (hUread : ∀ v ∈ U, RV n C (n + c) v)
    (htight : RO n C c → (∀ v : Fin n, RV n C (n + c) v → v ∈ U) → False) :
    U.card ≤ ((Finset.range C.gates.length).filter
      fun k => PEqualNP.SplitCount.InConeOrSelf n C k c).card := by
  classical
  set S := (Finset.range C.gates.length).filter
    (fun k => PEqualNP.SplitCount.InConeOrSelf n C k c) with hSdef
  have hS : ∀ k, k ∈ S ↔ IOS n C k c := by
    intro k
    simp only [hSdef, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨lt_of_le_of_lt (ios_le n C k c h) hc, h⟩
  have hcS : c ∈ S := (hS c).2 (Or.inl rfl)
  have rpos : ∀ j x, j ∈ S → x ∈ (gateAt C j).inputs → 1 ≤ readsIn C S x := by
    intro j x hj hx
    unfold readsIn
    exact le_trans (List.count_pos_iff.2 hx)
      (Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count x)
        (fun _ _ => Nat.zero_le _) hj)
  have rread : ∀ x, 1 ≤ readsIn C S x → ∃ j ∈ S, x ∈ (gateAt C j).inputs := by
    intro x hx
    unfold readsIn at hx
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by omega : (∑ j ∈ S, (gateAt C j).inputs.count x) ≠ 0)
    exact ⟨j, hj, List.count_pos_iff.1 (Nat.pos_of_ne_zero hne)⟩
  have bound : ∀ B : Finset ℕ, ∑ x ∈ B, readsIn C S x ≤ 2 * S.card := by
    intro B
    unfold readsIn
    rw [Finset.sum_comm, Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjlen : j < C.gates.length := lt_of_le_of_lt (ios_le n C j c ((hS j).1 hj)) hc
    obtain ⟨_, ⟨a, b, hab⟩, _⟩ := hC j hjlen
    rw [hab]
    have e : ∀ x, List.count x [a, b] = (if a = x then 1 else 0) + (if b = x then 1 else 0) := by
      intro x
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq]
    split_ifs <;> omega
  set A : Finset ℕ := U.image Fin.val ∪ (S.erase c).image (fun g => n + g) with hA
  have hAcard : A.card = U.card + (S.card - 1) := by
    rw [hA, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (add_right_injective n), Finset.card_erase_of_mem hcS]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨v, _, rfl⟩ := hx1
    obtain ⟨g, _, hg⟩ := hx2
    have := v.isLt; omega
  have hbase : ∀ x ∈ A, 1 ≤ readsIn C S x := by
    intro x hx
    rw [hA, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
    rcases hx with ⟨v, hv, rfl⟩ | ⟨g, hg, rfl⟩
    · have hr := hUread v hv
      rcases hr with h | ⟨_, k, _, hk, hin⟩
      · have := v.isLt; omega
      · rw [Nat.add_sub_cancel_left] at hk
        exact rpos k _ ((hS k).2 hk) hin
    · rw [Finset.mem_erase] at hg
      have hgc : InCone n C g c := by
        rcases (hS g).1 hg.2 with h | h
        · exact absurd h hg.1
        · exact h
      obtain ⟨q, _, _, hqin, hq⟩ := inCone_reader n C g c hgc
      exact rpos q _ ((hS q).2 hq) hqin
  have sumge : ∀ B : Finset ℕ, (∀ x ∈ B, 1 ≤ readsIn C S x) →
      B.card ≤ ∑ x ∈ B, readsIn C S x := by
    intro B hB
    rw [Finset.card_eq_sum_ones]; exact Finset.sum_le_sum hB
  have hScard : 1 ≤ S.card := Finset.card_pos.2 ⟨c, hcS⟩
  have extra : ∀ x0, ((x0 ∈ A ∧ 2 ≤ readsIn C S x0) ∨ (x0 ∉ A ∧ 1 ≤ readsIn C S x0)) →
      U.card ≤ S.card := by
    intro x0 h
    rcases h with ⟨hxA, h2⟩ | ⟨hxA, h1⟩
    · have e := Finset.add_sum_erase A (readsIn C S) hxA
      have g1 := sumge (A.erase x0) (fun x hx => hbase x (Finset.mem_of_mem_erase hx))
      rw [Finset.card_erase_of_mem hxA] at g1
      have g2 := bound A
      have hApos : 1 ≤ A.card := Finset.card_pos.2 ⟨x0, hxA⟩
      omega
    · have e := Finset.sum_insert (f := readsIn C S) hxA
      have g1 := sumge A hbase
      have g2 := bound (insert x0 A)
      omega
  by_cases hT : (∀ x, readsIn C S x ≤ 1) ∧ (∀ v : Fin n, RV n C (n + c) v → v ∈ U)
  · exfalso
    apply htight _ hT.2
    refine ⟨?_, ?_⟩
    · intro x j1 j2 h1 h2 hx1 hx2
      by_contra hne
      have := hT.1 x
      unfold readsIn at this
      have hsub : ({j1, j2} : Finset ℕ) ⊆ S := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact (hS _).2 h1
        · exact (hS _).2 h2
      have hle := Finset.sum_le_sum_of_subset (f := fun j => (gateAt C j).inputs.count x) hsub
      rw [Finset.sum_pair hne] at hle
      have c1 := List.count_pos_iff.2 hx1
      have c2 := List.count_pos_iff.2 hx2
      omega
    · intro j a hj hab
      have := hT.1 a
      unfold readsIn at this
      have hle := Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count a)
        (fun _ _ => Nat.zero_le _) ((hS j).2 hj)
      simp only [hab, List.count_cons, List.count_nil, beq_self_eq_true, ite_true] at hle
      omega
  · rw [not_and_or] at hT
    rcases hT with hT | hT
    · push_neg at hT
      obtain ⟨x, hx⟩ := hT
      by_cases hxA : x ∈ A
      · exact extra x (Or.inl ⟨hxA, by omega⟩)
      · exact extra x (Or.inr ⟨hxA, by omega⟩)
    · push_neg at hT
      obtain ⟨v, hv, hvU⟩ := hT
      have hvA : (v : ℕ) ∉ A := by
        rw [hA, Finset.mem_union, Finset.mem_image, Finset.mem_image]
        rintro (⟨v', hv', e⟩ | ⟨g, _, e⟩)
        · exact hvU (by have hh : v' = v := Fin.ext e; rw [← hh]; exact hv')
        · have := v.isLt; omega
      rcases hv with h | ⟨_, k, _, hk, hin⟩
      · have := v.isLt; omega
      · rw [Nat.add_sub_cancel_left] at hk
        exact extra v (Or.inr ⟨hvA, rpos k _ ((hS k).2 hk) hin⟩)

lemma partner_ft (n : ℕ) (C : Circuit) (hC : AO2 n C) (c j w : ℕ) (FT : (Fin n → Bool) → Prop)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hbf : ∀ z, wv n C z (n + j) = true → FT z)
    (hw : (gateAt C j).inputs = [n + c, w] ∨ (gateAt C j).inputs = [w, n + c]) :
    ∀ z, wv n C z (n + c) = true → wv n C z w = true → FT z := by
  intro z h1 h2
  apply hbf
  rcases hw with hw | hw
  · rw [wv_rec n C z (aob hC) j hj, hw, hand, eval_and_pair, h1, h2]; rfl
  · rw [wv_rec n C z (aob hC) j hj, hw, hand, eval_and_pair, h1, h2]; rfl

def FTd (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) (z : Fin (Np + Nl) → Bool) : Prop :=
  ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true

def sd (Np Nl : ℕ) (v : Fin (Np + Nl)) : Bool := decide ((v : ℕ) < Np)

abbrev LostP (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) (C : Circuit) (c : ℕ) (p : Fin Np)
    (l : Fin Nl) : Prop :=
  I p l ∧ wv (Np + Nl) C (unit (Fin.castAdd Nl p)) (Np + Nl + c) = false ∧
    wv (Np + Nl) C (unit (Fin.natAdd Np l)) (Np + Nl + c) = false ∧
    PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) = true ∧
    PEqualNP.MetaComplexity.circuitFun (Np + Nl)
      (Circuit.mk (C.gates.set c (Gate.mk GateOp.or [])) C.output)
      (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) = false

theorem main_core (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 (Np + Nl) C)
    (H5 : (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)))
    (hc : c < C.gates.length)
    (hcNB : ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true))
    (hlin : (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true))
    (hlost : (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)))
    (hpart : (∀ p47 : Fin Np, ∀ l48 : Fin Nl, (I p47 l48 ∧ (C.wires (List.ofFn (fun i51 : Fin (Np + Nl) => decide (i51 = Fin.castAdd Nl p47)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i52 : Fin (Np + Nl) => decide (i52 = Fin.natAdd Np l48)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i53 : Fin (Np + Nl) => decide (i53 = Fin.castAdd Nl p47 ∨ i53 = Fin.natAdd Np l48)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p47 ∨ i54 = Fin.natAdd Np l48)) = false) → ∃ j49 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ z55 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z55)).getD ((Np + Nl) + j49) false = true → ∃ p56 : Fin Np, ∃ l57 : Fin Nl, I p56 l57 ∧ z55 (Fin.castAdd Nl p56) = true ∧ z55 (Fin.natAdd Np l57) = true) ∧ ∃ w50 : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [(Np + Nl) + c, w50] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [w50, (Np + Nl) + c]) ∧ ((C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p47)))).getD (w50) false = true ∨ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l48)))).getD (w50) false = true)))
    : (Finset.univ.filter fun v60 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i66 : Fin (Np + Nl) => decide (i66 = v60)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p61 : Fin Np => ∃ l62 : Fin Nl, (I p61 l62 ∧ (C.wires (List.ofFn (fun i67 : Fin (Np + Nl) => decide (i67 = Fin.castAdd Nl p61)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i68 : Fin (Np + Nl) => decide (i68 = Fin.natAdd Np l62)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i69 : Fin (Np + Nl) => decide (i69 = Fin.castAdd Nl p61 ∨ i69 = Fin.natAdd Np l62)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i70 : Fin (Np + Nl) => decide (i70 = Fin.castAdd Nl p61 ∨ i70 = Fin.natAdd Np l62)) = false)).card + (Finset.univ.filter fun l64 : Fin Nl => ∃ p63 : Fin Np, (I p63 l64 ∧ (C.wires (List.ofFn (fun i71 : Fin (Np + Nl) => decide (i71 = Fin.castAdd Nl p63)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i72 : Fin (Np + Nl) => decide (i72 = Fin.natAdd Np l64)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i73 : Fin (Np + Nl) => decide (i73 = Fin.castAdd Nl p63 ∨ i73 = Fin.natAdd Np l64)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i74 : Fin (Np + Nl) => decide (i74 = Fin.castAdd Nl p63 ∨ i74 = Fin.natAdd Np l64)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k65 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k65 c).card := by
  show (Finset.univ.filter fun v : Fin (Np + Nl) => wv (Np + Nl) C (unit v) (Np + Nl + c) = true).card +
    (Finset.univ.filter fun p : Fin Np => ∃ l : Fin Nl, LostP Np Nl I C c p l).card +
    (Finset.univ.filter fun l : Fin Nl => ∃ p : Fin Np, LostP Np Nl I C c p l).card ≤
    ((Finset.range C.gates.length).filter
      fun k => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k c).card
  have hC := ao_of (Np + Nl) C hAO
  set lin := Finset.univ.filter fun v : Fin (Np + Nl) =>
    wv (Np + Nl) C (unit v) (Np + Nl + c) = true with hlin_def
  set LP := Finset.univ.filter fun p : Fin Np => ∃ l : Fin Nl, LostP Np Nl I C c p l with hLP
  set LL := Finset.univ.filter fun l : Fin Nl => ∃ p : Fin Np, LostP Np Nl I C c p l with hLL
  have cinj : Function.Injective (Fin.castAdd Nl : Fin Np → Fin (Np + Nl)) := by
    intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h)
  have ninj : Function.Injective (Fin.natAdd Np : Fin Nl → Fin (Np + Nl)) := by
    intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h)
  have hlt : ∀ (p : Fin Np) (l : Fin Nl), (Fin.castAdd Nl p) ≠ (Fin.natAdd Np l) := by
    intro p l h; have := congrArg Fin.val h; simp at this; omega
  set VL := LP.image (Fin.castAdd Nl) ∪ LL.image (Fin.natAdd Np) with hVL
  set U := lin ∪ VL with hU
  have lostc : ∀ p l, LostP Np Nl I C c p l →
      wv (Np + Nl) C (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) (Np + Nl + c) = true :=
    fun p l h => lost_true (Np + Nl) C c hc _ h.2.2.2.1 h.2.2.2.2
  have hcard : U.card = lin.card + LP.card + LL.card := by
    rw [hU, Finset.card_union_of_disjoint, hVL, Finset.card_union_of_disjoint,
      Finset.card_image_of_injective _ cinj, Finset.card_image_of_injective _ ninj]
    · omega
    · rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨p, _, rfl⟩ := h1
      obtain ⟨l, _, e⟩ := h2
      exact hlt p l e.symm
    · rw [Finset.disjoint_left]
      intro x h1 h2
      rw [hlin_def, Finset.mem_filter] at h1
      rw [hVL, Finset.mem_union, Finset.mem_image, Finset.mem_image] at h2
      rcases h2 with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · rw [hLP, Finset.mem_filter] at hp
        obtain ⟨l, hl⟩ := hp.2
        rw [hl.2.1] at h1; exact absurd h1.2 (by simp)
      · rw [hLL, Finset.mem_filter] at hl
        obtain ⟨p, hp⟩ := hl.2
        rw [hp.2.2.1] at h1; exact absurd h1.2 (by simp)
  rw [← hcard]
  apply final_count (Np + Nl) C hC c hc U
  · intro v hv
    by_contra hnr
    rw [hU, Finset.mem_union] at hv
    rcases hv with hv | hv
    · rw [hlin_def, Finset.mem_filter] at hv
      have : wv (Np + Nl) C (unit v) (Np + Nl + c) = false := by
        apply wv_out _ C hC
        intro u hu
        have : u ≠ v := fun e => hnr (by rw [← e]; exact hu)
        simp [unit, this]
      rw [this] at hv; exact absurd hv.2 (by simp)
    · rw [hVL, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hv
      rcases hv with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · rw [hLP, Finset.mem_filter] at hp
        obtain ⟨l, hl⟩ := hp.2
        have h1 := lostc p l hl
        have : wv (Np + Nl) C (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) (Np + Nl + c) =
            wv (Np + Nl) C (unit (Fin.natAdd Np l)) (Np + Nl + c) := by
          apply wv_local _ C hC
          intro u hu
          have : u ≠ Fin.castAdd Nl p := fun e => hnr (by rw [← e]; exact hu)
          simp [unit, pr, this]
        rw [this, hl.2.2.1] at h1; exact absurd h1 (by simp)
      · rw [hLL, Finset.mem_filter] at hl
        obtain ⟨p, hp⟩ := hl.2
        have h1 := lostc p l hp
        have : wv (Np + Nl) C (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) (Np + Nl + c) =
            wv (Np + Nl) C (unit (Fin.castAdd Nl p)) (Np + Nl + c) := by
          apply wv_local _ C hC
          intro u hu
          have : u ≠ Fin.natAdd Np l := fun e => hnr (by rw [← e]; exact hu)
          simp [unit, pr, this]
        rw [this, hp.2.1] at h1; exact absurd h1 (by simp)
  · intro hR hread
    have hNB : ∀ k, IOS (Np + Nl) C k c → ∃ z, wv (Np + Nl) C z (Np + Nl + k) = true ∧
        ¬ FTd Np Nl I z := by
      intro k hk
      have hnb : ¬ (∀ z, wv (Np + Nl) C z (Np + Nl + k) = true → FTd Np Nl I z) := by
        rcases hk with rfl | hk
        · exact hcNB
        · exact notBF_cone (Np + Nl) C
            (fun w => ∀ z : Fin (Np + Nl) → Bool, wv (Np + Nl) C z w = true → FTd Np Nl I z)
            H5 c hcNB k hk
      push_neg at hnb
      exact hnb
    have hTri : ∀ a b : Fin (Np + Nl), FTd Np Nl I (pr a b) → sd Np Nl a ≠ sd Np Nl b := by
      intro a b ⟨p, l, _, h1, h2⟩
      simp only [pr, decide_eq_true_eq] at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
      · exact absurd h2.symm (hlt p l)
      · subst h2; simp [sd]
      · subst h2; simp [sd]
      · exact absurd h2.symm (hlt p l)
    have hU' : ∀ v, RV (Np + Nl) C (Np + Nl + c) v →
        wv (Np + Nl) C (unit v) (Np + Nl + c) = true ∨ LostData (Np + Nl) C c (FTd Np Nl I) v := by
      intro v hv
      have hvU := hread v hv
      rw [hU, Finset.mem_union] at hvU
      rcases hvU with h | h
      · left; rw [hlin_def, Finset.mem_filter] at h; exact h.2
      · right
        rw [hVL, Finset.mem_union, Finset.mem_image, Finset.mem_image] at h
        rcases h with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
        · rw [hLP, Finset.mem_filter] at hp
          obtain ⟨l, hl⟩ := hp.2
          obtain ⟨j, hj, hjand, hjbf, w, hw, hwor⟩ := hpart p l hl
          exact ⟨Fin.natAdd Np l, lostc p l hl, hl.2.2.1, w,
            partner_ft (Np + Nl) C hC c j w (FTd Np Nl I) hj hjand hjbf hw, hwor⟩
        · rw [hLL, Finset.mem_filter] at hl
          obtain ⟨p, hp⟩ := hl.2
          obtain ⟨j, hj, hjand, hjbf, w, hw, hwor⟩ := hpart p l hp
          exact ⟨Fin.castAdd Nl p, by rw [pr_comm]; exact lostc p l hp, hp.2.1, w,
            partner_ft (Np + Nl) C hC c j w (FTd Np Nl I) hj hjand hjbf hw, hwor.symm⟩
    obtain ⟨p, l, hl⟩ := hlost
    obtain ⟨u, hu⟩ := hlin
    exact tight_false (Np + Nl) C hC c hc hR (FTd Np Nl I) (sd Np Nl) hNB hTri hU'
      ⟨_, _, lostc p l hl, hl.2.1, hl.2.2.1⟩ ⟨u, hu⟩

end PEqualNP.Outside.L_meta_3026

open PEqualNP.Outside.L_meta_3026

theorem PEqualNP.Outside.L_meta_3026 : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ j1 < C.gates.length, (∃ z2 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z2)).getD ((Np + Nl) + j1) false = true) ∧ ((Np + Nl) + j1 = C.output ∨ ∃ k3 < C.gates.length, (Np + Nl) + j1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k3).inputs)) → (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)) → (∀ j12 < C.gates.length, (∀ z15 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z15)).getD ((Np + Nl) + j12) false = true → ∃ p16 : Fin Np, ∃ l17 : Fin Nl, I p16 l17 ∧ z15 (Fin.castAdd Nl p16) = true ∧ z15 (Fin.natAdd Np l17) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j12).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ w13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j12).inputs, (∀ z18 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z18)).getD (w13) false = true → ∃ p19 : Fin Np, ∃ l20 : Fin Nl, I p19 l20 ∧ z18 (Fin.castAdd Nl p19) = true ∧ z18 (Fin.natAdd Np l20) = true)) ∧ ((Np + Nl) + j12 ≠ C.output → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) ((Np + Nl) + j12) = 1 ∧ ∀ k14 < C.gates.length, (Np + Nl) + j12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ z21 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z21)).getD ((Np + Nl) + k14) false = true → ∃ p22 : Fin Np, ∃ l23 : Fin Nl, I p22 l23 ∧ z21 (Fin.castAdd Nl p22) = true ∧ z21 (Fin.natAdd Np l23) = true))) → (∀ j24 < C.gates.length, ∀ k25 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z28 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z28)).getD ((Np + Nl) + j24) false = true → ∃ p29 : Fin Np, ∃ l30 : Fin Nl, I p29 l30 ∧ z28 (Fin.castAdd Nl p29) = true ∧ z28 (Fin.natAdd Np l30) = true) → (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z31 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z31)).getD ((Np + Nl) + k25) false = true → ∃ p32 : Fin Np, ∃ l33 : Fin Nl, I p32 l33 ∧ z31 (Fin.castAdd Nl p32) = true ∧ z31 (Fin.natAdd Np l33) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs.Nodup ∧ ∀ w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs, w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).inputs → j24 = k25)) → c < C.gates.length → ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true) → (∀ k37 < C.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k37 c → ∀ g38 < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C g38 c → (Np + Nl) + g38 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k37).inputs) → (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true) → (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)) → (∀ p47 : Fin Np, ∀ l48 : Fin Nl, (I p47 l48 ∧ (C.wires (List.ofFn (fun i51 : Fin (Np + Nl) => decide (i51 = Fin.castAdd Nl p47)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i52 : Fin (Np + Nl) => decide (i52 = Fin.natAdd Np l48)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i53 : Fin (Np + Nl) => decide (i53 = Fin.castAdd Nl p47 ∨ i53 = Fin.natAdd Np l48)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p47 ∨ i54 = Fin.natAdd Np l48)) = false) → ∃ j49 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ z55 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z55)).getD ((Np + Nl) + j49) false = true → ∃ p56 : Fin Np, ∃ l57 : Fin Nl, I p56 l57 ∧ z55 (Fin.castAdd Nl p56) = true ∧ z55 (Fin.natAdd Np l57) = true) ∧ ∃ w50 : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [(Np + Nl) + c, w50] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [w50, (Np + Nl) + c]) ∧ ((C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p47)))).getD (w50) false = true ∨ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l48)))).getD (w50) false = true)) → (Finset.univ.filter fun v60 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i66 : Fin (Np + Nl) => decide (i66 = v60)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p61 : Fin Np => ∃ l62 : Fin Nl, (I p61 l62 ∧ (C.wires (List.ofFn (fun i67 : Fin (Np + Nl) => decide (i67 = Fin.castAdd Nl p61)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i68 : Fin (Np + Nl) => decide (i68 = Fin.natAdd Np l62)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i69 : Fin (Np + Nl) => decide (i69 = Fin.castAdd Nl p61 ∨ i69 = Fin.natAdd Np l62)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i70 : Fin (Np + Nl) => decide (i70 = Fin.castAdd Nl p61 ∨ i70 = Fin.natAdd Np l62)) = false)).card + (Finset.univ.filter fun l64 : Fin Nl => ∃ p63 : Fin Np, (I p63 l64 ∧ (C.wires (List.ofFn (fun i71 : Fin (Np + Nl) => decide (i71 = Fin.castAdd Nl p63)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i72 : Fin (Np + Nl) => decide (i72 = Fin.natAdd Np l64)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i73 : Fin (Np + Nl) => decide (i73 = Fin.castAdd Nl p63 ∨ i73 = Fin.natAdd Np l64)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i74 : Fin (Np + Nl) => decide (i74 = Fin.castAdd Nl p63 ∨ i74 = Fin.natAdd Np l64)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k65 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k65 c).card := by
  intro Np Nl I _ C c _h4 hAO _hF _H4 H5 _H6 _H7 hc hcNB _hpriv hlin hlost hpart
  exact main_core Np Nl I C c hAO H5 hc hcNB hlin hlost hpart
