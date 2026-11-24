import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2058_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadK

def dflt : Gate := ⟨GateOp.or, []⟩

def evf (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def rvf (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def run {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) init

theorem run_length {α : Type} (f : List α → Gate → α) :
    ∀ (gs : List Gate) (init : List α), (run f gs init).length = init.length + gs.length
  | [], init => by simp [run]
  | g :: gs, init => by
    simp only [run, List.foldl_cons, List.length_cons]
    have h := run_length f gs (init ++ [f init g])
    simp only [run, List.length_append, List.length_singleton] at h
    omega

theorem run_getD_lt {α : Type} (f : List α → Gate → α) (d : α) :
    ∀ (gs : List Gate) (init : List α) (i : ℕ), i < init.length →
      (run f gs init).getD i d = init.getD i d
  | [], _, _, _ => rfl
  | g :: gs, init, i, hi => by
    simp only [run, List.foldl_cons]
    have h1 := run_getD_lt f d gs (init ++ [f init g]) i (by simp; omega)
    simp only [run] at h1
    rw [h1, List.getD_append _ _ _ _ hi]

theorem run_gate_aux {α : Type} (f : List α → Gate → α) (d : α)
    (hcongr : ∀ (w₁ w₂ : List α) (g : Gate),
      (∀ i ∈ g.inputs, w₁.getD i d = w₂.getD i d) → f w₁ g = f w₂ g) :
    ∀ (gs : List Gate) (init : List α) (k : ℕ), k < gs.length →
      (∀ i ∈ (gs.getD k dflt).inputs, i < init.length + k) →
      (run f gs init).getD (init.length + k) d = f (run f gs init) (gs.getD k dflt)
  | [], _, _, hk, _ => absurd hk (by simp)
  | g :: gs, init, 0, _, hrb => by
    simp only [run, List.foldl_cons, Nat.add_zero]
    have h1 := run_getD_lt f d gs (init ++ [f init g]) init.length (by simp)
    simp only [run] at h1
    rw [h1, List.getD_append_right _ _ _ _ le_rfl]
    simp only [Nat.sub_self, List.getD_cons_zero]
    apply hcongr
    intro i hi
    have hlt : i < init.length := by simpa using hrb i hi
    have h2 := run_getD_lt f d gs (init ++ [f init g]) i (by simp; omega)
    simp only [run] at h2
    rw [h2, List.getD_append _ _ _ _ hlt]
  | g :: gs, init, k + 1, hk, hrb => by
    simp only [run, List.foldl_cons]
    have hrb' : ∀ i ∈ (gs.getD k dflt).inputs, i < (init ++ [f init g]).length + k := by
      intro i hi
      have := hrb i (by simpa using hi)
      simp only [List.length_append, List.length_singleton]
      omega
    have hih := run_gate_aux f d hcongr gs (init ++ [f init g]) k (by simpa using hk) hrb'
    simp only [run, List.length_append, List.length_singleton] at hih
    have hidx : init.length + (k + 1) = init.length + 1 + k := by omega
    rw [hidx]
    simpa using hih

theorem evf_congr (w₁ w₂ : List Bool) (g : Gate)
    (h : ∀ i ∈ g.inputs, w₁.getD i false = w₂.getD i false) : evf w₁ g = evf w₂ g := by
  unfold evf
  congr 1
  exact List.map_congr_left h

theorem rvf_congr (S : List ℕ) (k : ℕ) (w₁ w₂ : List (List (List ℕ))) (g : Gate)
    (h : ∀ i ∈ g.inputs, w₁.getD i [] = w₂.getD i []) : rvf S k w₁ g = rvf S k w₂ g := by
  unfold rvf
  have hm : g.inputs.map (fun i => w₁.getD i []) = g.inputs.map (fun i => w₂.getD i []) :=
    List.map_congr_left h
  rw [hm]

def wv (C : Circuit) (n : ℕ) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

theorem wv_input (C : Circuit) (n : ℕ) (z : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv C n z w = z ⟨w, hw⟩ := by
  change (run evf C.gates (List.ofFn z)).getD w false = z ⟨w, hw⟩
  rw [run_getD_lt evf false C.gates (List.ofFn z) w (by simpa using hw),
    List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

theorem wv_ge (C : Circuit) (n : ℕ) (z : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wv C n z w = false := by
  change (run evf C.gates (List.ofFn z)).getD w false = false
  exact List.getD_eq_default _ _ (by rw [run_length]; simpa using hw)

theorem wv_gate (C : Circuit) (n : ℕ) (z : Fin n → Bool) (hR : ReadsBack n C) (k : ℕ)
    (hk : k < C.gates.length) :
    wv C n z (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map (wv C n z)) := by
  have h := run_gate_aux evf false evf_congr C.gates (List.ofFn z) k hk
    (by simpa [gateAt, dflt] using hR k hk)
  rw [List.length_ofFn] at h
  exact h

theorem list_eq_two {α : Type} (l : List α) (hl : l.length = 2) (d : α) :
    l = [l.getD 0 d, l.getD 1 d] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp_all

theorem gate_info {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs = [(gateAt C j).inputs.getD 0 0, (gateAt C j).inputs.getD 1 0] := by
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hop := hAO.1 _ hmem
  have hlen := hAO.2.2 _ hmem
  exact ⟨by simpa using hop, list_eq_two _ hlen 0⟩

theorem wv_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {z₁ z₂ : Fin n → Bool}
    (hz : ∀ i, z₁ i = true → z₂ i = true) :
    ∀ w, wv C n z₁ w = true → wv C n z₂ w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with hw | hw
    · rw [wv_input C n z₁ w hw, wv_input C n z₂ w hw]
      exact hz ⟨w, hw⟩
    · rcases Nat.lt_or_ge (w - n) C.gates.length with hk | hk
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk' : k < C.gates.length := by omega
        obtain ⟨hop, hinp⟩ := gate_info hAO hk'
        rw [wv_gate C n z₁ hAO.2.1 k hk', wv_gate C n z₂ hAO.2.1 k hk', hinp]
        have ha : (gateAt C k).inputs.getD 0 0 < n + k := hAO.2.1 k hk' _ (by rw [hinp]; simp)
        have hb : (gateAt C k).inputs.getD 1 0 < n + k := hAO.2.1 k hk' _ (by rw [hinp]; simp)
        rcases hop with hand | hor
        · rw [hand]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true]
          rintro ⟨h1, h2⟩
          exact ⟨ih _ ha h1, ih _ hb h2⟩
        · rw [hor]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.or_eq_true]
          rintro (h1 | h2)
          · exact Or.inl (ih _ ha h1)
          · exact Or.inr (ih _ hb h2)
      · rw [wv_ge C n z₁ w (by omega)]
        intro h; cases h

def orStep (n : ℕ) (C : Circuit) (w₁ w₂ : ℕ) : Prop :=
  ∃ j < C.gates.length, w₁ = n + j ∧ (gateAt C j).op = GateOp.or ∧ w₂ ∈ (gateAt C j).inputs

def OrReach (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (orStep n C)

theorem orStep_wv {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (z : Fin n → Bool) {w₁ w₂ : ℕ}
    (hs : orStep n C w₁ w₂) (h2 : wv C n z w₂ = true) : wv C n z w₁ = true := by
  obtain ⟨j, hj, rfl, hor, hin⟩ := hs
  obtain ⟨_, hinp⟩ := gate_info hAO hj
  rw [wv_gate C n z hAO.2.1 j hj, hor, hinp]
  rw [hinp] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, Bool.or_eq_true]
  rcases hin with rfl | rfl
  · exact Or.inl h2
  · exact Or.inr h2

theorem orReach_wv {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (z : Fin n → Bool) {w₁ w₂ : ℕ}
    (hr : OrReach n C w₁ w₂) : wv C n z w₂ = true → wv C n z w₁ = true := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact id
  | head hs _ ih => intro h; exact orStep_wv hAO z hs (ih h)

def rv (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

theorem rv_input (C : Circuit) (n : ℕ) (S : List ℕ) (k w : ℕ) (hw : w < n) :
    rv C n S k w = leafVectors S k w := by
  change (run (rvf S k) C.gates ((List.range n).map (leafVectors S k))).getD w [] = _
  rw [run_getD_lt (rvf S k) [] C.gates _ w (by simpa using hw),
    List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

theorem rv_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k w : ℕ) (hw : n + C.gates.length ≤ w) :
    rv C n S k w = [] := by
  change (run (rvf S k) C.gates ((List.range n).map (leafVectors S k))).getD w [] = []
  exact List.getD_eq_default _ _ (by rw [run_length]; simpa using hw)

theorem rv_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (hR : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    rv C n S k (n + j) = rvf S k (readVectors C n S k) (gateAt C j) := by
  have h := run_gate_aux (rvf S k) [] (rvf_congr S k) C.gates
    ((List.range n).map (leafVectors S k)) j hj (by simpa [gateAt, dflt] using hR j hj)
  rw [List.length_map, List.length_range] at h
  exact h

theorem mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | rfl) <;> assumption
  · simp

theorem mem_foldl_insertNew : ∀ (B A : List (List ℕ)) (x : List ℕ),
    x ∈ B.foldl insertNew A ↔ x ∈ A ∨ x ∈ B
  | [], A, x => by simp
  | v :: B, A, x => by
    simp only [List.foldl_cons, mem_foldl_insertNew, mem_insertNew, List.mem_cons]
    tauto

theorem mem_andStep (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, x = capAdd k u v := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩

theorem capAdd_zero_left (k : ℕ) (a b : ℕ) (ha : a ≤ k + 1) (hb : b ≤ k + 1) :
    capAdd k [0, 0] [a, b] = [a, b] := by
  simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, Nat.zero_add]
  rw [Nat.min_eq_left ha, Nat.min_eq_left hb]

theorem rv_or_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (S : List ℕ) (k j : ℕ)
    (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (v : List ℕ) :
    v ∈ rv C n S k (n + j) ↔
      v ∈ rv C n S k ((gateAt C j).inputs.getD 0 0) ∨
      v ∈ rv C n S k ((gateAt C j).inputs.getD 1 0) := by
  obtain ⟨_, hinp⟩ := gate_info hAO hj
  rw [rv_gate C n S k hAO.2.1 j hj]
  unfold rvf
  rw [hor, hinp]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, mem_foldl_insertNew,
    List.not_mem_nil, false_or]
  rfl

theorem leafVectors_pair {N : ℕ} (p l : Fin N) :
    leafVectors [p.val, N + l.val] 2 p.val = [[1, 0]] ∧
    leafVectors [p.val, N + l.val] 2 (N + l.val) = [[0, 1]] := by
  have hne1 : p.val ≠ N + l.val := by omega
  have hne2 : N + l.val ≠ p.val := by omega
  constructor
  · simp [leafVectors, hne2]
  · simp [leafVectors, hne1]

theorem rv_shape {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) (p l : Fin N) :
    ∀ w v, v ∈ rv C (N + N) [p.val, N + l.val] 2 w →
      ∃ a b : ℕ, v = [a, b] ∧ a ≤ 3 ∧ b ≤ 3 ∧ 1 ≤ a + b := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases Nat.lt_or_ge w (N + N) with hw | hw
    · rw [rv_input C (N + N) [p.val, N + l.val] 2 w hw] at hv
      by_cases hwp : w = p.val
      · rw [hwp, (leafVectors_pair p l).1] at hv
        simp only [List.mem_singleton] at hv
        exact ⟨1, 0, hv, by omega, by omega, by omega⟩
      · by_cases hwl : w = N + l.val
        · rw [hwl, (leafVectors_pair p l).2] at hv
          simp only [List.mem_singleton] at hv
          exact ⟨0, 1, hv, by omega, by omega, by omega⟩
        · unfold leafVectors at hv
          have hnm : w ∉ [p.val, N + l.val] := by simp [hwp, hwl]
          simp [hnm] at hv
    · rcases Nat.lt_or_ge (w - (N + N)) C.gates.length with hj | hj
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj' : j < C.gates.length := by omega
        obtain ⟨hop, hinp⟩ := gate_info hAO hj'
        have ha : (gateAt C j).inputs.getD 0 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        have hb : (gateAt C j).inputs.getD 1 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        rcases hop with hand | hor
        · rw [rv_gate C (N + N) [p.val, N + l.val] 2 hAO.2.1 j hj'] at hv
          unfold rvf at hv
          rw [hand, hinp] at hv
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hv
          rw [mem_andStep] at hv
          obtain ⟨u, hu, v2, hv2, rfl⟩ := hv
          rw [mem_andStep] at hu
          obtain ⟨z, hz, v1, hv1, rfl⟩ := hu
          simp only [List.mem_singleton] at hz
          subst hz
          obtain ⟨a1, b1, rfl, ha1, hb1, hp1⟩ := ih _ ha v1 hv1
          obtain ⟨a2, b2, rfl, ha2, hb2, hp2⟩ := ih _ hb v2 hv2
          rw [capAdd_zero_left 2 a1 b1 ha1 hb1]
          refine ⟨min (a1 + a2) 3, min (b1 + b2) 3, rfl, Nat.min_le_right _ _, Nat.min_le_right _ _, ?_⟩
          omega
        · rw [rv_or_iff hAO _ 2 j hj' hor] at hv
          rcases hv with h1 | h2
          · exact ih _ ha v h1
          · exact ih _ hb v h2
      · rw [rv_ge C (N + N) _ 2 w (by omega)] at hv
        simp at hv

theorem rv_and_iff {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) (p l : Fin N) (j : ℕ)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (a b : ℕ) :
    [a, b] ∈ rv C (N + N) [p.val, N + l.val] 2 (N + N + j) ↔
      ∃ a1 b1 a2 b2 : ℕ,
        [a1, b1] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C j).inputs.getD 0 0) ∧
        [a2, b2] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C j).inputs.getD 1 0) ∧
        a = min (a1 + a2) 3 ∧ b = min (b1 + b2) 3 := by
  obtain ⟨_, hinp⟩ := gate_info hAO hj
  rw [rv_gate C (N + N) [p.val, N + l.val] 2 hAO.2.1 j hj]
  unfold rvf
  rw [hand, hinp]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, mem_andStep,
    List.mem_singleton]
  constructor
  · rintro ⟨u, ⟨z, rfl, v1, hv1, rfl⟩, v2, hv2, heq⟩
    obtain ⟨a1, b1, rfl, ha1, hb1, _⟩ := rv_shape hAO p l _ v1 hv1
    obtain ⟨a2, b2, rfl, ha2, hb2, _⟩ := rv_shape hAO p l _ v2 hv2
    rw [capAdd_zero_left 2 a1 b1 ha1 hb1] at heq
    simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons.injEq,
      and_true] at heq
    exact ⟨a1, b1, a2, b2, hv1, hv2, heq.1, heq.2⟩
  · rintro ⟨a1, b1, a2, b2, hv1, hv2, rfl, rfl⟩
    obtain ⟨_, _, h1, ha1, hb1, _⟩ := rv_shape hAO p l _ _ hv1
    have h1a : a1 ≤ 3 := by cases h1; exact ha1
    have h1b : b1 ≤ 3 := by cases h1; exact hb1
    refine ⟨[a1, b1], ⟨[0, 0], rfl, [a1, b1], hv1, (capAdd_zero_left 2 a1 b1 h1a h1b).symm⟩,
      [a2, b2], hv2, rfl⟩

theorem rv_10 {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) (p l : Fin N) :
    ∀ w, [1, 0] ∈ rv C (N + N) [p.val, N + l.val] 2 w → OrReach (N + N) C w p.val := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    rcases Nat.lt_or_ge w (N + N) with hw | hw
    · rw [rv_input C (N + N) [p.val, N + l.val] 2 w hw] at hv
      by_cases hwp : w = p.val
      · rw [hwp]; exact Relation.ReflTransGen.refl
      · by_cases hwl : w = N + l.val
        · rw [hwl, (leafVectors_pair p l).2] at hv; simp at hv
        · unfold leafVectors at hv
          have hnm : w ∉ [p.val, N + l.val] := by simp [hwp, hwl]
          simp [hnm] at hv
    · rcases Nat.lt_or_ge (w - (N + N)) C.gates.length with hj | hj
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj' : j < C.gates.length := by omega
        obtain ⟨hop, hinp⟩ := gate_info hAO hj'
        have ha : (gateAt C j).inputs.getD 0 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        have hb : (gateAt C j).inputs.getD 1 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        rcases hop with hand | hor
        · rw [rv_and_iff hAO p l j hj' hand] at hv
          obtain ⟨a1, b1, a2, b2, h1, h2, hae, hbe⟩ := hv
          obtain ⟨_, _, he1, _, _, hp1⟩ := rv_shape hAO p l _ _ h1
          obtain ⟨_, _, he2, _, _, hp2⟩ := rv_shape hAO p l _ _ h2
          cases he1; cases he2; omega
        · rw [rv_or_iff hAO _ 2 j hj' hor] at hv
          rcases hv with h1 | h2
          · exact Relation.ReflTransGen.head ⟨j, hj', rfl, hor, by rw [hinp]; simp⟩ (ih _ ha h1)
          · exact Relation.ReflTransGen.head ⟨j, hj', rfl, hor, by rw [hinp]; simp⟩ (ih _ hb h2)
      · rw [rv_ge C (N + N) _ 2 w (by omega)] at hv; simp at hv

theorem rv_01 {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) (p l : Fin N) :
    ∀ w, [0, 1] ∈ rv C (N + N) [p.val, N + l.val] 2 w → OrReach (N + N) C w (N + l.val) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    rcases Nat.lt_or_ge w (N + N) with hw | hw
    · rw [rv_input C (N + N) [p.val, N + l.val] 2 w hw] at hv
      by_cases hwp : w = p.val
      · rw [hwp, (leafVectors_pair p l).1] at hv; simp at hv
      · by_cases hwl : w = N + l.val
        · rw [hwl]; exact Relation.ReflTransGen.refl
        · unfold leafVectors at hv
          have hnm : w ∉ [p.val, N + l.val] := by simp [hwp, hwl]
          simp [hnm] at hv
    · rcases Nat.lt_or_ge (w - (N + N)) C.gates.length with hj | hj
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj' : j < C.gates.length := by omega
        obtain ⟨hop, hinp⟩ := gate_info hAO hj'
        have ha : (gateAt C j).inputs.getD 0 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        have hb : (gateAt C j).inputs.getD 1 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        rcases hop with hand | hor
        · rw [rv_and_iff hAO p l j hj' hand] at hv
          obtain ⟨a1, b1, a2, b2, h1, h2, hae, hbe⟩ := hv
          obtain ⟨_, _, he1, _, _, hp1⟩ := rv_shape hAO p l _ _ h1
          obtain ⟨_, _, he2, _, _, hp2⟩ := rv_shape hAO p l _ _ h2
          cases he1; cases he2; omega
        · rw [rv_or_iff hAO _ 2 j hj' hor] at hv
          rcases hv with h1 | h2
          · exact Relation.ReflTransGen.head ⟨j, hj', rfl, hor, by rw [hinp]; simp⟩ (ih _ ha h1)
          · exact Relation.ReflTransGen.head ⟨j, hj', rfl, hor, by rw [hinp]; simp⟩ (ih _ hb h2)
      · rw [rv_ge C (N + N) _ 2 w (by omega)] at hv; simp at hv

theorem rv_split {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) (p l : Fin N) :
    ∀ w a b, [a, b] ∈ rv C (N + N) [p.val, N + l.val] 2 w → a ≤ 2 → b ≤ 2 → 2 ≤ a + b →
      ∃ j < C.gates.length, ∃ a1 b1 a2 b2 : ℕ,
        OrReach (N + N) C w (N + N + j) ∧ (gateAt C j).op = GateOp.and ∧
        [a1, b1] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C j).inputs.getD 0 0) ∧
        [a2, b2] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C j).inputs.getD 1 0) ∧
        a1 + a2 = a ∧ b1 + b2 = b ∧ 1 ≤ a1 + b1 ∧ 1 ≤ a2 + b2 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro a b hv ha2 hb2 hab
    rcases Nat.lt_or_ge w (N + N) with hw | hw
    · rw [rv_input C (N + N) [p.val, N + l.val] 2 w hw] at hv
      by_cases hwp : w = p.val
      · rw [hwp, (leafVectors_pair p l).1] at hv
        simp only [List.mem_singleton, List.cons.injEq, and_true] at hv; omega
      · by_cases hwl : w = N + l.val
        · rw [hwl, (leafVectors_pair p l).2] at hv
          simp only [List.mem_singleton, List.cons.injEq, and_true] at hv; omega
        · unfold leafVectors at hv
          have hnm : w ∉ [p.val, N + l.val] := by simp [hwp, hwl]
          simp [hnm] at hv
    · rcases Nat.lt_or_ge (w - (N + N)) C.gates.length with hj | hj
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj' : j < C.gates.length := by omega
        obtain ⟨hop, hinp⟩ := gate_info hAO hj'
        have hlt0 : (gateAt C j).inputs.getD 0 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        have hlt1 : (gateAt C j).inputs.getD 1 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        rcases hop with hand | hor
        · rw [rv_and_iff hAO p l j hj' hand] at hv
          obtain ⟨a1, b1, a2, b2, h1, h2, hae, hbe⟩ := hv
          obtain ⟨_, _, he1, _, _, hp1⟩ := rv_shape hAO p l _ _ h1
          obtain ⟨_, _, he2, _, _, hp2⟩ := rv_shape hAO p l _ _ h2
          cases he1; cases he2
          refine ⟨j, hj', a1, b1, a2, b2, Relation.ReflTransGen.refl, hand, h1, h2,
            by omega, by omega, hp1, hp2⟩
        · rw [rv_or_iff hAO _ 2 j hj' hor] at hv
          rcases hv with h1 | h2
          · obtain ⟨j0, hj0, a1, b1, a2, b2, hreach, hand0, hv1, hv2, hrest⟩ :=
              ih _ hlt0 a b h1 ha2 hb2 hab
            exact ⟨j0, hj0, a1, b1, a2, b2,
              Relation.ReflTransGen.head ⟨j, hj', rfl, hor, by rw [hinp]; simp⟩ hreach,
              hand0, hv1, hv2, hrest⟩
          · obtain ⟨j0, hj0, a1, b1, a2, b2, hreach, hand0, hv1, hv2, hrest⟩ :=
              ih _ hlt1 a b h2 ha2 hb2 hab
            exact ⟨j0, hj0, a1, b1, a2, b2,
              Relation.ReflTransGen.head ⟨j, hj', rfl, hor, by rw [hinp]; simp⟩ hreach,
              hand0, hv1, hv2, hrest⟩
      · rw [rv_ge C (N + N) _ 2 w (by omega)] at hv; simp at hv

theorem rv_sound_wv {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) (p l : Fin N)
    (z : Fin (N + N) → Bool) :
    ∀ w a b, [a, b] ∈ rv C (N + N) [p.val, N + l.val] 2 w →
      (1 ≤ a → z (Fin.castAdd N p) = true) →
      (1 ≤ b → z (Fin.natAdd N l) = true) →
      wv C (N + N) z w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro a b hv ha hb
    rcases Nat.lt_or_ge w (N + N) with hw | hw
    · rw [rv_input C (N + N) [p.val, N + l.val] 2 w hw] at hv
      by_cases hwp : w = p.val
      · subst hwp
        rw [(leafVectors_pair p l).1] at hv
        simp only [List.mem_singleton, List.cons.injEq, and_true] at hv
        rw [wv_input C (N + N) z p.val hw]
        exact ha (by omega)
      · by_cases hwl : w = N + l.val
        · subst hwl
          rw [(leafVectors_pair p l).2] at hv
          simp only [List.mem_singleton, List.cons.injEq, and_true] at hv
          rw [wv_input C (N + N) z (N + l.val) hw]
          exact hb (by omega)
        · unfold leafVectors at hv
          have hnm : w ∉ [p.val, N + l.val] := by simp [hwp, hwl]
          simp [hnm] at hv
    · rcases Nat.lt_or_ge (w - (N + N)) C.gates.length with hj | hj
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj' : j < C.gates.length := by omega
        obtain ⟨hop, hinp⟩ := gate_info hAO hj'
        have hlt0 : (gateAt C j).inputs.getD 0 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        have hlt1 : (gateAt C j).inputs.getD 1 0 < N + N + j := hAO.2.1 j hj' _ (by rw [hinp]; simp)
        rcases hop with hand | hor
        · rw [rv_and_iff hAO p l j hj' hand] at hv
          obtain ⟨a1, b1, a2, b2, h1, h2, hae, hbe⟩ := hv
          rw [wv_gate C (N + N) z hAO.2.1 j hj', hand, hinp]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true]
          exact ⟨ih _ hlt0 a1 b1 h1 (fun h => ha (by omega)) (fun h => hb (by omega)),
                 ih _ hlt1 a2 b2 h2 (fun h => ha (by omega)) (fun h => hb (by omega))⟩
        · rw [rv_or_iff hAO _ 2 j hj' hor] at hv
          rw [wv_gate C (N + N) z hAO.2.1 j hj', hor, hinp]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.or_eq_true]
          rcases hv with h1 | h2
          · exact Or.inl (ih _ hlt0 a b h1 ha hb)
          · exact Or.inr (ih _ hlt1 a b h2 ha hb)
      · rw [rv_ge C (N + N) _ 2 w (by omega)] at hv; simp at hv

theorem setList_pair {N : ℕ} (p l : Fin N) :
    setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) = [p.val, N + l.val] := by
  have hlt : Fin.castAdd N p < Fin.natAdd N l := by
    change p.val < N + l.val; omega
  set flt := (List.finRange (N + N)).filter
    (fun i => decide (i ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N)))))
  have hfilter : flt = [Fin.castAdd N p, Fin.natAdd N l] := by
    have hnd : flt.Nodup := (List.nodup_finRange (N + N)).filter _
    have hst : flt.Pairwise (· < ·) := (List.pairwise_lt_finRange (N + N)).filter _
    have hmem : ∀ x : Fin (N + N), x ∈ flt ↔ x ∈ [Fin.castAdd N p, Fin.natAdd N l] := by
      intro x; simp [flt]
    have hlen : flt.length = 2 := by
      have h1 := List.toFinset_card_of_nodup hnd
      have h2 : flt.toFinset = {Fin.castAdd N p, Fin.natAdd N l} := by
        ext x; simp [flt]
      rw [h2, Finset.card_pair (ne_of_lt hlt)] at h1
      exact h1.symm
    rcases heq : flt with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
    · rw [heq] at hlen; simp at hlen
    · rw [heq] at hlen; simp at hlen
    · rw [heq] at hst hmem
      have hxy : x < y := (List.pairwise_cons.mp hst).1 y (by simp)
      have hx : x = Fin.castAdd N p ∨ x = Fin.natAdd N l := by simpa using (hmem x).mp (by simp)
      have hy : y = Fin.castAdd N p ∨ y = Fin.natAdd N l := by simpa using (hmem y).mp (by simp)
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd hxy (lt_irrefl _)
      · rfl
      · exact absurd (lt_trans hlt hxy) (lt_irrefl _)
      · exact absurd hxy (lt_irrefl _)
    · rw [heq] at hlen; simp at hlen
  unfold setList
  change flt.map Fin.val = [p.val, N + l.val]
  rw [hfilter]
  simp [Nat.add_comm]

theorem no_c4 {N : ℕ} {I : Fin N → Fin N → Prop}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {p p' l l' : Fin N} (hpp : p ≠ p') (hll : l ≠ l')
    (h1 : I p l) (h2 : I p' l) (h3 : I p l') : ¬ I p' l' := by
  intro h4
  obtain ⟨_, _, hu⟩ := huniq p p' hpp
  exact hll ((hu l ⟨h1, h2⟩).trans (hu l' ⟨h3, h4⟩).symm)

theorem unique_p_of_two_l {N : ℕ} {I : Fin N → Fin N → Prop}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {S : Finset (Fin N)} (hS : 2 ≤ S.card) {p p' : Fin N}
    (hp : ∀ l ∈ S, I p l) (hp' : ∀ l ∈ S, I p' l) : p = p' := by
  by_contra hne
  obtain ⟨l1, hl1, l2, hl2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  exact no_c4 huniq hne h12 (hp l1 hl1) (hp' l1 hl1) (hp l2 hl2) (hp' l2 hl2)

theorem unique_l_of_two_p {N : ℕ} {I : Fin N → Fin N → Prop}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {S : Finset (Fin N)} (hS : 2 ≤ S.card) {l l' : Fin N}
    (hl : ∀ p ∈ S, I p l) (hl' : ∀ p ∈ S, I p l') : l = l' := by
  by_contra hne
  obtain ⟨p1, hp1, p2, hp2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  exact no_c4 huniq h12 hne (hl p1 hp1) (hl p2 hp2) (hl' p1 hp1) (hl' p2 hp2)

theorem unique_p_of_near_l {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {S : Finset (Fin N)} (hS : 4 ≤ S.card) {p p' : Fin N}
    (hp : (S.filter fun l => ¬ I p l).card ≤ 1)
    (hp' : (S.filter fun l => ¬ I p' l).card ≤ 1) : p = p' := by
  set T := S.filter (fun l => I p l ∧ I p' l)
  have hsub : S \ T ⊆ (S.filter fun l => ¬ I p l) ∪ (S.filter fun l => ¬ I p' l) := by
    intro l hl
    rw [Finset.mem_sdiff] at hl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h1 : I p l
    · right; refine ⟨hl.1, fun h2 => hl.2 (Finset.mem_filter.mpr ⟨hl.1, h1, h2⟩)⟩
    · left; exact ⟨hl.1, h1⟩
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hcard : (S \ T).card ≤ 2 :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  have hTcard : 2 ≤ T.card := by
    have := Finset.card_sdiff_add_card_eq_card hTsub
    omega
  exact unique_p_of_two_l huniq hTcard (fun l hl => (Finset.mem_filter.mp hl).2.1)
    (fun l hl => (Finset.mem_filter.mp hl).2.2)

theorem unique_l_of_near_p {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {S : Finset (Fin N)} (hS : 4 ≤ S.card) {l l' : Fin N}
    (hl : (S.filter fun p => ¬ I p l).card ≤ 1)
    (hl' : (S.filter fun p => ¬ I p l').card ≤ 1) : l = l' := by
  set T := S.filter (fun p => I p l ∧ I p l')
  have hsub : S \ T ⊆ (S.filter fun p => ¬ I p l) ∪ (S.filter fun p => ¬ I p l') := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h1 : I p l
    · right; refine ⟨hp.1, fun h2 => hp.2 (Finset.mem_filter.mpr ⟨hp.1, h1, h2⟩)⟩
    · left; exact ⟨hp.1, h1⟩
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hcard : (S \ T).card ≤ 2 :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  have hTcard : 2 ≤ T.card := by
    have := Finset.card_sdiff_add_card_eq_card hTsub
    omega
  exact unique_l_of_two_p huniq hTcard (fun p hp => (Finset.mem_filter.mp hp).2.1)
    (fun p hp => (Finset.mem_filter.mp hp).2.2)

theorem card_le_of_fiber {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop) [∀ x y, Decidable (R x y)] (K : ℕ)
    (hcov : ∀ x ∈ A, ∃ y ∈ B, R x y)
    (hfib : ∀ y ∈ B, (A.filter fun x => R x y).card ≤ K) :
    A.card ≤ K * B.card := by
  have hsub : A ⊆ B.biUnion (fun y => A.filter fun x => R x y) := by
    intro x hx
    obtain ⟨y, hy, hr⟩ := hcov x hx
    exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_filter.mpr ⟨hx, hr⟩⟩
  calc A.card ≤ (B.biUnion (fun y => A.filter fun x => R x y)).card := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ B, (A.filter fun x => R x y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ B, K := Finset.sum_le_sum (fun y hy => hfib y hy)
    _ = K * B.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem filter_or_card_le {α : Type} [DecidableEq α] (A : Finset α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (A.filter fun x => P x ∨ Q x).card ≤ (A.filter P).card + (A.filter Q).card := by
  have hsub : A.filter (fun x => P x ∨ Q x) ⊆ A.filter P ∪ A.filter Q := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hx.2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨hx.1, h⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem orReach_sub_F {n N : ℕ} {C : Circuit} (F : ℕ → Finset (Fin N))
    (hmono : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, F i ⊆ F (n + j))
    {w1 w2 : ℕ} (hr : OrReach n C w1 w2) : F w2 ⊆ F w1 := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact Finset.Subset.refl _
  | head hs _ ih =>
    obtain ⟨j, hj, rfl, hor, hi⟩ := hs
    exact Finset.Subset.trans ih (hmono j hj hor _ hi)

theorem or_walk_drop {n N : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (F : ℕ → Finset (Fin N))
    (hmono : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, F i ⊆ F (n + j))
    (K : ℕ) {w w0 : ℕ} {y : Fin N}
    (hr : OrReach n C w w0) (hhi : K < (F w).card) (hlo : (F w0).card ≤ K) (hy : y ∈ F w0) :
    ∃ j < C.gates.length, ∃ s : Fin 2,
      OrReach n C w (n + j) ∧ (gateAt C j).op = GateOp.or ∧
      K < (F (n + j)).card ∧ F (n + j) ⊆ F w ∧
      (F ((gateAt C j).inputs.getD s.val 0)).card ≤ K ∧
      y ∈ F ((gateAt C j).inputs.getD s.val 0) := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => omega
  | @head a b hs hr2 ih =>
    obtain ⟨j, hj, rfl, hor, hbin⟩ := hs
    obtain ⟨_, hinp⟩ := gate_info hAO hj
    have hbsub : F b ⊆ F (n + j) := hmono j hj hor b hbin
    have hyb : y ∈ F b := orReach_sub_F F hmono hr2 hy
    by_cases hbig : K < (F b).card
    · obtain ⟨j0, hj0, s0, hr0, hor0, h1, h2, h3, h4⟩ := ih hbig
      exact ⟨j0, hj0, s0, Relation.ReflTransGen.head ⟨j, hj, rfl, hor, hbin⟩ hr0,
        hor0, h1, Finset.Subset.trans h2 hbsub, h3, h4⟩
    · have hble : (F b).card ≤ K := by omega
      rw [hinp] at hbin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbin
      rcases hbin with rfl | rfl
      · exact ⟨j, hj, ⟨0, by omega⟩, Relation.ReflTransGen.refl, hor, hhi, Finset.Subset.refl _, hble, hyb⟩
      · exact ⟨j, hj, ⟨1, by omega⟩, Relation.ReflTransGen.refl, hor, hhi, Finset.Subset.refl _, hble, hyb⟩

theorem mf_mp {α : Type} {s : Finset α} {p : α → Prop} {d : DecidablePred p} {a : α}
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

theorem mfu_mpr {α : Type} [Fintype α] {p : α → Prop} {d : DecidablePred p} {a : α}
    (hp : p a) : a ∈ @Finset.filter α p d Finset.univ :=
  (@Finset.mem_filter α p d Finset.univ a).mpr ⟨Finset.mem_univ a, hp⟩

noncomputable def Ps (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N) (fun p => wv C (N + N) (setInput {Fin.castAdd N p}) w = true)
    (fun _ => Classical.propDecidable _) Finset.univ

noncomputable def Ls (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N) (fun l => wv C (N + N) (setInput {Fin.natAdd N l}) w = true)
    (fun _ => Classical.propDecidable _) Finset.univ

noncomputable def PO (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N) (fun p => OrReach (N + N) C w p.val)
    (fun _ => Classical.propDecidable _) Finset.univ

noncomputable def LO (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N) (fun l => OrReach (N + N) C w (N + l.val))
    (fun _ => Classical.propDecidable _) Finset.univ

theorem mem_Ps {N : ℕ} {C : Circuit} {w : ℕ} {p : Fin N} :
    p ∈ Ps N C w ↔ wv C (N + N) (setInput {Fin.castAdd N p}) w = true := by
  simp only [Ps, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_Ls {N : ℕ} {C : Circuit} {w : ℕ} {l : Fin N} :
    l ∈ Ls N C w ↔ wv C (N + N) (setInput {Fin.natAdd N l}) w = true := by
  simp only [Ls, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_PO {N : ℕ} {C : Circuit} {w : ℕ} {p : Fin N} :
    p ∈ PO N C w ↔ OrReach (N + N) C w p.val := by
  simp only [PO, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_LO {N : ℕ} {C : Circuit} {w : ℕ} {l : Fin N} :
    l ∈ LO N C w ↔ OrReach (N + N) C w (N + l.val) := by
  simp only [LO, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def BadL (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N)
    (fun l => ∃ p : Fin N, ¬ I p l ∧ wv C (N + N) (setInput {Fin.castAdd N p, Fin.natAdd N l}) w = true)
    (fun _ => Classical.propDecidable _) Finset.univ

noncomputable def BadP (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N)
    (fun p => ∃ l : Fin N, ¬ I p l ∧ wv C (N + N) (setInput {Fin.castAdd N p, Fin.natAdd N l}) w = true)
    (fun _ => Classical.propDecidable _) Finset.univ

noncomputable def BadL2 (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N)
    (fun l => ∃ p1 p2 : Fin N, p1 ≠ p2 ∧ ¬ I p1 l ∧ ¬ I p2 l ∧
      wv C (N + N) (setInput {Fin.castAdd N p1, Fin.natAdd N l}) w = true ∧
      wv C (N + N) (setInput {Fin.castAdd N p2, Fin.natAdd N l}) w = true)
    (fun _ => Classical.propDecidable _) Finset.univ

noncomputable def BadP2 (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N)
    (fun p => ∃ l1 l2 : Fin N, l1 ≠ l2 ∧ ¬ I p l1 ∧ ¬ I p l2 ∧
      wv C (N + N) (setInput {Fin.castAdd N p, Fin.natAdd N l1}) w = true ∧
      wv C (N + N) (setInput {Fin.castAdd N p, Fin.natAdd N l2}) w = true)
    (fun _ => Classical.propDecidable _) Finset.univ

noncomputable def BadLT (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N)
    (fun l => ∃ p2 l2a l2b : Fin N, l2a ≠ l2b ∧ ¬ I p2 l ∧ ¬ I p2 l2a ∧ ¬ I p2 l2b ∧
      wv C (N + N) (setInput {Fin.castAdd N p2, Fin.natAdd N l, Fin.natAdd N l2a}) w = true ∧
      wv C (N + N) (setInput {Fin.castAdd N p2, Fin.natAdd N l, Fin.natAdd N l2b}) w = true)
    (fun _ => Classical.propDecidable _) Finset.univ

noncomputable def BadPT (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N)
    (fun p => ∃ l2 p2a p2b : Fin N, p2a ≠ p2b ∧ ¬ I p l2 ∧ ¬ I p2a l2 ∧ ¬ I p2b l2 ∧
      wv C (N + N) (setInput {Fin.castAdd N p, Fin.castAdd N p2a, Fin.natAdd N l2}) w = true ∧
      wv C (N + N) (setInput {Fin.castAdd N p, Fin.castAdd N p2b, Fin.natAdd N l2}) w = true)
    (fun _ => Classical.propDecidable _) Finset.univ

def BadLT_ok (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (w : ℕ) (p : Fin N) : Prop :=
  ∀ l' ∈ BadLT N I C w, ∀ p2 l2a l2b : Fin N,
    l2a ≠ l2b → ¬ I p2 l' → ¬ I p2 l2a → ¬ I p2 l2b →
    wv C (N + N) (setInput {Fin.castAdd N p2, Fin.natAdd N l', Fin.natAdd N l2a}) w = true →
    wv C (N + N) (setInput {Fin.castAdd N p2, Fin.natAdd N l', Fin.natAdd N l2b}) w = true →
    I p l' ∨ (I p l2a ∧ I p l2b)

def BadPT_ok (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (w : ℕ) (l : Fin N) : Prop :=
  ∀ p' ∈ BadPT N I C w, ∀ l2 p2a p2b : Fin N,
    p2a ≠ p2b → ¬ I p' l2 → ¬ I p2a l2 → ¬ I p2b l2 →
    wv C (N + N) (setInput {Fin.castAdd N p', Fin.castAdd N p2a, Fin.natAdd N l2}) w = true →
    wv C (N + N) (setInput {Fin.castAdd N p', Fin.castAdd N p2b, Fin.natAdd N l2}) w = true →
    I p' l ∨ (I p2a l ∧ I p2b l)

theorem or_mono_Ps {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, Ps N C i ⊆ Ps N C (N + N + j) := fun j hj hor _i hi _ hp =>
  mem_Ps.mpr (orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ (mem_Ps.mp hp))

theorem or_mono_Ls {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, Ls N C i ⊆ Ls N C (N + N + j) := fun j hj hor _i hi _ hl =>
  mem_Ls.mpr (orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ (mem_Ls.mp hl))

theorem or_mono_PO {N : ℕ} {C : Circuit} :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, PO N C i ⊆ PO N C (N + N + j) := fun j hj hor _i hi _ hp =>
  mem_PO.mpr (Relation.ReflTransGen.head ⟨j, hj, rfl, hor, hi⟩ (mem_PO.mp hp))

theorem or_mono_LO {N : ℕ} {C : Circuit} :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, LO N C i ⊆ LO N C (N + N + j) := fun j hj hor _i hi _ hl =>
  mem_LO.mpr (Relation.ReflTransGen.head ⟨j, hj, rfl, hor, hi⟩ (mem_LO.mp hl))

theorem or_mono_BadL {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} (hAO : IsAO2 (N + N) C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, BadL N I C i ⊆ BadL N I C (N + N + j) := by
  intro j hj hor i hi l hl
  obtain ⟨p, hni, hv⟩ := mf_mp hl
  exact mfu_mpr ⟨p, hni, orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv⟩

theorem or_mono_BadP {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} (hAO : IsAO2 (N + N) C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, BadP N I C i ⊆ BadP N I C (N + N + j) := by
  intro j hj hor i hi p hp
  obtain ⟨l, hni, hv⟩ := mf_mp hp
  exact mfu_mpr ⟨l, hni, orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv⟩

theorem or_mono_BadL2 {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} (hAO : IsAO2 (N + N) C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, BadL2 N I C i ⊆ BadL2 N I C (N + N + j) := by
  intro j hj hor i hi l hl
  obtain ⟨p1, p2, hne, h1, h2, hv1, hv2⟩ := mf_mp hl
  exact mfu_mpr ⟨p1, p2, hne, h1, h2,
    orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv1, orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv2⟩

theorem or_mono_BadP2 {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} (hAO : IsAO2 (N + N) C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, BadP2 N I C i ⊆ BadP2 N I C (N + N + j) := by
  intro j hj hor i hi p hp
  obtain ⟨l1, l2, hne, h1, h2, hv1, hv2⟩ := mf_mp hp
  exact mfu_mpr ⟨l1, l2, hne, h1, h2,
    orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv1, orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv2⟩

theorem or_mono_BadLT {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} (hAO : IsAO2 (N + N) C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, BadLT N I C i ⊆ BadLT N I C (N + N + j) := by
  intro j hj hor i hi l hl
  obtain ⟨p2, l2a, l2b, hne, h1, h2, h3, hv1, hv2⟩ := mf_mp hl
  exact mfu_mpr ⟨p2, l2a, l2b, hne, h1, h2, h3,
    orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv1, orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv2⟩

theorem or_mono_BadPT {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} (hAO : IsAO2 (N + N) C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, BadPT N I C i ⊆ BadPT N I C (N + N + j) := by
  intro j hj hor i hi p hp
  obtain ⟨l2, p2a, p2b, hne, h1, h2, h3, hv1, hv2⟩ := mf_mp hp
  exact mfu_mpr ⟨l2, p2a, p2b, hne, h1, h2, h3,
    orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv1, orStep_wv hAO _ ⟨j, hj, rfl, hor, hi⟩ hv2⟩

theorem card_badLT_ok_le_three {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {w : ℕ} (h2 : 2 ≤ (BadLT N I C w).card) :
    (@Finset.filter (Fin N) (BadLT_ok N I C w) (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 3 := by
  classical
  obtain ⟨l1, hl1, l2, hl2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (BadLT N I C w).card)
  obtain ⟨p21, a1, b1, hab1, hn11, hn12, hn13, hv1a, hv1b⟩ := mf_mp hl1
  obtain ⟨p22, a2, b2, hab2, hn21, hn22, hn23, hv2a, hv2b⟩ := mf_mp hl2
  set S0 := Finset.univ.filter fun p => I p l1 ∧ I p l2
  set S1 := Finset.univ.filter fun p => I p a1 ∧ I p b1
  set S2 := Finset.univ.filter fun p => I p a2 ∧ I p b2
  have hsub : @Finset.filter (Fin N) (BadLT_ok N I C w) (fun _ => Classical.propDecidable _) Finset.univ ⊆
      S0 ∪ S1 ∪ S2 := by
    intro p hp
    have hok := mf_mp hp
    have h1 := hok l1 hl1 p21 a1 b1 hab1 hn11 hn12 hn13 hv1a hv1b
    have h2' := hok l2 hl2 p22 a2 b2 hab2 hn21 hn22 hn23 hv2a hv2b
    simp only [Finset.mem_union, S0, S1, S2, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hc0 : S0.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => by
    by_contra hne
    have hx' := mf_mp hx
    have hy' := mf_mp hy
    exact no_c4 huniq hne h12 hx'.1 hy'.1 hx'.2 hy'.2
  have hc1 : S1.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => by
    by_contra hne
    have hx' := mf_mp hx
    have hy' := mf_mp hy
    exact no_c4 huniq hne hab1 hx'.1 hy'.1 hx'.2 hy'.2
  have hc2 : S2.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => by
    by_contra hne
    have hx' := mf_mp hx
    have hy' := mf_mp hy
    exact no_c4 huniq hne hab2 hx'.1 hy'.1 hx'.2 hy'.2
  have hcu := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  omega

theorem card_badPT_ok_le_three {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {w : ℕ} (h2 : 2 ≤ (BadPT N I C w).card) :
    (@Finset.filter (Fin N) (BadPT_ok N I C w) (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 3 := by
  classical
  obtain ⟨p1, hp1, p2, hp2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (BadPT N I C w).card)
  obtain ⟨l21, a1, b1, hab1, hn11, hn12, hn13, hv1a, hv1b⟩ := mf_mp hp1
  obtain ⟨l22, a2, b2, hab2, hn21, hn22, hn23, hv2a, hv2b⟩ := mf_mp hp2
  set S0 := Finset.univ.filter fun l => I p1 l ∧ I p2 l
  set S1 := Finset.univ.filter fun l => I a1 l ∧ I b1 l
  set S2 := Finset.univ.filter fun l => I a2 l ∧ I b2 l
  have hsub : @Finset.filter (Fin N) (BadPT_ok N I C w) (fun _ => Classical.propDecidable _) Finset.univ ⊆
      S0 ∪ S1 ∪ S2 := by
    intro l hl
    have hok := mf_mp hl
    have h1 := hok p1 hp1 l21 a1 b1 hab1 hn11 hn12 hn13 hv1a hv1b
    have h2' := hok p2 hp2 l22 a2 b2 hab2 hn21 hn22 hn23 hv2a hv2b
    simp only [Finset.mem_union, S0, S1, S2, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hc0 : S0.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => by
    by_contra hne
    have hx' := mf_mp hx
    have hy' := mf_mp hy
    exact no_c4 huniq h12 hne hx'.1 hx'.2 hy'.1 hy'.2
  have hc1 : S1.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => by
    by_contra hne
    have hx' := mf_mp hx
    have hy' := mf_mp hy
    exact no_c4 huniq hab1 hne hx'.1 hx'.2 hy'.1 hy'.2
  have hc2 : S2.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => by
    by_contra hne
    have hx' := mf_mp hx
    have hy' := mf_mp hy
    exact no_c4 huniq hab2 hne hx'.1 hx'.2 hy'.1 hy'.2
  have hcu := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  omega

def starOrL (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (F : ℕ → Finset (Fin N))
    (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.or ∧ 2 ≤ (F (N + N + j)).card ∧
  (∀ l' ∈ F (N + N + j), I p l') ∧
  ∃ s : Fin 2, F ((gateAt C j).inputs.getD s.val 0) = {l}

def starOrP (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (F : ℕ → Finset (Fin N))
    (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.or ∧ 2 ≤ (F (N + N + j)).card ∧
  (∀ p' ∈ F (N + N + j), I p' l) ∧
  ∃ s : Fin 2, F ((gateAt C j).inputs.getD s.val 0) = {p}

def nearOrL (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.or ∧ 4 ≤ (LO N C (N + N + j)).card ∧
  ((LO N C (N + N + j)).filter fun l' => ¬ I p l').card ≤ 1 ∧
  ∃ s : Fin 2, l ∈ LO N C ((gateAt C j).inputs.getD s.val 0) ∧
    (LO N C ((gateAt C j).inputs.getD s.val 0)).card ≤ 3

def nearOrP (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.or ∧ 4 ≤ (PO N C (N + N + j)).card ∧
  ((PO N C (N + N + j)).filter fun p' => ¬ I p' l).card ≤ 1 ∧
  ∃ s : Fin 2, p ∈ PO N C ((gateAt C j).inputs.getD s.val 0) ∧
    (PO N C ((gateAt C j).inputs.getD s.val 0)).card ≤ 3

def twinOrL (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.or ∧ 2 ≤ (BadLT N I C (N + N + j)).card ∧
  BadLT_ok N I C (N + N + j) p ∧
  ∃ s : Fin 2, BadLT N I C ((gateAt C j).inputs.getD s.val 0) = {l}

def twinOrP (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.or ∧ 2 ≤ (BadPT N I C (N + N + j)).card ∧
  BadPT_ok N I C (N + N + j) l ∧
  ∃ s : Fin 2, BadPT N I C ((gateAt C j).inputs.getD s.val 0) = {p}

def orCov (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (j : ℕ) (p l : Fin N) : Prop :=
  starOrL N I C (Ls N C) j p l ∨
  starOrP N I C (Ps N C) j p l ∨
  starOrL N I C (LO N C) j p l ∨
  starOrP N I C (PO N C) j p l ∨
  nearOrL N I C j p l ∨
  nearOrP N I C j p l ∨
  starOrL N I C (BadL N I C) j p l ∨
  starOrP N I C (BadP N I C) j p l ∨
  starOrL N I C (BadL2 N I C) j p l ∨
  starOrP N I C (BadP2 N I C) j p l ∨
  twinOrL N I C j p l ∨
  twinOrP N I C j p l

def pairAnd (N : ℕ) (C : Circuit) (FP FL : ℕ → Finset (Fin N)) (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.and ∧
  ∃ s : Fin 2, FP ((gateAt C j).inputs.getD s.val 0) = {p} ∧
    FL ((gateAt C j).inputs.getD (1 - s.val) 0) = {l}

def pairAnd3L (N : ℕ) (C : Circuit) (FP FL : ℕ → Finset (Fin N)) (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.and ∧
  ∃ s : Fin 2, FP ((gateAt C j).inputs.getD s.val 0) = {p} ∧
    l ∈ FL ((gateAt C j).inputs.getD (1 - s.val) 0) ∧
    (FL ((gateAt C j).inputs.getD (1 - s.val) 0)).card ≤ 3

def pairAnd3P (N : ℕ) (C : Circuit) (FP FL : ℕ → Finset (Fin N)) (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.and ∧
  ∃ s : Fin 2, p ∈ FP ((gateAt C j).inputs.getD s.val 0) ∧
    (FP ((gateAt C j).inputs.getD s.val 0)).card ≤ 3 ∧
    FL ((gateAt C j).inputs.getD (1 - s.val) 0) = {l}

def gateBadL (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (FG FL : ℕ → Finset (Fin N))
    (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.and ∧ 2 ≤ (FG (N + N + j)).card ∧
  (∀ l' ∈ FG (N + N + j), I p l') ∧
  ∃ s : Fin 2, l ∈ FL ((gateAt C j).inputs.getD s.val 0) ∧
    (FL ((gateAt C j).inputs.getD s.val 0)).card ≤ 3

def gateBadP (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (FG FP : ℕ → Finset (Fin N))
    (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.and ∧ 2 ≤ (FG (N + N + j)).card ∧
  (∀ p' ∈ FG (N + N + j), I p' l) ∧
  ∃ s : Fin 2, p ∈ FP ((gateAt C j).inputs.getD s.val 0) ∧
    (FP ((gateAt C j).inputs.getD s.val 0)).card ≤ 3

def gateTwinL (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.and ∧ 2 ≤ (BadLT N I C (N + N + j)).card ∧
  BadLT_ok N I C (N + N + j) p ∧
  ∃ s : Fin 2, LO N C ((gateAt C j).inputs.getD s.val 0) = {l}

def gateTwinP (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (p l : Fin N) : Prop :=
  (gateAt C j).op = GateOp.and ∧ 2 ≤ (BadPT N I C (N + N + j)).card ∧
  BadPT_ok N I C (N + N + j) l ∧
  ∃ s : Fin 2, PO N C ((gateAt C j).inputs.getD s.val 0) = {p}

def andCov (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (p l : Fin N) : Prop :=
  pairAnd N C (Ps N C) (Ls N C) j p l ∨
  pairAnd3L N C (PO N C) (LO N C) j p l ∨
  pairAnd3P N C (PO N C) (LO N C) j p l ∨
  pairAnd N C (PO N C) (Ls N C) j p l ∨
  pairAnd N C (Ps N C) (LO N C) j p l ∨
  pairAnd N C (PO N C) (BadL N I C) j p l ∨
  pairAnd N C (BadP N I C) (LO N C) j p l ∨
  pairAnd N C (PO N C) (BadL2 N I C) j p l ∨
  pairAnd N C (BadP2 N I C) (LO N C) j p l ∨
  pairAnd3P N C (PO N C) (BadLT N I C) j p l ∨
  pairAnd3L N C (BadPT N I C) (LO N C) j p l ∨
  pairAnd N C (BadP2 N I C) (BadL2 N I C) j p l ∨
  gateBadL N I C (BadL N I C) (LO N C) j p l ∨
  gateBadP N I C (BadP N I C) (PO N C) j p l ∨
  gateBadL N I C (BadL N I C) (Ls N C) j p l ∨
  gateBadP N I C (BadP N I C) (Ps N C) j p l ∨
  gateBadL N I C (BadL2 N I C) (LO N C) j p l ∨
  gateBadP N I C (BadP2 N I C) (PO N C) j p l ∨
  gateTwinL N I C j p l ∨
  gateTwinP N I C j p l

def gateCov (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (j : ℕ) (p l : Fin N) : Prop :=
  orCov N I C j p l ∨ andCov N I C j p l

theorem fib_starOrL {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (F : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => starOrL N I C F j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 2 := by
  classical
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => starOrL N I C F j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (F (N + N + j)).card ∧ (∀ l' ∈ F (N + N + j), I pl.1 l') ∧
        F ((gateAt C j).inputs.getD 0 0) = {pl.2}) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (F (N + N + j)).card ∧ (∀ l' ∈ F (N + N + j), I pl.1 l') ∧
        F ((gateAt C j).inputs.getD 1 0) = {pl.2}) := by
    intro pl hpl
    obtain ⟨_, h2, hI, ⟨s, hs⟩, hF⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h2, hI, hF⟩
    · exact Or.inr ⟨Finset.mem_univ _, h2, hI, hF⟩
  have hle1 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (F (N + N + j)).card ∧ (∀ l' ∈ F (N + N + j), I pl.1 l') ∧
      F ((gateAt C j).inputs.getD s 0) = {pl.2}).card ≤ 1 := fun s =>
    Finset.card_le_one.mpr fun a ha b hb => by
      obtain ⟨h2, hIa, hFa⟩ := mf_mp ha
      obtain ⟨_, hIb, hFb⟩ := mf_mp hb
      exact Prod.ext (unique_p_of_two_l huniq h2 hIa hIb)
        (Finset.singleton_injective (hFa.symm.trans hFb))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle1 0; have := hle1 1; omega))

theorem fib_starOrP {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (F : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => starOrP N I C F j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 2 := by
  classical
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => starOrP N I C F j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (F (N + N + j)).card ∧ (∀ p' ∈ F (N + N + j), I p' pl.2) ∧
        F ((gateAt C j).inputs.getD 0 0) = {pl.1}) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (F (N + N + j)).card ∧ (∀ p' ∈ F (N + N + j), I p' pl.2) ∧
        F ((gateAt C j).inputs.getD 1 0) = {pl.1}) := by
    intro pl hpl
    obtain ⟨_, h2, hI, ⟨s, hs⟩, hF⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h2, hI, hF⟩
    · exact Or.inr ⟨Finset.mem_univ _, h2, hI, hF⟩
  have hle1 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (F (N + N + j)).card ∧ (∀ p' ∈ F (N + N + j), I p' pl.2) ∧
      F ((gateAt C j).inputs.getD s 0) = {pl.1}).card ≤ 1 := fun s =>
    Finset.card_le_one.mpr fun a ha b hb => by
      obtain ⟨h2, hIa, hFa⟩ := mf_mp ha
      obtain ⟨_, hIb, hFb⟩ := mf_mp hb
      exact Prod.ext (Finset.singleton_injective (hFa.symm.trans hFb))
        (unique_l_of_two_p huniq h2 hIa hIb)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle1 0; have := hle1 1; omega))

theorem fib_nearOrL {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => nearOrL N I C j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 6 := by
  classical
  have hle3 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      4 ≤ (LO N C (N + N + j)).card ∧
      ((LO N C (N + N + j)).filter fun l' => ¬ I pl.1 l').card ≤ 1 ∧
      pl.2 ∈ LO N C ((gateAt C j).inputs.getD s 0) ∧
      (LO N C ((gateAt C j).inputs.getD s 0)).card ≤ 3).card ≤ 3 := by
    intro s
    set A := Finset.univ.filter fun pl : Fin N × Fin N =>
      4 ≤ (LO N C (N + N + j)).card ∧
      ((LO N C (N + N + j)).filter fun l' => ¬ I pl.1 l').card ≤ 1 ∧
      pl.2 ∈ LO N C ((gateAt C j).inputs.getD s 0) ∧
      (LO N C ((gateAt C j).inputs.getD s 0)).card ≤ 3
    by_cases hne : A.Nonempty
    · obtain ⟨⟨p0, l0⟩, h0⟩ := hne
      obtain ⟨h4, hp0, _, hc3⟩ := mf_mp h0
      have hsub : A ⊆ ({p0} : Finset (Fin N)) ×ˢ LO N C ((gateAt C j).inputs.getD s 0) := by
        intro pl hpl
        obtain ⟨_, hp, hmem, _⟩ := mf_mp hpl
        rw [Finset.mem_product, Finset.mem_singleton]
        exact ⟨unique_p_of_near_l huniq h4 hp hp0, hmem⟩
      calc A.card ≤ (({p0} : Finset (Fin N)) ×ˢ LO N C ((gateAt C j).inputs.getD s 0)).card :=
            Finset.card_le_card hsub
        _ = (LO N C ((gateAt C j).inputs.getD s 0)).card := by simp
        _ ≤ 3 := hc3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => nearOrL N I C j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        4 ≤ (LO N C (N + N + j)).card ∧
        ((LO N C (N + N + j)).filter fun l' => ¬ I pl.1 l').card ≤ 1 ∧
        pl.2 ∈ LO N C ((gateAt C j).inputs.getD 0 0) ∧
        (LO N C ((gateAt C j).inputs.getD 0 0)).card ≤ 3) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        4 ≤ (LO N C (N + N + j)).card ∧
        ((LO N C (N + N + j)).filter fun l' => ¬ I pl.1 l').card ≤ 1 ∧
        pl.2 ∈ LO N C ((gateAt C j).inputs.getD 1 0) ∧
        (LO N C ((gateAt C j).inputs.getD 1 0)).card ≤ 3) := by
    intro pl hpl
    obtain ⟨_, h4, hp, ⟨s, hs⟩, hm, hc3⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h4, hp, hm, hc3⟩
    · exact Or.inr ⟨Finset.mem_univ _, h4, hp, hm, hc3⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle3 0; have := hle3 1; omega))

theorem fib_nearOrP {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => nearOrP N I C j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 6 := by
  classical
  have hle3 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      4 ≤ (PO N C (N + N + j)).card ∧
      ((PO N C (N + N + j)).filter fun p' => ¬ I p' pl.2).card ≤ 1 ∧
      pl.1 ∈ PO N C ((gateAt C j).inputs.getD s 0) ∧
      (PO N C ((gateAt C j).inputs.getD s 0)).card ≤ 3).card ≤ 3 := by
    intro s
    set A := Finset.univ.filter fun pl : Fin N × Fin N =>
      4 ≤ (PO N C (N + N + j)).card ∧
      ((PO N C (N + N + j)).filter fun p' => ¬ I p' pl.2).card ≤ 1 ∧
      pl.1 ∈ PO N C ((gateAt C j).inputs.getD s 0) ∧
      (PO N C ((gateAt C j).inputs.getD s 0)).card ≤ 3
    by_cases hne : A.Nonempty
    · obtain ⟨⟨p0, l0⟩, h0⟩ := hne
      obtain ⟨h4, hl0, _, hc3⟩ := mf_mp h0
      have hsub : A ⊆ PO N C ((gateAt C j).inputs.getD s 0) ×ˢ ({l0} : Finset (Fin N)) := by
        intro pl hpl
        obtain ⟨_, hl, hmem, _⟩ := mf_mp hpl
        rw [Finset.mem_product, Finset.mem_singleton]
        exact ⟨hmem, unique_l_of_near_p huniq h4 hl hl0⟩
      calc A.card ≤ (PO N C ((gateAt C j).inputs.getD s 0) ×ˢ ({l0} : Finset (Fin N))).card :=
            Finset.card_le_card hsub
        _ = (PO N C ((gateAt C j).inputs.getD s 0)).card := by simp
        _ ≤ 3 := hc3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => nearOrP N I C j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        4 ≤ (PO N C (N + N + j)).card ∧
        ((PO N C (N + N + j)).filter fun p' => ¬ I p' pl.2).card ≤ 1 ∧
        pl.1 ∈ PO N C ((gateAt C j).inputs.getD 0 0) ∧
        (PO N C ((gateAt C j).inputs.getD 0 0)).card ≤ 3) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        4 ≤ (PO N C (N + N + j)).card ∧
        ((PO N C (N + N + j)).filter fun p' => ¬ I p' pl.2).card ≤ 1 ∧
        pl.1 ∈ PO N C ((gateAt C j).inputs.getD 1 0) ∧
        (PO N C ((gateAt C j).inputs.getD 1 0)).card ≤ 3) := by
    intro pl hpl
    obtain ⟨_, h4, hl, ⟨s, hs⟩, hm, hc3⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h4, hl, hm, hc3⟩
    · exact Or.inr ⟨Finset.mem_univ _, h4, hl, hm, hc3⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle3 0; have := hle3 1; omega))

theorem fib_twin_L {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (F : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl =>
      2 ≤ (BadLT N I C (N + N + j)).card ∧ BadLT_ok N I C (N + N + j) pl.1 ∧
      ∃ s : Fin 2, F ((gateAt C j).inputs.getD s.val 0) = {pl.2})
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 6 := by
  classical
  have hle3 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (BadLT N I C (N + N + j)).card ∧ BadLT_ok N I C (N + N + j) pl.1 ∧
      F ((gateAt C j).inputs.getD s 0) = {pl.2}).card ≤ 3 := by
    intro s
    set A := Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (BadLT N I C (N + N + j)).card ∧ BadLT_ok N I C (N + N + j) pl.1 ∧
      F ((gateAt C j).inputs.getD s 0) = {pl.2}
    by_cases hne : A.Nonempty
    · obtain ⟨⟨p0, l0⟩, h0⟩ := hne
      obtain ⟨h2, _, hF0⟩ := mf_mp h0
      have hsub : A ⊆
          (@Finset.filter (Fin N) (BadLT_ok N I C (N + N + j)) (fun _ => Classical.propDecidable _) Finset.univ) ×ˢ
            ({l0} : Finset (Fin N)) := by
        intro pl hpl
        obtain ⟨_, hok, hF⟩ := mf_mp hpl
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_singleton]
        exact ⟨⟨Finset.mem_univ _, hok⟩, Finset.singleton_injective (hF.symm.trans hF0)⟩
      calc A.card ≤ ((@Finset.filter (Fin N) (BadLT_ok N I C (N + N + j)) (fun _ => Classical.propDecidable _) Finset.univ) ×ˢ
              ({l0} : Finset (Fin N))).card := Finset.card_le_card hsub
        _ = (@Finset.filter (Fin N) (BadLT_ok N I C (N + N + j)) (fun _ => Classical.propDecidable _) Finset.univ).card := by simp
        _ ≤ 3 := card_badLT_ok_le_three huniq h2
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl =>
      2 ≤ (BadLT N I C (N + N + j)).card ∧ BadLT_ok N I C (N + N + j) pl.1 ∧
      ∃ s : Fin 2, F ((gateAt C j).inputs.getD s.val 0) = {pl.2})
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (BadLT N I C (N + N + j)).card ∧ BadLT_ok N I C (N + N + j) pl.1 ∧
        F ((gateAt C j).inputs.getD 0 0) = {pl.2}) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (BadLT N I C (N + N + j)).card ∧ BadLT_ok N I C (N + N + j) pl.1 ∧
        F ((gateAt C j).inputs.getD 1 0) = {pl.2}) := by
    intro pl hpl
    obtain ⟨h2, hok, ⟨s, hs⟩, hF⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h2, hok, hF⟩
    · exact Or.inr ⟨Finset.mem_univ _, h2, hok, hF⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle3 0; have := hle3 1; omega))

theorem fib_twin_P {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (F : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl =>
      2 ≤ (BadPT N I C (N + N + j)).card ∧ BadPT_ok N I C (N + N + j) pl.2 ∧
      ∃ s : Fin 2, F ((gateAt C j).inputs.getD s.val 0) = {pl.1})
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 6 := by
  classical
  have hle3 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (BadPT N I C (N + N + j)).card ∧ BadPT_ok N I C (N + N + j) pl.2 ∧
      F ((gateAt C j).inputs.getD s 0) = {pl.1}).card ≤ 3 := by
    intro s
    set A := Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (BadPT N I C (N + N + j)).card ∧ BadPT_ok N I C (N + N + j) pl.2 ∧
      F ((gateAt C j).inputs.getD s 0) = {pl.1}
    by_cases hne : A.Nonempty
    · obtain ⟨⟨p0, l0⟩, h0⟩ := hne
      obtain ⟨h2, _, hF0⟩ := mf_mp h0
      have hsub : A ⊆ ({p0} : Finset (Fin N)) ×ˢ
          (@Finset.filter (Fin N) (BadPT_ok N I C (N + N + j)) (fun _ => Classical.propDecidable _) Finset.univ) := by
        intro pl hpl
        obtain ⟨_, hok, hF⟩ := mf_mp hpl
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_singleton]
        exact ⟨Finset.singleton_injective (hF.symm.trans hF0), Finset.mem_univ _, hok⟩
      calc A.card ≤ (({p0} : Finset (Fin N)) ×ˢ
              (@Finset.filter (Fin N) (BadPT_ok N I C (N + N + j)) (fun _ => Classical.propDecidable _) Finset.univ)).card :=
            Finset.card_le_card hsub
        _ = (@Finset.filter (Fin N) (BadPT_ok N I C (N + N + j)) (fun _ => Classical.propDecidable _) Finset.univ).card := by simp
        _ ≤ 3 := card_badPT_ok_le_three huniq h2
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl =>
      2 ≤ (BadPT N I C (N + N + j)).card ∧ BadPT_ok N I C (N + N + j) pl.2 ∧
      ∃ s : Fin 2, F ((gateAt C j).inputs.getD s.val 0) = {pl.1})
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (BadPT N I C (N + N + j)).card ∧ BadPT_ok N I C (N + N + j) pl.2 ∧
        F ((gateAt C j).inputs.getD 0 0) = {pl.1}) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (BadPT N I C (N + N + j)).card ∧ BadPT_ok N I C (N + N + j) pl.2 ∧
        F ((gateAt C j).inputs.getD 1 0) = {pl.1}) := by
    intro pl hpl
    obtain ⟨h2, hok, ⟨s, hs⟩, hF⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h2, hok, hF⟩
    · exact Or.inr ⟨Finset.mem_univ _, h2, hok, hF⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle3 0; have := hle3 1; omega))

theorem fib_pairAnd {N : ℕ} {C : Circuit} (FP FL : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => pairAnd N C FP FL j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 2 := by
  classical
  have hle1 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      FP ((gateAt C j).inputs.getD s 0) = {pl.1} ∧
      FL ((gateAt C j).inputs.getD (1 - s) 0) = {pl.2}).card ≤ 1 := fun s =>
    Finset.card_le_one.mpr fun a ha b hb => by
      obtain ⟨h1a, h2a⟩ := mf_mp ha
      obtain ⟨h1b, h2b⟩ := mf_mp hb
      exact Prod.ext (Finset.singleton_injective (h1a.symm.trans h1b))
        (Finset.singleton_injective (h2a.symm.trans h2b))
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => pairAnd N C FP FL j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        FP ((gateAt C j).inputs.getD 0 0) = {pl.1} ∧
        FL ((gateAt C j).inputs.getD (1 - 0) 0) = {pl.2}) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        FP ((gateAt C j).inputs.getD 1 0) = {pl.1} ∧
        FL ((gateAt C j).inputs.getD (1 - 1) 0) = {pl.2}) := by
    intro pl hpl
    obtain ⟨_, ⟨s, hs⟩, h1, h2⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h1, h2⟩
    · exact Or.inr ⟨Finset.mem_univ _, h1, h2⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle1 0; have := hle1 1; omega))

theorem fib_pairAnd3L {N : ℕ} {C : Circuit} (FP FL : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => pairAnd3L N C FP FL j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 6 := by
  classical
  have hle3 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      FP ((gateAt C j).inputs.getD s 0) = {pl.1} ∧
      pl.2 ∈ FL ((gateAt C j).inputs.getD (1 - s) 0) ∧
      (FL ((gateAt C j).inputs.getD (1 - s) 0)).card ≤ 3).card ≤ 3 := by
    intro s
    set A := Finset.univ.filter fun pl : Fin N × Fin N =>
      FP ((gateAt C j).inputs.getD s 0) = {pl.1} ∧
      pl.2 ∈ FL ((gateAt C j).inputs.getD (1 - s) 0) ∧
      (FL ((gateAt C j).inputs.getD (1 - s) 0)).card ≤ 3
    by_cases hne : A.Nonempty
    · obtain ⟨⟨p0, l0⟩, h0⟩ := hne
      obtain ⟨hp0, _, hc3⟩ := mf_mp h0
      have hsub : A ⊆ ({p0} : Finset (Fin N)) ×ˢ FL ((gateAt C j).inputs.getD (1 - s) 0) := by
        intro pl hpl
        obtain ⟨hp, hm, _⟩ := mf_mp hpl
        rw [Finset.mem_product, Finset.mem_singleton]
        exact ⟨Finset.singleton_injective (hp.symm.trans hp0), hm⟩
      calc A.card ≤ (({p0} : Finset (Fin N)) ×ˢ FL ((gateAt C j).inputs.getD (1 - s) 0)).card :=
            Finset.card_le_card hsub
        _ = (FL ((gateAt C j).inputs.getD (1 - s) 0)).card := by simp
        _ ≤ 3 := hc3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => pairAnd3L N C FP FL j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        FP ((gateAt C j).inputs.getD 0 0) = {pl.1} ∧
        pl.2 ∈ FL ((gateAt C j).inputs.getD (1 - 0) 0) ∧
        (FL ((gateAt C j).inputs.getD (1 - 0) 0)).card ≤ 3) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        FP ((gateAt C j).inputs.getD 1 0) = {pl.1} ∧
        pl.2 ∈ FL ((gateAt C j).inputs.getD (1 - 1) 0) ∧
        (FL ((gateAt C j).inputs.getD (1 - 1) 0)).card ≤ 3) := by
    intro pl hpl
    obtain ⟨_, ⟨s, hs⟩, h1, h2, h3⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h1, h2, h3⟩
    · exact Or.inr ⟨Finset.mem_univ _, h1, h2, h3⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle3 0; have := hle3 1; omega))

theorem fib_pairAnd3P {N : ℕ} {C : Circuit} (FP FL : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => pairAnd3P N C FP FL j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 6 := by
  classical
  have hle3 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      pl.1 ∈ FP ((gateAt C j).inputs.getD s 0) ∧
      (FP ((gateAt C j).inputs.getD s 0)).card ≤ 3 ∧
      FL ((gateAt C j).inputs.getD (1 - s) 0) = {pl.2}).card ≤ 3 := by
    intro s
    set A := Finset.univ.filter fun pl : Fin N × Fin N =>
      pl.1 ∈ FP ((gateAt C j).inputs.getD s 0) ∧
      (FP ((gateAt C j).inputs.getD s 0)).card ≤ 3 ∧
      FL ((gateAt C j).inputs.getD (1 - s) 0) = {pl.2}
    by_cases hne : A.Nonempty
    · obtain ⟨⟨p0, l0⟩, h0⟩ := hne
      obtain ⟨_, hc3, hl0⟩ := mf_mp h0
      have hsub : A ⊆ FP ((gateAt C j).inputs.getD s 0) ×ˢ ({l0} : Finset (Fin N)) := by
        intro pl hpl
        obtain ⟨hm, _, hl⟩ := mf_mp hpl
        rw [Finset.mem_product, Finset.mem_singleton]
        exact ⟨hm, Finset.singleton_injective (hl.symm.trans hl0)⟩
      calc A.card ≤ (FP ((gateAt C j).inputs.getD s 0) ×ˢ ({l0} : Finset (Fin N))).card :=
            Finset.card_le_card hsub
        _ = (FP ((gateAt C j).inputs.getD s 0)).card := by simp
        _ ≤ 3 := hc3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => pairAnd3P N C FP FL j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        pl.1 ∈ FP ((gateAt C j).inputs.getD 0 0) ∧
        (FP ((gateAt C j).inputs.getD 0 0)).card ≤ 3 ∧
        FL ((gateAt C j).inputs.getD (1 - 0) 0) = {pl.2}) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        pl.1 ∈ FP ((gateAt C j).inputs.getD 1 0) ∧
        (FP ((gateAt C j).inputs.getD 1 0)).card ≤ 3 ∧
        FL ((gateAt C j).inputs.getD (1 - 1) 0) = {pl.2}) := by
    intro pl hpl
    obtain ⟨_, ⟨s, hs⟩, h1, h2, h3⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h1, h2, h3⟩
    · exact Or.inr ⟨Finset.mem_univ _, h1, h2, h3⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle3 0; have := hle3 1; omega))

theorem fib_gateBadL {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (FG FL : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => gateBadL N I C FG FL j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 6 := by
  classical
  have hle3 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (FG (N + N + j)).card ∧ (∀ l' ∈ FG (N + N + j), I pl.1 l') ∧
      pl.2 ∈ FL ((gateAt C j).inputs.getD s 0) ∧
      (FL ((gateAt C j).inputs.getD s 0)).card ≤ 3).card ≤ 3 := by
    intro s
    set A := Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (FG (N + N + j)).card ∧ (∀ l' ∈ FG (N + N + j), I pl.1 l') ∧
      pl.2 ∈ FL ((gateAt C j).inputs.getD s 0) ∧
      (FL ((gateAt C j).inputs.getD s 0)).card ≤ 3
    by_cases hne : A.Nonempty
    · obtain ⟨⟨p0, l0⟩, h0⟩ := hne
      obtain ⟨h2, hp0, _, hc3⟩ := mf_mp h0
      have hsub : A ⊆ ({p0} : Finset (Fin N)) ×ˢ FL ((gateAt C j).inputs.getD s 0) := by
        intro pl hpl
        obtain ⟨_, hp, hm, _⟩ := mf_mp hpl
        rw [Finset.mem_product, Finset.mem_singleton]
        exact ⟨unique_p_of_two_l huniq h2 hp hp0, hm⟩
      calc A.card ≤ (({p0} : Finset (Fin N)) ×ˢ FL ((gateAt C j).inputs.getD s 0)).card :=
            Finset.card_le_card hsub
        _ = (FL ((gateAt C j).inputs.getD s 0)).card := by simp
        _ ≤ 3 := hc3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => gateBadL N I C FG FL j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (FG (N + N + j)).card ∧ (∀ l' ∈ FG (N + N + j), I pl.1 l') ∧
        pl.2 ∈ FL ((gateAt C j).inputs.getD 0 0) ∧
        (FL ((gateAt C j).inputs.getD 0 0)).card ≤ 3) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (FG (N + N + j)).card ∧ (∀ l' ∈ FG (N + N + j), I pl.1 l') ∧
        pl.2 ∈ FL ((gateAt C j).inputs.getD 1 0) ∧
        (FL ((gateAt C j).inputs.getD 1 0)).card ≤ 3) := by
    intro pl hpl
    obtain ⟨_, h2, hI, ⟨s, hs⟩, hm, hc3⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h2, hI, hm, hc3⟩
    · exact Or.inr ⟨Finset.mem_univ _, h2, hI, hm, hc3⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle3 0; have := hle3 1; omega))

theorem fib_gateBadP {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (FG FP : ℕ → Finset (Fin N)) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => gateBadP N I C FG FP j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 6 := by
  classical
  have hle3 : ∀ s : ℕ, (Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (FG (N + N + j)).card ∧ (∀ p' ∈ FG (N + N + j), I p' pl.2) ∧
      pl.1 ∈ FP ((gateAt C j).inputs.getD s 0) ∧
      (FP ((gateAt C j).inputs.getD s 0)).card ≤ 3).card ≤ 3 := by
    intro s
    set A := Finset.univ.filter fun pl : Fin N × Fin N =>
      2 ≤ (FG (N + N + j)).card ∧ (∀ p' ∈ FG (N + N + j), I p' pl.2) ∧
      pl.1 ∈ FP ((gateAt C j).inputs.getD s 0) ∧
      (FP ((gateAt C j).inputs.getD s 0)).card ≤ 3
    by_cases hne : A.Nonempty
    · obtain ⟨⟨p0, l0⟩, h0⟩ := hne
      obtain ⟨h2, hl0, _, hc3⟩ := mf_mp h0
      have hsub : A ⊆ FP ((gateAt C j).inputs.getD s 0) ×ˢ ({l0} : Finset (Fin N)) := by
        intro pl hpl
        obtain ⟨_, hl, hm, _⟩ := mf_mp hpl
        rw [Finset.mem_product, Finset.mem_singleton]
        exact ⟨hm, unique_l_of_two_p huniq h2 hl hl0⟩
      calc A.card ≤ (FP ((gateAt C j).inputs.getD s 0) ×ˢ ({l0} : Finset (Fin N))).card :=
            Finset.card_le_card hsub
        _ = (FP ((gateAt C j).inputs.getD s 0)).card := by simp
        _ ≤ 3 := hc3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hsub : @Finset.filter (Fin N × Fin N) (fun pl => gateBadP N I C FG FP j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ ⊆
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (FG (N + N + j)).card ∧ (∀ p' ∈ FG (N + N + j), I p' pl.2) ∧
        pl.1 ∈ FP ((gateAt C j).inputs.getD 0 0) ∧
        (FP ((gateAt C j).inputs.getD 0 0)).card ≤ 3) ∪
      (Finset.univ.filter fun pl : Fin N × Fin N =>
        2 ≤ (FG (N + N + j)).card ∧ (∀ p' ∈ FG (N + N + j), I p' pl.2) ∧
        pl.1 ∈ FP ((gateAt C j).inputs.getD 1 0) ∧
        (FP ((gateAt C j).inputs.getD 1 0)).card ≤ 3) := by
    intro pl hpl
    obtain ⟨_, h2, hI, ⟨s, hs⟩, hm, hc3⟩ := mf_mp hpl
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · exact Or.inl ⟨Finset.mem_univ _, h2, hI, hm, hc3⟩
    · exact Or.inr ⟨Finset.mem_univ _, h2, hI, hm, hc3⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have := hle3 0; have := hle3 1; omega))

theorem fib_gateCov {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (j : ℕ) :
    (@Finset.filter (Fin N × Fin N) (fun pl => gateCov N I C j pl.1 pl.2)
      (fun _ => Classical.propDecidable _) Finset.univ).card ≤ 112 := by
  classical
  by_cases hor : (gateAt C j).op = GateOp.or
  · have hsub : @Finset.filter (Fin N × Fin N) (fun pl => gateCov N I C j pl.1 pl.2)
        (fun _ => Classical.propDecidable _) Finset.univ ⊆
        Finset.univ.filter (fun pl : Fin N × Fin N => orCov N I C j pl.1 pl.2) := by
      intro pl hpl
      rw [Finset.mem_filter] at hpl ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hpl.2 with h | h
      · exact h
      · exfalso
        have hand : (gateAt C j).op = GateOp.and := by
          rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
            exact h.1
        rw [hor] at hand; cases hand
    have h1 : (Finset.univ.filter fun pl : Fin N × Fin N => starOrL N I C (Ls N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_starOrL huniq (Ls N C) j
    have h2 : (Finset.univ.filter fun pl : Fin N × Fin N => starOrP N I C (Ps N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_starOrP huniq (Ps N C) j
    have h3 : (Finset.univ.filter fun pl : Fin N × Fin N => starOrL N I C (LO N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_starOrL huniq (LO N C) j
    have h4 : (Finset.univ.filter fun pl : Fin N × Fin N => starOrP N I C (PO N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_starOrP huniq (PO N C) j
    have h5 : (Finset.univ.filter fun pl : Fin N × Fin N => nearOrL N I C j pl.1 pl.2).card ≤ 6 := by
      convert fib_nearOrL huniq j
    have h6 : (Finset.univ.filter fun pl : Fin N × Fin N => nearOrP N I C j pl.1 pl.2).card ≤ 6 := by
      convert fib_nearOrP huniq j
    have h7 : (Finset.univ.filter fun pl : Fin N × Fin N => starOrL N I C (BadL N I C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_starOrL huniq (BadL N I C) j
    have h8 : (Finset.univ.filter fun pl : Fin N × Fin N => starOrP N I C (BadP N I C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_starOrP huniq (BadP N I C) j
    have h9 : (Finset.univ.filter fun pl : Fin N × Fin N => starOrL N I C (BadL2 N I C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_starOrL huniq (BadL2 N I C) j
    have h10 : (Finset.univ.filter fun pl : Fin N × Fin N => starOrP N I C (BadP2 N I C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_starOrP huniq (BadP2 N I C) j
    have h11 : (Finset.univ.filter fun pl : Fin N × Fin N => twinOrL N I C j pl.1 pl.2).card ≤ 6 := by
      refine (Finset.card_le_card fun pl hpl => ?_).trans (fib_twin_L (C := C) huniq (BadLT N I C) j)
      exact mfu_mpr (mf_mp hpl).2
    have h12 : (Finset.univ.filter fun pl : Fin N × Fin N => twinOrP N I C j pl.1 pl.2).card ≤ 6 := by
      refine (Finset.card_le_card fun pl hpl => ?_).trans (fib_twin_P (C := C) huniq (BadPT N I C) j)
      exact mfu_mpr (mf_mp hpl).2
    have or_add : ∀ {p q : Fin N × Fin N → Prop} {dp : DecidablePred p} {dq : DecidablePred q} {a b : ℕ},
        (@Finset.filter _ p dp Finset.univ).card ≤ a →
        (@Finset.filter _ q dq Finset.univ).card ≤ b →
        (Finset.univ.filter fun x => p x ∨ q x).card ≤ a + b := by
      intro p q dp dq a b hp hq
      have hs : (Finset.univ.filter fun x => p x ∨ q x) ⊆
          @Finset.filter _ p dp Finset.univ ∪ @Finset.filter _ q dq Finset.univ := by
        intro x hx
        rcases (Finset.mem_filter.mp hx).2 with h | h
        · exact Finset.mem_union_left _ (mfu_mpr h)
        · exact Finset.mem_union_right _ (mfu_mpr h)
      exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hp hq))
    have htot := or_add h1 (or_add h2 (or_add h3 (or_add h4 (or_add h5 (or_add h6
      (or_add h7 (or_add h8 (or_add h9 (or_add h10 (or_add h11 h12))))))))))
    have hle : (@Finset.filter (Fin N × Fin N) (fun pl => gateCov N I C j pl.1 pl.2)
        (fun _ => Classical.propDecidable _) Finset.univ).card ≤
        (Finset.univ.filter fun pl : Fin N × Fin N =>
          starOrL N I C (Ls N C) j pl.1 pl.2 ∨ starOrP N I C (Ps N C) j pl.1 pl.2 ∨
          starOrL N I C (LO N C) j pl.1 pl.2 ∨ starOrP N I C (PO N C) j pl.1 pl.2 ∨
          nearOrL N I C j pl.1 pl.2 ∨ nearOrP N I C j pl.1 pl.2 ∨
          starOrL N I C (BadL N I C) j pl.1 pl.2 ∨ starOrP N I C (BadP N I C) j pl.1 pl.2 ∨
          starOrL N I C (BadL2 N I C) j pl.1 pl.2 ∨ starOrP N I C (BadP2 N I C) j pl.1 pl.2 ∨
          twinOrL N I C j pl.1 pl.2 ∨ twinOrP N I C j pl.1 pl.2).card :=
      Finset.card_le_card fun pl hpl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hsub hpl)).2⟩
    omega
  · have hsub : @Finset.filter (Fin N × Fin N) (fun pl => gateCov N I C j pl.1 pl.2)
        (fun _ => Classical.propDecidable _) Finset.univ ⊆
        Finset.univ.filter (fun pl : Fin N × Fin N => andCov N I C j pl.1 pl.2) := by
      intro pl hpl
      rw [Finset.mem_filter] at hpl ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hpl.2 with h | h
      · exfalso
        have ho : (gateAt C j).op = GateOp.or := by
          rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;> exact h.1
        exact hor ho
      · exact h
    have h1 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd N C (Ps N C) (Ls N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_pairAnd (C := C) (Ps N C) (Ls N C) j
    have h2 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd3L N C (PO N C) (LO N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_pairAnd3L (C := C) (PO N C) (LO N C) j
    have h3 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd3P N C (PO N C) (LO N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_pairAnd3P (C := C) (PO N C) (LO N C) j
    have h4 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd N C (PO N C) (Ls N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_pairAnd (C := C) (PO N C) (Ls N C) j
    have h5 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd N C (Ps N C) (LO N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_pairAnd (C := C) (Ps N C) (LO N C) j
    have h6 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd N C (PO N C) (BadL N I C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_pairAnd (C := C) (PO N C) (BadL N I C) j
    have h7 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd N C (BadP N I C) (LO N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_pairAnd (C := C) (BadP N I C) (LO N C) j
    have h8 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd N C (PO N C) (BadL2 N I C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_pairAnd (C := C) (PO N C) (BadL2 N I C) j
    have h9 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd N C (BadP2 N I C) (LO N C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_pairAnd (C := C) (BadP2 N I C) (LO N C) j
    have h10 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd3P N C (PO N C) (BadLT N I C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_pairAnd3P (C := C) (PO N C) (BadLT N I C) j
    have h11 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd3L N C (BadPT N I C) (LO N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_pairAnd3L (C := C) (BadPT N I C) (LO N C) j
    have h12 : (Finset.univ.filter fun pl : Fin N × Fin N => pairAnd N C (BadP2 N I C) (BadL2 N I C) j pl.1 pl.2).card ≤ 2 := by
      convert fib_pairAnd (C := C) (BadP2 N I C) (BadL2 N I C) j
    have h13 : (Finset.univ.filter fun pl : Fin N × Fin N => gateBadL N I C (BadL N I C) (LO N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_gateBadL huniq (C := C) (BadL N I C) (LO N C) j
    have h14 : (Finset.univ.filter fun pl : Fin N × Fin N => gateBadP N I C (BadP N I C) (PO N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_gateBadP huniq (C := C) (BadP N I C) (PO N C) j
    have h15 : (Finset.univ.filter fun pl : Fin N × Fin N => gateBadL N I C (BadL N I C) (Ls N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_gateBadL huniq (C := C) (BadL N I C) (Ls N C) j
    have h16 : (Finset.univ.filter fun pl : Fin N × Fin N => gateBadP N I C (BadP N I C) (Ps N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_gateBadP huniq (C := C) (BadP N I C) (Ps N C) j
    have h17 : (Finset.univ.filter fun pl : Fin N × Fin N => gateBadL N I C (BadL2 N I C) (LO N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_gateBadL huniq (C := C) (BadL2 N I C) (LO N C) j
    have h18 : (Finset.univ.filter fun pl : Fin N × Fin N => gateBadP N I C (BadP2 N I C) (PO N C) j pl.1 pl.2).card ≤ 6 := by
      convert fib_gateBadP huniq (C := C) (BadP2 N I C) (PO N C) j
    have h19 : (Finset.univ.filter fun pl : Fin N × Fin N => gateTwinL N I C j pl.1 pl.2).card ≤ 6 := by
      refine (Finset.card_le_card fun pl hpl => ?_).trans (fib_twin_L (C := C) huniq (LO N C) j)
      exact mfu_mpr (mf_mp hpl).2
    have h20 : (Finset.univ.filter fun pl : Fin N × Fin N => gateTwinP N I C j pl.1 pl.2).card ≤ 6 := by
      refine (Finset.card_le_card fun pl hpl => ?_).trans (fib_twin_P (C := C) huniq (PO N C) j)
      exact mfu_mpr (mf_mp hpl).2
    have or_add : ∀ {p q : Fin N × Fin N → Prop} {dp : DecidablePred p} {dq : DecidablePred q} {a b : ℕ},
        (@Finset.filter _ p dp Finset.univ).card ≤ a →
        (@Finset.filter _ q dq Finset.univ).card ≤ b →
        (Finset.univ.filter fun x => p x ∨ q x).card ≤ a + b := by
      intro p q dp dq a b hp hq
      have hs : (Finset.univ.filter fun x => p x ∨ q x) ⊆
          @Finset.filter _ p dp Finset.univ ∪ @Finset.filter _ q dq Finset.univ := by
        intro x hx
        rcases (Finset.mem_filter.mp hx).2 with h | h
        · exact Finset.mem_union_left _ (mfu_mpr h)
        · exact Finset.mem_union_right _ (mfu_mpr h)
      exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hp hq))
    have htot := or_add h1 (or_add h2 (or_add h3 (or_add h4 (or_add h5 (or_add h6
      (or_add h7 (or_add h8 (or_add h9 (or_add h10 (or_add h11 (or_add h12
      (or_add h13 (or_add h14 (or_add h15 (or_add h16 (or_add h17 (or_add h18
      (or_add h19 h20))))))))))))))))))
    have hle : (@Finset.filter (Fin N × Fin N) (fun pl => gateCov N I C j pl.1 pl.2)
        (fun _ => Classical.propDecidable _) Finset.univ).card ≤
        (Finset.univ.filter fun pl : Fin N × Fin N =>
          pairAnd N C (Ps N C) (Ls N C) j pl.1 pl.2 ∨
          pairAnd3L N C (PO N C) (LO N C) j pl.1 pl.2 ∨
          pairAnd3P N C (PO N C) (LO N C) j pl.1 pl.2 ∨
          pairAnd N C (PO N C) (Ls N C) j pl.1 pl.2 ∨
          pairAnd N C (Ps N C) (LO N C) j pl.1 pl.2 ∨
          pairAnd N C (PO N C) (BadL N I C) j pl.1 pl.2 ∨
          pairAnd N C (BadP N I C) (LO N C) j pl.1 pl.2 ∨
          pairAnd N C (PO N C) (BadL2 N I C) j pl.1 pl.2 ∨
          pairAnd N C (BadP2 N I C) (LO N C) j pl.1 pl.2 ∨
          pairAnd3P N C (PO N C) (BadLT N I C) j pl.1 pl.2 ∨
          pairAnd3L N C (BadPT N I C) (LO N C) j pl.1 pl.2 ∨
          pairAnd N C (BadP2 N I C) (BadL2 N I C) j pl.1 pl.2 ∨
          gateBadL N I C (BadL N I C) (LO N C) j pl.1 pl.2 ∨
          gateBadP N I C (BadP N I C) (PO N C) j pl.1 pl.2 ∨
          gateBadL N I C (BadL N I C) (Ls N C) j pl.1 pl.2 ∨
          gateBadP N I C (BadP N I C) (Ps N C) j pl.1 pl.2 ∨
          gateBadL N I C (BadL2 N I C) (LO N C) j pl.1 pl.2 ∨
          gateBadP N I C (BadP2 N I C) (PO N C) j pl.1 pl.2 ∨
          gateTwinL N I C j pl.1 pl.2 ∨ gateTwinP N I C j pl.1 pl.2).card :=
      Finset.card_le_card fun pl hpl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hsub hpl)).2⟩
    omega

theorem wv_of_setInput_sub {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C)
    {A B : Finset (Fin (N + N))} (hAB : A ⊆ B) {w : ℕ}
    (hw : wv C (N + N) (setInput A) w = true) : wv C (N + N) (setInput B) w = true :=
  wv_mono hAO (fun i hi => by
    simp only [setInput, decide_eq_true_eq] at hi ⊢
    exact hAB hi) w hw

theorem wv_of_PO {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) {p : Fin N} {w : ℕ}
    (hp : p ∈ PO N C w) {A : Finset (Fin (N + N))} (hA : Fin.castAdd N p ∈ A) :
    wv C (N + N) (setInput A) w = true := by
  have hr : OrReach (N + N) C w p.val := mem_PO.mp hp
  apply orReach_wv hAO _ hr
  rw [wv_input C (N + N) _ p.val (by omega)]
  simp only [setInput, decide_eq_true_eq]
  have heq : (⟨p.val, by omega⟩ : Fin (N + N)) = Fin.castAdd N p := by ext; simp
  rw [heq]; exact hA

theorem wv_of_LO {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) {l : Fin N} {w : ℕ}
    (hl : l ∈ LO N C w) {A : Finset (Fin (N + N))} (hA : Fin.natAdd N l ∈ A) :
    wv C (N + N) (setInput A) w = true := by
  have hr : OrReach (N + N) C w (N + l.val) := mem_LO.mp hl
  apply orReach_wv hAO _ hr
  rw [wv_input C (N + N) _ (N + l.val) (by omega)]
  simp only [setInput, decide_eq_true_eq]
  have heq : (⟨N + l.val, by omega⟩ : Fin (N + N)) = Fin.natAdd N l := by ext; simp [Nat.add_comm]
  rw [heq]; exact hA

theorem wv_of_Ps {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) {p : Fin N} {w : ℕ}
    (hp : p ∈ Ps N C w) {A : Finset (Fin (N + N))} (hA : Fin.castAdd N p ∈ A) :
    wv C (N + N) (setInput A) w = true :=
  wv_of_setInput_sub hAO (by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; exact hA)
    (mem_Ps.mp hp)

theorem wv_of_Ls {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) {l : Fin N} {w : ℕ}
    (hl : l ∈ Ls N C w) {A : Finset (Fin (N + N))} (hA : Fin.natAdd N l ∈ A) :
    wv C (N + N) (setInput A) w = true :=
  wv_of_setInput_sub hAO (by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; exact hA)
    (mem_Ls.mp hl)

theorem and_true {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) {j : ℕ}
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    {z : Fin (N + N) → Bool}
    (h0 : wv C (N + N) z ((gateAt C j).inputs.getD 0 0) = true)
    (h1 : wv C (N + N) z ((gateAt C j).inputs.getD 1 0) = true) :
    wv C (N + N) z (N + N + j) = true := by
  obtain ⟨_, hinp⟩ := gate_info hAO hj
  rw [wv_gate C (N + N) z hAO.2.1 j hj, hand, hinp]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, h0, h1]

theorem and_true_s {N : ℕ} {C : Circuit} (hAO : IsAO2 (N + N) C) {j : ℕ}
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (s : Fin 2)
    {z : Fin (N + N) → Bool}
    (h0 : wv C (N + N) z ((gateAt C j).inputs.getD s.val 0) = true)
    (h1 : wv C (N + N) z ((gateAt C j).inputs.getD (1 - s.val) 0) = true) :
    wv C (N + N) z (N + N + j) = true := by
  rcases (by omega : s.val = 0 ∨ s.val = 1) with hs | hs
  · exact and_true hAO hj hand (by simpa [hs] using h0) (by simpa [hs] using h1)
  · exact and_true hAO hj hand (by simpa [hs] using h1) (by simpa [hs] using h0)

theorem top_sound {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {w : ℕ} (htop : OrReach (N + N) C C.output w) {A : Finset (Fin (N + N))}
    (hw : wv C (N + N) (setInput A) w = true) :
    ∃ p l : Fin N, I p l ∧ Fin.castAdd N p ∈ A ∧ Fin.natAdd N l ∈ A := by
  have hout : wv C (N + N) (setInput A) C.output = true := orReach_wv hAO _ htop hw
  have hcf : circuitFun (N + N) C (setInput A) = true := hout
  rw [hfun, decide_eq_true_eq] at hcf
  obtain ⟨p, l, hI, hp, hl⟩ := hcf
  simp only [setInput, decide_eq_true_eq] at hp hl
  exact ⟨p, l, hI, hp, hl⟩

theorem card_eq_one_of_mem_le {α : Type} {S : Finset α} {x : α} (hx : x ∈ S) (hc : S.card ≤ 1) :
    S = {x} := by
  have hge : 1 ≤ S.card := Finset.one_le_card.mpr ⟨x, hx⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
  rw [hy] at hx ⊢
  simp only [Finset.mem_singleton] at hx
  rw [hx]

theorem PO_input {N : ℕ} {C : Circuit} (p : Fin N) :
    PO N C p.val = {p} := by
  ext p'
  simp only [PO, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hr
    rcases Relation.ReflTransGen.cases_head hr with heq | ⟨_, ⟨j, _, hjeq, _, _⟩, _⟩
    · ext; exact heq.symm
    · omega
  · rintro rfl; exact Relation.ReflTransGen.refl

theorem LO_input {N : ℕ} {C : Circuit} (l : Fin N) :
    LO N C (N + l.val) = {l} := by
  ext l'
  simp only [LO, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hr
    rcases Relation.ReflTransGen.cases_head hr with heq | ⟨_, ⟨j, _, hjeq, _, _⟩, _⟩
    · ext; omega
    · omega
  · rintro rfl; exact Relation.ReflTransGen.refl

theorem Ps_input {N : ℕ} {C : Circuit} (p : Fin N) :
    Ps N C p.val = {p} := by
  ext p'
  simp only [Ps, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [wv_input C (N + N) _ p.val (by omega)]
  simp only [setInput, decide_eq_true_eq, Finset.mem_singleton, Fin.ext_iff, Fin.val_castAdd]
  exact eq_comm

theorem Ls_input {N : ℕ} {C : Circuit} (l : Fin N) :
    Ls N C (N + l.val) = {l} := by
  ext l'
  simp only [Ls, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [wv_input C (N + N) _ (N + l.val) (by omega)]
  simp only [setInput, decide_eq_true_eq, Finset.mem_singleton, Fin.ext_iff, Fin.val_natAdd]
  omega

theorem castAdd_ne_natAdd {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem cover_LO_star {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C) {p l : Fin N} {w : ℕ} (hl : l ∈ LO N C w)
    (hsub : ∀ l' ∈ LO N C w, I p l') (h2 : 2 ≤ (LO N C w).card) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  have hr : OrReach (N + N) C w (N + l.val) := mem_LO.mp hl
  have hlo : (LO N C (N + l.val)).card ≤ 1 := by rw [LO_input l]; simp
  have hyl : l ∈ LO N C (N + l.val) := by rw [LO_input l]; simp
  obtain ⟨j, hj, s, _, hor, hhi, hwsub, hslo, hyls⟩ :=
    or_walk_drop hAO (LO N C) or_mono_LO 1 hr (by omega) hlo hyl
  exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inl
    ⟨hor, by omega, fun l' hl' => hsub l' (hwsub hl'), s, card_eq_one_of_mem_le hyls hslo⟩)))⟩

theorem cover_PO_star {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C) {p l : Fin N} {w : ℕ} (hp : p ∈ PO N C w)
    (hsub : ∀ p' ∈ PO N C w, I p' l) (h2 : 2 ≤ (PO N C w).card) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  have hr : OrReach (N + N) C w p.val := mem_PO.mp hp
  have hlo : (PO N C p.val).card ≤ 1 := by rw [PO_input p]; simp
  have hyp : p ∈ PO N C p.val := by rw [PO_input p]; simp
  obtain ⟨j, hj, s, _, hor, hhi, hwsub, hslo, hyps⟩ :=
    or_walk_drop hAO (PO N C) or_mono_PO 1 hr (by omega) hlo hyp
  exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hor, by omega, fun p' hp' => hsub p' (hwsub hp'), s, card_eq_one_of_mem_le hyps hslo⟩))))⟩

theorem cover_near_LO {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C) {p l : Fin N} {w : ℕ} (hl : l ∈ LO N C w)
    (h1 : ((LO N C w).filter fun l' => ¬ I p l').card ≤ 1)
    (h4 : 4 ≤ (LO N C w).card) : ∃ j < C.gates.length, gateCov N I C j p l := by
  have hr : OrReach (N + N) C w (N + l.val) := mem_LO.mp hl
  have hlo : (LO N C (N + l.val)).card ≤ 3 := by rw [LO_input l]; simp
  have hyl : l ∈ LO N C (N + l.val) := by rw [LO_input l]; simp
  obtain ⟨j, hj, s, _, hor, hhi, hwsub, hslo, hyls⟩ :=
    or_walk_drop hAO (LO N C) or_mono_LO 3 hr (by omega) hlo hyl
  have hflt : ((LO N C (N + N + j)).filter fun l' => ¬ I p l').card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hwsub)).trans h1
  exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hor, by omega, hflt, s, hyls, hslo⟩)))))⟩

theorem cover_near_PO {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C) {p l : Fin N} {w : ℕ} (hp : p ∈ PO N C w)
    (h1 : ((PO N C w).filter fun p' => ¬ I p' l).card ≤ 1)
    (h4 : 4 ≤ (PO N C w).card) : ∃ j < C.gates.length, gateCov N I C j p l := by
  have hr : OrReach (N + N) C w p.val := mem_PO.mp hp
  have hlo : (PO N C p.val).card ≤ 3 := by rw [PO_input p]; simp
  have hyp : p ∈ PO N C p.val := by rw [PO_input p]; simp
  obtain ⟨j, hj, s, _, hor, hhi, hwsub, hslo, hyps⟩ :=
    or_walk_drop hAO (PO N C) or_mono_PO 3 hr (by omega) hlo hyp
  have hflt : ((PO N C (N + N + j)).filter fun p' => ¬ I p' l).card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hwsub)).trans h1
  exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hor, by omega, hflt, s, hyps, hslo⟩))))))⟩

theorem cover_Ls_from_rv {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    (hp : p ∈ Ps N C ((gateAt C a).inputs.getD s.val 0))
    {cl : ℕ} (hcl1 : 1 ≤ cl) (hcl2 : cl ≤ 2)
    (hrv : [0, cl] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C a).inputs.getD (1 - s.val) 0))
    (h2 : 2 ≤ (Ls N C ((gateAt C a).inputs.getD (1 - s.val) 0)).card) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set u := (gateAt C a).inputs.getD s.val 0
  set v := (gateAt C a).inputs.getD (1 - s.val) 0
  have hsub : ∀ l' ∈ Ls N C v, I p l' := by
    intro l' hl'
    have ha_tr := and_true_s hAO ha hand s (wv_of_Ps hAO hp (A := {Fin.castAdd N p, Fin.natAdd N l'}) (by simp))
      (wv_of_Ls hAO hl' (A := {Fin.castAdd N p, Fin.natAdd N l'}) (by simp))
    obtain ⟨p', l'', hI, hp', hl''⟩ := top_sound hAO hfun htop ha_tr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hl''
    have hpe : p' = p := by
      rcases hp' with h | h
      · exact Fin.castAdd_injective N N h
      · exact absurd h (castAdd_ne_natAdd p' l')
    have hle : l'' = l' := by
      rcases hl'' with h | h
      · exact absurd h.symm (castAdd_ne_natAdd p l'')
      · exact Fin.natAdd_injective N N h
    rw [← hpe, ← hle]; exact hI
  rcases (by omega : cl = 1 ∨ cl = 2) with rfl | rfl
  · have hr := rv_01 hAO p l v hrv
    have hlo : (Ls N C (N + l.val)).card ≤ 1 := by rw [Ls_input l]; simp
    have hyl : l ∈ Ls N C (N + l.val) := by rw [Ls_input l]; simp
    obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
      or_walk_drop hAO (Ls N C) (or_mono_Ls hAO) 1 hr (by omega) hlo hyl
    exact ⟨j, hj, Or.inl (Or.inl ⟨hor, by omega, fun l' hl' => hsub l' (hwsub hl'), s',
      card_eq_one_of_mem_le hyls hslo⟩)⟩
  · obtain ⟨b, hb, a1, b1, a2, b2, hrvb, handb, h1, h2', hae, hbe, hp1, hp2⟩ :=
      rv_split hAO p l v 0 2 hrv (by omega) (by omega) (by omega)
    have h01_1 : b1 = 1 ∧ a1 = 0 := by omega
    have h01_2 : b2 = 1 ∧ a2 = 0 := by omega
    rw [h01_1.2, h01_1.1] at h1
    rw [h01_2.2, h01_2.1] at h2'
    have hd1 := rv_01 hAO p l _ h1
    have hd2 := rv_01 hAO p l _ h2'
    have hlb : l ∈ Ls N C (N + N + b) := mem_Ls.mpr
      (and_true hAO hb handb (wv_of_LO hAO (mem_LO.mpr hd1) (by simp))
        (wv_of_LO hAO (mem_LO.mpr hd2) (by simp)))
    by_cases hbc : (Ls N C (N + N + b)).card ≤ 1
    · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
        or_walk_drop hAO (Ls N C) (or_mono_Ls hAO) 1 hrvb (by omega) hbc hlb
      exact ⟨j, hj, Or.inl (Or.inl ⟨hor, by omega, fun l' hl' => hsub l' (hwsub hl'), s',
        card_eq_one_of_mem_le hyls hslo⟩)⟩
    · set d1 := (gateAt C b).inputs.getD 0 0
      set d2 := (gateAt C b).inputs.getD 1 0
      have hb_sub1 : Ls N C (N + N + b) ⊆ Ls N C d1 := by
        intro l' hl'
        have hv := mf_mp hl'
        obtain ⟨_, hinp⟩ := gate_info hAO hb
        rw [wv_gate C (N + N) _ hAO.2.1 b hb, handb, hinp] at hv
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true] at hv
        exact mfu_mpr (hv.1)
      have hb_sub2 : Ls N C (N + N + b) ⊆ Ls N C d2 := by
        intro l' hl'
        have hv := mf_mp hl'
        obtain ⟨_, hinp⟩ := gate_info hAO hb
        rw [wv_gate C (N + N) _ hAO.2.1 b hb, handb, hinp] at hv
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true] at hv
        exact mfu_mpr (hv.2)
      have hor_sub : (∀ l1 ∈ Ls N C d1, I p l1) ∨ (∀ l2 ∈ Ls N C d2, I p l2) := by
        by_contra hboth
        push Not at hboth
        obtain ⟨⟨l1, hl1, hni1⟩, ⟨l2, hl2, hni2⟩⟩ := hboth
        set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l1, Fin.natAdd N l2}
        have hbA := and_true hAO hb handb (wv_of_Ls hAO hl1 (A := A) (by simp [A]))
          (wv_of_Ls hAO hl2 (A := A) (by simp [A]))
        have haA := and_true_s hAO ha hand s (wv_of_Ps hAO hp (A := A) (by simp [A]))
          (orReach_wv hAO _ hrvb hbA)
        obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
        have hpe : p' = p := by
          rcases hp' with h | h | h
          · exact Fin.castAdd_injective N N h
          · exact absurd h (castAdd_ne_natAdd p' l1)
          · exact absurd h (castAdd_ne_natAdd p' l2)
        subst hpe
        rcases hl' with h | h | h
        · exact absurd h.symm (castAdd_ne_natAdd p' l')
        · exact hni1 ((Fin.natAdd_injective N N h) ▸ hI)
        · exact hni2 ((Fin.natAdd_injective N N h) ▸ hI)
      have hlo : (Ls N C (N + l.val)).card ≤ 1 := by rw [Ls_input l]; simp
      have hyl : l ∈ Ls N C (N + l.val) := by rw [Ls_input l]; simp
      rcases hor_sub with hsub1 | hsub2
      · have hc1 : 2 ≤ (Ls N C d1).card := (by omega : 2 ≤ (Ls N C (N + N + b)).card).trans (Finset.card_le_card hb_sub1)
        obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
          or_walk_drop hAO (Ls N C) (or_mono_Ls hAO) 1 hd1 (by omega) hlo hyl
        exact ⟨j, hj, Or.inl (Or.inl ⟨hor, by omega, fun l' hl' => hsub1 l' (hwsub hl'), s',
          card_eq_one_of_mem_le hyls hslo⟩)⟩
      · have hc2 : 2 ≤ (Ls N C d2).card := (by omega : 2 ≤ (Ls N C (N + N + b)).card).trans (Finset.card_le_card hb_sub2)
        obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
          or_walk_drop hAO (Ls N C) (or_mono_Ls hAO) 1 hd2 (by omega) hlo hyl
        exact ⟨j, hj, Or.inl (Or.inl ⟨hor, by omega, fun l' hl' => hsub2 l' (hwsub hl'), s',
          card_eq_one_of_mem_le hyls hslo⟩)⟩

theorem cover_Ps_from_rv {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    (hl : l ∈ Ls N C ((gateAt C a).inputs.getD (1 - s.val) 0))
    {cp : ℕ} (hcp1 : 1 ≤ cp) (hcp2 : cp ≤ 2)
    (hrv : [cp, 0] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C a).inputs.getD s.val 0))
    (h2 : 2 ≤ (Ps N C ((gateAt C a).inputs.getD s.val 0)).card) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set u := (gateAt C a).inputs.getD s.val 0
  set v := (gateAt C a).inputs.getD (1 - s.val) 0
  have hsub : ∀ p' ∈ Ps N C u, I p' l := by
    intro p' hp'
    have ha_tr := and_true_s hAO ha hand s (wv_of_Ps hAO hp' (A := {Fin.castAdd N p', Fin.natAdd N l}) (by simp))
      (wv_of_Ls hAO hl (A := {Fin.castAdd N p', Fin.natAdd N l}) (by simp))
    obtain ⟨p'', l', hI, hp'', hl'⟩ := top_sound hAO hfun htop ha_tr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp'' hl'
    have hpe : p'' = p' := by
      rcases hp'' with h | h
      · exact Fin.castAdd_injective N N h
      · exact absurd h (castAdd_ne_natAdd p'' l)
    have hle : l' = l := by
      rcases hl' with h | h
      · exact absurd h.symm (castAdd_ne_natAdd p' l')
      · exact Fin.natAdd_injective N N h
    rw [← hpe, ← hle]; exact hI
  rcases (by omega : cp = 1 ∨ cp = 2) with rfl | rfl
  · have hr := rv_10 hAO p l u hrv
    have hlo : (Ps N C p.val).card ≤ 1 := by rw [Ps_input p]; simp
    have hyp : p ∈ Ps N C p.val := by rw [Ps_input p]; simp
    obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
      or_walk_drop hAO (Ps N C) (or_mono_Ps hAO) 1 hr (by omega) hlo hyp
    exact ⟨j, hj, Or.inl (Or.inr (Or.inl ⟨hor, by omega, fun p' hp' => hsub p' (hwsub hp'), s',
      card_eq_one_of_mem_le hyps hslo⟩))⟩
  · obtain ⟨b, hb, a1, b1, a2, b2, hrvb, handb, h1, h2', hae, hbe, hp1, hp2⟩ :=
      rv_split hAO p l u 2 0 hrv (by omega) (by omega) (by omega)
    have h10_1 : a1 = 1 ∧ b1 = 0 := by omega
    have h10_2 : a2 = 1 ∧ b2 = 0 := by omega
    rw [h10_1.1, h10_1.2] at h1
    rw [h10_2.1, h10_2.2] at h2'
    have hc1 := rv_10 hAO p l _ h1
    have hc2 := rv_10 hAO p l _ h2'
    have hpb : p ∈ Ps N C (N + N + b) := mem_Ps.mpr
      (and_true hAO hb handb (wv_of_PO hAO (mem_PO.mpr hc1) (by simp))
        (wv_of_PO hAO (mem_PO.mpr hc2) (by simp)))
    by_cases hbc : (Ps N C (N + N + b)).card ≤ 1
    · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
        or_walk_drop hAO (Ps N C) (or_mono_Ps hAO) 1 hrvb (by omega) hbc hpb
      exact ⟨j, hj, Or.inl (Or.inr (Or.inl ⟨hor, by omega, fun p' hp' => hsub p' (hwsub hp'), s',
        card_eq_one_of_mem_le hyps hslo⟩))⟩
    · set c1 := (gateAt C b).inputs.getD 0 0
      set c2 := (gateAt C b).inputs.getD 1 0
      have hb_sub1 : Ps N C (N + N + b) ⊆ Ps N C c1 := by
        intro p' hp'
        have hv := mf_mp hp'
        obtain ⟨_, hinp⟩ := gate_info hAO hb
        rw [wv_gate C (N + N) _ hAO.2.1 b hb, handb, hinp] at hv
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true] at hv
        exact mfu_mpr (hv.1)
      have hb_sub2 : Ps N C (N + N + b) ⊆ Ps N C c2 := by
        intro p' hp'
        have hv := mf_mp hp'
        obtain ⟨_, hinp⟩ := gate_info hAO hb
        rw [wv_gate C (N + N) _ hAO.2.1 b hb, handb, hinp] at hv
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true] at hv
        exact mfu_mpr (hv.2)
      have hor_sub : (∀ p1 ∈ Ps N C c1, I p1 l) ∨ (∀ p2 ∈ Ps N C c2, I p2 l) := by
        by_contra hboth
        push Not at hboth
        obtain ⟨⟨p1, hp1', hni1⟩, ⟨p2, hp2', hni2⟩⟩ := hboth
        set A : Finset (Fin (N + N)) := {Fin.castAdd N p1, Fin.castAdd N p2, Fin.natAdd N l}
        have hbA := and_true hAO hb handb (wv_of_Ps hAO hp1' (A := A) (by simp [A]))
          (wv_of_Ps hAO hp2' (A := A) (by simp [A]))
        have haA := and_true_s hAO ha hand s (orReach_wv hAO _ hrvb hbA)
          (wv_of_Ls hAO hl (A := A) (by simp [A]))
        obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
        have hle : l' = l := by
          rcases hl' with h | h | h
          · exact absurd h.symm (castAdd_ne_natAdd p1 l')
          · exact absurd h.symm (castAdd_ne_natAdd p2 l')
          · exact Fin.natAdd_injective N N h
        subst hle
        rcases hp' with h | h | h
        · exact hni1 ((Fin.castAdd_injective N N h) ▸ hI)
        · exact hni2 ((Fin.castAdd_injective N N h) ▸ hI)
        · exact absurd h (castAdd_ne_natAdd p' l')
      have hlo : (Ps N C p.val).card ≤ 1 := by rw [Ps_input p]; simp
      have hyp : p ∈ Ps N C p.val := by rw [Ps_input p]; simp
      rcases hor_sub with hsub1 | hsub2
      · have hc1' : 2 ≤ (Ps N C c1).card := (by omega : 2 ≤ (Ps N C (N + N + b)).card).trans (Finset.card_le_card hb_sub1)
        obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
          or_walk_drop hAO (Ps N C) (or_mono_Ps hAO) 1 hc1 (by omega) hlo hyp
        exact ⟨j, hj, Or.inl (Or.inr (Or.inl ⟨hor, by omega, fun p' hp' => hsub1 p' (hwsub hp'), s',
          card_eq_one_of_mem_le hyps hslo⟩))⟩
      · have hc2' : 2 ≤ (Ps N C c2).card := (by omega : 2 ≤ (Ps N C (N + N + b)).card).trans (Finset.card_le_card hb_sub2)
        obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
          or_walk_drop hAO (Ps N C) (or_mono_Ps hAO) 1 hc2 (by omega) hlo hyp
        exact ⟨j, hj, Or.inl (Or.inr (Or.inl ⟨hor, by omega, fun p' hp' => hsub2 p' (hwsub hp'), s',
          card_eq_one_of_mem_le hyps hslo⟩))⟩

theorem cover_type1 {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    {cp cl : ℕ} (hcp1 : 1 ≤ cp) (hcp2 : cp ≤ 2) (hcl1 : 1 ≤ cl) (hcl2 : cl ≤ 2)
    (hru : [cp, 0] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C a).inputs.getD s.val 0))
    (hrv : [0, cl] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C a).inputs.getD (1 - s.val) 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set u := (gateAt C a).inputs.getD s.val 0
  set v := (gateAt C a).inputs.getD (1 - s.val) 0
  have hp : p ∈ Ps N C u := mem_Ps.mpr
    (rv_sound_wv hAO p l _ u cp 0 hru (fun _ => by simp [setInput]) (fun h => by omega))
  have hl : l ∈ Ls N C v := mem_Ls.mpr
    (rv_sound_wv hAO p l _ v 0 cl hrv (fun h => by omega) (fun _ => by simp [setInput]))
  by_cases hpu : 2 ≤ (Ps N C u).card
  · exact cover_Ps_from_rv hAO hfun ha htop hand s hl hcp1 hcp2 hru hpu
  · by_cases hlv : 2 ≤ (Ls N C v).card
    · exact cover_Ls_from_rv hAO hfun ha htop hand s hp hcl1 hcl2 hrv hlv
    · have hpeq : Ps N C u = {p} := card_eq_one_of_mem_le hp (by omega)
      have hleq : Ls N C v = {l} := card_eq_one_of_mem_le hl (by omega)
      exact ⟨a, ha, Or.inr (Or.inl ⟨hand, s, hpeq, hleq⟩)⟩

theorem badL_sub_of_top {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    (hp : p ∈ PO N C ((gateAt C a).inputs.getD s.val 0)) :
    ∀ l' ∈ BadL N I C ((gateAt C a).inputs.getD (1 - s.val) 0), I p l' := by
  intro l' hl'
  obtain ⟨pb, hni, hvb⟩ := mf_mp hl'
  set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.castAdd N pb, Fin.natAdd N l'}
  have huA := wv_of_PO hAO hp (A := A) (by simp [A])
  have hvA := wv_of_setInput_sub hAO (A := {Fin.castAdd N pb, Fin.natAdd N l'}) (B := A)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [A]) hvb
  have haA := and_true_s hAO ha hand s huA hvA
  obtain ⟨p', l'', hI, hp', hl''⟩ := top_sound hAO hfun htop haA
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl''
  have hle : l'' = l' := by
    rcases hl'' with h | h | h
    · exact absurd h.symm (castAdd_ne_natAdd p l'')
    · exact absurd h.symm (castAdd_ne_natAdd pb l'')
    · exact Fin.natAdd_injective N N h
  subst hle
  rcases hp' with h | h | h
  · exact (Fin.castAdd_injective N N h) ▸ hI
  · exact absurd ((Fin.castAdd_injective N N h) ▸ hI) hni
  · exact absurd h (castAdd_ne_natAdd p' l'')

theorem badP_sub_of_top {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    (hl : l ∈ LO N C ((gateAt C a).inputs.getD (1 - s.val) 0)) :
    ∀ p' ∈ BadP N I C ((gateAt C a).inputs.getD s.val 0), I p' l := by
  intro p' hp'
  obtain ⟨lb, hni, hub⟩ := mf_mp hp'
  set A : Finset (Fin (N + N)) := {Fin.castAdd N p', Fin.natAdd N l, Fin.natAdd N lb}
  have hvA := wv_of_LO hAO hl (A := A) (by simp [A])
  have huA := wv_of_setInput_sub hAO (A := {Fin.castAdd N p', Fin.natAdd N lb}) (B := A)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [A]) hub
  have haA := and_true_s hAO ha hand s huA hvA
  obtain ⟨p'', l'', hI, hp'', hl''⟩ := top_sound hAO hfun htop haA
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl''
  have hpe : p'' = p' := by
    rcases hp'' with h | h | h
    · exact Fin.castAdd_injective N N h
    · exact absurd h (castAdd_ne_natAdd p'' l)
    · exact absurd h (castAdd_ne_natAdd p'' lb)
  subst hpe
  rcases hl'' with h | h | h
  · exact absurd h.symm (castAdd_ne_natAdd p'' l'')
  · exact (Fin.natAdd_injective N N h) ▸ hI
  · exact absurd ((Fin.natAdd_injective N N h) ▸ hI) hni

theorem badL2_sub_badL {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {w : ℕ} :
    BadL2 N I C w ⊆ BadL N I C w := by
  intro l' hl'
  obtain ⟨p1, _, _, hni1, _, hv1, _⟩ := mf_mp hl'
  exact mfu_mpr ⟨p1, hni1, hv1⟩

theorem badP2_sub_badP {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {w : ℕ} :
    BadP2 N I C w ⊆ BadP N I C w := by
  intro p' hp'
  obtain ⟨l1, _, _, hni1, _, hv1, _⟩ := mf_mp hp'
  exact mfu_mpr ⟨l1, hni1, hv1⟩

theorem badLT_ok_of_top {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    (hp : p ∈ PO N C ((gateAt C a).inputs.getD s.val 0))
    {w : ℕ} (hvw : OrReach (N + N) C ((gateAt C a).inputs.getD (1 - s.val) 0) w) :
    BadLT_ok N I C w p := by
  intro l' _ p2 l2a l2b _ hn1 hn2 hn3 hva hvb
  have eval1 : ∀ lx : Fin N, ¬ I p2 lx →
      wv C (N + N) (setInput {Fin.castAdd N p2, Fin.natAdd N l', Fin.natAdd N lx}) w = true →
      I p l' ∨ I p lx := by
    intro lx hnx hwx
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.castAdd N p2, Fin.natAdd N l', Fin.natAdd N lx}
    have huA := wv_of_PO hAO hp (A := A) (by simp [A])
    have hwA := wv_of_setInput_sub hAO (B := A)
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> simp [A]) hwx
    have haA := and_true_s hAO ha hand s huA (orReach_wv hAO _ hvw hwA)
    obtain ⟨p', l'', hI, hp', hl''⟩ := top_sound hAO hfun htop haA
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl''
    rcases hp' with h | h | h | h
    · have hpe := Fin.castAdd_injective N N h; subst hpe
      rcases hl'' with h2 | h2 | h2 | h2
      · exact absurd h2.symm (castAdd_ne_natAdd p' l'')
      · exact absurd h2.symm (castAdd_ne_natAdd p2 l'')
      · exact Or.inl ((Fin.natAdd_injective N N h2) ▸ hI)
      · exact Or.inr ((Fin.natAdd_injective N N h2) ▸ hI)
    · have hpe := Fin.castAdd_injective N N h; subst hpe
      rcases hl'' with h2 | h2 | h2 | h2
      · exact absurd h2.symm (castAdd_ne_natAdd p l'')
      · exact absurd h2.symm (castAdd_ne_natAdd p' l'')
      · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hn1
      · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hnx
    · exact absurd h (castAdd_ne_natAdd p' l')
    · exact absurd h (castAdd_ne_natAdd p' lx)
  have h1 := eval1 l2a hn2 hva
  have h2 := eval1 l2b hn3 hvb
  tauto

theorem badPT_ok_of_top {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    (hl : l ∈ LO N C ((gateAt C a).inputs.getD (1 - s.val) 0))
    {w : ℕ} (huw : OrReach (N + N) C ((gateAt C a).inputs.getD s.val 0) w) :
    BadPT_ok N I C w l := by
  intro p' _ l2 p2a p2b _ hn1 hn2 hn3 hva hvb
  have eval1 : ∀ px : Fin N, ¬ I px l2 →
      wv C (N + N) (setInput {Fin.castAdd N p', Fin.castAdd N px, Fin.natAdd N l2}) w = true →
      I p' l ∨ I px l := by
    intro px hnx hwx
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p', Fin.castAdd N px, Fin.natAdd N l, Fin.natAdd N l2}
    have hvA := wv_of_LO hAO hl (A := A) (by simp [A])
    have hwA := wv_of_setInput_sub hAO (B := A)
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> simp [A]) hwx
    have haA := and_true_s hAO ha hand s (orReach_wv hAO _ huw hwA) hvA
    obtain ⟨p'', l'', hI, hp'', hl''⟩ := top_sound hAO hfun htop haA
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl''
    rcases hl'' with h | h | h | h
    · exact absurd h.symm (castAdd_ne_natAdd p' l'')
    · exact absurd h.symm (castAdd_ne_natAdd px l'')
    · have hle := Fin.natAdd_injective N N h; subst hle
      rcases hp'' with h2 | h2 | h2 | h2
      · exact Or.inl ((Fin.castAdd_injective N N h2) ▸ hI)
      · exact Or.inr ((Fin.castAdd_injective N N h2) ▸ hI)
      · exact absurd h2 (castAdd_ne_natAdd p'' l'')
      · exact absurd h2 (castAdd_ne_natAdd p'' l2)
    · have hle := Fin.natAdd_injective N N h; subst hle
      rcases hp'' with h2 | h2 | h2 | h2
      · exact absurd ((Fin.castAdd_injective N N h2) ▸ hI) hn1
      · exact absurd ((Fin.castAdd_injective N N h2) ▸ hI) hnx
      · exact absurd h2 (castAdd_ne_natAdd p'' l)
      · exact absurd h2 (castAdd_ne_natAdd p'' l'')
  have h1 := eval1 p2a hn2 hva
  have h2 := eval1 p2b hn3 hvb
  tauto

theorem cover_type2a_gen {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (sa : Fin 2)
    (hpu : p ∈ PO N C ((gateAt C a).inputs.getD sa.val 0))
    {b : ℕ} (hb : b < C.gates.length) (hvb : OrReach (N + N) C ((gateAt C a).inputs.getD (1 - sa.val) 0) (N + N + b))
    (handb : (gateAt C b).op = GateOp.and) (sb : Fin 2)
    (hpd1 : p ∈ PO N C ((gateAt C b).inputs.getD sb.val 0))
    {cl : ℕ} (hcl1 : 1 ≤ cl) (hcl2 : cl ≤ 2)
    (hrd2 : [0, cl] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C b).inputs.getD (1 - sb.val) 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set u := (gateAt C a).inputs.getD sa.val 0
  set v := (gateAt C a).inputs.getD (1 - sa.val) 0
  set d1 := (gateAt C b).inputs.getD sb.val 0
  set d2 := (gateAt C b).inputs.getD (1 - sb.val) 0
  have hld2 : l ∈ Ls N C d2 := mem_Ls.mpr
    (rv_sound_wv hAO p l _ d2 0 cl hrd2 (fun h => by omega) (fun _ => by simp [setInput]))
  have hLd2_sub : ∀ l' ∈ Ls N C d2, I p l' := by
    intro l' hl'
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l'}
    have hbA := and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (A := A) (by simp [A]))
      (wv_of_Ls hAO hl' (A := A) (by simp [A]))
    have haA := and_true_s hAO ha hand sa (wv_of_PO hAO hpu (A := A) (by simp [A]))
      (orReach_wv hAO _ hvb hbA)
    obtain ⟨p', l'', hI, hp', hl''⟩ := top_sound hAO hfun htop haA
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl''
    have hpe : p' = p := by
      rcases hp' with h | h
      · exact Fin.castAdd_injective N N h
      · exact absurd h (castAdd_ne_natAdd p' l')
    have hle : l'' = l' := by
      rcases hl'' with h | h
      · exact absurd h.symm (castAdd_ne_natAdd p l'')
      · exact Fin.natAdd_injective N N h
    rw [← hpe, ← hle]; exact hI
  by_cases hLd2_big : 2 ≤ (Ls N C d2).card
  · rcases (by omega : cl = 1 ∨ cl = 2) with rfl | rfl
    · have hr := rv_01 hAO p l d2 hrd2
      have hlo : (Ls N C (N + l.val)).card ≤ 1 := by rw [Ls_input l]; simp
      have hyl : l ∈ Ls N C (N + l.val) := by rw [Ls_input l]; simp
      obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
        or_walk_drop hAO (Ls N C) (or_mono_Ls hAO) 1 hr (by omega) hlo hyl
      exact ⟨j, hj, Or.inl (Or.inl ⟨hor, by omega, fun l' hl' => hLd2_sub l' (hwsub hl'), s',
        card_eq_one_of_mem_le hyls hslo⟩)⟩
    · obtain ⟨e, he, a1, b1, a2, b2, hrde, hande, h1, h2', hae, hbe, hp1, hp2⟩ :=
        rv_split hAO p l d2 0 2 hrd2 (by omega) (by omega) (by omega)
      have h01_1 : b1 = 1 ∧ a1 = 0 := by omega
      have h01_2 : b2 = 1 ∧ a2 = 0 := by omega
      rw [h01_1.2, h01_1.1] at h1
      rw [h01_2.2, h01_2.1] at h2'
      have he1 := rv_01 hAO p l _ h1
      have he2 := rv_01 hAO p l _ h2'
      have hle_mem : l ∈ Ls N C (N + N + e) := mem_Ls.mpr
        (and_true hAO he hande (wv_of_LO hAO (mem_LO.mpr he1) (by simp))
          (wv_of_LO hAO (mem_LO.mpr he2) (by simp)))
      by_cases hec : (Ls N C (N + N + e)).card ≤ 1
      · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
          or_walk_drop hAO (Ls N C) (or_mono_Ls hAO) 1 hrde (by omega) hec hle_mem
        exact ⟨j, hj, Or.inl (Or.inl ⟨hor, by omega, fun l' hl' => hLd2_sub l' (hwsub hl'), s',
          card_eq_one_of_mem_le hyls hslo⟩)⟩
      · set e1 := (gateAt C e).inputs.getD 0 0
        set e2 := (gateAt C e).inputs.getD 1 0
        have he_sub1 : Ls N C (N + N + e) ⊆ Ls N C e1 := by
          intro l' hl'
          have hv := mf_mp hl'
          obtain ⟨_, hinp⟩ := gate_info hAO he
          rw [wv_gate C (N + N) _ hAO.2.1 e he, hande, hinp] at hv
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true] at hv
          exact mfu_mpr (hv.1)
        have he_sub2 : Ls N C (N + N + e) ⊆ Ls N C e2 := by
          intro l' hl'
          have hv := mf_mp hl'
          obtain ⟨_, hinp⟩ := gate_info hAO he
          rw [wv_gate C (N + N) _ hAO.2.1 e he, hande, hinp] at hv
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true] at hv
          exact mfu_mpr (hv.2)
        have hor_sub : (∀ l1 ∈ Ls N C e1, I p l1) ∨ (∀ l2 ∈ Ls N C e2, I p l2) := by
          by_contra hboth
          push Not at hboth
          obtain ⟨⟨l1, hl1, hni1⟩, ⟨l2, hl2, hni2⟩⟩ := hboth
          set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l1, Fin.natAdd N l2}
          have heA := and_true hAO he hande (wv_of_Ls hAO hl1 (A := A) (by simp [A]))
            (wv_of_Ls hAO hl2 (A := A) (by simp [A]))
          have hbA := and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (A := A) (by simp [A]))
            (orReach_wv hAO _ hrde heA)
          have haA := and_true_s hAO ha hand sa (wv_of_PO hAO hpu (A := A) (by simp [A]))
            (orReach_wv hAO _ hvb hbA)
          obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
          simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
          have hpe : p' = p := by
            rcases hp' with h | h | h
            · exact Fin.castAdd_injective N N h
            · exact absurd h (castAdd_ne_natAdd p' l1)
            · exact absurd h (castAdd_ne_natAdd p' l2)
          subst hpe
          rcases hl' with h | h | h
          · exact absurd h.symm (castAdd_ne_natAdd p' l')
          · exact hni1 ((Fin.natAdd_injective N N h) ▸ hI)
          · exact hni2 ((Fin.natAdd_injective N N h) ▸ hI)
        have hlo : (Ls N C (N + l.val)).card ≤ 1 := by rw [Ls_input l]; simp
        have hyl : l ∈ Ls N C (N + l.val) := by rw [Ls_input l]; simp
        rcases hor_sub with hs1 | hs2
        · have hc1 : 2 ≤ (Ls N C e1).card := (by omega : 2 ≤ (Ls N C (N + N + e)).card).trans (Finset.card_le_card he_sub1)
          obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
            or_walk_drop hAO (Ls N C) (or_mono_Ls hAO) 1 he1 (by omega) hlo hyl
          exact ⟨j, hj, Or.inl (Or.inl ⟨hor, by omega, fun l' hl' => hs1 l' (hwsub hl'), s',
            card_eq_one_of_mem_le hyls hslo⟩)⟩
        · have hc2 : 2 ≤ (Ls N C e2).card := (by omega : 2 ≤ (Ls N C (N + N + e)).card).trans (Finset.card_le_card he_sub2)
          obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
            or_walk_drop hAO (Ls N C) (or_mono_Ls hAO) 1 he2 (by omega) hlo hyl
          exact ⟨j, hj, Or.inl (Or.inl ⟨hor, by omega, fun l' hl' => hs2 l' (hwsub hl'), s',
            card_eq_one_of_mem_le hyls hslo⟩)⟩
  · have hLd2_eq : Ls N C d2 = {l} := card_eq_one_of_mem_le hld2 (by omega)
    by_cases hd1_sub : ∀ p' ∈ PO N C d1, I p' l
    · by_cases hd1_big : 2 ≤ (PO N C d1).card
      · exact cover_PO_star hAO hpd1 hd1_sub hd1_big
      · have hpd1_eq : PO N C d1 = {p} := card_eq_one_of_mem_le hpd1 (by omega)
        exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨handb, sb, hpd1_eq, hLd2_eq⟩))))⟩
    · push Not at hd1_sub
      obtain ⟨pb, hpb_mem, hpb_ni⟩ := hd1_sub
      have hlb_bad : l ∈ BadL N I C (N + N + b) := mfu_mpr ⟨pb, hpb_ni,
        and_true_s hAO hb handb sb (wv_of_PO hAO hpb_mem (by simp)) (wv_of_Ls hAO hld2 (by simp))⟩
      have hBadV_sub := badL_sub_of_top hAO hfun ha htop hand sa hpu
      have hBadB_sub : BadL N I C (N + N + b) ⊆ BadL N I C v :=
        orReach_sub_F (BadL N I C) (or_mono_BadL hAO) hvb
      by_cases hbb : 2 ≤ (BadL N I C (N + N + b)).card
      · exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨handb, hbb, fun l' hl' => hBadV_sub l' (hBadB_sub hl'),
             ⟨1 - sb.val, by omega⟩, hld2, by change (Ls N C d2).card ≤ 3; rw [hLd2_eq]; simp⟩)))))))))))))))⟩
      · by_cases hbv : 2 ≤ (BadL N I C v).card
        · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
            or_walk_drop hAO (BadL N I C) (or_mono_BadL hAO) 1 hvb (by omega) (by omega) hlb_bad
          exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hor, by omega, fun l' hl' => hBadV_sub l' (hwsub hl'), s',
             card_eq_one_of_mem_le hyls hslo⟩)))))))⟩
        · have hBadV_eq : BadL N I C v = {l} := card_eq_one_of_mem_le (hBadB_sub hlb_bad) (by omega)
          by_cases hpu_big : 2 ≤ (PO N C u).card
          · have hu_sub : ∀ p' ∈ PO N C u, I p' l := by
              intro p' hp'
              set A : Finset (Fin (N + N)) := {Fin.castAdd N p', Fin.castAdd N pb, Fin.natAdd N l}
              have hbA := and_true_s hAO hb handb sb (wv_of_PO hAO hpb_mem (A := A) (by simp [A]))
                (wv_of_Ls hAO hld2 (A := A) (by simp [A]))
              have haA := and_true_s hAO ha hand sa (wv_of_PO hAO hp' (A := A) (by simp [A]))
                (orReach_wv hAO _ hvb hbA)
              obtain ⟨p'', l'', hI, hp'', hl''⟩ := top_sound hAO hfun htop haA
              simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl''
              have hle : l'' = l := by
                rcases hl'' with h | h | h
                · exact absurd h.symm (castAdd_ne_natAdd p' l'')
                · exact absurd h.symm (castAdd_ne_natAdd pb l'')
                · exact Fin.natAdd_injective N N h
              subst hle
              rcases hp'' with h | h | h
              · exact (Fin.castAdd_injective N N h) ▸ hI
              · exact absurd ((Fin.castAdd_injective N N h) ▸ hI) hpb_ni
              · exact absurd h (castAdd_ne_natAdd p'' l'')
            exact cover_PO_star hAO hpu hu_sub hpu_big
          · have hpu_eq : PO N C u = {p} := card_eq_one_of_mem_le hpu (by omega)
            exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hand, sa, hpu_eq, hBadV_eq⟩))))))⟩

theorem cover_type2b_gen {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (sa : Fin 2)
    (hlv : l ∈ LO N C ((gateAt C a).inputs.getD (1 - sa.val) 0))
    {b : ℕ} (hb : b < C.gates.length) (hub : OrReach (N + N) C ((gateAt C a).inputs.getD sa.val 0) (N + N + b))
    (handb : (gateAt C b).op = GateOp.and) (sb : Fin 2)
    (hld2 : l ∈ LO N C ((gateAt C b).inputs.getD (1 - sb.val) 0))
    {cp : ℕ} (hcp1 : 1 ≤ cp) (hcp2 : cp ≤ 2)
    (hrd1 : [cp, 0] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C b).inputs.getD sb.val 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set u := (gateAt C a).inputs.getD sa.val 0
  set v := (gateAt C a).inputs.getD (1 - sa.val) 0
  set d1 := (gateAt C b).inputs.getD sb.val 0
  set d2 := (gateAt C b).inputs.getD (1 - sb.val) 0
  have hpd1 : p ∈ Ps N C d1 := mem_Ps.mpr
    (rv_sound_wv hAO p l _ d1 cp 0 hrd1 (fun _ => by simp [setInput]) (fun h => by omega))
  have hPd1_sub : ∀ p' ∈ Ps N C d1, I p' l := by
    intro p' hp'
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p', Fin.natAdd N l}
    have hbA := and_true_s hAO hb handb sb (wv_of_Ps hAO hp' (A := A) (by simp [A]))
      (wv_of_LO hAO hld2 (A := A) (by simp [A]))
    have haA := and_true_s hAO ha hand sa (orReach_wv hAO _ hub hbA)
      (wv_of_LO hAO hlv (A := A) (by simp [A]))
    obtain ⟨p'', l', hI, hp'', hl'⟩ := top_sound hAO hfun htop haA
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl'
    have hpe : p'' = p' := by
      rcases hp'' with h | h
      · exact Fin.castAdd_injective N N h
      · exact absurd h (castAdd_ne_natAdd p'' l)
    have hle : l' = l := by
      rcases hl' with h | h
      · exact absurd h.symm (castAdd_ne_natAdd p' l')
      · exact Fin.natAdd_injective N N h
    rw [← hpe, ← hle]; exact hI
  by_cases hPd1_big : 2 ≤ (Ps N C d1).card
  · rcases (by omega : cp = 1 ∨ cp = 2) with rfl | rfl
    · have hr := rv_10 hAO p l d1 hrd1
      have hlo : (Ps N C p.val).card ≤ 1 := by rw [Ps_input p]; simp
      have hyp : p ∈ Ps N C p.val := by rw [Ps_input p]; simp
      obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
        or_walk_drop hAO (Ps N C) (or_mono_Ps hAO) 1 hr (by omega) hlo hyp
      exact ⟨j, hj, Or.inl (Or.inr (Or.inl ⟨hor, by omega, fun p' hp' => hPd1_sub p' (hwsub hp'), s',
        card_eq_one_of_mem_le hyps hslo⟩))⟩
    · obtain ⟨e, he, a1, b1, a2, b2, hrde, hande, h1, h2', hae, hbe, hp1, hp2⟩ :=
        rv_split hAO p l d1 2 0 hrd1 (by omega) (by omega) (by omega)
      have h10_1 : a1 = 1 ∧ b1 = 0 := by omega
      have h10_2 : a2 = 1 ∧ b2 = 0 := by omega
      rw [h10_1.1, h10_1.2] at h1
      rw [h10_2.1, h10_2.2] at h2'
      have he1 := rv_10 hAO p l _ h1
      have he2 := rv_10 hAO p l _ h2'
      have hpe_mem : p ∈ Ps N C (N + N + e) := mem_Ps.mpr
        (and_true hAO he hande (wv_of_PO hAO (mem_PO.mpr he1) (by simp))
          (wv_of_PO hAO (mem_PO.mpr he2) (by simp)))
      by_cases hec : (Ps N C (N + N + e)).card ≤ 1
      · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
          or_walk_drop hAO (Ps N C) (or_mono_Ps hAO) 1 hrde (by omega) hec hpe_mem
        exact ⟨j, hj, Or.inl (Or.inr (Or.inl ⟨hor, by omega, fun p' hp' => hPd1_sub p' (hwsub hp'), s',
          card_eq_one_of_mem_le hyps hslo⟩))⟩
      · set e1 := (gateAt C e).inputs.getD 0 0
        set e2 := (gateAt C e).inputs.getD 1 0
        have he_sub1 : Ps N C (N + N + e) ⊆ Ps N C e1 := by
          intro p' hp'
          have hv := mf_mp hp'
          obtain ⟨_, hinp⟩ := gate_info hAO he
          rw [wv_gate C (N + N) _ hAO.2.1 e he, hande, hinp] at hv
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true] at hv
          exact mfu_mpr (hv.1)
        have he_sub2 : Ps N C (N + N + e) ⊆ Ps N C e2 := by
          intro p' hp'
          have hv := mf_mp hp'
          obtain ⟨_, hinp⟩ := gate_info hAO he
          rw [wv_gate C (N + N) _ hAO.2.1 e he, hande, hinp] at hv
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_true] at hv
          exact mfu_mpr (hv.2)
        have hor_sub : (∀ p1 ∈ Ps N C e1, I p1 l) ∨ (∀ p2 ∈ Ps N C e2, I p2 l) := by
          by_contra hboth
          push Not at hboth
          obtain ⟨⟨p1, hp1', hni1⟩, ⟨p2, hp2', hni2⟩⟩ := hboth
          set A : Finset (Fin (N + N)) := {Fin.castAdd N p1, Fin.castAdd N p2, Fin.natAdd N l}
          have heA := and_true hAO he hande (wv_of_Ps hAO hp1' (A := A) (by simp [A]))
            (wv_of_Ps hAO hp2' (A := A) (by simp [A]))
          have hbA := and_true_s hAO hb handb sb (orReach_wv hAO _ hrde heA)
            (wv_of_LO hAO hld2 (A := A) (by simp [A]))
          have haA := and_true_s hAO ha hand sa (orReach_wv hAO _ hub hbA)
            (wv_of_LO hAO hlv (A := A) (by simp [A]))
          obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
          simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
          have hle : l' = l := by
            rcases hl' with h | h | h
            · exact absurd h.symm (castAdd_ne_natAdd p1 l')
            · exact absurd h.symm (castAdd_ne_natAdd p2 l')
            · exact Fin.natAdd_injective N N h
          subst hle
          rcases hp' with h | h | h
          · exact hni1 ((Fin.castAdd_injective N N h) ▸ hI)
          · exact hni2 ((Fin.castAdd_injective N N h) ▸ hI)
          · exact absurd h (castAdd_ne_natAdd p' l')
        have hlo : (Ps N C p.val).card ≤ 1 := by rw [Ps_input p]; simp
        have hyp : p ∈ Ps N C p.val := by rw [Ps_input p]; simp
        rcases hor_sub with hs1 | hs2
        · have hc1 : 2 ≤ (Ps N C e1).card := (by omega : 2 ≤ (Ps N C (N + N + e)).card).trans (Finset.card_le_card he_sub1)
          obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
            or_walk_drop hAO (Ps N C) (or_mono_Ps hAO) 1 he1 (by omega) hlo hyp
          exact ⟨j, hj, Or.inl (Or.inr (Or.inl ⟨hor, by omega, fun p' hp' => hs1 p' (hwsub hp'), s',
            card_eq_one_of_mem_le hyps hslo⟩))⟩
        · have hc2 : 2 ≤ (Ps N C e2).card := (by omega : 2 ≤ (Ps N C (N + N + e)).card).trans (Finset.card_le_card he_sub2)
          obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
            or_walk_drop hAO (Ps N C) (or_mono_Ps hAO) 1 he2 (by omega) hlo hyp
          exact ⟨j, hj, Or.inl (Or.inr (Or.inl ⟨hor, by omega, fun p' hp' => hs2 p' (hwsub hp'), s',
            card_eq_one_of_mem_le hyps hslo⟩))⟩
  · have hPd1_eq : Ps N C d1 = {p} := card_eq_one_of_mem_le hpd1 (by omega)
    by_cases hd2_sub : ∀ l' ∈ LO N C d2, I p l'
    · by_cases hd2_big : 2 ≤ (LO N C d2).card
      · exact cover_LO_star hAO hld2 hd2_sub hd2_big
      · have hld2_eq : LO N C d2 = {l} := card_eq_one_of_mem_le hld2 (by omega)
        exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨handb, sb, hPd1_eq, hld2_eq⟩)))))⟩
    · push Not at hd2_sub
      obtain ⟨lb, hlb_mem, hlb_ni⟩ := hd2_sub
      have hpb_bad : p ∈ BadP N I C (N + N + b) := mfu_mpr ⟨lb, hlb_ni,
        and_true_s hAO hb handb sb (wv_of_Ps hAO hpd1 (by simp)) (wv_of_LO hAO hlb_mem (by simp))⟩
      have hBadU_sub := badP_sub_of_top hAO hfun ha htop hand sa hlv
      have hBadB_sub : BadP N I C (N + N + b) ⊆ BadP N I C u :=
        orReach_sub_F (BadP N I C) (or_mono_BadP hAO) hub
      by_cases hbb : 2 ≤ (BadP N I C (N + N + b)).card
      · exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨handb, hbb, fun p' hp' => hBadU_sub p' (hBadB_sub hp'),
             sb, hpd1, by change (Ps N C d1).card ≤ 3; rw [hPd1_eq]; simp⟩))))))))))))))))⟩
      · by_cases hbu : 2 ≤ (BadP N I C u).card
        · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
            or_walk_drop hAO (BadP N I C) (or_mono_BadP hAO) 1 hub (by omega) (by omega) hpb_bad
          exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hor, by omega, fun p' hp' => hBadU_sub p' (hwsub hp'), s',
             card_eq_one_of_mem_le hyps hslo⟩))))))))⟩
        · have hBadU_eq : BadP N I C u = {p} := card_eq_one_of_mem_le (hBadB_sub hpb_bad) (by omega)
          by_cases hlv_big : 2 ≤ (LO N C v).card
          · have hv_sub : ∀ l' ∈ LO N C v, I p l' := by
              intro l' hl'
              set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l', Fin.natAdd N lb}
              have hbA := and_true_s hAO hb handb sb (wv_of_Ps hAO hpd1 (A := A) (by simp [A]))
                (wv_of_LO hAO hlb_mem (A := A) (by simp [A]))
              have haA := and_true_s hAO ha hand sa (orReach_wv hAO _ hub hbA)
                (wv_of_LO hAO hl' (A := A) (by simp [A]))
              obtain ⟨p'', l'', hI, hp'', hl''⟩ := top_sound hAO hfun htop haA
              simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl''
              have hpe : p'' = p := by
                rcases hp'' with h | h | h
                · exact Fin.castAdd_injective N N h
                · exact absurd h (castAdd_ne_natAdd p'' l')
                · exact absurd h (castAdd_ne_natAdd p'' lb)
              subst hpe
              rcases hl'' with h | h | h
              · exact absurd h.symm (castAdd_ne_natAdd p'' l'')
              · exact (Fin.natAdd_injective N N h) ▸ hI
              · exact absurd ((Fin.natAdd_injective N N h) ▸ hI) hlb_ni
            exact cover_LO_star hAO hlv hv_sub hlv_big
          · have hlv_eq : LO N C v = {l} := card_eq_one_of_mem_le hlv (by omega)
            exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hand, sa, hBadU_eq, hlv_eq⟩)))))))⟩

theorem cover_type2c2 {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (sa : Fin 2)
    (hpu : p ∈ PO N C ((gateAt C a).inputs.getD sa.val 0))
    {b : ℕ} (hb : b < C.gates.length) (hvb : OrReach (N + N) C ((gateAt C a).inputs.getD (1 - sa.val) 0) (N + N + b))
    (handb : (gateAt C b).op = GateOp.and) (sb : Fin 2)
    (hld1 : l ∈ LO N C ((gateAt C b).inputs.getD sb.val 0))
    {e : ℕ} (he : e < C.gates.length) (hd2e : OrReach (N + N) C ((gateAt C b).inputs.getD (1 - sb.val) 0) (N + N + e))
    (hande : (gateAt C e).op = GateOp.and) (se : Fin 2)
    (hpe1 : p ∈ PO N C ((gateAt C e).inputs.getD se.val 0))
    (hle2 : l ∈ LO N C ((gateAt C e).inputs.getD (1 - se.val) 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set u := (gateAt C a).inputs.getD sa.val 0
  set v := (gateAt C a).inputs.getD (1 - sa.val) 0
  set d1 := (gateAt C b).inputs.getD sb.val 0
  set d2 := (gateAt C b).inputs.getD (1 - sb.val) 0
  set e1 := (gateAt C e).inputs.getD se.val 0
  set e2 := (gateAt C e).inputs.getD (1 - se.val) 0
  have hlines : (∀ l1 ∈ LO N C d1, I p l1) ∨ (∀ l2 ∈ LO N C e2, I p l2) := by
    by_contra hboth; push Not at hboth
    obtain ⟨⟨l1, hl1, hn1⟩, ⟨l2, hl2, hn2⟩⟩ := hboth
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l1, Fin.natAdd N l2}
    have heA := and_true_s hAO he hande se (wv_of_PO hAO hpe1 (A := A) (by simp [A]))
      (wv_of_LO hAO hl2 (A := A) (by simp [A]))
    have hbA := and_true_s hAO hb handb sb (wv_of_LO hAO hl1 (A := A) (by simp [A]))
      (orReach_wv hAO _ hd2e heA)
    have haA := and_true_s hAO ha hand sa (wv_of_PO hAO hpu (A := A) (by simp [A]))
      (orReach_wv hAO _ hvb hbA)
    obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
    have hpe : p' = p := by
      rcases hp' with h | h | h
      · exact Fin.castAdd_injective N N h
      · exact absurd h (castAdd_ne_natAdd p' l1)
      · exact absurd h (castAdd_ne_natAdd p' l2)
    subst hpe
    rcases hl' with h | h | h
    · exact absurd h.symm (castAdd_ne_natAdd p' l')
    · exact hn1 ((Fin.natAdd_injective N N h) ▸ hI)
    · exact hn2 ((Fin.natAdd_injective N N h) ▸ hI)
  have hpts : (∀ p1 ∈ PO N C u, I p1 l) ∨ (∀ p2 ∈ PO N C e1, I p2 l) := by
    by_contra hboth; push Not at hboth
    obtain ⟨⟨p1, hp1, hn1⟩, ⟨p2, hp2, hn2⟩⟩ := hboth
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p1, Fin.castAdd N p2, Fin.natAdd N l}
    have heA := and_true_s hAO he hande se (wv_of_PO hAO hp2 (A := A) (by simp [A]))
      (wv_of_LO hAO hle2 (A := A) (by simp [A]))
    have hbA := and_true_s hAO hb handb sb (wv_of_LO hAO hld1 (A := A) (by simp [A]))
      (orReach_wv hAO _ hd2e heA)
    have haA := and_true_s hAO ha hand sa (wv_of_PO hAO hp1 (A := A) (by simp [A]))
      (orReach_wv hAO _ hvb hbA)
    obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
    have hle : l' = l := by
      rcases hl' with h | h | h
      · exact absurd h.symm (castAdd_ne_natAdd p1 l')
      · exact absurd h.symm (castAdd_ne_natAdd p2 l')
      · exact Fin.natAdd_injective N N h
    subst hle
    rcases hp' with h | h | h
    · exact hn1 ((Fin.castAdd_injective N N h) ▸ hI)
    · exact hn2 ((Fin.castAdd_injective N N h) ▸ hI)
    · exact absurd h (castAdd_ne_natAdd p' l')
  have hcase_ii : PO N C e1 = {p} → LO N C d1 = {l} → ∃ j < C.gates.length, gateCov N I C j p l := by
    intro hpe1_eq hld1_eq
    by_cases hle2_near : ((LO N C e2).filter fun l' => ¬ I p l').card ≤ 1
    · by_cases hle2_4 : 4 ≤ (LO N C e2).card
      · exact cover_near_LO hAO hle2 hle2_near hle2_4
      · have hle2_le : (LO N C e2).card ≤ 3 := by omega
        exact ⟨e, he, Or.inr (Or.inr (Or.inl ⟨hande, se, hpe1_eq, hle2, hle2_le⟩))⟩
    · obtain ⟨la, hla, lb, hlb, hlab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((LO N C e2).filter fun l' => ¬ I p l').card)
      obtain ⟨hla_in, hla_ni⟩ := Finset.mem_filter.mp hla
      obtain ⟨hlb_in, hlb_ni⟩ := Finset.mem_filter.mp hlb
      have hpe_b2 : p ∈ BadP2 N I C (N + N + e) := mfu_mpr ⟨la, lb, hlab, hla_ni, hlb_ni,
        and_true_s hAO he hande se (wv_of_PO hAO hpe1 (by simp)) (wv_of_LO hAO hla_in (by simp)),
        and_true_s hAO he hande se (wv_of_PO hAO hpe1 (by simp)) (wv_of_LO hAO hlb_in (by simp))⟩
      have hsub_b2 : BadP2 N I C (N + N + e) ⊆ BadP2 N I C d2 :=
        orReach_sub_F (BadP2 N I C) (or_mono_BadP2 hAO) hd2e
      by_cases hbp2_sub : ∀ p' ∈ BadP2 N I C d2, I p' l
      · by_cases hbe2 : 2 ≤ (BadP2 N I C (N + N + e)).card
        · exact ⟨e, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hande, hbe2, fun p' hp' => hbp2_sub p' (hsub_b2 hp'), se, hpe1,
               by change (PO N C e1).card ≤ 3; rw [hpe1_eq]; simp⟩))))))))))))))))))⟩
        · by_cases hbd2 : 2 ≤ (BadP2 N I C d2).card
          · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
              or_walk_drop hAO (BadP2 N I C) (or_mono_BadP2 hAO) 1 hd2e (by omega) (by omega) hpe_b2
            exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hor, by omega, fun p' hp' => hbp2_sub p' (hwsub hp'), s',
               card_eq_one_of_mem_le hyps hslo⟩))))))))))⟩
          · have hbd2_eq : BadP2 N I C d2 = {p} := card_eq_one_of_mem_le (hsub_b2 hpe_b2) (by omega)
            exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨handb, ⟨1 - sb.val, by omega⟩, hbd2_eq,
               by have h1s : 1 - (⟨1 - sb.val, by omega⟩ : Fin 2).val = sb.val := (by simp; omega); rw [h1s]; exact hld1_eq⟩)))))))))⟩
      · push Not at hbp2_sub
        obtain ⟨p2, hp2_mem, hp2_ni⟩ := hbp2_sub
        obtain ⟨l2a, l2b, hl2ab, hl2a_ni, hl2b_ni, hvd2a, hvd2b⟩ := mf_mp hp2_mem
        by_cases hpu_near : ((PO N C u).filter fun p' => ¬ I p' l).card ≤ 1
        · by_cases hpu_4 : 4 ≤ (PO N C u).card
          · exact cover_near_PO hAO hpu hpu_near hpu_4
          · have hlb_tw : l ∈ BadLT N I C (N + N + b) := mfu_mpr
              ⟨p2, l2a, l2b, hl2ab, hp2_ni, hl2a_ni, hl2b_ni,
               and_true_s hAO hb handb sb (wv_of_LO hAO hld1 (by simp))
                 (wv_of_setInput_sub hAO (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp) hvd2a),
               and_true_s hAO hb handb sb (wv_of_LO hAO hld1 (by simp))
                 (wv_of_setInput_sub hAO (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp) hvd2b)⟩
            have hsub_tw : BadLT N I C (N + N + b) ⊆ BadLT N I C v :=
              orReach_sub_F (BadLT N I C) (or_mono_BadLT hAO) hvb
            have hok_v := badLT_ok_of_top hAO hfun ha htop hand sa hpu Relation.ReflTransGen.refl
            have hok_b := badLT_ok_of_top hAO hfun ha htop hand sa hpu hvb
            by_cases htb : 2 ≤ (BadLT N I C (N + N + b)).card
            · exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨handb, htb, hok_b, sb, hld1_eq⟩)))))))))))))))))))⟩
            · by_cases htv : 2 ≤ (BadLT N I C v).card
              · obtain ⟨j, hj, s', hvj, hor, hhi, hwsub, hslo, hyls⟩ :=
                  or_walk_drop hAO (BadLT N I C) (or_mono_BadLT hAO) 1 hvb (by omega) (by omega) hlb_tw
                have hok_j := badLT_ok_of_top hAO hfun ha htop hand sa hpu hvj
                exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨hor, by omega, hok_j, s', card_eq_one_of_mem_le hyls hslo⟩)))))))))))⟩
              · have hpu_le : (PO N C u).card ≤ 3 := by omega
                have htv_eq : BadLT N I C v = {l} := card_eq_one_of_mem_le (hsub_tw hlb_tw) (by omega)
                exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨hand, sa, hpu, hpu_le, htv_eq⟩))))))))))⟩
        · exfalso
          obtain ⟨pa, hpa, pb', hpb', hpab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((PO N C u).filter fun p' => ¬ I p' l).card)
          obtain ⟨hpa_in, hpa_ni⟩ := Finset.mem_filter.mp hpa
          obtain ⟨hpb_in, hpb_ni⟩ := Finset.mem_filter.mp hpb'
          have hpair : ∀ px lx : Fin N, px ∈ PO N C u → ¬ I px l → ¬ I p2 lx →
              wv C (N + N) (setInput {Fin.castAdd N p2, Fin.natAdd N lx}) d2 = true → I px lx := by
            intro px lx hpx hpx_ni hp2_lx hwd2
            set A : Finset (Fin (N + N)) := {Fin.castAdd N px, Fin.castAdd N p2, Fin.natAdd N l, Fin.natAdd N lx}
            have hbA := and_true_s hAO hb handb sb (wv_of_LO hAO hld1 (A := A) (by simp [A]))
              (wv_of_setInput_sub hAO (B := A) (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [A]) hwd2)
            have haA := and_true_s hAO ha hand sa (wv_of_PO hAO hpx (A := A) (by simp [A]))
              (orReach_wv hAO _ hvb hbA)
            obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
            simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
            rcases hp' with h | h | h | h
            · have := Fin.castAdd_injective N N h; subst this
              rcases hl' with h2 | h2 | h2 | h2
              · exact absurd h2.symm (castAdd_ne_natAdd p' l')
              · exact absurd h2.symm (castAdd_ne_natAdd p2 l')
              · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hpx_ni
              · exact (Fin.natAdd_injective N N h2) ▸ hI
            · have := Fin.castAdd_injective N N h; subst this
              rcases hl' with h2 | h2 | h2 | h2
              · exact absurd h2.symm (castAdd_ne_natAdd px l')
              · exact absurd h2.symm (castAdd_ne_natAdd p' l')
              · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hp2_ni
              · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hp2_lx
            · exact absurd h (castAdd_ne_natAdd p' l)
            · exact absurd h (castAdd_ne_natAdd p' lx)
          exact no_c4 huniq hpab hl2ab
            (hpair pa l2a hpa_in hpa_ni hl2a_ni hvd2a)
            (hpair pb' l2a hpb_in hpb_ni hl2a_ni hvd2a)
            (hpair pa l2b hpa_in hpa_ni hl2b_ni hvd2b)
            (hpair pb' l2b hpb_in hpb_ni hl2b_ni hvd2b)
  have hL_or : (∃ j < C.gates.length, gateCov N I C j p l) ∨ LO N C d1 = {l} ∨ LO N C e2 = {l} := by
    rcases hlines with hd1_sub | he2_sub
    · by_cases h2 : 2 ≤ (LO N C d1).card
      · exact Or.inl (cover_LO_star hAO hld1 hd1_sub h2)
      · exact Or.inr (Or.inl (card_eq_one_of_mem_le hld1 (by omega)))
    · by_cases h2 : 2 ≤ (LO N C e2).card
      · exact Or.inl (cover_LO_star hAO hle2 he2_sub h2)
      · exact Or.inr (Or.inr (card_eq_one_of_mem_le hle2 (by omega)))
  have hP_or : (∃ j < C.gates.length, gateCov N I C j p l) ∨ PO N C u = {p} ∨ PO N C e1 = {p} := by
    rcases hpts with hu_sub | he1_sub
    · by_cases h2 : 2 ≤ (PO N C u).card
      · exact Or.inl (cover_PO_star hAO hpu hu_sub h2)
      · exact Or.inr (Or.inl (card_eq_one_of_mem_le hpu (by omega)))
    · by_cases h2 : 2 ≤ (PO N C e1).card
      · exact Or.inl (cover_PO_star hAO hpe1 he1_sub h2)
      · exact Or.inr (Or.inr (card_eq_one_of_mem_le hpe1 (by omega)))
  rcases hL_or with hcov | hld1_eq | hle2_eq
  · exact hcov
  · rcases hP_or with hcov | hpu_eq | hpe1_eq
    · exact hcov
    · by_cases he1_sub : ∀ p' ∈ PO N C e1, I p' l
      · by_cases he1_2 : 2 ≤ (PO N C e1).card
        · exact cover_PO_star hAO hpe1 he1_sub he1_2
        · exact hcase_ii (card_eq_one_of_mem_le hpe1 (by omega)) hld1_eq
      · push Not at he1_sub
        obtain ⟨pb, hpb_mem, hpb_ni⟩ := he1_sub
        have hlb_bad : l ∈ BadL N I C (N + N + b) := mfu_mpr ⟨pb, hpb_ni,
          and_true_s hAO hb handb sb (wv_of_LO hAO hld1 (by simp))
            (orReach_wv hAO _ hd2e (and_true_s hAO he hande se
              (wv_of_PO hAO hpb_mem (by simp)) (wv_of_LO hAO hle2 (by simp))))⟩
        have hBadV_sub := badL_sub_of_top hAO hfun ha htop hand sa hpu
        have hBadB_sub : BadL N I C (N + N + b) ⊆ BadL N I C v :=
          orReach_sub_F (BadL N I C) (or_mono_BadL hAO) hvb
        by_cases hbb : 2 ≤ (BadL N I C (N + N + b)).card
        · exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨handb, hbb, fun l' hl' => hBadV_sub l' (hBadB_sub hl'),
               sb, hld1, by change (LO N C d1).card ≤ 3; rw [hld1_eq]; simp⟩)))))))))))))⟩
        · by_cases hbv : 2 ≤ (BadL N I C v).card
          · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
              or_walk_drop hAO (BadL N I C) (or_mono_BadL hAO) 1 hvb (by omega) (by omega) hlb_bad
            exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hor, by omega, fun l' hl' => hBadV_sub l' (hwsub hl'), s',
               card_eq_one_of_mem_le hyls hslo⟩)))))))⟩
          · have hbv_eq : BadL N I C v = {l} := card_eq_one_of_mem_le (hBadB_sub hlb_bad) (by omega)
            exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hand, sa, hpu_eq, hbv_eq⟩))))))⟩
    · exact hcase_ii hpe1_eq hld1_eq
  · rcases hP_or with hcov | hpu_eq | hpe1_eq
    · exact hcov
    · by_cases he1_near : ((PO N C e1).filter fun p' => ¬ I p' l).card ≤ 1
      · by_cases he1_4 : 4 ≤ (PO N C e1).card
        · exact cover_near_PO hAO hpe1 he1_near he1_4
        · have hpe1_le : (PO N C e1).card ≤ 3 := by omega
          exact ⟨e, he, Or.inr (Or.inr (Or.inr (Or.inl ⟨hande, se, hpe1, hpe1_le, hle2_eq⟩)))⟩
      · obtain ⟨pa, hpa, pb', hpb', hpab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((PO N C e1).filter fun p' => ¬ I p' l).card)
        obtain ⟨hpa_in, hpa_ni⟩ := Finset.mem_filter.mp hpa
        obtain ⟨hpb_in, hpb_ni⟩ := Finset.mem_filter.mp hpb'
        have hle_b2 : l ∈ BadL2 N I C (N + N + e) := mfu_mpr ⟨pa, pb', hpab, hpa_ni, hpb_ni,
          and_true_s hAO he hande se (wv_of_PO hAO hpa_in (by simp)) (wv_of_LO hAO hle2 (by simp)),
          and_true_s hAO he hande se (wv_of_PO hAO hpb_in (by simp)) (wv_of_LO hAO hle2 (by simp))⟩
        have hsub_ed2 : BadL2 N I C (N + N + e) ⊆ BadL2 N I C d2 :=
          orReach_sub_F (BadL2 N I C) (or_mono_BadL2 hAO) hd2e
        have hlb_b2 : l ∈ BadL2 N I C (N + N + b) := by
          obtain ⟨p1, p2, hne, h1, h2, hv1, hv2⟩ := mf_mp (hsub_ed2 hle_b2)
          exact mfu_mpr ⟨p1, p2, hne, h1, h2,
            and_true_s hAO hb handb sb (wv_of_LO hAO hld1 (by simp)) hv1,
            and_true_s hAO hb handb sb (wv_of_LO hAO hld1 (by simp)) hv2⟩
        have hsub_bv : BadL2 N I C (N + N + b) ⊆ BadL2 N I C v :=
          orReach_sub_F (BadL2 N I C) (or_mono_BadL2 hAO) hvb
        have hBadV2_sub : ∀ l' ∈ BadL2 N I C v, I p l' := fun l' hl' =>
          badL_sub_of_top hAO hfun ha htop hand sa hpu l' (badL2_sub_badL hl')
        by_cases hbv2 : (BadL2 N I C v).card ≤ 1
        · have hbv2_eq : BadL2 N I C v = {l} := card_eq_one_of_mem_le (hsub_bv hlb_b2) hbv2
          exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hand, sa, hpu_eq, hbv2_eq⟩))))))))⟩
        · by_cases hbb2 : (BadL2 N I C (N + N + b)).card ≤ 1
          · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
              or_walk_drop hAO (BadL2 N I C) (or_mono_BadL2 hAO) 1 hvb (by omega) hbb2 hlb_b2
            exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hor, by omega, fun l' hl' => hBadV2_sub l' (hwsub hl'), s',
               card_eq_one_of_mem_le hyls hslo⟩)))))))))⟩
          · by_cases hd1_near : ((LO N C d1).filter fun l' => ¬ I p l').card ≤ 1
            · by_cases hd1_4 : 4 ≤ (LO N C d1).card
              · exact cover_near_LO hAO hld1 hd1_near hd1_4
              · have hd1_le : (LO N C d1).card ≤ 3 := by omega
                exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨handb, by omega, fun l' hl' => hBadV2_sub l' (hsub_bv hl'),
                     sb, hld1, hd1_le⟩)))))))))))))))))⟩
            · obtain ⟨la, hla, lb', hlb', hlab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((LO N C d1).filter fun l' => ¬ I p l').card)
              obtain ⟨hla_in, hla_ni⟩ := Finset.mem_filter.mp hla
              obtain ⟨hlb_in, hlb_ni⟩ := Finset.mem_filter.mp hlb'
              have hd2_sub : ∀ l' ∈ BadL2 N I C d2, I p l' := by
                intro l' hl'
                by_contra hni_pl'
                obtain ⟨p1, p2, hp12, hp1_ni, hp2_ni, hv1, hv2⟩ := mf_mp hl'
                have hpair : ∀ px lx : Fin N, lx ∈ LO N C d1 → ¬ I p lx → ¬ I px l' →
                    wv C (N + N) (setInput {Fin.castAdd N px, Fin.natAdd N l'}) d2 = true → I px lx := by
                  intro px lx hlx hplx hpxl' hwd2
                  set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.castAdd N px, Fin.natAdd N l', Fin.natAdd N lx}
                  have hbA := and_true_s hAO hb handb sb (wv_of_LO hAO hlx (A := A) (by simp [A]))
                    (wv_of_setInput_sub hAO (B := A) (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [A]) hwd2)
                  have haA := and_true_s hAO ha hand sa (wv_of_PO hAO hpu (A := A) (by simp [A]))
                    (orReach_wv hAO _ hvb hbA)
                  obtain ⟨p'', l'', hI, hp'', hl''⟩ := top_sound hAO hfun htop haA
                  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl''
                  rcases hp'' with h | h | h | h
                  · have := Fin.castAdd_injective N N h; subst this
                    rcases hl'' with h2 | h2 | h2 | h2
                    · exact absurd h2.symm (castAdd_ne_natAdd p'' l'')
                    · exact absurd h2.symm (castAdd_ne_natAdd px l'')
                    · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hni_pl'
                    · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hplx
                  · have := Fin.castAdd_injective N N h; subst this
                    rcases hl'' with h2 | h2 | h2 | h2
                    · exact absurd h2.symm (castAdd_ne_natAdd p l'')
                    · exact absurd h2.symm (castAdd_ne_natAdd p'' l'')
                    · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hpxl'
                    · exact (Fin.natAdd_injective N N h2) ▸ hI
                  · exact absurd h (castAdd_ne_natAdd p'' l')
                  · exact absurd h (castAdd_ne_natAdd p'' lx)
                exact no_c4 huniq hp12 hlab
                  (hpair p1 la hla_in hla_ni hp1_ni hv1)
                  (hpair p2 la hla_in hla_ni hp2_ni hv2)
                  (hpair p1 lb' hlb_in hlb_ni hp1_ni hv1)
                  (hpair p2 lb' hlb_in hlb_ni hp2_ni hv2)
              have hb_sub_d2 : BadL2 N I C (N + N + b) ⊆ BadL2 N I C d2 := by
                intro l' hl'
                obtain ⟨p1, p2, hne, h1, h2, hv1, hv2⟩ := mf_mp hl'
                obtain ⟨_, hinp⟩ := gate_info hAO hb
                rw [wv_gate C (N + N) _ hAO.2.1 b hb, handb, hinp] at hv1 hv2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true, Bool.and_eq_true] at hv1 hv2
                refine mfu_mpr ⟨p1, p2, hne, h1, h2, ?_, ?_⟩
                · rcases (by omega : sb.val = 0 ∨ sb.val = 1) with hs | hs
                  · simpa [d2, hs] using hv1.2
                  · simpa [d2, hs] using hv1.1
                · rcases (by omega : sb.val = 0 ∨ sb.val = 1) with hs | hs
                  · simpa [d2, hs] using hv2.2
                  · simpa [d2, hs] using hv2.1
              have hd2_2 : 2 ≤ (BadL2 N I C d2).card := (by omega : 2 ≤ (BadL2 N I C (N + N + b)).card).trans (Finset.card_le_card hb_sub_d2)
              by_cases he_2 : 2 ≤ (BadL2 N I C (N + N + e)).card
              · exact ⟨e, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨hande, he_2, fun l' hl' => hd2_sub l' (hsub_ed2 hl'),
                     ⟨1 - se.val, by omega⟩, hle2, by change (LO N C e2).card ≤ 3; rw [hle2_eq]; simp⟩)))))))))))))))))⟩
              · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
                  or_walk_drop hAO (BadL2 N I C) (or_mono_BadL2 hAO) 1 hd2e (by omega) (by omega) hle_b2
                exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨hor, by omega, fun l' hl' => hd2_sub l' (hwsub hl'), s',
                   card_eq_one_of_mem_le hyls hslo⟩)))))))))⟩
    · exact ⟨e, he, Or.inr (Or.inr (Or.inl ⟨hande, se, hpe1_eq, hle2, by change (LO N C e2).card ≤ 3; rw [hle2_eq]; simp⟩))⟩

theorem cover_type2d2 {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (sa : Fin 2)
    (hlv : l ∈ LO N C ((gateAt C a).inputs.getD (1 - sa.val) 0))
    {b : ℕ} (hb : b < C.gates.length) (hub : OrReach (N + N) C ((gateAt C a).inputs.getD sa.val 0) (N + N + b))
    (handb : (gateAt C b).op = GateOp.and) (sb : Fin 2)
    (hpd1 : p ∈ PO N C ((gateAt C b).inputs.getD sb.val 0))
    {e : ℕ} (he : e < C.gates.length) (hd2e : OrReach (N + N) C ((gateAt C b).inputs.getD (1 - sb.val) 0) (N + N + e))
    (hande : (gateAt C e).op = GateOp.and) (se : Fin 2)
    (hpe1 : p ∈ PO N C ((gateAt C e).inputs.getD se.val 0))
    (hle2 : l ∈ LO N C ((gateAt C e).inputs.getD (1 - se.val) 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set u := (gateAt C a).inputs.getD sa.val 0
  set v := (gateAt C a).inputs.getD (1 - sa.val) 0
  set d1 := (gateAt C b).inputs.getD sb.val 0
  set d2 := (gateAt C b).inputs.getD (1 - sb.val) 0
  set e1 := (gateAt C e).inputs.getD se.val 0
  set e2 := (gateAt C e).inputs.getD (1 - se.val) 0
  have hpts : (∀ p1 ∈ PO N C d1, I p1 l) ∨ (∀ p2 ∈ PO N C e1, I p2 l) := by
    by_contra hboth; push Not at hboth
    obtain ⟨⟨p1, hp1, hn1⟩, ⟨p2, hp2, hn2⟩⟩ := hboth
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p1, Fin.castAdd N p2, Fin.natAdd N l}
    have heA := and_true_s hAO he hande se (wv_of_PO hAO hp2 (A := A) (by simp [A]))
      (wv_of_LO hAO hle2 (A := A) (by simp [A]))
    have hbA := and_true_s hAO hb handb sb (wv_of_PO hAO hp1 (A := A) (by simp [A]))
      (orReach_wv hAO _ hd2e heA)
    have haA := and_true_s hAO ha hand sa (orReach_wv hAO _ hub hbA)
      (wv_of_LO hAO hlv (A := A) (by simp [A]))
    obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
    have hle : l' = l := by
      rcases hl' with h | h | h
      · exact absurd h.symm (castAdd_ne_natAdd p1 l')
      · exact absurd h.symm (castAdd_ne_natAdd p2 l')
      · exact Fin.natAdd_injective N N h
    subst hle
    rcases hp' with h | h | h
    · exact hn1 ((Fin.castAdd_injective N N h) ▸ hI)
    · exact hn2 ((Fin.castAdd_injective N N h) ▸ hI)
    · exact absurd h (castAdd_ne_natAdd p' l')
  have hlines : (∀ l1 ∈ LO N C v, I p l1) ∨ (∀ l2 ∈ LO N C e2, I p l2) := by
    by_contra hboth; push Not at hboth
    obtain ⟨⟨l1, hl1, hn1⟩, ⟨l2, hl2, hn2⟩⟩ := hboth
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l1, Fin.natAdd N l2}
    have heA := and_true_s hAO he hande se (wv_of_PO hAO hpe1 (A := A) (by simp [A]))
      (wv_of_LO hAO hl2 (A := A) (by simp [A]))
    have hbA := and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (A := A) (by simp [A]))
      (orReach_wv hAO _ hd2e heA)
    have haA := and_true_s hAO ha hand sa (orReach_wv hAO _ hub hbA)
      (wv_of_LO hAO hl1 (A := A) (by simp [A]))
    obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
    have hpe : p' = p := by
      rcases hp' with h | h | h
      · exact Fin.castAdd_injective N N h
      · exact absurd h (castAdd_ne_natAdd p' l1)
      · exact absurd h (castAdd_ne_natAdd p' l2)
    subst hpe
    rcases hl' with h | h | h
    · exact absurd h.symm (castAdd_ne_natAdd p' l')
    · exact hn1 ((Fin.natAdd_injective N N h) ▸ hI)
    · exact hn2 ((Fin.natAdd_injective N N h) ▸ hI)
  have hcase_ii : LO N C e2 = {l} → PO N C d1 = {p} → ∃ j < C.gates.length, gateCov N I C j p l := by
    intro hle2_eq hpd1_eq
    by_cases hpe1_near : ((PO N C e1).filter fun p' => ¬ I p' l).card ≤ 1
    · by_cases hpe1_4 : 4 ≤ (PO N C e1).card
      · exact cover_near_PO hAO hpe1 hpe1_near hpe1_4
      · have hpe1_le : (PO N C e1).card ≤ 3 := by omega
        exact ⟨e, he, Or.inr (Or.inr (Or.inr (Or.inl ⟨hande, se, hpe1, hpe1_le, hle2_eq⟩)))⟩
    · obtain ⟨pa, hpa, pb', hpb', hpab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((PO N C e1).filter fun p' => ¬ I p' l).card)
      obtain ⟨hpa_in, hpa_ni⟩ := Finset.mem_filter.mp hpa
      obtain ⟨hpb_in, hpb_ni⟩ := Finset.mem_filter.mp hpb'
      have hle_b2 : l ∈ BadL2 N I C (N + N + e) := mfu_mpr ⟨pa, pb', hpab, hpa_ni, hpb_ni,
        and_true_s hAO he hande se (wv_of_PO hAO hpa_in (by simp)) (wv_of_LO hAO hle2 (by simp)),
        and_true_s hAO he hande se (wv_of_PO hAO hpb_in (by simp)) (wv_of_LO hAO hle2 (by simp))⟩
      have hsub_b2 : BadL2 N I C (N + N + e) ⊆ BadL2 N I C d2 :=
        orReach_sub_F (BadL2 N I C) (or_mono_BadL2 hAO) hd2e
      by_cases hbl2_sub : ∀ l' ∈ BadL2 N I C d2, I p l'
      · by_cases hbe2 : 2 ≤ (BadL2 N I C (N + N + e)).card
        · exact ⟨e, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hande, hbe2, fun l' hl' => hbl2_sub l' (hsub_b2 hl'), ⟨1 - se.val, by omega⟩,
               hle2, by change (LO N C e2).card ≤ 3; rw [hle2_eq]; simp⟩)))))))))))))))))⟩
        · by_cases hbd2 : 2 ≤ (BadL2 N I C d2).card
          · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
              or_walk_drop hAO (BadL2 N I C) (or_mono_BadL2 hAO) 1 hd2e (by omega) (by omega) hle_b2
            exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hor, by omega, fun l' hl' => hbl2_sub l' (hwsub hl'), s',
               card_eq_one_of_mem_le hyls hslo⟩)))))))))⟩
          · have hbd2_eq : BadL2 N I C d2 = {l} := card_eq_one_of_mem_le (hsub_b2 hle_b2) (by omega)
            exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨handb, sb, hpd1_eq, hbd2_eq⟩))))))))⟩
      · push Not at hbl2_sub
        obtain ⟨l2, hl2_mem, hl2_ni⟩ := hbl2_sub
        obtain ⟨p2a, p2b, hp2ab, hp2a_ni, hp2b_ni, hvd2a, hvd2b⟩ := mf_mp hl2_mem
        by_cases hlv_near : ((LO N C v).filter fun l' => ¬ I p l').card ≤ 1
        · by_cases hlv_4 : 4 ≤ (LO N C v).card
          · exact cover_near_LO hAO hlv hlv_near hlv_4
          · have hpb_tw : p ∈ BadPT N I C (N + N + b) := mfu_mpr
              ⟨l2, p2a, p2b, hp2ab, hl2_ni, hp2a_ni, hp2b_ni,
               and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (by simp))
                 (wv_of_setInput_sub hAO (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp) hvd2a),
               and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (by simp))
                 (wv_of_setInput_sub hAO (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp) hvd2b)⟩
            have hsub_tw : BadPT N I C (N + N + b) ⊆ BadPT N I C u :=
              orReach_sub_F (BadPT N I C) (or_mono_BadPT hAO) hub
            have hok_u := badPT_ok_of_top hAO hfun ha htop hand sa hlv Relation.ReflTransGen.refl
            have hok_b := badPT_ok_of_top hAO hfun ha htop hand sa hlv hub
            by_cases htb : 2 ≤ (BadPT N I C (N + N + b)).card
            · exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨handb, htb, hok_b, sb, hpd1_eq⟩)))))))))))))))))))⟩
            · by_cases htu : 2 ≤ (BadPT N I C u).card
              · obtain ⟨j, hj, s', huj, hor, hhi, hwsub, hslo, hyps⟩ :=
                  or_walk_drop hAO (BadPT N I C) (or_mono_BadPT hAO) 1 hub (by omega) (by omega) hpb_tw
                have hok_j := badPT_ok_of_top hAO hfun ha htop hand sa hlv huj
                exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨hor, by omega, hok_j, s', card_eq_one_of_mem_le hyps hslo⟩)))))))))))⟩
              · have htu_eq : BadPT N I C u = {p} := card_eq_one_of_mem_le (hsub_tw hpb_tw) (by omega)
                have hlv_le : (LO N C v).card ≤ 3 := by omega
                exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨hand, sa, htu_eq, hlv, hlv_le⟩)))))))))))⟩
        · exfalso
          obtain ⟨la, hla, lb', hlb', hlab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((LO N C v).filter fun l' => ¬ I p l').card)
          obtain ⟨hla_in, hla_ni⟩ := Finset.mem_filter.mp hla
          obtain ⟨hlb_in, hlb_ni⟩ := Finset.mem_filter.mp hlb'
          have hpair : ∀ px lx : Fin N, lx ∈ LO N C v → ¬ I p lx → ¬ I px l2 →
              wv C (N + N) (setInput {Fin.castAdd N px, Fin.natAdd N l2}) d2 = true → I px lx := by
            intro px lx hlx hplx hpxl2 hwd2
            set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.castAdd N px, Fin.natAdd N lx, Fin.natAdd N l2}
            have hbA := and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (A := A) (by simp [A]))
              (wv_of_setInput_sub hAO (B := A) (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [A]) hwd2)
            have haA := and_true_s hAO ha hand sa (orReach_wv hAO _ hub hbA)
              (wv_of_LO hAO hlx (A := A) (by simp [A]))
            obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop haA
            simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
            rcases hp' with h | h | h | h
            · have := Fin.castAdd_injective N N h; subst this
              rcases hl' with h2 | h2 | h2 | h2
              · exact absurd h2.symm (castAdd_ne_natAdd p' l')
              · exact absurd h2.symm (castAdd_ne_natAdd px l')
              · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hplx
              · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hl2_ni
            · have := Fin.castAdd_injective N N h; subst this
              rcases hl' with h2 | h2 | h2 | h2
              · exact absurd h2.symm (castAdd_ne_natAdd p l')
              · exact absurd h2.symm (castAdd_ne_natAdd p' l')
              · exact (Fin.natAdd_injective N N h2) ▸ hI
              · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hpxl2
            · exact absurd h (castAdd_ne_natAdd p' lx)
            · exact absurd h (castAdd_ne_natAdd p' l2)
          exact no_c4 huniq hp2ab hlab
            (hpair p2a la hla_in hla_ni hp2a_ni hvd2a)
            (hpair p2b la hla_in hla_ni hp2b_ni hvd2b)
            (hpair p2a lb' hlb_in hlb_ni hp2a_ni hvd2a)
            (hpair p2b lb' hlb_in hlb_ni hp2b_ni hvd2b)
  have hP_or : (∃ j < C.gates.length, gateCov N I C j p l) ∨ PO N C d1 = {p} ∨ PO N C e1 = {p} := by
    rcases hpts with hd1_sub | he1_sub
    · by_cases h2 : 2 ≤ (PO N C d1).card
      · exact Or.inl (cover_PO_star hAO hpd1 hd1_sub h2)
      · exact Or.inr (Or.inl (card_eq_one_of_mem_le hpd1 (by omega)))
    · by_cases h2 : 2 ≤ (PO N C e1).card
      · exact Or.inl (cover_PO_star hAO hpe1 he1_sub h2)
      · exact Or.inr (Or.inr (card_eq_one_of_mem_le hpe1 (by omega)))
  have hL_or : (∃ j < C.gates.length, gateCov N I C j p l) ∨ LO N C v = {l} ∨ LO N C e2 = {l} := by
    rcases hlines with hv_sub | he2_sub
    · by_cases h2 : 2 ≤ (LO N C v).card
      · exact Or.inl (cover_LO_star hAO hlv hv_sub h2)
      · exact Or.inr (Or.inl (card_eq_one_of_mem_le hlv (by omega)))
    · by_cases h2 : 2 ≤ (LO N C e2).card
      · exact Or.inl (cover_LO_star hAO hle2 he2_sub h2)
      · exact Or.inr (Or.inr (card_eq_one_of_mem_le hle2 (by omega)))
  rcases hP_or with hcov | hpd1_eq | hpe1_eq
  · exact hcov
  · rcases hL_or with hcov | hlv_eq | hle2_eq
    · exact hcov
    · by_cases he2_sub : ∀ l' ∈ LO N C e2, I p l'
      · by_cases he2_2 : 2 ≤ (LO N C e2).card
        · exact cover_LO_star hAO hle2 he2_sub he2_2
        · exact hcase_ii (card_eq_one_of_mem_le hle2 (by omega)) hpd1_eq
      · push Not at he2_sub
        obtain ⟨lb, hlb_mem, hlb_ni⟩ := he2_sub
        have hpb_bad : p ∈ BadP N I C (N + N + b) := mfu_mpr ⟨lb, hlb_ni,
          and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (by simp))
            (orReach_wv hAO _ hd2e (and_true_s hAO he hande se
              (wv_of_PO hAO hpe1 (by simp)) (wv_of_LO hAO hlb_mem (by simp))))⟩
        have hBadU_sub := badP_sub_of_top hAO hfun ha htop hand sa hlv
        have hBadB_sub : BadP N I C (N + N + b) ⊆ BadP N I C u :=
          orReach_sub_F (BadP N I C) (or_mono_BadP hAO) hub
        by_cases hbb : 2 ≤ (BadP N I C (N + N + b)).card
        · exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨handb, hbb, fun p' hp' => hBadU_sub p' (hBadB_sub hp'),
               sb, hpd1, by change (PO N C d1).card ≤ 3; rw [hpd1_eq]; simp⟩))))))))))))))⟩
        · by_cases hbu : 2 ≤ (BadP N I C u).card
          · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
              or_walk_drop hAO (BadP N I C) (or_mono_BadP hAO) 1 hub (by omega) (by omega) hpb_bad
            exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hor, by omega, fun p' hp' => hBadU_sub p' (hwsub hp'), s',
               card_eq_one_of_mem_le hyps hslo⟩))))))))⟩
          · have hbu_eq : BadP N I C u = {p} := card_eq_one_of_mem_le (hBadB_sub hpb_bad) (by omega)
            exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hand, sa, hbu_eq, hlv_eq⟩)))))))⟩
    · exact hcase_ii hle2_eq hpd1_eq
  · rcases hL_or with hcov | hlv_eq | hle2_eq
    · exact hcov
    · by_cases he2_near : ((LO N C e2).filter fun l' => ¬ I p l').card ≤ 1
      · by_cases he2_4 : 4 ≤ (LO N C e2).card
        · exact cover_near_LO hAO hle2 he2_near he2_4
        · have hle2_le : (LO N C e2).card ≤ 3 := by omega
          exact ⟨e, he, Or.inr (Or.inr (Or.inl ⟨hande, se, hpe1_eq, hle2, hle2_le⟩))⟩
      · obtain ⟨la, hla, lb', hlb', hlab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((LO N C e2).filter fun l' => ¬ I p l').card)
        obtain ⟨hla_in, hla_ni⟩ := Finset.mem_filter.mp hla
        obtain ⟨hlb_in, hlb_ni⟩ := Finset.mem_filter.mp hlb'
        have hpe_b2 : p ∈ BadP2 N I C (N + N + e) := mfu_mpr ⟨la, lb', hlab, hla_ni, hlb_ni,
          and_true_s hAO he hande se (wv_of_PO hAO hpe1 (by simp)) (wv_of_LO hAO hla_in (by simp)),
          and_true_s hAO he hande se (wv_of_PO hAO hpe1 (by simp)) (wv_of_LO hAO hlb_in (by simp))⟩
        have hsub_ed2 : BadP2 N I C (N + N + e) ⊆ BadP2 N I C d2 :=
          orReach_sub_F (BadP2 N I C) (or_mono_BadP2 hAO) hd2e
        have hpb_b2 : p ∈ BadP2 N I C (N + N + b) := by
          obtain ⟨l1, l2, hne, h1, h2, hv1, hv2⟩ := mf_mp (hsub_ed2 hpe_b2)
          exact mfu_mpr ⟨l1, l2, hne, h1, h2,
            and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (by simp)) hv1,
            and_true_s hAO hb handb sb (wv_of_PO hAO hpd1 (by simp)) hv2⟩
        have hsub_bu : BadP2 N I C (N + N + b) ⊆ BadP2 N I C u :=
          orReach_sub_F (BadP2 N I C) (or_mono_BadP2 hAO) hub
        have hBadU2_sub : ∀ p' ∈ BadP2 N I C u, I p' l := fun p' hp' =>
          badP_sub_of_top hAO hfun ha htop hand sa hlv p' (badP2_sub_badP hp')
        by_cases hbu2 : (BadP2 N I C u).card ≤ 1
        · have hbu2_eq : BadP2 N I C u = {p} := card_eq_one_of_mem_le (hsub_bu hpb_b2) hbu2
          exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hand, sa, hbu2_eq, hlv_eq⟩)))))))))⟩
        · by_cases hbb2 : (BadP2 N I C (N + N + b)).card ≤ 1
          · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
              or_walk_drop hAO (BadP2 N I C) (or_mono_BadP2 hAO) 1 hub (by omega) hbb2 hpb_b2
            exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hor, by omega, fun p' hp' => hBadU2_sub p' (hwsub hp'), s',
               card_eq_one_of_mem_le hyps hslo⟩))))))))))⟩
          · by_cases hd1_near : ((PO N C d1).filter fun p' => ¬ I p' l).card ≤ 1
            · by_cases hd1_4 : 4 ≤ (PO N C d1).card
              · exact cover_near_PO hAO hpd1 hd1_near hd1_4
              · have hd1_le : (PO N C d1).card ≤ 3 := by omega
                exact ⟨b, hb, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨handb, by omega, fun p' hp' => hBadU2_sub p' (hsub_bu hp'),
                     sb, hpd1, hd1_le⟩))))))))))))))))))⟩
            · obtain ⟨pa, hpa, pb', hpb', hpab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((PO N C d1).filter fun p' => ¬ I p' l).card)
              obtain ⟨hpa_in, hpa_ni⟩ := Finset.mem_filter.mp hpa
              obtain ⟨hpb_in, hpb_ni⟩ := Finset.mem_filter.mp hpb'
              have hd2_sub : ∀ p' ∈ BadP2 N I C d2, I p' l := by
                intro p' hp'
                by_contra hni_p'l
                obtain ⟨l1, l2, hl12, hl1_ni, hl2_ni, hv1, hv2⟩ := mf_mp hp'
                have hpair : ∀ px lx : Fin N, px ∈ PO N C d1 → ¬ I px l → ¬ I p' lx →
                    wv C (N + N) (setInput {Fin.castAdd N p', Fin.natAdd N lx}) d2 = true → I px lx := by
                  intro px lx hpx hpxl hp'lx hwd2
                  set A : Finset (Fin (N + N)) := {Fin.castAdd N p', Fin.castAdd N px, Fin.natAdd N l, Fin.natAdd N lx}
                  have hbA := and_true_s hAO hb handb sb (wv_of_PO hAO hpx (A := A) (by simp [A]))
                    (wv_of_setInput_sub hAO (B := A) (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [A]) hwd2)
                  have haA := and_true_s hAO ha hand sa (orReach_wv hAO _ hub hbA)
                    (wv_of_LO hAO hlv (A := A) (by simp [A]))
                  obtain ⟨p'', l'', hI, hp'', hl''⟩ := top_sound hAO hfun htop haA
                  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl''
                  rcases hl'' with h | h | h | h
                  · exact absurd h.symm (castAdd_ne_natAdd p' l'')
                  · exact absurd h.symm (castAdd_ne_natAdd px l'')
                  · have := Fin.natAdd_injective N N h; subst this
                    rcases hp'' with h2 | h2 | h2 | h2
                    · exact absurd ((Fin.castAdd_injective N N h2) ▸ hI) hni_p'l
                    · exact absurd ((Fin.castAdd_injective N N h2) ▸ hI) hpxl
                    · exact absurd h2 (castAdd_ne_natAdd p'' l'')
                    · exact absurd h2 (castAdd_ne_natAdd p'' lx)
                  · have := Fin.natAdd_injective N N h; subst this
                    rcases hp'' with h2 | h2 | h2 | h2
                    · exact absurd ((Fin.castAdd_injective N N h2) ▸ hI) hp'lx
                    · exact (Fin.castAdd_injective N N h2) ▸ hI
                    · exact absurd h2 (castAdd_ne_natAdd p'' l)
                    · exact absurd h2 (castAdd_ne_natAdd p'' l'')
                exact no_c4 huniq hpab hl12
                  (hpair pa l1 hpa_in hpa_ni hl1_ni hv1)
                  (hpair pb' l1 hpb_in hpb_ni hl1_ni hv1)
                  (hpair pa l2 hpa_in hpa_ni hl2_ni hv2)
                  (hpair pb' l2 hpb_in hpb_ni hl2_ni hv2)
              have hb_sub_d2 : BadP2 N I C (N + N + b) ⊆ BadP2 N I C d2 := by
                intro p' hp'
                obtain ⟨l1, l2, hne, h1, h2, hv1, hv2⟩ := mf_mp hp'
                obtain ⟨_, hinp⟩ := gate_info hAO hb
                rw [wv_gate C (N + N) _ hAO.2.1 b hb, handb, hinp] at hv1 hv2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true, Bool.and_eq_true] at hv1 hv2
                refine mfu_mpr ⟨l1, l2, hne, h1, h2, ?_, ?_⟩
                · rcases (by omega : sb.val = 0 ∨ sb.val = 1) with hs | hs
                  · simpa [d2, hs] using hv1.2
                  · simpa [d2, hs] using hv1.1
                · rcases (by omega : sb.val = 0 ∨ sb.val = 1) with hs | hs
                  · simpa [d2, hs] using hv2.2
                  · simpa [d2, hs] using hv2.1
              have hd2_2 : 2 ≤ (BadP2 N I C d2).card := (by omega : 2 ≤ (BadP2 N I C (N + N + b)).card).trans (Finset.card_le_card hb_sub_d2)
              by_cases he_2 : 2 ≤ (BadP2 N I C (N + N + e)).card
              · exact ⟨e, he, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨hande, he_2, fun p' hp' => hd2_sub p' (hsub_ed2 hp'),
                     se, hpe1, by change (PO N C e1).card ≤ 3; rw [hpe1_eq]; simp⟩))))))))))))))))))⟩
              · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
                  or_walk_drop hAO (BadP2 N I C) (or_mono_BadP2 hAO) 1 hd2e (by omega) (by omega) hpe_b2
                exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨hor, by omega, fun p' hp' => hd2_sub p' (hwsub hp'), s',
                   card_eq_one_of_mem_le hyps hslo⟩))))))))))⟩
    · exact ⟨e, he, Or.inr (Or.inr (Or.inl ⟨hande, se, hpe1_eq, hle2, by change (LO N C e2).card ≤ 3; rw [hle2_eq]; simp⟩))⟩

theorem cover_type3_opp {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (sa : Fin 2)
    {b1 : ℕ} (hb1 : b1 < C.gates.length) (hub1 : OrReach (N + N) C ((gateAt C a).inputs.getD sa.val 0) (N + N + b1))
    (hand1 : (gateAt C b1).op = GateOp.and) (s1 : Fin 2)
    (hpc1 : p ∈ PO N C ((gateAt C b1).inputs.getD s1.val 0))
    (hlc2_eq : LO N C ((gateAt C b1).inputs.getD (1 - s1.val) 0) = {l})
    {b2 : ℕ} (hb2 : b2 < C.gates.length) (hvb2 : OrReach (N + N) C ((gateAt C a).inputs.getD (1 - sa.val) 0) (N + N + b2))
    (hand2 : (gateAt C b2).op = GateOp.and) (s2 : Fin 2)
    (hpd1_eq : PO N C ((gateAt C b2).inputs.getD s2.val 0) = {p})
    (hld2 : l ∈ LO N C ((gateAt C b2).inputs.getD (1 - s2.val) 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set u := (gateAt C a).inputs.getD sa.val 0
  set v := (gateAt C a).inputs.getD (1 - sa.val) 0
  set c1 := (gateAt C b1).inputs.getD s1.val 0
  set c2 := (gateAt C b1).inputs.getD (1 - s1.val) 0
  set d1 := (gateAt C b2).inputs.getD s2.val 0
  set d2 := (gateAt C b2).inputs.getD (1 - s2.val) 0
  have hlc2 : l ∈ LO N C c2 := by rw [hlc2_eq]; simp
  have hpd1 : p ∈ PO N C d1 := by rw [hpd1_eq]; simp
  by_cases hc1_near : ((PO N C c1).filter fun p' => ¬ I p' l).card ≤ 1
  · by_cases hc1_4 : 4 ≤ (PO N C c1).card
    · exact cover_near_PO hAO hpc1 hc1_near hc1_4
    · have hc1_le : (PO N C c1).card ≤ 3 := by omega
      exact ⟨b1, hb1, Or.inr (Or.inr (Or.inr (Or.inl ⟨hand1, s1, hpc1, hc1_le, hlc2_eq⟩)))⟩
  · by_cases hd2_near : ((LO N C d2).filter fun l' => ¬ I p l').card ≤ 1
    · by_cases hd2_4 : 4 ≤ (LO N C d2).card
      · exact cover_near_LO hAO hld2 hd2_near hd2_4
      · have hd2_le : (LO N C d2).card ≤ 3 := by omega
        exact ⟨b2, hb2, Or.inr (Or.inr (Or.inl ⟨hand2, s2, hpd1_eq, hld2, hd2_le⟩))⟩
    · obtain ⟨pa, hpa, pb', hpb', hpab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((PO N C c1).filter fun p' => ¬ I p' l).card)
      obtain ⟨hpa_in, hpa_ni⟩ := Finset.mem_filter.mp hpa
      obtain ⟨hpb_in, hpb_ni⟩ := Finset.mem_filter.mp hpb'
      obtain ⟨la, hla, lb', hlb', hlab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((LO N C d2).filter fun l' => ¬ I p l').card)
      obtain ⟨hla_in, hla_ni⟩ := Finset.mem_filter.mp hla
      obtain ⟨hlb_in, hlb_ni⟩ := Finset.mem_filter.mp hlb'
      have hlb1 : l ∈ BadL2 N I C (N + N + b1) := mfu_mpr ⟨pa, pb', hpab, hpa_ni, hpb_ni,
        and_true_s hAO hb1 hand1 s1 (wv_of_PO hAO hpa_in (by simp)) (wv_of_LO hAO hlc2 (by simp)),
        and_true_s hAO hb1 hand1 s1 (wv_of_PO hAO hpb_in (by simp)) (wv_of_LO hAO hlc2 (by simp))⟩
      have hpb2 : p ∈ BadP2 N I C (N + N + b2) := mfu_mpr ⟨la, lb', hlab, hla_ni, hlb_ni,
        and_true_s hAO hb2 hand2 s2 (wv_of_PO hAO hpd1 (by simp)) (wv_of_LO hAO hla_in (by simp)),
        and_true_s hAO hb2 hand2 s2 (wv_of_PO hAO hpd1 (by simp)) (wv_of_LO hAO hlb_in (by simp))⟩
      have hsub_u : BadL2 N I C (N + N + b1) ⊆ BadL2 N I C u :=
        orReach_sub_F (BadL2 N I C) (or_mono_BadL2 hAO) hub1
      have hsub_v : BadP2 N I C (N + N + b2) ⊆ BadP2 N I C v :=
        orReach_sub_F (BadP2 N I C) (or_mono_BadP2 hAO) hvb2
      have hBadU_sub : ∀ l' ∈ BadL2 N I C u, I p l' := by
        intro l' hl'
        by_contra hni_pl'
        obtain ⟨p1, p2, hp12, hp1_ni, hp2_ni, hv1, hv2⟩ := mf_mp hl'
        have hpair : ∀ px lx : Fin N, lx ∈ LO N C d2 → ¬ I p lx → ¬ I px l' →
            wv C (N + N) (setInput {Fin.castAdd N px, Fin.natAdd N l'}) u = true → I px lx := by
          intro px lx hlx hplx hpxl' hwu
          set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.castAdd N px, Fin.natAdd N l', Fin.natAdd N lx}
          have huA := wv_of_setInput_sub hAO (B := A) (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [A]) hwu
          have hvA := orReach_wv hAO _ hvb2 (and_true_s hAO hb2 hand2 s2
            (wv_of_PO hAO hpd1 (A := A) (by simp [A])) (wv_of_LO hAO hlx (A := A) (by simp [A])))
          have haA := and_true_s hAO ha hand sa huA hvA
          obtain ⟨p'', l'', hI, hp'', hl''⟩ := top_sound hAO hfun htop haA
          simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl''
          rcases hp'' with h | h | h | h
          · have := Fin.castAdd_injective N N h; subst this
            rcases hl'' with h2 | h2 | h2 | h2
            · exact absurd h2.symm (castAdd_ne_natAdd p'' l'')
            · exact absurd h2.symm (castAdd_ne_natAdd px l'')
            · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hni_pl'
            · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hplx
          · have := Fin.castAdd_injective N N h; subst this
            rcases hl'' with h2 | h2 | h2 | h2
            · exact absurd h2.symm (castAdd_ne_natAdd p l'')
            · exact absurd h2.symm (castAdd_ne_natAdd p'' l'')
            · exact absurd ((Fin.natAdd_injective N N h2) ▸ hI) hpxl'
            · exact (Fin.natAdd_injective N N h2) ▸ hI
          · exact absurd h (castAdd_ne_natAdd p'' l')
          · exact absurd h (castAdd_ne_natAdd p'' lx)
        exact no_c4 huniq hp12 hlab
          (hpair p1 la hla_in hla_ni hp1_ni hv1)
          (hpair p2 la hla_in hla_ni hp2_ni hv2)
          (hpair p1 lb' hlb_in hlb_ni hp1_ni hv1)
          (hpair p2 lb' hlb_in hlb_ni hp2_ni hv2)
      have hBadV_sub : ∀ p' ∈ BadP2 N I C v, I p' l := by
        intro p' hp'
        by_contra hni_p'l
        obtain ⟨l1, l2, hl12, hl1_ni, hl2_ni, hv1, hv2⟩ := mf_mp hp'
        have hpair : ∀ px lx : Fin N, px ∈ PO N C c1 → ¬ I px l → ¬ I p' lx →
            wv C (N + N) (setInput {Fin.castAdd N p', Fin.natAdd N lx}) v = true → I px lx := by
          intro px lx hpx hpxl hp'lx hwv
          set A : Finset (Fin (N + N)) := {Fin.castAdd N p', Fin.castAdd N px, Fin.natAdd N l, Fin.natAdd N lx}
          have huA := orReach_wv hAO _ hub1 (and_true_s hAO hb1 hand1 s1
            (wv_of_PO hAO hpx (A := A) (by simp [A])) (wv_of_LO hAO hlc2 (A := A) (by simp [A])))
          have hvA := wv_of_setInput_sub hAO (B := A) (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [A]) hwv
          have haA := and_true_s hAO ha hand sa huA hvA
          obtain ⟨p'', l'', hI, hp'', hl''⟩ := top_sound hAO hfun htop haA
          simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp'' hl''
          rcases hl'' with h | h | h | h
          · exact absurd h.symm (castAdd_ne_natAdd p' l'')
          · exact absurd h.symm (castAdd_ne_natAdd px l'')
          · have := Fin.natAdd_injective N N h; subst this
            rcases hp'' with h2 | h2 | h2 | h2
            · exact absurd ((Fin.castAdd_injective N N h2) ▸ hI) hni_p'l
            · exact absurd ((Fin.castAdd_injective N N h2) ▸ hI) hpxl
            · exact absurd h2 (castAdd_ne_natAdd p'' l'')
            · exact absurd h2 (castAdd_ne_natAdd p'' lx)
          · have := Fin.natAdd_injective N N h; subst this
            rcases hp'' with h2 | h2 | h2 | h2
            · exact absurd ((Fin.castAdd_injective N N h2) ▸ hI) hp'lx
            · exact (Fin.castAdd_injective N N h2) ▸ hI
            · exact absurd h2 (castAdd_ne_natAdd p'' l)
            · exact absurd h2 (castAdd_ne_natAdd p'' l'')
        exact no_c4 huniq hpab hl12
          (hpair pa l1 hpa_in hpa_ni hl1_ni hv1)
          (hpair pb' l1 hpb_in hpb_ni hl1_ni hv1)
          (hpair pa l2 hpa_in hpa_ni hl2_ni hv2)
          (hpair pb' l2 hpb_in hpb_ni hl2_ni hv2)
      by_cases hb1_2 : 2 ≤ (BadL2 N I C (N + N + b1)).card
      · exact ⟨b1, hb1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hand1, hb1_2, fun l' hl' => hBadU_sub l' (hsub_u hl'), ⟨1 - s1.val, by omega⟩,
             hlc2, by change (LO N C c2).card ≤ 3; rw [hlc2_eq]; simp⟩)))))))))))))))))⟩
      · by_cases hu_2 : 2 ≤ (BadL2 N I C u).card
        · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyls⟩ :=
            or_walk_drop hAO (BadL2 N I C) (or_mono_BadL2 hAO) 1 hub1 (by omega) (by omega) hlb1
          exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hor, by omega, fun l' hl' => hBadU_sub l' (hwsub hl'), s',
             card_eq_one_of_mem_le hyls hslo⟩)))))))))⟩
        · by_cases hb2_2 : 2 ≤ (BadP2 N I C (N + N + b2)).card
          · exact ⟨b2, hb2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨hand2, hb2_2, fun p' hp' => hBadV_sub p' (hsub_v hp'), s2,
                 hpd1, by change (PO N C d1).card ≤ 3; rw [hpd1_eq]; simp⟩))))))))))))))))))⟩
          · by_cases hv_2 : 2 ≤ (BadP2 N I C v).card
            · obtain ⟨j, hj, s', _, hor, hhi, hwsub, hslo, hyps⟩ :=
                or_walk_drop hAO (BadP2 N I C) (or_mono_BadP2 hAO) 1 hvb2 (by omega) (by omega) hpb2
              exact ⟨j, hj, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨hor, by omega, fun p' hp' => hBadV_sub p' (hwsub hp'), s',
                 card_eq_one_of_mem_le hyps hslo⟩))))))))))⟩
            · have hv_eq : BadP2 N I C v = {p} := card_eq_one_of_mem_le (hsub_v hpb2) (by omega)
              have hu_eq : BadL2 N I C u = {l} := card_eq_one_of_mem_le (hsub_u hlb1) (by omega)
              exact ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨hand, ⟨1 - sa.val, by omega⟩, hv_eq,
                 by have h1s : 1 - (⟨1 - sa.val, by omega⟩ : Fin 2).val = sa.val := (by simp; omega); rw [h1s]; exact hu_eq⟩))))))))))))⟩

theorem cover_type3 {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and)
    {b1 : ℕ} (hb1 : b1 < C.gates.length) (hub1 : OrReach (N + N) C ((gateAt C a).inputs.getD 0 0) (N + N + b1))
    (hand1 : (gateAt C b1).op = GateOp.and) (s1 : Fin 2)
    (hpc1 : p ∈ PO N C ((gateAt C b1).inputs.getD s1.val 0))
    (hlc2 : l ∈ LO N C ((gateAt C b1).inputs.getD (1 - s1.val) 0))
    {b2 : ℕ} (hb2 : b2 < C.gates.length) (hvb2 : OrReach (N + N) C ((gateAt C a).inputs.getD 1 0) (N + N + b2))
    (hand2 : (gateAt C b2).op = GateOp.and) (s2 : Fin 2)
    (hpd1 : p ∈ PO N C ((gateAt C b2).inputs.getD s2.val 0))
    (hld2 : l ∈ LO N C ((gateAt C b2).inputs.getD (1 - s2.val) 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set c1 := (gateAt C b1).inputs.getD s1.val 0
  set c2 := (gateAt C b1).inputs.getD (1 - s1.val) 0
  set d1 := (gateAt C b2).inputs.getD s2.val 0
  set d2 := (gateAt C b2).inputs.getD (1 - s2.val) 0
  have hlines : (∀ l1 ∈ LO N C c2, I p l1) ∨ (∀ l2 ∈ LO N C d2, I p l2) := by
    by_contra hboth; push Not at hboth
    obtain ⟨⟨l1, hl1, hn1⟩, ⟨l2, hl2, hn2⟩⟩ := hboth
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l1, Fin.natAdd N l2}
    have huA := orReach_wv hAO _ hub1 (and_true_s hAO hb1 hand1 s1 (wv_of_PO hAO hpc1 (A := A) (by simp [A])) (wv_of_LO hAO hl1 (A := A) (by simp [A])))
    have hvA := orReach_wv hAO _ hvb2 (and_true_s hAO hb2 hand2 s2 (wv_of_PO hAO hpd1 (A := A) (by simp [A])) (wv_of_LO hAO hl2 (A := A) (by simp [A])))
    obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop (and_true hAO ha hand huA hvA)
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
    have hpe : p' = p := by
      rcases hp' with h | h | h
      · exact Fin.castAdd_injective N N h
      · exact absurd h (castAdd_ne_natAdd p' l1)
      · exact absurd h (castAdd_ne_natAdd p' l2)
    subst hpe
    rcases hl' with h | h | h
    · exact absurd h.symm (castAdd_ne_natAdd p' l')
    · exact hn1 ((Fin.natAdd_injective N N h) ▸ hI)
    · exact hn2 ((Fin.natAdd_injective N N h) ▸ hI)
  have hpts : (∀ p1 ∈ PO N C c1, I p1 l) ∨ (∀ p2 ∈ PO N C d1, I p2 l) := by
    by_contra hboth; push Not at hboth
    obtain ⟨⟨p1, hp1, hn1⟩, ⟨p2, hp2, hn2⟩⟩ := hboth
    set A : Finset (Fin (N + N)) := {Fin.castAdd N p1, Fin.castAdd N p2, Fin.natAdd N l}
    have huA := orReach_wv hAO _ hub1 (and_true_s hAO hb1 hand1 s1 (wv_of_PO hAO hp1 (A := A) (by simp [A])) (wv_of_LO hAO hlc2 (A := A) (by simp [A])))
    have hvA := orReach_wv hAO _ hvb2 (and_true_s hAO hb2 hand2 s2 (wv_of_PO hAO hp2 (A := A) (by simp [A])) (wv_of_LO hAO hld2 (A := A) (by simp [A])))
    obtain ⟨p', l', hI, hp', hl'⟩ := top_sound hAO hfun htop (and_true hAO ha hand huA hvA)
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp' hl'
    have hle : l' = l := by
      rcases hl' with h | h | h
      · exact absurd h.symm (castAdd_ne_natAdd p1 l')
      · exact absurd h.symm (castAdd_ne_natAdd p2 l')
      · exact Fin.natAdd_injective N N h
    subst hle
    rcases hp' with h | h | h
    · exact hn1 ((Fin.castAdd_injective N N h) ▸ hI)
    · exact hn2 ((Fin.castAdd_injective N N h) ▸ hI)
    · exact absurd h (castAdd_ne_natAdd p' l')
  have hL_or : (∃ j < C.gates.length, gateCov N I C j p l) ∨ LO N C c2 = {l} ∨ LO N C d2 = {l} := by
    rcases hlines with hc | hd
    · by_cases h2 : 2 ≤ (LO N C c2).card
      · exact Or.inl (cover_LO_star hAO hlc2 hc h2)
      · exact Or.inr (Or.inl (card_eq_one_of_mem_le hlc2 (by omega)))
    · by_cases h2 : 2 ≤ (LO N C d2).card
      · exact Or.inl (cover_LO_star hAO hld2 hd h2)
      · exact Or.inr (Or.inr (card_eq_one_of_mem_le hld2 (by omega)))
  have hP_or : (∃ j < C.gates.length, gateCov N I C j p l) ∨ PO N C c1 = {p} ∨ PO N C d1 = {p} := by
    rcases hpts with hc | hd
    · by_cases h2 : 2 ≤ (PO N C c1).card
      · exact Or.inl (cover_PO_star hAO hpc1 hc h2)
      · exact Or.inr (Or.inl (card_eq_one_of_mem_le hpc1 (by omega)))
    · by_cases h2 : 2 ≤ (PO N C d1).card
      · exact Or.inl (cover_PO_star hAO hpd1 hd h2)
      · exact Or.inr (Or.inr (card_eq_one_of_mem_le hpd1 (by omega)))
  rcases hL_or with hcov | hlc2_eq | hld2_eq
  · exact hcov
  · rcases hP_or with hcov | hpc1_eq | hpd1_eq
    · exact hcov
    · exact ⟨b1, hb1, Or.inr (Or.inr (Or.inl ⟨hand1, s1, hpc1_eq, hlc2, by change (LO N C c2).card ≤ 3; rw [hlc2_eq]; simp⟩))⟩
    · exact cover_type3_opp huniq hAO hfun ha htop hand ⟨0, by omega⟩ hb1 hub1 hand1 s1 hpc1 hlc2_eq hb2 hvb2 hand2 s2 hpd1_eq hld2
  · rcases hP_or with hcov | hpc1_eq | hpd1_eq
    · exact hcov
    · exact cover_type3_opp huniq hAO hfun ha htop hand ⟨1, by omega⟩ hb2 (by simpa using hvb2) hand2 s2 hpd1 hld2_eq hb1 (by simpa using hub1) hand1 s1 hpc1_eq hlc2
    · exact ⟨b2, hb2, Or.inr (Or.inr (Or.inl ⟨hand2, s2, hpd1_eq, hld2, by change (LO N C d2).card ≤ 3; rw [hld2_eq]; simp⟩))⟩

theorem cover_type2a_dispatch {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (sa : Fin 2)
    (hpu : p ∈ PO N C ((gateAt C a).inputs.getD sa.val 0))
    {cl : ℕ} (hcl1 : 1 ≤ cl) (hcl2 : cl ≤ 2)
    (hrv : [1, cl] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C a).inputs.getD (1 - sa.val) 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  obtain ⟨b, hb, a1, b1, a2, b2, hvb, handb, h1, h2, hae, hbe, hp1, hp2⟩ :=
    rv_split hAO p l _ 1 cl hrv (by omega) hcl2 (by omega)
  by_cases ha1 : a1 = 1
  · have ha2 : a2 = 0 := by omega
    by_cases hb1 : b1 = 0
    · rw [ha1, hb1] at h1; rw [ha2] at h2
      exact cover_type2a_gen hAO hfun ha htop hand sa hpu hb hvb handb ⟨0, by omega⟩
        (mfu_mpr (rv_10 hAO p l _ h1)) (by omega) (by omega) h2
    · have hb1_eq : b1 = 1 := by omega
      have hb2_eq : b2 = 1 := by omega
      rw [ha1, hb1_eq] at h1; rw [ha2, hb2_eq] at h2
      obtain ⟨e, he, c1, d1, c2, d2, hbe', hande, he1, he2, hce, hde, hcp1, hcp2⟩ :=
        rv_split hAO p l _ 1 1 h1 (by omega) (by omega) (by omega)
      have hld1 : l ∈ LO N C ((gateAt C b).inputs.getD 1 0) :=
        mfu_mpr (rv_01 hAO p l _ h2)
      by_cases hc1 : c1 = 1
      · have hd1 : d1 = 0 := by omega
        have hc2 : c2 = 0 := by omega
        have hd2 : d2 = 1 := by omega
        rw [hc1, hd1] at he1; rw [hc2, hd2] at he2
        exact cover_type2c2 huniq hAO hfun ha htop hand sa hpu hb hvb handb ⟨1, by omega⟩ hld1
          he (by simpa using hbe') hande ⟨0, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ he1))
          (mfu_mpr (rv_01 hAO p l _ he2))
      · have hd1 : d1 = 1 := by omega
        have hc2 : c2 = 1 := by omega
        have hd2 : d2 = 0 := by omega
        have hc1_0 : c1 = 0 := by omega
        rw [hc1_0, hd1] at he1; rw [hc2, hd2] at he2
        exact cover_type2c2 huniq hAO hfun ha htop hand sa hpu hb hvb handb ⟨1, by omega⟩ hld1
          he (by simpa using hbe') hande ⟨1, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ he2))
          (mfu_mpr (rv_01 hAO p l _ he1))
  · have ha1_0 : a1 = 0 := by omega
    have ha2_1 : a2 = 1 := by omega
    by_cases hb2 : b2 = 0
    · rw [ha2_1, hb2] at h2; rw [ha1_0] at h1
      exact cover_type2a_gen hAO hfun ha htop hand sa hpu hb hvb handb ⟨1, by omega⟩
        (mfu_mpr (rv_10 hAO p l _ h2)) (cl := b1) (by omega) (by omega) (by simpa using h1)
    · have hb1_eq : b1 = 1 := by omega
      have hb2_eq : b2 = 1 := by omega
      rw [ha1_0, hb1_eq] at h1; rw [ha2_1, hb2_eq] at h2
      obtain ⟨e, he, c1, d1, c2, d2, hbe', hande, he1, he2, hce, hde, hcp1, hcp2⟩ :=
        rv_split hAO p l _ 1 1 h2 (by omega) (by omega) (by omega)
      have hld1 : l ∈ LO N C ((gateAt C b).inputs.getD 0 0) :=
        mfu_mpr (rv_01 hAO p l _ h1)
      by_cases hc1 : c1 = 1
      · have hd1 : d1 = 0 := by omega
        have hc2 : c2 = 0 := by omega
        have hd2 : d2 = 1 := by omega
        rw [hc1, hd1] at he1; rw [hc2, hd2] at he2
        exact cover_type2c2 huniq hAO hfun ha htop hand sa hpu hb hvb handb ⟨0, by omega⟩ hld1
          he (by simpa using hbe') hande ⟨0, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ he1))
          (mfu_mpr (rv_01 hAO p l _ he2))
      · have hd1 : d1 = 1 := by omega
        have hc2 : c2 = 1 := by omega
        have hd2 : d2 = 0 := by omega
        have hc1_0 : c1 = 0 := by omega
        rw [hc1_0, hd1] at he1; rw [hc2, hd2] at he2
        exact cover_type2c2 huniq hAO hfun ha htop hand sa hpu hb hvb handb ⟨0, by omega⟩ hld1
          he (by simpa using hbe') hande ⟨1, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ he2))
          (mfu_mpr (rv_01 hAO p l _ he1))

theorem cover_type2b_dispatch {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} {a : ℕ} (ha : a < C.gates.length) (htop : OrReach (N + N) C C.output (N + N + a))
    (hand : (gateAt C a).op = GateOp.and) (sa : Fin 2)
    (hlv : l ∈ LO N C ((gateAt C a).inputs.getD (1 - sa.val) 0))
    {cp : ℕ} (hcp1 : 1 ≤ cp) (hcp2 : cp ≤ 2)
    (hru : [cp, 1] ∈ rv C (N + N) [p.val, N + l.val] 2 ((gateAt C a).inputs.getD sa.val 0)) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  obtain ⟨b, hb, a1, b1, a2, b2, hub, handb, h1, h2, hae, hbe, hp1, hp2⟩ :=
    rv_split hAO p l _ cp 1 hru hcp2 (by omega) (by omega)
  by_cases hb2 : b2 = 1
  · have hb1 : b1 = 0 := by omega
    by_cases ha2 : a2 = 0
    · rw [ha2, hb2] at h2; rw [hb1] at h1
      exact cover_type2b_gen hAO hfun ha htop hand sa hlv hb hub handb ⟨0, by omega⟩
        (mfu_mpr (rv_01 hAO p l _ h2)) (by omega) (by omega) h1
    · have ha1_eq : a1 = 1 := by omega
      have ha2_eq : a2 = 1 := by omega
      rw [ha1_eq, hb1] at h1; rw [ha2_eq, hb2] at h2
      obtain ⟨e, he, c1, d1, c2, d2, hbe', hande, he1, he2, hce, hde, hcp1', hcp2'⟩ :=
        rv_split hAO p l _ 1 1 h2 (by omega) (by omega) (by omega)
      have hpd1 : p ∈ PO N C ((gateAt C b).inputs.getD 0 0) :=
        mfu_mpr (rv_10 hAO p l _ h1)
      by_cases hc1 : c1 = 1
      · have hd1 : d1 = 0 := by omega
        have hc2 : c2 = 0 := by omega
        have hd2 : d2 = 1 := by omega
        rw [hc1, hd1] at he1; rw [hc2, hd2] at he2
        exact cover_type2d2 huniq hAO hfun ha htop hand sa hlv hb hub handb ⟨0, by omega⟩ hpd1
          he (by simpa using hbe') hande ⟨0, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ he1))
          (mfu_mpr (rv_01 hAO p l _ he2))
      · have hd1 : d1 = 1 := by omega
        have hc2 : c2 = 1 := by omega
        have hd2 : d2 = 0 := by omega
        have hc1_0 : c1 = 0 := by omega
        rw [hc1_0, hd1] at he1; rw [hc2, hd2] at he2
        exact cover_type2d2 huniq hAO hfun ha htop hand sa hlv hb hub handb ⟨0, by omega⟩ hpd1
          he (by simpa using hbe') hande ⟨1, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ he2))
          (mfu_mpr (rv_01 hAO p l _ he1))
  · have hb2_0 : b2 = 0 := by omega
    have hb1_1 : b1 = 1 := by omega
    by_cases ha1 : a1 = 0
    · rw [ha1, hb1_1] at h1; rw [hb2_0] at h2
      exact cover_type2b_gen hAO hfun ha htop hand sa hlv hb hub handb ⟨1, by omega⟩
        (mfu_mpr (rv_01 hAO p l _ h1)) (cp := a2) (by omega) (by omega) (by simpa using h2)
    · have ha1_eq : a1 = 1 := by omega
      have ha2_eq : a2 = 1 := by omega
      rw [ha1_eq, hb1_1] at h1; rw [ha2_eq, hb2_0] at h2
      obtain ⟨e, he, c1, d1, c2, d2, hbe', hande, he1, he2, hce, hde, hcp1', hcp2'⟩ :=
        rv_split hAO p l _ 1 1 h1 (by omega) (by omega) (by omega)
      have hpd1 : p ∈ PO N C ((gateAt C b).inputs.getD 1 0) :=
        mfu_mpr (rv_10 hAO p l _ h2)
      by_cases hc1 : c1 = 1
      · have hd1 : d1 = 0 := by omega
        have hc2 : c2 = 0 := by omega
        have hd2 : d2 = 1 := by omega
        rw [hc1, hd1] at he1; rw [hc2, hd2] at he2
        exact cover_type2d2 huniq hAO hfun ha htop hand sa hlv hb hub handb ⟨1, by omega⟩ hpd1
          he (by simpa using hbe') hande ⟨0, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ he1))
          (mfu_mpr (rv_01 hAO p l _ he2))
      · have hd1 : d1 = 1 := by omega
        have hc2 : c2 = 1 := by omega
        have hd2 : d2 = 0 := by omega
        have hc1_0 : c1 = 0 := by omega
        rw [hc1_0, hd1] at he1; rw [hc2, hd2] at he2
        exact cover_type2d2 huniq hAO hfun ha htop hand sa hlv hb hub handb ⟨1, by omega⟩ hpd1
          he (by simpa using hbe') hande ⟨1, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ he2))
          (mfu_mpr (rv_01 hAO p l _ he1))

theorem every_inc_covered {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hRK : IsReadK (N + N) C 2) {p l : Fin N} (hI : I p l) :
    ∃ j < C.gates.length, gateCov N I C j p l := by
  set S : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l}
  have hprime : IsPrimeImplicant (N + N) C S := by
    refine ⟨?_, ?_⟩
    · rw [hfun, decide_eq_true_eq]
      exact ⟨p, l, hI, by simp [S, setInput], by simp [S, setInput]⟩
    · intro T hT
      rw [Finset.mem_ssubsets] at hT
      rw [hfun, decide_eq_false_iff_not]
      rintro ⟨p', l', _, hp', hl'⟩
      simp only [setInput, decide_eq_true_eq] at hp' hl'
      have hsub := hT.1
      have hp'S := hsub hp'
      have hl'S := hsub hl'
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp'S hl'S
      have hpe : p' = p := by
        rcases hp'S with h | h
        · exact Fin.castAdd_injective N N h
        · exact absurd h (castAdd_ne_natAdd p' l)
      have hle : l' = l := by
        rcases hl'S with h | h
        · exact absurd h.symm (castAdd_ne_natAdd p l')
        · exact Fin.natAdd_injective N N h
      subst hpe; subst hle
      apply hT.2
      intro x hx
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
  have hrm := hRK S hprime
  rw [setList_pair p l] at hrm
  unfold readsAtMost at hrm
  rw [List.any_eq_true] at hrm
  obtain ⟨v, hv_mem, hv_all⟩ := hrm
  obtain ⟨cp, cl, rfl, _, _, _⟩ := rv_shape hAO p l C.output v hv_mem
  simp only [List.all_cons, List.all_nil, decide_eq_true_eq, Bool.and_true, Bool.and_eq_true] at hv_all
  obtain ⟨hcp2, hcl2⟩ := hv_all
  have hcp1 : 1 ≤ cp := by
    by_contra h0
    have hcp0 : cp = 0 := by omega
    subst hcp0
    have hw := rv_sound_wv hAO p l (setInput {Fin.natAdd N l}) C.output 0 cl hv_mem
      (fun h => by omega) (fun _ => by simp [setInput])
    have hcf : circuitFun (N + N) C (setInput {Fin.natAdd N l}) = true := hw
    rw [hfun, decide_eq_true_eq] at hcf
    obtain ⟨p', _, _, hp', _⟩ := hcf
    simp only [setInput, decide_eq_true_eq, Finset.mem_singleton] at hp'
    exact castAdd_ne_natAdd p' l hp'
  have hcl1 : 1 ≤ cl := by
    by_contra h0
    have hcl0 : cl = 0 := by omega
    subst hcl0
    have hw := rv_sound_wv hAO p l (setInput {Fin.castAdd N p}) C.output cp 0 hv_mem
      (fun _ => by simp [setInput]) (fun h => by omega)
    have hcf : circuitFun (N + N) C (setInput {Fin.castAdd N p}) = true := hw
    rw [hfun, decide_eq_true_eq] at hcf
    obtain ⟨_, l', _, _, hl'⟩ := hcf
    simp only [setInput, decide_eq_true_eq, Finset.mem_singleton] at hl'
    exact (castAdd_ne_natAdd p l') hl'.symm
  obtain ⟨a, ha, a1, b1, a2, b2, htop, hand, hru, hrv, hae, hbe, hp1, hp2⟩ :=
    rv_split hAO p l C.output cp cl hv_mem hcp2 hcl2 (by omega)
  by_cases h1a : b1 = 0 ∧ a2 = 0
  · rw [h1a.1] at hru; rw [h1a.2] at hrv
    exact cover_type1 hAO hfun ha htop hand ⟨0, by omega⟩ (by omega) (by omega) (by omega) (by omega) hru hrv
  · by_cases h1b : a1 = 0 ∧ b2 = 0
    · rw [h1b.1] at hru; rw [h1b.2] at hrv
      exact cover_type1 hAO hfun ha htop hand ⟨1, by omega⟩ (by omega) (by omega) (by omega) (by omega) hrv hru
    · by_cases h2a0 : a1 = 1 ∧ b1 = 0
      · rw [h2a0.1, h2a0.2] at hru
        have ha2_1 : a2 = 1 := by omega
        rw [ha2_1] at hrv
        exact cover_type2a_dispatch huniq hAO hfun ha htop hand ⟨0, by omega⟩
          (mfu_mpr (rv_10 hAO p l _ hru)) (by omega) (by omega) hrv
      · by_cases h2a1 : a2 = 1 ∧ b2 = 0
        · rw [h2a1.1, h2a1.2] at hrv
          have ha1_1 : a1 = 1 := by omega
          rw [ha1_1] at hru
          exact cover_type2a_dispatch huniq hAO hfun ha htop hand ⟨1, by omega⟩
            (mfu_mpr (rv_10 hAO p l _ hrv)) (cl := b1) (by omega) (by omega) (by simpa using hru)
        · by_cases h2b0 : a2 = 0 ∧ b2 = 1
          · rw [h2b0.1, h2b0.2] at hrv
            have hb1_1 : b1 = 1 := by omega
            rw [hb1_1] at hru
            exact cover_type2b_dispatch huniq hAO hfun ha htop hand ⟨0, by omega⟩
              (mfu_mpr (rv_01 hAO p l _ hrv)) (by omega) (by omega) hru
          · by_cases h2b1 : a1 = 0 ∧ b1 = 1
            · rw [h2b1.1, h2b1.2] at hru
              have hb2_1 : b2 = 1 := by omega
              rw [hb2_1] at hrv
              exact cover_type2b_dispatch huniq hAO hfun ha htop hand ⟨1, by omega⟩
                (mfu_mpr (rv_01 hAO p l _ hru)) (cp := a2) (by omega) (by omega) (by simpa using hrv)
            · have h3 : a1 = 1 ∧ b1 = 1 ∧ a2 = 1 ∧ b2 = 1 := by omega
              rw [h3.1, h3.2.1] at hru; rw [h3.2.2.1, h3.2.2.2] at hrv
              obtain ⟨b1', hb1', c1, d1, c2, d2, hub1, hand1, hc1, hc2, _, _, _, _⟩ :=
                rv_split hAO p l _ 1 1 hru (by omega) (by omega) (by omega)
              obtain ⟨b2', hb2', e1, f1, e2, f2, hvb2, hand2, he1, he2, _, _, _, _⟩ :=
                rv_split hAO p l _ 1 1 hrv (by omega) (by omega) (by omega)
              have hs1 : ∃ s1 : Fin 2, p ∈ PO N C ((gateAt C b1').inputs.getD s1.val 0) ∧
                  l ∈ LO N C ((gateAt C b1').inputs.getD (1 - s1.val) 0) := by
                by_cases h : c1 = 1
                · have : d1 = 0 ∧ c2 = 0 ∧ d2 = 1 := by omega
                  rw [h, this.1] at hc1; rw [this.2.1, this.2.2] at hc2
                  exact ⟨⟨0, by omega⟩, mfu_mpr (rv_10 hAO p l _ hc1),
                    mfu_mpr (rv_01 hAO p l _ hc2)⟩
                · have : c1 = 0 ∧ d1 = 1 ∧ c2 = 1 ∧ d2 = 0 := by omega
                  rw [this.1, this.2.1] at hc1; rw [this.2.2.1, this.2.2.2] at hc2
                  exact ⟨⟨1, by omega⟩, mfu_mpr (rv_10 hAO p l _ hc2),
                    mfu_mpr (rv_01 hAO p l _ hc1)⟩
              have hs2 : ∃ s2 : Fin 2, p ∈ PO N C ((gateAt C b2').inputs.getD s2.val 0) ∧
                  l ∈ LO N C ((gateAt C b2').inputs.getD (1 - s2.val) 0) := by
                by_cases h : e1 = 1
                · have : f1 = 0 ∧ e2 = 0 ∧ f2 = 1 := by omega
                  rw [h, this.1] at he1; rw [this.2.1, this.2.2] at he2
                  exact ⟨⟨0, by omega⟩, mfu_mpr (rv_10 hAO p l _ he1),
                    mfu_mpr (rv_01 hAO p l _ he2)⟩
                · have : e1 = 0 ∧ f1 = 1 ∧ e2 = 1 ∧ f2 = 0 := by omega
                  rw [this.1, this.2.1] at he1; rw [this.2.2.1, this.2.2.2] at he2
                  exact ⟨⟨1, by omega⟩, mfu_mpr (rv_10 hAO p l _ he2),
                    mfu_mpr (rv_01 hAO p l _ he1)⟩
              obtain ⟨s1, hpc1, hlc2⟩ := hs1
              obtain ⟨s2, hpd1, hld2⟩ := hs2
              exact cover_type3 huniq hAO hfun ha htop hand hb1' hub1 hand1 s1 hpc1 hlc2 hb2' hvb2 hand2 s2 hpd1 hld2

theorem main_proof (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (_hq : 2 ≤ q) (_hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hRK : IsReadK (N + N) C 2) :
    N * (q + 1) ≤ 112 * C.size := by
  classical
  set E : Finset (Fin N × Fin N) := Finset.univ.filter fun pl => I pl.1 pl.2
  have hEcard : E.card = N * (q + 1) := by
    have hbij : E.card = ∑ l : Fin N, (Finset.univ.filter fun p => I p l).card := by
      have h1 : E = Finset.univ.biUnion fun l : Fin N =>
          (Finset.univ.filter fun p => I p l).map ⟨fun p => (p, l), fun _ _ h => (Prod.mk.inj h).1⟩ := by
        ext ⟨p, l⟩
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_map]
        exact ⟨fun h => ⟨l, p, h, rfl⟩, fun ⟨_, _, h, heq⟩ => by rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact h⟩
      rw [h1, Finset.card_biUnion]
      · simp
      · intro l1 _ l2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_map] at hx1 hx2
        obtain ⟨_, _, rfl⟩ := hx1
        obtain ⟨_, _, heq⟩ := hx2
        exact hne (Prod.mk.inj heq).2.symm
    rw [hbij]
    simp [hcard]
  have hle := card_le_of_fiber E (Finset.range C.gates.length)
    (fun pl j => gateCov N I C j pl.1 pl.2) 112
    (fun pl hpl => by
      obtain ⟨j, hj, hcov⟩ := every_inc_covered huniq hAO hfun hRK (Finset.mem_filter.mp hpl).2
      exact ⟨j, Finset.mem_range.mpr hj, hcov⟩)
    (fun j _ => by
      have hsub : E.filter (fun pl => gateCov N I C j pl.1 pl.2) ⊆
          @Finset.filter (Fin N × Fin N) (fun pl => gateCov N I C j pl.1 pl.2)
            (fun _ => Classical.propDecidable _) Finset.univ := fun pl hpl =>
        mfu_mpr (Finset.mem_filter.mp hpl).2
      exact (Finset.card_le_card hsub).trans (fib_gateCov huniq j))
  rw [hEcard, Finset.card_range] at hle
  exact hle

end PEqualNP.Outside.L_meta_2058_aux

theorem PEqualNP.Outside.L_meta_2058 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size :=
  PEqualNP.Outside.L_meta_2058_aux.main_proof
