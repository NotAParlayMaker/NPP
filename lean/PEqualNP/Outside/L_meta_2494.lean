import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2494

section Sec2471

namespace P2471


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadK

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem gd_left {α : Type} (l : List α) (s d : α) (k : ℕ) (h : k < l.length) :
    (l ++ [s]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gd_last {α : Type} (l : List α) (s d : α) : (l ++ [s]).getD l.length d = s := by
  simp [List.getD_eq_getElem?_getD]

def run {α β : Type} (F : List α → β → α) (gs : List β) (a : List α) : List α :=
  gs.foldl (fun w g => w ++ [F w g]) a

theorem run_app {α β : Type} (F : List α → β → α) (gs hs : List β) (a : List α) :
    run F (gs ++ hs) a = run F hs (run F gs a) := by
  simp [run, List.foldl_append]

theorem run_snoc {α β : Type} (F : List α → β → α) (gs : List β) (g : β) (a : List α) :
    run F (gs ++ [g]) a = run F gs a ++ [F (run F gs a) g] := by
  simp [run, List.foldl_append]

theorem run_len {α β : Type} (F : List α → β → α) : ∀ (gs : List β) (a : List α),
    (run F gs a).length = a.length + gs.length
  | [], a => by simp [run]
  | g :: gs, a => by
    have h := run_len F gs (a ++ [F a g])
    simp only [run, List.foldl_cons] at h ⊢
    rw [h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem run_keep {α β : Type} (F : List α → β → α) (d : α) :
    ∀ (gs : List β) (a : List α) (k : ℕ), k < a.length → (run F gs a).getD k d = a.getD k d
  | [], a, k, _ => rfl
  | g :: gs, a, k, hk => by
    have h := run_keep F d gs (a ++ [F a g]) k
      (by rw [List.length_append, List.length_singleton]; omega)
    simp only [run, List.foldl_cons] at h ⊢
    rw [h]
    exact gd_left a _ d k hk

def ev (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def cell (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

def ini (n : ℕ) (S : List ℕ) : List (List (List ℕ)) := (List.range n).map (leafVectors S 2)

theorem mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | rfl)
      · exact h1
      · exact h
  · simp

theorem mem_foldl_insertNew (L : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (x : List ℕ), x ∈ L.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ L := by
  induction L with
  | nil => intro acc x; simp
  | cons v L ih =>
    intro acc x
    rw [List.foldl_cons, ih, mem_insertNew]
    simp [or_assoc]

theorem mem_andStep (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, capAdd k p q = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap, List.mem_map]

theorem mem_orFold : ∀ (L : List (List (List ℕ))) (acc : List (List ℕ)) (x : List ℕ),
    x ∈ L.foldl (fun acc A => A.foldl insertNew acc) acc ↔ x ∈ acc ∨ ∃ A ∈ L, x ∈ A
  | [], acc, x => by simp
  | B :: L, acc, x => by
    rw [List.foldl_cons, mem_orFold L, mem_foldl_insertNew]
    simp [or_assoc]

theorem cap_len (a b : List ℕ) : (capAdd 2 a b).length = min a.length b.length := by
  simp [capAdd]

theorem cap_gd (a b : List ℕ) (t : ℕ) : (capAdd 2 a b).getD t 0 =
    if t < a.length ∧ t < b.length then min (a.getD t 0 + b.getD t 0) 3 else 0 := by
  by_cases h : t < a.length ∧ t < b.length
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := h
    simp [capAdd, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2]
  · rw [if_neg h]
    apply List.getD_eq_default
    rw [cap_len]
    omega

theorem z_gd (S : List ℕ) (t : ℕ) : (S.map fun _ => (0 : ℕ)).getD t 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases S[t]? <;> rfl

theorem cap2_gd (S u w : List ℕ) (t : ℕ) :
    (capAdd 2 (capAdd 2 (S.map fun _ => 0) u) w).getD t 0 =
      if t < S.length ∧ t < u.length ∧ t < w.length then min (min (u.getD t 0) 3 + w.getD t 0) 3
      else 0 := by
  rw [cap_gd, cap_gd, z_gd, cap_len, List.length_map]
  by_cases h : t < S.length ∧ t < u.length ∧ t < w.length
  · have h4 : t < min S.length u.length ∧ t < w.length := ⟨by omega, h.2.2⟩
    have h5 : t < S.length ∧ t < u.length := ⟨h.1, h.2.1⟩
    rw [if_pos h, if_pos h4, if_pos h5, Nat.zero_add]
  · have h4 : ¬(t < min S.length u.length ∧ t < w.length) := by omega
    rw [if_neg h, if_neg h4]

def Dom (u v : List ℕ) : Prop := ∀ t, u.getD t 0 ≤ v.getD t 0

theorem dom_refl (v : List ℕ) : Dom v v := fun _ => le_rfl

theorem dom_trans {u v w : List ℕ} (h1 : Dom u v) (h2 : Dom v w) : Dom u w :=
  fun t => le_trans (h1 t) (h2 t)

def RegV (S : List ℕ) (v : List ℕ) : Prop := v.length = S.length ∧ ∀ t, v.getD t 0 ≤ 3

theorem dom_and (S u w u2 w2 : List ℕ) (hu : u.length = S.length) (hw : w.length = S.length)
    (h1 : Dom u2 u) (h2 : Dom w2 w) :
    Dom (capAdd 2 (capAdd 2 (S.map fun _ => 0) u2) w2)
      (capAdd 2 (capAdd 2 (S.map fun _ => 0) u) w) := by
  intro t
  rw [cap2_gd, cap2_gd]
  have a1 := h1 t
  have a2 := h2 t
  split_ifs <;> omega

theorem dom_right (S u w : List ℕ) (hu : RegV S u) (hw : RegV S w) :
    Dom w (capAdd 2 (capAdd 2 (S.map fun _ => 0) u) w) := by
  intro t
  rw [cap2_gd]
  have a := hw.2 t
  by_cases h : t < S.length
  · have hc : t < S.length ∧ t < u.length ∧ t < w.length :=
      ⟨h, by rw [hu.1]; exact h, by rw [hw.1]; exact h⟩
    rw [if_pos hc]
    omega
  · rw [List.getD_eq_default w 0 (by rw [hw.1]; omega)]
    exact Nat.zero_le _

theorem dom_left (S u w : List ℕ) (hu : RegV S u) (hw : RegV S w) :
    Dom u (capAdd 2 (capAdd 2 (S.map fun _ => 0) u) w) := by
  intro t
  rw [cap2_gd]
  have a := hu.2 t
  by_cases h : t < S.length
  · have hc : t < S.length ∧ t < u.length ∧ t < w.length :=
      ⟨h, by rw [hu.1]; exact h, by rw [hw.1]; exact h⟩
    rw [if_pos hc]
    omega
  · rw [List.getD_eq_default u 0 (by rw [hu.1]; omega)]
    exact Nat.zero_le _

theorem dom_one (S u : List ℕ) (hu : RegV S u) : Dom u (capAdd 2 (S.map fun _ => 0) u) := by
  intro t
  rw [cap_gd, z_gd, List.length_map]
  have a := hu.2 t
  by_cases h : t < S.length
  · have hc : t < S.length ∧ t < u.length := ⟨h, by rw [hu.1]; exact h⟩
    rw [if_pos hc]
    omega
  · rw [List.getD_eq_default u 0 (by rw [hu.1]; omega)]
    exact Nat.zero_le _

theorem reg_cap (S a b : List ℕ) (ha : a.length = S.length) (hb : b.length = S.length) :
    RegV S (capAdd 2 a b) := by
  refine ⟨by rw [cap_len, ha, hb, Nat.min_self], fun t => ?_⟩
  rw [cap_gd]
  split_ifs <;> omega

theorem reg_zero (S : List ℕ) : RegV S (S.map fun _ => 0) :=
  ⟨by simp, fun t => by rw [z_gd]; omega⟩

theorem reg_leaf (S : List ℕ) (k : ℕ) (v : List ℕ) (h : v ∈ leafVectors S 2 k) : RegV S v := by
  unfold leafVectors at h
  split_ifs at h with hk
  · rw [List.mem_singleton] at h
    subst h
    refine ⟨by simp, fun t => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases S[t]? with
    | none => simp
    | some j =>
      show (if j = k then min 1 (2 + 1) else 0) ≤ 3
      split_ifs <;> omega
  · simp at h

theorem reg_andFold (S : List ℕ) : ∀ (L : List (List (List ℕ))) (acc : List (List ℕ)),
    (∀ v ∈ acc, RegV S v) → (∀ A ∈ L, ∀ v ∈ A, RegV S v) →
      ∀ v ∈ L.foldl (andStep 2) acc, RegV S v
  | [], acc, h1, _ => h1
  | B :: L, acc, h1, h2 => by
    rw [List.foldl_cons]
    refine reg_andFold S L _ ?_ (fun A hA => h2 A (List.mem_cons_of_mem _ hA))
    intro v hv
    rw [mem_andStep] at hv
    obtain ⟨p, hp, q, hq, rfl⟩ := hv
    exact reg_cap S p q (h1 p hp).1 (h2 B (by simp) q hq).1

theorem reg (n : ℕ) (S : List ℕ) : ∀ (gs : List Gate) (k : ℕ),
    ∀ v ∈ (run (cell S) gs (ini n S)).getD k [], RegV S v := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro k v hv
    by_cases hk : k < n
    · have e : (run (cell S) [] (ini n S)).getD k [] = leafVectors S 2 k := by
        simp [run, ini, List.getD_eq_getElem?_getD, hk]
      rw [e] at hv
      exact reg_leaf S k v hv
    · rw [List.getD_eq_default _ _ (by simp [run, ini]; omega)] at hv
      simp at hv
  | append_singleton gs g ih =>
    intro k v hv
    rw [run_snoc] at hv
    have hl : (run (cell S) gs (ini n S)).length = n + gs.length := by
      rw [run_len]; simp [ini]
    rcases Nat.lt_trichotomy k (n + gs.length) with h | h | h
    · rw [gd_left _ _ _ _ (by rw [hl]; exact h)] at hv
      exact ih k v hv
    · have hk : k = (run (cell S) gs (ini n S)).length := by rw [hl]; exact h
      rw [hk, gd_last] at hv
      obtain ⟨op, ins⟩ := g
      cases op with
      | or =>
        have hv2 : v ∈ (ins.map fun i => (run (cell S) gs (ini n S)).getD i []).foldl
            (fun acc A => A.foldl insertNew acc) [] := hv
        rw [mem_orFold] at hv2
        rcases hv2 with hv3 | ⟨A, hA, hv3⟩
        · simp at hv3
        · rw [List.mem_map] at hA
          obtain ⟨i, _, rfl⟩ := hA
          exact ih i v hv3
      | and =>
        have hv2 : v ∈ (ins.map fun i => (run (cell S) gs (ini n S)).getD i []).foldl
            (andStep 2) [S.map fun _ => 0] := hv
        refine reg_andFold S _ _ ?_ ?_ v hv2
        · intro u hu
          rw [List.mem_singleton] at hu
          subst hu
          exact reg_zero S
        · intro A hA u hu
          rw [List.mem_map] at hA
          obtain ⟨i, _, rfl⟩ := hA
          exact ih i u hu
      | not =>
        have hv2 : v ∈ ([] : List (List ℕ)) := hv
        simp at hv2
      | mod m =>
        have hv2 : v ∈ ([] : List (List ℕ)) := hv
        simp at hv2
      | maj =>
        have hv2 : v ∈ ([] : List (List ℕ)) := hv
        simp at hv2
    · rw [List.getD_eq_default _ _
        (by rw [List.length_append, List.length_singleton, hl]; omega)] at hv
      simp at hv

def RT {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∀ x, f x = true

def RF {n : ℕ} (f : (Fin n → Bool) → Bool) (A : List ℕ → List (List ℕ)) : Prop :=
  (∀ x, f x = false) ∧ ∀ S, A S = []

def RI (n : ℕ) (ng : List Gate) (f : (Fin n → Bool) → Bool) (A : List ℕ → List (List ℕ))
    (i : ℕ) : Prop :=
  i < n + ng.length ∧ (∀ x, f x = (run ev ng (List.ofFn x)).getD i false) ∧
    ∀ S v, v ∈ A S → ∃ v2 ∈ (run (cell S) ng (ini n S)).getD i [], Dom v2 v

def Rel (n : ℕ) (ng : List Gate) (f : (Fin n → Bool) → Bool) (A : List ℕ → List (List ℕ)) :
    Bool ⊕ ℕ → Prop
  | Sum.inl true => RT f
  | Sum.inl false => RF f A
  | Sum.inr i => RI n ng f A i

def OK2 (n L : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n + L

theorem la (n : ℕ) (ng : List Gate) (x : Fin n → Bool) :
    (run ev ng (List.ofFn x)).length = n + ng.length := by
  rw [run_len]; simp

theorem lb (n : ℕ) (ng : List Gate) (S : List ℕ) :
    (run (cell S) ng (ini n S)).length = n + ng.length := by
  rw [run_len]; simp [ini]

theorem RI_ext (n : ℕ) (ng ext : List Gate) (f : (Fin n → Bool) → Bool)
    (A : List ℕ → List (List ℕ)) (i : ℕ) (h : RI n ng f A i) : RI n (ng ++ ext) f A i := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [List.length_append]; omega, fun x => ?_, fun S v hv => ?_⟩
  · rw [run_app, run_keep _ _ _ _ _ (by rw [la]; exact h1)]
    exact h2 x
  · rw [run_app, run_keep _ _ _ _ _ (by rw [lb]; exact h1)]
    exact h3 S v hv

theorem Rel_ext (n : ℕ) (ng ext : List Gate) (f : (Fin n → Bool) → Bool)
    (A : List ℕ → List (List ℕ)) (s : Bool ⊕ ℕ) (h : Rel n ng f A s) :
    Rel n (ng ++ ext) f A s := by
  rcases s with (_ | _) | i
  · exact h
  · exact h
  · exact RI_ext n ng ext f A i h

theorem Rel_mono (n : ℕ) (ng : List Gate) (f f2 : (Fin n → Bool) → Bool)
    (A A2 : List ℕ → List (List ℕ)) (s : Bool ⊕ ℕ) (h1 : ∀ x, f2 x = f x)
    (h2 : ∀ S v, v ∈ A2 S → ∃ u ∈ A S, Dom u v) (h : Rel n ng f A s) : Rel n ng f2 A2 s := by
  rcases s with (_ | _) | i
  · have h5 : RF f A := h
    have h6 : RF f2 A2 := by
      refine ⟨fun x => by rw [h1, h5.1], fun S => ?_⟩
      rw [List.eq_nil_iff_forall_not_mem]
      intro v hv
      obtain ⟨u, hu, _⟩ := h2 S v hv
      rw [h5.2 S] at hu
      simp at hu
    exact h6
  · have h5 : RT f := h
    have h6 : RT f2 := fun x => by rw [h1, h5 x]
    exact h6
  · have h5 : RI n ng f A i := h
    obtain ⟨a, b, c⟩ := h5
    have h6 : RI n ng f2 A2 i := by
      refine ⟨a, fun x => by rw [h1, b], fun S v hv => ?_⟩
      obtain ⟨u, hu, hd⟩ := h2 S v hv
      obtain ⟨v2, hv2, hd2⟩ := c S u hu
      exact ⟨v2, hv2, dom_trans hd2 hd⟩
    exact h6

theorem new_and (n : ℕ) (ng : List Gate) (fa fb f : (Fin n → Bool) → Bool)
    (Aa Ab A : List ℕ → List (List ℕ)) (i j : ℕ)
    (hi : RI n ng fa Aa i) (hj : RI n ng fb Ab j)
    (ra : ∀ S, ∀ v ∈ Aa S, RegV S v) (rb : ∀ S, ∀ v ∈ Ab S, RegV S v)
    (h1 : ∀ x, f x = (fa x && fb x))
    (h2 : ∀ S v, v ∈ A S → ∃ u ∈ Aa S, ∃ w ∈ Ab S,
      capAdd 2 (capAdd 2 (S.map fun _ => 0) u) w = v) :
    RI n (ng ++ [⟨GateOp.and, [i, j]⟩]) f A (n + ng.length) := by
  obtain ⟨i1, i2, i3⟩ := hi
  obtain ⟨j1, j2, j3⟩ := hj
  refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun x => ?_,
    fun S v hv => ?_⟩
  · rw [run_snoc, ← la n ng x, gd_last, h1, i2, j2]
    simp [ev, GateOp.eval]
  · rw [run_snoc, ← lb n ng S, gd_last]
    obtain ⟨u, hu, w, hw, rfl⟩ := h2 S v hv
    obtain ⟨u2, hu2, du⟩ := i3 S u hu
    obtain ⟨w2, hw2, dw⟩ := j3 S w hw
    refine ⟨capAdd 2 (capAdd 2 (S.map fun _ => 0) u2) w2, ?_,
      dom_and S u w u2 w2 (ra S u hu).1 (rb S w hw).1 du dw⟩
    show _ ∈ andStep 2 (andStep 2 [S.map fun _ => 0] ((run (cell S) ng (ini n S)).getD i []))
      ((run (cell S) ng (ini n S)).getD j [])
    rw [mem_andStep]
    refine ⟨_, ?_, w2, hw2, rfl⟩
    rw [mem_andStep]
    exact ⟨_, List.mem_singleton.mpr rfl, u2, hu2, rfl⟩

theorem new_or (n : ℕ) (ng : List Gate) (fa fb f : (Fin n → Bool) → Bool)
    (Aa Ab A : List ℕ → List (List ℕ)) (i j : ℕ)
    (hi : RI n ng fa Aa i) (hj : RI n ng fb Ab j)
    (h1 : ∀ x, f x = (fa x || fb x))
    (h2 : ∀ S v, v ∈ A S → v ∈ Aa S ∨ v ∈ Ab S) :
    RI n (ng ++ [⟨GateOp.or, [i, j]⟩]) f A (n + ng.length) := by
  obtain ⟨i1, i2, i3⟩ := hi
  obtain ⟨j1, j2, j3⟩ := hj
  refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun x => ?_,
    fun S v hv => ?_⟩
  · rw [run_snoc, ← la n ng x, gd_last, h1, i2, j2]
    simp [ev, GateOp.eval]
  · rw [run_snoc, ← lb n ng S, gd_last]
    show ∃ v2 ∈ ((run (cell S) ng (ini n S)).getD j []).foldl insertNew
      (((run (cell S) ng (ini n S)).getD i []).foldl insertNew []), Dom v2 v
    rcases h2 S v hv with hu | hw
    · obtain ⟨u2, hu2, du⟩ := i3 S v hu
      exact ⟨u2, by rw [mem_foldl_insertNew, mem_foldl_insertNew]; exact Or.inl (Or.inr hu2), du⟩
    · obtain ⟨w2, hw2, dw⟩ := j3 S v hw
      exact ⟨w2, by rw [mem_foldl_insertNew]; exact Or.inr hw2, dw⟩

theorem and2 (n : ℕ) (ng : List Gate) (fa fb f : (Fin n → Bool) → Bool)
    (Aa Ab A : List ℕ → List (List ℕ)) (sa sb : Bool ⊕ ℕ)
    (ha : Rel n ng fa Aa sa) (hb : Rel n ng fb Ab sb)
    (ra : ∀ S, ∀ v ∈ Aa S, RegV S v) (rb : ∀ S, ∀ v ∈ Ab S, RegV S v)
    (h1 : ∀ x, f x = (fa x && fb x))
    (h2 : ∀ S v, v ∈ A S → ∃ u ∈ Aa S, ∃ w ∈ Ab S,
      capAdd 2 (capAdd 2 (S.map fun _ => 0) u) w = v) :
    ∃ (ext : List Gate) (s : Bool ⊕ ℕ), ext.length ≤ 1 ∧ (∀ g2 ∈ ext, OK2 n ng.length g2) ∧
      Rel n (ng ++ ext) f A s := by
  have nilA : ∀ S, (Aa S = [] ∨ Ab S = []) → A S = [] := by
    intro S h
    rw [List.eq_nil_iff_forall_not_mem]
    intro v hv
    obtain ⟨u, hu, w, hw, _⟩ := h2 S v hv
    rcases h with h | h
    · rw [h] at hu
      simp at hu
    · rw [h] at hw
      simp at hw
  rcases sa with (_ | _) | i
  · have ha2 : RF fa Aa := ha
    refine ⟨[], Sum.inl false, by simp, by simp, ?_⟩
    rw [List.append_nil]
    have h6 : RF f A := ⟨fun x => by simp [h1, ha2.1 x], fun S => nilA S (Or.inl (ha2.2 S))⟩
    exact h6
  · have ha2 : RT fa := ha
    refine ⟨[], sb, by simp, by simp, ?_⟩
    rw [List.append_nil]
    refine Rel_mono n ng fb f Ab A sb (fun x => by simp [h1, ha2 x]) ?_ hb
    intro S v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := h2 S v hv
    exact ⟨w, hw, dom_right S u w (ra S u hu) (rb S w hw)⟩
  · have ha2 : RI n ng fa Aa i := ha
    rcases sb with (_ | _) | j
    · have hb2 : RF fb Ab := hb
      refine ⟨[], Sum.inl false, by simp, by simp, ?_⟩
      rw [List.append_nil]
      have h6 : RF f A := ⟨fun x => by simp [h1, hb2.1 x], fun S => nilA S (Or.inr (hb2.2 S))⟩
      exact h6
    · have hb2 : RT fb := hb
      refine ⟨[], Sum.inr i, by simp, by simp, ?_⟩
      rw [List.append_nil]
      refine Rel_mono n ng fa f Aa A (Sum.inr i) (fun x => by simp [h1, hb2 x]) ?_ ha
      intro S v hv
      obtain ⟨u, hu, w, hw, rfl⟩ := h2 S v hv
      exact ⟨u, hu, dom_left S u w (ra S u hu) (rb S w hw)⟩
    · have hb2 : RI n ng fb Ab j := hb
      refine ⟨[⟨GateOp.and, [i, j]⟩], Sum.inr (n + ng.length), by simp, ?_, ?_⟩
      · intro g2 hg2
        rw [List.mem_singleton] at hg2
        subst hg2
        refine ⟨Or.inl rfl, rfl, ?_⟩
        intro t ht
        have ht2 : t ∈ [i, j] := ht
        simp at ht2
        rcases ht2 with rfl | rfl
        · exact ha2.1
        · exact hb2.1
      · exact new_and n ng fa fb f Aa Ab A i j ha2 hb2 ra rb h1 h2

theorem or2 (n : ℕ) (ng : List Gate) (fa fb f : (Fin n → Bool) → Bool)
    (Aa Ab A : List ℕ → List (List ℕ)) (sa sb : Bool ⊕ ℕ)
    (ha : Rel n ng fa Aa sa) (hb : Rel n ng fb Ab sb)
    (h1 : ∀ x, f x = (fa x || fb x))
    (h2 : ∀ S v, v ∈ A S → v ∈ Aa S ∨ v ∈ Ab S) :
    ∃ (ext : List Gate) (s : Bool ⊕ ℕ), ext.length ≤ 1 ∧ (∀ g2 ∈ ext, OK2 n ng.length g2) ∧
      Rel n (ng ++ ext) f A s := by
  rcases sa with (_ | _) | i
  · have ha2 : RF fa Aa := ha
    refine ⟨[], sb, by simp, by simp, ?_⟩
    rw [List.append_nil]
    refine Rel_mono n ng fb f Ab A sb (fun x => by simp [h1, ha2.1 x]) ?_ hb
    intro S v hv
    rcases h2 S v hv with h | h
    · rw [ha2.2 S] at h
      simp at h
    · exact ⟨v, h, dom_refl v⟩
  · have ha2 : RT fa := ha
    refine ⟨[], Sum.inl true, by simp, by simp, ?_⟩
    rw [List.append_nil]
    have h6 : RT f := fun x => by simp [h1, ha2 x]
    exact h6
  · have ha2 : RI n ng fa Aa i := ha
    rcases sb with (_ | _) | j
    · have hb2 : RF fb Ab := hb
      refine ⟨[], Sum.inr i, by simp, by simp, ?_⟩
      rw [List.append_nil]
      refine Rel_mono n ng fa f Aa A (Sum.inr i) (fun x => by simp [h1, hb2.1 x]) ?_ ha
      intro S v hv
      rcases h2 S v hv with h | h
      · exact ⟨v, h, dom_refl v⟩
      · rw [hb2.2 S] at h
        simp at h
    · have hb2 : RT fb := hb
      refine ⟨[], Sum.inl true, by simp, by simp, ?_⟩
      rw [List.append_nil]
      have h6 : RT f := fun x => by simp [h1, hb2 x]
      exact h6
    · have hb2 : RI n ng fb Ab j := hb
      refine ⟨[⟨GateOp.or, [i, j]⟩], Sum.inr (n + ng.length), by simp, ?_, ?_⟩
      · intro g2 hg2
        rw [List.mem_singleton] at hg2
        subst hg2
        refine ⟨Or.inr rfl, rfl, ?_⟩
        intro t ht
        have ht2 : t ∈ [i, j] := ht
        simp at ht2
        rcases ht2 with rfl | rfl
        · exact ha2.1
        · exact hb2.1
      · exact new_or n ng fa fb f Aa Ab A i j ha2 hb2 h1 h2

theorem gate_step (n : ℕ) (ng : List Gate) (W : (Fin n → Bool) → List Bool)
    (RV : List ℕ → List (List (List ℕ)))
    (hreg : ∀ S k, ∀ v ∈ (RV S).getD k [], RegV S v)
    (ih : ∀ k, ∃ s, Rel n ng (fun x => (W x).getD k false) (fun S => (RV S).getD k []) s) :
    ∀ (op : GateOp) (ins : List ℕ), (op = GateOp.and ∨ op = GateOp.or) → ins.length ≤ 2 →
      ∃ (ext : List Gate) (s : Bool ⊕ ℕ), ext.length ≤ 1 ∧
        (∀ g2 ∈ ext, OK2 n ng.length g2) ∧
        Rel n (ng ++ ext) (fun x => ev (W x) ⟨op, ins⟩) (fun S => cell S (RV S) ⟨op, ins⟩) s
  | op, [], hop, _ => by
    rcases hop with rfl | rfl
    · refine ⟨[], Sum.inl true, by simp, by simp, ?_⟩
      have h6 : RT (fun x : Fin n → Bool => ev (W x) ⟨GateOp.and, []⟩) := fun x => rfl
      exact h6
    · refine ⟨[], Sum.inl false, by simp, by simp, ?_⟩
      have h6 : RF (fun x : Fin n → Bool => ev (W x) ⟨GateOp.or, []⟩)
          (fun S => cell S (RV S) ⟨GateOp.or, []⟩) := ⟨fun x => rfl, fun S => rfl⟩
      exact h6
  | op, [a], hop, _ => by
    obtain ⟨s, hs⟩ := ih a
    refine ⟨[], s, by simp, by simp, ?_⟩
    rw [List.append_nil]
    rcases hop with rfl | rfl
    · refine Rel_mono n ng _ _ _ _ s (fun x => by simp [ev, GateOp.eval]) ?_ hs
      intro S v hv
      have hv2 : v ∈ andStep 2 [S.map fun _ => 0] ((RV S).getD a []) := hv
      rw [mem_andStep] at hv2
      obtain ⟨p, hp, q, hq, rfl⟩ := hv2
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨q, hq, dom_one S q (hreg S a q hq)⟩
    · refine Rel_mono n ng _ _ _ _ s (fun x => by simp [ev, GateOp.eval]) ?_ hs
      intro S v hv
      have hv2 : v ∈ ((RV S).getD a []).foldl insertNew [] := hv
      rw [mem_foldl_insertNew] at hv2
      rcases hv2 with h | h
      · simp at h
      · exact ⟨v, h, dom_refl v⟩
  | op, [a, b], hop, _ => by
    obtain ⟨sa, ha⟩ := ih a
    obtain ⟨sb, hb⟩ := ih b
    rcases hop with rfl | rfl
    · refine and2 n ng _ _ _ _ _ _ sa sb ha hb (fun S => hreg S a) (fun S => hreg S b)
        (fun x => by simp [ev, GateOp.eval]) ?_
      intro S v hv
      have hv2 : v ∈ andStep 2 (andStep 2 [S.map fun _ => 0] ((RV S).getD a []))
          ((RV S).getD b []) := hv
      rw [mem_andStep] at hv2
      obtain ⟨p, hp, w, hw, rfl⟩ := hv2
      rw [mem_andStep] at hp
      obtain ⟨z, hz, u, hu, rfl⟩ := hp
      rw [List.mem_singleton] at hz
      subst hz
      exact ⟨u, hu, w, hw, rfl⟩
    · refine or2 n ng _ _ _ _ _ _ sa sb ha hb (fun x => by simp [ev, GateOp.eval]) ?_
      intro S v hv
      have hv2 : v ∈ ((RV S).getD b []).foldl insertNew
          (((RV S).getD a []).foldl insertNew []) := hv
      rw [mem_foldl_insertNew, mem_foldl_insertNew] at hv2
      rcases hv2 with (h | h) | h
      · simp at h
      · exact Or.inl h
      · exact Or.inr h
  | op, _ :: _ :: _ :: _, _, h => by
    have h7 := h
    simp only [List.length_cons] at h7
    omega

theorem main (n : ℕ) : ∀ gs : List Gate,
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∃ ng : List Gate, ng.length ≤ gs.length ∧ (∀ j (h : j < ng.length), OK2 n j ng[j]) ∧
      ∀ k, ∃ s, Rel n ng (fun x : Fin n → Bool => (run ev gs (List.ofFn x)).getD k false)
        (fun S => (run (cell S) gs (ini n S)).getD k []) s := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], le_rfl, fun j h => absurd h (by simp), fun k => ?_⟩
    by_cases hk : k < n
    · refine ⟨Sum.inr k, ?_⟩
      show RI n [] _ _ k
      exact ⟨by simpa using hk, fun x => rfl, fun S v hv => ⟨v, hv, dom_refl v⟩⟩
    · refine ⟨Sum.inl false, ?_⟩
      show RF _ _
      exact ⟨fun x => List.getD_eq_default _ _ (by rw [la]; simp; omega),
        fun S => List.getD_eq_default _ _ (by rw [lb]; simp; omega)⟩
  | append_singleton gs g ih =>
    intro hall
    obtain ⟨ng, hlen, hok, hrel⟩ := ih (fun g2 hg2 => hall g2 (List.mem_append_left _ hg2))
    have hg := hall g (by simp)
    obtain ⟨ext, s, he1, he2, he3⟩ := gate_step n ng (fun x => run ev gs (List.ofFn x))
      (fun S => run (cell S) gs (ini n S)) (fun S k v hv => reg n S gs k v hv) hrel
      g.op g.inputs hg.1 hg.2
    refine ⟨ng ++ ext, by rw [List.length_append, List.length_append, List.length_singleton]; omega,
      ?_, fun k => ?_⟩
    · intro j hj
      by_cases h : j < ng.length
      · rw [List.getElem_append_left h]
        exact hok j h
      · have hmem : (ng ++ ext)[j] ∈ ext := by
          rw [List.getElem_append_right (by omega)]
          exact List.getElem_mem _
        obtain ⟨o1, o2, o3⟩ := he2 _ hmem
        refine ⟨o1, o2, fun t ht => ?_⟩
        have o4 := o3 t ht
        omega
    · rcases Nat.lt_trichotomy k (n + gs.length) with h | h | h
      · obtain ⟨s0, hs0⟩ := hrel k
        refine ⟨s0, ?_⟩
        have e1 : (fun x : Fin n → Bool => (run ev (gs ++ [g]) (List.ofFn x)).getD k false)
            = (fun x => (run ev gs (List.ofFn x)).getD k false) := by
          funext x
          rw [run_snoc, gd_left _ _ _ _ (by rw [la]; exact h)]
        have e2 : (fun S => (run (cell S) (gs ++ [g]) (ini n S)).getD k [])
            = (fun S => (run (cell S) gs (ini n S)).getD k []) := by
          funext S
          rw [run_snoc, gd_left _ _ _ _ (by rw [lb]; exact h)]
        rw [e1, e2]
        exact Rel_ext n ng ext _ _ s0 hs0
      · refine ⟨s, ?_⟩
        have e1 : (fun x : Fin n → Bool => (run ev (gs ++ [g]) (List.ofFn x)).getD k false)
            = (fun x => ev (run ev gs (List.ofFn x)) g) := by
          funext x
          rw [run_snoc, h, ← la n gs x, gd_last]
        have e2 : (fun S => (run (cell S) (gs ++ [g]) (ini n S)).getD k [])
            = (fun S => cell S (run (cell S) gs (ini n S)) g) := by
          funext S
          rw [run_snoc, h, ← lb n gs S, gd_last]
        rw [e1, e2]
        exact he3
      · refine ⟨Sum.inl false, ?_⟩
        show RF _ _
        exact ⟨fun x => List.getD_eq_default _ _
            (by rw [la, List.length_append, List.length_singleton]; omega),
          fun S => List.getD_eq_default _ _
            (by rw [lb, List.length_append, List.length_singleton]; omega)⟩

theorem fin (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (h0 : circuitFun n C (fun _ => false) = false)
    (h1 : ∃ x : Fin n → Bool, circuitFun n C x = true) :
    ∃ C2 : Circuit, IsAO2 n C2 ∧ C2.size ≤ C.size ∧ circuitFun n C2 = circuitFun n C ∧
      ∀ (S : List ℕ) (v : List ℕ), v ∈ (readVectors C n S 2).getD C.output [] →
        ∃ v2 ∈ (readVectors C2 n S 2).getD C2.output [], ∀ i : ℕ, v2.getD i 0 ≤ v.getD i 0 := by
  obtain ⟨ng, hlen, hok, hrel⟩ := main n C.gates (fun g hg => by
    have h5 := hM g hg
    simpa using h5)
  obtain ⟨s, hs⟩ := hrel C.output
  rcases s with (_ | _) | i
  · have hs2 : RF (fun x : Fin n → Bool => (run ev C.gates (List.ofFn x)).getD C.output false)
        (fun S => (run (cell S) C.gates (ini n S)).getD C.output []) := hs
    obtain ⟨x, hx⟩ := h1
    have e : circuitFun n C x = false := hs2.1 x
    rw [e] at hx
    exact absurd hx (by simp)
  · have hs2 : RT (fun x : Fin n → Bool => (run ev C.gates (List.ofFn x)).getD C.output false) :=
      hs
    have e : circuitFun n C (fun _ => false) = true := hs2 _
    rw [e] at h0
    exact absurd h0 (by simp)
  · have hs2 : RI n ng (fun x : Fin n → Bool => (run ev C.gates (List.ofFn x)).getD C.output false)
        (fun S => (run (cell S) C.gates (ini n S)).getD C.output []) i := hs
    obtain ⟨i1, i2, i3⟩ := hs2
    refine ⟨⟨ng, i⟩, ⟨?_, ?_, ?_⟩, hlen, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact (hok j hj).1
    · intro j hj i0 hi0
      rw [gateAt_eq _ j hj] at hi0
      exact (hok j hj).2.2 i0 hi0
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact (hok j hj).2.1
    · funext x
      exact (i2 x).symm
    · intro S v hv
      exact i3 S v hv


end P2471

theorem s2471 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.circuitFun n C (fun _ => false) = false → (∃ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ C'.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C ∧ ∀ (S : List ℕ) (v : List ℕ), v ∈ (PEqualNP.ReadK.readVectors C n S 2).getD C.output [] → ∃ v' ∈ (PEqualNP.ReadK.readVectors C' n S 2).getD C'.output [], ∀ i : ℕ, v'.getD i 0 ≤ v.getD i 0 := by
  intro n C hM h0 h1
  exact PEqualNP.Outside.L_meta_2494.P2471.fin n C hM h0 h1

end Sec2471

section Sec2500

namespace P2500


section Sec2493

namespace P2493


section Sec2477

namespace P2477


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_pre (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_pre _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_or2 (C : Circuit) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (u1 u2 : ℕ) (hin : (gateAt C k).inputs = [u1, u2])
    (u : ℕ) (hu : u = u1 ∨ u = u2) (hlt : u < n + k) (hv : val C.gates u x = true) :
    val C.gates (n + k) x = true := by
  rw [gateAt_eq C k hk] at hop hin
  exact (val_or C.gates x k hk hop).mpr ⟨u, by rw [hin]; simpa using hu, hlt, hv⟩

def rcell (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def rf (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  gs.foldl (fun R g => R ++ [rcell S k R g]) R

def ini (S : List ℕ) (n : ℕ) : List (List (List ℕ)) := (List.range n).map (leafVectors S 2)

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) :
    readVectors C n S 2 = rf S 2 C.gates (ini S n) := rfl

lemma rf_len (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ R : List (List (List ℕ)), (rf S k gs R).length = R.length + gs.length := by
  induction gs with
  | nil => intro R; simp [rf]
  | cons g gs ih =>
    intro R
    have := ih (R ++ [rcell S k R g])
    simp only [rf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma rf_keep (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ (R : List (List (List ℕ))) (i : ℕ), i < R.length →
      (rf S k gs R).getD i [] = R.getD i [] := by
  induction gs with
  | nil => intro R i _; rfl
  | cons g gs ih =>
    intro R i hi
    have := ih (R ++ [rcell S k R g]) i (by simp; omega)
    simp only [rf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma rcell_congr (S : List ℕ) (k : ℕ) (R R2 : List (List (List ℕ))) (g : Gate)
    (h : ∀ i ∈ g.inputs, R.getD i [] = R2.getD i []) : rcell S k R g = rcell S k R2 g := by
  unfold rcell
  rw [List.map_congr_left h]

def V (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S 2).getD w []

lemma V_gate (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    V C n S (n + j) = rcell S 2 (readVectors C n S 2) (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre, hgj⟩ := split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [gateAt_eq C j hj]; exact hgj
  rw [hga] at hrb ⊢
  have hc : readVectors C n S 2
      = rf S 2 post (rf S 2 pre (ini S n) ++ [rcell S 2 (rf S 2 pre (ini S n)) gj]) := by
    rw [rv_eq, hgs]
    simp only [rf, List.foldl_append, List.foldl_cons]
  have hl : (rf S 2 pre (ini S n)).length = n + j := by
    rw [rf_len]; simp [ini, hpre]
  have h1 : V C n S (n + j) = rcell S 2 (rf S 2 pre (ini S n)) gj := by
    unfold V
    rw [hc, rf_keep _ _ _ _ _ (by simp; omega), ← hl]
    simp [List.getD_eq_getElem?_getD]
  rw [h1]
  apply rcell_congr
  intro i hi
  have hlt : i < (rf S 2 pre (ini S n)).length := by rw [hl]; exact hrb i hi
  rw [hc, rf_keep S 2 post _ i (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

lemma V_leaf (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : w < n) :
    V C n S w = leafVectors S 2 w := by
  unfold V
  rw [rv_eq, rf_keep _ _ _ _ _ (by simp [ini]; exact hw)]
  simp [ini, List.getD_eq_getElem?_getD, hw]

lemma V_big (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    V C n S w = [] := by
  unfold V
  rw [List.getD_eq_default _ _ (by rw [rv_eq, rf_len]; simp [ini]; exact hw)]

lemma mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | rfl)
      · exact h1
      · exact h
  · simp

lemma mem_foldl_insertNew (L : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (x : List ℕ), x ∈ L.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ L := by
  induction L with
  | nil => intro acc x; simp
  | cons v L ih =>
    intro acc x
    rw [List.foldl_cons, ih, mem_insertNew]
    simp [or_assoc]

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, capAdd k p q = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap, List.mem_map]

lemma V_or (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (u1 u2 : ℕ) (hin : (gateAt C j).inputs = [u1, u2])
    (h1 : u1 < n + j) (h2 : u2 < n + j) (x : List ℕ) :
    x ∈ V C n S (n + j) ↔ x ∈ V C n S u1 ∨ x ∈ V C n S u2 := by
  rw [V_gate C n S j hj (by rw [hin]; intro i hi; simp at hi; omega)]
  simp only [rcell, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    mem_foldl_insertNew]
  simp [V]

lemma V_and (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (u1 u2 : ℕ) (hin : (gateAt C j).inputs = [u1, u2])
    (h1 : u1 < n + j) (h2 : u2 < n + j) (x : List ℕ) :
    x ∈ V C n S (n + j) ↔ ∃ p ∈ V C n S u1, ∃ q ∈ V C n S u2,
      capAdd 2 (capAdd 2 (S.map fun _ => 0) p) q = x := by
  rw [V_gate C n S j hj (by rw [hin]; intro i hi; simp at hi; omega)]
  simp only [rcell, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    mem_andStep, List.mem_singleton]
  constructor
  · rintro ⟨p2, ⟨z, rfl, p, hp, rfl⟩, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨_, ⟨_, rfl, p, hp, rfl⟩, q, hq, rfl⟩

lemma cap2 (a b x y x2 y2 : ℕ) :
    capAdd 2 (capAdd 2 (([a, b] : List ℕ).map fun _ => 0) [x, y]) [x2, y2]
      = [min (min x 3 + x2) 3, min (min y 3 + y2) 3] := by
  simp [capAdd]

lemma mem_leaf (a b w : ℕ) (v : List ℕ) :
    v ∈ leafVectors [a, b] 2 w ↔
      (w = a ∨ w = b) ∧ v = [if a = w then 1 else 0, if b = w then 1 else 0] := by
  unfold leafVectors
  by_cases h : w = a ∨ w = b
  · simp [h]
  · simp [h]

lemma wire_cases (n : ℕ) (C : Circuit) (h : IsAO2 n C) (w : ℕ) :
    w < n ∨ n + C.gates.length ≤ w ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧
      ∃ u1 u2, (gateAt C k).inputs = [u1, u2] ∧ u1 < n + k ∧ u2 < n + k ∧
        ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) := by
  obtain ⟨hao, hrb, hlen⟩ := h
  by_cases h1 : w < n
  · exact Or.inl h1
  by_cases h2 : n + C.gates.length ≤ w
  · exact Or.inr (Or.inl h2)
  right; right
  have hk : w - n < C.gates.length := by omega
  have hmem : gateAt C (w - n) ∈ C.gates := by
    rw [gateAt_eq C _ hk]; exact List.getElem_mem hk
  obtain ⟨u1, u2, hab⟩ := List.length_eq_two.mp (hlen _ hmem)
  exact ⟨w - n, hk, by omega, u1, u2, hab, hrb _ hk u1 (by rw [hab]; simp),
    hrb _ hk u2 (by rw [hab]; simp), hao _ hmem⟩


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


lemma swp (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ t, ∀ v ∈ V C n [a, b] t, ∃ x y : ℕ, v = [x, y] ∧ [y, x] ∈ V C n [b, a] t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv
    rcases wire_cases n C h t with ht | ht | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · rw [V_leaf C n _ t ht] at hv
      obtain ⟨hm, rfl⟩ := (mem_leaf a b t v).mp hv
      refine ⟨_, _, rfl, ?_⟩
      rw [V_leaf C n _ t ht]
      exact (mem_leaf b a t _).mpr ⟨hm.symm, rfl⟩
    · rw [V_big C n _ t ht] at hv
      simp at hv
    · obtain ⟨p, hp, q, hq, rfl⟩ := (V_and C n _ k hk hop u1 u2 hin h1 h2 v).mp hv
      obtain ⟨x, y, rfl, hs⟩ := ih u1 (by omega) p hp
      obtain ⟨x2, y2, rfl, hs2⟩ := ih u2 (by omega) q hq
      rw [cap2]
      refine ⟨_, _, rfl, ?_⟩
      exact (V_and C n _ k hk hop u1 u2 hin h1 h2 _).mpr ⟨_, hs, _, hs2, cap2 b a y x y2 x2⟩
    · rcases (V_or C n _ k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · obtain ⟨x, y, rfl, hs⟩ := ih u1 h1 v h3
        exact ⟨x, y, rfl, (V_or C n _ k hk hop u1 u2 hin h1 h2 _).mpr (Or.inl hs)⟩
      · obtain ⟨x, y, rfl, hs⟩ := ih u2 h2 v h3
        exact ⟨x, y, rfl, (V_or C n _ k hk hop u1 u2 hin h1 h2 _).mpr (Or.inr hs)⟩


lemma nz (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ w, ∀ v ∈ V C n [a, b] w, ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x + y := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases wire_cases n C h w with hw | hw | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · rw [V_leaf C n _ w hw] at hv
      obtain ⟨hm, rfl⟩ := (mem_leaf a b w v).mp hv
      refine ⟨_, _, rfl, ?_⟩
      rcases hm with hm | hm
      · simp [hm]
      · simp [hm]
    · rw [V_big C n _ w hw] at hv
      simp at hv
    · obtain ⟨p, hp, q, hq, rfl⟩ := (V_and C n _ k hk hop u1 u2 hin h1 h2 v).mp hv
      obtain ⟨x, y, rfl, hxy⟩ := ih u1 (by omega) p hp
      obtain ⟨x2, y2, rfl, hxy2⟩ := ih u2 (by omega) q hq
      rw [cap2]
      exact ⟨_, _, rfl, by omega⟩
    · rcases (V_or C n _ k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · exact ih u1 (by omega) v h3
      · exact ih u2 (by omega) v h3

lemma climb (n : ℕ) (C : Circuit) (h : IsAO2 n C) (S : List ℕ) (v : List ℕ) (P : ℕ → Prop)
    (hleaf : ∀ t, t < n → v ∈ V C n S t → P t)
    (hand : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
      v ∈ V C n S (n + k) → P (n + k))
    (hor : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ ui, ui ∈ (gateAt C k).inputs → ui < n + k → P ui → P (n + k)) :
    ∀ t, v ∈ V C n S t → P t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hv
    rcases wire_cases n C h t with ht | ht | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · exact hleaf t ht hv
    · rw [V_big C n S t ht] at hv
      simp at hv
    · exact hand k hk hop hv
    · rcases (V_or C n S k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · exact hor k hk hop u1 (by rw [hin]; simp) h1 (ih u1 h1 h3)
      · exact hor k hk hop u2 (by rw [hin]; simp) h2 (ih u2 h2 h3)

lemma leaf_vec (n : ℕ) (C : Circuit) (a b t : ℕ) (ht : t < n) (s r : ℕ)
    (hv : [s, r] ∈ V C n [a, b] t) :
    (t = a ∨ t = b) ∧ s = (if a = t then 1 else 0) ∧ r = (if b = t then 1 else 0) := by
  rw [V_leaf C n _ t ht] at hv
  obtain ⟨hm, he⟩ := (mem_leaf a b t _).mp hv
  injection he with e1 e2
  injection e2 with e2 e3
  exact ⟨hm, e1, e2⟩

lemma and_split (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (s r : ℕ) (hv : [s, r] ∈ V C n [a, b] (n + k)) :
    ∃ u1 u2 x y x2 y2 : ℕ, (gateAt C k).inputs = [u1, u2] ∧ [x, y] ∈ V C n [a, b] u1 ∧
      [x2, y2] ∈ V C n [a, b] u2 ∧ 1 ≤ x + y ∧ 1 ≤ x2 + y2 ∧
      min (min x 3 + x2) 3 = s ∧ min (min y 3 + y2) 3 = r := by
  rcases wire_cases n C h (n + k) with hw | hw | ⟨k2, hk2, e, u1, u2, hin, h1, h2, _⟩
  · omega
  · omega
  · have hkk : k2 = k := by omega
    subst hkk
    obtain ⟨p, hp, q, hq, he⟩ := (V_and C n _ k2 hk2 hop u1 u2 hin h1 h2 _).mp hv
    obtain ⟨x, y, rfl, hxy⟩ := nz n C h a b u1 p hp
    obtain ⟨x2, y2, rfl, hxy2⟩ := nz n C h a b u2 q hq
    rw [cap2] at he
    injection he with e1 e2
    injection e2 with e2 e3
    exact ⟨u1, u2, x, y, x2, y2, hin, hp, hq, hxy, hxy2, e1, e2⟩

def Reach (n : ℕ) (C : Circuit) (a t : ℕ) : Prop :=
  ∃ i : Fin n, i.val = a ∧ i ∈ orIn n C t

def AG (C : Circuit) (j K F : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [K, F] ∨ (gateAt C j).inputs = [F, K])

def T0 (n : ℕ) (C : Circuit) (a b t : ℕ) : Prop :=
  ∃ j K F, AG C j K F ∧ Reach n C a K ∧ Reach n C b F ∧ OrReaches n C t j

def DD (n : ℕ) (C : Circuit) (b t : ℕ) : Prop :=
  ∃ j F4 F5, AG C j F4 F5 ∧ Reach n C b F4 ∧ Reach n C b F5 ∧ OrReaches n C t j

def T1 (n : ℕ) (C : Circuit) (a b t : ℕ) : Prop :=
  ∃ j2 j3 K F V1 F3, AG C j2 K F ∧ Reach n C a K ∧ Reach n C b F ∧ OrReaches n C V1 j2 ∧
    AG C j3 V1 F3 ∧ Reach n C b F3 ∧ OrReaches n C t j3

def T2 (n : ℕ) (C : Circuit) (a b t : ℕ) : Prop :=
  ∃ j4 j5 F4 F5 U1 K, AG C j4 F4 F5 ∧ Reach n C b F4 ∧ Reach n C b F5 ∧ OrReaches n C U1 j4 ∧
    AG C j5 K U1 ∧ Reach n C a K ∧ OrReaches n C t j5

lemma OrR_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (orReaches_iff n C k k hk).mpr (Or.inl rfl)

lemma OrR_up (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (ui : ℕ) (hin2 : ui ∈ (gateAt C k).inputs)
    (hlt : ui < n + k) (j : ℕ) (hr : OrReaches n C ui j) : OrReaches n C (n + k) j :=
  (orReaches_iff n C j k hk).mpr
    (Or.inr ⟨hop, ui, hin2, (show n ≤ ui ∧ _ from hr).1, hlt, hr⟩)

lemma Reach_leaf (n : ℕ) (C : Circuit) (t : ℕ) (ht : t < n) : Reach n C t t := by
  refine ⟨⟨t, ht⟩, rfl, ?_⟩
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  first | exact Or.inl rfl | exact Or.inl trivial

lemma Reach_up (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (ui : ℕ) (hin2 : ui ∈ (gateAt C k).inputs)
    (hlt : ui < n + k) (a : ℕ) (hr : Reach n C a ui) : Reach n C a (n + k) := by
  obtain ⟨i, hi, ho⟩ := hr
  refine ⟨i, hi, ?_⟩
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
  right
  rcases ho with ho | ⟨k2, hk2, hr2, hop2, hmem2⟩
  · exact ⟨k, hk, OrR_self n C k hk, hop, by rw [ho]; exact hin2⟩
  · exact ⟨k2, hk2, OrR_up n C k hk hop ui hin2 hlt k2 hr2, hop2, hmem2⟩

lemma RA (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ t, [1, 0] ∈ V C n [a, b] t → Reach n C a t := by
  apply climb n C h [a, b] [1, 0] (fun t => Reach n C a t)
  · intro t ht hv
    obtain ⟨_, e1, _⟩ := leaf_vec n C a b t ht 1 0 hv
    have hat : a = t := by
      by_contra hne
      simp [hne] at e1
    subst hat
    exact Reach_leaf n C a ht
  · intro k hk hop hv
    exfalso
    obtain ⟨u1, u2, x, y, x2, y2, _, _, _, hxy, hxy2, e1, e2⟩ :=
      and_split n C h a b k hk hop 1 0 hv
    omega
  · intro k hk hop ui hin2 hlt hP
    exact Reach_up n C k hk hop ui hin2 hlt a hP

lemma swp1 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b t s r : ℕ)
    (hv : [s, r] ∈ V C n [a, b] t) : [r, s] ∈ V C n [b, a] t := by
  obtain ⟨x, y, e, hs⟩ := swp n C h a b t _ hv
  injection e with e1 e2
  injection e2 with e2 e3
  subst e1
  subst e2
  exact hs

lemma RB (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ t, [0, 1] ∈ V C n [a, b] t → Reach n C b t := by
  intro t hv
  exact RA n C h b a t (swp1 n C h a b t 0 1 hv)

lemma P0 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) (hne : a ≠ b) :
    ∀ t, [1, 1] ∈ V C n [a, b] t → T0 n C a b t := by
  apply climb n C h [a, b] [1, 1] (fun t => T0 n C a b t)
  · intro t ht hv
    exfalso
    obtain ⟨_, e1, e2⟩ := leaf_vec n C a b t ht 1 1 hv
    by_cases c1 : a = t
    · by_cases c2 : b = t
      · exact hne (c1.trans c2.symm)
      · simp [c2] at e2
    · simp [c1] at e1
  · intro k hk hop hv
    obtain ⟨u1, u2, x, y, x2, y2, hin, hp, hq, hxy, hxy2, e1, e2⟩ :=
      and_split n C h a b k hk hop 1 1 hv
    have hcase : (x = 1 ∧ y = 0 ∧ x2 = 0 ∧ y2 = 1) ∨ (x = 0 ∧ y = 1 ∧ x2 = 1 ∧ y2 = 0) := by
      omega
    rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨k, u1, u2, ⟨hk, hop, Or.inl hin⟩, RA n C h a b u1 hp, RB n C h a b u2 hq,
        OrR_self n C k hk⟩
    · exact ⟨k, u2, u1, ⟨hk, hop, Or.inr hin⟩, RA n C h a b u2 hq, RB n C h a b u1 hp,
        OrR_self n C k hk⟩
  · intro k hk hop ui hin2 hlt hP
    obtain ⟨j, K, F, hg, hK, hF, hr⟩ := hP
    exact ⟨j, K, F, hg, hK, hF, OrR_up n C k hk hop ui hin2 hlt j hr⟩

lemma PD (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) :
    ∀ t, [0, 2] ∈ V C n [a, b] t → DD n C b t := by
  apply climb n C h [a, b] [0, 2] (fun t => DD n C b t)
  · intro t ht hv
    exfalso
    obtain ⟨_, _, e2⟩ := leaf_vec n C a b t ht 0 2 hv
    by_cases c2 : b = t
    · simp [c2] at e2
    · simp [c2] at e2
  · intro k hk hop hv
    obtain ⟨u1, u2, x, y, x2, y2, hin, hp, hq, hxy, hxy2, e1, e2⟩ :=
      and_split n C h a b k hk hop 0 2 hv
    have hcase : x = 0 ∧ y = 1 ∧ x2 = 0 ∧ y2 = 1 := by omega
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
    exact ⟨k, u1, u2, ⟨hk, hop, Or.inl hin⟩, RB n C h a b u1 hp, RB n C h a b u2 hq,
      OrR_self n C k hk⟩
  · intro k hk hop ui hin2 hlt hP
    obtain ⟨j, K, F, hg, hK, hF, hr⟩ := hP
    exact ⟨j, K, F, hg, hK, hF, OrR_up n C k hk hop ui hin2 hlt j hr⟩

lemma P12 (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) (hne : a ≠ b) :
    ∀ t, [1, 2] ∈ V C n [a, b] t → T1 n C a b t ∨ T2 n C a b t := by
  apply climb n C h [a, b] [1, 2] (fun t => T1 n C a b t ∨ T2 n C a b t)
  · intro t ht hv
    exfalso
    obtain ⟨_, _, e2⟩ := leaf_vec n C a b t ht 1 2 hv
    by_cases c2 : b = t
    · simp [c2] at e2
    · simp [c2] at e2
  · intro k hk hop hv
    obtain ⟨u1, u2, x, y, x2, y2, hin, hp, hq, hxy, hxy2, e1, e2⟩ :=
      and_split n C h a b k hk hop 1 2 hv
    have hcase : (x = 1 ∧ y = 0 ∧ x2 = 0 ∧ y2 = 2) ∨ (x = 1 ∧ y = 1 ∧ x2 = 0 ∧ y2 = 1) ∨
        (x = 0 ∧ y = 1 ∧ x2 = 1 ∧ y2 = 1) ∨ (x = 0 ∧ y = 2 ∧ x2 = 1 ∧ y2 = 0) := by
      omega
    rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩
    · right
      obtain ⟨j4, F4, F5, hg, h4, h5, hr⟩ := PD n C h a b u2 hq
      exact ⟨j4, k, F4, F5, u2, u1, hg, h4, h5, hr, ⟨hk, hop, Or.inl hin⟩, RA n C h a b u1 hp,
        OrR_self n C k hk⟩
    · left
      obtain ⟨j2, K, F, hg, hK, hF, hr⟩ := P0 n C h a b hne u1 hp
      exact ⟨j2, k, K, F, u1, u2, hg, hK, hF, hr, ⟨hk, hop, Or.inl hin⟩, RB n C h a b u2 hq,
        OrR_self n C k hk⟩
    · left
      obtain ⟨j2, K, F, hg, hK, hF, hr⟩ := P0 n C h a b hne u2 hq
      exact ⟨j2, k, K, F, u2, u1, hg, hK, hF, hr, ⟨hk, hop, Or.inr hin⟩, RB n C h a b u1 hp,
        OrR_self n C k hk⟩
    · right
      obtain ⟨j4, F4, F5, hg, h4, h5, hr⟩ := PD n C h a b u1 hp
      exact ⟨j4, k, F4, F5, u1, u2, hg, h4, h5, hr, ⟨hk, hop, Or.inr hin⟩, RA n C h a b u2 hq,
        OrR_self n C k hk⟩
  · intro k hk hop ui hin2 hlt hP
    rcases hP with hP | hP
    · left
      obtain ⟨j2, j3, K, F, V1, F3, g1, g2, g3, g4, g5, g6, hr⟩ := hP
      exact ⟨j2, j3, K, F, V1, F3, g1, g2, g3, g4, g5, g6, OrR_up n C k hk hop ui hin2 hlt j3 hr⟩
    · right
      obtain ⟨j4, j5, F4, F5, U1, K, g1, g2, g3, g4, g5, g6, hr⟩ := hP
      exact ⟨j4, j5, F4, F5, U1, K, g1, g2, g3, g4, g5, g6, OrR_up n C k hk hop ui hin2 hlt j5 hr⟩

lemma main (n : ℕ) (C : Circuit) (h : IsAO2 n C) (a b : ℕ) (hne : a ≠ b) (t : ℕ)
    (hv : [1, 1] ∈ V C n [a, b] t ∨ [1, 2] ∈ V C n [a, b] t) :
    T0 n C a b t ∨ T1 n C a b t ∨ T2 n C a b t := by
  rcases hv with hv | hv
  · exact Or.inl (P0 n C h a b hne t hv)
  · exact Or.inr (P12 n C h a b hne t hv)


end P2477

theorem s2477 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ), PEqualNP.TopForm.IsAO2 n C → u < n → w < n → u ≠ w → (([1, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output []) → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = u ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = w ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = u ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = w ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = w ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = w ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = w ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = u ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) ∧ ([2, 1] ∈ (PEqualNP.ReadK.readVectors C n [u, w] 2).getD C.output [] → ((∃ j_6 K_4 F_6, (j_6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [K_4, F_6] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_6).inputs = [F_6, K_4])) ∧ (∃ i_9 : Fin n, i_9.val = w ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (K_4)) ∧ (∃ i_10 : Fin n, i_10.val = u ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_6) ∨ (∃ j_7 j_8 K_5 F_7 V_2 F_8, (j_7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [K_5, F_7] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_7).inputs = [F_7, K_5])) ∧ (∃ i_11 : Fin n, i_11.val = w ∧ i_11 ∈ PEqualNP.TopForm.orIn n C (K_5)) ∧ (∃ i_12 : Fin n, i_12.val = u ∧ i_12 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_7 ∧ (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [V_2, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [F_8, V_2])) ∧ (∃ i_13 : Fin n, i_13.val = u ∧ i_13 ∈ PEqualNP.TopForm.orIn n C (F_8)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_8) ∨ (∃ j_9 j_10 F_9 F_10 U_2 K_6, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_9, F_10] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_10, F_9])) ∧ (∃ i_14 : Fin n, i_14.val = u ∧ i_14 ∈ PEqualNP.TopForm.orIn n C (F_9)) ∧ (∃ i_15 : Fin n, i_15.val = u ∧ i_15 ∈ PEqualNP.TopForm.orIn n C (F_10)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [K_6, U_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [U_2, K_6])) ∧ (∃ i_16 : Fin n, i_16.val = w ∧ i_16 ∈ PEqualNP.TopForm.orIn n C (K_6)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10))) := by
  intro n C u w h _ _ hne
  exact ⟨PEqualNP.Outside.L_meta_2494.P2500.P2493.P2477.main n C h u w hne C.output,
    fun h21 => PEqualNP.Outside.L_meta_2494.P2500.P2493.P2477.main n C h w u (Ne.symm hne) C.output
      (Or.inr (PEqualNP.Outside.L_meta_2494.P2500.P2493.P2477.swp1 n C h u w C.output 2 1 h21))⟩

end Sec2477

section Sec2490

namespace P2490


section Sec2485

namespace P2485


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

theorem snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

theorem all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true → (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

theorem any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true → (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem run_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (runW gs w).getD i false = true → (runW gs w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact run_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine run_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · have e : ∀ z : Fin n → Bool, (List.ofFn z).getD k false = z ⟨k, hk⟩ := fun z => by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e x, e y]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem wires_eq (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    wireVal n C w x = val C.gates w x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    val gs (n + k) x = true ↔ ∀ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → val C.gates (n + j) x = true → val C.gates b x = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hv
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hv
      exact hv
    · rw [gateAt_eq C k hk] at hop hi
      exact (val_or C.gates x k hk hop).2 ⟨i, hi, hlt, ih i (by omega) hr hv⟩

theorem mem_filter' {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

theorem orIn_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (b : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C b) (hv : val C.gates i.val x = true) : val C.gates b x = true := by
  have hi2 : (i : ℕ) = b ∨ ∃ k < C.gates.length,
      OrReaches n C b k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs :=
    ((mem_filter' _ _ _ _).mp hi).2
  rcases hi2 with h1 | ⟨k, hk, hr, hop, hin⟩
  · rw [h1] at hv
    exact hv
  · rw [gateAt_eq C k hk] at hop hin
    have hlt : i.val < n + k := by
      have := i.isLt
      omega
    exact reach_up n C x k b hr ((val_or C.gates x k hk hop).2 ⟨i.val, hin, hlt, hv⟩)

theorem or_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ)
    (h : (∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C b) ∨
      (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C b j_1))
    (hv : val C.gates a x = true) : val C.gates b x = true := by
  rcases h with ⟨i, hia, hi⟩ | ⟨j, haj, hr⟩
  · rw [← hia] at hv
    exact orIn_up n C x b i hi hv
  · rw [haj] at hv
    exact reach_up n C x j b hr hv

theorem and_eq (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    val C.gates (n + j) x = (val C.gates ((gateAt C j).inputs.getD 0 0) x &&
      val C.gates ((gateAt C j).inputs.getD 1 0) x) := by
  obtain ⟨_, hrb, hlen⟩ := hC
  have hrbj := hrb j hj
  rw [gateAt_eq C j hj] at hop hrbj ⊢
  have hl := hlen C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  have hva := val_and C.gates x j hj hop
  rw [hab] at hrbj hva ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [Bool.eq_iff_iff, Bool.and_eq_true, hva]
  constructor
  · intro h
    exact ⟨(h a (by simp)).2, (h b (by simp)).2⟩
  · rintro ⟨h0, h1⟩ i hi
    have hi2 : i = a ∨ i = b := by simpa using hi
    rcases hi2 with h2 | h2
    · rw [h2]
      exact ⟨hrbj a (by simp), h0⟩
    · rw [h2]
      exact ⟨hrbj b (by simp), h1⟩

theorem val_input (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gs w x = x ⟨w, hw⟩ := by
  rw [val, fd_keep stB false gs _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def xs (n : ℕ) {K : ℕ} (f : Fin K → ℕ) (a : Fin K) : Fin n → Bool :=
  fun k => decide (k.val = f a)

def sh (n : ℕ) (C : Circuit) {K : ℕ} (f : Fin K → ℕ) (w : ℕ) : Set (Fin K) :=
  {a | wireVal n C w (fun k : Fin n => decide (k.val = f a)) = true}

def xin (n : ℕ) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (P : Finset (Fin N))
    (Y : Finset (Fin M)) : Fin n → Bool :=
  fun k => decide (k.val ∈ P.image pw ∪ Y.image lw)

def IsAnd (C : Circuit) (j a b : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [a, b] ∨ (gateAt C j).inputs = [b, a])

def Rch (n : ℕ) (C : Circuit) (a F : ℕ) : Prop :=
  (∃ i : Fin n, i.val = a ∧ i ∈ orIn n C F) ∨ (∃ j : ℕ, a = n + j ∧ OrReaches n C F j)

def Concl (n : ℕ) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (p : Fin N) (l : Fin M) : Prop :=
  (∃ a F, Rch n C a F ∧ sh n C lw a = {l} ∧ sh n C lw F ⊆ {m | I p m} ∧
      2 ≤ (sh n C lw F).ncard) ∨
  (∃ a F, Rch n C a F ∧ sh n C pw a = {p} ∧ sh n C pw F ⊆ {m | I m l} ∧
      2 ≤ (sh n C pw F).ncard) ∨
  (∃ j a b, IsAnd C j a b ∧ sh n C pw a = {p} ∧ sh n C lw b = {l}) ∨
  (∃ j K F V j2 F2 m, IsAnd C j K F ∧ sh n C pw K = {p} ∧ m ∈ sh n C lw F ∧ ¬ I p m ∧
      OrReaches n C V j ∧ IsAnd C j2 V F2 ∧ sh n C lw F2 = {l} ∧ OrReaches n C C.output j2)

theorem mem_sh (n : ℕ) (C : Circuit) {K : ℕ} (f : Fin K → ℕ) (w : ℕ) (a : Fin K) :
    a ∈ sh n C f w ↔ val C.gates w (xs n f a) = true := Iff.rfl

theorem and_iff (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j a b : ℕ)
    (h : IsAnd C j a b) :
    val C.gates (n + j) x = true ↔ val C.gates a x = true ∧ val C.gates b x = true := by
  obtain ⟨hj, hop, hin⟩ := h
  rw [and_eq n C hC x j hj hop, Bool.and_eq_true]
  rcases hin with h | h
  · rw [h]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · rw [h]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact and_comm

theorem up_p (n : ℕ) (C : Circuit) (hC : IsAO2 n C) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (P : Finset (Fin N)) (Y : Finset (Fin M)) (a : Fin N) (ha : a ∈ P) (w : ℕ)
    (h : val C.gates w (xs n pw a) = true) : val C.gates w (xin n pw lw P Y) = true := by
  refine wires_mono C hC.1 _ _ ?_ w h
  intro k hk
  have e : k.val = pw a := of_decide_eq_true hk
  show decide (k.val ∈ P.image pw ∪ Y.image lw) = true
  rw [decide_eq_true_eq, e]
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw ha)

theorem up_l (n : ℕ) (C : Circuit) (hC : IsAO2 n C) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (P : Finset (Fin N)) (Y : Finset (Fin M)) (a : Fin M) (ha : a ∈ Y) (w : ℕ)
    (h : val C.gates w (xs n lw a) = true) : val C.gates w (xin n pw lw P Y) = true := by
  refine wires_mono C hC.1 _ _ ?_ w h
  intro k hk
  have e : k.val = lw a := of_decide_eq_true hk
  show decide (k.val ∈ P.image pw ∪ Y.image lw) = true
  rw [decide_eq_true_eq, e]
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw ha)

theorem snd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (hC : IsAO2 n C)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) = false)
    (A B D : ℕ)
    (hout : ∀ x : Fin n → Bool, val C.gates A x = true → val C.gates B x = true →
      val C.gates D x = true → val C.gates C.output x = true)
    (a : Fin N) (m m2 : Fin M) (ha : a ∈ sh n C pw A) (hm : m ∈ sh n C lw B)
    (hm2 : m2 ∈ sh n C lw D) : I a m ∨ I a m2 := by
  by_contra hno
  rw [not_or] at hno
  have hs := hsound {a} {m, m2} (by simp) Finset.card_le_two (by
    intro p3 hp3 l3 hl3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp3 hl3
    rcases hl3 with f | f
    · rw [hp3, f]
      exact hno.1
    · rw [hp3, f]
      exact hno.2)
  have ht : val C.gates C.output (xin n pw lw {a} {m, m2}) = true :=
    hout _ (up_p n C hC pw lw _ _ a (Finset.mem_singleton_self a) A ((mem_sh n C pw A a).1 ha))
      (up_l n C hC pw lw _ _ m (Finset.mem_insert_self m _) B ((mem_sh n C lw B m).1 hm))
      (up_l n C hC pw lw _ _ m2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self m2)) D
        ((mem_sh n C lw D m2).1 hm2))
  have hs2 : val C.gates C.output (xin n pw lw {a} {m, m2}) = false := hs
  rw [ht] at hs2
  exact Bool.noConfusion hs2

theorem sh_input (n : ℕ) (C : Circuit) {K : ℕ} (f : Fin K → ℕ) (hf : Function.Injective f)
    (hn : ∀ a, f a < n) (p : Fin K) : sh n C f (f p) = {p} := by
  ext a
  rw [mem_sh, val_input C.gates _ _ (hn p)]
  show decide (f p = f a) = true ↔ _
  rw [decide_eq_true_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact (hf h).symm
  · intro h
    rw [h]

theorem sh_orIn (n : ℕ) (C : Circuit) {K : ℕ} (f : Fin K → ℕ) (a : Fin K) (w : ℕ)
    (h : ∃ i : Fin n, i.val = f a ∧ i ∈ orIn n C w) : a ∈ sh n C f w := by
  obtain ⟨i, hi, hin⟩ := h
  rw [mem_sh]
  refine orIn_up n C (xs n f a) w i hin ?_
  rw [val_input C.gates _ _ i.isLt]
  show decide (i.val = f a) = true
  exact decide_eq_true hi

theorem two_le {K : ℕ} (S : Set (Fin K)) (a : Fin K) (ha : a ∈ S) (hne : S ≠ {a}) :
    2 ≤ S.ncard := by
  have hex : ∃ b ∈ S, b ≠ a := by
    by_contra h
    push_neg at h
    exact hne (Set.eq_singleton_iff_unique_mem.2 ⟨ha, h⟩)
  obtain ⟨b, hb, hba⟩ := hex
  exact (Set.one_lt_ncard_iff (Set.toFinite S)).2 ⟨a, b, ha, hb, fun e => hba e.symm⟩

theorem t0 (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (p : Fin N) (l : Fin M) (hC : IsAO2 n C)
    (hpi : Function.Injective pw) (hli : Function.Injective lw)
    (hpn : ∀ a, pw a < n) (hln : ∀ a, lw a < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) = false)
    (j K F : ℕ) (hj : IsAnd C j K F)
    (hK : ∃ i : Fin n, i.val = pw p ∧ i ∈ orIn n C K)
    (hF : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F)
    (hout : OrReaches n C C.output j) : Concl n pw lw I C p l := by
  unfold Concl
  have hpK : p ∈ sh n C pw K := sh_orIn n C pw p K hK
  have hlF : l ∈ sh n C lw F := sh_orIn n C lw l F hF
  have ho : ∀ x : Fin n → Bool, val C.gates K x = true → val C.gates F x = true →
      val C.gates F x = true → val C.gates C.output x = true := by
    intro x hk hf _
    exact reach_up n C x j _ hout ((and_iff n C hC x j K F hj).2 ⟨hk, hf⟩)
  have key := fun a m m2 => snd n N M pw lw I C hC hsound K F F ho a m m2
  have hKs : sh n C pw K ⊆ {m | I m l} := fun a ha => (key a l l ha hlF hlF).elim id id
  have hFs : sh n C lw F ⊆ {m | I p m} := fun m hm => (key p m m hpK hm hm).elim id id
  by_cases h1 : sh n C pw K = {p}
  · by_cases h2 : sh n C lw F = {l}
    · exact Or.inr (Or.inr (Or.inl ⟨j, K, F, hj, h1, h2⟩))
    · exact Or.inl ⟨lw l, F, Or.inl hF, sh_input n C lw hli hln l, hFs, two_le _ l hlF h2⟩
  · exact Or.inr (Or.inl ⟨pw p, K, Or.inl hK, sh_input n C pw hpi hpn p, hKs,
      two_le _ p hpK h1⟩)

theorem t1 (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (p : Fin N) (l : Fin M) (hC : IsAO2 n C)
    (hpi : Function.Injective pw) (hli : Function.Injective lw)
    (hpn : ∀ a, pw a < n) (hln : ∀ a, lw a < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) = false)
    (j2 j3 K F2 V F3 : ℕ) (hj2 : IsAnd C j2 K F2)
    (hK : ∃ i : Fin n, i.val = pw p ∧ i ∈ orIn n C K)
    (hF2 : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F2)
    (hV : OrReaches n C V j2) (hj3 : IsAnd C j3 V F3)
    (hF3 : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F3)
    (hout : OrReaches n C C.output j3) : Concl n pw lw I C p l := by
  unfold Concl
  have hpK : p ∈ sh n C pw K := sh_orIn n C pw p K hK
  have hl2 : l ∈ sh n C lw F2 := sh_orIn n C lw l F2 hF2
  have hl3 : l ∈ sh n C lw F3 := sh_orIn n C lw l F3 hF3
  have ho : ∀ x : Fin n → Bool, val C.gates K x = true → val C.gates F2 x = true →
      val C.gates F3 x = true → val C.gates C.output x = true := by
    intro x hk hf2 hf3
    exact reach_up n C x j3 _ hout ((and_iff n C hC x j3 V F3 hj3).2
      ⟨reach_up n C x j2 V hV ((and_iff n C hC x j2 K F2 hj2).2 ⟨hk, hf2⟩), hf3⟩)
  have key := fun a m m2 => snd n N M pw lw I C hC hsound K F2 F3 ho a m m2
  have hKs : sh n C pw K ⊆ {m | I m l} := fun a ha => (key a l l ha hl2 hl3).elim id id
  by_cases h1 : sh n C pw K = {p}
  · by_cases h2 : sh n C lw F2 = {l}
    · exact Or.inr (Or.inr (Or.inl ⟨j2, K, F2, hj2, h1, h2⟩))
    · by_cases h3 : sh n C lw F2 ⊆ {m | I p m}
      · exact Or.inl ⟨lw l, F2, Or.inl hF2, sh_input n C lw hli hln l, h3, two_le _ l hl2 h2⟩
      · obtain ⟨m3, hm3, hnm⟩ := Set.not_subset.1 h3
        have hF3s : sh n C lw F3 ⊆ {m | I p m} := fun m hm =>
          (key p m3 m hpK hm3 hm).elim (fun h => (hnm h).elim) id
        by_cases h4 : sh n C lw F3 = {l}
        · exact Or.inr (Or.inr (Or.inr ⟨j2, K, F2, V, j3, F3, m3, hj2, h1, hm3, hnm, hV, hj3,
            h4, hout⟩))
        · exact Or.inl ⟨lw l, F3, Or.inl hF3, sh_input n C lw hli hln l, hF3s,
            two_le _ l hl3 h4⟩
  · exact Or.inr (Or.inl ⟨pw p, K, Or.inl hK, sh_input n C pw hpi hpn p, hKs,
      two_le _ p hpK h1⟩)

theorem t2 (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (p : Fin N) (l : Fin M) (hC : IsAO2 n C)
    (hpi : Function.Injective pw) (hli : Function.Injective lw)
    (hpn : ∀ a, pw a < n) (hln : ∀ a, lw a < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) = false)
    (j4 j5 F4 F5 U K : ℕ) (hj4 : IsAnd C j4 F4 F5)
    (hF4 : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F4)
    (hF5 : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F5)
    (hU : OrReaches n C U j4) (hj5 : IsAnd C j5 K U)
    (hK : ∃ i : Fin n, i.val = pw p ∧ i ∈ orIn n C K)
    (hout : OrReaches n C C.output j5) : Concl n pw lw I C p l := by
  unfold Concl
  have hpK : p ∈ sh n C pw K := sh_orIn n C pw p K hK
  have hl4 : l ∈ sh n C lw F4 := sh_orIn n C lw l F4 hF4
  have hl5 : l ∈ sh n C lw F5 := sh_orIn n C lw l F5 hF5
  have ho : ∀ x : Fin n → Bool, val C.gates K x = true → val C.gates F4 x = true →
      val C.gates F5 x = true → val C.gates C.output x = true := by
    intro x hk h4 h5
    exact reach_up n C x j5 _ hout ((and_iff n C hC x j5 K U hj5).2
      ⟨hk, reach_up n C x j4 U hU ((and_iff n C hC x j4 F4 F5 hj4).2 ⟨h4, h5⟩)⟩)
  have ho2 : ∀ x : Fin n → Bool, val C.gates K x = true → val C.gates U x = true →
      val C.gates U x = true → val C.gates C.output x = true := by
    intro x hk hu _
    exact reach_up n C x j5 _ hout ((and_iff n C hC x j5 K U hj5).2 ⟨hk, hu⟩)
  have key := fun a m m2 => snd n N M pw lw I C hC hsound K F4 F5 ho a m m2
  have key2 := fun a m m2 => snd n N M pw lw I C hC hsound K U U ho2 a m m2
  have hlg : l ∈ sh n C lw (n + j4) :=
    (mem_sh n C lw (n + j4) l).2 ((and_iff n C hC (xs n lw l) j4 F4 F5 hj4).2
      ⟨(mem_sh n C lw F4 l).1 hl4, (mem_sh n C lw F5 l).1 hl5⟩)
  have hgU : sh n C lw (n + j4) ⊆ sh n C lw U := fun m hm =>
    (mem_sh n C lw U m).2 (reach_up n C (xs n lw m) j4 U hU ((mem_sh n C lw (n + j4) m).1 hm))
  have hg4 : sh n C lw (n + j4) ⊆ sh n C lw F4 := fun m hm =>
    (mem_sh n C lw F4 m).2
      ((and_iff n C hC (xs n lw m) j4 F4 F5 hj4).1 ((mem_sh n C lw (n + j4) m).1 hm)).1
  have hg5 : sh n C lw (n + j4) ⊆ sh n C lw F5 := fun m hm =>
    (mem_sh n C lw F5 m).2
      ((and_iff n C hC (xs n lw m) j4 F4 F5 hj4).1 ((mem_sh n C lw (n + j4) m).1 hm)).2
  have hKs : sh n C pw K ⊆ {m | I m l} := fun a ha => (key a l l ha hl4 hl5).elim id id
  have hUs : sh n C lw U ⊆ {m | I p m} := fun m hm => (key2 p m m hpK hm hm).elim id id
  have hlU : l ∈ sh n C lw U := hgU hlg
  by_cases h1 : sh n C pw K = {p}
  · by_cases h2 : sh n C lw U = {l}
    · exact Or.inr (Or.inr (Or.inl ⟨j5, K, U, hj5, h1, h2⟩))
    · by_cases h3 : sh n C lw (n + j4) = {l}
      · exact Or.inl ⟨n + j4, U, Or.inr ⟨j4, rfl, hU⟩, h3, hUs, two_le _ l hlU h2⟩
      · by_cases h4 : sh n C lw F4 ⊆ {m | I p m}
        · exact Or.inl ⟨lw l, F4, Or.inl hF4, sh_input n C lw hli hln l, h4,
            le_trans (two_le _ l hlg h3) (Set.ncard_le_ncard hg4 (Set.toFinite _))⟩
        · obtain ⟨m3, hm3, hnm⟩ := Set.not_subset.1 h4
          have h5s : sh n C lw F5 ⊆ {m | I p m} := fun m hm =>
            (key p m3 m hpK hm3 hm).elim (fun h => (hnm h).elim) id
          exact Or.inl ⟨lw l, F5, Or.inl hF5, sh_input n C lw hli hln l, h5s,
            le_trans (two_le _ l hlg h3) (Set.ncard_le_ncard hg5 (Set.toFinite _))⟩
  · exact Or.inr (Or.inl ⟨pw p, K, Or.inl hK, sh_input n C pw hpi hpn p, hKs,
      two_le _ p hpK h1⟩)


end P2485

theorem s2485 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin N) (l : Fin M), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → I p l → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = pw p ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = lw l ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = pw p ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = lw l ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = lw l ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = lw l ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = lw l ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = pw p ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5)) → (∃ a_1 F_6, ((∃ i_9 : Fin n, i_9.val = a_1 ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∨ (∃ j_6 : ℕ, a_1 = n + j_6 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_6) j_6)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_3 : Fin n => decide (k_3.val = lw a_3)) = true} = {l} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_2 : Fin n => decide (k_2.val = lw a_2)) = true} ⊆ {m_1 | I p m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_4 : Fin n => decide (k_4.val = lw a_4)) = true}).ncard) ∨ (∃ a_5 F_7, ((∃ i_10 : Fin n, i_10.val = a_5 ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∨ (∃ j_7 : ℕ, a_5 = n + j_7 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_7) j_7)) ∧ {a_7 | PEqualNP.CleanedNonEdge.wireVal n C (a_5) (fun k_6 : Fin n => decide (k_6.val = pw a_7)) = true} = {p} ∧ {a_6 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_5 : Fin n => decide (k_5.val = pw a_6)) = true} ⊆ {m_2 | I m_2 l} ∧ 2 ≤ ({a_8 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_7 : Fin n => decide (k_7.val = pw a_8)) = true}).ncard) ∨ (∃ j_8 a_9 b_1, (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [a_9, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [b_1, a_9])) ∧ {a_10 | PEqualNP.CleanedNonEdge.wireVal n C (a_9) (fun k_8 : Fin n => decide (k_8.val = pw a_10)) = true} = {p} ∧ {a_11 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_9 : Fin n => decide (k_9.val = lw a_11)) = true} = {l}) ∨ (∃ j_9 K_4 F_8 V_2 j_10 F_9 m_3, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [K_4, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_8, K_4])) ∧ {a_12 | PEqualNP.CleanedNonEdge.wireVal n C (K_4) (fun k_10 : Fin n => decide (k_10.val = pw a_12)) = true} = {p} ∧ m_3 ∈ {a_13 | PEqualNP.CleanedNonEdge.wireVal n C (F_8) (fun k_11 : Fin n => decide (k_11.val = lw a_13)) = true} ∧ ¬ I p m_3 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [V_2, F_9] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [F_9, V_2])) ∧ {a_14 | PEqualNP.CleanedNonEdge.wireVal n C (F_9) (fun k_12 : Fin n => decide (k_12.val = lw a_14)) = true} = {l} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10) := by
  intro n N M pw lw I C p l hC hw hsound _ hcert
  obtain ⟨hpi, hli, _, hpn, hln⟩ := hw
  rcases hcert with ⟨j1, K1, F1, hj, hK, hF, hout⟩ | ⟨j2, j3, K2, F2, V1, F3, hj2, hK, hF2, hV, hj3, hF3, hout⟩ | ⟨j4, j5, F4, F5, U1, K3, hj4, hF4, hF5, hU, hj5, hK, hout⟩
  · exact PEqualNP.Outside.L_meta_2494.P2500.P2493.P2490.P2485.t0 n N M pw lw I C p l hC hpi hli hpn hln hsound j1 K1 F1 hj hK hF hout
  · exact PEqualNP.Outside.L_meta_2494.P2500.P2493.P2490.P2485.t1 n N M pw lw I C p l hC hpi hli hpn hln hsound j2 j3 K2 F2 V1 F3 hj2 hK hF2 hV hj3 hF3 hout
  · exact PEqualNP.Outside.L_meta_2494.P2500.P2493.P2490.P2485.t2 n N M pw lw I C p l hC hpi hli hpn hln hsound j4 j5 F4 F5 U1 K3 hj4 hF4 hF5 hU hj5 hK hout

end Sec2485

section Sec2482

namespace P2482


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem wires_eq (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    wireVal n C w x = val C.gates w x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → val C.gates (n + j) x = true → val C.gates b x = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hv
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hv
      exact hv
    · rw [gateAt_eq C k hk] at hop hi
      exact (val_or C.gates x k hk hop).2 ⟨i, hi, hlt, ih i (by omega) hr hv⟩

theorem mem_filter' {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

theorem in_two {l : List ℕ} (hl : l.length = 2) {w : ℕ} (hw : w ∈ l) :
    w = l.getD 0 0 ∨ w = l.getD 1 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hw ⊢
    exact hw
  · simp at hl

theorem gate_mem (C : Circuit) {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

def Sh (n M : ℕ) (lw : Fin M → ℕ) (C : Circuit) (w : ℕ) : Set (Fin M) :=
  {m | wireVal n C w (fun k : Fin n => decide (k.val = lw m)) = true}

theorem sh_reach (n M : ℕ) (lw : Fin M → ℕ) (C : Circuit) (b j : ℕ) (h : OrReaches n C b j) :
    Sh n M lw C (n + j) ⊆ Sh n M lw C b := by
  intro m hm
  have hm2 : val C.gates (n + j) (fun k : Fin n => decide (k.val = lw m)) = true := hm
  show val C.gates b (fun k : Fin n => decide (k.val = lw m)) = true
  exact reach_up n C (fun k : Fin n => decide (k.val = lw m)) j b h hm2

theorem sh_in (n M : ℕ) (lw : Fin M → ℕ) (C : Circuit) (k i : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hi : i ∈ (gateAt C k).inputs) (hlt : i < n + k) :
    Sh n M lw C i ⊆ Sh n M lw C (n + k) := by
  intro m hm
  have hm2 : val C.gates i (fun k : Fin n => decide (k.val = lw m)) = true := hm
  show val C.gates (n + k) (fun k : Fin n => decide (k.val = lw m)) = true
  rw [gateAt_eq C k hk] at hop hi
  exact (val_or C.gates (fun k : Fin n => decide (k.val = lw m)) k hk hop).2 ⟨i, hi, hlt, hm2⟩

theorem walk (n : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2) (Q : ℕ → Prop)
    (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → Q (n + j) → ¬ Q b →
      ∃ k, ∃ c : Bool, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        (gateAt C k).inputs.getD (cond c 1 0) 0 ∈ (gateAt C k).inputs ∧
        Q ((gateAt C k).inputs.getD (cond c 1 0) 0) ∧ ¬ Q (n + k) ∧ OrReaches n C b k := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hQ hnQ
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h hnQ ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hQ
      exact absurd hQ hnQ
    · have hself : OrReaches n C (n + k) k := (orReaches_iff n C k k).2 ⟨hk, Or.inl rfl⟩
      by_cases hQi : Q i
      · rcases in_two (hlen _ (gate_mem C hk)) hi with h2 | h2
        · rw [h2] at hi hQi
          exact ⟨k, false, hk, hop, hi, hQi, hnQ, hself⟩
        · rw [h2] at hi hQi
          exact ⟨k, true, hk, hop, hi, hQi, hnQ, hself⟩
      · obtain ⟨k2, c, hk2, hop2, hin2, hQ2, hnQ2, hr2⟩ := ih i (by omega) hr hQ hQi
        exact ⟨k2, c, hk2, hop2, hin2, hQ2, hnQ2,
          (orReaches_iff n C k k2).2 ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr2⟩⟩⟩

theorem climb (n : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2) (Q : ℕ → Prop)
    (a b : ℕ)
    (h : (∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C b) ∨
      (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C b j_1))
    (hQ : Q a) (hnQ : ¬ Q b) :
    ∃ k, ∃ c : Bool, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      (gateAt C k).inputs.getD (cond c 1 0) 0 ∈ (gateAt C k).inputs ∧
      Q ((gateAt C k).inputs.getD (cond c 1 0) 0) ∧ ¬ Q (n + k) ∧ OrReaches n C b k := by
  rcases h with ⟨i, hia, hi⟩ | ⟨j, haj, hr⟩
  · have hi2 : (i : ℕ) = b ∨ ∃ k < C.gates.length,
        OrReaches n C b k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs :=
      ((mem_filter' _ _ _ _).mp hi).2
    rcases hi2 with h1 | ⟨k, hk, hr, hop, hin⟩
    · rw [← hia, h1] at hQ
      exact absurd hQ hnQ
    · by_cases hQk : Q (n + k)
      · exact walk n C hlen Q k b hr hQk hnQ
      · rw [hia] at hin
        rcases in_two (hlen _ (gate_mem C hk)) hin with h2 | h2
        · rw [h2] at hin hQ
          exact ⟨k, false, hk, hop, hin, hQ, hQk, hr⟩
        · rw [h2] at hin hQ
          exact ⟨k, true, hk, hop, hin, hQ, hQk, hr⟩
  · rw [haj] at hQ
    exact walk n C hlen Q j b hr hQ hnQ

theorem count (n N M : ℕ) (C : Circuit) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (hC : IsAO2 n C)
    (hK : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (G : Set (Fin N × Fin M))
    (hG : ∀ e ∈ G, ∃ a F, ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C F) ∨
        (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C F j_1)) ∧
      Sh n M lw C a = {e.2} ∧ Sh n M lw C F ⊆ {m | I e.1 m} ∧ 2 ≤ (Sh n M lw C F).ncard) :
    G.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by
  classical
  obtain ⟨_, hrb, hlen⟩ := hC
  have hOf : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun j hj => hj.1)
  have hex : ∀ e ∈ G, ∃ jb : ℕ × Bool,
      jb.1 ∈ {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} ∧
      Sh n M lw C ((gateAt C jb.1).inputs.getD (cond jb.2 1 0) 0) = {e.2} ∧
      (∀ m ∈ Sh n M lw C (n + jb.1), I e.1 m) ∧
      ∃ m1 m2, m1 ∈ Sh n M lw C (n + jb.1) ∧ m2 ∈ Sh n M lw C (n + jb.1) ∧ m1 ≠ m2 := by
    intro e he
    obtain ⟨a, F, hbel, hSa, hSF, h2⟩ := hG e he
    have hnF : ¬ (Sh n M lw C F = {e.2}) := by
      intro hh
      rw [hh, Set.ncard_singleton] at h2
      omega
    obtain ⟨k, c, hk, hop, hin, hQ, hnQ, hr⟩ :=
      climb n C hlen (fun w => Sh n M lw C w = {e.2}) a F hbel hSa hnF
    have hQ1 : Sh n M lw C ((gateAt C k).inputs.getD (cond c 1 0) 0) = {e.2} := hQ
    have hnQ1 : ¬ (Sh n M lw C (n + k) = {e.2}) := hnQ
    have hsub : Sh n M lw C ((gateAt C k).inputs.getD (cond c 1 0) 0) ⊆ Sh n M lw C (n + k) :=
      sh_in n M lw C k _ hk hop hin (hrb k hk _ hin)
    have hl : e.2 ∈ Sh n M lw C (n + k) := by
      apply hsub
      rw [hQ1]
      exact Set.mem_singleton _
    have hex2 : ∃ m ∈ Sh n M lw C (n + k), m ≠ e.2 := by
      by_contra hcon
      push_neg at hcon
      apply hnQ1
      ext m
      constructor
      · intro hm
        exact Set.mem_singleton_iff.mpr (hcon m hm)
      · intro hm
        rw [Set.mem_singleton_iff.mp hm]
        exact hl
    obtain ⟨m, hm, hne⟩ := hex2
    exact ⟨(k, c), ⟨hk, hop⟩, hQ1, fun m' hm' => hSF (sh_reach n M lw C F k hr hm'),
      e.2, m, hl, hm, Ne.symm hne⟩
  choose! f hf using hex
  calc G.ncard
      ≤ (((fun j : ℕ => (j, true)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}) ∪
          ((fun j : ℕ => (j, false)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or})).ncard := by
        refine Set.ncard_le_ncard_of_injOn f ?_ ?_ ((hOf.image _).union (hOf.image _))
        · intro e he
          have hm := (hf e he).1
          rcases hfe : f e with ⟨j, b⟩
          rw [hfe] at hm
          cases b
          · right
            exact ⟨j, hm, rfl⟩
          · left
            exact ⟨j, hm, rfl⟩
        · intro e he e2 he2 heq
          have h1 := hf e he
          have h2 := hf e2 he2
          rw [← heq] at h2
          obtain ⟨_, hS, hI, m1, m2, hm1, hm2, hne⟩ := h1
          obtain ⟨_, hS2, hI2, _⟩ := h2
          have e3 : e.2 = e2.2 := Set.singleton_injective (hS.symm.trans hS2)
          have e1 : e.1 = e2.1 := by
            by_contra hne1
            exact hK e.1 e2.1 m1 m2 hne1 hne ⟨hI _ hm1, hI2 _ hm1, hI _ hm2, hI2 _ hm2⟩
          exact Prod.ext e1 e3
    _ ≤ ((fun j : ℕ => (j, true)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}).ncard +
          ((fun j : ℕ => (j, false)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}).ncard :=
        Set.ncard_union_le _ _
    _ ≤ {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard +
          {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard :=
        Nat.add_le_add (Set.ncard_image_le hOf) (Set.ncard_image_le hOf)
    _ = 2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by ring


end P2482

theorem s2482 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ a_1 F_1, ((∃ i_1 : Fin n, i_1.val = a_1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∨ (∃ j_1 : ℕ, a_1 = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_1) j_1)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_1 : Fin n => decide (k_1.val = lw a_2)) = true} ⊆ {m_1 | I pl.1 m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_4)) = true}).ncard)) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro n N M pw lw I C A hC hinj hK hA
  rw [← Set.ncard_coe_finset A]
  refine PEqualNP.Outside.L_meta_2494.P2500.P2493.P2490.P2482.count n N M C lw I hC hK _ ?_
  intro e he
  exact (hA e (Finset.mem_coe.mp he)).2

end Sec2482

section Sec2484

namespace P2484


theorem core {α β : Type} (A : Finset (α × β)) (T : Set ℕ) (hfin : T.Finite) (g0 g1 : ℕ → ℕ)
    (P : α → ℕ → Prop) (Q : β → ℕ → Prop)
    (h : ∀ e ∈ A, ∃ (j a b : ℕ), (j ∈ T ∧ ((g0 j = a ∧ g1 j = b) ∨ (g0 j = b ∧ g1 j = a))) ∧
      {x : α | P x a} = {e.1} ∧ {y : β | Q y b} = {e.2}) :
    A.card ≤ 2 * T.ncard := by
  classical
  choose! j a b hj using h
  have key : A.card ≤ (hfin.toFinset ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun e => (j e, decide (g0 (j e) = a e)))
    · intro e he
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨hfin.mem_toFinset.mpr (hj e he).1.1, Finset.mem_univ _⟩)
    · intro e he e1 he1 heq
      simp only [Prod.mk.injEq, decide_eq_decide] at heq
      obtain ⟨hjj, hside⟩ := heq
      obtain ⟨⟨_, hab⟩, h1, h2⟩ := hj e he
      obtain ⟨⟨_, hab1⟩, h11, h21⟩ := hj e1 he1
      rw [← hjj] at hab1 hside
      have haa : a e = a e1 ∧ b e = b e1 := by
        by_cases hc : g0 (j e) = a e
        · have hc1 := hside.mp hc
          refine ⟨hc.symm.trans hc1, ?_⟩
          rcases hab with ⟨_, hb⟩ | ⟨hb, ha⟩ <;> rcases hab1 with ⟨_, hb1⟩ | ⟨hb1, ha1⟩ <;> omega
        · have hc1 : ¬ g0 (j e) = a e1 := fun x => hc (hside.mpr x)
          rcases hab with ⟨ha, _⟩ | ⟨hb, ha⟩
          · exact absurd ha hc
          rcases hab1 with ⟨ha1, _⟩ | ⟨hb1, ha1⟩
          · exact absurd ha1 hc1
          exact ⟨ha.symm.trans ha1, hb.symm.trans hb1⟩
      rw [← haa.1] at h11
      rw [← haa.2] at h21
      exact Prod.ext (Set.singleton_injective (h1.symm.trans h11))
        (Set.singleton_injective (h2.symm.trans h21))
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool,
    ← Set.ncard_eq_toFinset_card T hfin] at key
  omega


end P2484

theorem s2484 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (∀ pl ∈ A, (∃ j_1 a_1 b_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [a_1, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [b_1, a_1])) ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {pl.1} ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2})) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro n N M pw lw C A _ h
  have hfin : {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun x hx => hx.1)
  refine PEqualNP.Outside.L_meta_2494.P2500.P2493.P2490.P2484.core A _ hfin
    (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)
    (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)
    (fun x a => PEqualNP.CleanedNonEdge.wireVal n C a (fun k : Fin n => decide (k.val = pw x)) = true)
    (fun y b => PEqualNP.CleanedNonEdge.wireVal n C b (fun k : Fin n => decide (k.val = lw y)) = true) ?_
  intro e he
  obtain ⟨j, a, b, ⟨hj, hop, hab⟩, h1, h2⟩ := h e he
  refine ⟨j, a, b, ⟨⟨hj, hop⟩, ?_⟩, h1, h2⟩
  rcases hab with hab | hab
  · left
    simp [hab]
  · right
    simp [hab]

end Sec2484

section Sec2489

namespace P2489



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

theorem snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

theorem all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true → (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

theorem any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true → (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem run_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (runW gs w).getD i false = true → (runW gs w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact run_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine run_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · have e : ∀ z : Fin n → Bool, (List.ofFn z).getD k false = z ⟨k, hk⟩ := fun z => by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e x, e y]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem wires_eq (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    wireVal n C w x = val C.gates w x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    val gs (n + k) x = true ↔ ∀ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → val C.gates (n + j) x = true → val C.gates b x = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hv
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hv
      exact hv
    · rw [gateAt_eq C k hk] at hop hi
      exact (val_or C.gates x k hk hop).2 ⟨i, hi, hlt, ih i (by omega) hr hv⟩

theorem mem_filter' {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

theorem orIn_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (b : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C b) (hv : val C.gates i.val x = true) : val C.gates b x = true := by
  have hi2 : (i : ℕ) = b ∨ ∃ k < C.gates.length,
      OrReaches n C b k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs :=
    ((mem_filter' _ _ _ _).mp hi).2
  rcases hi2 with h1 | ⟨k, hk, hr, hop, hin⟩
  · rw [h1] at hv
    exact hv
  · rw [gateAt_eq C k hk] at hop hin
    have hlt : i.val < n + k := by
      have := i.isLt
      omega
    exact reach_up n C x k b hr ((val_or C.gates x k hk hop).2 ⟨i.val, hin, hlt, hv⟩)

theorem or_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ)
    (h : (∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C b) ∨
      (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C b j_1))
    (hv : val C.gates a x = true) : val C.gates b x = true := by
  rcases h with ⟨i, hia, hi⟩ | ⟨j, haj, hr⟩
  · rw [← hia] at hv
    exact orIn_up n C x b i hi hv
  · rw [haj] at hv
    exact reach_up n C x j b hr hv

theorem and_eq (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    val C.gates (n + j) x = (val C.gates ((gateAt C j).inputs.getD 0 0) x &&
      val C.gates ((gateAt C j).inputs.getD 1 0) x) := by
  obtain ⟨_, hrb, hlen⟩ := hC
  have hrbj := hrb j hj
  rw [gateAt_eq C j hj] at hop hrbj ⊢
  have hl := hlen C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  have hva := val_and C.gates x j hj hop
  rw [hab] at hrbj hva ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [Bool.eq_iff_iff, Bool.and_eq_true, hva]
  constructor
  · intro h
    exact ⟨(h a (by simp)).2, (h b (by simp)).2⟩
  · rintro ⟨h0, h1⟩ i hi
    have hi2 : i = a ∨ i = b := by simpa using hi
    rcases hi2 with h2 | h2
    · rw [h2]
      exact ⟨hrbj a (by simp), h0⟩
    · rw [h2]
      exact ⟨hrbj b (by simp), h1⟩

theorem dirty_on (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : Circuit)
    (l : Fin M) (h V F2 j2 : ℕ) (hC : IsAO2 n C)
    (hS : ∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 →
      (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) →
      circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false)
    (hV : (∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ orIn n C V) ∨
      (∃ j_1 : ℕ, h = n + j_1 ∧ OrReaches n C V j_1))
    (hj : j2 < C.gates.length) (hop : (gateAt C j2).op = GateOp.and)
    (hin : (gateAt C j2).inputs = [V, F2] ∨ (gateAt C j2).inputs = [F2, V])
    (hout : OrReaches n C C.output j2)
    (hl : wireVal n C F2 (fun k_2 : Fin n => decide (k_2.val = lw l)) = true)
    (p : Fin N) (m1 : Fin M) (hnI : ¬ I p m1)
    (hw : wireVal n C h (fun k_3 : Fin n => decide (k_3.val ∈ ({pw p, lw m1} : Finset ℕ))) = true) :
    I p l := by
  by_contra hn
  have hz := hS {p} {m1, l} (by simp) Finset.card_le_two (by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha
    rw [Finset.mem_insert, Finset.mem_singleton] at hb
    rw [ha]
    rcases hb with hb | hb
    · rw [hb]; exact hnI
    · rw [hb]; exact hn)
  have h1 : wireVal n C h (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m1, l} : Finset (Fin M)).image lw)) = true := by
    refine wires_mono C hC.1
      (fun k_3 : Fin n => decide (k_3.val ∈ ({pw p, lw m1} : Finset ℕ)))
      (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
        ({m1, l} : Finset (Fin M)).image lw)) ?_ h hw
    intro k hk
    have hk2 := of_decide_eq_true hk
    apply decide_eq_true
    rw [Finset.mem_insert, Finset.mem_singleton] at hk2
    rcases hk2 with e | e
    · rw [e]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw (Finset.mem_singleton_self p))
    · rw [e]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw (Finset.mem_insert_self _ _))
  have h2 : wireVal n C F2 (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m1, l} : Finset (Fin M)).image lw)) = true := by
    refine wires_mono C hC.1
      (fun k_2 : Fin n => decide (k_2.val = lw l))
      (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
        ({m1, l} : Finset (Fin M)).image lw)) ?_ F2 hl
    intro k hk
    have hk2 := of_decide_eq_true hk
    apply decide_eq_true
    rw [hk2]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self l)))
  rw [wires_eq] at h1 h2
  have h3 := or_up n C _ h V hV h1
  have h4 : val C.gates (n + j2) (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m1, l} : Finset (Fin M)).image lw)) = true := by
    rw [and_eq n C hC _ j2 hj hop]
    rcases hin with e | e
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Bool.and_eq_true]
      exact ⟨h3, h2⟩
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Bool.and_eq_true]
      exact ⟨h2, h3⟩
  have h5 := reach_up n C _ j2 C.output hout h4
  have h6 : circuitFun n C (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m1, l} : Finset (Fin M)).image lw)) = true := h5
  rw [hz] at h6
  exact Bool.false_ne_true h6


theorem in_two {l : List ℕ} (hl : l.length = 2) {w : ℕ} (hw : w ∈ l) :
    w = l.getD 0 0 ∨ w = l.getD 1 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hw ⊢
    exact hw
  · simp at hl

theorem gate_mem (C : Circuit) {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj


theorem walk (n : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2) (Q : ℕ → Prop)
    (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → Q (n + j) → ¬ Q b →
      ∃ k, ∃ c : Bool, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        (gateAt C k).inputs.getD (cond c 1 0) 0 ∈ (gateAt C k).inputs ∧
        Q ((gateAt C k).inputs.getD (cond c 1 0) 0) ∧ ¬ Q (n + k) ∧ OrReaches n C b k := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hQ hnQ
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h hnQ ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hQ
      exact absurd hQ hnQ
    · have hself : OrReaches n C (n + k) k := (orReaches_iff n C k k).2 ⟨hk, Or.inl rfl⟩
      by_cases hQi : Q i
      · rcases in_two (hlen _ (gate_mem C hk)) hi with h2 | h2
        · rw [h2] at hi hQi
          exact ⟨k, false, hk, hop, hi, hQi, hnQ, hself⟩
        · rw [h2] at hi hQi
          exact ⟨k, true, hk, hop, hi, hQi, hnQ, hself⟩
      · obtain ⟨k2, c, hk2, hop2, hin2, hQ2, hnQ2, hr2⟩ := ih i (by omega) hr hQ hQi
        exact ⟨k2, c, hk2, hop2, hin2, hQ2, hnQ2,
          (orReaches_iff n C k k2).2 ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr2⟩⟩⟩



section Sec2487

namespace P2487


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def G {α : Type} (src : α → ℕ) (seg : α → ℕ → Prop) (D : ℕ → Finset α) (isOr : ℕ → Prop)
    (g0 g1 : ℕ → ℕ) (p : α) (y x : ℕ) : Prop :=
  seg p y ∧ 2 ≤ (D y).card ∧
    (y = src p ∨ (seg p x ∧ (D x).card < 2 ∧ isOr y ∧ (g0 y = x ∨ g1 y = x)))

theorem core {α : Type} (Pl : Finset α) (src top : α → ℕ) (seg : α → ℕ → Prop)
    (D : ℕ → Finset α) (L : ℕ) (isOr : ℕ → Prop) (g0 g1 : ℕ → ℕ)
    (h1 : ∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ¬ isOr (src p))
    (h2 : ∀ p ∈ Pl, ∀ x, seg p x → p ∈ D x ∧ x < L)
    (h3 : ∀ p ∈ Pl, ∀ x, seg p x → x ≠ top p →
      ∃ y, isOr y ∧ (g0 y = x ∨ g1 y = x) ∧ seg p y ∧ D x ⊆ D y ∧ x < y)
    (h4 : ∀ g : ℕ, (Pl.filter (fun p => src p = g)).card ≤ 2)
    (W : Finset ℕ) (mem_W : ∀ x, x ∈ W ↔ ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card) :
    Pl.card ≤ W.card + (Pl.image top).card := by
  classical
  have stepA : ∀ p ∈ Pl, ∀ k x, L - x ≤ k → seg p x → (D x).card < 2 →
      (∃ y x1, seg p y ∧ 2 ≤ (D y).card ∧ seg p x1 ∧ (D x1).card < 2 ∧ isOr y ∧
        (g0 y = x1 ∨ g1 y = x1)) ∨ (D (top p)).card < 2 := by
    intro p hp k
    induction k with
    | zero =>
      intro x hk hs _
      have := (h2 p hp x hs).2
      omega
    | succ k ih =>
      intro x hk hs hn
      by_cases hxt : x = top p
      · right
        rw [← hxt]
        exact hn
      · obtain ⟨y, hyo, hys, hsy, _, hxy⟩ := h3 p hp x hs hxt
        by_cases hwy : 2 ≤ (D y).card
        · exact Or.inl ⟨y, x, hsy, hwy, hs, hn, hyo, hys⟩
        · exact ih y (by omega) hsy (by omega)
  have stepB : ∀ p ∈ Pl, (∃ y x, G src seg D isOr g0 g1 p y x) ∨ (D (top p)).card < 2 := by
    intro p hp
    obtain ⟨hs, _, _⟩ := h1 p hp
    by_cases hw : 2 ≤ (D (src p)).card
    · exact Or.inl ⟨src p, 0, hs, hw, Or.inl rfl⟩
    · rcases stepA p hp (L - src p) (src p) le_rfl hs (by omega) with ⟨y, x, a, b, c, d, e, f⟩ | h
      · exact Or.inl ⟨y, x, a, b, Or.inr ⟨c, d, e, f⟩⟩
      · exact Or.inr h
  obtain ⟨P2, P1, hsum, mem_P2, mem_P1⟩ : ∃ P2 P1 : Finset α, P2.card + P1.card = Pl.card ∧
      (∀ p, p ∈ P2 ↔ p ∈ Pl ∧ ∃ y x, G src seg D isOr g0 g1 p y x) ∧
      (∀ p, p ∈ P1 ↔ p ∈ Pl ∧ ¬ ∃ y x, G src seg D isOr g0 g1 p y x) :=
    ⟨_, _, Finset.card_filter_add_card_filter_not (s := Pl)
      (fun p => ∃ y x, G src seg D isOr g0 g1 p y x),
      fun p => Finset.mem_filter, fun p => Finset.mem_filter⟩
  have hG : ∀ p ∈ P2, ∃ y x, G src seg D isOr g0 g1 p y x := fun p hp => ((mem_P2 p).mp hp).2
  choose! m px hm using hG
  have hP2Pl : ∀ p ∈ P2, p ∈ Pl := fun p hp => ((mem_P2 p).mp hp).1
  have hfib : ∀ p ∈ P2, isOr (m p) →
      seg p (px p) ∧ (D (px p)).card < 2 ∧ (g0 (m p) = px p ∨ g1 (m p) = px p) := by
    intro p hp ho
    obtain ⟨_, _, h | ⟨a, b, _, d⟩⟩ := hm p hp
    · rw [h] at ho
      exact absurd ho (h1 p (hP2Pl p hp)).2.2
    · exact ⟨a, b, d⟩
  have hsrc : ∀ p ∈ P2, ¬ isOr (m p) → m p = src p := by
    intro p hp ho
    obtain ⟨_, _, h | ⟨_, _, c, _⟩⟩ := hm p hp
    · exact h
    · exact absurd c ho
  have hmW : ∀ p ∈ P2, m p ∈ W := by
    intro p hp
    obtain ⟨hs, hw, _⟩ := hm p hp
    exact (mem_W _).mpr ⟨p, hP2Pl p hp, hs, hw⟩
  have hpar : ∀ y ∈ W \ Pl.image top, ∃ z, z ∈ W ∧ isOr z ∧ (g0 z = y ∨ g1 z = y) := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨p, hp, hs, hw⟩ := (mem_W y).mp hy.1
    have hne : y ≠ top p := by
      intro h
      apply hy.2
      rw [h]
      exact Finset.mem_image_of_mem top hp
    obtain ⟨z, hzo, hzs, hsz, hD, _⟩ := h3 p hp y hs hne
    exact ⟨z, (mem_W z).mpr ⟨p, hp, hsz, le_trans hw (Finset.card_le_card hD)⟩, hzo, hzs⟩
  choose! par hpar1 using hpar
  have hwide : ∀ y ∈ W \ Pl.image top, 2 ≤ (D y).card := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨_, _, _, hw⟩ := (mem_W y).mp hy.1
    exact hw
  have hnar : ∀ p ∈ P1, (D (top p)).card < 2 := by
    intro p hp
    have hp1 := (mem_P1 p).mp hp
    rcases stepB p hp1.1 with h | h
    · exact absurd h hp1.2
    · exact h
  have hP1c : P1.card ≤ (Pl.image top \ W).card := by
    apply Finset.card_le_card_of_injOn top
    · intro p hp
      have hp0 : p ∈ P1 := Finset.mem_coe.mp hp
      have hp1 := (mem_P1 p).mp hp0
      have hn := hnar p hp0
      refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem top hp1.1, ?_⟩)
      intro hw
      obtain ⟨_, _, _, hw2⟩ := (mem_W _).mp hw
      omega
    · intro p hp q hq hpq
      have hp0 : p ∈ P1 := Finset.mem_coe.mp hp
      have hq0 : q ∈ P1 := Finset.mem_coe.mp hq
      have hp1 := (mem_P1 p).mp hp0
      have hq1 := (mem_P1 q).mp hq0
      have hn := hnar p hp0
      have h1p := (h2 p hp1.1 (top p) (h1 p hp1.1).2.1).1
      have h1q := (h2 q hq1.1 (top q) (h1 q hq1.1).2.1).1
      rw [← hpq] at h1q
      exact Finset.card_le_one.mp (by omega) p h1p q h1q
  have hQ : (P2.disjSum (W \ Pl.image top)).card ≤ 2 * W.card := by
    refine Finset.card_le_mul_card_image_of_maps_to (f := Sum.elim m par) ?_ 2 ?_
    · intro q hq
      rcases Finset.mem_disjSum.mp hq with ⟨p, hp, rfl⟩ | ⟨y, hy, rfl⟩
      · exact hmW p hp
      · exact (hpar1 y hy).1
    · intro y hy
      by_cases hyo : isOr y
      · refine le_trans (Finset.card_le_card_of_injOn (t := ({g0 y, g1 y} : Finset ℕ))
          (Sum.elim px id) ?_ ?_) Finset.card_le_two
        · intro q hq
          obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          rcases Finset.mem_disjSum.mp hq1 with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
          · have hq3 : m p = y := hq2
            obtain ⟨_, _, hsl⟩ := hfib p hp (by rw [hq3]; exact hyo)
            rw [hq3] at hsl
            refine Finset.mem_coe.mpr ?_
            show px p ∈ ({g0 y, g1 y} : Finset ℕ)
            rw [Finset.mem_insert, Finset.mem_singleton]
            rcases hsl with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          · have hq3 : par z = y := hq2
            have hsl := (hpar1 z hz).2.2
            rw [hq3] at hsl
            refine Finset.mem_coe.mpr ?_
            show z ∈ ({g0 y, g1 y} : Finset ℕ)
            rw [Finset.mem_insert, Finset.mem_singleton]
            rcases hsl with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
        · intro q hq q1 hq1 heq
          obtain ⟨hqa, hqb⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          obtain ⟨hq1a, hq1b⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq1)
          rcases Finset.mem_disjSum.mp hqa with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
          · have hq3 : m p = y := hqb
            obtain ⟨hsp, hnp, _⟩ := hfib p hp (by rw [hq3]; exact hyo)
            rcases Finset.mem_disjSum.mp hq1a with ⟨p1, hp1, rfl⟩ | ⟨z1, hz1, rfl⟩
            · have hq4 : m p1 = y := hq1b
              obtain ⟨hsp1, _, _⟩ := hfib p1 hp1 (by rw [hq4]; exact hyo)
              have he : px p = px p1 := heq
              have hd := (h2 p (hP2Pl p hp) _ hsp).1
              have hd1 := (h2 p1 (hP2Pl p1 hp1) _ hsp1).1
              rw [← he] at hd1
              have : p = p1 := Finset.card_le_one.mp (by omega) p hd p1 hd1
              rw [this]
            · have he : px p = z1 := heq
              have := hwide z1 hz1
              rw [← he] at this
              omega
          · rcases Finset.mem_disjSum.mp hq1a with ⟨p1, hp1, rfl⟩ | ⟨z1, hz1, rfl⟩
            · have hq4 : m p1 = y := hq1b
              obtain ⟨_, hnp1, _⟩ := hfib p1 hp1 (by rw [hq4]; exact hyo)
              have he : z = px p1 := heq
              have := hwide z hz
              rw [he] at this
              omega
            · have he : z = z1 := heq
              rw [he]
      · refine le_trans (Finset.card_le_card ?_)
          (le_trans (Finset.card_image_le (f := Sum.inl)) (h4 y))
        intro q hq
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        rcases Finset.mem_disjSum.mp hq1 with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
        · have hq3 : m p = y := hq2
          refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hP2Pl p hp, ?_⟩, rfl⟩
          rw [← hsrc p hp (by rw [hq3]; exact hyo)]
          exact hq3
        · have hq3 : par z = y := hq2
          have := (hpar1 z hz).2.1
          rw [hq3] at this
          exact absurd this hyo
  rw [Finset.card_disjSum] at hQ
  have e1 := Finset.card_sdiff_add_card_inter W (Pl.image top)
  have e2 := Finset.card_sdiff_add_card_inter (Pl.image top) W
  rw [Finset.inter_comm] at e2
  omega

theorem main (n N : ℕ) (C : Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ)
    (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (h2 : ∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length)
    (h3 : ∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧
      (gateAt C j2).op = GateOp.or ∧ (gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧
      seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2))
    (h4 : ∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) :
    Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
  have hfin : {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.Finite :=
    (Set.finite_lt_nat (n + C.gates.length)).subset (fun x hx => by
      obtain ⟨p, hp, hs, _⟩ := hx
      exact (h2 p hp x hs).2.2)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine core Pl src top seg D (n + C.gates.length)
    (fun y => ∃ j, y = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or)
    (fun y => (gateAt C (y - n)).inputs.getD 0 0) (fun y => (gateAt C (y - n)).inputs.getD 1 0)
    ?_ ?_ ?_ h4 hfin.toFinset (fun x => hfin.mem_toFinset)
  · intro p hp
    obtain ⟨a, b, j, hj, hjl, hop⟩ := h1 p hp
    refine ⟨a, b, ?_⟩
    rintro ⟨j1, hj1, _, hop1⟩
    have hjj : j = j1 := by omega
    subst hjj
    rw [hop] at hop1
    cases hop1
  · intro p hp x hs
    exact ⟨(h2 p hp x hs).1, (h2 p hp x hs).2.2⟩
  · intro p hp x hs hne
    obtain ⟨j, c, hjl, hop, hc, hc2, hsj, hD⟩ := h3 p hp x hs hne
    refine ⟨n + j, ⟨j, rfl, hjl, hop⟩, ?_, hsj, hD, ?_⟩
    · show (gateAt C (n + j - n)).inputs.getD 0 0 = x ∨ (gateAt C (n + j - n)).inputs.getD 1 0 = x
      rw [Nat.add_sub_cancel_left]
      rcases (by omega : c = 0 ∨ c = 1) with hc0 | hc0
      · rw [hc0] at hc
        exact Or.inl hc
      · rw [hc0] at hc
        exact Or.inr hc
    · have hmemg : gateAt C j ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hjl]
        exact List.getElem_mem _
      have hlen := hAO.2.2 _ hmemg
      have hlt : c < (gateAt C j).inputs.length := by omega
      have hxm : x ∈ (gateAt C j).inputs := by
        rw [← hc, List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem _
      exact hAO.2.1 j hjl x hxm


end P2487

theorem s2487 : ∀ (n N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ) (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)), PEqualNP.TopForm.IsAO2 n C → (∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length) → (∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧ seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2)) → (∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) → Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
  intro n N C Pl src top seg D hAO h1 h2 h3 h4
  exact PEqualNP.Outside.L_meta_2494.P2500.P2493.P2490.P2489.P2487.main n N C Pl src top seg D hAO h1 h2 h3 h4

end Sec2487

theorem len_le2 (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) :
    (gateAt C j).inputs.length ≤ 2 := by
  by_cases hj : j < C.gates.length
  · exact le_of_eq (hC.2.2 _ (gate_mem C hj))
  · unfold gateAt
    rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem img_le {α β γ : Type} [DecidableEq β] [DecidableEq γ] (A : Finset α) (f : α → β)
    (g : α → γ) (h : ∀ a ∈ A, ∀ b ∈ A, g a = g b → f a = f b) :
    (A.image f).card ≤ (A.image g).card := by
  have e1 : A.image f = (A.image (fun a => (g a, f a))).image Prod.snd := by
    rw [Finset.image_image]
    rfl
  have e2 : A.image g = (A.image (fun a => (g a, f a))).image Prod.fst := by
    rw [Finset.image_image]
    rfl
  have e3 : ((A.image (fun a => (g a, f a))).image Prod.fst).card
      = (A.image (fun a => (g a, f a))).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact Prod.ext hxy (h a ha b hb hxy)
  rw [e1, e2, e3]
  exact Finset.card_image_le

noncomputable def Dd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (x : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N) (fun p => ∃ m : Fin M, ¬ I p m ∧
    wireVal n C x (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true)
    (Classical.decPred _) Finset.univ

theorem mem_Dd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (x : ℕ) (p : Fin N) : p ∈ Dd n N M pw lw I C x ↔ ∃ m : Fin M, ¬ I p m ∧
      wireVal n C x (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
  unfold Dd
  rw [mem_filter']
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

noncomputable def Wd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (l : Fin M) : Finset ℕ :=
  @Finset.filter ℕ (fun x => 2 ≤ (Dd n N M pw lw I C x).card ∧ ∀ q ∈ Dd n N M pw lw I C x, I q l)
    (Classical.decPred _) (Finset.Ico n (n + C.gates.length))

theorem mem_Wd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (l : Fin M) (x : ℕ) : x ∈ Wd n N M pw lw I C l ↔
      (n ≤ x ∧ x < n + C.gates.length) ∧ 2 ≤ (Dd n N M pw lw I C x).card ∧
        ∀ q ∈ Dd n N M pw lw I C x, I q l := by
  unfold Wd
  rw [mem_filter', Finset.mem_Ico]

theorem perline (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (hC : IsAO2 n C)
    (hS : ∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 →
      (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) →
      circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false)
    (l : Fin M) (Pl : Finset (Fin N)) (j1 K F1 V j2 F2 : Fin N → ℕ)
    (h : ∀ p ∈ Pl,
      (j1 p < C.gates.length ∧ (gateAt C (j1 p)).op = GateOp.and ∧
        ((gateAt C (j1 p)).inputs = [K p, F1 p] ∨ (gateAt C (j1 p)).inputs = [F1 p, K p])) ∧
      {a : Fin N | wireVal n C (K p) (fun k : Fin n => decide (k.val = pw a)) = true} = {p} ∧
      (∃ m : Fin M, wireVal n C (F1 p) (fun k : Fin n => decide (k.val = lw m)) = true ∧ ¬ I p m) ∧
      OrReaches n C (V p) (j1 p) ∧
      (j2 p < C.gates.length ∧ (gateAt C (j2 p)).op = GateOp.and ∧
        ((gateAt C (j2 p)).inputs = [V p, F2 p] ∨ (gateAt C (j2 p)).inputs = [F2 p, V p])) ∧
      wireVal n C (F2 p) (fun k : Fin n => decide (k.val = lw l)) = true ∧
      OrReaches n C C.output (j2 p)) :
    Pl.card ≤ (Wd n N M pw lw I C l).card + (Pl.image V).card := by
  refine le_trans (s2487 n N C Pl (fun p => n + j1 p) V
    (fun p x => ∃ j', x = n + j' ∧ j' < C.gates.length ∧ OrReaches n C x (j1 p) ∧
      OrReaches n C (V p) j') (Dd n N M pw lw I C) hC ?_ ?_ ?_ ?_) (Nat.add_le_add_right ?_ _)
  · intro p hp
    obtain ⟨hand1, hK, ⟨m, hm, hnI⟩, hr, hand2, hl, hout⟩ := h p hp
    have hV : n ≤ V p := hr.1
    obtain ⟨k, hk⟩ : ∃ k, V p = n + k := ⟨V p - n, by omega⟩
    have hr2 := hr
    rw [hk] at hr2
    have hklen := ((orReaches_iff n C k (j1 p)).1 hr2).1
    have hself : OrReaches n C (V p) k := by
      rw [hk]
      exact (orReaches_iff n C k k).2 ⟨hklen, Or.inl rfl⟩
    exact ⟨⟨j1 p, rfl, hand1.1, (orReaches_iff n C (j1 p) (j1 p)).2 ⟨hand1.1, Or.inl rfl⟩, hr⟩,
      ⟨k, hk, hklen, hr, hself⟩, j1 p, rfl, hand1.1, hand1.2.1⟩
  · intro p hp x hx
    obtain ⟨j', rfl, hj', hr1, hr2⟩ := hx
    refine ⟨?_, by omega, by omega⟩
    obtain ⟨hand1, hK, ⟨m, hm, hnI⟩, hr, hand2, hl, hout⟩ := h p hp
    rw [mem_Dd]
    refine ⟨m, hnI, ?_⟩
    rw [wires_eq]
    refine reach_up n C _ (j1 p) (n + j') hr1 ?_
    have hKp : wireVal n C (K p) (fun k : Fin n => decide (k.val = pw p)) = true := by
      have hmem : p ∈ {a : Fin N | wireVal n C (K p) (fun k : Fin n => decide (k.val = pw a)) = true} := by
        rw [hK]
        exact Set.mem_singleton p
      exact hmem
    have a1 : val C.gates (K p) (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
      refine wires_mono C hC.1 (fun k : Fin n => decide (k.val = pw p))
        (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) ?_ (K p) hKp
      intro k hk
      have hk2 := of_decide_eq_true hk
      apply decide_eq_true
      rw [hk2]
      exact Finset.mem_insert_self _ _
    have a2 : val C.gates (F1 p) (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
      refine wires_mono C hC.1 (fun k : Fin n => decide (k.val = lw m))
        (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) ?_ (F1 p) hm
      intro k hk
      have hk2 := of_decide_eq_true hk
      apply decide_eq_true
      rw [hk2]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [and_eq n C hC _ (j1 p) hand1.1 hand1.2.1]
    rcases hand1.2.2 with e | e
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Bool.and_eq_true]
      exact ⟨a1, a2⟩
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Bool.and_eq_true]
      exact ⟨a2, a1⟩
  · intro p hp x hx hne
    obtain ⟨j', rfl, hj', hr1, hr2⟩ := hx
    obtain ⟨k, c, hk, hop, hmem, hQ, hnQ, hrk⟩ :=
      walk n C hC.2.2 (fun w => w = n + j') j' (V p) hr2 rfl (fun e => hne e.symm)
    have hQ2 : (gateAt C k).inputs.getD (cond c 1 0) 0 = n + j' := hQ
    rw [hQ2] at hmem
    have hlt : n + j' < n + k := hC.2.1 k hk (n + j') hmem
    refine ⟨k, cond c 1 0, hk, hop, hQ2, by cases c <;> simp, ⟨k, rfl, hk, ?_, hrk⟩, ?_⟩
    · exact (orReaches_iff n C k (j1 p)).2 ⟨hk, Or.inr ⟨hop, n + j', hmem, hlt, hr1⟩⟩
    · intro q hq
      rw [mem_Dd] at hq ⊢
      obtain ⟨m, hnI, hw⟩ := hq
      refine ⟨m, hnI, ?_⟩
      rw [wires_eq] at hw ⊢
      exact reach_up n C _ j' (n + k) ((orReaches_iff n C k j').2 ⟨hk, Or.inr ⟨hop, n + j', hmem, hlt,
        (orReaches_iff n C j' j').2 ⟨hj', Or.inl rfl⟩⟩⟩) hw
  · intro g
    refine le_trans (Finset.card_le_card_of_injOn (t := (gateAt C (g - n)).inputs.toFinset) K ?_ ?_)
      (le_trans (List.toFinset_card_le _) (len_le2 n C hC (g - n)))
    · intro p hp
      have hp2 := Finset.mem_filter.1 hp
      obtain ⟨hand1, _⟩ := h p hp2.1
      have e : g - n = j1 p := by
        have := hp2.2
        omega
      refine Finset.mem_coe.2 (List.mem_toFinset.2 ?_)
      rw [e]
      rcases hand1.2.2 with e2 | e2 <;> rw [e2] <;> simp
    · intro p hp q hq hpq
      have hp2 := Finset.mem_filter.1 hp
      have hq2 := Finset.mem_filter.1 hq
      obtain ⟨_, hKp, _⟩ := h p hp2.1
      obtain ⟨_, hKq, _⟩ := h q hq2.1
      rw [hpq] at hKp
      exact Set.singleton_injective (hKp.symm.trans hKq)
  · refine le_trans (Set.ncard_le_ncard (t := ((Wd n N M pw lw I C l : Finset ℕ) : Set ℕ)) ?_
      (Finset.finite_toSet _)) (le_of_eq (Set.ncard_coe_finset _))
    rintro x ⟨p, hp, ⟨j', rfl, hj', hr1, hr2⟩, h2⟩
    rw [Finset.mem_coe, mem_Wd]
    refine ⟨⟨by omega, by omega⟩, h2, ?_⟩
    intro q hq
    obtain ⟨m, hnI, hw⟩ := (mem_Dd n N M pw lw I C (n + j') q).1 hq
    obtain ⟨_, _, _, _, hand, hl, hout⟩ := h p hp
    exact dirty_on n N M pw lw I C l (n + j') (V p) (F2 p) (j2 p) hC hS
      (Or.inr ⟨j', rfl, hr2⟩) hand.1 hand.2.1 hand.2.2 hout hl q m hnI hw

theorem main89 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [V_1, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_2)) → A.card ≤ C.size + 2 * {j_3 : ℕ | j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro n N M pw lw I C A hC hinj hno hS hA
  classical
  rcases A.eq_empty_or_nonempty with hAe | ⟨pl0, hpl0⟩
  · rw [hAe]
    simp
  have : Nonempty (Fin M) := ⟨pl0.2⟩
  have hA2 := fun pl (hpl : pl ∈ A) => (hA pl hpl).2
  choose! j1 K F1 V j2 F2 m hch using hA2
  have hper : ∀ l : Fin M, (A.filter (fun pl => pl.2 = l)).card ≤
      (Wd n N M pw lw I C l).card +
        ((Finset.univ.filter (fun p : Fin N => (p, l) ∈ A)).image (fun p => V (p, l))).card := by
    intro l
    have h1 : (A.filter (fun pl => pl.2 = l)).card ≤
        (Finset.univ.filter (fun p : Fin N => (p, l) ∈ A)).card := by
      refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
      · intro pl hpl
        have h2 := Finset.mem_filter.1 hpl
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
        have e : (pl.1, l) = pl := Prod.ext rfl h2.2.symm
        rw [e]
        exact h2.1
      · intro a ha b hb hab
        have h2 := Finset.mem_filter.1 ha
        have h3 := Finset.mem_filter.1 hb
        exact Prod.ext hab (h2.2.trans h3.2.symm)
    refine le_trans h1 (perline n N M pw lw I C hC hS l _ (fun p => j1 (p, l)) (fun p => K (p, l))
      (fun p => F1 (p, l)) (fun p => V (p, l)) (fun p => j2 (p, l)) (fun p => F2 (p, l)) ?_)
    intro p hp
    have hpA : (p, l) ∈ A := (Finset.mem_filter.1 hp).2
    obtain ⟨a, b, c, d, e, f, g, hh⟩ := hch (p, l) hpA
    have hl : l ∈ {a_3 : Fin M | wireVal n C (F2 (p, l)) (fun k : Fin n => decide (k.val = lw a_3)) = true} := by
      rw [g]
      exact Set.mem_singleton l
    exact ⟨a, b, ⟨m (p, l), c, d⟩, e, f, hl, hh⟩
  have hsum : A.card = ∑ l : Fin M, (A.filter (fun pl => pl.2 = l)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun _ _ => Finset.mem_univ _)
  have hW : ∑ l : Fin M, (Wd n N M pw lw I C l).card ≤ C.gates.length := by
    have hd : ∀ l ∈ (Finset.univ : Finset (Fin M)), ∀ l' ∈ (Finset.univ : Finset (Fin M)), l ≠ l' →
        Disjoint (Wd n N M pw lw I C l) (Wd n N M pw lw I C l') := by
      intro l _ l' _ hll
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_Wd] at hx hx'
      obtain ⟨q1, hq1, q2, hq2, hne⟩ := Finset.one_lt_card.1 hx.2.1
      exact hno q1 q2 l l' hne hll ⟨hx.2.2 q1 hq1, hx.2.2 q2 hq2, hx'.2.2 q1 hq1, hx'.2.2 q2 hq2⟩
    rw [← Finset.card_biUnion hd]
    refine le_trans (Finset.card_le_card (t := Finset.Ico n (n + C.gates.length))
      (Finset.biUnion_subset.2 (fun l _ x hx =>
        Finset.mem_Ico.2 ((mem_Wd n N M pw lw I C l x).1 hx).1))) ?_
    simp
  have hfin : {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.and}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun x hx => hx.1)
  have hT : ∑ l : Fin M,
      ((Finset.univ.filter (fun p : Fin N => (p, l) ∈ A)).image (fun p => V (p, l))).card
      ≤ 2 * {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.and}.ncard := by
    have s1 : ∀ l : Fin M,
        ((Finset.univ.filter (fun p : Fin N => (p, l) ∈ A)).image (fun p => V (p, l))).card
        ≤ ((A.image (fun pl => (pl.2, V pl))).filter (fun t => t.1 = l)).card := by
      intro l
      refine Finset.card_le_card_of_injOn (fun v => (l, v)) ?_ ?_
      · intro v hv
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
        exact Finset.mem_coe.2 (Finset.mem_filter.2
          ⟨Finset.mem_image.2 ⟨(p, l), (Finset.mem_filter.1 hp).2, rfl⟩, rfl⟩)
      · intro a _ b _ hab
        exact (Prod.mk.inj hab).2
    have s2 : (A.image (fun pl => (pl.2, V pl))).card
        = ∑ l : Fin M, ((A.image (fun pl => (pl.2, V pl))).filter (fun t => t.1 = l)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun _ _ => Finset.mem_univ _)
    have s3 : (A.image (fun pl => (pl.2, V pl))).card ≤ (A.image (fun pl => (j2 pl, V pl))).card := by
      refine img_le A _ _ ?_
      intro a ha b hb hab
      have hj : j2 a = j2 b := (Prod.mk.inj hab).1
      have hv : V a = V b := (Prod.mk.inj hab).2
      obtain ⟨_, _, _, _, _, fa, ga, _⟩ := hch a ha
      obtain ⟨_, _, _, _, _, fb, gb, _⟩ := hch b hb
      have hF : F2 a = F2 b := by
        have ia := fa.2.2
        have ib := fb.2.2
        rw [← hj, ← hv] at ib
        rcases ia with ia | ia <;> rcases ib with ib | ib <;> rw [ia] at ib <;> simp at ib <;> omega
      rw [← hF] at gb
      have hl : a.2 = b.2 := Set.singleton_injective (ga.symm.trans gb)
      exact Prod.ext hl hv
    have s4 : (A.image (fun pl => (j2 pl, V pl))).card ≤ 2 * hfin.toFinset.card := by
      have hsub : A.image (fun pl => (j2 pl, V pl)) ⊆
          hfin.toFinset.biUnion (fun j => ((gateAt C j).inputs.toFinset).image (fun v => (j, v))) := by
        intro t ht
        obtain ⟨pl, hpl, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨_, _, _, _, _, f, _, _⟩ := hch pl hpl
        refine Finset.mem_biUnion.2 ⟨j2 pl, hfin.mem_toFinset.2 ⟨f.1, f.2.1⟩,
          Finset.mem_image.2 ⟨V pl, ?_, rfl⟩⟩
        rw [List.mem_toFinset]
        rcases f.2.2 with e | e <;> rw [e] <;> simp
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
      refine le_trans (Finset.sum_le_card_nsmul _ _ 2 ?_) (le_of_eq ?_)
      · intro j _
        exact le_trans Finset.card_image_le
          (le_trans (List.toFinset_card_le _) (len_le2 n C hC j))
      · rw [smul_eq_mul, Nat.mul_comm]
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact le_trans (Finset.sum_le_sum (fun l _ => s1 l))
      (le_trans (le_of_eq s2.symm) (le_trans s3 s4))
  have hsz : C.size = C.gates.length := rfl
  rw [hsz, hsum]
  refine le_trans (Finset.sum_le_sum (fun l _ => hper l)) ?_
  rw [Finset.sum_add_distrib]
  exact Nat.add_le_add hW hT


end P2489

theorem s2489 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [V_1, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_2)) → A.card ≤ C.size + 2 * {j_3 : ℕ | j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
  PEqualNP.Outside.L_meta_2494.P2500.P2493.P2490.P2489.main89

end Sec2489

theorem four {α : Type} (A : Finset α) (Q P1 P2 P3 P4 : α → Prop) (c1 c2 c3 c4 : ℕ)
    (h : ∀ a ∈ A, Q a ∧ (P1 a ∨ P2 a ∨ P3 a ∨ P4 a))
    (h1 : ∀ B : Finset α, (∀ a ∈ B, Q a ∧ P1 a) → B.card ≤ c1)
    (h2 : ∀ B : Finset α, (∀ a ∈ B, Q a ∧ P2 a) → B.card ≤ c2)
    (h3 : ∀ B : Finset α, (∀ a ∈ B, Q a ∧ P3 a) → B.card ≤ c3)
    (h4 : ∀ B : Finset α, (∀ a ∈ B, Q a ∧ P4 a) → B.card ≤ c4) :
    A.card ≤ c1 + c2 + c3 + c4 := by
  classical
  have hsub : A ⊆ ((A.filter P1 ∪ A.filter P2) ∪ A.filter P3) ∪ A.filter P4 := by
    intro a ha
    have h' := (h a ha).2
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have e1 := h1 (A.filter P1)
    (fun a ha => ⟨(h a (Finset.mem_filter.1 ha).1).1, (Finset.mem_filter.1 ha).2⟩)
  have e2 := h2 (A.filter P2)
    (fun a ha => ⟨(h a (Finset.mem_filter.1 ha).1).1, (Finset.mem_filter.1 ha).2⟩)
  have e3 := h3 (A.filter P3)
    (fun a ha => ⟨(h a (Finset.mem_filter.1 ha).1).1, (Finset.mem_filter.1 ha).2⟩)
  have e4 := h4 (A.filter P4)
    (fun a ha => ⟨(h a (Finset.mem_filter.1 ha).1).1, (Finset.mem_filter.1 ha).2⟩)
  have e0 := Finset.card_le_card hsub
  have u1 := Finset.card_union_le ((A.filter P1 ∪ A.filter P2) ∪ A.filter P3) (A.filter P4)
  have u2 := Finset.card_union_le (A.filter P1 ∪ A.filter P2) (A.filter P3)
  have u3 := Finset.card_union_le (A.filter P1) (A.filter P2)
  omega

theorem cnt (C : PEqualNP.CircuitLowerBounds.Circuit) :
    {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard
      + {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard
      ≤ C.size := by
  have hf1 : {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun x hx => hx.1)
  have hf2 : {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun x hx => hx.1)
  have hd : Disjoint {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}
      {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
    rw [Set.disjoint_left]
    intro j h1 h2
    have e := h1.2.symm.trans h2.2
    cases e
  rw [← Set.ncard_union_eq hd hf1 hf2]
  have hsub : ({j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}
      ∪ {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and})
      ⊆ ((Finset.range C.gates.length : Finset ℕ) : Set ℕ) := by
    intro j hj
    rw [Finset.mem_coe, Finset.mem_range]
    rcases hj with hj | hj
    · exact hj.1
    · exact hj.1
  have h3 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_range] at h3
  exact h3

theorem main : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = pw pl.1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = lw pl.2 ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = pw pl.1 ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = lw pl.2 ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = lw pl.2 ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = lw pl.2 ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = lw pl.2 ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = pw pl.1 ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) → A.card ≤ 5 * C.size := by
  intro n N M pw lw I C A hC hinj hno hS hA
  have hcl : ∀ pl ∈ A, I pl.1 pl.2 ∧ _ := fun pl hpl =>
    ⟨(hA pl hpl).1, s2485 n N M pw lw I C pl.1 pl.2 hC hinj hS (hA pl hpl).1 (hA pl hpl).2⟩
  have hc := cnt C
  have key := four A _ _ _ _ _
    (2 * {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
    (2 * {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
    (2 * {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard)
    (C.size + 2 * {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard)
    hcl ?_ ?_ ?_ ?_
  · omega
  · intro B hB
    exact s2482 n N M pw lw I C B hC hinj hno (fun pl hpl => hB pl hpl)
  · intro B hB
    have hcard : (B.image Prod.swap).card = B.card :=
      Finset.card_image_of_injective _ Prod.swap_injective
    rw [← hcard]
    refine s2482 n M N lw pw (fun m p => I p m) C (B.image Prod.swap) hC
      ⟨hinj.2.1, hinj.1, fun l p => (hinj.2.2.1 p l).symm, hinj.2.2.2.2, hinj.2.2.2.1⟩
      (fun a b c d hab hcd hh => hno c d a b hcd hab ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2⟩) ?_
    intro pl hpl
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hpl
    exact ⟨(hB q hq).1, (hB q hq).2⟩
  · intro B hB
    exact s2484 n N M pw lw C B hC (fun pl hpl => (hB pl hpl).2)
  · intro B hB
    exact s2489 n N M pw lw I C B hC hinj hno hS (fun pl hpl => hB pl hpl)


end P2490

theorem s2490 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = pw pl.1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = lw pl.2 ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = pw pl.1 ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = lw pl.2 ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = lw pl.2 ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = lw pl.2 ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = lw pl.2 ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = pw pl.1 ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5))) → A.card ≤ 5 * C.size :=
  PEqualNP.Outside.L_meta_2494.P2500.P2493.P2490.main

end Sec2490

theorem comb2 {α β : Type} [DecidableEq α] [DecidableEq β] (E A B : Finset α) (f : α → β)
    (hf : Function.Injective f) (k : ℕ) (hsub : E ⊆ A ∪ B) (h1 : A.card ≤ 5 * k)
    (h2 : (B.image f).card ≤ 5 * k) : E.card ≤ 10 * k := by
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le A B
  have hi : (B.image f).card = B.card := Finset.card_image_of_injective B hf
  omega

theorem main : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l_1 : Fin N, (Finset.univ.filter (fun p_3 => I p_3 l_1)).card = q + 1) → (∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin N)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_4 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_4 l_3) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k_1 : Fin (N + N) => decide (k_1.val ∈ P_1.image (fun pa : Fin N => pa.val) ∪ Y_1.image (fun la : Fin N => N + la.val))) = false) → (∀ (P_2 : Finset (Fin N)) (Y_2 : Finset (Fin N)), P_2.card ≤ 1 → Y_2.card ≤ 2 → (∀ p_5 ∈ P_2, ∀ l_4 ∈ Y_2, ¬ I l_4 p_5) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k_2 : Fin (N + N) => decide (k_2.val ∈ P_2.image (fun lb : Fin N => N + lb.val) ∪ Y_2.image (fun pb : Fin N => pb.val))) = false) → (∀ p l : Fin N, I p l → [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output [] ∨ [2, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output []) → N * (q + 1) ≤ 10 * C.size := by
  intro q N I inst C hq hN hline huniq hAO hsound hsound2 hread
  have hpi : Function.Injective (fun pv : Fin N => pv.val) := by
    intro a b h
    have h2 : a.val = b.val := h
    exact Fin.ext h2
  have hli : Function.Injective (fun lv : Fin N => N + lv.val) := by
    intro a b h
    have h2 : N + a.val = N + b.val := h
    exact Fin.ext (by omega)
  have hne : ∀ (p1 : Fin N) (l1 : Fin N), (fun pv : Fin N => pv.val) p1 ≠ (fun lv : Fin N => N + lv.val) l1 := by
    intro p1 l1 h
    have h2 : p1.val = N + l1.val := h
    have := p1.isLt
    omega
  have hned : ∀ (l1 : Fin N) (p1 : Fin N), (fun lv : Fin N => N + lv.val) l1 ≠ (fun pv : Fin N => pv.val) p1 := by
    intro l1 p1 h
    exact hne p1 l1 h.symm
  have hpl : ∀ p2 : Fin N, (fun pv : Fin N => pv.val) p2 < N + N := by
    intro p2
    have h2 := p2.isLt
    show p2.val < N + N
    omega
  have hll : ∀ l2 : Fin N, (fun lv : Fin N => N + lv.val) l2 < N + N := by
    intro l2
    have h2 := l2.isLt
    show N + l2.val < N + N
    omega
  have hno4 : ∀ (a b : Fin N) (l m : Fin N), a ≠ b → l ≠ m → ¬ (I a l ∧ I b l ∧ I a m ∧ I b m) := by
    intro a b l m hab hlm hh
    obtain ⟨h1, h2, h3, h4⟩ := hh
    obtain ⟨x, _, hx⟩ := huniq a b hab
    exact hlm ((hx l ⟨h1, h2⟩).trans (hx m ⟨h3, h4⟩).symm)
  have hno4d : ∀ (l m : Fin N) (a b : Fin N), l ≠ m → a ≠ b →
      ¬ ((fun (lv : Fin N) (pv : Fin N) => I pv lv) l a ∧ (fun (lv : Fin N) (pv : Fin N) => I pv lv) m a
        ∧ (fun (lv : Fin N) (pv : Fin N) => I pv lv) l b ∧ (fun (lv : Fin N) (pv : Fin N) => I pv lv) m b) := by
    intro l m a b hlm hab hh
    obtain ⟨h1, h2, h3, h4⟩ := hh
    obtain ⟨x, _, hx⟩ := huniq a b hab
    exact hlm ((hx l ⟨h1, h3⟩).trans (hx m ⟨h2, h4⟩).symm)
  have hcard : (Finset.univ.filter (fun pl : Fin N × Fin N => I pl.1 pl.2)).card = N * (q + 1) := by
    have h1 : (Finset.univ.filter (fun pl : Fin N × Fin N => I pl.1 pl.2)).card
        = ∑ l : Fin N, ∑ p : Fin N, (if I p l then 1 else 0) := by
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
    rw [h1]
    have h2 : ∀ l : Fin N, (∑ p : Fin N, (if I p l then 1 else 0)) = q + 1 := by
      intro l
      rw [← hline l, Finset.card_filter]
    rw [Finset.sum_congr rfl (fun l _ => h2 l)]
    simp
  have h1 := s2490 (N + N) N N (fun pv : Fin N => pv.val) (fun lv : Fin N => N + lv.val) I C
    ((Finset.univ.filter (fun pl : Fin N × Fin N => I pl.1 pl.2)).filter
      (fun pl : Fin N × Fin N => [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [pl.1.val, N + pl.2.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [pl.1.val, N + pl.2.val] 2).getD C.output []))
    hAO ⟨hpi, hli, hne, hpl, hll⟩ hno4 hsound
    (by
      intro pl hmem
      obtain ⟨hE, hV⟩ := Finset.mem_filter.mp hmem
      have hI : I pl.1 pl.2 := (Finset.mem_filter.mp hE).2
      have b1 := pl.1.isLt
      have b2 := pl.2.isLt
      exact ⟨hI, (s2477 (N + N) C pl.1.val (N + pl.2.val) hAO (by omega) (by omega) (by omega)).1 hV⟩)
  have h2 := s2490 (N + N) N N (fun lv : Fin N => N + lv.val) (fun pv : Fin N => pv.val)
    (fun (lv : Fin N) (pv : Fin N) => I pv lv) C
    (((Finset.univ.filter (fun pl : Fin N × Fin N => I pl.1 pl.2)).filter
      (fun pl : Fin N × Fin N => [2, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [pl.1.val, N + pl.2.val] 2).getD C.output [])).image Prod.swap)
    hAO ⟨hli, hpi, hned, hll, hpl⟩ hno4d hsound2
    (by
      intro pl hmem
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hmem
      obtain ⟨hE, hV⟩ := Finset.mem_filter.mp hx
      have hI : I x.1 x.2 := (Finset.mem_filter.mp hE).2
      have b1 := x.1.isLt
      have b2 := x.2.isLt
      exact ⟨hI, (s2477 (N + N) C x.1.val (N + x.2.val) hAO (by omega) (by omega) (by omega)).2 hV⟩)
  have h3 := comb2 (Finset.univ.filter (fun pl : Fin N × Fin N => I pl.1 pl.2)) _ _ Prod.swap
    Prod.swap_injective C.size
    (by
      intro pl hmem
      have hI : I pl.1 pl.2 := (Finset.mem_filter.mp hmem).2
      rcases hread pl.1 pl.2 hI with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, Or.inl h⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, Or.inr h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, h⟩))
    h1 h2
  rw [hcard] at h3
  exact h3


end P2493

theorem s2493 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l_1 : Fin N, (Finset.univ.filter (fun p_3 => I p_3 l_1)).card = q + 1) → (∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin N)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_4 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_4 l_3) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k_1 : Fin (N + N) => decide (k_1.val ∈ P_1.image (fun pa : Fin N => pa.val) ∪ Y_1.image (fun la : Fin N => N + la.val))) = false) → (∀ (P_2 : Finset (Fin N)) (Y_2 : Finset (Fin N)), P_2.card ≤ 1 → Y_2.card ≤ 2 → (∀ p_5 ∈ P_2, ∀ l_4 ∈ Y_2, ¬ I l_4 p_5) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k_2 : Fin (N + N) => decide (k_2.val ∈ P_2.image (fun lb : Fin N => N + lb.val) ∪ Y_2.image (fun pb : Fin N => pb.val))) = false) → (∀ p l : Fin N, I p l → [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output [] ∨ [2, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p.val, N + l.val] 2).getD C.output []) → N * (q + 1) ≤ 10 * C.size :=
  PEqualNP.Outside.L_meta_2494.P2500.P2493.main

end Sec2493

section Glue

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

theorem all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true → (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

theorem any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true → (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem run_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (runW gs w).getD i false = true → (runW gs w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact run_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine run_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · have e : ∀ z : Fin n → Bool, (List.ofFn z).getD k false = z ⟨k, hk⟩ := fun z => by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e x, e y]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim

theorem cf_mono (n : ℕ) (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true)
    (hy : PEqualNP.MetaComplexity.circuitFun n C y = false) :
    PEqualNP.MetaComplexity.circuitFun n C x = false := by
  cases hx : PEqualNP.MetaComplexity.circuitFun n C x with
  | false => rfl
  | true =>
    have h2 : PEqualNP.MetaComplexity.circuitFun n C y = true :=
      wires_mono C hC x y h C.output hx
    rw [hy] at h2
    exact (Bool.false_ne_true h2).elim

theorem ptOff (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (Y : Finset (Fin N)) (hY : Y.card ≤ 2) : ∃ p : Fin N, ∀ l ∈ Y, ¬ I p l := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin N)) ⊆ Y.biUnion (fun l => Finset.univ.filter (fun p => I p l)) := by
    intro p _
    obtain ⟨l, hl, hI⟩ := hcon p
    exact Finset.mem_biUnion.mpr ⟨l, hl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Y.biUnion (fun l => Finset.univ.filter (fun p => I p l))).card
      ≤ ∑ l ∈ Y, (Finset.univ.filter (fun p => I p l)).card := Finset.card_biUnion_le
  have h3 : ∑ l ∈ Y, (Finset.univ.filter (fun p => I p l)).card = Y.card * (q + 1) := by
    rw [Finset.sum_congr rfl (fun l _ => hline l)]
    simp
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h4 : Y.card * (q + 1) ≤ 2 * (q + 1) := Nat.mul_le_mul_right _ hY
  have h5 : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have h6 : q ^ 2 = q * q := by ring
  omega

theorem lnOff (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2)
    (P : Finset (Fin N)) (hP : P.card ≤ 2) : ∃ l : Fin N, ∀ p ∈ P, ¬ I p l := by
  have h5 : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have h6 : q ^ 2 = q * q := by ring
  have hN0 : 0 < N := by omega
  by_cases hne : P.Nonempty
  · obtain ⟨p0, hp0⟩ := hne
    have hr : ∃ r : Fin N, r ∉ P := by
      by_contra hcon
      push_neg at hcon
      have h1 := Finset.card_le_card (fun r (_ : r ∈ (Finset.univ : Finset (Fin N))) => hcon r)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    obtain ⟨r, hr⟩ := hr
    have hex : ∀ p : Fin N, ∃ l : Fin N, p ≠ r → (I p l ∧ I r l ∧ ∀ m : Fin N, I p m ∧ I r m → m = l) := by
      intro p
      by_cases hp : p = r
      · exact ⟨⟨0, hN0⟩, fun h => (h hp).elim⟩
      · obtain ⟨l, hl, hu⟩ := huniq p r hp
        exact ⟨l, fun _ => ⟨hl.1, hl.2, fun m hm => hu m hm⟩⟩
    choose f hf using hex
    have hcard : (P.image f).card ≤ 2 := le_trans Finset.card_image_le hP
    obtain ⟨s, hs⟩ := ptOff q N I hq hN hline (P.image f) hcard
    have hp0r : p0 ≠ r := fun e => hr (e ▸ hp0)
    have hsr : s ≠ r := by
      intro e
      apply hs (f p0) (Finset.mem_image_of_mem f hp0)
      rw [e]
      exact (hf p0 hp0r).2.1
    obtain ⟨l, hl, _⟩ := huniq s r hsr
    refine ⟨l, ?_⟩
    intro p hp hI
    have hpr : p ≠ r := fun e => hr (e ▸ hp)
    have e2 : l = f p := (hf p hpr).2.2 l ⟨hI, hl.2⟩
    apply hs (f p) (Finset.mem_image_of_mem f hp)
    rw [← e2]
    exact hl.1
  · refine ⟨⟨0, hN0⟩, ?_⟩
    intro p hp
    exact (hne ⟨p, hp⟩).elim

theorem reduce (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hrejP : ∀ (p4 : Fin N) (Y : Finset (Fin N)), Y.card ≤ 2 → (∀ m4 ∈ Y, ¬ I p4 m4) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k2 => decide (k2 = Fin.castAdd N p4 ∨ ∃ m5 ∈ Y, k2 = Fin.natAdd N m5)) = false)
    (hrejL : ∀ (l6 : Fin N) (P : Finset (Fin N)), P.card ≤ 2 → (∀ p6 ∈ P, ¬ I p6 l6) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 => decide (k3 = Fin.natAdd N l6 ∨ ∃ p7 ∈ P, k3 = Fin.castAdd N p7)) = false) :
    (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin N)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_4 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_4 l_3) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k_1 : Fin (N + N) => decide (k_1.val ∈ P_1.image (fun pa : Fin N => pa.val) ∪ Y_1.image (fun la : Fin N => N + la.val))) = false) ∧ (∀ (P_2 : Finset (Fin N)) (Y_2 : Finset (Fin N)), P_2.card ≤ 1 → Y_2.card ≤ 2 → (∀ p_5 ∈ P_2, ∀ l_4 ∈ Y_2, ¬ I l_4 p_5) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k_2 : Fin (N + N) => decide (k_2.val ∈ P_2.image (fun lb : Fin N => N + lb.val) ∪ Y_2.image (fun pb : Fin N => pb.val))) = false) := by
  constructor
  · intro P1 Y1 hP1 hY1 hno
    have hex : ∃ p4 : Fin N, (∀ p ∈ P1, p = p4) ∧ ∀ l ∈ Y1, ¬ I p4 l := by
      by_cases hne : P1.Nonempty
      · obtain ⟨p4, hp4⟩ := hne
        exact ⟨p4, fun p hp => Finset.card_le_one.mp hP1 p hp p4 hp4, fun l hl => hno p4 hp4 l hl⟩
      · obtain ⟨p4, h4⟩ := ptOff q N I hq hN hline Y1 hY1
        exact ⟨p4, fun p hp => (hne ⟨p, hp⟩).elim, h4⟩
    obtain ⟨p4, hall, hoff⟩ := hex
    refine cf_mono (N + N) C hC _ _ ?_ (hrejP p4 Y1 hY1 hoff)
    intro k hk
    have hk1 : k.val ∈ P1.image (fun pa : Fin N => pa.val) ∪ Y1.image (fun la : Fin N => N + la.val) :=
      of_decide_eq_true hk
    apply decide_eq_true
    rcases Finset.mem_union.mp hk1 with h1 | h1
    · obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp h1
      left
      apply Fin.ext
      rw [Fin.val_castAdd, ← hall a ha]
      exact hav.symm
    · obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp h1
      right
      refine ⟨a, ha, ?_⟩
      apply Fin.ext
      rw [Fin.val_natAdd]
      exact hav.symm
  · intro L1 P1 hL1 hP1 hno
    have hex : ∃ l6 : Fin N, (∀ l ∈ L1, l = l6) ∧ ∀ p ∈ P1, ¬ I p l6 := by
      by_cases hne : L1.Nonempty
      · obtain ⟨l6, hl6⟩ := hne
        exact ⟨l6, fun l hl => Finset.card_le_one.mp hL1 l hl l6 hl6, fun p hp => hno l6 hl6 p hp⟩
      · obtain ⟨l6, h6⟩ := lnOff q N I hq hN hline huniq P1 hP1
        exact ⟨l6, fun l hl => (hne ⟨l, hl⟩).elim, h6⟩
    obtain ⟨l6, hall, hoff⟩ := hex
    refine cf_mono (N + N) C hC _ _ ?_ (hrejL l6 P1 hP1 hoff)
    intro k hk
    have hk1 : k.val ∈ L1.image (fun lb : Fin N => N + lb.val) ∪ P1.image (fun pb : Fin N => pb.val) :=
      of_decide_eq_true hk
    apply decide_eq_true
    rcases Finset.mem_union.mp hk1 with h1 | h1
    · obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp h1
      left
      apply Fin.ext
      rw [Fin.val_natAdd, ← hall a ha]
      exact hav.symm
    · obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp h1
      right
      refine ⟨a, ha, ?_⟩
      apply Fin.ext
      rw [Fin.val_castAdd]
      exact hav.symm

theorem main : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l_1 : Fin N, (Finset.univ.filter (fun p_3 => I p_3 l_1)).card = q + 1) → (∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p3 l3 : Fin N, I p3 l3 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p3 ∨ k1 = Fin.natAdd N l3)) = true) → (∀ (p4 : Fin N) (Y : Finset (Fin N)), Y.card ≤ 2 → (∀ m4 ∈ Y, ¬ I p4 m4) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k2 => decide (k2 = Fin.castAdd N p4 ∨ ∃ m5 ∈ Y, k2 = Fin.natAdd N m5)) = false) → (∀ (l6 : Fin N) (P : Finset (Fin N)), P.card ≤ 2 → (∀ p6 ∈ P, ¬ I p6 l6) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 => decide (k3 = Fin.natAdd N l6 ∨ ∃ p7 ∈ P, k3 = Fin.castAdd N p7)) = false) → (∀ p8 l8 : Fin N, I p8 l8 → [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output [] ∨ [2, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output []) → N * q ≤ 100 * C.size := by
  intro q N I inst C hq hN hline huniq hAO hacc hrejP hrejL hread
  have hred := reduce q N I C hq hN hline huniq hAO.1 hrejP hrejL
  have h : N * (q + 1) ≤ 10 * C.size := s2493 q N I C hq hN hline huniq hAO hred.1 hred.2 hread
  have h1 : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega

end Glue


end P2500

theorem s2500 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l_1 : Fin N, (Finset.univ.filter (fun p_3 => I p_3 l_1)).card = q + 1) → (∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p3 l3 : Fin N, I p3 l3 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p3 ∨ k1 = Fin.natAdd N l3)) = true) → (∀ (p4 : Fin N) (Y : Finset (Fin N)), Y.card ≤ 2 → (∀ m4 ∈ Y, ¬ I p4 m4) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k2 => decide (k2 = Fin.castAdd N p4 ∨ ∃ m5 ∈ Y, k2 = Fin.natAdd N m5)) = false) → (∀ (l6 : Fin N) (P : Finset (Fin N)), P.card ≤ 2 → (∀ p6 ∈ P, ¬ I p6 l6) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 => decide (k3 = Fin.natAdd N l6 ∨ ∃ p7 ∈ P, k3 = Fin.castAdd N p7)) = false) → (∀ p8 l8 : Fin N, I p8 l8 → [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output [] ∨ [2, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output []) → N * q ≤ 100 * C.size :=
  PEqualNP.Outside.L_meta_2494.P2500.main

end Sec2500

section Top

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadK

theorem snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

theorem all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true → (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

theorem any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true → (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem run_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (runW gs w).getD i false = true → (runW gs w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact run_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine run_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · have e : ∀ z : Fin n → Bool, (List.ofFn z).getD k false = z ⟨k, hk⟩ := fun z => by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e x, e y]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_pre (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_pre _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_or2 (C : Circuit) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (u1 u2 : ℕ) (hin : (gateAt C k).inputs = [u1, u2])
    (u : ℕ) (hu : u = u1 ∨ u = u2) (hlt : u < n + k) (hv : val C.gates u x = true) :
    val C.gates (n + k) x = true := by
  rw [gateAt_eq C k hk] at hop hin
  exact (val_or C.gates x k hk hop).mpr ⟨u, by rw [hin]; simpa using hu, hlt, hv⟩

def rcell (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def rf (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  gs.foldl (fun R g => R ++ [rcell S k R g]) R

def ini (S : List ℕ) (n : ℕ) : List (List (List ℕ)) := (List.range n).map (leafVectors S 2)

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) :
    readVectors C n S 2 = rf S 2 C.gates (ini S n) := rfl

lemma rf_len (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ R : List (List (List ℕ)), (rf S k gs R).length = R.length + gs.length := by
  induction gs with
  | nil => intro R; simp [rf]
  | cons g gs ih =>
    intro R
    have := ih (R ++ [rcell S k R g])
    simp only [rf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma rf_keep (S : List ℕ) (k : ℕ) (gs : List Gate) :
    ∀ (R : List (List (List ℕ))) (i : ℕ), i < R.length →
      (rf S k gs R).getD i [] = R.getD i [] := by
  induction gs with
  | nil => intro R i _; rfl
  | cons g gs ih =>
    intro R i hi
    have := ih (R ++ [rcell S k R g]) i (by simp; omega)
    simp only [rf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma rcell_congr (S : List ℕ) (k : ℕ) (R R2 : List (List (List ℕ))) (g : Gate)
    (h : ∀ i ∈ g.inputs, R.getD i [] = R2.getD i []) : rcell S k R g = rcell S k R2 g := by
  unfold rcell
  rw [List.map_congr_left h]

def V (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S 2).getD w []

lemma V_gate (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    V C n S (n + j) = rcell S 2 (readVectors C n S 2) (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre, hgj⟩ := split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [gateAt_eq C j hj]; exact hgj
  rw [hga] at hrb ⊢
  have hc : readVectors C n S 2
      = rf S 2 post (rf S 2 pre (ini S n) ++ [rcell S 2 (rf S 2 pre (ini S n)) gj]) := by
    rw [rv_eq, hgs]
    simp only [rf, List.foldl_append, List.foldl_cons]
  have hl : (rf S 2 pre (ini S n)).length = n + j := by
    rw [rf_len]; simp [ini, hpre]
  have h1 : V C n S (n + j) = rcell S 2 (rf S 2 pre (ini S n)) gj := by
    unfold V
    rw [hc, rf_keep _ _ _ _ _ (by simp; omega), ← hl]
    simp [List.getD_eq_getElem?_getD]
  rw [h1]
  apply rcell_congr
  intro i hi
  have hlt : i < (rf S 2 pre (ini S n)).length := by rw [hl]; exact hrb i hi
  rw [hc, rf_keep S 2 post _ i (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

lemma V_leaf (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : w < n) :
    V C n S w = leafVectors S 2 w := by
  unfold V
  rw [rv_eq, rf_keep _ _ _ _ _ (by simp [ini]; exact hw)]
  simp [ini, List.getD_eq_getElem?_getD, hw]

lemma V_big (C : Circuit) (n : ℕ) (S : List ℕ) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    V C n S w = [] := by
  unfold V
  rw [List.getD_eq_default _ _ (by rw [rv_eq, rf_len]; simp [ini]; exact hw)]

lemma mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | rfl)
      · exact h1
      · exact h
  · simp

lemma mem_foldl_insertNew (L : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (x : List ℕ), x ∈ L.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ L := by
  induction L with
  | nil => intro acc x; simp
  | cons v L ih =>
    intro acc x
    rw [List.foldl_cons, ih, mem_insertNew]
    simp [or_assoc]

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ p ∈ A, ∃ q ∈ B, capAdd k p q = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap, List.mem_map]

lemma V_or (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (u1 u2 : ℕ) (hin : (gateAt C j).inputs = [u1, u2])
    (h1 : u1 < n + j) (h2 : u2 < n + j) (x : List ℕ) :
    x ∈ V C n S (n + j) ↔ x ∈ V C n S u1 ∨ x ∈ V C n S u2 := by
  rw [V_gate C n S j hj (by rw [hin]; intro i hi; simp at hi; omega)]
  simp only [rcell, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    mem_foldl_insertNew]
  simp [V]

lemma V_and (C : Circuit) (n : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (u1 u2 : ℕ) (hin : (gateAt C j).inputs = [u1, u2])
    (h1 : u1 < n + j) (h2 : u2 < n + j) (x : List ℕ) :
    x ∈ V C n S (n + j) ↔ ∃ p ∈ V C n S u1, ∃ q ∈ V C n S u2,
      capAdd 2 (capAdd 2 (S.map fun _ => 0) p) q = x := by
  rw [V_gate C n S j hj (by rw [hin]; intro i hi; simp at hi; omega)]
  simp only [rcell, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    mem_andStep, List.mem_singleton]
  constructor
  · rintro ⟨p2, ⟨z, rfl, p, hp, rfl⟩, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨_, ⟨_, rfl, p, hp, rfl⟩, q, hq, rfl⟩

lemma cap2 (a b x y x2 y2 : ℕ) :
    capAdd 2 (capAdd 2 (([a, b] : List ℕ).map fun _ => 0) [x, y]) [x2, y2]
      = [min (min x 3 + x2) 3, min (min y 3 + y2) 3] := by
  simp [capAdd]

lemma mem_leaf (a b w : ℕ) (v : List ℕ) :
    v ∈ leafVectors [a, b] 2 w ↔
      (w = a ∨ w = b) ∧ v = [if a = w then 1 else 0, if b = w then 1 else 0] := by
  unfold leafVectors
  by_cases h : w = a ∨ w = b
  · simp [h]
  · simp [h]

lemma wire_cases (n : ℕ) (C : Circuit) (h : IsAO2 n C) (w : ℕ) :
    w < n ∨ n + C.gates.length ≤ w ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧
      ∃ u1 u2, (gateAt C k).inputs = [u1, u2] ∧ u1 < n + k ∧ u2 < n + k ∧
        ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) := by
  obtain ⟨hao, hrb, hlen⟩ := h
  by_cases h1 : w < n
  · exact Or.inl h1
  by_cases h2 : n + C.gates.length ≤ w
  · exact Or.inr (Or.inl h2)
  right; right
  have hk : w - n < C.gates.length := by omega
  have hmem : gateAt C (w - n) ∈ C.gates := by
    rw [gateAt_eq C _ hk]; exact List.getElem_mem hk
  obtain ⟨u1, u2, hab⟩ := List.length_eq_two.mp (hlen _ hmem)
  exact ⟨w - n, hk, by omega, u1, u2, hab, hrb _ hk u1 (by rw [hab]; simp),
    hrb _ hk u2 (by rw [hab]; simp), hao _ hmem⟩

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_and2 (C : Circuit) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (u1 u2 : ℕ) (hin : (gateAt C k).inputs = [u1, u2])
    (h1 : u1 < n + k) (h2 : u2 < n + k) (hv1 : val C.gates u1 x = true)
    (hv2 : val C.gates u2 x = true) : val C.gates (n + k) x = true := by
  rw [gateAt_eq C k hk] at hop hin
  refine (val_and C.gates x k hk hop).mpr ?_
  intro i hi
  rw [hin] at hi
  have hi2 : i = u1 ∨ i = u2 := by simpa using hi
  rcases hi2 with e | e
  · rw [e]; exact ⟨h1, hv1⟩
  · rw [e]; exact ⟨h2, hv2⟩

lemma zval (n : ℕ) (C : Circuit) (h : IsAO2 n C) (u w : ℕ) :
    ∀ t, ∀ v ∈ V C n [u, w] t, ∃ x y : ℕ, v = [x, y] ∧
      (y = 0 → val C.gates t (fun k1 : Fin n => decide (k1.val = u)) = true) ∧
      (x = 0 → val C.gates t (fun k2 : Fin n => decide (k2.val = w)) = true) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv
    rcases wire_cases n C h t with ht | ht | ⟨k, hk, rfl, u1, u2, hin, h1, h2, hop | hop⟩
    · rw [V_leaf C n _ t ht] at hv
      obtain ⟨hm, rfl⟩ := (mem_leaf u w t v).mp hv
      refine ⟨_, _, rfl, ?_, ?_⟩
      · intro hy
        rw [val_input C.gates _ t ht]
        by_cases e : w = t
        · rw [if_pos e] at hy
          exact absurd hy (by norm_num)
        · have e2 : t = u := by
            rcases hm with hm | hm
            · exact hm
            · exact absurd hm.symm e
          simpa using e2
      · intro hx
        rw [val_input C.gates _ t ht]
        by_cases e : u = t
        · rw [if_pos e] at hx
          exact absurd hx (by norm_num)
        · have e2 : t = w := by
            rcases hm with hm | hm
            · exact absurd hm.symm e
            · exact hm
          simpa using e2
    · rw [V_big C n _ t ht] at hv
      simp at hv
    · obtain ⟨p, hp, q, hq, rfl⟩ := (V_and C n _ k hk hop u1 u2 hin h1 h2 v).mp hv
      obtain ⟨x, y, rfl, hy, hx⟩ := ih u1 (by omega) p hp
      obtain ⟨x2, y2, rfl, hy2, hx2⟩ := ih u2 (by omega) q hq
      rw [cap2]
      refine ⟨_, _, rfl, ?_, ?_⟩
      · intro e
        exact val_and2 C _ k hk hop u1 u2 hin h1 h2 (hy (by omega)) (hy2 (by omega))
      · intro e
        exact val_and2 C _ k hk hop u1 u2 hin h1 h2 (hx (by omega)) (hx2 (by omega))
    · rcases (V_or C n _ k hk hop u1 u2 hin h1 h2 v).mp hv with h3 | h3
      · obtain ⟨x, y, rfl, hy, hx⟩ := ih u1 h1 v h3
        exact ⟨x, y, rfl,
          fun e => val_or2 C _ k hk hop u1 u2 hin u1 (Or.inl rfl) h1 (hy e),
          fun e => val_or2 C _ k hk hop u1 u2 hin u1 (Or.inl rfl) h1 (hx e)⟩
      · obtain ⟨x, y, rfl, hy, hx⟩ := ih u2 h2 v h3
        exact ⟨x, y, rfl,
          fun e => val_or2 C _ k hk hop u1 u2 hin u2 (Or.inr rfl) h2 (hy e),
          fun e => val_or2 C _ k hk hop u1 u2 hin u2 (Or.inr rfl) h2 (hx e)⟩


theorem cf_mono (n : ℕ) (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true)
    (hy : PEqualNP.MetaComplexity.circuitFun n C y = false) :
    PEqualNP.MetaComplexity.circuitFun n C x = false := by
  cases hx : PEqualNP.MetaComplexity.circuitFun n C x with
  | false => rfl
  | true =>
    have h2 : PEqualNP.MetaComplexity.circuitFun n C y = true :=
      wires_mono C hC x y h C.output hx
    rw [hy] at h2
    exact (Bool.false_ne_true h2).elim

theorem vpos (N : ℕ) (I : Fin N → Fin N → Prop) (C C2 : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hAO : IsAO2 (N + N) C2)
    (hfun : PEqualNP.MetaComplexity.circuitFun (N + N) C2 = PEqualNP.MetaComplexity.circuitFun (N + N) C)
    (hrejP : ∀ (p4 : Fin N) (Y : Finset (Fin N)), Y.card ≤ 2 → (∀ m4 ∈ Y, ¬ I p4 m4) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k2 => decide (k2 = Fin.castAdd N p4 ∨ ∃ m5 ∈ Y, k2 = Fin.natAdd N m5)) = false)
    (hrejL : ∀ (l6 : Fin N) (P : Finset (Fin N)), P.card ≤ 2 → (∀ p6 ∈ P, ¬ I p6 l6) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 => decide (k3 = Fin.natAdd N l6 ∨ ∃ p7 ∈ P, k3 = Fin.castAdd N p7)) = false)
    (p l : Fin N) (v : List ℕ)
    (hv : v ∈ (PEqualNP.ReadK.readVectors C2 (N + N) [p.val, N + l.val] 2).getD C2.output []) :
    ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x ∧ 1 ≤ y := by
  obtain ⟨x, y, rfl, hy, hx⟩ := zval (N + N) C2 hAO p.val (N + l.val) C2.output v hv
  refine ⟨x, y, rfl, ?_, ?_⟩
  · by_contra hx0
    have hx0' : x = 0 := by omega
    have ht : PEqualNP.MetaComplexity.circuitFun (N + N) C2 (fun k2 : Fin (N + N) => decide (k2.val = N + l.val)) = true :=
      hx hx0'
    rw [hfun] at ht
    have hf : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k2 : Fin (N + N) => decide (k2.val = N + l.val)) = false := by
      refine cf_mono (N + N) C hC _ _ ?_ (hrejL l ∅ (by simp) (by simp))
      intro k hk
      have hk1 : k.val = N + l.val := of_decide_eq_true hk
      apply decide_eq_true
      left
      apply Fin.ext
      rw [Fin.val_natAdd]
      exact hk1
    rw [hf] at ht
    exact Bool.false_ne_true ht
  · by_contra hy0
    have hy0' : y = 0 := by omega
    have ht : PEqualNP.MetaComplexity.circuitFun (N + N) C2 (fun k1 : Fin (N + N) => decide (k1.val = p.val)) = true :=
      hy hy0'
    rw [hfun] at ht
    have hf : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 : Fin (N + N) => decide (k1.val = p.val)) = false := by
      refine cf_mono (N + N) C hC _ _ ?_ (hrejP p ∅ (by simp) (by simp))
      intro k hk
      have hk1 : k.val = p.val := of_decide_eq_true hk
      apply decide_eq_true
      left
      apply Fin.ext
      rw [Fin.val_castAdd]
      exact hk1
    rw [hf] at ht
    exact Bool.false_ne_true ht

theorem main : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l_1 : Fin N, (Finset.univ.filter (fun p_3 => I p_3 l_1)).card = q + 1) → (∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p3 l3 : Fin N, I p3 l3 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p3 ∨ k1 = Fin.natAdd N l3)) = true) → (∀ (p4 : Fin N) (Y : Finset (Fin N)), Y.card ≤ 2 → (∀ m4 ∈ Y, ¬ I p4 m4) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k2 => decide (k2 = Fin.castAdd N p4 ∨ ∃ m5 ∈ Y, k2 = Fin.natAdd N m5)) = false) → (∀ (l6 : Fin N) (P : Finset (Fin N)), P.card ≤ 2 → (∀ p6 ∈ P, ¬ I p6 l6) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 => decide (k3 = Fin.natAdd N l6 ∨ ∃ p7 ∈ P, k3 = Fin.castAdd N p7)) = false) → (∀ p8 l8 : Fin N, I p8 l8 → [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output [] ∨ [2, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output []) → N * q ≤ 100 * C.size := by
  intro q N I inst C hq hN hline huniq hM hacc hrejP hrejL hread
  have hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  have h5 : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have h6 : q ^ 2 = q * q := by ring
  have hN0 : 0 < N := by omega
  have hz : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun _ => false) = false := by
    refine cf_mono (N + N) C hC _ _ ?_ (hrejP ⟨0, hN0⟩ ∅ (by simp) (by simp))
    intro k hk
    exact (Bool.false_ne_true hk).elim
  have hsome : ∃ x : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C x = true := by
    have hc : 0 < (Finset.univ.filter (fun p => I p (⟨0, hN0⟩ : Fin N))).card := by
      rw [hline]
      omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hc
    exact ⟨_, hacc p ⟨0, hN0⟩ (Finset.mem_filter.mp hp).2⟩
  obtain ⟨C2, hAO, hsz, hfun, hvec⟩ := s2471 (N + N) C hM hz hsome
  have h : N * q ≤ 100 * C2.size := by
    refine s2500 q N I C2 hq hN hline huniq hAO ?_ ?_ ?_ ?_
    · intro p l hI
      rw [hfun]
      exact hacc p l hI
    · intro p Y hY hno
      rw [hfun]
      exact hrejP p Y hY hno
    · intro l P hP hno
      rw [hfun]
      exact hrejL l P hP hno
    · intro p l hI
      rcases hread p l hI with h1 | h1 | h1
      · obtain ⟨v2, hv2, hle⟩ := hvec _ _ h1
        obtain ⟨x, y, rfl, hx, hy⟩ := vpos N I C C2 hC hAO hfun hrejP hrejL p l v2 hv2
        have h0 : x ≤ 1 := by simpa using hle 0
        have h1 : y ≤ 1 := by simpa using hle 1
        have ex : x = 1 := by omega
        have ey : y = 1 := by omega
        subst ex
        subst ey
        exact Or.inl hv2
      · obtain ⟨v2, hv2, hle⟩ := hvec _ _ h1
        obtain ⟨x, y, rfl, hx, hy⟩ := vpos N I C C2 hC hAO hfun hrejP hrejL p l v2 hv2
        have h0 : x ≤ 1 := by simpa using hle 0
        have h1 : y ≤ 2 := by simpa using hle 1
        have ex : x = 1 := by omega
        subst ex
        rcases (by omega : y = 1 ∨ y = 2) with ey | ey
        · subst ey
          exact Or.inl hv2
        · subst ey
          exact Or.inr (Or.inl hv2)
      · obtain ⟨v2, hv2, hle⟩ := hvec _ _ h1
        obtain ⟨x, y, rfl, hx, hy⟩ := vpos N I C C2 hC hAO hfun hrejP hrejL p l v2 hv2
        have h0 : x ≤ 2 := by simpa using hle 0
        have h1 : y ≤ 1 := by simpa using hle 1
        have ey : y = 1 := by omega
        subst ey
        rcases (by omega : x = 1 ∨ x = 2) with ex | ex
        · subst ex
          exact Or.inl hv2
        · subst ex
          exact Or.inr (Or.inr hv2)
  have hsz2 : C2.size ≤ C.size := hsz
  omega

end Top

end PEqualNP.Outside.L_meta_2494

theorem PEqualNP.Outside.L_meta_2494 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l_1 : Fin N, (Finset.univ.filter (fun p_3 => I p_3 l_1)).card = q + 1) → (∀ p_1 p_2 : Fin N, p_1 ≠ p_2 → ∃! l_2 : Fin N, I p_1 l_2 ∧ I p_2 l_2) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p3 l3 : Fin N, I p3 l3 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p3 ∨ k1 = Fin.natAdd N l3)) = true) → (∀ (p4 : Fin N) (Y : Finset (Fin N)), Y.card ≤ 2 → (∀ m4 ∈ Y, ¬ I p4 m4) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k2 => decide (k2 = Fin.castAdd N p4 ∨ ∃ m5 ∈ Y, k2 = Fin.natAdd N m5)) = false) → (∀ (l6 : Fin N) (P : Finset (Fin N)), P.card ≤ 2 → (∀ p6 ∈ P, ¬ I p6 l6) → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k3 => decide (k3 = Fin.natAdd N l6 ∨ ∃ p7 ∈ P, k3 = Fin.castAdd N p7)) = false) → (∀ p8 l8 : Fin N, I p8 l8 → [1, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output [] ∨ [1, 2] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output [] ∨ [2, 1] ∈ (PEqualNP.ReadK.readVectors C (N + N) [p8.val, N + l8.val] 2).getD C.output []) → N * q ≤ 100 * C.size :=
  PEqualNP.Outside.L_meta_2494.main
