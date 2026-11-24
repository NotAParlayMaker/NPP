import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2471

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

end PEqualNP.Outside.L_meta_2471

theorem PEqualNP.Outside.L_meta_2471 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.circuitFun n C (fun _ => false) = false → (∃ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ C'.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C ∧ ∀ (S : List ℕ) (v : List ℕ), v ∈ (PEqualNP.ReadK.readVectors C n S 2).getD C.output [] → ∃ v' ∈ (PEqualNP.ReadK.readVectors C' n S 2).getD C'.output [], ∀ i : ℕ, v'.getD i 0 ≤ v.getD i 0 := by
  intro n C hM h0 h1
  exact PEqualNP.Outside.L_meta_2471.fin n C hM h0 h1
