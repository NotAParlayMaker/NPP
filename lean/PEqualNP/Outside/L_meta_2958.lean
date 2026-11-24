import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2958

open PEqualNP.CircuitLowerBounds

def val (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def stp (w : List Bool) (g : Gate) : List Bool := w ++ [val g w]

lemma getD_one (l : List Bool) (a : Bool) (k : ℕ) :
    (l ++ [a]).getD k false
      = if k < l.length then l.getD k false else if k = l.length then a else false := by
  by_cases h : k < l.length
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega)]
    by_cases h2 : k = l.length
    · subst h2
      simp
    · rw [if_neg h2]
      exact List.getD_eq_default _ _ (by simp only [List.length_singleton]; omega)

lemma getD_two (l : List Bool) (a b : Bool) (k : ℕ) :
    (l ++ [a] ++ [b]).getD k false
      = if k < l.length then l.getD k false else if k = l.length then a
        else if k = l.length + 1 then b else false := by
  rw [getD_one, getD_one]
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> first | rfl | omega

def srcval : Option ℕ → List Bool → Bool
  | none, _ => true
  | some a, w => w.getD a false

def Good (J : ℕ) (src : Option ℕ) : ℕ → List Bool → List Gate → Prop
  | _, _, [] => True
  | j, w, g :: gs =>
    (j = J → g.op ≠ GateOp.not ∧ val g w = srcval src w) ∧ Good J src (j + 1) (stp w g) gs

lemma good_cons (J : ℕ) (src : Option ℕ) (j : ℕ) (w : List Bool) (g : Gate) (gs : List Gate) :
    Good J src j w (g :: gs)
      ↔ (j = J → g.op ≠ GateOp.not ∧ val g w = srcval src w) ∧ Good J src (j + 1) (stp w g) gs := by
  simp only [Good]

lemma good_after (J : ℕ) (src : Option ℕ) (gs : List Gate) :
    ∀ (j : ℕ) (w : List Bool), J < j → Good J src j w gs := by
  induction gs with
  | nil =>
    intro j w _
    simp only [Good]
  | cons g gs ih =>
    intro j w h
    rw [good_cons]
    exact ⟨fun h' => absurd h' (by omega), ih _ _ (by omega)⟩

def tr (ρ : ℕ → ℕ) (u n J : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs =>
    (if j = J then ([Gate.mk GateOp.not [u], Gate.mk GateOp.not [n + 2 + 2 * j]] : List Gate)
      else ([Gate.mk g.op (g.inputs.map ρ), Gate.mk GateOp.not []] : List Gate))
      ++ tr ρ u n J (j + 1) gs

def uOf (ρ : ℕ → ℕ) (n : ℕ) : Option ℕ → ℕ
  | none => n
  | some a => ρ a

lemma rel_step (ρ : ℕ → ℕ) (m n J j : ℕ)
    (h1 : ∀ k, k < m → ρ k < n + 2)
    (h2 : ∀ k, m ≤ k → ρ k = n + 2 + 2 * (k - m) + (if k - m = J then 1 else 0))
    (w w' : List Bool) (v a b : Bool) (hl : w.length = m + j) (hl' : w'.length = n + 2 + 2 * j)
    (hr : ∀ k, w.getD k false = w'.getD (ρ k) false)
    (hab : (if j = J then b else a) = v) :
    ∀ k, (w ++ [v]).getD k false = (w' ++ [a] ++ [b]).getD (ρ k) false := by
  intro k
  rw [getD_one, getD_two]
  rcases lt_or_ge k m with hk | hk
  · have := h1 k hk
    split_ifs <;> first | omega | exact hr k
  · have e := h2 k hk
    by_cases hjJ : j = J
    · rw [if_pos hjJ] at hab
      split_ifs at e <;> split_ifs <;> first | omega | exact hr k | exact hab.symm | rfl
    · rw [if_neg hjJ] at hab
      split_ifs at e <;> split_ifs <;> first | omega | exact hr k | exact hab.symm | rfl

lemma sim (ρ : ℕ → ℕ) (m n J : ℕ) (src : Option ℕ)
    (h1 : ∀ k, k < m → ρ k < n + 2)
    (h2 : ∀ k, m ≤ k → ρ k = n + 2 + 2 * (k - m) + (if k - m = J then 1 else 0))
    (gs : List Gate) :
    ∀ (j : ℕ) (w w' : List Bool), w.length = m + j → w'.length = n + 2 + 2 * j →
      (∀ k, w.getD k false = w'.getD (ρ k) false) → w'.getD n false = true → Good J src j w gs →
      ∀ k, (gs.foldl stp w).getD k false
        = ((tr ρ (uOf ρ n src) n J j gs).foldl stp w').getD (ρ k) false := by
  induction gs with
  | nil =>
    intro j w w' _ _ hr _ _ k
    exact hr k
  | cons g gs ih =>
    intro j w w' hl hl' hr ht hg
    rw [good_cons] at hg
    obtain ⟨hgh, hgt⟩ := hg
    have hv : val (Gate.mk g.op (g.inputs.map ρ)) w' = val g w := by
      simp only [val, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (hr a).symm
    by_cases hj : j = J
    · have etr : tr ρ (uOf ρ n src) n J j (g :: gs)
          = [Gate.mk GateOp.not [uOf ρ n src], Gate.mk GateOp.not [n + 2 + 2 * j]]
            ++ tr ρ (uOf ρ n src) n J (j + 1) gs := by
        simp only [tr, if_pos hj]
      have hu : w'.getD (uOf ρ n src) false = val g w := by
        rw [(hgh hj).2]
        cases src with
        | none => exact ht
        | some a => exact (hr a).symm
      have hb : (w' ++ [!(w'.getD (uOf ρ n src) false)]).getD (n + 2 + 2 * j) false
          = !(w'.getD (uOf ρ n src) false) := by
        rw [getD_one]
        split_ifs <;> first | omega | rfl
      rw [etr, List.foldl_append]
      refine ih (j + 1) (w ++ [val g w])
        (w' ++ [!(w'.getD (uOf ρ n src) false)]
          ++ [!((w' ++ [!(w'.getD (uOf ρ n src) false)]).getD (n + 2 + 2 * j) false)])
        ?_ ?_ (rel_step ρ m n J j h1 h2 w w' _ _ _ hl hl' hr ?_) ?_ hgt
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [List.length_append, List.length_singleton]
        omega
      · rw [if_pos hj, hb, Bool.not_not]
        exact hu
      · rw [getD_two]
        split_ifs <;> first | omega | exact ht
    · have etr : tr ρ (uOf ρ n src) n J j (g :: gs)
          = [Gate.mk g.op (g.inputs.map ρ), Gate.mk GateOp.not []]
            ++ tr ρ (uOf ρ n src) n J (j + 1) gs := by
        simp only [tr, if_neg hj]
      rw [etr, List.foldl_append]
      refine ih (j + 1) (w ++ [val g w])
        (w' ++ [val (Gate.mk g.op (g.inputs.map ρ)) w'] ++ [true])
        ?_ ?_ (rel_step ρ m n J j h1 h2 w w' _ _ _ hl hl' hr ?_) ?_ hgt
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [List.length_append, List.length_singleton]
        omega
      · rw [if_neg hj]
        exact hv
      · rw [getD_two]
        split_ifs <;> first | omega | exact ht

def nn (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => false
  | _ => true

lemma cnt_norm (g : Gate) (l : List ℕ) :
    List.countP nn [Gate.mk g.op l, Gate.mk GateOp.not []] = List.countP nn [g] := by
  rcases g with ⟨op, ins⟩
  cases op <;> rfl

lemma cnt_cons (g : Gate) (gs : List Gate) :
    List.countP nn (g :: gs) = List.countP nn [g] + List.countP nn gs := by
  rw [← List.singleton_append, List.countP_append]

lemma cnt_one (g : Gate) (h : g.op ≠ GateOp.not) : List.countP nn [g] = 1 := by
  rcases g with ⟨op, ins⟩
  cases op <;> first | rfl | exact absurd rfl h

lemma cnt_after (ρ : ℕ → ℕ) (u n J : ℕ) (gs : List Gate) :
    ∀ j, J < j → List.countP nn (tr ρ u n J j gs) = List.countP nn gs := by
  induction gs with
  | nil =>
    intro j _
    rfl
  | cons g gs ih =>
    intro j hj
    have hne : j ≠ J := by omega
    have e : tr ρ u n J j (g :: gs)
        = [Gate.mk g.op (g.inputs.map ρ), Gate.mk GateOp.not []] ++ tr ρ u n J (j + 1) gs := by
      simp only [tr, if_neg hne]
    rw [e, List.countP_append, cnt_norm, ih (j + 1) (by omega), cnt_cons g gs]

lemma cnt_at (ρ : ℕ → ℕ) (u n J : ℕ) (src : Option ℕ) (gs : List Gate) :
    ∀ (j : ℕ) (w : List Bool), Good J src j w gs → j ≤ J → J < j + gs.length →
      List.countP nn (tr ρ u n J j gs) + 1 = List.countP nn gs := by
  induction gs with
  | nil =>
    intro j w _ h1 h2
    simp only [List.length_nil] at h2
    omega
  | cons g gs ih =>
    intro j w hg h1 h2
    rw [good_cons] at hg
    obtain ⟨hgh, hgt⟩ := hg
    simp only [List.length_cons] at h2
    by_cases hj : j = J
    · have e : tr ρ u n J j (g :: gs)
          = [Gate.mk GateOp.not [u], Gate.mk GateOp.not [n + 2 + 2 * j]]
            ++ tr ρ u n J (j + 1) gs := by
        simp only [tr, if_pos hj]
      have e0 : List.countP nn [Gate.mk GateOp.not [u], Gate.mk GateOp.not [n + 2 + 2 * j]] = 0 := rfl
      rw [e, List.countP_append, e0, cnt_after ρ u n J gs (j + 1) (by omega), cnt_cons g gs,
        cnt_one g (hgh hj).1]
      omega
    · have e : tr ρ u n J j (g :: gs)
          = [Gate.mk g.op (g.inputs.map ρ), Gate.mk GateOp.not []] ++ tr ρ u n J (j + 1) gs := by
        simp only [tr, if_neg hj]
      have := ih (j + 1) _ hgt (by omega) (by omega)
      rw [e, List.countP_append, cnt_norm, cnt_cons g gs]
      omega

abbrev FI (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma fan_tr (ρ : ℕ → ℕ) (u n J : ℕ) (gs : List Gate) :
    ∀ j, (∀ g ∈ gs, FI g) → ∀ g ∈ tr ρ u n J j gs, FI g := by
  induction gs with
  | nil =>
    intro j _ g hg
    simp [tr] at hg
  | cons g0 gs ih =>
    intro j h g hg
    simp only [tr, List.mem_append] at hg
    rcases hg with hg | hg
    · have h0 := h g0 (by simp)
      split_ifs at hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> simp [FI]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · exact ⟨h0.1, by simpa using h0.2⟩
        · simp [FI]
    · exact ih (j + 1) (fun g' hg' => h g' (by simp [hg'])) g hg

abbrev IW {n : ℕ} (i : Fin (n + 1)) (S : (Fin (n + 1) → Bool) → List Bool) (k : ℕ) : Prop :=
  ∀ x, (S (Function.update x i true)).getD k false = (S (Function.update x i false)).getD k false

abbrev RC {n : ℕ} (i : Fin (n + 1)) (S : (Fin (n + 1) → Bool) → List Bool) (k : ℕ) : Prop :=
  ∃ c, ∀ x, x i = false → (S x).getD k false = c

lemma cls_step {n : ℕ} (i : Fin (n + 1)) (S : (Fin (n + 1) → Bool) → List Bool) (len : ℕ)
    (hlen : ∀ x, (S x).length = len) (hc : ∀ k, IW i S k ∨ RC i S k) (g : Gate)
    (hnew : (∀ x, val g (S (Function.update x i true)) = val g (S (Function.update x i false)))
      ∨ (∃ c, ∀ x, x i = false → val g (S x) = c)) :
    ∀ k, IW i (fun x => stp (S x) g) k ∨ RC i (fun x => stp (S x) g) k := by
  intro k
  rcases lt_trichotomy k len with h | h | h
  · rcases hc k with h' | ⟨c, h'⟩
    · left
      intro x
      simp only [stp, getD_one, hlen, if_pos h]
      exact h' x
    · right
      refine ⟨c, fun x hx => ?_⟩
      simp only [stp, getD_one, hlen, if_pos h]
      exact h' x hx
  · have a : ¬ k < len := by omega
    rcases hnew with h' | ⟨c, h'⟩
    · left
      intro x
      simp only [stp, getD_one, hlen, if_neg a, if_pos h]
      exact h' x
    · right
      refine ⟨c, fun x hx => ?_⟩
      simp only [stp, getD_one, hlen, if_neg a, if_pos h]
      exact h' x hx
  · have a : ¬ k < len := by omega
    have b : ¬ k = len := by omega
    left
    intro x
    simp only [stp, getD_one, hlen, if_neg a, if_neg b]

abbrev Res {n : ℕ} (i : Fin (n + 1)) (j : ℕ) (gs : List Gate)
    (S : (Fin (n + 1) → Bool) → List Bool) : Prop :=
  (∃ (J : ℕ) (src : Option ℕ), j ≤ J ∧ J < j + gs.length
      ∧ ∀ x, x i = false → Good J src j (S x) gs)
    ∨ (∀ k, IW i (fun x => gs.foldl stp (S x)) k ∨ RC i (fun x => gs.foldl stp (S x)) k)

lemma findB {n : ℕ} (i : Fin (n + 1)) (gs : List Gate) :
    ∀ (j len : ℕ) (S : (Fin (n + 1) → Bool) → List Bool), (∀ g ∈ gs, FI g) →
      (∀ x, (S x).length = len) → (∀ k, IW i S k ∨ RC i S k) → Res i j gs S := by
  induction gs with
  | nil =>
    intro j len S _ _ hc
    right
    exact hc
  | cons g gs ih =>
    intro j len S hF hlen hc
    have hFg := hF g (by simp)
    have hFt : ∀ g' ∈ gs, FI g' := fun g' h => hF g' (by simp [h])
    have cont : ((∀ x, val g (S (Function.update x i true)) = val g (S (Function.update x i false)))
        ∨ (∃ c, ∀ x, x i = false → val g (S x) = c)) → Res i j (g :: gs) S := by
      intro hnew
      have hc' := cls_step i S len hlen hc g hnew
      rcases ih (j + 1) (len + 1) (fun x => stp (S x) g) hFt
        (fun x => by simp only [stp, List.length_append, List.length_singleton, hlen]) hc'
        with ⟨J, src, h1, h2, h3⟩ | h
      · left
        refine ⟨J, src, by omega, by simp only [List.length_cons]; omega, fun x hx => ?_⟩
        rw [good_cons]
        exact ⟨fun h' => absurd h' (by omega), h3 x hx⟩
      · right
        exact h
    have elim : ∀ src : Option ℕ, g.op ≠ GateOp.not →
        (∀ x, x i = false → val g (S x) = srcval src (S x)) → Res i j (g :: gs) S := by
      intro src hop h
      left
      refine ⟨j, src, le_refl _, by simp only [List.length_cons]; omega, fun x hx => ?_⟩
      rw [good_cons]
      exact ⟨fun _ => ⟨hop, h x hx⟩, good_after _ _ _ _ _ (by omega)⟩
    have hfalse : ∀ x, false = srcval (some len) (S x) := fun x =>
      (List.getD_eq_default _ _ (hlen x).le).symm
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, hlen2⟩ := hFg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
      · exact cont (Or.inl fun x => rfl)
      · have e : ∀ w, val (Gate.mk GateOp.and [a]) w = w.getD a false := fun w => by
          simp [val, GateOp.eval]
        rcases hc a with ha | ⟨ca, ha⟩
        · exact cont (Or.inl fun x => by rw [e, e]; exact ha x)
        · exact cont (Or.inr ⟨ca, fun x hx => by rw [e]; exact ha x hx⟩)
      · have e : ∀ w, val (Gate.mk GateOp.and [a, b]) w = (w.getD a false && w.getD b false) :=
          fun w => by simp [val, GateOp.eval]
        rcases hc a with ha | ⟨ca, ha⟩
        · rcases hc b with hb | ⟨cb, hb⟩
          · exact cont (Or.inl fun x => by rw [e, e, ha x, hb x])
          · cases cb
            · exact elim (some len) (by simp) fun x hx => by
                rw [e, hb x hx, Bool.and_false]; exact hfalse x
            · exact elim (some a) (by simp) fun x hx => by
                rw [e, hb x hx, Bool.and_true]; rfl
        · cases ca
          · exact elim (some len) (by simp) fun x hx => by
              rw [e, ha x hx, Bool.false_and]; exact hfalse x
          · exact elim (some b) (by simp) fun x hx => by
              rw [e, ha x hx, Bool.true_and]; rfl
      · simp only [List.length_cons] at hlen2
        omega
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
      · exact cont (Or.inl fun x => rfl)
      · have e : ∀ w, val (Gate.mk GateOp.or [a]) w = w.getD a false := fun w => by
          simp [val, GateOp.eval]
        rcases hc a with ha | ⟨ca, ha⟩
        · exact cont (Or.inl fun x => by rw [e, e]; exact ha x)
        · exact cont (Or.inr ⟨ca, fun x hx => by rw [e]; exact ha x hx⟩)
      · have e : ∀ w, val (Gate.mk GateOp.or [a, b]) w = (w.getD a false || w.getD b false) :=
          fun w => by simp [val, GateOp.eval]
        rcases hc a with ha | ⟨ca, ha⟩
        · rcases hc b with hb | ⟨cb, hb⟩
          · exact cont (Or.inl fun x => by rw [e, e, ha x, hb x])
          · cases cb
            · exact elim (some a) (by simp) fun x hx => by
                rw [e, hb x hx, Bool.or_false]; rfl
            · exact elim none (by simp) fun x hx => by
                rw [e, hb x hx, Bool.or_true]; rfl
        · cases ca
          · exact elim (some b) (by simp) fun x hx => by
              rw [e, ha x hx, Bool.false_or]; rfl
          · exact elim none (by simp) fun x hx => by
              rw [e, ha x hx, Bool.true_or]; rfl
      · simp only [List.length_cons] at hlen2
        omega
    · rcases ins with _ | ⟨a, t⟩
      · exact cont (Or.inl fun x => rfl)
      · rcases hc a with ha | ⟨ca, ha⟩
        · exact cont (Or.inl fun x => congrArg (fun b => !b) (ha x))
        · exact cont (Or.inr ⟨!ca, fun x hx => congrArg (fun b => !b) (ha x hx)⟩)

lemma getD_map {n : ℕ} (x5 : List (Fin (n + 1))) (x : Fin (n + 1) → Bool) (k : ℕ)
    (hk : k < x5.length) : (x5.map x).getD k false = x x5[k] := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map]

noncomputable def sig {n : ℕ} (i : Fin (n + 1)) (x5 : List (Fin (n + 1))) (k : ℕ) : ℕ :=
  if h : k < x5.length then
    (if hv : x5[k] = i then n + 1 else (Classical.choose (Fin.exists_succAbove_eq hv)).val)
  else 0

lemma sig_lt {n : ℕ} (i : Fin (n + 1)) (x5 : List (Fin (n + 1))) (k : ℕ) (hk : k < x5.length) :
    sig i x5 k < n + 2 := by
  unfold sig
  rw [dif_pos hk]
  by_cases hv : x5[k] = i
  · rw [dif_pos hv]
    omega
  · rw [dif_neg hv]
    have := (Classical.choose (Fin.exists_succAbove_eq hv)).isLt
    omega

lemma sig_spec {n : ℕ} (i : Fin (n + 1)) (x5 : List (Fin (n + 1))) (k : ℕ) (y : Fin n → Bool)
    (hk : k < x5.length) :
    (List.ofFn y ++ [true] ++ [false]).getD (sig i x5 k) false
      = (Fin.insertNth i false y : Fin (n + 1) → Bool) x5[k] := by
  unfold sig
  rw [dif_pos hk, getD_two, List.length_ofFn]
  by_cases hv : x5[k] = i
  · rw [dif_pos hv, hv]
    simp
  · rw [dif_neg hv]
    have spec := Classical.choose_spec (Fin.exists_succAbove_eq hv)
    generalize Classical.choose (Fin.exists_succAbove_eq hv) = p at spec ⊢
    rw [← spec, Fin.insertNth_apply_succAbove, if_pos p.isLt,
      List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact p.isLt), List.getElem_ofFn]

noncomputable def rho {n : ℕ} (i : Fin (n + 1)) (x5 : List (Fin (n + 1))) (J k : ℕ) : ℕ :=
  if k < x5.length then sig i x5 k
  else n + 2 + 2 * (k - x5.length) + (if k - x5.length = J then 1 else 0)

lemma main (n : ℕ) (i : Fin (n + 1)) (C : Circuit) (x5 : List (Fin (n + 1)))
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hdep : ∃ x : Fin (n + 1) → Bool,
      C.eval (x5.map (Function.update x i true)) ≠ C.eval (x5.map (Function.update x i false)))
    (hnc : ∃ (y z : Fin n → Bool),
      C.eval (x5.map (Fin.insertNth i false y)) ≠ C.eval (x5.map (Fin.insertNth i false z))) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D
      ∧ List.countP nn D.gates + 1 ≤ List.countP nn C.gates
      ∧ PEqualNP.MetaComplexity.circuitFun n D
        = fun y : Fin n → Bool => C.eval (x5.map (Fin.insertNth i false y)) := by
  have hcls : ∀ k, IW i (fun x : Fin (n + 1) → Bool => x5.map x) k
      ∨ RC i (fun x : Fin (n + 1) → Bool => x5.map x) k := by
    intro k
    by_cases hk : k < x5.length
    · by_cases hv : x5[k] = i
      · right
        refine ⟨false, fun x hx => ?_⟩
        show (x5.map x).getD k false = false
        rw [getD_map x5 x k hk, hv, hx]
      · left
        intro x
        show (x5.map _).getD k false = (x5.map _).getD k false
        rw [getD_map x5 _ k hk, getD_map x5 _ k hk, Function.update_of_ne hv,
          Function.update_of_ne hv]
    · left
      intro x
      show (x5.map _).getD k false = (x5.map _).getD k false
      rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
        List.getD_eq_default _ _ (by rw [List.length_map]; omega)]
  have hins : ∀ y : Fin n → Bool, (Fin.insertNth i false y : Fin (n + 1) → Bool) i = false :=
    fun y => by simp
  rcases findB i C.gates 0 x5.length (fun x : Fin (n + 1) → Bool => x5.map x)
    (fun g hg => hF g hg) (fun x => List.length_map _) hcls with ⟨J, src, hJ1, hJ2, hG⟩ | hfin
  · have hρ1 : ∀ k, k < x5.length → rho i x5 J k < n + 2 := fun k hk => by
      unfold rho
      rw [if_pos hk]
      exact sig_lt i x5 k hk
    have hρ2 : ∀ k, x5.length ≤ k → rho i x5 J k
        = n + 2 + 2 * (k - x5.length) + (if k - x5.length = J then 1 else 0) := fun k hk => by
      have hnk : ¬ k < x5.length := by omega
      unfold rho
      rw [if_neg hnk]
    refine ⟨Circuit.mk (Gate.mk GateOp.not [] :: Gate.mk GateOp.not [n]
      :: tr (rho i x5 J) (uOf (rho i x5 J) n src) n J 0 C.gates) (rho i x5 J C.output),
      ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · simp
      · simp
      · exact fan_tr _ _ _ _ C.gates 0 (fun g hg => hF g hg) g hg
    · have h := cnt_at (rho i x5 J) (uOf (rho i x5 J) n src) n J src C.gates 0 _
        (hG (fun _ => false) rfl) (by omega) (by omega)
      have z1 : List.countP nn [Gate.mk GateOp.not []] = 0 := rfl
      have z2 : List.countP nn [Gate.mk GateOp.not [n]] = 0 := rfl
      have e2 : ∀ l : List Gate, List.countP nn
          (Gate.mk GateOp.not [] :: Gate.mk GateOp.not [n] :: l) = List.countP nn l := fun l => by
        rw [cnt_cons (Gate.mk GateOp.not []) (Gate.mk GateOp.not [n] :: l),
          cnt_cons (Gate.mk GateOp.not [n]) l, z1, z2]
        omega
      show List.countP nn (Gate.mk GateOp.not [] :: Gate.mk GateOp.not [n] :: _) + 1 ≤ _
      rw [e2]
      omega
    · funext y
      have hw : stp (stp (List.ofFn y) (Gate.mk GateOp.not [])) (Gate.mk GateOp.not [n])
          = List.ofFn y ++ [true] ++ [false] := by
        show (List.ofFn y ++ [true]) ++ [!((List.ofFn y ++ [true]).getD n false)] = _
        rw [getD_one, List.length_ofFn]
        simp
      show ((tr _ _ n J 0 C.gates).foldl stp
          (stp (stp (List.ofFn y) (Gate.mk GateOp.not [])) (Gate.mk GateOp.not [n]))).getD
            (rho i x5 J C.output) false
        = (C.gates.foldl stp (x5.map (Fin.insertNth i false y))).getD C.output false
      rw [hw]
      symm
      refine sim (rho i x5 J) x5.length n J src hρ1 hρ2 C.gates 0 _ _ (by simp) (by simp) ?_ ?_
        (hG _ (hins y)) C.output
      · intro k
        by_cases hk : k < x5.length
        · have hr : rho i x5 J k = sig i x5 k := by
            unfold rho
            rw [if_pos hk]
          rw [hr, sig_spec i x5 k y hk, getD_map x5 _ k hk]
        · have h2 := hρ2 k (by omega)
          rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega), getD_two,
            List.length_ofFn]
          split_ifs at h2 <;> split_ifs <;> first | omega | rfl
      · rw [getD_two, List.length_ofFn]
        simp
  · rcases hfin C.output with hI | ⟨c, hR⟩
    · obtain ⟨x, hx⟩ := hdep
      exact absurd (hI x) hx
    · obtain ⟨y, z, hyz⟩ := hnc
      exact absurd ((hR _ (hins y)).trans (hR _ (hins z)).symm) hyz

lemma nn_eq : (fun (g : Gate) =>
    GateOp.rec Bool.true Bool.true Bool.false (fun (_ : ℕ) => Bool.true) Bool.true g.op) = nn := by
  funext g
  rcases g with ⟨op, ins⟩
  cases op <;> rfl

lemma final : ∀ (x2 : ℕ) (x3 : Fin (x2 + 1)) (x4 : Circuit) (x5 : List (Fin (x2 + 1))),
    PEqualNP.MetaComplexity.FanInTwo x4 →
    (∃ (x8 : Fin (x2 + 1) → Bool), x4.eval (List.map (Function.update x8 x3 Bool.true) x5)
      ≠ x4.eval (List.map (Function.update x8 x3 Bool.false) x5)) →
    (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool),
      x4.eval (List.map (x3.insertNth Bool.false x9) x5)
        ≠ x4.eval (List.map (x3.insertNth Bool.false x10) x5)) →
    ∃ (x10 : Circuit), PEqualNP.MetaComplexity.FanInTwo x10
      ∧ List.countP (fun (g : Gate) =>
          GateOp.rec Bool.true Bool.true Bool.false (fun (_ : ℕ) => Bool.true) Bool.true g.op)
          x10.gates + 1
        ≤ List.countP (fun (g : Gate) =>
          GateOp.rec Bool.true Bool.true Bool.false (fun (_ : ℕ) => Bool.true) Bool.true g.op)
          x4.gates
      ∧ PEqualNP.MetaComplexity.circuitFun x2 x10
        = fun (x11 : Fin x2 → Bool) => x4.eval (List.map (x3.insertNth Bool.false x11) x5) := by
  intro x2 x3 x4 x5 hF hdep hnc
  obtain ⟨D, h1, h2, h3⟩ := main x2 x3 x4 x5 hF hdep hnc
  refine ⟨D, h1, ?_, h3⟩
  rw [nn_eq]
  exact h2

end PEqualNP.Outside.L_meta_2958

theorem PEqualNP.Outside.L_meta_2958 : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates ∧ PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x11 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x11) := by
  exact PEqualNP.Outside.L_meta_2958.final
