import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1954

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem difp {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a h := by simp [h]

theorem difn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a : c → α} {b : ¬ c → α} :
    dite c a b = b h := by simp [h]

def fd {α : Type} (F : Gate → List α → α) (X : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [F g w]) X

theorem fd_len {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α), (fd F X gs).length = X.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro X; simp [fd]
  | cons g gs ih =>
    intro X
    have := ih (X ++ [F g X])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp
    omega

theorem fd_pre {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α) (i : ℕ), i < X.length → (fd F X gs)[i]? = X[i]? := by
  intro gs
  induction gs with
  | nil => intro X i _; simp [fd]
  | cons g gs ih =>
    intro X i hi
    have := ih (X ++ [F g X]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this, List.getElem?_append_left hi]

theorem fd_app {α : Type} (F : Gate → List α → α) (X : List α) (gs hs : List Gate) :
    fd F X (gs ++ hs) = fd F (fd F X gs) hs := by
  simp [fd, List.foldl_append]

theorem fd_gate' {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (as : List Gate) (g : Gate) (bs : List Gate) (X : List α)
    (hrb : ∀ i ∈ g.inputs, i < X.length + as.length) :
    (fd F X (as ++ g :: bs)).getD (X.length + as.length) dflt = F g (fd F X (as ++ g :: bs)) := by
  have e1 : fd F X (as ++ g :: bs) = fd F (fd F X as ++ [F g (fd F X as)]) bs := by
    simp [fd, List.foldl_append]
  have hWl : (fd F X as).length = X.length + as.length := fd_len F as X
  have key : ∀ i, i < (fd F X as).length + 1 →
      (fd F X (as ++ g :: bs))[i]? = (fd F X as ++ [F g (fd F X as)])[i]? := by
    intro i hi
    rw [e1]
    exact fd_pre F bs _ i (by simp; omega)
  rw [List.getD_eq_getElem?_getD, key _ (by omega), ← hWl,
    List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  apply hF
  intro i hi
  have hi' := hrb i hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, key i (by omega),
    List.getElem?_append_left (by omega)]

theorem fd_gate {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (gs : List Gate) (X : List α) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < X.length + j) :
    (fd F X gs).getD (X.length + j) dflt = F (gs.getD j ⟨GateOp.or, []⟩) (fd F X gs) := by
  have h1 : gs.take j ++ gs[j] :: gs.drop (j + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hj]
    exact List.take_append_drop j gs
  have h2 : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := by
    simp [List.getD_eq_getElem?_getD, hj]
  have h3 := fd_gate' F dflt hF (gs.take j) gs[j] (gs.drop (j + 1)) X (by
    rw [List.length_take, min_eq_left hj.le, ← h2]
    exact hrb)
  rw [h1, List.length_take, min_eq_left hj.le] at h3
  rw [h2]
  exact h3

def stpF : Gate → List Bool → Bool :=
  fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

theorem stpF_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : stpF g w = stpF g w' := by
  unfold stpF
  rw [List.map_congr_left h]

theorem ld_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : g.lineDegree w = g.lineDegree w' := by
  unfold Gate.lineDegree
  rw [List.map_congr_left h]

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ifn (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ifn (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (fd stpF W1 gs).getD i false = true → (fd stpF W2 gs).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa [fd] using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    have := ih (W1 ++ [stpF g W1]) (W2 ++ [stpF g W2]) (by simp [hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) (by
        intro i
        simp only [getD_snoc, hl]
        split_ifs
        · unfold stpF
          rcases hop g List.mem_cons_self with ha | ho
          · rw [ev_and g _ ha, ev_and g _ ha]
            intro h k hk
            exact H k (h k hk)
          · rw [ev_or g _ ho, ev_or g _ ho]
            rintro ⟨k, hk, h⟩
            exact ⟨k, hk, H k h⟩
        · exact H i)
    simpa only [fd, List.foldl_cons] using this

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem app_getD {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ) :
    (List.ofFn (Fin.append x y)).getD i false =
      if h : i < n then x ⟨i, h⟩ else if h2 : i - n < m then y ⟨i - n, h2⟩ else false := by
  rw [ofFn_getD]
  by_cases h : i < n
  · rw [difp (by omega), difp h]
    exact Fin.append_left x y ⟨i, h⟩
  · rw [difn h]
    by_cases h2 : i - n < m
    · rw [difp (by omega), difp h2]
      have hh : (⟨i, by omega⟩ : Fin (n + m)) = Fin.natAdd n ⟨i - n, h2⟩ := by
        apply Fin.ext
        show i = n + (i - n)
        omega
      rw [hh, Fin.append_right]
    · rw [difn (by omega), difn h2]


theorem ble (a b : Bool) (h : a ≤ b) (ha : a = true) : b = true := by
  subst ha
  revert h
  cases b <;> decide

theorem mono_of {α : Type} [Preorder α] (f : α → Bool)
    (h : ∀ a b, a ≤ b → f a = true → f b = true) : Monotone f := by
  intro a b hab
  cases ha : f a
  · exact Bool.false_le _
  · rw [h a b hab ha]

theorem of_mono {α : Type} [Preorder α] (f : α → Bool) (h : Monotone f) (a b : α) (hab : a ≤ b)
    (ha : f a = true) : f b = true := ble _ _ (h hab) ha

def V (C : Circuit) (X : List Bool) (w : ℕ) : Bool := (C.wires X).getD w false

def D (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees K M).getD w 0

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl

theorem V_in (C : Circuit) (X : List Bool) (w : ℕ) (hw : w < X.length) :
    V C X w = X.getD w false := by
  unfold V
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, fd_pre _ _ _ _ hw]

theorem V_out (C : Circuit) (X : List Bool) (w : ℕ) (hw : X.length + C.gates.length ≤ w) :
    V C X w = false := by
  unfold V
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    rw [fd_len]; exact hw)]
  rfl

theorem V_gate (K : ℕ) (C : Circuit) (hrb : ReadsBack K C) (X : List Bool) (hX : X.length = K)
    (j : ℕ) (hj : j < C.gates.length) :
    V C X (K + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C X)) := by
  have h := fd_gate stpF false stpF_congr C.gates X j hj (by
    intro i hi
    have := hrb j hj i hi
    rw [hX]
    exact this)
  rw [hX] at h
  exact h

theorem D_len (K : ℕ) (M : Finset ℕ) (C : Circuit) :
    (C.lineDegrees K M).length = K + C.gates.length := by
  have := fd_len Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0)
  simpa [fd, Circuit.lineDegrees] using this

theorem D_in (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : w < K) :
    D K M C w = if w ∈ M then 1 else 0 := by
  unfold D Circuit.lineDegrees
  have := fd_pre Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) w
    (by simpa using hw)
  unfold fd at this
  rw [List.getD_eq_getElem?_getD, this]
  simp [hw]

theorem D_out (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : K + C.gates.length ≤ w) :
    D K M C w = 0 := by
  unfold D
  have hl := D_len K M C
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem foldr_max_zero : ∀ (l : List ℕ), l.foldr max 0 = 0 ↔ ∀ a ∈ l, a = 0 := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    omega

theorem D_zero_iff (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (j : ℕ)
    (hj : j < C.gates.length) :
    D K M C (K + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, D K M C i = 0 := by
  have h := fd_gate Gate.lineDegree 0 ld_congr C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_map, List.length_range] at h
  have h' : D K M C (K + j) = (gateAt C j).lineDegree (C.lineDegrees K M) := h
  rw [h']
  unfold Gate.lineDegree
  split_ifs
  · rw [List.sum_eq_zero_iff]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl
  · rw [foldr_max_zero]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl

theorem indep (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (X X' : List Bool)
    (hX : X.length = K) (hX' : X'.length = K)
    (h : ∀ i, i < K → i ∉ M → X.getD i false = X'.getD i false) :
    ∀ w, D K M C w = 0 → V C X w = V C X' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    by_cases h1 : w < K
    · rw [D_in K M C w h1] at hd
      have hwn : w ∉ M := by
        intro hc
        rw [ifp hc] at hd
        omega
      rw [V_in _ _ _ (by omega), V_in _ _ _ (by omega)]
      exact h w h1 hwn
    · by_cases h2 : w < K + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = K + j := ⟨w - K, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [V_gate K C hrb X hX j hj, V_gate K C hrb X' hX' j hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        have := hrb j hj i hi
        exact ih i (by omega) ((D_zero_iff K M C hrb j hj).mp hd i hi)
      · rw [V_out _ _ _ (by omega), V_out _ _ _ (by omega)]

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

def W (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

def DL (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

def DP (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0

theorem W_indL (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x y y' : Fin N → Bool) (w : ℕ)
    (h : DL N C w = 0) : W N C x y w = W N C x y' w := by
  refine indep (N + N) (Finset.Ico N (N + N)) C hrb _ _ (by simp) (by simp) ?_ w h
  intro i hi hni
  have hlt : i < N := by
    by_contra hc
    exact hni (Finset.mem_Ico.mpr ⟨by omega, hi⟩)
  rw [app_getD, app_getD, difp hlt, difp hlt]

theorem W_indP (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x x' y : Fin N → Bool) (w : ℕ)
    (h : DP N C w = 0) : W N C x y w = W N C x' y w := by
  refine indep (N + N) (Finset.range N) C hrb _ _ (by simp) (by simp) ?_ w h
  intro i hi hni
  have hlt : ¬ i < N := by
    intro hc
    exact hni (Finset.mem_range.mpr hc)
  rw [app_getD, app_getD, difn hlt, difn hlt]

theorem bt (b : Bool) (h : ¬ b = false) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem pos (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ w, w < N + N + C.gates.length → ¬ (DP N C w = 0 ∧ DL N C w = 0) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hc
    by_cases h1 : w < N + N
    · have ha : D (N + N) (Finset.range N) C w = 0 := hc.1
      have hb : D (N + N) (Finset.Ico N (N + N)) C w = 0 := hc.2
      rw [D_in _ _ _ _ h1] at ha
      rw [D_in _ _ _ _ h1] at hb
      by_cases h3 : w < N
      · rw [ifp (Finset.mem_range.mpr h3)] at ha
        omega
      · rw [ifp (Finset.mem_Ico.mpr ⟨by omega, h1⟩)] at hb
        omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := h2 _ (gateAt_mem C j hj)
      obtain ⟨a, ha⟩ : ∃ a, a ∈ (gateAt C j).inputs := by
        rcases hin : (gateAt C j).inputs with _ | ⟨a, t⟩
        · rw [hin] at hg
          simp at hg
        · exact ⟨a, by simp⟩
      have hlt := hrb j hj a ha
      exact ih a (by omega) (by omega)
        ⟨(D_zero_iff (N + N) (Finset.range N) C hrb j hj).mp hc.1 a ha,
         (D_zero_iff (N + N) (Finset.Ico N (N + N)) C hrb j hj).mp hc.2 a ha⟩

theorem cnt (n : ℕ) (a b : ℕ → ℕ) (h : ∀ j < n, ¬ (a j = 0 ∧ b j = 0)) :
    Set.ncard {j : ℕ | j < n ∧ a j = 0} + Set.ncard {j : ℕ | j < n ∧ b j = 0}
      + Set.ncard {j : ℕ | j < n ∧ 0 < a j ∧ 0 < b j} ≤ n := by
  have e1 : {j : ℕ | j < n ∧ a j = 0} = ↑((Finset.range n).filter (fun j => a j = 0)) := by
    ext j
    simp
  have e2 : {j : ℕ | j < n ∧ b j = 0} = ↑((Finset.range n).filter (fun j => b j = 0)) := by
    ext j
    simp
  have e3 : {j : ℕ | j < n ∧ 0 < a j ∧ 0 < b j}
      = ↑((Finset.range n).filter (fun j => 0 < a j ∧ 0 < b j)) := by
    ext j
    simp
  rw [e1, e2, e3, Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  calc _ ≤ ∑ j ∈ Finset.range n, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        have := h j (Finset.mem_range.mp hj)
        split_ifs <;> omega
    _ = n := by simp

theorem cnt3 (n : ℕ) (a b : ℕ → ℕ) (S : Set ℕ) (hS : ∀ j ∈ S, j < n ∧ 0 < a j ∧ 0 < b j)
    (h : ∀ j < n, ¬ (a j = 0 ∧ b j = 0)) :
    Set.ncard {j : ℕ | j < n ∧ a j = 0} + Set.ncard {j : ℕ | j < n ∧ b j = 0} + S.ncard ≤ n := by
  have h1 := cnt n a b h
  have h2 : S.ncard ≤ Set.ncard {j : ℕ | j < n ∧ 0 < a j ∧ 0 < b j} := by
    exact Set.ncard_le_ncard (fun j hj => hS j hj)
      ((Finset.finite_toSet (Finset.range n)).subset (by
        intro j hj
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr hj.1)))
  omega

theorem cardU (cone isAnd isOr : ℕ → Prop) (n : ℕ) (hc : ∀ j, cone j → j < n)
    (hex : ∀ j, isAnd j → isOr j → False) (KB KP J : Finset ℕ)
    (hKB : ∀ j ∈ KB, cone j ∧ isAnd j) (hKP : ∀ j ∈ KP, cone j ∧ isAnd j)
    (hJ : ∀ j ∈ J, cone j ∧ isAnd j) (d1 : Disjoint KB KP) (d2 : ∀ j ∈ J, j ∉ KB)
    (d3 : ∀ j ∈ J, j ∉ KP) :
    KB.card + KP.card + J.card + Set.ncard {j : ℕ | cone j ∧ isOr j}
      ≤ Set.ncard {j : ℕ | cone j} := by
  classical
  have hfin : {j : ℕ | cone j}.Finite := (Finset.finite_toSet (Finset.range n)).subset (by
    intro j hj
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hc j hj)))
  have hfo : {j : ℕ | cone j ∧ isOr j}.Finite := hfin.subset (fun j hj => hj.1)
  have hd : Disjoint (KB ∪ KP) J := by
    rw [Finset.disjoint_left]
    intro j hj hjJ
    rcases Finset.mem_union.mp hj with h | h
    · exact d2 j hjJ h
    · exact d3 j hjJ h
  have hcard : ((KB ∪ KP) ∪ J).card = KB.card + KP.card + J.card := by
    rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint d1]
  have hmem : ∀ j ∈ (KB ∪ KP) ∪ J, cone j ∧ isAnd j := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hKB j h
      · exact hKP j h
    · exact hJ j h
  have hdis : Disjoint (↑((KB ∪ KP) ∪ J) : Set ℕ) {j : ℕ | cone j ∧ isOr j} := by
    rw [Set.disjoint_left]
    intro j hj hjo
    exact hex j (hmem j (Finset.mem_coe.mp hj)).2 hjo.2
  have hun := Set.ncard_union_eq hdis (Finset.finite_toSet _) hfo
  rw [Set.ncard_coe_finset, hcard] at hun
  rw [← hun]
  apply Set.ncard_le_ncard _ hfin
  intro j hj
  rcases hj with hj | hj
  · exact (hmem j (Finset.mem_coe.mp hj)).1
  · exact hj.1

theorem core {N : ℕ} (C : Circuit) (I : Fin N → Fin N → Prop) (t : ℕ)
    (cone : ℕ → Prop) (lvx : (Fin N → Bool) → ℕ → Prop) (ppw : ℕ → Fin N → Prop)
    (lps pps : Fin N → Fin N → Prop)
    (hAO : (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
      ∧ ReadsBack (N + N) C)
    (hc1 : ∀ j, cone j → j < C.gates.length ∧ 0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j))
    (hpps : ∀ p w, pps p w → ∃ h, ppw h p)
    (hcov : ∀ A B : Finset (Fin N), (∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) → t ≤ A.card + B.card)
    (hsplit : ∀ p w : Fin N, I p w → lps p w ∨ pps p w)
    (TL TP : Finset (Fin N)) (KB KP : Finset ℕ) (own : ℕ → Fin N)
    (hK : ∀ j ∈ KB ∪ KP, cone j ∧ (gateAt C j).op = GateOp.and) (hdisj : Disjoint KB KP)
    (hKB : ∀ j ∈ KB, ∃ p p' : Fin N, p ≠ p' ∧ lvx (fun a : Fin N => decide (a = p)) j
      ∧ lvx (fun a : Fin N => decide (a = p')) j)
    (hKP : ∀ j ∈ KP, own j ∈ TP ∧ ∀ p : Fin N, lvx (fun a : Fin N => decide (a = p)) j → p = own j)
    (hTP : ∀ p ∈ TP, ∃ j ∈ KP, own j = p)
    (hcovL : ∀ p w : Fin N, lps p w → w ∈ TL ∨ p ∈ TP)
    (hown : ∀ (p : Fin N) (h : ℕ), ppw h p → ∃ j : ℕ, cone j ∧ (gateAt C j).op = GateOp.and
      ∧ lvx (fun a : Fin N => decide (a = p)) j
      ∧ ∀ p' : Fin N, lvx (fun a : Fin N => decide (a = p')) j → p' = p)
    {A Bm spf smx slpw PW : ℕ}
    (h1 : Set.ncard {j : ℕ | cone j ∧ (gateAt C j).op = GateOp.or} + Set.ncard {j : ℕ | cone j}
      = spf + smx)
    (h3 : A + TL.card + Set.ncard {j : ℕ | cone j}
      ≤ Set.ncard {j : ℕ | j < C.gates.length ∧ DL N C (N + N + j) = 0} + KB.card + slpw + smx + 1)
    (h4a : Bm ≤ Set.ncard {j : ℕ | j < C.gates.length ∧ DP N C (N + N + j) = 0} + PW)
    (h4b : slpw + PW ≤ spf) :
    A + Bm + t ≤ C.size + 1 := by
  classical
  have hex : ∀ p : Fin N, ∃ j : ℕ, (∃ h, ppw h p) → (cone j ∧ (gateAt C j).op = GateOp.and
      ∧ lvx (fun a : Fin N => decide (a = p)) j
      ∧ ∀ p' : Fin N, lvx (fun a : Fin N => decide (a = p')) j → p' = p) := by
    intro p
    by_cases hp : ∃ h, ppw h p
    · obtain ⟨h, hh⟩ := hp
      obtain ⟨j, hj⟩ := hown p h hh
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose jf hjf using hex
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset (Fin N), ∀ p, p ∈ Q ↔ ((∃ h, ppw h p) ∧ p ∉ TP) :=
    ⟨(Finset.univ.filter (fun p => ∃ h, ppw h p)) \ TP, by
      intro p
      simp⟩
  have hinj : Set.InjOn jf (↑Q : Set (Fin N)) := by
    intro p hp p' hp' e
    have h5 := hjf p ((hQ p).mp (Finset.mem_coe.mp hp)).1
    have h6 := hjf p' ((hQ p').mp (Finset.mem_coe.mp hp')).1
    have h7 : lvx (fun a : Fin N => decide (a = p')) (jf p) := by
      rw [e]
      exact h6.2.2.1
    exact (h5.2.2.2 p' h7).symm
  have ht : t ≤ TL.card + KP.card + (Q.image jf).card := by
    have hc := hcov (TP ∪ Q) TL (by
      intro p w hI
      rcases hsplit p w hI with h | h
      · rcases hcovL p w h with h' | h'
        · exact Or.inr h'
        · exact Or.inl (Finset.mem_union_left _ h')
      · by_cases hpT : p ∈ TP
        · exact Or.inl (Finset.mem_union_left _ hpT)
        · exact Or.inl (Finset.mem_union_right _ ((hQ p).mpr ⟨hpps p w h, hpT⟩)))
    have h5 : (TP ∪ Q).card ≤ TP.card + Q.card := Finset.card_union_le _ _
    have h6 : TP.card ≤ KP.card := by
      calc TP.card ≤ (KP.image own).card := Finset.card_le_card (by
            intro p hp
            obtain ⟨j, hj, e⟩ := hTP p hp
            exact Finset.mem_image.mpr ⟨j, hj, e⟩)
        _ ≤ KP.card := Finset.card_image_le
    rw [Finset.card_image_of_injOn hinj]
    omega
  have hJ : ∀ j ∈ Q.image jf, ∃ p : Fin N, p ∉ TP ∧ cone j ∧ (gateAt C j).op = GateOp.and
      ∧ lvx (fun a : Fin N => decide (a = p)) j
      ∧ ∀ p' : Fin N, lvx (fun a : Fin N => decide (a = p')) j → p' = p := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨p, ((hQ p).mp hp).2, hjf p ((hQ p).mp hp).1⟩
  have hU : KB.card + KP.card + (Q.image jf).card
      + Set.ncard {j : ℕ | cone j ∧ (gateAt C j).op = GateOp.or} ≤ Set.ncard {j : ℕ | cone j} :=
    cardU cone (fun j => (gateAt C j).op = GateOp.and) (fun j => (gateAt C j).op = GateOp.or)
      C.gates.length (fun j hj => (hc1 j hj).1)
      (by
        intro j h5 h6
        rw [h5] at h6
        exact GateOp.noConfusion h6)
      KB KP (Q.image jf)
      (fun j hj => hK j (Finset.mem_union_left _ hj))
      (fun j hj => hK j (Finset.mem_union_right _ hj))
      (by
        intro j hj
        obtain ⟨p, -, h5, h6, -⟩ := hJ j hj
        exact ⟨h5, h6⟩)
      hdisj
      (by
        intro j hj hjB
        obtain ⟨p, -, -, -, -, h5⟩ := hJ j hj
        obtain ⟨p1, p2, hne, h6, h7⟩ := hKB j hjB
        exact hne ((h5 p1 h6).trans (h5 p2 h7).symm))
      (by
        intro j hj hjP
        obtain ⟨p, hpT, -, -, h5, -⟩ := hJ j hj
        have h6 := hKP j hjP
        rw [h6.2 p h5] at hpT
        exact hpT h6.1)
  have hcount : Set.ncard {j : ℕ | j < C.gates.length ∧ DL N C (N + N + j) = 0}
      + Set.ncard {j : ℕ | j < C.gates.length ∧ DP N C (N + N + j) = 0}
      + Set.ncard {j : ℕ | cone j} ≤ C.gates.length :=
    cnt3 C.gates.length (fun j => DL N C (N + N + j)) (fun j => DP N C (N + N + j))
      {j : ℕ | cone j}
      (fun j hj => ⟨(hc1 j hj).1, (hc1 j hj).2.2, (hc1 j hj).2.1⟩)
      (fun j hj hc => pos N C hAO.2 hAO.1 (N + N + j) (by omega) ⟨hc.2, hc.1⟩)
  show A + Bm + t ≤ C.gates.length + 1
  omega

end PEqualNP.Outside.L_meta_1954

theorem PEqualNP.Outside.L_meta_1954 : (∀ (N230 : ℕ) (C230 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g230 ∈ C230.gates, (g230.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g230.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g230.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N230 + N230) C230) → (∀ j230x2 < C230.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i230x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x2 0 = 0) ∨ (∀ h230 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD h230 0 = 0)) → PEqualNP.MetaComplexity.circuitFun (N230 + N230) C230 (Fin.append (fun u230 : Fin N230 => true) (fun u230x1 : Fin N230 => false)) = false → ∀ mixed230 : ℕ → Prop, mixed230 = (fun i230 : ℕ => 0 < (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD i230 0 ∧ 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230 0) → ∀ cone230 : ℕ → Prop, cone230 = (fun j230 : ℕ => j230 < C230.gates.length ∧ mixed230 (N230 + N230 + j230) ∧ Relation.ReflTransGen (fun a230 b230 : ℕ => a230 < b230 ∧ ∃ f230 : Fin C230.gates.length, b230 = N230 + N230 + f230.val ∧ a230 ∈ (C230.gates.get f230).inputs) (N230 + N230 + j230) C230.output) → (∀ j230x1 : ℕ, cone230 j230x1 → (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i230x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).inputs, 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x1 0) ∧ Set.ncard {j230x3 : ℕ | cone230 j230x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x3).op = PEqualNP.CircuitLowerBounds.GateOp.or} + Set.ncard {j230x4 : ℕ | cone230 j230x4} = Set.ncard {js230 : ℕ × ℕ | cone230 js230.1 ∧ js230.2 < 2 ∧ (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230.1).inputs.getD js230.2 0) 0 = 0} + Set.ncard {js230x1 : ℕ × ℕ | cone230 js230x1.1 ∧ js230x1.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x1.1).inputs.getD js230x1.2 0)} ∧ Set.ncard {j230x5 : ℕ | cone230 j230x5} ≤ Set.ncard {js230x2 : ℕ × ℕ | cone230 js230x2.1 ∧ js230x2.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x2.1).inputs.getD js230x2.2 0)} + 1) → (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → (∀ (N241 : ℕ) (I241 : Fin N241 → Fin N241 → Prop) [DecidableRel I241] (C241 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g241 ∈ C241.gates, (g241.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g241.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g241.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N241 + N241) C241) → (∀ j241 < C241.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i241 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).inputs, (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241 0 = 0) ∨ (∀ h241 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).inputs, (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD h241 0 = 0)) → (∀ p241 p241x1 w241 w241x1 : Fin N241, p241 ≠ p241x1 → w241 ≠ w241x1 → I241 p241 w241 → I241 p241x1 w241 → I241 p241 w241x1 → I241 p241x1 w241x1 → False) → (∃ p241x2 w241x2 : Fin N241, I241 p241x2 w241x2) → (∀ p241x3 w241x3 : Fin N241, I241 p241x3 w241x3 → PEqualNP.MetaComplexity.circuitFun (N241 + N241) C241 (Fin.append (fun a241 : Fin N241 => decide (a241 = p241x3)) (fun a241x1 : Fin N241 => decide (a241x1 = w241x3))) = true) → (∀ x241 y241 : Fin N241 → Bool, (Finset.univ.filter (fun l241 : Fin N241 => y241 l241 = true)).card ≤ 1 → (¬ ∃ p241x4 w241x4 : Fin N241, I241 p241x4 w241x4 ∧ x241 p241x4 = true ∧ y241 w241x4 = true) → PEqualNP.MetaComplexity.circuitFun (N241 + N241) C241 (Fin.append x241 y241) = false) → ∀ mixed241 : ℕ → Prop, mixed241 = (fun i241x1 : ℕ => 0 < (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD i241x1 0 ∧ 0 < (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241x1 0) → ∀ cone241 : ℕ → Prop, cone241 = (fun j241x1 : ℕ => j241x1 < C241.gates.length ∧ mixed241 (N241 + N241 + j241x1) ∧ Relation.ReflTransGen (fun a241x2 b241 : ℕ => a241x2 < b241 ∧ ∃ f241 : Fin C241.gates.length, b241 = N241 + N241 + f241.val ∧ a241x2 ∈ (C241.gates.get f241).inputs) (N241 + N241 + j241x1) C241.output) → ∀ gok241 : (Fin N241 → Bool) → ℕ → Prop, gok241 = (fun (x241x1 : Fin N241 → Bool) (j241x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i241x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x2).inputs, (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241x2 0 = 0 ∧ (C241.wires (List.ofFn (Fin.append x241x1 (fun u241 : Fin N241 => false)))).getD i241x2 false = true) → ∀ step241 : (Fin N241 → Bool) → ℕ → ℕ → Prop, step241 = (fun (x241x2 : Fin N241 → Bool) (j241x3 j241x4 : ℕ) => cone241 j241x4 ∧ N241 + N241 + j241x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x4).inputs ∧ gok241 x241x2 j241x4) → ∀ lvx241 : (Fin N241 → Bool) → ℕ → Prop, lvx241 = (fun (x241x3 : Fin N241 → Bool) (j241x5 : ℕ) => cone241 j241x5 ∧ gok241 x241x3 j241x5 ∧ ∃ j241x6 : ℕ, N241 + N241 + j241x6 = C241.output ∧ Relation.ReflTransGen (step241 x241x3) j241x5 j241x6) → ∀ slot241 : ℕ → ℕ → Prop, slot241 = (fun h241x1 j241x7 : ℕ => cone241 j241x7 ∧ h241x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x7).inputs ∧ (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD h241x1 0 = 0) → ∀ ap241 : ℕ → Fin N241 → Prop, ap241 = (fun (h241x2 : ℕ) (p241x5 : Fin N241) => ∃ j241x8 : ℕ, slot241 h241x2 j241x8 ∧ lvx241 (fun a241x3 : Fin N241 => decide (a241x3 = p241x5)) j241x8) → ∀ lh241 : ℕ → Fin N241 → Prop, lh241 = (fun (h241x3 : ℕ) (w241x5 : Fin N241) => (C241.wires (List.ofFn (Fin.append (fun u241x1 : Fin N241 => false) (fun a241x4 : Fin N241 => decide (a241x4 = w241x5))))).getD h241x3 false = true) → ∀ lpw241 : ℕ → Fin N241 → Prop, lpw241 = (fun (h241x4 : ℕ) (w241x6 : Fin N241) => ∀ w241x7 : Fin N241, lh241 h241x4 w241x7 ↔ w241x7 = w241x6) → ∀ lps241 : Fin N241 → Fin N241 → Prop, lps241 = (fun p241x6 w241x8 : Fin N241 => ∃ h241x5 : ℕ, lpw241 h241x5 w241x8 ∧ ap241 h241x5 p241x6) → ∃ (TL241 TP241 : Finset (Fin N241)) (KB241 KP241 : Finset ℕ) (own241 : ℕ → Fin N241), (∀ j241x9 ∈ KB241 ∪ KP241, cone241 j241x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x9).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Disjoint KB241 KP241 ∧ (∀ j241x10 ∈ KB241, ∃ p241x7 p241x8 : Fin N241, p241x7 ≠ p241x8 ∧ lvx241 (fun a241x5 : Fin N241 => decide (a241x5 = p241x7)) j241x10 ∧ lvx241 (fun a241x6 : Fin N241 => decide (a241x6 = p241x8)) j241x10) ∧ (∀ j241x11 ∈ KP241, own241 j241x11 ∈ TP241 ∧ ∀ p241x9 : Fin N241, lvx241 (fun a241x7 : Fin N241 => decide (a241x7 = p241x9)) j241x11 → p241x9 = own241 j241x11) ∧ (∀ p241x10 ∈ TP241, ∃ j241x12 ∈ KP241, own241 j241x12 = p241x10) ∧ (∀ p241x11 w241x9 : Fin N241, lps241 p241x11 w241x9 → w241x9 ∈ TL241 ∨ p241x11 ∈ TP241) ∧ ∑ w241x10 : Fin N241, Set.ncard {p241x12 : Fin N241 | lps241 p241x12 w241x10} + TL241.card + Set.ncard {j241x13 : ℕ | cone241 j241x13} ≤ Set.ncard {j241x14 : ℕ | j241x14 < C241.gates.length ∧ (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD (N241 + N241 + j241x14) 0 = 0} + KB241.card + Set.ncard {js241 : ℕ × ℕ | cone241 js241.1 ∧ js241.2 < 2 ∧ (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241.1).inputs.getD js241.2 0) 0 = 0 ∧ ∃ w241x11 : Fin N241, lpw241 ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241.1).inputs.getD js241.2 0) w241x11} + Set.ncard {js241x1 : ℕ × ℕ | cone241 js241x1.1 ∧ js241x1.2 < 2 ∧ mixed241 ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241x1.1).inputs.getD js241x1.2 0)} + 1) → (∀ (N250 k250 : ℕ) (I250 : Fin N250 → Fin N250 → Prop) [DecidableRel I250] (C250 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g250 ∈ C250.gates, (g250.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g250.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g250.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N250 + N250) C250) → (∀ j250 < C250.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i250 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).inputs, (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250 0 = 0) ∨ (∀ h250 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).inputs, (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD h250 0 = 0)) → (∀ p250 p250x1 w250 w250x1 : Fin N250, p250 ≠ p250x1 → w250 ≠ w250x1 → I250 p250 w250 → I250 p250x1 w250 → I250 p250 w250x1 → I250 p250x1 w250x1 → False) → (∃ p250x2 w250x2 : Fin N250, I250 p250x2 w250x2) → 1 ≤ k250 → (∀ p250x3 w250x3 : Fin N250, I250 p250x3 w250x3 → PEqualNP.MetaComplexity.circuitFun (N250 + N250) C250 (Fin.append (fun a250 : Fin N250 => decide (a250 = p250x3)) (fun a250x1 : Fin N250 => decide (a250x1 = w250x3))) = true) → (∀ x250 y250 : Fin N250 → Bool, (Finset.univ.filter (fun l250 : Fin N250 => y250 l250 = true)).card ≤ k250 → (¬ ∃ p250x4 w250x4 : Fin N250, I250 p250x4 w250x4 ∧ x250 p250x4 = true ∧ y250 w250x4 = true) → PEqualNP.MetaComplexity.circuitFun (N250 + N250) C250 (Fin.append x250 y250) = false) → ∀ mixed250 : ℕ → Prop, mixed250 = (fun i250x1 : ℕ => 0 < (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD i250x1 0 ∧ 0 < (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250x1 0) → ∀ cone250 : ℕ → Prop, cone250 = (fun j250x1 : ℕ => j250x1 < C250.gates.length ∧ mixed250 (N250 + N250 + j250x1) ∧ Relation.ReflTransGen (fun a250x2 b250 : ℕ => a250x2 < b250 ∧ ∃ f250 : Fin C250.gates.length, b250 = N250 + N250 + f250.val ∧ a250x2 ∈ (C250.gates.get f250).inputs) (N250 + N250 + j250x1) C250.output) → ∀ gok250 : (Fin N250 → Bool) → ℕ → Prop, gok250 = (fun (x250x1 : Fin N250 → Bool) (j250x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i250x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x2).inputs, (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250x2 0 = 0 ∧ (C250.wires (List.ofFn (Fin.append x250x1 (fun u250 : Fin N250 => false)))).getD i250x2 false = true) → ∀ step250 : (Fin N250 → Bool) → ℕ → ℕ → Prop, step250 = (fun (x250x2 : Fin N250 → Bool) (j250x3 j250x4 : ℕ) => cone250 j250x4 ∧ N250 + N250 + j250x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x4).inputs ∧ gok250 x250x2 j250x4) → ∀ lvx250 : (Fin N250 → Bool) → ℕ → Prop, lvx250 = (fun (x250x3 : Fin N250 → Bool) (j250x5 : ℕ) => cone250 j250x5 ∧ gok250 x250x3 j250x5 ∧ ∃ j250x6 : ℕ, N250 + N250 + j250x6 = C250.output ∧ Relation.ReflTransGen (step250 x250x3) j250x5 j250x6) → ∀ slot250 : ℕ → ℕ → Prop, slot250 = (fun h250x1 j250x7 : ℕ => cone250 j250x7 ∧ h250x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x7).inputs ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD h250x1 0 = 0) → ∀ ap250 : ℕ → Fin N250 → Prop, ap250 = (fun (h250x2 : ℕ) (p250x5 : Fin N250) => ∃ j250x8 : ℕ, slot250 h250x2 j250x8 ∧ lvx250 (fun a250x3 : Fin N250 => decide (a250x3 = p250x5)) j250x8) → ∀ lh250 : ℕ → Fin N250 → Prop, lh250 = (fun (h250x3 : ℕ) (w250x5 : Fin N250) => (C250.wires (List.ofFn (Fin.append (fun u250x1 : Fin N250 => false) (fun a250x4 : Fin N250 => decide (a250x4 = w250x5))))).getD h250x3 false = true) → ∀ lpw250 : ℕ → Fin N250 → Prop, lpw250 = (fun (h250x4 : ℕ) (w250x6 : Fin N250) => ∀ w250x7 : Fin N250, lh250 h250x4 w250x7 ↔ w250x7 = w250x6) → ∀ ppw250 : ℕ → Fin N250 → Prop, ppw250 = (fun (h250x5 : ℕ) (p250x6 : Fin N250) => (∃ w250x8 w250x9 : Fin N250, w250x8 ≠ w250x9 ∧ lh250 h250x5 w250x8 ∧ lh250 h250x5 w250x9) ∧ ∀ p250x7 : Fin N250, ap250 h250x5 p250x7 ↔ p250x7 = p250x6) → ∀ pps250 : Fin N250 → Fin N250 → Prop, pps250 = (fun p250x8 w250x10 : Fin N250 => ∃ h250x6 : ℕ, ppw250 h250x6 p250x8 ∧ lh250 h250x6 w250x10) → (∀ (p250x9 : Fin N250) (h250x7 : ℕ), ppw250 h250x7 p250x9 → ∃ j250x9 : ℕ, cone250 j250x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ lvx250 (fun a250x5 : Fin N250 => decide (a250x5 = p250x9)) j250x9 ∧ ∀ p250x10 : Fin N250, lvx250 (fun a250x6 : Fin N250 => decide (a250x6 = p250x10)) j250x9 → p250x10 = p250x9) ∧ ∑ p250x11 : Fin N250, min (k250 + 1) (Set.ncard {w250x11 : Fin N250 | pps250 p250x11 w250x11}) ≤ Set.ncard {j250x10 : ℕ | j250x10 < C250.gates.length ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD (N250 + N250 + j250x10) 0 = 0} + Set.ncard {h250x8 : ℕ | ∃ p250x12 : Fin N250, ppw250 h250x8 p250x12} ∧ Set.ncard {js250 : ℕ × ℕ | cone250 js250.1 ∧ js250.2 < 2 ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250.1).inputs.getD js250.2 0) 0 = 0 ∧ ∃ w250x12 : Fin N250, lpw250 ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250.1).inputs.getD js250.2 0) w250x12} + Set.ncard {h250x9 : ℕ | ∃ p250x13 : Fin N250, ppw250 h250x9 p250x13} ≤ Set.ncard {js250x1 : ℕ × ℕ | cone250 js250x1.1 ∧ js250x1.2 < 2 ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250x1.1).inputs.getD js250x1.2 0) 0 = 0}) → ∀ (N260 k260 t260 : ℕ) (I260 : Fin N260 → Fin N260 → Prop) [DecidableRel I260] (C260 : PEqualNP.CircuitLowerBounds.Circuit), (∀ p260 p260x1 w260 w260x1 : Fin N260, p260 ≠ p260x1 → w260 ≠ w260x1 → I260 p260 w260 → I260 p260x1 w260 → I260 p260 w260x1 → I260 p260x1 w260x1 → False) → (∃ p260x2 w260x2 : Fin N260, I260 p260x2 w260x2) → 1 ≤ k260 → ((∀ g260 ∈ C260.gates, (g260.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g260.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g260.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N260 + N260) C260) → (∀ j260 < C260.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260 0 = 0) ∨ (∀ h260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD h260 0 = 0)) → (∀ p260x3 w260x3 : Fin N260, I260 p260x3 w260x3 → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append (fun a260 : Fin N260 => decide (a260 = p260x3)) (fun a260x1 : Fin N260 => decide (a260x1 = w260x3))) = true) → (∀ x260 y260 : Fin N260 → Bool, (Finset.univ.filter (fun l260 : Fin N260 => y260 l260 = true)).card ≤ k260 → (¬ ∃ p260x4 w260x4 : Fin N260, I260 p260x4 w260x4 ∧ x260 p260x4 = true ∧ y260 w260x4 = true) → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append x260 y260) = false) → (∀ A260 B260 : Finset (Fin N260), (∀ p260x5 w260x5 : Fin N260, I260 p260x5 w260x5 → p260x5 ∈ A260 ∨ w260x5 ∈ B260) → t260 ≤ A260.card + B260.card) → ∀ mixed260 : ℕ → Prop, mixed260 = (fun i260x1 : ℕ => 0 < (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD i260x1 0 ∧ 0 < (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260x1 0) → ∀ cone260 : ℕ → Prop, cone260 = (fun j260x1 : ℕ => j260x1 < C260.gates.length ∧ mixed260 (N260 + N260 + j260x1) ∧ Relation.ReflTransGen (fun a260x2 b260 : ℕ => a260x2 < b260 ∧ ∃ f260 : Fin C260.gates.length, b260 = N260 + N260 + f260.val ∧ a260x2 ∈ (C260.gates.get f260).inputs) (N260 + N260 + j260x1) C260.output) → ∀ gok260 : (Fin N260 → Bool) → ℕ → Prop, gok260 = (fun (x260x1 : Fin N260 → Bool) (j260x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i260x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260x2 0 = 0 ∧ (C260.wires (List.ofFn (Fin.append x260x1 (fun u260 : Fin N260 => false)))).getD i260x2 false = true) → ∀ step260 : (Fin N260 → Bool) → ℕ → ℕ → Prop, step260 = (fun (x260x2 : Fin N260 → Bool) (j260x3 j260x4 : ℕ) => cone260 j260x4 ∧ N260 + N260 + j260x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x4).inputs ∧ gok260 x260x2 j260x4) → ∀ lvx260 : (Fin N260 → Bool) → ℕ → Prop, lvx260 = (fun (x260x3 : Fin N260 → Bool) (j260x5 : ℕ) => cone260 j260x5 ∧ gok260 x260x3 j260x5 ∧ ∃ j260x6 : ℕ, N260 + N260 + j260x6 = C260.output ∧ Relation.ReflTransGen (step260 x260x3) j260x5 j260x6) → ∀ slot260 : ℕ → ℕ → Prop, slot260 = (fun h260x1 j260x7 : ℕ => cone260 j260x7 ∧ h260x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x7).inputs ∧ (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD h260x1 0 = 0) → ∀ ap260 : ℕ → Fin N260 → Prop, ap260 = (fun (h260x2 : ℕ) (p260x6 : Fin N260) => ∃ j260x8 : ℕ, slot260 h260x2 j260x8 ∧ lvx260 (fun a260x3 : Fin N260 => decide (a260x3 = p260x6)) j260x8) → ∀ lh260 : ℕ → Fin N260 → Prop, lh260 = (fun (h260x3 : ℕ) (w260x6 : Fin N260) => (C260.wires (List.ofFn (Fin.append (fun u260x1 : Fin N260 => false) (fun a260x4 : Fin N260 => decide (a260x4 = w260x6))))).getD h260x3 false = true) → ∀ lpw260 : ℕ → Fin N260 → Prop, lpw260 = (fun (h260x4 : ℕ) (w260x7 : Fin N260) => ∀ w260x8 : Fin N260, lh260 h260x4 w260x8 ↔ w260x8 = w260x7) → ∀ ppw260 : ℕ → Fin N260 → Prop, ppw260 = (fun (h260x5 : ℕ) (p260x7 : Fin N260) => (∃ w260x9 w260x10 : Fin N260, w260x9 ≠ w260x10 ∧ lh260 h260x5 w260x9 ∧ lh260 h260x5 w260x10) ∧ ∀ p260x8 : Fin N260, ap260 h260x5 p260x8 ↔ p260x8 = p260x7) → ∀ lps260 : Fin N260 → Fin N260 → Prop, lps260 = (fun p260x9 w260x11 : Fin N260 => ∃ h260x6 : ℕ, lpw260 h260x6 w260x11 ∧ ap260 h260x6 p260x9) → ∀ pps260 : Fin N260 → Fin N260 → Prop, pps260 = (fun p260x10 w260x12 : Fin N260 => ∃ h260x7 : ℕ, ppw260 h260x7 p260x10 ∧ lh260 h260x7 w260x12) → ∑ w260x13 : Fin N260, Set.ncard {p260x11 : Fin N260 | lps260 p260x11 w260x13} + ∑ p260x12 : Fin N260, min (k260 + 1) (Set.ncard {w260x14 : Fin N260 | pps260 p260x12 w260x14}) + t260 ≤ C260.size + 1 := by
  intro H1 H2 H3 H4 N k t I instI C hno hedge hk hAO hKM htrue hfalse hcov mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw lps hlps pps hpps
  obtain ⟨-, h1b, -⟩ := H1 N C hAO hKM
    (hfalse (fun _ => true) (fun _ => false) (by simp) (by simp)) mixed hmixed cone hcone
  obtain ⟨-, -, -, -, -, hsplit⟩ := H2 N I C hAO hKM hno hedge htrue
    (fun x y hy hn => hfalse x y (le_trans hy hk) hn) mixed hmixed cone hcone gok hgok step hstep
    lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw lps hlps pps hpps
  obtain ⟨TL, TP, KB, KP, own, hK, hdisj, hKB, hKP, hTP, hcovL, h3⟩ := H3 N I C hAO hKM hno hedge
    htrue (fun x y hy hn => hfalse x y (le_trans hy hk) hn) mixed hmixed cone hcone gok hgok
    step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw lps hlps
  obtain ⟨hown, h4a, h4b⟩ := H4 N k I C hAO hKM hno hedge hk htrue hfalse mixed hmixed cone hcone
    gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw pps hpps
  exact PEqualNP.Outside.L_meta_1954.core C I t cone lvx ppw lps pps hAO
    (by
      intro j hj
      obtain ⟨a, b, -⟩ := (congrFun hcone j).mp hj
      obtain ⟨c, d⟩ := (congrFun hmixed (N + N + j)).mp b
      exact ⟨a, c, d⟩)
    (by
      intro p w h
      obtain ⟨hh, hp, -⟩ := (congrFun (congrFun hpps p) w).mp h
      exact ⟨hh, hp⟩)
    hcov hsplit TL TP KB KP own hK hdisj hKB hKP hTP hcovL hown h1b h3 h4a h4b
