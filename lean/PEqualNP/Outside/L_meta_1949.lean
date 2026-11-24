import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1949

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

def T (N : ℕ) (C : Circuit) (w : ℕ) : Bool :=
  W N C (fun _ => true) (fun _ => false) w

def PR (N : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun a b => a < b ∧ ∃ f : Fin C.gates.length, b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs

def Cn (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)) ∧
    Relation.ReflTransGen (PR N C) (N + N + j) C.output

theorem T_gate (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (j : ℕ)
    (hj : j < C.gates.length) :
    T N C (N + N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (T N C)) :=
  V_gate (N + N) C hrb _ (by simp) j hj

theorem T_in (N : ℕ) (C : Circuit) (w : ℕ) (hw : w < N) : T N C w = true := by
  have h := V_in C (List.ofFn (Fin.append (fun _ : Fin N => true) (fun _ : Fin N => false))) w
    (by rw [List.length_ofFn]; omega)
  have h' : T N C w
      = (List.ofFn (Fin.append (fun _ : Fin N => true) (fun _ : Fin N => false))).getD w false := h
  rw [h', app_getD, difp hw]

theorem two (C : Circuit)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) : ∃ u v, (gateAt C j).inputs = [u, v] :=
  List.length_eq_two.mp (h2 _ (gateAt_mem C j hj)).2

theorem get_eq (C : Circuit) (f : Fin C.gates.length) : C.gates.get f = gateAt C f.val :=
  (List.getD_eq_getElem _ _ f.isLt).symm

theorem lf_true (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ w, w < N + N + C.gates.length → DL N C w = 0 → T N C w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hd
    by_cases h1 : w < N + N
    · have hb : D (N + N) (Finset.Ico N (N + N)) C w = 0 := hd
      rw [D_in _ _ _ _ h1] at hb
      by_cases h3 : w < N
      · exact T_in N C w h3
      · rw [ifp (Finset.mem_Ico.mpr ⟨by omega, h1⟩)] at hb
        omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := h2 _ (gateAt_mem C j hj)
      have hz := (D_zero_iff (N + N) (Finset.Ico N (N + N)) C hrb j hj).mp hd
      have hall : ∀ i ∈ (gateAt C j).inputs, T N C i = true := by
        intro i hi
        have hlt := hrb j hj i hi
        exact ih i (by omega) (by omega) (hz i hi)
      rw [T_gate N C hrb j hj]
      rcases hg.1 with hop | hop
      · rw [ev_and _ _ hop]
        exact hall
      · rw [ev_or _ _ hop]
        obtain ⟨u, v, huv⟩ := two C h2 j hj
        have hu : u ∈ (gateAt C j).inputs := by rw [huv]; simp
        exact ⟨u, hu, hall u hu⟩

theorem deg_up (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (j : ℕ)
    (hj : j < C.gates.length) (a : ℕ) (ha : a ∈ (gateAt C j).inputs) (h : 0 < D K M C a) :
    0 < D K M C (K + j) := by
  by_contra hc
  have := (D_zero_iff K M C hrb j hj).mp (by omega) a ha
  omega

theorem step (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (a j : ℕ) (hj : j < C.gates.length) (ha : a ∈ (gateAt C j).inputs)
    (hm : 0 < DP N C a ∧ 0 < DL N C a) :
    (0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)) ∧
      (T N C a = true → T N C (N + N + j) = true) := by
  refine ⟨⟨deg_up (N + N) (Finset.range N) C hrb j hj a ha hm.1,
     deg_up (N + N) (Finset.Ico N (N + N)) C hrb j hj a ha hm.2⟩, ?_⟩
  intro hT
  rw [T_gate N C hrb j hj]
  rcases (h2 _ (gateAt_mem C j hj)).1 with hop | hop
  · rw [ev_and _ _ hop]
    rcases hkm j hj hop with ⟨i, hi, hdi⟩ | hall
    · have hlt := hrb j hj i hi
      have hTi := lf_true N C hrb h2 i (by omega) hdi
      obtain ⟨u, v, huv⟩ := two C h2 j hj
      have hne : i ≠ a := by
        intro e
        rw [e] at hdi
        have := hm.2
        omega
      rw [huv] at ha hi ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hi
      have hb : T N C u = true ∧ T N C v = true := by
        rcases ha with e1 | e1 <;> rcases hi with e2 | e2
        · exact absurd (e2.trans e1.symm) hne
        · rw [e1] at hT
          rw [e2] at hTi
          exact ⟨hT, hTi⟩
        · rw [e1] at hT
          rw [e2] at hTi
          exact ⟨hTi, hT⟩
        · exact absurd (e2.trans e1.symm) hne
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with e | e
      · rw [e]
        exact hb.1
      · rw [e]
        exact hb.2
    · have h3 := hall a ha
      have h4 := hm.1
      omega
  · rw [ev_or _ _ hop]
    exact ⟨a, ha, hT⟩

theorem up (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0)) :
    ∀ a, Relation.ReflTransGen (PR N C) a C.output → (0 < DP N C a ∧ 0 < DL N C a) →
      T N C a = true → T N C C.output = true := by
  intro a h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ h
    exact h
  | head hab _ ih =>
    intro hm hT
    obtain ⟨_, f, rfl, hin⟩ := hab
    rw [get_eq] at hin
    have hs := step N C hrb h2 hkm _ f.val f.isLt hin hm
    exact ih hs.1 (hs.2 hT)

theorem facts (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (hout : T N C C.output = false) (j : ℕ) (hc : Cn N C j) :
    ((gateAt C j).op = GateOp.or → ∀ i ∈ (gateAt C j).inputs, 0 < DL N C i) ∧
    ((gateAt C j).op = GateOp.and → ∃ a b,
      ((gateAt C j).inputs = [a, b] ∨ (gateAt C j).inputs = [b, a]) ∧
      DL N C a = 0 ∧ 0 < DP N C a ∧ 0 < DL N C b) := by
  have hj := hc.1
  have hf : T N C (N + N + j) = false := by
    by_contra h
    have h5 := up N C hrb h2 hkm _ hc.2.2 hc.2.1 (bt _ h)
    exact absurd (h5.symm.trans hout) (by decide)
  rw [T_gate N C hrb j hj] at hf
  constructor
  · intro hop i hi
    by_contra hd
    have hlt := hrb j hj i hi
    have hTi := lf_true N C hrb h2 i (by omega) (by omega)
    have h5 : (gateAt C j).op.eval ((gateAt C j).inputs.map (T N C)) = true :=
      (ev_or _ _ hop).mpr ⟨i, hi, hTi⟩
    exact absurd (h5.symm.trans hf) (by decide)
  · intro hop
    rcases hkm j hj hop with ⟨i, hi, hdi⟩ | hall
    · have hlt := hrb j hj i hi
      have hTi := lf_true N C hrb h2 i (by omega) hdi
      have hpi : 0 < DP N C i := by
        by_contra hz
        exact pos N C hrb h2 i (by omega) ⟨by omega, hdi⟩
      obtain ⟨u, v, huv⟩ := two C h2 j hj
      have hnot : ¬ (T N C u = true ∧ T N C v = true) := by
        intro hb
        have h5 : (gateAt C j).op.eval ((gateAt C j).inputs.map (T N C)) = true := by
          rw [ev_and _ _ hop, huv]
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with e | e
          · rw [e]
            exact hb.1
          · rw [e]
            exact hb.2
        exact absurd (h5.symm.trans hf) (by decide)
      have hlu := hrb j hj u (by rw [huv]; simp)
      have hlv := hrb j hj v (by rw [huv]; simp)
      rw [huv] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with e | e
      · rw [e] at hdi hpi hTi
        refine ⟨u, v, Or.inl huv, hdi, hpi, ?_⟩
        by_contra hz
        exact hnot ⟨hTi, lf_true N C hrb h2 v (by omega) (by omega)⟩
      · rw [e] at hdi hpi hTi
        refine ⟨v, u, Or.inr huv, hdi, hpi, ?_⟩
        by_contra hz
        exact hnot ⟨lf_true N C hrb h2 u (by omega) (by omega), hTi⟩
    · exfalso
      have h3 := (D_zero_iff (N + N) (Finset.range N) C hrb j hj).mpr hall
      have h4 := hc.2.1.1
      have h6 : DP N C (N + N + j) = 0 := h3
      omega

theorem cnt0 (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (hP : ∀ j, P j → j < n) :
    Set.ncard {j : ℕ | P j} = ∑ j ∈ (Finset.range n).filter P, 1 := by
  have e : {j : ℕ | P j} = ↑((Finset.range n).filter P) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h1
      exact ⟨hP j h1, h1⟩
    · rintro ⟨_, h1⟩
      exact h1
  rw [e, Set.ncard_coe_finset, Finset.card_eq_sum_ones]

theorem cnt1 (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (hP : ∀ j, P j → j < n)
    (Q : ℕ → Prop) [DecidablePred Q] :
    Set.ncard {j : ℕ | P j ∧ Q j}
      = ∑ j ∈ (Finset.range n).filter P, (if Q j then 1 else 0) := by
  have e : {j : ℕ | P j ∧ Q j} = ↑(((Finset.range n).filter P).filter Q) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h3⟩
      exact ⟨⟨hP j h1, h1⟩, h3⟩
    · rintro ⟨⟨_, h1⟩, h3⟩
      exact ⟨h1, h3⟩
  rw [e, Set.ncard_coe_finset, Finset.card_filter]

theorem cnt2 (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (hP : ∀ j, P j → j < n)
    (Q : ℕ → ℕ → Prop) [∀ j s, Decidable (Q j s)] :
    Set.ncard {js : ℕ × ℕ | P js.1 ∧ js.2 < 2 ∧ Q js.1 js.2}
      = ∑ j ∈ (Finset.range n).filter P,
          ((if Q j 0 then 1 else 0) + (if Q j 1 then 1 else 0)) := by
  have e : {js : ℕ × ℕ | P js.1 ∧ js.2 < 2 ∧ Q js.1 js.2}
      = ↑((((Finset.range n).filter P) ×ˢ (Finset.range 2)).filter
          (fun js : ℕ × ℕ => Q js.1 js.2)) := by
    ext ⟨j, s⟩
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    constructor
    · rintro ⟨h1, h3, h4⟩
      exact ⟨⟨⟨hP j h1, h1⟩, h3⟩, h4⟩
    · rintro ⟨⟨⟨_, h1⟩, h3⟩, h4⟩
      exact ⟨h1, h3, h4⟩
  rw [e, Set.ncard_coe_finset, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.sum_range_succ (fun s => if Q j s then 1 else 0) 1).trans
    (by rw [Finset.sum_range_one])

theorem inj_cnt (K : ℕ) (S : Set ℕ) (B : Set (ℕ × ℕ)) (g : ℕ × ℕ → ℕ) (o : ℕ) (hB : B.Finite)
    (h : ∀ j ∈ S, K + j ≠ o → ∃ p ∈ B, g p = K + j) : S.ncard ≤ B.ncard + 1 := by
  have hfin : (insert o (g '' B)).Finite := (hB.image g).insert o
  have hsub : (fun j => K + j) '' S ⊆ insert o (g '' B) := by
    rintro _ ⟨j, hj, rfl⟩
    by_cases e : K + j = o
    · exact Set.mem_insert_iff.mpr (Or.inl e)
    · obtain ⟨p, hp, hg⟩ := h j hj e
      exact Set.mem_insert_iff.mpr (Or.inr ⟨p, hp, hg⟩)
  calc S.ncard = ((fun j => K + j) '' S).ncard :=
        (Set.ncard_image_of_injective S (fun a b hab => Nat.add_left_cancel hab)).symm
    _ ≤ (insert o (g '' B)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (g '' B).ncard + 1 := Set.ncard_insert_le o _
    _ ≤ B.ncard + 1 := Nat.add_le_add_right (Set.ncard_image_le hB) 1

theorem core (N : ℕ) (C : Circuit)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (hout : T N C C.output = false) :
    (∀ j : ℕ, Cn N C j → (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, 0 < DL N C i) ∧
    Set.ncard {j : ℕ | Cn N C j ∧ (gateAt C j).op = GateOp.or} + Set.ncard {j : ℕ | Cn N C j}
      = Set.ncard {js : ℕ × ℕ | Cn N C js.1 ∧ js.2 < 2 ∧
          DP N C ((gateAt C js.1).inputs.getD js.2 0) = 0}
        + Set.ncard {js : ℕ × ℕ | Cn N C js.1 ∧ js.2 < 2 ∧
          (0 < DP N C ((gateAt C js.1).inputs.getD js.2 0) ∧
            0 < DL N C ((gateAt C js.1).inputs.getD js.2 0))} ∧
    Set.ncard {j : ℕ | Cn N C j} ≤ Set.ncard {js : ℕ × ℕ | Cn N C js.1 ∧ js.2 < 2 ∧
          (0 < DP N C ((gateAt C js.1).inputs.getD js.2 0) ∧
            0 < DL N C ((gateAt C js.1).inputs.getD js.2 0))} + 1 := by
  refine ⟨fun j hc => (facts N C hrb h2 hkm hout j hc).1, ?_, ?_⟩
  · classical
    have e1 : Set.ncard {j : ℕ | Cn N C j ∧ (gateAt C j).op = GateOp.or}
        = ∑ j ∈ (Finset.range C.gates.length).filter (Cn N C),
            (if (gateAt C j).op = GateOp.or then 1 else 0) :=
      cnt1 C.gates.length (Cn N C) (fun j h => h.1) (fun j => (gateAt C j).op = GateOp.or)
    have e2 : Set.ncard {j : ℕ | Cn N C j}
        = ∑ j ∈ (Finset.range C.gates.length).filter (Cn N C), 1 :=
      cnt0 C.gates.length (Cn N C) (fun j h => h.1)
    have e3 : Set.ncard {js : ℕ × ℕ | Cn N C js.1 ∧ js.2 < 2 ∧
          DP N C ((gateAt C js.1).inputs.getD js.2 0) = 0}
        = ∑ j ∈ (Finset.range C.gates.length).filter (Cn N C),
            ((if DP N C ((gateAt C j).inputs.getD 0 0) = 0 then 1 else 0)
              + (if DP N C ((gateAt C j).inputs.getD 1 0) = 0 then 1 else 0)) :=
      cnt2 C.gates.length (Cn N C) (fun j h => h.1)
        (fun j s => DP N C ((gateAt C j).inputs.getD s 0) = 0)
    have e4 : Set.ncard {js : ℕ × ℕ | Cn N C js.1 ∧ js.2 < 2 ∧
          (0 < DP N C ((gateAt C js.1).inputs.getD js.2 0) ∧
            0 < DL N C ((gateAt C js.1).inputs.getD js.2 0))}
        = ∑ j ∈ (Finset.range C.gates.length).filter (Cn N C),
            ((if (0 < DP N C ((gateAt C j).inputs.getD 0 0) ∧
                0 < DL N C ((gateAt C j).inputs.getD 0 0)) then 1 else 0)
              + (if (0 < DP N C ((gateAt C j).inputs.getD 1 0) ∧
                0 < DL N C ((gateAt C j).inputs.getD 1 0)) then 1 else 0)) :=
      cnt2 C.gates.length (Cn N C) (fun j h => h.1)
        (fun j s => 0 < DP N C ((gateAt C j).inputs.getD s 0) ∧
          0 < DL N C ((gateAt C j).inputs.getD s 0))
    rw [e1, e2, e3, e4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hc : Cn N C j := (Finset.mem_filter.mp hj).2
    obtain ⟨hor, hand⟩ := facts N C hrb h2 hkm hout j hc
    rcases (h2 _ (gateAt_mem C j hc.1)).1 with hop | hop
    · obtain ⟨a, b, hab, h1, h3, h4⟩ := hand hop
      have hno : ¬ (gateAt C j).op = GateOp.or := by
        rw [hop]
        intro h
        cases h
      rw [ifn hno]
      rcases hab with e | e
      · rw [e, show [a, b].getD 0 0 = a from rfl, show [a, b].getD 1 0 = b from rfl]
        split_ifs <;> omega
      · rw [e, show [b, a].getD 0 0 = b from rfl, show [b, a].getD 1 0 = a from rfl]
        split_ifs <;> omega
    · rw [ifp hop]
      obtain ⟨u, v, huv⟩ := two C h2 j hc.1
      have hu := hor hop u (by rw [huv]; simp)
      have hv := hor hop v (by rw [huv]; simp)
      rw [huv, show [u, v].getD 0 0 = u from rfl, show [u, v].getD 1 0 = v from rfl]
      split_ifs <;> omega
  · refine inj_cnt (N + N) _ _ (fun p => (gateAt C p.1).inputs.getD p.2 0) C.output ?_ ?_
    · apply Set.Finite.subset
        (Finset.finite_toSet ((Finset.range C.gates.length) ×ˢ (Finset.range 2)))
      rintro ⟨j, s⟩ ⟨h1, h3, _⟩
      exact Finset.mem_coe.mpr
        (Finset.mem_product.mpr ⟨Finset.mem_range.mpr h1.1, Finset.mem_range.mpr h3⟩)
    · intro j hcj hne
      have hc : Cn N C j := hcj
      rcases Relation.ReflTransGen.cases_head hc.2.2 with e | ⟨c, hjc, hco⟩
      · exact absurd e hne
      · obtain ⟨_, f, rfl, hin⟩ := hjc
        rw [get_eq] at hin
        have hs := step N C hrb h2 hkm _ f.val f.isLt hin hc.2.1
        have hcf : Cn N C f.val := And.intro f.isLt (And.intro hs.1 hco)
        obtain ⟨u, v, huv⟩ := two C h2 f.val f.isLt
        have hmj := hc.2.1
        rw [huv] at hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with e | e
        · rw [e] at hmj
          refine ⟨(f.val, 0), ?_, ?_⟩
          · show Cn N C f.val ∧ 0 < 2 ∧
              (0 < DP N C ((gateAt C f.val).inputs.getD 0 0) ∧
                0 < DL N C ((gateAt C f.val).inputs.getD 0 0))
            rw [huv]
            exact And.intro hcf (And.intro (by norm_num) hmj)
          · show (gateAt C f.val).inputs.getD 0 0 = N + N + j
            rw [huv]
            exact e.symm
        · rw [e] at hmj
          refine ⟨(f.val, 1), ?_, ?_⟩
          · show Cn N C f.val ∧ 1 < 2 ∧
              (0 < DP N C ((gateAt C f.val).inputs.getD 1 0) ∧
                0 < DL N C ((gateAt C f.val).inputs.getD 1 0))
            rw [huv]
            exact And.intro hcf (And.intro (by norm_num) hmj)
          · show (gateAt C f.val).inputs.getD 1 0 = N + N + j
            rw [huv]
            exact e.symm

end PEqualNP.Outside.L_meta_1949

theorem PEqualNP.Outside.L_meta_1949 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → ∀ (N230 : ℕ) (C230 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g230 ∈ C230.gates, (g230.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g230.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g230.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N230 + N230) C230) → (∀ j230x2 < C230.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i230x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x2 0 = 0) ∨ (∀ h230 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD h230 0 = 0)) → PEqualNP.MetaComplexity.circuitFun (N230 + N230) C230 (Fin.append (fun u230 : Fin N230 => true) (fun u230x1 : Fin N230 => false)) = false → ∀ mixed230 : ℕ → Prop, mixed230 = (fun i230 : ℕ => 0 < (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD i230 0 ∧ 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230 0) → ∀ cone230 : ℕ → Prop, cone230 = (fun j230 : ℕ => j230 < C230.gates.length ∧ mixed230 (N230 + N230 + j230) ∧ Relation.ReflTransGen (fun a230 b230 : ℕ => a230 < b230 ∧ ∃ f230 : Fin C230.gates.length, b230 = N230 + N230 + f230.val ∧ a230 ∈ (C230.gates.get f230).inputs) (N230 + N230 + j230) C230.output) → (∀ j230x1 : ℕ, cone230 j230x1 → (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i230x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).inputs, 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x1 0) ∧ Set.ncard {j230x3 : ℕ | cone230 j230x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x3).op = PEqualNP.CircuitLowerBounds.GateOp.or} + Set.ncard {j230x4 : ℕ | cone230 j230x4} = Set.ncard {js230 : ℕ × ℕ | cone230 js230.1 ∧ js230.2 < 2 ∧ (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230.1).inputs.getD js230.2 0) 0 = 0} + Set.ncard {js230x1 : ℕ × ℕ | cone230 js230x1.1 ∧ js230x1.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x1.1).inputs.getD js230x1.2 0)} ∧ Set.ncard {j230x5 : ℕ | cone230 j230x5} ≤ Set.ncard {js230x2 : ℕ × ℕ | cone230 js230x2.1 ∧ js230x2.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x2.1).inputs.getD js230x2.2 0)} + 1 := by
  intro _ N C h hkm hout mixed hmixed cone hcone
  subst hmixed
  subst hcone
  exact PEqualNP.Outside.L_meta_1949.core N C h.1 h.2 hkm hout
