import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1622

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

def E (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

def dg (n m : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl

theorem E_in (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ)
    (hw : w < n + m) : E n m C x y w = (List.ofFn (Fin.append x y)).getD w false := by
  unfold E
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    fd_pre _ _ _ _ (by simpa using hw)]

theorem E_out (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ)
    (hw : n + m + C.gates.length ≤ w) : E n m C x y w = false := by
  unfold E
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    rw [fd_len]; simpa using hw)]
  rfl

theorem E_gate (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C) (x : Fin n → Bool)
    (y : Fin m → Bool) (j : ℕ) (hj : j < C.gates.length) :
    E n m C x y (n + m + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (E n m C x y)) := by
  have h := fd_gate stpF false stpF_congr C.gates (List.ofFn (Fin.append x y)) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_ofFn] at h
  exact h

theorem dg_in (n m : ℕ) (C : Circuit) (w : ℕ) (hw : w < n + m) :
    dg n m C w = if n ≤ w then 1 else 0 := by
  unfold dg Circuit.lineDegrees
  have := fd_pre Gate.lineDegree C.gates
    ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0) w
    (by simpa using hw)
  unfold fd at this
  rw [List.getD_eq_getElem?_getD, this]
  simp [hw]

theorem dg_out (n m : ℕ) (C : Circuit) (w : ℕ) (hw : n + m + C.gates.length ≤ w) :
    dg n m C w = 0 := by
  unfold dg
  have hl : (C.lineDegrees (n + m) (Finset.Ico n (n + m))).length = n + m + C.gates.length := by
    have := fd_len Gate.lineDegree C.gates
      ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0)
    simpa [fd, Circuit.lineDegrees] using this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem foldr_max_zero : ∀ (l : List ℕ), l.foldr max 0 = 0 → ∀ a ∈ l, a = 0 := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons b l ih =>
    intro h a ha
    simp only [List.foldr_cons] at h
    have h1 : b = 0 := by omega
    have h2 : l.foldr max 0 = 0 := by omega
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h1
    · exact ih h2 a ha

theorem dg_gate0 (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C) (j : ℕ)
    (hj : j < C.gates.length) (h0 : dg n m C (n + m + j) = 0) :
    ∀ i ∈ (gateAt C j).inputs, dg n m C i = 0 := by
  have h := fd_gate Gate.lineDegree 0 ld_congr C.gates
    ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_map, List.length_range] at h
  have h' : dg n m C (n + m + j) =
      (gateAt C j).lineDegree (C.lineDegrees (n + m) (Finset.Ico n (n + m))) := h
  rw [h0] at h'
  intro i hi
  unfold Gate.lineDegree at h'
  split_ifs at h'
  · have := List.sum_eq_zero_iff.mp h'.symm
    exact this _ (List.mem_map_of_mem hi)
  · exact foldr_max_zero _ h'.symm _ (List.mem_map_of_mem (f := fun i =>
      (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0) hi)

theorem E_indep (n m : ℕ) (C : Circuit) (hrb : ReadsBack (n + m) C) (x : Fin n → Bool) :
    ∀ (w : ℕ), dg n m C w = 0 → ∀ y y' : Fin m → Bool, E n m C x y w = E n m C x y' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd y y'
    by_cases h1 : w < n + m
    · rw [dg_in n m C w h1] at hd
      have hwn : w < n := by
        by_contra hc
        rw [ifp (by omega)] at hd
        omega
      rw [E_in _ _ _ _ _ _ h1, E_in _ _ _ _ _ _ h1, app_getD, app_getD, difp hwn, difp hwn]
    · by_cases h2 : w < n + m + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
        have hj : j < C.gates.length := by omega
        rw [E_gate n m C hrb x y j hj, E_gate n m C hrb x y' j hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        have := hrb j hj i hi
        exact ih i (by omega) (dg_gate0 n m C hrb j hj hd i hi) y y'
      · rw [E_out _ _ _ _ _ _ (by omega), E_out _ _ _ _ _ _ (by omega)]

theorem E_mono (n m : ℕ) (C : Circuit) (hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ)
    (h : E n m C x (fun _ => false) w = true) : E n m C x y w = true := by
  unfold E at h ⊢
  rw [wires_fd] at h ⊢
  refine mono C.gates _ _ (by simp) hm ?_ w h
  intro i
  rw [app_getD, app_getD]
  split_ifs <;> simp

abbrev St := List Gate × (ℕ → ℕ)

def el (b0 : ℕ) (s : St) (op : GateOp) (a b u : ℕ) : St :=
  (s.1 ++ [⟨op, [a, b]⟩], Function.update s.2 u (b0 + s.1.length))

def cedge (deg : ℕ → ℕ) (b0 : ℕ) (s : St) (u wg : ℕ) : St :=
  if 0 < deg u then el b0 s GateOp.or (s.2 u) (s.2 wg) u else s

def scale (b0 : ℕ) (s : St) (wg a : ℕ) : St := el b0 s GateOp.and (s.2 wg) a wg

open Classical in
noncomputable def gstep (deg : ℕ → ℕ) (b0 : ℕ) (wg : ℕ) (op : GateOp) : List ℕ → St → St
  | [u], s => cedge deg b0 s u wg
  | [u, v], s =>
    if op = GateOp.and then
      (if deg u = 0 then cedge deg b0 (scale b0 s wg u) v wg
        else cedge deg b0 (scale b0 s wg v) u wg)
    else cedge deg b0 (cedge deg b0 s u wg) v wg
  | _, s => s

noncomputable def step (deg : ℕ → ℕ) (b0 N : ℕ) (G : ℕ → Gate) (j : ℕ) (s : St) : St :=
  if 0 < deg (N + j) then gstep deg b0 (N + j) (G j).op (G j).inputs s else s

noncomputable def rev (deg : ℕ → ℕ) (b0 N : ℕ) (G : ℕ → Gate) : ℕ → St → St
  | 0, s => s
  | k + 1, s => rev deg b0 N G k (step deg b0 N G k s)

def WF (b0 : ℕ) (s : St) : Prop :=
  (∀ w, s.2 w < b0 + s.1.length) ∧
  (∀ t g, s.1[t]? = some g → ∀ i ∈ g.inputs, i < b0 + t) ∧
  (∀ g ∈ s.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)

def V (B : List Bool) (s : St) (i : ℕ) : Bool := (fd stpF B s.1).getD i false

def rr (B : List Bool) (s : St) (w : ℕ) : Bool := V B s (s.2 w)

theorem V_base (B : List Bool) (s : St) (i : ℕ) (hi : i < B.length) :
    V B s i = B.getD i false := by
  unfold V
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, fd_pre _ _ _ _ hi]

theorem el_fst (b0 : ℕ) (s : St) (op : GateOp) (a b u : ℕ) :
    (el b0 s op a b u).1 = s.1 ++ [⟨op, [a, b]⟩] := rfl

theorem el_snd (b0 : ℕ) (s : St) (op : GateOp) (a b u : ℕ) :
    (el b0 s op a b u).2 = Function.update s.2 u (b0 + s.1.length) := rfl

theorem el_spec (b0 : ℕ) (B : List Bool) (hB : B.length = b0) (s : St) (op : GateOp)
    (a b u : ℕ) (hw : WF b0 s) (ha : a < b0 + s.1.length) (hb : b < b0 + s.1.length)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    WF b0 (el b0 s op a b u) ∧
    (∀ w, rr B (el b0 s op a b u) w =
      if w = u then op.eval [V B s a, V B s b] else rr B s w) := by
  have hlen : (fd stpF B s.1).length = b0 + s.1.length := by rw [fd_len, hB]
  have hV : ∀ i, V B (el b0 s op a b u) i =
      if i = b0 + s.1.length then op.eval [V B s a, V B s b] else V B s i := by
    intro i
    unfold V
    rw [el_fst, fd_app]
    show ((fd stpF B s.1) ++ [stpF ⟨op, [a, b]⟩ (fd stpF B s.1)]).getD i false = _
    rw [getD_snoc, hlen]
    rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro w
    rw [el_fst, el_snd]
    simp only [Function.update_apply, List.length_append, List.length_singleton]
    have := hw.1 w
    split_ifs <;> omega
  · intro t g hg i hi
    rw [el_fst, List.getElem?_append] at hg
    split_ifs at hg with h
    · exact hw.2.1 t g hg i hi
    · have h0 : t - s.1.length = 0 := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hg
        cases hg
      rw [h0] at hg
      simp at hg
      subst hg
      simp at hi
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    rw [el_fst] at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hw.2.2 g hg
    · exact ⟨hop, by simp⟩
  · intro w
    unfold rr
    rw [hV, el_snd]
    simp only [Function.update_apply]
    by_cases hwu : w = u
    · simp [hwu]
    · have := hw.1 w
      simp [hwu, Nat.ne_of_lt this]

theorem cedge_spec (deg : ℕ → ℕ) (b0 : ℕ) (B : List Bool) (hB : B.length = b0) (s : St)
    (u wg : ℕ) (hw : WF b0 s) :
    WF b0 (cedge deg b0 s u wg) ∧
    (∀ w, rr B (cedge deg b0 s u wg) w =
      if 0 < deg u ∧ w = u then (rr B s u || rr B s wg) else rr B s w) := by
  unfold cedge
  split_ifs with h
  · obtain ⟨h1, h2⟩ := el_spec b0 B hB s GateOp.or (s.2 u) (s.2 wg) u hw (hw.1 u) (hw.1 wg)
      (Or.inr rfl)
    refine ⟨h1, fun w => ?_⟩
    rw [h2]
    by_cases hwu : w = u
    · simp [hwu, h, GateOp.eval, rr]
    · simp [hwu]
  · exact ⟨hw, fun w => by simp [h]⟩

theorem scale_spec (b0 : ℕ) (B : List Bool) (hB : B.length = b0) (s : St)
    (wg a : ℕ) (hw : WF b0 s) (ha : a < b0) :
    WF b0 (scale b0 s wg a) ∧
    (∀ w, rr B (scale b0 s wg a) w =
      if w = wg then (rr B s wg && B.getD a false) else rr B s w) := by
  unfold scale
  obtain ⟨h1, h2⟩ := el_spec b0 B hB s GateOp.and (s.2 wg) a wg hw (hw.1 wg) (by omega)
    (Or.inl rfl)
  refine ⟨h1, fun w => ?_⟩
  rw [h2, V_base B s a (by omega)]
  by_cases hwu : w = wg
  · simp [hwu, GateOp.eval, rr]
  · simp [hwu]

def Phi {Y : Type} (e : Y → ℕ → Bool) (y0 : Y) (deg : ℕ → ℕ) (out : ℕ) (bd : ℕ)
    (r : ℕ → Bool) : Prop :=
  ∀ y, (e y out = true ↔
    (e y0 out = true ∨ ∃ w, w < bd ∧ 0 < deg w ∧ r w = true ∧ e y w = true))

theorem phi_edge {Y : Type} (e : Y → ℕ → Bool) (y0 : Y) (deg : ℕ → ℕ) (out bd : ℕ)
    (r : ℕ → Bool) (u wg : ℕ) (c : Prop) [Decidable c]
    (h : Phi e y0 deg out bd r) (hwg : wg < bd) (hd : 0 < deg wg)
    (himp : ∀ y, r wg = true → e y u = true → e y wg = true)
    (r' : ℕ → Bool) (hr' : ∀ w, r' w = if c ∧ w = u then (r u || r wg) else r w) :
    Phi e y0 deg out bd r' := by
  intro y
  rw [h y]
  constructor
  · rintro (h0 | ⟨w, hw1, hw2, hw3, hw4⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨w, hw1, hw2, ?_, hw4⟩
      rw [hr']
      split_ifs with hc
      · obtain ⟨_, rfl⟩ := hc
        simp [hw3]
      · exact hw3
  · rintro (h0 | ⟨w, hw1, hw2, hw3, hw4⟩)
    · exact Or.inl h0
    · rw [hr'] at hw3
      split_ifs at hw3 with hc
      · obtain ⟨_, rfl⟩ := hc
        rcases (Bool.or_eq_true _ _).mp hw3 with h3 | h3
        · exact Or.inr ⟨w, hw1, hw2, h3, hw4⟩
        · exact Or.inr ⟨wg, hwg, hd, h3, himp y h3 hw4⟩
      · exact Or.inr ⟨w, hw1, hw2, hw3, hw4⟩

theorem phi_scale {Y : Type} (e : Y → ℕ → Bool) (y0 : Y) (deg : ℕ → ℕ) (out bd : ℕ)
    (r : ℕ → Bool) (wg : ℕ) (c : Bool)
    (h : Phi e y0 deg out bd r)
    (hc : ∀ y, e y wg = true → c = true)
    (r' : ℕ → Bool) (hr' : ∀ w, r' w = if w = wg then (r wg && c) else r w) :
    Phi e y0 deg out bd r' := by
  intro y
  rw [h y]
  constructor
  · rintro (h0 | ⟨w, hw1, hw2, hw3, hw4⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨w, hw1, hw2, ?_, hw4⟩
      rw [hr']
      split_ifs with hwe
      · subst hwe
        simp [hw3, hc y hw4]
      · exact hw3
  · rintro (h0 | ⟨w, hw1, hw2, hw3, hw4⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨w, hw1, hw2, ?_, hw4⟩
      rw [hr'] at hw3
      split_ifs at hw3 with hwe
      · subst hwe
        simp at hw3
        exact hw3.1
      · exact hw3

theorem phi_drop {Y : Type} (e : Y → ℕ → Bool) (y0 : Y) (deg : ℕ → ℕ) (out bd : ℕ)
    (r : ℕ → Bool)
    (h : Phi e y0 deg out (bd + 1) r)
    (hd : ∀ y, 0 < deg bd → r bd = true → e y bd = true →
      (e y0 out = true ∨ ∃ w, w < bd ∧ 0 < deg w ∧ r w = true ∧ e y w = true)) :
    Phi e y0 deg out bd r := by
  intro y
  rw [h y]
  constructor
  · rintro (h0 | ⟨w, hw1, hw2, hw3, hw4⟩)
    · exact Or.inl h0
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hw1 with hlt | rfl
      · exact Or.inr ⟨w, hlt, hw2, hw3, hw4⟩
      · exact hd y hw2 hw3 hw4
  · rintro (h0 | ⟨w, hw1, hw2, hw3, hw4⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨w, Nat.lt_succ_of_lt hw1, hw2, hw3, hw4⟩

theorem phi_zero {Y : Type} (e : Y → ℕ → Bool) (y0 : Y) (deg : ℕ → ℕ) (out bd : ℕ)
    (r : ℕ → Bool) (h : Phi e y0 deg out bd r) (w : ℕ) (hw : w < bd) (hd : 0 < deg w)
    (hr : r w = true) (he : e y0 w = true) : e y0 out = true :=
  (h y0).mpr (Or.inr ⟨w, hw, hd, hr, he⟩)

theorem and2_inv {Y : Type} (e : Y → ℕ → Bool) (y0 : Y) (deg : ℕ → ℕ) (out N b0 : ℕ)
    (B : List Bool) (hB : B.length = b0) (j : ℕ) (hNj : N + j < b0)
    (hbase : ∀ i, i < N + j → B.getD i false = e y0 i)
    (hA : ∀ w, deg w = 0 → ∀ y, e y w = e y0 w)
    (hdeg : 0 < deg (N + j))
    (a b : ℕ) (ha : a < N + j) (hb : b < N + j) (hda : deg a = 0)
    (heva : ∀ y, e y (N + j) = (e y a && e y b))
    (s : St) (hw : WF b0 s) (hphi : Phi e y0 deg out (N + j + 1) (rr B s)) :
    WF b0 (cedge deg b0 (scale b0 s (N + j) a) b (N + j)) ∧
    Phi e y0 deg out (N + j) (rr B (cedge deg b0 (scale b0 s (N + j) a) b (N + j))) := by
  have hza : B.getD a false = e y0 a := hbase a ha
  obtain ⟨w1, r1⟩ := scale_spec b0 B hB s (N + j) a hw (by omega)
  obtain ⟨w2, r2⟩ := cedge_spec deg b0 B hB (scale b0 s (N + j) a) b (N + j) w1
  have p1 := phi_scale e y0 deg out (N + j + 1) (rr B s) (N + j) (B.getD a false) hphi
    (fun y h => by
      rw [heva] at h
      rw [hza, ← hA a hda y]
      simp at h
      exact h.1) _ r1
  have p2 := phi_edge e y0 deg out (N + j + 1) _ b (N + j) (0 < deg b) p1 (by omega) hdeg
    (fun y h1 h2 => by
      rw [r1, ifp rfl, Bool.and_eq_true] at h1
      rw [heva, hA a hda y, ← hza, Bool.and_eq_true]
      exact ⟨h1.2, h2⟩) _ r2
  refine ⟨w2, phi_drop e y0 deg out (N + j) _ p2 ?_⟩
  intro y _ h1 h2
  rw [heva] at h2
  simp at h2
  by_cases hd : 0 < deg b
  · right
    refine ⟨b, hb, hd, ?_, h2.2⟩
    rw [r2, ifn (by omega)] at h1
    rw [r2, ifp ⟨hd, rfl⟩, h1]
    simp
  · left
    refine phi_zero e y0 deg out (N + j + 1) _ p2 (N + j) (by omega) hdeg h1 ?_
    rw [heva, ← hA a hda y, ← hA b (by omega) y, h2.1, h2.2]
    rfl

theorem gstep_inv {Y : Type} (e : Y → ℕ → Bool) (y0 : Y) (deg : ℕ → ℕ) (out N b0 : ℕ)
    (B : List Bool) (hB : B.length = b0) (j : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < N + j)
    (hNj : N + j < b0)
    (hbase : ∀ i, i < N + j → B.getD i false = e y0 i)
    (hev : ∀ y, e y (N + j) = g.op.eval (g.inputs.map (e y)))
    (hA : ∀ w, deg w = 0 → ∀ y, e y w = e y0 w)
    (hand : g.op = GateOp.and → g.inputs.length = 2 → ∃ i ∈ g.inputs, deg i = 0)
    (hdeg : 0 < deg (N + j))
    (s : St) (hw : WF b0 s) (hphi : Phi e y0 deg out (N + j + 1) (rr B s)) :
    WF b0 (gstep deg b0 (N + j) g.op g.inputs s) ∧
    Phi e y0 deg out (N + j) (rr B (gstep deg b0 (N + j) g.op g.inputs s)) := by
  rcases hins : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨c, rest⟩⟩⟩
  · simp only [gstep]
    refine ⟨hw, phi_drop e y0 deg out (N + j) _ hphi ?_⟩
    intro y _ h1 h2
    left
    refine phi_zero e y0 deg out (N + j + 1) _ hphi (N + j) (by omega) hdeg h1 ?_
    rw [hev y, hins] at h2
    rw [hev y0, hins]
    exact h2
  · simp only [gstep]
    have hu : u < N + j := hrb u (by rw [hins]; simp)
    have hevu : ∀ y, e y (N + j) = e y u := by
      intro y
      rw [hev y, hins]
      rcases hop with h | h <;> simp [h, GateOp.eval]
    obtain ⟨w1, r1⟩ := cedge_spec deg b0 B hB s u (N + j) hw
    have p1 := phi_edge e y0 deg out (N + j + 1) _ u (N + j) (0 < deg u) hphi (by omega) hdeg
      (fun y _ h => by rw [hevu]; exact h) _ r1
    refine ⟨w1, phi_drop e y0 deg out (N + j) _ p1 ?_⟩
    intro y _ h1 h2
    rw [hevu] at h2
    by_cases hd : 0 < deg u
    · right
      refine ⟨u, hu, hd, ?_, h2⟩
      rw [r1, ifn (by omega)] at h1
      rw [r1, ifp ⟨hd, rfl⟩, h1]
      simp
    · left
      refine phi_zero e y0 deg out (N + j + 1) _ p1 (N + j) (by omega) hdeg h1 ?_
      rw [hevu, ← hA u (by omega) y]
      exact h2
  · have hu : u < N + j := hrb u (by rw [hins]; simp)
    have hv : v < N + j := hrb v (by rw [hins]; simp)
    simp only [gstep]
    split_ifs with hopa hdu
    · have heva : ∀ y, e y (N + j) = (e y u && e y v) := by
        intro y
        rw [hev y, hins]
        simp [hopa, GateOp.eval]
      exact and2_inv e y0 deg out N b0 B hB j hNj hbase hA hdeg u v hu hv hdu heva s hw hphi
    · have heva : ∀ y, e y (N + j) = (e y u && e y v) := by
        intro y
        rw [hev y, hins]
        simp [hopa, GateOp.eval]
      have hdv : deg v = 0 := by
        obtain ⟨i, hi, hdi⟩ := hand hopa (by rw [hins]; rfl)
        rw [hins] at hi
        simp at hi
        rcases hi with rfl | rfl
        · exact absurd hdi hdu
        · exact hdi
      exact and2_inv e y0 deg out N b0 B hB j hNj hbase hA hdeg v u hv hu hdv
        (fun y => by rw [heva y, Bool.and_comm]) s hw hphi
    · have hopo : g.op = GateOp.or := by
        rcases hop with h | h
        · exact absurd h hopa
        · exact h
      have hevo : ∀ y, e y (N + j) = (e y u || e y v) := by
        intro y
        rw [hev y, hins]
        simp [hopo, GateOp.eval]
      obtain ⟨w1, r1⟩ := cedge_spec deg b0 B hB s u (N + j) hw
      obtain ⟨w2, r2⟩ := cedge_spec deg b0 B hB (cedge deg b0 s u (N + j)) v (N + j) w1
      have p1 := phi_edge e y0 deg out (N + j + 1) _ u (N + j) (0 < deg u) hphi (by omega) hdeg
        (fun y _ h => by rw [hevo]; simp [h]) _ r1
      have p2 := phi_edge e y0 deg out (N + j + 1) _ v (N + j) (0 < deg v) p1 (by omega) hdeg
        (fun y _ h => by rw [hevo]; simp [h]) _ r2
      refine ⟨w2, phi_drop e y0 deg out (N + j) _ p2 ?_⟩
      intro y _ h1 h2
      have h1' : rr B s (N + j) = true := by
        rw [r2, ifn (by omega), r1, ifn (by omega)] at h1
        exact h1
      have k1 : rr B (cedge deg b0 s u (N + j)) (N + j) = true := by
        rw [r1, ifn (by omega)]
        exact h1'
      have du : 0 < deg u → rr B (cedge deg b0 (cedge deg b0 s u (N + j)) v (N + j)) u = true := by
        intro hd
        rw [r2]
        split_ifs
        · rw [k1]
          simp
        · rw [r1, ifp ⟨hd, rfl⟩, h1']
          simp
      have dv : 0 < deg v → rr B (cedge deg b0 (cedge deg b0 s u (N + j)) v (N + j)) v = true := by
        intro hd
        rw [r2, ifp ⟨hd, rfl⟩, k1]
        simp
      have fin : ∀ i, i < N + j →
          (0 < deg i → rr B (cedge deg b0 (cedge deg b0 s u (N + j)) v (N + j)) i = true) →
          e y i = true → (e y0 i = true → e y0 (N + j) = true) →
          (e y0 out = true ∨ ∃ w, w < N + j ∧ 0 < deg w ∧
            rr B (cedge deg b0 (cedge deg b0 s u (N + j)) v (N + j)) w = true ∧ e y w = true) := by
        intro i hi hri hei hzi
        by_cases hd : 0 < deg i
        · exact Or.inr ⟨i, hi, hd, hri hd, hei⟩
        · left
          refine phi_zero e y0 deg out (N + j + 1) _ p2 (N + j) (by omega) hdeg h1 ?_
          apply hzi
          rw [← hA i (by omega) y]
          exact hei
      rw [hevo] at h2
      rcases (Bool.or_eq_true _ _).mp h2 with h | h
      · exact fin u hu du h (fun hz => by rw [hevo]; simp [hz])
      · exact fin v hv dv h (fun hz => by rw [hevo]; simp [hz])
  · rw [hins] at hlen
    simp at hlen

theorem rev_inv {Y : Type} (e : Y → ℕ → Bool) (y0 : Y) (deg : ℕ → ℕ) (out N b0 L : ℕ)
    (G : ℕ → Gate) (B : List Bool) (hB : B.length = b0)
    (hmono : ∀ j, j < L → ((G j).op = GateOp.and ∨ (G j).op = GateOp.or) ∧
      (G j).inputs.length ≤ 2)
    (hrb : ∀ j, j < L → ∀ i ∈ (G j).inputs, i < N + j)
    (hb0 : N + L ≤ b0)
    (hbase : ∀ i, i < N + L → B.getD i false = e y0 i)
    (hev : ∀ j, j < L → ∀ y, e y (N + j) = (G j).op.eval ((G j).inputs.map (e y)))
    (hA : ∀ w, deg w = 0 → ∀ y, e y w = e y0 w)
    (hand : ∀ j, j < L → (G j).op = GateOp.and → (G j).inputs.length = 2 →
      ∃ i ∈ (G j).inputs, deg i = 0) :
    ∀ (k : ℕ) (s : St), k ≤ L → WF b0 s → Phi e y0 deg out (N + k) (rr B s) →
      WF b0 (rev deg b0 N G k s) ∧ Phi e y0 deg out N (rr B (rev deg b0 N G k s)) := by
  intro k
  induction k with
  | zero => intro s _ hw hp; exact ⟨hw, hp⟩
  | succ k ih =>
    intro s hk hw hp
    have hp' : Phi e y0 deg out (N + k + 1) (rr B s) := hp
    simp only [rev]
    have hk' : k < L := by omega
    have key : WF b0 (step deg b0 N G k s) ∧
        Phi e y0 deg out (N + k) (rr B (step deg b0 N G k s)) := by
      unfold step
      split_ifs with hd
      · exact gstep_inv e y0 deg out N b0 B hB k (G k) (hmono k hk').1 (hmono k hk').2
          (hrb k hk') (by omega) (fun i hi => hbase i (by omega)) (hev k hk') hA (hand k hk')
          hd s hw hp'
      · exact ⟨hw, phi_drop e y0 deg out (N + k) _ hp' (fun y h => absurd h hd)⟩
    exact ih _ (by omega) key.1 key.2

theorem cedge_len (deg : ℕ → ℕ) (b0 : ℕ) (s : St) (u wg : ℕ) :
    (cedge deg b0 s u wg).1.length ≤ s.1.length + 1 := by
  unfold cedge
  split_ifs
  · rw [el_fst]
    simp
  · omega

theorem scale_len (b0 : ℕ) (s : St) (wg a : ℕ) :
    (scale b0 s wg a).1.length = s.1.length + 1 := by
  unfold scale
  rw [el_fst]
  simp

theorem gstep_len (deg : ℕ → ℕ) (b0 wg : ℕ) (op : GateOp) (ins : List ℕ) (s : St) :
    (gstep deg b0 wg op ins s).1.length ≤ s.1.length + 2 := by
  rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨c, rest⟩⟩⟩
  · simp [gstep]
  · have := cedge_len deg b0 s u wg
    simp only [gstep]
    omega
  · simp only [gstep]
    split_ifs
    · have h1 := scale_len b0 s wg u
      have h2 := cedge_len deg b0 (scale b0 s wg u) v wg
      omega
    · have h1 := scale_len b0 s wg v
      have h2 := cedge_len deg b0 (scale b0 s wg v) u wg
      omega
    · have h1 := cedge_len deg b0 s u wg
      have h2 := cedge_len deg b0 (cedge deg b0 s u wg) v wg
      omega
  · simp [gstep]

theorem rev_len (deg : ℕ → ℕ) (b0 N : ℕ) (G : ℕ → Gate) :
    ∀ (k : ℕ) (s : St), (rev deg b0 N G k s).1.length ≤
      s.1.length + 2 * ((Finset.range k).filter (fun j => 0 < deg (N + j))).card := by
  intro k
  induction k with
  | zero => intro s; simp [rev]
  | succ k ih =>
    intro s
    simp only [rev]
    have h1 := ih (step deg b0 N G k s)
    have hs : (step deg b0 N G k s).1.length ≤
        s.1.length + 2 * (if 0 < deg (N + k) then 1 else 0) := by
      unfold step
      split_ifs
      · have := gstep_len deg b0 (N + k) (G k).op (G k).inputs s
        omega
      · omega
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hd
    · rw [Finset.card_insert_of_notMem (by simp)]
      rw [ifp hd] at hs
      omega
    · rw [ifn hd] at hs
      omega

theorem fd_rep : ∀ (m : ℕ) (X : List Bool),
    fd stpF X (List.replicate m ⟨GateOp.or, []⟩) = X ++ List.replicate m false := by
  intro m
  induction m with
  | zero => intro X; simp [fd]
  | succ m ih =>
    intro X
    have := ih (X ++ [stpF ⟨GateOp.or, []⟩ X])
    rw [List.replicate_succ]
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [stpF, GateOp.eval, List.replicate_succ]

theorem rb_comp (n m : ℕ) (gs T : List Gate)
    (hgs : ∀ t g, gs[t]? = some g → ∀ i ∈ g.inputs, i < n + m + t)
    (hT : ∀ t g, T[t]? = some g → ∀ i ∈ g.inputs, i < n + m + gs.length + 1 + t) :
    ∀ t g, (List.replicate m (⟨GateOp.or, []⟩ : Gate) ++ gs ++ [(⟨GateOp.and, []⟩ : Gate)] ++ T)[t]? =
      some g → ∀ i ∈ g.inputs, i < n + t := by
  intro t g hg i hi
  simp only [List.getElem?_append, List.length_append, List.length_replicate,
    List.length_singleton] at hg
  split_ifs at hg with h1 h2 h3
  · have := List.eq_of_mem_replicate (List.mem_of_getElem? hg)
    subst this
    simp at hi
  · have := hgs _ g hg i hi
    omega
  · have := List.mem_of_getElem? hg
    simp at this
    subst this
    simp at hi
  · have := hT _ g hg i hi
    omega

theorem wires_D (n m : ℕ) (C : Circuit) (T : List Gate) (o : ℕ) (x : Fin n → Bool) :
    (Circuit.wires ⟨List.replicate m (⟨GateOp.or, []⟩ : Gate) ++ C.gates ++
      [(⟨GateOp.and, []⟩ : Gate)] ++ T, o⟩ (List.ofFn x)) =
    fd stpF (C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false))) ++ [true]) T := by
  rw [wires_fd, wires_fd]
  show fd stpF (List.ofFn x) (List.replicate m (⟨GateOp.or, []⟩ : Gate) ++ C.gates ++
      [(⟨GateOp.and, []⟩ : Gate)] ++ T) = _
  rw [fd_app, fd_app, fd_app, fd_rep, List.ofFn_fin_append, List.ofFn_const]
  congr 1

end PEqualNP.Outside.L_meta_1622

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1622 in
theorem PEqualNP.Outside.L_meta_1622 : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧ ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || (D.wires (List.ofFn x)).getD (o j) false) := by
  intro n m C hmono hrb hand
  have hcf : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      circuitFun (n + m) C (Fin.append x y) = E n m C x y C.output := fun x y => rfl
  have hGmem : ∀ j, j < C.gates.length → gateAt C j ∈ C.gates := by
    intro j hj
    have : gateAt C j = C.gates[j] := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj]
    rw [this]
    exact List.getElem_mem hj
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hmono g hg).1
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    refine ⟨⟨[], 0⟩, fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · intro j hj
      simp at hj
    · simp [Circuit.size]
    · intro x j
      exact j.elim0
  by_cases hd0 : dg n m C C.output = 0
  · refine ⟨⟨[], 0⟩, fun _ => n, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · intro j hj
      simp at hj
    · simp [Circuit.size]
    · intro x j
      rw [hcf, hcf, E_indep n m C hrb x C.output hd0 _ (fun _ => false)]
      have : (Circuit.wires ⟨[], 0⟩ (List.ofFn x)).getD n false = false := by
        show (List.ofFn x).getD n false = false
        rw [ofFn_getD, difn (by omega)]
      rw [this]
      simp
  · have hdpos : 0 < dg n m C C.output := Nat.pos_of_ne_zero hd0
    by_cases hin : C.output < n + m
    · have hno : n ≤ C.output := by
        by_contra hc
        rw [dg_in n m C _ hin, ifn hc] at hdpos
        omega
      refine ⟨⟨[(⟨GateOp.and, []⟩ : Gate)], 0⟩, fun j => if C.output = n + j.val then n else n + 1,
        ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp at hg
        subst hg
        simp
      · intro j hj i hi
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        simp [gateAt] at hi
      · simp [Circuit.size]
        omega
      · intro x j
        rw [hcf, hcf, E_in _ _ _ _ _ _ hin, E_in _ _ _ _ _ _ hin, app_getD, app_getD,
          difn (by omega), difp (by omega), difn (by omega), difp (by omega)]
        have hW : Circuit.wires ⟨[(⟨GateOp.and, []⟩ : Gate)], 0⟩ (List.ofFn x) = List.ofFn x ++ [true] := by
          simp [Circuit.wires, GateOp.eval]
        rw [hW]
        beta_reduce
        by_cases h : C.output = n + j.val
        · rw [ifp h, getD_snoc, ifp (by simp)]
          have : (⟨C.output - n, by omega⟩ : Fin m) = j := by
            apply Fin.ext
            show C.output - n = j.val
            omega
          simp [this]
        · rw [ifn h, getD_snoc, ifn (by simp), ofFn_getD, difn (by omega)]
          have : (⟨C.output - n, by omega⟩ : Fin m) ≠ j := by
            intro hc
            have := congrArg Fin.val hc
            simp at this
            omega
          simp [this]
    · have hout : C.output < n + m + C.gates.length := by
        by_contra hc
        rw [dg_out n m C _ (by omega)] at hdpos
        omega
      obtain ⟨j0, hj0e⟩ : ∃ j0, C.output = n + m + j0 := ⟨C.output - (n + m), by omega⟩
      have hj0 : j0 < C.gates.length := by omega
      let b0 := n + m + C.gates.length + 1
      let s0 : St := ([], fun w => if w = C.output then n + m + C.gates.length else n)
      let sf : St := rev (dg n m C) b0 (n + m) (gateAt C) C.gates.length s0
      have hw0 : WF b0 s0 := by
        refine ⟨?_, ?_, ?_⟩
        · intro w
          show (if w = C.output then n + m + C.gates.length else n) <
            n + m + C.gates.length + 1 + 0
          split_ifs <;> omega
        · intro t g hg
          simp [s0] at hg
        · intro g hg
          simp [s0] at hg
      have hsem : ∀ x : Fin n → Bool,
          WF b0 sf ∧ Phi (E n m C x) (fun _ => false) (dg n m C) C.output (n + m)
            (rr (C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false))) ++ [true]) sf) := by
        intro x
        have hBl : (C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false))) ++ [true]).length
            = b0 := by
          rw [wires_fd]
          simp [fd_len, b0]
        have hWl : (C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false)))).length
            = n + m + C.gates.length := by
          rw [wires_fd]
          simp [fd_len]
        have hbase : ∀ i, i < n + m + C.gates.length →
            (C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false))) ++ [true]).getD i false
              = E n m C x (fun _ => false) i := by
          intro i hi
          rw [getD_snoc, ifn (by omega)]
          rfl
        refine rev_inv (E n m C x) (fun _ => false) (dg n m C) C.output (n + m) b0 C.gates.length
          (gateAt C) _ hBl
          (fun j hj => ⟨hop _ (hGmem j hj), (hmono _ (hGmem j hj)).2⟩)
          (fun j hj => hrb j hj) (by omega) hbase
          (fun j hj y => E_gate n m C hrb x y j hj)
          (fun w hd y => E_indep n m C hrb x w hd y _)
          (fun j hj => hand j hj) C.gates.length s0 le_rfl hw0 ?_
        intro y
        have hr0 : ∀ w, rr (C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false))) ++ [true])
            s0 w = decide (w = C.output) := by
          intro w
          show ((C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false))) ++ [true]).getD
            (if w = C.output then n + m + C.gates.length else n) false) = _
          by_cases hwo : w = C.output
          · rw [ifp hwo, getD_snoc, ifp hWl.symm]
            simp [hwo]
          · rw [ifn hwo, hbase n (by omega), E_in _ _ _ _ _ _ (by omega), app_getD,
              difn (by omega), difp (by omega)]
            simp [hwo]
        constructor
        · intro h
          exact Or.inr ⟨C.output, hout, hdpos, by rw [hr0]; simp, h⟩
        · rintro (h | ⟨w, _, _, hw3, hw4⟩)
          · exact E_mono n m C hop x y _ h
          · rw [hr0] at hw3
            have : w = C.output := by simpa using hw3
            rw [this] at hw4
            exact hw4
      have hwf : WF b0 sf := (hsem (fun _ => false)).1
      refine ⟨⟨List.replicate m (⟨GateOp.or, []⟩ : Gate) ++ C.gates ++ [(⟨GateOp.and, []⟩ : Gate)] ++ sf.1,
        0⟩, fun j => sf.2 (n + j.val), ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with ((hg | hg) | hg) | hg
        · have := List.eq_of_mem_replicate hg
          subst this
          simp
        · exact hmono g hg
        · subst hg
          simp
        · obtain ⟨h1, h2⟩ := hwf.2.2 g hg
          refine ⟨?_, h2⟩
          rcases h1 with h | h <;> simp [h]
      · intro j hj i hi
        have hg : (List.replicate m (⟨GateOp.or, []⟩ : Gate) ++ C.gates ++
            [(⟨GateOp.and, []⟩ : Gate)] ++ sf.1)[j]? = some (gateAt ⟨List.replicate m
              (⟨GateOp.or, []⟩ : Gate) ++ C.gates ++ [(⟨GateOp.and, []⟩ : Gate)] ++ sf.1, 0⟩ j) := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          rfl
        refine rb_comp n m C.gates sf.1 ?_ ?_ j _ hg i hi
        · intro t g hgt i hi
          have ht : t < C.gates.length := by
            by_contra hc
            rw [List.getElem?_eq_none (by omega)] at hgt
            cases hgt
          have : gateAt C t = g := by
            simp [gateAt, List.getD_eq_getElem?_getD, hgt]
          rw [← this] at hi
          exact hrb t ht i hi
        · intro t g hgt i hi
          exact hwf.2.1 t g hgt i hi
      · have hl := rev_len (dg n m C) b0 (n + m) (gateAt C) C.gates.length s0
        have hset : {j : ℕ | j < C.gates.length ∧
            0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} =
            ↑((Finset.range C.gates.length).filter (fun j => 0 < dg n m C (n + m + j))) := by
          ext j
          simp [dg]
        rw [hset, Set.ncard_coe_finset]
        have hpos : 0 < ((Finset.range C.gates.length).filter
            (fun j => 0 < dg n m C (n + m + j))).card := by
          apply Finset.card_pos.mpr
          refine ⟨j0, ?_⟩
          rw [Finset.mem_filter, Finset.mem_range, ← hj0e]
          exact ⟨hj0, hdpos⟩
        have hs0 : s0.1.length = 0 := rfl
        simp only [Circuit.size, List.length_append, List.length_replicate, List.length_singleton]
        have hl' : sf.1.length ≤ s0.1.length + 2 * ((Finset.range C.gates.length).filter
            (fun j => 0 < dg n m C (n + m + j))).card := hl
        omega
      · intro x j
        obtain ⟨_, hphi⟩ := hsem x
        rw [hcf, hcf, wires_D]
        have hy := hphi (fun l => decide (l = j))
        have hjn : n + j.val < n + m := by omega
        have hEj : E n m C x (fun l => decide (l = j)) (n + j.val) = true := by
          rw [E_in _ _ _ _ _ _ hjn, app_getD, difn (by omega), difp (by omega)]
          have : (⟨n + j.val - n, by omega⟩ : Fin m) = j := by
            apply Fin.ext
            show n + j.val - n = j.val
            omega
          simp [this]
        rw [Bool.eq_iff_iff, Bool.or_eq_true, hy]
        constructor
        · rintro (h | ⟨w, hw1, hw2, hw3, hw4⟩)
          · exact Or.inl h
          · right
            have hwn : n ≤ w := by
              by_contra hc
              rw [dg_in n m C w hw1, ifn hc] at hw2
              omega
            rw [E_in _ _ _ _ _ _ hw1, app_getD, difn (by omega), difp (by omega)] at hw4
            have hwj : w = n + j.val := by
              have h5 : (⟨w - n, by omega⟩ : Fin m) = j := by simpa using hw4
              have := congrArg Fin.val h5
              simp at this
              omega
            rw [hwj] at hw3
            exact hw3
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨n + j.val, hjn, by rw [dg_in n m C _ hjn, ifp (by omega)]; omega,
              h, hEj⟩
