import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3477

open PEqualNP.CircuitLowerBounds Finset

-- A list built gate by gate, one value appended per gate.
def fa {α : Type} (f : List α → Gate → α) (gs : List Gate) (l : List α) : List α :=
  gs.foldl (fun acc g => acc ++ [f acc g]) l

lemma fa_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (l : List α) :
    fa f (g :: gs) l = fa f gs (l ++ [f l g]) := rfl

lemma fa_append {α : Type} (f : List α → Gate → α) (gs hs : List Gate) (l : List α) :
    fa f (gs ++ hs) l = fa f hs (fa f gs l) := by
  simp only [fa, List.foldl_append]

lemma fa_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (l : List α) :
    (fa f gs l).length = l.length + gs.length := by
  induction gs generalizing l with
  | nil => simp [fa]
  | cons g gs ih =>
    rw [fa_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma fa_getD_lt {α : Type} (f : List α → Gate → α) (gs : List Gate) (l : List α)
    (i : ℕ) (hi : i < l.length) (d : α) : (fa f gs l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    rw [fa_cons, ih (l ++ [f l g]) (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fa_getD_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (l : List α)
    (j i : ℕ) (hi : i < l.length + j) (hj : j ≤ gs.length) (d : α) :
    (fa f gs l).getD i d = (fa f (gs.take j) l).getD i d := by
  conv_lhs => rw [← List.take_append_drop j gs]
  rw [fa_append, fa_getD_lt]
  rw [fa_length, List.length_take]
  omega

lemma fa_getD_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (l : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (fa f gs l).getD (l.length + j) d = f (fa f (gs.take j) l) gs[j] := by
  have hl : (fa f (gs.take j) l).length = l.length + j := by
    rw [fa_length, List.length_take]; omega
  conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
  rw [fa_append, fa_cons, fa_getD_lt _ _ _ _ (by simp [hl])]
  rw [← hl]
  simp

-- Gate number j, read with a default past the end of the list.
def gt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨GateOp.or, []⟩

lemma gt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gt C j = C.gates[j] := by
  simp [gt, List.getD_eq_getElem?_getD, hj]

-- Operand b of gate j: the first one for false, the second one for true.
def inp (C : Circuit) (j : ℕ) (b : Bool) : ℕ := (gt C j).inputs.getD (if b then 1 else 0) 0

def wstep (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_fa (C : Circuit) (x : List Bool) : C.wires x = fa wstep C.gates x := rfl

-- The value of wire w at the input list x.
def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

lemma val_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    val C x w = x.getD w false := by
  unfold val; rw [wires_fa, fa_getD_lt _ _ _ _ hw]

lemma val_beyond (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    val C x w = false := by
  unfold val
  rw [List.getD_eq_default]
  rw [wires_fa, fa_length]; exact hw

lemma val_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hin : ∀ i ∈ (gt C j).inputs, i < x.length + j) :
    val C x (x.length + j) = (gt C j).op.eval ((gt C j).inputs.map fun i => val C x i) := by
  unfold val
  rw [wires_fa, fa_getD_gate _ _ _ _ hj, ← gt_eq C j hj, wstep]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [fa_getD_take wstep C.gates x j i (hin i hi) hj.le]

lemma gate_shape {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    (gt C j).inputs = [inp C j false, inp C j true] ∧ inp C j false < n + j ∧
      inp C j true < n + j ∧ ((gt C j).op = GateOp.and ∨ (gt C j).op = GateOp.or) := by
  obtain ⟨hao, hrb, h2⟩ := h
  have hmem : gt C j ∈ C.gates := by rw [gt_eq C j hj]; exact List.getElem_mem hj
  have hlen := h2 _ hmem
  have hop := hao _ hmem
  have hrb' : ∀ i ∈ (gt C j).inputs, i < n + j := hrb j hj
  obtain ⟨a, c, hac⟩ : ∃ a c, (gt C j).inputs = [a, c] := by
    rcases hl : (gt C j).inputs with _ | ⟨a, _ | ⟨c, _ | ⟨d, t⟩⟩⟩ <;> simp_all
  have ha : inp C j false = a := by simp [inp, hac]
  have hc : inp C j true = c := by simp [inp, hac]
  refine ⟨by rw [ha, hc, hac], ?_, ?_, hop⟩
  · rw [ha]; exact hrb' a (by simp [hac])
  · rw [hc]; exact hrb' c (by simp [hac])

lemma val_and {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) (hop : (gt C j).op = GateOp.and) :
    val C x (n + j) = (val C x (inp C j false) && val C x (inp C j true)) := by
  obtain ⟨hs, ha, hc, -⟩ := gate_shape h j hj
  have hg := val_gate C x j hj (by rw [hs, hx]; intro i hi; simp at hi; omega)
  rw [hx] at hg
  rw [hg, hop, hs]
  simp [GateOp.eval]

lemma val_or {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) (hop : (gt C j).op = GateOp.or) :
    val C x (n + j) = (val C x (inp C j false) || val C x (inp C j true)) := by
  obtain ⟨hs, ha, hc, -⟩ := gate_shape h j hj
  have hg := val_gate C x j hj (by rw [hs, hx]; intro i hi; simp at hi; omega)
  rw [hx] at hg
  rw [hg, hop, hs]
  simp [GateOp.eval]

lemma val_mono {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ w, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_input C x w (by omega)] at hw
      rw [val_input C y w (by omega)]
      exact hxy w hw
    · by_cases h2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨-, ha, hc, hop⟩ := gate_shape h j hj
        have iha := ih (inp C j false) (by omega)
        have ihc := ih (inp C j true) (by omega)
        rcases hop with hop | hop
        · rw [val_and h x hx j hj hop] at hw
          rw [val_and h y hy j hj hop]
          simp only [Bool.and_eq_true] at hw ⊢
          exact ⟨iha hw.1, ihc hw.2⟩
        · rw [val_or h x hx j hj hop] at hw
          rw [val_or h y hy j hj hop]
          simp only [Bool.or_eq_true] at hw ⊢
          rcases hw with hw | hw
          · exact Or.inl (iha hw)
          · exact Or.inr (ihc hw)
      · rw [val_beyond C x w (by omega)] at hw
        exact absurd hw (by simp)

-- The linear parts of the wires (the definition of the ReadK module, gate by gate).
def lins (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | GateOp.or  => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def lstep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  lins g.op (g.inputs.map fun i => w.getD i (false, false))

def linit (isLine : ℕ → Bool) (x : List Bool) : List (Bool × Bool) :=
  (x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)

lemma lp_fa (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C isLine x = fa lstep C.gates (linit isLine x) := rfl

lemma linit_length (isLine : ℕ → Bool) (x : List Bool) : (linit isLine x).length = x.length := by
  simp [linit]

lemma linit_getD (isLine : ℕ → Bool) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (linit isLine x).getD i (false, false) =
      if isLine i then (false, x.getD i false) else (x.getD i false, false) := by
  simp [linit, List.getD_eq_getElem?_getD, hi]

def lpv (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) (w : ℕ) : Bool × Bool :=
  (PEqualNP.ReadK.linearParts C isLine x).getD w (false, false)

lemma lpv_input (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    lpv C isLine x w = if isLine w then (false, x.getD w false) else (x.getD w false, false) := by
  unfold lpv
  rw [lp_fa, fa_getD_lt _ _ _ _ (by rw [linit_length]; exact hw), linit_getD _ _ _ hw]

lemma lpv_beyond (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) (w : ℕ)
    (hw : x.length + C.gates.length ≤ w) : lpv C isLine x w = (false, false) := by
  unfold lpv
  rw [List.getD_eq_default]
  rw [lp_fa, fa_length, linit_length]; exact hw

lemma lpv_gate (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hin : ∀ i ∈ (gt C j).inputs, i < x.length + j) :
    lpv C isLine x (x.length + j) =
      lstep (PEqualNP.ReadK.linearParts C isLine x) (gt C j) := by
  unfold lpv
  have h0 := fa_getD_gate lstep C.gates (linit isLine x) j hj (false, false)
  rw [linit_length] at h0
  rw [lp_fa, h0, ← gt_eq C j hj, lstep, lstep]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [fa_getD_take lstep C.gates (linit isLine x) j i (by rw [linit_length]; exact hin i hi) hj.le]

lemma lpv_and {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (isLine : ℕ → Bool)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gt C j).op = GateOp.and) :
    lpv C isLine x (n + j) =
      ((lpv C isLine x (inp C j false)).1 && (lpv C isLine x (inp C j true)).1,
       ((lpv C isLine x (inp C j false)).1 && (lpv C isLine x (inp C j true)).2) ||
       ((lpv C isLine x (inp C j false)).2 && (lpv C isLine x (inp C j true)).1)) := by
  obtain ⟨hs, ha, hc, -⟩ := gate_shape h j hj
  have hg := lpv_gate C isLine x j hj (by rw [hs, hx]; intro i hi; simp at hi; omega)
  rw [hx] at hg
  rw [hg, lstep, hop, hs]
  simp [lins, lpv]

lemma lpv_or {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (isLine : ℕ → Bool)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gt C j).op = GateOp.or) :
    lpv C isLine x (n + j) =
      ((lpv C isLine x (inp C j false)).1 || (lpv C isLine x (inp C j true)).1,
       (lpv C isLine x (inp C j false)).2 || (lpv C isLine x (inp C j true)).2) := by
  obtain ⟨hs, ha, hc, -⟩ := gate_shape h j hj
  have hg := lpv_gate C isLine x j hj (by rw [hs, hx]; intro i hi; simp at hi; omega)
  rw [hx] at hg
  rw [hg, lstep, hop, hs]
  simp [lins, lpv]

-- Part 0 of a wire is its value with the inputs marked by isLine set false.
lemma lpv_fst {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (isLine : ℕ → Bool)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ i, i < n → (if isLine i then false else x.getD i false) = y.getD i false) :
    ∀ w, (lpv C isLine x w).1 = val C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < n
    · rw [lpv_input C isLine x w (by omega), val_input C y w (by omega), ← hxy w h1]
      split <;> rfl
    · by_cases h2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨-, ha, hc, hop⟩ := gate_shape h j hj
        rcases hop with hop | hop
        · rw [lpv_and h isLine x hx j hj hop, val_and h y hy j hj hop, ih _ (by omega),
            ih _ (by omega)]
        · rw [lpv_or h isLine x hx j hj hop, val_or h y hy j hj hop, ih _ (by omega),
            ih _ (by omega)]
      · rw [lpv_beyond C isLine x w (by omega), val_beyond C y w (by omega)]

-- The input list of length n with exactly the wires i with S i true.
def lst (n : ℕ) (S : ℕ → Bool) : List Bool := (List.range n).map S

lemma lst_length (n : ℕ) (S : ℕ → Bool) : (lst n S).length = n := by simp [lst]

lemma lst_getD (n : ℕ) (S : ℕ → Bool) (i : ℕ) : (lst n S).getD i false = (decide (i < n) && S i) := by
  unfold lst
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · simp [h]
  · simp [h]

lemma ofFn_lst (n : ℕ) (S : ℕ → Bool) : List.ofFn (fun i : Fin n => S i.val) = lst n S := by
  apply List.ext_getElem
  · simp [lst]
  · intro i h1 h2
    simp [lst]

-- One OR step: wire a is read by an OR gate whose wire is b.
def orStep (C : Circuit) (n : ℕ) (a b : ℕ) : Prop :=
  ∃ j, j < C.gates.length ∧ (gt C j).op = GateOp.or ∧ a ∈ (gt C j).inputs ∧ b = n + j

-- Wire w reaches the input p through OR gates only.
def ORr (C : Circuit) (n p w : ℕ) : Prop := Relation.ReflTransGen (orStep C n) p w

lemma ORr_val {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (p : ℕ) (hp : p < n) (hxp : x.getD p false = true) :
    ∀ w, ORr C n p w → val C x w = true := by
  intro w hw
  induction hw with
  | refl => rw [val_input C x p (by omega)]; exact hxp
  | tail _ hst ih =>
    obtain ⟨j, hj, hop, ha, rfl⟩ := hst
    rw [val_or h x hx j hj hop]
    obtain ⟨hs, -, -, -⟩ := gate_shape h j hj
    rw [hs] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | ha
    · rw [← ha]; simp [ih]
    · rw [← ha]; simp [ih]

def isL (N : ℕ) : ℕ → Bool := fun i => decide (i < N)

-- The input with point p and line l on, and the input with only line l on.
def epl (N p l : ℕ) : ℕ → Bool := fun i => i == p || i == N + l

def el (N l : ℕ) : ℕ → Bool := fun i => i == N + l

-- Wire w is true only where the output is, on inputs with line l on.
def UpW (C : Circuit) (N w l : ℕ) : Prop :=
  ∀ S : ℕ → Bool, S (N + l) = true → val C (lst (N + N) S) w = true →
    val C (lst (N + N) S) C.output = true

-- Gate j is an AND gate whose operand b reaches the point p through OR gates and whose other
-- operand is true when only the line l is on.
def Good (C : Circuit) (N j : ℕ) (b : Bool) (p l : ℕ) : Prop :=
  (gt C j).op = GateOp.and ∧ ORr C (N + N) p (inp C j b) ∧
    val C (lst (N + N) (el N l)) (inp C j (!b)) = true

lemma el_le (N l : ℕ) (S : ℕ → Bool) (hS : S (N + l) = true) :
    ∀ i, (lst (N + N) (el N l)).getD i false = true → (lst (N + N) S).getD i false = true := by
  intro i hi
  simp only [lst_getD, el, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi ⊢
  obtain ⟨h1, rfl⟩ := hi
  exact ⟨h1, hS⟩

lemma part0_epl {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C) (p l : ℕ)
    (hp : p < N) (w : ℕ) :
    (lpv C (isL N) (lst (N + N) (epl N p l)) w).1 = val C (lst (N + N) (el N l)) w := by
  apply lpv_fst h (isL N) _ _ (lst_length _ _) (lst_length _ _)
  intro i hi
  simp only [lst_getD, isL, epl, el, hi, decide_true, Bool.true_and]
  by_cases h1 : i < N
  · simp only [h1, decide_true, ↓reduceIte]
    symm
    simp only [beq_eq_false_iff_ne]
    omega
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    have : (i == p) = false := by simp only [beq_eq_false_iff_ne]; omega
    rw [this, Bool.false_or]

lemma descent {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 (N + N) C) (p l : ℕ)
    (hp : p < N) :
    ∀ w, (lpv C (isL N) (lst (N + N) (epl N p l)) w).2 = true → UpW C N w l →
      (∃ j, j < C.gates.length ∧ ∃ b, Good C N j b p l ∧ UpW C N (N + N + j) l) ∨
        ORr C (N + N) p w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hup
    have hx : (lst (N + N) (epl N p l)).length = N + N := lst_length _ _
    by_cases h1 : w < N + N
    · rw [lpv_input C _ _ w (by rw [hx]; exact h1)] at hw
      by_cases h2 : w < N
      · have hw' : (lst (N + N) (epl N p l)).getD w false = true := by
          have h := hw
          simp only [isL, h2, decide_true, ↓reduceIte] at h
          exact h
        rw [lst_getD] at hw'
        simp only [epl, h1, decide_true, Bool.true_and, Bool.or_eq_true, beq_iff_eq] at hw'
        right
        have hwp : w = p := by omega
        rw [hwp]
        exact Relation.ReflTransGen.refl
      · simp [isL, h2] at hw
    · by_cases h3 : w < N + N + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨hs, ha, hc, hop⟩ := gate_shape hAO j hj
        rcases hop with hop | hop
        · rw [lpv_and hAO (isL N) _ hx j hj hop] at hw
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw
          rcases hw with ⟨h0, h1'⟩ | ⟨h1', h0⟩
          · rw [part0_epl hAO p l hp] at h0
            have hupc : UpW C N (inp C j true) l := by
              intro S hS hv
              apply hup S hS
              rw [val_and hAO _ (lst_length _ _) j hj hop]
              simp only [Bool.and_eq_true]
              exact ⟨val_mono hAO _ _ (lst_length _ _) (lst_length _ _) (el_le N l S hS) _ h0, hv⟩
            rcases ih (inp C j true) (by omega) h1' hupc with hres | hor
            · exact Or.inl hres
            · exact Or.inl ⟨j, hj, true, ⟨hop, hor, by simpa using h0⟩, hup⟩
          · rw [part0_epl hAO p l hp] at h0
            have hupa : UpW C N (inp C j false) l := by
              intro S hS hv
              apply hup S hS
              rw [val_and hAO _ (lst_length _ _) j hj hop]
              simp only [Bool.and_eq_true]
              exact ⟨hv, val_mono hAO _ _ (lst_length _ _) (lst_length _ _) (el_le N l S hS) _ h0⟩
            rcases ih (inp C j false) (by omega) h1' hupa with hres | hor
            · exact Or.inl hres
            · exact Or.inl ⟨j, hj, false, ⟨hop, hor, by simpa using h0⟩, hup⟩
        · rw [lpv_or hAO (isL N) _ hx j hj hop] at hw
          simp only [Bool.or_eq_true] at hw
          rcases hw with h1' | h1'
          · have hupa : UpW C N (inp C j false) l := by
              intro S hS hv
              apply hup S hS
              rw [val_or hAO _ (lst_length _ _) j hj hop]
              simp [hv]
            rcases ih (inp C j false) (by omega) h1' hupa with hres | hor
            · exact Or.inl hres
            · right
              exact Relation.ReflTransGen.tail hor ⟨j, hj, hop, by rw [hs]; simp, rfl⟩
          · have hupc : UpW C N (inp C j true) l := by
              intro S hS hv
              apply hup S hS
              rw [val_or hAO _ (lst_length _ _) j hj hop]
              simp [hv]
            rcases ih (inp C j true) (by omega) h1' hupc with hres | hor
            · exact Or.inl hres
            · right
              exact Relation.ReflTransGen.tail hor ⟨j, hj, hop, by rw [hs]; simp, rfl⟩
      · rw [lpv_beyond C _ _ _ (by rw [hx]; omega)] at hw
        simp at hw

-- The projective plane: a line has q + 1 points, a point lies on at most q + 1 lines.
lemma pts_card {N q : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hline : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) (l : Fin N) :
    (univ.filter (fun p => I p l)).card = q + 1 := by
  rw [← Fintype.card_subtype]
  exact hline l

lemma lines_le {N q : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) (p0 : Fin N) :
    (univ.filter (fun l => I p0 l)).card ≤ q + 1 := by
  set L := univ.filter (fun l => I p0 l) with hL
  let Sl : Fin N → Finset (Fin N) := fun l => (univ.filter (fun p => I p l)).erase p0
  have hcardS : ∀ l ∈ L, (Sl l).card = q := by
    intro l hl
    simp only [hL, mem_filter, mem_univ, true_and] at hl
    simp only [Sl]
    rw [card_erase_of_mem (by simp [hl]), pts_card hline l]
    simp
  have hdisj : ∀ l1 ∈ L, ∀ l2 ∈ L, l1 ≠ l2 → Disjoint (Sl l1) (Sl l2) := by
    intro l1 h1 l2 h2 hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Sl, mem_erase, mem_filter, mem_univ, true_and] at hp1 hp2
    simp only [hL, mem_filter, mem_univ, true_and] at h1 h2
    obtain ⟨l0, -, hu⟩ := huniq p0 p (Ne.symm hp1.1)
    exact hne ((hu l1 ⟨h1, hp1.2⟩).trans (hu l2 ⟨h2, hp2.2⟩).symm)
  have hsub : L.biUnion Sl ⊆ univ.erase p0 := by
    intro p hp
    simp only [mem_biUnion, Sl, mem_erase] at hp
    obtain ⟨l, -, hne, -⟩ := hp
    simp [hne]
  have h1 : (L.biUnion Sl).card = L.card * q := by
    rw [card_biUnion hdisj, sum_congr rfl hcardS, sum_const, smul_eq_mul]
  have hN' : N = (q + 1) * q + 1 := by rw [hN]; ring
  have h2 : (L.biUnion Sl).card ≤ (q + 1) * q := by
    calc _ ≤ (univ.erase p0).card := card_le_card hsub
      _ = N - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
      _ = (q + 1) * q := by rw [hN', Nat.add_sub_cancel]
  rw [h1] at h2
  exact Nat.le_of_mul_le_mul_right h2 hq

lemma rect {N q : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (T : Finset (Fin N × Fin N)) (hI : ∀ x ∈ T, ∀ y ∈ T, I x.1 y.2) : T.card ≤ q + 1 := by
  by_cases hd : ∃ x ∈ T, ∃ y ∈ T, x.1 ≠ y.1
  · obtain ⟨x, hx, y, hy, hne⟩ := hd
    obtain ⟨l0, -, hu⟩ := huniq x.1 y.1 hne
    have hz : ∀ z ∈ T, z.2 = l0 := fun z hz => hu z.2 ⟨hI x hx z hz, hI y hy z hz⟩
    have hsub : T ⊆ (univ.filter (fun p => I p l0)).image (fun p => (p, l0)) := by
      intro z hzT
      simp only [mem_image, mem_filter, mem_univ, true_and]
      refine ⟨z.1, ?_, ?_⟩
      · have := hI z hzT z hzT
        rwa [hz z hzT] at this
      · exact Prod.ext rfl (hz z hzT).symm
    calc T.card ≤ _ := card_le_card hsub
      _ ≤ (univ.filter (fun p => I p l0)).card := card_image_le
      _ = q + 1 := pts_card hline l0
  · simp only [not_exists, not_and, ne_eq, not_not] at hd
    rcases T.eq_empty_or_nonempty with he | ⟨x0, hx0⟩
    · simp [he]
    · have hsub : T ⊆ (univ.filter (fun l => I x0.1 l)).image (fun l => (x0.1, l)) := by
        intro z hzT
        simp only [mem_image, mem_filter, mem_univ, true_and]
        have h1 := hd z hzT x0 hx0
        refine ⟨z.2, ?_, ?_⟩
        · have := hI z hzT z hzT
          rwa [h1] at this
        · exact Prod.ext h1.symm rfl
      calc T.card ≤ _ := card_le_card hsub
        _ ≤ (univ.filter (fun l => I x0.1 l)).card := card_image_le
        _ ≤ q + 1 := lines_le hq hN hline huniq x0.1

-- The soundness hypothesis, on an input given by the wires that are on.
lemma sound_lst {N q : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (hs : ∀ y : Fin (N + N) → Bool, Fintype.card {m : Fin N // y (Fin.natAdd N m) = true} ≤ q →
      (¬∃ (a b : Fin N), I a b ∧ y (Fin.castAdd N a) = true ∧ y (Fin.natAdd N b) = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C y = false)
    (S : ℕ → Bool)
    (hl : Fintype.card {m : Fin N // S (N + m.val) = true} ≤ q)
    (hi : ∀ a b : Fin N, I a b → S a.val = true → S (N + b.val) = true → False) :
    val C (lst (N + N) S) C.output = false := by
  have h := hs (fun i => S i.val) hl (by
    rintro ⟨a, b, hab, h1, h2⟩
    exact hi a b hab h1 h2)
  rw [← h]
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval val
  rw [ofFn_lst]

lemma card_one_line {N : ℕ} (l : ℕ) :
    Fintype.card {m : Fin N // (N + m.val == N + l) = true} ≤ 1 := by
  rw [Fintype.card_subtype]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and, beq_iff_eq] at ha hb
  exact Fin.ext (by omega)

lemma card_two_lines {N : ℕ} (l1 l2 : ℕ) :
    Fintype.card {m : Fin N // (N + m.val == N + l1 || N + m.val == N + l2) = true} ≤ 2 := by
  rw [Fintype.card_subtype]
  have hsub : univ.filter (fun m : Fin N => (N + m.val == N + l1 || N + m.val == N + l2) = true) ⊆
      univ.filter (fun m : Fin N => m.val = l1) ∪ univ.filter (fun m : Fin N => m.val = l2) := by
    intro m hm
    simp only [mem_filter, mem_univ, true_and, Bool.or_eq_true, beq_iff_eq, mem_union] at hm ⊢
    omega
  have h1 : (univ.filter (fun m : Fin N => m.val = l1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Fin.ext (by omega)
  have h2 : (univ.filter (fun m : Fin N => m.val = l2)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Fin.ext (by omega)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ 2 := by omega

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq2 : 2 ≤ q) (hq9 : q ≤ 9) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hs : ∀ y : Fin (N + N) → Bool, Fintype.card {m : Fin N // y (Fin.natAdd N m) = true} ≤ q →
      (¬∃ (a b : Fin N), I a b ∧ y (Fin.castAdd N a) = true ∧ y (Fin.natAdd N b) = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C y = false) :
    Fintype.card {x : Fin N × Fin N // I x.1 x.2 ∧ PEqualNP.ReadK.lineSingle C (N + N)
      (fun i => decide (i < N)) (↑x.1) (N + ↑x.2) = true} ≤ 10 * C.size := by
  rw [Fintype.card_subtype]
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun j => univ.filter (fun x =>
    I x.1 x.2 ∧ ∃ b, Good C N j b x.1.val x.2.val ∧ UpW C N (N + N + j) x.2.val)
  -- no input with only a point on is accepted
  have hpoint : ∀ p : Fin N, val C (lst (N + N) (fun i => i == p.val)) C.output = false := by
    intro p
    apply sound_lst hs
    · have : Fintype.card {m : Fin N // (N + m.val == p.val) = true} = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        rintro ⟨m, hm⟩
        simp only [beq_iff_eq] at hm
        have := p.isLt
        omega
      omega
    · intro a b _ _ h2
      simp only [beq_iff_eq] at h2
      have := p.isLt
      omega
  have hsub : univ.filter (fun x : Fin N × Fin N => I x.1 x.2 ∧ PEqualNP.ReadK.lineSingle C (N + N)
      (fun i => decide (i < N)) (↑x.1) (N + ↑x.2) = true) ⊆ (range C.gates.length).biUnion T := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hI, hsingle⟩ := hx
    have hw : (lpv C (isL N) (lst (N + N) (epl N x.1.val x.2.val)) C.output).2 = true := hsingle
    rcases descent hAO x.1.val x.2.val x.1.isLt C.output hw (fun S _ hv => hv) with
      ⟨j, hj, b, hgood, hup⟩ | hor
    · simp only [mem_biUnion, mem_range]
      refine ⟨j, hj, ?_⟩
      simp only [T, mem_filter, mem_univ, true_and]
      exact ⟨hI, b, hgood, hup⟩
    · exfalso
      have hv := ORr_val hAO (lst (N + N) (fun i => i == x.1.val)) (lst_length _ _) x.1.val
        (by have := x.1.isLt; omega) (by
          rw [lst_getD]
          have := x.1.isLt
          simp only [beq_self_eq_true, Bool.and_true, decide_eq_true_eq]
          omega) C.output hor
      rw [hpoint x.1] at hv
      exact absurd hv (by simp)
  have hT : ∀ j ∈ range C.gates.length, (T j).card ≤ q + 1 := by
    intro j hjr
    have hj : j < C.gates.length := mem_range.mp hjr
    apply rect (by omega) hN hline huniq
    intro x hx y hy
    simp only [T, mem_filter, mem_univ, true_and] at hx hy
    obtain ⟨-, b1, ⟨hop, hor1, hsib1⟩, hup1⟩ := hx
    obtain ⟨-, b2, ⟨-, hor2, hsib2⟩, hup2⟩ := hy
    by_contra hnot
    by_cases hb : b1 = b2
    · subst hb
      have hval : val C (lst (N + N) (epl N x.1.val y.2.val)) (N + N + j) = true := by
        rw [val_and hAO _ (lst_length _ _) j hj hop]
        have hA : val C (lst (N + N) (epl N x.1.val y.2.val)) (inp C j b1) = true :=
          ORr_val hAO _ (lst_length _ _) x.1.val (by have := x.1.isLt; omega)
            (by
              rw [lst_getD]
              have := x.1.isLt
              simp only [epl, beq_self_eq_true, Bool.true_or, Bool.and_true, decide_eq_true_eq]
              omega) _ hor1
        have hB : val C (lst (N + N) (epl N x.1.val y.2.val)) (inp C j (!b1)) = true :=
          val_mono hAO _ _ (lst_length _ _) (lst_length _ _)
            (el_le N y.2.val _ (by simp [epl])) _ hsib2
        cases b1
        · simp only [Bool.and_eq_true]; exact ⟨hA, hB⟩
        · simp only [Bool.and_eq_true]; exact ⟨hB, hA⟩
      have hout := hup2 _ (by simp [epl]) hval
      rw [sound_lst hs (epl N x.1.val y.2.val)] at hout
      · exact absurd hout (by simp)
      · calc _ ≤ 1 := by
              have hc : ∀ m : Fin N, epl N x.1.val y.2.val (N + m.val) =
                  (N + m.val == N + y.2.val) := by
                intro m
                simp only [epl]
                have : (N + m.val == x.1.val) = false := by
                  simp only [beq_eq_false_iff_ne]; have := x.1.isLt; omega
                rw [this, Bool.false_or]
              simp only [hc]
              exact card_one_line y.2.val
          _ ≤ q := by omega
      · intro a b hab h1 h2
        simp only [epl, Bool.or_eq_true, beq_iff_eq] at h1 h2
        have ha' : a = x.1 := by
          apply Fin.ext
          rcases h1 with h1 | h1
          · exact h1
          · have := a.isLt; omega
        have hb' : b = y.2 := by
          apply Fin.ext
          rcases h2 with h2 | h2
          · have := x.1.isLt; omega
          · omega
        rw [ha', hb'] at hab
        exact hnot hab
    · have hb2 : b2 = !b1 := by cases b1 <;> cases b2 <;> simp_all
      let S : ℕ → Bool := fun i => i == N + x.2.val || i == N + y.2.val
      have hval : val C (lst (N + N) S) (N + N + j) = true := by
        rw [val_and hAO _ (lst_length _ _) j hj hop]
        have hA : val C (lst (N + N) S) (inp C j (!b1)) = true :=
          val_mono hAO _ _ (lst_length _ _) (lst_length _ _) (el_le N x.2.val _ (by simp [S])) _ hsib1
        have hB : val C (lst (N + N) S) (inp C j b1) = true := by
          have := val_mono hAO _ _ (lst_length _ _) (lst_length _ _) (el_le N y.2.val S (by simp [S]))
            _ hsib2
          rw [hb2, Bool.not_not] at this
          exact this
        cases b1
        · simp only [Bool.and_eq_true]; exact ⟨hB, hA⟩
        · simp only [Bool.and_eq_true]; exact ⟨hA, hB⟩
      have hout := hup1 S (by simp [S]) hval
      rw [sound_lst hs S] at hout
      · exact absurd hout (by simp)
      · calc _ ≤ 2 := card_two_lines x.2.val y.2.val
          _ ≤ q := hq2
      · intro a b _ h1 _
        simp only [S, Bool.or_eq_true, beq_iff_eq] at h1
        have := a.isLt
        omega
  calc (univ.filter _).card ≤ ((range C.gates.length).biUnion T).card := card_le_card hsub
    _ ≤ ∑ j ∈ range C.gates.length, (T j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ range C.gates.length, (q + 1) := sum_le_sum hT
    _ = C.gates.length * (q + 1) := by simp
    _ ≤ 10 * C.size := by
      show C.gates.length * (q + 1) ≤ 10 * C.gates.length
      nlinarith

end PEqualNP.Outside.L_meta_3477

theorem PEqualNP.Outside.L_meta_3477 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (9 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x14 < x2)) (↑x13.1) (x2 + ↑x13.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro q N I _ C hq2 hq9 hN hline huniq hAO hs
  exact PEqualNP.Outside.L_meta_3477.main q N I C hq2 hq9 hN hline huniq hAO hs
