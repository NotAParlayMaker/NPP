import Mathlib
import PEqualNP.Defs

-- Wire and degree identities adapted from Miles McGuire, L-meta-738.
namespace PEqualNP.Outside.L_meta_1623_aux

open PEqualNP.CircuitLowerBounds

def fw {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) init

lemma fw_nil {α : Type} (f : List α → Gate → α) (init : List α) : fw f [] init = init := rfl

lemma fw_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    fw f (g :: gs) init = fw f gs (init ++ [f init g]) := rfl

lemma fw_append {α : Type} (f : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    fw f (gs ++ hs) init = fw f hs (fw f gs init) := by
  simp [fw, List.foldl_append]

lemma fw_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    fw f (gs ++ [g]) init = fw f gs init ++ [f (fw f gs init) g] := by
  rw [fw_append]; rfl

lemma fw_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (fw f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [fw_nil]
  | cons g gs ih => rw [fw_cons, ih]; simp; omega

lemma fw_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    ∃ r, fw f gs init = init ++ r := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp [fw_nil]⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (init ++ [f init g])
    exact ⟨[f init g] ++ r, by rw [fw_cons, hr]; simp⟩

lemma getD_append_left' {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_take' {α : Type} (l : List α) (m i : ℕ) (d : α) :
    (l.take m).getD i d = if i < m then l.getD i d else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma fw_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j ≤ gs.length) :
    (fw f gs init).take (init.length + j) = fw f (gs.take j) init := by
  have h := List.take_append_drop j gs
  conv_lhs => rw [← h, fw_append]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop j) (fw f (gs.take j) init)
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

lemma fw_getD_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j < gs.length) (d : α) :
    (fw f gs init).getD (init.length + j) d =
      f ((fw f gs init).take (init.length + j)) gs[j] := by
  rw [fw_take f gs init j hj.le]
  have h : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    simp
  conv_lhs => rw [h, fw_append, fw_snoc]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop (j + 1)) (fw f (gs.take j) init ++ [f (fw f (gs.take j) init) gs[j]])
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hl]

section C

variable (P L : ℕ) (C : Circuit)

def deg (i : ℕ) : ℕ := (C.lineDegrees (P + L) (Finset.Ico P (P + L))).getD i 0

def val (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x ++ List.ofFn y)).getD i false

lemma lineDegrees_eq : C.lineDegrees (P + L) (Finset.Ico P (P + L)) =
    fw (fun d g => g.lineDegree d) C.gates
      ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0) := rfl

lemma wires_eq (z : List Bool) : C.wires z =
    fw (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates z := rfl

lemma deg_input (i : ℕ) (hi : i < P + L) : deg P L C i = if P ≤ i then 1 else 0 := by
  unfold deg
  rw [lineDegrees_eq]
  obtain ⟨r, hr⟩ := fw_prefix (fun d g => g.lineDegree d) C.gates
    ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0)
  rw [hr, getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma deg_point (i : ℕ) (hi : i < P) : deg P L C i = 0 := by
  rw [deg_input P L C i (by omega)]; simp; omega

lemma deg_line (i : ℕ) (hi : P ≤ i) (hi2 : i < P + L) : deg P L C i = 1 := by
  rw [deg_input P L C i hi2]; simp [hi]

lemma deg_ge (i : ℕ) (hi : P + L + C.gates.length ≤ i) : deg P L C i = 0 := by
  unfold deg
  apply List.getD_eq_default
  rw [lineDegrees_eq, fw_length]; simp; omega

lemma deg_gate_eq (j : ℕ) (hj : j < C.gates.length) :
    deg P L C (P + L + j) =
      C.gates[j].lineDegree ((C.lineDegrees (P + L) (Finset.Ico P (P + L))).take (P + L + j)) := by
  have h := fw_getD_gate (fun d g => g.lineDegree d) C.gates
    ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0) j hj 0
  simp only [List.length_map, List.length_range] at h
  unfold deg
  rw [lineDegrees_eq, h]

lemma deg_gate_and (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) :
    deg P L C (P + L + j) =
      (C.gates[j].inputs.map fun i => if i < P + L + j then deg P L C i else 0).sum := by
  rw [deg_gate_eq P L C j hj]
  unfold Gate.lineDegree
  rw [if_pos hop]
  simp only [getD_take']
  rfl

lemma deg_gate_or (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) :
    deg P L C (P + L + j) =
      (C.gates[j].inputs.map fun i => if i < P + L + j then deg P L C i else 0).foldr max 0 := by
  rw [deg_gate_eq P L C j hj]
  unfold Gate.lineDegree
  rw [if_neg (by rw [hop]; exact fun h => GateOp.noConfusion h)]
  simp only [getD_take']
  rfl

lemma val_input (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : i < P + L) :
    val P L C x y i = (List.ofFn x ++ List.ofFn y).getD i false := by
  unfold val
  rw [wires_eq]
  obtain ⟨r, hr⟩ := fw_prefix (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x ++ List.ofFn y)
  rw [hr, getD_append_left' _ _ _ _ (by simp; omega)]

lemma val_point (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : i < P) :
    val P L C x y i = x ⟨i, hi⟩ := by
  rw [val_input P L C x y i (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; exact hi)]
  simp [hi]

lemma val_line (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : P ≤ i) (hi2 : i < P + L) :
    val P L C x y i = y ⟨i - P, by omega⟩ := by
  rw [val_input P L C x y i hi2]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; exact hi)]
  have h3 : i - (List.ofFn x).length < L := by simp; omega
  simp only [List.getElem?_ofFn, List.length_ofFn]
  simp [show i - P < L by omega]

lemma val_ge (x : Fin P → Bool) (y : Fin L → Bool) (i : ℕ) (hi : P + L + C.gates.length ≤ i) :
    val P L C x y i = false := by
  unfold val
  apply List.getD_eq_default
  rw [wires_eq, fw_length]; simp; omega

lemma val_gate (x : Fin P → Bool) (y : Fin L → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val P L C x y (P + L + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < P + L + j then val P L C x y i else false) := by
  have h := fw_getD_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates
    (List.ofFn x ++ List.ofFn y) j hj false
  simp only [List.length_append, List.length_ofFn] at h
  unfold val
  rw [wires_eq, h]
  simp only [getD_take']

end C

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A cross gate has two operands that both depend syntactically on a line.
def Cross (n m : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = .and ∧ (gateAt C j).inputs.length = 2 ∧
    ∀ i ∈ (gateAt C j).inputs, 0 < deg n m C i

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma reads {n m : ℕ} {C : Circuit} (hb : ReadsBack (n+m) C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ C.gates[j].inputs) : i < n+m+j :=
  hb _ hj _ (by rwa [gateAt_eq hj])

lemma original_step {n m : ℕ} {C : Circuit} (hb : ReadsBack (n+m) C)
    (x : Fin n → Bool) (y : Fin m → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val n m C x y (n+m+j) = C.gates[j].op.eval (C.gates[j].inputs.map (val n m C x y)) := by
  rw [val_gate n m C x y j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [reads hb hj hi]

lemma degree_zero_kids {n m : ℕ} {C : Circuit} (hm : Monotone2 C) (hb : ReadsBack (n+m) C)
    {j : ℕ} (hj : j < C.gates.length) (hd : deg n m C (n+m+j) = 0)
    {i : ℕ} (hi : i ∈ C.gates[j].inputs) : deg n m C i = 0 := by
  have hop := (hm _ (List.getElem_mem hj)).1
  have he : deg n m C i ∈ C.gates[j].inputs.map (fun a => if a < n+m+j then deg n m C a else 0) :=
    List.mem_map.mpr ⟨i, hi, if_pos (reads hb hj hi)⟩
  rcases hop with hop | hop
  · rw [deg_gate_and n m C j hj hop] at hd
    have := List.le_sum_of_mem he
    omega
  · rw [deg_gate_or n m C j hj hop] at hd
    have max_le (l : List ℕ) (v : ℕ) (h : v ∈ l) : v ≤ l.foldr max 0 := by
      induction l with
      | nil => simp at h
      | cons a l ih =>
        simp only [List.foldr_cons]
        rcases List.mem_cons.mp h with h | h
        · subst v; exact le_max_left _ _
        · exact (ih h).trans (le_max_right _ _)
    have := max_le _ _ he
    omega

lemma pure_value {n m : ℕ} {C : Circuit} (hm : Monotone2 C) (hb : ReadsBack (n+m) C)
    (x : Fin n → Bool) (y z : Fin m → Bool) (w : ℕ) (hd : deg n m C w = 0) :
    val n m C x y w = val n m C x z w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hp : w < n
    · rw [val_point n m C x y w hp, val_point n m C x z w hp]
    by_cases hl : w < n+m
    · rw [deg_line n m C w (by omega) hl] at hd; contradiction
    by_cases hg : w < n+m+C.gates.length
    · let j := w-(n+m)
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hw : w = n+m+j := by dsimp [j]; omega
      rw [hw, original_step hb x y j hj, original_step hb x z j hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih _ (by rw [hw]; exact reads hb hj hi) (degree_zero_kids hm hb hj (hw ▸ hd) hi)
    · rw [val_ge n m C x y w (by omega), val_ge n m C x z w (by omega)]

def Env {m : ℕ} (Y : Finset (Fin m)) (f : (Fin m → Bool) → Bool) : Bool :=
  f (fun _ => false) || decide (∃ j ∈ Y, f (fun l => decide (l = j)) = true)

lemma env_const {m : ℕ} (Y : Finset (Fin m)) (b : Bool) : Env Y (fun _ => b) = b := by
  cases b <;> simp [Env]

lemma env_line {m : ℕ} (Y : Finset (Fin m)) (l : Fin m) :
    Env Y (fun y => y l) = decide (l ∈ Y) := by simp [Env]

lemma env_or {m : ℕ} (Y : Finset (Fin m)) (f g : (Fin m → Bool) → Bool) :
    Env Y (fun y => f y || g y) = (Env Y f || Env Y g) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Env, Bool.or_eq_true, decide_eq_true_eq]
  grind

lemma env_scale {m : ℕ} (Y : Finset (Fin m)) (c : Bool) (f : (Fin m → Bool) → Bool) :
    Env Y (fun y => c && f y) = (c && Env Y f) := by
  cases c <;> simp [Env]

lemma gate_kinds {C : Circuit} (hm : Monotone2 C) {j : ℕ} (hj : j < C.gates.length) :
    (C.gates[j].op = .and ∨ C.gates[j].op = .or) ∧
    (C.gates[j].inputs = [] ∨ (∃ a, C.gates[j].inputs = [a]) ∨
      ∃ a b, C.gates[j].inputs = [a,b]) := by
  obtain ⟨hop, hlen⟩ := hm _ (List.getElem_mem hj)
  refine ⟨hop, ?_⟩
  cases he : C.gates[j].inputs with
  | nil => simp
  | cons a l => cases l with
    | nil => simp
    | cons b l =>
      cases l with
      | nil => simp
      | cons c l => simp [he] at hlen

lemma and_pure_side {n m : ℕ} {C : Circuit} {j a b : ℕ} (hj : j < C.gates.length)
    (ho : C.gates[j].op = .and) (he : C.gates[j].inputs = [a,b]) (hc : ¬ Cross n m C j) :
    deg n m C a = 0 ∨ deg n m C b = 0 := by
  by_contra! hh
  have ca : 0 < deg n m C a := Nat.pos_of_ne_zero hh.1
  have cb : 0 < deg n m C b := Nat.pos_of_ne_zero hh.2
  exact hc (by simp [Cross, hj, gateAt_eq hj, ho, he, ca, cb])

-- Without cross gates the original circuit distributes over unions of singleton lines.
lemma no_cross_envelope {n m : ℕ} {C : Circuit} (hm : Monotone2 C) (hb : ReadsBack (n+m) C)
    (hc : ∀ j, ¬ Cross n m C j) (x : Fin n → Bool) (Y : Finset (Fin m)) (w : ℕ) :
    val n m C x (fun l => decide (l ∈ Y)) w = Env Y (fun y => val n m C x y w) := by
  let V := fun (w : ℕ) (y : Fin m → Bool) => val n m C x y w
  let yY := fun l => decide (l ∈ Y)
  change V w yY = Env Y (V w)
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hp : w < n
    · have hV : V w = fun _ => x ⟨w,hp⟩ := funext (fun y => val_point n m C x y w hp)
      simp [hV, env_const]
    by_cases hl : w < n+m
    · have hV : V w = fun y => y ⟨w-n, by omega⟩ := funext (fun y => val_line n m C x y w (by omega) hl)
      simp [hV, env_line, yY]
    by_cases hg : w < n+m+C.gates.length
    · let j := w-(n+m)
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hw : w = n+m+j := by dsimp [j]; omega
      have hv (y) : V w y = C.gates[j].op.eval (C.gates[j].inputs.map (fun i => V i y)) :=
        hw ▸ original_step hb x y j hj
      obtain ⟨hop, hshape⟩ := gate_kinds hm hj
      rcases hshape with he | ⟨a,he⟩ | ⟨a,b,he⟩
      · have eq : V w = fun _ => C.gates[j].op.eval [] := funext (fun y => by simpa [he] using hv y)
        simp [eq, env_const]
      · have ha : a < w := by rw [hw]; exact reads hb hj (by simp [he])
        have eq : V w = V a := funext (fun y => by rcases hop with h | h <;> simpa [he,h,GateOp.eval] using hv y)
        rw [eq]; exact ih _ ha
      · have ha : a < w := by rw [hw]; exact reads hb hj (by simp [he])
        have hb' : b < w := by rw [hw]; exact reads hb hj (by simp [he])
        rcases hop with h | h
        · have eq : V w = fun y => V a y && V b y := funext (fun y => by simpa [he,h,GateOp.eval] using hv y)
          rw [eq]
          rcases and_pure_side hj h he (hc j) with hd | hd
          · have e : V a = fun _ => V a (fun _ => false) := funext (fun y => pure_value hm hb x y _ a hd)
            rw [e, env_scale]
            exact congrArg (fun v => V a (fun _ => false) && v) (ih _ hb')
          · have e : V b = fun _ => V b (fun _ => false) := funext (fun y => pure_value hm hb x y _ b hd)
            conv_rhs => rw [e]; simp only [Bool.and_comm (V a _) _, env_scale]
            rw [e]
            exact (congrArg (fun v => v && V b (fun _ => false)) (ih _ ha)).trans (Bool.and_comm _ _)
        · have eq : V w = fun y => V a y || V b y := funext (fun y => by simpa [he,h,GateOp.eval] using hv y)
          rw [eq, env_or]
          exact congrArg₂ (fun u v => u || v) (ih _ ha) (ih _ hb')
    · have hV : V w = fun _ => false := funext (fun y => val_ge n m C x y w (by omega))
      simp [hV, env_const]

lemma bounded_ncard (N : ℕ) (S : Set ℕ) (hs : ∀ j ∈ S, j < N) : S.ncard ≤ N := by
  have sub : S ⊆ (Finset.range N : Set ℕ) := fun j hj => Finset.mem_range.mpr (hs j hj)
  simpa using Set.ncard_le_ncard sub (Finset.finite_toSet _)

lemma cross_finite {n m : ℕ} (C : Circuit) : {j | Cross n m C j}.Finite := by
  apply (Finset.range C.gates.length).finite_toSet.subset
  intro j hj
  exact Finset.mem_range.mpr hj.1

lemma no_cross_of_zero {n m : ℕ} {C : Circuit} (hc : {j | Cross n m C j}.ncard = 0) :
    ∀ j, ¬ Cross n m C j := by
  have he := (Set.ncard_eq_zero (cross_finite C)).mp hc
  intro j hj
  exact (Set.eq_empty_iff_forall_notMem.mp he) j hj

lemma zero_case {n m s k : ℕ} {C : Circuit} (hm : Monotone2 C) (hb : ReadsBack (n+m) C)
    (hs : C.size ≤ s) (hc : ∀ j, ¬ Cross n m C j) :
    ∃ M : Circuit, Monotone2 M ∧ ReadsBack (n+m) M ∧
      (∀ j < M.gates.length, (gateAt M j).op = .and → (gateAt M j).inputs.length = 2 →
        ∃ i ∈ (gateAt M j).inputs, deg n m M i = 0) ∧
      M.size ≤ (6*k+3)*s + 12*k^2*m + 7*k*m + 6*k^2 + 2*k ∧
      {j : ℕ | j < M.gates.length ∧ 0 < deg n m M (n+m+j)}.ncard ≤ s+k*(2*m+1) ∧
      ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), circuitFun (n+m) M (Fin.append x (fun l => decide (l ∈ Y))) =
        (circuitFun (n+m) C (Fin.append x (fun _ => false)) ||
          decide (∃ j ∈ Y, circuitFun (n+m) C (Fin.append x (fun l => decide (l = j))) = true)) := by
  refine ⟨C, hm, hb, ?_, ?_, ?_, ?_⟩
  · intro j hj ho hl
    by_contra! hh
    exact hc j ⟨hj, ho, hl, fun i hi => Nat.pos_of_ne_zero (hh i hi)⟩
  · calc C.size ≤ s := hs
         _ ≤ (6*k+3)*s + 12*k^2*m + 7*k*m + 6*k^2 + 2*k := by nlinarith
  · have hh := bounded_ncard C.gates.length {j : ℕ | j < C.gates.length ∧ 0 < deg n m C (n+m+j)} (fun _ h => h.1)
    change C.gates.length ≤ s at hs
    omega
  · intro x Y
    have h := Bool.eq_iff_iff.mp (no_cross_envelope hm hb hc x Y C.output)
    simp only [Env, Bool.or_eq_true, decide_eq_true_eq] at h
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    simpa only [circuitFun, Circuit.eval, List.ofFn_fin_append, val] using h

-- Point functions are computed before any gate that reads a marked input.
abbrev X (n : ℕ) := Fin n → Bool
abbrev Point (n : ℕ) := X n → Prop

def pzero {n : ℕ} : Point n := fun _ => False
def pone {n : ℕ} : Point n := fun _ => True
def pvar {n : ℕ} (i : Fin n) : Point n := fun x => x i = true
def por {n : ℕ} (a b : Point n) : Point n := fun x => a x ∨ b x
def pand {n : ℕ} (a b : Point n) : Point n := fun x => a x ∧ b x

def Av {n : ℕ} (ps : List (Point n)) (f : Point n) : Prop := f ∈ ps ∨ ∃ i, f = pvar i

inductive Recipe {n : ℕ} (ps : List (Point n)) : Point n → Prop where
  | zero : Recipe ps pzero
  | one : Recipe ps pone
  | join {a b} : Av ps a → Av ps b → Recipe ps (por a b)
  | meet {a b} : Av ps a → Av ps b → Recipe ps (pand a b)

inductive PureOK {n : ℕ} : List (Point n) → Prop where
  | nil : PureOK []
  | cons {ps f} : PureOK ps → Recipe ps f → PureOK (f :: ps)

structure Grow {n : ℕ} (ps qs : List (Point n)) (cost : ℕ) : Prop where
  avail : ∀ {f}, Av ps f → Av qs f
  ok : PureOK ps → PureOK qs
  size : qs.length ≤ ps.length + cost

lemma grow_id {n c : ℕ} (ps : List (Point n)) : Grow ps ps c :=
  ⟨fun h => h, id, by omega⟩

lemma Grow.chain {n a b c : ℕ} {ps qs rs : List (Point n)} (u : Grow ps qs a) (v : Grow qs rs b)
    (h : a+b ≤ c) : Grow ps rs c := ⟨fun e => v.avail (u.avail e), fun e => v.ok (u.ok e), by
  have := u.size; have := v.size; omega⟩

lemma emit {n : ℕ} {ps : List (Point n)} {f : Point n} (r : Recipe ps f) :
    ∃ qs, Grow ps qs 1 ∧ Av qs f := by
  refine ⟨f::ps, ⟨?_, fun h => .cons h r, by simp⟩, Or.inl (by simp)⟩
  intro g hg
  rcases hg with h | h
  · exact Or.inl (List.mem_cons_of_mem _ h)
  · exact Or.inr h

-- A mixed gate joins two marked registers, adds a point function, or scales by one.
inductive MOp (n : ℕ) where
  | join (u v : ℕ)
  | shift (u : ℕ) (p : Point n)
  | scale (u : ℕ) (p : Point n)

def MOp.ok {n : ℕ} (ps : List (Point n)) (N : ℕ) : MOp n → Prop
  | .join a b => a < N ∧ b < N
  | .shift a p | .scale a p => a < N ∧ Av ps p

def MOp.value {n : ℕ} (hom : Bool) (x : X n) (s : ℕ → Prop) : MOp n → Prop
  | .join a b => s a ∨ s b
  | .shift a p => if hom then s a else s a ∨ p x
  | .scale a p => s a ∧ p x

def mrun {n : ℕ} (m : ℕ) (hom : Bool) (x : X n) (init : ℕ → Prop) : List (MOp n) → ℕ → Prop
  | [] => init
  | op::gs => Function.update (mrun m hom x init gs) (m+gs.length)
      (op.value hom x (mrun m hom x init gs))

def lineIn {m : ℕ} (Y : Finset (Fin m)) (w : ℕ) : Prop := ∃ l ∈ Y, w = l.val

def MOK {n : ℕ} (m : ℕ) (ps : List (Point n)) : List (MOp n) → Prop
  | [] => True
  | op::gs => MOK m ps gs ∧ op.ok ps (m+gs.length)

lemma MOp.ok_grow {n m c : ℕ} {ps qs : List (Point n)} (h : Grow ps qs c) {op : MOp n}
    (ho : op.ok ps m) : op.ok qs m := by
  cases op with
  | join a b => exact ho
  | shift a p => exact ⟨ho.1, h.avail ho.2⟩
  | scale a p => exact ⟨ho.1, h.avail ho.2⟩

lemma mok_grow {n m c : ℕ} {ps qs : List (Point n)} (h : Grow ps qs c) {gs : List (MOp n)}
    (ho : MOK m ps gs) : MOK m qs gs := by
  induction gs with
  | nil => trivial
  | cons a gs ih => exact ⟨ih ho.1, a.ok_grow h ho.2⟩

lemma mixed_linear {n : ℕ} (m : ℕ) (x : X n) (source : ℕ → Prop) (gs : List (MOp n)) (w : ℕ) :
    mrun m false x source gs w ↔ mrun m false x (fun _ => False) gs w ∨ mrun m true x source gs w := by
  induction gs generalizing w with
  | nil => simp [mrun]
  | cons op gs ih =>
    by_cases he : w = m+gs.length
    · subst w
      simp only [mrun, Function.update_self]
      cases op with
      | join a b => simp only [MOp.value, ih]; tauto
      | shift a p => simp only [MOp.value, Bool.false_eq_true, ite_false, ite_true, ih]; tauto
      | scale a p => simp only [MOp.value, ih]; tauto
    · simpa only [mrun, Function.update_of_ne he] using ih w

inductive Ref (n : ℕ) where
  | pure (f : Point n)
  | mixed (i : ℕ)

def Ref.ok {n : ℕ} (ps : List (Point n)) (N : ℕ) : Ref n → Prop
  | .pure f => Av ps f
  | .mixed i => i < N

def Ref.val {n m : ℕ} (gs : List (MOp n)) (x : X n) (Y : Finset (Fin m)) : Ref n → Prop
  | .pure f => f x
  | .mixed i => mrun m false x (lineIn Y) gs i

lemma Ref.weaken {n N T c : ℕ} {ps qs : List (Point n)} {r : Ref n} (u : Grow ps qs c)
    (h : N ≤ T) (hr : r.ok ps N) : r.ok qs T := by
  cases r with
  | pure f => exact u.avail hr
  | mixed i => exact Nat.lt_of_lt_of_le hr h

lemma mrun_cons_old {n m : ℕ} (op : MOp n) (gs : List (MOp n)) (x : X n) (init : ℕ → Prop)
    (hom : Bool) {w : ℕ} (hw : w < m+gs.length) :
    mrun m hom x init (op::gs) w = mrun m hom x init gs w := by
  simp [mrun, Function.update_of_ne (Nat.ne_of_lt hw)]

lemma mrun_suffix {n m : ℕ} (new old : List (MOp n)) (x : X n) (init : ℕ → Prop)
    {w : ℕ} (hw : w < m+old.length) : mrun m false x init (new++old) w = mrun m false x init old w := by
  induction new with
  | nil => rfl
  | cons op new ih => rw [List.cons_append, mrun_cons_old, ih]; simp; omega

lemma Ref.stable {n m : ℕ} {ps : List (Point n)} {r : Ref n} {old : List (MOp n)}
    (hr : r.ok ps (m+old.length)) (new : List (MOp n)) (x : X n) (Y : Finset (Fin m)) :
    r.val (new++old) x Y = r.val old x Y := by
  cases r with
  | pure f => rfl
  | mixed i => exact mrun_suffix new old x _ hr

def MOp.edge {n : ℕ} (x : X n) (w : ℕ) : MOp n → Prop
  | .join a b => w = a ∨ w = b
  | .shift a _ => w = a
  | .scale a p => w = a ∧ p x

lemma hom_edges {n : ℕ} (op : MOp n) (x : X n) (s : ℕ → Prop) :
    op.value true x s ↔ ∃ w, op.edge x w ∧ s w := by
  cases op with
  | join a b => simp [MOp.value, MOp.edge, or_and_right, exists_or]
  | shift a p => simp [MOp.value, MOp.edge]
  | scale a p => simp [MOp.value, MOp.edge, and_assoc, and_comm]

-- Move a demand from a gate output to its operands in reverse evaluation order.
def pull {n : ℕ} (dst : ℕ) (op : MOp n) (d : ℕ → Point n) (w : ℕ) : Point n :=
  fun x => (w ≠ dst ∧ d w x) ∨ (d dst x ∧ op.edge x w)

lemma reverse_step {n : ℕ} (dst : ℕ) (op : MOp n) (d : ℕ → Point n) (x : X n) (s : ℕ → Prop) :
    (∃ w, d w x ∧ Function.update s dst (op.value true x s) w) ↔ ∃ w, pull dst op d w x ∧ s w := by
  constructor
  · rintro ⟨w, hd, hw⟩
    by_cases he : w = dst
    · subst w
      rw [Function.update_self] at hw
      obtain ⟨a,ha,hs⟩ := (hom_edges op x s).mp hw
      exact ⟨a,Or.inr ⟨hd,ha⟩,hs⟩
    · exact ⟨w,Or.inl ⟨he,hd⟩,by simpa [Function.update_of_ne he] using hw⟩
  · rintro ⟨w,(⟨he,hd⟩ | ⟨hd,ha⟩),hw⟩
    · exact ⟨w,hd,by simpa [Function.update_of_ne he] using hw⟩
    · exact ⟨dst,hd,by simpa using (hom_edges op x s).mpr ⟨w,ha,hw⟩⟩

def dropDemand {n : ℕ} (dst : ℕ) (d : ℕ → Point n) (w : ℕ) : Point n :=
  if w = dst then pzero else d w

def deposit {n : ℕ} (d : ℕ → Point n) (i : ℕ) (p : Point n) (w : ℕ) : Point n :=
  if w = i then por (d i) p else d w

lemma deposit_get {n : ℕ} (d : ℕ → Point n) (i : ℕ) (p : Point n) (w : ℕ) (x : X n) :
    deposit d i p w x ↔ d w x ∨ (w = i ∧ p x) := by
  by_cases hw : w = i <;> simp [deposit, hw, por]

lemma drop_get {n : ℕ} (dst : ℕ) (d : ℕ → Point n) (w : ℕ) (x : X n) :
    dropDemand dst d w x ↔ w ≠ dst ∧ d w x := by by_cases h : w = dst <;> simp [dropDemand, h, pzero]

lemma deposit_av {n : ℕ} (ps : List (Point n)) (d : ℕ → Point n) (i : ℕ) (p : Point n)
    (hd : ∀ w, Av ps (d w)) (hp : Av ps p) : ∃ qs, Grow ps qs 1 ∧ ∀ w, Av qs (deposit d i p w) := by
  obtain ⟨qs,gr,ha⟩ := emit (Recipe.join (hd i) hp)
  refine ⟨qs,gr,fun w => ?_⟩
  by_cases h : w = i
  · simpa only [deposit, if_pos h] using ha
  · simpa only [deposit, if_neg h] using gr.avail (hd w)

lemma pull_av {n : ℕ} (ps : List (Point n)) (d : ℕ → Point n) (dst : ℕ) (op : MOp n)
    (hd : ∀ w, Av ps (d w)) (hz : Av ps pzero) (ho : op.ok ps dst) :
    ∃ qs, Grow ps qs 2 ∧ ∀ w, Av qs (pull dst op d w) := by
  let q := dropDemand dst d
  have hq (w) : Av ps (q w) := by
    dsimp [q, dropDemand]
    split <;> first | exact hz | exact hd _
  cases op with
  | join a b =>
    obtain ⟨ps₁,g₁,t₁⟩ := deposit_av ps q a (d dst) hq (hd _)
    obtain ⟨ps₂,g₂,t₂⟩ := deposit_av ps₁ _ b (d dst) t₁ (g₁.avail (hd _))
    refine ⟨ps₂,g₁.chain g₂ (by omega),fun w => ?_⟩
    have e : pull dst (.join a b) d w = deposit (deposit q a (d dst)) b (d dst) w := by
      funext x; apply propext
      simp only [pull, MOp.edge, deposit_get, q, drop_get]; tauto
    exact e ▸ t₂ w
  | shift a p =>
    obtain ⟨ps₁,g₁,t₁⟩ := deposit_av ps q a (d dst) hq (hd _)
    refine ⟨ps₁,g₁.chain (grow_id (c:=0) _) (by omega),fun w => ?_⟩
    have e : pull dst (.shift a p) d w = deposit q a (d dst) w := by
      funext x; apply propext
      simp only [pull, MOp.edge, deposit_get, q, drop_get]; tauto
    exact e ▸ t₁ w
  | scale a p =>
    obtain ⟨ps₁,g₁,t₁⟩ := emit (Recipe.meet (hd dst) ho.2)
    obtain ⟨ps₂,g₂,t₂⟩ := deposit_av ps₁ q a _ (fun w => g₁.avail (hq w)) t₁
    refine ⟨ps₂,g₁.chain g₂ (by omega),fun w => ?_⟩
    have e : pull dst (.scale a p) d w = deposit q a (pand (d dst) p) w := by
      funext x; apply propext
      simp only [pull, MOp.edge, deposit_get, q, drop_get, pand]; tauto
    exact e ▸ t₂ w

lemma transpose_make {n m : ℕ} (gs : List (MOp n)) (ps : List (Point n)) (d : ℕ → Point n)
    (hd : ∀ w, Av ps (d w)) (hz : Av ps pzero) (hok : MOK m ps gs) :
    ∃ (qs : List (Point n)) (q : ℕ → Point n), Grow ps qs (2*gs.length) ∧ (∀ w, Av qs (q w)) ∧
      ∀ (x : X n) (s : ℕ → Prop), (∃ w, d w x ∧ mrun m true x s gs w) ↔ ∃ w, q w x ∧ s w := by
  induction gs generalizing ps d with
  | nil => exact ⟨ps,d,grow_id _,hd,fun _ _ => Iff.rfl⟩
  | cons op gs ih =>
    obtain ⟨t,g₁,hq⟩ := pull_av ps d _ op hd hz hok.2
    obtain ⟨qs,q,g₂,ha,hs⟩ := ih t _ hq (g₁.avail hz) (mok_grow g₁ hok.1)
    refine ⟨qs,q,g₁.chain g₂ (by simp; omega),ha,fun x s => ?_⟩
    exact (reverse_step (m+gs.length) op d x (mrun m true x s gs)).trans (hs x s)

-- Each backward pass produces all singleton coefficients using at most two point gates per mixed gate.
lemma coefficients {n m : ℕ} (gs : List (MOp n)) (ps : List (Point n)) (r : Ref n)
    (hz : Av ps pzero) (ht : Av ps pone) (hok : MOK m ps gs) :
    ∃ (qs : List (Point n)) (f : Fin m → Point n), Grow ps qs (2*gs.length) ∧ (∀ l, Av qs (f l)) ∧
      ∀ (x : X n) (l : Fin m), r.val gs x {l} ↔ r.val gs x (∅ : Finset (Fin m)) ∨ f l x := by
  cases r with
  | pure p => exact ⟨ps,fun _ => pzero,grow_id _,fun _ => hz,fun _ _ => by simp [Ref.val,pzero]⟩
  | mixed i =>
    let d := fun w => if w = i then (pone : Point n) else pzero
    have had (w) : Av ps (d w) := by dsimp [d]; split <;> assumption
    obtain ⟨qs,q,g,hq,hs⟩ := transpose_make gs ps d had hz hok
    refine ⟨qs,fun l => q l.val,g,fun l => hq l.val,fun x l => ?_⟩
    have hd (w) : d w x ↔ w = i := by by_cases h : w = i <;> simp [d,h,pone,pzero]
    have base : lineIn (∅ : Finset (Fin m)) = fun _ => False := by funext w; simp [lineIn]
    have single (w) : lineIn {l} w ↔ w = l.val := by simp [lineIn]
    have dual := hs x (lineIn {l})
    simp only [hd, single, exists_eq_left, exists_eq_right_right] at dual
    change mrun m false x (lineIn {l}) gs i ↔ mrun m false x (lineIn ∅) gs i ∨ q l.val x
    rw [base, mixed_linear m x (lineIn {l}) gs i]
    apply or_congr Iff.rfl
    exact dual.trans (by simp)

abbrev circ (gs : List Gate) : Circuit := ⟨gs,0⟩
abbrev gd (n m : ℕ) (gs : List Gate) := deg n m (circ gs)
def bit {n m : ℕ} (gs : List Gate) (w : ℕ) (x : X n) (Y : Finset (Fin m)) : Prop :=
  val n m (circ gs) x (fun l => decide (l ∈ Y)) w = true

lemma gd_old {n m : ℕ} (gs ts : List Gate) {w : ℕ} (hw : w < n+m+gs.length) :
    gd n m (gs++ts) w = gd n m gs w := by
  unfold gd deg
  rw [lineDegrees_eq, lineDegrees_eq]
  change (fw _ (gs++ts) _).getD w 0 = (fw _ gs _).getD w 0
  rw [fw_append]
  obtain ⟨r,hr⟩ := fw_prefix (fun d g => g.lineDegree d) ts
    (fw (fun d g => g.lineDegree d) gs ((List.range (n+m)).map fun i => if i ∈ Finset.Ico n (n+m) then 1 else 0))
  rw [hr, getD_append_left' _ _ _ _ (by rw [fw_length]; simpa using hw)]

lemma raw_old {n m : ℕ} (gs ts : List Gate) (x : X n) (y : Fin m → Bool) {w : ℕ}
    (hw : w < n+m+gs.length) : val n m (circ (gs++ts)) x y w = val n m (circ gs) x y w := by
  unfold val
  rw [wires_eq, wires_eq]
  let f := fun (v : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => v.getD i false)
  change (fw f (gs++ts) _).getD w false = (fw f gs _).getD w false
  rw [fw_append]
  obtain ⟨r,hr⟩ := fw_prefix f ts (fw f gs (List.ofFn x ++ List.ofFn y))
  rw [hr, getD_append_left' _ _ _ _ (by rw [fw_length]; simpa using hw)]

structure Well (n m : ℕ) (gs : List Gate) : Prop where
  mono : Monotone2 (circ gs)
  back : ReadsBack (n+m) (circ gs)
  safe : ∀ j (hj : j < gs.length), gs[j].op = .and → gs[j].inputs.length = 2 →
    ∃ i ∈ gs[j].inputs, gd n m gs i = 0

inductive Prim where
  | zero | one | join (a b : ℕ) | meet (a b : ℕ)

def Prim.gate : Prim → Gate
  | .zero => ⟨.or,[]⟩ | .one => ⟨.and,[]⟩ | .join a b => ⟨.or,[a,b]⟩ | .meet a b => ⟨.and,[a,b]⟩

def Prim.safe (D : ℕ → ℕ) : Prim → Prop
  | .meet a b => D a = 0 ∨ D b = 0
  | _ => True

def Prim.val (v : ℕ → Prop) : Prim → Prop
  | .zero => False | .one => True | .join a b => v a ∨ v b | .meet a b => v a ∧ v b

lemma well_nil (n m : ℕ) : Well n m [] := by
  refine ⟨?_,?_,?_⟩
  · intro g h; simp [circ] at h
  · intro j hj; simp [circ] at hj
  · intro j hj; simp at hj

lemma well_emit {n m : ℕ} {gs : List Gate} (old : Well n m gs) (p : Prim)
    (hb : ∀ w ∈ p.gate.inputs, w < n+m+gs.length) (hs : p.safe (gd n m gs)) : Well n m (gs++[p.gate]) := by
  have hnew : ∀ {j : ℕ} (hj : j < (gs++[p.gate]).length), j < gs.length ∨ j = gs.length := by simp; omega
  refine ⟨?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact old.mono g h
    · have he := List.mem_singleton.mp h
      subst g
      cases p <;> simp [Prim.gate]
  · intro j hj w hw
    rw [gateAt_eq hj] at hw
    change w ∈ (gs++[p.gate])[j].inputs at hw
    rcases hnew hj with he | he
    · rw [List.getElem_append_left he] at hw
      exact reads old.back he hw
    · subst j
      simp at hw
      exact hb _ hw
  · intro j hj ho hl
    rcases hnew hj with he | he
    · rw [List.getElem_append_left he] at ho hl ⊢
      obtain ⟨i,hi,hd⟩ := old.safe j he ho hl
      exact ⟨i,hi,(gd_old gs _ (lt_of_lt_of_le (reads old.back he hi) (by omega))).trans hd⟩
    · subst j
      simp at ho hl ⊢
      have get (i) (hi : i ∈ p.gate.inputs) := gd_old gs [p.gate] (hb i hi)
      cases p with
      | zero => simp [Prim.gate] at ho
      | one => simp [Prim.gate] at hl
      | join a b => simp [Prim.gate] at ho
      | meet a b =>
        rcases hs with h | h
        · exact ⟨a,by simp [Prim.gate],(get a (by simp [Prim.gate])).trans h⟩
        · exact ⟨b,by simp [Prim.gate],(get b (by simp [Prim.gate])).trans h⟩

lemma bit_emit {n m : ℕ} {gs : List Gate} (p : Prim) (well : Well n m (gs++[p.gate]))
    (hb : ∀ w ∈ p.gate.inputs, w < n+m+gs.length) (x : X n) (Y : Finset (Fin m)) :
    bit (gs++[p.gate]) (n+m+gs.length) x Y ↔ p.val (fun w => bit gs w x Y) := by
  let y := fun l => decide (l ∈ Y)
  have hj : gs.length < (circ (gs++[p.gate])).gates.length := by simp [circ]
  have hv := original_step well.back x y gs.length hj
  have hg : (circ (gs++[p.gate])).gates[gs.length] = p.gate := by simp [circ]
  rw [hg] at hv
  have emap : p.gate.inputs.map (val n m (circ (gs++[p.gate])) x y) = p.gate.inputs.map (val n m (circ gs) x y) :=
    List.map_congr_left (fun i hi => raw_old gs [p.gate] x y (hb i hi))
  change val n m (circ (gs++[p.gate])) x y (n+m+gs.length) = true ↔ _
  rw [hv, emap]
  cases p <;> simp [Prim.gate, Prim.val, GateOp.eval, bit, y]

lemma zero_emit {n m : ℕ} {gs : List Gate} (p : Prim)
    (hb : ∀ w ∈ p.gate.inputs, w < n+m+gs.length) (hd : ∀ w ∈ p.gate.inputs, gd n m gs w = 0) :
    gd n m (gs++[p.gate]) (n+m+gs.length) = 0 := by
  let D := circ (gs++[p.gate])
  have hj : gs.length < D.gates.length := by simp [D,circ]
  have hg : D.gates[gs.length] = p.gate := by simp [D,circ]
  have e (w) (hw : w ∈ p.gate.inputs) :
      (if w < n+m+gs.length then deg n m D w else 0) = 0 := by
    rw [if_pos (hb w hw)]; exact (gd_old gs [p.gate] (hb w hw)).trans (hd w hw)
  have emap : p.gate.inputs.map (fun w => if w < n+m+gs.length then deg n m D w else 0) =
      p.gate.inputs.map (fun _ => 0) := List.map_congr_left e
  change deg n m D (n+m+gs.length) = 0
  have hand (ho : p.gate.op = .and) := deg_gate_and n m D gs.length hj (hg ▸ ho)
  have hor (ho : p.gate.op = .or) := deg_gate_or n m D gs.length hj (hg ▸ ho)
  cases p with
  | zero => rw [hor rfl,hg,emap]; rfl
  | one => rw [hand rfl,hg,emap]; rfl
  | join a b => rw [hor rfl,hg,emap]; rfl
  | meet a b => rw [hand rfl,hg,emap]; rfl

abbrev Full (n m : ℕ) := X n → Finset (Fin m) → Prop
abbrev Wire {n m : ℕ} (gs : List Gate) (w : ℕ) (F : Full n m) : Prop :=
  w < n+m+gs.length ∧ ∀ x Y, bit gs w x Y ↔ F x Y

def PLoc (m : ℕ) {n : ℕ} (gs : List Gate) (p : Point n) : Prop :=
  ∃ w, gd n m gs w = 0 ∧ Wire gs w (fun x (_ : Finset (Fin m)) => p x)

lemma wire_old {n m : ℕ} {gs : List Gate} {w : ℕ} {F : Full n m} (h : Wire gs w F) (ts : List Gate) :
    Wire (gs++ts) w F := by
  refine ⟨by simp; have := h.1; omega,fun x Y => ?_⟩
  unfold bit
  rw [raw_old gs ts _ _ h.1]
  exact h.2 x Y

lemma ploc_old {n m : ℕ} {gs : List Gate} {p : Point n} (h : PLoc m gs p) (ts : List Gate) : PLoc m (gs++ts) p := by
  obtain ⟨w,hz,hw⟩ := h
  exact ⟨w,(gd_old gs ts hw.1).trans hz,wire_old hw ts⟩

lemma phys_point {n m : ℕ} (gs : List Gate) (i : Fin n) : PLoc m gs (pvar i) := by
  refine ⟨i.val,deg_point n m _ i.val i.isLt,by have := i.isLt; omega,fun x Y => ?_⟩
  simp [bit, val_point n m _ x _ i.val i.isLt, pvar]

lemma phys_line {n m : ℕ} (gs : List Gate) (l : Fin m) :
    Wire gs (n+l.val) (fun (_ : X n) (Y : Finset (Fin m)) => l ∈ Y) := by
  refine ⟨by have := l.isLt; omega,fun x Y => ?_⟩
  simp [bit, val_line n m _ x _ (n+l.val) (by omega) (by have := l.isLt; omega)]

lemma prim_safe_pure {n m : ℕ} {gs : List Gate} {p : Prim} (h : ∀ i ∈ p.gate.inputs, gd n m gs i = 0) :
    p.safe (gd n m gs) := by
  cases p with
  | meet a b => exact Or.inl (h a (by simp [Prim.gate]))
  | _ => trivial

lemma recipe_code {n m : ℕ} {ps : List (Point n)} {gs : List Gate} {f : Point n}
    (loc : ∀ p, Av ps p → PLoc m gs p) (r : Recipe ps f) :
    ∃ p : Prim, (∀ i ∈ p.gate.inputs, i < n+m+gs.length) ∧ (∀ i ∈ p.gate.inputs, gd n m gs i = 0) ∧
      ∀ x (Y : Finset (Fin m)), p.val (fun i => bit gs i x Y) ↔ f x := by
  cases r with
  | zero => exact ⟨.zero,by simp [Prim.gate],by simp [Prim.gate],fun _ _ => Iff.rfl⟩
  | one => exact ⟨.one,by simp [Prim.gate],by simp [Prim.gate],fun _ _ => Iff.rfl⟩
  | join ha hb =>
    obtain ⟨a,da,va⟩ := loc _ ha
    obtain ⟨b,db,vb⟩ := loc _ hb
    exact ⟨.join a b,by simp [Prim.gate,va.1,vb.1],by simp [Prim.gate,da,db],
      fun x Y => or_congr (va.2 x Y) (vb.2 x Y)⟩
  | meet ha hb =>
    obtain ⟨a,da,va⟩ := loc _ ha
    obtain ⟨b,db,vb⟩ := loc _ hb
    exact ⟨.meet a b,by simp [Prim.gate,va.1,vb.1],by simp [Prim.gate,da,db],
      fun x Y => and_congr (va.2 x Y) (vb.2 x Y)⟩

-- Lay out all point gates first, leaving the original line inputs at their assigned indices.
lemma realize_pure {n : ℕ} (m : ℕ) {ps : List (Point n)} (ok : PureOK ps) :
    ∃ gs : List Gate, Well n m gs ∧ gs.length = ps.length ∧
      (∀ j < gs.length, gd n m gs (n+m+j) = 0) ∧ ∀ p, Av ps p → PLoc m gs p := by
  induction ok with
  | nil =>
    refine ⟨[],well_nil _ _,rfl,by simp,fun f hf => ?_⟩
    rcases hf with h | ⟨i,rfl⟩
    · simp at h
    · exact phys_point _ i
  | @cons ps f _ recipe ih =>
    obtain ⟨gs,old,glen,prior,loc⟩ := ih
    obtain ⟨p,hb,hd,hv⟩ := recipe_code loc recipe
    have well := well_emit old p hb (prim_safe_pure hd)
    have hz := zero_emit p hb hd
    refine ⟨gs++[p.gate],well,by simp [glen],?_,fun a ha => ?_⟩
    · intro j hj
      simp at hj
      rcases Nat.lt_or_eq_of_le hj with h | rfl
      · rw [gd_old _ _ (by omega)]; exact prior j h
      · exact hz
    · rcases ha with ha | ha
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨n+m+gs.length,hz,by simp,fun x Y => (bit_emit p well hb x Y).trans (hv x Y)⟩
        · exact ploc_old (loc _ (Or.inl ha)) _
      · exact ploc_old (loc _ (Or.inr ha)) _

lemma op_code {n m N : ℕ} {ps : List (Point n)} {gs : List Gate} {op : MOp n} (ho : op.ok ps N)
    (v : ℕ → Full n m) (pureLoc : ∀ p, Av ps p → PLoc m gs p)
    (regLoc : ∀ i < N, ∃ w, Wire gs w (v i)) :
    ∃ p : Prim, (∀ i ∈ p.gate.inputs, i < n+m+gs.length) ∧ p.safe (gd n m gs) ∧
      ∀ x (Y : Finset (Fin m)), p.val (fun i => bit gs i x Y) ↔ op.value false x (fun i => v i x Y) := by
  cases op with
  | join i j =>
    obtain ⟨a,va⟩ := regLoc i ho.1
    obtain ⟨b,vb⟩ := regLoc j ho.2
    exact ⟨.join a b,by simp [Prim.gate,va.1,vb.1],trivial,fun x Y => or_congr (va.2 x Y) (vb.2 x Y)⟩
  | shift i p =>
    obtain ⟨a,va⟩ := regLoc i ho.1
    obtain ⟨b,db,vb⟩ := pureLoc p ho.2
    exact ⟨.join a b,by simp [Prim.gate,va.1,vb.1],trivial,fun x Y => or_congr (va.2 x Y) (vb.2 x Y)⟩
  | scale i p =>
    obtain ⟨a,va⟩ := regLoc i ho.1
    obtain ⟨b,db,vb⟩ := pureLoc p ho.2
    exact ⟨.meet a b,by simp [Prim.gate,va.1,vb.1],Or.inr db,fun x Y => and_congr (va.2 x Y) (vb.2 x Y)⟩

-- Append the mixed gates in evaluation order. Each mixed AND has a point operand.
lemma realize_mix {n m : ℕ} {ps : List (Point n)} (pureG : List Gate) (initial : Well n m pureG)
    (pl : ∀ p, Av ps p → PLoc m pureG p) (ops : List (MOp n)) (ok : MOK m ps ops) :
    ∃ more : List Gate, more.length = ops.length ∧ Well n m (pureG++more) ∧
      ∀ i < m+ops.length, ∃ w, Wire (pureG++more) w
        (fun (x : X n) (Y : Finset (Fin m)) => mrun m false x (lineIn Y) ops i) := by
  induction ops with
  | nil =>
    refine ⟨[],rfl,by simpa using initial,fun i hi => ?_⟩
    have hil : i < m := by simpa using hi
    let l : Fin m := ⟨i,hil⟩
    have h := phys_line (n:=n) pureG l
    refine ⟨n+i,by simpa [l] using h.1,fun x Y => ?_⟩
    simp only [List.append_nil,mrun]
    apply (h.2 x Y).trans
    constructor
    · intro hh; exact ⟨l,hh,rfl⟩
    · rintro ⟨v,hv,eq⟩
      have : l = v := Fin.ext eq
      exact this.symm ▸ hv
  | cons op ops ih =>
    obtain ⟨prev,hlen,well,rl⟩ := ih ok.1
    let G := pureG++prev
    let V := fun i (x : X n) (Y : Finset (Fin m)) => mrun m false x (lineIn Y) ops i
    obtain ⟨p,hb,hs,hv⟩ := op_code ok.2 V (fun a ha => ploc_old (pl a ha) prev) rl
    have well' := well_emit well p hb hs
    refine ⟨prev++[p.gate],by simp [hlen],by simpa [List.append_assoc] using well',fun i hi => ?_⟩
    have he : i < m+ops.length ∨ i = m+ops.length := by simp at hi; omega
    rcases he with he | rfl
    · obtain ⟨w,hw⟩ := rl i he
      have h := wire_old hw [p.gate]
      refine ⟨w,by simpa [List.append_assoc] using h.1,fun x Y => ?_⟩
      simp only [mrun_cons_old _ _ _ _ _ he]
      simpa [List.append_assoc] using h.2 x Y
    · refine ⟨n+m+G.length,?_,fun x Y => ?_⟩
      · simp [G]
      · simp only [mrun,Function.update_self]
        exact (by simpa only [List.append_assoc] using (bit_emit p well' hb x Y).trans (hv x Y))

lemma physical {n m : ℕ} {ps : List (Point n)} {ops : List (MOp n)} (hp : PureOK ps) (ho : MOK m ps ops)
    (r : Ref n) (hr : r.ok ps (m+ops.length)) :
    ∃ (gs : List Gate) (w : ℕ), Well n m gs ∧ gs.length = ps.length+ops.length ∧
      {j : ℕ | j < gs.length ∧ 0 < gd n m gs (n+m+j)}.ncard ≤ ops.length ∧
      Wire gs w (fun x (Y : Finset (Fin m)) => r.val ops x Y) := by
  obtain ⟨pG,wp,plen,zeros,ploc⟩ := realize_pure m hp
  obtain ⟨more,mlen,wm,loc⟩ := realize_mix pG wp ploc ops ho
  have bound : {j : ℕ | j < (pG++more).length ∧ 0 < gd n m (pG++more) (n+m+j)}.ncard ≤ ops.length := by
    let I := Finset.Ico pG.length (pG.length+more.length)
    have sub : {j : ℕ | j < (pG++more).length ∧ 0 < gd n m (pG++more) (n+m+j)} ⊆ (I : Set ℕ) := by
      intro j hj
      obtain ⟨hj,hd⟩ := hj
      apply Finset.mem_Ico.mpr
      refine ⟨?_,by simpa using hj⟩
      by_contra! h
      rw [gd_old _ _ (by omega),zeros j h] at hd
      omega
    simpa [I,mlen] using Set.ncard_le_ncard sub I.finite_toSet
  have hw : ∃ w, Wire (pG++more) w (fun x (Y : Finset (Fin m)) => r.val ops x Y) := by
    cases r with
    | pure p => obtain ⟨w,_,h⟩ := ploc_old (ploc p hr) more; exact ⟨w,h⟩
    | mixed i => exact loc i hr
  obtain ⟨w,hw⟩ := hw
  exact ⟨pG++more,w,wm,by simp [plen,mlen],bound,hw⟩

structure Stage (n : ℕ) where
  ps : List (Point n)
  ops : List (MOp n)

def Stage.good {n : ℕ} (m : ℕ) (A : Stage n) : Prop :=
  PureOK A.ps ∧ MOK m A.ps A.ops ∧ Av A.ps pzero ∧ Av A.ps pone

def Stage.size {n : ℕ} (A : Stage n) := A.ps.length + A.ops.length

structure Ext {n : ℕ} (m : ℕ) (A B : Stage n) (total marked : ℕ) : Prop where
  avail : ∀ {p}, Av A.ps p → Av B.ps p
  more : ∃ ops, B.ops = ops++A.ops
  good : A.good m → B.good m
  totalCost : B.size ≤ A.size + total
  markedCost : B.ops.length ≤ A.ops.length + marked

lemma ext_id {n m t p : ℕ} (A : Stage n) : Ext m A A t p :=
  ⟨fun h => h,⟨[],rfl⟩,id,by omega,by omega⟩

lemma Ext.then_ {n m a b c d t p : ℕ} {A B D : Stage n} (u : Ext m A B a b) (v : Ext m B D c d)
    (ht : a+c ≤ t) (hp : b+d ≤ p) : Ext m A D t p := by
  obtain ⟨l,hl⟩ := u.more
  obtain ⟨k,hk⟩ := v.more
  exact ⟨fun e => v.avail (u.avail e),⟨k++l,by rw [hk,hl,List.append_assoc]⟩,fun e => v.good (u.good e),
    by have := u.totalCost; have := v.totalCost; omega,by have := u.markedCost; have := v.markedCost; omega⟩

lemma Ext.ref_ok {n m t p : ℕ} {A B : Stage n} (u : Ext m A B t p) {r : Ref n}
    (hr : r.ok A.ps (m+A.ops.length)) : r.ok B.ps (m+B.ops.length) := by
  obtain ⟨l,hl⟩ := u.more
  cases r with
  | pure f => exact u.avail hr
  | mixed i => change i < m + A.ops.length at hr; change i < m+B.ops.length; rw [hl,List.length_append]; omega

lemma Ext.ref_val {n m t p : ℕ} {A B : Stage n} (u : Ext m A B t p) {r : Ref n}
    (hr : r.ok A.ps (m+A.ops.length)) (x : X n) (Y : Finset (Fin m)) : r.val B.ops x Y = r.val A.ops x Y := by
  obtain ⟨l,hl⟩ := u.more
  rw [hl,Ref.stable hr]

lemma pure_ext {n m t : ℕ} (A : Stage n) {qs : List (Point n)} (gr : Grow A.ps qs t) :
    Ext m A ⟨qs,A.ops⟩ t 0 := by
  refine ⟨fun h => gr.avail h,⟨[],rfl⟩,fun hg => ⟨gr.ok hg.1,mok_grow gr hg.2.1,gr.avail hg.2.2.1,gr.avail hg.2.2.2⟩,?_,by simp⟩
  dsimp [Stage.size]; have := gr.size; omega

lemma add_pure {n m : ℕ} (A : Stage n) {f : Point n} (h : Recipe A.ps f) :
    ∃ B, Ext m A B 1 0 ∧ Av B.ps f := by
  obtain ⟨qs,gr,hf⟩ := emit h
  exact ⟨_,pure_ext A gr,hf⟩

lemma add_mix {n m : ℕ} (A : Stage n) (op : MOp n) (hok : op.ok A.ps (m+A.ops.length)) :
    ∃ (B : Stage n) (r : Ref n), Ext m A B 1 1 ∧ r.ok B.ps (m+B.ops.length) ∧
      ∀ (x : X n) (Y : Finset (Fin m)), r.val B.ops x Y ↔ op.value false x (mrun m false x (lineIn Y) A.ops) := by
  let B : Stage n := ⟨A.ps,op::A.ops⟩
  refine ⟨B,.mixed (m+A.ops.length),⟨fun h => h,⟨[op],rfl⟩,fun g => ⟨g.1,⟨g.2.1,hok⟩,g.2.2⟩,by simp [B,Stage.size,Nat.add_assoc],by simp [B]⟩,
    by simp [B,Ref.ok],fun x Y => ?_⟩
  simp [B,Ref.val,mrun]

def Ref.clean {n : ℕ} : Ref n → Prop | .pure _ => True | .mixed _ => False

def logic (useAnd : Bool) (a b : Prop) : Prop := if useAnd then a ∧ b else a ∨ b

def pointOp {n : ℕ} (useAnd : Bool) (p q : Point n) : Point n := fun x => logic useAnd (p x) (q x)

lemma scalar_recipe {n : ℕ} {ps : List (Point n)} (flag : Bool) {a b : Point n} (ha : Av ps a) (hb : Av ps b) :
    Recipe ps (pointOp flag a b) := by cases flag with | false => exact .join ha hb | true => exact .meet ha hb

lemma combinable {n m : ℕ} (A : Stage n) (flag : Bool) (a b : Ref n)
    (ha : a.ok A.ps (m+A.ops.length)) (hb : b.ok A.ps (m+A.ops.length))
    (allowed : flag = true → a.clean ∨ b.clean) :
    ∃ (B : Stage n) (r : Ref n), Ext m A B 1 1 ∧ r.ok B.ps (m+B.ops.length) ∧
      (a.clean ∧ b.clean → r.clean) ∧ ∀ (x : X n) (Y : Finset (Fin m)),
      r.val B.ops x Y ↔ logic flag (a.val A.ops x Y) (b.val A.ops x Y) := by
  cases a with
  | pure f =>
    cases b with
    | pure g =>
      obtain ⟨B,e,h⟩ := add_pure (m:=m) A (scalar_recipe flag ha hb)
      exact ⟨B,.pure _,e.then_ (ext_id (t:=0) (p:=0) _) (by omega) (by omega),h,fun _ => trivial,fun _ _ => Iff.rfl⟩
    | mixed i =>
      cases flag with
      | false =>
        obtain ⟨B,r,e,h,v⟩ := add_mix A (.shift i f) ⟨hb,ha⟩
        exact ⟨B,r,e,h,fun h => h.2.elim,fun x Y => (v x Y).trans or_comm⟩
      | true =>
        obtain ⟨B,r,e,h,v⟩ := add_mix A (.scale i f) ⟨hb,ha⟩
        exact ⟨B,r,e,h,fun h => h.2.elim,fun x Y => (v x Y).trans and_comm⟩
  | mixed i =>
    cases b with
    | pure f =>
      cases flag with
      | false =>
        obtain ⟨B,r,e,h,v⟩ := add_mix A (.shift i f) ⟨ha,hb⟩
        exact ⟨B,r,e,h,fun h => h.1.elim,v⟩
      | true =>
        obtain ⟨B,r,e,h,v⟩ := add_mix A (.scale i f) ⟨ha,hb⟩
        exact ⟨B,r,e,h,fun h => h.1.elim,v⟩
    | mixed j =>
      cases flag with
      | true => rcases allowed rfl with h | h <;> exact h.elim
      | false =>
        obtain ⟨B,r,e,h,v⟩ := add_mix A (.join i j) ⟨ha,hb⟩
        exact ⟨B,r,e,h,fun h => h.1.elim,v⟩

lemma make_row_products {n m : ℕ} (L : List (Fin m)) (A : Stage n) (a b : Point n)
    (fa fb : Fin m → Point n) (ha : Av A.ps a) (hb : Av A.ps b) (hfa : ∀ l, Av A.ps (fa l))
    (hfb : ∀ l, Av A.ps (fb l)) : ∃ B, Ext m A B (3*L.length) 0 ∧
      ∀ l ∈ L, Av B.ps (pand (por a (fa l)) (por b (fb l))) := by
  induction L with
  | nil => exact ⟨A,ext_id A,by simp⟩
  | cons l L ih =>
    obtain ⟨B,e,past⟩ := ih
    obtain ⟨D,u,ha'⟩ := add_pure (m:=m) B (.join (e.avail ha) (e.avail (hfa l)))
    obtain ⟨E,v,hb'⟩ := add_pure (m:=m) D (.join (u.avail (e.avail hb)) (u.avail (e.avail (hfb l))))
    obtain ⟨F,w,prod⟩ := add_pure (m:=m) E (.meet (v.avail ha') hb')
    have step : Ext m B F 3 0 := (u.then_ v (t:=2) (p:=0) (by omega) (by omega)).then_ w (by omega) (by omega)
    refine ⟨F,e.then_ step (by simp; omega) (by omega),fun j hj => ?_⟩
    rcases List.mem_cons.mp hj with rfl | h
    · exact prod
    · exact step.avail (past j h)

-- Activate a point function for each selected line and take the disjunction with the baseline.
lemma mux {n m : ℕ} (L : List (Fin m)) (A : Stage n) (b : Point n) (f : Fin m → Point n)
    (hb : Av A.ps b) (hf : ∀ l ∈ L, Av A.ps (f l)) :
    ∃ (B : Stage n) (r : Ref n), Ext m A B (2*L.length) (2*L.length) ∧ r.ok B.ps (m+B.ops.length) ∧
      ∀ (x : X n) (Y : Finset (Fin m)), r.val B.ops x Y ↔ b x ∨ ∃ l ∈ L, l ∈ Y ∧ f l x := by
  induction L with
  | nil => exact ⟨A,.pure b,ext_id A,hb,fun x Y => by simp [Ref.val]⟩
  | cons j L ih =>
    obtain ⟨B,r,e,hr,v⟩ := ih (fun l hl => hf l (List.mem_cons_of_mem _ hl))
    have lj : j.val < m+B.ops.length := by have := j.isLt; omega
    obtain ⟨D,z,u,hz,vz⟩ := add_mix B (.scale j.val (f j)) ⟨lj,e.avail (hf j (by simp))⟩
    obtain ⟨E,z',w,hw,_,v'⟩ := combinable D false r z (u.ref_ok hr) hz (by simp)
    have step : Ext m B E 2 2 := u.then_ w (by omega) (by omega)
    refine ⟨E,z',e.then_ step (by simp; omega) (by simp; omega),hw,fun x Y => ?_⟩
    rw [v',u.ref_val hr,v,vz]
    have stable_line (gs : List (MOp n)) : mrun m false x (lineIn Y) gs j.val ↔ j ∈ Y := by
      induction gs with
      | nil =>
        change (∃ l ∈ Y, j.val = l.val) ↔ _
        constructor
        · rintro ⟨l,hl,he⟩; exact (Fin.ext he : j = l) ▸ hl
        · intro h; exact ⟨j,h,rfl⟩
      | cons o gs ih => rw [mrun_cons_old _ _ _ _ _ (by have := j.isLt; omega)]; exact ih
    simp only [logic, Bool.false_eq_true, ite_false, MOp.value, stable_line, List.mem_cons]
    grind

def mark {m : ℕ} : Option (Fin m) → Finset (Fin m)
  | none => ∅ | some l => {l}

def sample (n m : ℕ) (C : Circuit) (w : ℕ) (x : X n) (o : Option (Fin m)) : Prop :=
  val n m C x (fun l => decide (l ∈ mark o)) w = true

def baseline (n m : ℕ) (C : Circuit) (w : ℕ) : Point n := fun x => sample n m C w x none

structure Rep (n m : ℕ) (C : Circuit) (A : Stage n) (w : ℕ) : Prop where
  base : Av A.ps (baseline n m C w)
  data : ∃ r : Ref n, r.ok A.ps (m+A.ops.length) ∧ (deg n m C w = 0 → r.clean) ∧
    ∀ x o, r.val A.ops x (mark o) ↔ sample n m C w x o

lemma Rep.extend {n m c p : ℕ} {C : Circuit} {A B : Stage n} {w : ℕ} (h : Rep n m C A w) (e : Ext m A B c p) : Rep n m C B w := by
  obtain ⟨r,hr,clean,sem⟩ := h.data
  exact ⟨e.avail h.base,r,e.ref_ok hr,clean,fun x o => by rw [e.ref_val hr]; exact sem x o⟩

lemma rep_alias {n m : ℕ} {C : Circuit} {A : Stage n} {a w : ℕ} (ha : Rep n m C A a)
    (v : ∀ x o, sample n m C w x o ↔ sample n m C a x o) (d : deg n m C w = 0 → deg n m C a = 0) :
    Rep n m C A w := by
  have e : baseline n m C w = baseline n m C a := funext (fun x => propext (v x none))
  obtain ⟨r,hr,hc,hv⟩ := ha.data
  exact ⟨e ▸ ha.base,r,hr,fun h => hc (d h),fun x o => (hv x o).trans (v x o).symm⟩

lemma rep_pure {n m : ℕ} {C : Circuit} {A : Stage n} {w : ℕ} {p : Point n} (hp : Av A.ps p)
    (v : ∀ x o, sample n m C w x o ↔ p x) : Rep n m C A w := by
  have e : baseline n m C w = p := funext (fun x => propext (v x none))
  exact ⟨e ▸ hp,.pure p,hp,fun _ => trivial,fun x o => (v x o).symm⟩

lemma ordinary_bin {n m : ℕ} {C : Circuit} (A : Stage n) (flag : Bool) (a b w : ℕ)
    (ha : Rep n m C A a) (hb : Rep n m C A b)
    (sem : ∀ x o, sample n m C w x o ↔ logic flag (sample n m C a x o) (sample n m C b x o))
    (zd : deg n m C w = 0 → deg n m C a = 0 ∧ deg n m C b = 0)
    (one : flag = true → deg n m C a = 0 ∨ deg n m C b = 0) :
    ∃ B, Ext m A B 2 1 ∧ Rep n m C B w := by
  have ebase : baseline n m C w = pointOp flag (baseline n m C a) (baseline n m C b) :=
    funext (fun x => propext (sem x none))
  obtain ⟨u,ua,uc,uv⟩ := ha.data
  obtain ⟨v,va,vc,vv⟩ := hb.data
  obtain ⟨B,e,bx⟩ := add_pure (m:=m) A (scalar_recipe flag ha.base hb.base)
  have eligible (h : flag = true) : u.clean ∨ v.clean := (one h).imp uc vc
  obtain ⟨D,r,f,hr,cr,rv⟩ := combinable B flag u v (e.ref_ok ua) (e.ref_ok va) eligible
  refine ⟨D,e.then_ f (by omega) (by omega),ebase ▸ f.avail bx,r,hr,fun h => cr ⟨uc (zd h).1,vc (zd h).2⟩,fun x o => ?_⟩
  rw [rv,e.ref_val ua,e.ref_val va,uv,vv]
  exact (sem x o).symm

-- For a cross AND, take both coefficient rows, combine them on each singleton and multiplex the products.
lemma cross_bin {n m : ℕ} {C : Circuit} (A : Stage n) (good : A.good m) (a b w : ℕ)
    (ha : Rep n m C A a) (hb : Rep n m C A b)
    (sem : ∀ x o, sample n m C w x o ↔ sample n m C a x o ∧ sample n m C b x o)
    (nz : deg n m C w ≠ 0) : ∃ B, Ext m A B (4*A.ops.length+5*m+1) (2*m) ∧ Rep n m C B w := by
  let ba := baseline n m C a
  let bb := baseline n m C b
  have base_eq : baseline n m C w = pand ba bb := funext (fun x => propext (sem x none))
  obtain ⟨ra,_,_,sra⟩ := ha.data
  obtain ⟨rb,_,_,srb⟩ := hb.data
  obtain ⟨p₁,fa,g₁,vfa,sa⟩ := coefficients A.ops A.ps ra good.2.2.1 good.2.2.2 good.2.1
  obtain ⟨p₂,fb,g₂,vfb,sb⟩ := coefficients A.ops p₁ rb (g₁.avail good.2.2.1) (g₁.avail good.2.2.2) (mok_grow g₁ good.2.1)
  let P : Stage n := ⟨p₂,A.ops⟩
  have phase : Ext m A P (4*A.ops.length) 0 := pure_ext A (g₁.chain g₂ (by omega))
  let f := fun l => pand (por ba (fa l)) (por bb (fb l))
  obtain ⟨D,e,prod⟩ := make_row_products (List.finRange m) P ba bb fa fb (phase.avail ha.base) (phase.avail hb.base)
    (fun l => g₂.avail (vfa l)) vfb
  have ed : Ext m P D (3*m) 0 := by simpa using e
  obtain ⟨E,h,base_av⟩ := add_pure (m:=m) D (.meet (ed.avail (phase.avail ha.base)) (ed.avail (phase.avail hb.base)))
  obtain ⟨B,r,u,hr,rv⟩ := mux (List.finRange m) E (pand ba bb) f base_av (fun j hj => h.avail (prod j hj))
  have eu : Ext m E B (2*m) (2*m) := by simpa using u
  have before : Ext m A E (4*A.ops.length+3*m+1) 0 :=
    (phase.then_ ed (t:=4*A.ops.length+3*m) (p:=0) (by omega) (by omega)).then_ h (by omega) (by omega)
  have fa_ok (x) (l : Fin m) : por ba (fa l) x ↔ sample n m C a x (some l) :=
    ((or_congr (sra x none).symm Iff.rfl).trans (sa x l).symm).trans (sra x (some l))
  have fb_ok (x) (l : Fin m) : por bb (fb l) x ↔ sample n m C b x (some l) :=
    ((or_congr (srb x none).symm Iff.rfl).trans (sb x l).symm).trans (srb x (some l))
  have row (x) (l : Fin m) : f l x ↔ sample n m C w x (some l) :=
    (and_congr (fa_ok x l) (fb_ok x l)).trans (sem x (some l)).symm
  refine ⟨B,before.then_ eu (by omega) (by omega),base_eq ▸ eu.avail base_av,r,hr,fun h => (nz h).elim,fun x o => ?_⟩
  cases o with
  | none =>
    have v : r.val B.ops x (mark (m:=m) none) ↔ pand ba bb x := by simpa [mark] using rv x (mark none)
    exact v.trans (sem x none).symm
  | some l =>
    have v : r.val B.ops x (mark (some l)) ↔ pand ba bb x ∨ f l x := by simpa [mark] using rv x (mark (some l))
    apply v.trans
    apply Iff.trans _ (row x l)
    exact or_iff_right_of_imp (fun h => ⟨Or.inl h.1,Or.inl h.2⟩)

lemma rep_input {n m : ℕ} (C : Circuit) (A : Stage n) (good : A.good m) {i : ℕ}
    (hi : i < n+m) : Rep n m C A i := by
  by_cases hp : i < n
  · apply rep_pure (p:=pvar ⟨i,hp⟩) (Or.inr ⟨_,rfl⟩)
    intro x o
    simp [sample,pvar,val_point n m C x _ i hp]
  · let l : Fin m := ⟨i-n,by omega⟩
    have vs (x) (o) : sample n m C i x o ↔ l ∈ mark o := by
      simp [sample,val_line n m C x _ i (by omega) hi,l]
    have vb : baseline n m C i = pzero := by
      funext x; apply propext; exact (vs x none).trans (by simp [mark,pzero])
    refine ⟨vb ▸ good.2.2.1,.mixed l.val,by dsimp [Ref.ok]; have := l.isLt; omega,
      fun h => (by rw [deg_line n m C i (by omega) hi] at h; contradiction),fun x o => ?_⟩
    apply Iff.trans _ (vs x o).symm
    change mrun m false x (lineIn (mark o)) A.ops l.val ↔ _
    have run (ops : List (MOp n)) : mrun m false x (lineIn (mark o)) ops l.val = lineIn (mark o) l.val := by
      induction ops with
      | nil => rfl
      | cons op ops ih => rw [mrun_cons_old _ _ _ _ _ (by have := l.isLt; omega),ih]
    rw [run]
    constructor
    · rintro ⟨z,hz,he⟩; exact (Fin.ext he : l = z) ▸ hz
    · intro h; exact ⟨l,h,rfl⟩

noncomputable def count (n m : ℕ) (C : Circuit) (j : ℕ) : ℕ := by
  classical
  exact ((Finset.range j).filter (Cross n m C)).card

lemma count_succ {n m : ℕ} (C : Circuit) (j : ℕ) [Decidable (Cross n m C j)] :
    count n m C (j+1) = count n m C j + if Cross n m C j then 1 else 0 := by
  classical
  unfold count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : Cross n m C j <;> simp [h]

lemma count_le {n m : ℕ} (C : Circuit) (j : ℕ) : count n m C j ≤ {z | Cross n m C z}.ncard := by
  classical
  let S := (Finset.range j).filter (Cross n m C)
  have h : (S : Set ℕ) ⊆ {z | Cross n m C z} := fun _ hz => (Finset.mem_filter.mp hz).2
  change S.card ≤ _
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard h (cross_finite C)

lemma step {n m : ℕ} {C : Circuit} (hm : Monotone2 C) (hb : ReadsBack (n+m) C) (A : Stage n)
    (good : A.good m) (j : ℕ) (hj : j < C.gates.length) (prior : ∀ i < n+m+j, Rep n m C A i)
    [Decidable (Cross n m C j)] :
    ∃ B, Ext m A B (if Cross n m C j then 4*A.ops.length+5*m+1 else 2)
      (if Cross n m C j then 2*m else 1) ∧ Rep n m C B (n+m+j) := by
  let w := n+m+j
  have sv (x : X n) (o : Option (Fin m)) : sample n m C w x o ↔
      C.gates[j].op.eval (C.gates[j].inputs.map (val n m C x (fun l => decide (l ∈ mark o)))) = true := by
    simp only [sample,w,original_step hb _ _ j hj]
  obtain ⟨hop,shape⟩ := gate_kinds hm hj
  rcases shape with he | ⟨a,he⟩ | ⟨a,b,he⟩
  · have nc : ¬ Cross n m C j := by simp [Cross,gateAt_eq hj,he]
    simp only [if_neg nc]
    refine ⟨A,ext_id A,?_⟩
    rcases hop with ho | ho
    · apply rep_pure good.2.2.2
      intro x o; rw [sv]; simp [he,ho,GateOp.eval,pone]
    · apply rep_pure good.2.2.1
      intro x o; rw [sv]; simp [he,ho,GateOp.eval,pzero]
  · have nc : ¬ Cross n m C j := by simp [Cross,gateAt_eq hj,he]
    simp only [if_neg nc]
    have ma : a ∈ C.gates[j].inputs := by simp [he]
    refine ⟨A,ext_id A,rep_alias (prior a (reads hb hj ma)) (fun x o => ?_) (fun h => degree_zero_kids hm hb hj h ma)⟩
    rw [sv]
    rcases hop with ho | ho <;> simp [he,ho,GateOp.eval,sample]
  · have ma : a ∈ C.gates[j].inputs := by simp [he]
    have mb : b ∈ C.gates[j].inputs := by simp [he]
    have da := prior a (reads hb hj ma)
    have db := prior b (reads hb hj mb)
    have zd (h : deg n m C w = 0) : deg n m C a = 0 ∧ deg n m C b = 0 :=
      ⟨degree_zero_kids hm hb hj h ma,degree_zero_kids hm hb hj h mb⟩
    rcases hop with ho | ho
    · have eqv (x) (o) : sample n m C w x o ↔ sample n m C a x o ∧ sample n m C b x o := by
        rw [sv]; simp [he,ho,GateOp.eval,sample]
      by_cases cross : Cross n m C j
      · simp only [if_pos cross]
        have pos := cross.2.2.2 a (by rw [gateAt_eq hj]; exact ma)
        exact cross_bin A good a b w da db eqv (fun h => by have := (zd h).1; omega)
      · simp only [if_neg cross]
        exact ordinary_bin A true a b w da db eqv zd (fun _ => and_pure_side hj ho he cross)
    · have nc : ¬ Cross n m C j := by simp [Cross,gateAt_eq hj,ho]
      simp only [if_neg nc]
      refine ordinary_bin A false a b w da db (fun x o => ?_) zd (by simp)
      rw [sv]; simp [he,ho,GateOp.eval,sample,logic]

-- A fresh cross gate only invokes reverse passes on the mixed portion built so far.
lemma compile_prefix {n m s k : ℕ} {C : Circuit} (hm : Monotone2 C) (hb : ReadsBack (n+m) C)
    (hs : C.size ≤ s) (hc : {j | Cross n m C j}.ncard ≤ k) (j : ℕ) (hj : j ≤ C.gates.length) :
    ∃ A : Stage n, A.good m ∧ A.size ≤ 2+2*j+(4*(s+k*(2*m+1))+5*m+1)*count n m C j ∧
      A.ops.length ≤ j+(2*m)*count n m C j ∧ ∀ i < n+m+j, Rep n m C A i := by
  classical
  induction j with
  | zero =>
    let A : Stage n := ⟨[pone,pzero],[]⟩
    have good : A.good m := ⟨.cons (.cons .nil .zero) .one,trivial,Or.inl (by simp [A]),Or.inl (by simp [A])⟩
    exact ⟨A,good,by simp [A,count,Stage.size],by simp [A],fun i hi => rep_input C A good (by omega)⟩
  | succ j ih =>
    obtain ⟨A,hA,size,mix,ok⟩ := ih (by omega)
    have cj := (count_le (n:=n) (m:=m) C j).trans hc
    have js : j ≤ s := by change C.gates.length ≤ s at hs; omega
    have c : (2*m)*count n m C j ≤ (2*m)*k := Nat.mul_le_mul_left _ cj
    have peak : A.ops.length ≤ s+k*(2*m+1) := by rw [Nat.mul_add,Nat.mul_comm k (2*m),Nat.mul_one]; omega
    obtain ⟨B,e,newRep⟩ := step hm hb A hA j (by omega) ok
    have u := e.totalCost
    have v := e.markedCost
    refine ⟨B,e.good hA,?_,?_,fun i hi => ?_⟩
    · by_cases cross : Cross n m C j <;> simp only [count_succ,cross,ite_true,ite_false,Nat.mul_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero] at u size peak ⊢ <;> omega
    · by_cases cross : Cross n m C j <;> simp only [count_succ,cross,ite_true,ite_false,Nat.mul_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero] at v ⊢ <;> omega
    · by_cases h : i < n+m+j
      · exact (ok i h).extend e
      · have : i = n+m+j := by omega
        exact this ▸ newRep

lemma fun_val {n m : ℕ} (C : Circuit) (x : X n) (y : Fin m → Bool) :
    circuitFun (n+m) C (Fin.append x y) = val n m C x y C.output := by
  simp [circuitFun,Circuit.eval,List.ofFn_fin_append,val]

lemma transfer {n m : ℕ} (C M : Circuit) (hm : Monotone2 M) (hb : ReadsBack (n+m) M)
    (hc : ∀ j, ¬ Cross n m M j) (same : ∀ x o, sample n m M M.output x o ↔ sample n m C C.output x o)
    (x : X n) (Y : Finset (Fin m)) : circuitFun (n+m) M (Fin.append x (fun l => decide (l ∈ Y))) =
      (circuitFun (n+m) C (Fin.append x (fun _ => false)) ||
       decide (∃ j ∈ Y, circuitFun (n+m) C (Fin.append x (fun l => decide (l = j))) = true)) := by
  have h0 := same x none
  have h1 (l : Fin m) := same x (some l)
  simp [sample,mark] at h0 h1
  have out := Bool.eq_iff_iff.mp (no_cross_envelope hm hb hc x Y M.output)
  simp only [Env,Bool.or_eq_true,decide_eq_true_eq] at out
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq,fun_val]
  exact out.trans (or_congr (Bool.eq_iff_iff.mp h0) (exists_congr (fun l => and_congr_right (fun _ => Bool.eq_iff_iff.mp (h1 l)))))


def Claim (n m s k : ℕ) (C : Circuit) : Prop :=
    ∃ M : Circuit, Monotone2 M ∧ ReadsBack (n+m) M ∧
      (∀ j < M.gates.length, (gateAt M j).op = .and → (gateAt M j).inputs.length = 2 →
        ∃ i ∈ (gateAt M j).inputs, deg n m M i = 0) ∧
      M.size ≤ (6*k+3)*s + 12*k^2*m + 7*k*m + 6*k^2 + 2*k ∧
      {j : ℕ | j < M.gates.length ∧ 0 < deg n m M (n+m+j)}.ncard ≤ s+k*(2*m+1) ∧
      ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), circuitFun (n+m) M (Fin.append x (fun l => decide (l ∈ Y))) =
        (circuitFun (n+m) C (Fin.append x (fun _ => false)) ||
          decide (∃ j ∈ Y, circuitFun (n+m) C (Fin.append x (fun l => decide (l = j))) = true))

lemma compile_bound {n m s k : ℕ} {C : Circuit} (hm : Monotone2 C) (hb : ReadsBack (n+m) C)
    (hs : C.size ≤ s) (hc : {j | Cross n m C j}.ncard ≤ k) : Claim n m s k C := by
  classical
  by_cases hk : k = 0
  · exact zero_case hm hb hs (no_cross_of_zero (by omega))
  obtain ⟨A,g,sz,mz,all⟩ := compile_prefix hm hb hs hc C.gates.length le_rfl
  have carried : Rep n m C A C.output := by
    by_cases inside : C.output < n+m+C.gates.length
    · exact all _ inside
    · apply rep_pure g.2.2.1
      intro x o
      simp [sample,val_ge n m C x _ C.output (by omega),pzero]
  obtain ⟨r,rr,_,rs⟩ := carried.data
  obtain ⟨gs,w,W,size,pos,use⟩ := physical g.1 g.2.1 r rr
  let M : Circuit := ⟨gs,w⟩
  have well (j) (hj : j < M.gates.length) (ho : (gateAt M j).op = .and) (hi : (gateAt M j).inputs.length = 2) :
      ∃ i ∈ (gateAt M j).inputs, deg n m M i = 0 := by
    rw [gateAt_eq hj] at ho hi ⊢
    exact W.safe j hj ho hi
  have cj := (count_le (n:=n) (m:=m) C C.gates.length).trans hc
  change C.gates.length ≤ s at hs
  refine ⟨M,W.mono,W.back,well,?_,?_,?_⟩
  · change gs.length ≤ _
    rw [size]
    change A.size ≤ _
    have tax := Nat.mul_le_mul_left (4*(s+k*(2*m+1))+5*m+1) cj
    calc A.size ≤ 2+2*s+(4*(s+k*(2*m+1))+5*m+1)*k := by omega
         _ ≤ (6*k+3)*s+12*k^2*m+7*k*m+6*k^2+2*k := by
            have hk2 : 1 ≤ k^2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hk)
            nlinarith only [hk2,Nat.zero_le (2*k*s),Nat.zero_le s,Nat.zero_le (4*k^2*m),Nat.zero_le (2*k*m),Nat.zero_le k]
  · apply pos.trans
    have c := Nat.mul_le_mul_left (2*m) cj
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm k (2*m)]
    omega
  · apply transfer C M W.mono W.back
    · intro j hj
      obtain ⟨i,hi,hz⟩ := well j hj.1 hj.2.1 hj.2.2.1
      have := hj.2.2.2 i hi
      omega
    · intro x o
      exact (use.2 x (mark o)).trans (rs x o)

end PEqualNP.Outside.L_meta_1623_aux

theorem PEqualNP.Outside.L_meta_1623 : ∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true)) := by
  intro n m s k C hm hb hs hc
  exact PEqualNP.Outside.L_meta_1623_aux.compile_bound hm hb hs hc
