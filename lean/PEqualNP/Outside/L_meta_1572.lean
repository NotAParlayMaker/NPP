import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

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

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

/-- The value of wire `w` on input `x`. -/
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

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_eval (gates : List Gate) (w : ℕ) (x : Fin 13 → Bool) :
    val gates w x = Circuit.eval ⟨gates, w⟩ (List.ofFn x) := by
  simp [val, eval_eq]

/-- The line number `s` of Z13. -/
def Lf (s : Fin 13) : Finset (Fin 13) := {s, s + 1, s + 3, s + 9}

theorem zeroM : ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (0 : Fin 13) ∉ Lf m := by decide

theorem oneL : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (1 : Fin 13) ∉ Lf l := by decide

/-- A wire true at `x` is true at every input above `x`. -/
theorem up (gates : List Gate) (g : ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin 13 → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : Circuit.eval ⟨gates, g⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, g⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  exact mono2 gates hleg _ _ (by simp) (ofFn_mono 13 x y hxy) g h

/-- Wire `Y` lies in the OR-cone below output wire `g`. -/
def InOrCone (gates : List Gate) (g Y : ℕ) : Prop :=
  ∀ S : Set ℕ, g ∈ S →
    (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) →
    Y ∈ S

theorem inOrCone_self (gates : List Gate) (g : ℕ) : InOrCone gates g g :=
  fun _ hg _ => hg

theorem inOrCone_or_input (gates : List Gate) (g : ℕ) (i : Fin gates.length)
    (hY : InOrCone gates g (13 + (i : ℕ))) (hor : (gates.get i).op = GateOp.or)
    (a : ℕ) (ha : a ∈ (gates.get i).inputs) : InOrCone gates g a := by
  intro S hg hcl
  exact hcl i (hY S hg hcl) hor a ha

/-- Along an OR-only path, a true leaf forces the output true. -/
theorem orCone_forces (gates : List Gate) (g Y : ℕ)
    (hwf : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hY : InOrCone gates g Y) (x : Fin 13 → Bool) (h : val gates Y x = true) :
    val gates g x = true := by
  let S : Set ℕ := {w | val gates w x = true → val gates g x = true}
  have hgS : g ∈ S := by
    change val gates g x = true → val gates g x = true
    exact fun t => t
  have hcl : ∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S := by
    intro i hiS hor a ha hx
    have hop : gates[i.val].op = GateOp.or := by
      simpa [List.get_eq_getElem] using hor
    have ha' : a ∈ gates[i.val].inputs := by
      simpa [List.get_eq_getElem] using ha
    have halt : a < 13 + i.val := (hwf i).2 a (by simpa [List.get_eq_getElem] using ha)
    have hOr : val gates (13 + i.val) x = true :=
      (val_or (n := 13) gates x i.val i.isLt hop).2 ⟨a, ha', halt, hx⟩
    exact hiS hOr
  exact hY S hgS hcl h

/-- If the output is true, some OR-cone atom (input or AND gate) is true. -/
theorem orCone_atom (gates : List Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (_hwf : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (out w : ℕ) (hout : InOrCone gates out w) (x : Fin 13 → Bool)
    (hw : val gates w x = true) :
    ∃ Y : ℕ, InOrCone gates out Y ∧ val gates Y x = true ∧
      (Y < 13 ∨ ∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < 13
    · exact ⟨w, hout, hw, Or.inl hwn⟩
    · by_cases hbig : 13 + gates.length ≤ w
      · have := val_big (n := 13) gates x w hbig
        rw [this] at hw
        exact absurd hw (by simp)
      · have hi : w - 13 < gates.length := by omega
        have he : w = 13 + (w - 13) := by omega
        rw [he] at hout hw
        set k := w - 13 with hkdef
        have hk : k < gates.length := hi
        have hmem : gates[k] ∈ gates := List.getElem_mem hk
        rcases (hleg gates[k] hmem).1 with ha | ho
        · refine ⟨13 + k, hout, hw, Or.inr ⟨⟨k, hk⟩, rfl, ?_⟩⟩
          simpa [List.get_eq_getElem] using ha
        · have hop : gates[k].op = GateOp.or := ho
          obtain ⟨a, ha, halt, haval⟩ := (val_or (n := 13) gates x k hk hop).1 hw
          have haCone : InOrCone gates out a :=
            inOrCone_or_input gates out ⟨k, hk⟩ hout
              (by simpa [List.get_eq_getElem] using ho) a
              (by simpa [List.get_eq_getElem] using ha)
          have hlt : a < w := by omega
          exact ih a hlt haCone haval

/-- An input wire in the OR-cone of `g` lies on every co-line that kills `g`. -/
theorem input_in_cone (gates : List Gate) (g Y : ℕ)
    (hwf : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (_hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hY : InOrCone gates g Y) (hYn : Y < 13)
    (S : Finset (Fin 13))
    (hkill : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ S))) = false) :
    (⟨Y, hYn⟩ : Fin 13) ∈ S := by
  by_contra hnot
  have hforce := orCone_forces gates g Y hwf hY (fun v => decide (v ∉ S)) (by
    rw [val_input gates _ Y hYn]
    simpa using hnot)
  rw [val_eval] at hforce
  rw [hforce] at hkill
  exact absurd hkill (by simp)

/-- Test input for a point of an L-line: `{p}` if `p = 0`, else `{p, 1}`. -/
def testL (p : Fin 13) (v : Fin 13) : Bool := decide (v = p ∨ (p ≠ 0 ∧ v = 1))

/-- Test input for a point of an M-line: `{p}` if `p = 1`, else `{p, 0}`. -/
def testM (p : Fin 13) (v : Fin 13) : Bool := decide (v = p ∨ (p ≠ 1 ∧ v = 0))

theorem testL_zero_le_coM (m : Fin 13) (hm : m ∈ ({1, 5, 11} : Finset (Fin 13)))
    (v : Fin 13) (hv : testL 0 v = true) :
    decide (v ∉ Lf m) = true := by
  have : v = 0 := by
    have := of_decide_eq_true hv
    simpa using this
  subst this
  simpa using zeroM m hm

theorem testM_one_le_coL (l : Fin 13) (hl : l ∈ ({4, 10, 12} : Finset (Fin 13)))
    (v : Fin 13) (hv : testM 1 v = true) :
    decide (v ∉ Lf l) = true := by
  have : v = 1 := by
    have := of_decide_eq_true hv
    simpa using this
  subst this
  simpa using oneL l hl

theorem fireL_ne_zero (gates : List Gate) (g : ℕ) (l m : Fin 13) (p : Fin 13)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (_hl : l ∈ ({4, 10, 12} : Finset (Fin 13)))
    (hm : m ∈ ({1, 5, 11} : Finset (Fin 13)))
    (hfM : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lf m))) = false)
    (hp : Circuit.eval ⟨gates, g⟩ (List.ofFn (testL p)) = true) : p ≠ 0 := by
  intro hp0
  subst hp0
  have := up gates g hleg (testL 0) (fun v => decide (v ∉ Lf m)) (testL_zero_le_coM m hm) hp
  rw [this] at hfM
  exact absurd hfM (by simp)

theorem fireM_ne_one (gates : List Gate) (g : ℕ) (l m : Fin 13) (p : Fin 13)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hl : l ∈ ({4, 10, 12} : Finset (Fin 13)))
    (_hm : m ∈ ({1, 5, 11} : Finset (Fin 13)))
    (hfL : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lf l))) = false)
    (hp : Circuit.eval ⟨gates, g⟩ (List.ofFn (testM p)) = true) : p ≠ 1 := by
  intro hp1
  subst hp1
  have := up gates g hleg (testM 1) (fun v => decide (v ∉ Lf l)) (testM_one_le_coL l hl) hp
  rw [this] at hfL
  exact absurd hfL (by simp)

theorem halfL (gates : List Gate) (g : ℕ) (l m c : Fin 13)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hwf : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hl : l ∈ ({4, 10, 12} : Finset (Fin 13)))
    (hm : m ∈ ({1, 5, 11} : Finset (Fin 13)))
    (hmeet : Lf l ∩ Lf m = {c})
    (hfL : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lf l))) = false)
    (hfM : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lf m))) = false)
    (h2 : 2 ≤ ((Lf l).filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (testL p)) = true)).card) :
    ∃ Y : ℕ, InOrCone gates g Y ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      ∃ p ∈ Lf l, p ≠ 0 ∧ p ≠ c ∧ Circuit.eval ⟨gates, Y⟩ (List.ofFn (testL p)) = true := by
  set F := (Lf l).filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (testL p)) = true)
  have hF2 : 2 ≤ F.card := h2
  obtain ⟨p, hpF, hp_ne_c⟩ : ∃ p ∈ F, p ≠ c := by
    by_contra hcon
    push Not at hcon
    have hsub : F ⊆ ({c} : Finset (Fin 13)) := by
      intro p hp
      exact Finset.mem_singleton.2 (hcon p hp)
    have : F.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    omega
  have hpL : p ∈ Lf l := (Finset.mem_filter.1 hpF).1
  have hpT : Circuit.eval ⟨gates, g⟩ (List.ofFn (testL p)) = true := (Finset.mem_filter.1 hpF).2
  have hp0 : p ≠ 0 := fireL_ne_zero gates g l m p hleg hl hm hfM hpT
  have hv : val gates g (testL p) = true := by
    rw [val_eval]; exact hpT
  obtain ⟨Y, hY, hYv, hatom⟩ :=
    orCone_atom gates hleg hwf g g (inOrCone_self gates g) (testL p) hv
  rcases hatom with hYn | ⟨i, rfl, hand⟩
  · exfalso
    have hYl := input_in_cone gates g Y hwf hleg hY hYn (Lf l) hfL
    have hYm := input_in_cone gates g Y hwf hleg hY hYn (Lf m) hfM
    have hYc : (⟨Y, hYn⟩ : Fin 13) = c := by
      have : (⟨Y, hYn⟩ : Fin 13) ∈ Lf l ∩ Lf m := Finset.mem_inter.2 ⟨hYl, hYm⟩
      rw [hmeet] at this
      simpa using this
    have hYtrue : testL p ⟨Y, hYn⟩ = true := by
      rw [← val_input gates (testL p) Y hYn]; exact hYv
    have hdec := of_decide_eq_true hYtrue
    rcases hdec with hEq | ⟨_, h1⟩
    · exact hp_ne_c (hEq.symm.trans hYc)
    · have hY1 : (⟨Y, hYn⟩ : Fin 13) = 1 := h1
      have : (1 : Fin 13) ∈ Lf l := by rw [← hY1]; exact hYl
      exact (oneL l hl) this
  · refine ⟨13 + (i : ℕ), hY, ⟨i, rfl, hand⟩, p, hpL, hp0, hp_ne_c, ?_⟩
    rw [← val_eval]; exact hYv

theorem halfM (gates : List Gate) (g : ℕ) (l m c : Fin 13)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hwf : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hl : l ∈ ({4, 10, 12} : Finset (Fin 13)))
    (hm : m ∈ ({1, 5, 11} : Finset (Fin 13)))
    (hmeet : Lf l ∩ Lf m = {c})
    (hfL : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lf l))) = false)
    (hfM : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lf m))) = false)
    (h2 : 2 ≤ ((Lf m).filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (testM p)) = true)).card) :
    ∃ Y : ℕ, InOrCone gates g Y ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      ∃ p ∈ Lf m, p ≠ 1 ∧ p ≠ c ∧ Circuit.eval ⟨gates, Y⟩ (List.ofFn (testM p)) = true := by
  set F := (Lf m).filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (testM p)) = true)
  have hF2 : 2 ≤ F.card := h2
  obtain ⟨p, hpF, hp_ne_c⟩ : ∃ p ∈ F, p ≠ c := by
    by_contra hcon
    push Not at hcon
    have hsub : F ⊆ ({c} : Finset (Fin 13)) := by
      intro p hp
      exact Finset.mem_singleton.2 (hcon p hp)
    have : F.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    omega
  have hpM : p ∈ Lf m := (Finset.mem_filter.1 hpF).1
  have hpT : Circuit.eval ⟨gates, g⟩ (List.ofFn (testM p)) = true := (Finset.mem_filter.1 hpF).2
  have hp1 : p ≠ 1 := fireM_ne_one gates g l m p hleg hl hm hfL hpT
  have hv : val gates g (testM p) = true := by
    rw [val_eval]; exact hpT
  obtain ⟨Y, hY, hYv, hatom⟩ :=
    orCone_atom gates hleg hwf g g (inOrCone_self gates g) (testM p) hv
  rcases hatom with hYn | ⟨i, rfl, hand⟩
  · exfalso
    have hYl := input_in_cone gates g Y hwf hleg hY hYn (Lf l) hfL
    have hYm := input_in_cone gates g Y hwf hleg hY hYn (Lf m) hfM
    have hYc : (⟨Y, hYn⟩ : Fin 13) = c := by
      have : (⟨Y, hYn⟩ : Fin 13) ∈ Lf l ∩ Lf m := Finset.mem_inter.2 ⟨hYl, hYm⟩
      rw [hmeet] at this
      simpa using this
    have hYtrue : testM p ⟨Y, hYn⟩ = true := by
      rw [← val_input gates (testM p) Y hYn]; exact hYv
    have hdec := of_decide_eq_true hYtrue
    rcases hdec with hEq | ⟨_, h0⟩
    · exact hp_ne_c (hEq.symm.trans hYc)
    · have hY0 : (⟨Y, hYn⟩ : Fin 13) = 0 := h0
      have : (0 : Fin 13) ∈ Lf m := by rw [← hY0]; exact hYm
      exact (zeroM m hm) this
  · refine ⟨13 + (i : ℕ), hY, ⟨i, rfl, hand⟩, p, hpM, hp1, hp_ne_c, ?_⟩
    rw [← val_eval]; exact hYv

end PEqualNP.Outside.L_meta_1572

open PEqualNP.Outside.L_meta_1572 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1572 :
    ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ,
        (∀ S : Set ℕ, g ∈ S →
          (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
            (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
        (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧
          (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩
            (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ,
        (∀ S : Set ℕ, g ∈ S →
          (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
            (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
        (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧
          (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩
            (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates g l m c hleg hwf hl hm hmeet hfL hfM
  have hLf : L = Lf := by funext s; rw [hL s]; rfl
  subst hLf
  constructor
  · intro h2
    obtain ⟨Y, hY, hand, hp⟩ := halfL gates g l m c hleg hwf hl hm hmeet hfL hfM h2
    exact ⟨Y, hY, hand, by simpa [testL] using hp⟩
  · intro h2
    obtain ⟨Y, hY, hand, hp⟩ := halfM gates g l m c hleg hwf hl hm hmeet hfL hfM h2
    exact ⟨Y, hY, hand, by simpa [testM] using hp⟩
