import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1713_aux

-- The list lemmas and the unfolding of wire values and degrees (down to gate_mem) are taken from the
-- accepted proof of L-meta-1622 in this repository, Apache-2.0. What follows them is for this step.

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def dflt : Gate := Gate.mk GateOp.or []

-- generic gate-list fold
def run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem run_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    run f (gs ++ [g]) w = run f gs w ++ [f (run f gs w) g] := by
  simp [run]

theorem run_append {α : Type} (f : List α → Gate → α) (g1 g2 : List Gate) (w : List α) :
    run f (g1 ++ g2) w = run f g2 (run f g1 w) := by
  simp [run]

theorem run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (run f gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem run_lt {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α) (i : ℕ)
    (h : i < w.length) : (run f gs w).getD i d = w.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih]

theorem run_gate {α : Type} (f : List α → Gate → α) (d : α)
    (hf : ∀ (g : Gate) (w w' : List α), (∀ i ∈ g.inputs, w.getD i d = w'.getD i d) → f w g = f w' g)
    (gs : List Gate) (w : List α) (L : ℕ) (hL : w.length = L) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k dflt).inputs, i < L + k) :
    (run f gs w).getD (L + k) d = f (run f gs w) (gs.getD k dflt) := by
  subst hL
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [run_snoc]
    rcases Nat.lt_or_ge k gs.length with h | h
    · have e : (gs ++ [g]).getD k dflt = gs.getD k dflt := getD_app_lt _ _ _ _ h
      rw [e] at hr ⊢
      rw [getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih h hr]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)
    · have hk' : k = gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length dflt = g := getD_app_len _ _ _
      rw [e] at hr ⊢
      have e2 : w.length + gs.length = (run f gs w).length := (run_length f gs w).symm
      rw [e2, getD_app_len]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)

def evf (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def ldf (d : List ℕ) (g : Gate) : ℕ := g.lineDegree d

theorem evf_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : evf w g = evf w' g := by
  unfold evf
  rw [List.map_congr_left h]

theorem ldf_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : ldf w g = ldf w' g := by
  unfold ldf Gate.lineDegree
  rw [List.map_congr_left h]

-- wire values and degrees of the given circuit
def wv (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

theorem wires_run (C : Circuit) (inp : List Bool) : C.wires inp = run evf C.gates inp := rfl

theorem wv_input (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : w < N) :
    wv C N z w = z ⟨w, h⟩ := by
  unfold wv
  rw [wires_run, run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem wv_ge (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : N + C.gates.length ≤ w) :
    wv C N z w = false := by
  unfold wv
  rw [wires_run]
  exact getD_ge _ _ _ (by rw [run_length]; simpa using h)

theorem wv_gate (C : Circuit) (N : ℕ) (z : Fin N → Bool) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    wv C N z (N + k) = (C.gates.getD k dflt).op.eval ((C.gates.getD k dflt).inputs.map (wv C N z)) := by
  unfold wv
  rw [wires_run]
  exact run_gate evf false evf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem deg_run (C : Circuit) (N : ℕ) (M : Finset ℕ) : C.lineDegrees N M =
    run ldf C.gates ((List.range N).map fun i => if i ∈ M then 1 else 0) := rfl

theorem deg_input (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : w < N) :
    (C.lineDegrees N M).getD w 0 = if w ∈ M then 1 else 0 := by
  rw [deg_run, run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem deg_ge (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : N + C.gates.length ≤ w) :
    (C.lineDegrees N M).getD w 0 = 0 := by
  rw [deg_run]
  exact getD_ge _ _ _ (by rw [run_length]; simpa using h)

theorem deg_gate (C : Circuit) (N : ℕ) (M : Finset ℕ) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.lineDegrees N M).getD (N + k) 0 = (C.gates.getD k dflt).lineDegree (C.lineDegrees N M) := by
  rw [deg_run]
  exact run_gate ldf 0 ldf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem app_lt {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : w < n) : Fin.append x y ⟨w, h⟩ = x ⟨w, hw⟩ :=
  Fin.append_left x y ⟨w, hw⟩

theorem app_ge {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : n ≤ w) : Fin.append x y ⟨w, h⟩ = y ⟨w - n, by omega⟩ := by
  have e : (⟨w, h⟩ : Fin (n + m)) = Fin.natAdd n ⟨w - n, by omega⟩ := by
    ext
    simp only [Fin.natAdd_mk]
    omega
  rw [e, Fin.append_right]

theorem gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : C.gates.getD k dflt ∈ C.gates := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem bool_or_mono : ∀ p q r s : Bool, p ≤ q → r ≤ s → (p || r) ≤ (q || s) := by decide

theorem bool_and_mono : ∀ p q r s : Bool, p ≤ q → r ≤ s → (p && r) ≤ (q && s) := by decide

-- a gate of the circuit: two earlier wires, AND or OR, with its value and its degrees
theorem gate_view (C : Circuit) (n : ℕ) (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ReadsBack n C) (k : ℕ) (hk : k < C.gates.length) :
    ∃ a b, a < n + k ∧ b < n + k ∧ (gateAt C k).inputs = [a, b] ∧
      (((gateAt C k).op = GateOp.and ∧
          (∀ z : Fin n → Bool, wv C n z (n + k) = (wv C n z a && wv C n z b)) ∧
          (∀ M : Finset ℕ, (C.lineDegrees n M).getD (n + k) 0 =
            (C.lineDegrees n M).getD a 0 + (C.lineDegrees n M).getD b 0)) ∨
       ((gateAt C k).op = GateOp.or ∧
          (∀ z : Fin n → Bool, wv C n z (n + k) = (wv C n z a || wv C n z b)) ∧
          (∀ M : Finset ℕ, (C.lineDegrees n M).getD (n + k) 0 =
            max ((C.lineDegrees n M).getD a 0) ((C.lineDegrees n M).getD b 0)))) := by
  have hmem := gate_mem C k hk
  obtain ⟨hop, hl⟩ := hG _ hmem
  have hr : ∀ i ∈ (C.gates.getD k dflt).inputs, i < n + k := hR k hk
  have hw := fun z => wv_gate C n z hR k hk
  have hd := fun M => deg_gate C n M hR k hk
  have e : gateAt C k = C.gates.getD k dflt := rfl
  rw [e]
  generalize C.gates.getD k dflt = g at hop hl hr hw hd ⊢
  obtain ⟨op, l⟩ := g
  dsimp only at hop hl hr hw hd ⊢
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hl
  · simp at hl
  · refine ⟨a, b, hr a (by simp), hr b (by simp), rfl, ?_⟩
    rcases hop with rfl | rfl
    · left
      refine ⟨rfl, fun z => ?_, fun M => ?_⟩
      · rw [hw z]; simp [GateOp.eval]
      · rw [hd M]; simp [Gate.lineDegree]
    · right
      refine ⟨rfl, fun z => ?_, fun M => ?_⟩
      · rw [hw z]; simp [GateOp.eval]
      · rw [hd M]; simp [Gate.lineDegree]
  · simp at hl

-- every wire is monotone in the input
theorem wv_mono (C : Circuit) (n : ℕ) (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ReadsBack n C) (z z' : Fin n → Bool) (hz : ∀ i, z i ≤ z' i) (w : ℕ) :
    wv C n z w ≤ wv C n z' w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w n with h | h
    · rw [wv_input _ _ _ _ h, wv_input _ _ _ _ h]
      exact hz _
    · rcases Nat.lt_or_ge (w - n) C.gates.length with hk | hk
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk' : k < C.gates.length := by omega
        obtain ⟨a, b, ha, hb, -, hcase⟩ := gate_view C n hG hR k hk'
        rcases hcase with ⟨-, hv, -⟩ | ⟨-, hv, -⟩
        · rw [hv z, hv z']
          exact bool_and_mono _ _ _ _ (ih a ha) (ih b hb)
        · rw [hv z, hv z']
          exact bool_or_mono _ _ _ _ (ih a ha) (ih b hb)
      · have e1 := wv_ge C n z w (by omega)
        have e2 := wv_ge C n z' w (by omega)
        simp [e1, e2]

theorem append_mono {N : ℕ} (x x' : Fin N → Bool) (hxx : x ≤ x') (i : Fin (N + N)) :
    Fin.append x (fun _ : Fin N => false) i ≤ Fin.append x' (fun _ : Fin N => false) i := by
  obtain ⟨w, hw⟩ := i
  rcases Nat.lt_or_ge w N with h | h
  · rw [app_lt _ _ _ _ h, app_lt _ _ _ _ h]
    exact hxx ⟨w, h⟩
  · have e : Fin.append x (fun _ : Fin N => false) ⟨w, hw⟩ =
        Fin.append x' (fun _ : Fin N => false) ⟨w, hw⟩ := by
      rw [app_ge _ _ _ _ h, app_ge _ _ _ _ h]
    exact le_of_eq e

-- a wire of line-degree zero ignores the lines, one of point-degree zero ignores the points,
-- and every wire is false at the all-false input
theorem basic (C : Circuit) (N : ℕ) (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ReadsBack (N + N) C) (w : ℕ) :
    ((C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 = 0 → ∀ (x ya yb : Fin N → Bool),
        wv C (N + N) (Fin.append x ya) w = wv C (N + N) (Fin.append x yb) w) ∧
    ((C.lineDegrees (N + N) (Finset.range N)).getD w 0 = 0 → ∀ (xa xb y : Fin N → Bool),
        wv C (N + N) (Fin.append xa y) w = wv C (N + N) (Fin.append xb y) w) ∧
    wv C (N + N) (Fin.append (fun _ : Fin N => false) (fun _ : Fin N => false)) w = false := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w (N + N) with h | h
    · rcases Nat.lt_or_ge w N with hw | hw
      · refine ⟨fun _ x ya yb => ?_, fun h0 => ?_, ?_⟩
        · rw [wv_input _ _ _ _ h, wv_input _ _ _ _ h, app_lt _ _ _ _ hw, app_lt _ _ _ _ hw]
        · exfalso
          rw [deg_input _ _ _ _ h] at h0
          have hm : w ∈ Finset.range N := Finset.mem_range.2 hw
          simp [hm] at h0
        · rw [wv_input _ _ _ _ h, app_lt _ _ _ _ hw]
      · refine ⟨fun h0 => ?_, fun _ xa xb y => ?_, ?_⟩
        · exfalso
          rw [deg_input _ _ _ _ h] at h0
          have hm : w ∈ Finset.Ico N (N + N) := Finset.mem_Ico.2 ⟨hw, h⟩
          simp [hm] at h0
        · rw [wv_input _ _ _ _ h, wv_input _ _ _ _ h, app_ge _ _ _ _ hw, app_ge _ _ _ _ hw]
        · rw [wv_input _ _ _ _ h, app_ge _ _ _ _ hw]
    · rcases Nat.lt_or_ge (w - (N + N)) C.gates.length with hk | hk
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + N + k := ⟨w - (N + N), by omega⟩
        have hk' : k < C.gates.length := by omega
        obtain ⟨a, b, ha, hb, -, hcase⟩ := gate_view C (N + N) hG hR k hk'
        obtain ⟨a1, a2, a3⟩ := ih a ha
        obtain ⟨b1, b2, b3⟩ := ih b hb
        rcases hcase with ⟨-, hv, hd⟩ | ⟨-, hv, hd⟩
        · refine ⟨fun h0 x ya yb => ?_, fun h0 xa xb y => ?_, ?_⟩
          · rw [hd] at h0
            rw [hv, hv, a1 (by omega) x ya yb, b1 (by omega) x ya yb]
          · rw [hd] at h0
            rw [hv, hv, a2 (by omega) xa xb y, b2 (by omega) xa xb y]
          · simp [hv, a3, b3]
        · refine ⟨fun h0 x ya yb => ?_, fun h0 xa xb y => ?_, ?_⟩
          · rw [hd] at h0
            obtain ⟨h1, h2⟩ := Nat.max_eq_zero_iff.1 h0
            rw [hv, hv, a1 h1 x ya yb, b1 h2 x ya yb]
          · rw [hd] at h0
            obtain ⟨h1, h2⟩ := Nat.max_eq_zero_iff.1 h0
            rw [hv, hv, a2 h1 xa xb y, b2 h2 xa xb y]
          · simp [hv, a3, b3]
      · refine ⟨fun _ x ya yb => ?_, fun _ xa xb y => ?_, ?_⟩
        · rw [wv_ge _ _ _ _ (by omega), wv_ge _ _ _ _ (by omega)]
        · rw [wv_ge _ _ _ _ (by omega), wv_ge _ _ _ _ (by omega)]
        · exact wv_ge _ _ _ _ (by omega)

-- the pure line wires read by a mixed gate
def isH (C : Circuit) (N : ℕ) (h : ℕ) : Prop :=
  (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0 ∧ 0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD h 0 ∧
    ∃ j < C.gates.length, h ∈ (gateAt C j).inputs ∧ 0 < (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 ∧
      0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0

-- the normal form of a wire
def NF (C : Circuit) (N : ℕ) (w : ℕ) : Prop :=
  ∃ c : ℕ → (Fin N → Bool) → Bool, (∀ h : ℕ, Monotone (c h)) ∧ ∀ x y : Fin N → Bool,
    (wv C (N + N) (Fin.append x y) w = true ↔
      (wv C (N + N) (Fin.append x (fun _ : Fin N => false)) w = true ∨
        ∃ h : ℕ, isH C N h ∧
          wv C (N + N) (Fin.append (fun _ : Fin N => false) y) h = true ∧ c h x = true))

theorem nf_linefree (C : Circuit) (N : ℕ) (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ReadsBack (N + N) C) (w : ℕ) (h0 : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 = 0) : NF C N w := by
  refine ⟨fun _ _ => false, fun _ => monotone_const, fun x y => ?_⟩
  rw [(basic C N hG hR w).1 h0 x y (fun _ => false)]
  simp

theorem nf_pureline (C : Circuit) (N : ℕ) (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ReadsBack (N + N) C) (u : ℕ) (hp : (C.lineDegrees (N + N) (Finset.range N)).getD u 0 = 0) (hH : isH C N u) : NF C N u := by
  refine ⟨fun h _ => decide (h = u), fun _ => monotone_const, fun x y => ?_⟩
  have e1 := (basic C N hG hR u).2.1 hp x (fun _ => false) y
  have e2 := (basic C N hG hR u).2.1 hp x (fun _ => false) (fun _ => false)
  have e3 := (basic C N hG hR u).2.2
  rw [e1, e2, e3]
  constructor
  · intro hv
    exact Or.inr ⟨u, hH, hv, by simp⟩
  · rintro (hf | ⟨h, -, hv, hc⟩)
    · exact absurd hf (by simp)
    · have hu : h = u := by simpa using hc
      rw [hu] at hv
      exact hv

-- an input of a mixed gate has the normal form, once the mixed wires before it do
theorem nf_input (C : Circuit) (N : ℕ) (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ReadsBack (N + N) C) (k : ℕ) (hk : k < C.gates.length)
    (hp : 0 < (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + k) 0) (hl : 0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + k) 0)
    (u : ℕ) (hu : u ∈ (gateAt C k).inputs)
    (ih : 0 < (C.lineDegrees (N + N) (Finset.range N)).getD u 0 → 0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD u 0 → NF C N u) : NF C N u := by
  rcases Nat.eq_zero_or_pos ((C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD u 0) with h0 | h0
  · exact nf_linefree C N hG hR u h0
  · rcases Nat.eq_zero_or_pos ((C.lineDegrees (N + N) (Finset.range N)).getD u 0) with h1 | h1
    · exact nf_pureline C N hG hR u h1 ⟨h1, h0, k, hk, hu, hp, hl⟩
    · exact ih h1 h0

theorem nf_mixed (C : Circuit) (N : ℕ) (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ReadsBack (N + N) C)
    (hA : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨ (∀ h ∈ (gateAt C j).inputs, (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0))
    (w : ℕ) : 0 < (C.lineDegrees (N + N) (Finset.range N)).getD w 0 → 0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 → NF C N w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hp hl
    rcases Nat.lt_or_ge w (N + N) with h | h
    · exfalso
      rw [deg_input _ _ _ _ h] at hp hl
      rcases Nat.lt_or_ge w N with hw | hw
      · have hm : w ∉ Finset.Ico N (N + N) := by
          intro hc
          have := (Finset.mem_Ico.1 hc).1
          omega
        simp [hm] at hl
      · have hm : w ∉ Finset.range N := by
          intro hc
          have := Finset.mem_range.1 hc
          omega
        simp [hm] at hp
    · rcases Nat.lt_or_ge (w - (N + N)) C.gates.length with hk | hk
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + N + k := ⟨w - (N + N), by omega⟩
        have hk' : k < C.gates.length := by omega
        obtain ⟨a, b, ha, hb, hin, hcase⟩ := gate_view C (N + N) hG hR k hk'
        have hfa : NF C N a :=
          nf_input C N hG hR k hk' hp hl a (by rw [hin]; simp) (ih a ha)
        have hfb : NF C N b :=
          nf_input C N hG hR k hk' hp hl b (by rw [hin]; simp) (ih b hb)
        rcases hcase with ⟨hop, hv, hd⟩ | ⟨hop, hv, hd⟩
        · rcases hA k hk' hop with ⟨i, hi, hi0⟩ | hall
          · rw [hin] at hi
            have hi' : i = a ∨ i = b := by simpa using hi
            rcases hi' with hia | hib
            · rw [hia] at hi0
              obtain ⟨cb, hcb, hfb⟩ := hfb
              refine ⟨fun h x => wv C (N + N) (Fin.append x (fun _ : Fin N => false)) a && cb h x,
                fun h => ?_, fun x y => ?_⟩
              · intro x x' hxx
                exact bool_and_mono _ _ _ _
                  (wv_mono C (N + N) hG hR _ _ (append_mono x x' hxx) a) (hcb h hxx)
              · rw [hv, hv, (basic C N hG hR a).1 hi0 x y (fun _ => false)]
                simp only [Bool.and_eq_true]
                rw [hfb x y]
                constructor
                · rintro ⟨h1, h2 | ⟨h, hH, hy, hc⟩⟩
                  · exact Or.inl ⟨h1, h2⟩
                  · exact Or.inr ⟨h, hH, hy, h1, hc⟩
                · rintro (⟨h1, h2⟩ | ⟨h, hH, hy, h1, hc⟩)
                  · exact ⟨h1, Or.inl h2⟩
                  · exact ⟨h1, Or.inr ⟨h, hH, hy, hc⟩⟩
            · rw [hib] at hi0
              obtain ⟨ca, hca, hfa⟩ := hfa
              refine ⟨fun h x => ca h x && wv C (N + N) (Fin.append x (fun _ : Fin N => false)) b,
                fun h => ?_, fun x y => ?_⟩
              · intro x x' hxx
                exact bool_and_mono _ _ _ _ (hca h hxx)
                  (wv_mono C (N + N) hG hR _ _ (append_mono x x' hxx) b)
              · rw [hv, hv, (basic C N hG hR b).1 hi0 x y (fun _ => false)]
                simp only [Bool.and_eq_true]
                rw [hfa x y]
                constructor
                · rintro ⟨h1 | ⟨h, hH, hy, hc⟩, h2⟩
                  · exact Or.inl ⟨h1, h2⟩
                  · exact Or.inr ⟨h, hH, hy, hc, h2⟩
                · rintro (⟨h1, h2⟩ | ⟨h, hH, hy, hc, h2⟩)
                  · exact ⟨Or.inl h1, h2⟩
                  · exact ⟨Or.inr ⟨h, hH, hy, hc⟩, h2⟩
          · exfalso
            have h1 := hall a (by rw [hin]; simp)
            have h2 := hall b (by rw [hin]; simp)
            rw [hd] at hp
            omega
        · obtain ⟨ca, hca, hfa⟩ := hfa
          obtain ⟨cb, hcb, hfb⟩ := hfb
          refine ⟨fun h x => ca h x || cb h x, fun h => ?_, fun x y => ?_⟩
          · intro x x' hxx
            exact bool_or_mono _ _ _ _ (hca h hxx) (hcb h hxx)
          · rw [hv, hv]
            simp only [Bool.or_eq_true]
            rw [hfa x y, hfb x y]
            constructor
            · rintro ((h1 | ⟨h, hH, hy, hc⟩) | (h1 | ⟨h, hH, hy, hc⟩))
              · exact Or.inl (Or.inl h1)
              · exact Or.inr ⟨h, hH, hy, Or.inl hc⟩
              · exact Or.inl (Or.inr h1)
              · exact Or.inr ⟨h, hH, hy, Or.inr hc⟩
            · rintro ((h1 | h1) | ⟨h, hH, hy, hc | hc⟩)
              · exact Or.inl (Or.inl h1)
              · exact Or.inr (Or.inl h1)
              · exact Or.inl (Or.inr ⟨h, hH, hy, hc⟩)
              · exact Or.inr (Or.inr ⟨h, hH, hy, hc⟩)
      · exfalso
        rw [deg_ge _ _ _ _ (by omega)] at hp
        omega

end PEqualNP.Outside.L_meta_1713_aux

theorem PEqualNP.Outside.L_meta_1713 : ∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true))) := by
  intro N C hG hR hA
  refine ⟨fun w xa xb ya yb => ⟨fun h0 => ?_, fun h0 => ?_, ?_⟩, fun w hp hl => ?_⟩
  · exact (PEqualNP.Outside.L_meta_1713_aux.basic C N hG hR w).1 h0 xa ya yb
  · exact (PEqualNP.Outside.L_meta_1713_aux.basic C N hG hR w).2.1 h0 xa xb ya
  · exact (PEqualNP.Outside.L_meta_1713_aux.basic C N hG hR w).2.2
  · exact PEqualNP.Outside.L_meta_1713_aux.nf_mixed C N hG hR hA w hp hl
