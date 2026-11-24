import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1638
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

def InTop (gates : List Gate) (N u : ℕ) (Y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S →
    (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S

theorem top_step (gates : List Gate) (N u : ℕ) (i : Fin gates.length)
    (h : InTop gates N u (N + (i : ℕ))) (hop : (gates.get i).op = GateOp.or) (a : ℕ)
    (ha : a ∈ (gates.get i).inputs) : InTop gates N u a := by
  intro S hu hcl
  exact hcl i (h S hu hcl) hop a ha

theorem part1 {N : ℕ} (gates : List Gate) (u : ℕ) (x : Fin N → Bool)
    (hb : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hu : val gates u x = false) (Y : ℕ) (hY : InTop gates N u Y) : val gates Y x = false := by
  refine hY {Y | val gates Y x = false} hu ?_
  intro i hi hop a ha
  have hi' : val gates (N + (i : ℕ)) x = false := hi
  show val gates a x = false
  cases hv : val gates a x with
  | false => rfl
  | true =>
    have ht : val gates (N + (i : ℕ)) x = true :=
      (val_or gates x i i.2 hop).mpr ⟨a, ha, (hb i).2 a ha, hv⟩
    rw [hi'] at ht
    exact absurd ht (by simp)

theorem part3 {N : ℕ} (gates : List Gate) (u : ℕ) (L0 : Finset (Fin N)) (r : Fin N)
    (x : Fin N → Bool) (hx : ∀ v, x v = true → v ∉ L0 ∨ v = r)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h2 : ∀ p : Fin N, InTop gates N u (p : ℕ) → p ∈ L0) :
    ∀ Y : ℕ, InTop gates N u Y → val gates Y x = true →
      InTop gates N u (r : ℕ) ∨ ∃ a : ℕ, InTop gates N u a ∧
        (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
        val gates a x = true := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | ind Y ih =>
    intro hY hv
    by_cases hw : Y < N
    · left
      rw [val_input gates x Y hw] at hv
      rcases hx _ hv with h | h
      · exact absurd (h2 ⟨Y, hw⟩ hY) h
      · subst h
        exact hY
    by_cases hlt : Y < N + gates.length
    · have hi : Y - N < gates.length := by omega
      have he : N + (Y - N) = Y := by omega
      rcases (hg gates[Y - N] (List.getElem_mem hi)).1 with ha | ho
      · right
        refine ⟨Y, hY, ⟨⟨Y - N, hi⟩, he.symm, ?_⟩, hv⟩
        simpa [List.get_eq_getElem] using ha
      · have hv' : val gates (N + (Y - N)) x = true := by rw [he]; exact hv
        have hY' : InTop gates N u (N + (Y - N)) := by rw [he]; exact hY
        have ho' : (gates.get ⟨Y - N, hi⟩).op = GateOp.or := by
          simpa [List.get_eq_getElem] using ho
        obtain ⟨c, hc, hclt, hct⟩ := (val_or gates x (Y - N) hi ho).mp hv'
        exact ih c (by omega) (top_step gates N u ⟨Y - N, hi⟩ hY' ho' c hc) hct
    · rw [val_big gates x Y (by omega)] at hv
      exact absurd hv (by simp)

end PEqualNP.Outside.L_meta_1638

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1638 in
theorem PEqualNP.Outside.L_meta_1638 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hg hb1 hb2 hu
  have hb : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ) := fun i => ⟨hb1 i, hb2 i⟩
  have hu' : val gates u (fun v : Fin N => decide (v ∉ L i0)) = false := by
    simpa [val, eval_eq] using hu
  have h1 : ∀ Y : ℕ, InTop gates N u Y →
      Circuit.eval ⟨gates, Y⟩ (List.ofFn fun v : Fin N => decide (v ∉ L i0)) = false := by
    intro Y hY
    simpa [val, eval_eq] using part1 gates u (fun v : Fin N => decide (v ∉ L i0)) hb hu' Y hY
  have h2 : ∀ p : Fin N, InTop gates N u (p : ℕ) → p ∈ L i0 := by
    intro p hp
    have h := part1 gates u (fun v : Fin N => decide (v ∉ L i0)) hb hu' p hp
    rw [val_input gates _ p p.2] at h
    exact not_not.mp (of_decide_eq_false h)
  refine ⟨h1, h2, ?_, ?_⟩
  · intro r hr hv
    have hv' : val gates u (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true := by
      simpa [val, eval_eq] using hv
    rcases part3 gates u (L i0) r (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))
      (by intro v hv; exact of_decide_eq_true hv) hg h2 u (fun S hS _ => hS) hv' with h | ⟨a, ha, hand, haval⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, hand, by simpa [val, eval_eq] using haval⟩
  · intro a c hop _ hc _ r _ hv
    have hop' : gates[a.1].op = GateOp.and := by simpa [List.get_eq_getElem] using hop
    have hc' : c ∈ gates[a.1].inputs := by simpa [List.get_eq_getElem] using hc
    have hv' : val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true := by
      simpa [val, eval_eq] using hv
    have := ((val_and gates (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) a.1 a.2 hop').mp hv' c hc').2
    simpa [val, eval_eq] using this
