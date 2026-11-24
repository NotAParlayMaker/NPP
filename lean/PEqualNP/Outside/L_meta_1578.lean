import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1578

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

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

def off (L : Fin 13 → Finset (Fin 13)) (t v : Fin 13) : Bool :=
  decide (v ∉ L t)

def testPoint (L : Fin 13 → Finset (Fin 13)) (p v : Fin 13) : Bool :=
  decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0))

theorem propagate (gs : List Gate) (z : Fin gs.length) (a b x : Fin 13 → Bool)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (base : ∀ j, x j = true → a j = true ∨ b j = true)
    (early : ∀ i : Fin gs.length, i < z → (gs.get i).op = GateOp.and →
      val gs (13 + i.val) a = false → val gs (13 + i.val) b = false →
      val gs (13 + i.val) x = false)
    (w : ℕ) : w < 13 + z.val → val gs w x = true →
      val gs w a = true ∨ val gs w b = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    by_cases small : w < 13
    · rw [val_input _ _ _ small] at hx ⊢
      rw [val_input _ _ _ small]
      exact base _ hx
    · let i : Fin gs.length := ⟨w - 13, by have := z.isLt; omega⟩
      have heq : 13 + i.val = w := by dsimp [i]; omega
      have hiz : i < z := by change w - 13 < z.val; omega
      rcases ops (gs.get i) (List.get_mem _ i) with hand | hor
      · by_contra! h
        have f := early i hiz hand (by simpa [heq] using h.1) (by simpa [heq] using h.2)
        simp [heq, hx] at f
      · obtain ⟨j, hj, hjlt, hjx⟩ := (val_or gs x i.val i.isLt hor).mp (by simpa only [heq] using hx)
        rcases ih j (by simpa only [heq] using hjlt) (by omega) hjx with ha | hb
        · left
          rw [← heq]
          exact (val_or gs a i.val i.isLt hor).mpr ⟨j, hj, hjlt, ha⟩
        · right
          rw [← heq]
          exact (val_or gs b i.val i.isLt hor).mpr ⟨j, hj, hjlt, hb⟩

theorem geometry : ∀ (t p : Fin 13),
    (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13))) →
    (p = 3 ∨ p = 9) → p ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  decide

theorem split_values : ∀ (a b c d e f : Bool),
    (a && d) = false → (b && e) = false → (c && f) = false →
    (a = true ∨ b = true) → (a = true ∨ c = true) →
    (d = true ∨ e = true) → (d = true ∨ f = true) →
    (b = false ∧ c = false ∧ a = true ∧ d = false ∧ e = true ∧ f = true) ∨
    (e = false ∧ f = false ∧ d = true ∧ a = false ∧ b = true ∧ c = true) := by
  intro a b c d e f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

end PEqualNP.Outside.L_meta_1578

open PEqualNP.Outside.L_meta_1578 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1578 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = true) →
    (∀ i : Fin gates.length, i < zs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = false) →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) ∨
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) := by
  intro L hL gates z u v l m hops hwf hl hm hand huv h0 hl0 hm0 hx hearly
  obtain ⟨p, hp, hx⟩ : ∃ p : Fin 13, (p = 3 ∨ p = 9) ∧
      val gates (13 + z.val) (testPoint L p) = true := by
    rcases hx with h | h
    · exact ⟨3, Or.inl rfl, h⟩
    · exact ⟨9, Or.inr rfl, h⟩
  have bound (w : ℕ) (h : w = u ∨ w = v) : w < 13 + z.val := by
    apply (hwf z).2
    rw [huv]
    simpa using h
  have binary (y : Fin 13 → Bool) :
      val gates (13 + z.val) y = (val gates u y && val gates v y) := by
    apply Bool.eq_iff_iff.mpr
    rw [val_and gates y z.val z.isLt hand]
    change (∀ i ∈ (gates.get z).inputs, i < 13 + z.val ∧ val gates i y = true) ↔ _
    rw [huv]
    simp [bound u (Or.inl rfl), bound v (Or.inr rfl)]
  rw [binary] at hx
  obtain ⟨hux, hvx⟩ := Bool.and_eq_true_iff.mp hx
  have cover (t : Fin 13)
      (ht : t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13)))
      (w : ℕ) (hw : w = u ∨ w = v) (hactive : val gates w (testPoint L p) = true) :
      val gates w (off L 0) = true ∨ val gates w (off L t) = true := by
    apply propagate gates z (off L 0) (off L t) (testPoint L p) (fun g hg => (hops g hg).1) _ _ w (bound w hw) hactive
    · intro j hj
      simp only [testPoint, decide_eq_true_eq] at hj
      rcases hj with rfl | ⟨_, hout⟩
      · right
        simpa only [off, decide_eq_true_eq, hL] using geometry t j ht hp
      · left
        simpa only [off, decide_eq_true_eq] using hout
    · have ht0 : t ≠ 0 := by
        rintro rfl
        have no : ¬ ((0 : Fin 13) ∈ ({4, 10, 12} : Finset (Fin 13)) ∨
            (0 : Fin 13) ∈ ({1, 5, 11} : Finset (Fin 13))) := by decide
        exact no ht
      intro i hi hop hzero htval
      have pair := hearly i hi hop hzero t ht0 htval
      rcases hp with rfl | rfl
      · exact pair.1
      · exact pair.2
  apply split_values
    (val gates u (off L 0)) (val gates u (off L l)) (val gates u (off L m))
    (val gates v (off L 0)) (val gates v (off L l)) (val gates v (off L m))
  · exact (binary (off L 0)) ▸ h0
  · exact (binary (off L l)) ▸ hl0
  · exact (binary (off L m)) ▸ hm0
  · exact cover l (Or.inl hl) u (Or.inl rfl) hux
  · exact cover m (Or.inr hm) u (Or.inl rfl) hux
  · exact cover l (Or.inl hl) v (Or.inr rfl) hvx
  · exact cover m (Or.inr hm) v (Or.inr rfl) hvx
