import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1586
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

-- The value of wire `w` on input `x`.
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

abbrev Reach (gs : List Gate) (n u y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S →
    (∀ i : Fin gs.length, n + (i : ℕ) ∈ S → (gs.get i).op = GateOp.or →
      ∀ a ∈ (gs.get i).inputs, a ∈ S) → y ∈ S

lemma reach_self (gs : List Gate) (n u : ℕ) : Reach gs n u u := by
  intro S hu _
  exact hu

lemma reach_trans {gs : List Gate} {n u v w : ℕ}
    (h : Reach gs n u v) (h' : Reach gs n v w) : Reach gs n u w := by
  intro S hu hc
  exact h' S (h S hu hc) hc

lemma reach_child (gs : List Gate) (n : ℕ) (i : Fin gs.length)
    (hop : (gs.get i).op = GateOp.or) (a : ℕ) (ha : a ∈ (gs.get i).inputs) :
    Reach gs n (n + (i : ℕ)) a := by
  intro S hi hc
  exact hc i hi hop a ha

lemma reach_false (gs : List Gate) {n : ℕ}
    (hprev : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < n + (i : ℕ))
    (x : Fin n → Bool) (u y : ℕ) (hu : val gs u x = false)
    (hreach : Reach gs n u y) : val gs y x = false := by
  apply hreach {w | val gs w x = false} hu
  intro i hi hop a ha
  change val gs a x = false
  apply Bool.eq_false_iff.mpr
  intro ht
  have ht' : val gs (n + (i : ℕ)) x = true :=
    (val_or gs x i i.isLt hop).2 ⟨a, ha, hprev i a ha, ht⟩
  change val gs (n + (i : ℕ)) x = false at hi
  rw [hi] at ht'
  contradiction

lemma extract_atom (gs : List Gate) {n : ℕ}
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (u : ℕ) (hu : val gs u x = true) :
    ∃ y : ℕ, Reach gs n u y ∧
      ((∃ p : Fin n, y = (p : ℕ) ∧ x p = true) ∨
       (∃ i : Fin gs.length, y = n + (i : ℕ) ∧
         (gs.get i).op = GateOp.and ∧ val gs y x = true)) := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    by_cases hin : u < n
    · exact ⟨u, reach_self gs n u, Or.inl ⟨⟨u, hin⟩, rfl,
        by simpa [val_input gs x u hin] using hu⟩⟩
    · have hbound : u < n + gs.length := by
        by_contra hb
        have hf := val_big gs x u (by omega)
        rw [hf] at hu
        contradiction
      let i : Fin gs.length := ⟨u - n, by omega⟩
      have he : n + (i : ℕ) = u := by dsimp [i]; omega
      rcases hops (gs.get i) (List.get_mem gs i) with hand | hor
      · exact ⟨u, reach_self gs n u, Or.inr ⟨i, he.symm, hand, hu⟩⟩
      · have ht : val gs (n + (i : ℕ)) x = true := by simpa [he] using hu
        obtain ⟨a, ha, halt, hat⟩ := (val_or gs x i i.isLt hor).1 ht
        obtain ⟨y, hy, hyatom⟩ := ih a (by omega) hat
        refine ⟨y, ?_, hyatom⟩
        have hc := reach_child gs n i hor a ha
        rw [he] at hc
        exact reach_trans hc hy

end PEqualNP.Outside.L_meta_1586

open PEqualNP.Outside.L_meta_1586
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1586 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  classical
  intro q m N L i0 T0 hq hm hmq hN hcard hinter hjoin hsub hsize gates u hleg hprev hu
  have hp : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ) :=
    fun i => (hprev i).2
  have hf : ∀ y, Reach gates N u y →
      val gates y (fun v : Fin N => decide (v ∉ L i0)) = false := by
    intro y hy
    exact reach_false gates hp _ u y hu hy
  have hin : ∀ p : Fin N, Reach gates N u (p : ℕ) → p ∈ L i0 := by
    intro p hreach
    have h := hf p hreach
    rw [val_input gates _ p p.isLt] at h
    simpa using h
  refine ⟨hf, hin, ?_, ?_⟩
  · intro r hr ht
    obtain ⟨y, hy, ha⟩ := extract_atom gates
      (fun g hg => (hleg g hg).1)
      (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) u ht
    rcases ha with ⟨p, rfl, hptrue⟩ | ⟨i, hi, hand, htrue⟩
    · have hpL := hin p hy
      have hpr : p = r := by simpa [hpL] using hptrue
      subst p
      exact Or.inl hy
    · exact Or.inr ⟨y, hy, ⟨i, hi, hand⟩, htrue⟩
  · intro a c hop _ hc _ r _ htrue
    exact ((val_and gates (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))
      a a.isLt hop).1 htrue c hc).2
