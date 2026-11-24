import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1638

open PEqualNP.CircuitLowerBounds

private def run (gates : List Gate) (xs : List Bool) : List Bool :=
  Circuit.wires ⟨gates, 0⟩ xs

private lemma run_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    run (g :: gs) xs = run gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) :=
  rfl

private lemma run_length (gates : List Gate) (xs : List Bool) :
    (run gates xs).length = xs.length + gates.length := by
  induction gates generalizing xs with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp
    omega

private lemma run_prefix (gates : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (run gates xs).getD w false = xs.getD w false := by
  induction gates generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private def value {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

private lemma input_value {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (p : Fin n) :
    value gates x p = x p := by
  change (run gates (List.ofFn x)).getD p false = x p
  have hp : p.val < (List.ofFn x).length := by simp
  rw [run_prefix _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : value gates x w = false := by
  change (run gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

private lemma gate_value {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (i : Fin gates.length)
    (hEarlier : ∀ w ∈ (gates.get i).inputs, w < n + i.val) :
    value gates x (n + i.val) =
      (gates.get i).op.eval ((gates.get i).inputs.map fun w => value gates x w) := by
  let g := gates.get i
  let xs := List.ofFn x
  let earlier := run (gates.take i.val) xs
  have plen : earlier.length = n + i.val := by simp [earlier, xs, run_length]
  have split : run gates xs = run (g :: gates.drop (i.val + 1)) earlier := by
    have h := congrArg (fun gs : List Gate => run gs xs) (List.take_append_drop i.val gates).symm
    simpa only [earlier, g, List.get_eq_getElem, run, Circuit.wires, List.foldl_append,
      List.drop_eq_getElem_cons i.isLt] using h
  have reads : g.inputs.map (fun w => earlier.getD w false) =
      g.inputs.map (fun w => value gates x w) := by
    apply List.map_congr_left
    intro w hw
    change earlier.getD w false = (run gates xs).getD w false
    rw [split]
    exact (run_prefix _ earlier w (by simpa only [plen] using hEarlier w hw)).symm
  change (run gates xs).getD (n + i.val) false =
    g.op.eval (g.inputs.map fun w => value gates x w)
  rw [split, run_cons, run_prefix _ _ _ (by simp [plen]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, reads]

private lemma or_true {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (i : Fin gates.length)
    (hEarlier : ∀ w ∈ (gates.get i).inputs, w < n + i.val)
    (hop : (gates.get i).op = GateOp.or) :
    value gates x (n + i.val) = true ↔ ∃ w ∈ (gates.get i).inputs, value gates x w = true := by
  rw [gate_value gates x i hEarlier, hop]
  simp [GateOp.eval]

private lemma and_true {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (i : Fin gates.length)
    (hEarlier : ∀ w ∈ (gates.get i).inputs, w < n + i.val)
    (hop : (gates.get i).op = GateOp.and) :
    value gates x (n + i.val) = true ↔ ∀ w ∈ (gates.get i).inputs, value gates x w = true := by
  rw [gate_value gates x i hEarlier, hop]
  simp [GateOp.eval]

private def Reaches {n : ℕ} (gates : List Gate) (u w : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S →
    (∀ i : Fin gates.length, n + i.val ∈ S → (gates.get i).op = GateOp.or →
      ∀ e ∈ (gates.get i).inputs, e ∈ S) → w ∈ S

private lemma reaches_step {n : ℕ} {gates : List Gate} {u : ℕ} (i : Fin gates.length)
    (hi : Reaches (n := n) gates u (n + i.val)) (hop : (gates.get i).op = GateOp.or)
    {w : ℕ} (hw : w ∈ (gates.get i).inputs) : Reaches (n := n) gates u w :=
  fun S hu hclosed => hclosed i (hi S hu hclosed) hop w hw

end PEqualNP.Outside.L_meta_1638

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1638

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
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hOps _ hEarlier hu
  let off : Fin N → Bool := fun v => decide (v ∉ L i0)
  let rim (r : Fin N) (v : Fin N) : Bool := decide (v ∉ L i0 ∨ v = r)
  -- The wires that are false on the off-line input form an OR-closed set.
  have hFalse (w : ℕ) (hw : Reaches (n := N) gates u w) : value gates off w = false := by
    apply hw {e | value gates off e = false} hu
    intro i hi hop e he
    exact Bool.eq_false_iff.mpr fun ht =>
      Bool.noConfusion (hi.symm.trans ((or_true gates off i (hEarlier i) hop).mpr ⟨e, he, ht⟩))
  have hInput (p : Fin N) (hp : Reaches (n := N) gates u p) : p ∈ L i0 := by
    simpa [input_value, off] using hFalse p hp
  refine ⟨hFalse, hInput, ?_, ?_⟩
  · intro r _ hTrue
    have descend (w : ℕ) : Reaches (n := N) gates u w → value gates (rim r) w = true →
        Reaches (n := N) gates u r ∨
          ∃ a : ℕ, Reaches (n := N) gates u a ∧
            (∃ i : Fin gates.length, a = N + i.val ∧ (gates.get i).op = GateOp.and) ∧
            value gates (rim r) a = true := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw ht
        by_cases hInputWire : w < N
        · let p : Fin N := ⟨w, hInputWire⟩
          change Reaches (n := N) gates u p at hw
          change value gates (rim r) p = true at ht
          have hp := hInput p hw
          have hpr : p = r := by simpa [input_value, rim, hp] using ht
          exact Or.inl (hpr ▸ hw)
        by_cases hGateWire : w < N + gates.length
        · let i : Fin gates.length := ⟨w - N, by omega⟩
          have hwi : w = N + i.val := by dsimp [i]; omega
          rw [hwi] at hw ht
          rcases (hOps _ (List.get_mem gates i)).1 with hop | hop
          · exact Or.inr ⟨N + i.val, hw, ⟨i, rfl, hop⟩, ht⟩
          · obtain ⟨e, he, hEt⟩ := (or_true gates (rim r) i (hEarlier i) hop).mp ht
            exact ih e (hwi ▸ hEarlier i e he) (reaches_step i hw hop he) hEt
        · rw [missing_value gates (rim r) w (by omega)] at ht
          exact Bool.noConfusion ht
    exact descend u (fun _ h _ => h) hTrue
  · intro a c hop _ hc _ r _ ht
    exact (and_true gates (rim r) a (hEarlier a) hop).mp ht c hc
