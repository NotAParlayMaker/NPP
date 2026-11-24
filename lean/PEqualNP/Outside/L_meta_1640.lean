import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1640

open PEqualNP.CircuitLowerBounds

private def evalGates (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private lemma evalGates_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    evalGates (g :: gs) xs =
      evalGates gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) :=
  rfl

private lemma evalGates_length (gs : List Gate) (xs : List Bool) :
    (evalGates gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih]
    simp
    omega

private lemma evalGates_prefix (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (evalGates gs xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGates_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma evalGates_take_drop (gs : List Gate) (xs : List Bool) (k : ℕ) :
    evalGates gs xs = evalGates (gs.drop k) (evalGates (gs.take k) xs) := by
  simpa only [evalGates, List.foldl_append] using
    congrArg (fun l : List Gate => evalGates l xs) (List.take_append_drop k gs).symm

private def wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    wireVal C x p = x p := by
  change (evalGates C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [evalGates_prefix _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma wireVal_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wireVal C x w = false := by
  change (evalGates C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [evalGates_length] using hw)

private lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.gates.length) :
    let g := C.gates[w - n]'(by omega)
    wireVal C x w = g.op.eval (g.inputs.map fun r => if r < w then wireVal C x r else false) := by
  let idx := w - n
  have hidx : idx < C.gates.length := by omega
  let g := C.gates[idx]
  let pref := evalGates (C.gates.take idx) (List.ofFn x)
  have hplen : pref.length = w := by
    simp [pref, evalGates_length, Nat.min_eq_left hidx.le, idx]
    omega
  have hsplit :
      evalGates C.gates (List.ofFn x) = evalGates (g :: C.gates.drop (idx + 1)) pref := by
    rw [evalGates_take_drop C.gates (List.ofFn x) idx, List.drop_eq_getElem_cons hidx]
  have hread (r : ℕ) : pref.getD r false = if r < w then wireVal C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change pref.getD r false = (evalGates C.gates (List.ofFn x)).getD r false
      rw [hsplit]
      exact (evalGates_prefix _ pref r (by omega)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (evalGates C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then wireVal C x r else false)
  rw (occs := [1]) [hsplit]
  rw (occs := [1]) [evalGates_cons]
  rw [evalGates_prefix _ _ _ (by simp [hplen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [hplen, Nat.sub_self, List.getD_cons_zero, hread]


private lemma gate_value {N : ℕ} (gs : List Gate) (i : Fin gs.length) (x : Fin N → Bool)
    (hlt : ∀ e ∈ (gs.get i).inputs, e < N + i.val) :
    wireVal ⟨gs, 0⟩ x (N + i.val) =
      (gs.get i).op.eval ((gs.get i).inputs.map (wireVal ⟨gs, 0⟩ x)) := by
  have h := wireVal_gate (Circuit.mk gs 0) x (N + i.val) (by omega)
    (by change N + i.val < N + gs.length; omega)
  simp only [Nat.add_sub_cancel_left] at h
  refine h.trans (congrArg (gs.get i).op.eval ?_)
  apply List.map_congr_left
  intro e he
  exact ite_eq_left (hlt e he)

end PEqualNP.Outside.L_meta_1640

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1640

theorem PEqualNP.Outside.L_meta_1640 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (ch : Fin gates.length → ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) →
    (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) → ch a ∈ (gates.get a).inputs ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, ch a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) →
    (∀ r ∈ L i0 \ T0, (∀ S : Set ℕ, o ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨
      ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) ∧ (∀ S : Set ℕ, ch a ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S)) ∧
    (∀ a : Fin gates.length, o = N + (a : ℕ) → (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true)) := by
  intro q m N L i0 T0 hq hm hmq hN hsize hinter hline hsub hcard
  intro gs o ch hops hnonempty hprev hout hflip hchoose
  let C : Circuit := ⟨gs, 0⟩
  let x : Fin N → Bool := fun v => decide (v ∉ L i0)
  let y (r : Fin N) : Fin N → Bool := fun v => decide (v ∉ L i0 ∨ v = r)
  let rim := L i0 \ T0
  let carrying (a : Fin gs.length) := (gs.get a).op = GateOp.and ∧
    wireVal C x (N + a.val) = false ∧
    ∃ r ∈ rim, wireVal C (y r) (N + a.val) = true
  let reaches (w r : ℕ) := ∀ S : Set ℕ, w ∈ S →
    (∀ i : Fin gs.length, N + i.val ∈ S → (gs.get i).op = GateOp.or →
      ∀ e ∈ (gs.get i).inputs, e ∈ S) → r ∈ S
  change wireVal C x o = false at hout
  change ∀ r ∈ rim, wireVal C (y r) o = true at hflip
  change ∀ a, carrying a → ch a ∈ (gs.get a).inputs ∧ wireVal C x (ch a) = false at hchoose
  constructor
  · intro r hr
    change reaches o r ∨ ∃ a, carrying a ∧ reaches (ch a) r
    have trace (w : ℕ) : wireVal C x w = false → wireVal C (y r) w = true →
        reaches w r ∨ ∃ a, carrying a ∧ reaches (ch a) r := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hf ht
        by_cases hp : w < N
        · let p : Fin N := ⟨w, hp⟩
          change wireVal C x p = false at hf
          change wireVal C (y r) p = true at ht
          rw [wireVal_input] at hf ht
          have hpr : p = r := by
            simpa [y, show p ∈ L i0 by simpa [x] using hf] using ht
          exact Or.inl fun S hw _ => by simpa [← hpr, p] using hw
        by_cases hw : w < N + gs.length
        · let a : Fin gs.length := ⟨w - N, by omega⟩
          have ha : N + a.val = w := by dsimp [a]; omega
          have form (z : Fin N → Bool) : wireVal C z w =
              (gs.get a).op.eval ((gs.get a).inputs.map (wireVal C z)) := by
            exact ha ▸ gate_value gs a z (hprev a)
          rcases (hops _ (List.get_mem gs a)).1 with hand | hor
          · have hc : carrying a := ⟨hand, ha.symm ▸ hf, r, hr, ha.symm ▸ ht⟩
            obtain ⟨he, he0⟩ := hchoose a hc
            rw [form, hand] at ht
            have he1 : wireVal C (y r) (ch a) = true := by
              exact (List.all_eq_true.mp ht) _ (List.mem_map.mpr ⟨_, he, rfl⟩)
            rcases ih _ (ha ▸ hprev a _ he) he0 he1 with h | h
            · exact Or.inr ⟨a, hc, h⟩
            · exact Or.inr h
          · rw [form, hor] at hf ht
            change (((gs.get a).inputs.map (wireVal C (y r))).any id) = true at ht
            obtain ⟨_, hb, hb1⟩ := List.any_eq_true.mp ht
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
            have he0 : wireVal C x e = false := by
              simpa using (List.any_eq_false.mp hf) (wireVal C x e) (List.mem_map.mpr ⟨_, he, rfl⟩)
            rcases ih _ (ha ▸ hprev a _ he) he0 hb1 with h | h
            · exact Or.inl fun S hwS hS => h S (hS a (ha.symm ▸ hwS) hor e he) hS
            · exact Or.inr h
        · have := wireVal_oob C (y r) w (by change N + gs.length ≤ w; omega)
          exact (Bool.noConfusion (this.symm.trans ht))
    exact trace o hout (hflip r hr)
  · intro a he hand
    obtain ⟨r, hr⟩ : rim.Nonempty := by
      apply Finset.card_pos.mp
      dsimp [rim]
      rw [Finset.card_sdiff_of_subset hsub, hsize, hcard]
      omega
    exact ⟨hand, he ▸ hout, r, hr, he ▸ hflip r hr⟩
