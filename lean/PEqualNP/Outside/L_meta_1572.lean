import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572

open PEqualNP.CircuitLowerBounds

private def appendGate (wires : List Bool) (gate : Gate) : List Bool :=
  wires ++ [gate.op.eval (gate.inputs.map fun i => wires.getD i false)]

private def run (gates : List Gate) (bits : List Bool) : List Bool :=
  gates.foldl appendGate bits

private lemma run_cons (gate : Gate) (gates : List Gate) (bits : List Bool) :
    run (gate :: gates) bits = run gates (appendGate bits gate) := rfl

private lemma run_length (gates : List Gate) (bits : List Bool) :
    (run gates bits).length = bits.length + gates.length := by
  induction gates generalizing bits with
  | nil => simp [run]
  | cons gate gates ih =>
    rw [run_cons, ih]
    simp only [appendGate, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma run_getD (gates : List Gate) (bits : List Bool) (w : ℕ) (hw : w < bits.length) :
    (run gates bits).getD w false = bits.getD w false := by
  induction gates generalizing bits with
  | nil => rfl
  | cons gate gates ih =>
    rw [run_cons, ih _ (by simp [appendGate]; omega), appendGate, List.getD_append _ _ _ _ hw]

private lemma run_take_drop (gates : List Gate) (bits : List Bool) (i : ℕ) :
    run gates bits = run (gates.drop i) (run (gates.take i) bits) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun gs => run gs bits) (List.take_append_drop i gates).symm

private abbrev evalOn (gates : List Gate) (w : ℕ) (f : Fin 13 → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn f)

private lemma eval_input (gates : List Gate) (f : Fin 13 → Bool) (p : Fin 13) :
    evalOn gates p f = f p := by
  change (run gates (List.ofFn f)).getD p false = f p
  have hp : (p : ℕ) < (List.ofFn f).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  exact List.getElem_ofFn hp

private lemma eval_missing (gates : List Gate) (f : Fin 13 → Bool) (w : ℕ)
    (hw : 13 + gates.length ≤ w) : evalOn gates w f = false := by
  change (run gates (List.ofFn f)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

private lemma eval_gate (gates : List Gate)
    (earlier : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (i : Fin gates.length) (f : Fin 13 → Bool) :
    evalOn gates (13 + (i : ℕ)) f =
      (gates.get i).op.eval ((gates.get i).inputs.map fun w => evalOn gates w f) := by
  let bits := run (gates.take i.val) (List.ofFn f)
  have hlen : bits.length = 13 + (i : ℕ) := by
    simp [bits, run_length, List.length_take_of_le i.isLt.le]
  have hsplit :
      run gates (List.ofFn f) = run (gates.get i :: gates.drop (i.val + 1)) bits := by
    rw [run_take_drop gates (List.ofFn f) i.val, List.drop_eq_getElem_cons i.isLt]
    rfl
  have hread : ∀ w ∈ (gates.get i).inputs, bits.getD w false = evalOn gates w f := by
    intro w hw
    change bits.getD w false = (run gates (List.ofFn f)).getD w false
    rw [hsplit]
    exact (run_getD _ bits w (by rw [hlen]; exact earlier i w hw)).symm
  change (run gates (List.ofFn f)).getD (13 + (i : ℕ)) false = _
  rw [hsplit, run_cons, run_getD _ _ _ (by simp [appendGate, hlen]), appendGate,
    List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self, List.getD_cons_zero]
  exact congrArg (gates.get i).op.eval (List.map_congr_left hread)

private lemma eval_and (gates : List Gate)
    (earlier : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (i : Fin gates.length) (hop : (gates.get i).op = GateOp.and) (f : Fin 13 → Bool) :
    evalOn gates (13 + (i : ℕ)) f = true ↔
      ∀ w ∈ (gates.get i).inputs, evalOn gates w f = true := by
  rw [eval_gate gates earlier i, hop]
  simp [GateOp.eval]

private lemma eval_or (gates : List Gate)
    (earlier : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (i : Fin gates.length) (hop : (gates.get i).op = GateOp.or) (f : Fin 13 → Bool) :
    evalOn gates (13 + (i : ℕ)) f = true ↔
      ∃ w ∈ (gates.get i).inputs, evalOn gates w f = true := by
  rw [eval_gate gates earlier i, hop]
  simp [GateOp.eval]

private lemma eval_mono (gates : List Gate)
    (ops : ∀ i : Fin gates.length, (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or)
    (earlier : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (x y : Fin 13 → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    evalOn gates w x = true → evalOn gates w y = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hinput : w < 13
    · simpa only [eval_input gates _ (⟨w, hinput⟩ : Fin 13)] using
        hxy ⟨w, hinput⟩ ((eval_input gates x ⟨w, hinput⟩) ▸ hx)
    by_cases hgate : w < 13 + gates.length
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hw : w = 13 + (i : ℕ) := by dsimp [i]; omega
      rw [hw] at hx ⊢
      rcases ops i with hand | hor
      · apply (eval_and gates earlier i hand y).2
        intro a ha
        exact ih a (hw.symm ▸ earlier i a ha) ((eval_and gates earlier i hand x).1 hx a ha)
      · obtain ⟨a, ha, hax⟩ := (eval_or gates earlier i hor x).1 hx
        exact (eval_or gates earlier i hor y).2 ⟨a, ha, ih a (hw.symm ▸ earlier i a ha) hax⟩
    · simp [eval_missing gates x w (by omega)] at hx

private def orReach (gates : List Gate) (start target : ℕ) : Prop :=
  ∀ S : Set ℕ, start ∈ S →
    (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) → target ∈ S

private def isAndWire (gates : List Gate) (w : ℕ) : Prop :=
  ∃ i : Fin gates.length, w = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and

private lemma find_and (gates : List Gate)
    (ops : ∀ i : Fin gates.length, (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or)
    (earlier : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (x y z : Fin 13 → Bool)
    (noInput : ∀ p, x p = true → y p = false → z p = false → False) (w : ℕ)
    (hx : evalOn gates w x = true) (hy : evalOn gates w y = false)
    (hz : evalOn gates w z = false) :
    ∃ target, orReach gates w target ∧ isAndWire gates target ∧ evalOn gates target x = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hinput : w < 13
    · let p : Fin 13 := ⟨w, hinput⟩
      rw [show w = (p : ℕ) from rfl, eval_input] at hx hy hz
      exact (noInput p hx hy hz).elim
    by_cases hgate : w < 13 + gates.length
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hw : w = 13 + (i : ℕ) := by dsimp [i]; omega
      rcases ops i with hand | hor
      · exact ⟨w, fun _ hwS _ => hwS, ⟨i, hw, hand⟩, hx⟩
      · obtain ⟨a, ha, hax⟩ := (eval_or gates earlier i hor x).1 (hw ▸ hx)
        have child_false (f : Fin 13 → Bool) (hf : evalOn gates w f = false) :
            evalOn gates a f = false := by
          apply Bool.eq_false_iff.mpr
          intro haf
          have htrue := (eval_or gates earlier i hor f).2 ⟨a, ha, haf⟩
          rw [← hw, hf] at htrue
          exact Bool.noConfusion htrue
        obtain ⟨target, hreach, hAnd, ht⟩ :=
          ih a (hw.symm ▸ earlier i a ha) hax (child_false y hy) (child_false z hz)
        refine ⟨target, ?_, hAnd, ht⟩
        intro S hwS hclosed
        exact hreach S (hclosed i (hw ▸ hwS) hor a ha) hclosed
    · simp [eval_missing gates x w (by omega)] at hx

private abbrev testInput (base other point v : Fin 13) : Bool :=
  decide (v = point ∨ (point ≠ base ∧ v = other))

private abbrev complementInput (line : Finset (Fin 13)) (v : Fin 13) : Bool :=
  decide (v ∉ line)

private lemma find_for_line (gates : List Gate)
    (ops : ∀ i : Fin gates.length, (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or)
    (earlier : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (w : ℕ) (line cross : Finset (Fin 13)) (base other c : Fin 13)
    (hbase : base ∉ cross) (hother : other ∉ line) (hinter : line ∩ cross = {c})
    (hline : evalOn gates w (complementInput line) = false)
    (hcross : evalOn gates w (complementInput cross) = false)
    (htwo : 2 ≤ (line.filter fun p => evalOn gates w (testInput base other p) = true).card) :
    ∃ target, orReach gates w target ∧ isAndWire gates target ∧
      ∃ p ∈ line, p ≠ base ∧ p ≠ c ∧ evalOn gates target (testInput base other p) = true := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (show 1 < _ from htwo)
  obtain ⟨point, hpoint, hpc⟩ : ∃ point, point ∈
      (line.filter fun p => evalOn gates w (testInput base other p) = true) ∧ point ≠ c := by
    by_cases h : p = c
    · exact ⟨q, hq, fun eq => hpq (h.trans eq.symm)⟩
    · exact ⟨p, hp, h⟩
  obtain ⟨hpLine, hpTrue⟩ := Finset.mem_filter.mp hpoint
  have hpBase : point ≠ base := by
    intro eq
    subst point
    have hmono : ∀ v, testInput base other base v = true → complementInput cross v = true := by
      intro v hv
      have hvBase : v = base := by simpa [testInput] using hv
      simpa [complementInput, hvBase] using hbase
    have htrue := eval_mono gates ops earlier _ _ hmono w hpTrue
    rw [hcross] at htrue
    exact Bool.noConfusion htrue
  have noInput (v : Fin 13) (hv : testInput base other point v = true)
      (hvLine : complementInput line v = false) (hvCross : complementInput cross v = false) :
      False := by
    have hvLine' : v ∈ line := by simpa [complementInput] using hvLine
    have hvCross' : v ∈ cross := by simpa [complementInput] using hvCross
    have hvEq : v = c := by
      have hmem : v ∈ line ∩ cross := Finset.mem_inter.mpr ⟨hvLine', hvCross'⟩
      simpa [hinter] using hmem
    have htest : v = point ∨ (point ≠ base ∧ v = other) := of_decide_eq_true hv
    rcases htest with heq | ⟨_, heq⟩
    · exact hpc (heq.symm.trans hvEq)
    · exact hother (heq ▸ hvLine')
  obtain ⟨target, hreach, hAnd, htrue⟩ :=
    find_and gates ops earlier _ _ _ noInput w hpTrue hline hcross
  exact ⟨target, hreach, hAnd, point, hpLine, hpBase, hpc, htrue⟩

private lemma one_outside : ∀ t : Fin 13, t ∈ ({4, 10, 12} : Finset (Fin 13)) →
    (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by decide

private lemma zero_outside : ∀ t : Fin 13, t ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by decide

end PEqualNP.Outside.L_meta_1572

open PEqualNP.Outside.L_meta_1572

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates g l m c hop hinputs hl hm hc hEvalL hEvalM
  have ops (i : Fin gates.length) :
      (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    (hop _ (List.get_mem _ _)).1
  have earlier (i : Fin gates.length) := (hinputs i).2
  have h0 : (0 : Fin 13) ∉ L m := by rw [hL]; exact zero_outside m hm
  have h1 : (1 : Fin 13) ∉ L l := by rw [hL]; exact one_outside l hl
  constructor
  · exact find_for_line gates ops earlier g (L l) (L m) 0 1 c h0 h1 hc hEvalL hEvalM
  · exact find_for_line gates ops earlier g (L m) (L l) 1 0 c h1 h0
      ((Finset.inter_comm _ _).trans hc) hEvalM hEvalL
