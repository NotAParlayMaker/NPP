import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1579

open PEqualNP.CircuitLowerBounds

-- The wire evaluation lemmas are adapted from L-meta-1525 and L-meta-1457.
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma or_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.or) :
    value C x w = true ↔ ∃ r ∈ C.gates[w - n].inputs, r < w ∧ value C x r = true := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hv⟩
    by_cases h' : r < w
    · exact ⟨r, hr, h', by simpa [h'] using hv⟩
    · simp [h'] at hv
  · rintro ⟨r, hr, h', hv⟩
    exact ⟨r, hr, by simp [h', hv]⟩

lemma andInput (gates : List Gate) (zs : Fin gates.length) (u v : ℕ) (x : Fin 13 → Bool)
    (hop : (gates.get zs).op = GateOp.and) (hin : (gates.get zs).inputs = [u,v])
    (fires : value ⟨gates, 0⟩ x (13 + (zs : ℕ)) = true) :
    u < 13 + (zs : ℕ) ∧ value ⟨gates, 0⟩ x u = true := by
  have eqn := gate_value (n := 13) ⟨gates, 0⟩ x (13 + (zs : ℕ)) (by omega)
    (by change 13 + (zs : ℕ) < 13 + gates.length; omega)
  change gates[zs.val].op = GateOp.and at hop
  change gates[zs.val].inputs = [u,v] at hin
  simp only [Nat.add_sub_cancel_left] at eqn
  rw [eqn, hop, hin] at fires
  by_cases small : u < 13 + (zs : ℕ)
  · simp [GateOp.eval, small] at fires
    exact ⟨small, fires.1⟩
  · simp [GateOp.eval, small] at fires


lemma orDescent (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ)
    (x A B : Fin 13 → Bool)
    (hOps : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hx : value ⟨gates, 0⟩ x u = true)
    (hA : value ⟨gates, 0⟩ A u = false)
    (hB : value ⟨gates, 0⟩ B u = false)
    (hsafe : ∀ p : Fin 13, x p = true → A p = true ∨ B p = true) :
    ∃ Y : ℕ,
      (∀ S : Set ℕ, u ∈ S →
        (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
          (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
      Y ≤ u ∧ value ⟨gates, 0⟩ A Y = false ∧
      value ⟨gates, 0⟩ B Y = false ∧ value ⟨gates, 0⟩ x Y = true := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
  let Reach : ℕ → Prop := fun w =>
    ∀ S : Set ℕ, u ∈ S →
      (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ∀ a ∈ (gates.get i).inputs, a ∈ S) → w ∈ S
  have huReach : Reach u := by
    intro S huS _
    exact huS
  have descend : ∀ w : ℕ, Reach w → value C x w = true →
      value C A w = false → value C B w = false →
      ∃ Y : ℕ, Reach Y ∧
        (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧
          (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        Y ≤ w ∧ value C A Y = false ∧ value C B Y = false ∧ value C x Y = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwReach hwx hwA hwB
      by_cases hwInput : w < 13
      · let p : Fin 13 := ⟨w, hwInput⟩
        have hxp : x p = true := by
          change value C x p = true at hwx
          rw [input_value] at hwx
          exact hwx
        have hAp : A p = false := by
          change value C A p = false at hwA
          rw [input_value] at hwA
          exact hwA
        have hBp : B p = false := by
          change value C B p = false at hwB
          rw [input_value] at hwB
          exact hwB
        rcases hsafe p hxp with hpA | hpB
        · simp [hAp] at hpA
        · simp [hBp] at hpB
      · by_cases hwGate : w < 13 + gates.length
        · have hi : w - 13 < gates.length := by omega
          let i : Fin gates.length := ⟨w - 13, hi⟩
          have hwi : w = 13 + (i : ℕ) := by simp [i]; omega
          have hmem : gates.get i ∈ gates := by
            simpa [i] using List.getElem_mem hi
          rcases hOps (gates.get i) hmem with hAnd | hOr
          · exact ⟨w, hwReach, ⟨i, hwi, hAnd⟩, le_rfl, hwA, hwB, hwx⟩
          · have hOr' : gates[w - 13].op = PEqualNP.CircuitLowerBounds.GateOp.or := by
              simpa [i] using hOr
            obtain ⟨r, hr, hrlt, hxr⟩ :=
              (or_value C x w (by omega) hi hOr').mp hwx
            have hAr : value C A r = false := by
              cases hva : value C A r with
              | false => rfl
              | true =>
                have hAw' := (or_value C A w (by omega) hi hOr').mpr
                  ⟨r, hr, hrlt, hva⟩
                rw [hwA] at hAw'
                cases hAw'
            have hBr : value C B r = false := by
              cases hvb : value C B r with
              | false => rfl
              | true =>
                have hBw' := (or_value C B w (by omega) hi hOr').mpr
                  ⟨r, hr, hrlt, hvb⟩
                rw [hwB] at hBw'
                cases hBw'
            have hrReach : Reach r := by
              intro S huS hclosed
              have hwS := hwReach S huS hclosed
              have hiS : 13 + (i : ℕ) ∈ S := by simpa [hwi] using hwS
              exact hclosed i hiS hOr r hr
            obtain ⟨Y, hYReach, hYAnd, hYle, hYA, hYB, hYx⟩ :=
              ih r hrlt hrReach hxr hAr hBr
            exact ⟨Y, hYReach, hYAnd, hYle.trans hrlt.le, hYA, hYB, hYx⟩
        · have hwMissing : 13 + C.size ≤ w := by
            change 13 + gates.length ≤ w
            omega
          have hmissing := missing_value C x w hwMissing
          rw [hmissing] at hwx
          cases hwx
  obtain ⟨Y, hYReach, hYAnd, hYle, hYA, hYB, hYx⟩ := descend u huReach hx hA hB
  exact ⟨Y, hYReach, hYAnd, hYle, hYA, hYB, hYx⟩

end PEqualNP.Outside.L_meta_1579

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1579 in
theorem PEqualNP.Outside.L_meta_1579 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (∀ p ∈ L l, p ≠ 0 → p ≠ c → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Y < 13 + (zs : ℕ) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (∀ p ∈ L m, p ≠ 1 → p ≠ c → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Y < 13 + (zs : ℕ) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates zs u v l m c hG hread hl hm hint hop hin hFalseL hFalseM
  have hcMem : c ∈ L l ∩ L m := by rw [hint]; simp
  have hcL : c ∈ L l := (Finset.mem_inter.mp hcMem).1
  have hcM : c ∈ L m := (Finset.mem_inter.mp hcMem).2
  have hc0 : c ≠ (0 : Fin 13) := by
    have h0m : (0 : Fin 13) ∉ L m := by
      have hmCases : m = 1 ∨ m = 5 ∨ m = 11 := by simpa using hm
      rcases hmCases with hm' | hm' | hm' <;> subst m <;> rw [hL] <;> decide
    intro h
    subst c
    exact h0m hcM
  have hc1 : c ≠ (1 : Fin 13) := by
    have h1l : (1 : Fin 13) ∉ L l := by
      have hlCases : l = 4 ∨ l = 10 ∨ l = 12 := by simpa using hl
      rcases hlCases with hl' | hl' | hl' <;> subst l <;> rw [hL] <;> decide
    intro h
    subst c
    exact h1l hcL
  have hOps : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hG g hg).1
  have hsafe (x : Fin 13 → Bool) (hnotc : ∀ p, x p = true → p ≠ c) :
      ∀ p, x p = true →
        (fun q : Fin 13 => decide (q ∉ L l)) p = true ∨
        (fun q : Fin 13 => decide (q ∉ L m)) p = true := by
    intro p hp
    by_cases hA : (fun q : Fin 13 => decide (q ∉ L l)) p = true
    · exact Or.inl hA
    by_cases hB : (fun q : Fin 13 => decide (q ∉ L m)) p = true
    · exact Or.inr hB
    have hAfalse : (fun q : Fin 13 => decide (q ∉ L l)) p = false := by
      cases h : (fun q : Fin 13 => decide (q ∉ L l)) p <;> simp_all
    have hBfalse : (fun q : Fin 13 => decide (q ∉ L m)) p = false := by
      cases h : (fun q : Fin 13 => decide (q ∉ L m)) p <;> simp_all
    have hpL : p ∈ L l := by
      have h := hAfalse
      simp only [decide_eq_false_iff_not, not_not] at h
      exact h
    have hpM : p ∈ L m := by
      have h := hBfalse
      simp only [decide_eq_false_iff_not, not_not] at h
      exact h
    have hpInt : p ∈ L l ∩ L m := Finset.mem_inter.mpr ⟨hpL, hpM⟩
    rw [hint] at hpInt
    exact False.elim (hnotc p hp (Finset.mem_singleton.mp hpInt))
  constructor
  · intro p hp hp0 hpc hfire
    let x : Fin 13 → Bool := fun q => decide (q = p ∨ (p ≠ 0 ∧ q = 1))
    have hfire' : value ⟨gates, 0⟩ x (13 + (zs : ℕ)) = true := by
      change Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn x) = true
      exact hfire
    have hAndInput := andInput gates zs u v x hop hin hfire'
    have hA : value ⟨gates, 0⟩ (fun q => decide (q ∉ L l)) u = false := by
      change Circuit.eval ⟨gates, u⟩ (List.ofFn (fun q => decide (q ∉ L l))) = false
      exact hFalseL
    have hB : value ⟨gates, 0⟩ (fun q => decide (q ∉ L m)) u = false := by
      change Circuit.eval ⟨gates, u⟩ (List.ofFn (fun q => decide (q ∉ L m))) = false
      exact hFalseM
    obtain ⟨Y, hReach, hAnd, hYle, hYA, hYB, hYx⟩ :=
      orDescent gates u x (fun q => decide (q ∉ L l)) (fun q => decide (q ∉ L m))
        hOps hAndInput.2 hA hB (hsafe x (by
          intro q hq
          have htest : q = p ∨ q = 1 := by simpa [x, hp0] using hq
          rcases htest with hqp | hq1
          · subst q; exact hpc
          · subst q; exact Ne.symm hc1))
    refine ⟨Y, hReach, hAnd, ?_, hYA, hYB, ?_⟩
    · omega
    · change Circuit.eval ⟨gates, Y⟩ (List.ofFn x) = true
      exact hYx
  · intro p hp hp1 hpc hfire
    let x : Fin 13 → Bool := fun q => decide (q = p ∨ (p ≠ 1 ∧ q = 0))
    have hfire' : value ⟨gates, 0⟩ x (13 + (zs : ℕ)) = true := by
      change Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn x) = true
      exact hfire
    have hAndInput := andInput gates zs u v x hop hin hfire'
    have hA : value ⟨gates, 0⟩ (fun q => decide (q ∉ L l)) u = false := by
      change Circuit.eval ⟨gates, u⟩ (List.ofFn (fun q => decide (q ∉ L l))) = false
      exact hFalseL
    have hB : value ⟨gates, 0⟩ (fun q => decide (q ∉ L m)) u = false := by
      change Circuit.eval ⟨gates, u⟩ (List.ofFn (fun q => decide (q ∉ L m))) = false
      exact hFalseM
    obtain ⟨Y, hReach, hAnd, hYle, hYA, hYB, hYx⟩ :=
      orDescent gates u x (fun q => decide (q ∉ L l)) (fun q => decide (q ∉ L m))
        hOps hAndInput.2 hA hB (hsafe x (by
          intro q hq
          have htest : q = p ∨ q = 0 := by simpa [x, hp1] using hq
          rcases htest with hqp | hq0
          · subst q; exact hpc
          · subst q; exact Ne.symm hc0))
    refine ⟨Y, hReach, hAnd, ?_, hYA, hYB, ?_⟩
    · omega
    · change Circuit.eval ⟨gates, Y⟩ (List.ofFn x) = true
      exact hYx

