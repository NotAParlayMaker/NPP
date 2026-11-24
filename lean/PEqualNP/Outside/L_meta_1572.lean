import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572

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


lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]


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


lemma zero_not_mem_m (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (m : Fin 13) (hm : m ∈ ({1, 5, 11} : Finset (Fin 13))) :
    (0 : Fin 13) ∉ L m := by
  have hmcases : m = 1 ∨ m = 5 ∨ m = 11 := by simpa using hm
  rcases hmcases with h | h | h <;> subst m <;> rw [hL] <;> decide

lemma one_not_mem_l (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (l : Fin 13) (hl : l ∈ ({4, 10, 12} : Finset (Fin 13))) :
    (1 : Fin 13) ∉ L l := by
  have hlcases : l = 4 ∨ l = 10 ∨ l = 12 := by simpa using hl
  rcases hlcases with h | h | h <;> subst l <;> rw [hL] <;> decide

lemma intersectionPoint_ne_01 (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (l m c : Fin 13)
    (hl : l ∈ ({4, 10, 12} : Finset (Fin 13)))
    (hm : m ∈ ({1, 5, 11} : Finset (Fin 13)))
    (hint : L l ∩ L m = {c}) : c ≠ 0 ∧ c ≠ 1 := by
  have hc : c ∈ L l ∩ L m := by rw [hint]; simp
  have hcL : c ∈ L l := (Finset.mem_inter.mp hc).1
  have hcM : c ∈ L m := (Finset.mem_inter.mp hc).2
  have h0M := zero_not_mem_m L hL m hm
  have h1L := one_not_mem_l L hL l hl
  constructor
  · intro heq
    subst c
    exact h0M hcM
  · intro heq
    subst c
    exact h1L hcL

end PEqualNP.Outside.L_meta_1572

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1572 in
theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  classical
  intro L hL gates g l m c hG hEarlier hl hm hint hnegL hnegM
  have hOps : ∀ gd ∈ gates, gd.op = GateOp.and ∨ gd.op = GateOp.or := by
    intro gd hgd
    exact (hG gd hgd).1
  let C : Circuit := ⟨gates, 0⟩
  let A : Fin 13 → Bool := fun v => decide (v ∉ L l)
  let B : Fin 13 → Bool := fun v => decide (v ∉ L m)
  have hA : value C A g = false := by
    change Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false
    exact hnegL
  have hB : value C B g = false := by
    change Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false
    exact hnegM
  have h0M := zero_not_mem_m L hL m hm
  have h1L := one_not_mem_l L hL l hl
  have hcne := intersectionPoint_ne_01 L hL l m c hl hm hint
  have hzeroInput : value C (fun v : Fin 13 => decide (v = 0)) g = false := by
    cases hv : value C (fun v : Fin 13 => decide (v = 0)) g with
    | false => rfl
    | true =>
      have hm' : value C B g = true := value_mono C hG
        (fun v : Fin 13 => decide (v = 0)) B
        (by
          intro v h
          have hv' : v = 0 := of_decide_eq_true h
          subst v
          change decide (0 ∉ L m) = true
          exact decide_eq_true h0M)
        g hv
      rw [hB] at hm'
      cases hm'
  have honeInput : value C (fun v : Fin 13 => decide (v = 1)) g = false := by
    cases hv : value C (fun v : Fin 13 => decide (v = 1)) g with
    | false => rfl
    | true =>
      have hl' : value C A g = true := value_mono C hG
        (fun v : Fin 13 => decide (v = 1)) A
        (by
          intro v h
          have hv' : v = 1 := of_decide_eq_true h
          subst v
          change decide (1 ∉ L l) = true
          exact decide_eq_true h1L)
        g hv
      rw [hA] at hl'
      cases hl'
  refine ⟨?_, ?_⟩
  · intro hcount
    let F : Finset (Fin 13) := (L l).filter (fun p =>
      Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)
    have hFcard : 2 ≤ F.card := hcount
    have hzF : (0 : Fin 13) ∉ F := by
      intro hz
      have hfire := (Finset.mem_filter.mp hz).2
      have hv : value C (fun v : Fin 13 => decide (v = 0)) g = true := by
        change Circuit.eval ⟨gates, g⟩
          (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true
        simpa using hfire
      rw [hzeroInput] at hv
      cases hv
    have hlt : 1 < F.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
    have ha0 : a ≠ 0 := by intro e; subst a; exact hzF ha
    have hb0 : b ≠ 0 := by intro e; subst b; exact hzF hb
    have hfireF (p : Fin 13) (hp : p ∈ F) :
        Circuit.eval ⟨gates, g⟩
          (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true :=
      (Finset.mem_filter.mp hp).2
    have hchoose : ∃ p : Fin 13, p ∈ L l ∧ p ≠ 0 ∧ p ≠ c ∧
        Circuit.eval ⟨gates, g⟩
          (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true := by
      by_cases hac : a ≠ c
      · exact ⟨a, (Finset.mem_filter.mp ha).1, ha0, hac, hfireF a ha⟩
      · have hae : a = c := by by_contra h; exact hac h
        have hbc : b ≠ c := by
          intro h
          exact hab (hae.trans h.symm)
        exact ⟨b, (Finset.mem_filter.mp hb).1, hb0, hbc, hfireF b hb⟩
    obtain ⟨p, hpL, hp0, hpc, hfire⟩ := hchoose
    have hpNotM : p ∉ L m := by
      intro hpm
      have hpint : p ∈ L l ∩ L m := Finset.mem_inter.mpr ⟨hpL, hpm⟩
      have hpeq : p = c := by
        rw [hint] at hpint
        exact Finset.mem_singleton.mp hpint
      exact hpc hpeq
    let X : Fin 13 → Bool := fun v => decide (v = p ∨ (p ≠ 0 ∧ v = 1))
    have hX : value C X g = true := by
      change Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true
      exact hfire
    have hsafe : ∀ v : Fin 13, X v = true → A v = true ∨ B v = true := by
      intro v hv
      have hv' : v = p ∨ (p ≠ 0 ∧ v = 1) := of_decide_eq_true hv
      rcases hv' with hp | ⟨_, hv1⟩
      · subst v
        right
        change decide (p ∉ L m) = true
        exact decide_eq_true hpNotM
      · subst v
        left
        change decide (1 ∉ L l) = true
        exact decide_eq_true h1L
    obtain ⟨Y, hYclosed, hYand, _, _, _, hYX⟩ :=
      orDescent gates g X A B hOps hX hA hB hsafe
    refine ⟨Y, hYclosed, hYand, p, hpL, hp0, hpc, ?_⟩
    change Circuit.eval ⟨gates, Y⟩
      (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true
    exact hYX
  · intro hcount
    let F : Finset (Fin 13) := (L m).filter (fun p =>
      Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)
    have hFcard : 2 ≤ F.card := hcount
    have hOneF : (1 : Fin 13) ∉ F := by
      intro hone
      have hfire := (Finset.mem_filter.mp hone).2
      have hv : value C (fun v : Fin 13 => decide (v = 1)) g = true := by
        change Circuit.eval ⟨gates, g⟩
          (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true
        simpa using hfire
      rw [honeInput] at hv
      cases hv
    have hlt : 1 < F.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
    have ha1 : a ≠ 1 := by intro e; subst a; exact hOneF ha
    have hb1 : b ≠ 1 := by intro e; subst b; exact hOneF hb
    have hfireF (p : Fin 13) (hp : p ∈ F) :
        Circuit.eval ⟨gates, g⟩
          (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true :=
      (Finset.mem_filter.mp hp).2
    have hchoose : ∃ p : Fin 13, p ∈ L m ∧ p ≠ 1 ∧ p ≠ c ∧
        Circuit.eval ⟨gates, g⟩
          (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true := by
      by_cases hac : a ≠ c
      · exact ⟨a, (Finset.mem_filter.mp ha).1, ha1, hac, hfireF a ha⟩
      · have hae : a = c := by by_contra h; exact hac h
        have hbc : b ≠ c := by
          intro h
          exact hab (hae.trans h.symm)
        exact ⟨b, (Finset.mem_filter.mp hb).1, hb1, hbc, hfireF b hb⟩
    obtain ⟨p, hpM, hp1, hpc, hfire⟩ := hchoose
    have hpNotL : p ∉ L l := by
      intro hpl
      have hpint : p ∈ L l ∩ L m := Finset.mem_inter.mpr ⟨hpl, hpM⟩
      have hpeq : p = c := by
        rw [hint] at hpint
        exact Finset.mem_singleton.mp hpint
      exact hpc hpeq
    let X : Fin 13 → Bool := fun v => decide (v = p ∨ (p ≠ 1 ∧ v = 0))
    have hX : value C X g = true := by
      change Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true
      exact hfire
    have hsafe : ∀ v : Fin 13, X v = true → A v = true ∨ B v = true := by
      intro v hv
      have hv' : v = p ∨ (p ≠ 1 ∧ v = 0) := of_decide_eq_true hv
      rcases hv' with hp | ⟨_, hv0⟩
      · subst v
        left
        change decide (p ∉ L l) = true
        exact decide_eq_true hpNotL
      · subst v
        right
        change decide (0 ∉ L m) = true
        exact decide_eq_true h0M
    obtain ⟨Y, hYclosed, hYand, _, _, _, hYX⟩ :=
      orDescent gates g X A B hOps hX hA hB hsafe
    refine ⟨Y, hYclosed, hYand, p, hpM, hp1, hpc, ?_⟩
    change Circuit.eval ⟨gates, Y⟩
      (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true
    exact hYX

