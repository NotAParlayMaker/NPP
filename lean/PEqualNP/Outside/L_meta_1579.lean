import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1579

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

def vl {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  value (⟨gates, 0⟩ : Circuit) x w

lemma vl_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    vl gates x w = x ⟨w, h⟩ :=
  input_value (⟨gates, 0⟩ : Circuit) x ⟨w, h⟩

lemma vl_missing {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : vl gates x w = false :=
  missing_value (⟨gates, 0⟩ : Circuit) x w hw

lemma vl_gate {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) :
    vl gates x (n + k) =
      g.op.eval (g.inputs.map fun r => if r < n + k then vl gates x r else false) := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
  have h := gate_value (⟨gates, 0⟩ : Circuit) x (n + k) (by omega)
    (by show n + k < n + gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

lemma vl_and {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) (hop : g.op = GateOp.and) :
    vl gates x (n + k) = true ↔ ∀ r ∈ g.inputs, r < n + k ∧ vl gates x r = true := by
  rw [vl_gate gates x k g hk, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
  constructor
  · intro hall r hr
    have := hall _ ⟨r, hr, rfl⟩
    by_cases hrw : r < n + k
    · simpa [hrw] using this
    · simp [hrw] at this
  · rintro hall b ⟨r, hr, rfl⟩
    have := hall r hr
    simp [this.1, this.2]

lemma vl_or {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) (hop : g.op = GateOp.or) :
    vl gates x (n + k) = true ↔ ∃ r ∈ g.inputs, r < n + k ∧ vl gates x r = true := by
  rw [vl_gate gates x k g hk, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    by_cases hrw : r < n + k
    · exact ⟨r, hr, hrw, by simpa [hrw] using hb⟩
    · simp [hrw] at hb
  · rintro ⟨r, hr, hrw, hv⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hrw, hv]⟩

lemma core (gates : List Gate) (u : ℕ)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x1 x2 xt : Fin 13 → Bool)
    (hx : ∀ a : Fin 13, x1 a = false → x2 a = false → xt a = false) :
    ∀ w : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → w ∈ S) →
      vl gates x1 w = false → vl gates x2 w = false → vl gates xt w = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
        (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧ Y ≤ w ∧
        vl gates x1 Y = false ∧ vl gates x2 Y = false ∧ vl gates xt Y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hS h1 h2 ht
    by_cases hn : w < 13
    · exfalso
      rw [vl_input gates x1 w hn] at h1
      rw [vl_input gates x2 w hn] at h2
      rw [vl_input gates xt w hn, hx _ h1 h2] at ht
      exact Bool.noConfusion ht
    · by_cases hw : w < 13 + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = 13 + k := ⟨w - 13, by omega⟩
        have hk : k < gates.length := by omega
        have hgk : gates[k]? = some gates[k] := List.getElem?_eq_getElem hk
        rcases hg (gates[k]) (List.getElem_mem hk) with hop | hop
        · exact ⟨13 + k, hS, ⟨⟨k, hk⟩, rfl, hop⟩, le_refl _, h1, h2, ht⟩
        · rw [vl_or gates xt k _ hgk hop] at ht
          obtain ⟨r, hr, hlt, hv⟩ := ht
          have hr1 : vl gates x1 r = false := by
            cases h : vl gates x1 r with
            | false => rfl
            | true =>
              have h3 := (vl_or gates x1 k _ hgk hop).mpr ⟨r, hr, hlt, h⟩
              rw [h1] at h3
              exact Bool.noConfusion h3
          have hr2 : vl gates x2 r = false := by
            cases h : vl gates x2 r with
            | false => rfl
            | true =>
              have h3 := (vl_or gates x2 k _ hgk hop).mpr ⟨r, hr, hlt, h⟩
              rw [h2] at h3
              exact Bool.noConfusion h3
          have hrS : ∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
              (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → r ∈ S :=
            fun S huS hcl => hcl ⟨k, hk⟩ (hS S huS hcl) hop r hr
          obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := ih r hlt hrS hr1 hr2 hv
          exact ⟨Y, hY1, hY2, by omega, hY4⟩
      · rw [vl_missing gates xt w (by omega)] at ht
        exact Bool.noConfusion ht

lemma side (gates : List Gate) (zs : Fin gates.length) (u v : ℕ)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hop : (gates.get zs).op = GateOp.and) (hin : (gates.get zs).inputs = [u, v])
    (x1 x2 xt : Fin 13 → Bool)
    (hx : ∀ a : Fin 13, x1 a = false → x2 a = false → xt a = false)
    (h1 : vl gates x1 u = false) (h2 : vl gates x2 u = false)
    (ht : vl gates xt (13 + (zs : ℕ)) = true) :
    ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      Y < 13 + (zs : ℕ) ∧
      vl gates x1 Y = false ∧ vl gates x2 Y = false ∧ vl gates xt Y = true := by
  have hgk : gates[(zs : ℕ)]? = some (gates.get zs) := List.getElem?_eq_getElem zs.2
  have hu := (vl_and gates xt zs _ hgk hop).mp ht u (by rw [hin]; simp)
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ :=
    core gates u hg x1 x2 xt hx u (fun S huS _ => huS) h1 h2 hu.2
  exact ⟨Y, hY1, hY2, lt_of_le_of_lt hY3 hu.1, hY4⟩

lemma f1 : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)),
    (1 : Fin 13) ∉ ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)) := by decide

lemma f0 : ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)),
    (0 : Fin 13) ∉ ({m, m + 1, m + 3, m + 9} : Finset (Fin 13)) := by decide

end PEqualNP.Outside.L_meta_1579

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
  intro L hL gates zs u v l m c hg hback hl hm hc hop hin h1 h2
  have hcc : ∀ a : Fin 13, decide (a ∉ L l) = false → decide (a ∉ L m) = false → a = c := by
    intro a ha hb
    have ha' : a ∈ L l := by simpa using ha
    have hb' : a ∈ L m := by simpa using hb
    have hab : a ∈ L l ∩ L m := Finset.mem_inter.mpr ⟨ha', hb'⟩
    rw [hc] at hab
    exact Finset.mem_singleton.mp hab
  constructor
  · intro p hp hp0 hpc ht
    refine PEqualNP.Outside.L_meta_1579.side gates zs u v (fun g h => (hg g h).1) hop hin
      (fun v : Fin 13 => decide (v ∉ L l)) (fun v : Fin 13 => decide (v ∉ L m))
      (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1))) ?_ h1 h2 ht
    intro a ha hb
    have hac := hcc a ha hb
    apply decide_eq_false
    rintro (h | ⟨_, h⟩)
    · exact hpc (h.symm.trans hac)
    · have ha' : a ∈ L l := by simpa using ha
      rw [h, hL l] at ha'
      exact PEqualNP.Outside.L_meta_1579.f1 l hl ha'
  · intro p hp hp1 hpc ht
    refine PEqualNP.Outside.L_meta_1579.side gates zs u v (fun g h => (hg g h).1) hop hin
      (fun v : Fin 13 => decide (v ∉ L l)) (fun v : Fin 13 => decide (v ∉ L m))
      (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0))) ?_ h1 h2 ht
    intro a ha hb
    have hac := hcc a ha hb
    apply decide_eq_false
    rintro (h | ⟨_, h⟩)
    · exact hpc (h.symm.trans hac)
    · have hb' : a ∈ L m := by simpa using hb
      rw [h, hL m] at hb'
      exact PEqualNP.Outside.L_meta_1579.f0 m hm hb'
