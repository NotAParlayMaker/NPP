import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1577

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

lemma vl_mono {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, vl gates x w = true → vl gates y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hn : w < n
    · rw [vl_input gates x w hn] at hx
      rw [vl_input gates y w hn]
      exact hxy _ hx
    · by_cases hw : w < n + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gates.length := by omega
        have hgk : gates[k]? = some gates[k] := List.getElem?_eq_getElem hk
        rcases hg (gates[k]) (List.getElem_mem hk) with hop | hop
        · rw [vl_and gates x k _ hgk hop] at hx
          rw [vl_and gates y k _ hgk hop]
          intro r hr
          exact ⟨(hx r hr).1, ih r (hx r hr).1 (hx r hr).2⟩
        · rw [vl_or gates x k _ hgk hop] at hx
          rw [vl_or gates y k _ hgk hop]
          obtain ⟨r, hr, hlt, hv⟩ := hx
          exact ⟨r, hr, hlt, ih r hlt hv⟩
      · rw [vl_missing gates x w (by omega)] at hx
        exact Bool.noConfusion hx

lemma trace2 {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (x : Fin n → Bool) :
    ∀ w, vl gates x w = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, w ∈ S → (∀ i : Fin gates.length, n + (i : ℕ) ∈ S →
          (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
        vl gates x Y = true ∧
        (Y < n ∨ ∃ i : Fin gates.length, Y = n + (i : ℕ) ∧ (gates.get i).op = GateOp.and) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hn : w < n
    · exact ⟨w, fun S h _ => h, hx, Or.inl hn⟩
    · by_cases hw : w < n + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gates.length := by omega
        have hgk : gates[k]? = some gates[k] := List.getElem?_eq_getElem hk
        rcases hg (gates[k]) (List.getElem_mem hk) with hop | hop
        · exact ⟨n + k, fun S h _ => h, hx, Or.inr ⟨⟨k, hk⟩, rfl, hop⟩⟩
        · have hx' := hx
          rw [vl_or gates x k _ hgk hop] at hx'
          obtain ⟨r, hr, hlt, hv⟩ := hx'
          obtain ⟨Y, hY1, hY2, hY3⟩ := ih r hlt hv
          exact ⟨Y, fun S hS hc => hY1 S (hc ⟨k, hk⟩ hS hop r hr) hc, hY2, hY3⟩
      · rw [vl_missing gates x w (by omega)] at hx
        exact Bool.noConfusion hx

lemma false_closed {n : ℕ} (gates : List Gate) (x : Fin n → Bool)
    (hwf : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ)) :
    ∀ i : Fin gates.length, vl gates x (n + (i : ℕ)) = false → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, vl gates x a = false := by
  intro i hi hop a ha
  by_contra hne
  have ha' : vl gates x a = true := by simpa using hne
  have h : vl gates x (n + (i : ℕ)) = true :=
    (vl_or gates x i _ (List.getElem?_eq_getElem i.2) hop).mpr ⟨a, ha, hwf i a ha, ha'⟩
  rw [hi] at h
  exact Bool.noConfusion h

def L0 : Fin 13 → Finset (Fin 13) := fun t => {t, t + 1, t + 3, t + 9}

lemma f1 : ∀ t : Fin 13, t ≠ 0 → ∀ a ∈ L0 0, ∀ b ∈ L0 0, a ≠ b → a ∉ L0 t ∨ b ∉ L0 t := by
  decide +kernel

lemma main (gates : List Gate) (g : ℕ) (t : Fin 13)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hwf : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (ht : t ≠ 0)
    (h0 : vl gates (fun v : Fin 13 => decide (v ∉ L0 0)) g = false)
    (h1 : vl gates (fun v : Fin 13 => decide (v ∉ L0 t)) g = false)
    (h2 : 2 ≤ ((L0 0).filter (fun p => vl gates
      (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L0 0))) g = true)).card) :
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      vl gates (fun v : Fin 13 => decide (v ∉ L0 0)) Y = false ∧
      vl gates (fun v : Fin 13 => decide (v ∉ L0 t)) Y = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L0 t ∧ vl gates
        (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L0 0))) Y = true := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le Nat.one_lt_two h2)
  rw [Finset.mem_filter] at ha hb
  have key : ∃ p ∈ L0 0, p ∉ L0 t ∧ vl gates
      (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L0 0))) g = true := by
    rcases f1 t ht a ha.1 b hb.1 hab with h | h
    · exact ⟨a, ha.1, h, ha.2⟩
    · exact ⟨b, hb.1, h, hb.2⟩
  obtain ⟨p, hp0, hpt, hp⟩ := key
  have hmono : ∀ g' ∈ gates, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
    fun g' hg' => (hg g' hg').1
  have hp39 : p = 3 ∨ p = 9 := by
    by_contra hne
    have hm : vl gates (fun v : Fin 13 => decide (v ∉ L0 t)) g = true := by
      refine vl_mono gates hmono _ _ (fun v hv => ?_) g hp
      have hv' : v = p := by
        rcases of_decide_eq_true hv with h | h
        · exact h
        · exact absurd h.1 hne
      subst hv'
      exact decide_eq_true hpt
    rw [h1] at hm
    exact Bool.noConfusion hm
  obtain ⟨Y, hY1, hY2, hY3⟩ := trace2 gates hmono _ g hp
  have hwf' : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ) :=
    fun i => (hwf i).2
  have c0 : vl gates (fun v : Fin 13 => decide (v ∉ L0 0)) Y = false :=
    hY1 {w | vl gates (fun v : Fin 13 => decide (v ∉ L0 0)) w = false} h0
      (fun i hi hop a ha => false_closed gates _ hwf' i hi hop a ha)
  have ct : vl gates (fun v : Fin 13 => decide (v ∉ L0 t)) Y = false :=
    hY1 {w | vl gates (fun v : Fin 13 => decide (v ∉ L0 t)) w = false} h1
      (fun i hi hop a ha => false_closed gates _ hwf' i hi hop a ha)
  rcases hY3 with hlt | hand
  · exfalso
    have d0 := c0
    have dt := ct
    have dp := hY2
    rw [vl_input gates _ Y hlt] at d0
    rw [vl_input gates _ Y hlt] at dt
    rw [vl_input gates _ Y hlt] at dp
    have e0 : (⟨Y, hlt⟩ : Fin 13) ∈ L0 0 := by
      by_contra h
      have h' : decide ((⟨Y, hlt⟩ : Fin 13) ∉ L0 0) = true := decide_eq_true h
      exact Bool.noConfusion (d0.symm.trans h')
    have et : (⟨Y, hlt⟩ : Fin 13) ∈ L0 t := by
      by_contra h
      have h' : decide ((⟨Y, hlt⟩ : Fin 13) ∉ L0 t) = true := decide_eq_true h
      exact Bool.noConfusion (dt.symm.trans h')
    rcases of_decide_eq_true dp with h | h
    · rw [h] at et
      exact hpt et
    · exact h.2 e0
  · exact ⟨Y, hY1, hand, c0, ct, p, hp39, hpt, hY2⟩

end PEqualNP.Outside.L_meta_1577

theorem PEqualNP.Outside.L_meta_1577 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → t ≠ 0 →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
    2 ≤ ((L 0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0)))) = true)).card →
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L t ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true := by
  intro L hL gates g t hg hwf ht h0 h1 h2
  obtain rfl : L = PEqualNP.Outside.L_meta_1577.L0 := funext hL
  exact PEqualNP.Outside.L_meta_1577.main gates g t hg hwf ht h0 h1 h2
