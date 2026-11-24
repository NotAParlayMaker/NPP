import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1610

open PEqualNP.CircuitLowerBounds

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

abbrev good (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma value_mono {n : ℕ} (C : Circuit) (hG : good C)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · intro hx
      have hfx := gate_value C x w (by omega) hw
      have hfy := gate_value C y w (by omega) hw
      rw [hfx] at hx
      rw [hfy]
      obtain ⟨hop, _⟩ := hG (C.gates[w - n]'(by unfold Circuit.size at hw; omega)) (List.getElem_mem _)
      rcases hop with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
        rintro b ⟨r, hr, rfl⟩
        by_cases hrt : r < w
        · simpa [hrt] using ih r hrt (by simpa [hrt] using hx _ ⟨r, hr, rfl⟩)
        · have := hx _ ⟨r, hr, rfl⟩
          simp [hrt] at this
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
        obtain ⟨_, ⟨r, hr, rfl⟩, hv⟩ := hx
        by_cases hrt : r < w
        · exact ⟨_, ⟨r, hr, rfl⟩, by simpa [hrt] using ih r hrt (by simpa [hrt] using hv)⟩
        · simp [hrt] at hv
    · simp [missing_value C x w (by omega)]

lemma gate_value' {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    value (⟨gs, 0⟩ : Circuit) x (n + k) =
      (gs[k]).op.eval ((gs[k]).inputs.map fun r =>
        if r < n + k then value (⟨gs, 0⟩ : Circuit) x r else false) := by
  have h := gate_value (⟨gs, 0⟩ : Circuit) x (n + k) (by omega)
    (by simp only [Circuit.size]; omega)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

lemma forest {ι α : Type} [LinearOrder ι] [DecidableEq α] (r r' : ι → α) (X : ι → Finset α) :
    ∀ (k : ℕ) (E : Finset ι) (V : Finset α), E.card = k →
    (∀ j ∈ E, r j ∈ V ∧ r' j ∈ V ∧ r j ∈ X j ∧ r' j ∉ X j ∧
      ∀ i ∈ E, i < j → (r i ∈ X j ↔ r' i ∈ X j)) →
    E.card ≤ V.card - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro E V hk hE
  rcases E.eq_empty_or_nonempty with h0 | hne
  · simp [h0]
  obtain ⟨j, hjdef⟩ : ∃ j, j = E.max' hne := ⟨_, rfl⟩
  have hjE : j ∈ E := by rw [hjdef]; exact E.max'_mem hne
  obtain ⟨hrV, hr'V, hrX, hr'X, -⟩ := hE j hjE
  have hcons : ∀ i ∈ E.erase j, (r i ∈ X j ↔ r' i ∈ X j) := by
    intro i hi
    have hiE := Finset.mem_of_mem_erase hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hle : i ≤ j := by rw [hjdef]; exact E.le_max' i hiE
    exact (hE j hjE).2.2.2.2 i hiE (lt_of_le_of_ne hle hij)
  obtain ⟨Ein, hEin⟩ : ∃ s, s = (E.erase j).filter (fun i => r i ∈ X j) := ⟨_, rfl⟩
  obtain ⟨Eout, hEout⟩ : ∃ s, s = (E.erase j).filter (fun i => ¬ (r i ∈ X j)) := ⟨_, rfl⟩
  obtain ⟨Vin, hVin⟩ : ∃ s, s = V.filter (fun v => v ∈ X j) := ⟨_, rfl⟩
  obtain ⟨Vout, hVout⟩ : ∃ s, s = V.filter (fun v => ¬ (v ∈ X j)) := ⟨_, rfl⟩
  have hEcard : E.card = Ein.card + Eout.card + 1 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := E.erase j) (fun i => r i ∈ X j)
    have h2 := Finset.card_erase_of_mem hjE
    have h3 : 0 < E.card := Finset.card_pos.mpr hne
    rw [hEin, hEout]
    omega
  have hVcard : V.card = Vin.card + Vout.card := by
    rw [hVin, hVout]
    exact (Finset.card_filter_add_card_filter_not (s := V) (fun v => v ∈ X j)).symm
  have hVin1 : 1 ≤ Vin.card := by
    rw [hVin]
    exact Finset.card_pos.mpr ⟨r j, Finset.mem_filter.mpr ⟨hrV, hrX⟩⟩
  have hVout1 : 1 ≤ Vout.card := by
    rw [hVout]
    exact Finset.card_pos.mpr ⟨r' j, Finset.mem_filter.mpr ⟨hr'V, hr'X⟩⟩
  have hin := ih Ein.card (by omega) Ein Vin rfl (by
    intro a ha
    rw [hEin, Finset.mem_filter] at ha
    obtain ⟨haE', hra⟩ := ha
    have haE := Finset.mem_of_mem_erase haE'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hE a haE
    refine ⟨?_, ?_, h3, h4, ?_⟩
    · rw [hVin]; exact Finset.mem_filter.mpr ⟨h1, hra⟩
    · rw [hVin]; exact Finset.mem_filter.mpr ⟨h2, (hcons a haE').mp hra⟩
    · intro i hi hia
      rw [hEin, Finset.mem_filter] at hi
      exact h5 i (Finset.mem_of_mem_erase hi.1) hia)
  have hout := ih Eout.card (by omega) Eout Vout rfl (by
    intro a ha
    rw [hEout, Finset.mem_filter] at ha
    obtain ⟨haE', hra⟩ := ha
    have haE := Finset.mem_of_mem_erase haE'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hE a haE
    refine ⟨?_, ?_, h3, h4, ?_⟩
    · rw [hVout]; exact Finset.mem_filter.mpr ⟨h1, hra⟩
    · rw [hVout]; exact Finset.mem_filter.mpr ⟨h2, fun h => hra ((hcons a haE').mpr h)⟩
    · intro i hi hia
      rw [hEout, Finset.mem_filter] at hi
      exact h5 i (Finset.mem_of_mem_erase hi.1) hia)
  omega

lemma endpoint (n : ℕ) (M : Finset (Fin n)) (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlt : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ))
    (g : Fin gates.length) (hop : (gates.get g).op = GateOp.or)
    (hM : Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false)
    (w : ℕ) (hw : w ∈ (gates.get g).inputs) (x : Fin n → Bool)
    (hx : Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true) : ∃ v ∈ M, x v = true := by
  by_contra hcon
  have hle : ∀ p, x p = true → (fun v : Fin n => decide (v ∉ M)) p = true := by
    intro p hp
    simp only [decide_eq_true_eq]
    intro hpM
    exact hcon ⟨p, hpM, hp⟩
  have hx' : value (⟨gates, 0⟩ : Circuit) x w = true := hx
  have hmono := value_mono (⟨gates, 0⟩ : Circuit) hG x (fun v : Fin n => decide (v ∉ M)) hle w hx'
  have hwlt : w < n + (g : ℕ) := hlt g w hw
  have hk : (g : ℕ) < gates.length := g.isLt
  have hop' : (gates[(g : ℕ)]'hk).op = GateOp.or := by
    rw [List.get_eq_getElem] at hop; exact hop
  have hw' : w ∈ (gates[(g : ℕ)]'hk).inputs := by
    rw [List.get_eq_getElem] at hw; exact hw
  have hval : value (⟨gates, 0⟩ : Circuit) (fun v : Fin n => decide (v ∉ M)) (n + (g : ℕ)) = true := by
    rw [gate_value' gates _ (g : ℕ) hk]
    simp only [hop', GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    exact ⟨_, ⟨w, hw', rfl⟩, by simpa [hwlt] using hmono⟩
  have hM' : value (⟨gates, 0⟩ : Circuit) (fun v : Fin n => decide (v ∉ M)) (n + (g : ℕ)) = false := hM
  rw [hM'] at hval
  exact absurd hval (by simp)

lemma side (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (t : Fin n → Fin n → Bool)
    (gates : List Gate)
    (hLM : L ∩ M = {m})
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlt : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ))
    (I : Finset (Fin gates.length))
    (hMf : ∀ g ∈ I, Circuit.eval ⟨gates, n + (g : ℕ)⟩
      (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false)
    (hA : ∀ g ∈ I, ((gates.get g).op = GateOp.or ∧ Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L, ∃ r' ∈ L,
          Circuit.eval ⟨gates, w1⟩ (List.ofFn (t r)) = true ∧ Circuit.eval ⟨gates, w2⟩ (List.ofFn (t r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
            Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ L, ∀ y' ∈ L, (Circuit.eval ⟨gates, a⟩ (List.ofFn (t y)) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (t y)) = true) →
              (Circuit.eval ⟨gates, a⟩ (List.ofFn (t y')) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (t y')) = true) → (y ∈ X ↔ y' ∈ X))) :
    I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card := by
  rcases I.eq_empty_or_nonempty with hI0 | ⟨g0, hg0⟩
  · simp [hI0]
  have hne : Nonempty (Fin n) := by
    obtain ⟨-, -, w1, w2, -, r, hr, -⟩ := hA g0 hg0
    exact ⟨r⟩
  choose! hop hfalse w1 w2 hin r hr r' hr' h1 h2 X hrX hr'X hX using hA
  obtain ⟨V, hV⟩ : ∃ s, s = L.filter (fun y => ∃ v ∈ M, t y v = true) := ⟨_, rfl⟩
  have hVD : V.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card + 1 := by
    have hsub : V ⊆ insert m ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)) := by
      intro y hy
      rw [hV, Finset.mem_filter] at hy
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_sdiff]
      by_cases hyM : y ∈ M
      · left
        have hy2 : y ∈ L ∩ M := Finset.mem_inter.mpr ⟨hy.1, hyM⟩
        rw [hLM] at hy2
        exact Finset.mem_singleton.mp hy2
      · right
        exact ⟨⟨hy.1, hyM⟩, hy.2⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hend : ∀ g ∈ I, ∀ w ∈ (gates.get g).inputs, ∀ y ∈ L,
      Circuit.eval ⟨gates, w⟩ (List.ofFn (t y)) = true → y ∈ V := by
    intro g hg w hw y hy hev
    rw [hV, Finset.mem_filter]
    exact ⟨hy, endpoint n M gates hG hlt g (hop g hg) (hMf g hg) w hw (t y) hev⟩
  have hF := forest r r' X I.card I V rfl (by
    intro j hj
    refine ⟨hend j hj (w1 j) (by rw [hin j hj]; simp) (r j) (hr j hj) (h1 j hj),
            hend j hj (w2 j) (by rw [hin j hj]; simp) (r' j) (hr' j hj) (h2 j hj),
            hrX j hj, hr'X j hj, ?_⟩
    intro i hi hij
    exact hX j hj i hij (hop i hi) (hfalse i hi) (w1 i) (w2 i) (hin i hi) (r i) (hr i hi)
      (r' i) (hr' i hi) (Or.inl (h1 i hi)) (Or.inr (h2 i hi)))
  omega

end PEqualNP.Outside.L_meta_1610

theorem PEqualNP.Outside.L_meta_1610 : ∀ (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (t u : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (oL oM : ℕ),
    L ∩ M = {m} →
    (∀ r ∈ L, ∀ v ∈ L, t r v = true ↔ v = r) → (∀ r ∈ M, ∀ v ∈ M, u r v = true ↔ v = r) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oL⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → (∀ r ∈ L, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oL⟩ (List.ofFn (t r)) = true) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oM⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false → (∀ r ∈ M, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oM⟩ (List.ofFn (u r)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L, ∃ r' ∈ L,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (t r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (t r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ L, ∀ y' ∈ L, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (t y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (t y)) = true) →
              (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (t y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (t y')) = true) → (y ∈ X ↔ y' ∈ X)) ∧
        ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (u r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (u r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ M, ∀ y' ∈ M, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (u y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (u y)) = true) →
              (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (u y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (u y')) = true) → (y ∈ X ↔ y' ∈ X))) →
      I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card ∧
      I.card ≤ ((M \ L).filter (fun r => ∃ v ∈ L, u r v = true)).card := by
  intro n L M m t u gates oL oM hLM _ _ hG hlt _ _ _ _ I hI
  refine ⟨?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_1610.side n L M m t gates hLM hG hlt I
      (fun g hg => (hI g hg).2.2.1) (fun g hg => (hI g hg).1)
  · exact PEqualNP.Outside.L_meta_1610.side n M L m u gates
      (by rw [Finset.inter_comm]; exact hLM) hG hlt I
      (fun g hg => (hI g hg).1.2.1) (fun g hg => (hI g hg).2)
