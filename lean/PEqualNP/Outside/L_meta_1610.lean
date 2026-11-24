import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1610

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

lemma cnt {ι α : Type*} [LinearOrder ι] [DecidableEq α] :
    ∀ (k : ℕ) (I : Finset ι) (S : Finset α) (a b : ι → α) (X : ι → Finset α), I.card = k →
      S.Nonempty → (∀ g ∈ I, a g ∈ S ∧ b g ∈ S ∧ a g ∈ X g ∧ b g ∉ X g) →
      (∀ g ∈ I, ∀ g' ∈ I, g' < g → (a g' ∈ X g ↔ b g' ∈ X g)) → I.card + 1 ≤ S.card := by
  intro k
  induction k with
  | zero =>
    intro I S a b X hk hS _ _
    have := Finset.card_pos.mpr hS
    omega
  | succ k ih =>
    intro I S a b X hk hS h1 h2
    have hne : I.Nonempty := Finset.card_pos.mp (by omega)
    have hg0I : I.min' hne ∈ I := Finset.min'_mem I hne
    have hmin : ∀ g ∈ I, I.min' hne ≤ g := fun g hg => Finset.min'_le I g hg
    generalize I.min' hne = g0 at hg0I hmin
    obtain ⟨ha0, hb0, hax, hbx⟩ := h1 g0 hg0I
    have hab : a g0 ≠ b g0 := fun h => hbx (h ▸ hax)
    have hf : ∀ g ∈ I.erase g0, ∀ x : α,
        ((if x = b g0 then a g0 else x) ∈ X g ↔ x ∈ X g) := by
      intro g hg x
      have hgI := Finset.mem_of_mem_erase hg
      have hlt : g0 < g := lt_of_le_of_ne (hmin g hgI) (Ne.symm (Finset.ne_of_mem_erase hg))
      by_cases hx : x = b g0
      · rw [if_pos hx, hx]
        exact h2 g hgI g0 hg0I hlt
      · rw [if_neg hx]
    have hfS : ∀ x ∈ S, (if x = b g0 then a g0 else x) ∈ S.erase (b g0) := by
      intro x hx
      by_cases hxb : x = b g0
      · rw [if_pos hxb]
        exact Finset.mem_erase.mpr ⟨hab, ha0⟩
      · rw [if_neg hxb]
        exact Finset.mem_erase.mpr ⟨hxb, hx⟩
    have key := ih (I.erase g0) (S.erase (b g0)) (fun g => if a g = b g0 then a g0 else a g)
      (fun g => if b g = b g0 then a g0 else b g) X
      (by rw [Finset.card_erase_of_mem hg0I, hk]; rfl)
      ⟨a g0, Finset.mem_erase.mpr ⟨hab, ha0⟩⟩ ?_ ?_
    · rw [Finset.card_erase_of_mem hg0I, Finset.card_erase_of_mem hb0] at key
      have h3 := Finset.card_pos.mpr (⟨_, hb0⟩ : S.Nonempty)
      have h4 := Finset.card_pos.mpr hne
      omega
    · intro g hg
      obtain ⟨h1a, h1b, h1c, h1d⟩ := h1 g (Finset.mem_of_mem_erase hg)
      exact ⟨hfS _ h1a, hfS _ h1b, (hf g hg _).mpr h1c, fun h => h1d ((hf g hg _).mp h)⟩
    · intro g hg g' hg' hlt
      show ((if a g' = b g0 then a g0 else a g') ∈ X g ↔
        (if b g' = b g0 then a g0 else b g') ∈ X g)
      rw [hf g hg, hf g hg]
      exact h2 g (Finset.mem_of_mem_erase hg) g' (Finset.mem_of_mem_erase hg') hlt

lemma side (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (hLM : L ∩ M = {m})
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ))
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, (gates.get g).op = GateOp.or ∧
      vl gates (fun v : Fin n => decide (v ∉ L)) (n + (g : ℕ)) = false ∧
      vl gates (fun v : Fin n => decide (v ∉ M)) (n + (g : ℕ)) = false ∧
      ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L, ∃ r' ∈ L,
        vl gates (t r) w1 = true ∧ vl gates (t r') w2 = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g →
          (gates.get i).op = GateOp.or →
          vl gates (fun v : Fin n => decide (v ∉ L)) (n + (i : ℕ)) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
          ∀ y ∈ L, ∀ y' ∈ L, (vl gates (t y) a = true ∨ vl gates (t y) b = true) →
            (vl gates (t y') a = true ∨ vl gates (t y') b = true) → (y ∈ X ↔ y' ∈ X)) :
    I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card := by
  obtain ⟨D, hDdef⟩ : ∃ D, D = (L \ M).filter (fun r => ∃ v ∈ M, t r v = true) := ⟨_, rfl⟩
  rw [← hDdef]
  have memD : ∀ p, p ∈ D ↔ (p ∈ L ∧ p ∉ M) ∧ ∃ v ∈ M, t p v = true := by
    intro p
    rw [hDdef, Finset.mem_filter, Finset.mem_sdiff]
  have hmLM : m ∈ L ∩ M := by
    rw [hLM]
    exact Finset.mem_singleton_self m
  have hmM : m ∈ M := (Finset.mem_inter.mp hmLM).2
  have hmD : m ∉ D := fun h => ((memD m).mp h).1.2 hmM
  have step1 : ∀ g ∈ I, ∀ w ∈ (gates.get g).inputs, ∀ p ∈ L, vl gates (t p) w = true →
      p ∈ insert m D := by
    intro g hg w hw p hp hv
    obtain ⟨hor, _, hcoM, _⟩ := hI g hg
    have hk : gates[(g : ℕ)]? = some (gates.get g) := List.getElem?_eq_getElem g.2
    have htrue : vl gates (t p) (n + (g : ℕ)) = true :=
      (vl_or gates (t p) g _ hk hor).mpr ⟨w, hw, hback g w hw, hv⟩
    by_cases hpM : p ∈ M
    · have hpm : p ∈ L ∩ M := Finset.mem_inter.mpr ⟨hp, hpM⟩
      rw [hLM] at hpm
      rw [Finset.mem_singleton.mp hpm]
      exact Finset.mem_insert_self _ _
    · by_contra hnot
      have hno : ¬ ∃ v ∈ M, t p v = true := fun hex =>
        hnot (Finset.mem_insert_of_mem ((memD p).mpr ⟨⟨hp, hpM⟩, hex⟩))
      have h5 := vl_mono gates (fun g' hg' => (hgates g' hg').1) (t p)
        (fun v : Fin n => decide (v ∉ M))
        (fun v hv' => decide_eq_true (fun hvM => hno ⟨v, hvM, hv'⟩)) (n + (g : ℕ)) htrue
      rw [hcoM] at h5
      exact Bool.noConfusion h5
  have H : ∀ g : Fin gates.length, ∃ r r' : Fin n, ∃ X : Finset (Fin n), g ∈ I →
      (r ∈ insert m D ∧ r' ∈ insert m D ∧ r ∈ X ∧ r' ∉ X) ∧
      (r ∈ L ∧ r' ∈ L ∧ ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧
        vl gates (t r) w1 = true ∧ vl gates (t r') w2 = true) ∧
      ∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
          vl gates (fun v : Fin n => decide (v ∉ L)) (n + (i : ℕ)) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
          ∀ y ∈ L, ∀ y' ∈ L, (vl gates (t y) a = true ∨ vl gates (t y) b = true) →
            (vl gates (t y') a = true ∨ vl gates (t y') b = true) → (y ∈ X ↔ y' ∈ X) := by
    intro g
    by_cases hg : g ∈ I
    · obtain ⟨hor, hcoL, hcoM, w1, w2, hin, r, hr, r', hr', h1, h2, X, hX1, hX2, hX3⟩ := hI g hg
      exact ⟨r, r', X, fun _ => ⟨⟨step1 g hg w1 (by rw [hin]; simp) r hr h1,
        step1 g hg w2 (by rw [hin]; simp) r' hr' h2, hX1, hX2⟩,
        ⟨hr, hr', w1, w2, hin, h1, h2⟩, hX3⟩⟩
    · exact ⟨m, m, ∅, fun h => absurd h hg⟩
  choose a b X hab using H
  have hc := cnt I.card I (insert m D) a b X rfl ⟨m, Finset.mem_insert_self _ _⟩
    (fun g hg => (hab g hg).1) (by
      intro g hg g' hg' hlt
      obtain ⟨hor', hcoL', _, _⟩ := hI g' hg'
      obtain ⟨_, ⟨hr, hr', w1, w2, hin, h1, h2⟩, _⟩ := hab g' hg'
      exact (hab g hg).2.2 g' hlt hor' hcoL' w1 w2 hin (a g') hr (b g') hr'
        (Or.inl h1) (Or.inr h2))
  rw [Finset.card_insert_of_notMem hmD] at hc
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
  intro n L M m t u gates oL oM hLM _ _ hgates hback _ _ _ _ I hI
  refine ⟨PEqualNP.Outside.L_meta_1610.side n L M m t gates hLM hgates hback I ?_,
    PEqualNP.Outside.L_meta_1610.side n M L m u gates (by rw [Finset.inter_comm]; exact hLM)
      hgates hback I ?_⟩
  · intro g hg
    obtain ⟨⟨hor, hcoL, hrest⟩, ⟨_, hcoM, _⟩⟩ := hI g hg
    exact ⟨hor, hcoL, hcoM, hrest⟩
  · intro g hg
    obtain ⟨⟨_, hcoL, _⟩, ⟨hor, hcoM, hrest⟩⟩ := hI g hg
    exact ⟨hor, hcoM, hcoL, hrest⟩
