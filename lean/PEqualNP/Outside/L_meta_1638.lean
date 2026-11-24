import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1638_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma eval_wire_eq (gates : List Gate) {N : ℕ} (x : Fin N → Bool) (w : ℕ) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = (wiresFrom gates (List.ofFn x)).getD w false := by
  rfl

lemma gate_or_false_inputs {l : List Bool} (h : GateOp.eval GateOp.or l = false) :
    ∀ b ∈ l, b = false := by
  simpa [GateOp.eval] using h

lemma gate_or_true_exists {l : List Bool} (h : GateOp.eval GateOp.or l = true) :
    ∃ b ∈ l, b = true := by
  simpa [GateOp.eval] using h

lemma gate_and_true_inputs {l : List Bool} (h : GateOp.eval GateOp.and l = true) :
    ∀ b ∈ l, b = true := by
  simpa [GateOp.eval] using h

lemma gate_or_out_false {N : ℕ} (gates : List Gate) (x : Fin N → Bool)
    (i : ℕ) (hi : i < gates.length)
    (hops : ∀ e ∈ (gates.get ⟨i, hi⟩).inputs, e < N + i)
    (hop : (gates.get ⟨i, hi⟩).op = GateOp.or)
    (hout : Circuit.eval ⟨gates, N + i⟩ (List.ofFn x) = false) :
    ∀ e ∈ (gates.get ⟨i, hi⟩).inputs, Circuit.eval ⟨gates, e⟩ (List.ofFn x) = false := by
  intro e he
  have hg : GateOp.eval (gates.get ⟨i, hi⟩).op
      ((gates.get ⟨i, hi⟩).inputs.map fun e' =>
        if e' < N + i then (wiresFrom gates (List.ofFn x)).getD e' false else false)
      = Circuit.eval ⟨gates, N + i⟩ (List.ofFn x) := by
    have hg0 := getD_wiresFrom_gate gates (List.ofFn x) i hi
    simpa [eval_wire_eq, List.length_ofFn] using hg0.symm
  have hg' : GateOp.eval (gates.get ⟨i, hi⟩).op
      ((gates.get ⟨i, hi⟩).inputs.map fun e' =>
        if e' < N + i then (wiresFrom gates (List.ofFn x)).getD e' false else false) = false := by
    rw [hg]
    exact hout
  rw [hop] at hg'
  have hval := gate_or_false_inputs hg' (if e < N + i then (wiresFrom gates (List.ofFn x)).getD e false else false)
    (List.mem_map.mpr ⟨e, he, rfl⟩)
  have helt := hops e he
  simp [helt] at hval
  simpa [eval_wire_eq] using hval

lemma gate_or_out_true_some {N : ℕ} (gates : List Gate) (x : Fin N → Bool)
    (i : ℕ) (hi : i < gates.length)
    (hops : ∀ e ∈ (gates.get ⟨i, hi⟩).inputs, e < N + i)
    (hop : (gates.get ⟨i, hi⟩).op = GateOp.or)
    (hout : Circuit.eval ⟨gates, N + i⟩ (List.ofFn x) = true) :
    ∃ e ∈ (gates.get ⟨i, hi⟩).inputs, Circuit.eval ⟨gates, e⟩ (List.ofFn x) = true := by
  have hg : GateOp.eval (gates.get ⟨i, hi⟩).op
      ((gates.get ⟨i, hi⟩).inputs.map fun e' =>
        if e' < N + i then (wiresFrom gates (List.ofFn x)).getD e' false else false)
      = Circuit.eval ⟨gates, N + i⟩ (List.ofFn x) := by
    have hg0 := getD_wiresFrom_gate gates (List.ofFn x) i hi
    simpa [eval_wire_eq, List.length_ofFn] using hg0.symm
  have hg' : GateOp.eval (gates.get ⟨i, hi⟩).op
      ((gates.get ⟨i, hi⟩).inputs.map fun e' =>
        if e' < N + i then (wiresFrom gates (List.ofFn x)).getD e' false else false) = true := by
    rw [hg]
    exact hout
  rw [hop] at hg'
  rcases gate_or_true_exists hg' with ⟨b, hbmem, hbtrue⟩
  rcases List.mem_map.mp hbmem with ⟨e, he, rfl⟩
  have helt := hops e he
  simp [helt] at hbtrue
  exact ⟨e, he, by simpa [eval_wire_eq] using hbtrue⟩

lemma gate_and_out_true_inputs {N : ℕ} (gates : List Gate) (x : Fin N → Bool)
    (i : ℕ) (hi : i < gates.length)
    (hops : ∀ e ∈ (gates.get ⟨i, hi⟩).inputs, e < N + i)
    (hop : (gates.get ⟨i, hi⟩).op = GateOp.and)
    (hout : Circuit.eval ⟨gates, N + i⟩ (List.ofFn x) = true) :
    ∀ e ∈ (gates.get ⟨i, hi⟩).inputs, Circuit.eval ⟨gates, e⟩ (List.ofFn x) = true := by
  intro e he
  have hg : GateOp.eval (gates.get ⟨i, hi⟩).op
      ((gates.get ⟨i, hi⟩).inputs.map fun e' =>
        if e' < N + i then (wiresFrom gates (List.ofFn x)).getD e' false else false)
      = Circuit.eval ⟨gates, N + i⟩ (List.ofFn x) := by
    have hg0 := getD_wiresFrom_gate gates (List.ofFn x) i hi
    simpa [eval_wire_eq, List.length_ofFn] using hg0.symm
  have hg' : GateOp.eval (gates.get ⟨i, hi⟩).op
      ((gates.get ⟨i, hi⟩).inputs.map fun e' =>
        if e' < N + i then (wiresFrom gates (List.ofFn x)).getD e' false else false) = true := by
    rw [hg]
    exact hout
  rw [hop] at hg'
  have hval := gate_and_true_inputs hg' (if e < N + i then (wiresFrom gates (List.ofFn x)).getD e false else false)
    (List.mem_map.mpr ⟨e, he, rfl⟩)
  have helt := hops e he
  simp [helt] at hval
  simpa [eval_wire_eq] using hval

def Reach (N : ℕ) (gates : List Gate) (u w : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S →
    (∀ i : Fin gates.length, N + (i : ℕ) ∈ S →
      (gates.get i).op = GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) →
    w ∈ S

lemma reach_refl (N : ℕ) (gates : List Gate) (u : ℕ) : Reach N gates u u := by
  intro S hu _
  exact hu

lemma reach_of_or_input (N : ℕ) (gates : List Gate) {u e : ℕ} (i : Fin gates.length)
    (hr : Reach N gates u (N + (i : ℕ)))
    (hop : (gates.get i).op = GateOp.or) (he : e ∈ (gates.get i).inputs) :
    Reach N gates u e := by
  intro S hu hcl
  exact hcl i (hr S hu hcl) hop e he

end PEqualNP.Outside.L_meta_1638_aux

open PEqualNP.Outside.L_meta_1638_aux
open PEqualNP.CircuitLowerBounds

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
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, ((∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true)) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 hq hm hmq hN hline hmeet hpair hTsub hTcard gates u hgate hnonempty hinput hu0
  classical
  let x0 : Fin N → Bool := fun v => decide (v ∉ L i0)
  let R : ℕ → Prop := fun w =>
    ∀ S : Set ℕ, u ∈ S →
      (∀ i : Fin gates.length, N + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) →
      w ∈ S
  have hu0' : Circuit.eval ⟨gates, u⟩ (List.ofFn x0) = false := by
    simpa [x0] using hu0
  have hRu : R u := by
    intro S huS _
    exact huS
  have hfalse : ∀ Y, R Y → Circuit.eval ⟨gates, Y⟩ (List.ofFn x0) = false := by
    intro Y hY
    apply hY {w : ℕ | Circuit.eval ⟨gates, w⟩ (List.ofFn x0) = false}
    · exact hu0'
    · intro i hiN hop e he
      exact gate_or_out_false gates x0 i.val i.isLt (fun w hw => hinput i w hw) (by simpa using hop) hiN e he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y hY
    exact hfalse Y hY
  · intro p hp
    have hpfalse : Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn x0) = false :=
      hfalse (p : ℕ) hp
    have hpx0 : x0 p = false := by
      change (wiresFrom gates (List.ofFn x0)).getD (p : ℕ) false = false at hpfalse
      rw [getD_wiresFrom_lt gates (List.ofFn x0) (p : ℕ) (by simpa using p.isLt)] at hpfalse
      simpa using hpfalse
    simpa [x0] using hpx0
  · intro r hr huflip
    let xr : Fin N → Bool := fun v => decide (v ∉ L i0 ∨ v = r)
    have huflip' : Circuit.eval ⟨gates, u⟩ (List.ofFn xr) = true := by
      simpa [xr] using huflip
    let F : ℕ → Prop := fun w =>
      R w ∧ Circuit.eval ⟨gates, w⟩ (List.ofFn x0) = false ∧
        Circuit.eval ⟨gates, w⟩ (List.ofFn xr) = true
    have hFu : F u := ⟨hRu, hu0', huflip'⟩
    have hFuEx : ∃ n, F n := ⟨u, hFu⟩
    let w : ℕ := Nat.find hFuEx
    have hwF : F w := Nat.find_spec hFuEx
    have hmin : ∀ v, F v → w ≤ v := by
      intro v hv
      exact Nat.find_min' hFuEx hv
    rcases hwF with ⟨hwreach, hw0, hw1⟩
    by_cases hwN : w < N
    · let p : Fin N := ⟨w, hwN⟩
      have hpx0 : x0 p = false := by
        change (wiresFrom gates (List.ofFn x0)).getD w false = false at hw0
        rw [getD_wiresFrom_lt gates (List.ofFn x0) w (by simpa [List.length_ofFn] using hwN)] at hw0
        simpa [p, hwN] using hw0
      have hpin : p ∈ L i0 := by
        simpa [x0] using hpx0
      have hpxr : xr p = true := by
        change (wiresFrom gates (List.ofFn xr)).getD w false = true at hw1
        rw [getD_wiresFrom_lt gates (List.ofFn xr) w (by simpa [List.length_ofFn] using hwN)] at hw1
        simpa [p, hwN] using hw1
      have hprval : (p : ℕ) = (r : ℕ) := by
        by_contra hne
        have hnefin : p ≠ r := by
          intro h
          apply hne
          exact congrArg Fin.val h
        have hxrfalse : xr p = false := by
          simp [xr, hpin, hnefin]
        rw [hxrfalse] at hpxr
        contradiction
      have hpr : p = r := Fin.ext hprval
      have hwr : w = (r : ℕ) := by
        simpa [p] using hprval
      left
      intro S huS hcl
      have hwS := hwreach S huS hcl
      simpa [hwr] using hwS
    · have hwlen : w < N + gates.length := by
        by_contra hge
        have hdef : (wiresFrom gates (List.ofFn xr)).getD w false = false := by
          rw [List.getD_eq_default]
          simpa [length_wiresFrom] using hge
        have : Circuit.eval ⟨gates, w⟩ (List.ofFn xr) = false := by
          simpa [eval_wire_eq] using hdef
        rw [this] at hw1
        contradiction
      let i : ℕ := w - N
      have hi : i < gates.length := by omega
      have hweq : w = N + i := by omega
      let fi : Fin gates.length := ⟨i, hi⟩
      have hopcase := (hgate (gates.get fi) (List.getElem_mem fi.isLt)).1
      rcases hopcase with hand | hor
      · right
        refine ⟨w, ?_, ?_, ?_⟩
        · simpa [R] using hwreach
        · exact ⟨fi, hweq, by simpa [fi] using hand⟩
        · exact hw1
      · have hflipsome := gate_or_out_true_some gates xr i hi
          (fun e he => hinput fi e he) (by simpa [fi] using hor)
          (by simpa [hweq] using hw1)
        rcases hflipsome with ⟨e, he, hxe1⟩
        have hxe0 := gate_or_out_false gates x0 i hi
          (fun e he => hinput fi e he) (by simpa [fi] using hor)
          (by simpa [hweq] using hw0) e he
        have hereach : R e := by
          intro S huS hcl
          have hwS := hwreach S huS hcl
          have hiS : N + (i : ℕ) ∈ S := by simpa [hweq] using hwS
          exact hcl fi hiS (by simpa [fi] using hor) e he
        have hFe : F e := ⟨hereach, hxe0, hxe1⟩
        have hle := hmin e hFe
        have helt : e < w := by
          rw [hweq]
          exact hinput fi e he
        exfalso
        exact (not_lt_of_ge hle) helt
  · intro a c haop ha0 hc hc0 r hr haflip
    let xr : Fin N → Bool := fun v => decide (v ∉ L i0 ∨ v = r)
    have haflip' : Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn xr) = true := by
      simpa [xr] using haflip
    have hc1 := gate_and_out_true_inputs gates xr a.val a.isLt
      (fun e he => hinput a e he) (by simpa using haop) haflip'
    exact hc1 c hc
