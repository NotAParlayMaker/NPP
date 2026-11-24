import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1655

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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]


private lemma transfer {n : ℕ} (gs : List Gate) (j h : Fin gs.length)
    (ops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (unique : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (hj : h < j) (arg : ∃ r, (gs.get j).inputs = (n + h.val) :: r)
    (x y : Fin n → Bool) (xy : ∀ v, x v = true → y v = true) (w : ℕ)
    (ok : w < n + j.val ∨ value ⟨gs, 0⟩ y (n + h.val) = false) :
    value ⟨gs, 0⟩ x w = true → value ⟨gs, 0⟩ y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value ⟨gs, 0⟩ x p = true → value ⟨gs, 0⟩ y p = true
      simpa only [input_value] using xy p
    by_cases hw : w < n + gs.length
    · let k : Fin gs.length := ⟨w - n, by omega⟩
      have wk : n + k.val = w := by dsimp [k]; omega
      rcases (ops (gs.get k) (List.get_mem ..)).1 with ha | ho | hnot
      · rw [← wk]
        exact gate_mono ⟨gs, 0⟩ k k.isLt (.inl ha) x y fun r _ hr =>
          ih r (by omega) (ok.imp_left (by omega))
      · rw [← wk]
        exact gate_mono ⟨gs, 0⟩ k k.isLt (.inr ho) x y fun r _ hr =>
          ih r (by omega) (ok.imp_left (by omega))
      · have kj := unique k hnot
        have wj : w = n + j.val := by simpa [kj] using wk.symm
        have hy := ok.resolve_left (by omega)
        intro _
        have form := gate_value (n := n) ⟨gs, 0⟩ y (n + j.val) (by omega)
          (by change n + j.val < n + gs.length; have := j.isLt; omega)
        simp only [Nat.add_sub_cancel_left] at form
        have nj : (gs.get j).op = GateOp.not := (congrArg (fun i => (gs.get i).op) kj).symm.trans hnot
        change gs[j.val].op = GateOp.not at nj
        obtain ⟨r, hr⟩ := arg
        change gs[j.val].inputs = _ at hr
        have earlier : n + h.val < n + j.val := Nat.add_lt_add_left hj n
        rw [wj, form]
        simp [nj, hr, GateOp.eval, earlier, hy]
    · simp [missing_value (n := n) (C := ⟨gs, 0⟩) x w (by change n + gs.length ≤ w; omega)]

end PEqualNP.Outside.L_meta_1655

open PEqualNP.Outside.L_meta_1655

theorem PEqualNP.Outside.L_meta_1655 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    ∀ Sm Dm : Fin N → ℕ → Prop,
    (∀ (t : Fin N) (w : ℕ), Sm t w ↔ ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true → ∃ v ∈ L t, x v = true) →
    (∀ (t : Fin N) (w : ℕ), Dm t w ↔ (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t)) →
    ∀ Vs : Fin N → ℕ → Fin N → Prop,
    (∀ (t : Fin N) (w : ℕ) (v : Fin N), Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨ (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true))) →
    ∀ t : Fin N,
    (∀ (w : ℕ) (v : Fin N), Dm t w → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → (Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e) ∧ (Dm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Dm t e)) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and → Sm t (N + (g : ℕ)) → ∃ e ∈ (gates.get g).inputs, Sm t e) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → Vs t w v → v ∈ L t) := by
  classical
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ gs o j h ops valid _ unique hj arg _ ev hev _ _ _ top Sm Dm sm dm Vs vs t
  let cap (v : Fin N) := decide (v ∉ L i0)
  let clean (v : Fin N) := decide (v ∉ L i0 ∧ v ∉ L t)
  have eqv (w : ℕ) (x : Fin N → Bool) : ev w x = value ⟨gs, 0⟩ x w := hev w x
  have hc : ev (N+h.val) clean = false := by
    cases hh : ev (N+h.val) clean with
    | false => rfl
    | true =>
      have up := transfer gs j h ops unique hj arg clean cap
        (by intro v hv; exact decide_eq_true (of_decide_eq_true hv).1) (N+h.val)
        (.inl (Nat.add_lt_add_left hj N)) ((eqv ..).symm.trans hh)
      exact Bool.noConfusion (top.symm.trans ((eqv ..).trans up))
  have test (w : ℕ) : Sm t w ↔ ev w clean = false := by
    rw [sm]
    constructor
    · intro sound
      cases hw : ev w clean with
      | false => rfl
      | true =>
        obtain ⟨v, hl, hv⟩ := sound clean (fun _ hx => (of_decide_eq_true hx).1) hw
        exact False.elim ((of_decide_eq_true hv).2 hl)
    · intro hw x hx hot
      by_contra none
      have le (v : Fin N) (hv : x v = true) : clean v = true :=
        decide_eq_true ⟨hx v hv, fun hl => none ⟨v, hl, hv⟩⟩
      have fire := transfer gs j h ops unique hj arg x clean le w (.inr ((eqv ..).symm.trans hc))
        ((eqv ..).symm.trans hot)
      exact Bool.noConfusion (hw.symm.trans ((eqv ..).trans fire))
  have outside (w : ℕ) (v : Fin N) (hs : Sm t w) (hv : v ∉ L i0)
      (hf : ev w (fun u => decide (u = v)) = true) : v ∈ L t := by
    obtain ⟨p, hp, hpv⟩ := (sm t w).mp hs _ (by intro u hu; simpa [of_decide_eq_true hu] using hv) hf
    exact (of_decide_eq_true hpv) ▸ hp
  have inside (w : ℕ) (v : Fin N) (hd : Dm t w)
      (hf : ev w (fun u => decide (u = v)) = true) : v ∈ L t := by
    obtain ⟨hs, hp⟩ := (dm t w).mp hd
    by_cases hv : v ∈ L i0
    · exact hp v hv hf
    · exact outside w v hs hv hf
  refine ⟨inside, outside, ?_, ?_, ?_⟩
  · intro g op
    have lift (e : ℕ) (he : e ∈ (gs.get g).inputs) (x : Fin N → Bool) (hxe : ev e x = true) :
        ev (N+g.val) x = true :=
      (eqv ..).trans ((or_value ⟨gs, 0⟩ g g.isLt op x).mpr
        ⟨e, he, valid g e he, (eqv ..).symm.trans hxe⟩)
    have down (hs : Sm t (N+g.val)) (e : ℕ) (he : e ∈ (gs.get g).inputs) : Sm t e :=
      (sm t e).mpr fun x hx hf => (sm ..).mp hs x hx (lift e he x hf)
    refine ⟨down, ?_⟩
    intro hd e he
    obtain ⟨hs, hp⟩ := (dm ..).mp hd
    exact (dm ..).mpr ⟨down hs e he, fun p hpi hf => hp p hpi (lift e he _ hf)⟩
  · intro g op hs
    by_contra no
    have allhot (e : ℕ) (he : e ∈ (gs.get g).inputs) : ev e clean = true := by
      cases hh : ev e clean with
      | false => exact False.elim (no ⟨e, he, (test e).mpr hh⟩)
      | true => rfl
    have out := (and_value ⟨gs, 0⟩ g g.isLt op clean).mpr
      (fun e he => ⟨valid g e he, (eqv ..).symm.trans (allhot e he)⟩)
    exact Bool.noConfusion (((test _).mp hs).symm.trans ((eqv ..).trans out))
  · intro w v hs hv
    rcases (vs ..).mp hv with ⟨hd, hf⟩ | ⟨_, ho, hf⟩
    · exact inside w v hd hf
    · exact outside w v hs ho hf
