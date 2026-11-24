import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1572

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

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]


private def reachable (gs : List Gate) (w y : ℕ) : Prop :=
  ∀ S : Set ℕ, w ∈ S → (∀ i : Fin gs.length, 13 + i.val ∈ S →
    (gs.get i).op = GateOp.or → ∀ a ∈ (gs.get i).inputs, a ∈ S) → y ∈ S

private def point (a b p v : Fin 13) := decide (v = p ∨ (p ≠ a ∧ v = b))
private def off (A : Finset (Fin 13)) (v : Fin 13) := decide (v ∉ A)

private lemma atom (gs : List Gate)
    (ops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (A B : Finset (Fin 13)) (x : Fin 13 → Bool)
    (dis : ∀ v ∈ A, v ∈ B → x v ≠ true) (w : ℕ)
    (ha : value ⟨gs, 0⟩ (off A) w = false) (hb : value ⟨gs, 0⟩ (off B) w = false)
    (hx : value ⟨gs, 0⟩ x w = true) :
    ∃ y, reachable gs w y ∧ (∃ i : Fin gs.length, y = 13+i.val ∧ (gs.get i).op = GateOp.and) ∧
      value ⟨gs, 0⟩ x y = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < 13
    · let p : Fin 13 := ⟨w, hn⟩
      change value ⟨gs, 0⟩ (off A) p = false at ha
      change value ⟨gs, 0⟩ (off B) p = false at hb
      change value ⟨gs, 0⟩ x p = true at hx
      simp only [input_value, off, decide_eq_false_iff_not, not_not] at ha hb
      exact False.elim (dis p ha hb ((input_value ..).symm.trans hx))
    by_cases hw : w < 13 + gs.length
    · let i : Fin gs.length := ⟨w-13, by omega⟩
      have wi : 13+i.val = w := by dsimp [i]; omega
      rcases (ops _ (gs.get_mem i)).1 with h | h
      · exact ⟨w, fun _ hw _ => hw, ⟨i, wi.symm, h⟩, hx⟩
      · have form (z : Fin 13 → Bool) := or_value ⟨gs, 0⟩ i i.isLt h z
        obtain ⟨r, hr, hlt, hf⟩ := (form x).mp (wi ▸ hx)
        have down (z : Fin 13 → Bool) (hz : value ⟨gs, 0⟩ z w = false) :
            value ⟨gs, 0⟩ z r = false := by
          cases e : value ⟨gs, 0⟩ z r with
          | false => rfl
          | true =>
            have bad := (form z).mpr ⟨r, hr, hlt, e⟩
            rw [wi, hz] at bad
            contradiction
        obtain ⟨y, reach, gate, hot⟩ := ih r (by omega) (down _ ha) (down _ hb) hf
        exact ⟨y, fun S hw close => reach S (close i (wi ▸ hw) h r hr) close, gate, hot⟩
    · exact False.elim (Bool.noConfusion ((missing_value ⟨gs, 0⟩ x w (by change 13+gs.length ≤ w; omega)).symm.trans hx))

private lemma side (gs : List Gate) (w : ℕ) (A B : Finset (Fin 13)) (a b c : Fin 13)
    (ops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (inter : A ∩ B = {c}) (hab : a ∉ B) (hba : b ∉ A)
    (ha : value ⟨gs, 0⟩ (off A) w = false) (hb : value ⟨gs, 0⟩ (off B) w = false)
    (count : 2 ≤ (A.filter (fun p => value ⟨gs, 0⟩ (point a b p) w = true)).card) :
    ∃ y, reachable gs w y ∧ (∃ i : Fin gs.length, y = 13+i.val ∧ (gs.get i).op = GateOp.and) ∧
      ∃ p ∈ A, p ≠ a ∧ p ≠ c ∧ value ⟨gs, 0⟩ (point a b p) y = true := by
  classical
  obtain ⟨p, hp, pc⟩ : ∃ p ∈ A.filter (fun u => value ⟨gs, 0⟩ (point a b u) w = true), p ≠ c := by
    by_contra! h
    have sub : A.filter (fun u => value ⟨gs, 0⟩ (point a b u) w = true) ⊆ {c} :=
      fun i hi => Finset.mem_singleton.mpr (h i hi)
    have bd := Finset.card_le_card sub
    simp only [Finset.card_singleton] at bd
    omega
  obtain ⟨hp, hot⟩ := Finset.mem_filter.mp hp
  have pa : p ≠ a := by
    rintro rfl
    have le (v : Fin 13) (h : point p b p v = true) : off B v = true := by
      have : v = p := by simpa [point] using h
      subst v
      exact decide_eq_true hab
    exact Bool.noConfusion (hb.symm.trans (mono ⟨gs, 0⟩ ops _ _ le w hot))
  have dis (v : Fin 13) (h1 : v ∈ A) (h2 : v ∈ B) (hv : point a b p v = true) : False := by
    have hvC : v ∈ A ∩ B := Finset.mem_inter.mpr ⟨h1,h2⟩
    rw [inter, Finset.mem_singleton] at hvC
    rcases of_decide_eq_true hv with vp | ⟨_,vb⟩
    · exact pc (vp.symm.trans hvC)
    · exact hba (vb ▸ h1)
  obtain ⟨y,reach,gate,fire⟩ := atom gs ops A B _ dis w ha hb hot
  exact ⟨y,reach,gate,p,hp,pa,pc,fire⟩

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
  intro L hL gs w l m c ops _ hl hm inter ha hb
  let line (s : Fin 13) : Finset (Fin 13) := {s,s+1,s+3,s+9}
  have fl : ∀ i ∈ ({4,10,12} : Finset (Fin 13)), 1 ∉ line i := by decide
  have fm : ∀ i ∈ ({1,5,11} : Finset (Fin 13)), 0 ∉ line i := by decide
  have bl : (1 : Fin 13) ∉ L l := by rw [hL]; exact fl l hl
  have am : (0 : Fin 13) ∉ L m := by rw [hL]; exact fm m hm
  exact ⟨side gs w _ _ 0 1 c ops inter am bl ha hb,
    side gs w _ _ 1 0 c ops ((Finset.inter_comm ..).trans inter) bl am hb ha⟩
