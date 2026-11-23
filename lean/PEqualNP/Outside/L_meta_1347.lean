import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1347

open PEqualNP.CircuitLowerBounds

-- Running a gate list on an input list (the same fold as Circuit.wires).
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

-- The final value of wire w of the gate list gs on input x.
def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

lemma eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = val gs x o := rfl

lemma val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gs x w = x ⟨w, hw⟩ := by
  unfold val
  have hp : w < (List.ofFn x).length := by simp [hw]
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma val_missing {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : val gs x w = false := by
  unfold val
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

-- A gate wire: its gate applied to the final values of earlier wires, later wires read false.
lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gs.length) :
    val gs x w = (gs[w - n]'(by omega)).op.eval
      ((gs[w - n]'(by omega)).inputs.map fun r => if r < w then val gs x r else false) := by
  let j := w - n
  have hj : j < gs.length := by omega
  let g := gs[j]
  let earlier := run (gs.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run gs (List.ofFn x) = run (g :: gs.drop (j + 1)) earlier := by
    rw [run_split gs (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then val gs x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run gs (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run gs (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then val gs x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

-- Gate rewriting: reads of p go to the never-present wire Z.
def sig (p Z : ℕ) (i : ℕ) : ℕ := if i = p then Z else i

def gen (p Z : ℕ) (G : Gate) : Gate := ⟨G.op, G.inputs.map (sig p Z)⟩

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

-- A two-wire gate one of whose reads u carries the constant c: a constant or a copy.
def kill (p Z u : ℕ) (c : Bool) (G : Gate) : Gate :=
  if isAnd G.op then
    (if c then ⟨GateOp.and, (G.inputs.filter (fun i => i != u)).map (sig p Z)⟩
      else ⟨GateOp.or, []⟩)
  else
    (if c then ⟨GateOp.and, []⟩
      else ⟨GateOp.or, (G.inputs.filter (fun i => i != u)).map (sig p Z)⟩)

lemma gen_eval (p Z : ℕ) (G : Gate) (R R' : ℕ → Bool) (hRR : ∀ r, R (sig p Z r) = R' r) :
    (gen p Z G).op.eval ((gen p Z G).inputs.map R) = G.op.eval (G.inputs.map R') := by
  have h : R ∘ sig p Z = R' := funext hRR
  simp only [gen, List.map_map, h]

lemma kill_op (p Z u : ℕ) (c : Bool) (G : Gate) :
    (kill p Z u c G).op = GateOp.and ∨ (kill p Z u c G).op = GateOp.or := by
  unfold kill
  split_ifs <;> simp

lemma kill_len (p Z u : ℕ) (c : Bool) (G : Gate) (hlen : G.inputs.length = 2)
    (hu : u ∈ G.inputs) : (kill p Z u c G).inputs.length ≤ 1 := by
  have hf : (G.inputs.filter (fun i => i != u)).length < G.inputs.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨u, hu, by simp⟩
  unfold kill
  split_ifs <;> simp <;> omega

lemma kill_eval (p Z u : ℕ) (c : Bool) (G : Gate)
    (hop : G.op = GateOp.and ∨ G.op = GateOp.or) (hu : u ∈ G.inputs)
    (R R' : ℕ → Bool) (hRR : ∀ r, R (sig p Z r) = R' r) (hc : R' u = c) :
    (kill p Z u c G).op.eval ((kill p Z u c G).inputs.map R) = G.op.eval (G.inputs.map R') := by
  have hcomp : R ∘ sig p Z = R' := funext hRR
  rcases hop with hop | hop
  · cases c with
    | false =>
      simp only [kill, hop, isAnd, ite_true, Bool.false_eq_true, ite_false, List.map_nil,
        GateOp.eval, List.any_nil]
      symm
      rw [List.all_eq_false]
      exact ⟨R' u, List.mem_map.mpr ⟨u, hu, rfl⟩, by simp [hc]⟩
    | true =>
      simp only [kill, hop, isAnd, ite_true, GateOp.eval, List.map_map, hcomp]
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      constructor
      · intro h b hb
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
        by_cases hru : r = u
        · subst hru; simpa using hc
        · exact h _ (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hru⟩, rfl⟩)
      · intro h b hb
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
        exact h _ (List.mem_map.mpr ⟨r, (List.mem_filter.mp hr).1, rfl⟩)
  · cases c with
    | true =>
      simp only [kill, hop, isAnd, Bool.false_eq_true, ite_false, ite_true, List.map_nil,
        GateOp.eval, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨R' u, List.mem_map.mpr ⟨u, hu, rfl⟩, by simp [hc]⟩
    | false =>
      simp only [kill, hop, isAnd, Bool.false_eq_true, ite_false, GateOp.eval, List.map_map,
        hcomp]
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨b, hb, hbt⟩
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
        exact ⟨R' r, List.mem_map.mpr ⟨r, (List.mem_filter.mp hr).1, rfl⟩, hbt⟩
      · rintro ⟨b, hb, hbt⟩
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
        by_cases hru : r = u
        · subst hru; simp [hc] at hbt
        · exact ⟨R' r, List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hru⟩, rfl⟩,
            hbt⟩


lemma not_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < gs.length)
    (p : Fin n) (hop : (gs[i]'hi).op = GateOp.not)
    (hhead : (gs[i]'hi).inputs.head? = some p.val) :
    val gs x (n + i) = !(x p) := by
  rw [val_gate gs x (n + i) (by omega) (by omega)]
  simp only [Nat.add_sub_cancel_left]
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hhead
  rw [hop, ht]
  have hp : p.val < n + i := by omega
  simp only [GateOp.eval, List.map_cons, List.headD_cons, ite_eq_left hp, val_input gs x p.val p.isLt]

lemma two_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < gs.length)
    (ar br : ℕ) (hin : (gs[i]'hi).inputs = [ar, br]) :
    val gs x (n + i) = (gs[i]'hi).op.eval [if ar < n + i then val gs x ar else false,
      if br < n + i then val gs x br else false] := by
  rw [val_gate gs x (n + i) (by omega) (by omega)]
  simp only [Nat.add_sub_cancel_left, hin, List.map_cons, List.map_nil]

-- The new gate list: g (index a) and h (index kr) become constants or copies, every other gate
-- reads Z instead of p.
def newGate (gates : List Gate) (P Z ν i0 : ℕ) (a kr : Fin gates.length)
    (j : Fin gates.length) : Gate :=
  if j = a then kill P Z P false (gates.get j)
  else if j = kr then kill P Z ν (decide (i0 < j.val)) (gates.get j)
  else gen P Z (gates.get j)

abbrev newList (gates : List Gate) (P Z ν i0 : ℕ) (a kr : Fin gates.length) : List Gate :=
  List.ofFn (newGate gates P Z ν i0 a kr)

lemma newList_length (gates : List Gate) (P Z ν i0 : ℕ) (a kr : Fin gates.length) :
    (newList gates P Z ν i0 a kr).length = gates.length := by
  simp [newList]

lemma sim {n : ℕ} (gates : List Gate) (p : Fin n) (i0 : ℕ) (hi0 : i0 < gates.length)
    (hop0 : (gates[i0]'hi0).op = GateOp.not)
    (hhead0 : (gates[i0]'hi0).inputs.head? = some p.val)
    (a kr : Fin gates.length)
    (haop : (gates.get a).op = GateOp.and ∨ (gates.get a).op = GateOp.or)
    (hpa : p.val ∈ (gates.get a).inputs)
    (hkop : (gates.get kr).op = GateOp.and ∨ (gates.get kr).op = GateOp.or)
    (hkν : n + i0 ∈ (gates.get kr).inputs)
    (x2 : Fin n → Bool) (w : ℕ) :
    val (newList gates p.val (n + gates.length) (n + i0) i0 a kr) x2
        (sig p.val (n + gates.length) w) =
      val gates (fun v => if v = p then false else x2 v) w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  set Z := n + gates.length with hZ
  set gl := newList gates p.val Z (n + i0) i0 a kr with hgl
  set x' : Fin n → Bool := fun v => if v = p then false else x2 v with hx'
  have hgllen : gl.length = gates.length := newList_length _ _ _ _ _ _ _
  have hx'p : x' p = false := by simp [x']
  by_cases hwp : w = p.val
  · rw [hwp, show sig p.val Z p.val = Z from ite_eq_left rfl,
      val_missing gl x2 Z (by omega), val_input gates x' p.val p.isLt]
    exact hx'p.symm
  rw [show sig p.val Z w = w from ite_eq_right hwp]
  by_cases hwn : w < n
  · rw [val_input gl x2 w hwn, val_input gates x' w hwn]
    have hne : (⟨w, hwn⟩ : Fin n) ≠ p := fun h => hwp (by rw [← h])
    simp [x', hne]
  by_cases hwl : w < n + gates.length
  swap
  · rw [val_missing gl x2 w (by omega), val_missing gates x' w (by omega)]
  have hjl : w - n < gates.length := by omega
  rw [val_gate gl x2 w (by omega) (by omega), val_gate gates x' w (by omega) hwl]
  have hRR : ∀ r, (fun r => if r < w then val gl x2 r else false) (sig p.val Z r) =
      (fun r => if r < w then val gates x' r else false) r := by
    intro r
    by_cases hrp : r = p.val
    · rw [hrp, show sig p.val Z p.val = Z from ite_eq_left rfl]
      simp only
      rw [ite_eq_right (by omega : ¬ Z < w)]
      by_cases hpw : p.val < w
      · rw [ite_eq_left hpw, val_input gates x' p.val p.isLt, hx'p]
      · rw [ite_eq_right hpw]
    · rw [show sig p.val Z r = r from ite_eq_right hrp]
      simp only
      by_cases hrw : r < w
      · rw [ite_eq_left hrw, ite_eq_left hrw]
        have h := ih r hrw
        rwa [show sig p.val Z r = r from ite_eq_right hrp] at h
      · rw [ite_eq_right hrw, ite_eq_right hrw]
  have hglj : gl[w - n]'(by omega) = newGate gates p.val Z (n + i0) i0 a kr ⟨w - n, hjl⟩ := by
    simp [gl, newList]
  rw [hglj]
  have hget : gates.get ⟨w - n, hjl⟩ = gates[w - n]'hjl := rfl
  unfold newGate
  by_cases hja : (⟨w - n, hjl⟩ : Fin gates.length) = a
  · rw [ite_eq_left hja, hget]
    have hop : (gates[w - n]'hjl).op = GateOp.and ∨ (gates[w - n]'hjl).op = GateOp.or := by
      rw [← hget, hja]; exact haop
    have hu : p.val ∈ (gates[w - n]'hjl).inputs := by rw [← hget, hja]; exact hpa
    refine kill_eval p.val Z p.val false _ hop hu _ _ hRR ?_
    split_ifs
    · rw [val_input gates x' p.val p.isLt, hx'p]
    · rfl
  rw [ite_eq_right hja]
  by_cases hjk : (⟨w - n, hjl⟩ : Fin gates.length) = kr
  · rw [ite_eq_left hjk, hget]
    have hop : (gates[w - n]'hjl).op = GateOp.and ∨ (gates[w - n]'hjl).op = GateOp.or := by
      rw [← hget, hjk]; exact hkop
    have hu : n + i0 ∈ (gates[w - n]'hjl).inputs := by rw [← hget, hjk]; exact hkν
    refine kill_eval p.val Z (n + i0) _ _ hop hu _ _ hRR ?_
    simp only
    by_cases hlt : n + i0 < w
    · rw [ite_eq_left hlt, not_val gates x' i0 hi0 p hop0 hhead0, hx'p]
      simp only [Bool.not_false]
      symm
      exact decide_eq_true (by omega)
    · rw [ite_eq_right hlt]
      symm
      exact decide_eq_false (by omega)
  · rw [ite_eq_right hjk, hget]
    exact gen_eval p.val Z _ _ _ hRR


lemma newList_get (gates : List Gate) (P Z ν i0 : ℕ) (a kr : Fin gates.length)
    (q : Fin (newList gates P Z ν i0 a kr).length) :
    (newList gates P Z ν i0 a kr).get q =
      newGate gates P Z ν i0 a kr ⟨q.val, by simpa [newList_length] using q.isLt⟩ := by
  rw [List.get_ofFn]
  rfl

lemma kill_op3 (p Z u : ℕ) (c : Bool) (G : Gate) :
    (kill p Z u c G).op = GateOp.and ∨ (kill p Z u c G).op = GateOp.or ∨
      (kill p Z u c G).op = GateOp.not := by
  rcases kill_op p Z u c G with h | h <;> simp [h]

lemma kill_ne_not (p Z u : ℕ) (c : Bool) (G : Gate) : (kill p Z u c G).op ≠ GateOp.not := by
  rcases kill_op p Z u c G with h | h <;> rw [h] <;> intro h' <;> cases h'

lemma gen_op (P Z : ℕ) (G : Gate) : (gen P Z G).op = G.op := rfl

lemma gen_len (P Z : ℕ) (G : Gate) : (gen P Z G).inputs.length = G.inputs.length := by
  simp [gen]

end PEqualNP.Outside.L_meta_1347

open PEqualNP.Outside.L_meta_1347 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1347 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → (∀ jr : Fin gates.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gates.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gates.length, (∃ oq : Fin m, out oq = n + jr3.val) ∨ ∃ kr : Fin gates.length, ((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gates.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gates.get kr).inputs)) ∧ (∀ jr4 : Fin gates.length, ((gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gates.get jr4).inputs = [ar, br]) → ∀ p : Fin n, (gates.get (ι 0)).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get (ι 0)).inputs.head? = some p.val → ∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true)) := by
  classical
  intro n m S gates out hG hout ι hnot hred p hιop hιhead a haop halen hpa I hI
  obtain ⟨hred1, hred2, hred3, hred4⟩ := hred
  have hi0 : (ι 0).val < gates.length := (ι 0).isLt
  have hop0 : (gates[(ι 0).val]'hi0).op = GateOp.not := hιop
  have hhead0 : (gates[(ι 0).val]'hi0).inputs.head? = some p.val := hιhead
  have hpn : p.val < n := p.isLt
  have hnotv : ∀ x : Fin n → Bool, val gates x (n + (ι 0).val) = !(x p) :=
    fun x => not_val gates x (ι 0).val hi0 p hop0 hhead0
  obtain ⟨kr, hkop, hkν⟩ : ∃ kr : Fin gates.length,
      ((gates.get kr).op = GateOp.and ∨ (gates.get kr).op = GateOp.or) ∧
        n + (ι 0).val ∈ (gates.get kr).inputs := by
    rcases hred3 (ι 0) with ⟨oq, hoq⟩ | ⟨kr, hk⟩
    · exfalso
      have h1 := hout oq (fun _ => false)
      rw [eval_eq, hoq, hnotv] at h1
      simp at h1
    · rcases hk with ⟨hkn, hkh⟩ | ⟨hko, hkm⟩
      · exfalso
        obtain ⟨r, hr⟩ := hnot kr hkn
        have hr0 : r = 0 := Subsingleton.elim _ _
        rw [hr0] at hr
        rw [← hr, hιhead] at hkh
        have := Option.some.inj hkh
        omega
      · exact ⟨kr, hko, hkm⟩
  obtain ⟨kar, kbr, hkab, hkin⟩ := hred4 kr hkop
  have hklen : (gates.get kr).inputs.length = 2 := by rw [hkin]; rfl
  have hak : a ≠ kr := by
    intro hak
    rw [← hak] at hkin hkν
    have hpm : p.val ∈ [kar, kbr] := hkin ▸ hpa
    have hνm : n + (ι 0).val ∈ [kar, kbr] := hkin ▸ hkν
    have hcases : (kar = p.val ∧ kbr = n + (ι 0).val) ∨ (kar = n + (ι 0).val ∧ kbr = p.val) := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpm hνm
      omega
    have hRp : ∀ x : Fin n → Bool,
        (if p.val < n + a.val then val gates x p.val else false) = x p := by
      intro x
      rw [ite_eq_left (by omega), val_input gates x p.val p.isLt]
    have hRν : ∀ x : Fin n → Bool,
        (if n + (ι 0).val < n + a.val then val gates x (n + (ι 0).val) else false) =
          (if (ι 0).val < a.val then !(x p) else false) := by
      intro x
      by_cases h : (ι 0).val < a.val
      · rw [ite_eq_left (by omega), hnotv, ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]
    have hval : ∀ x : Fin n → Bool, val gates x (n + a.val) =
        (gates.get a).op.eval [x p, if (ι 0).val < a.val then !(x p) else false] := by
      intro x
      rw [two_val gates x a.val a.isLt kar kbr hkin]
      change (gates.get a).op.eval _ = _
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hRp x, hRν x]
      · rw [h1, h2, hRp x, hRν x]
        rcases haop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
    have hconst : ∀ c : Bool, (∀ x : Fin n → Bool, val gates x (n + a.val) = c) → False := by
      intro c hc
      obtain ⟨xr, yr, hne⟩ := hred1 a
      rw [eval_eq, eval_eq, hc xr, hc yr] at hne
      exact hne rfl
    rcases haop with hop | hop
    · apply hconst false
      intro x
      rw [hval x, hop]
      by_cases h : (ι 0).val < a.val
      · cases hx : x p <;> simp [GateOp.eval, h]
      · simp [GateOp.eval, h]
    · by_cases h : (ι 0).val < a.val
      · apply hconst true
        intro x
        rw [hval x, hop]
        cases hx : x p <;> simp [GateOp.eval, h]
      · obtain ⟨xr, hne⟩ := hred2 a p.val (by omega)
        rw [eval_eq, eval_eq, hval xr, hop, val_input gates xr p.val p.isLt] at hne
        apply hne
        simp [GateOp.eval, h]
  have haI : a ∈ I := hI a ⟨haop, halen⟩
  have hkI : kr ∈ I := hI kr ⟨hkop, hklen⟩
  have hlen := newList_length gates p.val (n + gates.length) (n + (ι 0).val) (ι 0).val a kr
  refine ⟨newList gates p.val (n + gates.length) (n + (ι 0).val) (ι 0).val a kr,
    fun o => sig p.val (n + gates.length) (out o),
    fun r => Fin.cast hlen.symm (ι r),
    Finset.univ.filter (fun q => (((newList gates p.val (n + gates.length) (n + (ι 0).val)
      (ι 0).val a kr).get q).op = GateOp.and ∨ ((newList gates p.val (n + gates.length)
      (n + (ι 0).val) (ι 0).val a kr).get q).op = GateOp.or) ∧ ((newList gates p.val
      (n + gates.length) (n + (ι 0).val) (ι 0).val a kr).get q).inputs.length = 2),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨q, rfl⟩ := List.get_of_mem hh
    rw [newList_get]
    unfold newGate
    split_ifs with h1 h2
    · refine ⟨kill_op3 _ _ _ _ _, ?_⟩
      · have := kill_len p.val (n + gates.length) p.val false (gates.get a) halen hpa
        rw [h1]; omega
    · refine ⟨kill_op3 _ _ _ _ _, ?_⟩
      · have := kill_len p.val (n + gates.length) (n + (ι 0).val)
          (decide ((ι 0).val < kr.val)) (gates.get kr) hklen hkν
        rw [h2]; omega
    · rw [gen_op, gen_len]
      exact hG _ (List.get_mem _ _)
  · intro q hq
    rw [newList_get] at hq
    unfold newGate at hq
    split_ifs at hq with h1 h2
    · exact absurd hq (kill_ne_not _ _ _ _ _)
    · exact absurd hq (kill_ne_not _ _ _ _ _)
    · rw [gen_op] at hq
      obtain ⟨r, hr⟩ := hnot _ hq
      refine ⟨r, ?_⟩
      ext
      simp [hr]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hq
  · let J := Finset.univ.filter (fun q => (((newList gates p.val (n + gates.length)
      (n + (ι 0).val) (ι 0).val a kr).get q).op = GateOp.and ∨ ((newList gates p.val
      (n + gates.length) (n + (ι 0).val) (ι 0).val a kr).get q).op = GateOp.or) ∧
      ((newList gates p.val (n + gates.length) (n + (ι 0).val) (ι 0).val a kr).get
        q).inputs.length = 2)
    change J.card + 2 ≤ I.card
    have hsub : J.image (Fin.cast hlen) ⊆ (I.erase a).erase kr := by
      intro j hj
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
      have hq' := (Finset.mem_filter.mp hq).2
      rw [newList_get] at hq'
      have hjq : (⟨q.val, by simpa [newList_length] using q.isLt⟩ : Fin gates.length) =
          Fin.cast hlen q := rfl
      rw [hjq] at hq'
      unfold newGate at hq'
      split_ifs at hq' with h1 h2
      · have := kill_len p.val (n + gates.length) p.val false (gates.get a) halen hpa
        rw [h1] at hq'; omega
      · have := kill_len p.val (n + gates.length) (n + (ι 0).val)
          (decide ((ι 0).val < kr.val)) (gates.get kr) hklen hkν
        rw [h2] at hq'; omega
      · rw [gen_op, gen_len] at hq'
        exact Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hI _ hq'⟩⟩
    have hcard : J.card = (J.image (Fin.cast hlen)).card :=
      (Finset.card_image_of_injective _ (Fin.cast_injective hlen)).symm
    have h1 := Finset.card_le_card hsub
    have h2 : ((I.erase a).erase kr).card + 2 = I.card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hak, hkI⟩),
        Finset.card_erase_of_mem haI]
      have : 2 ≤ I.card := by
        have hpair : ({a, kr} : Finset (Fin gates.length)) ⊆ I := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact haI
          · rw [Finset.mem_singleton.mp hz]; exact hkI
        have := Finset.card_le_card hpair
        rw [Finset.card_pair hak] at this
        exact this
      omega
    omega
  · intro o2 x2
    rw [eval_eq, sim gates p (ι 0).val hi0 hop0 hhead0 a kr haop hpa hkop hkν x2 (out o2),
      ← eval_eq, hout]
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨v, hv, h⟩
      by_cases hvp : v = p
      · simp [hvp] at h
      · exact ⟨v, hv, hvp, by simpa [hvp] using h⟩
    · rintro ⟨v, hv, hvp, h⟩
      exact ⟨v, hv, by simp [hvp, h]⟩
