import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds Finset
namespace PEqualNP.Outside.L_meta_1578_aux

-- Wire evaluation identities from the project proof of L-meta-1558.
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

abbrev P := Fin 13
def line (t : P) : Finset P := {t,t+1,t+3,t+9}
def outer (t v : P) := decide (v ∉ line t)
def bonus (p v : P) := decide (v = p ∨ v ∉ line 0)
def LS : Finset P := {4,10,12}
def MS : Finset P := {1,5,11}
lemma geometry : ∀ t ∈ LS ∪ MS, ∀ p : P, p = 3 ∨ p = 9 → ∀ v : P,
    ¬ (outer 0 v = false ∧ outer t v = false ∧ bonus p v = true) := by decide +kernel
lemma nonzero : ∀ t ∈ LS ∪ MS, t ≠ 0 := by decide +kernel

def V (gs : List Gate) (w : ℕ) (x : P → Bool) := value (⟨gs,0⟩ : Circuit) x w
abbrev Law (gs : List Gate) := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma descend {gs : List Gate} (law : Law gs) (z : Fin gs.length) (X Y T : P → Bool)
    (base : ∀ i, ¬ (X i = false ∧ Y i = false ∧ T i = true))
    (prior : ∀ k : Fin gs.length, k < z → (gs.get k).op = GateOp.and →
      V gs (13+k) X = false → V gs (13+k) Y = false → V gs (13+k) T = false)
    (w : ℕ) (lt : w < 13+z.val) : ¬ (V gs w X = false ∧ V gs w Y = false ∧ V gs w T = true) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rintro ⟨nx,ny,pt⟩
    by_cases low : w < 13
    · let i : P := ⟨w,low⟩
      exact base i ⟨(input_value _ X i).symm.trans nx,(input_value _ Y i).symm.trans ny,
        (input_value _ T i).symm.trans pt⟩
    have hlen := z.isLt
    let k : Fin gs.length := ⟨w-13,by omega⟩
    have eq : 13+k.val = w := by change 13+(w-13)=w; omega
    have kz : k < z := by change w-13 < z.val; omega
    rw [← eq] at nx ny pt
    rcases (law _ (List.get_mem gs k)).1 with hop | hop
    · exact Bool.noConfusion ((prior k kz hop nx ny).symm.trans pt)
    · obtain ⟨a,ha,hlt,yes⟩ := (or_value ⟨gs,0⟩ k k.isLt hop T).mp pt
      have dark (x : P → Bool) (n : V gs (13+k) x = false) : V gs a x = false := by
        cases h : V gs a x
        · rfl
        · have con := (or_value ⟨gs,0⟩ k k.isLt hop x).mpr ⟨a,ha,hlt,h⟩
          exact Bool.noConfusion (n.symm.trans con)
      apply ih a (by omega) (by omega)
      exact ⟨dark X nx,dark Y ny,yes⟩

lemma and_pair {gs : List Gate} (z : Fin gs.length) (u v : ℕ)
    (op : (gs.get z).op = GateOp.and) (ins : (gs.get z).inputs = [u,v])
    (hu : u < 13+z.val) (hv : v < 13+z.val) (x : P → Bool) :
    V gs (13+z) x = (V gs u x && V gs v x) := by
  apply Bool.eq_iff_iff.mpr
  change value (⟨gs,0⟩ : Circuit) x (13+z) = true ↔ _
  rw [and_value _ _ z.isLt op]
  change (∀ r ∈ (gs.get z).inputs, r < 13+z.val ∧ V gs r x = true) ↔ _
  rw [ins]
  simp [hu,hv]

end PEqualNP.Outside.L_meta_1578_aux

open PEqualNP.Outside.L_meta_1578_aux

theorem PEqualNP.Outside.L_meta_1578 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = true) →
    (∀ i : Fin gates.length, i < zs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = false) →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) ∨
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) := by
  intro L hL gs z u v l m law proper hl hm op ins n0 nl nm pos old
  have eL : L = line := funext hL
  subst L
  simp only [true_or,or_true,true_and] at pos old
  change V gs (13+z) (bonus 3) = true ∨ V gs (13+z) (bonus 9) = true at pos
  change V gs (13+z) (outer 0) = false at n0
  change V gs (13+z) (outer l) = false at nl
  change V gs (13+z) (outer m) = false at nm
  have hu := (proper z).2 u (by rw [ins]; simp)
  have hv := (proper z).2 v (by rw [ins]; simp)
  rw [and_pair z u v op ins hu hv] at n0 nl nm
  change (_ ∧ _ ∧ V gs u (outer 0) = true ∧ V gs v (outer 0) = false ∧
      V gs v (outer l) = true ∧ V gs v (outer m) = true) ∨
    (V gs v (outer l) = false ∧ V gs v (outer m) = false ∧ V gs v (outer 0) = true ∧
      V gs u (outer 0) = false ∧ V gs u (outer l) = true ∧ V gs u (outer m) = true)
  change (V gs u (outer l) = false ∧ V gs u (outer m) = false ∧ _) ∨ _
  have hx : ∃ p : P, (p = 3 ∨ p = 9) ∧ V gs (13+z) (bonus p) = true := by
    rcases pos with h|h
    · exact ⟨3,Or.inl rfl,h⟩
    · exact ⟨9,Or.inr rfl,h⟩
  obtain ⟨p,hp,hit⟩ := hx
  rw [and_pair z u v op ins hu hv,Bool.and_eq_true] at hit
  have sep (w : ℕ) (lt : w < 13+z.val) (on : V gs w (bonus p) = true)
      (t : P) (ht : t ∈ LS ∪ MS) : ¬ (V gs w (outer 0) = false ∧ V gs w (outer t) = false) := by
    intro ⟨q,r⟩
    apply descend law z (outer 0) (outer t) (bonus p) (geometry t ht p hp) _ w lt ⟨q,r,on⟩
    intro k kz hop off0 offt
    have dx := old k kz hop off0 t (nonzero t ht) offt
    rcases hp with rfl|rfl
    · exact dx.1
    · exact dx.2
  have ul := sep u hu hit.1 l (mem_union_left _ hl)
  have um := sep u hu hit.1 m (mem_union_right _ hm)
  have vl := sep v hv hit.2 l (mem_union_left _ hl)
  have vm := sep v hv hit.2 m (mem_union_right _ hm)
  revert ul um vl vm n0 nl nm
  cases V gs u (outer 0) <;> cases V gs v (outer 0) <;>
    cases V gs u (outer l) <;> cases V gs v (outer l) <;>
    cases V gs u (outer m) <;> cases V gs v (outer m) <;> decide
