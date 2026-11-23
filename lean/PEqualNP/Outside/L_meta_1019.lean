import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_1019.Components

open PEqualNP.CircuitLowerBounds

def prior (n : ℕ) (gs : List Gate) (u v : Fin (n + gs.length)) : Prop :=
  n ≤ u.val ∧ v.val < u.val ∧
    v.val ∈ (gs.getD (u.val - n) ⟨GateOp.or, []⟩).inputs

def wireGraph (n : ℕ) (gs : List Gate) : SimpleGraph (Fin (n + gs.length)) where
  Adj u v := prior n gs u v ∨ prior n gs v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by rcases h with h | h <;> exact Nat.lt_irrefl _ h.2.1⟩

open Classical in
noncomputable def inputComponent (n : ℕ) (gs : List Gate) (o : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun p => (wireGraph n gs).Reachable o (Fin.castAdd gs.length p)

open Classical in
noncomputable def gateComponent (n : ℕ) (gs : List Gate) (o : Fin (n + gs.length)) : Finset (Fin gs.length) :=
  Finset.univ.filter fun j => (wireGraph n gs).Reachable o (Fin.natAdd n j)

lemma earlier_adj (n : ℕ) (gs : List Gate) (j : Fin gs.length)
    (r : ℕ) (hr : r < n + j.val) (hmem : r ∈ gs[j.val].inputs) :
    (wireGraph n gs).Adj (Fin.natAdd n j) ⟨r, by omega⟩ := by
  left
  refine ⟨by simp, by simpa using hr, ?_⟩
  simpa [List.getD_eq_getElem, j.isLt] using hmem

lemma earlier_reachable (n : ℕ) (gs : List Gate) (o : Fin (n + gs.length))
    (j : Fin gs.length) (ho : (wireGraph n gs).Reachable o (Fin.natAdd n j))
    (r : ℕ) (hr : r < n + j.val) (hmem : r ∈ gs[j.val].inputs) :
    (wireGraph n gs).Reachable o ⟨r, by omega⟩ :=
  ho.trans (earlier_adj n gs j r hr hmem).reachable

open Classical in
lemma edge_count_le_two_gates {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (rank : V → ℕ) (hinj : Function.Injective rank) (n : ℕ)
    (hhigh : ∀ u v, G.Adj u v → rank u < rank v → n ≤ rank v)
    (hlow : ∀ v, n ≤ rank v →
      (Finset.univ.filter (fun u => rank u < rank v ∧ G.Adj u v)).card ≤ 2) :
    G.edgeFinset.card ≤ 2 * (Finset.univ.filter (fun v => n ≤ rank v)).card := by
  let B := Finset.univ.filter (fun v => n ≤ rank v)
  let star (v : V) := (Finset.univ.filter (fun u => rank u < rank v ∧ G.Adj u v)).image
    (fun u => s(v, u))
  have hstar : ∀ v ∈ B, (star v).card ≤ 2 := by
    intro v hv
    exact (Finset.card_image_le).trans (hlow v (Finset.mem_filter.mp hv).2)
  have hsub : G.edgeFinset ⊆ B.biUnion star := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    have hab : G.Adj a b := by simpa using he
    have hne : rank a ≠ rank b := fun h => hab.ne (hinj h)
    by_cases hlt : rank a < rank b
    · apply Finset.mem_biUnion.mpr
      refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhigh a b hab hlt⟩, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hab⟩, Sym2.eq_swap⟩
    · have hlt' : rank b < rank a := by omega
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhigh b a hab.symm hlt'⟩, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt', hab.symm⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_biUnion_le_card_mul B star 2 hstar).trans_eq (Nat.mul_comm _ _))

open Classical in
lemma connected_inputs_le_gates_add_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (rank : V → ℕ) (hinj : Function.Injective rank) (n : ℕ)
    (hconn : G.Connected)
    (hhigh : ∀ u v, G.Adj u v → rank u < rank v → n ≤ rank v)
    (hlow : ∀ v, n ≤ rank v →
      (Finset.univ.filter (fun u => rank u < rank v ∧ G.Adj u v)).card ≤ 2) :
    (Finset.univ.filter (fun v => rank v < n)).card ≤
      (Finset.univ.filter (fun v => n ≤ rank v)).card + 1 := by
  have he := edge_count_le_two_gates G rank hinj n hhigh hlow
  have hc : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, G.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  have hp : (Finset.univ.filter (fun v => rank v < n)).card +
      (Finset.univ.filter (fun v => n ≤ rank v)).card = Fintype.card V := by
    simpa only [Nat.not_lt, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (fun v => rank v < n))
  omega

lemma wireGraph_high (n : ℕ) (gs : List Gate) (u v : Fin (n + gs.length))
    (h : (wireGraph n gs).Adj u v) (hlt : u.val < v.val) : n ≤ v.val := by
  rcases h with h | h
  · have := h.2.1; omega
  · exact h.1

open Classical in
lemma wireGraph_lower_neighbors (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (v : Fin (n + gs.length)) (hv : n ≤ v.val) :
    (Finset.univ.filter (fun u => u.val < v.val ∧ (wireGraph n gs).Adj u v)).card ≤ 2 := by
  have hj : v.val - n < gs.length := by have := v.isLt; omega
  let g := gs.getD (v.val - n) ⟨GateOp.or, []⟩
  have hgm : g ∈ gs := by
    dsimp [g]
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hle : (Finset.univ.filter (fun u => u.val < v.val ∧ (wireGraph n gs).Adj u v)).card ≤
      g.inputs.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun u : Fin (n + gs.length) => u.val)
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      rcases hu'.2 with h | h
      · have := h.2.1; omega
      · exact List.mem_toFinset.mpr h.2.2
    · intro a _ b _ hab
      exact Fin.ext hab
  exact hle.trans ((List.toFinset_card_le _).trans (hg g hgm))

open Classical in
lemma card_input_subtype (n s : ℕ) (P : Fin (n + s) → Prop) :
    (Finset.univ.filter (fun v : Subtype P => v.val.val < n)).card =
      (Finset.univ.filter (fun p : Fin n => P (Fin.castAdd s p))).card := by
  symm
  apply Finset.card_bij
    (fun p hp => (⟨Fin.castAdd s p, (Finset.mem_filter.mp hp).2⟩ : Subtype P))
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.isLt⟩
  · intro p hp q hq he
    exact Fin.ext (congrArg (fun v : Subtype P => v.val.val) he)
  · intro v hv
    let p : Fin n := ⟨v.val.val, (Finset.mem_filter.mp hv).2⟩
    have he : Fin.castAdd s p = v.val := Fin.ext rfl
    have hp : p ∈ Finset.univ.filter (fun p : Fin n => P (Fin.castAdd s p)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [he]; exact v.prop⟩
    exact ⟨p, hp, Subtype.ext he⟩

open Classical in
lemma card_gate_subtype (n s : ℕ) (P : Fin (n + s) → Prop) :
    (Finset.univ.filter (fun v : Subtype P => n ≤ v.val.val)).card =
      (Finset.univ.filter (fun j : Fin s => P (Fin.natAdd n j))).card := by
  symm
  apply Finset.card_bij
    (fun j hj => (⟨Fin.natAdd n j, (Finset.mem_filter.mp hj).2⟩ : Subtype P))
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
  · intro j hj k hk he
    apply Fin.ext
    have h := congrArg (fun v : Subtype P => v.val.val) he
    simpa using h
  · intro v hv
    have hge := (Finset.mem_filter.mp hv).2
    let j : Fin s := ⟨v.val.val - n, by have := v.val.isLt; omega⟩
    have he : Fin.natAdd n j = v.val := by
      apply Fin.ext
      dsimp [j]
      omega
    have hj : j ∈ Finset.univ.filter (fun j : Fin s => P (Fin.natAdd n j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [he]; exact v.prop⟩
    exact ⟨j, hj, Subtype.ext he⟩

open Classical in
lemma component_bound (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (o : Fin (n + gs.length)) :
    (inputComponent n gs o).card ≤ (gateComponent n gs o).card + 1 := by
  let G := wireGraph n gs
  let C := G.connectedComponentMk o
  let H := C.toSimpleGraph
  let rank (v : C) := v.val.val
  have hinj : Function.Injective rank := by
    intro a b h
    exact Subtype.ext (Fin.ext h)
  have hhigh : ∀ u v : C, H.Adj u v → rank u < rank v → n ≤ rank v := by
    intro u v h huv
    exact wireGraph_high n gs u.val v.val h huv
  have hlow : ∀ v : C, n ≤ rank v →
      (Finset.univ.filter (fun u : C => rank u < rank v ∧ H.Adj u v)).card ≤ 2 := by
    intro v hv
    have hle : (Finset.univ.filter (fun u : C => rank u < rank v ∧ H.Adj u v)).card ≤
        (Finset.univ.filter (fun u : Fin (n + gs.length) =>
          u.val < v.val.val ∧ G.Adj u v.val)).card := by
      apply Finset.card_le_card_of_injOn (fun u : C => u.val)
      · intro u hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
      · intro a _ b _ hab
        exact Subtype.ext hab
    exact hle.trans (wireGraph_lower_neighbors n gs hg v.val hv)
  have hc := connected_inputs_le_gates_add_one H rank hinj n C.connected_toSimpleGraph hhigh hlow
  have memC (v : Fin (n + gs.length)) : v ∈ C ↔ G.Reachable o v := by
    change G.connectedComponentMk v = G.connectedComponentMk o ↔ G.Reachable o v
    constructor
    · intro h
      exact (SimpleGraph.ConnectedComponent.exact h).symm
    · intro h
      exact SimpleGraph.ConnectedComponent.sound h.symm
  have hi : (Finset.univ.filter (fun v : C => rank v < n)).card =
      (inputComponent n gs o).card := by
    calc
      _ = (Finset.univ.filter (fun p : Fin n => Fin.castAdd gs.length p ∈ C)).card :=
        card_input_subtype n gs.length (fun v => v ∈ C)
      _ = _ := by
        congr 1
        ext p
        simp only [inputComponent, Finset.mem_filter, Finset.mem_univ, true_and]
        exact memC _
  have hj : (Finset.univ.filter (fun v : C => n ≤ rank v)).card =
      (gateComponent n gs o).card := by
    calc
      _ = (Finset.univ.filter (fun j : Fin gs.length => Fin.natAdd n j ∈ C)).card :=
        card_gate_subtype n gs.length (fun v => v ∈ C)
      _ = _ := by
        congr 1
        ext j
        simp only [gateComponent, Finset.mem_filter, Finset.mem_univ, true_and]
        exact memC _
  rw [hi, hj] at hc
  exact hc

open Classical in
lemma gateComponent_eq_univ_of_large (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (o : Fin (n + gs.length))
    (hlarge : gs.length + 1 ≤ (inputComponent n gs o).card) :
    gateComponent n gs o = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  have h := component_bound n gs hg o
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

open Classical in
lemma inputComponent_subset_of_reachable (n : ℕ) (gs : List Gate)
    (o o' : Fin (n + gs.length)) (h : (wireGraph n gs).Reachable o o') :
    inputComponent n gs o' ⊆ inputComponent n gs o := by
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (Finset.mem_filter.mp hp).2⟩

open Classical in
lemma reachable_gate_of_saturation (n : ℕ) (gs : List Gate) (o v : Fin (n + gs.length))
    (hall : gateComponent n gs o = Finset.univ) (hv : n ≤ v.val) :
    (wireGraph n gs).Reachable o v := by
  let j : Fin gs.length := ⟨v.val - n, by have := v.isLt; omega⟩
  have he : Fin.natAdd n j = v := by
    apply Fin.ext
    dsimp [j]
    omega
  have hj : j ∈ gateComponent n gs o := by rw [hall]; exact Finset.mem_univ _
  have h := (Finset.mem_filter.mp hj).2
  simpa only [he] using h

end PEqualNP.Outside.L_meta_1019.Components


namespace PEqualNP.Outside.L_meta_1019.Semantics

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

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
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

lemma value_eq_of_closed {n : ℕ} (C : Circuit) (B : Set ℕ)
    (closed : ∀ w, n ≤ w → w < n + C.size → w ∈ B →
      ∀ r ∈ (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs, r < w → r ∈ B)
    (x y : Fin n → Bool) (agree : ∀ p : Fin n, p.val ∈ B → x p = y p) :
    ∀ w, w ∈ B → value C x w = value C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwB
    by_cases hin : w < n
    · let p : Fin n := ⟨w, hin⟩
      change value C x p = value C y p
      rw [input_value, input_value]
      exact agree p hwB
    by_cases hgate : w < n + C.size
    · have hn : n ≤ w := by omega
      rw [gate_value C x w hn hgate, gate_value C y w hn hgate]
      apply congrArg (fun l => (C.gates[w - n]'(by unfold Circuit.size at hgate; omega)).op.eval l)
      apply List.map_congr_left
      intro r hr
      by_cases hread : r < w
      · rw [ite_eq_left hread, ite_eq_left hread]
        apply ih r hread
        apply closed w hn hgate hwB r
        · have hgi : w - n < C.gates.length := by unfold Circuit.size at hgate; omega
          have he : C.gates.getD (w - n) ⟨GateOp.or, []⟩ = C.gates[w - n]'hgi := by
            exact List.getD_eq_getElem _ _ hgi
          rwa [he]
        · exact hread
      · rw [ite_eq_right hread, ite_eq_right hread]
    · rw [missing_value C x w (by omega), missing_value C y w (by omega)]

lemma value_eq_on_component {n : ℕ} (C : Circuit)
    (G : SimpleGraph (Fin (n + C.size)))
    (edges : ∀ w (_hn : n ≤ w) (hw : w < n + C.size),
      ∀ r ∈ (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs, ∀ hr : r < w,
        G.Adj ⟨w, hw⟩ ⟨r, lt_trans hr hw⟩)
    (o : Fin (n + C.size)) (x y : Fin n → Bool)
    (agree : ∀ p : Fin n, G.Reachable o (Fin.castAdd C.size p) → x p = y p) :
    value C x o = value C y o := by
  let B : Set ℕ := {w | ∃ hw : w < n + C.size, G.Reachable o ⟨w, hw⟩}
  apply value_eq_of_closed C B
  · intro w hn hw hwB r hr hlt
    obtain ⟨_, hreach⟩ := hwB
    exact ⟨lt_trans hlt hw, hreach.trans (edges w hn hw r hr hlt).reachable⟩
  · intro p hp
    obtain ⟨_, hreach⟩ := hp
    exact agree p hreach
  · exact ⟨o.isLt, SimpleGraph.Reachable.refl _⟩

end PEqualNP.Outside.L_meta_1019.Semantics



namespace PEqualNP.Outside.L_meta_1019

def lines (i : Fin 3) : Finset (Fin 13) :=
  if i = 0 then ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 0)
  else if i = 1 then ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 12)
  else ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 10)

lemma line_union_size : (Finset.univ.biUnion lines).card = 10 := by decide

def positiveMask (i : Fin 3) : ℕ :=
  if i = 0 then 543 else if i = 1 then 4367 else 3143

lemma line_positive : ∀ i : Fin 3, ∃ x : Fin 13 → Bool,
    (Finset.univ.filter (fun v : Fin 13 => x v = true)).card = 6 ∧
      ∀ v ∈ lines i, x v = true := by
  have h : ∀ i : Fin 3,
      (Finset.univ.filter (fun v : Fin 13 => (positiveMask i).testBit v.val = true)).card = 6 ∧
        ∀ v ∈ lines i, (positiveMask i).testBit v.val = true := by decide
  intro i
  exact ⟨fun v => (positiveMask i).testBit v.val, h i⟩


lemma line_size : ∀ i : Fin 3, (lines i).card = 4 := by decide

lemma line_zero : ∀ i : Fin 3, (0 : Fin 13) ∈ lines i := by decide

end PEqualNP.Outside.L_meta_1019

namespace PEqualNP.Outside.L_meta_1019

def supportPoint (A : Finset (Fin 13)) : Fin 13 → Bool := fun i => decide (i ∈ A)

lemma supportPoint_weight (A : Finset (Fin 13)) :
    (Finset.univ.filter (fun i : Fin 13 => supportPoint A i = true)).card = A.card := by
  congr 1
  ext i
  simp [supportPoint]

lemma essential_subset_support (f : (Fin 13 → Bool) → Bool)
    (S T : Finset (Fin 13)) (hScard : S.card = 4)
    (hsupport : ∀ x y : Fin 13 → Bool, (∀ i ∈ T, x i = y i) → f x = f y)
    (hband : ∀ x : Fin 13 → Bool,
      ((Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 6 ∨
        (Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 7) →
      f x = decide (∀ i ∈ S, x i = true)) : S ⊆ T := by
  classical
  have hcompl : (Finset.univ \ S).card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), hScard]
    decide
  obtain ⟨E, hE, hEcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ (Finset.univ \ S).card by omega)
  have hdis : Disjoint S E := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiE
    exact (Finset.mem_sdiff.mp (hE hiE)).2 hiS
  have hycard : (S ∪ E).card = 7 := by
    rw [Finset.card_union_of_disjoint hdis, hScard, hEcard]
  have hytrue : f (supportPoint (S ∪ E)) = true := by
    rw [hband (supportPoint (S ∪ E)) (Or.inr (by rw [supportPoint_weight, hycard]))]
    simp only [decide_eq_true_eq]
    intro i hiS
    simp [supportPoint, hiS]
  intro p hpS
  by_contra hpT
  have hnpE : p ∉ E := fun hpE => (Finset.mem_sdiff.mp (hE hpE)).2 hpS
  have hxcard : (S.erase p ∪ E).card = 6 := by
    rw [Finset.card_union_of_disjoint (hdis.mono_left (Finset.erase_subset p S)),
      Finset.card_erase_of_mem hpS, hScard, hEcard]
  have hxfalse : f (supportPoint (S.erase p ∪ E)) = false := by
    rw [hband (supportPoint (S.erase p ∪ E)) (Or.inl (by rw [supportPoint_weight, hxcard]))]
    simp only [decide_eq_false_iff_not]
    intro h
    have ht := h p hpS
    simp [supportPoint, hnpE] at ht
  have heq : f (supportPoint (S ∪ E)) = f (supportPoint (S.erase p ∪ E)) := by
    apply hsupport
    intro i hiT
    have hip : i ≠ p := by rintro rfl; exact hpT hiT
    simp [supportPoint, Finset.mem_union, Finset.mem_erase, hip]
  rw [hytrue, hxfalse] at heq
  contradiction


end PEqualNP.Outside.L_meta_1019


namespace PEqualNP.Outside.L_meta_1019

open PEqualNP.CircuitLowerBounds

lemma component_support (n : ℕ) (gs : List Gate) (o : Fin (n + gs.length))
    (x y : Fin n → Bool)
    (h : ∀ p ∈ Components.inputComponent n gs o, x p = y p) :
    Semantics.value ⟨gs, 0⟩ x o = Semantics.value ⟨gs, 0⟩ y o := by
  classical
  refine Semantics.value_eq_on_component ⟨gs, 0⟩ (Components.wireGraph n gs) ?_ o x y ?_
  · intro w hn hw r hr hlt
    exact Or.inl ⟨hn, hlt, hr⟩
  · intro p hp
    apply h p
    simpa only [Components.inputComponent, Circuit.size, Finset.mem_filter, Finset.mem_univ,
      true_and] using hp

lemma outputs_valid (gs : List Gate) (out : Fin 3 → ℕ)
    (he : ∀ (i : Fin 3) (x : Fin 13 → Bool),
      ((Finset.univ.filter (fun p : Fin 13 => x p = true)).card = 6 ∨
        (Finset.univ.filter (fun p : Fin 13 => x p = true)).card = 7) →
      Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∀ v ∈ lines i, x v = true)) :
    ∀ i, out i < 13 + gs.length := by
  intro i
  by_contra! hhi
  obtain ⟨x, hx, hs⟩ := line_positive i
  have hv : Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = false :=
    Semantics.missing_value ⟨gs, 0⟩ x (out i) hhi
  have h := he i x (Or.inl hx)
  rw [hv] at h
  have ht : decide (∀ v ∈ lines i, x v = true) = true := decide_eq_true hs
  rw [ht] at h
  contradiction

lemma lower_from_band (gs : List Gate) (out : Fin 3 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ (i : Fin 3) (x : Fin 13 → Bool),
      ((Finset.univ.filter (fun p : Fin 13 => x p = true)).card = 6 ∨
        (Finset.univ.filter (fun p : Fin 13 => x p = true)).card = 7) →
      Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∀ v ∈ lines i, x v = true)) :
    9 ≤ gs.length := by
  classical
  have hb := outputs_valid gs out he
  let os (i : Fin 3) : Fin (13 + gs.length) := ⟨out i, hb i⟩
  let T (i : Fin 3) := Components.inputComponent 13 gs (os i)
  have dep (i : Fin 3) : ∀ x y : Fin 13 → Bool,
      (∀ p ∈ T i, x p = y p) →
        Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = Circuit.eval ⟨gs, out i⟩ (List.ofFn y) := by
    intro x y hxy
    exact component_support 13 gs (os i) x y hxy
  have sub (i : Fin 3) : lines i ⊆ T i :=
    essential_subset_support _ _ _ (line_size i) (dep i) (he i)
  have hz (i : Fin 3) :
      (Components.wireGraph 13 gs).Reachable (os i) (Fin.castAdd gs.length (0 : Fin 13)) := by
    have h : (0 : Fin 13) ∈ T i := sub i (line_zero i)
    exact (Finset.mem_filter.mp h).2
  have reach (i : Fin 3) : (Components.wireGraph 13 gs).Reachable (os 0) (os i) :=
    (hz 0).trans (hz i).symm
  have hu : Finset.univ.biUnion lines ⊆ T 0 := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact Components.inputComponent_subset_of_reachable 13 gs (os 0) (os i) (reach i) (sub i hi)
  have hc := Components.component_bound 13 gs (fun g h => (hg g h).2) (os 0)
  have hcard : (Components.gateComponent 13 gs (os 0)).card ≤ gs.length := by
    have h := Finset.card_le_card (Finset.subset_univ (Components.gateComponent 13 gs (os 0)))
    simpa using h
  have hten := Finset.card_le_card hu
  rw [line_union_size] at hten
  change (T 0).card ≤ _ at hc
  omega

end PEqualNP.Outside.L_meta_1019


theorem PEqualNP.Outside.L_meta_1019 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 3 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin 13 → Bool, ((Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 6 ∨ (Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 7) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 0⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 0)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 1⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 12)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 2⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 10)), x v = true)) → 9 ≤ gates.length := by
  intro gates out hg hb
  apply PEqualNP.Outside.L_meta_1019.lower_from_band gates out hg
  intro i x hx
  have h := hb x hx
  fin_cases i
  · simpa [PEqualNP.Outside.L_meta_1019.lines] using h.1
  · simpa [PEqualNP.Outside.L_meta_1019.lines] using h.2.1
  · simpa [PEqualNP.Outside.L_meta_1019.lines] using h.2.2
