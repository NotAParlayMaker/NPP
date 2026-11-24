import Mathlib
import PEqualNP.Defs

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost

namespace PEqualNP.Outside.L_meta_2874
namespace BlockToShared

private theorem wireLength (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  change (C.gates.foldl step x).length = _
  induction C.gates generalizing x with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega

private def Preserves (n : ℕ) (C D : Circuit) : Prop :=
  ∀ w S, ComputesOr n C w S → ComputesOr n D w S

private theorem appendOr (n : ℕ) (C : Circuit) (hC : IsOrCircuit n C)
    (s t : Finset (Fin n)) (a b : ℕ) (ha : ComputesOr n C a s) (hb : ComputesOr n C b t) :
    ∃ D, IsOrCircuit n D ∧ Preserves n C D ∧ D.gates.length = C.gates.length + 1 ∧
      ∃ w, ComputesOr n D w (s ∪ t) := by
  let g : Gate := ⟨GateOp.or, [a, b]⟩
  let D : Circuit := ⟨C.gates ++ [g], C.output⟩
  have hLen : D.gates.length = C.gates.length + 1 := by simp [D]
  have hWires (x : Fin n → Bool) :
      D.wires (List.ofFn x) =
        C.wires (List.ofFn x) ++ [PEqualNP.BlindGate.wireValue C n x a || PEqualNP.BlindGate.wireValue C n x b] := by
    simp [D, g, Circuit.wires, List.foldl_append, PEqualNP.BlindGate.wireValue, GateOp.eval]
  have hLength (x : Fin n → Bool) : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wireLength, List.length_ofFn]
  refine ⟨D, ?_, ?_, hLen, n + C.gates.length, ?_⟩
  · intro j hj
    by_cases old : j < C.gates.length
    · change isOrOp ((C.gates ++ [g])[j]).op = true ∧
        ((C.gates ++ [g])[j]).inputs.length = 2 ∧
        ∀ i ∈ ((C.gates ++ [g])[j]).inputs, i < n + j
      rw [List.getElem_append_left old]
      exact hC j old
    · have eq : j = C.gates.length := by omega
      subst j
      change isOrOp ((C.gates ++ [g])[C.gates.length]).op = true ∧
        ((C.gates ++ [g])[C.gates.length]).inputs.length = 2 ∧
        ∀ i ∈ ((C.gates ++ [g])[C.gates.length]).inputs, i < n + C.gates.length
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp [g, isOrOp, ha.1, hb.1]
  · intro w S hw
    refine ⟨by have := hw.1; omega, fun x => ?_⟩
    unfold PEqualNP.BlindGate.wireValue
    rw [hWires, List.getD_append _ _ _ _ (by rw [hLength]; exact hw.1)]
    exact hw.2 x
  · refine ⟨by omega, fun x => ?_⟩
    unfold PEqualNP.BlindGate.wireValue
    rw [hWires, ← hLength x, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    simp only [List.getD_cons_zero, Bool.or_eq_true, ha.2 x, hb.2 x, Finset.mem_union]
    constructor
    · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
      · exact ⟨i, Or.inl hi, hx⟩
      · exact ⟨i, Or.inr hi, hx⟩
    · rintro ⟨i, hi | hi, hx⟩
      · exact Or.inl ⟨i, hi, hx⟩
      · exact Or.inr ⟨i, hi, hx⟩

private theorem unionRoots (n : ℕ) (R : Finset (Finset (Fin n))) (hR : R.Nonempty) :
    ∀ (C : Circuit), IsOrCircuit n C →
      (∀ s ∈ R, ∃ w, ComputesOr n C w s) →
      ∃ D, IsOrCircuit n D ∧ Preserves n C D ∧
        D.gates.length ≤ C.gates.length + (R.card - 1) ∧ ∃ w, ComputesOr n D w (R.biUnion id) := by
  classical
  induction R using Finset.induction_on with
  | empty => simp at hR
  | @insert s R hs ih =>
      intro C hC avail
      obtain ⟨a, ha⟩ := avail s (Finset.mem_insert_self _ _)
      by_cases hEmpty : R = ∅
      · subst R
        exact ⟨C, hC, fun _ _ hw => hw, by simp, a, by simpa using ha⟩
      · have hR' : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
        obtain ⟨D, hD, keep, count, b, hb⟩ :=
          ih hR' C hC (fun t ht => avail t (Finset.mem_insert_of_mem ht))
        obtain ⟨E, hE, keep', count', w, hw⟩ := appendOr n D hD _ _ a b (keep _ _ ha) hb
        have hPos := Finset.card_pos.mpr hR'
        refine ⟨E, hE, fun v t ht => keep' v t (keep v t ht), ?_, w, ?_⟩
        · rw [Finset.card_insert_of_notMem hs]
          omega
        · simpa only [Finset.biUnion_insert, id_eq] using hw

theorem groupOr (n : ℕ) (H : Finset (Block n)) (roots : Block n → Finset (Finset (Fin n))) :
    ∀ (C : Circuit), IsOrCircuit n C →
      (∀ p ∈ H, (roots p).Nonempty ∧ (roots p).biUnion id = p.2 ∧
        ∀ s ∈ roots p, ∃ w, ComputesOr n C w s) →
      ∃ D, IsOrCircuit n D ∧ Preserves n C D ∧
        D.gates.length ≤ C.gates.length + (∑ p ∈ H, ((roots p).card - 1)) ∧
        ∀ p ∈ H, ∃ w, ComputesOr n D w p.2 := by
  classical
  induction H using Finset.induction_on with
  | empty =>
      intro C hC _
      exact ⟨C, hC, fun _ _ hw => hw, by simp, by simp⟩
  | @insert p H hp ih =>
      intro C hC hRoots
      obtain ⟨D, hD, keep, count, ready⟩ :=
        ih C hC (fun q hq => hRoots q (Finset.mem_insert_of_mem hq))
      obtain ⟨nonempty, eq, avail⟩ := hRoots p (Finset.mem_insert_self _ _)
      have avail' : ∀ s ∈ roots p, ∃ w, ComputesOr n D w s := by
        intro s hs
        obtain ⟨w, hw⟩ := avail s hs
        exact ⟨w, keep _ _ hw⟩
      obtain ⟨E, hE, keep', count', w, hw⟩ := unionRoots n (roots p) nonempty D hD avail'
      refine ⟨E, hE, fun v t ht => keep' v t (keep v t ht), ?_, ?_⟩
      · rw [Finset.sum_insert hp]
        omega
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact ⟨w, eq ▸ hw⟩
        · obtain ⟨v, hv⟩ := ready q hq
          exact ⟨v, keep' v _ hv⟩

private theorem singleton_wire (n : ℕ) (C : Circuit) (a : Fin n) :
    ComputesOr n C a.val {a} := by
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (ha : a.val < w.length) :
      (gs.foldl step w).getD a.val false = w.getD a.val false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ ha
  have hlt : a.val < n + C.gates.length := a.isLt.trans_le (Nat.le_add_right _ _)
  refine ⟨hlt, fun x => ?_⟩
  have haux : a.val < (List.ofFn x).length := by simp
  change (C.gates.foldl step (List.ofFn x)).getD a.val false = true ↔ _
  rw [keep C.gates (List.ofFn x) haux, List.getD_eq_getElem _ _ haux]
  simp only [List.getElem_ofFn, Finset.mem_singleton]
  exact ⟨fun hx => ⟨a, rfl, hx⟩, by rintro ⟨u, rfl, h⟩; exact h⟩

private theorem serveSeconds (n : ℕ) (F : Finset (Block n)) (C : Circuit)
    (hC : IsOrCircuit n C) (hN : ∀ p ∈ F, p.2.Nonempty) :
    ∃ D, IsOrCircuit n D ∧ Preserves n C D ∧
      D.gates.length ≤ C.gates.length + (∑ p ∈ F, (p.2.card - 1)) ∧
      ∀ p ∈ F, ∃ w, ComputesOr n D w p.2 := by
  let single := fun u : Fin n => ({u} : Finset (Fin n))
  let roots := fun p : Block n => p.2.image single
  have rootCard (p : Block n) : (roots p).card = p.2.card :=
    Finset.card_image_of_injective _ Finset.singleton_injective
  have rootEq (p : Block n) : (roots p).biUnion id = p.2 := by
    ext u
    constructor
    · intro hu
      obtain ⟨s, hs, hu⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
      have he : u = a := Finset.mem_singleton.mp hu
      exact he.symm ▸ ha
    · intro hu
      exact Finset.mem_biUnion.mpr ⟨single u, Finset.mem_image_of_mem _ hu, Finset.mem_singleton_self _⟩
  have rootAvail (p : Block n) (hp : p ∈ F) :
      (roots p).Nonempty ∧ (roots p).biUnion id = p.2 ∧ ∀ s ∈ roots p, ∃ w, ComputesOr n C w s := by
    refine ⟨(hN p hp).image _, rootEq p, ?_⟩
    intro s hs
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨a.val, singleton_wire n C a⟩
  obtain ⟨D, hD, keep, hSize, hWires⟩ := groupOr n F roots C hC rootAvail
  exact ⟨D, hD, keep, by simpa only [rootCard] using hSize, hWires⟩

theorem hasSharedBlockCostOfHasBlockCost (n c : ℕ) (G : SimpleGraph (Fin n))
    (h : HasBlockCost G c) : HasSharedBlockCost G c := by
  obtain ⟨F, hCover, hBudget⟩ := h
  let base : Circuit := ⟨[], 0⟩
  have hBase : IsOrCircuit n base := by
    intro j hj
    simp [base] at hj
  obtain ⟨C, hC, _, hSizeR, hRight⟩ :=
    serveSeconds n F base hBase (fun p hp => (hCover.1 p hp).2.2.1)
  let swap : Block n ↪ Block n :=
    ⟨Prod.swap, fun _ _ h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)⟩
  let swapped := F.map swap
  have hLeftNonempty : ∀ p ∈ swapped, p.2.Nonempty := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    exact (hCover.1 q hq).2.1
  obtain ⟨D, hD, keep, hSizeL, hLeft⟩ := serveSeconds n swapped C hC hLeftNonempty
  have hChargeL : (∑ p ∈ swapped, (p.2.card - 1)) = ∑ p ∈ F, (p.1.card - 1) := by
    simp only [swapped, Finset.sum_map]
    rfl
  let k := (∑ p ∈ F, (p.2.card - 1)) + (∑ p ∈ F, (p.1.card - 1))
  have hSize : D.gates.length ≤ k := by
    rw [hChargeL] at hSizeL
    simp only [base, List.length_nil, zero_add] at hSizeR
    dsimp [k]
    omega
  have charges : (∑ p ∈ F, blockCost p) = k + F.card := by
    calc
      _ = ∑ p ∈ F, ((p.2.card - 1) + (p.1.card - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hA := Finset.card_pos.mpr (hCover.1 p hp).2.1
        have hB := Finset.card_pos.mpr (hCover.1 p hp).2.2.1
        unfold blockCost
        omega
      _ = _ := by simp [k, Finset.sum_add_distrib]
  refine ⟨F, hCover, k, ⟨D, ⟨hD, ?_⟩, hSize⟩, ?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
      have hSwap : swap p ∈ swapped := Finset.mem_map.mpr ⟨p, hp, rfl⟩
      obtain ⟨w, hw⟩ := hLeft _ hSwap
      exact ⟨w, hw.1, hw⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨w, hw⟩ := hRight p hp
      exact ⟨w, (keep w _ hw).1, keep w _ hw⟩
  · unfold familyCost at hBudget
    rw [charges] at hBudget
    exact hBudget


end BlockToShared

namespace WireEvaluation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

end WireEvaluation

namespace Compiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost PEqualNP.ReadTwo PEqualNP.BlindGate

private def append (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.size⟩

private theorem append_size (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (append n C op a b).size = C.size + 1 := by simp [append, Circuit.size]

private theorem gate_old (n : ℕ) (C : Circuit) (op : GateOp) (a b j : ℕ)
    (hj : j < C.size) : gateAt (append n C op a b) j = gateAt C j := by
  simp [gateAt, append, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

private theorem gate_last (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    gateAt (append n C op a b) C.size = ⟨op, [a, b]⟩ := by
  simp [gateAt, append, Circuit.size, List.getD_eq_getElem?_getD]

private theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  rcases C with ⟨gs, o⟩
  simp only [Circuit.wires, Circuit.size]
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp
      omega

private theorem append_wires (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    (append n C op a b).wires (List.ofFn x) = C.wires (List.ofFn x) ++
      [op.eval [wval C x a, wval C x b]] := by
  simp [append, Circuit.wires, List.foldl_append, wval]

private theorem append_keep (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.size) :
    wval (append n C op a b) x w = wval C x w := by
  unfold wval
  rw [append_wires]
  exact List.getD_append _ _ _ _ (by simpa [wires_length] using hw)

private theorem append_eval (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    (append n C op a b).eval (List.ofFn x) = op.eval [wval C x a, wval C x b] := by
  unfold Circuit.eval
  rw [append_wires]
  have h : (append n C op a b).output = (C.wires (List.ofFn x)).length := by
    simp [append, wires_length]
  rw [h]
  simp

private theorem append_model (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (op : GateOp) (ho : op = .and ∨ op = .or) (a b : ℕ) (ha : a < n + C.size)
    (hb : b < n + C.size) : PEqualNP.TopForm.IsAO2 n (append n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hC.1 g hg
    · have he := List.mem_singleton.mp hg
      subst g
      exact ho
  · intro j hj w hw
    change j < (append n C op a b).size at hj
    rw [append_size] at hj
    by_cases hj' : j < C.size
    · rw [gate_old _ _ _ _ _ _ hj'] at hw
      exact hC.2.1 j hj' w hw
    · have he : j = C.size := by omega
      subst j
      rw [gate_last] at hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      exact hw.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hC.2.2 g hg
    · rcases List.mem_singleton.mp hg with rfl
      rfl

private theorem or_model (n : ℕ) (C : Circuit) (hC : IsOrCircuit n C) :
    PEqualNP.TopForm.IsAO2 n C := by
  have valid (j : ℕ) (hj : j < C.gates.length) : (C.gates[j]).op = GateOp.or := by
    have hOp := (hC j hj).1
    cases he : (C.gates[j]).op <;> simp_all [isOrOp]
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    exact Or.inr (valid j hj)
  · intro j hj i hi
    exact (hC j hj).2.2 i (by simpa only [gateAt, List.getD_eq_getElem _ _ hj] using hi)
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    exact (hC j hj).2.1

private def Crossing (P L : Finset ℕ) (a b : ℕ) : Prop :=
  (a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)

private structure Compatible (n : ℕ) (base C : Circuit) (P L : Finset ℕ) : Prop where
  model : PEqualNP.TopForm.IsAO2 n C
  lower : base.size ≤ C.size
  keep : ∀ (x : Fin n → Bool) w, w < n + base.size → wval C x w = wval base x w
  gates : ∀ j < base.size, gateAt C j = gateAt base j
  andPins : ∀ j, isAnd C j →
    ∃ a b : ℕ, (gateAt C j).inputs = [a,b] ∧ Crossing P L a b

private theorem compatible_base (n : ℕ) (C : Circuit) (hC : IsOrCircuit n C) (P L : Finset ℕ) :
    Compatible n C C P L := by
  refine ⟨or_model n C hC, le_rfl, fun _ _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro j hj
  obtain ⟨a, b⟩ := hj
  have hop := (hC j a).1
  rw [← List.getD_eq_getElem _ ⟨GateOp.or, []⟩ a] at hop
  change isOrOp (gateAt C j).op = true at hop
  rw [b] at hop
  contradiction

private theorem compatible_append {n : ℕ} {base C : Circuit} {P L : Finset ℕ}
    (hC : Compatible n base C P L) (op : GateOp) (ho : op = .and ∨ op = .or)
    (a b : ℕ) (ha : a < n + C.size) (hb : b < n + C.size)
    (hAnd : op = .and → Crossing P L a b) :
    Compatible n base (append n C op a b) P L := by
  refine ⟨append_model n C hC.model op ho a b ha hb, ?_, ?_, ?_, ?_⟩
  · rw [append_size]
    exact hC.lower.trans (Nat.le_succ _)
  · intro x w hw
    rw [append_keep n C op a b x w (by have h := hC.lower; omega)]
    exact hC.keep x w hw
  · intro j hj
    rw [gate_old _ _ _ _ _ _ (hj.trans_le hC.lower),hC.gates j hj]
  · intro j hj
    have hJ := hj.1
    change j < (append n C op a b).size at hJ
    rw [append_size] at hJ
    by_cases hj' : j < C.size
    · have hgate := gate_old n C op a b j hj'
      rw [hgate]
      exact hC.andPins j ⟨hj',hgate ▸ hj.2⟩
    · have hEq : j = C.size := by omega
      subst j
      have hGate := gate_last n C op a b
      have hOp := hj.2
      rw [hGate] at hOp ⊢
      exact ⟨a,b,rfl,hAnd hOp⟩

private def Fires {n : ℕ} (p : Block n) (x : Fin n → Bool) : Prop :=
  (∃ u ∈ p.1, x u = true) ∧ ∃ v ∈ p.2, x v = true

private theorem attach {n : ℕ} (base : Circuit) (hBase : IsOrCircuit n base) (P L : Finset ℕ) (bs : List (Block n))
    (hSides : ∀ p ∈ bs, ∃ a b, ComputesOr n base a p.1 ∧ ComputesOr n base b p.2 ∧ Crossing P L a b) :
    ∃ D : Circuit, Compatible n base D P L ∧
      D.size ≤ base.size + bs.length + (bs.length - 1) ∧
      (bs ≠ [] → D.output < n + D.size) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ p ∈ bs, Fires p x := by
  induction bs with
  | nil =>
      let D : Circuit := ⟨base.gates, n + base.size⟩
      have hEq : D.gates = base.gates := rfl
      have hCompatible : Compatible n base D P L := by
        have h := compatible_base n base hBase P L
        exact ⟨h.model, h.lower, h.keep, h.gates, h.andPins⟩
      refine ⟨D, hCompatible, by simp [D, Circuit.size], by simp, ?_⟩
      intro x
      have hLen : (D.wires (List.ofFn x)).length ≤ D.output := by
        simp [D, wires_length, Circuit.size]
      unfold Circuit.eval
      rw [List.getD_eq_default _ _ hLen]
      simp
  | cons p bs ih =>
      obtain ⟨C, hC, hSize, hOut, hFun⟩ := ih fun q hq => hSides q (List.mem_cons_of_mem _ hq)
      obtain ⟨a, b, ha, hb, hCross⟩ := hSides p List.mem_cons_self
      have haOld : a < n + C.size := ha.1.trans_le (Nat.add_le_add_left hC.lower n)
      have hbOld : b < n + C.size := hb.1.trans_le (Nat.add_le_add_left hC.lower n)
      let A := append n C .and a b
      have hA : Compatible n base A P L :=
        compatible_append hC .and (Or.inl rfl) a b haOld hbOld (fun _ => hCross)
      have hASize : A.size = C.size + 1 := append_size _ _ _ _ _
      have hAOut : A.output < n + A.size := by change n + C.size < n + A.size; omega
      have hAVal (x : Fin n → Bool) : A.eval (List.ofFn x) = true ↔ Fires p x := by
        change (append n C .and a b).eval (List.ofFn x) = true ↔ Fires p x
        rw [append_eval]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
        rw [hC.keep x a ha.1, hC.keep x b hb.1]
        exact and_congr (ha.2 x) (hb.2 x)
      by_cases hEmpty : bs = []
      · refine ⟨A, hA, by simp [hEmpty] at hSize ⊢; omega, fun _ => hAOut, ?_⟩
        simp only [hEmpty, List.mem_cons, List.not_mem_nil, or_false]
        exact fun x => (hAVal x).trans (by simp)
      · have hcA : C.output < n + A.size := by have := hOut hEmpty; omega
        let D := append n A .or A.output C.output
        have hD : Compatible n base D P L :=
          compatible_append hA .or (Or.inr rfl) _ _ hAOut hcA (fun h => by cases h)
        have hDSize : D.size = A.size + 1 := append_size _ _ _ _ _
        have hDOut : D.output < n + D.size := by change n + A.size < n + D.size; omega
        have hLen : 0 < bs.length := by
          cases bs with
          | nil => exact (hEmpty rfl).elim
          | cons q qs => simp
        refine ⟨D, hD, by simp only [List.length_cons]; omega, fun _ => hDOut, ?_⟩
        intro x
        change (append n A .or A.output C.output).eval (List.ofFn x) = true ↔ _
        rw [append_eval]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
        have hAC : wval A x C.output = wval C x C.output :=
          append_keep n C .and a b x C.output (hOut hEmpty)
        rw [hAC]
        change A.eval (List.ofFn x) = true ∨ C.eval (List.ofFn x) = true ↔ _
        rw [hAVal, hFun]
        simp only [List.mem_cons]
        constructor
        · rintro (hp | ⟨q, hq, hFire⟩)
          · exact ⟨p, Or.inl rfl, hp⟩
          · exact ⟨q, Or.inr hq, hFire⟩
        · rintro ⟨q, (rfl | hq), hFire⟩
          · exact Or.inl hFire
          · exact Or.inr ⟨q, hq, hFire⟩


private def rejectedWires {n : ℕ} (C : Circuit) (x : Fin n → Bool) : Finset ℕ :=
  (Finset.range (n + C.size)).filter fun w => wval C x w = false

private theorem mem_rejectedWires {n : ℕ} {C : Circuit} {x : Fin n → Bool} {w : ℕ} :
    w ∈ rejectedWires C x ↔ w < n + C.size ∧ wval C x w = false := by
  simp [rejectedWires]

private theorem reject_computesOr {n : ℕ} {C : Circuit} {x : Fin n → Bool}
    {w : ℕ} {s : Finset (Fin n)} (hw : ComputesOr n C w s)
    (off : ∀ a ∈ s, x a = false) :
    w ∈ rejectedWires C x := by
  refine mem_rejectedWires.mpr ⟨hw.1, Bool.eq_false_iff.mpr ?_⟩
  intro yes
  obtain ⟨a,ha,hx⟩ := (hw.2 x).mp yes
  rw [off a ha] at hx
  contradiction

private theorem rejected_closed {n : ℕ} {base D : Circuit} {P L : Finset ℕ}
    (hBase : IsOrCircuit n base) (hD : Compatible n base D P L)
    (x : Fin n → Bool) (raw : ℕ → Prop)
    (hRaw : ∀ a : Fin n, x a = false → raw a.val) :
    ∀ w ∈ rejectedWires base x, raw w ∨ ∃ j < D.gates.length,
      w = n + j ∧ (gateAt D j).op = GateOp.or ∧
        ∀ u ∈ (gateAt D j).inputs, u ∈ rejectedWires base x := by
  intro w hw
  obtain ⟨bound,rejected⟩ := mem_rejectedWires.mp hw
  by_cases input : w < n
  · left
    let p : Fin n := ⟨w,input⟩
    apply hRaw p
    have source : wval base x w = x p := by
      have h := WireEvaluation.val_input (C := base) (x := List.ofFn x)
        (by simp : (List.ofFn x).length = n) input
      change wval base x w = (List.ofFn x).getD w false at h
      rw [h,List.getD_eq_getElem _ _ (by simpa using input),List.getElem_ofFn]
    exact source.symm.trans rejected
  · right
    obtain ⟨j,hj,rfl⟩ : ∃ j < base.size, w = n + j :=
      ⟨w-n,by omega,by omega⟩
    have earlier : ∀ u ∈ (gateAt base j).inputs, u < n+j :=
      (or_model n base hBase).2.1 j hj
    have hop : (gateAt base j).op = GateOp.or := by
      have isOr := (hBase j hj).1
      rw [← List.getD_eq_getElem _ ⟨GateOp.or,[]⟩ hj] at isOr
      change isOrOp (gateAt base j).op = true at isOr
      cases h : (gateAt base j).op <;> simp_all [isOrOp]
    have gateValue : wval base x (n+j) =
        GateOp.or.eval ((gateAt base j).inputs.map fun i => wval base x i) := by
      have h := WireEvaluation.val_gate (C := base) (x := List.ofFn x)
        (by simp : (List.ofFn x).length = n) hj
      change wval base x (n+j) = (gateAt base j).op.eval
        ((gateAt base j).inputs.map fun i => if i < n+j then wval base x i else false) at h
      rw [h,hop]
      congr 1
      apply List.map_congr_left
      intro i hi
      simp [earlier i hi]
    refine ⟨j,hj.trans_le hD.lower,rfl,?_⟩
    rw [hD.gates j hj]
    refine ⟨hop,?_⟩
    intro u hu
    have hlt := earlier u hu
    refine mem_rejectedWires.mpr ⟨by omega,Bool.eq_false_iff.mpr ?_⟩
    intro yes
    have hOr : GateOp.or.eval ((gateAt base j).inputs.map fun i => wval base x i) = true :=
      List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨u,hu,yes⟩,rfl⟩
    exact Bool.false_ne_true (rejected.symm.trans (gateValue.trans hOr))

private def HasParts (A B : ℕ) (G : SimpleGraph (Fin (A+B))) : Prop :=
  ∀ u v, G.Adj u v → (u.val < A ∧ A ≤ v.val) ∨ (A ≤ u.val ∧ v.val < A)

private theorem typedBlock {A B : ℕ} {G : SimpleGraph (Fin (A+B))} (parts : HasParts A B G)
    {p : Block (A+B)} (legal : IsBlock G p) :
    ((∀ u ∈ p.1, u.val < A) ∧ (∀ v ∈ p.2, A ≤ v.val)) ∨
      ((∀ u ∈ p.1, A ≤ u.val) ∧ (∀ v ∈ p.2, v.val < A)) := by
  obtain ⟨a,ha⟩ := legal.2.1
  obtain ⟨b,hb⟩ := legal.2.2.1
  have edges := legal.2.2.2
  rcases parts a b (edges a ha b hb) with ⟨hA,hB⟩ | ⟨hA,hB⟩
  · left
    constructor
    · intro u hu
      rcases parts u b (edges u hu b hb) with h | h
      · exact h.1
      · omega
    · intro v hv
      rcases parts a v (edges a ha v hv) with h | h
      · exact h.2
      · omega
  · right
    constructor
    · intro u hu
      rcases parts u b (edges u hu b hb) with h | h
      · omega
      · exact h.1
    · intro v hv
      rcases parts a v (edges a ha v hv) with h | h
      · omega
      · exact h.2

-- Construction with any legal shared OR cost, using only point-line AND gates.
theorem sharedGivesTwoLevel (A B c : ℕ) (G : SimpleGraph (Fin (A+B)))
    [DecidableRel G.Adj] (parts : HasParts A B G) (budget : HasSharedBlockCost G c) :
    ∃ (D : Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (A+B) D ∧
      (∀ x : Fin (A+B) → Bool, circuitFun (A+B) D x =
        decide (∃ u v : Fin (A+B), G.Adj u v ∧ x u = true ∧ x v = true)) ∧ D.size ≤ c ∧
      (∀ w ∈ P, w < A ∨ ∃ j < D.gates.length, w = A+B+j ∧
        (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ P) ∧
      (∀ w ∈ L, (A ≤ w ∧ w < A+B) ∨ ∃ j < D.gates.length, w = A+B+j ∧
        (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ L) ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∃ a b : ℕ, (gateAt D j).inputs = [a,b] ∧
          ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  classical
  obtain ⟨F,cover,k,⟨base,⟨hBase,ready⟩,baseSize⟩,total⟩ := budget
  let onlyLines : Fin (A+B) → Bool := fun p => decide (A ≤ p.val)
  let onlyPoints : Fin (A+B) → Bool := fun p => decide (p.val < A)
  let P := rejectedWires base onlyLines
  let L := rejectedWires base onlyPoints
  have hSides : ∀ p ∈ F.toList, ∃ a b,
      ComputesOr (A+B) base a p.1 ∧ ComputesOr (A+B) base b p.2 ∧ Crossing P L a b := by
    intro p hp
    have h := Finset.mem_toList.mp hp
    have m₁ : p.1 ∈ sides F := Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
    have m₂ : p.2 ∈ sides F := Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    obtain ⟨a,_,ha⟩ := ready p.1 m₁
    obtain ⟨b,_,hb⟩ := ready p.2 m₂
    refine ⟨a,b,ha,hb,?_⟩
    rcases typedBlock parts (cover.1 p h) with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨reject_computesOr ha (fun u hu => by simp [onlyLines,not_le_of_gt (h₁ u hu)]),
        reject_computesOr hb (fun u hu => by simp [onlyPoints,not_lt_of_ge (h₂ u hu)])⟩
    · exact Or.inr ⟨reject_computesOr ha (fun u hu => by simp [onlyPoints,not_lt_of_ge (h₁ u hu)]),
        reject_computesOr hb (fun u hu => by simp [onlyLines,not_le_of_gt (h₂ u hu)])⟩
  obtain ⟨D,hD,hSize,_,hFun⟩ := attach base hBase P L F.toList hSides
  refine ⟨D,P,L,hD.model,?_,?_,?_,?_,?_⟩
  · intro x
    apply Bool.eq_iff_iff.mpr
    change D.eval (List.ofFn x) = true ↔ _
    rw [hFun,decide_eq_true_eq]
    constructor
    · rintro ⟨p,hp,⟨u,hu,hxu⟩,⟨v,hv,hxv⟩⟩
      exact ⟨u,v,(cover.1 p (Finset.mem_toList.mp hp)).2.2.2 u hu v hv,hxu,hxv⟩
    · rintro ⟨u,v,adj,hu,hv⟩
      obtain ⟨p,hp,hCross⟩ := cover.2 u v adj
      exact ⟨p,Finset.mem_toList.mpr hp,hCross.elim
        (fun h => ⟨⟨u,h.1,hu⟩,⟨v,h.2,hv⟩⟩)
        (fun h => ⟨⟨v,h.1,hv⟩,⟨u,h.2,hu⟩⟩)⟩
  · simp only [Finset.length_toList] at hSize
    change base.size ≤ k at baseSize
    omega
  · apply rejected_closed hBase hD onlyLines (· < A)
    intro i hi
    have h : ¬ A ≤ i.val := of_decide_eq_false hi
    omega
  · apply rejected_closed hBase hD onlyPoints (fun w => A ≤ w ∧ w < A+B)
    intro i hi
    have h : ¬ i.val < A := of_decide_eq_false hi
    exact ⟨Nat.le_of_not_gt h,i.isLt⟩
  · intro j hj hop
    exact hD.andPins j ⟨hj,hop⟩

end Compiler


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.SharedBlockCost PEqualNP.BicliqueBlockCost

def incidenceGraph {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop) : SimpleGraph (Fin (Np+Nl)) :=
  SimpleGraph.fromRel fun a b =>
    ∃ p l, a = Fin.castAdd Nl p ∧ b = Fin.natAdd Np l ∧ I p l

private theorem point_ne_line {A B : ℕ} (p : Fin A) (l : Fin B) :
    Fin.castAdd B p ≠ Fin.natAdd A l := by
  intro eq
  have h := congrArg Fin.val eq
  change p.val = A + l.val at h
  omega

theorem incidenceAdj {A B : ℕ} (I : Fin A → Fin B → Prop) (u v : Fin (A+B)) :
    (incidenceGraph I).Adj u v ↔
      (∃ p l, u = Fin.castAdd B p ∧ v = Fin.natAdd A l ∧ I p l) ∨
      (∃ p l, v = Fin.castAdd B p ∧ u = Fin.natAdd A l ∧ I p l) := by
  unfold incidenceGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    rcases h with ⟨p,l,rfl,rfl,_⟩ | ⟨p,l,rfl,rfl,_⟩
    · exact point_ne_line p l
    · exact (point_ne_line p l).symm

private theorem incidence_parts {A B : ℕ} (I : Fin A → Fin B → Prop) :
    Compiler.HasParts A B (incidenceGraph I) := by
  intro u v h
  rcases (incidenceAdj I u v).mp h with ⟨p,l,rfl,rfl,_⟩ | ⟨p,l,rfl,rfl,_⟩
  · exact Or.inl ⟨p.isLt,Nat.le_add_right _ _⟩
  · exact Or.inr ⟨Nat.le_add_right _ _,p.isLt⟩

private theorem incidence_pred {A B : ℕ} (I : Fin A → Fin B → Prop) (x : Fin (A+B) → Bool) :
    (∃ u v, (incidenceGraph I).Adj u v ∧ x u = true ∧ x v = true) ↔
      ∃ p l, I p l ∧ x (Fin.castAdd B p) = true ∧ x (Fin.natAdd A l) = true := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    rcases (incidenceAdj I u v).mp h with ⟨p,l,rfl,rfl,edge⟩ | ⟨p,l,rfl,rfl,edge⟩
    · exact ⟨p,l,edge,hu,hv⟩
    · exact ⟨p,l,edge,hv,hu⟩
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨_,_,(incidenceAdj I _ _).mpr (Or.inl ⟨p,l,rfl,rfl,h⟩),hp,hl⟩

abbrev TwoLevel (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (c : ℕ) : Prop :=
  ∃ (D : Circuit) (P L : Finset ℕ), IsAO2 (Np+Nl) D ∧
    (∀ y : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) D y =
      decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧
        y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ c ∧
    (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np+Nl+i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ P) ∧
    (∀ w ∈ L, (Np ≤ w ∧ w < Np+Nl) ∨ ∃ i < D.gates.length, w = Np+Nl+i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L) ∧
    ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
      ∃ a b : ℕ, (gateAt D i).inputs = [a,b] ∧
        ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))

-- Compile a shared block cover into the specified two-level incidence circuit.
theorem compileShared (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (c : ℕ) :
    let G := SimpleGraph.fromRel (fun (a b : Fin (Np+Nl)) =>
      ∃ (p : Fin Np) (l : Fin Nl), a = Fin.castAdd Nl p ∧ b = Fin.natAdd Np l ∧ I p l)
    HasSharedBlockCost G c → TwoLevel Np Nl I c := by
  intro G h
  letI : DecidableRel (incidenceGraph I).Adj := by
    unfold incidenceGraph
    infer_instance
  obtain ⟨D,P,L,ao,correct,budget,hP,hL,hAND⟩ :=
    Compiler.sharedGivesTwoLevel Np Nl c (incidenceGraph I) (incidence_parts I) h
  refine ⟨D,P,L,ao,?_,budget,hP,hL,hAND⟩
  intro x
  rw [correct x]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact incidence_pred I x

-- Compile an ordinary block cover without exceeding the block cost.
theorem compile (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (c : ℕ) :
    let G := SimpleGraph.fromRel (fun (a b : Fin (Np+Nl)) =>
      ∃ (p : Fin Np) (l : Fin Nl), a = Fin.castAdd Nl p ∧ b = Fin.natAdd Np l ∧ I p l)
    HasBlockCost G c → TwoLevel Np Nl I c := by
  intro G h
  exact compileShared Np Nl I c (BlockToShared.hasSharedBlockCostOfHasBlockCost (Np+Nl) c G h)



namespace Stars

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.BicliqueBlockCost
open scoped BigOperators

-- Assign each edge to one endpoint in the given vertex cover and gather the resulting stars.
theorem block_cost_of_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (cover : ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) :
    HasBlockCost G (G.edgeFinset.card + (T.card - 1)) := by
  classical
  let E := {e : Sym2 (Fin n) // e ∈ G.edgeFinset}
  have endsFor (e : Sym2 (Fin n)) (he : e ∈ G.edgeFinset) :
      ∃ a b : Fin n, a ∈ T ∧ G.Adj a b ∧ s(a,b) = e := by
    induction e using Sym2.ind with
    | h a b =>
      have adj := SimpleGraph.mem_edgeFinset.mp he
      rcases cover a b adj with ha | hb
      · exact ⟨a,b,ha,adj,rfl⟩
      · exact ⟨b,a,hb,adj.symm,Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)⟩
  have ends (e : E) : ∃ a b : Fin n, a ∈ T ∧ G.Adj a b ∧ s(a,b) = e.val :=
    endsFor e.val e.prop
  choose center leaf spec using ends
  let allEdges : Finset E := Finset.univ
  let centers := allEdges.image center
  let fiber := fun a => allEdges.filter (fun e => center e = a)
  let leaves := fun a => (fiber a).image leaf
  let star : Fin n ↪ Block n :=
    ⟨fun a => ({a}, leaves a), fun _ _ h => Finset.singleton_injective (congrArg Prod.fst h)⟩
  let F := centers.map star
  have centerMem (a : Fin n) (ha : a ∈ centers) : a ∈ T := by
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
    exact (spec e).1
  have leafMem (e : E) : leaf e ∈ leaves (center e) :=
    Finset.mem_image_of_mem leaf (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)
  have adj (a b : Fin n) (hb : b ∈ leaves a) : G.Adj a b := by
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
    have h : center e = a := (Finset.mem_filter.mp he).2
    exact h ▸ (spec e).2.1
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · intro B hB
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hB
    have ne : (leaves a).Nonempty := by
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨leaf e,leafMem e⟩
    change IsBlock G ({a},leaves a)
    refine ⟨Finset.disjoint_left.mpr ?_, by simp, ne, ?_⟩
    · intro b hb hl
      obtain rfl := Finset.mem_singleton.mp hb
      exact G.irrefl (adj _ _ hl)
    · intro b hb c hc
      obtain rfl := Finset.mem_singleton.mp hb
      exact adj _ _ hc
  · intro a b hab
    let e : E := ⟨s(a,b),SimpleGraph.mem_edgeFinset.mpr hab⟩
    refine ⟨star (center e), Finset.mem_map.mpr
      ⟨center e, Finset.mem_image_of_mem _ (Finset.mem_univ _), rfl⟩, ?_⟩
    have he : s(center e,leaf e) = s(a,b) := (spec e).2.2
    rcases Sym2.eq_iff.mp he with ⟨hc,hl⟩ | ⟨hc,hl⟩
    · exact Or.inl ⟨by change a ∈ ({center e} : Finset (Fin n)); simp [hc], hl ▸ leafMem e⟩
    · exact Or.inr ⟨by change b ∈ ({center e} : Finset (Fin n)); simp [hc], hl ▸ leafMem e⟩
  · have nF : F.card ≤ T.card := by
      rw [Finset.card_map]
      exact Finset.card_le_card centerMem
    have count :
        (∑ B ∈ F, blockCost B) = ∑ a ∈ centers, (leaves a).card := by
      rw [show F = centers.map star from rfl, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro a _
      change ({a} : Finset (Fin n)).card + (leaves a).card - 1 = (leaves a).card
      rw [Finset.card_singleton]
      omega
    have fibers :
        (∑ a ∈ centers, (fiber a).card) = G.edgeFinset.card := by
      have eq := (Finset.card_eq_sum_card_image center allEdges).symm
      change (∑ a ∈ centers, (fiber a).card) = allEdges.card at eq
      simpa only [allEdges, Finset.card_univ, E, Fintype.card_coe] using eq
    have sumBound : (∑ a ∈ centers, (leaves a).card) ≤ ∑ a ∈ centers, (fiber a).card :=
      Finset.sum_le_sum (fun a _ => Finset.card_image_le)
    unfold familyCost
    rw [count]
    omega

end Stars


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

private theorem pointNeLine {P L : ℕ} (p : Fin P) (l : Fin L) :
    Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro eq
  have val := congrArg Fin.val eq
  change p.val = P+l.val at val
  have := p.isLt
  omega

private def edgeEmbedding (P L : ℕ) : Fin P × Fin L ↪ Sym2 (Fin (P+L)) where
  toFun e := s(Fin.castAdd L e.1, Fin.natAdd P e.2)
  inj' := by
    rintro ⟨p,l⟩ ⟨q,m⟩ eq
    have h : s(Fin.castAdd L p,Fin.natAdd P l) = s(Fin.castAdd L q,Fin.natAdd P m) := eq
    rcases Sym2.eq_iff.mp h with ⟨a,b⟩ | ⟨a,_⟩
    · exact Prod.ext (Fin.ext (congrArg (fun w : Fin (P+L) => w.val) a)) (Fin.ext (Nat.add_left_cancel (congrArg (fun w : Fin (P+L) => w.val) b)))
    · exact (pointNeLine p m a).elim

-- Counting incidence pairs agrees with counting unordered edges of the bipartite graph.
theorem incidenceEdgeCard {P L : ℕ} (E : Finset (Fin P × Fin L))
    [DecidableRel (incidenceGraph (fun p l => (p,l) ∈ E)).Adj] :
    (incidenceGraph (fun p l => (p,l) ∈ E)).edgeFinset.card = E.card := by
  have mapped : E.map (edgeEmbedding P L) =
      (incidenceGraph (fun p l => (p,l) ∈ E)).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,incidenceAdj,Finset.mem_map]
      constructor
      · rintro ⟨⟨p,l⟩,h,eq⟩
        have asEdge : s(Fin.castAdd L p,Fin.natAdd P l) = s(a,b) := eq
        rcases Sym2.eq_iff.mp asEdge with ⟨ep,el⟩ | ⟨ep,el⟩
        · exact Or.inl ⟨p,l,ep.symm,el.symm,h⟩
        · exact Or.inr ⟨p,l,ep.symm,el.symm,h⟩
      · rintro (⟨p,l,rfl,rfl,h⟩ | ⟨p,l,rfl,rfl,h⟩)
        · exact ⟨(p,l),h,rfl⟩
        · exact ⟨(p,l),h,Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)⟩
  rw [← mapped,Finset.card_map]


end PEqualNP.Outside.L_meta_2874

open PEqualNP.Outside.L_meta_2874 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm in
theorem PEqualNP.Outside.L_meta_2874 :
  ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  classical
  intro P L E U V cover
  let I : Fin P → Fin L → Prop := fun p l => (p,l) ∈ E
  let T : Finset (Fin (P+L)) := U.image (Fin.castAdd L) ∪ V.image (Fin.natAdd P)
  have covers : ∀ a b, (incidenceGraph I).Adj a b → a ∈ T ∨ b ∈ T := by
    intro a b adj
    rcases (incidenceAdj I _ _).mp adj with ⟨p,l,rfl,rfl,h⟩ | ⟨p,l,rfl,rfl,h⟩
    · rcases cover (p,l) h with hp | hl
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hl))
    · rcases cover (p,l) h with hp | hl
      · exact Or.inr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
      · exact Or.inl (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hl))
  have tCard : T.card ≤ U.card + V.card := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  have edgeCard : (incidenceGraph I).edgeFinset.card = E.card := incidenceEdgeCard E
  have cost : HasBlockCost (incidenceGraph I) (E.card + U.card + V.card - 1) := by
    have h := Stars.block_cost_of_cover (incidenceGraph I) T covers
    obtain ⟨blocks, valid, budget⟩ := h
    have coverNonempty : E.Nonempty → 0 < U.card + V.card := by
      rintro ⟨⟨p,l⟩,edge⟩
      rcases cover (p,l) edge with hp | hl
      · have h : 0 < U.card := Finset.card_pos.mpr ⟨p,hp⟩
        omega
      · have h : 0 < V.card := Finset.card_pos.mpr ⟨l,hl⟩
        omega
    have sizes : (incidenceGraph I).edgeFinset.card + (T.card - 1) ≤
        E.card + U.card + V.card - 1 := by
      by_cases h : E.Nonempty
      · have := coverNonempty h
        omega
      · rw [Finset.not_nonempty_iff_eq_empty] at h
        have : E.card = 0 := Finset.card_eq_zero.mpr h
        omega
    exact ⟨blocks, valid, budget.trans sizes⟩
  obtain ⟨D,S,T,model,correct,budget,pointPure,linePure,cross⟩ :=
    compile P L I (E.card + U.card + V.card - 1) cost
  let color : Bool → Finset ℕ := fun b => if b then T else S
  refine ⟨D, color, model, budget, correct, ?_, ?_⟩
  · intro b w hw
    cases b
    · change w ∈ S at hw
      rcases pointPure w hw with raw | ⟨j,hj,hw,isOr,inputs⟩
      · exact Or.inl ⟨by omega, decide_eq_false (by omega)⟩
      · exact Or.inr ⟨j,hj,hw,isOr,inputs⟩
    · change w ∈ T at hw
      rcases linePure w hw with raw | ⟨j,hj,hw,isOr,inputs⟩
      · exact Or.inl ⟨raw.2, decide_eq_true raw.1⟩
      · exact Or.inr ⟨j,hj,hw,isOr,inputs⟩
  · intro i hi isAnd
    obtain ⟨a,b,pins,ab | ba⟩ := cross i hi isAnd
    · exact ⟨a,b,false,pins,ab.1,ab.2⟩
    · exact ⟨a,b,true,pins,ba.1,ba.2⟩
