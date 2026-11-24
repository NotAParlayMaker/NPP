import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_3245

def gateIn (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

def Wired (B : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ((gateIn gs j).op = GateOp.and ∨ (gateIn gs j).op = GateOp.or) ∧
    (gateIn gs j).inputs.length = 2 ∧ ∀ i ∈ (gateIn gs j).inputs, i < B + j

def Pure (B : ℕ) (gs : List Gate) (side : ℕ → Prop) (wires : Finset ℕ) : Prop :=
  ∀ w ∈ wires, side w ∨ ∃ j < gs.length,
    w = B + j ∧ (gateIn gs j).op = GateOp.or ∧
      ∀ i ∈ (gateIn gs j).inputs, i ∈ wires

def Crossed (gs : List Gate) (P L : Finset ℕ) : Prop :=
  ∀ j < gs.length, (gateIn gs j).op = GateOp.and →
    ∃ u v, (gateIn gs j).inputs = [u, v] ∧
      ((u ∈ P ∧ v ∈ L) ∨ (u ∈ L ∧ v ∈ P))

def Layout (B : ℕ) (gs : List Gate) (point line : ℕ → Prop) : Prop :=
  ∃ P L, Wired B gs ∧ Pure B gs point P ∧ Pure B gs line L ∧ Crossed gs P L

theorem atBefore (gs hs : List Gate) {j : ℕ} (hj : j < gs.length) :
    gateIn (gs ++ hs) j = gateIn gs j :=
  List.getD_append _ _ _ _ hj

theorem atAfter (gs hs : List Gate) {j : ℕ} (hj : gs.length ≤ j) :
    gateIn (gs ++ hs) j = gateIn hs (j - gs.length) :=
  List.getD_append_right _ _ _ _ hj

theorem pureAppend (B : ℕ) (gs hs : List Gate) (side : ℕ → Prop) (U V : Finset ℕ)
    (first : Pure B gs side U) (last : Pure (B + gs.length) hs side V) :
    Pure B (gs ++ hs) side (U ∪ V) := by
  intro w hw
  rcases Finset.mem_union.mp hw with hu | hv
  · rcases first w hu with h | ⟨j, hj, he, hop, hargs⟩
    · exact Or.inl h
    · refine Or.inr ⟨j, by simp; omega, he, ?_, ?_⟩
      · rwa [atBefore gs hs hj]
      · rw [atBefore gs hs hj]
        exact fun i hi => Finset.mem_union.mpr (Or.inl (hargs i hi))
  · rcases last w hv with h | ⟨j, hj, he, hop, hargs⟩
    · exact Or.inl h
    · have ge : gs.length ≤ gs.length + j := by omega
      have atJ : gateIn (gs ++ hs) (gs.length + j) = gateIn hs j := by
        rw [atAfter gs hs ge, show gs.length + j - gs.length = j by omega]
      refine Or.inr ⟨gs.length + j, by simp; omega, by omega, ?_, ?_⟩
      · rwa [atJ]
      · rw [atJ]
        exact fun i hi => Finset.mem_union.mpr (Or.inr (hargs i hi))

theorem layoutAppend (B : ℕ) (gs hs : List Gate) (point line : ℕ → Prop)
    (first : Layout B gs point line) (last : Layout (B + gs.length) hs point line) :
    Layout B (gs ++ hs) point line := by
  obtain ⟨P, L, fw, fp, fl, fc⟩ := first
  obtain ⟨Q, M, lw, lp, ll, lc⟩ := last
  refine ⟨P ∪ Q, L ∪ M, ?_, pureAppend B gs hs point _ _ fp lp,
    pureAppend B gs hs line _ _ fl ll, ?_⟩
  · intro j hj
    by_cases before : j < gs.length
    · rw [atBefore gs hs before]
      exact fw j before
    · have jh : j - gs.length < hs.length := by simp at hj; omega
      rw [atAfter gs hs (by omega : gs.length ≤ j)]
      obtain ⟨hop, ha, hread⟩ := lw (j - gs.length) jh
      exact ⟨hop, ha, fun i hi => by have := hread i hi; omega⟩
  · intro j hj hop
    by_cases before : j < gs.length
    · rw [atBefore gs hs before] at hop ⊢
      obtain ⟨u, v, he, h | h⟩ := fc j before hop
      · exact ⟨u, v, he, Or.inl ⟨Finset.mem_union.mpr (Or.inl h.1),
          Finset.mem_union.mpr (Or.inl h.2)⟩⟩
      · exact ⟨u, v, he, Or.inr ⟨Finset.mem_union.mpr (Or.inl h.1),
          Finset.mem_union.mpr (Or.inl h.2)⟩⟩
    · have jh : j - gs.length < hs.length := by simp at hj; omega
      rw [atAfter gs hs (by omega : gs.length ≤ j)] at hop ⊢
      obtain ⟨u, v, he, h | h⟩ := lc (j - gs.length) jh hop
      · exact ⟨u, v, he, Or.inl ⟨Finset.mem_union.mpr (Or.inr h.1),
          Finset.mem_union.mpr (Or.inr h.2)⟩⟩
      · exact ⟨u, v, he, Or.inr ⟨Finset.mem_union.mpr (Or.inr h.1),
          Finset.mem_union.mpr (Or.inr h.2)⟩⟩

theorem swapLayout (B : ℕ) (gs : List Gate) (point line : ℕ → Prop)
    (h : Layout B gs point line) : Layout B gs line point := by
  obtain ⟨P, L, hw, hp, hl, hc⟩ := h
  refine ⟨L, P, hw, hl, hp, ?_⟩
  intro i hi hop
  obtain ⟨u, v, he, h⟩ := hc i hi hop
  exact ⟨u, v, he, h.elim Or.inr Or.inl⟩

def accumulator (B v m i : ℕ) : ℕ :=
  (v :: (List.range m).map (fun j => B + j)).getD i 0

theorem accumulatorZero (B v m : ℕ) : accumulator B v m 0 = v := rfl

theorem accumulatorSucc (B v m k : ℕ) (hk : k < m) :
    accumulator B v m (k + 1) = B + k := by
  change ((List.range m).map (fun j => B + j)).getD k 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem accumulatorEarlier {B v m i : ℕ} (hv : v < B) (hi : i ≤ m) :
    accumulator B v m i < B + i := by
  cases i with
  | zero => simpa [accumulatorZero] using hv
  | succ k =>
    rw [accumulatorSucc B v m k (by omega)]
    omega

def chainWires (B m : ℕ) : Finset ℕ :=
  (Finset.range m).image (fun j => B + j)

theorem memChain {B m w : ℕ} :
    w ∈ chainWires B m ↔ ∃ j < m, w = B + j := by
  simp only [chainWires, Finset.mem_image, Finset.mem_range]
  exact exists_congr (fun _ => and_congr_right (fun _ => eq_comm))

theorem accumulatorIn (B v m i : ℕ) (V : Finset ℕ) (hv : v ∈ V) (hi : i ≤ m) :
    accumulator B v m i ∈ V ∪ chainWires B m := by
  cases i with
  | zero => exact Finset.mem_union.mpr (Or.inl hv)
  | succ k =>
    have hk : k < m := by omega
    rw [accumulatorSucc B v m k hk]
    exact Finset.mem_union.mpr (Or.inr (memChain.mpr ⟨k, hk, rfl⟩))

theorem blockLength (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

theorem blockOr (B a t v : ℕ) (rest : List ℕ) (lead : Bool) (i : ℕ)
    (hi : i < rest.length) :
    gateIn (blockGates B a t v rest lead) i =
      ⟨GateOp.or, [accumulator B v rest.length i, rest.getD i 0]⟩ := by
  unfold gateIn blockGates
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [accumulator]

theorem blockAnd (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    gateIn (blockGates B a t v rest lead) rest.length =
      ⟨GateOp.and, [t, accumulator B v rest.length rest.length]⟩ := by
  unfold gateIn blockGates
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [accumulator]

theorem blockMerge (B a t v : ℕ) (rest : List ℕ) :
    gateIn (blockGates B a t v rest false) (rest.length + 1) =
      ⟨GateOp.or, [a, B + rest.length]⟩ := by
  unfold gateIn blockGates
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem blockLayout (B a t v n : ℕ) (rest : List ℕ) (lead : Bool)
    (owner neighbor : ℕ → Prop) (base : n ≤ B)
    (ownerBound : t < n) (neighborBound : ∀ i ∈ v :: rest, i < n)
    (earlier : lead = false → a < B)
    (ownerOK : owner t) (neighborOK : ∀ i ∈ v :: rest, neighbor i) :
    Layout B (blockGates B a t v rest lead) owner neighbor := by
  let U : Finset ℕ := {t}
  let V : Finset ℕ := (v :: rest).toFinset
  let gs := blockGates B a t v rest lead
  have vin : v ∈ V := by simp [V]
  have ownerIn : t ∈ U := by simp [U]
  have beforeV : v < B := lt_of_lt_of_le (neighborBound v (by simp)) base
  have getIn (i : ℕ) (hi : i < rest.length) : rest.getD i 0 ∈ rest := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have rhsBefore (i : ℕ) (hi : i < rest.length) : rest.getD i 0 < B + i := by
    have := neighborBound (rest.getD i 0) (List.mem_cons_of_mem _ (getIn i hi))
    omega
  have blockCases (j : ℕ) (hj : j < gs.length) :
      j < rest.length ∨ j = rest.length ∨ (j = rest.length + 1 ∧ lead = false) := by
    change j < (blockGates B a t v rest lead).length at hj
    rw [blockLength] at hj
    cases lead <;> simp at hj ⊢ <;> omega
  refine ⟨U, V ∪ chainWires B rest.length, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases blockCases j hj with hi | rfl | ⟨rfl, rfl⟩
    · rw [blockOr B a t v rest lead j hi]
      refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hin
      rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hin :
        i = accumulator B v rest.length j ∨ i = rest.getD j 0) with rfl | rfl
      · exact accumulatorEarlier beforeV (by omega)
      · exact rhsBefore j hi
    · rw [blockAnd]
      refine ⟨Or.inl rfl, rfl, ?_⟩
      intro i hin
      rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hin :
        i = t ∨ i = accumulator B v rest.length rest.length) with rfl | rfl
      · omega
      · exact accumulatorEarlier beforeV (by omega)
    · rw [blockMerge]
      refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hin
      rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hin :
        i = a ∨ i = B + rest.length) with rfl | rfl
      · have := earlier rfl
        omega
      · omega
  · intro w hw
    have eq : w = t := Finset.mem_singleton.mp hw
    exact Or.inl (eq.symm ▸ ownerOK)
  · intro w hw
    rcases Finset.mem_union.mp hw with hV | hchain
    · exact Or.inl (neighborOK _ (List.mem_toFinset.mp hV))
    · obtain ⟨j, hj, he⟩ := memChain.mp hchain
      have hj' : j < gs.length := by
        change j < (blockGates B a t v rest lead).length
        rw [blockLength]
        omega
      refine Or.inr ⟨j, hj', he, ?_, ?_⟩
      · show (gateIn (blockGates B a t v rest lead) j).op = GateOp.or
        rw [blockOr B a t v rest lead j hj]
      · show ∀ i ∈ (gateIn (blockGates B a t v rest lead) j).inputs,
          i ∈ V ∪ chainWires B rest.length
        rw [blockOr B a t v rest lead j hj]
        intro i hi
        rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hi :
          i = accumulator B v rest.length j ∨ i = rest.getD j 0) with rfl | rfl
        · exact accumulatorIn _ _ _ _ _ vin (by omega)
        · exact Finset.mem_union.mpr (Or.inl
            (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (getIn j hj))))
  · intro j hj hop
    rcases blockCases j hj with hi | rfl | ⟨rfl, rfl⟩
    · change (gateIn (blockGates B a t v rest lead) j).op = GateOp.and at hop
      rw [blockOr B a t v rest lead j hi] at hop
      cases hop
    · have hEq : (gateIn gs rest.length).inputs =
          [t, accumulator B v rest.length rest.length] := by
        change (gateIn (blockGates B a t v rest lead) rest.length).inputs = _
        rw [blockAnd]
      exact ⟨t, accumulator B v rest.length rest.length, hEq,
        Or.inl ⟨ownerIn, accumulatorIn _ _ _ _ _ vin (by omega)⟩⟩
    · change (gateIn (blockGates B a t v rest false) (rest.length + 1)).op = GateOp.and at hop
      rw [blockMerge] at hop
      cases hop

theorem coverLayout (Np Nl : ℕ) (own : List (ℕ × List ℕ))
    (tagged : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ w ∈ tx.2, Np ≤ w ∧ w < Np + Nl) ∨
        Np ≤ tx.1 ∧ tx.1 < Np + Nl ∧ ∀ w ∈ tx.2, w < Np))
    (B a : ℕ) (lead : Bool) (base : Np + Nl ≤ B)
    (earlier : lead = false → a < B) :
    Layout B (coverGatesB B lead a own) (fun w => w < Np)
      (fun w => Np ≤ w ∧ w < Np + Nl) := by
  induction own generalizing B a lead with
  | nil =>
    change Layout B [] _ _
    exact ⟨∅, ∅, by intro j hj; simp at hj,
      by simp [Pure], by simp [Pure], by intro j hj; simp at hj⟩
  | cons tx own ih =>
    rcases tx with ⟨t, ns⟩
    have now := tagged (t, ns) (by simp)
    have restValid : ∀ tx ∈ own, tx.2 ≠ [] ∧
        ((tx.1 < Np ∧ ∀ w ∈ tx.2, Np ≤ w ∧ w < Np + Nl) ∨
          Np ≤ tx.1 ∧ tx.1 < Np + Nl ∧ ∀ w ∈ tx.2, w < Np) :=
      fun tx h => tagged tx (by simp [h])
    cases ns with
    | nil => exact (now.1 rfl).elim
    | cons v rest =>
      let gs := blockGates B a t v rest lead
      have head : Layout B gs (fun w => w < Np) (fun w => Np ≤ w ∧ w < Np + Nl) := by
        rcases now.2 with ⟨hp, hN⟩ | ⟨hleft, hright, hN⟩
        · exact blockLayout B a t v (Np + Nl) rest lead _ _ base (by omega)
            (fun i hi => (hN i hi).2) earlier hp hN
        · apply swapLayout B gs
          exact blockLayout B a t v (Np + Nl) rest lead _ _ base hright
            (fun i hi => by have := hN i hi; omega) earlier ⟨hleft, hright⟩ hN
      have nonzero : 0 < gs.length := by
        change 0 < (blockGates B a t v rest lead).length
        rw [blockLength]
        omega
      have tail := ih restValid (B + gs.length) (B + gs.length - 1) false (by omega)
        (fun _ => by omega)
      change Layout B (gs ++ coverGatesB (B + gs.length) false (B + gs.length - 1) own) _ _
      exact layoutAppend B gs _ _ _ head tail

end PEqualNP.Outside.L_meta_3245

open PEqualNP.Outside.L_meta_3245 in
theorem PEqualNP.Outside.L_meta_3245 :
    ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro Np Nl own
  dsimp only
  intro valid
  let n := Np + Nl
  let C := coverCircuitB n own
  have hGates : C.gates = coverGatesB n true 0 own := by
    unfold C coverCircuitB
    split
    · rename_i h
      change [] = _
      exact h.symm
    · rfl
  have hLayout : Layout n C.gates (fun w => w < Np) (fun w => Np ≤ w ∧ w < n) := by
    rw [hGates]
    exact coverLayout Np Nl own valid n 0 true (le_refl _) (by simp)
  obtain ⟨P, L, wf, pureP, pureL, cross⟩ := hLayout
  have atMem (g : Gate) (hg : g ∈ C.gates) :
      ∃ j < C.gates.length, gateIn C.gates j = g := by
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hg
    refine ⟨j, hj, ?_⟩
    change C.gates.getD j ⟨GateOp.or, []⟩ = g
    rw [List.getD_eq_getElem _ _ hj]
    exact he
  refine ⟨P, L, ?_, pureP, pureL, cross⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, he⟩ := atMem g hg
    rw [← he]
    exact (wf j hj).1
  · intro j hj i hi
    exact (wf j hj).2.2 i hi
  · intro g hg
    obtain ⟨j, hj, he⟩ := atMem g hg
    rw [← he]
    exact (wf j hj).2.1
