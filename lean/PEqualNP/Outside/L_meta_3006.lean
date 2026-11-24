import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3006
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

end PEqualNP.Outside.L_meta_3006

open PEqualNP.Outside.L_meta_3006 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3006 : ∀ (x1 x2 : List ℕ) (x3 : ℕ), (∀ (x4 : Fin x2.length), ∃ x5 ∈ x1 ++ List.take (↑x4) x2, ∃ x6 ∈ x1 ++ List.take (↑x4) x2, x2.get x4 = x5 &&& x6 ∨ x2.get x4 = x5 ||| x6) → x3 ∈ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x2.length ∧ ∀ (x7 : ℕ), x6.eval (List.map (fun (x8 : ℕ) => x8.testBit x7) x1) = x3.testBit x7 := by
  intro x1 x2 x3 h hx3
  choose a ha b hb hab using h
  let gate : Fin x2.length → Gate := fun k =>
    ⟨if x2.get k = a k &&& b k then GateOp.and else GateOp.or,
      [List.idxOf (a k) (x1 ++ List.take (↑k) x2), List.idxOf (b k) (x1 ++ List.take (↑k) x2)]⟩
  have hglen : (List.ofFn gate).length = x2.length := List.length_ofFn
  have gd : ∀ (i : ℕ) (L : List ℕ) (v : ℕ), v ∈ L →
      (L.map (fun x8 : ℕ => x8.testBit i)).getD (L.idxOf v) false = v.testBit i := by
    intro i L v hv
    have hlt : L.idxOf v < L.length := List.idxOf_lt_length_of_mem hv
    rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_idxOf hlt]
  refine ⟨⟨List.ofFn gate, x1.length + List.idxOf x3 x2⟩, ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_ofFn] at hg
    obtain ⟨k, rfl⟩ := hg
    refine ⟨?_, by simp [gate]⟩
    show (if x2.get k = a k &&& b k then GateOp.and else GateOp.or) ∈ ({GateOp.and, GateOp.or} : Set GateOp)
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · show (List.ofFn gate).length ≤ x2.length
    rw [hglen]
  · intro i
    have claim : ∀ k, k ≤ x2.length →
        wf ((List.ofFn gate).take k) (x1.map (fun x8 : ℕ => x8.testBit i))
          = (x1 ++ x2.take k).map (fun x8 : ℕ => x8.testBit i) := by
      intro k
      induction k with
      | zero => intro _; simp [wf]
      | succ k ih =>
        intro hk
        have hk' : k < x2.length := by omega
        have hkg : k < (List.ofFn gate).length := by rw [hglen]; exact hk'
        have hget : x2.get ⟨k, hk'⟩ = x2[k] := rfl
        have hv : (gate ⟨k, hk'⟩).op.eval ((gate ⟨k, hk'⟩).inputs.map fun j =>
            ((x1 ++ List.take k x2).map (fun x8 : ℕ => x8.testBit i)).getD j false) = x2[k].testBit i := by
          show GateOp.eval (if x2.get ⟨k, hk'⟩ = a ⟨k, hk'⟩ &&& b ⟨k, hk'⟩ then GateOp.and else GateOp.or)
            ([List.idxOf (a ⟨k, hk'⟩) (x1 ++ List.take k x2), List.idxOf (b ⟨k, hk'⟩) (x1 ++ List.take k x2)].map
              fun j => ((x1 ++ List.take k x2).map (fun x8 : ℕ => x8.testBit i)).getD j false) = _
          simp only [List.map_cons, List.map_nil]
          rw [gd i _ _ (ha ⟨k, hk'⟩), gd i _ _ (hb ⟨k, hk'⟩)]
          by_cases hc : x2.get ⟨k, hk'⟩ = a ⟨k, hk'⟩ &&& b ⟨k, hk'⟩
          · rw [if_pos hc, ← hget, hc, Nat.testBit_and]
            simp [GateOp.eval]
          · rw [if_neg hc]
            have ho : x2.get ⟨k, hk'⟩ = a ⟨k, hk'⟩ ||| b ⟨k, hk'⟩ := (hab ⟨k, hk'⟩).resolve_left hc
            rw [← hget, ho, Nat.testBit_or]
            simp [GateOp.eval]
        rw [List.take_succ_eq_append_getElem hkg, wf_snoc, ih (by omega), List.getElem_ofFn, hv,
          List.take_succ_eq_append_getElem hk']
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    have hall := claim x2.length (le_refl _)
    rw [List.take_of_length_le (by rw [hglen]), List.take_of_length_le (le_refl _)] at hall
    show (wf (List.ofFn gate) (x1.map (fun x8 : ℕ => x8.testBit i))).getD (x1.length + List.idxOf x3 x2) false = _
    rw [hall, List.map_append, List.getD_append_right _ _ _ _ (by simp)]
    have e : x1.length + List.idxOf x3 x2 - (x1.map (fun x8 : ℕ => x8.testBit i)).length = List.idxOf x3 x2 := by
      simp
    rw [e]
    exact gd i x2 x3 hx3
