import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4708

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_len (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma wires_getD_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    (C.wires (List.ofFn x)).getD u.val false = x u := by
  rw [wires_eq_foldl, foldl_stepWire_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma wire_gate (C : Circuit) (L : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (C.gates[j]'hj).inputs, i < L.length + j) :
    (C.wires L).getD (L.length + j) false =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => (C.wires L).getD i false) := by
  obtain ⟨pre, post, gj, hgs, hlen, hget⟩ := split_gates C.gates j hj
  have hw : C.wires L = post.foldl stepWire (stepWire (pre.foldl stepWire L) gj) := by
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl stepWire L).length = L.length + j := by
    rw [foldl_stepWire_length, hlen]
  have key : ∀ i, i < L.length + j + 1 →
      (C.wires L).getD i false = (stepWire (pre.foldl stepWire L) gj).getD i false := by
    intro i hi
    rw [hw, foldl_stepWire_getD_lt]
    simp [stepWire, hl0]
    omega
  rw [hget] at hrb ⊢
  rw [key _ (by omega)]
  rw [show L.length + j = (pre.foldl stepWire L).length from hl0.symm, stepWire_getD_len]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h1 := hrb i hi
  rw [key _ (by omega), stepWire_getD_lt _ _ _ (by rw [hl0]; exact h1)]

lemma reach (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hrb : ReadsBack n C) :
    ∀ w, w < n + C.size → ∃ S I : Finset ℕ,
      (∀ k ∈ S, k < C.size ∧ (gateAt C k).op = GateOp.and) ∧ (∀ i ∈ I, i < n) ∧
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true ↔
        (∃ k ∈ S, gateVal n C k x = true) ∨
          (∃ i ∈ I, (C.wires (List.ofFn x)).getD i false = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases hwn : w < n
  · refine ⟨∅, {w}, by simp, by simpa using hwn, ?_⟩
    intro x
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by
      unfold Circuit.size at hw
      omega
    have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
    have hga : gateAt C j = C.gates[j] := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj]
    rcases hm _ hmem with ⟨hop, -⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop
    · refine ⟨{j}, ∅, ?_, by simp, ?_⟩
      · intro k hk
        simp only [Finset.mem_singleton] at hk
        subst hk
        exact ⟨hj, by rw [hga, hop]⟩
      · intro x
        simp [gateVal]
    · have hin : ∀ i ∈ (C.gates[j]).inputs, i < n + j := by
        intro i hi
        exact hrb j hj i (by rw [hga]; exact hi)
      have ih' : ∀ i, ∃ S I : Finset ℕ, i ∈ (C.gates[j]).inputs →
          ((∀ k ∈ S, k < C.size ∧ (gateAt C k).op = GateOp.and) ∧ (∀ i ∈ I, i < n) ∧
            ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false = true ↔
              (∃ k ∈ S, gateVal n C k x = true) ∨
                (∃ i' ∈ I, (C.wires (List.ofFn x)).getD i' false = true)) := by
        intro i
        by_cases h : i ∈ (C.gates[j]).inputs
        · obtain ⟨S, I, h1, h2, h3⟩ := ih i (hin i h) (by have := hin i h; omega)
          exact ⟨S, I, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨∅, ∅, fun h' => absurd h' h⟩
      choose Sf If hSI using ih'
      refine ⟨(C.gates[j]).inputs.toFinset.biUnion Sf,
        (C.gates[j]).inputs.toFinset.biUnion If, ?_, ?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_biUnion, List.mem_toFinset] at hk
        obtain ⟨i, hi, hk⟩ := hk
        exact (hSI i hi).1 k hk
      · intro k hk
        simp only [Finset.mem_biUnion, List.mem_toFinset] at hk
        obtain ⟨i, hi, hk⟩ := hk
        exact (hSI i hi).2.1 k hk
      · intro x
        have hlen : (List.ofFn x).length = n := List.length_ofFn
        have hwg := wire_gate C (List.ofFn x) j hj (by rw [hlen]; exact hin)
        rw [hlen] at hwg
        rw [hwg, hop]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id,
          Finset.mem_biUnion, List.mem_toFinset]
        constructor
        · rintro ⟨i, hi, hv⟩
          rcases ((hSI i hi).2.2 x).1 hv with ⟨k, hk, h⟩ | ⟨i', hi', h⟩
          · exact Or.inl ⟨k, ⟨i, hi, hk⟩, h⟩
          · exact Or.inr ⟨i', ⟨i, hi, hi'⟩, h⟩
        · rintro (⟨k, ⟨i, hi, hk⟩, h⟩ | ⟨i', ⟨i, hi, hi'⟩, h⟩)
          · exact ⟨i, hi, ((hSI i hi).2.2 x).2 (Or.inl ⟨k, hk, h⟩)⟩
          · exact ⟨i, hi, ((hSI i hi).2.2 x).2 (Or.inr ⟨i', hi', h⟩)⟩

end PEqualNP.Outside.L_meta_4708

theorem PEqualNP.Outside.L_meta_4708 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → (∀ (x6 : Fin x1), (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x6)) = Bool.false) → ∃ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x2.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x8 = Bool.true ↔ ∃ x9 ∈ x7, PEqualNP.EdgeOwnership.gateVal x1 x2 x9 x8 = Bool.true := by
  intro n C hm hrb hout hsing
  obtain ⟨S, I, hS, hI, hval⟩ := PEqualNP.Outside.L_meta_4708.reach n C hm hrb C.output hout
  have hIe : ∀ i ∈ I, False := by
    intro i hi
    have hin := hI i hi
    have h1 := hsing ⟨i, hin⟩
    have h2 : PEqualNP.MetaComplexity.circuitFun n C
        (fun x7 : Fin n => decide (x7 = ⟨i, hin⟩)) = true := by
      show (C.wires (List.ofFn _)).getD C.output false = true
      rw [hval]
      right
      refine ⟨i, hi, ?_⟩
      rw [PEqualNP.Outside.L_meta_4708.wires_getD_input n C _ ⟨i, hin⟩]
      simp
    rw [h1] at h2
    exact Bool.false_ne_true h2
  refine ⟨S, hS, fun x => ?_⟩
  show (C.wires (List.ofFn x)).getD C.output false = true ↔ _
  rw [hval]
  constructor
  · rintro (h | ⟨i, hi, -⟩)
    · exact h
    · exact (hIe i hi).elim
  · intro h
    exact Or.inl h
