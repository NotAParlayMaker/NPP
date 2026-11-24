import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3081

open PEqualNP.CircuitLowerBounds

def val (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def stp (w : List Bool) (g : Gate) : List Bool := w ++ [val g w]

lemma getD_one (l : List Bool) (a : Bool) (k : ℕ) :
    (l ++ [a]).getD k false
      = if k < l.length then l.getD k false else if k = l.length then a else false := by
  by_cases h : k < l.length
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega)]
    by_cases h2 : k = l.length
    · subst h2
      simp
    · rw [if_neg h2]
      exact List.getD_eq_default _ _ (by simp only [List.length_singleton]; omega)

lemma pre (gs : List Gate) :
    ∀ (w : List Bool) (k : ℕ), k < w.length → (gs.foldl stp w).getD k false = w.getD k false := by
  induction gs with
  | nil =>
    intro w k _
    rfl
  | cons g gs ih =>
    intro w k hk
    show (gs.foldl stp (w ++ [val g w])).getD k false = w.getD k false
    rw [ih (w ++ [val g w]) k (by simp only [List.length_append, List.length_singleton]; omega),
      getD_one, if_pos hk]

abbrev Reads (g : Gate) (v : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = Option.some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs

lemma val_agree (g : Gate) (v : ℕ) (w w' : List Bool) (hg : ¬ Reads g v)
    (h : ∀ k, k ≠ v → w.getD k false = w'.getD k false) : val g w = val g w' := by
  rcases g with ⟨op, ins⟩
  by_cases hop : op = GateOp.not
  · subst hop
    rcases ins with _ | ⟨a, t⟩
    · rfl
    · have ha : a ≠ v := fun e => hg (Or.inl ⟨rfl, by subst e; rfl⟩)
      show (!(w.getD a false)) = (!(w'.getD a false))
      rw [h a ha]
  · have hv : v ∉ ins := fun hm => hg (Or.inr ⟨hop, hm⟩)
    show op.eval (ins.map fun i => w.getD i false) = op.eval (ins.map fun i => w'.getD i false)
    congr 1
    apply List.map_congr_left
    intro a ha
    exact h a (fun e => hv (e ▸ ha))

lemma agree (v : ℕ) (gs : List Gate) : (∀ g ∈ gs, ¬ Reads g v) →
    ∀ (w w' : List Bool), w.length = w'.length → v < w.length →
      (∀ k, k ≠ v → w.getD k false = w'.getD k false) →
      ∀ k, k ≠ v → (gs.foldl stp w).getD k false = (gs.foldl stp w').getD k false := by
  induction gs with
  | nil =>
    intro _ w w' _ _ h k hk
    exact h k hk
  | cons g gs ih =>
    intro hno w w' hl hvl h k hk
    have hval : val g w = val g w' := val_agree g v w w' (hno g (by simp)) h
    show (gs.foldl stp (w ++ [val g w])).getD k false
      = (gs.foldl stp (w' ++ [val g w'])).getD k false
    refine ih (fun g' hg' => hno g' (by simp [hg'])) (w ++ [val g w]) (w' ++ [val g w'])
      (by simp only [List.length_append, List.length_singleton, hl])
      (by simp only [List.length_append, List.length_singleton]; omega) ?_ k hk
    intro j hj
    rw [getD_one, getD_one, ← hl, hval]
    split_ifs <;> first | exact h j hj | rfl

lemma getD_ofFn (x : Fin 9 → Bool) (k : ℕ) (hk : k < 9) :
    (List.ofFn x).getD k false = x ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn]

lemma core (C : Circuit) (f : (Fin 9 → Bool) → Bool)
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (hf : PEqualNP.MetaComplexity.circuitFun 9 C = f) (v : ℕ) (hv : v < 9)
    (a b : Fin 9 → Bool) (hab : ∀ k : Fin 9, (k : ℕ) ≠ v → a k = b k)
    (h02 : (a 0 || a 2) = (b 0 || b 2)) (hfab : f a ≠ f b)
    (c : Fin 9 → Bool) (hc : f c ≠ (List.ofFn c).getD v false) :
    ∃ g ∈ List.drop 1 C.gates, Reads g v := by
  by_contra hno
  have hno' : ∀ g ∈ List.drop 1 C.gates, ¬ Reads g v := fun g hg hr => hno ⟨g, hg, hr⟩
  have hwires : ∀ x : List Bool, C.wires x = C.gates.foldl stp x := fun x => rfl
  rcases hgs : C.gates with _ | ⟨g0, rest⟩
  · have h := h9 (fun _ => true)
    rw [hwires, hgs, List.foldl_nil, List.getD_eq_default _ _ (by rw [List.length_ofFn])] at h
    simp at h
  · rw [hgs] at hno'
    have hno2 : ∀ g ∈ rest, ¬ Reads g v := fun g hg => hno' g (by simpa using hg)
    have hw : ∀ x : Fin 9 → Bool, C.wires (List.ofFn x)
        = rest.foldl stp (List.ofFn x ++ [val g0 (List.ofFn x)]) := fun x => by
      rw [hwires, hgs]
      rfl
    have hlt : ∀ (x : Fin 9 → Bool) (k : ℕ), k < 10 →
        k < (List.ofFn x ++ [val g0 (List.ofFn x)]).length := fun x k hk => by
      simp only [List.length_append, List.length_singleton, List.length_ofFn]
      omega
    have hg0 : ∀ x : Fin 9 → Bool, val g0 (List.ofFn x) = (x 0 || x 2) := fun x => by
      have h := h9 x
      rw [hw, pre rest _ 9 (hlt x 9 (by omega)), getD_one, List.length_ofFn] at h
      simpa using h
    have hinit : ∀ k, k ≠ v → (List.ofFn a ++ [val g0 (List.ofFn a)]).getD k false
        = (List.ofFn b ++ [val g0 (List.ofFn b)]).getD k false := by
      intro k hk
      rw [getD_one, getD_one, List.length_ofFn, List.length_ofFn, hg0 a, hg0 b, h02]
      split_ifs with h1 h2
      · rw [getD_ofFn a k h1, getD_ofFn b k h1]
        exact hab ⟨k, h1⟩ hk
      · rfl
      · rfl
    have key := agree v rest hno2 (List.ofFn a ++ [val g0 (List.ofFn a)])
      (List.ofFn b ++ [val g0 (List.ofFn b)])
      (by simp only [List.length_append, List.length_singleton, List.length_ofFn])
      (hlt a v (by omega)) hinit
    by_cases ho : C.output = v
    · apply hc
      rw [← hf]
      show (C.wires (List.ofFn c)).getD C.output false = _
      have hvc : v < (List.ofFn c).length := by
        rw [List.length_ofFn]
        exact hv
      rw [ho, hw, pre rest _ v (hlt c v (by omega)), getD_one, if_pos hvc]
    · apply hfab
      rw [← hf]
      show (C.wires (List.ofFn a)).getD C.output false = (C.wires (List.ofFn b)).getD C.output false
      rw [hw, hw]
      exact key C.output ho

end PEqualNP.Outside.L_meta_3081

theorem PEqualNP.Outside.L_meta_3081 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 := by
  show ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), _ → _ → ∀ (x5 : ℕ), _ →
    ∃ x7 ∈ List.drop 1 x2.gates, PEqualNP.Outside.L_meta_3081.Reads x7 x5
  intro C h9 hf x5 hx5
  rcases hx5 with rfl | rfl
  · exact PEqualNP.Outside.L_meta_3081.core C _ h9 hf 0 (by omega)
      (fun k => decide (k = 0 ∨ k = 2 ∨ k = 5)) (fun k => decide (k = 2 ∨ k = 5))
      (by decide) (by decide) (by decide) (fun k => decide (k = 0)) (by decide)
  · exact PEqualNP.Outside.L_meta_3081.core C _ h9 hf 2 (by omega)
      (fun k => decide (k = 0 ∨ k = 2 ∨ k = 7)) (fun k => decide (k = 0 ∨ k = 7))
      (by decide) (by decide) (by decide) (fun k => decide (k = 2)) (by decide)
