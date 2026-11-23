import PEqualNP.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic

-- Mythos 6 et Codex Betelgeuse

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_736_aux

def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun k => w.getD k false)
def tick (w : List Bool) (g : Gate) := w ++ [val g w]
def ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩

lemma transport (a b : List Bool) (f : ℕ → ℕ)
    (h : ∀ (s : List Bool) (i : ℕ), (b ++ s).getD (f i) false = (a ++ s).getD i false)
    (gs : List Gate) (s : List Bool) (i : ℕ) :
    ((gs.map (ren f)).foldl tick (b ++ s)).getD (f i) false =
      (gs.foldl tick (a ++ s)).getD i false := by
  induction gs generalizing s with
  | nil => exact h s i
  | cons g gs ih =>
    have v : val (ren f g) (b ++ s) = val g (a ++ s) := by
      simp only [val, ren, List.map_map, Function.comp_def, h]
    simpa only [List.map_cons, List.foldl_cons, tick, v, List.append_assoc] using
      ih (s ++ [val g (a ++ s)])

end PEqualNP.Outside.L_meta_736_aux

theorem PEqualNP.Outside.L_meta_736 : ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  classical
  intro n n' O e mono cover _ gs
  let f (i : ℕ) := if h : i < n then
      if t : ∃ j : Fin n', e j = ⟨i,h⟩ then (Classical.choose t).val else n'
    else n'+1+(i-n)
  refine ⟨f, ?_⟩
  intro x y lx ly on keep
  have base (s : List Bool) (i : ℕ) :
      ((y ++ [true]) ++ s).getD (f i) false = (x ++ s).getD i false := by
    by_cases hi : i < n
    · rw [List.getD_append _ _ _ _ (by omega : i < x.length)]
      by_cases h : ∃ j : Fin n', e j = ⟨i,hi⟩
      · let j := Classical.choose h
        have ej : e j = ⟨i,hi⟩ := Classical.choose_spec h
        have fj : f i = j.val := by simp [f, hi, h, j]
        have jlt : j.val < y.length := by simp [ly]
        rw [fj, List.getD_append _ _ _ _ (by simp [ly]; omega),
            List.getD_append _ _ _ _ jlt]
        simpa [ej] using (keep j).symm
      · have ho : (⟨i,hi⟩ : Fin n) ∈ O := by
          by_contra notmem
          exact h ((cover _).mp notmem)
        have ff : f i = n' := by simp [f, hi, h]
        rw [ff, List.getD_append _ _ _ _ (by simp [ly]),
            List.getD_append_right _ _ _ _ (by omega), ly, Nat.sub_self]
        exact (on _ ho).symm
    · have ff : f i = n'+1+(i-n) := by simp [f,hi]
      rw [ff, List.getD_append_right _ _ _ _ (by simp [ly]),
          List.getD_append_right _ _ _ _ (by omega)]
      simp [ly,lx]
  have allw := PEqualNP.Outside.L_meta_736_aux.transport x (y ++ [true]) f base gs []
  simp only [List.append_nil] at allw
  exact ⟨allw,allw⟩
