import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_591_aux

open PEqualNP.CircuitLowerBounds

def sw (u v : ℕ) (i : ℕ) : ℕ := if i = u then v else i

def reGate (u v : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sw u v)⟩

theorem step (u v : ℕ) (b : Bool) (w w' : List Bool) (hlen : w.length = w'.length)
    (hu : u < w.length) (hv : v < w.length)
    (h : ∀ i, w.getD i false = w'.getD (sw u v i) false) :
    ∀ i, (w ++ [b]).getD i false = (w' ++ [b]).getD (sw u v i) false := by
  intro i
  have hi := h i
  simp only [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hiu : i = u
  · have hs : sw u v i = v := by simp [sw, hiu]
    rw [hs] at hi ⊢
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact hi
  · have hs : sw u v i = i := by simp [sw, hiu]
    rw [hs] at hi ⊢
    rcases lt_trichotomy i w.length with hlt | heq | hgt
    · rw [List.getElem?_append_left hlt, List.getElem?_append_left (by omega)]
      exact hi
    · subst heq
      rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right (by omega)]
      simp [hlen]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem fold (u v : ℕ) (gs : List Gate) :
    ∀ (w w' : List Bool), w.length = w'.length → u < w.length → v < w.length →
      (∀ i, w.getD i false = w'.getD (sw u v i) false) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          w).getD i false =
        ((gs.map (reGate u v)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD
          (sw u v i) false := by
  induction gs with
  | nil => intro w w' _ _ _ h; simpa using h
  | cons g gs ih =>
    intro w w' hlen hu hv h
    simp only [List.map_cons, List.foldl_cons]
    have hb : (reGate u v g).op.eval ((reGate u v g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [reGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (h i).symm
    rw [hb]
    apply ih
    · simp [hlen]
    · simp; omega
    · simp; omega
    · exact step u v _ w w' hlen hu hv h

end PEqualNP.Outside.L_meta_591_aux

theorem PEqualNP.Outside.L_meta_591 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), PEqualNP.MetaComplexity.HasCircuitSize n F s → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => F (Function.update x u (x v))) s := by
  intro n s F u v h
  obtain ⟨C, hfan, hsize, heval⟩ := h
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_591_aux.reGate u v),
    PEqualNP.Outside.L_meta_591_aux.sw u v C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hfan g0 hg0
    simpa [PEqualNP.Outside.L_meta_591_aux.reGate] using this
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hsize
  · intro x
    show _ = F (Function.update x u (x v))
    rw [← heval (Function.update x u (x v))]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    symm
    apply PEqualNP.Outside.L_meta_591_aux.fold
    · simp
    · simp
    · simp
    · intro i
      simp only [List.getD_eq_getElem?_getD, PEqualNP.Outside.L_meta_591_aux.sw]
      by_cases hiu : i = (u : ℕ)
      · subst hiu
        simp
      · simp only [hiu, ite_false]
        by_cases hin : i < n
        · simp [hin, Function.update, Fin.ext_iff, hiu]
        · simp [hin]
