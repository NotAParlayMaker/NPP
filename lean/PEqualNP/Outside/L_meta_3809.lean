import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3809_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

lemma step_inv (r : ℕ → ℕ) (L : ℕ) (W Y : List Bool) (g : Gate) (hl : W.length = Y.length)
    (hL : L ≤ Y.length) (h1 : ∀ k, L ≤ k → r k = k)
    (h2 : ∀ k, k < L → r k < L)
    (hv : ∀ k, W.getD (r k) false = Y.getD k false) :
    ∀ k, (stepW W (reGate r g)).getD (r k) false = (stepW Y g).getD k false := by
  intro k
  have hm : (g.inputs.map r).map (fun i => W.getD i false)
      = g.inputs.map (fun i => Y.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hv i)
  show (W ++ [g.op.eval ((g.inputs.map r).map fun i => W.getD i false)]).getD (r k) false
    = (Y ++ [g.op.eval (g.inputs.map fun i => Y.getD i false)]).getD k false
  rw [hm]
  by_cases hk : k < L
  · have h := h2 k hk
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hv k]
  · have hrk := h1 k (by omega)
    have e := hv k
    rw [hrk] at e
    rw [hrk]
    by_cases hk2 : k < Y.length
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hk2, e]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

lemma fold_inv (r : ℕ → ℕ) (L : ℕ) (h1 : ∀ k, L ≤ k → r k = k)
    (h2 : ∀ k, k < L → r k < L) (gs : List Gate) :
    ∀ (W Y : List Bool), W.length = Y.length →
    L ≤ Y.length → (∀ k, W.getD (r k) false = Y.getD k false) →
    ∀ k, ((gs.map (reGate r)).foldl stepW W).getD (r k) false = (gs.foldl stepW Y).getD k false := by
  induction gs with
  | nil => intro W Y _ _ hv; exact hv
  | cons g gs ih =>
    intro W Y hl hL hv
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_ (step_inv r L W Y g hl hL h1 h2 hv)
    · simp [stepW, hl]
    · simp [stepW]; omega

def rel (x1 : Fin 9 → Fin 9) (k : ℕ) : ℕ := if h : k < 9 then (x1 ⟨k, h⟩).val else k

lemma base (x1 : Fin 9 → Fin 9) (x5 : Fin 9 → Bool) (a b : Bool) (k : ℕ) :
    (List.ofFn x5 ++ [a, b]).getD (rel x1 k) false
      = (List.ofFn (x5 ∘ x1) ++ [a, b]).getD k false := by
  unfold rel
  by_cases hk : k < 9
  · rw [dif_pos hk, List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simpa using hk)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (x1 ⟨k, hk⟩).isLt), List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn, List.getElem_ofFn]
    rfl
  · rw [dif_neg hk, List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

end PEqualNP.Outside.L_meta_3809_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3809_aux in
theorem PEqualNP.Outside.L_meta_3809 : ∀ (x1 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x2.size ∧ ∀ (x5 : Fin (9 : ℕ) → Bool) (x6 x7 : Bool), x4.eval (List.ofFn x5 ++ [x6, x7]) = x2.eval (List.ofFn (x5 ∘ x1) ++ [x6, x7]) := by
  intro x1 C hC
  refine ⟨⟨C.gates.map (reGate (rel x1)), rel x1 C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hC g0 hg0
    simpa [reGate] using this
  · simp [Circuit.size]
  · intro x5 a b
    exact fold_inv (rel x1) 9 (fun k hk => by simp [rel]; omega)
      (fun k hk => by simp [rel, hk]) C.gates _ _ (by simp) (by simp)
      (base x1 x5 a b) C.output
