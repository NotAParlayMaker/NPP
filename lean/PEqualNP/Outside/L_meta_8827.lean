import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8827
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def rho (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (σ ⟨i, h⟩).val else i

def rgs (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho n σ)⟩

theorem simS (n : ℕ) (σ : Equiv.Perm (Fin n)) : ∀ (gs : List Gate) (U U' : List Bool),
    U.length = U'.length → n ≤ U.length →
    (∀ i, U.getD i false = U'.getD (rho n σ i) false) →
    ∀ i, (wf gs U).getD i false = (wf (gs.map (rgs n σ)) U').getD (rho n σ i) false := by
  intro gs
  induction gs with
  | nil => intro U U' _ _ h i; exact h i
  | cons g gs ih =>
    intro U U' hlen hn h i
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false)
        = (rgs n σ g).op.eval ((rgs n σ g).inputs.map fun i => U'.getD i false) := by
      show _ = g.op.eval ((g.inputs.map (rho n σ)).map fun i => U'.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h a
    refine ih _ _ (by simp [hlen]) (by simp; omega) ?_ i
    intro j
    rw [← hv]
    have hfix : ∀ j, n ≤ j → rho n σ j = j := by
      intro j hj
      unfold rho
      rw [dif_neg (by omega)]
    have hlt : ∀ j, j < n → rho n σ j < n := by
      intro j hj
      unfold rho
      rw [dif_pos hj]
      exact (σ ⟨j, hj⟩).isLt
    rcases Nat.lt_trichotomy j U.length with hj | hj | hj
    · rw [getD_snoc_lt _ _ _ hj]
      by_cases hjn : j < n
      · rw [getD_snoc_lt _ _ _ (by have := hlt j hjn; omega)]
        exact h j
      · rw [hfix j (by omega), getD_snoc_lt _ _ _ (by omega)]
        have := h j
        rwa [hfix j (by omega)] at this
    · rw [hfix j (by omega), hj, getD_snoc_eq, hlen, getD_snoc_eq]
    · rw [hfix j (by omega), getD_snoc_gt _ _ _ hj, getD_snoc_gt _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_8827

open PEqualNP.Outside.L_meta_8827 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8827 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : Equiv.Perm (Fin x1)), ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x2.size ∧ ∀ (x6 : ℕ) (x7 : Fin x1 → Bool), x1 ≤ x6 → (x5.wires (List.ofFn x7)).getD x6 Bool.false = (x2.wires (List.ofFn (x7 ∘ ⇑x4))).getD x6 Bool.false := by
  intro n C hm σ
  refine ⟨⟨C.gates.map (rgs n σ), C.output⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := hm g0 hg0
    exact ⟨this.1, by simpa [rgs] using this.2⟩
  · intro w x hw
    have key := simS n σ C.gates (List.ofFn (x ∘ σ)) (List.ofFn x) (by simp) (by simp) (by
      intro i
      by_cases hi : i < n
      · have e1 := getD_ofFn (x ∘ σ) ⟨i, hi⟩
        have e2 := getD_ofFn x (σ ⟨i, hi⟩)
        simp only at e1 e2
        rw [e1]
        unfold rho
        rw [dif_pos hi, e2]
        rfl
      · unfold rho
        rw [dif_neg hi, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]) w
    have hfix : rho n σ w = w := by
      unfold rho
      rw [dif_neg (by omega)]
    rw [hfix] at key
    exact key.symm
