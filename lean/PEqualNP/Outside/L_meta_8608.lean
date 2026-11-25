import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8608

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem aux (v : ℕ → Bool) : ∀ (G : List Gate) (x : List Bool),
    (∀ (i : ℕ) (h : i < x.length), x[i] = v i) →
    (∀ (k : ℕ) (hk : k < G.length), (∀ j ∈ (G[k]).inputs, j < x.length + k) ∧
      (G[k]).op.eval ((G[k]).inputs.map v) = v (x.length + k)) →
    ∀ w, w < x.length + G.length → (G.foldl stepB x).getD w false = v w := by
  intro G
  induction G with
  | nil =>
    intro x hx _ w hw
    have hw2 : w < x.length := hw
    show x.getD w false = v w
    rw [List.getD_eq_getElem x false hw2]
    exact hx w hw2
  | cons g t ih =>
    intro x hx hG w hw
    rw [List.foldl_cons]
    have h0 := hG 0 (Nat.succ_pos _)
    have h0a : ∀ j ∈ g.inputs, j < x.length := fun j hj => h0.1 j hj
    have h0b : g.op.eval (g.inputs.map v) = v x.length := h0.2
    have hmap : (g.inputs.map fun i => x.getD i false) = g.inputs.map v := by
      apply List.map_congr_left
      intro j hj
      show x.getD j false = v j
      rw [List.getD_eq_getElem x false (h0a j hj)]
      exact hx j (h0a j hj)
    have hlen : (stepB x g).length = x.length + 1 := by simp [stepB]
    apply ih (stepB x g)
    · intro i hi
      by_cases hlt : i < x.length
      · have h1 : (stepB x g)[i] = x[i] := List.getElem_append_left hlt
        rw [h1]
        exact hx i hlt
      · have hieq : i = x.length := by omega
        subst hieq
        have h1 : (stepB x g)[x.length] = g.op.eval (g.inputs.map fun i => x.getD i false) := by
          simp [stepB]
        rw [h1, hmap]
        exact h0b
    · intro k hk
      have h := hG (k + 1) (Nat.succ_lt_succ hk)
      have he : x.length + 1 + k = x.length + (k + 1) := by omega
      rw [hlen, he]
      exact h
    · rw [hlen]
      have h2 : (g :: t).length = t.length + 1 := rfl
      omega

end PEqualNP.Outside.L_meta_8608

theorem PEqualNP.Outside.L_meta_8608 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List Bool) (x3 : ℕ → Bool), (∀ (x4 : Fin x2.length), x2.get x4 = x3 ↑x4) → (∀ (x5 : Fin x1.length), (∀ x6 ∈ (x1.get x5).inputs, x6 < x2.length + ↑x5) ∧ (x1.get x5).op.eval (List.map x3 (x1.get x5).inputs) = x3 (x2.length + ↑x5)) → ∀ (x6 : Fin (x2.length + x1.length)), ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x2).getD (↑x6) Bool.false = x3 ↑x6 := by
  intro x1 x2 x3 hx hG w
  exact PEqualNP.Outside.L_meta_8608.aux x3 x1 x2 (fun i h => hx ⟨i, h⟩)
    (fun k hk => hG ⟨k, hk⟩) w w.isLt
