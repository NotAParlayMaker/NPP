import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1331

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem fold_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length =
      w.length + (gs.length + 1)
    rw [ih]
    simp
    omega

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wiresFrom (gs ++ [g]) w =
      wiresFrom gs w ++ [g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false)] := by
  induction gs generalizing w with
  | nil => rfl
  | cons h gs ih =>
    change wiresFrom (gs ++ [g]) (w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) =
      wiresFrom gs (w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) ++
        [g.op.eval (g.inputs.map fun i =>
          (wiresFrom gs (w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)])).getD i false)]
    exact ih _

theorem const_prefix (n : ℕ) (gates : List Gate) (G : Finset (Fin gates.length))
    (hout : ∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u)
    (k : Fin gates.length) (hkmin : ∀ i ∈ G, k ≤ i)
    (x y : Fin n → Bool) (t : ℕ) (ht : t ≤ k.val) :
    ∀ i : ℕ, n ≤ i →
      (wiresFrom (gates.take t) (List.ofFn x)).getD i false =
        (wiresFrom (gates.take t) (List.ofFn y)).getD i false := by
  induction t with
  | zero =>
    intro i hi
    have hx : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    have hy : (List.ofFn y).getD i false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    simpa [wiresFrom] using hx.trans hy.symm
  | succ t ih =>
    intro i hi
    have ht0 : t < k.val := Nat.lt_of_succ_le ht
    have hlen : t < gates.length := by
      have := k.isLt
      omega
    have htake : gates.take (t + 1) = gates.take t ++ [gates[t]] :=
      List.take_succ_eq_append_getElem hlen
    rw [htake, wiresFrom_snoc, wiresFrom_snoc]
    have hlx : (wiresFrom (gates.take t) (List.ofFn x)).length = n + t := by
      rw [fold_length, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hlen)]
    have hly : (wiresFrom (gates.take t) (List.ofFn y)).length = n + t := by
      rw [fold_length, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hlen)]
    by_cases hieq : i = n + t
    · subst hieq
      have hx : (wiresFrom (gates.take t) (List.ofFn x) ++
          [gates[t].op.eval (gates[t].inputs.map fun i =>
            (wiresFrom (gates.take t) (List.ofFn x)).getD i false)]).getD (n + t) false =
          gates[t].op.eval (gates[t].inputs.map fun i =>
            (wiresFrom (gates.take t) (List.ofFn x)).getD i false) := by
        rw [← hlx]; exact getD_snoc_eq _ _ _
      have hy : (wiresFrom (gates.take t) (List.ofFn y) ++
          [gates[t].op.eval (gates[t].inputs.map fun i =>
            (wiresFrom (gates.take t) (List.ofFn y)).getD i false)]).getD (n + t) false =
          gates[t].op.eval (gates[t].inputs.map fun i =>
            (wiresFrom (gates.take t) (List.ofFn y)).getD i false) := by
        rw [← hly]; exact getD_snoc_eq _ _ _
      rw [hx, hy]
      have hjG : (⟨t, hlen⟩ : Fin gates.length) ∉ G := by
        intro hj
        have hkj : (k : ℕ) ≤ t := by
          simpa using Fin.val_le_of_le (hkmin _ hj)
        exact Nat.not_le.mpr ht0 hkj
      have hinputs : ∀ u ∈ (gates.get ⟨t, hlen⟩).inputs, n ≤ u := hout _ hjG
      have hg : gates.get ⟨t, hlen⟩ = gates[t] := by
        simpa using List.get_eq_getElem (l := gates) (i := ⟨t, hlen⟩)
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu0 : u ∈ (gates.get ⟨t, hlen⟩).inputs := by
        rw [hg]; exact hu
      exact ih (Nat.le_of_lt ht0) u (hinputs u hu0)
    · have hne : i ≠ n + t := hieq
      rw [getD_snoc_ne _ _ _ _ (by rw [hlx]; exact hne),
        getD_snoc_ne _ _ _ _ (by rw [hly]; exact hne)]
      exact ih (Nat.le_of_lt ht0) i hi

theorem main (n : ℕ) (gates : List Gate) (G : Finset (Fin gates.length))
    (hout : ∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u)
    (k : Fin gates.length) (_hkG : k ∈ G) (hkmin : ∀ i ∈ G, k ≤ i)
    (w : ℕ) (_hw : w ∈ (gates.get k).inputs) (hwn : n ≤ w)
    (x y : Fin n → Bool) :
    Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn x) =
      Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn y) := by
  simp only [Circuit.eval, wires_eq]
  exact const_prefix n gates G hout k hkmin x y k.val le_rfl w hwn

end PEqualNP.Outside.L_meta_1331

theorem PEqualNP.Outside.L_meta_1331 :
    ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate)
      (G : Finset (Fin gates.length)),
      (∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u) →
      ∀ k ∈ G, (∀ i ∈ G, k ≤ i) → ∀ w ∈ (gates.get k).inputs, n ≤ w →
        ∀ x y : Fin n → Bool,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn x) =
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn y) := by
  intro n gates G hout k hkG hkmin w hw hwn x y
  exact PEqualNP.Outside.L_meta_1331.main n gates G hout k hkG hkmin w hw hwn x y
