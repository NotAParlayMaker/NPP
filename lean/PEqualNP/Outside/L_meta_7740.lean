import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7740

open PEqualNP.CircuitLowerBounds

def step (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def mapGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def lift (n m : ℕ) (π : Fin n → Fin m) (k : ℕ) : ℕ :=
  if h : k < n then (π ⟨k, h⟩).val else m + (k - n)

lemma getD_lift {n m : ℕ} (W y T : List Bool) (π : Fin n → Fin m)
    (hW : W.length = m) (hy : y.length = n)
    (hyv : ∀ k (h : k < n), y.getD k false = W.getD (π ⟨k, h⟩) false) (k : ℕ) :
    (W ++ T).getD (lift n m π k) false = (y ++ T).getD k false := by
  unfold lift
  split_ifs with h
  · have := (π ⟨k, h⟩).isLt
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hyv k h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

lemma fold_agree {n m : ℕ} (W y : List Bool) (π : Fin n → Fin m)
    (hW : W.length = m) (hy : y.length = n)
    (hyv : ∀ k (h : k < n), y.getD k false = W.getD (π ⟨k, h⟩) false)
    (gs : List Gate) : ∀ T : List Bool, ∃ R : List Bool,
      (gs.map (mapGate (lift n m π))).foldl step (W ++ T) = W ++ R ∧
      gs.foldl step (y ++ T) = y ++ R := by
  induction gs with
  | nil => intro T; exact ⟨T, rfl, rfl⟩
  | cons g gs ih =>
    intro T
    have hm : (g.inputs.map (lift n m π)).map (fun i => (W ++ T).getD i false)
        = g.inputs.map (fun i => (y ++ T).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_lift W y T π hW hy hyv i)
    have e1 : step (W ++ T) (mapGate (lift n m π) g)
        = W ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (W ++ T) ++ [g.op.eval ((g.inputs.map (lift n m π)).map fun i => (W ++ T).getD i false)] = W ++ (T ++ _)
      rw [hm, List.append_assoc]
    have e2 : step (y ++ T) g
        = y ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (y ++ T) ++ _ = _
      rw [List.append_assoc]
    obtain ⟨R, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)])
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons, e1, h1]
    · rw [List.foldl_cons, e2, h2]

lemma ofFn_comp {n m : ℕ} (π : Fin n → Fin m) (x : Fin m → Bool) :
    ∀ k (h : k < n), (List.ofFn (x ∘ π)).getD k false = (List.ofFn x).getD (π ⟨k, h⟩) false := by
  intro k h
  have := (π ⟨k, h⟩).isLt
  simp [List.getD_eq_getElem?_getD, h, this]

end PEqualNP.Outside.L_meta_7740

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_7740 in
theorem PEqualNP.Outside.L_meta_7740 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ → ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size = x4.size ∧ (∀ x8 < x1 + x4.size, x7 x8 < x2 + x6.size) ∧ ∀ (x8 : Fin x2 → Bool), ∀ x9 < x1 + x4.size, (x6.wires (List.ofFn x8)).getD (x7 x9) Bool.false = (x4.wires (List.ofFn (x8 ∘ x3))).getD x9 Bool.false := by
  intro n m π C hC
  refine ⟨⟨C.gates.map (mapGate (lift n m π)), C.output⟩, lift n m π, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hC g' hg'
    simpa [mapGate] using this
  · simp [Circuit.size]
  · intro k hk
    simp only [Circuit.size, List.length_map] at hk ⊢
    unfold lift
    split_ifs with h
    · have := (π ⟨k, h⟩).isLt
      omega
    · omega
  · intro x k _
    have hW : (List.ofFn x).length = m := by simp
    have hy : (List.ofFn (x ∘ π)).length = n := by simp
    obtain ⟨R, h1, h2⟩ := fold_agree _ _ π hW hy (ofFn_comp π x) C.gates []
    simp only [List.append_nil] at h1 h2
    show (List.foldl step _ _).getD _ false = (List.foldl step _ _).getD _ false
    rw [h1, h2, getD_lift _ _ R π hW hy (ofFn_comp π x)]
