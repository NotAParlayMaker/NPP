import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1316

open PEqualNP.CircuitLowerBounds

-- a wire read from a list bounded by B is bounded by B (a missing wire counts 0)
theorem getD_le (d : List ℕ) (B i : ℕ) (h : ∀ x ∈ d, x ≤ B) : d.getD i 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : d[i]? with
  | none => simp
  | some v =>
    have hv : v ∈ d := List.mem_of_getElem? hi
    simpa using h v hv

theorem foldr_max_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldr_cons]
    exact max_le (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

-- a gate of fan-in at most two at most doubles the bound
theorem gate_le (g : Gate) (d : List ℕ) (B : ℕ) (hlen : g.inputs.length ≤ 2)
    (h : ∀ x ∈ d, x ≤ B) : g.lineDegree d ≤ B * 2 := by
  have hm : ∀ x ∈ g.inputs.map (fun i => d.getD i 0), x ≤ B := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact getD_le d B i h
  unfold Gate.lineDegree
  split_ifs
  · have h1 := List.sum_le_length_nsmul (g.inputs.map (fun i => d.getD i 0)) B hm
    rw [List.length_map, smul_eq_mul] at h1
    calc (g.inputs.map (fun i => d.getD i 0)).sum ≤ g.inputs.length * B := h1
      _ ≤ 2 * B := Nat.mul_le_mul_right B hlen
      _ = B * 2 := Nat.mul_comm 2 B
  · have h2 := foldr_max_le (g.inputs.map (fun i => d.getD i 0)) B hm
    omega

theorem fold_le (gs : List Gate) : ∀ (d : List ℕ) (B : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → (∀ x ∈ d, x ≤ B) →
    ∀ x ∈ gs.foldl (fun d g => d ++ [g.lineDegree d]) d, x ≤ B * 2 ^ gs.length := by
  induction gs with
  | nil =>
    intro d B _ h x hx
    simpa using h x hx
  | cons g t ih =>
    intro d B hg h x hx
    rw [List.foldl_cons] at hx
    have hstep : ∀ y ∈ d ++ [g.lineDegree d], y ≤ B * 2 := by
      intro y hy
      rw [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | hy
      · have := h y hy
        omega
      · rw [hy]
        exact gate_le g d B (hg g (by simp)) h
    have := ih (d ++ [g.lineDegree d]) (B * 2) (fun g' hg' => hg g' (by simp [hg'])) hstep x hx
    rw [List.length_cons, pow_succ, Nat.mul_comm (2 ^ t.length) 2, ← Nat.mul_assoc]
    exact this

end PEqualNP.Outside.L_meta_1316

theorem PEqualNP.Outside.L_meta_1316 : ∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.lineDeg n marked ≤ 2 ^ C.size := by
  intro n marked C hC
  have h0 : ∀ x ∈ (List.range n).map (fun i => if i ∈ marked then 1 else 0), x ≤ 1 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    split_ifs <;> omega
  have hall := PEqualNP.Outside.L_meta_1316.fold_le C.gates _ 1 (fun g hg => (hC g hg).2) h0
  rw [Nat.one_mul] at hall
  exact PEqualNP.Outside.L_meta_1316.getD_le _ _ _ hall
