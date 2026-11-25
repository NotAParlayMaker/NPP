import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9039_aux

open PEqualNP.CircuitLowerBounds

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

def pf (x7 : Fin 10 → Bool) : Bool := x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))

theorem edge_avoid : ∀ a b : Fin 10, ∃ u v : Fin 10,
    pf (fun k => decide (k = u) || decide (k = v)) = true ∧ u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b := by
  decide

theorem wires_eq (x : List Bool) (gs : List Gate) (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < x.length) :
    ∀ ys : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (x ++ ys)
      = x ++ ys ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => x.getD i false)) := by
  induction gs with
  | nil => intro ys; simp
  | cons g gs ih =>
    intro ys
    simp only [List.foldl_cons, List.map_cons]
    have hm : (g.inputs.map fun i => (x ++ ys).getD i false) = g.inputs.map fun i => x.getD i false := by
      apply List.map_congr_left
      intro i hi
      have := h g (by simp) i hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
    rw [hm, List.append_assoc x ys, ih (fun g' hg' => h g' (by simp [hg'])) (ys ++ _)]
    simp

end PEqualNP.Outside.L_meta_9039_aux

open PEqualNP.Outside.L_meta_9039_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9039 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (10 : ℕ) ≤ x1.output → (∀ x5 ∈ x1.gates, ∀ x7 ∈ x5.inputs, x7 < (10 : ℕ)) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C hF _ ho hin
  have hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
      (List.ofFn x ++ C.gates.map (fun g => g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))).getD C.output false := by
    intro x
    have := wires_eq (List.ofFn x) C.gates (by simpa using hin) []
    simp only [List.append_nil] at this
    simp only [Circuit.eval, Circuit.wires, this]
  show ∃ x6 : Fin 10 → Bool, C.eval (List.ofFn x6) ≠ pf x6
  have hgd : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
      (C.gates.map (fun g => g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))).getD (C.output - 10) false := by
    intro x
    rw [hev, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp [List.getD_eq_getElem?_getD]
  rcases hg : C.gates[C.output - 10]? with _ | g
  · refine ⟨fun k => decide (k = 0) || decide (k = 1), ?_⟩
    rw [hgd]
    simp [List.getD_eq_getElem?_getD, hg]
    decide
  · have hgm : g ∈ C.gates := List.mem_of_getElem? hg
    have hl := (hF g hgm).2
    have hi := hin g hgm
    obtain ⟨a, b, hab⟩ : ∃ a b : Fin 10, ∀ i ∈ g.inputs, i = a.val ∨ i = b.val := by
      match hgi : g.inputs, hl with
      | [], _ => exact ⟨0, 0, by simp⟩
      | [i], _ =>
        have h1 : i < 10 := hi i (by simp [hgi])
        exact ⟨⟨i, h1⟩, ⟨i, h1⟩, by simp⟩
      | [i, j], _ =>
        have h1 : i < 10 := hi i (by simp [hgi])
        have h2 : j < 10 := hi j (by simp [hgi])
        exact ⟨⟨i, h1⟩, ⟨j, h2⟩, by simp⟩
    obtain ⟨u, v, hpf, h1, h2, h3, h4⟩ := edge_avoid a b
    have hsame : (g.inputs.map fun i => (List.ofFn (fun k : Fin 10 => decide (k = u) || decide (k = v))).getD i false)
        = g.inputs.map fun i => (List.ofFn (fun _ : Fin 10 => false)).getD i false := by
      apply List.map_congr_left
      intro i him
      have hi10 := hi i him
      have hne : (⟨i, hi10⟩ : Fin 10) ≠ u ∧ (⟨i, hi10⟩ : Fin 10) ≠ v := by
        rcases hab i him with e | e
        · subst e; exact ⟨fun h => h1 h.symm, fun h => h3 h.symm⟩
        · subst e; exact ⟨fun h => h2 h.symm, fun h => h4 h.symm⟩
      rw [getD_ofFn, getD_ofFn, dif_pos hi10, dif_pos hi10]
      simp [hne.1, hne.2]
    by_cases hc : C.eval (List.ofFn (fun _ : Fin 10 => false)) = false
    · refine ⟨fun k => decide (k = u) || decide (k = v), ?_⟩
      rw [hgd, List.getD_eq_getElem?_getD, List.getElem?_map, hg]
      rw [hgd, List.getD_eq_getElem?_getD, List.getElem?_map, hg] at hc
      simp only [Option.map_some, Option.getD_some] at hc ⊢
      rw [hsame, hc, hpf]
      simp
    · refine ⟨fun _ => false, ?_⟩
      have : pf (fun _ : Fin 10 => false) = false := by decide
      rw [this]
      exact hc
