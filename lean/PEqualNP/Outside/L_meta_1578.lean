import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1578_aux

open PEqualNP.CircuitLowerBounds

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length ∧
    ∀ j < w.length, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false = w.getD j false := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    obtain ⟨h1, h2⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons]
      rw [h1]
      simp
      omega
    · intro j hj
      simp only [List.foldl_cons]
      rw [h2 j (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem key (pre : List Gate) (g : Gate) (post : List Gate) (x : List Bool)
    (h : ∀ a ∈ g.inputs, a < x.length + pre.length) :
    ((pre ++ g :: post).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD (x.length + pre.length) false =
      g.op.eval (g.inputs.map fun a => ((pre ++ g :: post).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD a false) := by
  rw [List.foldl_append, List.foldl_cons]
  obtain ⟨hl, _⟩ := fold_prefix pre x
  set W := pre.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  obtain ⟨_, hp⟩ := fold_prefix post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
  rw [hp _ (by simp; omega)]
  have e1 : (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD (x.length + pre.length) false
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    rw [← hl]
    simp [List.getD_eq_getElem?_getD]
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro a ha
  have := h a ha
  rw [hp _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show a < W.length by omega)]

theorem eval_gate (gates : List Gate) (x : List Bool) (hx : x.length = 13) (i : Fin gates.length)
    (h : ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) :
    Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ x =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => Circuit.eval ⟨gates, a⟩ x) := by
  have e : gates.take i ++ (gates.get i :: gates.drop (i + 1)) = gates := by
    simp [List.get_eq_getElem]
  have hk := key (gates.take i) (gates.get i) (gates.drop (i + 1)) x (by
    intro a ha
    have := h a ha
    simp [hx]
    omega)
  rw [e] at hk
  have hl : x.length + (gates.take i).length = 13 + (i : ℕ) := by
    simp [hx]
  rw [hl] at hk
  exact hk

theorem eval_input (gates : List Gate) (f : Fin 13 → Bool) (w : ℕ) (hw : w < 13) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn f) = f ⟨w, hw⟩ := by
  unfold Circuit.eval Circuit.wires
  obtain ⟨_, hp⟩ := fold_prefix gates (List.ofFn f)
  rw [hp w (by simp; omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), List.getElem_ofFn]
  rfl

theorem inv (L : Fin 13 → Finset (Fin 13)) (gates : List Gate) (zs : ℕ) (hzs : zs ≤ gates.length)
    (hop : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (s : Fin 13) (hs0 : s ∈ L 0)
    (hand : ∀ i : Fin gates.length, (i : ℕ) < zs → (gates.get i).op = GateOp.and →
      Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      ∀ t : Fin 13, t ≠ 0 → Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
      Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = false) :
    ∀ w, w < 13 + zs → Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true →
      ∀ t : Fin 13, Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false → s ∈ L t := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw h0 hy t ht
  by_cases hw13 : w < 13
  · rw [eval_input _ _ w hw13] at h0 hy ht
    simp at h0 hy ht
    rcases hy with hy | ⟨_, hy⟩
    · rw [← hy]
      exact ht
    · exact absurd h0 hy
  · obtain ⟨i, rfl⟩ : ∃ i, w = 13 + i := ⟨w - 13, by omega⟩
    have hi : i < gates.length := by omega
    have hg : ∀ x : List Bool, x.length = 13 → Circuit.eval ⟨gates, 13 + i⟩ x =
        (gates.get ⟨i, hi⟩).op.eval ((gates.get ⟨i, hi⟩).inputs.map fun a => Circuit.eval ⟨gates, a⟩ x) :=
      fun x hx => eval_gate gates x hx ⟨i, hi⟩ (hin ⟨i, hi⟩)
    rcases hop (gates.get ⟨i, hi⟩) (List.get_mem _ _) with hop' | hop'
    · by_cases ht0 : t = 0
      · subst ht0
        exact hs0
      · have := hand ⟨i, hi⟩ (by simp; omega) hop' h0 t ht0 ht
        rw [this] at hy
        exact absurd hy (by simp)
    · rw [hg _ (by simp), hop'] at h0 hy ht
      simp [GateOp.eval, List.any_eq_true, List.any_eq_false] at h0 hy ht
      obtain ⟨a, ha, hya⟩ := hy
      have hai := hin ⟨i, hi⟩ a ha
      simp at hai
      exact ih a (by omega) (by omega) (by simpa using h0 a ha) hya t (by simpa using ht a ha)

end PEqualNP.Outside.L_meta_1578_aux

theorem PEqualNP.Outside.L_meta_1578 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = true) →
    (∀ i : Fin gates.length, i < zs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = false) →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) ∨
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) := by
  intro L hL gates zs u v l m hops hin hl hm hop hinp h0 hl' hm' hy hand
  have hzl : ∀ x : List Bool, x.length = 13 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ x =
      (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ x && PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ x) := by
    intro x hx
    rw [PEqualNP.Outside.L_meta_1578_aux.eval_gate gates x hx zs (hin zs).2, hop, hinp]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have huv : u < 13 + (zs : ℕ) ∧ v < 13 + (zs : ℕ) := by
    have h2 := (hin zs).2
    rw [hinp] at h2
    exact ⟨h2 u (by simp), h2 v (by simp)⟩
  have core : ∀ s : Fin 13, (s = 3 ∨ s = 9) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true →
      (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) ∨
      (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) := by
    intro s hs hys
    have hs0 : s ∈ L 0 := by
      rw [hL]
      rcases hs with rfl | rfl <;> decide
    have hsl : s ∉ L l := by
      rw [hL]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl <;> rcases hs with rfl | rfl <;> decide
    have hsm : s ∉ L m := by
      rw [hL]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> rcases hs with rfl | rfl <;> decide
    have hI := PEqualNP.Outside.L_meta_1578_aux.inv L gates zs (le_of_lt zs.isLt)
      (fun g hg => (hops g hg).1) (fun i => (hin i).2) s hs0 (by
        intro i hi hop2 h1 t ht h2
        have := hand i (Fin.lt_def.mpr hi) hop2 h1 t ht h2
        rcases hs with rfl | rfl
        · exact this.1
        · exact this.2)
    rw [hzl _ (by simp)] at h0 hl' hm' hys
    simp only [Bool.and_eq_true] at hys
    obtain ⟨huy, hvy⟩ := hys
    cases hv0 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0)))
    · have hvl : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true := by
        cases h : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l)))
        · exact absurd (hI v huv.2 hv0 hvy l h) hsl
        · rfl
      have hvm : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true := by
        cases h : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m)))
        · exact absurd (hI v huv.2 hv0 hvy m h) hsm
        · rfl
      rw [hvl, Bool.and_true] at hl'
      rw [hvm, Bool.and_true] at hm'
      have hu0 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true := by
        cases h : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0)))
        · exact absurd (hI u huv.1 h huy l hl') hsl
        · rfl
      exact Or.inl ⟨hl', hm', hu0, rfl, hvl, hvm⟩
    · rw [hv0, Bool.and_true] at h0
      have hul : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true := by
        cases h : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l)))
        · exact absurd (hI u huv.1 h0 huy l h) hsl
        · rfl
      have hum : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true := by
        cases h : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m)))
        · exact absurd (hI u huv.1 h0 huy m h) hsm
        · rfl
      rw [hul, Bool.true_and] at hl'
      rw [hum, Bool.true_and] at hm'
      exact Or.inr ⟨hl', hm', rfl, h0, hul, hum⟩
  rcases hy with hy | hy
  · exact core 3 (Or.inl rfl) hy
  · exact core 9 (Or.inr rfl) hy
