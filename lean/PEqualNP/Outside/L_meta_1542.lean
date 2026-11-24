import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1542_aux

open PEqualNP.CircuitLowerBounds

theorem wires_snoc (gs : List Gate) (g : Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ l = Circuit.wires ⟨gs, o2⟩ l ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o2⟩ l).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (o : ℕ) (l : List Bool) :
    (Circuit.wires ⟨gs, o⟩ l).length = l.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc gs g o o, List.length_append, ih]
    simp
    omega

theorem all_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).all id = true) : (l.map f2).all id = true := by
  simp only [List.all_eq_true, List.mem_map] at *
  rintro b ⟨a, ha, rfl⟩
  exact h a (h1 _ ⟨a, ha, rfl⟩)

theorem any_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).any id = true) : (l.map f2).any id = true := by
  simp only [List.any_eq_true, List.mem_map] at *
  obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := h1
  exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩

theorem mono (n : ℕ) (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (gs rest : List Gate), gates = gs ++ rest →
    ∀ (w : ℕ) (x y : Fin n → Bool), (∀ v : Fin n, x v = true → y v = true) →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false = true →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD w false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro rest _ w x y hxy h
    simp only [Circuit.wires, List.foldl_nil] at h ⊢
    by_cases hw : w < n
    · simp [List.getD_eq_getElem?_getD, hw] at h ⊢
      exact hxy _ h
    · simp [List.getD_eq_getElem?_getD, hw] at h
  | append_singleton gs g ih =>
    intro rest hg w x y hxy h
    have ih' := ih (g :: rest) (by simp [hg])
    have hlen : ∀ z : Fin n → Bool,
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).length = n + gs.length := by
      intro z
      rw [wires_length]
      simp
    rcases lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [wires_snoc gs g 0 0] at h ⊢
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hw)] at h ⊢
      exact ih' w x y hxy h
    · have hgm : g ∈ gates := by rw [hg]; simp
      have hval : ∀ z : Fin n → Bool,
          (Circuit.wires ⟨gs ++ [g], 0⟩ (List.ofFn z)).getD w false =
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false) := by
        intro z
        rw [wires_snoc gs g 0 0, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, hw]
        simp
      rcases hops g hgm with ho | ho
      · rw [hval, ho] at h ⊢
        exact all_mono _ _ (fun i hi => ih' i x y hxy hi) _ h
      · rw [hval, ho] at h ⊢
        exact any_mono _ _ (fun i hi => ih' i x y hxy hi) _ h
    · rw [wires_snoc gs g 0 0] at h
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen] at h
      have : w - (n + gs.length) ≠ 0 := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hk] at h
      simp at h

end PEqualNP.Outside.L_meta_1542_aux

theorem PEqualNP.Outside.L_meta_1542 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = q →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (a b : Fin N),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    a ∈ T0 → b ∈ T0 → a ≠ b →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v = a))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v = b))) = true →
    ∀ s : Fin N, s ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L s))) = true := by
  intro q N L i0 T0 _ _ _ hmeet _ hT0 _ gates g a b hops ha hb hab hea heb s hs
  have hm : ∀ c : Fin N, c ∉ L s →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v = c))) = true →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L s))) = true := by
    intro c hc he
    exact PEqualNP.Outside.L_meta_1542_aux.mono N gates (fun x hx => (hops x hx).1) gates [] (by simp) g _ _
      (by
        intro v hv
        simp only [decide_eq_true_eq] at hv ⊢
        rw [hv]
        exact hc) he
  by_cases hA : a ∈ L s
  · by_cases hB : b ∈ L s
    · exfalso
      have h1 := hmeet s i0 hs
      have hsub : ({a, b} : Finset (Fin N)) ⊆ L s ∩ L i0 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hA, hT0 ha⟩
        · exact Finset.mem_inter.mpr ⟨hB, hT0 hb⟩
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_pair hab, h1] at h2
      omega
    · exact hm b hB heb
  · exact hm a hA hea
