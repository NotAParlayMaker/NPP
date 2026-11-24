import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1634

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

theorem mono (n : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (w : ℕ) (x y : Fin n → Bool), (∀ v : Fin n, x v = true → y v = true) →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false = true →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD w false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ w x y hxy h
    simp only [Circuit.wires, List.foldl_nil] at h ⊢
    by_cases hw : w < n
    · simp [List.getD_eq_getElem?_getD, hw] at h ⊢
      exact hxy _ h
    · simp [List.getD_eq_getElem?_getD, hw] at h
  | append_singleton gs g ih =>
    intro hops w x y hxy h
    have ih2 := ih (fun g2 hg2 => hops g2 (by simp [hg2]))
    have hlen : ∀ z : Fin n → Bool,
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).length = n + gs.length := by
      intro z
      rw [wires_length]
      simp
    rcases lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [wires_snoc gs g 0 0] at h ⊢
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hw)] at h ⊢
      exact ih2 w x y hxy h
    · have hval : ∀ z : Fin n → Bool,
          (Circuit.wires ⟨gs ++ [g], 0⟩ (List.ofFn z)).getD w false =
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false) := by
        intro z
        rw [wires_snoc gs g 0 0, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, hw]
        simp
      rcases hops g (by simp) with ho | ho
      · rw [hval, ho] at h ⊢
        exact all_mono _ _ (fun i hi => ih2 i x y hxy hi) _ h
      · rw [hval, ho] at h ⊢
        exact any_mono _ _ (fun i hi => ih2 i x y hxy hi) _ h
    · rw [wires_snoc gs g 0 0] at h
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen] at h
      have : w - (n + gs.length) ≠ 0 := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hk] at h
      simp at h

end PEqualNP.Outside.L_meta_1634

theorem PEqualNP.Outside.L_meta_1634 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ (w : ℕ) (t u : Fin N), t ≠ u → ev w (fun v : Fin N => decide (v ∉ L t)) = false → ev w (fun v : Fin N => decide (v ∉ L u)) = false →
      2 ≤ ((L t).filter (fun p => ev w (T t p) = true)).card → 2 ≤ ((L u).filter (fun p => ev w (T u p) = true)).card →
      (∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin hp01 h0 h1 T hT gates hops hlen hread ev hev w t u htu hft hfu h2t h2u
  have hmono : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) → ev w x = true → ev w y = true := by
    intro x y hxy h
    rw [hev] at h ⊢
    exact PEqualNP.Outside.L_meta_1634.mono N gates (fun g hg => (hops g hg).1) w x y hxy h
  have key : ∀ a b : Fin N, a ≠ b → ev w (fun v : Fin N => decide (v ∉ L b)) = false →
      2 ≤ ((L a).filter (fun p => ev w (T a p) = true)).card →
      ∃ p ∈ L a \ L b, ∃ v ∈ L b, T a p v = true := by
    intro a b hab hfb h2
    have hex : ∃ p ∈ (L a).filter (fun p => ev w (T a p) = true), p ∉ L b := by
      by_contra hcon
      have hsub : (L a).filter (fun p => ev w (T a p) = true) ⊆ L a ∩ L b := by
        intro p hp
        refine Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, ?_⟩
        by_contra hpb
        exact hcon ⟨p, hp, hpb⟩
      have hle := Finset.card_le_card hsub
      rw [hint a b hab] at hle
      omega
    obtain ⟨p, hp, hpb⟩ := hex
    obtain ⟨hpa, hpe⟩ := Finset.mem_filter.mp hp
    refine ⟨p, Finset.mem_sdiff.mpr ⟨hpa, hpb⟩, ?_⟩
    by_contra hcon
    have hy := hmono (T a p) (fun v : Fin N => decide (v ∉ L b)) (fun v hv => by
      simp only [decide_eq_true_eq]
      intro hvb
      exact hcon ⟨v, hvb, hv⟩) hpe
    rw [hfb] at hy
    exact Bool.false_ne_true hy
  exact ⟨key t u htu hfu h2t, key u t htu.symm hft h2u⟩
