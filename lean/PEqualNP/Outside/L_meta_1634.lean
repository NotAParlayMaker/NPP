import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1634

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma stepWire_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (h : ∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) :
    (stepWire w1 g).length = (stepWire w2 g).length ∧
      ∀ i : ℕ, (stepWire w1 g).getD i false = true → (stepWire w2 g).getD i false = true := by
  have hlen' : (stepWire w1 g).length = (stepWire w2 g).length := by
    simp [stepWire, hlen]
  refine ⟨hlen', fun i hi => ?_⟩
  by_cases hlt : i < w1.length
  · have hlt2 : i < w2.length := by omega
    rw [stepWire, List.getD_append _ _ _ _ hlt] at hi
    rw [stepWire, List.getD_append _ _ _ _ hlt2]
    exact h i hi
  · by_cases heq : i = w1.length
    · subst heq
      rw [stepWire, List.getD_append_right _ _ _ _ (le_refl _)] at hi
      rw [stepWire, List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      have hsub : w1.length - w2.length = 0 := by omega
      rw [hsub]
      simp only [List.getD_cons_zero]
      rcases hop with hop | hop
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map] at hi ⊢
        rintro _ ⟨a, ha, rfl⟩
        exact h a (hi _ ⟨a, ha, rfl⟩)
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map] at hi ⊢
        rcases hi with ⟨_, ⟨a, ha, rfl⟩, htrue⟩
        exact ⟨_, ⟨a, ha, rfl⟩, h a htrue⟩
    · have hge : (stepWire w1 g).length ≤ i := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      rw [List.getD_eq_default _ _ hge] at hi
      cases hi

lemma foldl_stepWire_mono (gates : List Gate)
    (hgates : ∀ gt ∈ gates, gt.op = GateOp.and ∨ gt.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (h : ∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) :
    ∀ i : ℕ, (gates.foldl stepWire w1).getD i false = true →
      (gates.foldl stepWire w2).getD i false = true := by
  induction gates generalizing w1 w2 with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep := stepWire_mono g (hgates g (List.mem_cons_self ..)) w1 w2 hlen h
    exact ih (fun gt hgt => hgates gt (List.mem_cons_of_mem g hgt))
      (stepWire w1 g) (stepWire w2 g) hstep.1 hstep.2

lemma eval_mono {N : ℕ} (gates : List Gate)
    (hgates : ∀ gt ∈ gates, gt.op = GateOp.and ∨ gt.op = GateOp.or)
    (w : ℕ) (x y : Fin N → Bool)
    (hxy : ∀ v : Fin N, x v = true → y v = true) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true →
      Circuit.eval ⟨gates, w⟩ (List.ofFn y) = true := by
  apply foldl_stepWire_mono gates hgates (List.ofFn x) (List.ofFn y) (by simp)
  intro i hi
  by_cases hlt : i < N
  · have hx : (List.ofFn x).getD i false = x ⟨i, hlt⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp [hlt])]
      simp
    have hy : (List.ofFn y).getD i false = y ⟨i, hlt⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp [hlt])]
      simp
    rw [hx] at hi
    rw [hy]
    exact hxy ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

lemma half {N : ℕ} (L : Fin N → Finset (Fin N)) (T : Fin N → Fin N → Fin N → Bool)
    (gates : List Gate)
    (hgates : ∀ gt ∈ gates, gt.op = GateOp.and ∨ gt.op = GateOp.or)
    (w : ℕ) (t u : Fin N)
    (hinter : (L t ∩ L u).card = 1)
    (hfu : Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L u))) = false)
    (hcard : 2 ≤ ((L t).filter (fun p => Circuit.eval ⟨gates, w⟩ (List.ofFn (T t p)) = true)).card) :
    ∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true := by
  have hex : ∃ p ∈ (L t).filter (fun p => Circuit.eval ⟨gates, w⟩ (List.ofFn (T t p)) = true),
      p ∉ L u := by
    by_contra hall
    push_neg at hall
    have hsub : (L t).filter (fun p => Circuit.eval ⟨gates, w⟩ (List.ofFn (T t p)) = true) ⊆
        L t ∩ L u := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, hall p hp⟩
    have hle := Finset.card_le_card hsub
    omega
  rcases hex with ⟨p, hp_filt, hp_not_u⟩
  have hp_t : p ∈ L t := (Finset.mem_filter.mp hp_filt).1
  have hp_ev : Circuit.eval ⟨gates, w⟩ (List.ofFn (T t p)) = true := (Finset.mem_filter.mp hp_filt).2
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hp_t, hp_not_u⟩, ?_⟩
  by_contra hno
  push_neg at hno
  have hle : ∀ v : Fin N, T t p v = true → (fun v : Fin N => decide (v ∉ L u)) v = true := by
    intro v hv
    simp only [decide_eq_true_eq]
    intro hvu
    have := hno v hvu
    rw [hv] at this
    exact this rfl
  have htrue := eval_mono gates hgates w (T t p) (fun v => decide (v ∉ L u)) hle hp_ev
  rw [hfu] at htrue
  cases htrue

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
  intro q N L i0 p0 p1 _ _ _ hinter _ _ _ _ T _ gates hgates _ _ ev hev w t u hne hft hfu hct hcu
  have hgates' : ∀ gt ∈ gates,
      gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    fun gt h => (hgates gt h).1
  simp only [hev] at hft hfu hct hcu
  exact ⟨PEqualNP.Outside.L_meta_1634.half L T gates hgates' w t u (hinter t u hne) hfu hct,
    PEqualNP.Outside.L_meta_1634.half L T gates hgates' w u t (hinter u t hne.symm) hft hcu⟩
