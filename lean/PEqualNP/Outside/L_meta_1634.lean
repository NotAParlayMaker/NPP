import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1634

open PEqualNP.CircuitLowerBounds

private lemma getD_append_lt {l : List Bool} (v : Bool) {i : ℕ} (h : i < l.length) :
    (l ++ [v]).getD i false = l.getD i false := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n =>
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih (by simpa using h)

private lemma getD_append_eq {l : List Bool} (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.getD_cons_succ, List.length_cons]
    exact ih

private lemma getD_append_gt {l : List Bool} (v : Bool) {i : ℕ} (h : l.length < i) :
    (l ++ [v]).getD i false = false := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => simp at h
    | succ m => simp
  | cons x xs ih =>
    cases i with
    | zero => simp at h
    | succ n =>
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih (by simpa using h)

private lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : List Bool} (hpt : ∀ i : ℕ, (x.getD i false = true → y.getD i false = true))
    (h : (g.op.eval (g.inputs.map fun i => x.getD i false)) = true) :
    (g.op.eval (g.inputs.map fun i => y.getD i false)) = true := by
  rcases hop with hop' | hop'
  · rw [hop'] at h ⊢
    simp only [GateOp.eval, List.all_eq_true] at h ⊢
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hpt i (h _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [hop'] at h ⊢
    simp only [GateOp.eval, List.any_eq_true] at h ⊢
    obtain ⟨a, ha, hx⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, hpt i hx⟩

private lemma step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : List Bool} (hlen : x.length = y.length)
    (hpt : ∀ i : ℕ, (x.getD i false = true → y.getD i false = true)) :
    ∀ i : ℕ, ((x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD i false = true →
              (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD i false = true) := by
  intro i hi
  rcases Nat.lt_trichotomy i x.length with hlt | heq | hgt
  · rw [getD_append_lt _ hlt] at hi
    have hyi : i < y.length := by omega
    rw [getD_append_lt _ hyi]
    exact hpt i hi
  · rw [heq] at hi ⊢
    rw [getD_append_eq] at hi
    rw [hlen]
    rw [getD_append_eq]
    exact gate_mono g hop hpt hi
  · rw [getD_append_gt _ hgt] at hi
    simp at hi

private lemma foldl_mono : ∀ (gates : List Gate),
    (∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (x y : List Bool), x.length = y.length →
    (∀ i : ℕ, (x.getD i false = true → y.getD i false = true)) →
    ∀ i : ℕ, ((List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x gates).getD i false = true → (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y gates).getD i false = true) := by
  intro gates
  induction gates with
  | nil => intro _ x y _ hpt; exact hpt
  | cons g gs ih =>
    intro hops x y hlen hpt i hi
    simp only [List.foldl_cons] at hi ⊢
    have hops' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hops g' (by simp [hg'])
    have hlen2 : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).length =
                 (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hpt2 := step_mono g (hops g (by simp)) hlen hpt
    exact ih hops' _ _ hlen2 hpt2 i hi

private lemma getD_ofFn_lt {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

private lemma eval_pt_mono {N : ℕ} {gates : List Gate}
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ (w : ℕ) (z : Fin N → Bool), ev w z = Circuit.eval ⟨gates, w⟩ (List.ofFn z))
    {x y : Fin N → Bool} (hle : ∀ v, x v = true → y v = true) (w : ℕ)
    (hx : ev w x = true) : ev w y = true := by
  rw [hev w y]
  have hx' : Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true := by
    rw [← hev w x]; exact hx
  have hlen : (List.ofFn x).length = (List.ofFn y).length := by
    rw [List.length_ofFn, List.length_ofFn]
  have hpt : ∀ i : ℕ, ((List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true) := by
    intro i hi
    by_cases h : i < N
    · rw [getD_ofFn_lt x i h] at hi
      rw [getD_ofFn_lt y i h]
      exact hle _ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg h] at hi
      simp at hi
  have HW := foldl_mono gates hops (List.ofFn x) (List.ofFn y) hlen hpt
  simp only [Circuit.eval, Circuit.wires] at hx' ⊢
  exact HW w hx'

private lemma exists_pt {N : ℕ} (L : Fin N → Finset (Fin N)) {gates : List Gate}
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ (w : ℕ) (z : Fin N → Bool), ev w z = Circuit.eval ⟨gates, w⟩ (List.ofFn z))
    (T : Fin N → Fin N → Fin N → Bool) (w : ℕ) (a b : Fin N)
    (hle : (L a ∩ L b).card ≤ 1)
    (hcb : ev w (fun v => decide (v ∉ L b)) = false)
    (hcard : 2 ≤ ((L a).filter (fun p => ev w (T a p) = true)).card) :
    ∃ p ∈ L a \ L b, ∃ v ∈ L b, T a p v = true := by
  have hpex : ∃ p ∈ L a \ L b, ev w (T a p) = true := by
    by_contra hcon
    have hcon' : ∀ p ∈ L a \ L b, ev w (T a p) ≠ true := by
      intro p hp hpe
      exact hcon ⟨p, hp, hpe⟩
    have hsub : ((L a).filter (fun p => ev w (T a p) = true)) ⊆ L b := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      by_contra hpb
      exact hcon' p (Finset.mem_sdiff.mpr ⟨hp'.1, hpb⟩) hp'.2
    have h2 : ((L a).filter (fun p => ev w (T a p) = true)) ⊆ L a ∩ L b :=
      Finset.subset_inter (fun p hp => (Finset.mem_filter.mp hp).1) hsub
    have h3 := Finset.card_le_card h2
    omega
  obtain ⟨p, hpm, hpv⟩ := hpex
  refine ⟨p, hpm, ?_⟩
  by_contra hno
  have hno' : ∀ v ∈ L b, T a p v ≠ true := by
    intro v hv hvt
    exact hno ⟨v, hv, hvt⟩
  have hmono : ∀ v : Fin N, (T a p) v = true → (fun v => decide (v ∉ L b)) v = true := by
    intro v hv
    by_cases h : v ∈ L b
    · exact absurd hv (hno' v h)
    · simp [h]
  have hbad := eval_pt_mono hops ev hev hmono w hpv
  rw [hcb] at hbad
  exact absurd hbad (by simp)

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
  intro q N L i0 p0 p1 hq hN hcard1 hinter hpair hpq hp0 hp1 T hT gates hops h1 h2 ev hev w t u htu hft hfu hct hcu
  have hop : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    fun g hg => (hops g hg).1
  have hle_tu : (L t ∩ L u).card ≤ 1 := by
    have h := hinter t u htu
    omega
  have hle_ut : (L u ∩ L t).card ≤ 1 := by
    rw [Finset.inter_comm]
    have h := hinter u t (fun hh => htu hh.symm)
    omega
  exact ⟨PEqualNP.Outside.L_meta_1634.exists_pt L hop ev hev T w t u hle_tu hfu hct,
          PEqualNP.Outside.L_meta_1634.exists_pt L hop ev hev T w u t hle_ut hft hcu⟩
