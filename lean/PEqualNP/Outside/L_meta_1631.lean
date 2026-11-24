import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1631

open PEqualNP.CircuitLowerBounds

-- One evaluation step: the gate adds one wire.
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_app (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false
      = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp [List.getD_eq_getElem?_getD]
  · exact getD_ge _ _ (by simp; omega)

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with e | e
  · rw [e]
    simp only [GateOp.eval]
    intro H
    rw [List.all_eq_true] at H ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i (H _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [e]
    simp only [GateOp.eval]
    intro H
    rw [List.any_eq_true] at H ⊢
    obtain ⟨b, hb, hbt⟩ := H
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f' i, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hbt⟩

-- Raising wire values never lowers a later wire of a circuit of AND and OR gates.
theorem mono_fold : ∀ (gs : List Gate) (W W' : List Bool), W.length = W'.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W.getD i false = true → W'.getD i false = true) →
    ∀ i, (gs.foldl stp W).getD i false = true → (gs.foldl stp W').getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W W' _ _ h i; exact h i
  | cons g gs ih =>
    intro W W' hl hops h
    simp only [List.foldl_cons]
    apply ih (stp W g) (stp W' g) (by simp [stp, hl]) (fun g' hg' => hops g' (by simp [hg']))
    intro i
    simp only [stp]
    rw [getD_app, getD_app, ← hl]
    split_ifs
    · exact h i
    · exact eval_mono g (hops g (by simp)) _ _ h
    · exact id

theorem wire_mono {N : ℕ} (gates : List Gate)
    (hops : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ w x, ev w x = Circuit.eval ⟨gates, w⟩ (List.ofFn x))
    (w : ℕ) {x y : Fin N → Bool} (hxy : ∀ v, x v = true → y v = true) :
    ev w x = true → ev w y = true := by
  rw [hev, hev]
  apply mono_fold gates (List.ofFn x) (List.ofFn y) (by simp) (fun g hg => (hops g hg).1)
  intro i hi
  by_cases h : i < N
  · rw [getD_ofFn x i h] at hi
    rw [getD_ofFn y i h]
    exact hxy _ hi
  · rw [getD_ge _ _ (by simp; omega)] at hi
    contradiction

theorem forward : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) →
    ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true) := by
  intro q N L i0 p0 p1 hq hN hcard hinter hjoin hne hp0 hp1 gates hmono hneG htop ev hev o h t
  have outside (ht : t ≠ i0) : ∃ v ∈ L t, v ∉ L i0 := by
    by_contra! hall
    have hs : L t ⊆ L i0 := by exact hall
    have he : L t ∩ L i0 = L t := Finset.inter_eq_left.mpr hs
    have hi := hinter t i0 ht
    rw [he, hcard] at hi
    omega
  have hdom : (decide (p0 ∉ L t) = true ∨ decide (p1 ∉ L t) = true ∨
        ∀ u : Fin N, u ∉ L i0 → decide (u ∉ L t) = true) := by
    by_cases ht : t = i0
    · subst t
      exact Or.inr (Or.inr (fun u hu => decide_eq_true hu))
    by_cases h0 : p0 ∈ L t
    · by_cases h1 : p1 ∈ L t
      · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hinter t i0 ht)
        have m0 : p0 ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨h0, hp0⟩
        have m1 : p1 ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨h1, hp1⟩
        rw [hv, Finset.mem_singleton] at m0 m1
        exact False.elim (hne (m0.trans m1.symm))
      · exact Or.inr (Or.inl (decide_eq_true h1))
    · exact Or.inl (decide_eq_true h0)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h t (fun v => decide (v ∉ L t)) hdom]
    simp
  · intro h0
    rw [h t (fun v => decide (v = p0)) (Or.inl (by simp))]
    exact decide_eq_true ⟨p0, h0, by simp⟩
  · intro h1
    rw [h t (fun v => decide (v = p1)) (Or.inr (Or.inl (by simp)))]
    exact decide_eq_true ⟨p1, h1, by simp⟩
  · intro p hp
    constructor
    · rw [h t (fun v => decide (v = p0 ∨ v = p)) (Or.inl (by simp))]
      exact decide_eq_true ⟨p, hp, by simp⟩
    · rw [h t (fun v => decide (v = p1 ∨ v = p)) (Or.inr (Or.inl (by simp)))]
      exact decide_eq_true ⟨p, hp, by simp⟩
  · intro ht
    rw [h t (fun v => decide (v ∉ L i0)) (Or.inr (Or.inr (fun u hu => decide_eq_true hu)))]
    obtain ⟨v, hv, hv'⟩ := outside ht
    exact decide_eq_true ⟨v, hv, decide_eq_true hv'⟩
  · intro w hw _ _
    rw [h t (fun v => decide (v ∉ L i0 ∨ v = w)) (Or.inr (Or.inr (fun u hu => decide_eq_true (Or.inl hu))))]
    exact decide_eq_true ⟨w, (Finset.mem_inter.mp hw).1, by simp⟩

theorem backward {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (ev : ℕ → (Fin N → Bool) → Bool) (o : Fin N → ℕ)
    (hmono : ∀ (w : ℕ) (x y : Fin N → Bool), (∀ i, x i ≤ y i) → ev w x ≤ ev w y)
    (htest : ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧
      (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧
      (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧
        ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧
      (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 →
        ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) :
    ∀ (t : Fin N) (x : Fin N → Bool),
      (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true) := by
  classical
  intro t x hx
  obtain ⟨hn,hs0,hs1,hpairs,hout,hboth⟩ := htest t
  have liftPos (y : Fin N → Bool) (hy : ev (o t) y = true)
      (hxy : ∀ i, y i = true → x i = true) : ev (o t) x = true := by
    apply Bool.eq_true_of_true_le
    rw [← hy]
    apply hmono
    intro i
    cases hh : y i with
    | false => simp
    | true => simp [hxy i hh]
  by_cases h : ∃ v ∈ L t, x v = true
  · simp only [decide_eq_true h]
    obtain ⟨p,hp,hxp⟩ := h
    rcases hx with hx | hx | hx
    · apply liftPos _ (hpairs p hp).1
      intro i hi
      rcases of_decide_eq_true hi with he | he
      · simpa [he] using hx
      · simpa [he] using hxp
    · apply liftPos _ (hpairs p hp).2
      intro i hi
      rcases of_decide_eq_true hi with he | he
      · simpa [he] using hx
      · simpa [he] using hxp
    · by_cases ht : t = i0
      · by_cases he0 : p = p0
        · subst p
          apply liftPos _ (hs0 hp)
          intro i hi
          simpa [of_decide_eq_true hi] using hxp
        by_cases he1 : p = p1
        · subst p
          apply liftPos _ (hs1 hp)
          intro i hi
          simpa [of_decide_eq_true hi] using hxp
        have hpi : p ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hp, ht ▸ hp⟩
        apply liftPos _ (hboth p hpi he0 he1)
        intro i hi
        rcases of_decide_eq_true hi with ho | he
        · exact hx i ho
        · simpa [he] using hxp
      · apply liftPos _ (hout ht)
        intro i hi
        exact hx i (of_decide_eq_true hi)
  · simp only [decide_eq_false h]
    apply Bool.eq_false_of_le_false
    rw [← hn]
    apply hmono
    intro i
    cases hi : x i with
    | false => simp
    | true =>
      have hni : i ∉ L t := fun hit => h ⟨i,hit,hi⟩
      simp [hni]

end PEqualNP.Outside.L_meta_1631

theorem PEqualNP.Outside.L_meta_1631 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, ((∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) ↔
    ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) := by
  intro q N L i0 p0 p1 hq hN hc hi hj hp hp0 hp1 gates hops hlen hwire ev hev o
  constructor
  · exact PEqualNP.Outside.L_meta_1631.forward q N L i0 p0 p1 hq hN hc hi hj hp hp0 hp1 gates hops hlen hwire ev hev o
  · apply PEqualNP.Outside.L_meta_1631.backward L i0 p0 p1 ev o
    intro w x y hxy
    apply Bool.le_iff_imp.mpr
    apply PEqualNP.Outside.L_meta_1631.wire_mono gates hops ev hev w
    intro i
    exact Bool.le_iff_imp.mp (hxy i)
