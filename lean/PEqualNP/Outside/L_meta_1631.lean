import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1631

open PEqualNP.CircuitLowerBounds

def Le (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

theorem getD_snoc (a : List Bool) (c : Bool) (i : ℕ) :
    (a ++ [c]).getD i false = if i < a.length then a.getD i false else
      if i = a.length then c else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - a.length = k + 1 := ⟨i - a.length - 1, by omega⟩
    rw [hk]; simp

theorem step_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : Le a b) :
    Le (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  have hv : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
    · simp only [List.all_map, List.all_eq_true, Function.comp, id]
      intro H j hj; exact h.2 _ (H j hj)
    · simp only [List.any_map, List.any_eq_true, Function.comp, id]
      rintro ⟨j, hj, hj'⟩; exact ⟨j, hj, h.2 _ hj'⟩
  refine ⟨by simp [h.1], fun i => ?_⟩
  rw [getD_snoc, getD_snoc, ← h.1]
  split_ifs
  · exact h.2 i
  · exact hv
  · exact id

theorem foldl_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b, Le a b →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_mono g (hgs g (List.mem_cons_self ..)) a b h)

theorem eval_mono {N : ℕ} (gates : List Gate)
    (hgs : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true → Circuit.eval ⟨gates, w⟩ (List.ofFn y) = true := by
  have h0 : Le (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, fun i hi => ?_⟩
    by_cases hN : i < N
    · rw [List.getD_eq_getElem _ _ (by simpa using hN), List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simpa using hN)] at hi
      exact absurd hi (by simp)
  exact (foldl_mono gates hgs _ _ h0).2 w

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
  intro q N L i0 p0 p1 hq hN hcard hint _ hne h0 h1 gates hops _ _ ev hev o
  have hgs : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hops g hg).1
  have mono : ∀ w (x y : Fin N → Bool), (∀ v, x v = true → y v = true) →
      ev w x = true → ev w y = true := fun w x y hxy hx => by
    rw [hev] at hx ⊢
    exact PEqualNP.Outside.L_meta_1631.eval_mono gates hgs w x y hxy hx
  have two : ∀ t, t ≠ i0 → p0 ∈ L t → p1 ∈ L t → False := fun t ht a b => by
    have hc := hint t i0 ht
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> simp_all
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at this
    omega
  have out : ∀ t, t ≠ i0 → ∃ v ∈ L t, v ∉ L i0 := fun t ht => by
    by_contra hc
    push_neg at hc
    have : L t ∩ L i0 = L t := Finset.inter_eq_left.mpr hc
    have h1 := hint t i0 ht
    rw [this, hcard] at h1
    omega
  constructor
  · intro H t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [H t]
      · simp
      · by_cases a : p0 ∈ L t
        · by_cases b : p1 ∈ L t
          · have ht : t = i0 := by
              by_contra ht; exact two t ht a b
            subst ht
            right; right; intro u hu; simpa using hu
          · right; left; simpa using b
        · left; simpa using a
    · intro hp
      rw [H t _ (Or.inl (by simp))]
      simpa using hp
    · intro hp
      rw [H t _ (Or.inr (Or.inl (by simp)))]
      simpa using hp
    · intro p hp
      constructor
      · rw [H t _ (Or.inl (by simp))]
        simpa using ⟨p, hp, Or.inr rfl⟩
      · rw [H t _ (Or.inr (Or.inl (by simp)))]
        simpa using ⟨p, hp, Or.inr rfl⟩
    · intro ht
      rw [H t _ (Or.inr (Or.inr (fun u hu => by simpa using hu)))]
      obtain ⟨v, hv, hv'⟩ := out t ht
      simpa using ⟨v, hv, hv'⟩
    · intro w hw _ _
      rw [H t _ (Or.inr (Or.inr (fun u hu => by simp [hu])))]
      simpa using ⟨w, (Finset.mem_inter.mp hw).1, Or.inr rfl⟩
  · intro H t x hx
    obtain ⟨T1, _, _, T4, T5, T6⟩ := H t
    by_cases hd : ∃ v ∈ L t, x v = true
    · rw [decide_eq_true hd]
      obtain ⟨v, hv, hxv⟩ := hd
      have c0 : x p0 = true → ev (o t) x = true := fun hp =>
        mono _ _ _ (fun u hu => by
          simp only [decide_eq_true_eq] at hu
          rcases hu with rfl | rfl <;> assumption) (T4 v hv).1
      have c1 : x p1 = true → ev (o t) x = true := fun hp =>
        mono _ _ _ (fun u hu => by
          simp only [decide_eq_true_eq] at hu
          rcases hu with rfl | rfl <;> assumption) (T4 v hv).2
      rcases hx with hx | hx | hx
      · exact c0 hx
      · exact c1 hx
      · by_cases ht : t = i0
        · subst ht
          by_cases e0 : v = p0
          · subst e0; exact c0 hxv
          by_cases e1 : v = p1
          · subst e1; exact c1 hxv
          exact mono _ _ _ (fun u hu => by
            simp only [decide_eq_true_eq] at hu
            rcases hu with hu | rfl
            · exact hx u hu
            · exact hxv) (T6 v (Finset.mem_inter.mpr ⟨hv, hv⟩) e0 e1)
        · exact mono _ _ _ (fun u hu => hx u (by simpa using hu)) (T5 ht)
    · rw [decide_eq_false hd]
      by_contra hc
      have hc' : ev (o t) x = true := by simpa using hc
      have := mono _ x (fun v : Fin N => decide (v ∉ L t)) (fun u hu =>
        decide_eq_true (fun hu' => hd ⟨u, hu', hu⟩)) hc'
      rw [T1] at this
      exact absurd this (by simp)
