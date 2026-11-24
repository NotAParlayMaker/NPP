import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1631

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem eval_mono_fn {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
    (h : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  refine mono gates _ _ (by simp) hg ?_ o h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id

theorem two_off {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 t : Fin N)
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (h01 : p0 ≠ p1) (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0) (ht : t ≠ i0) :
    p0 ∉ L t ∨ p1 ∉ L t := by
  by_contra hcon
  push_neg at hcon
  have h1' := hI t i0 ht
  have h2 : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rw [Finset.mem_inter]
    rcases hv with rfl | rfl
    · exact ⟨hcon.1, h0⟩
    · exact ⟨hcon.2, h1⟩
  have h3 := Finset.card_le_card h2
  rw [Finset.card_pair h01, h1'] at h3
  omega

theorem main {N : ℕ} (q : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hq : 3 ≤ q) (hc : ∀ i : Fin N, (L i).card = q + 1)
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (h01 : p0 ≠ p1) (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0)
    (f : (Fin N → Bool) → Bool)
    (hm : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) → f x = true → f y = true)
    (t : Fin N) :
    (∀ x : Fin N → Bool, (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      f x = decide (∃ v ∈ L t, x v = true)) ↔
    (f (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → f (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → f (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, f (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ f (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → f (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → f (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) := by
  constructor
  · intro H
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hF : ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨ (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨
          ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true) := by
        by_cases ht : t = i0
        · right
          right
          intro u hu
          rw [ht]
          exact decide_eq_true hu
        · rcases two_off L i0 p0 p1 t hI h01 h0 h1 ht with h | h
          · left
            exact decide_eq_true h
          · right
            left
            exact decide_eq_true h
      rw [H _ hF]
      refine decide_eq_false ?_
      rintro ⟨v, hv, hv'⟩
      exact (of_decide_eq_true hv') hv
    · intro hp
      rw [H _ (Or.inl (decide_eq_true rfl))]
      exact decide_eq_true ⟨p0, hp, decide_eq_true rfl⟩
    · intro hp
      rw [H _ (Or.inr (Or.inl (decide_eq_true rfl)))]
      exact decide_eq_true ⟨p1, hp, decide_eq_true rfl⟩
    · intro p hp
      constructor
      · rw [H _ (Or.inl (decide_eq_true (Or.inl rfl)))]
        exact decide_eq_true ⟨p, hp, decide_eq_true (Or.inr rfl)⟩
      · rw [H _ (Or.inr (Or.inl (decide_eq_true (Or.inl rfl))))]
        exact decide_eq_true ⟨p, hp, decide_eq_true (Or.inr rfl)⟩
    · intro ht
      rw [H _ (Or.inr (Or.inr (fun u hu => decide_eq_true hu)))]
      have hcard := Finset.card_sdiff_add_card_inter (L t) (L i0)
      rw [hI t i0 ht, hc t] at hcard
      have hpos : 0 < (L t \ L i0).card := by omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_sdiff] at hv
      exact decide_eq_true ⟨v, hv.1, decide_eq_true hv.2⟩
    · intro w hw _ _
      rw [H _ (Or.inr (Or.inr (fun u hu => decide_eq_true (Or.inl hu))))]
      exact decide_eq_true ⟨w, (Finset.mem_inter.mp hw).1, decide_eq_true (Or.inr rfl)⟩
  · rintro ⟨hz, he0, he1, hp, hzi, hw⟩ x hx
    by_cases hex : ∃ v ∈ L t, x v = true
    · rw [decide_eq_true hex]
      obtain ⟨v, hv, hxv⟩ := hex
      rcases hx with hx | hx | hx
      · refine hm _ _ (fun u hu => ?_) (hp v hv).1
        rcases of_decide_eq_true hu with h | h
        · rw [h]
          exact hx
        · rw [h]
          exact hxv
      · refine hm _ _ (fun u hu => ?_) (hp v hv).2
        rcases of_decide_eq_true hu with h | h
        · rw [h]
          exact hx
        · rw [h]
          exact hxv
      · by_cases hti : t = i0
        · by_cases hv0 : v = p0
          · rw [hv0] at hv hxv
            refine hm _ _ (fun u hu => ?_) (he0 hv)
            rw [of_decide_eq_true hu]
            exact hxv
          · by_cases hv1 : v = p1
            · rw [hv1] at hv hxv
              refine hm _ _ (fun u hu => ?_) (he1 hv)
              rw [of_decide_eq_true hu]
              exact hxv
            · have hvi : v ∈ L i0 := by
                rw [← hti]
                exact hv
              refine hm _ _ (fun u hu => ?_) (hw v (Finset.mem_inter.mpr ⟨hv, hvi⟩) hv0 hv1)
              rcases of_decide_eq_true hu with h | h
              · exact hx u h
              · rw [h]
                exact hxv
        · exact hm _ _ (fun u hu => hx u (of_decide_eq_true hu)) (hzi hti)
    · rw [decide_eq_false hex]
      cases hfx : f x with
      | false => rfl
      | true =>
        have h2 := hm x (fun v : Fin N => decide (v ∉ L t))
          (fun u hu => decide_eq_true (fun hmem => hex ⟨u, hmem, hu⟩)) hfx
        rw [hz] at h2
        exact h2.symm

end PEqualNP.Outside.L_meta_1631

open PEqualNP.Outside.L_meta_1631 in
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
  intro q N L i0 p0 p1 hq _ hc hI _ h01 h0 h1 gates hg _ _ ev he o
  refine forall_congr' (fun t => ?_)
  refine main q L i0 p0 p1 hq hc hI h01 h0 h1 (ev (o t)) (fun x y hxy h => ?_) t
  rw [he] at h ⊢
  exact eval_mono_fn gates (fun g' hg' => (hg g' hg').1) x y hxy (o t) h
