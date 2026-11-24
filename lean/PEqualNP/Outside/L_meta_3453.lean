import Mathlib
import PEqualNP.Defs

-- Substituting reads changes only input lists, so the two gate lists have the same length and
-- the same operations. Along the gate list, the new wire prefix is below (or equal to) the old
-- one at x: an unchanged read compares by induction, and a read of wire n + u, now of sigma r,
-- compares through the hypothesis, both wires lying in the prefix since gates read back.

namespace PEqualNP.Outside.L_meta_3453

open PEqualNP.CircuitLowerBounds

-- The wires of the first t gates on input x.
def W {n : ℕ} (gates : List Gate) (t : ℕ) (x : Fin n → Bool) : List Bool :=
  Circuit.wires ⟨gates.take t, 0⟩ (List.ofFn x)

theorem W_zero {n : ℕ} (gates : List Gate) (x : Fin n → Bool) : W gates 0 x = List.ofFn x := by
  simp [W, Circuit.wires]

theorem W_succ {n : ℕ} (gates : List Gate) (t : ℕ) (ht : t < gates.length)
    (x : Fin n → Bool) :
    W gates (t + 1) x = W gates t x ++
      [gates[t].op.eval (gates[t].inputs.map fun k => (W gates t x).getD k false)] := by
  unfold W Circuit.wires
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem W_length {n : ℕ} (gates : List Gate) (x : Fin n → Bool) :
    ∀ t : ℕ, t ≤ gates.length → (W gates t x).length = n + t := by
  intro t
  induction t with
  | zero => intro _; simp [W_zero]
  | succ t ih =>
    intro ht
    rw [W_succ gates t (by omega), List.length_append, ih (by omega)]
    simp
    omega

theorem W_prefix {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (t : ℕ) :
    ∀ u : ℕ, t + u ≤ gates.length → W gates t x <+: W gates (t + u) x := by
  intro u
  induction u with
  | zero => intro _; exact List.prefix_refl _
  | succ u ih =>
    intro h
    rw [← Nat.add_assoc, W_succ gates (t + u) (by omega)]
    exact (ih (by omega)).trans (List.prefix_append _ _)

theorem getD_of_prefix {l1 l2 : List Bool} (h : l1 <+: l2) (i : ℕ) (hi : i < l1.length) :
    l1.getD i false = l2.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc (l : List Bool) (b : Bool) (k : ℕ) :
    (l ++ [b]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

theorem wires_eq_W {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    C.wires (List.ofFn x) = W C.gates C.gates.length x := by
  simp [W, Circuit.wires]

theorem all_mono' (ks : List ℕ) (f g : ℕ → Bool) (hfg : ∀ k ∈ ks, f k = true → g k = true) :
    (ks.map f).all id = true → (ks.map g).all id = true := by
  simp only [List.all_eq_true, List.mem_map, id]
  rintro h b ⟨k, hk, rfl⟩
  exact hfg k hk (h (f k) ⟨k, hk, rfl⟩)

theorem any_mono' (ks : List ℕ) (f g : ℕ → Bool) (hfg : ∀ k ∈ ks, f k = true → g k = true) :
    (ks.map f).any id = true → (ks.map g).any id = true := by
  simp only [List.any_eq_true, List.mem_map, id]
  rintro ⟨b, ⟨k, hk, rfl⟩, hb⟩
  exact ⟨g k, ⟨k, hk, rfl⟩, hfg k hk hb⟩

theorem subst_length (C : Circuit) (n u : ℕ) (sigma : ℕ → ℕ) :
    (PEqualNP.FactorSubst.substReads C n u sigma).gates.length = C.gates.length := by
  simp [PEqualNP.FactorSubst.substReads]

theorem subst_get (C : Circuit) (n u : ℕ) (sigma : ℕ → ℕ) (t : ℕ)
    (ht : t < (PEqualNP.FactorSubst.substReads C n u sigma).gates.length)
    (ht' : t < C.gates.length) :
    (PEqualNP.FactorSubst.substReads C n u sigma).gates[t] =
      ⟨C.gates[t].op, C.gates[t].inputs.map fun i => if i = n + u then sigma t else i⟩ := by
  simp [PEqualNP.FactorSubst.substReads]

theorem gateAt_eq (C : Circuit) (t : ℕ) (ht : t < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C t = C.gates[t] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ht]

end PEqualNP.Outside.L_meta_3453

open PEqualNP.Outside.L_meta_3453

theorem PEqualNP.Outside.L_meta_3453 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool), PEqualNP.TopForm.IsAO2 n C → u < C.gates.length → (∀ r : ℕ, sigma r < n + u) → ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = true → (C.wires (List.ofFn x)).getD (n + u) false = true) → ∀ i : ℕ, ((PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn x)).getD i false = true) ∧ ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = (C.wires (List.ofFn x)).getD (n + u) false) → (PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x)) := by
  intro n C u sigma x hC hu hsig
  obtain ⟨hops, hback, _⟩ := hC
  set C' := PEqualNP.FactorSubst.substReads C n u sigma with hC'
  have hlen : C'.gates.length = C.gates.length := subst_length C n u sigma
  have hfull := wires_eq_W C x
  have hfull' := wires_eq_W C' x
  rw [hlen] at hfull'
  -- the old prefix agrees with the full wire list below its length
  have hpre : ∀ t, t ≤ C.gates.length → ∀ k, k < n + t →
      (W C.gates t x).getD k false = (C.wires (List.ofFn x)).getD k false := by
    intro t ht k hk
    rw [hfull]
    have hp := W_prefix C.gates x t (C.gates.length - t) (by omega)
    rw [show t + (C.gates.length - t) = C.gates.length by omega] at hp
    exact getD_of_prefix hp k (by rw [W_length C.gates x t ht]; exact hk)
  -- facts about gate t reading wire n + u
  have hread : ∀ t (ht : t < C.gates.length), n + u ∈ C.gates[t].inputs →
      n + u < n + t ∧ sigma t < n + u := by
    intro t ht hm
    have h1 := hback t ht (n + u) (by rw [gateAt_eq C t ht]; exact hm)
    exact ⟨h1, hsig t⟩
  constructor
  · intro H
    have key : ∀ t, t ≤ C.gates.length → ∀ k, (W C'.gates t x).getD k false = true →
        (W C.gates t x).getD k false = true := by
      intro t
      induction t with
      | zero =>
        intro _ k hk
        simpa [W_zero] using hk
      | succ t ih =>
        intro ht k hk
        have htl : t < C.gates.length := by omega
        have htl' : t < C'.gates.length := by omega
        have ih' := ih (by omega)
        rw [W_succ C'.gates t htl', getD_snoc, W_length C'.gates x t (by omega)] at hk
        rw [W_succ C.gates t htl, getD_snoc, W_length C.gates x t (by omega)]
        split_ifs at hk ⊢ with h1 h2
        · exact ih' k hk
        · rw [subst_get C n u sigma t htl' htl] at hk
          simp only [List.map_map] at hk
          have hfg : ∀ i ∈ C.gates[t].inputs,
              ((fun k => (W C'.gates t x).getD k false) ∘
                (fun i => if i = n + u then sigma t else i)) i = true →
              (W C.gates t x).getD i false = true := by
            intro i hi h
            simp only [Function.comp] at h
            split_ifs at h with hiu
            · subst hiu
              obtain ⟨r1, r2⟩ := hread t htl hi
              have a1 := ih' _ h
              rw [hpre t (by omega) _ (by omega)] at a1
              have a2 := H t htl (by rw [gateAt_eq C t htl]; exact hi) a1
              rw [hpre t (by omega) _ (by omega)]
              exact a2
            · exact ih' i h
          rcases hops _ (List.getElem_mem htl) with hop | hop
          · rw [hop] at hk ⊢
            exact all_mono' _ _ _ hfg hk
          · rw [hop] at hk ⊢
            exact any_mono' _ _ _ hfg hk
    intro i hi
    rw [hfull'] at hi
    rw [hfull]
    exact key C.gates.length le_rfl i hi
  · intro H
    have key : ∀ t, t ≤ C.gates.length → W C'.gates t x = W C.gates t x := by
      intro t
      induction t with
      | zero => intro _; simp [W_zero]
      | succ t ih =>
        intro ht
        have htl : t < C.gates.length := by omega
        have htl' : t < C'.gates.length := by omega
        have ih' := ih (by omega)
        rw [W_succ C'.gates t htl', W_succ C.gates t htl, ih', subst_get C n u sigma t htl' htl]
        congr 2
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp]
        split_ifs with hiu
        · subst hiu
          obtain ⟨r1, r2⟩ := hread t htl hi
          rw [hpre t (by omega) _ (by omega), hpre t (by omega) _ (by omega)]
          exact H t htl (by rw [gateAt_eq C t htl]; exact hi)
        · rfl
    rw [hfull', hfull, key C.gates.length le_rfl]
