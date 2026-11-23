import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_752

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Dep (D : Finset (Fin 4)) (h : (Fin 4 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 4 → Bool, (∀ i ∈ D, x i = y i) → h x = h y

def St (W : (Fin 4 → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin 4)) : Prop :=
  (∀ x, (W x).length = m) ∧ ∀ i, Dep (Sup i) (fun x => (W x).getD i false)

def sup0 (i : ℕ) : Finset (Fin 4) := if h : i < 4 then {⟨i, h⟩} else ∅

def sup1 (l : List ℕ) (i : ℕ) : Finset (Fin 4) :=
  if i = 4 then l.toFinset.biUnion sup0 else sup0 i

def base (j : Fin 4) : Fin 4 → Bool := fun i => decide (i.val / 2 = j.val / 2)

lemma st_step (W : (Fin 4 → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin 4))
    (h : St W m Sup) (g : Gate) :
    St (fun x => step (W x) g) (m + 1)
      (fun i => if i = m then g.inputs.toFinset.biUnion Sup else Sup i) := by
  obtain ⟨hm, hD⟩ := h
  refine ⟨fun x => by simp [step, hm x], fun i => ?_⟩
  intro x y hxy
  show (step (W x) g).getD i false = (step (W y) g).getD i false
  unfold step
  rcases lt_trichotomy i m with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by rw [hm x]; exact hi),
      List.getD_append _ _ _ _ (by rw [hm y]; exact hi)]
    refine hD i x y (fun j hj => hxy j ?_)
    simpa [hi.ne] using hj
  · rw [List.getD_append_right _ _ _ _ (by rw [hm x]; omega),
      List.getD_append_right _ _ _ _ (by rw [hm y]; omega), hm x, hm y]
    have e : (g.inputs.map fun k => (W x).getD k false) =
        (g.inputs.map fun k => (W y).getD k false) := by
      apply List.map_congr_left
      intro k hk
      refine hD k x y (fun j hj => hxy j ?_)
      have hmem : j ∈ g.inputs.toFinset.biUnion Sup :=
        Finset.mem_biUnion.mpr ⟨k, List.mem_toFinset.mpr hk, hj⟩
      simpa [hi] using hmem
    rw [e]
  · rw [List.getD_append_right _ _ _ _ (by rw [hm x]; omega),
      List.getD_append_right _ _ _ _ (by rw [hm y]; omega), hm x, hm y]
    obtain ⟨k, hk⟩ : ∃ k, i - m = k + 1 := ⟨i - m - 1, by omega⟩
    rw [hk]
    rfl

lemma st_init : St (fun x : Fin 4 → Bool => List.ofFn x) 4 sup0 := by
  refine ⟨fun x => List.length_ofFn, fun i x y hxy => ?_⟩
  show (List.ofFn x).getD i false = (List.ofFn y).getD i false
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    List.getElem?_ofFn]
  by_cases h : i < 4
  · have hx := hxy ⟨i, h⟩ (by simp [sup0, h])
    simp [h, hx]
  · simp [h]

lemma sup0_card (i : ℕ) : (sup0 i).card ≤ 1 := by
  unfold sup0
  split <;> simp

lemma bi_card (Sup : ℕ → Finset (Fin 4)) (l : List ℕ) (hl : l.length ≤ 2)
    (h : ∀ k, (Sup k).card ≤ 1) : (l.toFinset.biUnion Sup).card ≤ 2 := by
  have h1 := Finset.card_biUnion_le_card_mul l.toFinset Sup 1 (fun a _ => h a)
  have h2 := List.toFinset_card_le l
  omega

lemma sup1_card4 (l : List ℕ) (hl : l.length ≤ 2) : (sup1 l 4).card ≤ 2 := by
  have h := bi_card sup0 l hl sup0_card
  simpa [sup1] using h

lemma sup1_card_ne (l : List ℕ) (k : ℕ) (hk : k ≠ 4) : (sup1 l k).card ≤ 1 := by
  have h := sup0_card k
  simpa [sup1, hk] using h

lemma bi_card3 (Sup : ℕ → Finset (Fin 4)) (h4 : (Sup 4).card ≤ 2)
    (h : ∀ k, k ≠ 4 → (Sup k).card ≤ 1) :
    ∀ l : List ℕ, l.length ≤ 2 → (l.toFinset.biUnion Sup).card ≤ 3
  | [], _ => by simp
  | [a], _ => by
    have e : ([a].toFinset.biUnion Sup) = Sup a := by simp
    rw [e]
    by_cases ha : a = 4
    · rw [ha]
      omega
    · have := h a ha
      omega
  | [a, b], _ => by
    have e : ([a, b].toFinset.biUnion Sup) = Sup a ∪ Sup b := by simp
    rw [e]
    have hu := Finset.card_union_le (Sup a) (Sup b)
    by_cases ha : a = 4
    · by_cases hb : b = 4
      · rw [ha, hb, Finset.union_self]
        omega
      · have := h b hb
        rw [ha] at hu ⊢
        omega
    · have := h a ha
      by_cases hb : b = 4
      · rw [hb] at hu ⊢
        omega
      · have := h b hb
        omega
  | _ :: _ :: _ :: _, hl => by simp at hl

lemma supp : ∀ gs : List Gate, gs.length ≤ 2 → (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∃ Sup : ℕ → Finset (Fin 4), (∀ i, (Sup i).card ≤ 3) ∧
      ∀ i, Dep (Sup i) (fun x => (gs.foldl step (List.ofFn x)).getD i false)
  | [], _, _ => ⟨sup0, fun i => (sup0_card i).trans (by norm_num), st_init.2⟩
  | [g0], _, hfan => by
    have h0 := hfan g0 (by simp)
    refine ⟨sup1 g0.inputs, fun i => ?_, (st_step _ 4 sup0 st_init g0).2⟩
    by_cases hi : i = 4
    · rw [hi]
      exact (sup1_card4 _ h0).trans (by norm_num)
    · exact (sup1_card_ne _ i hi).trans (by norm_num)
  | [g0, g1], _, hfan => by
    have h0 := hfan g0 (by simp)
    have h1 := hfan g1 (by simp)
    have s1 : St (fun x => step (List.ofFn x) g0) (4 + 1) (sup1 g0.inputs) :=
      st_step _ 4 sup0 st_init g0
    refine ⟨_, fun i => ?_, (st_step _ (4 + 1) (sup1 g0.inputs) s1 g1).2⟩
    show (if i = 4 + 1 then g1.inputs.toFinset.biUnion (sup1 g0.inputs)
      else sup1 g0.inputs i).card ≤ 3
    split
    · exact bi_card3 (sup1 g0.inputs) (sup1_card4 _ h0) (sup1_card_ne _) g1.inputs h1
    · by_cases hi : i = 4
      · rw [hi]
        exact (sup1_card4 _ h0).trans (by norm_num)
      · exact (sup1_card_ne _ i hi).trans (by norm_num)
  | _ :: _ :: _ :: _, hl, _ => by simp at hl

lemma wit : ∀ j : Fin 4,
    ((base j 0 && base j 1) || (base j 2 && base j 3)) = true ∧
    ((Function.update (base j) j false 0 && Function.update (base j) j false 1) ||
      (Function.update (base j) j false 2 && Function.update (base j) j false 3)) = false := by
  decide

lemma up_eval : ∀ a b c d : Bool,
    Circuit.eval ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩
      [a, b, c, d] = ((a && b) || (c && d)) := by
  decide

lemma ofFn4 (x : Fin 4 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3] := by
  rfl

end PEqualNP.Outside.L_meta_752

open PEqualNP.Outside.L_meta_752 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_752 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hfan, hsize, hC⟩
    by_contra hs
    have hlen : C.gates.length ≤ 2 := by
      have : C.size = C.gates.length := rfl
      omega
    obtain ⟨Sup, hcard, hdep⟩ := supp C.gates hlen (fun g hg => (hfan g hg).2)
    have hD := hdep C.output
    obtain ⟨j, hj⟩ : ∃ j, j ∉ Sup C.output := by
      by_contra hne
      push_neg at hne
      have hu := Finset.eq_univ_iff_forall.mpr hne
      have h3 := hcard C.output
      rw [hu] at h3
      simp at h3
    have e : C.eval (List.ofFn (base j)) =
        C.eval (List.ofFn (Function.update (base j) j false)) :=
      hD (base j) (Function.update (base j) j false) (fun i hi => by
        have hij : i ≠ j := by
          rintro rfl
          exact hj hi
        simp [Function.update, hij])
    have e1 := hC (base j)
    have e2 := hC (Function.update (base j) j false)
    have k := wit j
    have hfalse : true = false :=
      k.1.symm.trans (e1.symm.trans (e.trans (e2.trans k.2)))
    cases hfalse
  · intro hs
    refine ⟨⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩,
      ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp
    · exact hs
    · intro x
      rw [ofFn4 x]
      exact up_eval (x 0) (x 1) (x 2) (x 3)
