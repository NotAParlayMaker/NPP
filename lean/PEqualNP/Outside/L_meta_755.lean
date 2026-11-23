import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_755

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Dep (n : ℕ) (D : Finset (Fin n)) (h : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i ∈ D, x i = y i) → h x = h y

def St (n : ℕ) (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n)) : Prop :=
  (∀ x, (W x).length = m) ∧ ∀ i, Dep n (Sup i) (fun x => (W x).getD i false)

def sup0 (n : ℕ) (i : ℕ) : Finset (Fin n) := if h : i < n then {⟨i, h⟩} else ∅

def base (j : Fin 6) : Fin 6 → Bool :=
  fun i => decide (i = j ∨ i.val = [1, 0, 0, 0, 5, 4].getD j.val 0)

lemma st_step (n : ℕ) (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n))
    (h : St n W m Sup) (g : Gate) :
    St n (fun x => step (W x) g) (m + 1)
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

lemma st_init (n : ℕ) : St n (fun x : Fin n → Bool => List.ofFn x) n (sup0 n) := by
  refine ⟨fun x => List.length_ofFn, fun i x y hxy => ?_⟩
  show (List.ofFn x).getD i false = (List.ofFn y).getD i false
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    List.getElem?_ofFn]
  by_cases h : i < n
  · have hx := hxy ⟨i, h⟩ (by simp [sup0, h])
    simp [h, hx]
  · simp [h]

lemma sup0_card (n i : ℕ) : (sup0 n i).card ≤ 1 := by
  unfold sup0
  split <;> simp

lemma bound_step (n : ℕ) (Sup : ℕ → Finset (Fin n)) (k m : ℕ) (T : Finset ℕ)
    (hT : T.card ≤ 2) (h : ∀ Q : Finset ℕ, (Q.biUnion Sup).card ≤ Q.card + k) :
    ∀ Q : Finset ℕ,
      (Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i)).card ≤
        Q.card + (k + 1) := by
  intro Q
  by_cases hm : m ∈ Q
  · have e : Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i) =
        (T ∪ Q.erase m).biUnion Sup := by
      ext j
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
      constructor
      · rintro ⟨i, hi, hj⟩
        by_cases him : i = m
        · rw [if_pos him] at hj
          obtain ⟨t, ht, hjt⟩ := Finset.mem_biUnion.mp hj
          exact ⟨t, Or.inl ht, hjt⟩
        · rw [if_neg him] at hj
          exact ⟨i, Or.inr ⟨him, hi⟩, hj⟩
      · rintro ⟨t, ht | ⟨htm, htQ⟩, hj⟩
        · refine ⟨m, hm, ?_⟩
          rw [if_pos rfl]
          exact Finset.mem_biUnion.mpr ⟨t, ht, hj⟩
        · refine ⟨t, htQ, ?_⟩
          rw [if_neg htm]
          exact hj
    rw [e]
    have h1 := h (T ∪ Q.erase m)
    have h2 := Finset.card_union_le T (Q.erase m)
    have h3 := Finset.card_erase_of_mem hm
    have h4 : 0 < Q.card := Finset.card_pos.mpr ⟨m, hm⟩
    omega
  · have e : Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i) =
        Q.biUnion Sup := by
      apply Finset.biUnion_congr rfl
      intro i hi
      have him : i ≠ m := fun h' => hm (h' ▸ hi)
      simp [him]
    rw [e]
    have := h Q
    omega

lemma fold_sup (n : ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n)) (k : ℕ),
      St n W m Sup → (∀ Q : Finset ℕ, (Q.biUnion Sup).card ≤ Q.card + k) →
      ∃ Sup' : ℕ → Finset (Fin n),
        (∀ i, Dep n (Sup' i) (fun x => (gs.foldl step (W x)).getD i false)) ∧
        ∀ Q : Finset ℕ, (Q.biUnion Sup').card ≤ Q.card + (k + gs.length) := by
  intro gs
  induction gs with
  | nil =>
    intro _ W m Sup k hSt hb
    exact ⟨Sup, hSt.2, fun Q => by simpa using hb Q⟩
  | cons g gs ih =>
    intro hfan W m Sup k hSt hb
    have hg := hfan g List.mem_cons_self
    have hT : g.inputs.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans hg
    obtain ⟨Sup', hdep, hb'⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      _ (m + 1) _ (k + 1) (st_step n W m Sup hSt g) (bound_step n Sup k m _ hT hb)
    refine ⟨Sup', hdep, fun Q => ?_⟩
    have := hb' Q
    simp only [List.length_cons]
    omega

lemma wit : ∀ j : Fin 6,
    ((base j 0 && base j 1) || (base j 0 && base j 2) || (base j 0 && base j 3) ||
      (base j 4 && base j 5)) = true ∧
    ((Function.update (base j) j false 0 && Function.update (base j) j false 1) ||
      (Function.update (base j) j false 0 && Function.update (base j) j false 2) ||
      (Function.update (base j) j false 0 && Function.update (base j) j false 3) ||
      (Function.update (base j) j false 4 && Function.update (base j) j false 5)) = false := by
  decide

lemma up_eval : ∀ a b c d e f : Bool,
    Circuit.eval ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩,
      ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩
      [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (e && f)) := by
  decide

lemma ofFn6 (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := rfl

end PEqualNP.Outside.L_meta_755

open PEqualNP.Outside.L_meta_755 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hfan, hsize, hC⟩
    by_contra hs
    have hlen : C.gates.length ≤ 4 := by
      have : C.size = C.gates.length := rfl
      omega
    obtain ⟨Sup, hdep, hb⟩ := fold_sup 6 C.gates (fun g hg => (hfan g hg).2) _ 6 (sup0 6) 0
      (st_init 6) (fun Q => by
        have := Finset.card_biUnion_le_card_mul Q (sup0 6) 1 (fun a _ => sup0_card 6 a)
        omega)
    have hD := hdep C.output
    have h1 := hb {C.output}
    rw [Finset.singleton_biUnion, Finset.card_singleton] at h1
    obtain ⟨j, hj⟩ : ∃ j, j ∉ Sup C.output := by
      by_contra hne
      have hall : ∀ j, j ∈ Sup C.output := fun j => by
        by_contra hj
        exact hne ⟨j, hj⟩
      have hu := Finset.eq_univ_iff_forall.mpr hall
      rw [hu] at h1
      have h6 : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
      omega
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
    refine ⟨⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩,
      ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
    · exact hs
    · intro x
      rw [ofFn6 x]
      exact up_eval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
