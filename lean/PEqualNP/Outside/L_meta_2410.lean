import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2410

section Sec2409

namespace P2409


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def Stp (n : ℕ) (C : Circuit) (ra rb : ℕ) : Prop :=
  ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (gateAt C rj).op = GateOp.or ∧
    ra ∈ (gateAt C rj).inputs

abbrev Rr (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (Stp n C)

theorem base_or (n : ℕ) (C : Circuit) {a b : ℕ} (h : Rr n C a b) : a = b ∨ n ≤ b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs _ =>
    obtain ⟨_, rj, rfl, _⟩ := hs
    exact Or.inr (Nat.le_add_right _ _)

theorem in_two {l : List ℕ} (hl : l.length = 2) {w : ℕ} (hw : w ∈ l) :
    w = l.getD 0 0 ∨ w = l.getD 1 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hw ⊢
    exact hw
  · simp at hl

theorem gate_mem (C : Circuit) {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem charge (n N : ℕ) (C : Circuit) (pw : Fin N → ℕ)
    (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hpi : Function.Injective pw) (hpn : ∀ p, pw p < n) (p : Fin N) :
    ∀ w, Rr n C (pw p) w →
      (∀ r, Rr n C (pw r) w → r = p) ∨
      ∃ j, ∃ b : Bool, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
        Rr n C (pw p) ((gateAt C j).inputs.getD (cond b 1 0) 0) ∧
        (∀ r, Rr n C (pw r) ((gateAt C j).inputs.getD (cond b 1 0) 0) → r = p) ∧
        (∃ r, r ≠ p ∧ Rr n C (pw r) (n + j)) ∧ Rr n C (pw p) (n + j) ∧ Rr n C (n + j) w := by
  intro w hw
  induction hw with
  | refl =>
    left
    intro r hr
    rcases base_or n C hr with h | h
    · exact hpi h
    · exact absurd (hpn p) (not_lt.mpr h)
  | @tail w w2 hpw hs ih =>
    have hpw2 : Rr n C (pw p) w2 := Relation.ReflTransGen.tail hpw hs
    rcases ih with h1 | ⟨j, b, hj, hop, ha, hu, hr, hpj, hjw⟩
    · by_cases hall : ∀ r, Rr n C (pw r) w2 → r = p
      · exact Or.inl hall
      · right
        push_neg at hall
        obtain ⟨r, hr, hne⟩ := hall
        obtain ⟨hlt, rj, rfl, hrj, hop, hin⟩ := hs
        rcases in_two (hlen _ (gate_mem C hrj)) hin with h2 | h2
        · rw [h2] at hpw h1
          exact ⟨rj, false, hrj, hop, hpw, h1, ⟨r, hne, hr⟩, hpw2, Relation.ReflTransGen.refl⟩
        · rw [h2] at hpw h1
          exact ⟨rj, true, hrj, hop, hpw, h1, ⟨r, hne, hr⟩, hpw2, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨j, b, hj, hop, ha, hu, hr, hpj, Relation.ReflTransGen.tail hjw hs⟩

theorem count (n N M : ℕ) (C : Circuit) (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hpi : Function.Injective pw) (hpn : ∀ p, pw p < n)
    (hK : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (G : Set (Fin N × Fin M))
    (hG : ∀ e ∈ G, ∃ t, Rr n C (pw e.1) t ∧ (∀ q, Rr n C (pw q) t → I q e.2) ∧
      2 ≤ {r : Fin N | Rr n C (pw r) t}.ncard) :
    G.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by
  classical
  have hOf : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun j hj => hj.1)
  have hex : ∀ e ∈ G, ∃ jb : ℕ × Bool,
      jb.1 ∈ {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} ∧
      Rr n C (pw e.1) ((gateAt C jb.1).inputs.getD (cond jb.2 1 0) 0) ∧
      (∀ r, Rr n C (pw r) ((gateAt C jb.1).inputs.getD (cond jb.2 1 0) 0) → r = e.1) ∧
      (∃ r, r ≠ e.1 ∧ Rr n C (pw r) (n + jb.1)) ∧ Rr n C (pw e.1) (n + jb.1) ∧
      ∀ q, Rr n C (pw q) (n + jb.1) → I q e.2 := by
    intro e he
    obtain ⟨t, hpt, hall, h2⟩ := hG e he
    have h2b : 1 < {r : Fin N | Rr n C (pw r) t}.ncard := h2
    rw [Set.one_lt_ncard_iff] at h2b
    obtain ⟨q1, q2, hq1, hq2, hne⟩ := h2b
    rcases charge n N C pw hlen hpi hpn e.1 t hpt with h | ⟨j, b, hj, hop, ha, hu, hr, hpj, hjt⟩
    · exact absurd ((h q1 hq1).trans (h q2 hq2).symm) hne
    · exact ⟨(j, b), ⟨hj, hop⟩, ha, hu, hr, hpj, fun q hq => hall q (hq.trans hjt)⟩
  choose! f hf using hex
  calc G.ncard
      ≤ (((fun j : ℕ => (j, true)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}) ∪
          ((fun j : ℕ => (j, false)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or})).ncard := by
        refine Set.ncard_le_ncard_of_injOn f ?_ ?_ ((hOf.image _).union (hOf.image _))
        · intro e he
          have hm := (hf e he).1
          rcases hfe : f e with ⟨j, b⟩
          rw [hfe] at hm
          cases b
          · right
            exact ⟨j, hm, rfl⟩
          · left
            exact ⟨j, hm, rfl⟩
        · intro e he e2 he2 heq
          have h1 := hf e he
          have h2 := hf e2 he2
          rw [← heq] at h2
          obtain ⟨_, ha, hu, ⟨r, hr, hrj⟩, hpj, hI⟩ := h1
          obtain ⟨_, ha2, hu2, _, hpj2, hI2⟩ := h2
          have e1 : e2.1 = e.1 := hu _ ha2
          have e3 : e.2 = e2.2 := by
            by_contra hne
            exact hK e.1 r e.2 e2.2 (Ne.symm hr) hne ⟨hI _ hpj, hI _ hrj, hI2 _ hpj, hI2 _ hrj⟩
          exact Prod.ext e1.symm e3
    _ ≤ ((fun j : ℕ => (j, true)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}).ncard +
          ((fun j : ℕ => (j, false)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}).ncard :=
        Set.ncard_union_le _ _
    _ ≤ {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard +
          {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard :=
        Nat.add_le_add (Set.ncard_image_le hOf) (Set.ncard_image_le hOf)
    _ = 2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by ring

theorem t_mem (n : ℕ) (C : Circuit) (R : ℕ → ℕ → Prop) (tt : ℕ) (tL : List (ℕ × ℕ))
    (h : ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
      (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) →
      (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
        (gateAt C qj).op = GateOp.and → R (n + qj) qt →
        Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
        Q qt (qL1 ++ qL2)) → Q tt tL) :
    ∀ g ∈ tL, R g.2 g.1 := by
  refine h (fun _ L => ∀ g ∈ L, R g.2 g.1) ?_ ?_
  · intro qv qt _ hR g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact hR
  · intro qj qt L1 L2 _ _ _ h1 h2 g hg
    rcases List.mem_append.mp hg with h | h
    · exact h1 g h
    · exact h2 g h

theorem split {α : Type} [Finite α] (E X : α → Prop) (k : ℕ)
    (h : {e : α | E e ∧ X e}.ncard ≤ k) :
    {e : α | E e}.ncard ≤ k + {e : α | E e ∧ ¬ X e}.ncard := by
  have hsub : {e : α | E e} ⊆ {e : α | E e ∧ X e} ∪ {e : α | E e ∧ ¬ X e} := by
    intro e he
    by_cases hx : X e
    · exact Or.inl ⟨he, hx⟩
    · exact Or.inr ⟨he, hx⟩
  calc {e : α | E e}.ncard
      ≤ ({e : α | E e ∧ X e} ∪ {e : α | E e ∧ ¬ X e}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {e : α | E e ∧ X e}.ncard + {e : α | E e ∧ ¬ X e}.ncard := Set.ncard_union_le _ _
    _ ≤ k + {e : α | E e ∧ ¬ X e}.ncard := Nat.add_le_add_right h _


end P2409

theorem s2409 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard := by
  intro n N M pw lw I C hC hpi hli hdisj hpn hln hK hsound R hR T hT hH
  subst hR
  subst hT
  refine PEqualNP.Outside.L_meta_2410.P2409.split _ _ _ ?_
  refine PEqualNP.Outside.L_meta_2410.P2409.count n N M C pw I hC.2.2 hpi hpn hK _ ?_
  intro e he
  obtain ⟨hI, L7, ⟨j7, La, Lb, hj, hop, hRo, hTa, hTb, hL⟩, hlab, hc1, hc2, g8, hg8, hg8p, hall, h2⟩ := he
  refine ⟨g8.1, ?_, hall, h2⟩
  rw [hL] at hg8
  rcases List.mem_append.mp hg8 with h | h
  · have hm := PEqualNP.Outside.L_meta_2410.P2409.t_mem n C _ _ _ hTa g8 h
    rw [hg8p] at hm
    exact hm
  · have hm := PEqualNP.Outside.L_meta_2410.P2409.t_mem n C _ _ _ hTb g8 h
    rw [hg8p] at hm
    exact hm

end Sec2409

theorem one_type {α : Type} [Finite α] (J Px Py : α → Prop) (k : ℕ)
    (h1 : {e : α | J e}.ncard ≤ 2 * k + {e : α | J e ∧ ¬ Px e}.ncard)
    (h2 : {e : α | J e}.ncard ≤ 2 * k + {e : α | J e ∧ ¬ Py e}.ncard) :
    {e : α | J e}.ncard ≤ 4 * k + {e : α | J e ∧ ¬ Px e ∧ ¬ Py e}.ncard := by
  have hX : {e : α | J e ∧ ¬ Px e} ⊆ {e : α | J e} := fun e he => he.1
  have hY : {e : α | J e ∧ ¬ Py e} ⊆ {e : α | J e} := fun e he => he.1
  have dX := Set.ncard_sdiff_add_ncard_of_subset hX (Set.toFinite _)
  have dY := Set.ncard_sdiff_add_ncard_of_subset hY (Set.toFinite _)
  have hsub : {e : α | J e} ⊆ (({e : α | J e} \ {e : α | J e ∧ ¬ Px e}) ∪
      ({e : α | J e} \ {e : α | J e ∧ ¬ Py e})) ∪ {e : α | J e ∧ ¬ Px e ∧ ¬ Py e} := by
    intro e he
    by_cases hx : Px e
    · exact Or.inl (Or.inl ⟨he, fun h => h.2 hx⟩)
    · by_cases hy : Py e
      · exact Or.inl (Or.inr ⟨he, fun h => h.2 hy⟩)
      · exact Or.inr ⟨he, hx, hy⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hu1 := Set.ncard_union_le (({e : α | J e} \ {e : α | J e ∧ ¬ Px e}) ∪
      ({e : α | J e} \ {e : α | J e ∧ ¬ Py e})) {e : α | J e ∧ ¬ Px e ∧ ¬ Py e}
  have hu2 := Set.ncard_union_le ({e : α | J e} \ {e : α | J e ∧ ¬ Px e})
      ({e : α | J e} \ {e : α | J e ∧ ¬ Py e})
  omega

theorem comb {α β : Type} [Finite α] [Finite β] (J Px Py : α → Prop) (J2 Py2 : β → Prop)
    (f : α ≃ β) (hJ : ∀ a, J2 (f a) ↔ J a) (hP : ∀ a, Py2 (f a) ↔ Py a) (k : ℕ)
    (h1 : {e : α | J e}.ncard ≤ 2 * k + {e : α | J e ∧ ¬ Px e}.ncard)
    (h2 : {e : β | J2 e}.ncard ≤ 2 * k + {e : β | J2 e ∧ ¬ Py2 e}.ncard) :
    {e : α | J e}.ncard ≤ 4 * k + {e : α | J e ∧ ¬ Px e ∧ ¬ Py e}.ncard := by
  have e1 : {e : β | J2 e}.ncard = {e : α | J e}.ncard := by
    rw [← Set.ncard_image_of_injective {e : α | J e} f.injective]
    congr 1
    ext b
    constructor
    · intro hb
      refine ⟨f.symm b, ?_, by simp⟩
      have := hJ (f.symm b)
      simp only [Equiv.apply_symm_apply] at this
      exact this.1 hb
    · rintro ⟨a, ha, rfl⟩
      exact (hJ a).2 ha
  have e2 : {e : β | J2 e ∧ ¬ Py2 e}.ncard = {e : α | J e ∧ ¬ Py e}.ncard := by
    rw [← Set.ncard_image_of_injective {e : α | J e ∧ ¬ Py e} f.injective]
    congr 1
    ext b
    constructor
    · intro hb
      refine ⟨f.symm b, ?_, by simp⟩
      have h3 := hJ (f.symm b)
      have h4 := hP (f.symm b)
      simp only [Equiv.apply_symm_apply] at h3 h4
      exact ⟨h3.1 hb.1, fun h => hb.2 (h4.2 h)⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(hJ a).2 ha.1, fun h => ha.2 ((hP a).1 h)⟩
  rw [e1, e2] at h2
  exact one_type J Px Py k h1 h2

theorem main : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 4 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ey : Fin N × Fin M | I ey.1 ey.2 ∧ (¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ey.1 ∨ g7.2 = lw ey.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ey.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ey.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ey.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ey.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard) ∧ ¬ ∃ L9 : List (ℕ × ℕ), (∃ (j9 : ℕ) (La9 Lb9 : List (ℕ × ℕ)), j9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j9) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j9).inputs.getD 0 0) La9 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j9).inputs.getD 1 0) Lb9 ∧ L9 = La9 ++ Lb9) ∧ (∀ g9 ∈ L9, g9.2 = pw ey.1 ∨ g9.2 = lw ey.2) ∧ (L9.filter (fun e9 => decide (e9.2 = pw ey.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L9.filter (fun f9 => decide (f9.2 = lw ey.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g10 ∈ L9, g10.2 = lw ey.2 ∧ (∀ q10 : Fin M, R (lw q10) g10.1 → I ey.1 q10) ∧ 2 ≤ {r10 : Fin M | R (lw r10) g10.1}.ncard}.ncard := by
  intro n N M pw lw I C hC hpw hlw hd hpn hln h4 hs R hR T hT htree
  have h1 := s2409 n N M pw lw I C hC hpw hlw hd hpn hln h4 hs R hR T hT htree
  have h2 := s2409 n M N lw pw (fun l p => I p l) C hC hlw hpw (fun l p => (hd p l).symm) hln hpn
    (fun l4 l5 p4 p5 hl hp h => h4 p4 p5 l4 l5 hp hl ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩)
    (fun P Y hP hY hno => by
      have h := hs Y P hY hP (fun p hp l hl => hno l hl p hp)
      rw [Finset.union_comm]
      exact h)
    R hR T hT
    (fun l p hI => by
      obtain ⟨L, hr, ha, c1, c2⟩ := htree p l hI
      exact ⟨L, hr, fun g hg => (ha g hg).symm, c2, c1⟩)
  refine comb _ _ _ _ _ (Equiv.prodComm (Fin N) (Fin M)) ?_ ?_ _ h1 h2
  · intro a
    exact Iff.rfl
  · intro a
    constructor
    · rintro ⟨L, hr, ha, c1, c2, hx⟩
      exact ⟨L, hr, fun g hg => (ha g hg).symm, c2, c1, hx⟩
    · rintro ⟨L, hr, ha, c1, c2, hx⟩
      exact ⟨L, hr, fun g hg => (ha g hg).symm, c2, c1, hx⟩

end PEqualNP.Outside.L_meta_2410

theorem PEqualNP.Outside.L_meta_2410 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 4 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ey : Fin N × Fin M | I ey.1 ey.2 ∧ (¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ey.1 ∨ g7.2 = lw ey.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ey.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ey.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ey.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ey.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard) ∧ ¬ ∃ L9 : List (ℕ × ℕ), (∃ (j9 : ℕ) (La9 Lb9 : List (ℕ × ℕ)), j9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j9) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j9).inputs.getD 0 0) La9 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j9).inputs.getD 1 0) Lb9 ∧ L9 = La9 ++ Lb9) ∧ (∀ g9 ∈ L9, g9.2 = pw ey.1 ∨ g9.2 = lw ey.2) ∧ (L9.filter (fun e9 => decide (e9.2 = pw ey.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L9.filter (fun f9 => decide (f9.2 = lw ey.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g10 ∈ L9, g10.2 = lw ey.2 ∧ (∀ q10 : Fin M, R (lw q10) g10.1 → I ey.1 q10) ∧ 2 ≤ {r10 : Fin M | R (lw r10) g10.1}.ncard}.ncard :=
  PEqualNP.Outside.L_meta_2410.main
