import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_2409

private def OrGates (C : Circuit) : Set ℕ :=
  {j | j < C.gates.length ∧ (gateAt C j).op = .or}

private def OrStep (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ j, b = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = .or ∧
    a ∈ (gateAt C j).inputs

private abbrev Reach (n : ℕ) (C : Circuit) := Relation.ReflTransGen (OrStep n C)

private def Trace (n : ℕ) (C : Circuit) (w : ℕ) (leaves : List (ℕ × ℕ)) : Prop :=
  ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
    (∀ i root, i < n → Reach n C i root → Q root [(root, i)]) →
    (∀ j root left right, j < C.gates.length → (gateAt C j).op = .and →
      Reach n C (n + j) root → Q ((gateAt C j).inputs.getD 0 0) left →
      Q ((gateAt C j).inputs.getD 1 0) right → Q root (left ++ right)) → Q w leaves

private theorem leafReach {n : ℕ} {C : Circuit} {w : ℕ} {leaves : List (ℕ × ℕ)}
    (h : Trace n C w leaves) : ∀ e ∈ leaves, Reach n C e.2 e.1 := by
  apply h (fun _ L => ∀ e ∈ L, Reach n C e.2 e.1)
  · intro i root _ path e he
    obtain rfl := List.mem_singleton.mp he
    exact path
  · intro _ _ _ _ _ _ _ left right e he
    exact (List.mem_append.mp he).elim (left e) (right e)

private def Shadow {N : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (w : ℕ) : Set (Fin N) :=
  {p | Reach n C (pw p) w}

private theorem firstLarge {n : ℕ} {C : Circuit} {a b : ℕ} (large : ℕ → Prop)
    (path : Reach n C a b) (start : ¬ large a) (finish : large b) :
    ∃ u v, Reach n C a u ∧ OrStep n C u v ∧ ¬ large u ∧ large v ∧ Reach n C v b := by
  classical
  induction path with
  | refl => exact (start finish).elim
  | @tail c d path edge ih =>
    by_cases hc : large c
    · obtain ⟨u, v, hu, huv, hsmall, hlarge, hvc⟩ := ih hc
      exact ⟨u, v, hu, huv, hsmall, hlarge, hvc.tail edge⟩
    · exact ⟨c, d, path, edge, hc, finish, .refl⟩

private theorem charge {n N M : ℕ} {C : Circuit} {pw : Fin N → ℕ}
    {I : Fin N → Fin M → Prop} {S : Set (Fin N × Fin M)}
    (two : PEqualNP.TopForm.IsAO2 n C) (distinct : Function.Injective pw)
    (inputWire : ∀ p, pw p < n)
    (rectangle : ∀ p q l m, p ≠ q → l ≠ m → ¬ (I p l ∧ I q l ∧ I p m ∧ I q m))
    (roots : ∀ e ∈ S, ∃ w, e.1 ∈ Shadow n C pw w ∧ 2 ≤ (Shadow n C pw w).ncard ∧
      ∀ q ∈ Shadow n C pw w, I q e.2) : S.ncard ≤ 2 * (OrGates C).ncard := by
  classical
  let large (w : ℕ) := 2 ≤ (Shadow n C pw w).ncard
  have start (p : Fin N) : ¬ large (pw p) := by
    have onlyPoint : ∀ q ∈ Shadow n C pw (pw p), q = p := by
      intro q hq
      change Reach n C (pw q) (pw p) at hq
      rcases hq.cases_tail with eq | ⟨_, _, _, j, eq, _, _, _⟩
      · exact distinct eq.symm
      · have hp := inputWire p
        omega
    have one : (Shadow n C pw (pw p)).ncard ≤ 1 := by
      apply (Set.ncard_le_one (Set.toFinite _)).2
      intro a ha b hb
      exact (onlyPoint a ha).trans (onlyPoint b hb).symm
    change ¬ 2 ≤ (Shadow n C pw (pw p)).ncard
    omega
  let wire (c : OrGates C × Fin 2) := (gateAt C c.1.val).inputs.getD c.2.val 0
  let root (c : OrGates C × Fin 2) := n + c.1.val
  have choices (e : S) : ∃ c : OrGates C × Fin 2,
      e.val.1 ∈ Shadow n C pw (wire c) ∧ ¬ large (wire c) ∧ large (root c) ∧
        ∀ q ∈ Shadow n C pw (root c), I q e.val.2 := by
    obtain ⟨w, reach, big, tight⟩ := roots e.val e.property
    obtain ⟨u, v, hu, edge, hsmall, hbig, hv⟩ := firstLarge large reach (start e.val.1) big
    obtain ⟨_, j, rfl, hj, hor, member⟩ := edge
    have real : gateAt C j ∈ C.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have len := two.2.2 _ real
    obtain ⟨i, hi, reads⟩ := List.mem_iff_getElem.mp member
    let code : OrGates C × Fin 2 := (⟨j, hj, hor⟩, ⟨i, by omega⟩)
    have hwire : wire code = u := (List.getD_eq_getElem _ _ hi).trans reads
    refine ⟨code, ?_, ?_, hbig, ?_⟩
    · rwa [hwire]
    · rwa [hwire]
    · intro q hq
      exact tight q (Relation.ReflTransGen.trans hq hv)
  choose code details using choices
  have injective : Function.Injective code := by
    intro e f eq
    obtain ⟨he, hsmall, hbig, tightE⟩ := details e
    have hfAll := details f
    rw [← eq] at hfAll
    obtain ⟨hf, _, _, tightF⟩ := hfAll
    have smallCard : (Shadow n C pw (wire (code e))).ncard ≤ 1 := by
      change ¬ 2 ≤ (Shadow n C pw (wire (code e))).ncard at hsmall
      omega
    have pointEq : e.val.1 = f.val.1 := ((Set.ncard_le_one (Set.toFinite _)).mp smallCard) _ he _ hf
    change 1 < (Shadow n C pw (root (code e))).ncard at hbig
    obtain ⟨p, hp, q, hq, diff⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp hbig
    have lineEq : e.val.2 = f.val.2 := by
      by_contra different
      exact rectangle p q e.val.2 f.val.2 diff different
        ⟨tightE p hp, tightE q hq, tightF p hp, tightF q hq⟩
    exact Subtype.ext (Prod.ext pointEq lineEq)
  have finiteGates : (OrGates C).Finite := (Set.finite_lt_nat C.gates.length).subset
    (fun _ h => h.1)
  let gateTypeFinite : Finite (OrGates C) := finiteGates.to_subtype
  have cardBound := Nat.card_le_card_of_injective code injective
  rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fin, Nat.mul_comm] at cardBound
  exact cardBound

private def Qualified {N M : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ L : List (ℕ × ℕ),
    (∃ j La Lb, j < C.gates.length ∧ (gateAt C j).op = .and ∧ Reach n C (n + j) C.output ∧
      Trace n C ((gateAt C j).inputs.getD 0 0) La ∧
      Trace n C ((gateAt C j).inputs.getD 1 0) Lb ∧ L = La ++ Lb) ∧
    (∀ g ∈ L, g.2 = pw p ∨ g.2 = lw l) ∧
    (L.filter (fun e => decide (e.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧
    (L.filter (fun e => decide (e.2 = lw l))).length ∈ ({1, 2} : Finset ℕ) ∧
    ∃ g ∈ L, g.2 = pw p ∧ (∀ q, Reach n C (pw q) g.1 → I q l) ∧
      2 ≤ (Shadow n C pw g.1).ncard

private theorem bound {n N M : ℕ} {C : Circuit} {pw : Fin N → ℕ} {lw : Fin M → ℕ}
    {I : Fin N → Fin M → Prop}
    (two : PEqualNP.TopForm.IsAO2 n C) (distinct : Function.Injective pw)
    (inputWire : ∀ p, pw p < n)
    (rectangle : ∀ p q l m, p ≠ q → l ≠ m → ¬ (I p l ∧ I q l ∧ I p m ∧ I q m)) :
    {e : Fin N × Fin M | I e.1 e.2}.ncard ≤ 2 * (OrGates C).ncard +
      {e : Fin N × Fin M | I e.1 e.2 ∧ ¬ Qualified n C pw lw I e.1 e.2}.ncard := by
  classical
  let good : Set (Fin N × Fin M) := {e | I e.1 e.2 ∧ Qualified n C pw lw I e.1 e.2}
  let bad : Set (Fin N × Fin M) := {e | I e.1 e.2 ∧ ¬ Qualified n C pw lw I e.1 e.2}
  have roots : ∀ e ∈ good, ∃ w, e.1 ∈ Shadow n C pw w ∧ 2 ≤ (Shadow n C pw w).ncard ∧
      ∀ q ∈ Shadow n C pw w, I q e.2 := by
    intro e h
    obtain ⟨L, ⟨_, La, Lb, _, _, _, left, right, rfl⟩, _, _, _, g, hg, eq, tight, big⟩ := h.2
    have path : Reach n C g.2 g.1 := (List.mem_append.mp hg).elim (leafReach left g) (leafReach right g)
    rw [eq] at path
    exact ⟨g.1, path, big, tight⟩
  have edges : {e : Fin N × Fin M | I e.1 e.2} ⊆ good ∪ bad := by
    intro e h
    by_cases hq : Qualified n C pw lw I e.1 e.2
    · exact Or.inl ⟨h, hq⟩
    · exact Or.inr ⟨h, hq⟩
  exact (Set.ncard_le_ncard edges).trans ((Set.ncard_union_le good bad).trans
    (Nat.add_le_add_right (charge two distinct inputWire rectangle roots) bad.ncard))

end PEqualNP.Outside.L_meta_2409

theorem PEqualNP.Outside.L_meta_2409 :
    ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard := by
  intro n N M pw lw I C two distinct _ _ inputWire _ rectangle _ R hR T hT _
  subst R
  subst T
  exact PEqualNP.Outside.L_meta_2409.bound two distinct inputWire rectangle
