import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_2974_2256
    (support :
      ∀ (n : ℕ) (C : Circuit), (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
        ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
          ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) →
            circuitFun n C x = circuitFun n C y)
    (sparse :
      ∀ (A B : Type) [Fintype A] [Fintype B] (J : A → B → Prop) [DecidableRel J],
        (∀ (a a' : A) (b b' : B), a ≠ a' →
          J a b → J a' b → J a b' → J a' b' → b = b') →
        Fintype.card A ≤ 2256 →
        Fintype.card {e : A × B // J e.1 e.2} ≤
          24 * (Fintype.card A + Fintype.card B - 1))
    (large : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → (4513 : ℕ) ≤ x5.size → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  classical
  intro q N I dec C hq hn hlines huniq hAO hsound
  by_cases big : 4513 ≤ C.size
  · exact @large q N I dec C hq hn hlines huniq hAO hsound big
  obtain ⟨S, hsmall, hdep⟩ := support (N + N) C
    (fun g hg => le_of_eq (hAO.2.2 g hg))
  let P := {p : Fin N // Fin.castAdd N p ∈ S}
  let L := {l : Fin N // Fin.natAdd N l ∈ S}
  have disjointPins (p l : Fin N) : (Fin.castAdd N p : Fin (N + N)) ≠ Fin.natAdd N l := by
    intro eq
    have he := congrArg Fin.val eq
    change p.val = N + l.val at he
    have := p.isLt
    omega
  have pointInj : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) :=
    (Fin.castAddEmb N).injective
  have lineInj : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) :=
    (Fin.natAddEmb N).injective
  let packed : P ⊕ L → ↥S := Sum.elim
    (fun p => ⟨Fin.castAdd N p.val, p.property⟩)
    (fun l => ⟨Fin.natAdd N l.val, l.property⟩)
  have packedInj : Function.Injective packed := by
    rintro (p | l) (r | m) h
    · exact congrArg Sum.inl (Subtype.ext (pointInj (congrArg Subtype.val h)))
    · exact (disjointPins p.val m.val (congrArg Subtype.val h)).elim
    · exact (disjointPins r.val l.val (congrArg Subtype.val h).symm).elim
    · exact congrArg Sum.inr (Subtype.ext (lineInj (congrArg Subtype.val h)))
  have slots := Fintype.card_le_of_injective packed packedInj
  rw [Fintype.card_sum, Fintype.card_coe] at slots
  let lone (v : Fin (N + N)) (i : Fin (N + N)) : Bool := decide (i = v)
  have loneFalse (v : Fin (N + N)) : circuitFun (N + N) C (lone v) = false := by
    have one : Fintype.card {l : Fin N // lone v (Fin.natAdd N l) = true} ≤ 1 := by
      apply Fintype.card_le_one_iff_subsingleton.mpr
      constructor
      intro a b
      apply Subtype.ext
      apply lineInj
      exact (of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm
    apply hsound (lone v) (one.trans (by omega))
    rintro ⟨p, l, _, hp, hl⟩
    exact disjointPins p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  let pair (u v : Fin (N + N)) (i : Fin (N + N)) : Bool := decide (i = u ∨ i = v)
  have bothActive (u v : Fin (N + N)) (ha : circuitFun (N + N) C (pair u v) = true) :
      u ∈ S ∧ v ∈ S := by
    constructor
    · by_contra hu
      have eq := hdep (pair u v) (lone v) (fun i hi => by
        have ne : i ≠ u := fun e => hu (e ▸ hi)
        simp [pair, lone, ne])
      exact Bool.noConfusion (ha.symm.trans (eq.trans (loneFalse v)))
    · by_contra hv
      have eq := hdep (pair u v) (lone u) (fun i hi => by
        have ne : i ≠ v := fun e => hv (e ▸ hi)
        simp [pair, lone, ne])
      exact Bool.noConfusion (ha.symm.trans (eq.trans (loneFalse u)))
  let E := {e : Fin N × Fin N // I e.1 e.2 ∧
    circuitFun (N + N) C (pair (Fin.castAdd N e.1) (Fin.natAdd N e.2)) = true ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false}
  change Fintype.card E ≤ 24 * C.size
  have rectangle (p r : Fin N) (l m : Fin N) (different : p ≠ r)
      (hpl : I p l) (hrl : I r l) (hpm : I p m) (hrm : I r m) : l = m := by
    obtain ⟨_, _, uniq⟩ := huniq p r different
    exact (uniq l ⟨hpl, hrl⟩).trans (uniq m ⟨hpm, hrm⟩).symm
  have finish (A B : Type) [Fintype A] [Fintype B] (J : A → B → Prop) [DecidableRel J]
      (unique : ∀ a a' b b', a ≠ a' → J a b → J a' b → J a b' → J a' b' → b = b')
      (cap : Fintype.card A ≤ 2256) (budget : Fintype.card A + Fintype.card B ≤ C.size + 1)
      (f : E → {e : A × B // J e.1 e.2}) (inj : Function.Injective f) :
      Fintype.card E ≤ 24 * C.size :=
    (Fintype.card_le_of_injective f inj).trans
      ((sparse A B J unique cap).trans (Nat.mul_le_mul_left 24 (by omega)))
  by_cases capP : Fintype.card P ≤ 2256
  · let J (p : P) (l : L) := I p.val l.val
    let f (e : E) : {a : P × L // J a.1 a.2} :=
      let h := bothActive _ _ e.property.2.1
      ⟨(⟨e.val.1, h.1⟩, ⟨e.val.2, h.2⟩), e.property.1⟩
    refine finish P L J ?_ capP (slots.trans hsmall) f ?_
    · intro p r l m pr hpl hrl hpm hrm
      exact Subtype.ext (rectangle p.val r.val l.val m.val (fun eq => pr (Subtype.ext eq))
        hpl hrl hpm hrm)
    · intro a b h
      apply Subtype.ext
      exact congrArg (fun x : {a : P × L // J a.1 a.2} => (x.val.1.val, x.val.2.val)) h
  · have capL : Fintype.card L ≤ 2256 := by omega
    let J (l : L) (p : P) := I p.val l.val
    let f (e : E) : {a : L × P // J a.1 a.2} :=
      let h := bothActive _ _ e.property.2.1
      ⟨(⟨e.val.2, h.2⟩, ⟨e.val.1, h.1⟩), e.property.1⟩
    refine finish L P J ?_ capL (by omega) f ?_
    · intro l m p r lm hpl hpm hrl hrm
      by_contra pr
      exact lm (Subtype.ext (rectangle p.val r.val l.val m.val
        (fun eq => pr (Subtype.ext eq)) hpl hrl hpm hrm))
    · intro a b h
      apply Subtype.ext
      exact congrArg (fun x : {a : L × P // J a.1 a.2} => (x.val.2.val, x.val.1.val)) h
