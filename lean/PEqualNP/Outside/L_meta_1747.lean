import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1747

def circ : PEqualNP.CircuitLowerBounds.Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 } : PEqualNP.CircuitLowerBounds.Circuit)

def inc (x y : Fin 13) : Bool := Nat.testBit 523 ((x.val + 13 - y.val) % 13)

lemma inc_iff : ∀ x y : Fin 13, (x - y ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ↔ inc x y = true := by
  decide +kernel

def ok (a b c d : Fin 13) : Bool :=
  (List.finRange 13).all fun k =>
    Nat.ble ((inc a k).toNat + (inc b k).toNat + (inc c k).toNat + (inc d k).toNat) 2

def bits (a b c d : Fin 13) : List Bool :=
  List.ofFn (fun u : Fin 13 => (u == a) || (u == b) || (u == c) || (u == d)) ++
    List.ofFn (fun v : Fin 13 => !(inc a v) && !(inc b v) && !(inc c v) && !(inc d v))

lemma main : ∀ a b c d : Fin 13, a < b → b < c → c < d → ok a b c d = true →
    circ.eval (bits a b c d) = false := by
  decide +kernel

lemma quad (Q : Finset (Fin 13)) (hQ : Q.card = 4) :
    ∃ a b c d : Fin 13, a < b ∧ b < c ∧ c < d ∧ Q = {a, b, c, d} := by
  refine ⟨Q.orderEmbOfFin hQ 0, Q.orderEmbOfFin hQ 1, Q.orderEmbOfFin hQ 2,
    Q.orderEmbOfFin hQ 3, ?_, ?_, ?_, ?_⟩
  · exact (Q.orderEmbOfFin hQ).strictMono (by decide)
  · exact (Q.orderEmbOfFin hQ).strictMono (by decide)
  · exact (Q.orderEmbOfFin hQ).strictMono (by decide)
  · ext x
    have h : x ∈ Q ↔ x ∈ Set.range (Q.orderEmbOfFin hQ) := by
      rw [Finset.range_orderEmbOfFin]; rfl
    rw [h, Set.mem_range, Fin.exists_fin_succ, Fin.exists_fin_succ, Fin.exists_fin_succ,
      Fin.exists_fin_succ]
    simp only [Finset.mem_insert, Finset.mem_singleton, IsEmpty.exists_iff, or_false]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inr (Or.inr h.symm))
    · rintro (h | h | h | h)
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inr (Or.inr h.symm))

lemma last (Q : Finset (Fin 13)) (hQ : Q.card = 4)
    (hk : ∀ k : Fin 13,
      (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) :
    circ.eval (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q))
      ++ List.ofFn (fun v2 : Fin 13 =>
        decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, rfl⟩ := quad Q hQ
  have hac := hab.trans hbc
  have hbd := hbc.trans hcd
  have had := hac.trans hcd
  have hok : ok a b c d = true := by
    unfold ok
    rw [List.all_eq_true]
    intro k _
    have h := hk k
    rw [Finset.card_filter, Finset.sum_insert (by simp [hab.ne, hac.ne, had.ne]),
      Finset.sum_insert (by simp [hbc.ne, hbd.ne]), Finset.sum_insert (by simp [hcd.ne]),
      Finset.sum_singleton] at h
    simp only [inc_iff] at h
    apply Nat.ble_eq.mpr
    revert h
    cases inc a k <;> cases inc b k <;> cases inc c k <;> cases inc d k <;> simp
  have hb : (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ ({a, b, c, d} : Finset (Fin 13))))
      ++ List.ofFn (fun v2 : Fin 13 =>
        decide (∀ r ∈ ({a, b, c, d} : Finset (Fin 13)),
          r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = bits a b c d := by
    have h1 : ∀ u : Fin 13, decide (u ∈ ({a, b, c, d} : Finset (Fin 13)))
        = ((u == a) || (u == b) || (u == c) || (u == d)) := by
      intro u
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true,
        beq_iff_eq, or_assoc]
    have h2 : ∀ v : Fin 13, decide (∀ r ∈ ({a, b, c, d} : Finset (Fin 13)),
          r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13)))
        = (!(inc a v) && !(inc b v) && !(inc c v) && !(inc d v)) := by
      intro v
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq,
        inc_iff, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true, and_assoc]
    unfold bits
    rw [funext h1, funext h2]
  rw [hb]
  exact main a b c d hab hbc hcd hok

end PEqualNP.Outside.L_meta_1747

theorem PEqualNP.Outside.L_meta_1747 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 23 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
     C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l)))
       = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 1), (2, 2), (5, 4)] : List (ℕ × ℕ)))) ∧
  (∀ Q : Finset (Fin 13), Q.card = 4 →
     (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
     C.eval (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q))
             ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) := by
  intro C hC
  subst hC
  refine ⟨rfl, by decide +kernel, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> simp
  · intro Q hQ hk
    exact PEqualNP.Outside.L_meta_1747.last Q hQ hk
