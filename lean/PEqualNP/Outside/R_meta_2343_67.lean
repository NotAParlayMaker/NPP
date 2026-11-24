import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A point set with no three collinear is an arc. The bidirectional incidence
-- tests below distinguish its point constraint from the dual line constraint.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2343_67
    (extend_arc :
      let d : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ P L : Finset (Fin 13),
        (∀ p ∈ P, ∀ l ∈ L, p - l ∉ d) →
        (∀ l : Fin 13, (P.filter (fun p => p - l ∈ d)).card ≤ 2) →
        L.card ≤ 3 → (∀ p : Fin 13, (L.filter (fun l => p - l ∈ d)).card ≤ 2) →
        ∃ Q : Finset (Fin 13), P ⊆ Q ∧ Q.card = 4 ∧
          (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ d)).card ≤ 2) ∧
          (∀ l ∈ L, ∀ p ∈ Q, p - l ∉ d))
    (interval_bound :
      let d : Finset (Fin 13) := {0, 1, 3, 9}
      let hit := fun P L : Finset (Fin 13) => ∃ p ∈ P, ∃ l ∈ L, p - l ∈ d
      ∀ (C : Circuit) (s : List ℕ), s.length ≤ 2 → Monotone2 C →
        (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val) →
        let f := fun P L : Finset (Fin 13) =>
          let v := (List.ofFn fun p : Fin 13 => decide (p ∈ P)) ++
            List.ofFn fun l : Fin 13 => decide (l ∈ L)
          C.eval (v ++ [s.any fun i => v.getD i false])
        (∀ P L, hit P L → f P L = true) →
        (∀ P L, f P L = true → hit P L ∨
          (∃ l : Fin 13, 2 < (P.filter (fun p => p - l ∈ d)).card) ∨
          3 < L.card ∨ ∃ p : Fin 13, 2 < (L.filter (fun l => p - l ∈ d)).card) →
        63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  have monotone_eval : ∀ (C : Circuit) (s : List ℕ), Monotone2 C →
        Monotone (fun A : Finset (Fin 13) × Finset (Fin 13) =>
          let v := (List.ofFn fun p : Fin 13 => decide (p ∈ A.1)) ++
            List.ofFn fun l : Fin 13 => decide (l ∈ A.2)
          C.eval (v ++ [s.any fun i => v.getD i false])) := by
    intro C s hm A B hAB
    let R := fun a b : Bool => a = true → b = true
    have bits {U V : Finset (Fin 13)} (h : U ⊆ V) :
        List.Forall₂ R (List.ofFn fun p : Fin 13 => decide (p ∈ U))
          (List.ofFn fun p : Fin 13 => decide (p ∈ V)) := by
      apply List.forall₂_of_length_eq_of_get (by simp)
      intro i hu hv
      change _ = true → _ = true
      simp only [List.get_eq_getElem, List.getElem_ofFn, decide_eq_true_eq]
      exact fun hx => h hx
    have read {u v : List Bool} (hr : List.Forall₂ R u v) (j : ℕ) :
        R (u.getD j false) (v.getD j false) := by
      by_cases hu : j < u.length
      · have hv : j < v.length := hr.length_eq ▸ hu
        rw [List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hv]
        exact hr.get hu hv
      · have hv : v.length ≤ j := hr.length_eq ▸ Nat.le_of_not_lt hu
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu), List.getD_eq_default _ _ hv]
        exact id
    have gates (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
        (u v : List Bool) (huv : List.Forall₂ R u v) :
        List.Forall₂ R ((Circuit.mk gs 0).wires u) ((Circuit.mk gs 0).wires v) := by
      induction gs generalizing u v with
      | nil => exact huv
      | cons g gs ih =>
        apply ih (fun k hk => ops k (List.mem_cons_of_mem g hk))
        apply List.rel_append huv
        apply List.Forall₂.cons _ List.Forall₂.nil
        have step (i : ℕ) := read huv i
        rcases ops g List.mem_cons_self with ha | ho
        · rw [ha]
          change (g.inputs.map (fun i => u.getD i false)).all id = true →
            (g.inputs.map (fun i => v.getD i false)).all id = true
          simp only [List.all_map, Function.comp_def, id_eq, List.all_eq_true]
          exact fun hh i hi => step i (hh i hi)
        · rw [ho]
          change (g.inputs.map (fun i => u.getD i false)).any id = true →
            (g.inputs.map (fun i => v.getD i false)).any id = true
          simp only [List.any_map, Function.comp_def, id_eq, List.any_eq_true]
          rintro ⟨i, hi, ht⟩
          exact ⟨i, hi, step i ht⟩
    have raw := List.rel_append (bits hAB.1) (bits hAB.2)
    let v := fun T : Finset (Fin 13) × Finset (Fin 13) => (List.ofFn fun p : Fin 13 => decide (p ∈ T.1)) ++ List.ofFn fun l : Fin 13 => decide (l ∈ T.2)
    have extra : R (s.any fun i => (v A).getD i false) (s.any fun i => (v B).getD i false) := by
      change _ = true → _ = true
      simp only [List.any_eq_true]
      rintro ⟨i, hi, ht⟩
      exact ⟨i, hi, read raw i ht⟩
    have all := List.rel_append raw (List.Forall₂.cons extra List.Forall₂.nil)
    exact Bool.le_iff_imp.mpr (read (gates C.gates (fun g hg => (hm g hg).1) _ _ all) C.output)
  intro C s hs hm hback
  dsimp only
  intro pos neg
  let d : Finset (Fin 13) := {0, 1, 3, 9}
  let f := fun P L : Finset (Fin 13) =>
    let v := (List.ofFn fun p : Fin 13 => decide (p ∈ P)) ++
      List.ofFn fun l : Fin 13 => decide (l ∈ L)
    C.eval (v ++ [s.any fun i => v.getD i false])
  have mono : Monotone (fun A : Finset (Fin 13) × Finset (Fin 13) => f A.1 A.2) :=
    monotone_eval C s hm
  refine interval_bound C s hs hm hback ?_ ?_
  · intro P L hh
    obtain ⟨p, hp, l, hl, hpl⟩ := hh
    have one : f {p} {l} = true := by
      simpa only [f, Finset.mem_singleton] using pos p l hpl
    have inc : (({p}, {l}) : Finset (Fin 13) × Finset (Fin 13)) ≤ (P, L) :=
      ⟨Finset.singleton_subset_iff.mpr hp, Finset.singleton_subset_iff.mpr hl⟩
    have both : f {p} {l} ≤ f P L := @mono ({p}, {l}) (P, L) inc
    change f P L = true
    exact (Bool.le_iff_imp.mp both) one
  · intro P L yes
    change f P L = true at yes
    by_contra absent
    have dis : ∀ p ∈ P, ∀ l ∈ L, p - l ∉ d :=
      fun p hp l hl hpl => absent (Or.inl ⟨p, hp, l, hl, hpl⟩)
    have arc (l : Fin 13) : (P.filter (fun p => p - l ∈ d)).card ≤ 2 :=
      le_of_not_gt (fun h => absent (Or.inr (Or.inl ⟨l, h⟩)))
    have small : L.card ≤ 3 := le_of_not_gt (fun h => absent (Or.inr (Or.inr (Or.inl h))))
    have dual (p : Fin 13) : (L.filter (fun l => p - l ∈ d)).card ≤ 2 :=
      le_of_not_gt (fun h => absent (Or.inr (Or.inr (Or.inr ⟨p, h⟩))))
    obtain ⟨Q, sub, four, qarc, avoids⟩ := extend_arc P L dis arc small dual
    let E := Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ Q, p - l ∉ d)
    have subE : L ⊆ E := fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ l, avoids l hl⟩
    have zero : f Q E = false := by
      simpa only [f, E, Finset.mem_filter, Finset.mem_univ, true_and] using neg Q ⟨four, qarc⟩
    have both : f P L ≤ f Q E := @mono (P, L) (Q, E) (show (P, L) ≤ (Q, E) from ⟨sub, subE⟩)
    exact Bool.noConfusion (zero.symm.trans ((Bool.le_iff_imp.mp both) yes))
