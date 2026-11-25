import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.PairShadow
open PEqualNP.ReadTwo

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5284_8
    (shape :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
        Monotone2 C →
        (∀ j : ℕ, (gateAt C j).op = GateOp.and →
          ∀ S : Finset (Fin n), S.card ≤ 1 →
            gateVal n C j (fun i => decide (i ∈ S)) = false) →
        ∀ j : ℕ, (gateAt C j).op = GateOp.and →
          (∀ i : ℕ, i < j → (gateAt C i).op = GateOp.and →
            ¬ ∃ a b : Fin n, InShadow n G C i a b) →
          ∃ p q : Fin n, ∃ w1 w2 : ℕ, InShadow n G C j p q ∧
            (gateAt C j).inputs.length = 2 ∧
            w1 ∈ (gateAt C j).inputs ∧ w2 ∈ (gateAt C j).inputs ∧
            (∀ z : Fin n → Bool, z p = true → wval C z w1 = true) ∧
            (∀ z : Fin n → Bool, z q = true → wval C z w2 = true) ∧
            wval C (unitInput q) w1 = false ∧ wval C (unitInput p) w2 = false)
    (repair :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
          a = c ∨ b = d) →
        ∀ C : Circuit, Monotone2 C →
          (∀ u v : Fin n, G.Adj u v →
            C.eval (List.ofFn (fun i => decide (i = u ∨ i = v))) = true) →
          (∀ u : Fin n, C.eval (List.ofFn (fun i => decide (i = u))) = false) →
          (∀ j : ℕ, (gateAt C j).op = GateOp.and →
            ∀ S : Finset (Fin n), S.card ≤ 1 →
              gateVal n C j (fun i => decide (i ∈ S)) = false) →
          ∀ (j : ℕ) (p q : Fin n),
            (gateAt C j).op = GateOp.and →
            InShadow n G C j p q →
            ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
              (∀ u v : Fin n, G.Adj u v →
                D.eval (List.ofFn (fun i => decide (i = u ∨ i = v))) = true) ∧
              (∀ u : Fin n, D.eval (List.ofFn (fun i => decide (i = u))) = false) ∧
              (∀ t : ℕ, (gateAt D t).op = GateOp.and →
                ∀ S : Finset (Fin n), S.card ≤ 1 →
                  gateVal n D t (fun i => decide (i ∈ S)) = false) ∧
              shadowCount n G D < shadowCount n G C) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = x4 x11) → x6 x9 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size ≤ x9.size ∧ (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = Bool.true) ∧ (∀ (x14 : Fin x1), x13.eval (List.ofFn (x5 {x14})) = Bool.false) ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x13.gates[x14]? = Option.some x15 → x15.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x18 : Finset (Fin x1)), x18.card ≤ (2 : ℕ) → (x13.wires (List.ofFn (x5 x18))).getD (x1 + x14) Bool.false = Bool.true → ∃ x21 ∈ x18, ∃ x22 ∈ x18, x2.Adj x21 x22
  := by
    intro n G inst
    dsimp only
    intro tri c4 C monoC hf hsafe
    letI : DecidableEq GateOp := gateOpDecEq
    let andBad (C : Circuit) : ℕ := shadowCount n G C
    let edgeP (C : Circuit) : Prop :=
      ∀ u v : Fin n, G.Adj u v →
        C.eval (List.ofFn (fun i => decide (i ∈ ({u, v} : Finset (Fin n))))) = true
    let singP (C : Circuit) : Prop :=
      ∀ u : Fin n, C.eval (List.ofFn (fun i => decide (i ∈ ({u} : Finset (Fin n))))) = false
    let safeP (C : Circuit) : Prop :=
      ∀ j : ℕ, (gateAt C j).op = GateOp.and →
        ∀ S : Finset (Fin n), S.card ≤ 1 → gateVal n C j (fun i => decide (i ∈ S)) = false
    let badP (C : Circuit) (j : ℕ) : Prop :=
      (gateAt C j).op = GateOp.and ∧ ∃ p q : Fin n, InShadow n G C j p q
    let condP (C : Circuit) : Prop :=
      ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
        ∀ S : Finset (Fin n), S.card ≤ 2 →
          (C.wires (List.ofFn (fun i => decide (i ∈ S)))).getD (n + j) false = true →
          ∃ a ∈ S, ∃ b ∈ S, G.Adj a b
    have and_lt {C : Circuit} {j : ℕ} (hop : (gateAt C j).op = GateOp.and) : j < C.gates.length := by
      by_contra hj
      have hle : C.gates.length ≤ j := Nat.not_lt.mp hj
      unfold gateAt at hop
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle, Option.getD_none] at hop
      exact GateOp.noConfusion hop
    have gate_at_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have gate_some {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
        C.gates[j]? = some (gateAt C j) := by
      rw [gate_at_eq hj]
      exact List.getElem?_eq_getElem hj
    have safe_of_hsafe : safeP C := by
      intro j hop S hS
      have hj := and_lt hop
      have h := hsafe j (gateAt C j) (gate_some hj) hop S hS
      exact h
    have edge_of_hf : edgeP C := by
      intro u v huv
      rw [hf]
      apply decide_eq_true
      refine ⟨u, v, huv, ?_, ?_⟩
      · exact decide_eq_true (Finset.mem_insert_self u {v})
      · exact decide_eq_true (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
    have sing_of_hf : singP C := by
      intro v
      rw [hf]
      apply decide_eq_false
      intro h
      refine Exists.elim h fun a rest => Exists.elim rest fun b restb => ?_
      have hab := restb.1
      have ha := restb.2.1
      have hb := restb.2.2
      have ha' : a = v := Finset.eq_of_mem_singleton (of_decide_eq_true ha)
      have hb' : b = v := Finset.eq_of_mem_singleton (of_decide_eq_true hb)
      have hloop : G.Adj a a := by
        rw [hb'.trans ha'.symm] at hab
        exact hab
      exact G.loopless.irrefl a hloop
    have pairEq (u v : Fin n) :
        (fun i => decide (i ∈ ({u, v} : Finset (Fin n)))) =
          fun i => decide (i = u ∨ i = v) := by
      funext i
      apply decide_eq_decide.mpr
      constructor
      · intro h
        refine Or.elim (Finset.mem_insert.mp h) ?_ ?_
        · intro hiu
          exact Or.inl hiu
        · intro hiv
          exact Or.inr (Finset.mem_singleton.mp hiv)
      · intro h
        refine Or.elim h ?_ ?_
        · intro hiu
          exact Finset.mem_insert.mpr (Or.inl hiu)
        · intro hiv
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hiv))
    have unitEq (u : Fin n) :
        (fun i => decide (i ∈ ({u} : Finset (Fin n)))) = fun i => decide (i = u) := by
      funext i
      apply decide_eq_decide.mpr
      constructor
      · exact Finset.mem_singleton.mp
      · exact Finset.mem_singleton.mpr
    have step :
        ∀ k (C : Circuit), Monotone2 C → edgeP C → singP C → safeP C → andBad C = k →
          ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ edgeP D ∧ singP D ∧ condP D := by
      intro k
      refine Nat.strongRecOn k ?_
      intro k ih C monoC edgeC singC safeC hk
      refine Or.elim (Classical.em (∃ j, badP C j)).symm ?clean ?bad
      · intro hclean
        refine ⟨C, monoC, le_rfl, edgeC, singC, ?_⟩
        intro j g hg hop S hS htrue
        refine Exists.elim (List.getElem?_eq_some_iff.mp hg) fun hj hgval => ?_
        have hgate : gateAt C j = g := by
          rw [gate_at_eq hj, hgval]
        have hop' : (gateAt C j).op = GateOp.and := by
          rw [hgate]
          exact hop
        have htrue' : gateVal n C j (fun i => decide (i ∈ S)) = true := htrue
        have hsplit : S.card ≤ 1 ∨ S.card = 2 := by omega
        refine Or.elim hsplit ?small ?two
        · intro h1
          have hfalse := safeC j hop' S h1
          rw [hfalse] at htrue'
          exact Bool.noConfusion htrue'
        · intro h2
          refine Exists.elim (Finset.card_eq_two.mp h2) fun u rest =>
            Exists.elim rest fun v restv => ?_
          have huv := restv.1
          have hs := restv.2
          subst hs
          refine Or.elim (Classical.em (G.Adj u v)) ?edge ?gap
          · intro hab
            exact ⟨u, Finset.mem_insert_self u {v}, v,
              Finset.mem_insert_of_mem (Finset.mem_singleton_self v), hab⟩
          · intro hab
            have hpair : (fun i => decide (i ∈ ({u, v} : Finset (Fin n)))) = pairInput u v := by
              funext i
              show decide (i ∈ ({u, v} : Finset (Fin n))) = decide (i = u ∨ i = v)
              apply decide_eq_decide.mpr
              constructor
              · intro h
                refine Or.elim (Finset.mem_insert.mp h) ?_ ?_
                · intro hiu
                  exact Or.inl hiu
                · intro hiv
                  exact Or.inr (Finset.mem_singleton.mp hiv)
              · intro h
                refine Or.elim h ?_ ?_
                · intro hiu
                  exact Finset.mem_insert.mpr (Or.inl hiu)
                · intro hiv
                  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hiv))
            have hunitU : (fun i => decide (i ∈ ({u} : Finset (Fin n)))) = unitInput u := by
              funext i
              show decide (i ∈ ({u} : Finset (Fin n))) = decide (i = u)
              apply decide_eq_decide.mpr
              constructor
              · exact Finset.mem_singleton.mp
              · exact Finset.mem_singleton.mpr
            have hunitV : (fun i => decide (i ∈ ({v} : Finset (Fin n)))) = unitInput v := by
              funext i
              show decide (i ∈ ({v} : Finset (Fin n))) = decide (i = v)
              apply decide_eq_decide.mpr
              constructor
              · exact Finset.mem_singleton.mp
              · exact Finset.mem_singleton.mpr
            rw [hpair] at htrue'
            have hu : gateVal n C j (unitInput u) = false := by
              have h := safeC j hop' {u} (Nat.le_of_eq (Finset.card_singleton u))
              rw [hunitU] at h
              exact h
            have hv : gateVal n C j (unitInput v) = false := by
              have h := safeC j hop' {v} (Nat.le_of_eq (Finset.card_singleton v))
              rw [hunitV] at h
              exact h
            have hsh : InShadow n G C j u v := ⟨huv, hab, htrue', hu, hv⟩
            exact False.elim (hclean ⟨j, hop', u, v, hsh⟩)
      · intro hex
        let j := Nat.find hex
        have hj := Nat.find_spec hex
        have hop := hj.1
        have hleast : ∀ i : ℕ, i < j → (gateAt C i).op = GateOp.and →
            ¬ ∃ a b : Fin n, InShadow n G C i a b := by
          intro i hi hopi hexI
          exact Nat.find_min hex hi ⟨hopi, hexI⟩
        refine Exists.elim (shape n G C monoC safeC j hop hleast) fun p rest =>
          Exists.elim rest fun q rest => Exists.elim rest fun w1 rest =>
            Exists.elim rest fun w2 hand => ?_
        have hsh := hand.1
        have edgeEq : ∀ u v : Fin n, G.Adj u v →
            C.eval (List.ofFn (fun i => decide (i = u ∨ i = v))) = true := by
          intro u v huv
          rw [← pairEq u v]
          exact edgeC u v huv
        have singEq : ∀ u : Fin n, C.eval (List.ofFn (fun i => decide (i = u))) = false := by
          intro u
          rw [← unitEq u]
          exact singC u
        refine Exists.elim (repair n G c4 C monoC edgeEq singEq safeC j p q hop hsh)
          fun D handD => ?_
        have monoD := handD.1
        have sizeD := handD.2.1
        have edgeD := handD.2.2.1
        have singD := handD.2.2.2.1
        have safeD := handD.2.2.2.2.1
        have hlt := handD.2.2.2.2.2
        have edgeP_D : edgeP D := by
          intro u v huv
          rw [pairEq u v]
          exact edgeD u v huv
        have singP_D : singP D := by
          intro u
          rw [unitEq u]
          exact singD u
        have hlt' : andBad D < k := by
          have : andBad D < andBad C := hlt
          omega
        refine Exists.elim (ih (andBad D) hlt' D monoD edgeP_D singP_D safeD rfl) fun E handE => ?_
        have monoE := handE.1
        have sizeE := handE.2.1
        have edgeE := handE.2.2.1
        have singE := handE.2.2.2.1
        have condE := handE.2.2.2.2
        exact ⟨E, monoE, sizeE.trans sizeD, edgeE, singE, condE⟩
    refine step (andBad C) C monoC edge_of_hf sing_of_hf safe_of_hsafe rfl
