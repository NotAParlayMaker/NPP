import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.TopForm PEqualNP.HeptadCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3797_684
    (erase : ∀ (C : Circuit) (j p : ℕ),
      Monotone2 C → ReadsBack 26 C → j < C.gates.length →
      (gateAt C j).op = .and → p ∈ (gateAt C j).inputs →
      let D := eraseGate 26 C j p
      Monotone2 D ∧ ReadsBack 26 D ∧ D.size < C.size ∧
      ∀ x : List Bool, x.length = 26 →
        let v := fun i => (C.wires x).getD i false
        (C.eval x = true → D.eval x = true) ∧
        ((C.output = 26+j → v p = v (26+j)) ∧
          (∀ k ∈ readers 26 C j, 26+k ≤ C.output →
            (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
              v (if i = 26+j then p else i)) = v (26+k)) → D.eval x = C.eval x))
    (terminal : let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
      let good (C : Circuit) :=
        (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval
          (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
        ∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false
      ∀ C : Circuit, IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        C.size < 64 → 2 ≤ andPairs 26 C → good C →
        (∃ j < C.gates.length, (gateAt C j).op = .and ∧ C.output = 26+j ∧
          ∀ p ∈ (gateAt C j).inputs, ∃ Q ∈ quadrangles singerLines3,
            (C.wires (N Q)).getD p false = true) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ good D ∧ D.size < C.size)
    (oneReader : let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
      let good (C : Circuit) :=
        (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval
          (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
        ∀ Q ∈ quadrangles singerLines3, C.eval (N Q) = false
      ∀ C : Circuit, IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        C.size < 64 → 2 ≤ andPairs 26 C → good C →
        let v (Q : Finset (Fin 13)) (i : ℕ) := (C.wires (N Q)).getD i false
        (∃ j < C.size, (gateAt C j).op = .and ∧
          (readers 26 C j).card ≤ 1 ∧ ∀ p ∈ (gateAt C j).inputs,
            ∃ Q ∈ quadrangles singerLines3, ∃ k ∈ readers 26 C j, 26+k ≤ C.output ∧
              (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
                v Q (if i = 26+j then p else i)) ≠ v Q (26+k)) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ good D ∧ D.size < C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x12 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.TopForm.readers (26 : ℕ) x4 x12).card ≤ (1 : ℕ)) → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x13 ∧ x2 x13 ∧ x13.size < x4.size := by
  intro D Correct _ C hm hr hC small _ pins pairs low
  classical
  let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))
  let N' (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
  let good (E : Circuit) :=
    (∀ p l : Fin 13, p ∈ singerLines3 l → E.eval
      (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
    ∀ Q ∈ quadrangles singerLines3, E.eval (N Q) = false
  have hInc : ∀ p l : Fin 13, p - l ∈ D ↔ p ∈ singerLines3 l := by decide
  have hQ (Q : Finset (Fin 13)) : Q ∈ quadrangles singerLines3 ↔
      Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2 := by
    have heq (k : Fin 13) : Q ∩ singerLines3 k = Q.filter (fun u => u - k ∈ D) := by
      ext u
      simp [hInc u k]
    change Q ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
        (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, heq]
  have hN (Q : Finset (Fin 13)) : N Q = N' Q := by
    have hTail : List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q)) =
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D)) := by
      apply congrArg List.ofFn
      funext v
      apply decide_eq_decide.mpr
      change (v ∈ (Finset.univ : Finset (Fin 13)).filter
        (fun l => Disjoint (singerLines3 l) Q)) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, ← hInc]
      constructor
      · intro h r hr hi
        exact h hi hr
      · intro h r hi hr
        exact h r hr hi
    exact congrArg (fun tail : List Bool => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++ tail) hTail
  have sameTests (E : Circuit) : Correct E ↔ good E := by
    change ((∀ p l : Fin 13, p-l ∈ D → E.eval
        (List.ofFn (fun u : Fin 13 => decide (u=p)) ++
          List.ofFn (fun v : Fin 13 => decide (v=l))) = true) ∧
      ∀ Q : Finset (Fin 13), Q.card = 4 →
        (∀ k : Fin 13, (Q.filter (fun u => u-k ∈ D)).card ≤ 2) →
        E.eval (N' Q) = false) ↔ _
    simp only [good,hInc,hQ,hN,and_imp]
  have ok : good C := (sameTests C).mp hC
  have ao : IsAO2 26 C := by
    refine ⟨?_,hr,fun g hg => (pins g hg).1⟩
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (hm g hg).1
  have different (g : Gate) (hg : g ∈ C.gates) : g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 :=
    (pins g hg).2
  obtain ⟨j,jlt,jand,jread⟩ := low
  let v (Q : Finset (Fin 13)) (i : ℕ) := (C.wires (N Q)).getD i false
  let sameReader (p : ℕ) (Q : Finset (Fin 13)) (k : ℕ) : Prop :=
    (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => v Q (if i=26+j then p else i)) = v Q (26+k)
  have drop (p : ℕ) (hp : p ∈ (gateAt C j).inputs)
      (safe : ∀ Q ∈ quadrangles singerLines3,
        (C.output = 26+j → v Q p = v Q (26+j)) ∧
        (∀ k ∈ readers 26 C j, 26+k ≤ C.output → sameReader p Q k)) :
      ∃ E : Circuit, Monotone2 E ∧ ReadsBack 26 E ∧ Correct E ∧ E.size < C.size := by
    let E := eraseGate 26 C j p
    obtain ⟨em,eb,es,eq⟩ := erase C j p hm hr jlt jand hp
    refine ⟨E,em,eb,(sameTests E).mpr ⟨?_,?_⟩,es⟩
    · intro p l h
      exact (eq _ (by simp only [List.length_append,List.length_ofFn])).1 (ok.1 p l h)
    · intro Q hQ
      exact ((eq (N Q) (by simp only [N,List.length_append,List.length_ofFn])).2 (safe Q hQ)).trans
        (ok.2 Q hQ)
  by_cases isOutput : C.output = 26+j
  · by_cases possible : ∃ p ∈ (gateAt C j).inputs, ∀ Q ∈ quadrangles singerLines3, v Q p = false
    · obtain ⟨p,hp,hzero⟩ := possible
      refine drop p hp (fun Q hQ => ⟨fun _ => ?_,?_⟩)
      · have hz := ok.2 Q hQ
        change (C.wires (N Q)).getD C.output false = false at hz
        exact (hzero Q hQ).trans (by simpa only [isOutput] using hz.symm)
      · intro k hk hko
        obtain ⟨bound,reads⟩ := Finset.mem_filter.mp hk
        have before := hr k (Finset.mem_range.mp bound) (26+j) reads
        omega
    · have witness (p : ℕ) (hp : p ∈ (gateAt C j).inputs) :
          ∃ Q ∈ quadrangles singerLines3, v Q p = true := by
        by_contra absent
        apply possible
        refine ⟨p,hp,fun Q hQ => ?_⟩
        cases eq : v Q p
        · rfl
        · exact (absent ⟨Q,hQ,eq⟩).elim
      obtain ⟨E,em,eb,eg,es⟩ := terminal C ao different small pairs ok
        ⟨j,jlt,jand,isOutput,witness⟩
      exact ⟨E,em,eb,(sameTests E).mpr eg,es⟩
  · by_cases possible : ∃ p ∈ (gateAt C j).inputs, ∀ Q ∈ quadrangles singerLines3,
        ∀ k ∈ readers 26 C j, 26+k ≤ C.output → sameReader p Q k
    · obtain ⟨p,hp,hkeep⟩ := possible
      exact drop p hp (fun Q hQ => ⟨fun h => (isOutput h).elim,hkeep Q hQ⟩)
    · have witness (p : ℕ) (hp : p ∈ (gateAt C j).inputs) :
          ∃ Q ∈ quadrangles singerLines3, ∃ k ∈ readers 26 C j,
            26+k ≤ C.output ∧ ¬sameReader p Q k := by
        by_contra absent
        apply possible
        exact ⟨p,hp,fun Q hQ k hk hko => of_not_not (fun h => absent ⟨Q,hQ,k,hk,hko,h⟩)⟩
      obtain ⟨E,em,eb,eg,es⟩ := oneReader C ao different small pairs ok
        ⟨j,jlt,jand,jread,witness⟩
      exact ⟨E,em,eb,(sameTests E).mpr eg,es⟩
