import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2063_317
    (geometry :
      let S := PEqualNP.HeptadCover.singerLines3
      let y := fun Q => PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
      let good := fun C : PEqualNP.CircuitLowerBounds.Circuit => PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
        PEqualNP.GenericRejection.RightOnIncidentPairs S C ∧ ∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q → C.eval (y Q)=false
      let mask := fun (g : PEqualNP.CircuitLowerBounds.Gate) (s : Bool) (b : Fin 26) =>
        g.op=(if s then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and) ∧ b.val∈g.inputs
      let profile := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ r b d : Fin 26, r≠b → r≠d → ∀ s t : Bool,
        (∀ g∈C.gates, r.val∈g.inputs → mask g s b ∨ mask g t d) → s=true ∧ t=true ∧
        ∃ p l : Fin 13, p∈S l ∧ ((b.val+0=p.val ∧ d.val=13+l.val) ∨ (d.val+0=p.val ∧ b.val=13+l.val))
      ∀ C, good C → profile C)
    (counting :
      let S := PEqualNP.HeptadCover.singerLines3
      let y := fun Q => PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
      let good := fun C : PEqualNP.CircuitLowerBounds.Circuit => PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
        PEqualNP.GenericRejection.RightOnIncidentPairs S C ∧ ∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q → C.eval (y Q)=false
      let mask := fun (g : PEqualNP.CircuitLowerBounds.Gate) (s : Bool) (b : Fin 26) =>
        g.op=(if s then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and) ∧ b.val∈g.inputs
      let below := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ) =>
        (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op=PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op=PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone 26 C i j
      ∀ C, good C → (∀ r b d : Fin 26, r≠b → r≠d → ∀ s t : Bool,
        (∀ g∈C.gates, r.val∈g.inputs → mask g s b ∨ mask g t d) → s=true ∧ t=true ∧
        ∃ p l : Fin 13, p∈S l ∧ ((b.val+0=p.val ∧ d.val=13+l.val) ∨ (d.val+0=p.val ∧ b.val=13+l.val))) → C.size<64 →
        (∀ i j, below C i j → ∃ Q, PEqualNP.HeptadCover.IsQuadrangle S Q ∧ (C.wires (y Q)).getD (26+i) false=true) →
        (∃ i j, below C i j) → ∃ D, good D ∧ D.size<C.size) :
    have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → x5.size < (64 : ℕ) → (∀ (x10 x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size := by
  intro D Quad N Test C hm hb hc sz dirty nest
  let S := PEqualNP.HeptadCover.singerLines3
  let y := fun Q => PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
  have incid : ∀ p l : Fin 13, p∈S l ↔ D (p-l)=true := by decide +kernel
  have geom (Q : Finset (Fin 13)) : PEqualNP.HeptadCover.IsQuadrangle S Q ↔ Quad Q := by
    have f (l : Fin 13) : Q∩S l=Q.filter (fun p => D (p-l)=true) := by
      ext p
      simp [incid]
    change (Q.card=4 ∧ ∀ l, (Q∩S l).card≤2) ↔ _
    simp_rw [f]
    rfl
  have yn (Q : Finset (Fin 13)) : y Q=N Q := by
    apply congrArg (List.append _)
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change (l ∈ Finset.univ.filter (fun j => Disjoint (S j) Q)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
    constructor
    · intro h p hp
      exact Bool.eq_false_iff.mpr (fun e => h ((incid p l).2 e) hp)
    · intro h p hl hp
      exact Bool.noConfusion ((h p hp).symm.trans ((incid p l).1 hl))
  have singletonInput (p l : Fin 13) :
      PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) =
      ((List.ofFn fun i : Fin 13 => decide (i=p)) ++ (List.ofFn fun i : Fin 13 => decide (i=l))) := by
    delta PEqualNP.GenericRejection.incidenceInput
    simp
  have good (U : PEqualNP.CircuitLowerBounds.Circuit) : Test U ↔ PEqualNP.GenericRejection.RightOnIncidentPairs S U ∧
      ∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q → U.eval (y Q)=false := by
    constructor
    · intro h
      refine ⟨?_, fun Q hQ => (yn Q).symm ▸ h.2 Q ((geom Q).1 hQ)⟩
      intro l p hp
      rw [singletonInput]
      exact h.1 p l ((incid p l).1 hp)
    · rintro ⟨hp,hn⟩
      refine ⟨?_, fun Q hQ => (yn Q) ▸ hn Q ((geom Q).2 hQ)⟩
      intro p l e
      have hit := hp l p ((incid p l).2 e)
      rw [singletonInput] at hit
      exact hit
  obtain ⟨U,hu,sm⟩ := counting C ⟨hm,hb,(good C).1 hc⟩ (geometry C ⟨hm,hb,(good C).1 hc⟩) sz
    (fun i j h => by
      obtain ⟨Q,ok,hit⟩ := dirty i j h.1 h.2.1 h.2.2
      refine ⟨Q,(geom Q).2 ok,?_⟩
      change (C.wires (y Q)).getD (26+i) false=true
      rw [yn Q]
      exact hit) nest
  exact ⟨U,hu.1,hu.2.1,(good U).2 hu.2.2,sm⟩
