import Mathlib.Data.Finset.Sort
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadTwo PEqualNP.EdgeOwnership

-- An AND or OR duplicates an operand when pinning a vertex removes one direction
-- in which its operands disagree. Only inclusion-minimal distinguishing assignments
-- need to be examined. Direct readers already account for part of the three gates.
theorem PEqualNP.Outside.R_meta_7887_618
    (collapse : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (j : ℕ), IsAO2 n C → j < C.size →
    (v.val ∈ (gateAt C j).inputs ∨ (let F := fun (b : Fin 2) (x : Fin n → Bool) => wval C x (opnd C j b);
    ∃ b : Fin 2, ∀ y, Minimal (fun x => F b x = true ∧ F (1-b) x = false) y → y v = true)) →
    ∃ i < n+j, ∀ x : Fin n → Bool, x v = false → wval C x (n+j) = wval C x i)
    (count : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)];
    ∀ C : Circuit,
    let R := fun (v : Fin 11) => (Finset.range C.size).filter fun j => v.val ∈ (gateAt C j).inputs;
    let F := fun (j : ℕ) (b : Fin 2) (x : Fin 11 → Bool) => wval C x (opnd C j b);
    IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
    2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2*(Ustar G C).card →
    (∀ v : Fin 11, v.val < 4 → (R v).card ≤ 2 ∧
      (2 ≤ (R v).card → ∀ j ∈ R v, (gateAt C j).op = GateOp.or)) →
    ∃ v : Fin 11, v.val < 4 ∧ ∃ S : Finset ℕ, 3 ≤ (R v).card + S.card ∧
      ∀ j ∈ S, j < C.size ∧ j ∉ R v ∧ ∃ b : Fin 2,
        ∀ y, Minimal (fun x => F j b x = true ∧ F j (1-b) x = false) y → y v = true) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)),                 ↑x8 < (4 : ℕ) →                   ¬have x10 : ℕ → Prop := fun (x10 : ℕ) => x10 < x2.size ∧ ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs;                     (∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) ∨ ∃ (x11 : ℕ) (x12 : ℕ), x11 ≠ x12 ∧ x10 x11 ∧ x10 x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13 := by
  classical
  intro original C least top junkCount size charge sparse
  let R := fun (v : Fin 11) => (Finset.range C.size).filter fun j => v.val ∈ (gateAt C j).inputs
  have triple {T : Finset ℕ} (big : 3 ≤ T.card) :
      ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a < b ∧ b < c := by
    let e := T.orderEmbOfFin rfl
    let a : Fin T.card := ⟨0,by omega⟩
    let b : Fin T.card := ⟨1,by omega⟩
    let c : Fin T.card := ⟨2,by omega⟩
    exact ⟨e a,T.orderEmbOfFin_mem rfl a,e b,T.orderEmbOfFin_mem rfl b,e c,
      T.orderEmbOfFin_mem rfl c,e.strictMono (by change (0:ℕ)<1; decide),e.strictMono (by change (1:ℕ)<2; decide)⟩
  have pattern (v : Fin 11) (hv : v.val < 4) : (R v).card ≤ 2 ∧
      (2 ≤ (R v).card → ∀ j∈R v, (gateAt C j).op = GateOp.or) := by
    have miss := sparse v hv
    have member (j : ℕ) (hj : j∈R v) : j<C.size ∧ v.val ∈ (gateAt C j).inputs := by simpa [R] using hj
    constructor
    · by_contra! h
      obtain ⟨a,ha,b,hb,c,hc,ab,bc⟩ := triple h
      exact miss (.inl ⟨a,b,c,ab,bc,member a ha,member b hb,member c hc⟩)
    · intro many j hj
      obtain ⟨k,hk,ne⟩ := (R v).exists_mem_ne many j
      have op := least.1.1 _ (by
        have jl := (member j hj).1
        change gateAt C j ∈ C.gates
        have jl' : j < C.gates.length := jl
        change C.gates.getD j _ ∈ C.gates
        rw [List.getD_eq_getElem _ _ jl']
        exact List.getElem_mem jl')
      exact op.resolve_left (fun hand => miss (.inr ⟨j,k,ne.symm,member j hj,member k hk,hand⟩))
  dsimp only at count
  obtain ⟨v,hv,S,lower,cert⟩ := count C least top junkCount size charge pattern
  change 3 ≤ (R v).card + S.card at lower
  have dis : Disjoint (R v) S := Finset.disjoint_left.mpr (fun _ hr hs => (cert _ hs).2.1 hr)
  obtain ⟨a,ha,b,hb,c,hc,ab,bc⟩ := triple (T:=R v ∪ S) (by rwa [Finset.card_union_of_disjoint dis])
  have one (j : ℕ) (hj : j ∈ R v ∪ S) : j < C.size ∧
      ∃ i < 11+j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11+j)=wval C x i := by
    rcases Finset.mem_union.mp hj with hr|hs
    · obtain ⟨jl,rd⟩ : j<C.size ∧ v.val∈(gateAt C j).inputs := by simpa [R] using hr
      exact ⟨jl,collapse _ C v j least.1 jl (.inl rd)⟩
    · exact ⟨(cert j hs).1,collapse _ C v j least.1 (cert j hs).1 (.inr (cert j hs).2.2)⟩
  exact ⟨v,hv,a,b,c,ab,bc,(one c hc).1,(one a ha).2,(one b hb).2,(one c hc).2⟩
