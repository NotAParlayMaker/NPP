import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2846_517
    (normal : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
      let F := fun z : Fin (n+m) → Bool =>
        ∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true
      let computes := fun D => ∀ z, circuitFun (n+m) D z = decide (F z)
      let clean := fun w => ∀ z, (C.wires (List.ofFn z)).getD w false = true → F z
      let op := fun i => (gateAt C i).op
      let reads := fun w i => w ∈ (gateAt C i).inputs
      (∀ p q l s, p ≠ q → l ≠ s → ¬ (I p l ∧ I p s ∧ I q l ∧ I q s)) →
      IsAO2 (n+m) C → computes C →
      (∀ D, IsAO2 (n+m) D → computes D → C.size ≤ D.size) →
      (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ op i = .or ∧
        (n+m+i = C.output ∨ ∃ k ∈ T, ∀ j < C.gates.length, reads (n+m+i) j ↔ j = k)) ∧
        ∀ w, clean w → (∃ k < C.gates.length, op k = .or ∧ reads w k) →
          ∀ k < C.gates.length, reads w k → k ∈ T) →
      (¬ ∃ i j, op i = .and ∧ op j = .and ∧ InCone (n+m) C i j) ∧
        ∀ i < C.gates.length, op i = .and → clean (n+m+i))
    (supports : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      (¬ ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone n C i j) →
      ∃ W : Finset ℕ, ∃ S : ℕ → Finset (Fin n),
        (∀ w ∈ W, (S w).Nonempty) ∧
        (∀ w ∈ W, (∃ v : Fin n, w = ↑v ∧ S w = {v}) ∨
          ∃ i < C.gates.length, w = n + i ∧ (gateAt C i).op = .or ∧
            ∀ u ∈ (gateAt C i).inputs, u ∈ W ∧ S u ⊆ S w) ∧
        ∀ i < C.gates.length, (gateAt C i).op = .and →
          ∃ a b : ℕ, (gateAt C i).inputs = [a,b] ∧ a ∈ W ∧ b ∈ W ∧
            ∀ z : Fin n → Bool, (∃ u ∈ S a, z u = true) →
              (∃ v ∈ S b, z v = true) → gateVal n C i z = true) :
∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  let acceptedPair {points lines : ℕ} (incident : Fin points → Fin lines → Prop)
      (input : Fin (points + lines) → Bool) : Prop :=
    ∃ p l, incident p l ∧ input (Fin.castAdd lines p) = true ∧
      input (Fin.natAdd points l) = true

  have cleanOrProductHasOppositeTypes {points lines : ℕ}
      (incident : Fin points → Fin lines → Prop)
      (A B : Finset (Fin (points + lines))) (aNonempty : A.Nonempty)
      (bNonempty : B.Nonempty)
      (clean : ∀ input : Fin (points + lines) → Bool,
        (∃ a ∈ A, input a = true) → (∃ b ∈ B, input b = true) →
        acceptedPair incident input) :
      ((∀ a ∈ A, a.val < points) ∧ (∀ b ∈ B, points ≤ b.val)) ∨
      ((∀ a ∈ A, points ≤ a.val) ∧ (∀ b ∈ B, b.val < points)) := by
    have pairTypes (a b : Fin (points + lines)) (ha : a ∈ A) (hb : b ∈ B) :
        (a.val < points ∧ points ≤ b.val) ∨ (points ≤ a.val ∧ b.val < points) := by
      let input (i : Fin (points + lines)) : Bool := decide (i = a ∨ i = b)
      obtain ⟨p, l, _, hp, hl⟩ := clean input
        ⟨a, ha, by simp [input]⟩ ⟨b, hb, by simp [input]⟩
      have pHits : Fin.castAdd lines p = a ∨ Fin.castAdd lines p = b :=
        of_decide_eq_true hp
      have lHits : Fin.natAdd points l = a ∨ Fin.natAdd points l = b :=
        of_decide_eq_true hl
      have pBound : (Fin.castAdd lines p).val < points := p.isLt
      have lBound : points ≤ (Fin.natAdd points l).val := by
        change points ≤ points + l.val
        omega
      rcases pHits with hpa | hpb <;> rcases lHits with hla | hlb
      · rw [hpa] at pBound
        rw [hla] at lBound
        omega
      · exact Or.inl ⟨hpa ▸ pBound, hlb ▸ lBound⟩
      · exact Or.inr ⟨hla ▸ lBound, hpb ▸ pBound⟩
      · rw [hpb] at pBound
        rw [hlb] at lBound
        omega
    obtain ⟨a, ha⟩ := aNonempty
    obtain ⟨b, hb⟩ := bNonempty
    rcases pairTypes a b ha hb with ⟨pa, lb⟩ | ⟨la, pb⟩
    · left
      constructor
      · intro i hi
        rcases pairTypes i b hi hb with h | h
        · exact h.1
        · omega
      · intro i hi
        rcases pairTypes a i ha hi with h | h
        · exact h.2
        · omega
    · right
      constructor
      · intro i hi
        rcases pairTypes i b hi hb with h | h
        · omega
        · exact h.1
      · intro i hi
        rcases pairTypes a i ha hi with h | h
        · omega
        · exact h.2


  have assembleTwoLevelFromOrSupports {points lines : ℕ}
      (incident : Fin points → Fin lines → Prop) (C : Circuit)
      (wireDomain : Finset ℕ) (support : ℕ → Finset (Fin (points + lines)))
      (nonempty : ∀ w ∈ wireDomain, (support w).Nonempty)
      (source : ∀ w ∈ wireDomain,
        (∃ v : Fin (points + lines), w = v.val ∧ support w = {v}) ∨
        ∃ i < C.gates.length, w = points + lines + i ∧ (gateAt C i).op = .or ∧
          ∀ u ∈ (gateAt C i).inputs, u ∈ wireDomain ∧ support u ⊆ support w)
      (products : ∀ i < C.gates.length, (gateAt C i).op = .and →
        ∃ a b : ℕ, (gateAt C i).inputs = [a,b] ∧ a ∈ wireDomain ∧ b ∈ wireDomain ∧
          ∀ input : Fin (points + lines) → Bool,
            (∃ u ∈ support a, input u = true) → (∃ v ∈ support b, input v = true) →
            acceptedPair incident input) :
      ∃ P L : Finset ℕ,
        (∀ w ∈ P, w < points ∨ ∃ i < C.gates.length, w = points + lines + i ∧
          (gateAt C i).op = .or ∧ ∀ u ∈ (gateAt C i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (points ≤ w ∧ w < points + lines) ∨ ∃ i < C.gates.length,
          w = points + lines + i ∧ (gateAt C i).op = .or ∧
          ∀ u ∈ (gateAt C i).inputs, u ∈ L) ∧
        ∀ i < C.gates.length, (gateAt C i).op = .and →
          ∃ a b : ℕ, (gateAt C i).inputs = [a,b] ∧
            ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
    classical
    let P := wireDomain.filter (fun w => ∀ v ∈ support w, v.val < points)
    let L := wireDomain.filter (fun w => ∀ v ∈ support w, points ≤ v.val)
    refine ⟨P, L, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨domain, color⟩ := Finset.mem_filter.mp hw
      rcases source w domain with ⟨v, rfl, hv⟩ | ⟨i, hi, hwire, hop, sub⟩
      · left
        exact color v (by rw [hv]; simp)
      · right
        refine ⟨i, hi, hwire, hop, ?_⟩
        intro u hu
        obtain ⟨du, subset⟩ := sub u hu
        exact Finset.mem_filter.mpr ⟨du, fun v hv => color v (subset hv)⟩
    · intro w hw
      obtain ⟨domain, color⟩ := Finset.mem_filter.mp hw
      rcases source w domain with ⟨v, rfl, hv⟩ | ⟨i, hi, hwire, hop, sub⟩
      · left
        exact ⟨color v (by rw [hv]; simp), v.isLt⟩
      · right
        refine ⟨i, hi, hwire, hop, ?_⟩
        intro u hu
        obtain ⟨du, subset⟩ := sub u hu
        exact Finset.mem_filter.mpr ⟨du, fun v hv => color v (subset hv)⟩
    · intro i hi hop
      obtain ⟨a,b,inputs,da,db,clean⟩ := products i hi hop
      refine ⟨a,b,inputs,?_⟩
      rcases cleanOrProductHasOppositeTypes incident (support a) (support b)
        (nonempty a da) (nonempty b db) clean with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact Or.inl ⟨Finset.mem_filter.mpr ⟨da,ha⟩, Finset.mem_filter.mpr ⟨db,hb⟩⟩
      · exact Or.inr ⟨Finset.mem_filter.mpr ⟨da,ha⟩, Finset.mem_filter.mpr ⟨db,hb⟩⟩
  intro n m I dec C c4 ao computes least stuck
  obtain ⟨noNest, clean⟩ := normal n m I C c4 ao computes least stuck
  obtain ⟨W, S, nonempty, source, products⟩ := supports (n+m) C ao noNest
  apply assembleTwoLevelFromOrSupports I C W S nonempty source
  intro i hi hop
  obtain ⟨a,b,inputs,da,db,val⟩ := products i hi hop
  refine ⟨a,b,inputs,da,db,?_⟩
  intro z ha hb
  exact clean i hi hop z (val z ha hb)
