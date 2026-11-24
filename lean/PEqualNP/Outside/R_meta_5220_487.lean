import Mathlib
import PEqualNP.Defs

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open scoped Classical

-- The finite selection and endpoint translations adapt singmereal-hub's PR 10140.
-- The pivotal-coordinate argument uses the bound checked in PR 10026.

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4500000 in
theorem PEqualNP.Outside.R_meta_5220_487
    (core : ∀ (n k : ℕ) (S : Finset (Fin n × Fin n)) (A : Fin n × Fin n → Finset (Fin k)),
      44*(S.biUnion A).card < S.card →
      ∃ U ⊆ S, U.card = 44*(U.biUnion A).card+1 ∧
        ∀ j ∈ U.biUnion A, 45 ≤ (U.filter fun e => j ∈ A e).card)
    (charge : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    1 ≤ q → Monotone2 C →
    (∀ s : Finset (Fin N), s.card ≤ q → C.eval (List.ofFn (Fin.addCases
      (fun p => decide (¬∃ l ∈ s, I p l)) (fun l => decide (l ∈ s)))) = false) →
    let pair (e : Fin N × Fin N) := pairInput (Fin.castAdd N e.2) (Fin.natAdd N e.1)
    let A (e : Fin N × Fin N) := univ.filter (fun j : Fin C.size =>
      (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
      gateVal (N+N) C j.val (pair e) = true)
    ∀ U : Finset (Fin N × Fin N),
      (∀ e ∈ U, C.eval (List.ofFn (pair e)) = true) →
      (U.image Prod.fst).card + (U.image Prod.snd).card ≤ (U.biUnion A).card+1)
    (geometry : ∀ (N : ℕ) (T : Fin N → Finset (Fin N)) (L : Finset (Fin N)),
      (∀ l, l ∈ L ↔ (T l).Nonempty) →
      (∀ p r l m, p ≠ r → p ∈ T l → r ∈ T l → p ∈ T m → r ∈ T m → l=m) →
      44*((univ.biUnion T).card+L.card-1) < ∑ l, (T l).card →
      7657 ≤ (univ.biUnion T).card ∧ 7657 ≤ L.card)
    (light : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      N=q*q+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsMinimalMonoCircuit (N+N) C →
      (∀ s : Finset (Fin N), s.card ≤ q → C.eval (List.ofFn (Fin.addCases
        (fun p => decide (¬∃ l∈s, I p l)) (fun l => decide (l ∈ s)))) = false) →
      let pair (e : Fin N × Fin N) := pairInput (Fin.castAdd N e.2) (Fin.natAdd N e.1)
      let D : Circuit := ⟨C.gates.map (fun g =>
        if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          (g.inputs.all fun i => decide (0 < (C.lineDegrees (N+N) (Ico N (N+N))).getD i 0)) = true
        then ⟨.or,[]⟩ else g), C.output⟩
      let A (e : Fin N × Fin N) := univ.filter (fun j : Fin C.size =>
        (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
        gateVal (N+N) C j.val (pair e) = true)
      ∀ U : Finset (Fin N × Fin N),
        (∀ e ∈ U, I e.2 e.1 ∧ C.eval (List.ofFn (pair e)) = true ∧ D.eval (List.ofFn (pair e)) = false) →
        U.card = 44*(U.biUnion A).card+1 →
        7657 ≤ min (U.image Prod.fst).card (U.image Prod.snd).card →
        ∃ j ∈ U.biUnion A, (U.filter fun e => j ∈ A e).card ≤ 44) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 = x1 * x1 + x1 + (1 : ℕ) →     (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →       (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →         PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →           (∀ (x10 : Finset (Fin x2)), x10.card ≤ x1 → x5.eval (List.ofFn fun (x12 : Fin (x2 + x2)) => Fin.addCases (fun (x13 : Fin x2) => Decidable.decide ¬∃ x14 ∈ x10, x3 x13 x14) (fun (x13 : Fin x2) => Decidable.decide (x13 ∈ x10)) x12) = Bool.false) →             have x11 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x11 x12 : Fin x2) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x2 x11) (Fin.natAdd x2 x12);             have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };             ∀ (x13 : Fin x2 → Finset (Fin x2)), (∀ (x14 x15 : Fin x2), x15 ∈ x13 x14 → x3 x15 x14 ∧ x5.eval (List.ofFn (x11 x15 x14)) = Bool.true ∧ x12.eval (List.ofFn (x11 x15 x14)) = Bool.false) → (44 : ℕ) * (Fintype.card { x15 : Fin (x2 + x2) // ∃ (x16 : Fin x2), ∃ x17 ∈ x13 x16, x11 x17 x16 x15 = Bool.true } - (1 : ℕ)) < ∑ x15 : Fin x2, (x13 x15).card → ∑ x16 : Fin x2, (x13 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x13 x17, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 (↑x16) (x11 x18 x17) = Bool.true } := by
  classical
  have endpoint_count {N : ℕ} (T : Fin N → Finset (Fin N)) :
      Fintype.card {j : Fin (N+N) // ∃ l, ∃ p ∈ T l, pairInput (Fin.castAdd N p) (Fin.natAdd N l) j = true} =
      (univ.biUnion T).card + (univ.filter (fun l => (T l).Nonempty)).card := by
    classical
    let P := univ.biUnion T
    let L := univ.filter (fun l => (T l).Nonempty)
    let A := P.image (Fin.castAdd N)
    let B := L.image (Fin.natAdd N)
    rw [Fintype.card_subtype]
    have split : (univ.filter fun j => ∃ l, ∃ p ∈ T l, pairInput (Fin.castAdd N p) (Fin.natAdd N l) j = true) = A ∪ B := by
      ext j
      simp only [mem_filter,mem_univ,true_and,mem_union,mem_image,A,B]
      constructor
      · rintro ⟨l,p,hp,on⟩
        rcases of_decide_eq_true on with eq|eq
        · exact Or.inl ⟨p,mem_biUnion.mpr ⟨l,mem_univ _,hp⟩,eq.symm⟩
        · exact Or.inr ⟨l,mem_filter.mpr ⟨mem_univ _,p,hp⟩,eq.symm⟩
      · rintro (⟨p,ph,rfl⟩|⟨l,lh,rfl⟩)
        · obtain ⟨l,_,hp⟩ := mem_biUnion.mp ph
          exact ⟨l,p,hp,decide_eq_true (Or.inl rfl)⟩
        · obtain ⟨p,hp⟩ := (mem_filter.mp lh).2
          exact ⟨l,p,hp,decide_eq_true (Or.inr rfl)⟩
    have disjoint : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro j ha hb
      obtain ⟨p,_,rfl⟩ := mem_image.mp ha
      obtain ⟨l,_,eq⟩ := mem_image.mp hb
      have h := congrArg Fin.val eq
      change N+l.val = p.val at h
      omega
    rw [split,Finset.card_union_of_disjoint disjoint]
    change (P.image _).card + (L.image _).card = P.card + L.card
    rw [card_image_of_injective _ (Fin.castAdd_injective N N)]
    have inj : Function.Injective (Fin.natAdd N : Fin N → Fin (N+N)) := by
      intro a b h; apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val h)
    rw [card_image_of_injective _ inj]
  intro q N I inst C order lines unique minimal sound pair D T valid dense
  have noFour (H : Fin N → Finset (Fin N)) (contained : ∀ l p, p ∈ H l → I p l) :
      ∀ p r l m, p ≠ r → p ∈ H l → r ∈ H l → p ∈ H m → r ∈ H m → l=m := by
    intro p r l m ne pl rl pm rm
    obtain ⟨u,_,single⟩ := unique p r ne
    exact (single l ⟨contained l p pl,contained l r rl⟩).trans
      (single m ⟨contained m p pm,contained m r rm⟩).symm
  have pairGeometry (U : Finset (Fin N × Fin N)) (inside : ∀ e ∈ U, I e.2 e.1)
      (many : 44*((U.image Prod.fst).card+(U.image Prod.snd).card-1) < U.card) :
      7657 ≤ min (U.image Prod.fst).card (U.image Prod.snd).card := by
    let H (l : Fin N) := univ.filter (fun p => (l,p) ∈ U)
    have sum : U.card = ∑ l, (H l).card := by
      have eq : U = univ.filter (fun e : Fin N × Fin N => e.2 ∈ H e.1) := by
        ext e
        simp [H]
      rw [eq,Finset.card_filter,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_boole]; simp
    have left : (U.image Prod.fst) = univ.filter (fun l => (H l).Nonempty) := by
      ext l
      simp only [mem_image,mem_filter,mem_univ,true_and,Finset.Nonempty,H]
      constructor
      · rintro ⟨⟨r,p⟩,hp,eq⟩
        change r = l at eq
        exact ⟨p,eq ▸ hp⟩
      · rintro ⟨p,hp⟩
        exact ⟨(l,p),hp,rfl⟩
    have right : (U.image Prod.snd) = univ.biUnion H := by
      ext p
      simp only [mem_image,mem_biUnion,mem_filter,mem_univ,true_and,H]
      constructor
      · rintro ⟨⟨l,r⟩,hr,eq⟩
        change r = p at eq
        exact ⟨l,eq ▸ hr⟩
      · rintro ⟨l,hl⟩
        exact ⟨(l,p),hl,rfl⟩
    have bounds := geometry N H (univ.filter fun l => (H l).Nonempty) (by simp)
      (noFour H (fun l p hp => inside (l,p) (mem_filter.mp hp).2))
      (by rw [left,right,sum,Nat.add_comm] at many; exact many)
    rw [left,right]
    exact le_min bounds.2 bounds.1
  have positive : 1 ≤ q := by
    rw [endpoint_count] at dense
    have endpoints := geometry N T (univ.filter fun l => (T l).Nonempty) (by simp)
      (noFour T (fun l p hp => (valid l p hp).1)) dense
    have available : (univ.biUnion T).card ≤ N := by simpa using Finset.card_le_univ (univ.biUnion T)
    by_contra! bad
    have zero : q=0 := by omega
    simp [zero] at order
    omega
  let S := univ.filter (fun e : Fin N × Fin N => e.2 ∈ T e.1)
  let A (e : Fin N × Fin N) := univ.filter (fun j : Fin C.size =>
    (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
    gateVal (N+N) C j.val (pair e.2 e.1) = true)
  have count : S.card = ∑ l, (T l).card := by
    dsimp only [S]
    rw [Finset.card_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_boole]; simp
  have same : S.biUnion A = univ.filter (fun j : Fin C.size =>
    (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
    ∃ l, ∃ p ∈ T l, gateVal (N+N) C j.val (pair p l) = true) := by
    ext j
    simp only [A,S,mem_biUnion,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨⟨l,p⟩,hp,off,on⟩; exact ⟨off,l,p,hp,on⟩
    · rintro ⟨off,l,p,hp,on⟩; exact ⟨(l,p),hp,off,on⟩
  rw [Fintype.card_subtype,← same,← count]
  by_contra! excess
  obtain ⟨U,sub,balance,heavy⟩ := core N C.size S A excess
  have kept (e : Fin N × Fin N) (he : e ∈ U) := valid e.1 e.2 (mem_filter.mp (sub he)).2
  have nodes := charge q N I C positive minimal.1 sound U (fun e he => (kept e he).2.1)
  change (U.image Prod.fst).card + (U.image Prod.snd).card ≤ (U.biUnion A).card+1 at nodes
  have trail : 44*((U.image Prod.fst).card+(U.image Prod.snd).card-1) < U.card := by omega
  have endpoints := pairGeometry U (fun e he => (kept e he).1) trail
  obtain ⟨j,hj,low⟩ := light q N I C order lines unique minimal sound U kept balance endpoints
  have high := heavy j hj
  change (U.filter fun e => j ∈ A e).card ≤ 44 at low
  omega
