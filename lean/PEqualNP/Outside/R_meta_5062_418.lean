import PEqualNP.Defs

open PEqualNP.AndCount
open Finset

set_option maxHeartbeats 700000 in
theorem PEqualNP.Outside.R_meta_5062_418
    (privateSide :
    let G : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]
    let bare (C : AndCountCircuit 42) (t : Fin C.size × Bool) :=
      if t.2 then C.leftVars t.1 else C.rightVars t.1
    ∀ C : AndCountCircuit 42, C.Computes G → C.outVars=∅ →
      (∀ j, Disjoint (C.leftVars j) (C.rightVars j)) →
      (∀ v, {j : Fin C.size | v∈C.leftVars j ∨ v∈C.rightVars j}.ncard ≤ 4) →
      ∀ v : Fin 42, ∃ t, v∈bare C t ∧ ∀ u∈bare C t, (u.val<21 ↔ v.val<21) → u=v)
    (residual :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (20 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) → (let bare (t : Fin x2.size × Bool) := if t.2 then x2.leftVars t.1 else x2.rightVars t.1
      ∃ (a b : Fin x2.size × Bool) (p q l m : Fin 21), a≠b ∧ p≠q ∧ l≠m ∧
        bare a = {Fin.castAdd 21 p,Fin.natAdd 21 l} ∧ bare b = {Fin.castAdd 21 q,Fin.natAdd 21 m}) → False) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (20 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) → False := by
  dsimp only
  intro C wf computes noOut noSingle disj size cap pairs
  apply residual C wf computes noOut noSingle disj size cap pairs
  classical
  let bare (t : Fin C.size × Bool) := if t.2 then C.leftVars t.1 else C.rightVars t.1
  have select := privateSide C computes noOut disj cap
  choose chosen member unique using select
  let pt (p : Fin 21) := chosen (Fin.castAdd 21 p)
  let ln (l : Fin 21) := chosen (Fin.natAdd 21 l)
  let P := univ.image pt
  let L := univ.image ln
  have ptLower (p : Fin 21) : (Fin.castAdd 21 p).val<21 := p.isLt
  have lnUpper (l : Fin 21) : ¬ (Fin.natAdd 21 l).val<21 := by
    change ¬21+l.val<21; omega
  have injP : Function.Injective pt := by
    intro p q eqn
    have hp := member (Fin.castAdd 21 p)
    change Fin.castAdd 21 p∈bare (pt p) at hp
    rw [eqn] at hp
    have eq := unique (Fin.castAdd 21 q) (Fin.castAdd 21 p) hp
      (iff_of_true (ptLower p) (ptLower q))
    exact Fin.ext (congrArg (fun i : Fin 42 => i.val) eq)
  have injL : Function.Injective ln := by
    intro p q eqn
    have hp := member (Fin.natAdd 21 p)
    change Fin.natAdd 21 p∈bare (ln p) at hp
    rw [eqn] at hp
    have eq := unique (Fin.natAdd 21 q) (Fin.natAdd 21 p) hp
      (iff_of_false (lnUpper p) (lnUpper q))
    have val := congrArg Fin.val eq
    change 21+p.val=21+q.val at val
    exact Fin.ext (Nat.add_left_cancel val)
  have countP : P.card=21 := by simp [P,card_image_of_injective _ injP]
  have countL : L.card=21 := by simp [L,card_image_of_injective _ injL]
  have capacity : (P∪L).card≤40 := by
    have h := card_le_univ (P∪L)
    simpa [Fintype.card_prod,size] using h
  have tally := card_union_add_card_inter P L
  have overlap : 2≤(P∩L).card := by omega
  have slot (t : Fin C.size × Bool) (ht : t∈P∩L) :
      ∃ p l, pt p=t ∧ ln l=t ∧ bare t={Fin.castAdd 21 p,Fin.natAdd 21 l} := by
    obtain ⟨hp,hl⟩ := mem_inter.mp ht
    obtain ⟨p,_,ep⟩ := mem_image.mp hp
    obtain ⟨l,_,el⟩ := mem_image.mp hl
    refine ⟨p,l,ep,el,?_⟩
    change bare t={Fin.castAdd 21 p,Fin.natAdd 21 l}
    ext u
    simp only [mem_insert,mem_singleton]
    constructor
    · intro hu
      by_cases low : u.val<21
      · left
        apply unique (Fin.castAdd 21 p) u _ (iff_of_true low (ptLower p))
        change u∈bare (pt p); rwa [ep]
      · right
        apply unique (Fin.natAdd 21 l) u _ (iff_of_false low (lnUpper l))
        change u∈bare (ln l); rwa [el]
    · rintro (rfl|rfl)
      · rw [←ep]; exact member _
      · rw [←el]; exact member _

  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp overlap
  obtain ⟨p,l,pa,la,first⟩ := slot a ha
  obtain ⟨q,m,qb,mb,second⟩ := slot b hb
  refine ⟨a,b,p,q,l,m,ab,?_,?_,first,second⟩
  · exact fun eq => ab (pa.symm.trans ((congrArg pt eq).trans qb))
  · exact fun eq => ab (la.symm.trans ((congrArg ln eq).trans mb))
