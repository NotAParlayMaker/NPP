import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2448_3
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (h2 : open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
        PEqualNP.MetaComplexity.NestedCover in
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      let edge := fun D j u v => G.Adj u v ∧ Owns n D j u v
      let meet := fun a b c d : Fin n => a = c ∨ a = d ∨ b = c ∨ b = d
      let clean := fun D j => ∀ a b c d, edge D j a b → edge D j c d → meet a b c d
      ∀ (C : Circuit) (j : ℕ), IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        (∀ i < j, clean C i) → ∀ a b c d, edge C j a b → edge C j c d →
        ¬meet a b c d → ¬G.Adj a c → ¬G.Adj a d → ¬G.Adj b c →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
          ∀ i ≤ j, clean D i) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by
  open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
    PEqualNP.MetaComplexity.NestedCover in
  (intro n G _ tri square
   classical
   let edge := fun D j u v => G.Adj u v ∧ Owns n D j u v
   let meet := fun a b c d : Fin n => a = c ∨ a = d ∨ b = c ∨ b = d
   let clean := fun D j => ∀ a b c d, edge D j a b → edge D j c d → meet a b c d
   have flip {D j u v} (h : edge D j u v) : edge D j v u := by
     have hp : pairInput v u = pairInput u v := by
       funext w
       change decide (w = v ∨ w = u) = decide (w = u ∨ w = v)
       simp only [or_comm]
     obtain ⟨adj, owns⟩ := h
     refine ⟨adj.symm, ?_⟩
     unfold Owns at owns ⊢
     rwa [hp]
   -- Orient the disjoint owned edges so that only their second endpoints can be adjacent.
   have orient {D j} (bad : ¬clean D j) :
       ∃ a b c d, edge D j a b ∧ edge D j c d ∧ ¬meet a b c d ∧
         ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c := by
     unfold clean at bad
     push Not at bad
     obtain ⟨a, b, c, d, ab, cd, disj⟩ := bad
     have hab := ab.1
     have hcd := cd.1
     have row (u v w : Fin n) (vw : G.Adj v w) (uv : G.Adj u v) : ¬G.Adj u w :=
       fun uw => tri u v w uv vw uw.symm
     have diag {u v w z : Fin n} (uv : G.Adj u v) (wz : G.Adj w z)
         (uw : G.Adj u w) (uz : u ≠ z) (vw : v ≠ w) : ¬G.Adj v z :=
       fun vz => (square u v z w uv vz wz.symm uw.symm).elim uz vw
     unfold meet at disj ⊢
     by_cases ac : G.Adj a c
     · exact ⟨b,a,d,c,flip ab,flip cd,by tauto,
         diag hab hcd ac (by tauto) (by tauto),
         fun bc => row c a b hab ac.symm bc.symm, row a c d hcd ac⟩
     by_cases ad : G.Adj a d
     · exact ⟨b,a,c,d,flip ab,cd,by tauto,
         diag hab hcd.symm ad (by tauto) (by tauto),
         fun bd => row d a b hab ad.symm bd.symm, ac⟩
     by_cases bc : G.Adj b c
     · exact ⟨a,b,d,c,ab,flip cd,by tauto,ad,ac,row b c d hcd bc⟩
     exact ⟨a,b,c,d,ab,cd,disj,ac,ad,bc⟩
   let realises := fun C : Circuit => Monotone2 C ∧ circuitFun n C = graphFun G ∅
   obtain ⟨seed, hm, hf⟩ := h1 n G
   have sizes : ∃ s, ∃ C : Circuit, realises C ∧ C.size = s :=
     ⟨seed.size, seed, ⟨hm, hf⟩, rfl⟩
   let s := Nat.find sizes
   have least (C : Circuit) (h : realises C) : s ≤ C.size :=
     Nat.find_min' sizes ⟨C, h, rfl⟩
   have cleanPrefix (k : ℕ) : ∃ C : Circuit, realises C ∧ C.size = s ∧ ∀ j < k, clean C j := by
     induction k with
     | zero =>
       obtain ⟨C, h, hs⟩ := Nat.find_spec sizes
       exact ⟨C, h, hs, fun j hj => (Nat.not_lt_zero j hj).elim⟩
     | succ k ih =>
       obtain ⟨C, h, hs, prev⟩ := ih
       by_cases good : clean C k
       · exact ⟨C,h,hs, fun j hj => (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)).elim
           (prev j) (fun e => e ▸ good)⟩
       obtain ⟨a,b,c,d,ab,cd,disj,ac,ad,bc⟩ := orient good
       have minC : IsMinimalMonoCircuit n C :=
         ⟨h.1, fun E mono same => hs ▸ least E ⟨mono, same.trans h.2⟩⟩
       obtain ⟨D, mono, correct, small, fixed⟩ :=
         h2 n G tri square C k minC h.2 prev a b c d ab cd disj ac ad bc
       have hD : realises D := ⟨mono, correct⟩
       exact ⟨D, hD, le_antisymm (small.trans hs.le) (least D hD),
         fun j hj => fixed j (Nat.le_of_lt_succ hj)⟩
   obtain ⟨C, h, hs, allClean⟩ := cleanPrefix s
   refine ⟨C, h.1, h.2, fun D hm hf => hs ▸ least D ⟨hm, hf⟩, ?_⟩
   intro j hj _
   have pairs := allClean j (hs ▸ (show j < C.size from hj))
   by_cases empty : ∀ u v, ¬edge C j u v
   · exact Or.inl (fun u v adj owns => empty u v ⟨adj, owns⟩)
   push Not at empty
   obtain ⟨a, b, ab⟩ := empty
   right
   by_cases center : ∀ u v, edge C j u v → u = a ∨ v = a
   · exact ⟨a, fun u v adj owns => center u v ⟨adj, owns⟩⟩
   push Not at center
   obtain ⟨p, q, pq, pa, qa⟩ := center
   -- The second edge misses a and meets ab at b. An edge missing b would close a triangle.
   have neighbor : ∃ z, z ≠ a ∧ edge C j b z := by
     rcases pairs a b p q ab pq with e | e | e | e
     · exact (pa e.symm).elim
     · exact (qa e.symm).elim
     · exact ⟨q, qa, e ▸ pq⟩
     · exact ⟨p, pa, e ▸ flip pq⟩
   obtain ⟨z, za, bz⟩ := neighbor
   refine ⟨b, ?_⟩
   intro u v adj owns
   have uv : edge C j u v := ⟨adj, owns⟩
   have first := pairs a b u v ab uv
   have second := pairs b z u v bz uv
   change a = u ∨ a = v ∨ b = u ∨ b = v at first
   change b = u ∨ b = v ∨ z = u ∨ z = v at second
   have noZA := tri a b z ab.1 bz.1
   have noAZ : ¬G.Adj a z := fun az => noZA az.symm
   by_contra misses
   have bu : b ≠ u := fun e => misses (Or.inl e.symm)
   have bv : b ≠ v := fun e => misses (Or.inr e.symm)
   have ha : a = u ∨ a = v := by tauto
   have hz := (second.resolve_left bu).resolve_left bv
   rcases ha with rfl | rfl <;> rcases hz with rfl | rfl
   all_goals first | exact za rfl | exact noAZ adj | exact noZA adj)
