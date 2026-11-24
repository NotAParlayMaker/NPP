import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2662_44
  (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    Monotone2 C → circuitFun n C = NestedCover.graphFun G ∅ →
    ∀ S ⊆ G.edgeFinset, (S.biUnion Sym2.toFinset).card ≤ C.size + 1)
  (extend : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (hGirth : ∀ v (p : H.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (mono : Monotone2 C) (j : ℕ) (a c : Fin m) (T : Finset (Fin m))
    (ac : a ≠ c) (deg : T.card + 2 < H.degree c)
    (singleton : gateVal m C j (pairInput a a) = true), ∃ b ∉ T, a ≠ b ∧ ¬H.Adj a b ∧ gateVal m C j (pairInput a b) = true)
  (core : ∃ (k m d : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
 (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) → (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
 ∀ (C : Circuit), IsMinimalMonoCircuit n C → circuitFun n C = NestedCover.graphFun G ∅ →
 ∀ S ⊆ G.edgeFinset, (∀ v ∈ S.biUnion Sym2.toFinset, d < (S.filter fun e => v ∈ e).card) →
 (∀ (u v : Fin n), s(u,v) ∈ S → ∀ j : Fin C.size, Owns n C j u v →
   ∀ B : Finset (Fin n), B.card ≤ k → u ∉ B → v ∉ B →
   ∃ a ∉ B, ∃ b ∉ B, a ≠ b ∧ ¬G.Adj a b ∧ gateVal n C j (pairInput a b) = true) →
 S.card ≤ m * (C.size+1)) :
∃ (x1 : ℕ) (x2 : ℕ), ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj], (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) → (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) → ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 → PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ → ∀ x11 ⊆ x4.edgeFinset, (∀ x13 ∈ x11, ∀ (x15 x16 : Fin x3), x13 = s(x15, x16) → ∀ (x18 : Fin x8.gates.length), PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 → have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true; have x21 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x21 : Fin x3 × Fin x3) => {x21.1, x21.2} \ {x15, x16}; x20 x15 x15 ∨ x20 x16 x16 ∨ ∃ (x22 : Finset (Fin x3 × Fin x3)), x22.card = x1 + (3 : ℕ) ∧ (∀ x23 ∈ x22, x20 x23.1 x23.2 ∧ ¬x4.Adj x23.1 x23.2) ∧ ∀ x23 ∈ x22, ∀ x25 ∈ x22, x23 ≠ x25 → Disjoint (x21 x23) (x21 x25)) → x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  classical
  have peel (n K : ℕ) (S : Finset (Sym2 (Fin n))) :
      ∃ T ⊆ S, (∀ v ∈ T.biUnion Sym2.toFinset, K < (T.filter fun e => v ∈ e).card) ∧
          S.card + K * (T.biUnion Sym2.toFinset).card ≤ T.card + K * (S.biUnion Sym2.toFinset).card := by
    classical
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases dense : ∀ v ∈ S.biUnion Sym2.toFinset, K < (S.filter fun e => v ∈ e).card
      · exact ⟨S,Finset.Subset.rfl,dense,le_rfl⟩
      push Not at dense
      obtain ⟨v,hv,hdeg⟩ := dense
      let U := S.filter fun e => v ∉ e
      have us : U ⊆ S := Finset.filter_subset _ _
      obtain ⟨e,he,ve⟩ := Finset.mem_biUnion.mp hv
      have ve' : v ∈ e := Sym2.mem_toFinset.mp ve
      have strict : U ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨us, fun eq =>
        (Finset.mem_filter.mp (show e ∈ U from eq ▸ he)).2 ve'⟩
      obtain ⟨T,hT,ht,c⟩ := ih U strict
      have vu : U.biUnion Sym2.toFinset ⊆ (S.biUnion Sym2.toFinset).erase v := by
        intro w hw
        obtain ⟨a,ha,wa⟩ := Finset.mem_biUnion.mp hw
        refine Finset.mem_erase.mpr ⟨?_,Finset.mem_biUnion.mpr ⟨a,us ha,wa⟩⟩
        intro eq
        exact (Finset.mem_filter.mp ha).2 (eq ▸ Sym2.mem_toFinset.mp wa)
      have small := Finset.card_le_card vu
      have pos := Finset.card_pos.mpr ⟨v,hv⟩
      rw [Finset.card_erase_of_mem hv] at small
      have du : (U.biUnion Sym2.toFinset).card + 1 ≤ (S.biUnion Sym2.toFinset).card := by omega
      have wt := Nat.mul_le_mul_left K du
      rw [Nat.mul_add, Nat.mul_one] at wt
      have split := Finset.card_filter_add_card_filter_not (s := S) (fun e => v ∈ e)
      change (S.filter fun e => v ∈ e).card + U.card = S.card at split
      exact ⟨T,Finset.Subset.trans hT us,ht,by omega⟩
  have avoid (n : ℕ) (u v : Fin n) (T : Finset (Fin n)) (hu : u ∉ T) (hv : v ∉ T)
      (P : Finset (Fin n × Fin n)) (large : T.card < P.card)
      (hp : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → Disjoint
        (({a.1,a.2} : Finset (Fin n)) \ {u,v}) (({b.1,b.2} : Finset (Fin n)) \ {u,v})) :
      ∃ a ∈ P, a.1 ∉ T ∧ a.2 ∉ T := by
    classical
    by_contra! h
    have pick (z : P) : ∃ w : T, w.val ∈ (({z.val.1,z.val.2} : Finset (Fin n)) \ {u,v}) := by
      by_cases hz : z.val.1 ∈ T
      · exact ⟨⟨_,hz⟩,Finset.mem_sdiff.mpr ⟨by simp,by simpa [eq_comm] using
          (show z.val.1 ≠ u ∧ z.val.1 ≠ v from ⟨fun e => hu (e ▸ hz),fun e => hv (e ▸ hz)⟩)⟩⟩
      · have h2 := h z z.property hz
        exact ⟨⟨_,h2⟩,Finset.mem_sdiff.mpr ⟨by simp,by simpa [eq_comm] using
          (show z.val.2 ≠ u ∧ z.val.2 ≠ v from ⟨fun e => hu (e ▸ h2),fun e => hv (e ▸ h2)⟩)⟩⟩
    choose f hf using pick
    have inj : Function.Injective f := by
      intro a b ab
      by_contra ne
      have hd := hp a a.property b b.property (fun eq => ne (Subtype.ext eq))
      exact Finset.disjoint_left.mp hd (hf a) (ab ▸ hf b)
    have bound := Fintype.card_le_of_injective f inj
    simpa using (show P.card ≤ T.card by simpa using bound) |>.not_gt large
  obtain ⟨k,m,d,hcore⟩ := core
  let D := max d (k+2)
  refine ⟨k,m+D,?_⟩
  intro n G inst deg girth C hmin funG S hs dirty
  obtain ⟨T,ht,high,cost⟩ := peel n D S
  have hTG := Finset.Subset.trans ht hs
  have bounded := hcore n G deg girth C hmin funG T hTG
    (fun v h => lt_of_le_of_lt (Nat.le_max_left _ _) (high v h))
  have tsize : T.card ≤ m * (C.size+1) := by
    apply bounded
    intro u v uv j own B small hu hv
    have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (hTG uv)
    have ends (c : Fin n) (mem : c ∈ s(u,v)) : B.card+2 < G.degree c := by
      have h := high c (Finset.mem_biUnion.mpr ⟨s(u,v),uv,Sym2.mem_toFinset.mpr mem⟩)
      have cap : (T.filter fun e => c ∈ e).card ≤ G.degree c := by
        rw [← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter]
        exact Finset.card_le_card (Finset.filter_subset_filter _ hTG)
      have mxd : k+2 ≤ D := Nat.le_max_right _ _
      omega
    have long (a : Fin n) (ha : a ∉ B) (on : gateVal n C j (pairInput a a) = true) :
        ∃ z ∉ B, ∃ w ∉ B, z ≠ w ∧ ¬G.Adj z w ∧ gateVal n C j (pairInput z w) = true := by
      obtain ⟨c,ac,mc⟩ : ∃ c : Fin n, a ≠ c ∧ c ∈ s(u,v) := by
        by_cases aa : a = u
        · exact ⟨v,aa ▸ adj.ne,by simp⟩
        · exact ⟨u,aa,by simp⟩
      obtain ⟨b,bB,ab,non,ok⟩ := extend n G girth C hmin.1 j a c B ac (ends c mc) on
      exact ⟨a,ha,b,bB,ab,non,ok⟩
    rcases dirty _ (ht uv) u v rfl j own with on|on|⟨P,count,spurious,apart⟩
    · exact long u hu on
    · exact long v hv on
    · obtain ⟨a,ap,h₁,h₂⟩ := avoid n u v B hu hv P (by omega) apart
      obtain ⟨yes,non⟩ := spurious a ap
      by_cases eq : a.1 = a.2
      · apply long a.1 h₁
        simpa only [← eq] using yes
      · exact ⟨a.1,h₁,a.2,h₂,eq,non,yes⟩
  have total := support n G C hmin.1 funG S hs
  have weight := Nat.mul_le_mul_left D total
  rw [Nat.add_mul]
  omega
