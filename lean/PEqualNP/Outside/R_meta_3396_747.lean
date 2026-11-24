import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- The augmentation preserves the gate deficit and gives a perfect matching.
-- A matched edge reserves one repeated wire. The remaining charge is half
-- the sum of vertex degrees in excess of two. It is zero on unions of cycles.
theorem PEqualNP.Outside.R_meta_3396_747
  (augment :
    let sq := fun (n m : ℕ) (E : Finset (Fin n × Fin m)) => ∀ p q l r, p ≠ q → l ≠ r → ¬((p,l) ∈ E ∧ (p,r) ∈ E ∧ (q,l) ∈ E ∧ (q,r) ∈ E)
    let ok := fun (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (n+m) C ∧ ∀ x, PEqualNP.MetaComplexity.circuitFun (n+m) C x = decide (∃ p l, (p,l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)
    ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit), E.Nonempty → sq n m E → ok n m E C → M ⊆ E → (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) → (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) → ∃ (N : ℕ) (F : Finset (Fin N × Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit), sq N N F ∧ (∀ i, (i,i) ∈ F ∧ (∃ j ≠ i, (i,j) ∈ F) ∧ ∃ j ≠ i, (j,i) ∈ F) ∧ ok N N F D ∧ E.card+M.card+D.size ≤ F.card+N+C.size)
  (budget : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    G.edgeFinset.Nonempty → IsLeastAO G C →
    let r := C.output :: C.gates.flatMap Gate.inputs
    G.support.ncard +
      (∑ w ∈ r.toFinset, (r.count w - 1)) ≤ C.size+1)
  (matching : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (T : Finset (Fin n × Fin n)), NoFourCycle G → (∀ v, (G.neighborSet v).ncard ≠ 1) →
    IsLeastAO G C → (∀ e ∈ T, G.Adj e.1 e.2) →
    (∀ e ∈ T, ∀ d ∈ T, e.1 = d.1 → e = d) → (∀ e ∈ T, ∀ d ∈ T, e.2 = d.2 → e = d) →
    (∀ e ∈ T, ∀ d ∈ T, e.1 ≠ d.2) →
    let r := C.output :: C.gates.flatMap Gate.inputs
    T.card ≤ (r.toFinset.filter (fun w => 2 ≤ r.count w)).card)
  (surplus : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (T : Finset (Fin n × Fin n)), NoFourCycle G → (∀ v, (G.neighborSet v).ncard ≠ 1) →
    (∃ color : Fin n → Bool, ∀ v w, G.Adj v w → color v ≠ color w) →
    IsLeastAO G C → 2*T.card = n → (∃ v, 3 ≤ G.degree v) → (∀ e ∈ T, G.Adj e.1 e.2) →
    (∀ e ∈ T, ∀ d ∈ T, e.1 = d.1 → e = d) → (∀ e ∈ T, ∀ d ∈ T, e.2 = d.2 → e = d) →
    (∀ e ∈ T, ∀ d ∈ T, e.1 ≠ d.2) →
    let r := C.output :: C.gates.flatMap Gate.inputs
    (∃ v : Fin n, 0 < G.degree v ∧ 2*r.count v.val ≤ G.degree v) →
    let b := (r.toFinset.filter (fun w => 2 ≤ r.count w)).card
    (∑ v, (G.degree v - 2)) ≤ 2 * ((b - T.card) + ∑ w ∈ r.toFinset, (r.count w - 2)))
  : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →     PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →       (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →         x4 ⊆ x3 →           (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →             (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →               have x12 : Fin x1 × Fin x2 → Prop := fun (x12 : Fin x1 × Fin x2) => (∀ x13 ∈ x3, x13.1 = x12.1 → x13 = x12) ∨ ∀ x13 ∈ x3, x13.2 = x12.2 → x13 = x12;               (∀ x13 ∈ x3, ¬x12 x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  have embedding : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)),
      (∀ p q l s, p ≠ q → l ≠ s →
        ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      M ⊆ E →
      (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) →
      (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
      (∀ e ∈ E, ¬ ((∀ d ∈ E, d.1 = e.1 → d = e) ∨
        (∀ d ∈ E, d.2 = e.2 → d = e))) →
      ∃ (G : SimpleGraph (Fin (n+m))) (T : Finset (Fin (n+m) × Fin (n+m))),
        ∀ [DecidableRel G.Adj],
        G.edgeFinset.card = E.card ∧ T.card = M.card ∧ NoFourCycle G ∧
        (∃ c : Fin (n+m) → Bool, ∀ u v, G.Adj u v → c u ≠ c v) ∧
        (∀ u, (G.neighborSet u).ncard ≠ 1) ∧
        (∀ e ∈ T, G.Adj e.1 e.2) ∧
        (∀ e ∈ T, ∀ d ∈ T, e.1 = d.1 → e = d) ∧
        (∀ e ∈ T, ∀ d ∈ T, e.2 = d.2 → e = d) ∧
        (∀ e ∈ T, ∀ d ∈ T, e.1 ≠ d.2) ∧
        ∀ z, graphFun G ∅ z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) := by
    classical
    intro n m E M square sub row col noLeaf
    let L : Fin n → Fin (n+m) := Fin.castAdd m
    let R : Fin m → Fin (n+m) := Fin.natAdd n
    have Linj : Function.Injective L := Fin.castAdd_injective _ _
    have Rinj : Function.Injective R := Fin.natAdd_injective _ _
    have disj (p : Fin n) (l : Fin m) : L p ≠ R l := by
      intro h
      have bad := congrArg Fin.val h
      change p.val = n+l.val at bad
      omega
    have split (x : Fin (n+m)) : (∃ p, x = L p) ∨ ∃ l, x = R l :=
      Fin.addCases (fun p => Or.inl ⟨p,rfl⟩) (fun l => Or.inr ⟨l,rfl⟩) x
    let G : SimpleGraph (Fin (n+m)) := {
      Adj := fun u v => ∃ p l, (p,l) ∈ E ∧
        ((u=L p ∧ v=R l) ∨ (u=R l ∧ v=L p))
      symm := by
        constructor
        rintro _ _ ⟨p,l,he,h⟩
        exact ⟨p,l,he,h.elim (fun xy => Or.inr ⟨xy.2,xy.1⟩) (fun xy => Or.inl ⟨xy.2,xy.1⟩)⟩
      loopless := by
        constructor
        rintro a ⟨p,l,_,h⟩
        rcases h with ⟨v,w⟩|⟨w,v⟩ <;> exact disj p l (v.symm.trans w)
    }
    have lr (p l) : G.Adj (L p) (R l) ↔ (p,l) ∈ E := by
      constructor
      · rintro ⟨a,b,he,h⟩
        rcases h with ⟨u,v⟩ | ⟨u,v⟩
        · rwa [Linj u,Rinj v]
        · exact (disj _ _ u).elim
      · exact fun h => ⟨p,l,h,Or.inl ⟨rfl,rfl⟩⟩
    have rl (l p) : G.Adj (R l) (L p) ↔ (p,l) ∈ E := (G.adj_comm _ _).trans (lr p l)
    have ll (p q) : ¬G.Adj (L p) (L q) := by
      rintro ⟨i,j,_,h⟩
      rcases h with ⟨_,h⟩|⟨h,_⟩ <;> exact disj _ _ h
    have rr (l k) : ¬G.Adj (R l) (R k) := by
      rintro ⟨i,j,_,h⟩
      rcases h with ⟨h,_⟩|⟨_,h⟩ <;> exact disj _ _ h.symm
    let pack : Fin n × Fin m ↪ Fin (n+m) × Fin (n+m) :=
      ⟨fun e => (L e.1,R e.2),fun a b h => Prod.ext (Linj (congrArg Prod.fst h)) (Rinj (congrArg Prod.snd h))⟩
    let und (e : Fin n × Fin m) : Sym2 (Fin (n+m)) := s(L e.1,R e.2)
    have inj : Function.Injective und := by
      intro a b h
      rcases Sym2.eq_iff.mp h with ⟨u,v⟩ | ⟨u,_⟩
      · exact Prod.ext (Linj u) (Rinj v)
      · exact (disj _ _ u).elim
    refine ⟨G,M.map pack,?_⟩
    intro decG
    have image : G.edgeFinset = E.image und := by
      ext e
      induction e using Sym2.inductionOn with
      | _ u v =>
        rw [SimpleGraph.mem_edgeFinset,Finset.mem_image]
        constructor
        · rintro ⟨p,l,he,h⟩
          exact ⟨(p,l),he,Sym2.eq_iff.mpr (h.elim (fun xy => Or.inl ⟨xy.1.symm,xy.2.symm⟩) (fun xy => Or.inr ⟨xy.2.symm,xy.1.symm⟩))⟩
        · rintro ⟨⟨p,l⟩,he,h⟩
          rcases Sym2.eq_iff.mp h with ⟨a,b⟩ | ⟨a,b⟩
          · exact ⟨p,l,he,Or.inl ⟨a.symm,b.symm⟩⟩
          · exact ⟨p,l,he,Or.inr ⟨b.symm,a.symm⟩⟩
    refine ⟨by rw [image,Finset.card_image_of_injective _ inj],Finset.card_map _,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro a b ne
      apply Finset.card_le_one.mpr
      intro c hc d hd
      obtain ⟨ac,bc⟩ := (Finset.mem_filter.mp hc).2
      obtain ⟨ad,bd⟩ := (Finset.mem_filter.mp hd).2
      rcases split a with ⟨p,rfl⟩|⟨p,rfl⟩ <;> rcases split b with ⟨q,rfl⟩|⟨q,rfl⟩ <;>
        rcases split c with ⟨l,rfl⟩|⟨l,rfl⟩ <;> rcases split d with ⟨k,rfl⟩|⟨k,rfl⟩ <;>
        simp only [ll,rr,lr,rl] at ac bc ad bd
      · by_contra kd
        exact square p q l k (fun h => ne (congrArg L h)) (fun h => kd (congrArg R h)) ⟨ac,ad,bc,bd⟩
      · by_contra kd
        exact square l k p q (fun h => kd (congrArg L h)) (fun h => ne (congrArg R h)) ⟨ac,bc,ad,bd⟩
    · let color (v : Fin (n+m)) := decide (n ≤ v.val)
      have leftColor (p : Fin n) : color (L p) = false := decide_eq_false (Nat.not_le_of_lt p.isLt)
      have rightColor (l : Fin m) : color (R l) = true := decide_eq_true (Nat.le_add_right n l.val)
      refine ⟨color,?_⟩
      rintro _ _ ⟨p,l,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ <;> rw [leftColor,rightColor] <;> decide
    · intro u one
      obtain ⟨w,hw⟩ := Set.ncard_eq_one.mp one
      have uw : G.Adj u w := by change w ∈ G.neighborSet u; rw [hw]; exact Set.mem_singleton _
      have solo (v) (uv : G.Adj u v) : v = w := by
        change v ∈ G.neighborSet u at uv
        rwa [hw,Set.mem_singleton_iff] at uv
      rcases split u with ⟨p,rfl⟩|⟨l,rfl⟩ <;> rcases split w with ⟨s,rfl⟩|⟨t,rfl⟩
      · exact ll _ _ uw
      · apply noLeaf (p,t) ((lr _ _).mp uw)
        left
        rintro ⟨q,k⟩ h (eq : q = p)
        subst q
        exact Prod.ext rfl (Rinj (solo (R k) ((lr _ _).mpr h)))
      · apply noLeaf (s,l) ((rl _ _).mp uw)
        right
        rintro ⟨p,k⟩ h (eq : k = l)
        subst k
        exact Prod.ext (Linj (solo (L p) ((rl _ _).mpr h))) rfl
      · exact rr _ _ uw
    · intro e he
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp he
      exact (lr _ _).mpr (sub ha)
    · intro e he d hd eq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp he
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hd
      exact congrArg pack (row a ha b hb (Linj eq))
    · intro e he d hd eq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp he
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hd
      exact congrArg pack (col a ha b hb (Rinj eq))
    · intro e he d hd
      obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp he
      obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp hd
      exact disj _ _
    · intro z
      apply Bool.eq_iff_iff.mpr
      change (decide (∃ a ∈ (∅ : Finset (Fin (n+m))), z a = true) ||
        decide (∃ a b, G.Adj a b ∧ z a = true ∧ z b = true)) = true ↔ _
      simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
      constructor
      · rintro ⟨a,b,⟨p,l,he,h⟩,za,zb⟩
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨p,l,he,za,zb⟩
        · exact ⟨p,l,he,zb,za⟩
      · rintro ⟨p,l,he,zp,zl⟩
        exact ⟨L p,R l,(lr p l).mpr he,zp,zl⟩
  have onSquare (N : ℕ) (E M : Finset (Fin N × Fin N)) (C : Circuit)
      (h4 : ∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E))
      (model : IsAO2 (N+N) C)
      (computes : ∀ x, circuitFun (N+N) C x = decide (∃ p l, (p,l) ∈ E ∧
        x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true))
      (sub : M ⊆ E) (rows : ∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d)
      (cols : ∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d)
      (noLeaf : ∀ e ∈ E, ¬ ((∀ d ∈ E, d.1 = e.1 → d = e) ∨ ∀ d ∈ E, d.2 = e.2 → d = e))
      (perfect : M.card = N) : E.card + M.card ≤ C.size+1 := by
    by_cases full : E.Nonempty
    · obtain ⟨G,T,bridge⟩ := embedding N N E M h4 sub rows cols noLeaf
      obtain ⟨cardE,cardM,nc,color,hd,adj,tr,tc,disj,ev⟩ := bridge
      have ne : G.edgeFinset.Nonempty := Finset.card_pos.mp (cardE ▸ Finset.card_pos.mpr full)
      have same : circuitFun (N+N) C = graphFun G ∅ := funext (fun x => (computes x).trans (ev x).symm)
      let P (s : ℕ) := ∃ D : Circuit, IsAO2 (N+N) D ∧ circuitFun (N+N) D = graphFun G ∅ ∧ D.size = s
      have has : ∃ s, P s := ⟨C.size,C,model,same,rfl⟩
      obtain ⟨D,dm,de,ds⟩ := Nat.find_spec has
      have least : IsLeastAO G D := ⟨dm,de,fun A am ae => ds.trans_le (Nat.find_min' has ⟨A,am,ae,rfl⟩)⟩
      have leC := least.2.2 C model same
      let r := D.output :: D.gates.flatMap Gate.inputs
      let V := (Finset.univ.filter (fun v : Fin (N+N) => ∃ u, G.Adj v u)).card
      let B := (r.toFinset.filter (fun w => 2 ≤ r.count w)).card
      let U := ∑ w ∈ r.toFinset, (r.count w - 1)
      let H := ∑ w ∈ r.toFinset, (r.count w - 2)
      have vset : G.support = ↑(Finset.univ.filter (fun v : Fin (N+N) => ∃ u, G.Adj v u)) := by
        ext v
        simp only [SimpleGraph.mem_support,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and]
      have paid := budget _ G D ne least
      rw [vset,Set.ncard_coe_finset] at paid
      change V+U ≤ D.size+1 at paid
      have matched : T.card ≤ B := matching _ G D T nc hd least adj tr tc disj
      have split : U = B+H := by
        have e : B = ∑ w ∈ r.toFinset, (if 2 ≤ r.count w then 1 else 0 : ℕ) := by
          simp only [B,←Finset.sum_filter,Finset.sum_const,smul_eq_mul,mul_one]
        rw [e]; unfold U H
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w _
        split <;> omega
      have sumdeg : (∑ v, (G.degree v-2)) + 2*V = 2*G.edgeFinset.card := by
        have e : 2*V = ∑ v : Fin (N+N), (if ∃ u, G.Adj v u then 2 else 0 : ℕ) := by
          simp only [V,←Finset.sum_filter,Finset.sum_const,smul_eq_mul,Nat.mul_comm 2]
        rw [e,←Finset.sum_add_distrib,←G.sum_degrees_eq_twice_card_edges]
        apply Finset.sum_congr rfl
        intro v _
        have hdv := hd v
        rw [G.ncard_neighborSet] at hdv
        split
        · rename_i alive
          have pos := (G.degree_pos_iff_exists_adj v).mpr alive
          omega
        · rename_i dead
          have zero := mt (G.degree_pos_iff_exists_adj v).mp dead
          omega
      by_cases light : ∃ v : Fin (N+N), 0 < G.degree v ∧ 2*r.count v.val ≤ G.degree v
      · by_cases high : ∃ v, 3 ≤ G.degree v
        · have rest : (∑ v, (G.degree v-2)) ≤ 2*((B-T.card)+H) :=
            surplus _ G D T nc hd color least (by omega) high adj tr tc disj light
          omega
        · have none : (∑ v, (G.degree v-2)) = 0 := by
            apply Finset.sum_eq_zero
            intro v _
            have small : ¬ 3 ≤ G.degree v := fun hv => high ⟨v,hv⟩
            omega
          omega
      · let A := Finset.univ.filter (fun v : Fin (N+N) => ∃ u, G.Adj v u)
        have good (v) (hv : v ∈ A) : G.degree v + 1 ≤ 2*r.count v.val := by
          have h := (G.degree_pos_iff_exists_adj v).mpr (Finset.mem_filter.mp hv).2
          exact Nat.lt_of_not_ge (fun small => light ⟨v,h,small⟩)
        have cc : 2*T.card ≤ A.card := by
          let X := T.image Prod.fst
          let Y := T.image Prod.snd
          have cx : X.card = T.card := Finset.card_image_of_injOn (by intro a ha b hb h; exact tr a ha b hb h)
          have cy : Y.card = T.card := Finset.card_image_of_injOn (by intro a ha b hb h; exact tc a ha b hb h)
          have sep : Disjoint X Y := Finset.disjoint_left.mpr (by
            intro v vx vy
            obtain ⟨e,he,ep⟩ := Finset.mem_image.mp vx
            obtain ⟨f,hf,fp⟩ := Finset.mem_image.mp vy
            exact disj e he f hf (ep.trans fp.symm))
          have incl : X ∪ Y ⊆ A := by
            intro v hv
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _,?_⟩
            rcases Finset.mem_union.mp hv with h | h
            · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h; exact ⟨_,adj e he⟩
            · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h; exact ⟨_,(adj e he).symm⟩
          have counted := Finset.card_le_card incl
          rw [Finset.card_union_of_disjoint sep,cx,cy] at counted
          omega
        have cap : (∑ v ∈ A, (r.count v.val - 1)) ≤ U := by
          let mapped := A.image Fin.val
          have incl : mapped ⊆ r.toFinset := by
            intro k hk
            obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
            apply List.mem_toFinset.mpr
            apply List.count_pos_iff.mp
            have := good v hv
            omega
          change _ ≤ ∑ w ∈ r.toFinset, (r.count w - 1)
          apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg incl (fun _ _ _ => Nat.zero_le _))
          change _ ≤ ∑ w ∈ A.image Fin.val, (r.count w-1)
          rw [Finset.sum_image (fun a _ b _ h => Fin.ext h)]
        have all_deg : (∑ v ∈ A, G.degree v) = 2*G.edgeFinset.card := by
          rw [←G.sum_degrees_eq_twice_card_edges]
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ nv
          have absent : ¬ ∃ u, G.Adj v u := by simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using nv
          have := mt (G.degree_pos_iff_exists_adj v).mp absent
          omega
        have sumgood : (∑ v ∈ A, G.degree v)+A.card ≤ 2*(A.card + ∑ v ∈ A, (r.count v.val-1)) := by
          have H := Finset.sum_le_sum (s:=A) (f:= fun v => G.degree v+1)
            (g:=fun v => 2*(1+(r.count v.val-1))) (fun v hv => by have := good v hv; omega)
          simpa only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one,←Finset.mul_sum] using H
        change 2*T.card ≤ V at cc
        change (∑ v ∈ A, G.degree v)+V ≤ 2*(V+∑ v ∈ A, (r.count v.val-1)) at sumgood
        omega
    · have e0 := Finset.not_nonempty_iff_eq_empty.mp full
      have m0 : M = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro a ha
        have := sub ha
        simp only [e0,Finset.notMem_empty] at this)
      simp only [e0,m0,Finset.card_empty,Nat.zero_add,Nat.zero_le]
  intro n m E M C h4 model ev subset row col _
  by_cases ne : E.Nonempty
  · obtain ⟨N,F,D,square,ng,ok,cost⟩ := augment n m E M C ne h4 ⟨model,ev⟩ subset
      (fun e he d hd h => row e he d hd h) (fun e he d hd h => col e he d hd h)
    let diag := (Finset.univ : Finset (Fin N)).image (fun i => (i,i))
    have mem (e : Fin N × Fin N) : e ∈ diag ↔ e.1 = e.2 := by
      constructor
      · intro h
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
        rfl
      · intro h
        exact Finset.mem_image.mpr ⟨e.1,Finset.mem_univ _,Prod.ext rfl h⟩
    have count : diag.card = N := by
      dsimp [diag]
      rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
      exact Finset.card_fin N
    have noLeaf : ∀ e ∈ F, ¬ ((∀ d ∈ F, d.1 = e.1 → d = e) ∨ ∀ d ∈ F, d.2 = e.2 → d = e) := by
      intro e _
      rintro (left | right)
      · obtain ⟨j,ne,alt⟩ := (ng e.1).2.1
        have eq := (left _ alt rfl).trans (left _ (ng e.1).1 rfl).symm
        exact ne (congrArg Prod.snd eq)
      · obtain ⟨j,ne,alt⟩ := (ng e.2).2.2
        have eq := (right _ alt rfl).trans (right _ (ng e.2).1 rfl).symm
        exact ne (congrArg Prod.fst eq)
    have result := onSquare N F diag D square ok.1 ok.2 (by
      intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact (ng i).1) (by
      intro e he d hd h
      exact Prod.ext h (((mem e).mp he).symm.trans (h.trans ((mem d).mp hd)))) (by
      intro e he d hd h
      exact Prod.ext (((mem e).mp he).trans (h.trans ((mem d).mp hd).symm)) h) noLeaf count
    omega
  · have nil := Finset.not_nonempty_iff_eq_empty.mp ne
    have no : M = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => by have := subset ha; simp [nil] at this)
    simp [nil,no]
