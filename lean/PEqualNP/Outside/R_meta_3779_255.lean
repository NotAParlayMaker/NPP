import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

-- All quadrangles in this plane are projectively equivalent. The negative
-- test for the first AND below another AND can be fixed to points 0,1,2,5
-- and external lines 3,7,8. Their seven active input wires have mask 3211303.
set_option maxHeartbeats 30000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_3779_255
    (coverage : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      ∃ b ∈ ([39,71,135,2055,83,275,2067,1059,2083,195,1155,1283,2307,85,533,549,1061,1157] : List ℕ), ∃ t : Fin 13,
        Q = ((Finset.univ : Finset (Fin 13)).filter (fun p => b.testBit p.val)).image (fun p => p+t))
    (rename : let S := singerLines3
      let row (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
      let ok (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
      let inner (C : Circuit) (i : ℕ) := (gateAt C i).op = .and ∧
        ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
      let binary (C : Circuit) := ∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.Nodup
      ∀ P L : Equiv.Perm (Fin 13), (∀ p l, p ∈ S l ↔ P p ∈ S (L l)) →
      ∀ C : Circuit, ok C → binary C → ∃ E : Circuit, E.size = C.size ∧ ok E ∧ binary E ∧
        (∀ i, inner E i ↔ inner C i) ∧
        ∀ (Q : Finset (Fin 13)) (i : ℕ), IsQuadrangle S Q →
          (E.wires (row (Q.map P.toEmbedding))).getD (26+i) false =
          (C.wires (row Q)).getD (26+i) false)
    (fixedFrame : let S := singerLines3
      let row (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
      let ok (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
      let inner (C : Circuit) (i : ℕ) := (gateAt C i).op = .and ∧
        ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
      let binary (C : Circuit) := ∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.Nodup
      ∀ C : Circuit, ok C → C.size < 64 → binary C →
      (∀ D, ok D → C.size ≤ D.size) →
      (∀ i, inner C i → ∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+i) false = true) →
      ∀ i, inner C i → (∀ j < i, ¬ inner C j) →
        (C.wires (List.ofFn fun k : Fin 26 => (3211303 : ℕ).testBit k.val)).getD (26+i) false = false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 → x5.size < (64 : ℕ) → (∀ (x8 x9 : ℕ), x4 x5 x8 x9 → ∃ (x11 : List Bool), x2 Bool.false x11 ∧ (x5.wires x11).getD ((26 : ℕ) + x8) Bool.false = Bool.true) → (∃ (x9 : ℕ) (x10 : ℕ), x4 x5 x9 x10) → (∀ x10 ∈ x5.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x3 x11 ∧ x11.size < x5.size := by
  intro diff rows valid nested C validC small witnesses anyNested norm
  let S := singerLines3
  let row (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
  let ok (D : Circuit) := Monotone2 D ∧ ReadsBack 26 D ∧ RightOnIncidentPairs S D ∧
    ∀ Q, IsQuadrangle S Q → D.eval (row Q) = false
  let inner (D : Circuit) (i : ℕ) := (gateAt D i).op = .and ∧
    ∃ j, (gateAt D j).op = .and ∧ InCone 26 D i j
  let binary (D : Circuit) := ∀ g ∈ D.gates, g.inputs.length = 2 ∧ g.inputs.Nodup
  have geom : ∀ p l : Fin 13, p ∈ S l ↔ p-l ∈ diff := by decide +kernel
  have isQ (Q : Finset (Fin 13)) : IsQuadrangle S Q ↔
      Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p-l ∈ diff).card ≤ 2 := by
    have eq (l : Fin 13) : Q ∩ S l = Q.filter (fun p => p-l ∈ diff) := by
      ext p
      simp only [Finset.mem_inter,Finset.mem_filter]
      exact and_congr_right fun _ => geom p l
    change (_ ∧ ∀ l, (Q ∩ S l).card ≤ 2) ↔ _
    simp only [eq]
  have negRow (Q : Finset (Fin 13)) : row Q = (List.ofFn fun a : Fin 13 => decide (a ∈ Q)) ++
      List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ diff) := by
    change List.ofFn _ ++ List.ofFn _ = List.ofFn _ ++ List.ofFn _
    apply congrArg (List.append (List.ofFn fun p : Fin 13 => decide (p ∈ Q)))
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change (l ∈ (Finset.univ.filter fun w : Fin 13 => Disjoint (S w) Q)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right]
    exact forall₂_congr fun p _ => not_congr (geom p l)
  have posRow (p l : Fin 13) : incidenceInput {p} {l} =
      (List.ofFn fun a : Fin 13 => decide (a = p)) ++ List.ofFn fun b : Fin 13 => decide (b = l) := by
    change List.ofFn _ ++ List.ofFn _ = List.ofFn _ ++ List.ofFn _
    simp only [Finset.mem_singleton]
  have validIff (D : Circuit) : valid D ↔ ok D := by
    constructor
    · rintro ⟨mono,back,hits⟩
      refine ⟨mono,back,?_,?_⟩
      · intro l p hp
        rw [posRow]
        exact hits true _ ⟨p,l,(geom p l).1 hp,rfl⟩
      · intro Q hQ
        obtain ⟨card,lines⟩ := (isQ Q).1 hQ
        exact hits false _ ⟨Q,card,lines,negRow Q⟩
    · rintro ⟨mono,back,pos,neg⟩
      refine ⟨mono,back,?_⟩
      intro sign x hx
      cases sign with
      | true =>
        obtain ⟨p,l,inc,rfl⟩ := hx
        rw [← posRow]
        exact pos _ _ ((geom p l).2 inc)
      | false =>
        obtain ⟨Q,card,lines,rfl⟩ := hx
        rw [← negRow]
        exact neg Q ((isQ Q).2 ⟨card,lines⟩)
  have normC : binary C := by
    intro g hg
    obtain ⟨len,pins⟩ := norm g hg
    refine ⟨len,?_⟩
    cases h : g.inputs with
    | nil => simp [h] at len
    | cons a xs =>
      cases xs with
      | nil => simp [h] at len
      | cons b xs =>
        cases xs with
        | cons c xs => simp [h] at len
        | nil => simpa [h] using pins
  have existsInner : ∃ i, inner C i := by
    obtain ⟨i,j,p,q,h⟩ := anyNested
    exact ⟨i,p,j,q,h⟩
  have bad (i : ℕ) (h : inner C i) : ∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+i) false = true := by
    obtain ⟨p,j,q,hc⟩ := h
    obtain ⟨x,rx,fires⟩ := witnesses i j ⟨p,q,hc⟩
    obtain ⟨Q,card,lines,e⟩ := rx
    exact ⟨Q,(isQ Q).2 ⟨card,lines⟩,by rw [e, ← negRow] at fires; exact fires⟩
  let cert : List (List (Fin 13) × List (Fin 13)) := [
    ([0,1,2,3,4,5,6,7,8,9,10,11,12], [0,1,2,3,4,5,6,7,8,9,10,11,12]),
    ([0,1,2,9,10,6,5,11,8,3,4,7,12], [0,1,6,9,10,5,2,8,7,3,4,11,12]),
    ([0,1,2,9,4,7,11,5,12,3,10,6,8], [0,1,6,8,4,11,2,9,3,7,10,5,12]),
    ([0,1,2,3,10,11,7,6,12,9,4,5,8], [0,1,2,7,10,11,6,3,9,8,4,5,12]),
    ([0,1,4,3,10,6,8,11,5,9,2,12,7], [0,1,3,7,10,5,8,2,9,6,12,11,4]),
    ([0,1,4,9,2,8,6,12,5,3,10,11,7], [0,1,8,6,12,5,3,9,2,7,10,11,4]),
    ([0,1,4,9,10,11,12,6,7,3,2,8,5], [0,1,8,9,10,11,3,6,7,2,12,5,4]),
    ([0,1,5,9,6,10,2,11,4,3,8,12,7], [0,5,9,6,10,1,2,8,3,7,12,11,4]),
    ([0,1,5,3,6,11,12,10,7,9,8,2,4], [0,5,2,3,10,11,9,7,6,8,12,1,4]),
    ([0,1,6,9,5,7,12,4,11,3,8,2,10], [0,5,6,9,4,11,3,8,2,7,12,1,10]),
    ([0,1,7,3,11,10,2,6,4,9,12,8,5], [0,11,7,2,10,1,6,3,8,9,12,5,4]),
    ([0,1,8,3,6,10,4,11,2,9,5,7,12], [0,5,7,3,10,1,8,2,6,9,4,11,12]),
    ([0,1,8,9,6,11,7,10,12,3,5,4,2], [0,5,8,6,10,11,7,9,3,2,4,1,12]),
    ([0,2,4,12,10,6,9,11,7,8,1,3,5], [12,1,3,9,10,6,8,11,7,5,0,2,4]),
    ([0,2,4,8,1,9,6,3,7,12,10,11,5], [12,1,8,5,0,6,3,7,11,9,10,2,4]),
    ([0,2,5,12,3,9,6,1,7,8,11,10,4], [12,2,9,3,0,6,5,11,7,8,10,1,4]),
    ([0,2,5,12,11,10,1,6,4,8,3,9,7], [12,2,9,11,10,1,5,3,8,7,0,6,4]),
    ([0,2,7,8,6,10,1,11,4,12,9,3,5], [12,6,7,5,10,1,11,8,3,9,0,2,4])]
  let sig (a : List (Fin 13)) (x : Fin 13) := a.getD x.val 0
  let q0 : Finset (Fin 13) := {0, 1, 2, 5}
  have cert_good : ∀ m ∈ cert,
      Function.Bijective (sig m.1) ∧ Function.Bijective (sig m.2) ∧
      ∀ p l : Fin 13, p ∈ singerLines3 l ↔ sig m.1 p ∈ singerLines3 (sig m.2 l) := by
    intro m hm
    simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have translation_good : ∀ t p l : Fin 13,
      p ∈ singerLines3 l ↔ p + t ∈ singerLines3 (l + t) := by
    decide
  have indexed : ∀ b ∈ ([39,71,135,2055,83,275,2067,1059,2083,195,1155,1283,2307,85,533,549,1061,1157] : List ℕ), ∃ m ∈ cert,
      (Finset.univ.filter fun p : Fin 13 => b.testBit p.val) = q0.image (sig m.1) := by
    decide
  have cert_cover (Q : Finset (Fin 13)) (hQ : IsQuadrangle singerLines3 Q) :
      ∃ m ∈ cert, ∃ t : Fin 13, Q = (q0.image (sig m.1)).image (fun x => x + t) := by
    obtain ⟨b,hb,t,ht⟩ := coverage Q hQ
    obtain ⟨m,hm,he⟩ := indexed b hb
    exact ⟨m,hm,t,by rw [← he]; exact ht⟩
  have orbit (Q : Finset (Fin 13)) (hq : IsQuadrangle singerLines3 Q) :
      ∃ P L : Fin 13 ≃ Fin 13,
        (∀ p l, p ∈ singerLines3 l ↔ P p ∈ singerLines3 (L l)) ∧
        q0.map P.toEmbedding = Q := by
    obtain ⟨m, hm, t, hQ⟩ := cert_cover Q hq
    obtain ⟨hp, hl, he⟩ := cert_good m hm
    let P := (Equiv.ofBijective (sig m.1) hp).trans (Equiv.addRight t)
    let L := (Equiv.ofBijective (sig m.2) hl).trans (Equiv.addRight t)
    refine ⟨P, L, ?_, ?_⟩
    · intro p l
      exact (he p l).trans (translation_good t _ _)
    · rw [hQ, Finset.map_eq_image, Finset.image_image]
      rfl


  have preserves (P L : Equiv.Perm (Fin 13)) (col : ∀ p l, p ∈ S l ↔ P p ∈ S (L l))
      (Q : Finset (Fin 13)) (hq : IsQuadrangle S Q) : IsQuadrangle S (Q.map P.toEmbedding) := by
    refine ⟨by rw [Finset.card_map]; exact hq.1,?_⟩
    intro l
    have eq : (Q.map P.toEmbedding ∩ S l) = (Q ∩ S (L.symm l)).map P.toEmbedding := by
      ext p
      have mapMem (T : Finset (Fin 13)) : p ∈ T.map P.toEmbedding ↔ P.symm p ∈ T := by
        constructor
        · intro h
          obtain ⟨a,ha,pa⟩ := Finset.mem_map.mp h
          change P a = p at pa
          rw [← pa,P.symm_apply_apply]
          exact ha
        · intro h
          exact Finset.mem_map.mpr ⟨P.symm p,h,P.apply_symm_apply p⟩
      rw [Finset.mem_inter,mapMem,mapMem,Finset.mem_inter]
      have inc := col (P.symm p) (L.symm l)
      simpa only [P.apply_symm_apply,L.apply_symm_apply] using
        (and_congr_right (fun _ => inc.symm))
    rw [eq,Finset.card_map]
    exact hq.2 (L.symm l)
  classical
  let i := Nat.find existsInner
  have hi : inner C i := Nat.find_spec existsInner
  have first : ∀ j < i, ¬ inner C j := fun j hj => Nat.find_min existsInner hj
  obtain ⟨Q,hQ,fires⟩ := bad i hi
  obtain ⟨P0,L0,col0,frame0⟩ := orbit Q hQ
  let P := P0.symm
  let L := L0.symm
  have col (p l : Fin 13) : p ∈ S l ↔ P p ∈ S (L l) := by
    simpa only [Equiv.apply_symm_apply,P,L] using (col0 (P p) (L l)).symm
  have frame : Q.map P.toEmbedding = ({0,1,2,5} : Finset (Fin 13)) := by
    rw [← frame0]
    simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
      Equiv.coe_toEmbedding,P,Equiv.symm_apply_apply,Finset.image_id',q0]

  obtain ⟨E,sz,good,binaryE,inside,wire⟩ := rename P L col C ((validIff C).1 validC) normC
  by_contra no
  have least (D : Circuit) (hd : ok D) : E.size ≤ D.size := by
    rw [sz]
    by_contra! lt
    exact no ⟨D,(validIff D).2 hd,lt⟩
  have badE (j : ℕ) (hj : inner E j) :
      ∃ T, IsQuadrangle S T ∧ (E.wires (row T)).getD (26+j) false = true := by
    obtain ⟨T,ht,on⟩ := bad j ((inside j).1 hj)
    exact ⟨T.map P.toEmbedding,preserves P L col T ht,(wire T j ht).trans on⟩
  have frameRow : row ({0,1,2,5} : Finset (Fin 13)) =
      List.ofFn (fun k : Fin 26 => (3211303 : ℕ).testBit k.val) := by decide +kernel
  have off := fixedFrame E good (by rw [sz]; exact small) binaryE least badE i ((inside i).2 hi)
    (fun j hj h => first j hj ((inside j).1 h))
  have on := (wire Q i hQ).trans fires
  rw [frame] at on
  change (E.wires (row ({0,1,2,5} : Finset (Fin 13)))).getD (26+i) false = true at on
  rw [frameRow] at on
  exact Bool.false_ne_true (off.symm.trans on)
