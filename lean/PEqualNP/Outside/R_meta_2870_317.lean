import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_2870_317
    (compress : ∀ (N : ℕ) (C : Circuit), Monotone2 C → C.output < N+N+C.size →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∃ a b : ℕ, g.inputs = [a,b] ∧ a < b ∧ b < N+N+j) →
      ∀ J : Finset ℕ, (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and →
        (∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
          (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
          (C.wires (List.ofFn x ++ List.replicate N true)).getD w false) → j ∈ J) →
      ∀ X Y : Finset (Fin N), C.eval (incidenceInput X Y) = true →
        ∃ S ⊆ Y, S.card ≤ J.card+1 ∧ ∀ X' : Finset (Fin N), X ⊆ X' → C.eval (incidenceInput X' S) = true)
    (globalBound : ∀ (q N : ℕ) (A : Fin N → Finset (Fin N)) (C : Circuit),
      100 < q → N = q^2+q+1 → (∀ l, (A l).card=q+1) →
      (∀ p p' : Fin N, p≠p' → ∃! l, p∈A l ∧ p'∈A l) →
      Monotone2 C → RightOnIncidentPairs A C →
      let bad (S : Finset (Fin N)) := C.eval (incidenceInput (zeroSet A S) S)
      (∀ S, bad S = false) →
      (∃ g ∈ C.gates, g.op = .and ∧ ∃ b : Bool, ∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
        let row (v : Bool) := if b then List.ofFn x ++ List.replicate N v else List.replicate N v ++ List.ofFn x
        (C.wires (row false)).getD w false ≠ (C.wires (row true)).getD w false) → N*q ≤ 100*C.size)
    (overflowBound : ∀ (q N : ℕ) (A : Fin N → Finset (Fin N)) (C : Circuit),
      100 < q → N = q^2+q+1 → (∀ l, (A l).card=q+1) →
      (∀ p p' : Fin N, p≠p' → ∃! l, p∈A l ∧ p'∈A l) →
      Monotone2 C → RightOnIncidentPairs A C →
      let bad (S : Finset (Fin N)) := C.eval (incidenceInput (zeroSet A S) S)
      (∀ S, S.card ≤ q → bad S = false) →
      ∀ (J : Finset ℕ) (S : Finset (Fin N)),
        (∀ j ∈ J, ∃ g : Gate, C.gates[j]? = some g ∧ g.op = .and ∧
          ∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
           (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
           (C.wires (List.ofFn x ++ List.replicate N true)).getD w false) →
        100*J.card < N*q → q < S.card → S.card ≤ J.card+1 → bad S = true →
        (∀ l ∈ S, bad (S.erase l) = false) → N*q ≤ 100*C.size)
:
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  classical
  intro marked q N I dec C big nGeom lineCard unique mono outBound ordered positive sparse J js jpos marks jsz
  let A : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun p => I p l)
  have memA (p l : Fin N) : p ∈ A l ↔ I p l := by simp [A]
  have gCard (l : Fin N) : (A l).card = q+1 := by simpa only [A,Fintype.card_subtype] using lineCard l
  have gUnique (p t : Fin N) (ne : p ≠ t) : ∃! l, p ∈ A l ∧ t ∈ A l := by simpa only [memA] using unique p t ne
  let row (X Y : Finset (Fin N)) := Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have leftVal (X Y : Finset (Fin N)) (p : Fin N) : row X Y (Fin.castAdd N p) = decide (p∈X) := Fin.append_left _ _ _
  have rightVal (X Y : Finset (Fin N)) (l : Fin N) : row X Y (Fin.natAdd N l) = decide (l∈Y) := Fin.append_right _ _ _
  have dis (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro h;have h' := congrArg Fin.val h;change p.val = N + l.val at h';omega
  have rightInj (i l : Fin N) : Fin.natAdd N i = Fin.natAdd N l ↔ i=l := by
    constructor
    · intro h;apply Fin.ext;have h' := congrArg Fin.val h;change N+i.val=N+l.val at h';omega
    · exact congrArg _
  have ev (X Y : Finset (Fin N)) : circuitFun (N+N) C (row X Y) = C.eval (incidenceInput X Y) := by
    change C.eval (List.ofFn (Fin.append (fun p : Fin N => decide (p∈X)) (fun l : Fin N => decide (l∈Y)))) = C.eval (List.ofFn (fun p : Fin N => decide (p∈X)) ++ List.ofFn (fun l : Fin N => decide (l∈Y)))
    rw [List.ofFn_fin_append]
  have on : RightOnIncidentPairs A C := by
    intro l p hp
    have eq : (fun w : Fin (N+N) => decide (w=Fin.castAdd N p ∨ w=Fin.natAdd N l)) = row {p} {l} := by
      funext w
      refine Fin.addCases ?_ ?_ w
      · intro i;rw [leftVal];simp only [Fin.castAdd_inj,dis,or_false,Finset.mem_singleton]
      · intro i;rw [rightVal];simp only [Ne.symm (dis p i),false_or,Finset.mem_singleton,rightInj]
    rw [←ev,←eq]
    exact positive p l ((memA p l).mp hp)
  let bad (S : Finset (Fin N)) := C.eval (incidenceInput (zeroSet A S) S)
  have off (S : Finset (Fin N)) (hs : S.card ≤ q) : bad S = false := by
    rw [show bad S = circuitFun (N+N) C (row (zeroSet A S) S) from (ev _ _).symm]
    apply sparse
    · simpa only [Fintype.card_subtype,rightVal,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter] using hs
    · rintro ⟨p,l,ip,hp,hl⟩
      rw [leftVal] at hp;rw [rightVal] at hl
      have hpp := (Finset.mem_filter.mp (of_decide_eq_true hp)).2
      exact hpp l (of_decide_eq_true hl) ((memA p l).mpr ip)
  by_cases alloff : ∀ S, bad S = false
  · apply globalBound q N A C big nGeom gCard gUnique mono on alloff
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (by omega : 0<J.card)
    have jr : j < C.gates.length := Finset.mem_range.mp (js hj)
    let g := C.gates[j]
    have member : C.gates[j]?=some g := List.getElem?_eq_some_iff.mpr ⟨jr,rfl⟩
    obtain ⟨ga,side⟩ := (marks j g member).mp hj
    refine ⟨g,List.mem_of_getElem? member,ga,?_⟩
    rcases side with side|side
    · exact ⟨true,side⟩
    · exact ⟨false,side⟩
  let charged (j : ℕ) := ∃ g : Gate, C.gates[j]? = some g ∧ g.op = .and ∧
    ∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
      (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
      (C.wires (List.ofFn x ++ List.replicate N true)).getD w false
  let L := J.filter charged
  have cap : 100*L.card < N*q := by
    have h : L.card ≤ J.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega
  have covers (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (op : g.op = .and)
      (d : ∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
        (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
        (C.wires (List.ofFn x ++ List.replicate N true)).getD w false) : j ∈ L := by
    exact Finset.mem_filter.mpr ⟨(marks j g hg).mpr ⟨op,Or.inl d⟩,g,hg,op,d⟩
  let E (k : ℕ) := ∃ S : Finset (Fin N), S.card=k ∧ bad S=true
  have ex : ∃ k, E k := by
    push_neg at alloff
    obtain ⟨S,hS⟩ := alloff
    exact ⟨S.card,S,rfl,by cases h : bad S with | false => exact (hS h).elim | true => rfl⟩
  obtain ⟨S,sz,yes⟩ := Nat.find_spec ex
  have minimal (T : Finset (Fin N)) (ht : bad T=true) : S.card ≤ T.card := by
    rw [sz];exact Nat.find_min' ex ⟨T,rfl,ht⟩
  obtain ⟨T,sub,tc,lift⟩ := compress N C mono outBound ordered L covers (zeroSet A S) S yes
  have zs : zeroSet A S ⊆ zeroSet A T := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, fun l hl => (Finset.mem_filter.mp hp).2 l (sub hl)⟩
  have ub := (minimal T (lift _ zs)).trans tc
  have lb : q < S.card := by by_contra! h; rw [off S h] at yes; contradiction
  have dels (l : Fin N) (hl : l ∈ S) : bad (S.erase l)=false := by
    cases h : bad (S.erase l) with
    | false => rfl
    | true => exact (False.elim ((Nat.not_lt_of_ge (minimal _ h)) (Finset.card_erase_lt_of_mem hl)))
  exact overflowBound q N A C big nGeom gCard gUnique mono on off L S
    (fun _ h => (Finset.mem_filter.mp h).2) cap lb ub yes dels
