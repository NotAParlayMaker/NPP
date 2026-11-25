import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_1749_649
    (columns :
        ∀ (A : Type) (n : ℕ) (C : Circuit), ReadsBack n C →
    ∀ rows : A → List Bool, (∀ x, (rows x).length = n) →
    ∃ v : ℕ → Set A,
      (∀ i < n, v i = {x | (rows x).getD i false = true}) ∧
      (∀ i, n + C.size ≤ i → v i = ∅) ∧
      (∀ j < C.size, let g := gateAt C j
        (g.op = .and → v (n+j) = {x | ∀ i ∈ g.inputs, x ∈ v i}) ∧
        (g.op = .or → v (n+j) = {x | ∃ i ∈ g.inputs, x ∈ v i})) ∧
      ∀ x, x ∈ v C.output ↔ C.eval (rows x) = true)
    (depths :
        ∀ n (C : Circuit), ReadsBack n C →
      ∃ d : ℕ → ℕ, (∀ i < n, d i = 0) ∧
        (∀ j < C.size, let g := gateAt C j
          d (n+j) = (g.inputs.map d).foldr max 0 + (g.op.eval []).toNat) ∧
        ∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and →
          InCone n C i j → j < C.size ∧ 2 ≤ d (n+j))
    (barrier :
    let T := Set (List Bool) × ℕ
    let col (i : ℕ) : T := ({x | x.getD i false = true}, 0)
    let combine (b : Bool) (l : List T) : T :=
      ((if b then {x | ∀ a ∈ l, x ∈ a.1} else {x | ∃ a ∈ l, x ∈ a.1}),
        (l.map Prod.snd).foldr max 0 + b.toNat)
    let S := PEqualNP.HeptadCover.singerLines3
    let good (u : Set (List Bool)) :=
      (∀ p l : Fin 13, p ∈ S l → PEqualNP.LowMerge.pointLineInput 13 13 p l ∈ u) ∧
       ∀ q ∈ PEqualNP.HeptadCover.quadrangles S,
         PEqualNP.GenericRejection.incidenceInput q (PEqualNP.HeptadCover.missLines S q) ∉ u
    ∃ U : Set (Multiset T), (Multiset.range 26).map col ∈ U ∧
      (∀ K ∈ U, K.card < 89 → ∀ l : List T, l.length ≤ 2 → (∀ a ∈ l, a ∈ K) →
        ∀ b, combine b l ::ₘ K ∈ U) ∧
      ∀ K ∈ U, (∃ a ∈ K, 2 ≤ a.2) → ∀ t ∈ K, ¬ good t.1) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x2 x10 ∧ x10.size < x4.size := by
  classical
  intro offsets valid nested C hm back spec small nest
  let T := Set (List Bool) × ℕ
  let col (i : ℕ) : T := ({x | x.getD i false = true}, 0)
  let combine (b : Bool) (l : List T) : T :=
    ((if b then {x | ∀ a ∈ l, x ∈ a.1} else {x | ∃ a ∈ l, x ∈ a.1}),
      (l.map Prod.snd).foldr max 0 + b.toNat)
  let S := PEqualNP.HeptadCover.singerLines3
  let good (u : Set (List Bool)) :=
    (∀ p l : Fin 13, p ∈ S l → PEqualNP.LowMerge.pointLineInput 13 13 p l ∈ u) ∧
     ∀ q ∈ PEqualNP.HeptadCover.quadrangles S,
       PEqualNP.GenericRejection.incidenceInput q (PEqualNP.HeptadCover.missLines S q) ∉ u
  let rows (x : List Bool) := List.ofFn fun k : Fin 26 => x.getD k.val false
  have rl (x : List Bool) : (rows x).length = 26 := List.length_ofFn
  have fixed (x : List Bool) (h : x.length = 26) : rows x = x := by
    apply List.ext_getElem (by rw [rl, h])
    intro i h₁ h₂
    simp only [rows, List.getElem_ofFn, List.getD_eq_getElem _ _ h₂]
  obtain ⟨v,inp,absent,step,out⟩ := columns (List Bool) 26 C back rows rl
  obtain ⟨d,zero,level,pair⟩ := depths 26 C back
  let w (i : ℕ) : T := (v i, d i)
  let bag (j : ℕ) := (Multiset.range (26+j)).map w
  obtain ⟨U,base,move,block⟩ := barrier
  have wb (i : ℕ) (hi : i < 26) : w i = col i := by
    apply Prod.ext
    · change v i = _
      rw [inp i hi]
      ext x
      change (List.ofFn _).getD i false = true ↔ x.getD i false = true
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi),List.getElem_ofFn]
    · exact zero i hi
  have bags (j : ℕ) (hj : j ≤ C.size) : bag j ∈ U := by
    induction j with
    | zero =>
      change (Multiset.range 26).map w ∈ U
      convert base using 1
      exact Multiset.map_congr rfl fun i h => wb i (Multiset.mem_range.mp h)
    | succ j ih =>
      have lt : j < C.size := by omega
      let g := gateAt C j
      have E : g = C.gates[j]'lt := List.getD_eq_getElem _ _ lt
      have hg := hm g (E ▸ List.getElem_mem _)
      have ops : g.op = .and ∨ g.op = .or := by simpa using hg.1
      let args := g.inputs.map w
      let b := g.op.eval []
      have recur : w (26+j) = combine b args := by
        apply Prod.ext
        · change v (26+j) = _
          rcases ops with tag | tag
          · have bit : b = true := by change g.op.eval [] = true; rw [tag]; rfl
            rw [(step j lt).1 tag]
            ext x
            simp [combine,bit,args,w,g]
          · have bit : b = false := by change g.op.eval [] = false; rw [tag]; rfl
            rw [(step j lt).2 tag]
            ext x
            simp [combine,bit,args,w,g]
        · change d (26+j) = (args.map Prod.snd).foldr max 0 + b.toNat
          simpa [args,w,Function.comp_def] using level j lt
      have hargs : ∀ a ∈ args, a ∈ bag j := by
        intro a ha
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
        exact Multiset.mem_map.mpr ⟨i,Multiset.mem_range.mpr (back j lt i hi),rfl⟩
      have hlen : args.length ≤ 2 := by simpa [args] using hg.2
      have hcard : (bag j).card < 89 := by simp [bag]; omega
      have next := move (bag j) (ih (by omega)) hcard args hlen hargs b
      change (Multiset.range ((26+j)+1)).map w ∈ U
      rwa [Multiset.range_succ,Multiset.map_cons,recur]
  obtain ⟨i,j,hi,hj,hij⟩ := nest
  obtain ⟨hj',deep⟩ := pair i j hi hj hij
  have deepmem : w (26+j) ∈ bag C.size :=
    Multiset.mem_map.mpr ⟨26+j,Multiset.mem_range.mpr (by omega),rfl⟩
  have inc : ∀ p l : Fin 13, p ∈ S l ↔ p-l ∈ ({0,1,3,9} : Finset (Fin 13)) := by decide
  have pos (p l : Fin 13) (h : p ∈ S l) : PEqualNP.LowMerge.pointLineInput 13 13 p l ∈ v C.output := by
    apply (out _).mpr
    rw [fixed _ (by change (List.ofFn _ ++ List.ofFn _).length = 26; simp)]
    exact spec.1 p l ((inc p l).mp h)
  have goodout : good (v C.output) := by
    refine ⟨pos, ?_⟩
    intro q hq h
    have qinfo : q.card = 4 ∧ ∀ l, (q ∩ S l).card ≤ 2 := by
      change q ∈ (Finset.univ.powersetCard 4).filter _ at hq
      simpa using hq
    have pl (l : Fin 13) : q.filter (fun a : Fin 13 => a-l ∈ ({0,1,3,9} : Finset (Fin 13))) = q ∩ S l := by
      ext a
      simp [inc]
    have miss (l : Fin 13) : l ∈ PEqualNP.HeptadCover.missLines S q ↔ ∀ a ∈ q, a-l ∉ ({0,1,3,9} : Finset (Fin 13)) := by
      change l ∈ Finset.univ.filter _ ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.disjoint_left]
      constructor
      · intro z a ha hb; exact z ((inc a l).mpr hb) ha
      · intro z a ha hb; exact z a hb ((inc a l).mp ha)
    have tr := (out _).mp h
    rw [fixed _ (by change (List.ofFn _ ++ List.ofFn _).length = 26; simp)] at tr
    have no := spec.2 q qinfo.1 (fun l => by rw [pl]; exact qinfo.2 l)
    have same : PEqualNP.GenericRejection.incidenceInput q (PEqualNP.HeptadCover.missLines S q) =
        (List.ofFn fun a : Fin 13 => decide (a ∈ q)) ++
          List.ofFn fun l : Fin 13 => decide (∀ a ∈ q, a-l ∉ ({0,1,3,9} : Finset (Fin 13))) := by
      apply congrArg (List.append _)
      apply congrArg List.ofFn
      funext l
      exact decide_eq_decide.mpr (miss l)
    rw [same,no] at tr
    contradiction
  have inside : C.output < 26 + C.size := by
    by_contra! outof
    have h := pos 0 0 (by decide)
    rw [absent C.output outof] at h
    exact h
  have omem : w C.output ∈ bag C.size := Multiset.mem_map.mpr ⟨_,Multiset.mem_range.mpr inside,rfl⟩
  exact False.elim (block _ (bags _ le_rfl) ⟨_,deepmem,deep⟩ _ omem goodout)
