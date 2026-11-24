import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3324_417
    (core : ∃ C : Circuit, IsAO2 10 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.size = 14 ∧
      C.output = 23 ∧ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ((x 0 && (x 4 || (x 5 || x 7))) || ((x 1 && (x 4 || (x 6 || x 9))) || ((x 2 && (x 5 || (x 8 || x 9))) || (x 3 && (x 6 || (x 7 || x 8)))))))
    (rest : ∃ D : Circuit, IsAO2 11 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.size ≤ 12 ∧
      ∀ x : Fin 11 → Bool, D.eval (List.ofFn x) = (x 10 || ((x 0 && (x 3 || (x 7 || x 8))) || ((x 1 && (x 6 || (x 7 || x 9))) || (x 2 && (x 4 || (x 5 || x 7))))))) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 ∧ (∀ x3 ∈ x2.gates, x3.inputs.Nodup) ∧ (2 : ℕ) ≤ x2.size ∧ x2.size ≤ (26 : ℕ) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Decidable.decide (∃ (x4 : Fin (14 : ℕ)) (x5 : Fin (14 : ℕ)), (↑x4, ↑x5) ∈ x1 ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) := by
  have liftCircuit (n m : ℕ) (hnm : n ≤ m) (e : Fin n → Fin m) (inj : Function.Injective e)
      (C : Circuit) (hm : IsAO2 n C) (hd : ∀ g ∈ C.gates, g.inputs.Nodup) :
      ∃ T : Circuit, IsAO2 m T ∧ (∀ g ∈ T.gates, g.inputs.Nodup) ∧ T.size = C.size ∧
        (n ≤ C.output → T.output = C.output + (m-n)) ∧
        ∀ x : Fin m → Bool, T.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e)) := by
    let f (i : ℕ) := if h : i < n then (e ⟨i,h⟩).val else i+(m-n)
    have low (i : ℕ) (hi : i < n) : f i < m := by simp [f,hi]
    have fix (i : ℕ) (hi : n ≤ i) : f i = i+(m-n) := by simp [f,Nat.not_lt.mpr hi]
    have fi : Function.Injective f := by
      intro i j hij
      by_cases hi : i < n <;> by_cases hj : j < n
      · have he : e ⟨i,hi⟩ = e ⟨j,hj⟩ := Fin.ext (by simpa [f,hi,hj] using hij)
        exact congrArg (fun a : Fin n => a.val) (inj he)
      · have := low i hi
        rw [fix _ (by omega : n ≤ j)] at hij
        omega
      · have := low j hj
        rw [fix _ (by omega : n ≤ i)] at hij
        omega
      · simpa [f,hi,hj] using hij
    let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
    let T : Circuit := ⟨C.gates.map rename,f C.output⟩
    have props (g : Gate) (hg : g ∈ T.gates) :
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
      exact ⟨hm.1 k hk,by simpa [rename] using hm.2.2 k hk,(hd k hk).map fi⟩
    have back : NestedCover.ReadsBack m T := by
      intro j hj v hv
      have hj' : j < C.gates.length := by simpa [T] using hj
      have he : NestedCover.gateAt T j = rename (NestedCover.gateAt C j) := by
        change (C.gates.map rename).getD j _ = rename (C.gates.getD j _)
        rw [List.getD_eq_getElem _ _ (by simpa),List.getD_eq_getElem _ _ hj',List.getElem_map]
      rw [he] at hv
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
      by_cases h : i < n
      · have := low i h
        omega
      · have := hm.2.1 j hj' i hi
        rw [fix _ (by omega)]
        omega
    refine ⟨T,⟨fun g hg => (props g hg).1,back,fun g hg => (props g hg).2.1⟩,
      fun g hg => (props g hg).2.2,by change (C.gates.map rename).length = C.gates.length; simp,
      fun ho => fix _ ho,?_⟩
    intro x
    let rel (w v : List Bool) := ∀ i, v.getD (f i) false = w.getD i false
    let run (gs : List Gate) (w : List Bool) := gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]) w
    have step (w v : List Bool) (hl : v.length = w.length + (m-n)) (hn : n ≤ w.length)
        (hr : rel w v) (b : Bool) : rel (w ++ [b]) (v ++ [b]) := by
      intro i
      by_cases h : i < w.length
      · have h' : f i < v.length := by
          by_cases h₀ : i < n
          · have := low i h₀
            omega
          · rw [fix _ (by omega)]
            omega
        rw [List.getD_append _ _ _ _ h',List.getD_append _ _ _ _ h]
        exact hr i
      · rw [fix _ (by omega),List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
        congr 1
        omega
    have simulation (gs : List Gate) (w v : List Bool) (hl : v.length = w.length + (m-n))
        (hn : n ≤ w.length) (hr : rel w v) : rel (run gs w) (run (gs.map rename) v) := by
      induction gs generalizing w v with
      | nil => exact hr
      | cons g gs ih =>
        have he : (rename g).op.eval ((rename g).inputs.map fun i => v.getD i false) =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp only [rename,List.map_map]
          congr 2
          exact funext hr
        simp only [run,List.map_cons,List.foldl_cons,he]
        apply ih
        · simp only [List.length_append,List.length_singleton]
          omega
        · simp only [List.length_append,List.length_singleton]
          omega
        · exact step w v hl hn hr _
    have init : rel (List.ofFn (x ∘ e)) (List.ofFn x) := by
      intro i
      by_cases h : i < n
      · have h' := low i h
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h'),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),List.getElem_ofFn,List.getElem_ofFn]
        change x ⟨f i,_⟩ = x (e ⟨i,h⟩)
        congr 1
        exact Fin.ext (by simp [f,h])
      · rw [fix _ (by omega),List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
    exact simulation C.gates _ _ (by simp only [List.length_ofFn]; omega)
      (by simp only [List.length_ofFn,le_refl]) init C.output
  let embedC : Fin 10 → Fin 14 := ![0,1,2,5,7,8,9,10,12,13]
  have injC : Function.Injective embedC := by decide
  obtain ⟨Q,hm,hn,hs,ho,he⟩ := core
  obtain ⟨C,hmC,hnC,sizeC,outC,evalC⟩ := liftCircuit 10 14 (by decide) embedC injC Q hm hn
  have hsC : C.size = 14 := by rwa [sizeC]
  have hoC : C.output = 27 := by rw [outC (by omega),ho]
  have hC (x : Fin 14 → Bool) : C.eval (List.ofFn x) = ((x 0 && (x 7 || (x 8 || x 10))) || ((x 1 && (x 7 || (x 9 || x 13))) || ((x 2 && (x 8 || (x 12 || x 13))) || (x 5 && (x 9 || (x 10 || x 12)))))) := (evalC x).trans (he (x ∘ embedC))
  let embedD : Fin 11 → Fin 28 := ![3,4,6,7,8,9,10,11,12,13,27]
  have injD : Function.Injective embedD := by decide
  obtain ⟨Q,hm,hn,hs,he⟩ := rest
  obtain ⟨D,hmD,hnD,sizeD,outD,evalD⟩ := liftCircuit 11 28 (by decide) embedD injD Q hm hn
  have hsD : D.size ≤ 12 := by rwa [sizeD]
  have hD (x : Fin 28 → Bool) : D.eval (List.ofFn x) = (x 27 || ((x 3 && (x 7 || (x 11 || x 12))) || ((x 4 && (x 10 || (x 11 || x 13))) || (x 6 && (x 8 || (x 9 || x 11)))))) := (evalD x).trans (he (x ∘ embedD))
  let E : Circuit := ⟨C.gates ++ D.gates,D.output⟩
  have lC : C.gates.length = 14 := hsC
  have lD : D.gates.length ≤ 12 := hsD
  have ops : PEqualNP.EdgeOwnership.AndOrOnly E := by
    intro g hg
    rcases List.mem_append.mp hg with hc|hd
    · exact hmC.1 g hc
    · exact hmD.1 g hd
  have inputs : ∀ g ∈ E.gates, g.inputs.length = 2 ∧ g.inputs.Nodup := by
    intro g hg
    rcases List.mem_append.mp hg with hc|hd
    · exact ⟨hmC.2.2 g hc,hnC g hc⟩
    · exact ⟨hmD.2.2 g hd,hnD g hd⟩
  have back : NestedCover.ReadsBack 14 E := by
    intro j hj i hi
    change j < (C.gates ++ D.gates).length at hj
    by_cases h : j < C.gates.length
    · have eq : NestedCover.gateAt E j = NestedCover.gateAt C j := by
        exact List.getD_append _ _ _ _ h
      exact hmC.2.1 j h i (eq ▸ hi)
    · have eq : NestedCover.gateAt E j = NestedCover.gateAt D (j - C.gates.length) := by
        exact List.getD_append_right _ _ _ _ (by omega)
      have hlen : j - C.gates.length < D.gates.length := by simp only [List.length_append] at hj; omega
      have := hmD.2.1 _ hlen i (eq ▸ hi)
      omega
  refine ⟨E,⟨ops,back,fun g hg => (inputs g hg).1⟩,fun g hg => (inputs g hg).2,?_,?_,?_⟩
  · change 2 ≤ (C.gates ++ D.gates).length
    simp only [List.length_append,lC]
    omega
  · change (C.gates ++ D.gates).length ≤ 26
    simp only [List.length_append,lC]
    omega
  · intro x
    let w := C.wires (List.ofFn x)
    let run (gs : List Gate) (v : List Bool) := gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]) v
    have extension (gs : List Gate) (v : List Bool) :
        ∃ tail : List Bool, tail.length = gs.length ∧ run gs v = v ++ tail := by
      induction gs generalizing v with
      | nil => exact ⟨[],rfl,by simp [run]⟩
      | cons g gs ih =>
        let b := g.op.eval (g.inputs.map fun i => v.getD i false)
        obtain ⟨t,hl,he⟩ := ih (v ++ [b])
        exact ⟨b :: t,by simp [hl],by simpa only [run,List.foldl_cons,List.append_assoc,List.singleton_append] using he⟩
    obtain ⟨t,hlen,he⟩ := extension C.gates (List.ofFn x)
    have hw : w = List.ofFn x ++ t := he
    have lw : w.length = 28 := by rw [hw,List.length_append,List.length_ofFn,hlen,lC]
    let y : Fin 28 → Bool := fun i => w.getD i.val false
    have hy : List.ofFn y = w := by
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using lw.symm
      · intro i hi hj
        rw [List.getElem_ofFn]
        exact List.getD_eq_getElem _ _ hj
    have old (i : Fin 14) : y (Fin.castLE (by decide) i) = x i := by
      change w.getD i.val false = _
      rw [hw,List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]
    have top : y 27 = ((x 0 && (x 7 || (x 8 || x 10))) || ((x 1 && (x 7 || (x 9 || x 13))) || ((x 2 && (x 8 || (x 12 || x 13))) || (x 5 && (x 9 || (x 10 || x 12)))))) := by
      change w.getD 27 false = _
      rw [← hoC]
      exact hC x
    have e : E.eval (List.ofFn x) = D.eval (List.ofFn y) := by
      rw [hy]
      change (run (C.gates ++ D.gates) (List.ofFn x)).getD D.output false = (run D.gates (run C.gates (List.ofFn x))).getD D.output false
      simp only [run,List.foldl_append]
    rw [e,hD,top]
    rw [show y 3 = x 3 from old 3, show y 4 = x 4 from old 4, show y 6 = x 6 from old 6, show y 7 = x 7 from old 7, show y 8 = x 8 from old 8, show y 9 = x 9 from old 9, show y 10 = x 10 from old 10, show y 11 = x 11 from old 11, show y 12 = x 12 from old 12, show y 13 = x 13 from old 13]
    let edges : List (Fin 14 × Fin 14) := [(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,12), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]
    have bridge : (edges.any (fun z => x z.1 && x z.2)) = decide (∃ a b : Fin 14,
        (a.val,b.val) ∈ (edges.map fun z => (z.1.val,z.2.val)) ∧ x a = true ∧ x b = true) := by
      apply Bool.eq_iff_iff.mpr
      rw [List.any_eq_true,decide_eq_true_eq]
      constructor
      · rintro ⟨⟨a,b⟩,hab,hx⟩
        exact ⟨a,b,List.mem_map.mpr ⟨(a,b),hab,rfl⟩,Bool.and_eq_true_iff.mp hx⟩
      · rintro ⟨a,b,h,ha,hb⟩
        obtain ⟨⟨u,v⟩,hu,heq⟩ := List.mem_map.mp h
        have h₁ : u = a := Fin.ext (congrArg Prod.fst heq)
        have h₂ : v = b := Fin.ext (congrArg Prod.snd heq)
        subst u
        subst v
        exact ⟨(a,b),hu,Bool.and_eq_true_iff.mpr ⟨ha,hb⟩⟩
    apply Eq.trans _ bridge
    simp only [edges,List.any_cons,List.any_nil,Bool.or_false]
    simp only [Bool.and_or_distrib_left]
    ac_rfl
