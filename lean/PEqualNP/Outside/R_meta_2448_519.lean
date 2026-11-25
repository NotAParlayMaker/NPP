import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- Each true input of an owned conjunction can be traced back through disjunctions.
-- Two disjoint owned edges then give a false positive on at most two of their endpoints.
-- The four endpoints induce two disjoint edges or a path of length three.
-- Order them so that only the middle edge of that path can be present.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2448_519
    (tracePins : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ j < C.size,
      (gateAt C j).op = GateOp.and → ∃ A B : Set (Fin n),
        (∀ u v, Owns n C j u v → (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B)) ∧
        ∀ u ∈ A, ∀ v ∈ B, gateVal n C j (pairInput u v) = true)
    (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      let owns := fun C j a b => G.Adj a b ∧ Owns n C j a b
      let bad := fun (C : Circuit) =>
        {j : Fin C.size | ∃ a b c d, owns C j.val a b ∧ owns C j.val c d ∧
          a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d}.ncard
      ∀ (C : Circuit), IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ j a b c d, owns C j a b → owns C j c d → (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) →
      (¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b d) →
      ∀ p q : Fin n, (p=a ∨ p=b ∨ p=c ∨ p=d) → (q=a ∨ q=b ∨ q=c ∨ q=d) →
        ¬ G.Adj p q → gateVal n C j (pairInput p q) = true →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧
          D.size ≤ C.size ∧ bad D < bad C) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by
  classical
  intro n G _ triangle square
  let st (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) : (gs.foldl st w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [st]; omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl st w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [st]; omega)]
      exact List.getD_append _ _ _ _ hi
  have build (es : List (Fin n × Fin n)) : ∃ C : Circuit, Monotone2 C ∧ C.output < n+C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = es.any (fun e => x e.1 && x e.2) := by
    induction es with
    | nil =>
      refine ⟨⟨[⟨.or, []⟩], n⟩, ?_, by change n < n + 1; omega, ?_⟩
      · intro g hg
        obtain rfl := List.mem_singleton.mp hg
        simp
      · intro x
        change ((List.ofFn x) ++ [false]).getD n false = false
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
    | cons e es ih =>
      obtain ⟨C,hm,hout,eval⟩ := ih
      let k := n + C.size
      let g : Gate := ⟨.and, [e.1.val, e.2.val]⟩
      let h : Gate := ⟨.or, [k, C.output]⟩
      refine ⟨⟨C.gates ++ [g,h], k+1⟩, ?_, by change n + C.gates.length + 1 < n + (C.gates ++ [g,h]).length; simp; omega, ?_⟩
      · intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hm t ht
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl <;> simp [g,h]
      · intro x
        let w := C.gates.foldl st (List.ofFn x)
        have lw : w.length = k := by change (C.gates.foldl st (List.ofFn x)).length = n + C.gates.length; rw [len, List.length_ofFn]
        have bit (i : Fin n) : w.getD i.val false = x i := by
          rw [show w = C.gates.foldl st (List.ofFn x) from rfl, keep _ _ _ (by simp)]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        let z := x e.1 && x e.2
        have pin : g.op.eval (g.inputs.map (fun i => w.getD i false)) = z := by
          change (w.getD e.1.val false && (w.getD e.2.val false && true)) = _
          rw [bit, bit, Bool.and_true]
        have prev : w.getD C.output false = es.any (fun t => x t.1 && x t.2) := eval x
        have stepped : st w g = w ++ [z] := by dsimp only [st]; rw [pin]
        have top : h.op.eval (h.inputs.map (fun i => (w ++ [z]).getD i false)) =
            (z || es.any (fun t => x t.1 && x t.2)) := by
          have a : (w ++ [z]).getD k false = z := by rw [List.getD_append_right _ _ _ _ lw.le, lw]; simp
          have b : (w ++ [z]).getD C.output false = w.getD C.output false :=
            List.getD_append _ _ _ _ (by simpa only [lw] using hout)
          change ((w ++ [z]).getD k false || ((w ++ [z]).getD C.output false || false)) = _
          rw [a,b,prev,Bool.or_false]
        change ((C.gates ++ [g,h]).foldl st (List.ofFn x)).getD (k+1) false = _
        rw [List.foldl_append]
        change (st (st w g) h).getD (k+1) false = _
        rw [stepped]
        dsimp only [st]
        rw [top, List.getD_append_right _ _ _ _ (by simp [lw])]
        simp [lw, z]
  let es := (Finset.univ.filter (fun e : Fin n × Fin n => G.Adj e.1 e.2)).toList
  obtain ⟨initial, mono, _, val⟩ := build es
  have same : circuitFun n initial = graphFun G ∅ := by
    funext x
    change initial.eval (List.ofFn x) = _
    rw [val]
    change es.any (fun e => x e.1 && x e.2) =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    apply Bool.eq_iff_iff.mpr
    simp [es, List.any_eq_true, Prod.exists]
  let valid (C : Circuit) := Monotone2 C ∧ circuitFun n C = graphFun G ∅
  have existsSize : ∃ s, ∃ C : Circuit, C.size = s ∧ valid C := ⟨_,initial,rfl,mono,same⟩
  obtain ⟨least,leastSize,hl,fl⟩ := Nat.find_spec existsSize
  have minimal : IsMinimalMonoCircuit n least := by
    refine ⟨hl,fun D hd fd => ?_⟩
    exact leastSize.le.trans (Nat.find_min' existsSize ⟨D,rfl,hd,fd.trans fl⟩)
  let r (C : Circuit) (j : ℕ) (a b : Fin n) := G.Adj a b ∧ Owns n C j a b
  let score (C : Circuit) := {j : Fin C.size | ∃ a b c d, r C j.val a b ∧ r C j.val c d ∧
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d}.ncard
  let optimal (C : Circuit) := IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅
  have ex : ∃ k, ∃ C, optimal C ∧ score C = k := ⟨_,least,⟨minimal,fl⟩,rfl⟩
  obtain ⟨C,⟨hm,fc⟩,sc⟩ := Nat.find_spec ex
  refine ⟨C,hm.1,fc,fun D hd fd => hm.2 D hd (fd.trans fc.symm),?_⟩
  intro j hj hand
  obtain ⟨A,B,hit,fires⟩ := tracePins n C hm.1 j hj hand
  have intersect {a b c d : Fin n} (ab : r C j a b) (cd : r C j c d) :
      ¬ Disjoint ({a,b} : Finset _) {c,d} := by
    intro apart
    let S : Finset (Fin n) := {a,b,c,d}
    by_cases neg : ∃ p ∈ S, ∃ q ∈ S, ¬G.Adj p q ∧ gateVal n C j (pairInput p q) = true
    · obtain ⟨p,hp,q,hq,off,on⟩ := neg
      have swap {u v : Fin n} (h : r C j u v) : r C j v u := by
        have pair : pairInput u v = pairInput v u := by
          funext i
          change decide (i=u ∨ i=v) = decide (i=v ∨ i=u)
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          exact or_comm
        obtain ⟨limit,op,on,below⟩ := h.2
        refine ⟨h.1.symm, limit, op, ?_, ?_⟩
        · rw [←pair]; exact on
        · rw [←pair]; exact below
      have shape {u v w t : Fin n} (uv : r C j u v) (wt : r C j w t)
          (sep : Disjoint ({u,v} : Finset _) {w,t}) (vw : G.Adj v w) :
          ¬G.Adj u w ∧ ¬G.Adj u t ∧ ¬G.Adj v t := by
        refine ⟨fun uw => triangle u v w uv.1 vw uw.symm, ?_, fun vt => triangle v w t vw wt.1 vt.symm⟩
        intro ut
        rcases square u v w t uv.1 vw wt.1 ut.symm with eq | eq
        · exact Finset.disjoint_left.mp sep (by simp : u ∈ ({u,v} : Finset _)) (by simp [eq])
        · exact Finset.disjoint_left.mp sep (by simp : v ∈ ({u,v} : Finset _)) (by simp [eq])
      have fixGate {u v w t : Fin n} (uv : r C j u v) (wt : r C j w t)
          (one : ({u,v} : Finset _) = {a,b}) (two : ({w,t} : Finset _) = {c,d})
          (form : ¬G.Adj u w ∧ ¬G.Adj u t ∧ ¬G.Adj v t) : False := by
        have sep : Disjoint ({u,v} : Finset _) {w,t} := by rwa [one,two]
        have endpoints : ({u,v,w,t} : Finset _) = S := by
          change insert u (insert v {w,t}) = insert a (insert b {c,d})
          rw [two]
          calc
            _ = ({u,v} : Finset _) ∪ {c,d} := by ext i; simp; tauto
            _ = _ := by rw [one]; ext i; simp; tauto
        obtain ⟨D,md,fd,size,less⟩ :=
          exchange n G triangle square C hm fc j u v w t uv wt
            (by simpa [Finset.disjoint_left, not_or, and_assoc] using sep) form p q
            (by simpa only [Finset.mem_insert, Finset.mem_singleton] using (endpoints.symm ▸ hp : p ∈ ({u,v,w,t} : Finset _)))
            (by simpa only [Finset.mem_insert, Finset.mem_singleton] using (endpoints.symm ▸ hq : q ∈ ({u,v,w,t} : Finset _))) off on
        have dmin : IsMinimalMonoCircuit n D :=
          ⟨md,fun E he fe => size.trans (hm.2 E he (fe.trans fd))⟩
        have best := Nat.find_min' ex ⟨D,⟨dmin,fd.trans fc⟩,rfl⟩
        change score D < score C at less
        omega
      by_cases ac : G.Adj a c
      · have sep : Disjoint ({b,a} : Finset _) {c,d} := by rwa [Finset.pair_comm b a]
        exact fixGate (swap ab) cd (Finset.pair_comm b a) rfl (shape (swap ab) cd sep ac)
      by_cases ad : G.Adj a d
      · have sep : Disjoint ({b,a} : Finset _) {d,c} := by rwa [Finset.pair_comm b a,Finset.pair_comm d c]
        exact fixGate (swap ab) (swap cd) (Finset.pair_comm b a) (Finset.pair_comm d c)
          (shape (swap ab) (swap cd) sep ad)
      by_cases bd : G.Adj b d
      · have sep : Disjoint ({a,b} : Finset _) {d,c} := by rwa [Finset.pair_comm d c]
        exact fixGate ab (swap cd) rfl (Finset.pair_comm d c) (shape ab (swap cd) sep bd)
      exact fixGate ab cd rfl rfl ⟨ac,ad,bd⟩
    · have link {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (ha : u ∈ A) (hb : v ∈ B) : G.Adj u v := by
        by_contra h
        exact neg ⟨u,hu,v,hv,h,fires u ha v hb⟩
      have orient {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (edge : r C j u v) :
          ∃ x ∈ ({u,v} : Finset _), ∃ y ∈ ({u,v} : Finset _), x ∈ A ∧ y ∈ B ∧ G.Adj x y := by
        obtain ⟨ua|va,ub|vb⟩ := hit u v edge.2
        · exact (G.loopless.irrefl u (link hu hu ua ub)).elim
        · exact ⟨u,by simp,v,by simp,ua,vb,edge.1⟩
        · exact ⟨v,by simp,u,by simp,va,ub,edge.1.symm⟩
        · exact (G.loopless.irrefl v (link hv hv va vb)).elim
      have s1 : ({a,b} : Finset _) ⊆ S := by simp [S]
      have s2 : ({c,d} : Finset _) ⊆ S := fun x hx =>
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
      obtain ⟨u,hu,v,hv,ua,vb,uv⟩ := orient (s1 (by simp)) (s1 (by simp)) ab
      obtain ⟨w,hw,z,hz,wa,zb,wz⟩ := orient (s2 (by simp)) (s2 (by simp)) cd
      have cross1 := link (s1 hu) (s2 hz) ua zb
      have cross2 := link (s2 hw) (s1 hv) wa vb
      rcases square u v w z uv cross2.symm wz cross1.symm with e | e
      · exact Finset.disjoint_left.mp apart hu (e ▸ hw)
      · exact Finset.disjoint_left.mp apart hv (e ▸ hz)
  by_cases empty : ∀ a b, ¬r C j a b
  · exact Or.inl (fun a b hab own => empty a b ⟨hab,own⟩)
  push Not at empty
  obtain ⟨a,b,ab⟩ := empty
  have meet {u v s t : Fin n} (uv : r C j u v) (st' : r C j s t) :
      u=s ∨ u=t ∨ v=s ∨ v=t := by
    have h := intersect uv st'
    simp [Finset.disjoint_left] at h
    tauto
  by_cases ha : ∀ u v, r C j u v → u=a ∨ v=a
  · exact Or.inr ⟨a,fun u v h o => ha u v ⟨h,o⟩⟩
  push Not at ha
  obtain ⟨u,v,uv,una,vna⟩ := ha
  have hub : b=u ∨ b=v := by
    rcases meet ab uv with h | h | h | h
    · exact (una h.symm).elim
    · exact (vna h.symm).elim
    · exact Or.inl h
    · exact Or.inr h
  have third : ∃ c, c ≠ a ∧ G.Adj b c ∧
      ∀ s t, r C j s t → b=s ∨ b=t ∨ c=s ∨ c=t := by
    rcases hub with rfl | rfl
    · exact ⟨v,vna,uv.1,fun _ _ e => meet uv e⟩
    · refine ⟨u,una,uv.1.symm,fun s t e => ?_⟩
      rcases meet uv e with h | h | h | h <;> tauto
  obtain ⟨c,hca,bc,meet2⟩ := third
  refine Or.inr ⟨b,fun s t hs own => ?_⟩
  by_contra! miss
  have e : r C j s t := ⟨hs,own⟩
  have m1 := meet ab e
  have m2 := meet2 s t e
  have ac : ¬G.Adj c a := triangle a b c ab.1 bc
  have ns : b ≠ s := Ne.symm miss.1
  have nt : b ≠ t := Ne.symm miss.2
  have hasA : a=s ∨ a=t := by tauto
  have hasC : c=s ∨ c=t := by tauto
  rcases hasA with aS | aT <;> rcases hasC with cS | cT
  · exact hca (cS.trans aS.symm)
  · exact ac (by rw [cT,aS]; exact hs.symm)
  · exact ac (by rw [cS,aT]; exact hs)
  · exact hca (cT.trans aT.symm)
