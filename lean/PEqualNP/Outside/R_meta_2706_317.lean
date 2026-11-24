import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.R_meta_2706_317
    (geometry : let col (k : Fin 14) : BitVec 58 := BitVec.ofNat 58 (([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] : List ℕ).getD k.val 0)
      ∀ (x y : BitVec 58), (x ||| y) = 2097151 → x ≠ 2097151 → y ≠ 2097151 →
        ∃ (r : Fin 58 → Fin 58) (e : Fin 14 → Fin 14) (a b : BitVec 58), Function.Surjective e ∧
        (∀ k i, (col (e k)).getLsbD i.val = (col k).getLsbD (r i).val) ∧
        (∀ i, a.getLsbD i.val = x.getLsbD (r i).val ∧ b.getLsbD i.val = y.getLsbD (r i).val) ∧
        (a ||| b) = 2097151 ∧ ∃ s ∈ ([(1,1,2),(4,527,557112),(7,335487,511970)] : List (ℕ × ℕ × ℕ)), b.getLsbD 0 = false ∧ a.getLsbD s.1 = false ∧ (a.toNat &&& s.2.1) = s.2.1 ∧ (b.toNat &&& s.2.2) = s.2.2)
    (compile : ∀ (col : Fin 14 → BitVec 58) (t u : BitVec 58) (C : Circuit) (i j : ℕ), Monotone2 C → t ≠ 0 → t ≠ -1 → u ≠ 0 → u ≠ -1 →
      (∀ r : Fin 58, let w := C.wires (List.ofFn fun k => (col k).getLsbD r.val)
        w.getD i false = t.getLsbD r.val ∧ w.getD j false = u.getLsbD r.val) →
      let p := List.ofFn col
      ∃ fs : List (BitVec 58), fs.length ≤ C.size ∧ t ∈ p ++ fs ∧ u ∈ p ++ fs ∧
        ∀ j : Fin fs.length, let old := p ++ fs.take j.val
          fs.get j ∉ old ∧ fs.get j ≠ 0 ∧ fs.get j ≠ -1 ∧ ∃ a ∈ old, ∃ b ∈ old, fs.get j = a &&& b ∨ fs.get j = a ||| b)
    (finite : let col (k : Fin 14) : BitVec 58 := BitVec.ofNat 58 (([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] : List ℕ).getD k.val 0)
      let p := List.ofFn col
      ∀ (fs : List (BitVec 58)) (a b : BitVec 58), a ∈ p ++ fs → b ∈ p ++ fs → (a ||| b)=2097151 →
        (∃ s ∈ ([(1,1,2),(4,527,557112),(7,335487,511970)] : List (ℕ × ℕ × ℕ)), b.getLsbD 0 = false ∧ a.getLsbD s.1 = false ∧ (a.toNat &&& s.2.1) = s.2.1 ∧ (b.toNat &&& s.2.2) = s.2.2) →
        (∀ j : Fin fs.length, let old := p ++ fs.take j.val
          fs.get j ∉ old ∧ fs.get j ≠ 0 ∧ fs.get j ≠ -1 ∧ ∃ u ∈ old, ∃ v ∈ old, fs.get j = u &&& v ∨ fs.get j = u ||| v) → 26 ≤ fs.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) → (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) → (26 : ℕ) ≤ x1.size := by
  intro C i j hm _bndi _bndj
  dsimp only
  intro cover sound left right
  let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let H (x : Fin 14 → Bool) : Prop := ∃ u v : Fin 14, (u.val,v.val) ∈ E ∧ x u=true ∧ x v=true
  let w (k : ℕ) (x : Fin 14 → Bool) := (C.wires (List.ofFn x)).getD k false
  change ∀ x, H x → w i x=true ∨ w j x=true at cover
  change ∀ x, ¬ H x → w i x=false ∧ w j x=false at sound
  change ∃ x, H x ∧ w i x=true ∧ w j x=false at left
  change ∃ x, H x ∧ w j x=true ∧ w i x=false at right
  let col (k : Fin 14) : BitVec 58 := BitVec.ofNat 58 (([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] : List ℕ).getD k.val 0)
  let row (r : Fin 58) (k : Fin 14) := (col k).getLsbD r.val
  let target : BitVec 58 := 2097151
  let encode (k : ℕ) : BitVec 58 := (BitVec.ofBoolListLE (List.ofFn fun r : Fin 58 => w k (row r))).cast (by simp)
  have bits (k : ℕ) (r : Fin 58) : (encode k).getLsbD r.val = w k (row r) := by
    simp only [encode,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa using r.isLt),List.getElem_ofFn]
  have truth : ∀ r : Fin 58, target.getLsbD r.val = true ↔ H (row r) := by decide +kernel
  have located : ∀ u v : Fin 14, (u.val,v.val)∈E → ∃ r : Fin 58, target.getLsbD r.val=true ∧ ∀ k : Fin 14, row r k = decide (k=u ∨ k=v) := by decide +kernel
  have combined : (encode i ||| encode j) = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let r : Fin 58 := ⟨k,hk⟩
    change (encode i ||| encode j).getLsbD r.val = target.getLsbD r.val
    rw [BitVec.getLsbD_or,bits,bits]
    cases h : target.getLsbD r.val with
    | false =>
      have hn : ¬ H (row r) := fun he => Bool.noConfusion (h.symm.trans ((truth r).2 he))
      obtain ⟨ha,hb⟩ := sound (row r) hn
      simp [ha,hb]
    | true =>
      rcases cover (row r) ((truth r).1 h) with ha|hb
      · rw [ha,Bool.true_or]
      · rw [hb,Bool.or_true]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have snoc (w : List Bool) (z : Bool) (i : ℕ) : (w++[z]).getD i false = if i=w.length then z else w.getD i false := by
    by_cases h : i<w.length
    · rw [List.getD_append _ _ _ _ h,ite_eq_right (by omega)]
    · by_cases h' : i=w.length
      · subst i; simp [List.getD_eq_getElem?_getD]
      · rw [ite_eq_right h',List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by omega)]
  have transfer (gs : List Gate) (ok : ∀ g∈gs, g.op=.and ∨ g.op=.or) (a b : List Bool) (len : a.length=b.length)
      (le : ∀ i, a.getD i false=true → b.getD i false=true) :
      ∀ i, (gs.foldl step a).getD i false=true → (gs.foldl step b).getD i false=true := by
    induction gs generalizing a b with
    | nil => exact le
    | cons g gs ih =>
      rw [List.foldl_cons,List.foldl_cons]
      apply ih (fun k hk => ok _ (List.mem_cons_of_mem _ hk)) _ _ (by simp [step,len])
      intro i
      simp only [step,snoc,len]; split_ifs
      · rcases ok g List.mem_cons_self with op|op
        · rw [op]; change (g.inputs.map fun k => a.getD k false).all id = true → (g.inputs.map fun k => b.getD k false).all id = true
          simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
          exact fun h k hk => le k (h k hk)
        · rw [op]; change (g.inputs.map fun k => a.getD k false).any id = true → (g.inputs.map fun k => b.getD k false).any id = true
          simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          rintro ⟨k,hk,t⟩; exact ⟨k,hk,le k t⟩
      · exact le i
  have mono (k : ℕ) (p q : Fin 14 → Bool) (hle : ∀ j, p j=true → q j=true) : w k p=true → w k q=true := by
    apply transfer C.gates (fun g hg => (hm g hg).1) (List.ofFn p) (List.ofFn q) (by simp) _ k
    intro i
    by_cases h : i<14
    · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn,List.getElem_ofFn]
      exact hle ⟨i,h⟩
    · rw [List.getD_eq_default _ _ (by simp;omega)]; simp
  have differs (k : ℕ) (lost : ∃ x, H x ∧ w k x=false) : encode k ≠ target := by
    intro equal
    obtain ⟨x,⟨u,v,edge,hu,hv⟩,absent⟩ := lost
    obtain ⟨r,hit,hr⟩ := located u v edge
    have rises : w k (row r)=true := (bits k r).symm.trans (equal ▸ hit)
    have all : ∀ j, row r j=true → x j=true := by
      intro j hj; rw [hr] at hj
      rcases of_decide_eq_true hj with rfl|rfl
      · exact hu
      · exact hv
    exact Bool.noConfusion (absent.symm.trans (mono k _ _ all rises))
  obtain ⟨r,e,a,b,sur,cols,rb,hab,mark⟩ := geometry (encode i) (encode j) combined
    (differs i (right.imp fun _ h => ⟨h.1,h.2.2⟩)) (differs j (left.imp fun _ h => ⟨h.1,h.2.2⟩))
  have retained := mark
  obtain ⟨s,hs,b0,as,_,_⟩ := retained
  have one : (2097151 : BitVec 58).getLsbD s.1=true ∧ s.1<58 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl <;> decide +kernel
  have zeroBit := congrArg (fun t : BitVec 58 => t.getLsbD 0) hab
  have atBit := congrArg (fun t : BitVec 58 => t.getLsbD s.1) hab
  rw [BitVec.getLsbD_or,b0,Bool.or_false] at zeroBit
  rw [BitVec.getLsbD_or,as,Bool.false_or,one.1] at atBit
  have nonzero (v : BitVec 58) (k : ℕ) (h : v.getLsbD k=true) : v≠0 := by
    rintro rfl; simp at h
  have nontop (v : BitVec 58) (k : ℕ) (bound : k<58) (h : v.getLsbD k=false) : v≠-1 := by
    rintro rfl; change (BitVec.allOnes 58).getLsbD k=false at h
    rw [BitVec.getLsbD_allOnes] at h
    exact Bool.noConfusion ((decide_eq_true bound).symm.trans h)
  have reads (z : Fin 58) : List.ofFn (fun k => (col (e k)).getLsbD z.val) = List.ofFn (row (r z)) := by
    congr 1; funext k; exact cols k z
  obtain ⟨fs,len,ina,inb,valid⟩ := compile (fun k => col (e k)) a b C i j hm
    (nonzero a 0 (zeroBit.trans (by decide))) (nontop a _ one.2 as)
    (nonzero b _ atBit) (nontop b 0 (by decide) b0) (fun z => by
      rw [reads]
      exact ⟨(bits i _).symm.trans (rb z).1.symm,(bits j _).symm.trans (rb z).2.symm⟩)
  have same (v : BitVec 58) : v ∈ List.ofFn (fun k => col (e k)) ↔ v ∈ List.ofFn col := by
    simp only [List.mem_ofFn]
    constructor
    · rintro ⟨k,h⟩; exact ⟨e k,h⟩
    · rintro ⟨k,h⟩; obtain ⟨m,rfl⟩ := sur k; exact ⟨m,h⟩
  apply le_trans (finite fs a b (by simpa only [List.mem_append,same] using ina)
    (by simpa only [List.mem_append,same] using inb) hab mark ?_) len
  intro k
  simpa only [List.mem_append,same] using valid k
