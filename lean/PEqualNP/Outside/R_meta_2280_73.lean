import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Delete the first paid gate and conjugate all later wires by a graph
-- automorphism preserving the free OR. Each child fixes one of its two types.
-- The row masks encode canonical unordered operand pairs, including constants.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2280_73
    (case7 :
      let M : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816, 11, 69, 98, 49, 88, 44, 22]
      let F (x : Fin 14 → Bool) := ∃ p q : Fin 14, (M.getD p.val 0).testBit q.val = true ∧ x p = true ∧ x q = true
      let B (x : Fin 14 → Bool) := (F x ∧ ∀ v, x v = true → ¬ F (Function.update x v false)) ∨
        (¬ F x ∧ ∀ v, x v = false → F (Function.update x v true))
      let K : List ℕ := [115591, 117518, 119380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114688, 98304, 65536]
      ∀ (T : Circuit) (a b : Fin 17) (aand : Bool), (K.getD a.val 0).testBit b.val = true →
        Monotone2 T → (∀ x : Fin 14 → Bool, B x →
          let w := List.ofFn x ++ [GateOp.or.eval [x 0, x 7]]
          let z := w ++ [false,true]
          let p := z.getD a.val false
          let q := z.getD b.val false
          T.eval (w ++ [if aand then p && q else p || q]) = true ↔ F x) → 25 ≤ T.size)
    (case9 :
      let M : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816, 11, 69, 98, 49, 88, 44, 22]
      let F (x : Fin 14 → Bool) := ∃ p q : Fin 14, (M.getD p.val 0).testBit q.val = true ∧ x p = true ∧ x q = true
      let B (x : Fin 14 → Bool) := (F x ∧ ∀ v, x v = true → ¬ F (Function.update x v false)) ∨
        (¬ F x ∧ ∀ v, x v = false → F (Function.update x v true))
      let K : List ℕ := [117383, 125358, 120844, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114688, 98304, 65536]
      ∀ (T : Circuit) (a b : Fin 17) (aand : Bool), (K.getD a.val 0).testBit b.val = true →
        Monotone2 T → (∀ x : Fin 14 → Bool, B x →
          let w := List.ofFn x ++ [GateOp.or.eval [x 0, x 9]]
          let z := w ++ [false,true]
          let p := z.getD a.val false
          let q := z.getD b.val false
          T.eval (w ++ [if aand then p && q else p || q]) = true ↔ F x) → 25 ≤ T.size) :
  have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)), x5 = (7 : Fin (14 : ℕ)) ∨ x5 = (9 : Fin (14 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin (14 : ℕ) → Bool), x3 x8 → (x4.eval (List.ofFn x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x8 (0 : Fin (14 : ℕ)), x8 x5]]) = Bool.true ↔ x2 x8)) → (26 : ℕ) ≤ x4.size := by
  classical
  intro xEdges xHit xBoundary C j hj hmono original
  let edges : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let mat : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816, 11, 69, 98, 49, 88, 44, 22]
  let adj (p q : Fin 14) := (mat.getD p.val 0).testBit q.val = true
  let F (x : Fin 14 → Bool) := ∃ p q : Fin 14, adj p q ∧ x p = true ∧ x q = true
  let O (x : Fin 14 → Bool) := ∃ p q : Fin 14, (p.val,q.val) ∈ edges ∧ x p = true ∧ x q = true
  let B (P : (Fin 14 → Bool) → Prop) (x : Fin 14 → Bool) :=
    (P x ∧ ∀ v, x v = true → ¬ P (Function.update x v false)) ∨
    (¬ P x ∧ ∀ v, x v = false → P (Function.update x v true))
  let free (x : Fin 14 → Bool) := GateOp.or.eval [x 0,x j]
  let seed (x : Fin 14 → Bool) := List.ofFn x ++ [free x]
  let atom (x : Fin 14 → Bool) (a : Fin 17) := (seed x ++ [false,true]).getD a.val false
  let comb (op x y : Bool) := if op then x && y else x || y
  let K : List ℕ := if j=7 then [115591, 117518, 119380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114688, 98304, 65536] else [117383, 125358, 120844, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114688, 98304, 65536]
  let codes : List ℕ := if j=7 then [62129658859368976, 61863585619522576, 44113344757904656, 43851652369036816, 57872487274582576, 53366765914559536, 56814765646943536, 52313425137899056, 28502781892209031, 28236708652362631, 10486467790744711, 10224775401876871, 24245610307422631, 19739888947399591, 23187888679783591, 18686548170739111] else [62129658859368976, 61863585619522576, 57904236474876496, 57377566031496016, 53157639866295136, 53418237069829216, 14677406902967161, 14150736569687161, 9923115702140041, 10191379312197001, 18895134577773481, 18636727854550441, 62129658859368976, 62129658859368976, 62129658859368976, 62129658859368976]
  let perm (s : Fin 16) (i : Fin 14) : Fin 14 :=
    Fin.ofNat 14 (((codes.getD s.val 0) >>> (4*i.val)) % 16)
  let lift (p : Fin 14 → Fin 14) (i : Fin 17) : Fin 17 :=
    if h : i.val < 14 then ⟨(p ⟨i.val,h⟩).val, by have := (p ⟨i.val,h⟩).isLt; omega⟩ else i
  have table : ∀ p q : Fin 14, adj p q ↔ (p.val,q.val) ∈ edges ∨ (q.val,p.val) ∈ edges := by
    dsimp only [adj,mat,edges]
    decide +kernel
  have equiv (x : Fin 14 → Bool) : F x ↔ O x := by
    constructor
    · rintro ⟨p,q,ha,hp,hq⟩
      rcases (table p q).mp ha with h | h
      · exact ⟨p,q,h,hp,hq⟩
      · exact ⟨q,p,h,hq,hp⟩
    · rintro ⟨p,q,ha,hp,hq⟩
      exact ⟨p,q,(table p q).mpr (Or.inl ha),hp,hq⟩
  have beq (x : Fin 14 → Bool) : B F x ↔ B O x := by simp only [B,equiv]
  change ∀ x, B O x → (C.eval (seed x) = true ↔ O x) at original
  have correct (x : Fin 14 → Bool) (hx : B F x) : C.eval (seed x) = true ↔ F x :=
    (original x ((beq x).mp hx)).trans (equiv x).symm
  have autos (s : Fin 16) : Function.Bijective (perm s) ∧
      ((perm s 0 = 0 ∧ perm s j = j) ∨ (perm s 0 = j ∧ perm s j = 0)) ∧
      ∀ u v, adj (perm s u) (perm s v) ↔ adj u v := by
    revert s
    rcases hj with h | h <;> subst j <;>
      dsimp only [perm,codes,adj,mat,Function.Bijective,Function.Injective,Function.Surjective] <;>
      decide +kernel
  have covers (a b : Fin 17) : ∃ s : Fin 16,
      (K.getD (min (lift (perm s) a) (lift (perm s) b)).val 0).testBit
        (max (lift (perm s) a) (lift (perm s) b)).val = true := by
    revert a b
    rcases hj with h | h <;> subst j <;> dsimp only [K,lift,perm,codes] <;> decide +kernel
  have charge (T : Circuit) (a b : Fin 17) (op : Bool)
      (hk : (K.getD a.val 0).testBit b.val = true) (ht : Monotone2 T)
      (h : ∀ x, B F x → (T.eval (seed x ++ [comb op (atom x a) (atom x b)]) = true ↔ F x)) :
      25 ≤ T.size := by
    rcases hj with rfl | rfl
    · exact case7 T a b op hk ht h
    · exact case9 T a b op hk ht h
  have length_seed (x) : (seed x).length = 15 := by simp [seed]
  have read15 (x) : atom x 15 = false := by
    change (seed x ++ [false,true]).getD 15 false = false
    rw [List.getD_append_right _ _ _ _ (by rw [length_seed]),length_seed]
    rfl
  have read16 (x) : atom x 16 = true := by
    change (seed x ++ [false,true]).getD 16 false = true
    rw [List.getD_append_right _ _ _ _ (by rw [length_seed]; decide),length_seed]
    rfl
  let raw (k : ℕ) : Fin 17 := if h : k<15 then ⟨k,by omega⟩ else 15
  have readRaw (x) (k : ℕ) : (seed x).getD k false = atom x (raw k) := by
    by_cases h : k<15
    · simp only [raw,dite_eq_left h,atom]
      exact (List.getD_append (seed x) [false,true] false k (by rw [length_seed]; exact h)).symm
    · rw [show raw k = 15 from dite_eq_right h, read15]
      apply List.getD_eq_default
      rw [length_seed]
      omega
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have classify (g : Gate) (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
      ∃ (a b : Fin 17) (op : Bool), ∀ x, g.op.eval (g.inputs.map fun k => (seed x).getD k false)
        = comb op (atom x a) (atom x b) := by
    rcases g with ⟨op,ins⟩
    obtain ⟨hOp,hlen⟩ := hg
    change op = .and ∨ op = .or at hOp
    change ins.length ≤ 2 at hlen
    rcases ins with _ | ⟨k,tl⟩
    · rcases hOp with rfl | rfl
      · exact ⟨16,16,true,fun x => by simp [comb,read16,evalAnd]⟩
      · exact ⟨15,15,false,fun x => by simp [comb,read15,evalOr]⟩
    · rcases tl with _ | ⟨l,tl⟩
      · rcases hOp with rfl | rfl
        · exact ⟨raw k,raw k,true,fun x => by rw [← readRaw x k]; simp [evalAnd,comb]⟩
        · exact ⟨raw k,raw k,false,fun x => by rw [← readRaw x k]; simp [evalOr,comb]⟩
      · cases tl with
        | nil =>
          rcases hOp with rfl | rfl
          · exact ⟨raw k,raw l,true,fun x => by rw [← readRaw x k, ← readRaw x l]; simp [evalAnd,comb]⟩
          · exact ⟨raw k,raw l,false,fun x => by rw [← readRaw x k, ← readRaw x l]; simp [evalOr,comb]⟩
        | cons k' tl => simp at hlen
  let run (gs : List Gate) (z : List Bool) := Circuit.wires ⟨gs,0⟩ z
  have paid (gs : List Gate) (out : ℕ) (a b : Fin 17) (op : Bool)
      (mono : Monotone2 ⟨gs,out⟩)
      (ok : ∀ x, B F x → ((⟨gs,out⟩ : Circuit).eval (seed x ++
        [comb op (atom x a) (atom x b)]) = true ↔ F x)) : 25 ≤ gs.length := by
    obtain ⟨s,hs⟩ := covers a b
    let p := perm s
    obtain ⟨bij,fix,graph⟩ := autos s
    let ren (k : ℕ) : ℕ := if h : k < 14 then (p ⟨k,h⟩).val else k
    let gate (g : Gate) : Gate := ⟨g.op,g.inputs.map ren⟩
    let D : Circuit := ⟨gs.map gate,ren out⟩
    have low {k : ℕ} (hk : k < 14) : ren k < 14 := by
      simp only [ren,dite_eq_left hk]
      exact (p ⟨k,hk⟩).isLt
    have fixed {k : ℕ} (hk : 14 ≤ k) : ren k = k := dite_eq_right (by omega)
    have lifted (v : Fin 17) : (lift p v).val = ren v.val := by
      by_cases h : v.val < 14 <;> simp [lift,ren,h]
    have graphEq (x : Fin 14 → Bool) : F (x ∘ p) ↔ F x := by
      constructor
      · rintro ⟨i,k,he,hi,hk⟩
        exact ⟨p i,p k,(graph i k).mpr he,hi,hk⟩
      · rintro ⟨i,k,he,hi,hk⟩
        obtain ⟨i',rfl⟩ := bij.2 i
        obtain ⟨k',rfl⟩ := bij.2 k
        exact ⟨i',k',(graph i' k').mp he,hi,hk⟩
    have commute (x : Fin 14 → Bool) (i : Fin 14) (v : Bool) :
        Function.update (x ∘ p) i v = (Function.update x (p i) v) ∘ p := by
      funext k
      by_cases h : k=i
      · subst k; simp [Function.comp_apply]
      · have ne : p k ≠ p i := fun eq => h (bij.1 eq)
        simp [Function.comp_apply,Function.update_of_ne,h,ne]
    have boundary (x : Fin 14 → Bool) (hx : B F x) : B F (x ∘ p) := by
      rcases hx with ⟨hpos,hmin⟩ | ⟨hneg,hmax⟩
      · left
        refine ⟨(graphEq x).mpr hpos, ?_⟩
        intro i hi hnew
        rw [commute] at hnew
        exact hmin (p i) hi ((graphEq _).mp hnew)
      · right
        refine ⟨fun ha => hneg ((graphEq _).mp ha), ?_⟩
        intro i hi
        rw [commute]
        exact (graphEq _).mpr (hmax (p i) hi)
    have extend (x y : List Bool) (hlen : x.length=y.length) (hn : 14 ≤ x.length)
        (matchW : ∀ k, x.getD k false = y.getD (ren k) false) (z : List Bool) :
        ∀ k, (x++z).getD k false = (y++z).getD (ren k) false := by
      intro k
      by_cases h : k < x.length
      · have h' : ren k < y.length := by
          by_cases hh : k < 14
          · have := low hh; omega
          · rw [fixed (by omega)]; omega
        rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h']
        exact matchW k
      · rw [fixed (by omega),List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),hlen]
    have seedEq (x : Fin 14 → Bool) : ∀ k, (seed (x ∘ p)).getD k false = (seed x).getD (ren k) false := by
      have fr : free (x ∘ p) = free x := by
        rcases fix with ⟨h0,hj'⟩ | ⟨h0,hj'⟩ <;> simp [free,Function.comp_apply,p,h0,hj',evalOr,Bool.or_comm]
      simp only [seed,fr]
      apply extend _ _ (by simp) (by simp)
      intro k
      by_cases h : k<14
      · have read (f : Fin 14 → Bool) (i : Fin 14) : (List.ofFn f).getD i.val false = f i := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt)]
          simp only [List.getElem_ofFn]
        let i : Fin 14 := ⟨k,h⟩
        rw [show ren k = (p i).val from dite_eq_left h]
        exact (read (x ∘ p) i).trans (read x (p i)).symm
      · rw [fixed (by omega)]
        rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
    have atomEq (x : Fin 14 → Bool) (v : Fin 17) : atom (x ∘ p) v = atom x (lift p v) := by
      change (seed (x ∘ p) ++ [false,true]).getD v.val false = (seed x ++ [false,true]).getD (lift p v).val false
      rw [lifted]
      apply extend _ _ (by simp only [length_seed]) (by rw [length_seed]; decide) (seedEq x)
    let aa := lift p a
    let bb := lift p b
    let lo := min aa bb
    let hi := max aa bb
    have canon (x : Fin 14 → Bool) :
        comb op (atom (x ∘ p) a) (atom (x ∘ p) b) = comb op (atom x lo) (atom x hi) := by
      rw [atomEq,atomEq]
      rcases le_total aa bb with h | h
      · simp only [lo,hi,min_eq_left h,max_eq_right h,aa,bb]
      · simp only [lo,hi,min_eq_right h,max_eq_left h,aa,bb]
        cases op <;> simp [comb,Bool.or_comm,Bool.and_comm]
    have simulate (ls : List Gate) (x y : List Bool) (hlen : x.length=y.length) (hn : 14 ≤ x.length)
        (agree : ∀ k, x.getD k false = y.getD (ren k) false) :
        ∀ k, (run ls x).getD k false = (run (ls.map gate) y).getD (ren k) false := by
      induction ls generalizing x y with
      | nil => exact agree
      | cons g ls ih =>
        have ins : g.inputs.map (fun k => x.getD k false) =
            (g.inputs.map ren).map (fun k => y.getD k false) := by
          rw [List.map_map]
          exact List.map_congr_left (fun k _ => agree k)
        change ∀ k, (run ls (x ++ [g.op.eval _])).getD k false =
          (run (ls.map gate) (y ++ [g.op.eval _])).getD (ren k) false
        rw [ins]
        exact ih _ _ (by simp [hlen]) (by simp; omega) (extend _ _ hlen hn agree _)
    have hD : Monotone2 D := by
      intro g hg
      change g ∈ gs.map gate at hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      simpa only [gate,List.length_map] using mono v hv
    have counted := charge D lo hi op hs hD (by
      intro x hx
      have corr := ok (x ∘ p) (boundary x hx)
      rw [canon] at corr
      have ev := simulate gs _ _ (by simp only [List.length_append,length_seed])
        (by simp [length_seed]) (extend _ _ (by simp only [length_seed])
          (by rw [length_seed]; decide) (seedEq x) [comb op (atom x lo) (atom x hi)]) out
      change (run gs _).getD out false = (run (gs.map gate) _).getD (ren out) false at ev
      change (run (gs.map gate) _).getD (ren out) false = true ↔ F x
      rw [← ev]
      exact corr.trans (graphEq x))
    change 25 ≤ (gs.map gate).length at counted
    simpa only [List.length_map] using counted
  rcases C with ⟨gs,out⟩
  cases gs with
  | nil =>
    have bad := paid [] out 15 15 false hmono (by
      intro x hx
      have h := correct x hx
      change (seed x).getD out false = true ↔ F x at h
      change (seed x ++ [comb false (atom x 15) (atom x 15)]).getD out false = true ↔ F x
      simp only [read15,comb,Bool.false_eq_true,ite_false,Bool.or_self]
      by_cases hlt : out < (seed x).length
      · rwa [List.getD_append _ _ _ _ hlt]
      · rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [List.getD_eq_default _ _ (by omega)] at h
        cases out - (seed x).length <;> simpa using h)
    simp at bad
  | cons g gs =>
    have hk := hmono g (by simp)
    have hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hk
    obtain ⟨a,b,op,H⟩ := classify g hg
    have htail : Monotone2 ⟨gs,out⟩ := fun v hv => hmono v (List.mem_cons_of_mem _ hv)
    have h := paid gs out a b op htail (by
      intro x hB
      have eq := correct x hB
      change (⟨gs,out⟩ : Circuit).eval (seed x ++ [g.op.eval (g.inputs.map fun k => (seed x).getD k false)]) = true ↔ F x at eq
      rwa [H] at eq)
    change 26 ≤ (g :: gs).length
    simp only [List.length_cons]
    omega
