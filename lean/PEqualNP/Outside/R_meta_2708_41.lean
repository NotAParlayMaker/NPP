import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The Heawood graph has 37 maximal independent sets. Its 336 symmetries and an exchange of
-- the two output wires put the two opposite negative witnesses into thirteen representative pairs.
-- Each integer stores successive fourteen-bit input rows, with the low bits first.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_2708_41
  (boundary : ∀ (C : Circuit) (a : ℕ), Monotone2 C →
    let es : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
    let hit := fun x : Fin 14 → Bool => ∃ v w : Fin 14, (v.val,w.val) ∈ es ∧ x v = true ∧ x w = true
    let val := fun x : Fin 14 → Bool => (C.wires (List.ofFn x)).getD a false
    ∀ x, ¬ hit x → val x = true → ∃ h : Fin 37,
      val (fun i => (851443273546742815633452366165855361620043003567075327019484330638834190910994541292876580990816495532390521596238013513452042875020252705193610977262502015 : ℕ).testBit (14*h.val+i.val)) = true)
  (geometry : let row (t j : ℕ) (i : Fin 14) := t.testBit (14*j+i.val)
    let pos := row 4102984999651647307957327920005611094866467687867296087670008105841438761192997383061633
    let neg := row 851443273546742815633452366165855361620043003567075327019484330638834190910994541292876580990816495532390521596238013513452042875020252705193610977262502015
    let rep := row 3550396341084511536871745401863745197313443575557245541974600361644472658046470375804414795090700492726927487
    ∀ i j : Fin 37, i ≠ j → ∃ (t : Fin 14 → Fin 14) (k : Fin 13),
      (∀ u : Fin 21, ∃ v : Fin 21, pos u.val ∘ t = pos v.val) ∧
      (∀ u : Fin 37, ∃ v : Fin 37, neg u.val ∘ t = neg v.val) ∧
      (let x := rep (2*k.val) ∘ t
       let y := rep (2*k.val+1) ∘ t
       (x = neg i.val ∧ y = neg j.val) ∨ (x = neg j.val ∧ y = neg i.val)))
  (search : let row (t j : ℕ) (i : Fin 14) := t.testBit (14*j+i.val)
    let pos := row 4102984999651647307957327920005611094866467687867296087670008105841438761192997383061633
    let neg := row 851443273546742815633452366165855361620043003567075327019484330638834190910994541292876580990816495532390521596238013513452042875020252705193610977262502015
    let rep := row 3550396341084511536871745401863745197313443575557245541974600361644472658046470375804414795090700492726927487
    ∀ (D : Circuit) (a b : ℕ), Monotone2 D →
      let state := fun x : Fin 14 → Bool => ((D.wires (List.ofFn x)).getD a false,(D.wires (List.ofFn x)).getD b false)
      (∀ i : Fin 21, state (pos i.val) = (true,true)) →
      (∀ i : Fin 37, state (neg i.val) ≠ (true,true)) →
      (∃ k : Fin 13, state (rep (2*k.val)) = (false,true) ∧ state (rep (2*k.val+1)) = (true,false)) →
      26 ≤ D.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size := by
  intro C a b hm _ _
  dsimp only
  intro hp hn hab hba
  let es : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let hit := fun x : Fin 14 → Bool => ∃ v w : Fin 14, (v.val,w.val) ∈ es ∧ x v = true ∧ x w = true
  let val := fun w (x : Fin 14 → Bool) => (C.wires (List.ofFn x)).getD w false
  let row (t j : ℕ) (i : Fin 14) := t.testBit (14*j+i.val)
  let pos := row 4102984999651647307957327920005611094866467687867296087670008105841438761192997383061633
  let neg := row 851443273546742815633452366165855361620043003567075327019484330638834190910994541292876580990816495532390521596238013513452042875020252705193610977262502015
  let rep := row 3550396341084511536871745401863745197313443575557245541974600361644472658046470375804414795090700492726927487
  have positive : ∀ i : Fin 21, hit (pos i.val) := by dsimp [hit,es,pos,row]; decide +kernel
  have negative : ∀ i : Fin 37, ¬hit (neg i.val) := by dsimp [hit,es,neg,row]; decide +kernel
  obtain ⟨x,nx,ax,bx⟩ := hab
  obtain ⟨y,ny,byy,ay⟩ := hba
  obtain ⟨i,bi⟩ := boundary C b hm x nx bx
  obtain ⟨j,aj⟩ := boundary C a hm y ny ay
  change val b (neg i.val) = true at bi
  change val a (neg j.val) = true at aj
  have ai : val a (neg i.val) = false := by
    rcases hn _ (negative i) with h|h
    · exact h
    · exact False.elim (Bool.noConfusion (h.symm.trans bi))
  have bj : val b (neg j.val) = false := by
    rcases hn _ (negative j) with h|h
    · exact False.elim (Bool.noConfusion (h.symm.trans aj))
    · exact h
  have ne : i ≠ j := by rintro rfl; exact Bool.noConfusion (ai.symm.trans aj)
  obtain ⟨t,k,pmap,nmap,repmap⟩ := geometry i j ne
  change (∀ u : Fin 21, ∃ v : Fin 21, pos u.val ∘ t = pos v.val) at pmap
  change (∀ u : Fin 37, ∃ v : Fin 37, neg u.val ∘ t = neg v.val) at nmap
  change ((rep (2*k.val) ∘ t = neg i.val ∧ rep (2*k.val+1) ∘ t = neg j.val) ∨
          (rep (2*k.val) ∘ t = neg j.val ∧ rep (2*k.val+1) ∘ t = neg i.val)) at repmap
  let f (w : ℕ) := if h : w < 14 then (t ⟨w,h⟩).val else w
  let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
  let D : Circuit := ⟨C.gates.map rename,f C.output⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have md : Monotone2 D := by
    intro g hg
    change g ∈ C.gates.map rename at hg
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hg
    exact ⟨(hm o ho).1,by simpa [rename] using (hm o ho).2⟩
  have sim (z : Fin 14 → Bool) (w : ℕ) :
      (D.wires (List.ofFn z)).getD (f w) false = val w (z ∘ t) := by
    let u := List.ofFn (z ∘ t)
    let v := List.ofFn z
    have reads (s : List Bool) (i : ℕ) : (u++s).getD i false = (v++s).getD (f i) false := by
      simp only [u,v,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn]
      by_cases hi : i < 14
      · simp only [f,dite_eq_left hi,ite_eq_left hi,ite_eq_left (t ⟨i,hi⟩).isLt,List.getElem?_ofFn]
        rw [dite_eq_left (t ⟨i,hi⟩).isLt]
        rfl
      · simp only [f,dite_eq_right hi,ite_eq_right hi]
    have run (gs : List Gate) (s : List Bool) : ∃ q : List Bool,
        gs.foldl step (u++s) = u++q ∧ (gs.map rename).foldl step (v++s) = v++q := by
      induction gs generalizing s with
      | nil => exact ⟨s,rfl,rfl⟩
      | cons g gs ih =>
        let bit := g.op.eval (g.inputs.map fun i => (u++s).getD i false)
        have eb : bit = (rename g).op.eval ((rename g).inputs.map fun i => (v++s).getD i false) := by
          change g.op.eval _ = g.op.eval _
          congr 1
          simp only [rename,List.map_map]
          apply List.map_congr_left
          intro i _
          exact reads s i
        obtain ⟨q,h1,h2⟩ := ih (s++[bit])
        refine ⟨q,?_,?_⟩
        · simpa only [List.foldl_cons,step,List.append_assoc,bit] using h1
        · change (gs.map rename).foldl step ((v++s)++[_]) = _
          rw [← eb,List.append_assoc]
          exact h2
    obtain ⟨q,h1,h2⟩ := run C.gates []
    simp only [List.append_nil] at h1 h2
    change ((C.gates.map rename).foldl step v).getD (f w) false = (C.gates.foldl step u).getD w false
    rw [h1,h2]
    exact (reads q w).symm
  have pa (u : Fin 21) : val a (pos u.val ∘ t) = true ∧ val b (pos u.val ∘ t) = true := by
    obtain ⟨v,hv⟩ := pmap u
    rw [hv];exact hp _ (positive v)
  have nn (u : Fin 37) : val a (neg u.val ∘ t) = false ∨ val b (neg u.val ∘ t) = false := by
    obtain ⟨v,hv⟩ := nmap u
    rw [hv];exact hn _ (negative v)
  have sizeEq : D.size = C.size := List.length_map _
  rw [← sizeEq]
  rcases repmap with ⟨left,right⟩|⟨left,right⟩
  · apply search D (f a) (f b) md
    · intro u
      exact Prod.ext ((sim _ _).trans (pa u).1) ((sim _ _).trans (pa u).2)
    · intro u eq
      rcases nn u with h|h
      · exact Bool.noConfusion (h.symm.trans ((sim _ _).symm.trans (congrArg Prod.fst eq)))
      · exact Bool.noConfusion (h.symm.trans ((sim _ _).symm.trans (congrArg Prod.snd eq)))
    · refine ⟨k,Prod.ext ?_ ?_,Prod.ext ?_ ?_⟩
      · exact (sim _ _).trans (left.symm ▸ ai)
      · exact (sim _ _).trans (left.symm ▸ bi)
      · exact (sim _ _).trans (right.symm ▸ aj)
      · exact (sim _ _).trans (right.symm ▸ bj)
  · apply search D (f b) (f a) md
    · intro u
      exact Prod.ext ((sim _ _).trans (pa u).2) ((sim _ _).trans (pa u).1)
    · intro u eq
      rcases nn u with h|h
      · exact Bool.noConfusion (h.symm.trans ((sim _ _).symm.trans (congrArg Prod.snd eq)))
      · exact Bool.noConfusion (h.symm.trans ((sim _ _).symm.trans (congrArg Prod.fst eq)))
    · refine ⟨k,Prod.ext ?_ ?_,Prod.ext ?_ ?_⟩
      · exact (sim _ _).trans (left.symm ▸ bj)
      · exact (sim _ _).trans (left.symm ▸ aj)
      · exact (sim _ _).trans (right.symm ▸ bi)
      · exact (sim _ _).trans (right.symm ▸ ai)
