import Mathlib
import PEqualNP.Defs

open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity BigOperators

-- Compress each restriction by keeping a gate only when it adds a new truth table.
-- The first three premises coincide with the public bounds L-meta-2012, 2036 and 1664.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_4163_864
    (lower9 : let f := (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun d => x (Fin.ofNat 9 (d / 10)) && x (Fin.ofNat 9 (d % 10))))
      ¬ HasCircuitSize 9 f 14)
    (lowerA : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
      (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (lowerB : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 5 && x 7)) 11)
    (residual :
      ∀ (p s : List Gate) (g : Gate),
      let C : Circuit := ⟨⟨.or,[0,6]⟩ :: (p ++ g :: s),23⟩
      let rd (h : Gate) := if h.op.eval [false,false] then h.inputs.take 1 else h.inputs
      let w (v j : ℕ) (x : Fin 9 → Bool) :=
        (C.wires (List.ofFn fun i : Fin 9 => if i.val = v then false else x i)).getD j false
      let score (v : ℕ) := ((Finset.range 24).image (w v) \
        insert (fun _ => false) ((Finset.range 9).image (w v))).card
      FanInTwo C → p.length+s.length = 13 →
      (∀ h ∈ C.gates, ∀ i ∈ h.inputs, i ≤ 24) →
      g.op = .or → 6 ∈ rd g → (∀ h ∈ p ++ s, 6 ∉ rd h) →
      (p.filter (fun h => (rd h).contains 9)).length +
        (s.filter (fun h => (rd h).contains 9 || (rd h).contains (10+p.length))).length ≤ 3 →
      (∀ v < 10, (if v = 9 then 15 else if v ∈ ([4,6,7] : List ℕ) then 13 else 12) ≤ score v) →
      ¬ ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit (tableIndex x))
    : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) =>   have x2 : ℕ := PEqualNP.MetaComplexity.tableIndex x1;   ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x2 / (64 : ℕ)) (0 : ℕ)).testBit (x2 % (64 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => if x3.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs; ∀ (x4 x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x4 ++ x6 :: x5, output := x7 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 → x4.length + x5.length ≤ (13 : ℕ) → (∀ x11 ∈ x4 ++ x5, ((x3 x11).any fun (x13 : ℕ) => Decidable.decide (x13 = (6 : ℕ))) = Bool.false) → ((x3 x6).any fun (x12 : ℕ) => Decidable.decide (x12 = (6 : ℕ))) = Bool.true → x6.op = PEqualNP.CircuitLowerBounds.GateOp.or → (10 : ℕ) ≤ x4.length + x5.length - ((List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (x3 x14).contains (9 : ℕ)) x4).length + (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (x3 x14).contains (9 : ℕ) || (x3 x14).contains ((10 : ℕ) + x4.length)) x5).length) → ¬((∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.false x15) = x1 x15) ∧ ∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.true x15) = (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ)))) := by
  have petCompress (n m : ℕ) (L : List Gate) (seed : (Fin n → Bool) → List Bool)
      (len : ∀ x, (seed x).length = m)
      (initial : ∀ j : ℕ, (∀ x, (seed x).getD j false = false) ∨
        ∃ i : Fin n, ∀ x, (seed x).getD j false = x i)
      (fan : FanInTwo ⟨L,0⟩) (o : ℕ) :
      let w (j : ℕ) (x : Fin n → Bool) := ((⟨L,0⟩ : Circuit).wires (seed x)).getD j false
      let A := (Finset.range (m + L.length)).image w
      let B := insert (fun _ : Fin n → Bool => false) ((Finset.range m).image w)
      HasCircuitSize n (w o) (A \ B).card := by
    clear lower9 lowerA lowerB residual
    classical
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have ext (xs : List Gate) (u : List Bool) : ∃ v, xs.foldl step u = u ++ v := by
      induction xs generalizing u with
      | nil => exact ⟨[],by simp⟩
      | cons a xs ih =>
        obtain ⟨t,h⟩ := ih (step u a)
        exact ⟨[_] ++ t,by simpa [step,List.foldl_cons,List.append_assoc] using h⟩
    have lens (xs : List Gate) (u : List Bool) : (xs.foldl step u).length = u.length + xs.length := by
      induction xs generalizing u with
      | nil => simp
      | cons a xs ih => rw [List.foldl_cons,ih]; simp [step]; omega
    have snocNe (u : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ u.length) :
        (u ++ [b]).getD i false = u.getD i false := by
      by_cases h : i < u.length
      · exact List.getD_append _ _ _ _ h
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
    have snocEq (u : List Bool) (b : Bool) : (u ++ [b]).getD u.length false = b := by simp
    let Z := fun _ : Fin n → Bool => false
    let V (xs : List Gate) (j : ℕ) (x : Fin n → Bool) := (xs.foldl step (seed x)).getD j false
    let val (xs : List Gate) (g : Gate) (x : Fin n → Bool) := g.op.eval (g.inputs.map fun i => V xs i x)
    let pool (xs : List Gate) := (Finset.range (m+xs.length)).image (V xs)
    let basis := insert Z ((Finset.range m).image (V []))
    let fresh (xs : List Gate) := pool xs \ basis
    have preserve (xs : List Gate) (i : ℕ) (hi : i < m) : V xs i = V [] i := by
      funext x
      obtain ⟨v,hv⟩ := ext xs (seed x)
      change (xs.foldl step (seed x)).getD i false = (seed x).getD i false
      rw [hv,List.getD_append _ _ _ _ (by rwa [len])]
    have far (xs : List Gate) : V xs (m+xs.length) = Z := by
      funext x
      change (xs.foldl step (seed x)).getD _ false = false
      apply List.getD_eq_default
      rw [lens,len]
    have next (xs : List Gate) (g : Gate) (i : ℕ) :
        V (xs ++ [g]) i = if i = m+xs.length then val xs g else V xs i := by
      funext x
      change ((xs ++ [g]).foldl step (seed x)).getD i false = _
      rw [List.foldl_append]
      change ((xs.foldl step (seed x)) ++ [val xs g x]).getD i false = _
      by_cases h : i = m+xs.length
      · rw [ite_eq_left h]
        have e : i = (xs.foldl step (seed x)).length := by rw [lens,len,h]
        rw [e,snocEq]
      · rw [ite_eq_right h]
        apply snocNe
        rwa [lens,len]
    have build (xs : List Gate) (ok : FanInTwo ⟨xs,0⟩) :
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ (fresh xs).card ∧
        ∀ i : ℕ, ∃ j : ℕ, ∀ x : Fin n → Bool,
          (D.wires (List.ofFn x)).getD j false = V xs i x := by
      induction xs using List.reverseRecOn with
      | nil =>
        refine ⟨⟨[],0⟩,?_,Nat.zero_le _,?_⟩
        · intro g h; cases h
        · intro i
          rcases initial i with hz | ⟨j,hj⟩
          · refine ⟨n,fun x => ?_⟩
            change (List.ofFn x).getD n false = (seed x).getD i false
            rw [hz]; simp
          · refine ⟨j.val,fun x => ?_⟩
            change (List.ofFn x).getD j.val false = (seed x).getD i false
            rw [hj]; simp
      | append_singleton xs g ih =>
        obtain ⟨D,hm,hs,links⟩ := ih (fun a ha => ok a (List.mem_append_left _ ha))
        choose idx hidx using links
        have oldSub : fresh xs ⊆ fresh (xs ++ [g]) := by
          intro f hf
          obtain ⟨hpool,hb⟩ := Finset.mem_sdiff.mp hf
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hpool
          have lt := Finset.mem_range.mp hi
          apply Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by simp; omega),?_⟩,hb⟩
          rw [next,ite_eq_right (Nat.ne_of_lt lt)]
        have covered (hc : val xs g ∈ pool xs ∨ val xs g ∈ basis) :
            ∃ j, ∀ x, (D.wires (List.ofFn x)).getD j false = val xs g x := by
          rcases hc with h | h
          · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
            exact ⟨idx i,fun x => (hidx i x).trans (congrFun hi x)⟩
          · rcases Finset.mem_insert.mp h with hz | h
            · exact ⟨idx (m+xs.length),fun x => (hidx _ x).trans (congrFun ((far xs).trans hz.symm) x)⟩
            · obtain ⟨i,hi,e⟩ := Finset.mem_image.mp h
              exact ⟨idx i,fun x => (hidx _ x).trans (congrFun ((preserve xs i (Finset.mem_range.mp hi)).trans e) x)⟩
        by_cases already : val xs g ∈ pool xs ∨ val xs g ∈ basis
        · obtain ⟨j,hj⟩ := covered already
          refine ⟨D,hm,hs.trans (Finset.card_le_card oldSub),?_⟩
          intro i
          by_cases e : i = m+xs.length
          · exact ⟨j,fun x => (hj x).trans (congrFun ((next xs g i).trans (ite_eq_left e)).symm x)⟩
          · exact ⟨idx i,fun x => (hidx i x).trans (congrFun ((next xs g i).trans (ite_eq_right e)).symm x)⟩
        · have vnew : val xs g ∈ fresh (xs++[g]) := by
            refine Finset.mem_sdiff.mpr ⟨?_,fun h => already (Or.inr h)⟩
            apply Finset.mem_image.mpr
            exact ⟨m+xs.length,Finset.mem_range.mpr (by simp),(next _ _ _).trans (ite_eq_left rfl)⟩
          have inc : (fresh xs).card < (fresh (xs++[g])).card := by
            apply Finset.card_lt_card
            exact Finset.ssubset_iff_of_subset oldSub |>.mpr ⟨_,vnew,fun h => already (.inl (Finset.mem_sdiff.mp h).1)⟩
          let a : Gate := ⟨g.op,g.inputs.map idx⟩
          let D' : Circuit := ⟨D.gates ++ [a],0⟩
          have strong (x : Fin n → Bool) : D'.wires (List.ofFn x) =
              D.wires (List.ofFn x) ++ [val xs g x] := by
            change ((D.gates ++ [a]).foldl step (List.ofFn x)) = _
            rw [List.foldl_append]
            change D.wires (List.ofFn x) ++ [g.op.eval ((g.inputs.map idx).map _)] = _
            simp only [List.map_map]
            congr 3
            apply List.map_congr_left
            intro i _
            exact hidx i x
          have ld (x : Fin n → Bool) : (D.wires (List.ofFn x)).length = n+D.size := by
            change (D.gates.foldl step (List.ofFn x)).length = _
            rw [lens,List.length_ofFn]
            rfl
          refine ⟨D',?_,?_,?_⟩
          · intro b hb
            change b ∈ D.gates ++ [a] at hb
            rcases List.mem_append.mp hb with p | p
            · exact hm b p
            · obtain rfl := List.mem_singleton.mp p
              have ha := ok g (List.mem_append_right xs (List.mem_singleton_self _))
              exact ⟨ha.1,by simpa [a] using ha.2⟩
          · change (D.gates++[a]).length ≤ _
            change D.gates.length ≤ _ at hs
            simp only [List.length_append,List.length_singleton]
            omega
          · intro i
            by_cases h : i = m+xs.length
            · refine ⟨n+D.size,fun x => ?_⟩
              rw [strong,← ld x,snocEq,next,ite_eq_left h]
            · by_cases b : idx i = n+D.size
              · refine ⟨n+D.size+1,fun x => ?_⟩
                rw [strong,List.getD_eq_default _ _ (by simp [ld]),next,ite_eq_right h,← hidx i x,b]
                exact (List.getD_eq_default _ _ (by rw [ld])).symm
              · refine ⟨idx i,fun x => ?_⟩
                rw [strong,snocNe _ _ _ (by rwa [ld]),next,ite_eq_right h]
                exact hidx i x
    obtain ⟨D,hm,hs,bind⟩ := build L fan
    obtain ⟨j,res⟩ := bind o
    have basisL : (Finset.range m).image (V L) = (Finset.range m).image (V []) := by
      apply Finset.image_congr
      intro i hi
      exact preserve L i (Finset.mem_range.mp hi)
    refine ⟨⟨D.gates,j⟩,hm,?_,res⟩
    change D.size ≤ (pool L \ insert Z ((Finset.range m).image (V L))).card
    rw [basisL]
    exact hs

  have petDeck4163 :
    let standard (y : Fin 9 → Bool) :=
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun d => y (Fin.ofNat 9 (d / 10)) && y (Fin.ofNat 9 (d % 10)))
    let f2036 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
      (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
    let f1664 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 5 && x 7)
    let pull (y : Fin 9 → Bool) (i : Fin 8) :=
      ([y 1,y 0,y 5,y 8,y 2,y 4,y 7,y 3] : List Bool).getD i.val false
    let packed (x : Fin 8 → Bool) :=
      let n := tableIndex x
      (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608]
        : List ℕ).getD (n / 64) 0).testBit (n % 64)
    (∀ v : Fin 9, ∃ lift : (Fin 8 → Bool) → Fin 9 → Bool,
      (∀ x, lift x v = false) ∧
      (∀ j, (∀ x, lift x j = false) ∨ ∃ i : Fin 8, ∀ x, lift x j = x i) ∧
      (∀ x, standard (lift x) = if v.val ∈ ([4,6,7] : List ℕ) then f2036 x else f1664 x)) ∧
    (∀ y : Fin 9 → Bool, standard y =
      (if y 6 then packed (pull y) || y 1 || y 8 else packed (pull y))) := by
    clear lower9 lowerA lowerB residual petCompress
    let standard (y : Fin 9 → Bool) :=
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun d => y (Fin.ofNat 9 (d / 10)) && y (Fin.ofNat 9 (d % 10)))
    let f2036 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
      (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
    let f1664 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 5 && x 7)
    let pull (y : Fin 9 → Bool) (i : Fin 8) :=
      ([y 1,y 0,y 5,y 8,y 2,y 4,y 7,y 3] : List Bool).getD i.val false
    let packed (x : Fin 8 → Bool) :=
      let n := tableIndex x
      (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608]
        : List ℕ).getD (n / 64) 0).testBit (n % 64)
    let deck : List (List ℕ) :=
      [[8,7,3,2,6,0,5,4,1],
       [0,8,7,3,4,1,6,5,2],
       [1,0,8,7,5,2,4,6,3],
       [2,1,0,8,6,3,5,4,7],
       [0,1,2,3,8,4,5,6,7],
       [0,1,2,3,4,8,5,6,7],
       [1,0,4,7,5,2,8,6,3],
       [2,1,5,7,3,6,0,8,4],
       [1,2,3,7,5,0,6,4,8]]
    let src (v j : Fin 9) := (deck.getD v.val []).getD j.val 8
    let lift (v : Fin 9) (x : Fin 8 → Bool) (j : Fin 9) :=
      if h : src v j < 8 then x ⟨src v j,h⟩ else false
    have missing : ∀ v : Fin 9, src v v = 8 := by decide
    have cofactor : ∀ (v : Fin 9) (x : Fin 8 → Bool), standard (lift v x) =
        if v.val ∈ ([4,6,7] : List ℕ) then f2036 x else f1664 x := by
      decide +kernel
    have bridge : ∀ y : Fin 9 → Bool, standard y =
        (if y 6 then packed (pull y) || y 1 || y 8 else packed (pull y)) := by
      decide +kernel
    refine ⟨fun v => ⟨lift v,?_,?_,cofactor v⟩,bridge⟩
    · intro x
      simp only [lift,missing]
      rfl
    · intro j
      by_cases h : src v j < 8
      · exact Or.inr ⟨⟨_,h⟩,fun x => by simp only [lift,dite_eq_left h]⟩
      · exact Or.inl (fun x => by simp only [lift,dite_eq_right h])

  have petClamp4163 :
      let cap (g : Gate) : Gate := ⟨g.op,g.inputs.map (fun i => min i 24)⟩
      let rd (g : Gate) := if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
      (∀ (gs : List Gate) (u : List Bool) (o : ℕ), u.length + gs.length ≤ 24 →
        (⟨gs.map cap,o⟩ : Circuit).eval u = (⟨gs,o⟩ : Circuit).eval u) ∧
      (∀ (g : Gate) (i : ℕ), i < 24 → (rd (cap g)).contains i = (rd g).contains i) ∧
      (∀ (g : Gate) (i : ℕ), i ∈ (cap g).inputs → i ≤ 24) ∧
      (∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ → FanInTwo ⟨gs.map cap,o⟩) := by
    clear lower9 lowerA lowerB residual petCompress petDeck4163
    intro cap rd
    let step (u : List Bool) (g : Gate) :=
      u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
    have readCap (u : List Bool) (h : u.length ≤ 24) (i : ℕ) :
        u.getD (min i 24) false = u.getD i false := by
      by_cases hi : i ≤ 24
      · rw [Nat.min_eq_left hi]
      · have le : 24 ≤ i := by omega
        rw [Nat.min_eq_right le,List.getD_eq_default _ _ h,List.getD_eq_default _ _ (by omega)]
    have allWire (gs : List Gate) (u : List Bool) (h : u.length + gs.length ≤ 24) :
        (gs.map cap).foldl step u = gs.foldl step u := by
      induction gs generalizing u with
      | nil => rfl
      | cons g gs ih =>
        have bound : u.length ≤ 24 := by simp only [List.length_cons] at h; omega
        have args : g.inputs.map (fun i => u.getD (min i 24) false) = g.inputs.map (fun i => u.getD i false) :=
          List.map_congr_left (fun i _ => readCap u bound i)
        have single : step u (cap g) = step u g := by
          change u ++ [g.op.eval ((g.inputs.map (fun i => min i 24)).map fun i => u.getD i false)] = u ++ [_]
          simp only [List.map_map,Function.comp_def,args]
        simp only [List.map_cons,List.foldl_cons,single]
        apply ih
        simp only [step,List.length_append,List.length_cons,List.length_nil] at h ⊢
        omega
    have used (g : Gate) : rd (cap g) = (rd g).map (fun i => min i 24) := by
      rcases g with ⟨op,ls⟩
      cases c : op.eval [false,false] <;> cases ls <;> simp [cap,rd,c]
    have contains (ls : List ℕ) (j : ℕ) (hj : j < 24) :
        (ls.map (fun i => min i 24)).contains j = ls.contains j := by
      have same (i : ℕ) : (min i 24 == j) = (i == j) ∧ (j == min i 24) = (j == i) := by
        by_cases h : i ≤ 24
        · simp [Nat.min_eq_left h]
        · have le : 24 ≤ i := by omega
          have a : 24 ≠ j := by omega
          have b : i ≠ j := by omega
          simp [Nat.min_eq_right le,a,b,Ne.symm a,Ne.symm b]
      induction ls with
      | nil => rfl
      | cons i ls ih =>
        simp only [List.map_cons,List.contains_cons,(same i).1,(same i).2,ih]
    refine ⟨?_,?_,?_,?_⟩
    · intro gs u o h
      exact congrArg (fun w : List Bool => w.getD o false) (allWire gs u h)
    · intro g i h
      rw [used]
      exact contains (rd g) i h
    · intro g i h
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
      exact Nat.min_le_right _ _
    · intro gs o h g hg
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
      have ok := h k hk
      exact ⟨ok.1,by simpa only [cap,List.length_map] using ok.2⟩

  classical
  let full := (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun d => x (Fin.ofNat 9 (d / 10)) && x (Fin.ofNat 9 (d % 10))))
  let fa := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
      (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
  let fb := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
      (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 7) || (x 5 && x 7))
  let raw (v : ℕ) (x : Fin 9 → Bool) (i : Fin 9) := if i.val = v then false else x i
  let W (C : Circuit) (v j : ℕ) (x : Fin 9 → Bool) := (C.wires (List.ofFn (raw v x))).getD j false
  let score (C : Circuit) (v : ℕ) := ((Finset.range 24).image (W C v) \
    insert (fun _ => false) ((Finset.range 9).image (W C v))).card
  have scores (C : Circuit) (fan : FanInTwo C) (sz : C.gates.length = 15)
      (agree : ∀ x, C.eval (List.ofFn x) = full x) :
      ∀ v < 10, (if v = 9 then 15 else if v ∈ ([4,6,7] : List ℕ) then 13 else 12) ≤ score C v := by
    have compact {n : ℕ} (lift : (Fin n → Bool) → Fin 9 → Bool)
        (axis : ∀ j, (∀ x, lift x j = false) ∨ ∃ i : Fin n, ∀ x, lift x j = x i) :
        let w (j : ℕ) (x : Fin n → Bool) := (C.wires (List.ofFn (lift x))).getD j false
        HasCircuitSize n (fun x => C.eval (List.ofFn (lift x)))
          (((Finset.range 24).image w \ insert (fun _ => false) ((Finset.range 9).image w)).card) := by
      have init : ∀ j : ℕ, (∀ x, (List.ofFn (lift x)).getD j false = false) ∨
          ∃ i : Fin n, ∀ x, (List.ofFn (lift x)).getD j false = x i := by
        intro j
        by_cases hj : j < 9
        · have lookup (x) : (List.ofFn (lift x)).getD j false = lift x ⟨j,hj⟩ := by
            rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn]
          rcases axis ⟨j,hj⟩ with h | ⟨i,h⟩
          · exact .inl fun x => (lookup x).trans (h x)
          · exact .inr ⟨i,fun x => (lookup x).trans (h x)⟩
        · exact .inl fun x => List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)
      have z := petCompress n 9 C.gates (fun x => List.ofFn (lift x)) (by simp) init fan C.output
      dsimp only at z ⊢
      rw [show 9+C.gates.length = 24 by omega] at z
      convert z using 1 <;> first | rfl | (congr 1; ext f; simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_image]; rfl)
    have need {n k b : ℕ} {f g : (Fin n → Bool) → Bool} (eq : ∀ x, f x = g x)
        (bad : ¬ HasCircuitSize n g b) (reach : HasCircuitSize n f k) : b+1 ≤ k := by
      by_contra! small
      obtain ⟨D,hm,hs,ev⟩ := reach
      exact bad ⟨D,hm,hs.trans (by omega),fun x => (ev x).trans (eq x)⟩
    have projected {α β : Type} [DecidableEq α] [DecidableEq β] (h : α → β) (A B : Finset α) :
        (A.image h \ B.image h).card ≤ (A \ B).card := by
      apply Nat.le_trans (m := ((A \ B).image h).card) _ Finset.card_image_le
      apply Finset.card_le_card
      intro y hy
      obtain ⟨hA,hB⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA
      exact Finset.mem_image.mpr ⟨x,Finset.mem_sdiff.mpr ⟨hx,fun hxB => hB (Finset.mem_image_of_mem h hxB)⟩,rfl⟩
    intro v hv
    by_cases last : v = 9
    · subst v
      have free (x : Fin 9 → Bool) : raw 9 x = x := by
        funext i
        simp [raw,Nat.ne_of_lt i.isLt]
      have idW : W C 9 = fun j (x : Fin 9 → Bool) => (C.wires (List.ofFn x)).getD j false := by
        funext j x
        change (C.wires (List.ofFn (raw 9 x))).getD j false = _
        rw [free]
      have reach := compact (n:=9) (fun x => x) (fun j => .inr ⟨j,fun _ => rfl⟩)
      simpa only [score,idW,ite_true] using (need agree lower9 reach)
    · let vertex : Fin 9 := ⟨v,by omega⟩
      obtain ⟨lift,atZero,axis,edge⟩ := petDeck4163.1 vertex
      let s (j : ℕ) (x : Fin 8 → Bool) := (C.wires (List.ofFn (lift x))).getD j false
      let pull (f : (Fin 9 → Bool) → Bool) (x : Fin 8 → Bool) := f (lift x)
      have clipped (x) : raw v (lift x) = lift x := by
        funext i
        by_cases e : i.val = v
        · have eq : i = vertex := Fin.ext e
          subst i
          simpa [raw,vertex] using (atZero x).symm
        · simp [raw,e]
      have transfer (k : ℕ) : ((Finset.range k).image (W C v)).image pull = (Finset.range k).image s := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro j _
        funext x
        change (C.wires (List.ofFn (raw v (lift x)))).getD j false = _
        rw [clipped]
      have le : ((Finset.range 24).image s \ insert (fun _ => false) ((Finset.range 9).image s)).card ≤ score C v := by
        have h := projected pull ((Finset.range 24).image (W C v))
          (insert (fun _ => false) ((Finset.range 9).image (W C v)))
        simpa only [Finset.image_insert,transfer] using h
      have reach := compact lift axis
      by_cases heavy : v ∈ ([4,6,7] : List ℕ)
      · have shape (x : Fin 8 → Bool) : C.eval (List.ofFn (lift x)) = fa x := by
          exact (agree _).trans (by simpa only [vertex,heavy,ite_true] using edge x)
        simpa only [ite_eq_right last,ite_eq_left heavy] using (need shape lowerA reach).trans le
      · have shape (x : Fin 8 → Bool) : C.eval (List.ofFn (lift x)) = fb x := by
          exact (agree _).trans (by simpa only [vertex,ite_eq_right heavy] using edge x)
        simpa only [ite_eq_right last,ite_eq_right heavy] using (need shape lowerB reach).trans le
  intro T I rd p s g o D fan budget quiet rawG opG limits both
  let first : Gate := ⟨.or,[0,6]⟩
  let gates := first :: (p ++ g :: s)
  let step (w : List Bool) (h : Gate) := w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
  let pull (y : Fin 9 → Bool) (i : Fin 8) := ([y 1,y 0,y 5,y 8,y 2,y 4,y 7,y 3] : List Bool).getD i.val false
  have boot (x : Fin 9 → Bool) : step (List.ofFn x) first = I (x 6) (pull x) := by
    change [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 0 || (x 6 || false)] =
      [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 0 || x 6]
    simp
  have correct (x : Fin 9 → Bool) : (⟨gates,o⟩ : Circuit).eval (List.ofFn x) = full x := by
    have orig : (⟨gates,o⟩ : Circuit).eval (List.ofFn x) = D.eval (I (x 6) (pull x)) := by
      change ((first :: (p ++ g :: s)).foldl step (List.ofFn x)).getD o false =
        ((p ++ g :: s).foldl step (I (x 6) (pull x))).getD o false
      rw [List.foldl_cons,boot]
    have view : full x = (if x 6 then T (pull x) || x 1 || x 8 else T (pull x)) := petDeck4163.2 x
    rw [orig,view]
    cases b : x 6 with
    | false => exact both.1 _
    | true => exact both.2 _
  have fits : FanInTwo ⟨gates,o⟩ := by
    intro h hh
    rcases List.mem_cons.mp hh with e | e
    · subst h
      exact ⟨Or.inr (Or.inl rfl),by decide⟩
    · exact fan _ e
  have qty : gates.length = 15 := by
    have up : gates.length ≤ 15 := by simp [gates]; omega
    by_contra bad
    apply lower9
    exact ⟨⟨gates,o⟩,fits,(show gates.length ≤ 14 by omega),correct⟩
  have ps : p.length + s.length = 13 := by
    have h := qty
    simp only [gates,List.length_cons,List.length_append] at h
    omega
  have outLast (gs : List Gate) (ok : FanInTwo ⟨gs,o⟩) (len : gs.length = 15)
      (ev : ∀ x : Fin 9 → Bool, (⟨gs,o⟩ : Circuit).eval (List.ofFn x) = full x) : o = 23 := by
    induction gs using List.reverseRecOn with
    | nil => simp at len
    | append_singleton rest last _ =>
      have lr : rest.length = 14 := by simpa using len
      by_contra h
      apply lower9
      refine ⟨⟨rest,o⟩,(fun a ha => ok a (List.mem_append_left _ ha)),lr.le,?_⟩
      intro x
      let u := rest.foldl step (List.ofFn x)
      have lens (ls : List Gate) (w : List Bool) : (ls.foldl step w).length = w.length+ls.length := by
        induction ls generalizing w with
        | nil => simp
        | cons a ls ih => rw [List.foldl_cons,ih]; simp [step]; omega
      have lu : u.length = 23 := by simp only [u,lens,List.length_ofFn,lr]
      have ex := ev x
      change ((rest++[last]).foldl step (List.ofFn x)).getD o false = full x at ex
      rw [List.foldl_append] at ex
      change (u ++ [last.op.eval (last.inputs.map fun i => u.getD i false)]).getD o false = full x at ex
      change u.getD o false = full x
      by_cases inside : o < u.length
      · rwa [List.getD_append _ _ _ _ inside] at ex
      · have far : u.length < o := by omega
        rw [List.getD_eq_default _ _ (by simp; omega)] at ex
        rwa [List.getD_eq_default _ _ (by omega)]
  have oo := outLast gates fits qty correct
  subst o
  let cap (h : Gate) : Gate := ⟨h.op,h.inputs.map (fun i => min i 24)⟩
  let P := p.map cap
  let S := s.map cap
  let G := cap g
  let C : Circuit := ⟨first :: (P ++ G :: S),23⟩
  have capFirst : cap first = first := rfl
  have mapped : gates.map cap = C.gates := by simp [gates,C,P,S,G,capFirst]
  have agrees (x : Fin 9 → Bool) : C.eval (List.ofFn x) = full x := by
    have q := petClamp4163.1 gates (List.ofFn x) 23 (by simp [qty])
    change (⟨gates.map cap,23⟩ : Circuit).eval (List.ofFn x) = _ at q
    rw [mapped] at q
    exact q.trans (correct x)
  have fanC : FanInTwo C := by
    intro h hh
    rw [← mapped] at hh
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hh
    have kh := fits k hk
    exact ⟨kh.1,by simpa [cap] using kh.2⟩
  have sizeC : C.gates.length = 15 := by rw [← mapped,List.length_map,qty]
  have psC : P.length + S.length = 13 := by simpa [P,S] using ps
  have rdCap (h : Gate) (j : ℕ) (hj : j < 24) : (rd (cap h)).contains j = (rd h).contains j :=
    petClamp4163.2.1 h j hj
  have useG : 6 ∈ rd G := by
    have hr : 6 ∈ rd g := by simpa using rawG
    have old : (rd g).contains 6 = true := by simpa using hr
    have new := (rdCap g 6 (by decide)).trans old
    simpa [G] using new
  have freeG : ∀ h ∈ P ++ S, 6 ∉ rd h := by
    intro h hh
    change h ∈ p.map cap ++ s.map cap at hh
    rw [← List.map_append] at hh
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hh
    have old : 6 ∉ rd k := by
      intro yes
      have t : (rd k).any (fun j => decide (j = 6)) = true := List.any_eq_true.mpr ⟨6,yes,by decide⟩
      exact Bool.noConfusion ((quiet k hk).symm.trans t)
    have oldB : (rd k).contains 6 = false := by simpa using old
    have new := (rdCap k 6 (by decide)).trans oldB
    simpa using new
  have filters {a b : Gate → Bool} (xs : List Gate) (eq : ∀ h, a (cap h) = b h) :
      ((xs.map cap).filter a).length = (xs.filter b).length := by
    induction xs with
    | nil => rfl
    | cons h xs ih =>
      cases e : b h <;> simp [List.filter_cons,eq,e,ih]
  have tally : (P.filter (fun h => (rd h).contains 9)).length +
      (S.filter (fun h => (rd h).contains 9 || (rd h).contains (10+P.length))).length ≤ 3 := by
    have limit : 10+p.length < 24 := by omega
    have left := filters (a := fun h => (rd h).contains 9) (b := fun h => (rd h).contains 9)
      p (fun h => rdCap h 9 (by decide))
    have right := filters (a := fun h => (rd h).contains 9 || (rd h).contains (10+p.length))
      (b := fun h => (rd h).contains 9 || (rd h).contains (10+p.length))
      s (fun h => by rw [rdCap h 9 (by decide),rdCap h _ limit])
    simp only [P,S,List.length_map]
    rw [left,right]
    omega
  have dense : ∀ x : Fin 9 → Bool, full x = (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit (tableIndex x) := by decide +kernel
  apply residual P S G fanC psC _ opG useG freeG tally (scores C fanC sizeC agrees) (fun x => (agrees x).trans (dense x))
  · intro h hh i hi
    rw [← mapped] at hh
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hh
    exact petClamp4163.2.2.1 k i hi
