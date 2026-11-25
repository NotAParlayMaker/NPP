import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.R_meta_3983_418
    (terminal :
    ∀ (gs : List BinaryGate) (g : BinaryGate),
      0 < gs.length → 8 ≤ g.left → 8 ≤ g.right → g.left < 8+gs.length →
      g.right < 8+gs.length → g.left ≠ g.right →
      (∀ i < gs.length, ∃ v ∈ (gs++[g]).drop (i+1), v.left=8+i ∨ v.right=8+i) →
      ∃ j : Nat, 8 ≤ j ∧ j < 7+gs.length ∧
        ((g.left=7+gs.length ∧ g.right=j) ∨ (g.left=j ∧ g.right=7+gs.length)) ∧
        ∀ i < gs.length-1, j=8+i ∨ ∃ v ∈ gs.drop (i+1), v.left=8+i ∨ v.right=8+i)
    (collision :
    let f (x : Fin 7 → Bool) := ([1,12,4,15,26,35,46,63] : List Nat).any fun e =>
      x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
    ∀ (side : Bool) (gs : List BinaryGate), 7 ≤ gs.length → gs.length ≤ 9 →
      (∀ i (h : i < gs.length), let g := gs[i];
        (∃ a b : Bool, g.op = fun x y => (x==a) && (y==b)) ∧
        g.left < 8+i ∧ g.right < 8+i ∧ g.left ≠ 7 ∧ g.right ≠ 7 ∧ g.left ≠ g.right) →
      let reads := gs.flatMap fun g => [g.left,g.right]
      12 ≤ gs.length + ((Finset.range 7).filter fun i => reads.count i=1).card →
      (∀ g ∈ gs, g.left<7 → g.right<7 → reads.count g.left≠1 ∨ reads.count g.right≠1) →
      ∀ j : Nat, 8 ≤ j → j < 7+gs.length →
      (∀ i < gs.length-1, j=8+i ∨ ∃ g ∈ gs.drop (i+1), g.left=8+i ∨ g.right=8+i) →
      let w (x : Fin 7 → Bool) := (BinaryCircuit.mk gs 0).wires (List.ofFn x ++ [false])
      let trace (x : Fin 7 → Bool) := ((w x).getD (7+gs.length) false,(w x).getD j false)
      (∀ x, f x=side → trace x=trace (fun _ => side)) →
      ∃ x, f x=(!side) ∧ trace x=trace (fun _ => side)) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (63 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (7 : ℕ) → Bool) → List Bool := fun (x2 : Fin (7 : ℕ) → Bool) => List.ofFn x2 ++ [Bool.false]; have x3 : ℕ → PEqualNP.MetaComplexity.BinaryGate → Prop := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.BinaryGate) => (∃ (x5 : Bool) (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) ∧ x4.left < x3 ∧ x4.right < x3 ∧ x4.left ≠ (7 : ℕ) ∧ x4.right ≠ (7 : ℕ) ∧ x4.left ≠ x4.right; ¬∃ (x4 : List PEqualNP.MetaComplexity.BinaryGate) (x5 : PEqualNP.MetaComplexity.BinaryGate) (x6 : Bool),     have x7 : List ℕ := List.flatMap (fun (x7 : PEqualNP.MetaComplexity.BinaryGate) => [x7.left, x7.right]) (x4 ++ [x5]);     (7 : ℕ) ≤ x4.length ∧ x4.length ≤ (9 : ℕ) ∧ (∀ (x8 : ℕ) (x9 : x8 < x4.length), x3 ((8 : ℕ) + x8) x4[x8]) ∧ x3 ((8 : ℕ) + x4.length) x5 ∧ (8 : ℕ) ≤ x5.left ∧ (8 : ℕ) ≤ x5.right ∧ (∀ x8 < x4.length, ∃ x10 ∈ List.drop (x8 + (1 : ℕ)) (x4 ++ [x5]), x10.left = (8 : ℕ) + x8 ∨ x10.right = (8 : ℕ) + x8) ∧ (12 : ℕ) ≤ x4.length + {x8 ∈ Finset.range (7 : ℕ) | List.count x8 x7 = (1 : ℕ)}.card ∧ (∀ x8 ∈ x4 ++ [x5], x8.left < (7 : ℕ) → x8.right < (7 : ℕ) → List.count x8.left x7 ≠ (1 : ℕ) ∨ List.count x8.right x7 ≠ (1 : ℕ)) ∧ ∀ (x8 : Fin (7 : ℕ) → Bool), ({ gates := x4 ++ [x5], output := (8 : ℕ) + x4.length : PEqualNP.MetaComplexity.BinaryCircuit }.eval (x2 x8) != x6) = x1 x8 := by
  let f (x : Fin 7 → Bool) := ([1,12,4,15,26,35,46,63] : List Nat).any fun e =>
    x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
  let input (x : Fin 7 → Bool) := List.ofFn x ++ [false]
  let good (n : Nat) (g : BinaryGate) := (∃ a b : Bool, g.op=fun x y => (x==a) && (y==b)) ∧
    g.left<n ∧ g.right<n ∧ g.left≠7 ∧ g.right≠7 ∧ g.left≠g.right
  change ¬ ∃ (gs : List BinaryGate) (g : BinaryGate) (inv : Bool),
    let reads := (gs++[g]).flatMap (fun h => [h.left,h.right])
    7≤gs.length ∧ gs.length≤9 ∧ (∀ i (h:i<gs.length), good (8+i) gs[i]) ∧ good (8+gs.length) g ∧
    8≤g.left ∧ 8≤g.right ∧
    (∀ i<gs.length, ∃ v∈(gs++[g]).drop (i+1), v.left=8+i ∨ v.right=8+i) ∧
    12≤gs.length+((Finset.range 7).filter fun t => reads.count t=1).card ∧
    (∀ v∈gs++[g], v.left<7 → v.right<7 → reads.count v.left≠1 ∨ reads.count v.right≠1) ∧
    ∀ x, ((BinaryCircuit.mk (gs++[g]) (8+gs.length)).eval (input x) != inv)=f x
  rintro ⟨gs,g,inv,low,high,wellFormed,hg,left,right,used,count,once,output⟩
  obtain ⟨⟨a,b,op⟩,gl,gr,_,_,different⟩ := hg
  let reads := gs.flatMap (fun (v : BinaryGate) => [v.left,v.right])
  have occurs (n : Nat) (hn : n<7) :
      ((gs++[g]).flatMap (fun v => [v.left,v.right])).count n = reads.count n := by
    have hl : g.left ≠ n := by omega
    have hr : g.right ≠ n := by omega
    simp [reads,List.flatMap_append,List.count_append,hl,hr]
  have filter_eq : ((Finset.range 7).filter (fun n => ((gs++[g]).flatMap
      (fun v => [v.left,v.right])).count n=1)) = ((Finset.range 7).filter (fun n => reads.count n=1)) := by
    apply Finset.filter_congr
    intro n hn
    rw [occurs n (Finset.mem_range.mp hn)]
  rw [filter_eq] at count
  have singles (v : BinaryGate) (hv : v∈gs) (l : v.left<7) (r : v.right<7) :
      reads.count v.left≠1 ∨ reads.count v.right≠1 := by
    have e := once v (List.mem_append_left _ hv) l r
    rwa [occurs _ l,occurs _ r] at e
  let top := 7+gs.length
  obtain ⟨j,lower,upper,orient,drain⟩ := terminal gs g (by omega) left right gl gr different used
  have last : g.left=top ∨ g.right=top := orient.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
  let w (x : Fin 7 → Bool) := (BinaryCircuit.mk gs 0).wires (input x)
  have len (x : Fin 7 → Bool) : (w x).length=8+gs.length := by
    have aux (l : List BinaryGate) (v : List Bool) :
        (l.foldl (fun z (e : BinaryGate) => z++[e.op (z.getD e.left false) (z.getD e.right false)]) v).length=v.length+l.length := by
      induction l generalizing v with
      | nil => simp
      | cons a l ih => rw [List.foldl_cons,ih];simp;omega
    change (gs.foldl (fun z e => z++[e.op (z.getD e.left false) (z.getD e.right false)]) (input x)).length=_
    rw [aux]; simp [input]
  have outcome (x : Fin 7 → Bool) :
      ((((w x).getD g.left false == a) && ((w x).getD g.right false == b)) != inv) = f x := by
    have h := output x
    change (((gs++[g]).foldl (fun z e => z++[e.op (z.getD e.left false) (z.getD e.right false)]) (input x)).getD (8+gs.length) false != inv)=f x at h
    rw [List.foldl_append] at h
    change (((w x ++ [g.op ((w x).getD g.left false) ((w x).getD g.right false)]).getD (8+gs.length) false) != inv)=f x at h
    rw [List.getD_append_right (w x) _ false (8+gs.length) (by rw [len x])] at h
    simpa only [len x,Nat.sub_self,List.getD_cons_zero,op] using h
  let trace (x : Fin 7 → Bool) := ((w x).getD top false,(w x).getD j false)
  let pair := if g.left=top then (a,b) else (b,a)
  have characterize (x : Fin 7 → Bool) : f x=(!inv) ↔ trace x=pair := by
    rw [← outcome]
    by_cases h : g.left=top
    · have r : g.right=j := by rcases orient with z|z <;> dsimp [top] at * <;> omega
      simp only [trace,pair,h,r,ite_true,Prod.mk.injEq]
      cases inv <;> simp
    · have r := last.resolve_left h
      have l : g.left=j := by rcases orient with z|z <;> tauto
      simp only [trace,pair,r,l]
      have ne : j ≠ top := by dsimp [top]; omega
      cases inv <;> simp [and_comm,ne]
  have anchor (b : Bool) : f (fun _ => b)=b := by cases b <;> decide
  have fixed (x : Fin 7 → Bool) (hx : f x=(!inv)) : trace x=trace (fun _ => !inv) :=
    ((characterize x).mp hx).trans ((characterize _).mp (anchor _)).symm
  have clash : ∃ x, f x=inv ∧ trace x=trace (fun _ => !inv) := by
    simpa only [Bool.not_not] using collision (!inv) gs low high wellFormed count singles j lower upper drain fixed
  obtain ⟨x,opposite,same⟩ := clash
  have both := (characterize x).mpr (same.trans ((characterize _).mp (anchor _)))
  rw [opposite] at both
  cases inv <;> contradiction
