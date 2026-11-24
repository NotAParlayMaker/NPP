import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Mask both copies of the distinguished input except at the unique reader.
-- Its output must distinguish the two cofactors at every pivotal assignment.
theorem PEqualNP.Outside.R_meta_2309_601
    (splice : ∀ (gs : List Gate), gs ≠ [] → (gs.filter (fun g => [0,9].any fun j => g.inputs.contains j)).length ≤ 1 →
      ∃ (p : List Gate) (g : Gate) (s : List Gate), gs = p ++ g :: s ∧
      ∀ (a b : List Bool) (o : ℕ), 9 < a.length → (a.length = b.length ∧ ∀ i : ℕ, i ≠ 0 → i ≠ 9 → a.getD i false = b.getD i false) → o ≠ 0 → o ≠ 9 →
      (Circuit.mk gs o).eval a = (let w := (Circuit.mk p 0).wires b; (Circuit.mk s o).eval (w ++ [g.op.eval (g.inputs.map fun i => if i = 0 ∨ i = 9 then a.getD i false else w.getD i false)])))
    (exclude : ∀ (p : List Gate) (g : Gate) (s : List Gate) (o : ℕ), p.length + s.length ≤ 13 → FanInTwo ⟨p ++ g :: s,o⟩ →
      let bank := fun (r : ℕ) => (Circuit.mk p 0).wires (List.ofFn (fun i : Fin 9 => (2*r).testBit i.val) ++ [false])
      let sel := fun (r : ℕ) (b : Bool) => g.op.eval (g.inputs.map fun i => if i = 0 then b else if i = 9 then !b else (bank r).getD i false)
      let f := Nat.testBit 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
      (∀ r < 256, f (2*r) ≠ f (2*r+1) → sel r false ≠ sel r true) →
      ∃ r < 256, ∃ b : Bool, (Circuit.mk s o).eval (bank r ++ [sel r b]) ≠ f (2*r+b.toNat)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 ≤ (1 : ℕ) → False := by
  dsimp only
  intro C fan first computes small few
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let norm := fun (g : Gate) => Gate.mk g.op (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs)
  let F := fun (x : Fin 9 → Bool) => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let seed := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!(x 0)]
  have extends' (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w ++ t := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih => obtain ⟨t,h⟩ := ih (step w g); exact ⟨_,by simpa [step,List.append_assoc] using h⟩
  have fn := fun x => congrFun computes x
  cases C with | mk gs o =>
  cases gs with
  | nil => exact Bool.noConfusion (show false = true from first (fun _ => false))
  | cons a tl =>
    have fanT (g : Gate) (hg : g ∈ tl) := fan g (.tail a hg)
    have normStep (g : Gate) (hg : g ∈ tl) (w : List Bool) : step w (norm g) = step w g := by
      obtain ⟨hop,_⟩ := fanT g hg
      change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
      obtain ⟨op,ins⟩ := g
      change op = .and ∨ op = .or ∨ op = .not at hop
      rcases hop with rfl|rfl|rfl <;> cases ins <;> rfl
    have foldEq (l : List Gate) (hl : ∀ g ∈ l, g ∈ tl) (w : List Bool) : (l.map norm).foldl step w = l.foldl step w := by
      induction l generalizing w with
      | nil => rfl
      | cons g l ih => simp only [List.map_cons,List.foldl_cons,normStep g (hl _ (.head _))]; exact ih (fun v hv => hl v (.tail _ hv)) _
    have seeded (x : Fin 9 → Bool) : step (List.ofFn x) a = seed x := by
      obtain ⟨v,hv⟩ := extends' tl (step (List.ofFn x) a)
      have h := first x
      change (tl.foldl step (step (List.ofFn x) a)).getD 9 false = _ at h
      rw [hv,List.getD_append _ _ _ _ (by simp [step]), List.getD_append_right _ _ _ _ (by simp)] at h
      simpa [step,seed] using congrArg (fun b : Bool => List.ofFn x ++ [b]) (by simpa using h : a.op.eval (a.inputs.map fun i => (List.ofFn x).getD i false) = !(x 0))
    have semantic (x : Fin 9 → Bool) : ((tl.map norm).foldl step (seed x)).getD o false = F x := by
      rw [foldEq _ (fun _ h => h),← seeded]; exact fn x
    have ho (j : ℕ) (hj : j = 0 ∨ j = 9) : o ≠ j := by
      rintro rfl
      rcases hj with rfl|rfl
      · let x : Fin 9 → Bool := fun i => i == 0
        obtain ⟨t,ht⟩ := extends' (tl.map norm) (seed x)
        have h := semantic x
        rw [ht,List.getD_append _ _ _ _ (by simp [seed])] at h
        exact Bool.noConfusion (show true = false from h)
      · let x : Fin 9 → Bool := fun _ => false
        obtain ⟨t,ht⟩ := extends' (tl.map norm) (seed x)
        have h := semantic x
        rw [ht,List.getD_append _ _ _ _ (by simp [seed])] at h
        exact Bool.noConfusion (show true = false from h)
    have nonempty : tl.map norm ≠ [] := by
      intro nil
      let x : Fin 9 → Bool := fun i => i == 1 || i == 2
      have hx := semantic x
      rw [nil,List.foldl_nil] at hx
      have hy := semantic (fun i => i == 1)
      rw [nil,List.foldl_nil] at hy
      have hz := semantic (fun i => i == 2)
      rw [nil,List.foldl_nil] at hz
      change (seed x).getD o false = true at hx
      change (seed _).getD o false = false at hy hz
      have chk : ∀ j : Fin 10, (seed x).getD j false = true → (seed (fun i => i == 1)).getD j false = true ∨ (seed (fun i => i == 2)).getD j false = true := by decide +kernel
      by_cases ol : o < 10
      · rcases chk ⟨o,ol⟩ hx with h|h <;> simp_all
      · rw [List.getD_eq_default _ _ (by simpa [seed] using Nat.le_of_not_gt ol)] at hx; contradiction
    obtain ⟨p,g,s,split,transfer⟩ := splice (tl.map norm) nonempty few
    have len := congrArg List.length split
    change (a::tl).length ≤ 15 at small
    simp only [List.length_cons,List.length_map,List.length_append] at small len
    have legal : FanInTwo ⟨p++g::s,o⟩ := by
      intro v hv
      change v ∈ p++g::s at hv
      rw [← split] at hv
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      obtain ⟨hop,hlen⟩ := fanT _ hu
      refine ⟨hop,?_⟩
      change (if u.op.eval [false] = true then u.inputs.take 1 else u.inputs).length ≤ 2
      split
      · simp
      · exact hlen
    let row := fun (r : ℕ) (b : Bool) (i : Fin 9) => if i = 0 then b else (2*r).testBit i.val
    let base := fun (r : ℕ) => List.ofFn (fun i : Fin 9 => (2*r).testBit i.val) ++ [false]
    let bank := fun r => (Circuit.mk p 0).wires (base r)
    let sel := fun (r : ℕ) (b : Bool) => g.op.eval (g.inputs.map fun i => if i = 0 then b else if i = 9 then !b else (bank r).getD i false)
    have runOK (r : ℕ) (b : Bool) : (Circuit.mk s o).eval (bank r ++ [sel r b]) = F (row r b) := by
      let a' := seed (row r b)
      have ha : a'.length = 10 := by simp [a',seed]
      have hv := transfer a' (base r) o (by omega) ⟨by simp [ha,base],by
        intro i h0 h9
        by_cases hi : i < 9
        · interval_cases i <;> first | contradiction | rfl
        · have ge : 10 ≤ i := by omega
          rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simpa [base] using ge)]⟩ (ho _ (.inl rfl)) (ho _ (.inr rfl))
      have hs := semantic (row r b)
      change (Circuit.mk (tl.map norm) o).eval a' = _ at hs
      rw [hv] at hs
      have eqv : sel r b = g.op.eval (g.inputs.map fun i => if i = 0 ∨ i = 9 then a'.getD i false else (bank r).getD i false) := by
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i _
        by_cases h0 : i=0
        · subst i; rfl
        by_cases h9 : i=9
        · subst i; rfl
        simp only [h0,h9,false_or,ite_false]
      rw [eqv]; exact hs
    have table : ∀ (r : Fin 256) (b : Bool), F (row r.val b) = (0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : ℕ).testBit (2*r.val+b.toNat) := by decide +kernel
    have correct (r : ℕ) (hr : r < 256) (b : Bool) := (runOK r b).trans (table ⟨r,hr⟩ b)
    apply False.elim
    obtain ⟨r,hr,b,hbad⟩ := exclude p g s o (by omega) legal (by
      intro r hr different eqsel
      have h := (correct r hr false).symm.trans ((congrArg (fun v => (Circuit.mk s o).eval (bank r ++ [v])) eqsel).trans (correct r hr true))
      exact different (by simpa using h))
    exact hbad (correct r hr b)
