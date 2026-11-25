import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2590_371
    (small : ∀ (p : List (List Nat × List Nat)) (out : List Nat), p.length ≤ 4 →
      ∃ x : Fin 10 → Bool,
        let ws := p.foldl (fun (ws : List Bool) a => ws ++
          [a.1.any (fun i => ws.getD i false) && a.2.any (fun i => ws.getD i false)])
          (List.ofFn x ++ [true])
        out.any (fun i => ws.getD i false) ≠ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
    (five : ∀ C : Circuit, Monotone2 C → (C.gates.countP fun g => !(g.op.eval [false, true])) = 5 → (C.gates.countP fun g => g.op.eval [false, true]) ≤ 14 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
    (many : ∀ C : Circuit, Monotone2 C → 6 ≤ (C.gates.countP fun g => !(g.op.eval [false, true])) → (C.gates.countP fun g => g.op.eval [false, true]) ≤ 19 - (C.gates.countP fun g => !(g.op.eval [false, true])) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C mono budget computes
  let pa : Gate → Bool := fun g => !(g.op.eval [false, true])
  let po : Gate → Bool := fun g => g.op.eval [false, true]
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have paAnd (g : Gate) (h : g.op = GateOp.and) : pa g = true := by
    simpa only [pa,h] using (show Bool.not (GateOp.and.eval [false,true]) = true from rfl)
  have paOr (g : Gate) (h : g.op = GateOp.or) : pa g = false := by
    simpa only [pa,h] using (show Bool.not (GateOp.or.eval [false,true]) = false from rfl)
  have poAnd (g : Gate) (h : g.op = GateOp.and) : po g = false := by
    simpa only [po,h] using (show GateOp.and.eval [false,true] = false from rfl)
  have poOr (g : Gate) (h : g.op = GateOp.or) : po g = true := by
    simpa only [po,h] using (show GateOp.or.eval [false,true] = true from rfl)
  have ops (g : Gate) (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
      g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using h
  have partition : ∀ gs : List Gate, (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
      gs.countP pa + gs.countP po = gs.length := by
    intro gs good
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have hh := ih (fun h hg => good h (List.mem_cons_of_mem _ hg))
      rcases ops g (good g (by simp)) with hop | hop
      · have ha := paAnd g hop
        have ho := poAnd g hop
        simp only [List.countP_cons, List.length_cons, ha, ho, Bool.false_eq_true, ite_false, ite_true]
        omega
      · have ha := paOr g hop
        have ho := poOr g hop
        simp only [List.countP_cons, List.length_cons, ha, ho, Bool.false_eq_true, ite_false, ite_true]
        omega
  have hpart := partition C.gates (fun g hg => (mono g hg).1)
  change C.gates.length ≤ 19 at budget
  let read : List Bool → List Nat → Bool := fun ws s => s.any fun i => ws.getD i false
  let step : List Bool → (List Nat × List Nat) → List Bool :=
    fun ws a => ws ++ [read ws a.1 && read ws a.2]
  let gateStep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run (p : List (List Nat × List Nat)) (x : Fin 10 → Bool) :=
    p.foldl step (List.ofFn x ++ [true])
  have allLen : ∀ (p : List (List Nat × List Nat)) (ws : List Bool),
      (p.foldl step ws).length = ws.length + p.length := by
    intro p
    induction p with
    | nil => intro ws; simp
    | cons a p ih =>
      intro ws
      simp [List.foldl_cons, ih, step]
      omega
  have len (p : List (List Nat × List Nat)) (x : Fin 10 → Bool) :
      (run p x).length = 11 + p.length := by
    simp [run, allLen]
  have oldRead : ∀ (p : List (List Nat × List Nat)) (ws : List Bool) (i : Nat),
      i < ws.length → (p.foldl step ws).getD i false = ws.getD i false := by
    intro p
    induction p with
    | nil => intro ws i hi; rfl
    | cons a p ih =>
      intro ws i hi
      rw [List.foldl_cons, ih (step ws a) i (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have trueWire (p : List (List Nat × List Nat)) (x : Fin 10 → Bool) :
      read (run p x) [10] = true := by
    change ((p.foldl step (List.ofFn x ++ [true])).getD 10 false || false) = true
    rw [oldRead p _ 10 (by simp)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp : (List.ofFn x).length ≤ 10),
      List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero]
    rfl
  have getAlias (as : List (List Nat)) (ws : List Bool) (i : Nat) :
      (as.map (read ws)).getD i false = read ws (as.getD i []) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases as[i]? <;> simp [read]
  have optionAlias (as : List (List Nat)) (ws : List Bool) (i : Nat) :
      (as[i]?.map (read ws)).getD false = read ws (as[i]?.getD []) := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_map] using getAlias as ws i
  have compress : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∃ (p : List (List Nat × List Nat)) (aliases : List (List Nat)), p.length = gs.countP pa ∧
        (∀ a ∈ aliases, ∀ i ∈ a, i < 11 + p.length) ∧
        ∀ x : Fin 10 → Bool, gs.foldl gateStep (List.ofFn x) = aliases.map (read (run p x)) := by
    intro gs good
    induction gs using List.reverseRecOn with
    | nil =>
      refine ⟨[], (List.finRange 10).map fun i => [i.val], rfl, ?_, ?_⟩
      · rintro _ ha i hi
        simp only [List.mem_map] at ha
        obtain ⟨j, _, rfl⟩ := ha
        simp only [List.mem_singleton] at hi
        subst i
        exact j.isLt.trans (by decide)
      · intro x
        simp only [List.foldl_nil, List.map_map]
        apply List.ext_getElem
        · simp
        · intro i hi hj
          have hi10 : i < 10 := by simpa using hi
          simp only [List.getElem_ofFn, List.getElem_map, List.getElem_finRange, Function.comp_def,
            run, List.foldl_nil, read, List.any_cons, List.any_nil, Bool.or_false]
          have same : (List.ofFn x ++ [true]).getD i false = x ⟨i,hi10⟩ := by
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hi]
            simp only [List.getElem_ofFn]
          exact same.symm
    | append_singleton gs g ih =>
      have hg := good g (by simp)
      obtain ⟨p, as, count, indices, eval⟩ := ih (fun h hh => good h (by simp [hh]))
      have getIn (j : Nat) : ∀ i ∈ as.getD j [], i < 11 + p.length := by
        rw [List.getD_eq_getElem?_getD]
        cases h : as[j]? with
        | none => simp
        | some a => exact indices a (List.mem_of_getElem? h)
      rcases ops g hg.1 with hor | hor
      · let packets := (g.inputs.map (fun i => as.getD i [])) ++ [[10],[10]]
        let a := packets.getD 0 []
        let b := packets.getD 1 []
        let q := p ++ [(a,b)]
        refine ⟨q, as ++ [[11+p.length]], ?_, ?_, ?_⟩
        · simp [q, count, paAnd g hor]
        · intro s hs i hi
          simp only [List.mem_append, List.mem_singleton] at hs
          rcases hs with h | rfl
          · have hi' := indices s h i hi
            simp [q]
            omega
          · simp only [List.mem_singleton] at hi
            subst i
            simp [q]
        · intro x
          have wr : run q x = run p x ++ [read (run p x) a && read (run p x) b] := by
            simp [run, q, step]
          have unchanged : as.map (read (run q x)) = as.map (read (run p x)) := by
            apply List.map_congr_left
            intro t ht
            unfold read
            have each (i : Nat) (hi : i ∈ t) :
                (run q x).getD i false = (run p x).getD i false := by
              have before : i < (run p x).length := by rw [len]; exact indices t ht i hi
              rw [wr, List.getD_eq_getElem?_getD, List.getElem?_append_left before,
                  ← List.getD_eq_getElem?_getD]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true]
            constructor
            · rintro ⟨i, hi, hv⟩
              exact ⟨i, hi, by rw [← each i hi]; exact hv⟩
            · rintro ⟨i, hi, hv⟩
              exact ⟨i, hi, by rw [each i hi]; exact hv⟩
          rw [List.foldl_append, eval x, List.foldl_cons, List.foldl_nil, List.map_append, unchanged]
          simp only [gateStep, List.map_cons, List.map_nil, List.append_cancel_left_eq, List.cons.injEq, and_true]
          have atLast : read (run q x) [11+p.length] = (read (run p x) a && read (run p x) b) := by
            simp only [read, List.any_cons, List.any_nil, Bool.or_false] at wr ⊢
            rw [wr, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [len]), len, Nat.sub_self]
            rfl
          rw [atLast, hor, evalAnd]
          have hl := hg.2
          cases h : g.inputs with
          | nil => simp [a, b, packets, h, trueWire]
          | cons i t =>
            cases t with
            | nil => simp [a, b, packets, h, trueWire, optionAlias]
            | cons j t =>
              cases t with
              | nil => simp [a, b, packets, h, optionAlias]
              | cons k t => simp [h] at hl
      · let a := g.inputs.flatMap fun i => as.getD i []
        refine ⟨p, as ++ [a], ?_, ?_, ?_⟩
        · simp [count, paOr g hor]
        · intro s hs j hj
          simp only [List.mem_append, List.mem_singleton] at hs
          rcases hs with h | rfl
          · exact indices s h j hj
          · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hj
            exact getIn i j hi
        · intro x
          rw [List.foldl_append, eval x, List.foldl_cons, List.foldl_nil, List.map_append]
          simp [gateStep, hor, evalOr, a, read, List.any_flatMap, List.any_map]
          apply List.any_congr rfl
          intro i
          simpa only [read, List.getD_eq_getElem?_getD] using optionAlias as (run p x) i
  let edges : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  have correct (x : Fin 10 → Bool) : C.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2) := by
    simpa [edges, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using computes x
  by_cases hlow : C.gates.countP pa ≤ 4
  · obtain ⟨p, as, hc, _, hw⟩ := compress C.gates mono
    obtain ⟨x, hx⟩ := small p (as.getD C.output []) (by rw [hc]; exact hlow)
    apply hx
    change read (run p x) (as.getD C.output []) = edges.any (fun e => x e.1 && x e.2)
    rw [← getAlias, ← hw x]
    exact correct x
  · by_cases hfive : C.gates.countP pa = 5
    · obtain ⟨x, hx⟩ := five C mono hfive (by change C.gates.countP po ≤ 14; omega)
      exact hx (correct x)
    · obtain ⟨x, hx⟩ := many C mono
        (by change 6 ≤ C.gates.countP pa; omega)
        (by change C.gates.countP po ≤ 19 - C.gates.countP pa; omega)
      exact hx (correct x)
