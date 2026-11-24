import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3839_522
    (hCert : ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 x1.1 && x5 x1.2)) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x3.size)
    (hRest :
      let F (x : Fin 9 → Bool) : Bool :=
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
        (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
          (fun e => x e.1 && x e.2)
      let X (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
      ∀ (C : Circuit), FanInTwo C → C.size = 13 →
        ∀ (a b : Fin 10) (t : Bool), a < b → (t = true ∨ b = 9) →
          ∃ x : Fin 9 → Bool, C.eval (X x ++ [if t = true then
            (X x).getD a.val false || (X x).getD b.val false else
            (X x).getD a.val false && (X x).getD b.val false]) ≠ F x) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → ∀ (x6 x7 : Fin (10 : ℕ)) (x8 : Bool), x6 < x7 → ∃ (x10 : Fin (9 : ℕ) → Bool), x3.eval (x2 x10 ++ [if x8 = Bool.true then (x2 x10).getD (↑x6) Bool.false || (x2 x10).getD (↑x7) Bool.false else (x2 x10).getD (↑x6) Bool.false && (x2 x10).getD (↑x7) Bool.false]) ≠ x1 x10 := by
  have wires_relabel (f : Nat → Nat) (gs : List Gate) (W V : List Bool)
      (hlen : W.length = V.length) (hge : 11 ≤ W.length)
      (hf : ∀ i, 11 ≤ i → f i = i)
      (hf_lt : ∀ i, i < W.length → f i < V.length)
      (hagree : ∀ i, W.getD i false = V.getD (f i) false) :
      ∀ i, ((Circuit.mk gs 0).wires W).getD i false =
        ((Circuit.mk (gs.map fun g => ⟨g.op, g.inputs.map f⟩) 0).wires V).getD (f i) false := by
    induction gs generalizing W V with
    | nil => exact hagree
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map fun i => W.getD i false)
      have hv : g.op.eval ((g.inputs.map f).map fun i => V.getD i false) = v := by
        apply congrArg g.op.eval
        simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left (fun i _ => (hagree i).symm)
      change ∀ i, ((Circuit.mk gs 0).wires (W ++ [v])).getD i false =
        ((Circuit.mk (gs.map fun g => ⟨g.op, g.inputs.map f⟩) 0).wires (V ++ [_])).getD (f i) false
      rw [hv]
      apply ih (W ++ [v]) (V ++ [v]) (by simp [hlen]) (by simp; omega)
      · intro i hi
        by_cases h1 : i < W.length
        · exact Nat.lt_trans (hf_lt i h1) (by simp)
        · have hge11 : 11 ≤ i := by omega
          rw [hf i hge11]
          simp only [List.length_append, List.length_singleton] at hi ⊢
          omega
      · intro i
        by_cases h1 : i < W.length
        · have h2 : f i < V.length := hf_lt i h1
          rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
          exact hagree i
        · have hge11 : 11 ≤ i := by omega
          rw [hf i hge11, List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), hlen]

  have getD_ofFn9 (z : Fin 9 → Bool) (i : Fin 9) : (List.ofFn z).getD i.val false = z i := by
    rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]

  let swap (i : Nat) : Nat := if i = 9 then 10 else if i = 10 then 9 else i

  have swap_high (i : Nat) (hi : 11 ≤ i) : swap i = i := by
    simp [swap, show i ≠ 9 by omega, show i ≠ 10 by omega]

  have swap_agree (W : List Bool) (hW : W.length = 9) (u v : Bool) :
      ∀ i, (W ++ [u,v]).getD i false = (W ++ [v,u]).getD (swap i) false := by
    intro i
    by_cases hi : i < 9
    · have hs : swap i = i := by
        simp [swap, show i ≠ 9 by omega, show i ≠ 10 by omega]
      rw [hs, List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
    · by_cases h9 : i = 9
      · subst i
        change (W ++ [u,v]).getD 9 false = (W ++ [v,u]).getD 10 false
        rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
        simp [hW]
      · by_cases h10 : i = 10
        · subst i
          change (W ++ [u,v]).getD 10 false = (W ++ [v,u]).getD 9 false
          rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega)]
          simp [hW]
        · rw [swap_high i (by omega), List.getD_eq_default _ _ (by simp [hW]; omega),
            List.getD_eq_default _ _ (by simp [hW]; omega)]

  have wires_prefix (gs : List Gate) (W : List Bool) (i : Nat) (hi : i < W.length) :
      ((Circuit.mk gs 0).wires W).getD i false = W.getD i false := by
    induction gs generalizing W with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires
        (W ++ [g.op.eval (g.inputs.map fun j => W.getD j false)])).getD i false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

  let switched (C : Circuit) (op₀ op₁ : GateOp) (a b c d : Fin 9) : Circuit :=
    ⟨⟨op₁, [c.val,d.val]⟩ :: ⟨op₀, [a.val,b.val]⟩ ::
      C.gates.map (fun g => ⟨g.op, g.inputs.map swap⟩), swap C.output⟩

  have switched_fan (C : Circuit) (op₀ op₁ : GateOp) (a b c d : Fin 9)
      (hC : FanInTwo C)
      (h₀ : op₀ ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (h₁ : op₁ ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
      FanInTwo (switched C op₀ op₁ a b c d) := by
    intro g hg
    simp only [switched, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | rfl | ⟨g', hg', rfl⟩
    · exact ⟨h₁, by simp⟩
    · exact ⟨h₀, by simp⟩
    · exact ⟨(hC g' hg').1, by simpa using (hC g' hg').2⟩

  have switched_size (C : Circuit) (op₀ op₁ : GateOp) (a b c d : Fin 9) :
      (switched C op₀ op₁ a b c d).size = C.size + 2 := by
    change (switched C op₀ op₁ a b c d).gates.length = C.gates.length + 2
    simp only [switched, List.length_cons, List.length_map]

  have switched_first (C : Circuit) (op₀ op₁ : GateOp) (a b c d : Fin 9)
      (x : Fin 9 → Bool) :
      ((switched C op₀ op₁ a b c d).wires (List.ofFn x)).getD 9 false =
        op₁.eval [x c,x d] := by
    change ((Circuit.mk (⟨op₀,[a.val,b.val]⟩ ::
      C.gates.map (fun g => ⟨g.op,g.inputs.map swap⟩)) 0).wires
      (List.ofFn x ++ [op₁.eval ([c.val,d.val].map fun i =>
        (List.ofFn x).getD i false)])).getD 9 false = _
    simp only [List.map_cons, List.map_nil, getD_ofFn9]
    rw [wires_prefix _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp

  have switched_eval (C : Circuit) (op₀ op₁ : GateOp) (a b c d : Fin 9)
      (x : Fin 9 → Bool) :
      (switched C op₀ op₁ a b c d).eval (List.ofFn x) =
        C.eval (List.ofFn x ++ [op₀.eval [x a,x b], op₁.eval [x c,x d]]) := by
    have h₀ : op₁.eval ([c.val,d.val].map fun i => (List.ofFn x).getD i false) =
        op₁.eval [x c,x d] := by simp only [List.map_cons, List.map_nil, getD_ofFn9]
    have h₁ : op₀.eval ([a.val,b.val].map fun i =>
        (List.ofFn x ++ [op₁.eval [x c,x d]]).getD i false) = op₀.eval [x a,x b] := by
      simp only [List.map_cons, List.map_nil]
      rw [List.getD_append (List.ofFn x) _ false a.val
          (by simpa only [List.length_ofFn] using a.isLt),
        List.getD_append (List.ofFn x) _ false b.val
          (by simpa only [List.length_ofFn] using b.isLt), getD_ofFn9, getD_ofFn9]
    change ((Circuit.mk (C.gates.map fun g => ⟨g.op,g.inputs.map swap⟩) 0).wires
      ((List.ofFn x ++ [op₁.eval ([c.val,d.val].map fun i => (List.ofFn x).getD i false)]) ++
        [op₀.eval ([a.val,b.val].map fun i =>
          (List.ofFn x ++ [op₁.eval ([c.val,d.val].map fun i =>
            (List.ofFn x).getD i false)]).getD i false)] )).getD (swap C.output) false = _
    rw [h₀, h₁]
    simp only [List.append_assoc, List.singleton_append]
    symm
    exact wires_relabel swap C.gates _ _ (by simp) (by simp) swap_high
      (by intro i hi; simp only [swap]; split_ifs <;> simp_all)
      (swap_agree _ (by simp) _ _) C.output



  have wires_relabel9 (f : Nat → Nat) (gs : List Gate) (W V : List Bool)
      (hlen : W.length = V.length) (hge : 9 ≤ W.length)
      (hf : ∀ i, 9 ≤ i → f i = i)
      (hf_lt : ∀ i, i < W.length → f i < V.length)
      (hagree : ∀ i, W.getD i false = V.getD (f i) false) :
      ∀ i, ((Circuit.mk gs 0).wires W).getD i false =
        ((Circuit.mk (gs.map fun g => ⟨g.op, g.inputs.map f⟩) 0).wires V).getD (f i) false := by
    induction gs generalizing W V with
    | nil => exact hagree
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map fun i => W.getD i false)
      have hv : g.op.eval ((g.inputs.map f).map fun i => V.getD i false) = v := by
        apply congrArg g.op.eval
        simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left (fun i _ => (hagree i).symm)
      change ∀ i, ((Circuit.mk gs 0).wires (W ++ [v])).getD i false =
        ((Circuit.mk (gs.map fun g => ⟨g.op, g.inputs.map f⟩) 0).wires (V ++ [_])).getD (f i) false
      rw [hv]
      apply ih (W ++ [v]) (V ++ [v]) (by simp [hlen]) (by simp; omega)
      · intro i hi
        by_cases h1 : i < W.length
        · exact Nat.lt_trans (hf_lt i h1) (by simp)
        · have hge9 : 9 ≤ i := by omega
          rw [hf i hge9]
          simp only [List.length_append, List.length_singleton] at hi ⊢
          omega
      · intro i
        by_cases h1 : i < W.length
        · have h2 : f i < V.length := hf_lt i h1
          rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
          exact hagree i
        · have hge9 : 9 ≤ i := by omega
          rw [hf i hge9, List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), hlen]


  let relab (p : Fin 9 → Fin 9) (i : Nat) : Nat :=
    if h : i < 9 then (p ⟨i,h⟩).val else i

  let renamed (C : Circuit) (p : Fin 9 → Fin 9) : Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op,g.inputs.map (relab p)⟩), relab p C.output⟩

  have renamed_fan (C : Circuit) (p : Fin 9 → Fin 9) (hC : FanInTwo C) :
      FanInTwo (renamed C p) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(hC g' hg').1, by simpa using (hC g' hg').2⟩

  have renamed_size (C : Circuit) (p : Fin 9 → Fin 9) :
      (renamed C p).size = C.size := by
    change (C.gates.map _).length = C.gates.length
    exact List.length_map _

  have renamed_wires (C : Circuit) (p : Fin 9 → Fin 9) (x : Fin 9 → Bool) :
      ∀ i, (C.wires (List.ofFn (x ∘ p))).getD i false =
        ((renamed C p).wires (List.ofFn x)).getD (relab p i) false := by
    apply wires_relabel9 (relab p) C.gates _ _ (by simp) (by simp)
    · intro i hi
      simp [relab, show ¬i < 9 by omega]
    · intro i hi
      have hi' : i < 9 := by simpa only [List.length_ofFn] using hi
      simpa only [relab, dite_eq_left hi', List.length_ofFn] using (p ⟨i,hi'⟩).isLt
    · intro i
      by_cases hi : i < 9
      · rw [show relab p i = (p ⟨i,hi⟩).val by simp [relab, hi]]
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (p ⟨i,hi⟩).isLt),
          List.getElem_ofFn, List.getElem_ofFn]
        rfl
      · rw [show relab p i = i by simp [relab, hi],
          List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]

  have renamed_eval (C : Circuit) (p : Fin 9 → Fin 9) (x : Fin 9 → Bool) :
      (renamed C p).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ p)) := by
    exact (renamed_wires C p x C.output).symm

  have renamed_first (C : Circuit) (p : Fin 9 → Fin 9)
      (f : (Fin 9 → Bool) → Bool)
      (hfirst : ∀ x, (C.wires (List.ofFn x)).getD 9 false = f x) :
      ∀ x, ((renamed C p).wires (List.ofFn x)).getD 9 false = f (x ∘ p) := by
    intro x
    have h := renamed_wires C p x 9
    rw [show relab p 9 = 9 by simp [relab], hfirst] at h
    exact h.symm



  let F (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

  let aut : Fin 12 → Fin 9 → Fin 9 := ![
  ![0,1,2,3,4,5,6,7,8],
  ![3,8,5,0,4,2,6,7,1],
  ![0,5,8,3,4,1,7,6,2],
  ![3,2,1,0,4,8,7,6,5],
  ![1,0,5,8,6,2,4,7,3],
  ![8,3,2,1,6,5,4,7,0],
  ![1,2,3,8,6,0,7,4,5],
  ![8,5,0,1,6,3,7,4,2],
  ![2,3,8,5,7,1,4,6,0],
  ![5,0,1,2,7,8,4,6,3],
  ![2,1,0,5,7,3,6,4,8],
  ![5,8,3,2,7,0,6,4,1]]
  let reps : List (Fin 9 × Fin 9) := [(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)]

  have aut_preserves : ∀ j x, F (x ∘ aut j) = F x := by decide +kernel

  have route : ∀ a b : Fin 9, a < b → ∃ j : Fin 12, ∃ q ∈ reps,
      (aut j a = q.1 ∧ aut j b = q.2) ∨ (aut j a = q.2 ∧ aut j b = q.1) := by
    decide +kernel

  have eval_and (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by
    change [a,b].all id = (a && b)
    cases a <;> cases b <;> rfl
  have eval_or (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
    change [a,b].any id = (a || b)
    cases a <;> cases b <;> rfl

  have raw_and_case
      (hCert : ∀ q ∈ reps, ∀ D : Circuit, FanInTwo D →
        (∀ x, (D.wires (List.ofFn x)).getD 9 false = (x q.1 && x q.2)) →
        circuitFun 9 D = F → 16 ≤ D.size)
      (C : Circuit) (hC : FanInTwo C) (hsize : C.size = 13)
      (a b : Fin 9) (hab : a < b) :
      ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 6, x a && x b]) ≠ F x := by
    by_contra hn
    have he : ∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 6, x a && x b]) = F x := by
      intro x
      by_contra hne
      exact hn ⟨x,hne⟩
    obtain ⟨j,q,hq,hmap⟩ := route a b hab
    let D₀ := switched C .or .and 0 6 a b
    let D := renamed D₀ (aut j)
    have hfan : FanInTwo D := renamed_fan D₀ (aut j)
      (switched_fan C .or .and 0 6 a b hC (by simp) (by simp))
    have hs : D.size = 15 := by
      dsimp [D,D₀]
      rw [renamed_size, switched_size, hsize]
    have hfirst₀ : ∀ x, (D₀.wires (List.ofFn x)).getD 9 false = (x a && x b) := by
      intro x
      simpa only [D₀, eval_and] using switched_first C .or .and 0 6 a b x
    have hfirst : ∀ x, (D.wires (List.ofFn x)).getD 9 false = (x q.1 && x q.2) := by
      intro x
      have hh := renamed_first D₀ (aut j) (fun x => x a && x b) hfirst₀ x
      change (D.wires (List.ofFn x)).getD 9 false = (x (aut j a) && x (aut j b)) at hh
      rw [hh]
      rcases hmap with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · rw [h₁,h₂]
      · rw [h₁,h₂,Bool.and_comm]
    have hfun : circuitFun 9 D = F := by
      funext x
      change (renamed (switched C .or .and 0 6 a b) (aut j)).eval (List.ofFn x) = F x
      rw [renamed_eval, switched_eval]
      rw [eval_or, eval_and]
      exact (he (x ∘ aut j)).trans (aut_preserves j x)
    have hlo := hCert q hq D hfan hfirst hfun
    omega


  have lift_raw_pair (C : Circuit)
      (h : ∀ a b : Fin 9, a < b → ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 6, x a && x b]) ≠ F x)
      (a b : Fin 10) (hab : a < b) (hb : b.val < 9) :
      ∃ x : Fin 9 → Bool,
        C.eval ((List.ofFn x ++ [x 0 || x 6]) ++
          [(List.ofFn x ++ [x 0 || x 6]).getD a.val false &&
           (List.ofFn x ++ [x 0 || x 6]).getD b.val false]) ≠ F x := by
    let a' : Fin 9 := ⟨a.val, by have := hab; change a.val < b.val at this; omega⟩
    let b' : Fin 9 := ⟨b.val,hb⟩
    obtain ⟨x,hx⟩ := h a' b' hab
    refine ⟨x,?_⟩
    have hga : (List.ofFn x ++ [x 0 || x 6]).getD a.val false = x a' := by
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using a'.isLt)]
      exact getD_ofFn9 x a'
    have hgb : (List.ofFn x ++ [x 0 || x 6]).getD b.val false = x b' := by
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using b'.isLt)]
      exact getD_ofFn9 x b'
    simpa only [hga,hgb,List.append_assoc,List.singleton_append] using hx

  have raw_and_child
      (hCert : ∀ q ∈ reps, ∀ D : Circuit, FanInTwo D →
        (∀ x, (D.wires (List.ofFn x)).getD 9 false = (x q.1 && x q.2)) →
        circuitFun 9 D = F → 16 ≤ D.size) :
      let G (x : Fin 9 → Bool) : Bool :=
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
          (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
            (fun e => x e.1 && x e.2)
      ∀ (C : Circuit), FanInTwo C → C.size = 13 → ∀ a b : Fin 9, a < b →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6, x a && x b]) ≠ G x := by
    dsimp only
    intro C hC hs a b hab
    simpa only [F, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using
      raw_and_case hCert C hC hs a b hab

  have hRaw := raw_and_child hCert

  dsimp only at hRaw hRest ⊢
  intro C hC hs a b t hab
  by_cases ht : t = true
  · simpa only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using
      hRest C hC hs a b t hab (Or.inl ht)
  by_cases hb : b = 9
  · simpa only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using
      hRest C hC hs a b t hab (Or.inr hb)
  have hb9 : b.val < 9 := by
    have : b.val ≠ 9 := fun h => hb (Fin.ext h)
    omega
  let a' : Fin 9 := ⟨a.val, by have := hab; change a.val < b.val at this; omega⟩
  let b' : Fin 9 := ⟨b.val,hb9⟩
  obtain ⟨x,hx⟩ := hRaw C hC hs a' b' hab
  refine ⟨x,?_⟩
  have hga : (List.ofFn x ++ [x 0 || x 6]).getD a.val false = x a' := by
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using a'.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using a'.isLt), List.getElem_ofFn]
  have hgb : (List.ofFn x ++ [x 0 || x 6]).getD b.val false = x b' := by
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using b'.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using b'.isLt), List.getElem_ofFn]
  rw [ite_eq_right ht,hga,hgb]
  simpa only [List.append_assoc, List.singleton_append,
    List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using hx
