import PEqualNP.Defs

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 5000 in
theorem PEqualNP.Outside.R_meta_3869_1
    (hLow : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4) = x1 x4) → (15 : ℕ) ≤ x2.size ∧ (13 : ℕ) ≤ (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false, Bool.false]) x2.gates).length)
    (hRemaining : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (k : Fin 12),
      gs.length = 13 →
      PEqualNP.MetaComplexity.FanInTwo ⟨gs,0⟩ →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      (∀ v ∈ ([0,3] : List Nat),
        let n := gs.countP (fun g =>
          g.op.eval [false] && g.inputs.head? == some v ||
            !g.op.eval [false] && g.inputs.contains v)
        1 ≤ n ∧ n ≤ 2) →
      ∃ x : Fin 9 → Bool,
        let w := (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires
          (List.ofFn x ++ [x 0 || x 3])
        (w.getD 22 false || w.getD (10+k.val) false) ≠
          ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
            (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
  ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             (∀ x9 ∈ [(0 : ℕ), (3 : ℕ)],                 have x11 : ℕ := List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false] && x11.inputs.head? == Option.some x9 || !x11.op.eval [Bool.false] && x11.inputs.contains x9) (x1 ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate }]);                 (1 : ℕ) ≤ x11 ∧ x11 ≤ (2 : ℕ)) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false || x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  classical
  have eval_or1 (u : Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval [u] = u := by
    cases u <;> rfl
  have eval_or2 (u v : Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval [u,v] = (u || v) := by
    cases u <;> cases v <;> rfl
  let f (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let wf (ss : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    ss.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  let start (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
  have f_eq (x : Fin 9 → Bool) : f x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) := by
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  have lower14 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 f 14 := by
    rintro ⟨C, fan, small, correct⟩
    have large : 15 ≤ C.size := (hLow C fan correct).1
    omega
  have wf_append (A B : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      wf (A ++ B) w = wf B (wf A w) := by
    simp [wf, List.foldl_append]
  have wf_length (A : List PEqualNP.CircuitLowerBounds.Gate) :
      ∀ w : List Bool, (wf A w).length = w.length + A.length := by
    induction A with
    | nil => intro w; rfl
    | cons g A ih =>
      intro w
      show (wf A (w ++ [_])).length = _
      rw [ih]; simp; omega
  have wf_prefix (A : List PEqualNP.CircuitLowerBounds.Gate) :
      ∀ (w : List Bool) (i : Nat), i < w.length →
        (wf A w).getD i false = w.getD i false := by
    induction A with
    | nil => intro w i _; rfl
    | cons g A ih =>
      intro w i hi
      show (wf A (w ++ [_])).getD i false = _
      rw [ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]
  have wf_gate (A : List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) (B : List PEqualNP.CircuitLowerBounds.Gate)
      (w : List Bool) :
      (wf (A ++ g :: B) w).getD (w.length + A.length) false =
        g.op.eval (g.inputs.map fun i => (wf A w).getD i false) := by
    rw [wf_append]
    show (wf B (wf A w ++ [_])).getD _ false = _
    rw [← wf_length A w, wf_prefix _ _ _ (by simp)]
    simp
  have start_length (x : Fin 9 → Bool) : (start x).length = 10 := by simp [start]
  have start_lt (x : Fin 9 → Bool) (j : Fin 9) : (start x).getD j.val false = x j := by
    fin_cases j <;> rfl
  have wf_first (ss : List PEqualNP.CircuitLowerBounds.Gate) (x : Fin 9 → Bool) :
      wf (⟨.or,[0,3]⟩ :: ss) (List.ofFn x) = wf ss (start x) := by
    show wf ss (List.ofFn x ++ [_]) = wf ss (List.ofFn x ++ [_])
    congr 3
    have h0 : (List.ofFn x).getD 0 false = x 0 := rfl
    have h3 : (List.ofFn x).getD 3 false = x 3 := rfl
    simp only [List.map_cons, List.map_nil, eval_or2, h0, h3]
  have noA (ss : List PEqualNP.CircuitLowerBounds.Gate)
      (hf : PEqualNP.MetaComplexity.FanInTwo ⟨ss,0⟩)
      (hl : ss.length ≤ 13) (o : Nat) :
      ¬ ∀ x : Fin 9 → Bool, (wf ss (start x)).getD o false = f x := by
    intro correct
    apply lower14
    refine ⟨⟨⟨.or,[0,3]⟩ :: ss,o⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact hf g hg
    · change ss.length + 1 ≤ 14
      omega
    · intro x
      change (wf (⟨.or,[0,3]⟩ :: ss) (List.ofFn x)).getD o false = f x
      rw [wf_first]
      exact correct x
  have noB (ss : List PEqualNP.CircuitLowerBounds.Gate)
      (hf : PEqualNP.MetaComplexity.FanInTwo ⟨ss,0⟩)
      (hl : ss.length ≤ 12) (a b : Nat) :
      ¬ ∀ x : Fin 9 → Bool,
        ((wf ss (start x)).getD a false || (wf ss (start x)).getD b false) = f x := by
    intro correct
    refine noA (ss ++ [⟨.or,[a,b]⟩]) ?_ (by simp; omega) (10+ss.length) ?_
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hf g hg
      · rw [List.mem_singleton.mp hg]
        exact ⟨by simp, by simp⟩
    · intro x
      have hg := wf_gate ss ⟨.or,[a,b]⟩ [] (start x)
      rw [← correct x]
      simpa [start_length, eval_or2] using hg
  intro gs a b hlen hfan hnot ha hb hread
  by_contra absent
  have correct (x : Fin 9 → Bool) :
      ((wf gs (start x)).getD a false || (wf gs (start x)).getD b false) = f x := by
    apply Eq.trans ?_ (f_eq x).symm
    apply Classical.byContradiction
    intro differs
    exact absent ⟨x,differs⟩
  have place (q : Nat)
      (h : ∀ x : Fin 9 → Bool,
        ((wf gs (start x)).getD 22 false || (wf gs (start x)).getD q false) = f x) :
      10 ≤ q ∧ q < 22 := by
    constructor
    · by_contra hq
      have hpre (x : Fin 9 → Bool) : (wf gs (start x)).getD q false = (start x).getD q false :=
        wf_prefix gs (start x) q (by rw [start_length]; omega)
      by_cases h9 : q = 9
      · subst q
        let x : Fin 9 → Bool := fun i => decide (i = 0)
        have hx := h x
        rw [hpre] at hx
        have ht : (start x).getD 9 false = true := rfl
        have hf : f x = false := by decide +kernel
        rw [ht, Bool.or_true, hf] at hx
        cases hx
      · let j : Fin 9 := ⟨q,by omega⟩
        let x : Fin 9 → Bool := fun i => decide (i = j)
        have hx := h x
        rw [hpre] at hx
        have ht : (start x).getD q false = true := by
          change (start x).getD j.val false = true
          rw [start_lt]
          simp [x]
        have hf : f x = false :=
          (by decide +kernel : ∀ j : Fin 9, f (fun i => decide (i=j)) = false) j
        rw [ht, Bool.or_true, hf] at hx
        cases hx
    · by_contra hq
      by_cases he : q = 22
      · subst q
        apply noA gs hfan (by omega) 22
        intro x
        simpa only [Bool.or_self] using h x
      · apply noA gs hfan (by omega) 22
        intro x
        have hx := h x
        rw [List.getD_eq_default (n:=q) _ _
          (by rw [wf_length, start_length, hlen]; omega), Bool.or_false] at hx
        exact hx
  have shape : (a=22 ∧ 10≤b ∧ b<22) ∨ (b=22 ∧ 10≤a ∧ a<22) := by
    by_cases hae : a=22
    · exact Or.inl ⟨hae,place b (by simpa only [hae] using correct)⟩
    · by_cases hbe : b=22
      · apply Or.inr
        refine ⟨hbe,place a ?_⟩
        intro x
        rw [Bool.or_comm]
        simpa only [hbe] using correct x
      · exfalso
        obtain ⟨A,g,he⟩ : ∃ (A : List PEqualNP.CircuitLowerBounds.Gate)
            (g : PEqualNP.CircuitLowerBounds.Gate), gs=A++[g] :=
          ⟨gs.dropLast,gs.getLast (by intro h; simp [h] at hlen),
            (List.dropLast_append_getLast _).symm⟩
        have hA : A.length=12 := by rw [he] at hlen; simp only [List.length_append, List.length_singleton] at hlen; omega
        have hw (x : Fin 9 → Bool) (i : Nat) (hi : i ≠ 22) :
            (wf gs (start x)).getD i false = (wf A (start x)).getD i false := by
          have hwlen : (wf A (start x)).length=22 := by rw [wf_length,start_length,hA]
          rw [he,wf_append]
          show (wf A (start x) ++ [_]).getD i false = _
          by_cases hlt : i<22
          · exact List.getD_append _ _ _ _ (by omega)
          · rw [List.getD_eq_default _ _ (by simp [hwlen]; omega),
              List.getD_eq_default _ _ (by omega)]
        apply noB A (fun g hg => hfan g (he ▸ List.mem_append_left _ hg)) (by omega) a b
        intro x
        rw [← correct x,hw x a hae,hw x b hbe]
  have ha10 : 10 ≤ a := by rcases shape with h|h <;> omega
  have hb10 : 10 ≤ b := by rcases shape with h|h <;> omega
  have cleanReaders : ∀ v ∈ ([0,3] : List Nat),
      let n := gs.countP (fun g => g.op.eval [false] && g.inputs.head? == some v ||
        !g.op.eval [false] && g.inputs.contains v)
      1 ≤ n ∧ n ≤ 2 := by
    intro v hv
    have hv' : v=0 ∨ v=3 := by simpa using hv
    have hav : a ≠ v := by omega
    have hbv : b ≠ v := by omega
    have hr := hread v hv
    simpa [List.countP_append, eval_or1,
      hav,hbv,Ne.symm hav,Ne.symm hbv] using hr
  rcases shape with ⟨hae,hb10,hb22⟩ | ⟨hbe,ha10,ha22⟩
  · let k : Fin 12 := ⟨b-10,by omega⟩
    obtain ⟨x,hx⟩ := hRemaining gs k hlen hfan hnot cleanReaders
    change ((wf gs (start x)).getD 22 false || (wf gs (start x)).getD (10+k.val) false) ≠ f x at hx
    have hk : 10+k.val=b := by dsimp [k]; omega
    rw [hk,← hae] at hx
    exact hx (correct x)
  · let k : Fin 12 := ⟨a-10,by omega⟩
    obtain ⟨x,hx⟩ := hRemaining gs k hlen hfan hnot cleanReaders
    change ((wf gs (start x)).getD 22 false || (wf gs (start x)).getD (10+k.val) false) ≠ f x at hx
    have hk : 10+k.val=a := by dsimp [k]; omega
    rw [hk,← hbe,Bool.or_comm] at hx
    exact hx (correct x)
