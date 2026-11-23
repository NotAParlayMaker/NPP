import PEqualNP.Defs

namespace PEqualNP.Outside.Meta175

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wireStep (w : List Bool) (gt : Gate) : List Bool :=
  w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]

private theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl wireStep x := rfl

private theorem wireStep_length (w : List Bool) (gt : Gate) :
    (wireStep w gt).length = w.length + 1 := by
  simp [wireStep]

private theorem foldl_wireStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons gt rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, wireStep_length]
      omega

private theorem getD_append_single {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d =
      if i < l.length then l.getD i d
      else if i = l.length then a
      else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < l.length
  · simp [h1, List.getElem?_append_left h1]
  · by_cases h2 : i = l.length
    · simp [h2]
    · have hge : (l ++ [a]).length ≤ i := by simp; omega
      simp [h1, h2, List.getElem?_eq_none hge]

private theorem getD_append_single_lt {α : Type} (l : List α) (a d : α) (i : ℕ)
    (hi : i < l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  rw [getD_append_single, ite_eq_left hi]

private theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem getD_ofFn_ge {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : n ≤ i) :
    (List.ofFn x).getD i false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl

private theorem list_ofFn_snoc {m : ℕ} (u : Fin m → Bool) (b : Bool) :
    List.ofFn (Fin.snoc u b) = List.ofFn u ++ [b] := by
  refine List.ext_getElem ?_ ?_
  · simp
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    rw [List.getElem_ofFn]
    by_cases hi : i < m
    · rw [List.getElem_append_left (by simp [hi]), List.getElem_ofFn]
      have hcast : (⟨i, h1⟩ : Fin (m + 1)) = (⟨i, hi⟩ : Fin m).castSucc := rfl
      rw [hcast, Fin.snoc_castSucc]
    · have him : i = m := by omega
      rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn, him, Nat.sub_self, List.getElem_cons_zero]
      have hlast : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
      rw [hlast, Fin.snoc_last]

private def targetFun (n : ℕ) (g : (Fin (n + 1) → Bool) → Bool) (x : Fin (n + 2) → Bool) : Bool :=
  g (Fin.snoc (fun i : Fin n => x i.castSucc.castSucc)
    (x (Fin.last n).castSucc && x (Fin.last (n + 1))))

private theorem targetFun_snoc_true (n : ℕ) (g : (Fin (n + 1) → Bool) → Bool)
    (u : Fin (n + 1) → Bool) :
    targetFun n g (Fin.snoc u true) = g u := by
  unfold targetFun
  congr 1
  funext k
  refine Fin.lastCases ?_ ?_ k
  · simp [Fin.snoc_last, Fin.snoc_castSucc]
  · intro i
    simp [Fin.snoc_castSucc]

private theorem targetFun_snoc_snoc (n : ℕ) (g : (Fin (n + 1) → Bool) → Bool)
    (y : Fin n → Bool) (b : Bool) :
    targetFun n g (Fin.snoc (Fin.snoc y true) b) = g (Fin.snoc y b) := by
  unfold targetFun
  congr 1
  funext k
  refine Fin.lastCases ?_ ?_ k
  · simp [Fin.snoc_last, Fin.snoc_castSucc]
  · intro i
    simp [Fin.snoc_castSucc]

private def shiftIdx (n i : ℕ) : ℕ :=
  if i < n then i
  else if i = n then n + 2
  else i + 2

private def shiftGate (n : ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map (shiftIdx n)⟩

private def expandCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨⟨GateOp.and, [n, n + 1]⟩ :: C.gates.map (shiftGate n), shiftIdx n C.output⟩

private theorem expandCircuit_fanInTwo (n : ℕ) (C : Circuit) (hC : FanInTwo C) :
    FanInTwo (expandCircuit n C) := by
  intro gt hgt
  simp only [expandCircuit, List.mem_cons, List.mem_map] at hgt
  rcases hgt with rfl | ⟨gt0, hgt0, rfl⟩
  · refine ⟨by simp, by simp⟩
  · rcases hC gt0 hgt0 with ⟨hop, hlen⟩
    exact ⟨hop, by simp [shiftGate, hlen]⟩

private theorem expandCircuit_size (n : ℕ) (C : Circuit) :
    (expandCircuit n C).size = C.size + 1 := by
  simp [expandCircuit, Circuit.size]

private theorem foldl_shift_invariant (n : ℕ) (gs : List Gate) (wOld wNew : List Bool)
    (hge : n + 1 ≤ wOld.length)
    (hlen : wNew.length = wOld.length + 2)
    (hinv : ∀ i, wNew.getD (shiftIdx n i) false = wOld.getD i false) :
    ∀ i, ((gs.map (shiftGate n)).foldl wireStep wNew).getD (shiftIdx n i) false =
      (gs.foldl wireStep wOld).getD i false := by
  induction gs generalizing wOld wNew with
  | nil => exact hinv
  | cons gt rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hmap : (shiftGate n gt).inputs.map (fun j => wNew.getD j false) =
          gt.inputs.map (fun i => wOld.getD i false) := by
        simp only [shiftGate, List.map_map]
        exact List.map_congr_left fun i _ => hinv i
      apply ih
      · rw [wireStep_length]; omega
      · rw [wireStep_length, wireStep_length]; omega
      · intro i
        simp only [wireStep, hmap, getD_append_single]
        by_cases h1 : i < n
        · have hs : shiftIdx n i = i := by simp [shiftIdx, h1]
          have hlt1 : i < wOld.length := by omega
          have hlt2 : i < wNew.length := by omega
          rw [hs, ite_eq_left hlt2, ite_eq_left hlt1]
          simpa [hs] using hinv i
        · by_cases h2 : i = n
          · have hs : shiftIdx n i = n + 2 := by simp [shiftIdx, h2]
            have hlt1 : i < wOld.length := by omega
            have hlt2 : n + 2 < wNew.length := by omega
            rw [hs, ite_eq_left hlt2, ite_eq_left hlt1]
            simpa [hs] using hinv i
          · have hs : shiftIdx n i = i + 2 := by simp [shiftIdx, h1, h2]
            rw [hs]
            by_cases h3 : i < wOld.length
            · have hlt2 : i + 2 < wNew.length := by omega
              rw [ite_eq_left hlt2, ite_eq_left h3]
              simpa [hs] using hinv i
            · by_cases h4 : i = wOld.length
              · have heq2 : i + 2 = wNew.length := by omega
                have hnlt2 : ¬ i + 2 < wNew.length := by omega
                rw [ite_eq_right hnlt2, ite_eq_left heq2, ite_eq_right h3, ite_eq_left h4]
                rfl
              · have hnlt2 : ¬ i + 2 < wNew.length := by omega
                have hneq2 : i + 2 ≠ wNew.length := by omega
                rw [ite_eq_right hnlt2, ite_eq_right hneq2, ite_eq_right h3, ite_eq_right h4]

private theorem expandCircuit_eval (n : ℕ) (C : Circuit) (x : Fin (n + 2) → Bool) :
    (expandCircuit n C).eval (List.ofFn x) =
      C.eval (List.ofFn (Fin.snoc (fun i : Fin n => x i.castSucc.castSucc)
        (x (Fin.last n).castSucc && x (Fin.last (n + 1))))) := by
  unfold Circuit.eval
  rw [wires_eq_foldl, wires_eq_foldl]
  simp only [expandCircuit, List.foldl_cons]
  set u : Fin (n + 1) → Bool :=
    Fin.snoc (fun i : Fin n => x i.castSucc.castSucc)
      (x (Fin.last n).castSucc && x (Fin.last (n + 1)))
  set w0 : List Bool := wireStep (List.ofFn x) ⟨GateOp.and, [n, n + 1]⟩
  have hw0_len : w0.length = (List.ofFn u).length + 2 := by
    simp [w0, wireStep]
  have hw0_inv : ∀ i, w0.getD (shiftIdx n i) false = (List.ofFn u).getD i false := by
    intro i
    simp only [w0, wireStep, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, getD_append_single, List.length_ofFn]
    by_cases h1 : i < n
    · have hs : shiftIdx n i = i := by simp [shiftIdx, h1]
      rw [hs, ite_eq_left (by omega), getD_ofFn x i (by omega), getD_ofFn u i (by omega)]
      have hcast : (⟨i, by omega⟩ : Fin (n + 1)) = (⟨i, h1⟩ : Fin n).castSucc := rfl
      rw [hcast]
      simp only [u, Fin.snoc_castSucc]
      rfl
    · by_cases h2 : i = n
      · have hs : shiftIdx n i = n + 2 := by simp [shiftIdx, h2]
        rw [hs, ite_eq_right (by omega), ite_eq_left rfl,
          getD_ofFn x n (by omega), getD_ofFn x (n + 1) (by omega),
          getD_ofFn u i (by omega)]
        have hlast : (⟨i, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext h2
        rw [hlast]
        simp only [u, Fin.snoc_last]
        rfl
      · have hs : shiftIdx n i = i + 2 := by simp [shiftIdx, h1, h2]
        rw [hs, ite_eq_right (by omega), ite_eq_right (by omega), getD_ofFn_ge u i (by omega)]
  exact foldl_shift_invariant n C.gates (List.ofFn u) w0 (by simp) hw0_len hw0_inv C.output

private abbrev SymWire := Bool ⊕ ℕ

private def evalSym (w : List Bool) : SymWire → Bool
  | Sum.inl b => b
  | Sum.inr idx => w.getD idx false

private def initEnv (n : ℕ) : List SymWire :=
  List.ofFn (fun i : Fin (n + 1) => Sum.inr (i : ℕ)) ++ [Sum.inl true]

private def compileAnd2 (n : ℕ) (env : List SymWire) (out : List Gate)
    (a b : SymWire) : List SymWire × List Gate :=
  match a, b with
  | Sum.inl false, _ => (env ++ [Sum.inl false], out)
  | _, Sum.inl false => (env ++ [Sum.inl false], out)
  | Sum.inl true, y => (env ++ [y], out)
  | x, Sum.inl true => (env ++ [x], out)
  | Sum.inr wi, Sum.inr wj =>
      (env ++ [Sum.inr (n + 1 + out.length)], out ++ [⟨GateOp.and, [wi, wj]⟩])

private def compileOr2 (n : ℕ) (env : List SymWire) (out : List Gate)
    (a b : SymWire) : List SymWire × List Gate :=
  match a, b with
  | Sum.inl true, _ => (env ++ [Sum.inl true], out)
  | _, Sum.inl true => (env ++ [Sum.inl true], out)
  | Sum.inl false, y => (env ++ [y], out)
  | x, Sum.inl false => (env ++ [x], out)
  | Sum.inr wi, Sum.inr wj =>
      (env ++ [Sum.inr (n + 1 + out.length)], out ++ [⟨GateOp.or, [wi, wj]⟩])

private def compileNot1 (n : ℕ) (env : List SymWire) (out : List Gate)
    (a : SymWire) : List SymWire × List Gate :=
  match a with
  | Sum.inl b => (env ++ [Sum.inl (!b)], out)
  | Sum.inr wi =>
      (env ++ [Sum.inr (n + 1 + out.length)], out ++ [⟨GateOp.not, [wi]⟩])

private def compileGate (n : ℕ) : List SymWire × List Gate → Gate → List SymWire × List Gate
  | (env, out), ⟨GateOp.and, []⟩ => (env ++ [Sum.inl true], out)
  | (env, out), ⟨GateOp.and, [i]⟩ => (env ++ [env.getD i (Sum.inl false)], out)
  | (env, out), ⟨GateOp.and, [i, j]⟩ =>
      compileAnd2 n env out (env.getD i (Sum.inl false)) (env.getD j (Sum.inl false))
  | (env, out), ⟨GateOp.or, []⟩ => (env ++ [Sum.inl false], out)
  | (env, out), ⟨GateOp.or, [i]⟩ => (env ++ [env.getD i (Sum.inl false)], out)
  | (env, out), ⟨GateOp.or, [i, j]⟩ =>
      compileOr2 n env out (env.getD i (Sum.inl false)) (env.getD j (Sum.inl false))
  | (env, out), ⟨GateOp.not, []⟩ => (env ++ [Sum.inl true], out)
  | (env, out), ⟨GateOp.not, i :: _⟩ =>
      compileNot1 n env out (env.getD i (Sum.inl false))
  | (env, out), _ => (env ++ [Sum.inl false], out)

private def GateFanInTwo (gt : Gate) : Prop :=
  gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2

private def EnvBounded (n : ℕ) (env : List SymWire) (outLen : ℕ) : Prop :=
  ∀ wi, Sum.inr wi ∈ env → wi < n + 1 + outLen

private theorem rd_bound (n : ℕ) (env : List SymWire) (outLen : ℕ)
    (hb : EnvBounded n env outLen) (i wi : ℕ)
    (h : env.getD i (Sum.inl false) = Sum.inr wi) : wi < n + 1 + outLen := by
  by_cases hi : i < env.length
  · have hmem : env.getD i (Sum.inl false) ∈ env := by
      simp [List.getD_eq_getElem?_getD, hi]
    rw [h] at hmem
    exact hb wi hmem
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
      Option.getD_none] at h
    cases h

private theorem compileAnd2_basic (n : ℕ) (env : List SymWire) (out : List Gate)
    (a b : SymWire)
    (hout : ∀ g ∈ out, GateFanInTwo g)
    (hb : EnvBounded n env out.length)
    (ha : ∀ wi, a = Sum.inr wi → wi < n + 1 + out.length)
    (hb' : ∀ wj, b = Sum.inr wj → wj < n + 1 + out.length) :
    let res := compileAnd2 n env out a b
    res.1.length = env.length + 1 ∧
    (∀ k < env.length, res.1.getD k (Sum.inl false) = env.getD k (Sum.inl false)) ∧
    res.2.length ≤ out.length + 1 ∧
    (∀ g ∈ res.2, GateFanInTwo g) ∧
    EnvBounded n res.1 res.2.length := by
  cases a with
  | inl b1 =>
      cases b1
      · refine ⟨by simp [compileAnd2], fun k hk => getD_append_single_lt env _ _ k hk,
          by simp [compileAnd2], hout, ?_⟩
        intro wi hmem
        simp only [compileAnd2, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
        exact hb wi hmem
      · cases b with
        | inl b2 =>
            cases b2 <;>
              (refine ⟨by simp [compileAnd2], fun k hk => getD_append_single_lt env _ _ k hk,
                by simp [compileAnd2], hout, ?_⟩;
               intro wi hmem;
               simp only [compileAnd2, List.mem_append, List.mem_singleton, reduceCtorEq,
                 or_false] at hmem;
               exact hb wi hmem)
        | inr w2 =>
            refine ⟨by simp [compileAnd2], fun k hk => getD_append_single_lt env _ _ k hk,
              by simp [compileAnd2], hout, ?_⟩
            intro wi hmem
            simp only [compileAnd2, List.mem_append, List.mem_singleton, Sum.inr.injEq] at hmem
            rcases hmem with hmem | rfl
            · exact hb wi hmem
            · exact hb' wi rfl
  | inr w1 =>
      cases b with
      | inl b2 =>
          cases b2
          · refine ⟨by simp [compileAnd2], fun k hk => getD_append_single_lt env _ _ k hk,
              by simp [compileAnd2], hout, ?_⟩
            intro wi hmem
            simp only [compileAnd2, List.mem_append, List.mem_singleton, reduceCtorEq,
              or_false] at hmem
            exact hb wi hmem
          · refine ⟨by simp [compileAnd2], fun k hk => getD_append_single_lt env _ _ k hk,
              by simp [compileAnd2], hout, ?_⟩
            intro wi hmem
            simp only [compileAnd2, List.mem_append, List.mem_singleton, Sum.inr.injEq] at hmem
            rcases hmem with hmem | rfl
            · exact hb wi hmem
            · exact ha wi rfl
      | inr w2 =>
          refine ⟨by simp [compileAnd2], fun k hk => getD_append_single_lt env _ _ k hk,
            by simp [compileAnd2], ?_, ?_⟩
          · intro g hg
            simp only [compileAnd2, List.mem_append, List.mem_singleton] at hg
            rcases hg with hg | rfl
            · exact hout g hg
            · exact ⟨by simp, by simp⟩
          · intro wi hmem
            simp only [compileAnd2, List.mem_append, List.mem_singleton, Sum.inr.injEq,
              List.length_append, List.length_singleton] at hmem ⊢
            rcases hmem with hmem | rfl
            · have := hb wi hmem; omega
            · omega

private theorem compileOr2_basic (n : ℕ) (env : List SymWire) (out : List Gate)
    (a b : SymWire)
    (hout : ∀ g ∈ out, GateFanInTwo g)
    (hb : EnvBounded n env out.length)
    (ha : ∀ wi, a = Sum.inr wi → wi < n + 1 + out.length)
    (hb' : ∀ wj, b = Sum.inr wj → wj < n + 1 + out.length) :
    let res := compileOr2 n env out a b
    res.1.length = env.length + 1 ∧
    (∀ k < env.length, res.1.getD k (Sum.inl false) = env.getD k (Sum.inl false)) ∧
    res.2.length ≤ out.length + 1 ∧
    (∀ g ∈ res.2, GateFanInTwo g) ∧
    EnvBounded n res.1 res.2.length := by
  cases a with
  | inl b1 =>
      cases b1
      · cases b with
        | inl b2 =>
            cases b2 <;>
              (refine ⟨by simp [compileOr2], fun k hk => getD_append_single_lt env _ _ k hk,
                by simp [compileOr2], hout, ?_⟩;
               intro wi hmem;
               simp only [compileOr2, List.mem_append, List.mem_singleton, reduceCtorEq,
                 or_false] at hmem;
               exact hb wi hmem)
        | inr w2 =>
            refine ⟨by simp [compileOr2], fun k hk => getD_append_single_lt env _ _ k hk,
              by simp [compileOr2], hout, ?_⟩
            intro wi hmem
            simp only [compileOr2, List.mem_append, List.mem_singleton, Sum.inr.injEq] at hmem
            rcases hmem with hmem | rfl
            · exact hb wi hmem
            · exact hb' wi rfl
      · refine ⟨by simp [compileOr2], fun k hk => getD_append_single_lt env _ _ k hk,
          by simp [compileOr2], hout, ?_⟩
        intro wi hmem
        simp only [compileOr2, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
        exact hb wi hmem
  | inr w1 =>
      cases b with
      | inl b2 =>
          cases b2
          · refine ⟨by simp [compileOr2], fun k hk => getD_append_single_lt env _ _ k hk,
              by simp [compileOr2], hout, ?_⟩
            intro wi hmem
            simp only [compileOr2, List.mem_append, List.mem_singleton, Sum.inr.injEq] at hmem
            rcases hmem with hmem | rfl
            · exact hb wi hmem
            · exact ha wi rfl
          · refine ⟨by simp [compileOr2], fun k hk => getD_append_single_lt env _ _ k hk,
              by simp [compileOr2], hout, ?_⟩
            intro wi hmem
            simp only [compileOr2, List.mem_append, List.mem_singleton, reduceCtorEq,
              or_false] at hmem
            exact hb wi hmem
      | inr w2 =>
          refine ⟨by simp [compileOr2], fun k hk => getD_append_single_lt env _ _ k hk,
            by simp [compileOr2], ?_, ?_⟩
          · intro g hg
            simp only [compileOr2, List.mem_append, List.mem_singleton] at hg
            rcases hg with hg | rfl
            · exact hout g hg
            · exact ⟨by simp, by simp⟩
          · intro wi hmem
            simp only [compileOr2, List.mem_append, List.mem_singleton, Sum.inr.injEq,
              List.length_append, List.length_singleton] at hmem ⊢
            rcases hmem with hmem | rfl
            · have := hb wi hmem; omega
            · omega

private theorem compileNot1_basic (n : ℕ) (env : List SymWire) (out : List Gate)
    (a : SymWire)
    (hout : ∀ g ∈ out, GateFanInTwo g)
    (hb : EnvBounded n env out.length) :
    let res := compileNot1 n env out a
    res.1.length = env.length + 1 ∧
    (∀ k < env.length, res.1.getD k (Sum.inl false) = env.getD k (Sum.inl false)) ∧
    res.2.length ≤ out.length + 1 ∧
    (∀ g ∈ res.2, GateFanInTwo g) ∧
    EnvBounded n res.1 res.2.length := by
  cases a with
  | inl b1 =>
      refine ⟨by simp [compileNot1], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileNot1], hout, ?_⟩
      intro wi hmem
      simp only [compileNot1, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
      exact hb wi hmem
  | inr w1 =>
      refine ⟨by simp [compileNot1], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileNot1], ?_, ?_⟩
      · intro g hg
        simp only [compileNot1, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hout g hg
        · exact ⟨by simp, by simp⟩
      · intro wi hmem
        simp only [compileNot1, List.mem_append, List.mem_singleton, Sum.inr.injEq,
          List.length_append, List.length_singleton] at hmem ⊢
        rcases hmem with hmem | rfl
        · have := hb wi hmem; omega
        · omega

private theorem compileGate_basic (n : ℕ) (st : List SymWire × List Gate) (gt : Gate)
    (hout : ∀ g ∈ st.2, GateFanInTwo g)
    (hb : EnvBounded n st.1 st.2.length) :
    let res := compileGate n st gt
    res.1.length = st.1.length + 1 ∧
    (∀ k < st.1.length, res.1.getD k (Sum.inl false) = st.1.getD k (Sum.inl false)) ∧
    res.2.length ≤ st.2.length + 1 ∧
    (∀ g ∈ res.2, GateFanInTwo g) ∧
    EnvBounded n res.1 res.2.length := by
  rcases st with ⟨env, out⟩
  rcases gt with ⟨op, ins⟩
  match op, ins with
  | GateOp.and, [] =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
      exact hb wi hmem
  | GateOp.and, [i] =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hEq
      · exact hb wi hmem
      · exact rd_bound n env out.length hb i wi hEq.symm
  | GateOp.and, [i, j] =>
      exact compileAnd2_basic n env out (env.getD i (Sum.inl false)) (env.getD j (Sum.inl false))
        hout hb (fun wi h => rd_bound n env out.length hb i wi h)
        (fun wj h => rd_bound n env out.length hb j wj h)
  | GateOp.and, _ :: _ :: _ :: _ =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
      exact hb wi hmem
  | GateOp.or, [] =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
      exact hb wi hmem
  | GateOp.or, [i] =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hEq
      · exact hb wi hmem
      · exact rd_bound n env out.length hb i wi hEq.symm
  | GateOp.or, [i, j] =>
      exact compileOr2_basic n env out (env.getD i (Sum.inl false)) (env.getD j (Sum.inl false))
        hout hb (fun wi h => rd_bound n env out.length hb i wi h)
        (fun wj h => rd_bound n env out.length hb j wj h)
  | GateOp.or, _ :: _ :: _ :: _ =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
      exact hb wi hmem
  | GateOp.not, [] =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
      exact hb wi hmem
  | GateOp.not, i :: _ =>
      exact compileNot1_basic n env out (env.getD i (Sum.inl false)) hout hb
  | GateOp.mod _, _ =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
      exact hb wi hmem
  | GateOp.maj, _ =>
      refine ⟨by simp [compileGate], fun k hk => getD_append_single_lt env _ _ k hk,
        by simp [compileGate], hout, ?_⟩
      intro wi hmem
      simp only [compileGate, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hmem
      exact hb wi hmem

private theorem evalSym_append_of_lt (w : List Bool) (v : Bool) (s : SymWire)
    (hs : ∀ wi, s = Sum.inr wi → wi < w.length) :
    evalSym (w ++ [v]) s = evalSym w s := by
  cases s with
  | inl b => rfl
  | inr wi =>
      have hlt : wi < w.length := hs wi rfl
      exact getD_append_single_lt w v false wi hlt

private theorem compileGate_sound_step (n : ℕ) (env : List SymWire) (out : List Gate)
    (gt : Gate) (hgt : GateFanInTwo gt) (uList wOld : List Bool)
    (huLen : uList.length = n + 1)
    (hwOld : wOld.length = env.length)
    (hb : EnvBounded n env out.length)
    (hinv : ∀ k, evalSym (out.foldl wireStep uList) (env.getD k (Sum.inl false)) =
      wOld.getD k false) :
    ∀ k, evalSym ((compileGate n (env, out) gt).2.foldl wireStep uList)
      ((compileGate n (env, out) gt).1.getD k (Sum.inl false)) =
      (wireStep wOld gt).getD k false := by
  set wNew := out.foldl wireStep uList
  have hwNewLen : wNew.length = n + 1 + out.length := by
    rw [foldl_wireStep_length, huLen]
  have hkeep : ∀ k (v : Bool), k < env.length →
      evalSym (wNew ++ [v]) (env.getD k (Sum.inl false)) = wOld.getD k false := by
    intro k v hk
    rw [evalSym_append_of_lt wNew v (env.getD k (Sum.inl false))]
    · exact hinv k
    · intro wi hwi
      rw [hwNewLen]
      exact rd_bound n env out.length hb k wi hwi
  rcases hgt with ⟨hop, hlen⟩
  rcases gt with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ =>
        intro k
        simp only [compileGate, wireStep, GateOp.eval, List.map_nil, List.all_nil,
          getD_append_single, hwOld]
        split_ifs with h1 h2
        · exact hinv k
        · rfl
        · rfl
    | [i], _ =>
        intro k
        simp only [compileGate, wireStep, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, getD_append_single, hwOld]
        split_ifs with h1 h2
        · exact hinv k
        · exact hinv i
        · rfl
    | [i, j], _ =>
        intro k
        have hi := hinv i
        have hj := hinv j
        simp only [compileGate, wireStep, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, id_eq, Bool.and_true]
        cases hri : env.getD i (Sum.inl false) with
        | inl b1 =>
            cases b1
            · simp only [compileAnd2, getD_append_single, hwOld, hri, evalSym] at hi ⊢
              split_ifs with h1 h2
              · exact hinv k
              · rw [← hi]; rfl
              · rfl
            · cases hrj : env.getD j (Sum.inl false) with
              | inl b2 =>
                  cases b2 <;>
                    (simp only [compileAnd2, getD_append_single, hwOld, hri, hrj,
                       evalSym] at hi hj ⊢;
                     split_ifs with h1 h2;
                     · exact hinv k
                     · rw [← hi, ← hj]; rfl
                     · rfl)
              | inr wj =>
                  simp only [compileAnd2, getD_append_single, hwOld, hri, hrj,
                    evalSym] at hi hj ⊢
                  split_ifs with h1 h2
                  · exact hinv k
                  · rw [← hi, ← hj]; exact (Bool.true_and _).symm
                  · rfl
        | inr wi =>
            cases hrj : env.getD j (Sum.inl false) with
            | inl b2 =>
                cases b2
                · simp only [compileAnd2, getD_append_single, hwOld, hri, hrj,
                    evalSym] at hi hj ⊢
                  split_ifs with h1 h2
                  · exact hinv k
                  · rw [← hi, ← hj]; exact (Bool.and_false _).symm
                  · rfl
                · simp only [compileAnd2, getD_append_single, hwOld, hri, hrj,
                    evalSym] at hi hj ⊢
                  split_ifs with h1 h2
                  · exact hinv k
                  · rw [← hi, ← hj]; exact (Bool.and_true _).symm
                  · rfl
            | inr wj =>
                simp only [compileAnd2, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  getD_append_single, hwOld]
                simp only [hri, hrj, evalSym] at hi hj
                split_ifs with h1 h2
                · exact hkeep k _ h1
                · simp only [wireStep, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                    List.all_nil, id_eq, Bool.and_true, evalSym, getD_append_single,
                    foldl_wireStep_length, huLen, lt_irrefl, ↓reduceIte]
                  rw [hi, hj]
                · rfl
  · match ins, hlen with
    | [], _ =>
        intro k
        simp only [compileGate, wireStep, GateOp.eval, List.map_nil, List.any_nil,
          getD_append_single, hwOld]
        split_ifs with h1 h2
        · exact hinv k
        · rfl
        · rfl
    | [i], _ =>
        intro k
        simp only [compileGate, wireStep, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false, getD_append_single, hwOld]
        split_ifs with h1 h2
        · exact hinv k
        · exact hinv i
        · rfl
    | [i, j], _ =>
        intro k
        have hi := hinv i
        have hj := hinv j
        simp only [compileGate, wireStep, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false]
        cases hri : env.getD i (Sum.inl false) with
        | inl b1 =>
            cases b1
            · cases hrj : env.getD j (Sum.inl false) with
              | inl b2 =>
                  cases b2 <;>
                    (simp only [compileOr2, getD_append_single, hwOld, hri, hrj,
                       evalSym] at hi hj ⊢;
                     split_ifs with h1 h2;
                     · exact hinv k
                     · rw [← hi, ← hj]; rfl
                     · rfl)
              | inr wj =>
                  simp only [compileOr2, getD_append_single, hwOld, hri, hrj,
                    evalSym] at hi hj ⊢
                  split_ifs with h1 h2
                  · exact hinv k
                  · rw [← hi, ← hj]; exact (Bool.false_or _).symm
                  · rfl
            · simp only [compileOr2, getD_append_single, hwOld, hri, evalSym] at hi ⊢
              split_ifs with h1 h2
              · exact hinv k
              · rw [← hi]; rfl
              · rfl
        | inr wi =>
            cases hrj : env.getD j (Sum.inl false) with
            | inl b2 =>
                cases b2
                · simp only [compileOr2, getD_append_single, hwOld, hri, hrj,
                    evalSym] at hi hj ⊢
                  split_ifs with h1 h2
                  · exact hinv k
                  · rw [← hi, ← hj]; exact (Bool.or_false _).symm
                  · rfl
                · simp only [compileOr2, getD_append_single, hwOld, hri, hrj,
                    evalSym] at hi hj ⊢
                  split_ifs with h1 h2
                  · exact hinv k
                  · rw [← hi, ← hj]; exact (Bool.or_true _).symm
                  · rfl
            | inr wj =>
                simp only [compileOr2, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  getD_append_single, hwOld]
                simp only [hri, hrj, evalSym] at hi hj
                split_ifs with h1 h2
                · exact hkeep k _ h1
                · simp only [wireStep, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                    List.any_nil, id_eq, Bool.or_false, evalSym, getD_append_single,
                    foldl_wireStep_length, huLen, lt_irrefl, ↓reduceIte]
                  rw [hi, hj]
                · rfl
  · match ins, hlen with
    | [], _ =>
        intro k
        simp only [compileGate, wireStep, GateOp.eval, List.map_nil, List.headD_nil,
          getD_append_single, hwOld]
        split_ifs with h1 h2
        · exact hinv k
        · rfl
        · rfl
    | i :: rest, _ =>
        intro k
        have hi := hinv i
        simp only [compileGate, wireStep, GateOp.eval, List.map_cons, List.headD_cons]
        cases hri : env.getD i (Sum.inl false) with
        | inl b1 =>
            simp only [compileNot1, getD_append_single, hwOld, hri, evalSym] at hi ⊢
            split_ifs with h1 h2
            · exact hinv k
            · rw [← hi]
            · rfl
        | inr wi =>
            simp only [compileNot1, List.foldl_append, List.foldl_cons, List.foldl_nil,
              getD_append_single, hwOld]
            simp only [hri, evalSym] at hi
            split_ifs with h1 h2
            · exact hkeep k _ h1
            · simp only [wireStep, GateOp.eval, List.map_cons, List.headD_cons, evalSym,
                getD_append_single, foldl_wireStep_length, huLen, lt_irrefl, ↓reduceIte]
              rw [hi]
            · rfl

private theorem compileGate_nodrop_step (n : ℕ) (env : List SymWire) (out : List Gate)
    (gt : Gate) (hgt : GateFanInTwo gt) (uList wOld : List Bool)
    (huLen : uList.length = n + 1)
    (hwOld : wOld.length = env.length)
    (hconst : env.getD (n + 1) (Sum.inl false) = Sum.inl true)
    (hb : EnvBounded n env out.length)
    (hnodrop : (compileGate n (env, out) gt).2.length = out.length + 1)
    (hinv : ∀ k, k ≠ n + 1 →
      evalSym (out.foldl wireStep uList) (env.getD k (Sum.inl false)) = wOld.getD k false) :
    ∀ k, k ≠ n + 1 →
      evalSym ((compileGate n (env, out) gt).2.foldl wireStep uList)
        ((compileGate n (env, out) gt).1.getD k (Sum.inl false)) =
      (wireStep wOld gt).getD k false := by
  set wNew := out.foldl wireStep uList
  have hwNewLen : wNew.length = n + 1 + out.length := by
    rw [foldl_wireStep_length, huLen]
  have hkeep : ∀ k (v : Bool), k < env.length → k ≠ n + 1 →
      evalSym (wNew ++ [v]) (env.getD k (Sum.inl false)) = wOld.getD k false := by
    intro k v hk hne
    rw [evalSym_append_of_lt wNew v (env.getD k (Sum.inl false))]
    · exact hinv k hne
    · intro wi hwi
      rw [hwNewLen]
      exact rd_bound n env out.length hb k wi hwi
  have hne_of_inr : ∀ i wi, env.getD i (Sum.inl false) = Sum.inr wi → i ≠ n + 1 := by
    intro i wi hri hEq
    subst hEq
    rw [hconst] at hri
    cases hri
  rcases hgt with ⟨hop, hlen⟩
  rcases gt with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ =>
        simp [compileGate] at hnodrop
    | [i], _ =>
        simp [compileGate] at hnodrop
    | [i, j], _ =>
        simp only [compileGate] at hnodrop ⊢
        cases hri : env.getD i (Sum.inl false) with
        | inl b1 =>
            rw [hri] at hnodrop
            cases b1
            · simp [compileAnd2] at hnodrop
            · cases hrj : env.getD j (Sum.inl false) with
              | inl b2 =>
                  rw [hrj] at hnodrop
                  cases b2 <;> simp [compileAnd2] at hnodrop
              | inr wj =>
                  rw [hrj] at hnodrop
                  simp [compileAnd2] at hnodrop
        | inr wi =>
            rw [hri] at hnodrop
            cases hrj : env.getD j (Sum.inl false) with
            | inl b2 =>
                rw [hrj] at hnodrop
                cases b2 <;> simp [compileAnd2] at hnodrop
            | inr wj =>
                intro k hk
                have hi := hinv i (hne_of_inr i wi hri)
                have hj := hinv j (hne_of_inr j wj hrj)
                simp only [hri, hrj, evalSym] at hi hj
                simp only [compileAnd2, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  wireStep, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                  List.all_nil, id_eq, Bool.and_true, getD_append_single, hwOld]
                split_ifs with h1 h2
                · exact hkeep k _ h1 hk
                · simp only [evalSym, getD_append_single, foldl_wireStep_length, huLen,
                    lt_irrefl, ↓reduceIte]
                  rw [hi, hj]
                · rfl
  · match ins, hlen with
    | [], _ =>
        simp [compileGate] at hnodrop
    | [i], _ =>
        simp [compileGate] at hnodrop
    | [i, j], _ =>
        simp only [compileGate] at hnodrop ⊢
        cases hri : env.getD i (Sum.inl false) with
        | inl b1 =>
            rw [hri] at hnodrop
            cases b1
            · cases hrj : env.getD j (Sum.inl false) with
              | inl b2 =>
                  rw [hrj] at hnodrop
                  cases b2 <;> simp [compileOr2] at hnodrop
              | inr wj =>
                  rw [hrj] at hnodrop
                  simp [compileOr2] at hnodrop
            · simp [compileOr2] at hnodrop
        | inr wi =>
            rw [hri] at hnodrop
            cases hrj : env.getD j (Sum.inl false) with
            | inl b2 =>
                rw [hrj] at hnodrop
                cases b2 <;> simp [compileOr2] at hnodrop
            | inr wj =>
                intro k hk
                have hi := hinv i (hne_of_inr i wi hri)
                have hj := hinv j (hne_of_inr j wj hrj)
                simp only [hri, hrj, evalSym] at hi hj
                simp only [compileOr2, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  wireStep, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                  List.any_nil, id_eq, Bool.or_false, getD_append_single, hwOld]
                split_ifs with h1 h2
                · exact hkeep k _ h1 hk
                · simp only [evalSym, getD_append_single, foldl_wireStep_length, huLen,
                    lt_irrefl, ↓reduceIte]
                  rw [hi, hj]
                · rfl
  · match ins, hlen with
    | [], _ =>
        simp [compileGate] at hnodrop
    | i :: rest, _ =>
        simp only [compileGate] at hnodrop ⊢
        cases hri : env.getD i (Sum.inl false) with
        | inl b1 =>
            rw [hri] at hnodrop
            simp [compileNot1] at hnodrop
        | inr wi =>
            intro k hk
            have hi := hinv i (hne_of_inr i wi hri)
            simp only [hri, evalSym] at hi
            simp only [compileNot1, List.foldl_append, List.foldl_cons, List.foldl_nil,
              wireStep, GateOp.eval, List.map_cons, List.headD_cons, getD_append_single, hwOld]
            split_ifs with h1 h2
            · exact hkeep k _ h1 hk
            · simp only [evalSym, getD_append_single, foldl_wireStep_length, huLen,
                lt_irrefl, ↓reduceIte]
              rw [hi]
            · rfl

private theorem foldl_compileGate_props (n : ℕ) (gs : List Gate)
    (st : List SymWire × List Gate)
    (hout : ∀ g ∈ st.2, GateFanInTwo g)
    (hb : EnvBounded n st.1 st.2.length)
    (henv_ge : n + 2 ≤ st.1.length)
    (hconst : st.1.getD (n + 1) (Sum.inl false) = Sum.inl true) :
    let res := gs.foldl (compileGate n) st
    (∀ g ∈ res.2, GateFanInTwo g) ∧
    res.2.length ≤ st.2.length + gs.length ∧
    res.1.length = st.1.length + gs.length ∧
    res.1.getD (n + 1) (Sum.inl false) = Sum.inl true := by
  induction gs generalizing st with
  | nil =>
      exact ⟨hout, by simp, by simp, hconst⟩
  | cons gt rest ih =>
      simp only [List.foldl_cons]
      rcases compileGate_basic n st gt hout hb with ⟨hlen1, hget1, houtLen1, hout1, hb1⟩
      have hconst1 : (compileGate n st gt).1.getD (n + 1) (Sum.inl false) = Sum.inl true := by
        rw [hget1 (n + 1) (by omega), hconst]
      rcases ih (compileGate n st gt) hout1 hb1 (by omega) hconst1 with
        ⟨hF, hL, hE, hC⟩
      refine ⟨hF, ?_, ?_, hC⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

private theorem foldl_compileGate_sound (n : ℕ) (gs : List Gate)
    (st : List SymWire × List Gate) (uList wOld : List Bool)
    (hgs : ∀ g ∈ gs, GateFanInTwo g)
    (hout : ∀ g ∈ st.2, GateFanInTwo g)
    (huLen : uList.length = n + 1)
    (hwOld : wOld.length = st.1.length)
    (hb : EnvBounded n st.1 st.2.length)
    (hinv : ∀ k, evalSym (st.2.foldl wireStep uList) (st.1.getD k (Sum.inl false)) =
      wOld.getD k false) :
    let res := gs.foldl (compileGate n) st
    ∀ k, evalSym (res.2.foldl wireStep uList) (res.1.getD k (Sum.inl false)) =
      (gs.foldl wireStep wOld).getD k false := by
  induction gs generalizing st wOld with
  | nil => exact hinv
  | cons gt rest ih =>
      simp only [List.foldl_cons]
      have hgt : GateFanInTwo gt := hgs gt (List.mem_cons_self ..)
      have hrest : ∀ g ∈ rest, GateFanInTwo g := fun g hg => hgs g (List.mem_cons_of_mem _ hg)
      rcases compileGate_basic n st gt hout hb with ⟨hlen1, _, _, hout1, hb1⟩
      have hstep := compileGate_sound_step n st.1 st.2 gt hgt uList wOld huLen hwOld hb hinv
      have hwOld1 : (wireStep wOld gt).length = (compileGate n st gt).1.length := by
        rw [wireStep_length, hlen1, hwOld]
      exact ih (compileGate n st gt) (wireStep wOld gt) hrest hout1 hwOld1 hb1 hstep

private theorem foldl_compileGate_nodrop (n : ℕ) (gs : List Gate)
    (st : List SymWire × List Gate) (uList wOld : List Bool)
    (hgs : ∀ g ∈ gs, GateFanInTwo g)
    (hout : ∀ g ∈ st.2, GateFanInTwo g)
    (huLen : uList.length = n + 1)
    (hwOld : wOld.length = st.1.length)
    (hb : EnvBounded n st.1 st.2.length)
    (henv_ge : n + 2 ≤ st.1.length)
    (hconst : st.1.getD (n + 1) (Sum.inl false) = Sum.inl true)
    (hnodrop : (gs.foldl (compileGate n) st).2.length = st.2.length + gs.length)
    (hinv : ∀ k, k ≠ n + 1 →
      evalSym (st.2.foldl wireStep uList) (st.1.getD k (Sum.inl false)) = wOld.getD k false) :
    let res := gs.foldl (compileGate n) st
    ∀ k, k ≠ n + 1 →
      evalSym (res.2.foldl wireStep uList) (res.1.getD k (Sum.inl false)) =
      (gs.foldl wireStep wOld).getD k false := by
  induction gs generalizing st wOld with
  | nil => exact hinv
  | cons gt rest ih =>
      simp only [List.foldl_cons] at hnodrop ⊢
      have hgt : GateFanInTwo gt := hgs gt (List.mem_cons_self ..)
      have hrest : ∀ g ∈ rest, GateFanInTwo g := fun g hg => hgs g (List.mem_cons_of_mem _ hg)
      rcases compileGate_basic n st gt hout hb with ⟨hlen1, hget1, houtLen1, hout1, hb1⟩
      have hconst1 : (compileGate n st gt).1.getD (n + 1) (Sum.inl false) = Sum.inl true := by
        rw [hget1 (n + 1) (by omega), hconst]
      have hrestBound := (foldl_compileGate_props n rest (compileGate n st gt) hout1 hb1
        (by omega) hconst1).2.1
      have hgt_nodrop : (compileGate n st gt).2.length = st.2.length + 1 := by
        simp only [List.length_cons] at hnodrop
        omega
      have hrest_nodrop :
          (rest.foldl (compileGate n) (compileGate n st gt)).2.length =
            (compileGate n st gt).2.length + rest.length := by
        simp only [List.length_cons] at hnodrop
        omega
      have hstep := compileGate_nodrop_step n st.1 st.2 gt hgt uList wOld huLen hwOld
        hconst hb hgt_nodrop hinv
      have hwOld1 : (wireStep wOld gt).length = (compileGate n st gt).1.length := by
        rw [wireStep_length, hlen1, hwOld]
      exact ih (compileGate n st gt) (wireStep wOld gt) hrest hout1 hwOld1 hb1 (by omega)
        hconst1 hrest_nodrop hstep

private theorem initEnv_length (n : ℕ) : (initEnv n).length = n + 2 := by
  simp [initEnv]

private theorem initEnv_getD (n k : ℕ) :
    (initEnv n).getD k (Sum.inl false) =
      if k < n + 1 then Sum.inr k
      else if k = n + 1 then Sum.inl true
      else Sum.inl false := by
  simp only [initEnv, getD_append_single, List.length_ofFn]
  split_ifs with h1 h2
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h1, ↓reduceDIte, Option.getD_some]
  · rfl
  · rfl

private theorem initEnv_getD_last (n : ℕ) :
    (initEnv n).getD (n + 1) (Sum.inl false) = Sum.inl true := by
  rw [initEnv_getD]
  simp

private theorem initEnv_bounded (n : ℕ) : EnvBounded n (initEnv n) 0 := by
  intro wi hmem
  simp only [initEnv, List.mem_append, List.mem_ofFn, List.mem_singleton, reduceCtorEq,
    or_false] at hmem
  rcases hmem with ⟨i, hi⟩
  have hwi : wi = (i : ℕ) := (Sum.inr.inj hi).symm
  omega

private theorem initEnv_sound (n : ℕ) (u : Fin (n + 1) → Bool) (k : ℕ) :
    evalSym (List.ofFn u) ((initEnv n).getD k (Sum.inl false)) =
      (List.ofFn (Fin.snoc u true)).getD k false := by
  rw [initEnv_getD, list_ofFn_snoc, getD_append_single, List.length_ofFn]
  split_ifs with h1 h2
  · rfl
  · rfl
  · rfl

private theorem initEnv_sound_ne (n : ℕ) (u : Fin (n + 1) → Bool) (b : Bool) (k : ℕ)
    (hk : k ≠ n + 1) :
    evalSym (List.ofFn u) ((initEnv n).getD k (Sum.inl false)) =
      (List.ofFn (Fin.snoc u b)).getD k false := by
  rw [initEnv_getD, list_ofFn_snoc, getD_append_single, List.length_ofFn]
  by_cases h1 : k < n + 1
  · rw [ite_eq_left h1, ite_eq_left h1]; rfl
  · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hk, ite_eq_right hk]; rfl

private theorem contract_forward (n s : ℕ) (g : (Fin (n + 1) → Bool) → Bool)
    (hdep : ∃ y : Fin n → Bool, g (Fin.snoc y false) ≠ g (Fin.snoc y true))
    (hsz : HasCircuitSize (n + 2) (targetFun n g) (s + 1)) :
    HasCircuitSize (n + 1) g s := by
  rcases hdep with ⟨y, hy⟩
  rcases hsz with ⟨C, hFan, hCsize, hCeval⟩
  set res := C.gates.foldl (compileGate n) (initEnv n, [])
  have hgs : ∀ gt ∈ C.gates, GateFanInTwo gt := hFan
  have hprops := foldl_compileGate_props n C.gates (initEnv n, [])
    (fun _ hg => nomatch hg) (initEnv_bounded n) (by simp [initEnv_length])
    (initEnv_getD_last n)
  rcases hprops with ⟨hResFan, hResLen, hResEnvLen, hResConst⟩
  simp only [List.length_nil, Nat.zero_add] at hResLen
  have hsound : ∀ u : Fin (n + 1) → Bool,
      evalSym (res.2.foldl wireStep (List.ofFn u)) (res.1.getD C.output (Sum.inl false)) = g u := by
    intro u
    have h1 := foldl_compileGate_sound n C.gates (initEnv n, [])
      (List.ofFn u) (List.ofFn (Fin.snoc u true)) hgs (fun _ hg => nomatch hg) (by simp)
      (by simp [initEnv_length]) (initEnv_bounded n) (initEnv_sound n u) C.output
    rw [h1, ← wires_eq_foldl]
    have h2 := hCeval (Fin.snoc u true)
    unfold Circuit.eval at h2
    rw [h2, targetFun_snoc_true]
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl c =>
      exfalso
      have hf := hsound (Fin.snoc y false)
      have ht := hsound (Fin.snoc y true)
      simp only [hout, evalSym] at hf ht
      exact hy (hf.symm.trans ht)
  | inr outIdx =>
      have hne_out : C.output ≠ n + 1 := by
        intro hEq
        rw [hEq, hResConst] at hout
        cases hout
      have hstrict : res.2.length < C.gates.length := by
        by_contra hnotlt
        have heqLen : res.2.length = ([] : List Gate).length + C.gates.length := by
          dsimp only [res] at hnotlt ⊢
          simp only [List.length_nil, Nat.zero_add]
          omega
        set u0 : Fin (n + 1) → Bool := Fin.snoc y true
        have hfalse := foldl_compileGate_nodrop n C.gates (initEnv n, [])
          (List.ofFn u0) (List.ofFn (Fin.snoc u0 false)) hgs
          (fun _ hg => nomatch hg) (by simp) (by simp [initEnv_length])
          (initEnv_bounded n) (by simp [initEnv_length]) (initEnv_getD_last n)
          heqLen (initEnv_sound_ne n u0 false) C.output hne_out
        have htrue := foldl_compileGate_nodrop n C.gates (initEnv n, [])
          (List.ofFn u0) (List.ofFn (Fin.snoc u0 true)) hgs
          (fun _ hg => nomatch hg) (by simp) (by simp [initEnv_length])
          (initEnv_bounded n) (by simp [initEnv_length]) (initEnv_getD_last n)
          heqLen (initEnv_sound_ne n u0 true) C.output hne_out
        have hevf := hCeval (Fin.snoc u0 false)
        have hevt := hCeval (Fin.snoc u0 true)
        unfold Circuit.eval at hevf hevt
        rw [wires_eq_foldl] at hevf hevt
        rw [hevf, targetFun_snoc_snoc] at hfalse
        rw [hevt, targetFun_snoc_snoc] at htrue
        exact hy (hfalse.symm.trans htrue)
      refine ⟨⟨res.2, outIdx⟩, hResFan, ?_, ?_⟩
      · simp only [Circuit.size] at hCsize ⊢
        omega
      · intro u
        have hu := hsound u
        simp only [hout, evalSym] at hu
        simpa [Circuit.eval, wires_eq_foldl] using hu

private theorem contract_backward (n s : ℕ) (g : (Fin (n + 1) → Bool) → Bool)
    (hsz : HasCircuitSize (n + 1) g s) :
    HasCircuitSize (n + 2) (targetFun n g) (s + 1) := by
  rcases hsz with ⟨C, hFan, hCsize, hCeval⟩
  refine ⟨expandCircuit n C, expandCircuit_fanInTwo n C hFan, ?_, ?_⟩
  · rw [expandCircuit_size]
    omega
  · intro x
    rw [expandCircuit_eval, hCeval]
    rfl

end PEqualNP.Outside.Meta175

theorem PEqualNP.Outside.L_meta_175 : ∀ (n s : ℕ) (g : (Fin (n + 1) → Bool) → Bool), (∃ y : Fin n → Bool, g (Fin.snoc y false) ≠ g (Fin.snoc y true)) → (PEqualNP.MetaComplexity.HasCircuitSize (n + 2) (fun x : Fin (n + 2) → Bool => g (Fin.snoc (fun i : Fin n => x i.castSucc.castSucc) (x (Fin.last n).castSucc && x (Fin.last (n + 1))))) (s + 1) ↔ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) g s) := by
  intro n s g hdep
  exact ⟨PEqualNP.Outside.Meta175.contract_forward n s g hdep,
    PEqualNP.Outside.Meta175.contract_backward n s g⟩
