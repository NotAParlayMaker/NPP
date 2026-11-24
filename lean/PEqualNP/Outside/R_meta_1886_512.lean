import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_1886_512
    (noExtraWire :
      let f10 : (Fin 10 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ E : Circuit, FanInTwo E → E.size ≤ 18 →
        ∃ x : Fin 10 → Bool, E.eval (List.ofFn x) ≠ f10 x)
    (firstAnd_residual :
      let f10 : (Fin 10 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ E : Circuit, FanInTwo E → E.size ≤ 17 →
        ∃ x : Fin 10 → Bool, (x 0 && x 1) = false ∧ E.eval (List.ofFn x) ≠ f10 x)
    (firstOr_used :
      let f10 : (Fin 10 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ D : Circuit, FanInTwo D → D.size ≤ 18 →
        (∃ g ∈ D.gates, (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 10) →
        ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 1]) ≠ f10 x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [if x3 = Bool.true then x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) else x6 (0 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C p b hC hs
  let n : ℕ := 10
  let f10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let r : ℕ → ℕ := fun i => if h : i < 10 then ((p ⟨i, h⟩ : Fin 10) : ℕ) else i
  let D : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map r⟩), r C.output⟩
  have hD : FanInTwo D := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hC g0 hg0
    exact ⟨h1, by simpa using h2⟩
  have hsD : D.size ≤ 18 := by
    change (C.gates.map _).length ≤ 18
    rw [List.length_map]; exact hs
  have snoc : ∀ (l : List Bool) (v : Bool) (i : ℕ),
      (l ++ [v]).getD i false = if i < l.length then l.getD i false
        else if i = l.length then v else false := by
    intro l v i
    split_ifs with h1 h2
    · exact List.getD_append _ _ _ _ h1
    · subst h2; simp
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, i - l.length = k + 1 := ⟨i - l.length - 1, by omega⟩
      rw [hk]; simp
  have step : ∀ (gs : List Gate) (w' w : List Bool),
      w'.length = w.length → 10 ≤ w.length →
      (∀ i, w'.getD (r i) false = w.getD i false) →
      ∀ i, ((gs.map (fun g => (⟨g.op, g.inputs.map r⟩ : Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (r i) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
    intro gs; induction gs with
    | nil => intro w' w _ _ hinv; exact hinv
    | cons g gs ih =>
      intro w' w hlen h10 hinv
      simp only [List.map_cons, List.foldl_cons]
      have hv : g.op.eval ((g.inputs.map r).map fun i => w'.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [List.map_map]; congr 1; exact List.map_congr_left (fun i _ => hinv i)
      rw [hv]
      apply ih
      · simp [hlen]
      · simp; omega
      · intro i
        rw [snoc, snoc, hlen]
        by_cases hi : i < 10
        · have hr : r i = ((p ⟨i, hi⟩ : Fin 10) : ℕ) := by simp [r, hi]
          have hpi : ((p ⟨i, hi⟩ : Fin 10) : ℕ) < w.length := by omega
          rw [hr]; simp only [hpi, show i < w.length by omega, ite_true]; rw [← hr]; exact hinv i
        · have hr : r i = i := by simp [r, hi]
          have hi' := hinv i; rw [hr] at hi' ⊢; split_ifs <;> first | exact hi' | rfl
  have key : ∀ (x : Fin 10 → Bool) (e : Bool),
      D.eval (List.ofFn x ++ [e]) = C.eval (List.ofFn (x ∘ p) ++ [e]) := by
    intro x e
    apply step C.gates
    · simp
    · simp
    · intro i
      by_cases hi : i < 10
      · have hr : r i = ((p ⟨i, hi⟩ : Fin 10) : ℕ) := by simp [r, hi]
        rw [hr, List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
        simp only [List.getElem_ofFn, Function.comp_apply, Fin.eta]
      · have hr : r i = i := by simp [r, hi]
        rw [hr, List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp
  let effInputs : Gate → List ℕ := fun g =>
    g.inputs.take (bif g.op.eval [false] then 1 else 2)
  have effInputs_not : ∀ g : Gate, g.op = .not → effInputs g = g.inputs.take 1 := by
    intro g h; simp [effInputs, h, GateOp.eval]
  have effInputs_and : ∀ g : Gate, g.op = .and → g.inputs.length ≤ 2 → effInputs g = g.inputs := by
    intro g h hlen; simp [effInputs, h, GateOp.eval, List.take_of_length_le hlen]
  have effInputs_or : ∀ g : Gate, g.op = .or → g.inputs.length ≤ 2 → effInputs g = g.inputs := by
    intro g h hlen; simp [effInputs, h, GateOp.eval, List.take_of_length_le hlen]
  have circuitWires_len : ∀ (gs : List Gate) (acc : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
        acc.length + gs.length := by
    intro gs; induction gs with
    | nil => intro acc; simp
    | cons g r ih => intro acc; simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]; omega
  have circuitWires_prefix : ∀ (gs : List Gate) (acc : List Bool) (w : ℕ), w < acc.length →
      (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) acc).getD w false =
        acc.getD w false := by
    intro gs; induction gs with
    | nil => intro acc w _; rfl
    | cons g r ih =>
      intro acc w hw; simp only [List.foldl_cons]
      have hlen : w < (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]).length := by simp; omega
      rw [ih _ w hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  let evalSym : List Bool → (Bool ⊕ ℕ) → Bool := fun ws s =>
    match s with
    | Sum.inl b => b
    | Sum.inr u => ws.getD u false
  let simplifyOne : ℕ → List (Bool ⊕ ℕ) → Gate → Option Gate × (Bool ⊕ ℕ) := fun k env g =>
    match g.op with
    | .not =>
      match g.inputs with
      | [] => (none, Sum.inl true)
      | u :: _ =>
        match env.getD u (Sum.inl false) with
        | Sum.inl b => (none, Sum.inl (!b))
        | Sum.inr u' => (some ⟨.not, [u']⟩, Sum.inr (n + k))
    | .and =>
      match g.inputs with
      | [] => (none, Sum.inl true)
      | [u] => (none, env.getD u (Sum.inl false))
      | [u1, u2] =>
        match env.getD u1 (Sum.inl false) with
        | Sum.inl false => (none, Sum.inl false)
        | Sum.inl true => (none, env.getD u2 (Sum.inl false))
        | Sum.inr a =>
          match env.getD u2 (Sum.inl false) with
          | Sum.inl false => (none, Sum.inl false)
          | Sum.inl true => (none, Sum.inr a)
          | Sum.inr b => (some ⟨.and, [a, b]⟩, Sum.inr (n + k))
      | _ => (none, Sum.inl false)
    | .or =>
      match g.inputs with
      | [] => (none, Sum.inl false)
      | [u] => (none, env.getD u (Sum.inl false))
      | [u1, u2] =>
        match env.getD u1 (Sum.inl false) with
        | Sum.inl true => (none, Sum.inl true)
        | Sum.inl false => (none, env.getD u2 (Sum.inl false))
        | Sum.inr a =>
          match env.getD u2 (Sum.inl false) with
          | Sum.inl true => (none, Sum.inl true)
          | Sum.inl false => (none, Sum.inr a)
          | Sum.inr b => (some ⟨.or, [a, b]⟩, Sum.inr (n + k))
      | _ => (none, Sum.inl false)
    | _ => (none, Sum.inl false)
  let simplifyGate : (List Gate × List (Bool ⊕ ℕ)) → Gate → (List Gate × List (Bool ⊕ ℕ)) := fun st g =>
    let r := simplifyOne st.1.length st.2 g
    (match r.1 with | none => st.1 | some ng => st.1 ++ [ng], st.2 ++ [r.2])
  have simplifyGate_env_len : ∀ st g, (simplifyGate st g).2.length = st.2.length + 1 := by
    intro st g; simp [simplifyGate]
  have simplifyGate_gs_le : ∀ st g, (simplifyGate st g).1.length ≤ st.1.length + 1 := by
    intro st g; dsimp only [simplifyGate]; cases (simplifyOne st.1.length st.2 g).1 <;> simp
  have simplifyGate_env_prefix : ∀ st g w, w < st.2.length →
      (simplifyGate st g).2.getD w (Sum.inl false) = st.2.getD w (Sum.inl false) := by
    intro st g w hw
    simp only [simplifyGate, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
  have simplifyFold_env_len : ∀ (gs : List Gate) st,
      (gs.foldl simplifyGate st).2.length = st.2.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro st; simp
    | cons g r ih => intro st; simp only [List.foldl_cons, ih, simplifyGate_env_len, List.length_cons]; omega
  have simplifyFold_env_prefix : ∀ (gs : List Gate) st w, w < st.2.length →
      (gs.foldl simplifyGate st).2.getD w (Sum.inl false) = st.2.getD w (Sum.inl false) := by
    intro gs
    induction gs with
    | nil => intro st w _; rfl
    | cons g r ih =>
      intro st w hw
      simp only [List.foldl_cons]
      have hlt : w < (simplifyGate st g).2.length := by rw [simplifyGate_env_len]; omega
      rw [ih _ w hlt, simplifyGate_env_prefix st g w hw]
  have simplifyGate_elim_of_const_input : ∀ st (g : Gate),
      (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ u ∈ effInputs g, ∀ b : Bool, st.2.getD u (Sum.inl false) = Sum.inl b →
      (simplifyGate st g).1.length = st.1.length := by
    intro st g hfan u hu b hconst
    dsimp only [simplifyGate, simplifyOne]
    rcases hfan.1 with hop | hop | hop
    · rw [effInputs_and g hop hfan.2] at hu
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu
      | cons u1 tl =>
        cases tl with
        | nil => simp [hop, hgin]
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · rw [hop]; dsimp only []; rw [hconst]; cases b <;> (cases st.2.getD u2 (Sum.inl false) with | inl b2 => cases b2 <;> rfl | inr _ => rfl)
            · rw [hop]; dsimp only []; rw [hconst]; cases st.2.getD u1 (Sum.inl false) with | inl b1 => cases b1 <;> (cases b <;> rfl) | inr _ => cases b <;> rfl
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · rw [effInputs_or g hop hfan.2] at hu
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu
      | cons u1 tl =>
        cases tl with
        | nil => simp [hop]
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            rw [hgin] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · rw [hop]; dsimp only []; rw [hconst]; cases b <;> (cases st.2.getD u2 (Sum.inl false) with | inl b2 => cases b2 <;> rfl | inr _ => rfl)
            · rw [hop]; dsimp only []; rw [hconst]; cases st.2.getD u1 (Sum.inl false) with | inl b1 => cases b1 <;> (cases b <;> rfl) | inr _ => cases b <;> rfl
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · rw [Set.mem_singleton_iff] at hop
      rw [effInputs_not g hop] at hu
      cases hgin : g.inputs with
      | nil => simp [hgin] at hu
      | cons u1 tl =>
        rw [hgin] at hu
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        subst hu
        rw [hop]; dsimp only []; rw [hconst]
  have simplifyGate_sound : ∀ st (g : Gate),
      (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ t ∈ st.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) →
      (∀ s ∈ st.2, ∀ u, s = Sum.inr u → u < n + st.1.length) →
      ∀ (x : Fin n → Bool) (ws : List Bool), ws.length = st.2.length →
      (∀ w < st.2.length, ws.getD w false = evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) (st.2.getD w (Sum.inl false))) →
      (∀ t ∈ (simplifyGate st g).1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
      (∀ s ∈ (simplifyGate st g).2, ∀ u, s = Sum.inr u → u < n + (simplifyGate st g).1.length) ∧
      ∀ w < st.2.length + 1,
        (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false =
          evalSym (Circuit.wires ⟨(simplifyGate st g).1, 0⟩ (List.ofFn x)) ((simplifyGate st g).2.getD w (Sum.inl false)) := by
    intro st g hfan hfanSt hbound x ws hwsLen heq
    have hread : ∀ u, ws.getD u false = evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) (st.2.getD u (Sum.inl false)) := by
      intro u
      by_cases hu : u < st.2.length
      · exact heq u hu
      · have h1 : ws.getD u false = false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ u)]
        have h2 : st.2.getD u (Sum.inl false) = Sum.inl false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : st.2.length ≤ u)]
        rw [h1, h2]
    have hgetBound : ∀ u k, st.2.getD u (Sum.inl false) = Sum.inr k → k < n + st.1.length := by
      intro u k hk
      by_cases hu : u < st.2.length
      · have hmem : st.2.getD u (Sum.inl false) ∈ st.2 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, Option.getD_some]
          exact List.getElem_mem hu
        exact hbound _ hmem k hk
      · have h2 : st.2.getD u (Sum.inl false) = Sum.inl false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : st.2.length ≤ u)]
        rw [h2] at hk; cases hk
    have hnoEmit : ∀ (a : Bool ⊕ ℕ),
        (∀ u, a = Sum.inr u → u < n + st.1.length) →
        g.op.eval (g.inputs.map fun i => ws.getD i false) =
          evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) a →
        (∀ t ∈ st.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
        (∀ s ∈ st.2 ++ [a], ∀ u, s = Sum.inr u → u < n + st.1.length) ∧
        ∀ w < st.2.length + 1,
          (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false =
            evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) ((st.2 ++ [a]).getD w (Sum.inl false)) := by
      intro a haB haE
      refine ⟨hfanSt, ?_, ?_⟩
      · intro s hs u hu
        rcases List.mem_append.mp hs with h1 | h2
        · exact hbound s h1 u hu
        · rw [List.mem_singleton.mp h2] at hu; exact haB u hu
      · intro w hw
        by_cases hlt : w < st.2.length
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < ws.length),
            List.getElem?_append_left hlt]
          simpa only [List.getD_eq_getElem?_getD] using heq w hlt
        · have hweq : w = st.2.length := by omega
          subst hweq
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega : ws.length ≤ st.2.length),
              List.getElem?_append_right le_rfl]
          simp only [hwsLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          exact haE
    have hEmit : ∀ (ng : Gate),
        (ng.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ ng.inputs.length ≤ 2) →
        g.op.eval (g.inputs.map fun i => ws.getD i false) =
          ng.op.eval (ng.inputs.map fun i => (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).getD i false) →
        (∀ t ∈ st.1 ++ [ng], t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
        (∀ s ∈ st.2 ++ [Sum.inr (n + st.1.length)], ∀ u, s = Sum.inr u → u < n + (st.1 ++ [ng]).length) ∧
        ∀ w < st.2.length + 1,
          (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false =
            evalSym (Circuit.wires ⟨st.1 ++ [ng], 0⟩ (List.ofFn x)) ((st.2 ++ [Sum.inr (n + st.1.length)]).getD w (Sum.inl false)) := by
      intro ng hngF hngE
      have hlenW : (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).length = n + st.1.length := by
        unfold Circuit.wires; rw [circuitWires_len, List.length_ofFn]
      have hWapp : Circuit.wires ⟨st.1 ++ [ng], 0⟩ (List.ofFn x) =
          Circuit.wires ⟨st.1, 0⟩ (List.ofFn x) ++
            [ng.op.eval (ng.inputs.map fun i => (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).getD i false)] := by
        unfold Circuit.wires; rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        rcases List.mem_append.mp ht with h1 | h2
        · exact hfanSt t h1
        · rw [List.mem_singleton.mp h2]; exact hngF
      · intro s hs u hu
        rw [List.length_append, List.length_singleton]
        rcases List.mem_append.mp hs with h1 | h2
        · have := hbound s h1 u hu; omega
        · rw [List.mem_singleton.mp h2] at hu; injection hu with hEq; omega
      · intro w hw
        by_cases hlt : w < st.2.length
        · have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false = ws.getD w false := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < ws.length)]
          have h2 : (st.2 ++ [Sum.inr (n + st.1.length)]).getD w (Sum.inl false) = st.2.getD w (Sum.inl false) := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
          rw [h1, h2, heq w hlt, hWapp]
          cases hsw : st.2.getD w (Sum.inl false) with
          | inl b => rfl
          | inr u =>
            have hu : u < n + st.1.length := hgetBound w u hsw
            simp only [evalSym, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).length)]
        · have hweq : w = st.2.length := by omega
          subst hweq
          have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD st.2.length false =
              g.op.eval (g.inputs.map fun i => ws.getD i false) := by
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega : ws.length ≤ st.2.length)]
            simp [hwsLen]
          have h2 : (st.2 ++ [Sum.inr (n + st.1.length)]).getD st.2.length (Sum.inl false) = Sum.inr (n + st.1.length) := by
            simp [List.getD_eq_getElem?_getD]
          rw [h1, h2, hWapp]
          simp only [evalSym, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega : (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)).length ≤ n + st.1.length)]
          simp only [hlenW, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          exact hngE
    rcases hfan.1 with hop | hop | hop
    · cases hgin : g.inputs with
      | nil =>
        have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
          dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
        rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by simp [hop, hgin, GateOp.eval, evalSym])
      | cons u1 tl =>
        cases tl with
        | nil =>
          have hres : simplifyGate st g = (st.1, st.2 ++ [st.2.getD u1 (Sum.inl false)]) := by
            dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
          rw [hres, ← hgin]; exact hnoEmit (st.2.getD u1 (Sum.inl false)) (hgetBound u1) (by
            simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact hread u1)
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            cases h1 : st.2.getD u1 (Sum.inl false) with
            | inl b1 =>
              cases b1
              · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
                  dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1]
                rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by
                  simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [hread u1, h1]; rfl)
              · cases h2 : st.2.getD u2 (Sum.inl false) with
                | inl b2 =>
                  cases b2
                  · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
                      dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                    rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by
                      simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                      rw [hread u1, hread u2, h1, h2]; rfl)
                  · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
                      dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                    rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by
                      simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                      rw [hread u1, hread u2, h1, h2]; rfl)
                | inr b =>
                  have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inr b]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inr b) (fun _ h => hgetBound u2 _ (h2.trans h)) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rw [hread u1, hread u2, h1, h2]; rfl)
            | inr a =>
              cases h2 : st.2.getD u2 (Sum.inl false) with
              | inl b2 =>
                cases b2
                · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rw [hread u1, hread u2, h1, h2]; simp [evalSym])
                · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inr a]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inr a) (fun _ h => hgetBound u1 _ (h1.trans h)) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rw [hread u1, hread u2, h1, h2]; simp [evalSym])
              | inr b =>
                have hres : simplifyGate st g = (st.1 ++ [⟨.and, [a, b]⟩], st.2 ++ [Sum.inr (n + st.1.length)]) := by
                  dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                rw [hres, ← hgin]; exact hEmit ⟨.and, [a, b]⟩ (by simp) (by
                  simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [hread u1, hread u2, h1, h2])
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · cases hgin : g.inputs with
      | nil =>
        have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
          dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
        rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by simp [hop, hgin, GateOp.eval, evalSym])
      | cons u1 tl =>
        cases tl with
        | nil =>
          have hres : simplifyGate st g = (st.1, st.2 ++ [st.2.getD u1 (Sum.inl false)]) := by
            dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
          rw [hres, ← hgin]; exact hnoEmit (st.2.getD u1 (Sum.inl false)) (hgetBound u1) (by
            simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact hread u1)
        | cons u2 tl2 =>
          cases tl2 with
          | nil =>
            cases h1 : st.2.getD u1 (Sum.inl false) with
            | inl b1 =>
              cases b1
              · cases h2 : st.2.getD u2 (Sum.inl false) with
                | inl b2 =>
                  cases b2
                  · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl false]) := by
                      dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                    rw [hres, ← hgin]; exact hnoEmit (Sum.inl false) (fun _ h => by cases h) (by
                      simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                      rw [hread u1, hread u2, h1, h2]; rfl)
                  · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
                      dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                    rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by
                      simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                      rw [hread u1, hread u2, h1, h2]; rfl)
                | inr b =>
                  have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inr b]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inr b) (fun _ h => hgetBound u2 _ (h2.trans h)) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    rw [hread u1, hread u2, h1, h2]; rfl)
              · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
                  dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1]
                rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by
                  simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1, h1]; rfl)
            | inr a =>
              cases h2 : st.2.getD u2 (Sum.inl false) with
              | inl b2 =>
                cases b2
                · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inr a]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inr a) (fun _ h => hgetBound u1 _ (h1.trans h)) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    rw [hread u1, hread u2, h1, h2]; simp [evalSym])
                · have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
                    dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                  rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by
                    simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    rw [hread u1, hread u2, h1, h2]; simp [evalSym])
              | inr b =>
                have hres : simplifyGate st g = (st.1 ++ [⟨.or, [a, b]⟩], st.2 ++ [Sum.inr (n + st.1.length)]) := by
                  dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1, h2]
                rw [hres, ← hgin]; exact hEmit ⟨.or, [a, b]⟩ (by simp) (by
                  simp only [hop, hgin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1, hread u2, h1, h2])
          | cons _ _ => rw [hgin] at hfan; simp at hfan
    · rw [Set.mem_singleton_iff] at hop
      cases hgin : g.inputs with
      | nil =>
        have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl true]) := by
          dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]
        rw [hres, ← hgin]; exact hnoEmit (Sum.inl true) (fun _ h => by cases h) (by simp [hop, hgin, GateOp.eval, evalSym])
      | cons u1 tl =>
        cases h1 : st.2.getD u1 (Sum.inl false) with
        | inl b1 =>
          have hres : simplifyGate st g = (st.1, st.2 ++ [Sum.inl (!b1)]) := by
            dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1]
          rw [hres, ← hgin]; exact hnoEmit (Sum.inl (!b1)) (fun _ h => by cases h) (by
            simp only [hop, hgin, GateOp.eval, List.map_cons, List.headD_cons]
            rw [hread u1, h1])
        | inr a =>
          have hres : simplifyGate st g = (st.1 ++ [⟨.not, [a]⟩], st.2 ++ [Sum.inr (n + st.1.length)]) := by
            dsimp only [simplifyGate, simplifyOne]; rw [hop, hgin]; simp only [h1]
          rw [hres, ← hgin]; exact hEmit ⟨.not, [a]⟩ (by simp) (by
            simp only [hop, hgin, GateOp.eval, List.map_cons, List.headD_cons]
            rw [hread u1, h1])
  have simplifyFold_sound_gen : ∀ (gs : List Gate) (st0 : List Gate × List (Bool ⊕ ℕ)),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ t ∈ st0.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) →
      (∀ s ∈ st0.2, ∀ u, s = Sum.inr u → u < n + st0.1.length) →
      ∀ (x : Fin n → Bool) (ws : List Bool), ws.length = st0.2.length →
      (∀ w < st0.2.length, ws.getD w false = evalSym (Circuit.wires ⟨st0.1, 0⟩ (List.ofFn x)) (st0.2.getD w (Sum.inl false))) →
      let st1 := gs.foldl simplifyGate st0
      (∀ t ∈ st1.1, t.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ t.inputs.length ≤ 2) ∧
      (∀ s ∈ st1.2, ∀ u, s = Sum.inr u → u < n + st1.1.length) ∧
      ∀ w < st0.2.length + gs.length,
        (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) ws).getD w false =
          evalSym (Circuit.wires ⟨st1.1, 0⟩ (List.ofFn x)) (st1.2.getD w (Sum.inl false)) := by
    intro gs; induction gs with
    | nil =>
      intro st0 _ hfan0 hbound0 x ws _ heq0
      exact ⟨hfan0, hbound0, fun w hw => heq0 w (by simpa using hw)⟩
    | cons g r ih =>
      intro st0 hfanG hfan0 hbound0 x ws hwsLen heq0
      have hstep := simplifyGate_sound st0 g (hfanG g (by simp)) hfan0 hbound0 x ws hwsLen heq0
      have hlen1 : (ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]).length = (simplifyGate st0 g).2.length := by
        rw [List.length_append, List.length_singleton, hwsLen, simplifyGate_env_len]
      have hrec := ih (simplifyGate st0 g) (fun t ht => hfanG t (by simp [ht])) hstep.1 hstep.2.1 x
        (ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]) hlen1
        (fun w hw => hstep.2.2 w (by rw [simplifyGate_env_len] at hw; exact hw))
      refine ⟨hrec.1, hrec.2.1, fun w hw => ?_⟩
      simp only [List.foldl_cons]
      exact hrec.2.2 w (by rw [simplifyGate_env_len]; simp at hw; omega)
  have fold_len_le : ∀ (gs : List Gate) (st0 : List Gate × List (Bool ⊕ ℕ)),
      (gs.foldl simplifyGate st0).1.length ≤ st0.1.length + gs.length := by
    intro gs; induction gs with
    | nil => intro st0; simp
    | cons g r ih =>
      intro st0; simp only [List.foldl_cons]
      have h1 := ih (simplifyGate st0 g)
      have h2 := simplifyGate_gs_le st0 g
      simp; omega
  by_cases hused10 : ∃ g ∈ D.gates, (effInputs g).contains 10
  · cases b with
    | false =>
      obtain ⟨x, hx⟩ := firstOr_used D hD hsD hused10
      exact ⟨x, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [← key x (x 0 || x 1)]; exact hx⟩
    | true =>
      obtain ⟨g10, hg10, hcon10⟩ := hused10
      obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg10
      have hmem10 : 10 ∈ effInputs D.gates[k] := by rw [hgk]; exact List.contains_iff_mem.mp hcon10
      let env0 : List (Bool ⊕ ℕ) := (List.range 10).map Sum.inr ++ [Sum.inl false]
      let st := D.gates.foldl simplifyGate ([], env0)
      have henv0_len : env0.length = 11 := by simp [env0]
      have henv0_bound : ∀ s ∈ env0, ∀ u, s = Sum.inr u → u < n + ([] : List Gate).length := by
        intro s hs u hu; dsimp only [env0] at hs
        rcases List.mem_append.mp hs with h1 | h2
        · obtain ⟨j, hj, hjeq⟩ := List.mem_map.mp h1; rw [List.mem_range] at hj
          rw [← hjeq] at hu; cases hu; dsimp only [n]; simp; omega
        · rw [List.mem_singleton.mp h2] at hu; cases hu
      have henv0_eq : ∀ (x : Fin 10 → Bool) (w : ℕ), w < env0.length →
          (List.ofFn x ++ [false]).getD w false =
            evalSym (Circuit.wires ⟨[], 0⟩ (List.ofFn x)) (env0.getD w (Sum.inl false)) := by
        intro x w hw; rw [henv0_len] at hw
        by_cases hlt : w < 10
        · have h2 : env0.getD w (Sum.inl false) = Sum.inr w := by
            dsimp only [env0]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hlt]; rfl
          rw [h2]; dsimp only [evalSym, Circuit.wires]
          rw [List.foldl_nil, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt])]
        · have hw10 : w = 10 := by omega
          subst hw10
          have h1 : (List.ofFn x ++ [false]).getD 10 false = false := by
            simp [List.getD_eq_getElem?_getD]
          have h2 : env0.getD 10 (Sum.inl false) = Sum.inl false := by
            dsimp only [env0]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
          rw [h1, h2]
      have hstSound := simplifyFold_sound_gen D.gates ([], env0) hD (fun _ h => by simp at h) henv0_bound
      have hstFan : FanInTwo ⟨st.1, 0⟩ :=
        (hstSound (fun _ => false) (List.ofFn (fun _ => false) ++ [false]) (by simp [env0]) (henv0_eq (fun _ => false))).1
      have hstEq : ∀ (x : Fin 10 → Bool) (w : ℕ), w < 11 + D.gates.length →
          (D.wires (List.ofFn x ++ [false])).getD w false =
            evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) (st.2.getD w (Sum.inl false)) := by
        intro x w hw
        exact (hstSound x (List.ofFn x ++ [false]) (by simp [env0]) (henv0_eq x)).2.2 w (by rw [henv0_len]; exact hw)
      have hstSz : st.1.length ≤ 17 := by
        have hsplit : D.gates = D.gates.take k ++ D.gates[k] :: D.gates.drop (k + 1) := by
          have h1 := (List.take_append_drop k D.gates).symm
          have h2 := List.drop_eq_getElem_cons hk
          rw [h2] at h1; exact h1
        set stPre := (D.gates.take k).foldl simplifyGate ([], env0)
        have hPreLen : stPre.1.length ≤ k := by
          have := fold_len_le (D.gates.take k) ([], env0)
          rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this; simpa using this
        have hPreEnv10 : stPre.2.getD 10 (Sum.inl false) = Sum.inl false := by
          dsimp only [stPre]
          rw [simplifyFold_env_prefix (D.gates.take k) ([], env0) 10 (by simp [env0])]
          dsimp only [env0]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
        have hElim : (simplifyGate stPre D.gates[k]).1.length = stPre.1.length :=
          simplifyGate_elim_of_const_input stPre D.gates[k] (hD _ (List.getElem_mem hk)) 10 hmem10 false hPreEnv10
        have hEnd : st = (D.gates.drop (k + 1)).foldl simplifyGate (simplifyGate stPre D.gates[k]) := by
          dsimp only [st]; conv_lhs => rw [hsplit]
          rw [List.foldl_append, List.foldl_cons]
        rw [hEnd]
        have hDrop := fold_len_le (D.gates.drop (k + 1)) (simplifyGate stPre D.gates[k])
        rw [hElim, List.length_drop] at hDrop
        unfold Circuit.size at hsD; omega
      by_cases houtLt : D.output < 11 + D.gates.length
      · cases houtSym : st.2.getD D.output (Sum.inl false) with
        | inl c =>
          cases c
          · refine ⟨fun i => decide (i = 2 ∨ i = 3), ?_⟩
            rw [← key]; simp only [↓reduceIte]
            have h01 : (decide ((0 : Fin 10) = 2 ∨ (0 : Fin 10) = 3) && decide ((1 : Fin 10) = 2 ∨ (1 : Fin 10) = 3)) = false := by decide
            rw [h01]; unfold Circuit.eval; rw [hstEq _ D.output houtLt, houtSym]
            dsimp only [evalSym]; decide
          · refine ⟨fun _ => false, ?_⟩
            rw [← key]; simp only [↓reduceIte, Bool.and_self]
            unfold Circuit.eval; rw [hstEq _ D.output houtLt, houtSym]
            dsimp only [evalSym]; decide
        | inr out' =>
          obtain ⟨x, hx01, hne⟩ := firstAnd_residual ⟨st.1, out'⟩ hstFan hstSz
          refine ⟨x, ?_⟩
          rw [← key]; simp only [↓reduceIte]
          conv_lhs => rw [hx01]
          unfold Circuit.eval at hne ⊢
          rw [hstEq x D.output houtLt, houtSym]
          dsimp only [evalSym]
          exact hne
      · refine ⟨fun i => decide (i = 2 ∨ i = 3), ?_⟩
        rw [← key]; simp only [↓reduceIte]
        have h01 : (decide ((0 : Fin 10) = 2 ∨ (0 : Fin 10) = 3) && decide ((1 : Fin 10) = 2 ∨ (1 : Fin 10) = 3)) = false := by decide
        rw [h01]; unfold Circuit.eval Circuit.wires
        have hlenW : (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (fun i : Fin 10 => decide (i = 2 ∨ i = 3)) ++ [false])).length = 11 + D.gates.length := by
          rw [circuitWires_len]; simp
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlenW]; omega)]
        decide
  · -- Wire 10 is NOT read by any gate in D!
    push Not at hused10
    have hnot10 : ∀ g ∈ D.gates, 10 ∉ effInputs g := fun g hg h => hused10 g hg (List.contains_iff_mem.mpr h)
    have hgate_eff : ∀ (g : Gate), (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        ∀ (f1 f2 : ℕ → Bool), (∀ u ∈ effInputs g, f1 u = f2 u) →
        g.op.eval (g.inputs.map f1) = g.op.eval (g.inputs.map f2) := by
      intro g hfg f1 f2 heq
      rcases hfg.1 with h | h | h
      · rw [effInputs_and g h hfg.2] at heq; rw [h]; congr 1; exact List.map_congr_left heq
      · rw [effInputs_or g h hfg.2] at heq; rw [h]; congr 1; exact List.map_congr_left heq
      · rw [Set.mem_singleton_iff] at h; rw [effInputs_not g h] at heq
        cases hgin : g.inputs with
        | nil => simp [h, hgin, GateOp.eval]
        | cons u tl =>
          have hu : u ∈ (u :: tl).take 1 := by simp
          rw [hgin] at heq; simp [h, hgin, GateOp.eval, heq u hu]
    have hindep : ∀ (x : Fin 10 → Bool) (e : Bool) (w : ℕ), w ≠ 10 →
        (D.wires (List.ofFn x ++ [e])).getD w false = (D.wires (List.ofFn x ++ [false])).getD w false := by
      intro x e
      suffices hrec : ∀ (gs : List Gate) (a1 a2 : List Bool),
          (∀ g ∈ gs, g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2 ∧ 10 ∉ effInputs g) →
          a1.length = a2.length → 11 ≤ a1.length →
          (∀ w, w ≠ 10 → a1.getD w false = a2.getD w false) →
          ∀ w, w ≠ 10 →
            (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) a1).getD w false =
            (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) a2).getD w false by
        apply hrec D.gates (List.ofFn x ++ [e]) (List.ofFn x ++ [false])
          (fun g hg => ⟨(hD g hg).1, (hD g hg).2, hnot10 g hg⟩) (by simp) (by simp)
        intro w hw
        by_cases hlt : w < 10
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp [hlt]), List.getElem?_append_left (by simp [hlt])]
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      intro gs; induction gs with
      | nil => intro a1 a2 _ _ _ hinv; exact hinv
      | cons g r ih =>
        intro a1 a2 hgs hlen h11 hinv
        simp only [List.foldl_cons]
        have hg := hgs g (by simp)
        have hval : g.op.eval (g.inputs.map fun i => a1.getD i false) = g.op.eval (g.inputs.map fun i => a2.getD i false) :=
          hgate_eff g ⟨hg.1, hg.2.1⟩ _ _ (fun u hu => hinv u (fun heq => hg.2.2 (heq ▸ hu)))
        rw [hval]
        apply ih _ _ (fun t ht => hgs t (by simp [ht])) (by simp [hlen]) (by simp; omega)
        intro w hw
        rw [snoc, snoc, hlen]
        split_ifs <;> first | exact hinv w hw | rfl
    by_cases hout10 : D.output = 10
    · refine ⟨fun i => decide (i = 2 ∨ i = 3), ?_⟩
      rw [← key]; unfold Circuit.eval Circuit.wires
      rw [hout10, circuitWires_prefix D.gates _ 10 (by simp)]
      cases b <;> decide
    · -- Wire 10 is unused and not output: compile D with env0 to get E of size <= 18 computing D(x ++ [false]) = D(x ++ [e])!
      let env0 : List (Bool ⊕ ℕ) := (List.range 10).map Sum.inr ++ [Sum.inl false]
      let st := D.gates.foldl simplifyGate ([], env0)
      have henv0_len : env0.length = 11 := by simp [env0]
      have henv0_bound : ∀ s ∈ env0, ∀ u, s = Sum.inr u → u < n + ([] : List Gate).length := by
        intro s hs u hu; dsimp only [env0] at hs
        rcases List.mem_append.mp hs with h1 | h2
        · obtain ⟨j, hj, hjeq⟩ := List.mem_map.mp h1; rw [List.mem_range] at hj
          rw [← hjeq] at hu; cases hu; dsimp only [n]; simp; omega
        · rw [List.mem_singleton.mp h2] at hu; cases hu
      have henv0_eq : ∀ (x : Fin 10 → Bool) (w : ℕ), w < env0.length →
          (List.ofFn x ++ [false]).getD w false =
            evalSym (Circuit.wires ⟨[], 0⟩ (List.ofFn x)) (env0.getD w (Sum.inl false)) := by
        intro x w hw; rw [henv0_len] at hw
        by_cases hlt : w < 10
        · have h2 : env0.getD w (Sum.inl false) = Sum.inr w := by
            dsimp only [env0]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hlt]; rfl
          rw [h2]; dsimp only [evalSym, Circuit.wires]
          rw [List.foldl_nil, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt])]
        · have hw10 : w = 10 := by omega
          subst hw10
          have h1 : (List.ofFn x ++ [false]).getD 10 false = false := by simp [List.getD_eq_getElem?_getD]
          have h2 : env0.getD 10 (Sum.inl false) = Sum.inl false := by
            dsimp only [env0]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
          rw [h1, h2]
      have hstSound := simplifyFold_sound_gen D.gates ([], env0) hD (fun _ h => by simp at h) henv0_bound
      have hstFan : FanInTwo ⟨st.1, 0⟩ :=
        (hstSound (fun _ => false) (List.ofFn (fun _ => false) ++ [false]) (by simp [env0]) (henv0_eq (fun _ => false))).1
      have hstEq : ∀ (x : Fin 10 → Bool) (w : ℕ), w < 11 + D.gates.length →
          (D.wires (List.ofFn x ++ [false])).getD w false =
            evalSym (Circuit.wires ⟨st.1, 0⟩ (List.ofFn x)) (st.2.getD w (Sum.inl false)) := by
        intro x w hw
        exact (hstSound x (List.ofFn x ++ [false]) (by simp [env0]) (henv0_eq x)).2.2 w (by rw [henv0_len]; exact hw)
      have hstSz : st.1.length ≤ 18 := by
        have h1 := fold_len_le D.gates ([], env0)
        unfold Circuit.size at hsD
        dsimp only [st]
        simp only [List.length_nil, Nat.zero_add] at h1
        omega
      by_cases houtLt : D.output < 11 + D.gates.length
      · cases houtSym : st.2.getD D.output (Sum.inl false) with
        | inl c =>
          cases c
          · refine ⟨fun i => decide (i = 2 ∨ i = 3), ?_⟩
            rw [← key]; unfold Circuit.eval; rw [hindep _ _ D.output hout10, hstEq _ D.output houtLt, houtSym]
            dsimp only [evalSym]; decide
          · refine ⟨fun _ => false, ?_⟩
            rw [← key]; unfold Circuit.eval; rw [hindep _ _ D.output hout10, hstEq _ D.output houtLt, houtSym]
            dsimp only [evalSym]; decide
        | inr out' =>
          obtain ⟨x, hne⟩ := noExtraWire ⟨st.1, out'⟩ hstFan hstSz
          refine ⟨x, ?_⟩
          rw [← key]; unfold Circuit.eval at hne ⊢
          rw [hindep x _ D.output hout10, hstEq x D.output houtLt, houtSym]
          dsimp only [evalSym]
          exact hne
      · refine ⟨fun i => decide (i = 2 ∨ i = 3), ?_⟩
        rw [← key]; unfold Circuit.eval; rw [hindep _ _ D.output hout10]
        unfold Circuit.wires
        have hlenW : (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (fun i : Fin 10 => decide (i = 2 ∨ i = 3)) ++ [false])).length = 11 + D.gates.length := by
          rw [circuitWires_len]; simp
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlenW]; omega)]
        decide
