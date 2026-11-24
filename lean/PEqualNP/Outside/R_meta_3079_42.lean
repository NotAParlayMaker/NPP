import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3079_42
    (hG6 : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)) 12)
    (h41 : ¬ ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧
      (∀ g ∈ D.gates, 4 ∉ g.inputs) ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x 4 || x 1]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (hPairsA : ∀ p ∈ ([(0, 3), (0, 1), (0, 2), (0, 6), (3, 1), (3, 2), (3, 6), (1, 5)] : List (Fin 9 × Fin 9)),
      ¬ ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧
        (D.gates.filter (fun g => decide (4 ∈ g.inputs))).length = 1 ∧
        (∀ g ∈ D.gates, 4 ∈ g.inputs → g.op = GateOp.or) ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
           (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
           (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (hPairsB : ∀ p ∈ ([(2, 8), (6, 7), (1, 2), (1, 8), (1, 6), (1, 7), (2, 6), (2, 7)] : List (Fin 9 × Fin 9)),
      ¬ ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧
        (D.gates.filter (fun g => decide (4 ∈ g.inputs))).length = 1 ∧
        (∀ g ∈ D.gates, 4 ∈ g.inputs → g.op = GateOp.or) ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
           (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
           (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2 ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨ (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  classical
  intro x1 x2 x3 x4 hlen hne9 hx1_25 hx2_25 _
  by_contra hno
  let f9 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let f8 : (Fin 8 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
  let readR : List Bool → Fin 26 → Bool := fun w i =>
    if i.val = 25 then true else w.getD i.val false
  let stepR : List Bool → Fin 3 × Fin 26 × Fin 26 → List Bool := fun w g =>
    w ++ [if g.1.val = 0 then readR w g.2.1 && readR w g.2.2
          else if g.1.val = 1 then readR w g.2.1 || readR w g.2.2
          else !readR w g.2.1]
  -- 1. Convert ¬∃ x10 < 512 ... into ∀ x : Fin 9 → Bool.
  let enc : ∀ k : ℕ, (Fin k → Bool) → ℕ :=
    Nat.rec (fun _ => 0) (fun _ ih f => (if f 0 then 1 else 0) + 2 * ih (fun i => f i.succ))
  have enc_lt : ∀ k (f : Fin k → Bool), enc k f < 2 ^ k := by
    intro k
    induction k with
    | zero => intro f; simp [enc]
    | succ k ih =>
      intro f
      have h := ih (fun i => f i.succ)
      change (if f 0 then 1 else 0) + 2 * enc k (fun i => f i.succ) < 2 ^ (k + 1)
      rw [pow_succ]
      cases f 0 <;> simp <;> omega
  have enc_bit : ∀ k (f : Fin k → Bool) (i : Fin k), (enc k f).testBit i.val = f i := by
    intro k
    induction k with
    | zero => intro f i; exact i.elim0
    | succ k ih =>
      intro f i
      cases i using Fin.cases with
      | zero =>
        change ((if f 0 then 1 else 0) + 2 * enc k (fun j => f j.succ)).testBit 0 = f 0
        cases h0 : f 0 <;> simp [Nat.testBit_zero]
      | succ j =>
        change ((if f 0 then 1 else 0) + 2 * enc k (fun m => f m.succ)).testBit (j.val + 1) = f j.succ
        rw [Nat.testBit_succ]
        have hdiv : ((if f 0 then 1 else 0) + 2 * enc k (fun m => f m.succ)) / 2 =
            enc k (fun m => f m.succ) := by
          cases f 0 <;> simp <;> omega
        rw [hdiv]
        exact ih (fun m => f m.succ) j
  have htarget_eq : ∀ x : Fin 9 → Bool,
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) = f9 x := by
    intro x
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 ||
      (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 ||
        (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = _
    simp [f9, Bool.or_assoc]
  have hraw : ∀ x : Fin 9 → Bool,
      (List.foldl stepR (List.ofFn x ++ [x 0 || x 4]) (((1 : Fin 3), x1, x2) :: x4)).getD x3.val false =
        f9 x := by
    intro x
    by_contra hne
    apply hno
    refine ⟨enc 9 x, by simpa using enc_lt 9 x, ?_⟩
    have hbit : ∀ i : Fin 9, (enc 9 x).testBit i.val = x i := enc_bit 9 x
    dsimp only
    simp only [hbit]
    rw [htarget_eq]
    exact hne
  -- Basic circuit evaluation helpers.
  let stepC : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_stepC_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepC w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g rest ih =>
      intro w; rw [List.foldl_cons, ih]; simp [stepC]; omega
  have stepC_snoc_lt : ∀ (w : List Bool) (g : Gate) (i : ℕ), i < w.length →
      (stepC w g).getD i false = w.getD i false := by
    intro w g i hi
    simp [stepC, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have stepC_snoc_self : ∀ (w : List Bool) (g : Gate),
      (stepC w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro w g
    simp [stepC, List.getD_eq_getElem?_getD]
  let CleanGate : Gate → Prop := fun g =>
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)
  have clean_to_fan : ∀ C : Circuit, (∀ g ∈ C.gates, CleanGate g) → FanInTwo C := by
    intro C hc g hg
    rcases hc g hg with ⟨ho | ho, hl⟩ | ⟨ho, hl⟩ <;> simp [ho, hl]
  have heval_and : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := fun a b => by
    cases a <;> cases b <;> rfl
  have heval_or : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := fun a b => by
    cases a <;> cases b <;> rfl
  have heval_not : ∀ a : Bool, GateOp.not.eval [a] = !a := fun a => by
    cases a <;> rfl
  -- 2. Shared constant-propagating single-op emitter (op: 0=AND, 1=OR, 2=NOT).
  let evalS : List Bool → Sum Bool ℕ → Bool := fun ws v =>
    Sum.rec (motive := fun _ => Bool) (fun b => b) (fun k => ws.getD k false) v
  let emitOp : ℕ → List Gate → List (Sum Bool ℕ) → ℕ → Sum Bool ℕ → Sum Bool ℕ →
      List Gate × List (Sum Bool ℕ) := fun base gs env op va vb =>
    if op = 0 then
      Sum.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
        (fun ba => Bool.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
          (gs, env ++ [Sum.inl false]) (gs, env ++ [vb]) ba)
        (fun u => Sum.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
          (fun bb => Bool.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
            (gs, env ++ [Sum.inl false]) (gs, env ++ [Sum.inr u]) bb)
          (fun v => (gs ++ [⟨GateOp.and, [u, v]⟩], env ++ [Sum.inr (base + gs.length)]))
          vb)
        va
    else if op = 1 then
      Sum.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
        (fun ba => Bool.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
          (gs, env ++ [vb]) (gs, env ++ [Sum.inl true]) ba)
        (fun u => Sum.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
          (fun bb => Bool.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
            (gs, env ++ [Sum.inr u]) (gs, env ++ [Sum.inl true]) bb)
          (fun v => (gs ++ [⟨GateOp.or, [u, v]⟩], env ++ [Sum.inr (base + gs.length)]))
          vb)
        va
    else
      Sum.rec (motive := fun _ => List Gate × List (Sum Bool ℕ))
        (fun b => (gs, env ++ [Sum.inl (!b)]))
        (fun u => (gs ++ [⟨GateOp.not, [u]⟩], env ++ [Sum.inr (base + gs.length)]))
        va
  have emitOp_inv : ∀ (base : ℕ) (gs : List Gate) (env : List (Sum Bool ℕ))
      (op : ℕ) (va vb : Sum Bool ℕ), op < 3 →
      (∀ gt ∈ gs, CleanGate gt) →
      (∀ (j : ℕ) (hj : j < gs.length), ∀ w ∈ gs[j].inputs, w < base + j) →
      (∀ v ∈ env, ∀ k, v = Sum.inr k → k < base + gs.length) →
      (∀ k, va = Sum.inr k → k < base + gs.length) →
      (∀ k, vb = Sum.inr k → k < base + gs.length) →
      let st' := emitOp base gs env op va vb
      (∀ gt ∈ st'.1, CleanGate gt) ∧
      (∀ (j : ℕ) (hj : j < st'.1.length), ∀ w ∈ st'.1[j].inputs, w < base + j) ∧
      (∀ v ∈ st'.2, ∀ k, v = Sum.inr k → k < base + st'.1.length) ∧
      st'.1.length ≤ gs.length + 1 ∧
      (((∃ b, va = Sum.inl b) ∨ (op ≠ 2 ∧ ∃ b, vb = Sum.inl b)) → st'.1.length = gs.length) ∧
      ((va = Sum.inl false ∨ (op = 0 ∧ vb = Sum.inl false)) → op ≠ 1 →
        ∃ b, st'.2.getD env.length (Sum.inl false) = Sum.inl b) ∧
      st'.2.length = env.length + 1 ∧
      (∀ j < env.length, st'.2.getD j (Sum.inl false) = env.getD j (Sum.inl false)) ∧
      ∀ (cw0 : List Bool), cw0.length = base →
        (∀ j < env.length,
          evalS (st'.1.foldl stepC cw0) (st'.2.getD j (Sum.inl false)) =
            evalS (gs.foldl stepC cw0) (env.getD j (Sum.inl false))) ∧
        evalS (st'.1.foldl stepC cw0) (st'.2.getD env.length (Sum.inl false)) =
          (if op = 0 then evalS (gs.foldl stepC cw0) va && evalS (gs.foldl stepC cw0) vb
           else if op = 1 then evalS (gs.foldl stepC cw0) va || evalS (gs.foldl stepC cw0) vb
           else !evalS (gs.foldl stepC cw0) va) := by
    intro base gs env op va vb hop hcl hrb hbd hva_bd hvb_bd
    have hbd_no : ∀ vnew, (∀ k, vnew = Sum.inr k → k < base + gs.length) →
        ∀ v ∈ env ++ [vnew], ∀ k, v = Sum.inr k → k < base + gs.length := by
      intro vnew hv v hm k hk
      rcases List.mem_append.mp hm with h1 | h2
      · exact hbd v h1 k hk
      · rw [List.mem_singleton.mp h2] at hk; exact hv k hk
    have hbd_yes : ∀ gt : Gate,
        ∀ v ∈ env ++ [Sum.inr (base + gs.length)], ∀ k, v = Sum.inr k → k < base + (gs ++ [gt]).length := by
      intro gt v hm k hk
      simp only [List.length_append, List.length_singleton]
      rcases List.mem_append.mp hm with h1 | h2
      · have := hbd v h1 k hk; omega
      · rw [List.mem_singleton.mp h2] at hk; cases hk; omega
    have hcl_yes : ∀ gt : Gate, CleanGate gt → ∀ g' ∈ gs ++ [gt], CleanGate g' := by
      intro gt hgt g' hg'
      rcases List.mem_append.mp hg' with h1 | h2
      · exact hcl g' h1
      · rw [List.mem_singleton.mp h2]; exact hgt
    have hrb_yes : ∀ gt : Gate, (∀ w ∈ gt.inputs, w < base + gs.length) →
        ∀ (j : ℕ) (hj : j < (gs ++ [gt]).length), ∀ w ∈ (gs ++ [gt])[j].inputs, w < base + j := by
      intro gt hgt j hj w hw
      by_cases hlt : j < gs.length
      · rw [List.getElem_append_left hlt] at hw; exact hrb j hlt w hw
      · have heq : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
        subst heq
        rw [List.getElem_append_right (le_refl _)] at hw
        simp only [Nat.sub_self, List.getElem_cons_zero] at hw
        exact hgt w hw
    have hget_lt : ∀ (v : Sum Bool ℕ) (j : ℕ), j < env.length →
        (env ++ [v]).getD j (Sum.inl false) = env.getD j (Sum.inl false) :=
      fun v j hj => List.getD_append _ _ _ _ hj
    have hget_last : ∀ (v : Sum Bool ℕ), (env ++ [v]).getD env.length (Sum.inl false) = v := by
      intro v; simp [List.getD_eq_getElem?_getD]
    have hno_ev : ∀ (vnew : Sum Bool ℕ) (cw0 : List Bool),
        (∀ j < env.length,
          evalS (gs.foldl stepC cw0) ((env ++ [vnew]).getD j (Sum.inl false)) =
            evalS (gs.foldl stepC cw0) (env.getD j (Sum.inl false))) ∧
        evalS (gs.foldl stepC cw0) ((env ++ [vnew]).getD env.length (Sum.inl false)) =
          evalS (gs.foldl stepC cw0) vnew := by
      intro vnew cw0
      exact ⟨fun j hj => by rw [hget_lt _ _ hj], by rw [hget_last]⟩
    have hyes_ev : ∀ (gt : Gate) (cw0 : List Bool), cw0.length = base →
        (∀ j < env.length,
          evalS ((gs ++ [gt]).foldl stepC cw0) ((env ++ [Sum.inr (base + gs.length)]).getD j (Sum.inl false)) =
            evalS (gs.foldl stepC cw0) (env.getD j (Sum.inl false))) ∧
        evalS ((gs ++ [gt]).foldl stepC cw0) ((env ++ [Sum.inr (base + gs.length)]).getD env.length (Sum.inl false)) =
          gt.op.eval (gt.inputs.map fun i => (gs.foldl stepC cw0).getD i false) := by
      intro gt cw0 hcw
      have hl : (gs.foldl stepC cw0).length = base + gs.length := by rw [foldl_stepC_len, hcw]
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [hget_lt _ _ hj]
        cases hv : env.getD j (Sum.inl false) with
        | inl b => rfl
        | inr k =>
          have hk : k < base + gs.length := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at hv
            exact hbd env[j] (List.getElem_mem hj) k hv
          simp only [evalS]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact stepC_snoc_lt _ gt k (by omega)
      · rw [hget_last]
        simp only [evalS]
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hl, stepC_snoc_self]
    by_cases h0 : op = 0
    · subst h0
      cases va with
      | inl ba =>
        cases ba with
        | false =>
          dsimp only [emitOp]; simp only [ite_true]
          refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
            fun _ => trivial, fun _ _ => ⟨false, hget_last _⟩, by simp, hget_lt _, fun cw0 _ => ?_⟩
          simpa [evalS] using hno_ev (Sum.inl false) cw0
        | true =>
          cases vb with
          | inl bb =>
            cases bb with
            | false =>
              dsimp only [emitOp]; simp only [ite_true]
              refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
                fun _ => trivial, fun _ _ => ⟨false, hget_last _⟩, by simp, hget_lt _, fun cw0 _ => ?_⟩
              simpa [evalS] using hno_ev (Sum.inl false) cw0
            | true =>
              dsimp only [emitOp]; simp only [ite_true]
              refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
                fun _ => trivial, (fun h _ => by rcases h with h | ⟨_, h⟩ <;> cases h), by simp, hget_lt _, fun cw0 _ => ?_⟩
              simpa [evalS] using hno_ev (Sum.inl true) cw0
          | inr vb =>
            dsimp only [emitOp]; simp only [ite_true]
            refine ⟨hcl, hrb, hbd_no _ hvb_bd, Nat.le_succ _,
              fun _ => trivial, (fun h _ => by rcases h with h | ⟨_, h⟩ <;> cases h), by simp, hget_lt _, fun cw0 _ => ?_⟩
            simpa [evalS] using hno_ev (Sum.inr vb) cw0
      | inr ua =>
        cases vb with
        | inl bb =>
          cases bb with
          | false =>
            dsimp only [emitOp]; simp only [ite_true]
            refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
              fun _ => trivial, fun _ _ => ⟨false, hget_last _⟩, by simp, hget_lt _, fun cw0 _ => ?_⟩
            simpa [evalS] using hno_ev (Sum.inl false) cw0
          | true =>
            dsimp only [emitOp]; simp only [ite_true]
            refine ⟨hcl, hrb, hbd_no _ hva_bd, Nat.le_succ _,
              fun _ => trivial, (fun h _ => by rcases h with h | ⟨_, h⟩ <;> cases h), by simp, hget_lt _, fun cw0 _ => ?_⟩
            simpa [evalS] using hno_ev (Sum.inr ua) cw0
        | inr vb =>
          dsimp only [emitOp]; simp only [ite_true]
          refine ⟨hcl_yes _ (Or.inl ⟨Or.inl rfl, rfl⟩),
            hrb_yes _ (by intro w hw; simp at hw; rcases hw with rfl | rfl; exact hva_bd _ rfl; exact hvb_bd _ rfl),
            hbd_yes _, by simp,
            (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h),
            (fun h _ => by rcases h with h | ⟨_, h⟩ <;> cases h),
            by simp, hget_lt _, fun cw0 hcw => ?_⟩
          simpa [evalS, heval_and] using hyes_ev ⟨GateOp.and, [ua, vb]⟩ cw0 hcw
    · by_cases h1 : op = 1
      · subst h1
        cases va with
        | inl ba =>
          cases ba with
          | true =>
            dsimp only [emitOp]; simp only [OfNat.one_ne_ofNat, ite_false, ite_true]
            refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
              fun _ => rfl, fun _ h => (h rfl).elim, by simp, hget_lt _, fun cw0 _ => ?_⟩
            simpa [evalS] using hno_ev (Sum.inl true) cw0
          | false =>
            cases vb with
            | inl bb =>
              cases bb with
              | true =>
                dsimp only [emitOp]; simp only [OfNat.one_ne_ofNat, ite_false, ite_true]
                refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
                  fun _ => rfl, fun _ h => (h rfl).elim, by simp, hget_lt _, fun cw0 _ => ?_⟩
                simpa [evalS] using hno_ev (Sum.inl true) cw0
              | false =>
                dsimp only [emitOp]; simp only [OfNat.one_ne_ofNat, ite_false, ite_true]
                refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
                  fun _ => rfl, fun _ h => (h rfl).elim, by simp, hget_lt _, fun cw0 _ => ?_⟩
                simpa [evalS] using hno_ev (Sum.inl false) cw0
            | inr vb =>
              dsimp only [emitOp]; simp only [OfNat.one_ne_ofNat, ite_false, ite_true]
              refine ⟨hcl, hrb, hbd_no _ hvb_bd, Nat.le_succ _,
                fun _ => rfl, fun _ h => (h rfl).elim, by simp, hget_lt _, fun cw0 _ => ?_⟩
              simpa [evalS] using hno_ev (Sum.inr vb) cw0
        | inr ua =>
          cases vb with
          | inl bb =>
            cases bb with
            | true =>
              dsimp only [emitOp]; simp only [OfNat.one_ne_ofNat, ite_false, ite_true]
              refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
                fun _ => rfl, fun _ h => (h rfl).elim, by simp, hget_lt _, fun cw0 _ => ?_⟩
              simpa [evalS] using hno_ev (Sum.inl true) cw0
            | false =>
              dsimp only [emitOp]; simp only [OfNat.one_ne_ofNat, ite_false, ite_true]
              refine ⟨hcl, hrb, hbd_no _ hva_bd, Nat.le_succ _,
                fun _ => rfl, fun _ h => (h rfl).elim, by simp, hget_lt _, fun cw0 _ => ?_⟩
              simpa [evalS] using hno_ev (Sum.inr ua) cw0
          | inr vb =>
            dsimp only [emitOp]; simp only [OfNat.one_ne_ofNat, ite_false, ite_true]
            refine ⟨hcl_yes _ (Or.inl ⟨Or.inr rfl, rfl⟩),
              hrb_yes _ (by intro w hw; simp at hw; rcases hw with rfl | rfl; exact hva_bd _ rfl; exact hvb_bd _ rfl),
              hbd_yes _, by simp,
              (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h),
              fun _ h => (h rfl).elim,
              by simp, hget_lt _, fun cw0 hcw => ?_⟩
            simpa [evalS, heval_or] using hyes_ev ⟨GateOp.or, [ua, vb]⟩ cw0 hcw
      · have h2 : op = 2 := by omega
        subst h2
        cases va with
        | inl ba =>
          dsimp only [emitOp]; simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false]
          refine ⟨hcl, hrb, hbd_no _ (fun _ h => by cases h), Nat.le_succ _,
            fun _ => trivial, fun _ _ => ⟨!ba, hget_last _⟩, by simp, hget_lt _, fun cw0 _ => ?_⟩
          simpa [evalS] using hno_ev (Sum.inl (!ba)) cw0
        | inr ua =>
          dsimp only [emitOp]; simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false]
          refine ⟨hcl_yes _ (Or.inr ⟨rfl, rfl⟩),
            hrb_yes _ (by intro w hw; simp at hw; exact hva_bd w (hw ▸ rfl)),
            hbd_yes _, by simp,
            (fun h => by rcases h with ⟨_, h⟩ | ⟨h2, _, _⟩; cases h; exact (h2 rfl).elim),
            (fun h _ => by rcases h with h | ⟨he, _⟩; cases h; exact absurd he (by decide)),
            by simp, hget_lt _, fun cw0 hcw => ?_⟩
          simpa [evalS, heval_not] using hyes_ev ⟨GateOp.not, [ua]⟩ cw0 hcw
  -- 3. Compile x4 (Fin 3 × Fin 26 × Fin 26) to CleanGate + ReadsBack 11 circuit D0 via emitOp!
  let lookupR : List (Sum Bool ℕ) → Fin 26 → Sum Bool ℕ := fun env i =>
    if i.val = 25 then Sum.inl true else env.getD i.val (Sum.inl false)
  let compGateR : ℕ → List Gate × List (Sum Bool ℕ) → Fin 3 × Fin 26 × Fin 26 →
      List Gate × List (Sum Bool ℕ) := fun base st g =>
    emitOp base st.1 st.2 g.1.val (lookupR st.2 g.2.1) (lookupR st.2 g.2.2)
  have compListR_inv : ∀ (base : ℕ) (xs : List (Fin 3 × Fin 26 × Fin 26))
      (gs : List Gate) (env : List (Sum Bool ℕ)),
      (∀ gt ∈ gs, CleanGate gt) →
      (∀ (j : ℕ) (hj : j < gs.length), ∀ w ∈ gs[j].inputs, w < base + j) →
      (∀ v ∈ env, ∀ k, v = Sum.inr k → k < base + gs.length) →
      let st' := xs.foldl (compGateR base) (gs, env)
      (∀ gt ∈ st'.1, CleanGate gt) ∧
      (∀ (j : ℕ) (hj : j < st'.1.length), ∀ w ∈ st'.1[j].inputs, w < base + j) ∧
      (∀ v ∈ st'.2, ∀ k, v = Sum.inr k → k < base + st'.1.length) ∧
      st'.1.length ≤ gs.length + xs.length ∧
      ∀ (rw0 cw0 : List Bool), cw0.length = base → rw0.length = env.length →
        (∀ j, rw0.getD j false = evalS (gs.foldl stepC cw0) (env.getD j (Sum.inl false))) →
        ∀ j, (xs.foldl stepR rw0).getD j false =
          evalS (st'.1.foldl stepC cw0) (st'.2.getD j (Sum.inl false)) := by
    intro base xs
    induction xs with
    | nil =>
      intro gs env hcl hrb hbd
      exact ⟨hcl, hrb, hbd, by simp, fun _ _ _ _ hag j => hag j⟩
    | cons g rest ih =>
      intro gs env hcl hrb hbd
      have hlook_bd : ∀ i : Fin 26, ∀ k, lookupR env i = Sum.inr k → k < base + gs.length := by
        intro i k hk
        simp only [lookupR] at hk
        by_cases h25 : i.val = 25
        · simp [h25] at hk
        · simp only [h25, ite_false, List.getD_eq_getElem?_getD] at hk
          cases he : env[i.val]? with
          | none => simp [he] at hk
          | some v => simp [he] at hk; exact hbd v (List.mem_of_getElem? he) k hk
      obtain ⟨hcl1, hrb1, hbd1, hlen1, _, _, helen1, _, hev1⟩ :=
        emitOp_inv base gs env g.1.val (lookupR env g.2.1) (lookupR env g.2.2) g.1.isLt
          hcl hrb hbd (hlook_bd g.2.1) (hlook_bd g.2.2)
      obtain ⟨hcl2, hrb2, hbd2, hlen2, hev2⟩ := ih _ _ hcl1 hrb1 hbd1
      have hlen1' : (compGateR base (gs, env) g).1.length ≤ gs.length + 1 := hlen1
      have hlen2' : (rest.foldl (compGateR base) (compGateR base (gs, env) g)).1.length ≤
          (compGateR base (gs, env) g).1.length + rest.length := hlen2
      refine ⟨hcl2, hrb2, hbd2, by rw [List.foldl_cons]; simp only [List.length_cons]; omega, ?_⟩
      intro rw0 cw0 hcw hrl hag j
      rw [List.foldl_cons]
      apply hev2 (stepR rw0 g) cw0 hcw (by simp [stepR, hrl, helen1]) _ j
      intro m
      obtain ⟨hprev, hnew⟩ := hev1 cw0 hcw
      have hlook_ev : ∀ i : Fin 26, readR rw0 i = evalS (gs.foldl stepC cw0) (lookupR env i) := by
        intro i; simp only [readR, lookupR]; split_ifs; rfl; exact hag i.val
      by_cases hm : m < env.length
      · rw [List.getD_append _ _ _ _ (by omega), hprev m hm]; exact hag m
      · by_cases hmeq : m = env.length
        · subst hmeq
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
          simp only [hrl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hnew, hlook_ev]
        · rw [List.getD_eq_default _ _ (by simp [stepR]; omega),
              List.getD_eq_default _ _ (by omega)]
  have hf9_nonconst : ∀ b : Bool, ∃ x : Fin 9 → Bool, f9 x ≠ b := by
    intro b; cases b
    · exact ⟨fun i => decide (i = 0 ∨ i = 1), by decide⟩
    · exact ⟨fun _ => false, by decide⟩
  have hf8_nonconst : ∀ b : Bool, ∃ x : Fin 8 → Bool, f8 x ≠ b := by
    intro b; cases b
    · exact ⟨fun i => decide (i = 0 ∨ i = 1), by decide⟩
    · exact ⟨fun _ => false, by decide⟩
  let wVal10 : (Fin 9 → Bool) → Bool := fun x =>
    readR (List.ofFn x ++ [x 0 || x 4]) x1 || readR (List.ofFn x ++ [x 0 || x 4]) x2
  let env11 : List (Sum Bool ℕ) := (List.range 11).map Sum.inr
  obtain ⟨hD0cl, hD0rb, _, hD0len, hD0ev⟩ := compListR_inv 11 x4 [] env11
    (by simp) (by intro j hj; simp at hj) (by
      intro v hv k hk
      simp only [env11, List.mem_map, List.mem_range] at hv
      obtain ⟨m, hm, rfl⟩ := hv; cases hk; omega)
  let stD0 := x4.foldl (compGateR 11) ([], env11)
  have hD0_eval_all : ∀ x : Fin 9 → Bool,
      evalS (stD0.1.foldl stepC (List.ofFn x ++ [x 0 || x 4, wVal10 x]))
        (stD0.2.getD x3.val (Sum.inl false)) = f9 x := by
    intro x
    have h0 : stepR (List.ofFn x ++ [x 0 || x 4]) ((1 : Fin 3), x1, x2) =
        List.ofFn x ++ [x 0 || x 4, wVal10 x] := by simp [stepR, wVal10]
    have hraw' := hraw x
    rw [List.foldl_cons, h0] at hraw'
    have hinit : ∀ j, (List.ofFn x ++ [x 0 || x 4, wVal10 x]).getD j false =
        evalS (List.ofFn x ++ [x 0 || x 4, wVal10 x]) (env11.getD j (Sum.inl false)) := by
      intro j
      by_cases hj : j < 11
      · have he : env11.getD j (Sum.inl false) = Sum.inr j := by
          simp [env11, List.getD_eq_getElem?_getD, hj]
        rw [he]
      · have he : env11.getD j (Sum.inl false) = Sum.inl false :=
          List.getD_eq_default _ _ (by simp [env11]; omega)
        rw [he, List.getD_eq_default _ _ (by simp; omega)]
    have heq := hD0ev (List.ofFn x ++ [x 0 || x 4, wVal10 x]) (List.ofFn x ++ [x 0 || x 4, wVal10 x])
      (by simp) (by simp [env11]) hinit x3.val
    rw [← heq]; exact hraw'
  have houtD0 : ∃ out : ℕ, stD0.2.getD x3.val (Sum.inl false) = Sum.inr out := by
    cases h : stD0.2.getD x3.val (Sum.inl false) with
    | inl b =>
      exfalso; obtain ⟨x, hx⟩ := hf9_nonconst b
      have he := hD0_eval_all x; rw [h] at he; exact hx he.symm
    | inr out => exact ⟨out, rfl⟩
  obtain ⟨outD0, houtD0_eq⟩ := houtD0
  let D0 : Circuit := ⟨stD0.1, outD0⟩
  have hD0_size : D0.size ≤ 13 := by
    change stD0.1.length ≤ 13
    have h0 : stD0.1.length ≤ 0 + x4.length := hD0len
    omega
  have hD0_eval : ∀ x : Fin 9 → Bool, D0.eval (List.ofFn x ++ [x 0 || x 4, wVal10 x]) = f9 x := by
    intro x; have he := hD0_eval_all x; rw [houtD0_eq] at he; exact he
  -- 4. Constant-propagating compiler on CleanGate lists via emitOp!
  let gateOpCode : GateOp → ℕ := fun op =>
    GateOp.rec (motive := fun _ => ℕ) 0 1 2 (fun _ => 2) 2 op
  let compGateC : ℕ → List Gate × List (Sum Bool ℕ) → Gate → List Gate × List (Sum Bool ℕ) :=
    fun base st g =>
      emitOp base st.1 st.2 (gateOpCode g.op)
        (st.2.getD (g.inputs.getD 0 0) (Sum.inl false))
        (st.2.getD (g.inputs.getD 1 0) (Sum.inl false))
  have compGateC_inv : ∀ (base : ℕ) (gs : List Gate) (env : List (Sum Bool ℕ)) (g : Gate),
      CleanGate g →
      (∀ gt ∈ gs, CleanGate gt) →
      (∀ (j : ℕ) (hj : j < gs.length), ∀ w ∈ gs[j].inputs, w < base + j) →
      (∀ v ∈ env, ∀ k, v = Sum.inr k → k < base + gs.length) →
      let st' := compGateC base (gs, env) g
      (∀ gt ∈ st'.1, CleanGate gt) ∧
      (∀ (j : ℕ) (hj : j < st'.1.length), ∀ w ∈ st'.1[j].inputs, w < base + j) ∧
      (∀ v ∈ st'.2, ∀ k, v = Sum.inr k → k < base + st'.1.length) ∧
      st'.1.length ≤ gs.length + 1 ∧
      ((∃ i ∈ g.inputs, ∃ b, env.getD i (Sum.inl false) = Sum.inl b) → st'.1.length = gs.length) ∧
      ((∃ i ∈ g.inputs, env.getD i (Sum.inl false) = Sum.inl false) → g.op ≠ GateOp.or →
        ∃ b, st'.2.getD env.length (Sum.inl false) = Sum.inl b) ∧
      st'.2.length = env.length + 1 ∧
      (∀ j < env.length, st'.2.getD j (Sum.inl false) = env.getD j (Sum.inl false)) ∧
      ∀ (rw0 cw0 : List Bool), cw0.length = base → rw0.length = env.length →
        (∀ j ∈ g.inputs, rw0.getD j false = evalS (gs.foldl stepC cw0) (env.getD j (Sum.inl false))) →
        (∀ j < env.length,
          (rw0.getD j false = evalS (gs.foldl stepC cw0) (env.getD j (Sum.inl false)) →
           (stepC rw0 g).getD j false = evalS (st'.1.foldl stepC cw0) (st'.2.getD j (Sum.inl false)))) ∧
        (stepC rw0 g).getD env.length false =
          evalS (st'.1.foldl stepC cw0) (st'.2.getD env.length (Sum.inl false)) := by
    intro base gs env g hcg hcl hrb hbd
    have hget_bd : ∀ i k, env.getD i (Sum.inl false) = Sum.inr k → k < base + gs.length := by
      intro i k hk
      rw [List.getD_eq_getElem?_getD] at hk
      cases he : env[i]? with
      | none => simp [he] at hk
      | some v => simp [he] at hk; exact hbd v (List.mem_of_getElem? he) k hk
    have hop_lt : gateOpCode g.op < 3 := by cases g.op <;> simp [gateOpCode]
    obtain ⟨hcl1, hrb1, hbd1, hlen1, hdrop1, hconst1, helen1, hkeep1, hev1⟩ :=
      emitOp_inv base gs env (gateOpCode g.op)
        (env.getD (g.inputs.getD 0 0) (Sum.inl false))
        (env.getD (g.inputs.getD 1 0) (Sum.inl false))
        hop_lt hcl hrb hbd (hget_bd _) (hget_bd _)
    refine ⟨hcl1, hrb1, hbd1, hlen1, ?_, ?_, helen1, hkeep1, ?_⟩
    · rintro ⟨i, hi, b, hib⟩
      apply hdrop1
      rcases g with ⟨op, ins⟩
      rcases hcg with ⟨rfl | rfl, hlen2⟩ | ⟨rfl, hlen1'⟩
      · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, ds⟩⟩⟩ <;> try (simp at hlen2)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · left; exact ⟨b, by simpa using hib⟩
        · right; exact ⟨by simp [gateOpCode], b, by simpa using hib⟩
      · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, ds⟩⟩⟩ <;> try (simp at hlen2)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · left; exact ⟨b, by simpa using hib⟩
        · right; exact ⟨by simp [gateOpCode], b, by simpa using hib⟩
      · rcases ins with _ | ⟨a, _ | ⟨c, cs⟩⟩ <;> try (simp at hlen1')
        simp only [List.mem_singleton] at hi; subst hi
        left; exact ⟨b, by simpa using hib⟩
    · rintro ⟨i, hi, hif⟩ hneor
      rcases g with ⟨op, ins⟩
      rcases hcg with ⟨rfl | rfl, hlen2⟩ | ⟨rfl, hlen1'⟩
      · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, ds⟩⟩⟩ <;> try (simp at hlen2)
        apply hconst1 _ (by simp [gateOpCode])
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · left; simpa using hif
        · right; exact ⟨rfl, by simpa using hif⟩
      · exact (hneor rfl).elim
      · rcases ins with _ | ⟨a, _ | ⟨c, cs⟩⟩ <;> try (simp at hlen1')
        simp only [List.mem_singleton] at hi; subst hi
        exact hconst1 (Or.inl (by simpa using hif)) (by simp [gateOpCode])
    · intro rw0 cw0 hcw hrl hag
      obtain ⟨hprev, hnew⟩ := hev1 cw0 hcw
      refine ⟨fun j hj heq => by rw [stepC_snoc_lt _ _ _ (by omega), hprev j hj]; exact heq, ?_⟩
      rw [← hrl, stepC_snoc_self, hrl, hnew]
      rcases g with ⟨op, ins⟩
      rcases hcg with ⟨rfl | rfl, hlen2⟩ | ⟨rfl, hlen1'⟩
      · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, ds⟩⟩⟩ <;> try (simp at hlen2)
        have ha := hag a (by simp); have hc := hag c (by simp)
        simp only [gateOpCode, ite_true, List.map_cons, List.map_nil, heval_and,
          List.getD_cons_zero, List.getD_cons_succ, ha, hc]
      · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, ds⟩⟩⟩ <;> try (simp at hlen2)
        have ha := hag a (by simp); have hc := hag c (by simp)
        simp only [gateOpCode, show (1 : ℕ) ≠ 0 by decide, ite_false, ite_true,
          List.map_cons, List.map_nil, heval_or, List.getD_cons_zero, List.getD_cons_succ, ha, hc]
      · rcases ins with _ | ⟨a, _ | ⟨c, cs⟩⟩ <;> try (simp at hlen1')
        have ha := hag a (by simp)
        simp only [gateOpCode, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false,
          List.map_cons, List.map_nil, heval_not, List.getD_cons_zero, ha]
  -- Fold of compGateC with full tracking (including ignoring a dead wire `dead`!).
  have compListC_inv : ∀ (base : ℕ) (xs : List Gate) (gs : List Gate) (env : List (Sum Bool ℕ))
      (dead : Option ℕ),
      (∀ g ∈ xs, CleanGate g) →
      (∀ g ∈ xs, ∀ w ∈ g.inputs, dead ≠ some w) →
      (∀ gt ∈ gs, CleanGate gt) →
      (∀ (j : ℕ) (hj : j < gs.length), ∀ w ∈ gs[j].inputs, w < base + j) →
      (∀ v ∈ env, ∀ k, v = Sum.inr k → k < base + gs.length) →
      let st' := xs.foldl (compGateC base) (gs, env)
      (∀ gt ∈ st'.1, CleanGate gt) ∧
      (∀ (j : ℕ) (hj : j < st'.1.length), ∀ w ∈ st'.1[j].inputs, w < base + j) ∧
      (∀ v ∈ st'.2, ∀ k, v = Sum.inr k → k < base + st'.1.length) ∧
      st'.1.length ≤ gs.length + xs.length ∧
      st'.2.length = env.length + xs.length ∧
      (∀ j < env.length, st'.2.getD j (Sum.inl false) = env.getD j (Sum.inl false)) ∧
      (∀ (j : ℕ) (hj : j < xs.length),
        (∃ i ∈ xs[j].inputs, ∃ b, ((xs.take j).foldl (compGateC base) (gs, env)).2.getD i (Sum.inl false) = Sum.inl b) →
        st'.1.length + 1 ≤ gs.length + xs.length) ∧
      ∀ (rw0 cw0 : List Bool), cw0.length = base → rw0.length = env.length →
        (∀ j, j < env.length → dead ≠ some j →
          rw0.getD j false = evalS (gs.foldl stepC cw0) (env.getD j (Sum.inl false))) →
        ∀ j, j < env.length + xs.length → dead ≠ some j →
          (xs.foldl stepC rw0).getD j false =
            evalS (st'.1.foldl stepC cw0) (st'.2.getD j (Sum.inl false)) := by
    intro base xs
    induction xs with
    | nil =>
      intro gs env dead _ _ hcl hrb hbd
      refine ⟨hcl, hrb, hbd, by simp, by simp, fun _ _ => rfl, fun j hj => by simp at hj, ?_⟩
      intro rw0 cw0 _ _ hag j hj hne; exact hag j (by simpa using hj) hne
    | cons g rest ih =>
      intro gs env dead hxs hnd hcl hrb hbd
      obtain ⟨hcl1, hrb1, hbd1, hlen1, hdrop1, _, helen1, hkeep1, hstep1⟩ :=
        compGateC_inv base gs env g (hxs g (by simp)) hcl hrb hbd
      have hxs' : ∀ g' ∈ rest, CleanGate g' := fun g' hg' => hxs g' (by simp [hg'])
      have hnd' : ∀ g' ∈ rest, ∀ w ∈ g'.inputs, dead ≠ some w := fun g' hg' => hnd g' (by simp [hg'])
      obtain ⟨hcl2, hrb2, hbd2, hlen2, helen2, hkeep2, hdrop2, hev2⟩ :=
        ih _ _ dead hxs' hnd' hcl1 hrb1 hbd1
      have hlen1' : (compGateC base (gs, env) g).1.length ≤ gs.length + 1 := hlen1
      have helen1' : (compGateC base (gs, env) g).2.length = env.length + 1 := helen1
      have hlen2' : (rest.foldl (compGateC base) (compGateC base (gs, env) g)).1.length ≤
          (compGateC base (gs, env) g).1.length + rest.length := hlen2
      have helen2' : (rest.foldl (compGateC base) (compGateC base (gs, env) g)).2.length =
          (compGateC base (gs, env) g).2.length + rest.length := helen2
      refine ⟨hcl2, hrb2, hbd2, by rw [List.foldl_cons]; simp only [List.length_cons]; omega,
        by rw [List.foldl_cons]; simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
      · intro j hj
        rw [List.foldl_cons, hkeep2 j (by omega), hkeep1 j hj]
      · intro j hj hconst
        rw [List.foldl_cons]
        cases j with
        | zero =>
          simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hconst
          have heq : (compGateC base (gs, env) g).1.length = gs.length := hdrop1 hconst
          simp only [List.length_cons]; omega
        | succ j' =>
          simp only [List.length_cons] at hj
          simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] at hconst
          have h2 : (rest.foldl (compGateC base) (compGateC base (gs, env) g)).1.length + 1 ≤
              (compGateC base (gs, env) g).1.length + rest.length := hdrop2 j' (by omega) hconst
          simp only [List.length_cons]; omega
      · intro rw0 cw0 hcw hrl hag j hj hne
        rw [List.foldl_cons, List.foldl_cons]
        have hg_in : ∀ i ∈ g.inputs,
            rw0.getD i false = evalS (gs.foldl stepC cw0) (env.getD i (Sum.inl false)) := by
          intro i hi
          by_cases hil : i < env.length
          · exact hag i hil (hnd g (by simp) i hi)
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        obtain ⟨hprev, hnew⟩ := hstep1 rw0 cw0 hcw hrl hg_in
        apply hev2 (stepC rw0 g) cw0 hcw (by simp [stepC, hrl, helen1]) _ j
          (by simp only [List.length_cons] at hj; omega) hne
        intro m hm hnem
        by_cases hml : m < env.length
        · exact hprev m hml (hag m hml hnem)
        · have hmeq : m = env.length := by omega
          subst hmeq; exact hnew
  have compListC_save2 : ∀ (base : ℕ) (xs : List Gate) (gs : List Gate) (env : List (Sum Bool ℕ))
      (j1 j2 : ℕ) (hj1 : j1 < xs.length) (hj2 : j2 < xs.length), j1 < j2 →
      (∀ g ∈ xs, CleanGate g) →
      (∀ gt ∈ gs, CleanGate gt) →
      (∀ (j : ℕ) (hj : j < gs.length), ∀ w ∈ gs[j].inputs, w < base + j) →
      (∀ v ∈ env, ∀ k, v = Sum.inr k → k < base + gs.length) →
      (∃ i ∈ xs[j1].inputs, ∃ b, ((xs.take j1).foldl (compGateC base) (gs, env)).2.getD i (Sum.inl false) = Sum.inl b) →
      (∃ i ∈ xs[j2].inputs, ∃ b, ((xs.take j2).foldl (compGateC base) (gs, env)).2.getD i (Sum.inl false) = Sum.inl b) →
      (xs.foldl (compGateC base) (gs, env)).1.length + 2 ≤ gs.length + xs.length := by
    intro base xs
    induction xs with
    | nil => intro _ _ _ _ hj1; simp at hj1
    | cons g rest ih =>
      intro gs env j1 j2 hj1 hj2 hlt hxs hcl hrb hbd hc1 hc2
      obtain ⟨hcl1, hrb1, hbd1, hlen1, hdrop1, _, _, _, _⟩ :=
        compGateC_inv base gs env g (hxs g (by simp)) hcl hrb hbd
      have hxs' : ∀ g' ∈ rest, CleanGate g' := fun g' hg' => hxs g' (by simp [hg'])
      cases j2 with
      | zero => omega
      | succ j2' =>
        simp only [List.length_cons] at hj2
        cases j1 with
        | zero =>
          simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hc1
          have heq1 := hdrop1 hc1
          simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] at hc2
          obtain ⟨_, _, _, _, _, _, hdrop2, _⟩ :=
            compListC_inv base rest _ _ none hxs' (fun _ _ _ _ h => by cases h) hcl1 hrb1 hbd1
          have h2 : (rest.foldl (compGateC base) (compGateC base (gs, env) g)).1.length + 1 ≤
              (compGateC base (gs, env) g).1.length + rest.length := hdrop2 j2' (by omega) hc2
          rw [List.foldl_cons]; simp only [List.length_cons]
          have hlen_c1 : (compGateC base (gs, env) g).1.length = gs.length := heq1
          omega
        | succ j1' =>
          simp only [List.length_cons] at hj1
          simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] at hc1 hc2
          have hrec : (rest.foldl (compGateC base) (compGateC base (gs, env) g)).1.length + 2 ≤
              (compGateC base (gs, env) g).1.length + rest.length :=
            ih _ _ j1' j2' (by omega) (by omega) (by omega) hxs' hcl1 hrb1 hbd1 hc1 hc2
          rw [List.foldl_cons]; simp only [List.length_cons]
          have hlen_c1 : (compGateC base (gs, env) g).1.length ≤ gs.length + 1 := hlen1
          omega
  have compListC_env_eq : ∀ (base : ℕ) (xs : List Gate) (gs : List Gate) (env : List (Sum Bool ℕ)),
      (∀ g ∈ xs, CleanGate g) →
      (∀ gt ∈ gs, CleanGate gt) →
      (∀ (j : ℕ) (hj : j < gs.length), ∀ w ∈ gs[j].inputs, w < base + j) →
      (∀ v ∈ env, ∀ k, v = Sum.inr k → k < base + gs.length) →
      ∀ j < env.length, (xs.foldl (compGateC base) (gs, env)).2.getD j (Sum.inl false) =
        env.getD j (Sum.inl false) :=
    fun base xs gs env hxs hcl hrb hbd =>
      (compListC_inv base xs gs env none hxs (fun _ _ _ _ h => by cases h) hcl hrb hbd).2.2.2.2.2.1
  -- 5. Dead-gate pruning on CleanGate + ReadsBack 11 circuits.
  have prune_dead : ∀ (n : ℕ) (C : Circuit), C.size ≤ n →
      (∀ g ∈ C.gates, CleanGate g) →
      (∀ (j : ℕ) (hj : j < C.gates.length), ∀ w ∈ C.gates[j].inputs, w < 11 + j) →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, wVal10 x]) = f9 x) →
      ∃ D : Circuit, D.size ≤ C.size ∧
        (∀ g ∈ D.gates, CleanGate g) ∧
        (∀ (j : ℕ) (hj : j < D.gates.length), ∀ w ∈ D.gates[j].inputs, w < 11 + j) ∧
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, wVal10 x]) = f9 x) ∧
        ∀ (j : ℕ), j < D.gates.length →
          11 + j = D.output ∨ ∃ (m : ℕ) (hm : m < D.gates.length), j < m ∧ 11 + j ∈ D.gates[m].inputs := by
    intro n
    induction n with
    | zero =>
      intro C hsz hcl hrb hev
      exact ⟨C, le_refl _, hcl, hrb, hev, fun j hj => by change C.gates.length ≤ 0 at hsz; omega⟩
    | succ n ih =>
      intro C hsz hcl hrb hev
      by_cases hlive : ∀ (j : ℕ), j < C.gates.length →
          11 + j = C.output ∨ ∃ (m : ℕ) (hm : m < C.gates.length), j < m ∧ 11 + j ∈ C.gates[m].inputs
      · exact ⟨C, le_refl _, hcl, hrb, hev, hlive⟩
      · push_neg at hlive
        obtain ⟨j, hj, hjout, hjunused⟩ := hlive
        let pref := C.gates.take j
        let suff := C.gates.drop (j + 1)
        let envInit : List (Sum Bool ℕ) := (List.range (11 + j)).map Sum.inr ++ [Sum.inl false]
        have hpref_len : pref.length = j := List.length_take_of_le (by omega)
        have hsuff_len : suff.length = C.gates.length - (j + 1) := List.length_drop
        have hpref_cl : ∀ g ∈ pref, CleanGate g := fun g hg => hcl g (List.mem_of_mem_take hg)
        have hsuff_cl : ∀ g ∈ suff, CleanGate g := fun g hg => hcl g (List.mem_of_mem_drop hg)
        have hpref_rb : ∀ (i : ℕ) (hi : i < pref.length), ∀ w ∈ pref[i].inputs, w < 11 + i := by
          intro i hi w hw
          have hi' : i < C.gates.length := by omega
          have heq : pref[i] = C.gates[i] := List.getElem_take
          rw [heq] at hw; exact hrb i hi' w hw
        have hsuff_nd : ∀ g ∈ suff, ∀ w ∈ g.inputs, some (11 + j) ≠ some w := by
          intro g hg w hw heq
          have hwj : w = 11 + j := (Option.some.inj heq).symm
          subst hwj
          obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
          have hk' : j + 1 + k < C.gates.length := by omega
          have heq' : suff[k] = C.gates[j + 1 + k] := List.getElem_drop
          rw [← hgk, heq'] at hw
          exact hjunused (j + 1 + k) hk' (by omega) hw
        have henv_bd : ∀ v ∈ envInit, ∀ k, v = Sum.inr k → k < 11 + pref.length := by
          intro v hv k hk
          rcases List.mem_append.mp hv with h1 | h2
          · simp only [List.mem_map, List.mem_range] at h1
            obtain ⟨m, hm, rfl⟩ := h1; cases hk; omega
          · rw [List.mem_singleton.mp h2] at hk; cases hk
        obtain ⟨hcl', hrb', _, hlen', helen', _, _, hev'⟩ :=
          compListC_inv 11 suff pref envInit (some (11 + j)) hsuff_cl hsuff_nd hpref_cl hpref_rb henv_bd
        let st' := suff.foldl (compGateC 11) (pref, envInit)
        have hev_all : ∀ x : Fin 9 → Bool,
            evalS (st'.1.foldl stepC (List.ofFn x ++ [x 0 || x 4, wVal10 x]))
              (st'.2.getD C.output (Sum.inl false)) = f9 x := by
          intro x
          let base := List.ofFn x ++ [x 0 || x 4, wVal10 x]
          have hbase_len : base.length = 11 := by simp [base]
          have hsplit : C.gates = pref ++ [C.gates[j]] ++ suff := by
            conv_lhs => rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj]
            simp [pref, suff]
          have hCev : (C.gates.foldl stepC base).getD C.output false = f9 x := hev x
          by_cases hout_lt : C.output < 11 + C.gates.length
          · rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil] at hCev
            have hrw_len : (stepC (pref.foldl stepC base) C.gates[j]).length = envInit.length := by
              have hs1 : (stepC (pref.foldl stepC base) C.gates[j]).length = (pref.foldl stepC base).length + 1 := by
                simp [stepC]
              rw [hs1, foldl_stepC_len, hbase_len, hpref_len]; simp [envInit]
            have hinit : ∀ m, m < envInit.length → some (11 + j) ≠ some m →
                (stepC (pref.foldl stepC base) C.gates[j]).getD m false =
                  evalS (pref.foldl stepC base) (envInit.getD m (Sum.inl false)) := by
              intro m hm hne
              have hm_ne : m ≠ 11 + j := fun h => hne (congrArg some h.symm)
              have hm_lt : m < 11 + j := by simp [envInit] at hm; omega
              have hplen : (pref.foldl stepC base).length = 11 + j := by
                rw [foldl_stepC_len, hbase_len, hpref_len]
              rw [stepC_snoc_lt _ _ _ (by omega)]
              have he : envInit.getD m (Sum.inl false) = Sum.inr m := by
                simp only [envInit]
                rw [List.getD_append _ _ _ _ (by simp; omega)]
                simp [List.getD_eq_getElem?_getD, hm_lt]
              rw [he]
            have heq := hev' (stepC (pref.foldl stepC base) C.gates[j]) base hbase_len hrw_len hinit
              C.output (by simp [envInit, hsuff_len]; omega) (fun h => hjout (Option.some.inj h))
            rw [← heq]; exact hCev
          · have hf : f9 x = false := by
              rw [← hCev, List.getD_eq_default]
              rw [foldl_stepC_len, hbase_len]; omega
            have hst_len : st'.2.length = envInit.length + suff.length := helen'
            have hge_st : st'.2.length ≤ C.output := by
              have : envInit.length = 11 + j + 1 := by simp [envInit]
              omega
            rw [hf, List.getD_eq_default _ _ hge_st]
        have hout' : ∃ out : ℕ, st'.2.getD C.output (Sum.inl false) = Sum.inr out := by
          cases h : st'.2.getD C.output (Sum.inl false) with
          | inl b =>
            exfalso; obtain ⟨x, hx⟩ := hf9_nonconst b
            have he := hev_all x; rw [h] at he; exact hx he.symm
          | inr out => exact ⟨out, rfl⟩
        obtain ⟨out', hout'_eq⟩ := hout'
        let C' : Circuit := ⟨st'.1, out'⟩
        have hC'_sz : C'.size ≤ n := by
          change st'.1.length ≤ n
          have hst1 : st'.1.length ≤ pref.length + suff.length := hlen'
          change C.gates.length ≤ n + 1 at hsz; omega
        have hC'_lt : C'.size ≤ C.size := by
          change st'.1.length ≤ C.gates.length
          have hst1 : st'.1.length ≤ pref.length + suff.length := hlen'
          omega
        have hC'_ev : ∀ x : Fin 9 → Bool, C'.eval (List.ofFn x ++ [x 0 || x 4, wVal10 x]) = f9 x := by
          intro x; have he := hev_all x; rw [hout'_eq] at he; exact he
        obtain ⟨D, hDle, hDcl, hDrb, hDev, hDlive⟩ := ih C' hC'_sz hcl' hrb' hC'_ev
        exact ⟨D, le_trans hDle hC'_lt, hDcl, hDrb, hDev, hDlive⟩
  obtain ⟨D, hD_le, hD_cl, hD_rb, hD_ev, hD_live⟩ := prune_dead 13 D0 hD0_size hD0cl hD0rb hD0_eval
  have hD_size : D.size ≤ 13 := le_trans hD_le hD0_size
  have hD_fan : FanInTwo D := clean_to_fan D hD_cl
  -- 6. Embed Fin 8 → Fin 9 skipping vertex 4.
  let ins4 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y i =>
    if h : i.val < 4 then y ⟨i.val, by omega⟩
    else if h4 : i.val = 4 then false
    else y ⟨i.val - 1, by omega⟩
  have hins4_f9 : ∀ y : Fin 8 → Bool, f9 (ins4 y) = f8 y := by intro y; simp [f9, f8, ins4]
  let idx8 : ℕ → ℕ := fun i => if i < 4 then i else i - 1
  have hins4_getD : ∀ (y : Fin 8 → Bool) (i : ℕ), i < 9 → i ≠ 4 →
      (List.ofFn (ins4 y)).getD i false = (List.ofFn y).getD (idx8 i) false := by
    intro y i hi hne
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    have hidx : idx8 i < 8 := by dsimp only [idx8]; split_ifs <;> omega
    simp only [List.getElem?_ofFn, hi, hidx, dite_true, Option.getD_some, ins4]
    by_cases h1 : i < 4
    · simp only [h1, dite_true]
      congr 1; exact Fin.ext (by simp [idx8, h1])
    · simp only [h1, hne, dite_false]
      congr 1; exact Fin.ext (by simp [idx8, h1])
  -- 7. Two runs agreeing off an unread wire set produce the same output.
  have hD_out_ne4 : D.output ≠ 4 := by
    intro heq
    let x4only : Fin 9 → Bool := fun i => decide (i = 4)
    have h1 := hD_ev x4only
    have h2 : f9 x4only = false := by decide
    rw [h2] at h1
    have h3 : D.eval (List.ofFn x4only ++ [x4only 0 || x4only 4, wVal10 x4only]) = true := by
      change (D.gates.foldl stepC (List.ofFn x4only ++ [x4only 0 || x4only 4, wVal10 x4only])).getD
        D.output false = true
      rw [heq]
      have hlt : ∀ (gs : List Gate) (w : List Bool), 4 < w.length →
          (gs.foldl stepC w).getD 4 false = w.getD 4 false := by
        intro gs; induction gs with
        | nil => intro w _; rfl
        | cons g rest ih => intro w hw; rw [List.foldl_cons, ih _ (by simp [stepC]; omega), stepC_snoc_lt _ _ _ hw]
      rw [hlt _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, x4only]
    rw [h3] at h1; cases h1
  have agree_off_set : ∀ (S : ℕ → Prop) (gs : List Gate),
      (∀ g ∈ gs, ∀ w ∈ g.inputs, ¬ S w) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, ¬ S i → w1.getD i false = w2.getD i false) →
      ∀ i, ¬ S i → (gs.foldl stepC w1).getD i false = (gs.foldl stepC w2).getD i false := by
    intro S gs
    induction gs with
    | nil => intro _ w1 w2 _ hag i hi; exact hag i hi
    | cons g rest ih =>
      intro hno w1 w2 hlen hag i hi
      have hg : g.op.eval (g.inputs.map fun k => w1.getD k false) =
          g.op.eval (g.inputs.map fun k => w2.getD k false) := by
        congr 1; apply List.map_congr_left; intro k hk; exact hag k (hno g (by simp) k hk)
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hno g' (by simp [hg'])) _ _ (by simp [stepC, hlen]) _ i hi
      intro j hj
      by_cases hlt : j < w1.length
      · rw [stepC_snoc_lt _ _ _ hlt, stepC_snoc_lt _ _ _ (by omega)]; exact hag j hj
      · by_cases heq : j = w1.length
        · subst heq; rw [stepC_snoc_self, hlen, stepC_snoc_self, hg]
        · rw [List.getD_eq_default _ _ (by simp [stepC]; omega),
              List.getD_eq_default _ _ (by simp [stepC]; omega)]
  have no4_contra_pair : ∀ (x y : Fin 9 → Bool),
      (∀ g ∈ D.gates, 4 ∉ g.inputs) →
      (∀ i : Fin 9, i ≠ 4 → x i = y i) →
      (x 0 || x 4) = (y 0 || y 4) →
      wVal10 x = wVal10 y →
      f9 x ≠ f9 y → False := by
    intro x y hno4 hxy h9 h10 hne
    have hsame := agree_off_set (fun w => w = 4) D.gates
      (fun g hg w hw h4 => hno4 g hg (h4 ▸ hw))
      (List.ofFn x ++ [x 0 || x 4, wVal10 x])
      (List.ofFn y ++ [y 0 || y 4, wVal10 y]) (by simp) (by
        intro i hi
        by_cases hlt : i < 9
        · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
          exact hxy ⟨i, hlt⟩ (fun he => hi (congrArg Fin.val he))
        · by_cases hi9 : i = 9
          · subst hi9; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h9]
          · by_cases hi10 : i = 10
            · subst hi10; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h10]
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)]) D.output hD_out_ne4
    have h1 := hD_ev x
    have h2 := hD_ev y
    change (D.gates.foldl stepC _).getD D.output false = f9 x at h1
    change (D.gates.foldl stepC _).getD D.output false = f9 y at h2
    exact hne (h1.symm.trans (hsame.trans h2))
  -- 8. Restrict D with x_4 = false via compGateC 8: shared evaluation + contradiction with hG6.
  have restrict_eval : ∀ (gs0 : List Gate) (v10 : Sum Bool ℕ),
      (∀ gt ∈ gs0, CleanGate gt) →
      (∀ (j : ℕ) (hj : j < gs0.length), ∀ w ∈ gs0[j].inputs, w < 8 + j) →
      (∀ k, v10 = Sum.inr k → k < 8 + gs0.length) →
      (∀ y : Fin 8 → Bool, wVal10 (ins4 y) = evalS (gs0.foldl stepC (List.ofFn y)) v10) →
      let env8 : List (Sum Bool ℕ) :=
        [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
         Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 0, v10]
      let st8 := D.gates.foldl (compGateC 8) (gs0, env8)
      (∀ gt ∈ st8.1, CleanGate gt) ∧
      ∀ y : Fin 8 → Bool,
        evalS (st8.1.foldl stepC (List.ofFn y)) (st8.2.getD D.output (Sum.inl false)) = f8 y := by
    intro gs0 v10 hgs0_cl hgs0_rb hv10_bd hv10_ev env8 st8
    have henv8_bd : ∀ v ∈ env8, ∀ k, v = Sum.inr k → k < 8 + gs0.length := by
      intro v hv k hk
      simp only [env8, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hv10_bd k hk | (cases hk; omega) | cases hk
    obtain ⟨hcl', _, _, _, helen', _, _, hev'⟩ :=
      compListC_inv 8 D.gates gs0 env8 none hD_cl (fun _ _ _ _ h => by cases h) hgs0_cl hgs0_rb henv8_bd
    refine ⟨hcl', ?_⟩
    intro y
    have hgs0_lt : ∀ m < 8, (gs0.foldl stepC (List.ofFn y)).getD m false = (List.ofFn y).getD m false := by
      intro m hm
      have hlt : ∀ (gs : List Gate) (w : List Bool), m < w.length →
          (gs.foldl stepC w).getD m false = w.getD m false := by
        intro gs; induction gs with
        | nil => intro w _; rfl
        | cons g rest ih => intro w hw; rw [List.foldl_cons, ih _ (by simp [stepC]; omega), stepC_snoc_lt _ _ _ hw]
      exact hlt gs0 (List.ofFn y) (by simp; omega)
    have hbase_ag : ∀ j, j < env8.length → none ≠ some j →
        (List.ofFn (ins4 y) ++ [ins4 y 0 || ins4 y 4, wVal10 (ins4 y)]).getD j false =
          evalS (gs0.foldl stepC (List.ofFn y)) (env8.getD j (Sum.inl false)) := by
      intro j hj _
      have hj11 : j < 11 := by simpa [env8] using hj
      by_cases hj9 : j < 9
      · rw [List.getD_append _ _ _ _ (by simp; omega)]
        by_cases hj4 : j = 4
        · subst hj4
          have he4 : env8.getD 4 (Sum.inl false) = Sum.inl false := rfl
          rw [he4]
          simp [evalS, List.getD_eq_getElem?_getD, ins4]
        · have hej : env8.getD j (Sum.inl false) = Sum.inr (idx8 j) := by
            have : ∀ k < 9, k ≠ 4 → env8.getD k (Sum.inl false) = Sum.inr (idx8 k) := by
              intro k hk hne
              interval_cases k <;> first | exact (hne rfl).elim | rfl
            exact this j hj9 hj4
          rw [hej]
          change (List.ofFn (ins4 y)).getD j false = (gs0.foldl stepC (List.ofFn y)).getD (idx8 j) false
          have hidx8 : idx8 j < 8 := by dsimp only [idx8]; split_ifs <;> omega
          rw [hgs0_lt (idx8 j) hidx8]
          exact hins4_getD y j hj9 hj4
      · by_cases hje9 : j = 9
        · subst hje9
          have he9 : env8.getD 9 (Sum.inl false) = Sum.inr 0 := rfl
          rw [he9]
          change (List.ofFn (ins4 y) ++ [ins4 y 0 || ins4 y 4, wVal10 (ins4 y)]).getD 9 false =
            (gs0.foldl stepC (List.ofFn y)).getD 0 false
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          simp only [List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          have h0 : ins4 y 0 = y 0 := by simp [ins4]
          have h4 : ins4 y 4 = false := by simp [ins4]
          rw [h0, h4, Bool.or_false, hgs0_lt 0 (by omega)]
          simp [List.getD_eq_getElem?_getD]
        · have hje10 : j = 10 := by omega
          subst hje10
          have he10 : env8.getD 10 (Sum.inl false) = v10 := rfl
          rw [he10]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          simp only [List.length_ofFn, show 10 - 9 = 1 by rfl, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.getD_some]
          exact hv10_ev y
    by_cases hout : D.output < env8.length + D.gates.length
    · have heq := hev' (List.ofFn (ins4 y) ++ [ins4 y 0 || ins4 y 4, wVal10 (ins4 y)])
        (List.ofFn y) (by simp) (by simp [env8]) hbase_ag D.output hout (fun h => by cases h)
      rw [← heq]
      have he := hD_ev (ins4 y); rw [hins4_f9] at he; exact he
    · have hst_len : st8.2.length = env8.length + D.gates.length := helen'
      rw [List.getD_eq_default _ _ (by omega)]
      have he := hD_ev (ins4 y); rw [hins4_f9] at he
      have hdef : D.eval (List.ofFn (ins4 y) ++ [ins4 y 0 || ins4 y 4, wVal10 (ins4 y)]) = false := by
        change (D.gates.foldl stepC _).getD D.output false = false
        rw [List.getD_eq_default _ _ (by rw [foldl_stepC_len]; simp [env8] at hout ⊢; omega)]
      rw [hdef] at he; exact he
  have restrict_to_G6 : ∀ (gs0 : List Gate) (v10 : Sum Bool ℕ),
      (∀ gt ∈ gs0, CleanGate gt) →
      (∀ (j : ℕ) (hj : j < gs0.length), ∀ w ∈ gs0[j].inputs, w < 8 + j) →
      (∀ k, v10 = Sum.inr k → k < 8 + gs0.length) →
      (∀ y : Fin 8 → Bool, wVal10 (ins4 y) = evalS (gs0.foldl stepC (List.ofFn y)) v10) →
      let env8 : List (Sum Bool ℕ) :=
        [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
         Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 0, v10]
      (D.gates.foldl (compGateC 8) (gs0, env8)).1.length ≤ 12 → False := by
    intro gs0 v10 hgs0_cl hgs0_rb hv10_bd hv10_ev env8 hle12
    obtain ⟨hcl', hD8_ev⟩ := restrict_eval gs0 v10 hgs0_cl hgs0_rb hv10_bd hv10_ev
    let st8 := D.gates.foldl (compGateC 8) (gs0, env8)
    cases hout8 : st8.2.getD D.output (Sum.inl false) with
    | inl b =>
      obtain ⟨y, hy⟩ := hf8_nonconst b
      have he := hD8_ev y; rw [hout8] at he; exact hy he.symm
    | inr out8 =>
      apply hG6
      refine ⟨⟨st8.1, out8⟩, clean_to_fan ⟨st8.1, out8⟩ hcl', hle12, ?_⟩
      intro y; have he := hD8_ev y; rw [hout8] at he; exact he
  -- 9. Reflection symmetry τ = (1 5)(2 8)(6 7) of P - v fixing 0, 3, 4.
  let tau : Fin 9 → Fin 9 := fun i =>
    if i.val = 1 then 5 else if i.val = 5 then 1
    else if i.val = 2 then 8 else if i.val = 8 then 2
    else if i.val = 6 then 7 else if i.val = 7 then 6
    else i
  have htau_inv : ∀ i : Fin 9, tau (tau i) = i := by decide
  have htau_f9 : ∀ x : Fin 9 → Bool, f9 (x ∘ tau) = f9 x := by
    intro x
    change (x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 1 ||
      x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 || x 7 && x 2 || x 2 && x 1) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    rw [Bool.and_comm (x 5) (x 8), Bool.and_comm (x 8) (x 3), Bool.and_comm (x 8) (x 6),
        Bool.and_comm (x 3) (x 2), Bool.and_comm (x 7) (x 2), Bool.and_comm (x 2) (x 1)]
    ac_rfl
  let mapW : ℕ → ℕ := fun w => if h : w < 9 then (tau ⟨w, h⟩).val else w
  let mapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map mapW⟩
  let mapCirc : Circuit → Circuit := fun C => ⟨C.gates.map mapGate, mapW C.output⟩
  have mapCirc_eval : ∀ (C : Circuit) (x : Fin 9 → Bool) (b10 : Bool),
      (mapCirc C).eval (List.ofFn x ++ [x 0 || x 4, b10]) =
        C.eval (List.ofFn (x ∘ tau) ++ [(x ∘ tau) 0 || (x ∘ tau) 4, b10]) := by
    intro C x b10
    have hstep : ∀ (gs : List Gate) (w1 w2 : List Bool), w1.length = w2.length → 9 ≤ w1.length →
        (∀ i < 9, w2.getD i false = w1.getD (mapW i) false) →
        (∀ i ≥ 9, w2.getD i false = w1.getD i false) →
        ∀ i, (gs.foldl stepC w2).getD i false =
          ((gs.map mapGate).foldl stepC w1).getD (mapW i) false := by
      intro gs; induction gs with
      | nil =>
        intro w1 w2 _ _ hlt hge i
        by_cases hi : i < 9
        · exact hlt i hi
        · have hm : mapW i = i := by simp [mapW, hi]
          rw [hm]; exact hge i (by omega)
      | cons g rest ih =>
        intro w1 w2 hlen hw9 hlt hge i
        have hgev : g.op.eval (g.inputs.map fun k => w2.getD k false) =
            (mapGate g).op.eval ((mapGate g).inputs.map fun k => w1.getD k false) := by
          simp only [mapGate, List.map_map]; congr 1
          apply List.map_congr_left; intro k _
          by_cases hk : k < 9
          · exact hlt k hk
          · have hm : mapW k = k := by simp [mapW, hk]
            simp only [Function.comp, hm]; exact hge k (by omega)
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        apply ih _ _ (by simp [stepC, hlen]) (by simp [stepC]; omega)
        · intro k hk
          have hmk : mapW k < 9 := by simp only [mapW, hk, dite_true]; exact (tau ⟨k, hk⟩).isLt
          rw [stepC_snoc_lt _ _ _ (by omega), stepC_snoc_lt _ _ _ (by omega)]; exact hlt k hk
        · intro k hk
          by_cases hltw : k < w1.length
          · rw [stepC_snoc_lt _ _ _ (by omega), stepC_snoc_lt _ _ _ hltw]; exact hge k hk
          · by_cases heqw : k = w1.length
            · subst heqw; rw [hlen, stepC_snoc_self, ← hlen, stepC_snoc_self, hgev]
            · rw [List.getD_eq_default _ _ (by simp [stepC]; omega),
                  List.getD_eq_default _ _ (by simp [stepC]; omega)]
    have h0 : (x ∘ tau) 0 = x 0 := rfl
    have h4 : (x ∘ tau) 4 = x 4 := rfl
    rw [h0, h4]
    exact (hstep C.gates (List.ofFn x ++ [x 0 || x 4, b10])
      (List.ofFn (x ∘ tau) ++ [x 0 || x 4, b10]) (by simp) (by simp)
      (by
        intro i hi
        have hmi : mapW i < 9 := by simp only [mapW, hi, dite_true]; exact (tau ⟨i, hi⟩).isLt
        rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, hmi, dite_true,
          Option.getD_some, Function.comp]
        congr 1; exact Fin.ext (by simp [mapW, hi]))
      (by
        intro i hi
        by_cases hi9 : i = 9
        · subst hi9; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
        · by_cases hi10 : i = 10
          · subst hi10; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]) C.output).symm
  have mapW_eq4 : ∀ w : ℕ, mapW w = 4 ↔ w = 4 := by
    intro w
    by_cases hw : w < 9
    · simp only [mapW, hw, dite_true]
      have : ∀ k : Fin 9, (tau k).val = 4 ↔ k.val = 4 := by decide
      exact this ⟨w, hw⟩
    · simp only [mapW, hw, dite_false]
  have mapCirc_fan : FanInTwo (mapCirc D) := by
    intro g hg
    simp only [mapCirc, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [mapGate] using hD_fan g0 hg0
  have mapCirc_size : (mapCirc D).size ≤ 13 := by
    change (D.gates.map mapGate).length ≤ 13; rw [List.length_map]; exact hD_size
  have mapCirc_mem4 : ∀ g : Gate, (4 ∈ (mapGate g).inputs) ↔ (4 ∈ g.inputs) := by
    intro g; simp only [mapGate, List.mem_map]
    exact ⟨fun h => by obtain ⟨w, hw, h4⟩ := h; exact (mapW_eq4 w).mp h4 ▸ hw,
           fun h4 => ⟨4, h4, (mapW_eq4 4).mpr rfl⟩⟩
  -- 10. Simplify wVal10 x.
  have hread_le : ∀ (x : Fin 9 → Bool) (i : Fin 26), i.val ≠ 9 → i.val ≠ 25 →
      readR (List.ofFn x ++ [x 0 || x 4]) i =
        if h : i.val < 9 then x ⟨i.val, h⟩ else false := by
    intro x i h9 h25
    simp only [readR, h25, ite_false]
    split_ifs with hlt
    · rw [List.getD_append _ _ _ _ (by simp; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
  have hw10_eq : ∀ x : Fin 9 → Bool,
      wVal10 x =
        ((if h1 : x1.val < 9 then x ⟨x1.val, h1⟩ else false) ||
         (if h2 : x2.val < 9 then x ⟨x2.val, h2⟩ else false)) := by
    intro x; simp only [wVal10, hread_le x x1 hne9.1 hx1_25, hread_le x x2 hne9.2 hx2_25]
  have kill_deg_or_has4 : ∀ (v10 : Sum Bool ℕ),
      (∀ k, v10 = Sum.inr k → k < 8) →
      (∀ y : Fin 8 → Bool, wVal10 (ins4 y) = evalS (List.ofFn y) v10) →
      (∃ g ∈ D.gates, 4 ∈ g.inputs ∨ (v10 = Sum.inl false ∧ 10 ∈ g.inputs)) → False := by
    intro v10 hv10_bd hv10_ev hex
    obtain ⟨g, hg, hread⟩ := hex
    obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
    let env8 : List (Sum Bool ℕ) :=
      [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
       Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 0, v10]
    have henv8_bd : ∀ v ∈ env8, ∀ k, v = Sum.inr k → k < 8 + ([] : List Gate).length := by
      intro v hv k hk
      simp only [env8, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | (have := hv10_bd k hk; simp; omega) | (cases hk; omega) | cases hk
    obtain ⟨_, _, _, _, _, _, hdrop, _⟩ :=
      compListC_inv 8 D.gates [] env8 none hD_cl (fun _ _ _ _ h => by cases h)
        (by simp) (by intro i hi; simp at hi) henv8_bd
    have hconst : ∃ i ∈ D.gates[j].inputs, ∃ b,
        ((D.gates.take j).foldl (compGateC 8) ([], env8)).2.getD i (Sum.inl false) = Sum.inl b := by
      rcases hread with h4 | ⟨hv10f, h10⟩
      · refine ⟨4, hgj ▸ h4, false, ?_⟩
        rw [compListC_env_eq 8 (D.gates.take j) [] env8
          (fun g' hg' => hD_cl g' (List.mem_of_mem_take hg'))
          (by simp) (by intro i hi; simp at hi) henv8_bd 4 (by simp [env8])]; rfl
      · refine ⟨10, hgj ▸ h10, false, ?_⟩
        rw [compListC_env_eq 8 (D.gates.take j) [] env8
          (fun g' hg' => hD_cl g' (List.mem_of_mem_take hg'))
          (by simp) (by intro i hi; simp at hi) henv8_bd 10 (by simp [env8])]
        simp [env8, hv10f]
    have hle12 : (D.gates.foldl (compGateC 8) ([], env8)).1.length ≤ 12 := by
      have h1 := hdrop j hj hconst
      change D.gates.length ≤ 13 at hD_size
      simp only [List.length_nil, Nat.zero_add] at h1; omega
    exact restrict_to_G6 [] v10 (by simp) (by intro i hi; simp at hi)
      (by intro k hk; simpa using hv10_bd k hk) (by intro y; simpa using hv10_ev y) hle12
  -- 11. Case split on (x1, x2).
  by_cases hdeg : x1.val = x2.val ∨ 10 ≤ x1.val ∨ 10 ≤ x2.val
  · have hcases : (∀ x, wVal10 x = false) ∨ (∃ a : Fin 9, ∀ x, wVal10 x = x a) := by
      rcases hdeg with heq | h10 | h10
      · by_cases h1 : x1.val < 9
        · right; refine ⟨⟨x1.val, h1⟩, fun x => ?_⟩
          have h2 : x2.val < 9 := by omega
          rw [hw10_eq x]; simp only [h1, h2, dite_true]
          have : (⟨x2.val, h2⟩ : Fin 9) = ⟨x1.val, h1⟩ := Fin.ext heq.symm
          rw [this, Bool.or_self]
        · left; intro x; rw [hw10_eq x]; have h2 : ¬ x2.val < 9 := (by omega); simp [h1, h2]
      · by_cases h2 : x2.val < 9
        · right; refine ⟨⟨x2.val, h2⟩, fun x => ?_⟩
          have h1 : ¬ x1.val < 9 := (by omega); rw [hw10_eq x]; simp [h1, h2]
        · left; intro x; rw [hw10_eq x]; have h1 : ¬ x1.val < 9 := (by omega); simp [h1, h2]
      · by_cases h1 : x1.val < 9
        · right; refine ⟨⟨x1.val, h1⟩, fun x => ?_⟩
          have h2 : ¬ x2.val < 9 := (by omega); rw [hw10_eq x]; simp [h1, h2]
        · left; intro x; rw [hw10_eq x]; have h2 : ¬ x2.val < 9 := (by omega); simp [h1, h2]
    rcases hcases with hwfalse | ⟨a, hwa⟩
    · by_cases h4 : ∃ g ∈ D.gates, 4 ∈ g.inputs
      · exact kill_deg_or_has4 (Sum.inl false) (fun _ h => by cases h) (fun y => by simp [hwfalse, evalS])
          (by obtain ⟨g, hg, h⟩ := h4; exact ⟨g, hg, Or.inl h⟩)
      · push_neg at h4
        exact no4_contra_pair (fun i => decide (i = 0)) (fun i => decide (i = 0 ∨ i = 4)) h4
          (by intro i hi; simp [hi]) (by decide) (by simp [hwfalse]) (by decide)
    · by_cases ha4 : a = 4
      · subst ha4
        by_cases h410 : ∃ g ∈ D.gates, 4 ∈ g.inputs ∨ 10 ∈ g.inputs
        · exact kill_deg_or_has4 (Sum.inl false) (fun _ h => by cases h)
            (fun y => by simp [hwa, ins4, evalS])
            (by obtain ⟨g, hg, h⟩ := h410; exact ⟨g, hg, by rcases h with h | h; exact Or.inl h; exact Or.inr ⟨rfl, h⟩⟩)
        · push_neg at h410
          have hD_out_ne10 : D.output ≠ 10 := by
            intro heq
            let x4only : Fin 9 → Bool := fun i => decide (i = 4)
            have h1 := hD_ev x4only
            have h2 : f9 x4only = false := by decide
            rw [h2] at h1
            have h3 : D.eval (List.ofFn x4only ++ [x4only 0 || x4only 4, wVal10 x4only]) = true := by
              change (D.gates.foldl stepC _).getD D.output false = true; rw [heq]
              have hlt : ∀ (gs : List Gate) (w : List Bool), 10 < w.length →
                  (gs.foldl stepC w).getD 10 false = w.getD 10 false := by
                intro gs; induction gs with
                | nil => intro w _; rfl
                | cons g rest ih => intro w hw; rw [List.foldl_cons, ih _ (by simp [stepC]; omega), stepC_snoc_lt _ _ _ hw]
              rw [hlt _ _ (by simp)]
              simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, hwa, x4only]
            rw [h3] at h1; cases h1
          have hsame := agree_off_set (fun w => w = 4 ∨ w = 10) D.gates
            (fun g hg w hw h => by rcases h with rfl | rfl; exact (h410 g hg).1 hw; exact (h410 g hg).2 hw)
            (List.ofFn (fun i : Fin 9 => decide (i = 0)) ++ [true, false])
            (List.ofFn (fun i : Fin 9 => decide (i = 0 ∨ i = 4)) ++ [true, true]) (by simp) (by
              intro i hi; push_neg at hi
              by_cases hlt : i < 9
              · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
                simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
                have : (⟨i, hlt⟩ : Fin 9) ≠ 4 := fun h => hi.1 (congrArg Fin.val h)
                simp [this]
              · by_cases hi9 : i = 9
                · subst hi9; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
                · by_cases hi10 : i = 10
                  · exact (hi.2 hi10).elim
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
            D.output (fun h => by rcases h with h | h; exact hD_out_ne4 h; exact hD_out_ne10 h)
          have h1 := hD_ev (fun i : Fin 9 => decide (i = 0))
          have h2 := hD_ev (fun i : Fin 9 => decide (i = 0 ∨ i = 4))
          have hw1 : wVal10 (fun i : Fin 9 => decide (i = 0)) = false := by rw [hwa]; decide
          have hw2 : wVal10 (fun i : Fin 9 => decide (i = 0 ∨ i = 4)) = true := by rw [hwa]; decide
          have hf1 : f9 (fun i : Fin 9 => decide (i = 0)) = false := by decide
          have hf2 : f9 (fun i : Fin 9 => decide (i = 0 ∨ i = 4)) = true := by decide
          rw [hw1, hf1] at h1; rw [hw2, hf2] at h2
          have : false = true := h1.symm.trans (hsame.trans h2); cases this
      · have ha4' : a.val ≠ 4 := fun h => ha4 (Fin.ext h)
        by_cases h4 : ∃ g ∈ D.gates, 4 ∈ g.inputs
        · refine kill_deg_or_has4 (Sum.inr (idx8 a.val))
            (by intro k hk; cases hk; dsimp only [idx8]; split_ifs <;> omega)
            (fun y => ?_) (by obtain ⟨g, hg, h⟩ := h4; exact ⟨g, hg, Or.inl h⟩)
          rw [hwa]
          have hget := hins4_getD y a.val a.isLt ha4'
          have hl : (List.ofFn (ins4 y)).getD a.val false = ins4 y a := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, a.isLt, dite_true, Option.getD_some]
          rw [← hl]; exact hget
        · push_neg at h4
          exact no4_contra_pair (fun i => decide (i = 0)) (fun i => decide (i = 0 ∨ i = 4)) h4
            (by intro i hi; simp [hi]) (by decide)
            (by rw [hwa, hwa]; simp [ha4]) (by decide)
  · push_neg at hdeg
    have hx1_lt : x1.val < 9 := by have := hne9.1; omega
    have hx2_lt : x2.val < 9 := by have := hne9.2; omega
    let a1 : Fin 9 := ⟨x1.val, hx1_lt⟩
    let a2 : Fin 9 := ⟨x2.val, hx2_lt⟩
    have ha12_ne : a1 ≠ a2 := fun h => hdeg.1 (congrArg (fun z : Fin 9 => z.val) h)
    have hw10_pair : ∀ x : Fin 9 → Bool, wVal10 x = (x a1 || x a2) := by
      intro x; rw [hw10_eq x]; simp [hx1_lt, hx2_lt, a1, a2]
    by_cases hhas4_gate1 : a1 = 4 ∨ a2 = 4
    · obtain ⟨a, ha4, hw10_4a⟩ : ∃ a : Fin 9, a ≠ 4 ∧ ∀ x : Fin 9 → Bool, wVal10 x = (x 4 || x a) := by
        rcases hhas4_gate1 with h1 | h2
        · exact ⟨a2, fun h => ha12_ne (h1.trans h.symm), fun x => by rw [hw10_pair x, h1]⟩
        · exact ⟨a1, fun h => ha12_ne (h.trans h2.symm), fun x => by rw [hw10_pair x, h2, Bool.or_comm]⟩
      have ha4' : a.val ≠ 4 := fun h => ha4 (Fin.ext h)
      by_cases h4 : ∃ g ∈ D.gates, 4 ∈ g.inputs
      · refine kill_deg_or_has4 (Sum.inr (idx8 a.val))
          (by intro k hk; cases hk; dsimp only [idx8]; split_ifs <;> omega)
          (fun y => ?_) (by obtain ⟨g, hg, h⟩ := h4; exact ⟨g, hg, Or.inl h⟩)
        rw [hw10_4a]
        have h4f : ins4 y 4 = false := by simp [ins4]
        rw [h4f, Bool.false_or]
        have hget := hins4_getD y a.val a.isLt ha4'
        have hl : (List.ofFn (ins4 y)).getD a.val false = ins4 y a := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, a.isLt, dite_true, Option.getD_some]
        rw [← hl]; exact hget
      · push_neg at h4
        by_cases ha15 : a = 1 ∨ a = 5
        · rcases ha15 with rfl | rfl
          · exact h41 ⟨D, hD_fan, hD_size, h4, fun x => by simpa [hw10_4a x] using hD_ev x⟩
          · refine h41 ⟨mapCirc D, mapCirc_fan, mapCirc_size, ?_, ?_⟩
            · intro g hg; simp only [mapCirc, List.mem_map] at hg
              obtain ⟨g0, hg0, rfl⟩ := hg; rw [mapCirc_mem4]; exact h4 g0 hg0
            · intro x; rw [mapCirc_eval]
              have he := hD_ev (x ∘ tau); rw [htau_f9] at he
              have hw : wVal10 (x ∘ tau) = (x 4 || x 1) := by rw [hw10_4a]; rfl
              simpa [hw] using he
        · push_neg at ha15
          refine no4_contra_pair (fun i => decide (i = 0 ∨ i = a))
            (fun i => decide (i = 0 ∨ i = a ∨ i = 4)) h4
            (by intro i hi; simp [hi]) (by simp) (by rw [hw10_4a, hw10_4a]; simp) ?_
          have hf9_a : ∀ k : Fin 9, k ≠ 1 → k ≠ 5 → k ≠ 4 →
              f9 (fun i => decide (i = 0 ∨ i = k)) ≠ f9 (fun i => decide (i = 0 ∨ i = k ∨ i = 4)) := by
            decide
          exact hf9_a a ha15.1 ha15.2 ha4
    · push_neg at hhas4_gate1
      have ha1_ne4 : a1.val ≠ 4 := fun h => hhas4_gate1.1 (Fin.ext h)
      have ha2_ne4 : a2.val ≠ 4 := fun h => hhas4_gate1.2 (Fin.ext h)
      let gs1 : List Gate := [⟨GateOp.or, [idx8 a1.val, idx8 a2.val]⟩]
      have hgs1_cl : ∀ gt ∈ gs1, CleanGate gt := by
        intro gt hg; simp only [gs1, List.mem_singleton] at hg; subst hg; exact Or.inl ⟨Or.inr rfl, rfl⟩
      have hgs1_rb : ∀ (j : ℕ) (hj : j < gs1.length), ∀ w ∈ gs1[j].inputs, w < 8 + j := by
        intro j hj w hw
        have hj0 : j = 0 := by simp [gs1] at hj; omega
        subst hj0
        simp only [gs1, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> (dsimp only [idx8]; split_ifs <;> omega)
      have hgs1_ev : ∀ y : Fin 8 → Bool, wVal10 (ins4 y) = evalS (gs1.foldl stepC (List.ofFn y)) (Sum.inr 8) := by
        intro y; rw [hw10_pair]
        simp only [gs1, List.foldl_cons, List.foldl_nil, evalS]
        have hlen8 : (List.ofFn y).length = 8 := by simp
        have hsnoc := stepC_snoc_self (List.ofFn y) ⟨GateOp.or, [idx8 a1.val, idx8 a2.val]⟩
        rw [hlen8] at hsnoc
        rw [hsnoc]
        have h1 := hins4_getD y a1.val a1.isLt ha1_ne4
        have h2 := hins4_getD y a2.val a2.isLt ha2_ne4
        have hl1 : (List.ofFn (ins4 y)).getD a1.val false = ins4 y a1 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, a1.isLt, dite_true, Option.getD_some]
        have hl2 : (List.ofFn (ins4 y)).getD a2.val false = ins4 y a2 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, a2.isLt, dite_true, Option.getD_some]
        rw [hl1] at h1; rw [hl2] at h2
        rw [h1, h2]
        simp only [List.map_cons, List.map_nil, heval_or]
      let env8C : List (Sum Bool ℕ) :=
        [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
         Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 0, Sum.inr 8]
      have henv8C_bd : ∀ v ∈ env8C, ∀ k, v = Sum.inr k → k < 8 + gs1.length := by
        intro v hv k hk
        simp only [env8C, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | (cases hk; have : gs1.length = 1 := rfl; omega) | cases hk
      by_cases h4 : ∃ g ∈ D.gates, 4 ∈ g.inputs
      · let r4 := D.gates.filter (fun g => decide (4 ∈ g.inputs))
        have hr4_pos : 1 ≤ r4.length := by
          obtain ⟨g, hg, h4g⟩ := h4
          exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true h4g⟩)
        by_cases hge2 : 2 ≤ r4.length
        · have hex2 : ∃ (j1 j2 : ℕ) (hj1 : j1 < D.gates.length) (hj2 : j2 < D.gates.length),
              j1 < j2 ∧ 4 ∈ D.gates[j1].inputs ∧ 4 ∈ D.gates[j2].inputs := by
            have haux : ∀ (l : List Gate), 2 ≤ (l.filter (fun g => decide (4 ∈ g.inputs))).length →
                ∃ (j1 j2 : ℕ) (hj1 : j1 < l.length) (hj2 : j2 < l.length),
                  j1 < j2 ∧ 4 ∈ l[j1].inputs ∧ 4 ∈ l[j2].inputs := by
              intro l; induction l with
              | nil => intro h; simp at h
              | cons g rest ih =>
                intro h
                by_cases hg : 4 ∈ g.inputs
                · simp only [List.filter_cons, decide_eq_true hg, ite_true, List.length_cons] at h
                  have hne : (rest.filter (fun g => decide (4 ∈ g.inputs))) ≠ [] := by
                    intro he; rw [he] at h; simp at h
                  obtain ⟨g2, hg2⟩ := List.exists_mem_of_ne_nil _ hne
                  obtain ⟨hg2m, hg24⟩ := List.mem_filter.mp hg2
                  obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg2m
                  exact ⟨0, k + 1, by simp, by simp; omega, by omega, hg, hgk ▸ of_decide_eq_true hg24⟩
                · simp only [List.filter_cons, decide_eq_false hg, Bool.false_eq_true, ite_false] at h
                  obtain ⟨j1, j2, hj1, hj2, hlt, h1, h2⟩ := ih h
                  exact ⟨j1 + 1, j2 + 1, by simp; omega, by simp; omega, by omega, h1, h2⟩
            exact haux D.gates hge2
          obtain ⟨j1, j2, hj1, hj2, hlt, h41', h42'⟩ := hex2
          have hc1 : ∃ i ∈ D.gates[j1].inputs, ∃ b,
              ((D.gates.take j1).foldl (compGateC 8) (gs1, env8C)).2.getD i (Sum.inl false) = Sum.inl b :=
            ⟨4, h41', false, by
              rw [compListC_env_eq 8 (D.gates.take j1) gs1 env8C
                (fun g' hg' => hD_cl g' (List.mem_of_mem_take hg')) hgs1_cl hgs1_rb henv8C_bd
                4 (by simp [env8C])]; rfl⟩
          have hc2 : ∃ i ∈ D.gates[j2].inputs, ∃ b,
              ((D.gates.take j2).foldl (compGateC 8) (gs1, env8C)).2.getD i (Sum.inl false) = Sum.inl b :=
            ⟨4, h42', false, by
              rw [compListC_env_eq 8 (D.gates.take j2) gs1 env8C
                (fun g' hg' => hD_cl g' (List.mem_of_mem_take hg')) hgs1_cl hgs1_rb henv8C_bd
                4 (by simp [env8C])]; rfl⟩
          have hle12 : (D.gates.foldl (compGateC 8) (gs1, env8C)).1.length ≤ 12 := by
            have h2 := compListC_save2 8 D.gates gs1 env8C j1 j2 hj1 hj2 hlt hD_cl hgs1_cl hgs1_rb henv8C_bd hc1 hc2
            change D.gates.length ≤ 13 at hD_size
            have hgs1_len : gs1.length = 1 := rfl
            omega
          exact restrict_to_G6 gs1 (Sum.inr 8) hgs1_cl hgs1_rb (by intro k hk; cases hk; simp [gs1]) hgs1_ev hle12
        · have hr4_eq1 : r4.length = 1 := by omega
          by_cases hall_or : ∀ g ∈ D.gates, 4 ∈ g.inputs → g.op = GateOp.or
          · have hitA : ∀ p ∈ ([(0, 3), (0, 1), (0, 2), (0, 6), (3, 1), (3, 2), (3, 6), (1, 5)] : List (Fin 9 × Fin 9)),
                (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) = f9 x) → False :=
              fun p hp hev => hPairsA p hp ⟨D, hD_fan, hD_size, hr4_eq1, hall_or, hev⟩
            have hitB : ∀ p ∈ ([(2, 8), (6, 7), (1, 2), (1, 8), (1, 6), (1, 7), (2, 6), (2, 7)] : List (Fin 9 × Fin 9)),
                (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) = f9 x) → False :=
              fun p hp hev => hPairsB p hp ⟨D, hD_fan, hD_size, hr4_eq1, hall_or, hev⟩
            have hDtau_r4 : ((mapCirc D).gates.filter (fun g => decide (4 ∈ g.inputs))).length = 1 := by
              change ((D.gates.map mapGate).filter (fun g => decide (4 ∈ g.inputs))).length = 1
              rw [List.filter_map, List.length_map]
              have hfeq : ((fun g : Gate => decide (4 ∈ g.inputs)) ∘ mapGate) =
                  (fun g : Gate => decide (4 ∈ g.inputs)) := by funext g; simp [Function.comp, mapCirc_mem4]
              rw [hfeq]; exact hr4_eq1
            have hDtau_or : ∀ g ∈ (mapCirc D).gates, 4 ∈ g.inputs → g.op = GateOp.or := by
              intro g hg h4g; simp only [mapCirc, List.mem_map] at hg
              obtain ⟨g0, hg0, rfl⟩ := hg; exact hall_or g0 hg0 ((mapCirc_mem4 g0).mp h4g)
            have hitAtau : ∀ p ∈ ([(0, 3), (0, 1), (0, 2), (0, 6), (3, 1), (3, 2), (3, 6), (1, 5)] : List (Fin 9 × Fin 9)),
                (∀ x : Fin 9 → Bool, (mapCirc D).eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) = f9 x) → False :=
              fun p hp hev => hPairsA p hp ⟨mapCirc D, mapCirc_fan, mapCirc_size, hDtau_r4, hDtau_or, hev⟩
            have hitBtau : ∀ p ∈ ([(2, 8), (6, 7), (1, 2), (1, 8), (1, 6), (1, 7), (2, 6), (2, 7)] : List (Fin 9 × Fin 9)),
                (∀ x : Fin 9 → Bool, (mapCirc D).eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) = f9 x) → False :=
              fun p hp hev => hPairsB p hp ⟨mapCirc D, mapCirc_fan, mapCirc_size, hDtau_r4, hDtau_or, hev⟩
            have hD_ev_pair : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x a1 || x a2]) = f9 x :=
              fun x => by simpa [hw10_pair x] using hD_ev x
            have hD_ev_swap : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, x a2 || x a1]) = f9 x :=
              fun x => by rw [Bool.or_comm (x a2) (x a1)]; exact hD_ev_pair x
            have hD_ev_tau : ∀ x : Fin 9 → Bool,
                (mapCirc D).eval (List.ofFn x ++ [x 0 || x 4, x (tau a1) || x (tau a2)]) = f9 x := by
              intro x; rw [mapCirc_eval, ← htau_f9 x]
              simpa [Function.comp, htau_inv] using hD_ev_pair (x ∘ tau)
            have hD_ev_tauswap : ∀ x : Fin 9 → Bool,
                (mapCirc D).eval (List.ofFn x ++ [x 0 || x 4, x (tau a2) || x (tau a1)]) = f9 x :=
              fun x => by rw [Bool.or_comm (x (tau a2)) (x (tau a1))]; exact hD_ev_tau x
            let pA : List (Fin 9 × Fin 9) := [(0, 3), (0, 1), (0, 2), (0, 6), (3, 1), (3, 2), (3, 6), (1, 5)]
            let pB : List (Fin 9 × Fin 9) := [(2, 8), (6, 7), (1, 2), (1, 8), (1, 6), (1, 7), (2, 6), (2, 7)]
            let memP : List (Fin 9 × Fin 9) → Fin 9 × Fin 9 → Bool :=
              fun l p => l.any (fun q => decide (q.1 = p.1) && decide (q.2 = p.2))
            have hmemP : ∀ l p, memP l p = true → p ∈ l := by
              intro l p h
              simp only [memP, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨⟨q1, q2⟩, hq, h1, h2⟩ := h
              cases p; subst h1; subst h2; exact hq
            have hpair_orbit_b : ∀ u v : Fin 9,
                (decide (u = v) || decide (u = 4) || decide (v = 4) ||
                 memP pA (u, v) || memP pA (v, u) || memP pB (u, v) || memP pB (v, u) ||
                 memP pA (tau u, tau v) || memP pA (tau v, tau u) ||
                 memP pB (tau u, tau v) || memP pB (tau v, tau u)) = true := by
              decide
            have horb := hpair_orbit_b a1 a2
            simp only [decide_eq_false ha12_ne, decide_eq_false hhas4_gate1.1, decide_eq_false hhas4_gate1.2,
              Bool.false_or, Bool.or_eq_true] at horb
            rcases horb with ((((((h | h) | h) | h) | h) | h) | h) | h
            · exact hitA _ (hmemP pA _ h) hD_ev_pair
            · exact hitA _ (hmemP pA _ h) hD_ev_swap
            · exact hitB _ (hmemP pB _ h) hD_ev_pair
            · exact hitB _ (hmemP pB _ h) hD_ev_swap
            · exact hitAtau _ (hmemP pA _ h) hD_ev_tau
            · exact hitAtau _ (hmemP pA _ h) hD_ev_tauswap
            · exact hitBtau _ (hmemP pB _ h) hD_ev_tau
            · exact hitBtau _ (hmemP pB _ h) hD_ev_tauswap
          · push_neg at hall_or
            obtain ⟨g, hg, h4g, hneor⟩ := hall_or
            obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
            have hneor' : D.gates[j].op ≠ GateOp.or := hgj.symm ▸ hneor
            have h4j : 4 ∈ D.gates[j].inputs := hgj.symm ▸ h4g
            let prefj := D.gates.take j
            let stj := prefj.foldl (compGateC 8) (gs1, env8C)
            obtain ⟨hcl_j, hrb_j, hbd_j, _, helen_j, hkeep_j, _, _⟩ :=
              compListC_inv 8 prefj gs1 env8C none
                (fun g' hg' => hD_cl g' (List.mem_of_mem_take hg'))
                (fun _ _ _ _ h => by cases h) hgs1_cl hgs1_rb henv8C_bd
            have h4_stj : stj.2.getD 4 (Sum.inl false) = Sum.inl false := by
              rw [hkeep_j 4 (by simp [env8C])]; rfl
            obtain ⟨_, _, _, _, _, hconst_j, _, _, _⟩ :=
              compGateC_inv 8 stj.1 stj.2 D.gates[j] (hD_cl _ (List.getElem_mem hj)) hcl_j hrb_j hbd_j
            obtain ⟨bj, hbj⟩ := hconst_j ⟨4, h4j, h4_stj⟩ hneor'
            have hlen_stj : stj.2.length = 11 + j := by
              have hplen : prefj.length = j := List.length_take_of_le (by omega)
              have helen_j' : stj.2.length = env8C.length + prefj.length := helen_j
              have henv_len : env8C.length = 11 := rfl
              omega
            rcases hD_live j hj with hjout | ⟨m, hm, hjm, hreadm⟩
            · have hsplit : D.gates = prefj ++ [D.gates[j]] ++ D.gates.drop (j + 1) := by
                conv_lhs => rw [← List.take_append_drop j D.gates, List.drop_eq_getElem_cons hj]
                simp [prefj]
              let stj1 := compGateC 8 stj D.gates[j]
              obtain ⟨hcl_j1, hrb_j1, hbd_j1, _, _, _, helen_j1, _, _⟩ :=
                compGateC_inv 8 stj.1 stj.2 D.gates[j] (hD_cl _ (List.getElem_mem hj)) hcl_j hrb_j hbd_j
              have helen_j1' : stj1.2.length = stj.2.length + 1 := helen_j1
              have hout_const : (D.gates.foldl (compGateC 8) (gs1, env8C)).2.getD D.output (Sum.inl false) =
                  Sum.inl bj := by
                rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
                rw [compListC_env_eq 8 (D.gates.drop (j + 1)) stj1.1 stj1.2
                  (fun g' hg' => hD_cl g' (List.mem_of_mem_drop hg')) hcl_j1 hrb_j1 hbd_j1
                  D.output (by omega)]
                rw [← hjout, ← hlen_stj]; exact hbj
              obtain ⟨_, hD8_ev⟩ := restrict_eval gs1 (Sum.inr 8) hgs1_cl hgs1_rb
                (by intro k hk; cases hk; simp [gs1]) hgs1_ev
              obtain ⟨y, hy⟩ := hf8_nonconst bj
              have he := hD8_ev y
              rw [hout_const] at he
              exact hy he.symm
            · have hsplit_m : D.gates.take m = prefj ++ [D.gates[j]] ++ (D.gates.take m).drop (j + 1) := by
                have hlen_tm : (D.gates.take m).length = m := List.length_take_of_le (by omega)
                have htake_j : (D.gates.take m).take j = prefj := by
                  simp [prefj, List.take_take, Nat.min_eq_left (by omega : j ≤ m)]
                have hget_j : (D.gates.take m)[j]'(by omega) = D.gates[j] := List.getElem_take
                conv_lhs => rw [← List.take_append_drop j (D.gates.take m),
                  List.drop_eq_getElem_cons (by omega : j < (D.gates.take m).length)]
                rw [htake_j, hget_j]; simp
              let stj1 := compGateC 8 stj D.gates[j]
              obtain ⟨hcl_j1, hrb_j1, hbd_j1, _, _, _, helen_j1, _, _⟩ :=
                compGateC_inv 8 stj.1 stj.2 D.gates[j] (hD_cl _ (List.getElem_mem hj)) hcl_j hrb_j hbd_j
              have helen_j1' : stj1.2.length = stj.2.length + 1 := helen_j1
              have hconst_m : ((D.gates.take m).foldl (compGateC 8) (gs1, env8C)).2.getD (11 + j) (Sum.inl false) =
                  Sum.inl bj := by
                rw [hsplit_m, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
                rw [compListC_env_eq 8 ((D.gates.take m).drop (j + 1)) stj1.1 stj1.2
                  (fun g' hg' => hD_cl g' (List.mem_of_mem_take (List.mem_of_mem_drop hg')))
                  hcl_j1 hrb_j1 hbd_j1 (11 + j) (by omega)]
                rw [← hlen_stj]; exact hbj
              have hc1 : ∃ i ∈ D.gates[j].inputs, ∃ b,
                  ((D.gates.take j).foldl (compGateC 8) (gs1, env8C)).2.getD i (Sum.inl false) = Sum.inl b :=
                ⟨4, h4j, false, h4_stj⟩
              have hc2 : ∃ i ∈ D.gates[m].inputs, ∃ b,
                  ((D.gates.take m).foldl (compGateC 8) (gs1, env8C)).2.getD i (Sum.inl false) = Sum.inl b :=
                ⟨11 + j, hreadm, bj, hconst_m⟩
              have hle12 : (D.gates.foldl (compGateC 8) (gs1, env8C)).1.length ≤ 12 := by
                have h2 := compListC_save2 8 D.gates gs1 env8C j m hj hm hjm hD_cl hgs1_cl hgs1_rb henv8C_bd hc1 hc2
                change D.gates.length ≤ 13 at hD_size
                have hgs1_len : gs1.length = 1 := rfl
                omega
              exact restrict_to_G6 gs1 (Sum.inr 8) hgs1_cl hgs1_rb (by intro k hk; cases hk; simp [gs1]) hgs1_ev hle12
      · push_neg at h4
        refine no4_contra_pair (fun i => decide (i = 0)) (fun i => decide (i = 0 ∨ i = 4)) h4
          (by intro i hi; simp [hi]) (by decide) ?_ (by decide)
        rw [hw10_pair, hw10_pair]; simp [hhas4_gate1.1, hhas4_gate1.2]
