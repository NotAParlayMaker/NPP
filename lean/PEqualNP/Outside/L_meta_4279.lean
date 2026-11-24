import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4279

open PEqualNP.CircuitLowerBounds PEqualNP.CarriedProduct PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- Plan. Keep the gates that are live on some input of the set and are not the replaced gate.
-- Re-index them, and send every reference to a dropped gate to a wire that does not exist,
-- which reads false. The new circuit is pointwise below the old one, and on an input of the
-- set every live wire keeps the value true.

def dflt : Gate := ⟨GateOp.or, []⟩

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl stp w

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = stp (run gs w) g := by
  simp [run, List.foldl_append]

-- The wires of the first k gates.
def U (gs : List Gate) (x : List Bool) : ℕ → List Bool
  | 0 => x
  | k + 1 => stp (U gs x k) (gs.getD k dflt)

theorem U_length (gs : List Gate) (x : List Bool) (k : ℕ) :
    (U gs x k).length = x.length + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (U gs x k ++ [_]).length = _
    rw [List.length_append, ih]
    rfl

theorem U_congr (gs gs' : List Gate) (x : List Bool) (k : ℕ)
    (h : ∀ j < k, gs.getD j dflt = gs'.getD j dflt) : U gs x k = U gs' x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show stp (U gs x k) (gs.getD k dflt) = stp (U gs' x k) (gs'.getD k dflt)
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]

theorem run_eq_U (gs : List Gate) (x : List Bool) : run gs x = U gs x gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton l g ih =>
    rw [run_snoc, ih, List.length_append, List.length_singleton]
    show _ = stp (U (l ++ [g]) x l.length) ((l ++ [g]).getD l.length dflt)
    have h1 : U (l ++ [g]) x l.length = U l x l.length :=
      U_congr _ _ _ _ (fun j hj => List.getD_append _ _ _ _ hj)
    have h2 : (l ++ [g]).getD l.length dflt = g := by simp
    rw [h1, h2]

theorem U_stable (gs : List Gate) (x : List Bool) (j i : ℕ) (hi : i < x.length + j) (k : ℕ)
    (hk : j ≤ k) : (U gs x k).getD i false = (U gs x j).getD i false := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this
    rfl
  | succ k ih =>
    by_cases h : j = k + 1
    · subst h
      rfl
    · rw [← ih (by omega)]
      show (U gs x k ++ [_]).getD i false = _
      exact List.getD_append _ _ _ _ (by rw [U_length]; omega)

theorem U_gate (gs : List Gate) (x : List Bool) (k : ℕ) :
    (U gs x (k + 1)).getD (x.length + k) false =
      (gs.getD k dflt).op.eval ((gs.getD k dflt).inputs.map fun i => (U gs x k).getD i false) := by
  show (U gs x k ++ [_]).getD (x.length + k) false = _
  rw [← U_length gs x k]
  simp

theorem eval_transfer (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ w ∈ ins, f w = true → f' w = true)
    (hv : op.eval (ins.map f) = true) : op.eval (ins.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv ⊢
    intro w hw
    exact h w hw (hv w hw)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv ⊢
    obtain ⟨w, hw, hval⟩ := hv
    exact ⟨w, hw, h w hw hval⟩

-- The pruned circuit.
def rank (keep : ℕ → Prop) [DecidablePred keep] : ℕ → ℕ
  | 0 => 0
  | k + 1 => if keep k then rank keep k + 1 else rank keep k

def rho (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (k w : ℕ) : ℕ :=
  if w < n then w else if w < n + k ∧ keep (w - n) then n + rank keep (w - n) else M

def pg (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate) (k : ℕ) : Gate :=
  ⟨(gs.getD k dflt).op, (gs.getD k dflt).inputs.map (rho n M keep k)⟩

def PL (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate) : ℕ → List Gate
  | 0 => []
  | k + 1 => if keep k then PL n M keep gs k ++ [pg n M keep gs k] else PL n M keep gs k

def V (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate) (x : List Bool) :
    ℕ → List Bool
  | 0 => x
  | k + 1 => if keep k then stp (V n M keep gs x k) (pg n M keep gs k) else V n M keep gs x k

theorem rank_le (keep : ℕ → Prop) [DecidablePred keep] (k : ℕ) : rank keep k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    show (if keep k then rank keep k + 1 else rank keep k) ≤ k + 1
    split_ifs <;> omega

theorem rank_mono (keep : ℕ → Prop) [DecidablePred keep] (j k : ℕ) (h : j ≤ k) :
    rank keep j ≤ rank keep k := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ k ih =>
    by_cases hj : j = k + 1
    · subst hj
      exact Nat.le_refl _
    · have := ih (by omega)
      show rank keep j ≤ (if keep k then rank keep k + 1 else rank keep k)
      split_ifs <;> omega

theorem rank_lt (keep : ℕ → Prop) [DecidablePred keep] (j k : ℕ) (h : j < k) (hj : keep j) :
    rank keep j < rank keep k := by
  have h1 : rank keep (j + 1) = rank keep j + 1 := by
    show (if keep j then rank keep j + 1 else rank keep j) = _
    rw [if_pos hj]
  have h2 := rank_mono keep (j + 1) k (by omega)
  omega

theorem rank_card (keep : ℕ → Prop) [DecidablePred keep] (k : ℕ) :
    rank keep k = ((Finset.range k).filter keep).card := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    show (if keep k then rank keep k + 1 else rank keep k) = _
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]
    · exact ih

theorem PL_length (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate) (k : ℕ) :
    (PL n M keep gs k).length = rank keep k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (if keep k then PL n M keep gs k ++ [pg n M keep gs k] else PL n M keep gs k).length =
      (if keep k then rank keep k + 1 else rank keep k)
    split_ifs
    · rw [List.length_append, ih]
      rfl
    · exact ih

theorem PL_mem (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate) (k : ℕ) :
    ∀ g ∈ PL n M keep gs k, ∃ j, g = pg n M keep gs j := by
  induction k with
  | zero =>
    intro g hg
    exact absurd hg (List.not_mem_nil)
  | succ k ih =>
    intro g hg
    change g ∈ (if keep k then PL n M keep gs k ++ [pg n M keep gs k] else PL n M keep gs k) at hg
    split_ifs at hg
    · rcases List.mem_append.mp hg with h | h
      · exact ih g h
      · exact ⟨k, List.mem_singleton.mp h⟩
    · exact ih g hg

theorem V_eq_run (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate)
    (x : List Bool) (k : ℕ) : V n M keep gs x k = run (PL n M keep gs k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (if keep k then stp (V n M keep gs x k) (pg n M keep gs k) else V n M keep gs x k) =
      run (if keep k then PL n M keep gs k ++ [pg n M keep gs k] else PL n M keep gs k) x
    split_ifs
    · rw [run_snoc, ih]
    · exact ih

theorem V_length (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate)
    (x : List Bool) (k : ℕ) : (V n M keep gs x k).length = x.length + rank keep k := by
  rw [V_eq_run, ← PL_length n M keep gs k]
  generalize PL n M keep gs k = l
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l g ih =>
    rw [run_snoc]
    show (run l x ++ [_]).length = _
    rw [List.length_append, ih, List.length_append]
    simp only [List.length_singleton]
    omega

theorem V_step (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate)
    (x : List Bool) (k i : ℕ) (hi : i < x.length + rank keep k) :
    (V n M keep gs x (k + 1)).getD i false = (V n M keep gs x k).getD i false := by
  show (if keep k then stp (V n M keep gs x k) (pg n M keep gs k)
    else V n M keep gs x k).getD i false = _
  split_ifs
  · show (V n M keep gs x k ++ [_]).getD i false = _
    exact List.getD_append _ _ _ _ (by rw [V_length]; exact hi)
  · rfl

theorem V_inputs (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate)
    (x : List Bool) (k i : ℕ) (hi : i < x.length) :
    (V n M keep gs x k).getD i false = x.getD i false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [V_step n M keep gs x k i (by omega)]
    exact ih

theorem V_gate (n M : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate)
    (x : List Bool) (k : ℕ) (hk : keep k) :
    (V n M keep gs x (k + 1)).getD (x.length + rank keep k) false =
      (gs.getD k dflt).op.eval ((gs.getD k dflt).inputs.map fun w =>
        (V n M keep gs x k).getD (rho n M keep k w) false) := by
  show (if keep k then stp (V n M keep gs x k) (pg n M keep gs k)
    else V n M keep gs x k).getD _ false = _
  rw [if_pos hk]
  show (V n M keep gs x k ++ [(gs.getD k dflt).op.eval
    (((gs.getD k dflt).inputs.map (rho n M keep k)).map fun i =>
      (V n M keep gs x k).getD i false)]).getD _ false = _
  rw [← V_length n M keep gs x k, List.map_map]
  simp
  rfl

-- The pruned wires are below the wires of any list that agrees on the kept gates.
theorem invA (n M m : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs gs' : List Gate)
    (x : List Bool) (hx : x.length = n) (hM : n + m ≤ M)
    (hmono : ∀ k, (gs.getD k dflt).op = GateOp.and ∨ (gs.getD k dflt).op = GateOp.or)
    (heq : ∀ k, keep k → gs.getD k dflt = gs'.getD k dflt) :
    ∀ k ≤ m, ∀ j < k, keep j → (V n M keep gs x k).getD (n + rank keep j) false = true →
      (U gs' x k).getD (n + j) false = true := by
  subst hx
  intro k
  induction k with
  | zero =>
    intro _ j hj
    omega
  | succ k ih =>
    intro hk j hj hkj hv
    have ihk := ih (by omega)
    by_cases hjk : j = k
    · subst hjk
      rw [V_gate x.length M keep gs x j hkj] at hv
      rw [U_gate, ← heq j hkj]
      refine eval_transfer _ (hmono j) _ _ _ ?_ hv
      intro w _ hw
      unfold rho at hw
      split_ifs at hw with h1 h2
      · rw [V_inputs _ _ _ _ _ _ _ h1] at hw
        rw [U_stable gs' x 0 w (by omega) j (Nat.zero_le _)]
        exact hw
      · have h3 := ihk (w - x.length) (by omega) h2.2 hw
        rwa [show x.length + (w - x.length) = w by omega] at h3
      · rw [List.getD_eq_default _ _ (by
          rw [V_length]
          have := rank_le keep j
          omega)] at hw
        exact absurd hw (by decide)
    · have hjk' : j < k := by omega
      rw [V_step x.length M keep gs x k _ (by
        have := rank_lt keep j k hjk' hkj
        omega)] at hv
      have h3 := ihk j hjk' hkj hv
      rw [U_stable gs' x k (x.length + j) (by omega) (k + 1) (by omega)]
      exact h3

-- On an input where the wires marked by T are true and closed under true operands,
-- every marked gate keeps the value true in the pruned circuit.
theorem invB (n M m : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate)
    (x : List Bool) (hx : x.length = n)
    (hmono : ∀ k, (gs.getD k dflt).op = GateOp.and ∨ (gs.getD k dflt).op = GateOp.or)
    (T : ℕ → Prop)
    (hT1 : ∀ k < m, T (n + k) → keep k)
    (hT2 : ∀ k < m, T (n + k) → (U gs x (k + 1)).getD (n + k) false = true)
    (hT3 : ∀ k < m, T (n + k) → ∀ w ∈ (gs.getD k dflt).inputs,
      (U gs x k).getD w false = true → T w) :
    ∀ k ≤ m, ∀ j < k, T (n + j) → (V n M keep gs x k).getD (n + rank keep j) false = true := by
  subst hx
  intro k
  induction k with
  | zero =>
    intro _ j hj
    omega
  | succ k ih =>
    intro hk j hj hT
    have ihk := ih (by omega)
    by_cases hjk : j = k
    · subst hjk
      have hkeep := hT1 j (by omega) hT
      rw [V_gate x.length M keep gs x j hkeep]
      have old := hT2 j (by omega) hT
      rw [U_gate] at old
      refine eval_transfer _ (hmono j) _ _ _ ?_ old
      intro w hwin hw
      have hTw := hT3 j (by omega) hT w hwin hw
      have hlt : w < x.length + j := by
        by_contra hge
        rw [List.getD_eq_default _ _ (by rw [U_length]; omega)] at hw
        exact absurd hw (by decide)
      unfold rho
      split_ifs with h1 h2
      · rw [V_inputs _ _ _ _ _ _ _ h1]
        rw [U_stable gs x 0 w (by omega) j (Nat.zero_le _)] at hw
        exact hw
      · exact ihk (w - x.length) (by omega)
          (by rwa [show x.length + (w - x.length) = w by omega])
      · exfalso
        apply h2
        exact ⟨hlt, hT1 (w - x.length) (by omega)
          (by rwa [show x.length + (w - x.length) = w by omega])⟩
    · have hjk' : j < k := by omega
      have hkeep := hT1 j (by omega) hT
      rw [V_step x.length M keep gs x k _ (by
        have := rank_lt keep j k hjk' hkeep
        omega)]
      exact ihk j hjk' hT

theorem prune_le (n M m : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs gs' : List Gate)
    (x : List Bool) (o : ℕ) (hx : x.length = n) (hM : n + m ≤ M)
    (hmono : ∀ k, (gs.getD k dflt).op = GateOp.and ∨ (gs.getD k dflt).op = GateOp.or)
    (heq : ∀ k, keep k → gs.getD k dflt = gs'.getD k dflt)
    (hv : (V n M keep gs x m).getD (rho n M keep m o) false = true) :
    (U gs' x m).getD o false = true := by
  have hA := invA n M m keep gs gs' x hx hM hmono heq m (Nat.le_refl m)
  subst hx
  unfold rho at hv
  split_ifs at hv with h1 h2
  · rw [V_inputs _ _ _ _ _ _ _ h1] at hv
    rw [U_stable gs' x 0 o (by omega) m (Nat.zero_le _)]
    exact hv
  · have h3 := hA (o - x.length) (by omega) h2.2 hv
    rwa [show x.length + (o - x.length) = o by omega] at h3
  · rw [List.getD_eq_default _ _ (by
      rw [V_length]
      have := rank_le keep m
      omega)] at hv
    exact absurd hv (by decide)

theorem prune_ge (n M m : ℕ) (keep : ℕ → Prop) [DecidablePred keep] (gs : List Gate)
    (x : List Bool) (o : ℕ) (hx : x.length = n)
    (hmono : ∀ k, (gs.getD k dflt).op = GateOp.and ∨ (gs.getD k dflt).op = GateOp.or)
    (T : ℕ → Prop)
    (hT1 : ∀ k < m, T (n + k) → keep k)
    (hT2 : ∀ k < m, T (n + k) → (U gs x (k + 1)).getD (n + k) false = true)
    (hT3 : ∀ k < m, T (n + k) → ∀ w ∈ (gs.getD k dflt).inputs,
      (U gs x k).getD w false = true → T w)
    (hTo : T o) (hval : (U gs x m).getD o false = true) :
    (V n M keep gs x m).getD (rho n M keep m o) false = true := by
  have hB := invB n M m keep gs x hx hmono T hT1 hT2 hT3 m (Nat.le_refl m)
  subst hx
  have hlt : o < x.length + m := by
    by_contra hge
    rw [List.getD_eq_default _ _ (by rw [U_length]; omega)] at hval
    exact absurd hval (by decide)
  unfold rho
  split_ifs with h1 h2
  · rw [V_inputs _ _ _ _ _ _ _ h1]
    rw [U_stable gs x 0 o (by omega) m (Nat.zero_le _)] at hval
    exact hval
  · exact hB (o - x.length) (by omega) (by rwa [show x.length + (o - x.length) = o by omega])
  · exfalso
    apply h2
    exact ⟨hlt, hT1 (o - x.length) (by omega)
      (by rwa [show x.length + (o - x.length) = o by omega])⟩

-- The backward pass that computes the live wires.
def F (n : ℕ) (C : Circuit) (vals : List Bool) : ℕ → List ℕ → List ℕ
  | 0, L => L
  | k + 1, L => F n C vals k (liveStep n C vals L k)

theorem fold_eq_F (n : ℕ) (C : Circuit) (vals : List Bool) (k : ℕ) :
    ∀ L, ((List.range k).reverse).foldl (liveStep n C vals) L = F n C vals k L := by
  induction k with
  | zero =>
    intro L
    rfl
  | succ k ih =>
    intro L
    rw [List.range_succ, List.reverse_append]
    show List.foldl (liveStep n C vals) (liveStep n C vals L k) (List.range k).reverse = _
    exact ih _

theorem ls_mem (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ) (h : w ∈ L) :
    w ∈ liveStep n C vals L j := by
  unfold liveStep
  split_ifs
  · exact List.mem_append_left _ h
  · exact h

theorem ls_cases (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j v : ℕ)
    (h : v ∈ liveStep n C vals L j) :
    v ∈ L ∨ (n + j ∈ L ∧ v ∈ (C.gates.getD j dflt).inputs ∧ v < n + j ∧
      vals.getD v false = true) := by
  unfold liveStep at h
  split_ifs at h with h0
  · rcases List.mem_append.mp h with h1 | h1
    · exact Or.inl h1
    · right
      rw [List.mem_filter] at h1
      obtain ⟨h2, h3⟩ := h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
      exact ⟨h0, h2, h3.1, h3.2⟩
  · exact Or.inl h

theorem ls_inputs (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j v : ℕ)
    (h0 : n + j ∈ L) (h1 : v ∈ (C.gates.getD j dflt).inputs) (h2 : v < n + j)
    (h3 : vals.getD v false = true) : v ∈ liveStep n C vals L j := by
  unfold liveStep
  rw [if_pos h0]
  apply List.mem_append_right
  rw [List.mem_filter]
  refine ⟨h1, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h2, h3⟩

theorem F_mem (n : ℕ) (C : Circuit) (vals : List Bool) (k : ℕ) :
    ∀ (L : List ℕ) (w : ℕ), w ∈ L → w ∈ F n C vals k L := by
  induction k with
  | zero =>
    intro L w h
    exact h
  | succ k ih =>
    intro L w h
    exact ih _ w (ls_mem n C vals L k w h)

theorem F_small (n : ℕ) (C : Circuit) (vals : List Bool) (k : ℕ) :
    ∀ (L : List ℕ) (v : ℕ), v ∈ F n C vals k L → v ∈ L ∨ v < n + k := by
  induction k with
  | zero =>
    intro L v h
    exact Or.inl h
  | succ k ih =>
    intro L v h
    rcases ih _ v h with h1 | h1
    · rcases ls_cases n C vals L k v h1 with h2 | ⟨_, _, h2, _⟩
      · exact Or.inl h2
      · right
        omega
    · right
      omega

theorem F_true (n : ℕ) (C : Circuit) (vals : List Bool) (k : ℕ) :
    ∀ (L : List ℕ), (∀ w ∈ L, vals.getD w false = true) →
      ∀ w ∈ F n C vals k L, vals.getD w false = true := by
  induction k with
  | zero =>
    intro L hL w h
    exact hL w h
  | succ k ih =>
    intro L hL w h
    refine ih (liveStep n C vals L k) ?_ w h
    intro v hv
    rcases ls_cases n C vals L k v hv with h2 | ⟨_, _, _, h2⟩
    · exact hL v h2
    · exact h2

theorem F_closed (n : ℕ) (C : Circuit) (vals : List Bool) (k : ℕ) :
    ∀ (L : List ℕ) (j : ℕ), j < k → n + j ∈ F n C vals k L →
      ∀ v ∈ (C.gates.getD j dflt).inputs, v < n + j → vals.getD v false = true →
        v ∈ F n C vals k L := by
  induction k with
  | zero =>
    intro L j hj
    omega
  | succ k ih =>
    intro L j hj hmem v hv hlt hval
    change n + j ∈ F n C vals k (liveStep n C vals L k) at hmem
    show v ∈ F n C vals k (liveStep n C vals L k)
    by_cases hjk : j = k
    · subst hjk
      rcases F_small n C vals j _ _ hmem with h | h
      · rcases ls_cases n C vals L j _ h with h1 | ⟨_, _, h1, _⟩
        · exact F_mem n C vals j _ v (ls_inputs n C vals L j v h1 hv hlt hval)
        · omega
      · omega
    · exact ih _ j (by omega) hmem v hv hlt hval

theorem live_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    IsLive n C x w ↔ w ∈ F n C (C.wires (List.ofFn x)) C.gates.length
      (if (C.wires (List.ofFn x)).getD C.output false then [C.output] else []) := by
  unfold IsLive liveWires
  rw [fold_eq_F]

theorem live_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : IsLive n C x w) :
    (C.wires (List.ofFn x)).getD w false = true := by
  rw [live_iff] at h
  refine F_true n C _ _ _ ?_ w h
  intro v hv
  split_ifs at hv with h0
  · rw [List.mem_singleton] at hv
    rw [hv]
    exact h0
  · exact absurd hv (List.not_mem_nil)

theorem live_out (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (h : (C.wires (List.ofFn x)).getD C.output false = true) : IsLive n C x C.output := by
  rw [live_iff]
  apply F_mem
  rw [if_pos h]
  exact List.mem_singleton.mpr rfl

theorem live_closed (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k v : ℕ)
    (hk : k < C.gates.length) (h : IsLive n C x (n + k))
    (hv : v ∈ (C.gates.getD k dflt).inputs) (hlt : v < n + k)
    (hval : (C.wires (List.ofFn x)).getD v false = true) : IsLive n C x v := by
  rw [live_iff] at h ⊢
  exact F_closed n C _ _ _ k hk h v hv hlt hval

theorem getD_good (P : Gate → Prop) (l : List Gate) (hl : ∀ g ∈ l, P g) (hd : P dflt) (k : ℕ) :
    P (l.getD k dflt) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => exact hd
  | some g => exact hl g (List.mem_of_getElem? h)

theorem bool_le (a b : Bool) (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

theorem wires_eq_U (C : Circuit) (x : List Bool) : C.wires x = U C.gates x C.gates.length :=
  run_eq_U C.gates x

end PEqualNP.Outside.L_meta_4279

open PEqualNP.Outside.L_meta_4279 PEqualNP.CircuitLowerBounds PEqualNP.CarriedProduct in
theorem PEqualNP.Outside.L_meta_4279 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Finset (Fin x1 → Bool)),   PEqualNP.MetaComplexity.Monotone2 x2 →     x3 < x2.size →       have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := PEqualNP.NotPremium.replaceByConst x2.gates x3 Bool.false, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ PEqualNP.MetaComplexity.circuitFun x1 x8 ≤ PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ x9 ∈ x4, PEqualNP.MetaComplexity.circuitFun x1 x8 x9 = PEqualNP.MetaComplexity.circuitFun x1 x7 x9) ∧ x8.size ≤ {x9 ∈ (Finset.range x2.size).erase x3 | ∃ x10 ∈ x4, PEqualNP.CarriedProduct.IsLive x1 x7 x10 (x1 + x9)}.card := by
  intro n C2 q S hmono hq
  dsimp only
  classical
  obtain ⟨C7, hC7⟩ : ∃ C7 : Circuit,
      C7 = ⟨PEqualNP.NotPremium.replaceByConst C2.gates q false, C2.output⟩ := ⟨_, rfl⟩
  rw [← hC7]
  have hlen : C7.gates.length = C2.gates.length := by
    rw [hC7]
    simp [PEqualNP.NotPremium.replaceByConst]
  have hout : C7.output = C2.output := by rw [hC7]
  have hq' : q < C2.gates.length := hq
  have good2 : ∀ g ∈ C2.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    simpa using h1
  have good7 : ∀ k, ((C7.gates.getD k dflt).op = GateOp.and ∨
      (C7.gates.getD k dflt).op = GateOp.or) ∧ (C7.gates.getD k dflt).inputs.length ≤ 2 := by
    intro k
    refine getD_good (fun g => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      C7.gates ?_ ⟨Or.inr rfl, by simp [dflt]⟩ k
    intro g hg
    rw [hC7] at hg
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact good2 g h
    · rw [h]
      simp [PEqualNP.NotPremium.constGate]
  have heq72 : ∀ k, k ≠ q → C7.gates.getD k dflt = C2.gates.getD k dflt := by
    intro k hk
    rw [hC7]
    simp only [PEqualNP.NotPremium.replaceByConst, List.getD_eq_getElem?_getD]
    rw [List.getElem?_set_ne (Ne.symm hk)]
  have hgq : C7.gates.getD q dflt = dflt := by
    rw [hC7]
    simp [PEqualNP.NotPremium.replaceByConst, PEqualNP.NotPremium.constGate,
      List.getD_eq_getElem?_getD, hq', dflt]
  let keep : ℕ → Prop := fun k => k ≠ q ∧ ∃ x ∈ S, IsLive n C7 x (n + k)
  let m := C2.gates.length
  let M := n + m
  have hsz : C7.gates.length = m := hlen
  refine ⟨⟨PL n M keep C7.gates m, rho n M keep m C2.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, rfl⟩ := PL_mem n M keep C7.gates m g hg
    obtain ⟨h1, h2⟩ := good7 j
    refine ⟨?_, ?_⟩
    · show (C7.gates.getD j dflt).op ∈ ({GateOp.and, GateOp.or} : Set GateOp)
      rcases h1 with h | h
      · rw [h]
        exact Set.mem_insert _ _
      · rw [h]
        exact Set.mem_insert_of_mem _ rfl
    · show ((C7.gates.getD j dflt).inputs.map (rho n M keep j)).length ≤ 2
      rw [List.length_map]
      exact h2
  · intro x
    apply bool_le
    intro hv
    change (run (PL n M keep C7.gates m) (List.ofFn x)).getD (rho n M keep m C2.output) false
      = true at hv
    rw [← V_eq_run] at hv
    show (C2.wires (List.ofFn x)).getD C2.output false = true
    rw [wires_eq_U]
    exact prune_le n M m keep C7.gates C2.gates (List.ofFn x) C2.output (by simp)
      (Nat.le_refl _) (fun k => (good7 k).1) (fun k hk => heq72 k hk.1) hv
  · intro x hxS
    have hX : (List.ofFn x).length = n := by simp
    have hW : C7.wires (List.ofFn x) = U C7.gates (List.ofFn x) m := by
      rw [wires_eq_U, hsz]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hv
      change (run (PL n M keep C7.gates m) (List.ofFn x)).getD (rho n M keep m C2.output) false
        = true at hv
      rw [← V_eq_run] at hv
      show (C7.wires (List.ofFn x)).getD C7.output false = true
      rw [hW, hout]
      exact prune_le n M m keep C7.gates C7.gates (List.ofFn x) C2.output hX
        (Nat.le_refl _) (fun k => (good7 k).1) (fun k _ => rfl) hv
    · intro hv
      change (C7.wires (List.ofFn x)).getD C7.output false = true at hv
      show (run (PL n M keep C7.gates m) (List.ofFn x)).getD (rho n M keep m C2.output) false
        = true
      rw [← V_eq_run]
      have hTo : IsLive n C7 x C2.output := by
        rw [← hout]
        exact live_out n C7 x hv
      rw [hW, hout] at hv
      have hval : ∀ w, IsLive n C7 x w → (U C7.gates (List.ofFn x) m).getD w false = true := by
        intro w hw
        rw [← hW]
        exact live_true n C7 x w hw
      refine prune_ge n M m keep C7.gates (List.ofFn x) C2.output hX (fun k => (good7 k).1)
        (fun w => IsLive n C7 x w) ?_ ?_ ?_ hTo hv
      · intro k hk hT
        refine ⟨?_, x, hxS, hT⟩
        intro hkq
        have h1 := hval _ hT
        rw [hkq, U_stable C7.gates (List.ofFn x) (q + 1) (n + q) (by rw [hX]; omega) m
          (by omega)] at h1
        have hg := U_gate C7.gates (List.ofFn x) q
        rw [hX] at hg
        rw [hg, hgq] at h1
        simp [dflt, GateOp.eval] at h1
      · intro k hk hT
        have h1 := hval _ hT
        rw [U_stable C7.gates (List.ofFn x) (k + 1) (n + k) (by rw [hX]; omega) m
          (by omega)] at h1
        exact h1
      · intro k hk hT w hw hwv
        have hlt : w < n + k := by
          by_contra hge
          rw [List.getD_eq_default _ _ (by rw [U_length, hX]; omega)] at hwv
          exact absurd hwv (by decide)
        refine live_closed n C7 x k w (by rw [hsz]; exact hk) hT hw hlt ?_
        rw [hW, U_stable C7.gates (List.ofFn x) k w (by rw [hX]; exact hlt) m (by omega)]
        exact hwv
  · show (PL n M keep C7.gates m).length ≤ _
    rw [PL_length, rank_card]
    apply Finset.card_le_card
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
    exact ⟨⟨hk.2.1, hk.1⟩, hk.2.2⟩
