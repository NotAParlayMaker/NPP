import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3706_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core

-- evaluation toolkit (step .. val_gate) copied from the merged L_meta_1406
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]


structure Good (n : ℕ) (C : Circuit) : Prop where
  ao : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  rb : ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma two {n : ℕ} {C : Circuit} (hG : Good n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C j hj]
    exact List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hG.ao _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  exact ⟨a, b, hab, hG.rb j hj a (by simp [hab]), hG.rb j hj b (by simp [hab]), hop⟩

lemma val_and {n : ℕ} {C : Circuit} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hin : (gateAt C j).inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (hop : (gateAt C j).op = GateOp.and) :
    val C.gates x (n + j) = (val C.gates x a && val C.gates x b) := by
  rw [val_gate C.gates x j hj, ← gateAt_eq C j hj, hin, hop]
  simp [GateOp.eval, ha, hb]

lemma val_or {n : ℕ} {C : Circuit} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hin : (gateAt C j).inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (hop : (gateAt C j).op = GateOp.or) :
    val C.gates x (n + j) = (val C.gates x a || val C.gates x b) := by
  rw [val_gate C.gates x j hj, ← gateAt_eq C j hj, hin, hop]
  simp [GateOp.eval, ha, hb]

-- generic fold over the gate list (run .. rv_gate), from the submitted L_meta_2672
def run {α : Type} (st : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) init

lemma run_length {α : Type} (st : List α → Gate → α) (gs : List Gate) (init : List α) :
    (run st init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [run]
  | cons g gs ih =>
    have h := ih (init ++ [st init g])
    simp only [run, List.foldl_cons] at h ⊢
    rw [h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    run st init (gs ++ [g]) = run st init gs ++ [st (run st init gs) g] := by
  simp [run, List.foldl_append]

lemma run_getD_snoc {α : Type} (d : α) (st : List α → Gate → α) (init : List α) (gs : List Gate)
    (g : Gate) (i : ℕ) :
    (run st init (gs ++ [g])).getD i d =
      if i = init.length + gs.length then st (run st init gs) g
      else (run st init gs).getD i d := by
  rw [run_snoc]
  have hl := run_length st gs init
  rcases lt_trichotomy i (init.length + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- the value of wire `i` in a generic run -/
def rv {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate) (i : ℕ) : α :=
  (run (fun w g => G g (g.inputs.map fun i => w.getD i d)) init gs).getD i d

lemma rv_snoc {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (g : Gate) (i : ℕ) :
    rv d G init (gs ++ [g]) i =
      if i = init.length + gs.length then G g (g.inputs.map fun j => rv d G init gs j)
      else rv d G init gs i := by
  unfold rv
  rw [run_getD_snoc]

lemma rv_ge {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (i : ℕ) (hi : init.length + gs.length ≤ i) : rv d G init gs i = d := by
  unfold rv
  generalize (fun (w : List α) (g : Gate) => G g (g.inputs.map fun i => w.getD i d)) = st
  have hl := run_length st gs init
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma rv_lt {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (i : ℕ) (hi : i < init.length) : rv d G init gs i = init.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => simp [rv, run]
  | append_singleton gs g ih =>
    rw [rv_snoc, if_neg (by omega)]
    exact ih

lemma rv_gate {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate) :
    ∀ (k : ℕ) (hk : k < gs.length), (∀ j ∈ gs[k].inputs, j < init.length + k) →
      rv d G init gs (init.length + k) =
        G gs[k] (gs[k].inputs.map fun j => rv d G init gs j) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk hrb
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl] at hrb ⊢
      rw [rv_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [rv_snoc, if_neg (by have := hrb j hj; omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget] at hrb ⊢
      rw [rv_snoc, if_neg (by omega), ih k hk2 hrb]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [rv_snoc, if_neg (by have := hrb j hj; omega)]


lemma rv_two {α : Type} (d : α) (G : Gate → List α → α) (init : List α) {n : ℕ} {C : Circuit}
    (hn : init.length = n) (hG : Good n C) (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) :
    rv d G init C.gates (n + j) =
      G (gateAt C j) [rv d G init C.gates a, rv d G init C.gates b] := by
  subst hn
  have h := rv_gate d G init C.gates j hj (by rw [← gateAt_eq C j hj]; exact hG.rb j hj)
  rw [h, ← gateAt_eq C j hj, hin]
  rfl

/-! read vectors -/

def RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

def Gv (S : List ℕ) (k : ℕ) (g : Gate) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma RV_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) :
    RV C n S k w = rv [] (Gv S k) ((List.range n).map (leafVectors S k)) C.gates w := rfl

lemma RV_lt (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    RV C n S k w = leafVectors S k w := by
  rw [RV_eq, rv_lt _ _ _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma RV_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    RV C n S k w = [] := by
  rw [RV_eq, rv_ge _ _ _ _ _ (by simpa using hw)]

lemma mem_insertNew (A : List (List ℕ)) (a v : List ℕ) : v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  split
  · constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · assumption
  · simp

lemma mem_fold_insertNew (A : List (List ℕ)) (v : List ℕ) :
    ∀ acc : List (List ℕ), v ∈ A.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ A := by
  induction A with
  | nil => intro acc; simp
  | cons a A ih =>
    intro acc
    rw [List.foldl_cons, ih, mem_insertNew]
    simp [or_assoc]

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ t ∈ B, v = capAdd k u t := by
  unfold andStep
  rw [mem_fold_insertNew]
  constructor
  · rintro (h | h)
    · simp at h
    · rw [List.mem_flatMap] at h
      obtain ⟨u, hu, h⟩ := h
      rw [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      exact ⟨u, hu, t, ht, rfl⟩
  · rintro ⟨u, hu, t, ht, rfl⟩
    right
    exact List.mem_flatMap.2 ⟨u, hu, List.mem_map.2 ⟨t, ht, rfl⟩⟩

lemma RV_or {n : ℕ} {C : Circuit} (hG : Good n C) (S : List ℕ) (k : ℕ)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) (hop : (gateAt C j).op = GateOp.or) (v : List ℕ) :
    v ∈ RV C n S k (n + j) ↔ v ∈ RV C n S k a ∨ v ∈ RV C n S k b := by
  have e : ∀ w, RV C n S k w = rv [] (Gv S k) ((List.range n).map (leafVectors S k)) C.gates w :=
    fun _ => rfl
  simp only [e]
  rw [rv_two [] (Gv S k) _ (by simp) hG j hj a b hin]
  simp only [Gv, hop, List.foldl_cons, List.foldl_nil]
  rw [mem_fold_insertNew, mem_fold_insertNew]
  simp

lemma RV_and {n : ℕ} {C : Circuit} (hG : Good n C) (S : List ℕ) (k : ℕ)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) (hop : (gateAt C j).op = GateOp.and) (v : List ℕ) :
    v ∈ RV C n S k (n + j) ↔ ∃ u ∈ RV C n S k a, ∃ t ∈ RV C n S k b,
      v = capAdd k (capAdd k (S.map fun _ => 0) u) t := by
  have e : ∀ w, RV C n S k w = rv [] (Gv S k) ((List.range n).map (leafVectors S k)) C.gates w :=
    fun _ => rfl
  simp only [e]
  rw [rv_two [] (Gv S k) _ (by simp) hG j hj a b hin]
  simp only [Gv, hop, List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨u', hu', t, ht, rfl⟩
    rw [mem_andStep] at hu'
    obtain ⟨z, hz, u, hu, rfl⟩ := hu'
    simp only [List.mem_singleton] at hz
    subst hz
    exact ⟨u, hu, t, ht, rfl⟩
  · rintro ⟨u, hu, t, ht, rfl⟩
    refine ⟨_, ?_, t, ht, rfl⟩
    rw [mem_andStep]
    exact ⟨_, by simp, u, hu, rfl⟩


def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

lemma F_eof {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (eof i) = false := by
  simp only [graphFun, eof, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_false_iff_not, decide_eq_true_eq]
  rintro ⟨u, v, h, rfl, rfl⟩
  exact h.ne rfl

lemma F_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (h : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  simp only [graphFun, pairInput, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

/-! OR-reachability: `OR n C s w` says wire `s` reaches wire `w` through OR gates only -/

inductive OR (n : ℕ) (C : Circuit) (s : ℕ) : ℕ → Prop
  | refl : OR n C s s
  | step (j i : ℕ) : j < C.gates.length → (gateAt C j).op = GateOp.or →
      i ∈ (gateAt C j).inputs → OR n C s i → OR n C s (n + j)

lemma OR_trans {n : ℕ} {C : Circuit} {a b c : ℕ} (h1 : OR n C a b) (h2 : OR n C b c) :
    OR n C a c := by
  induction h2 with
  | refl => exact h1
  | step j i hj hop hi _ ih => exact OR.step j i hj hop hi ih

lemma OR_le {n : ℕ} {C : Circuit} (hG : Good n C) {a b : ℕ} (h : OR n C a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | step j i hj hop hi _ ih =>
    have := hG.rb j hj i hi
    omega

lemma OR_val {n : ℕ} {C : Circuit} (hG : Good n C) (x : Fin n → Bool) {a b : ℕ}
    (h : OR n C a b) : val C.gates x a = true → val C.gates x b = true := by
  induction h with
  | refl => exact id
  | step j i hj hop hi _ ih =>
    intro ha
    obtain ⟨p, q, hin, hp, hq, _⟩ := two hG j hj
    rw [val_or x j hj p q hin hp hq hop]
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rw [ih ha]
      rfl
    · rw [ih ha]
      simp

lemma OR_inv {n : ℕ} {C : Circuit} {a b : ℕ} (h : OR n C a b) :
    a = b ∨ ∃ j i, b = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      i ∈ (gateAt C j).inputs ∧ OR n C a i := by
  cases h with
  | refl => exact Or.inl rfl
  | step j i hj hop hi h => exact Or.inr ⟨j, i, rfl, hj, hop, hi, h⟩

/-- count vectors of the pair list against OR-reachability -/
lemma rinv {n : ℕ} {C : Circuit} (hG : Good n C) (s0 s1 : ℕ) (h01 : s0 ≠ s1) :
    ∀ w, ∀ v ∈ RV C n [s0, s1] 1 w, ∃ a b, v = [a, b] ∧ 1 ≤ a + b ∧
      (a = 1 → b = 0 → OR n C s0 w) ∧ (a = 0 → b = 1 → OR n C s1 w) ∧
      (a = 1 → b = 1 → ∃ j p q, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        (gateAt C j).inputs = [p, q] ∧ OR n C (n + j) w ∧
        ((OR n C s0 p ∧ OR n C s1 q) ∨ (OR n C s1 p ∧ OR n C s0 q))) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases hw : w < n
    · rw [RV_lt _ _ _ _ _ hw] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_singleton] at hv
        subst hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact ⟨1, 0, by simp [h01.symm], by omega, fun _ _ => OR.refl,
            fun h _ => absurd h (by decide), fun _ h => absurd h (by decide)⟩
        · exact ⟨0, 1, by simp [h01], by omega, fun h _ => absurd h (by decide),
            fun _ _ => OR.refl, fun h _ => absurd h (by decide)⟩
      · simp at hv
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [RV_ge _ _ _ _ _ hw2] at hv
        simp at hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨a, b, hin, ha, hb, hop⟩ := two hG j hj
        rcases hop with hop | hop
        · rw [RV_and hG _ _ j hj a b hin hop] at hv
          obtain ⟨u, hu, t, ht, rfl⟩ := hv
          obtain ⟨u0, u1, rfl, hu1, hu2, hu3, _⟩ := ih a ha u hu
          obtain ⟨t0, t1, rfl, ht1, ht2, ht3, _⟩ := ih b hb t ht
          refine ⟨min (min (0 + u0) (1 + 1) + t0) (1 + 1), min (min (0 + u1) (1 + 1) + t1) (1 + 1),
            by simp [capAdd], by omega, fun h1 h2 => by omega, fun h1 h2 => by omega, ?_⟩
          intro h1 h2
          refine ⟨j, a, b, hj, hop, hin, OR.refl, ?_⟩
          have hc : (u0 = 1 ∧ u1 = 0 ∧ t0 = 0 ∧ t1 = 1) ∨ (u0 = 0 ∧ u1 = 1 ∧ t0 = 1 ∧ t1 = 0) := by
            omega
          rcases hc with ⟨h5, h6, h7, h8⟩ | ⟨h5, h6, h7, h8⟩
          · exact Or.inl ⟨hu2 h5 h6, ht3 h7 h8⟩
          · exact Or.inr ⟨hu3 h5 h6, ht2 h7 h8⟩
        · rw [RV_or hG _ _ j hj a b hin hop] at hv
          rcases hv with hv | hv
          · obtain ⟨u0, u1, rfl, hu1, hu2, hu3, hu4⟩ := ih a ha v hv
            have hm : a ∈ (gateAt C j).inputs := by simp [hin]
            refine ⟨u0, u1, rfl, hu1, fun h1 h2 => OR.step j a hj hop hm (hu2 h1 h2),
              fun h1 h2 => OR.step j a hj hop hm (hu3 h1 h2), ?_⟩
            intro h1 h2
            obtain ⟨j', p, q, hj', hop', hin', hr, hh⟩ := hu4 h1 h2
            exact ⟨j', p, q, hj', hop', hin', OR.step j a hj hop hm hr, hh⟩
          · obtain ⟨u0, u1, rfl, hu1, hu2, hu3, hu4⟩ := ih b hb v hv
            have hm : b ∈ (gateAt C j).inputs := by simp [hin]
            refine ⟨u0, u1, rfl, hu1, fun h1 h2 => OR.step j b hj hop hm (hu2 h1 h2),
              fun h1 h2 => OR.step j b hj hop hm (hu3 h1 h2), ?_⟩
            intro h1 h2
            obtain ⟨j', p, q, hj', hop', hin', hr, hh⟩ := hu4 h1 h2
            exact ⟨j', p, q, hj', hop', hin', OR.step j b hj hop hm hr, hh⟩

/-! semantics at the output -/

lemma hval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hF : circuitFun n C = graphFun G ∅) (x : Fin n → Bool) :
    val C.gates x C.output = graphFun G ∅ x := by
  rw [← hF]
  rfl

lemma out_ge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hF : circuitFun n C = graphFun G ∅) : n ≤ C.output := by
  by_contra h
  have h1 : C.output < n := by omega
  have h2 := hval G hF (eof ⟨C.output, h1⟩)
  rw [val_lt _ _ _ h1, F_eof] at h2
  simp [eof] at h2

lemma no_var {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hG : Good n C) (hF : circuitFun n C = graphFun G ∅) (i : Fin n) :
    ¬ OR n C i.val C.output := by
  intro h
  have h1 := OR_val hG (eof i) h (by rw [val_lt _ _ _ i.isLt]; simp [eof])
  rw [hval G hF, F_eof] at h1
  cases h1

lemma val_pair_l {n : ℕ} {C : Circuit} (u v : Fin n) :
    val C.gates (pairInput u v) u.val = true := by
  rw [val_lt _ _ _ u.isLt]
  simp [pairInput]

lemma val_pair_r {n : ℕ} {C : Circuit} (u v : Fin n) :
    val C.gates (pairInput u v) v.val = true := by
  rw [val_lt _ _ _ v.isLt]
  simp [pairInput]

lemma F_pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (h : graphFun G ∅ (pairInput u v) = true) : G.Adj u v := by
  simp only [graphFun, pairInput, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at h
  obtain ⟨a, b, hab, ha, hb⟩ := h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab.ne rfl).elim
  · exact hab
  · exact hab.symm
  · exact (hab.ne rfl).elim

/-- the rectangle of a productive AND gate consists of edges -/
lemma rect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hG : Good n C) (hF : circuitFun n C = graphFun G ∅) (j p q : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [p, q]) (hr : OR n C (n + j) C.output) (u v : Fin n)
    (hu : OR n C u.val p) (hv : OR n C v.val q) : G.Adj u v := by
  apply F_pair_adj
  rw [← hval G hF]
  apply OR_val hG _ hr
  have hp := hG.rb j hj p (by simp [hin])
  have hq := hG.rb j hj q (by simp [hin])
  rw [val_and _ j hj p q hin hp hq hop, OR_val hG _ hu (val_pair_l u v),
    OR_val hG _ hv (val_pair_r u v)]
  rfl

/-- one side of the rectangle is a single vertex, the centre -/
lemma centre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hG : Good n C) (hF : circuitFun n C = graphFun G ∅) (h4 : NoFourCycle G) (j p q : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [p, q]) (hr : OR n C (n + j) C.output) (u0 v0 : Fin n)
    (hu0 : OR n C u0.val p) (hv0 : OR n C v0.val q) :
    ∃ c : Fin n, ∃ b : ℕ, (∀ i : Fin n, OR n C i.val b → G.Adj c i) ∧
      ∀ u v : Fin n, OR n C u.val p → OR n C v.val q →
        ∃ w : Fin n, s(u, v) = s(c, w) ∧ OR n C w.val b := by
  have R := rect G hG hF j p q hj hop hin hr
  by_cases h1 : ∀ u : Fin n, OR n C u.val p → u = u0
  · exact ⟨u0, q, fun i hi => R u0 i hu0 hi, fun u v hu hv => ⟨v, by rw [h1 u hu], hv⟩⟩
  · push_neg at h1
    obtain ⟨u1, hu1, hne⟩ := h1
    have h2 : ∀ v : Fin n, OR n C v.val q → v = v0 := by
      intro v hv
      have hc := h4 u1 u0 hne
      rw [Finset.card_le_one] at hc
      exact hc v (Finset.mem_filter.2 ⟨Finset.mem_univ _, R u1 v hu1 hv, R u0 v hu0 hv⟩) v0
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, R u1 v0 hu1 hv0, R u0 v0 hu0 hv0⟩)
    exact ⟨v0, p, fun i hi => (R i v0 hi hv0).symm,
      fun u v hu hv => ⟨u, by rw [h2 v hv, Sym2.eq_swap], hu⟩⟩

/-- an edge not read twice at the output has a productive AND gate -/
lemma edge_struct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hG : Good n C) (hF : circuitFun n C = graphFun G ∅) (u v : Fin n) (hadj : G.Adj u v)
    (hr : ¬ ReadTwiceAt n C (C.output - n) u v) :
    ∃ j p q, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs = [p, q] ∧
      OR n C (n + j) C.output ∧
      ((OR n C u.val p ∧ OR n C v.val q) ∨ (OR n C v.val p ∧ OR n C u.val q)) := by
  have ho := out_ge G hF
  unfold ReadTwiceAt readsAtMost at hr
  rw [Bool.not_eq_false, List.any_eq_true] at hr
  obtain ⟨vec, hvec, hall⟩ := hr
  have hvec' : vec ∈ RV C n [u.val, v.val] 1 (n + (C.output - n)) := hvec
  have e : n + (C.output - n) = C.output := by omega
  rw [e] at hvec'
  have hne : u.val ≠ v.val := fun h => hadj.ne (Fin.ext h)
  obtain ⟨a, b, rfl, hab, h1, h2, h3⟩ := rinv hG u.val v.val hne C.output vec hvec'
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    at hall
  by_cases ha : a = 0
  · exact absurd (h2 ha (by omega)) (no_var G hG hF v)
  · by_cases hb : b = 0
    · exact absurd (h1 (by omega) hb) (no_var G hG hF u)
    · exact h3 (by omega) (by omega)

/-- forest count: sources `X` joined through OR gates into the roots `B` need at least
`|X| - |B|` OR gates that merge two sources and reach a root -/
lemma forest {n : ℕ} {C : Circuit} (hG : Good n C) (U : Finset ℕ)
    (hU : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → n + j ∉ U) :
    ∀ m : ℕ, ∀ (B X O : Finset ℕ), (∀ w ∈ B, w < m) → X ⊆ U →
      (∀ x ∈ X, ∃ w ∈ B, OR n C x w) →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        (∃ x1 ∈ U, ∃ x2 ∈ U, x1 ≠ x2 ∧ OR n C x1 (n + j) ∧ OR n C x2 (n + j)) →
        (∃ w ∈ B, OR n C (n + j) w) → j ∈ O) →
      X.card ≤ B.card + O.card := by
  intro m
  induction m with
  | zero =>
    intro B X O hB hX hreach _
    have hXe : X = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨w, hw, _⟩ := hreach x hx
      exact absurd (hB w hw) (by omega)
    simp [hXe]
  | succ m ih =>
    intro B X O hB hX hreach hO
    by_cases hm : m ∈ B
    swap
    · refine ih B X O (fun w hw => ?_) hX hreach hO
      have h1 := hB w hw
      have h2 : w ≠ m := fun h => hm (h ▸ hw)
      omega
    by_cases hcase : ∃ j, m = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
        ∃ x1 ∈ U, ∃ x2 ∈ U, x1 ≠ x2 ∧ OR n C x1 (n + j) ∧ OR n C x2 (n + j)
    · obtain ⟨j, rfl, hj, hop, hmult⟩ := hcase
      obtain ⟨p, q, hin, hp, hq, _⟩ := two hG j hj
      have hjO : j ∈ O := hO j hj hop hmult ⟨n + j, hm, OR.refl⟩
      have key := ih (insert p (insert q (B.erase (n + j)))) X (O.erase j) ?_ hX ?_ ?_
      · have c0 := Finset.card_insert_le p (insert q (B.erase (n + j)))
        have c1 := Finset.card_insert_le q (B.erase (n + j))
        have c2 := Finset.card_erase_of_mem hm
        have c3 := Finset.card_erase_of_mem hjO
        have c4 : 0 < B.card := Finset.card_pos.2 ⟨_, hm⟩
        have c5 : 0 < O.card := Finset.card_pos.2 ⟨_, hjO⟩
        omega
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_erase] at hw
        rcases hw with rfl | rfl | ⟨hne, hw⟩
        · exact hp
        · exact hq
        · have := hB w hw
          omega
      · intro x hx
        obtain ⟨w, hw, hxw⟩ := hreach x hx
        by_cases hwm : w = n + j
        · subst hwm
          rcases OR_inv hxw with h | ⟨j', i, he, hj', hop', hi, hxi⟩
          · rw [h] at hx
            exact absurd (hX hx) (hU j hj hop)
          · have hjj : j' = j := by omega
            rw [hjj, hin] at hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact ⟨i, by simp, hxi⟩
            · exact ⟨i, by simp, hxi⟩
        · exact ⟨w, by simp [hwm, hw], hxw⟩
      · rintro j' hj' hop' hmult' ⟨w, hw, hjw⟩
        simp only [Finset.mem_insert, Finset.mem_erase] at hw
        have hle := OR_le hG hjw
        rw [Finset.mem_erase]
        rcases hw with rfl | rfl | ⟨hne, hw⟩
        · exact ⟨by omega, hO j' hj' hop' hmult'
            ⟨n + j, hm, OR.step j w hj hop (by simp [hin]) hjw⟩⟩
        · exact ⟨by omega, hO j' hj' hop' hmult'
            ⟨n + j, hm, OR.step j w hj hop (by simp [hin]) hjw⟩⟩
        · have := hB w hw
          exact ⟨by omega, hO j' hj' hop' hmult' ⟨w, hw, hjw⟩⟩
    · have huniq : ∀ x1 ∈ X, ∀ x2 ∈ X, OR n C x1 m → OR n C x2 m → x1 = x2 := by
        intro x1 h1 x2 h2 r1 r2
        by_contra hne
        apply hcase
        have hex : ∃ x, x ≠ m ∧ OR n C x m := by
          by_cases hx : x1 = m
          · exact ⟨x2, fun h => hne (hx.trans h.symm), r2⟩
          · exact ⟨x1, hx, r1⟩
        obtain ⟨x, hxm, rx⟩ := hex
        rcases OR_inv rx with h | ⟨j, i, he, hj, hop, _, _⟩
        · exact absurd h hxm
        · subst he
          exact ⟨j, rfl, hj, hop, x1, hX h1, x2, hX h2, hne, r1, r2⟩
      have hBm : ∀ w ∈ B.erase m, w < m := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hB w hw.2
        omega
      have hOm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
          (∃ x1 ∈ U, ∃ x2 ∈ U, x1 ≠ x2 ∧ OR n C x1 (n + j) ∧ OR n C x2 (n + j)) →
          (∃ w ∈ B.erase m, OR n C (n + j) w) → j ∈ O := by
        rintro j hj hop hmult ⟨w, hw, hjw⟩
        exact hO j hj hop hmult ⟨w, (Finset.mem_erase.1 hw).2, hjw⟩
      by_cases hex : ∃ x0 ∈ X, OR n C x0 m
      · obtain ⟨x0, hx0, r0⟩ := hex
        have key := ih (B.erase m) (X.erase x0) O hBm ((Finset.erase_subset _ _).trans hX) ?_ hOm
        · have c2 := Finset.card_erase_of_mem hm
          have c3 := Finset.card_erase_of_mem hx0
          have c4 : 0 < B.card := Finset.card_pos.2 ⟨_, hm⟩
          have c5 : 0 < X.card := Finset.card_pos.2 ⟨_, hx0⟩
          omega
        · intro x hx
          rw [Finset.mem_erase] at hx
          obtain ⟨w, hw, hxw⟩ := hreach x hx.2
          refine ⟨w, Finset.mem_erase.2 ⟨?_, hw⟩, hxw⟩
          intro hwm
          rw [hwm] at hxw
          exact hx.1 (huniq x hx.2 x0 hx0 hxw r0)
      · have key := ih (B.erase m) X O hBm hX ?_ hOm
        · have c2 := Finset.card_erase_le (s := B) (a := m)
          omega
        · intro x hx
          obtain ⟨w, hw, hxw⟩ := hreach x hx
          refine ⟨w, Finset.mem_erase.2 ⟨?_, hw⟩, hxw⟩
          intro hwm
          rw [hwm] at hxw
          exact hex ⟨x, hx, hxw⟩

/-- summing a fibrewise count over the centres -/
lemma fiber_count {α ι : Type} [DecidableEq ι] (E : Finset α) (P : Finset ℕ) (Z : Finset ι)
    (f : α → ι) (g : ℕ → ι) (Oc : ι → Finset ℕ) (hf : ∀ e ∈ E, f e ∈ Z)
    (hg : ∀ k ∈ P, g k ∈ Z)
    (hdis : ∀ c ∈ Z, ∀ c' ∈ Z, c ≠ c' → Disjoint (Oc c) (Oc c'))
    (h : ∀ c ∈ Z, (E.filter (fun e => f e = c)).card ≤
      (P.filter (fun k => g k = c)).card + (Oc c).card) :
    E.card ≤ P.card + (Z.biUnion Oc).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := E) (t := Z) (fun e he => hf e he),
    Finset.card_eq_sum_card_fiberwise (f := g) (s := P) (t := Z) (fun k hk => hg k hk),
    Finset.card_biUnion (fun c hc c' hc' hne => hdis c hc c' hc' hne), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum h

/-- three disjoint ledgers of gates -/
lemma three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hG : Good n C) (hF : circuitFun n C = graphFun G ∅) (Lf P J : Finset ℕ)
    (hLf : ∀ j ∈ Lf, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      ∃ i : Fin n, OR n C i.val (n + j))
    (hP : ∀ k ∈ P, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hJ : ∀ j ∈ J, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ OR n C (n + j) C.output) :
    Lf.card + P.card + J.card ≤ C.gates.length := by
  have d1 : Disjoint Lf P := Finset.disjoint_left.2 (fun j h1 h2 => by
    have h := (hLf j h1).2.1
    rw [(hP j h2).2] at h
    cases h)
  have d2 : Disjoint Lf J := Finset.disjoint_left.2 (fun j h1 h2 => by
    obtain ⟨_, _, i, hi⟩ := hLf j h1
    exact no_var G hG hF i (OR_trans hi (hJ j h2).2.2))
  have d3 : Disjoint P J := Finset.disjoint_left.2 (fun j h1 h2 => by
    have h := (hJ j h2).2.1
    rw [(hP j h1).2] at h
    cases h)
  have hsub : (Lf ∪ P ∪ J).card ≤ (Finset.range C.gates.length).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_union] at hj
    rw [Finset.mem_range]
    rcases hj with (h | h) | h
    · exact (hLf j h).1
    · exact (hP j h).1
    · exact (hJ j h).1
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨d2, d3⟩),
    Finset.card_union_of_disjoint d1, Finset.card_range] at hsub
  exact hsub

/-- leaf ledger of one centre -/
lemma leaf {α : Type} {n : ℕ} {C : Circuit} (hG : Good n C) (Ec : Finset α) (Pc : Finset ℕ)
    (wv : α → ℕ) (bb : ℕ → ℕ) (kk : α → ℕ) (hinj : Set.InjOn wv Ec)
    (hlt : ∀ e ∈ Ec, wv e < n) (hkk : ∀ e ∈ Ec, kk e ∈ Pc)
    (hreach : ∀ e ∈ Ec, OR n C (wv e) (bb (kk e))) (O : Finset ℕ)
    (hO : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      (∃ e1 ∈ Ec, ∃ e2 ∈ Ec, wv e1 ≠ wv e2 ∧ OR n C (wv e1) (n + j) ∧ OR n C (wv e2) (n + j)) →
      (∃ k ∈ Pc, OR n C (n + j) (bb k)) → j ∈ O) :
    Ec.card ≤ Pc.card + O.card := by
  classical
  have h := forest hG (Ec.image wv) ?_ ((Pc.image bb).sup id + 1) (Pc.image bb) (Ec.image wv) O
    ?_ (Finset.Subset.refl _) ?_ ?_
  · rw [Finset.card_image_of_injOn hinj] at h
    have h2 := Finset.card_image_le (s := Pc) (f := bb)
    omega
  · intro j hj hop hmem
    obtain ⟨e, he, hej⟩ := Finset.mem_image.1 hmem
    have := hlt e he
    omega
  · intro w hw
    have h2 := Finset.le_sup (f := id) hw
    simp only [id] at h2
    omega
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨bb (kk e), Finset.mem_image_of_mem bb (hkk e he), hreach e he⟩
  · rintro j hj hop ⟨x1, hx1, x2, hx2, hne, r1, r2⟩ ⟨w, hw, hjw⟩
    obtain ⟨e1, he1, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨e2, he2, rfl⟩ := Finset.mem_image.1 hx2
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
    exact hO j hj hop ⟨e1, he1, e2, he2, hne, r1, r2⟩ ⟨k, hk, hjw⟩

lemma core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (T : Finset (Fin n)) (h4 : NoFourCycle G) (hG : Good n C)
    (hF : circuitFun n C = graphFun G ∅) (D : Finset (Sym2 (Fin n)))
    (hD : ∀ e, e ∈ D ↔ e ∈ G.edgeFinset ∧
      ∃ u v : Fin n, e = s(u, v) ∧ ReadTwiceAt n C (C.output - n) u v)
    (hT : IsMinCover (G.deleteEdges (D : Set (Sym2 (Fin n)))) T) :
    G.edgeFinset.card + T.card ≤ C.size + D.card + 1 := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hE | hN
  · have h1 : T.card = 0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_isEmpty T)
    have h2 : G.edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro e
      refine Sym2.ind (fun u v => ?_) e
      exact isEmptyElim u
    omega
  have hDsub : D ⊆ G.edgeFinset := fun e he => ((hD e).1 he).1
  have hcard := Finset.card_sdiff_add_card_eq_card hDsub
  obtain ⟨E', hE'⟩ : ∃ E' : Finset (Sym2 (Fin n)), E' = G.edgeFinset \ D := ⟨_, rfl⟩
  rw [← hE'] at hcard
  have hEG : ∀ e ∈ E', e ∈ G.edgeFinset := by
    intro e he
    rw [hE'] at he
    exact (Finset.mem_sdiff.1 he).1
  -- every remaining edge has a productive AND gate
  have hS : ∀ e ∈ E', ∃ j p q, ∃ u v : Fin n, j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs = [p, q] ∧ OR n C (n + j) C.output ∧
      e = s(u, v) ∧ OR n C u.val p ∧ OR n C v.val q := by
    intro e
    refine Sym2.ind (fun u v => ?_) e
    intro he
    rw [hE', Finset.mem_sdiff] at he
    have hadj : G.Adj u v := by
      have h := he.1
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h
    have hnr : ¬ ReadTwiceAt n C (C.output - n) u v :=
      fun h => he.2 ((hD _).2 ⟨he.1, u, v, rfl, h⟩)
    obtain ⟨j, p, q, hj, hop, hin, hr, h | h⟩ := edge_struct G hG hF u v hadj hnr
    · exact ⟨j, p, q, u, v, hj, hop, hin, hr, rfl, h.1, h.2⟩
    · exact ⟨j, p, q, v, u, hj, hop, hin, hr, Sym2.eq_swap, h.1, h.2⟩
  choose! kk pp qq uu vv hk using hS
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = E'.image kk := ⟨_, rfl⟩
  have hPmem : ∀ e ∈ E', kk e ∈ P := by
    intro e he
    rw [hPdef]
    exact Finset.mem_image_of_mem kk he
  have hPand : ∀ k ∈ P, k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      OR n C (n + k) C.output := by
    intro k hk'
    rw [hPdef] at hk'
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 hk'
    exact ⟨(hk e0 he0).1, (hk e0 he0).2.1, (hk e0 he0).2.2.2.1⟩
  -- the centre and the star side of each productive AND gate
  have hC : ∀ k ∈ P, ∃ c : Fin n, ∃ b : ℕ, (∀ i : Fin n, OR n C i.val b → G.Adj c i) ∧
      ∀ e ∈ E', kk e = k → ∃ w : Fin n, e = s(c, w) ∧ OR n C w.val b := by
    intro k hk'
    rw [hPdef] at hk'
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 hk'
    obtain ⟨hj, hop, hin, hr, hes, hu, hv⟩ := hk e0 he0
    obtain ⟨c, b, h1, h2⟩ := centre G hG hF h4 (kk e0) (pp e0) (qq e0) hj hop hin hr
      (uu e0) (vv e0) hu hv
    refine ⟨c, b, h1, fun e he hke => ?_⟩
    obtain ⟨hj', hop', hin', hr', hes', hu', hv'⟩ := hk e he
    rw [hke, hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    rw [← hin'.1] at hu'
    rw [← hin'.2] at hv'
    obtain ⟨w, hw1, hw2⟩ := h2 (uu e) (vv e) hu' hv'
    exact ⟨w, hes'.trans hw1, hw2⟩
  choose! cc bb hcb using hC
  have hW : ∀ e ∈ E', ∃ w : Fin n, e = s(cc (kk e), w) ∧ OR n C w.val (bb (kk e)) :=
    fun e he => (hcb (kk e) (hPmem e he)).2 e he rfl
  choose! ww hww using hW
  have hadjc : ∀ e ∈ E', G.Adj (cc (kk e)) (ww e) := by
    intro e he
    have h1 := hEG e he
    rw [(hww e he).1, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h1
    exact h1
  -- the centres cover the remaining edges
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset (Fin n), Z = P.image cc := ⟨_, rfl⟩
  have hZmem : ∀ k ∈ P, cc k ∈ Z := by
    intro k hk'
    rw [hZdef]
    exact Finset.mem_image_of_mem cc hk'
  have hcov : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover (Z : Set (Fin n)) := by
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    have he : s(u, v) ∈ E' := by
      rw [hE', Finset.mem_sdiff]
      refine ⟨?_, fun h => huv.2 (Finset.mem_coe.2 h)⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact huv.1
    have hz := hZmem _ (hPmem _ he)
    rcases Sym2.eq_iff.1 (hww _ he).1 with ⟨h1, _⟩ | ⟨_, h2⟩
    · left
      rw [h1]
      exact Finset.mem_coe.2 hz
    · right
      rw [h2]
      exact Finset.mem_coe.2 hz
  have hTZ : T.card ≤ Z.card := hT.2 Z hcov
  have hZP : Z.card ≤ P.card := by
    rw [hZdef]
    exact Finset.card_image_le
  -- joining ledger
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, ∀ j, j ∈ J ↔ j < C.gates.length ∧
      ((gateAt C j).op = GateOp.or ∧ OR n C (n + j) C.output) :=
    ⟨(Finset.range C.gates.length).filter
      (fun j => (gateAt C j).op = GateOp.or ∧ OR n C (n + j) C.output),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hPJ : P.card ≤ 1 + J.card := by
    have h := forest hG (P.image (fun k => n + k)) ?_ (C.output + 1) {C.output}
      (P.image (fun k => n + k)) J ?_ (Finset.Subset.refl _) ?_ ?_
    · rw [Finset.card_image_of_injective _ (add_right_injective n), Finset.card_singleton] at h
      exact h
    · intro j hj hop hmem
      obtain ⟨k, hk', hkj⟩ := Finset.mem_image.1 hmem
      have hkj' : k = j := by omega
      rw [hkj'] at hk'
      have h := (hPand j hk').2.1
      rw [hop] at h
      cases h
    · intro w hw
      rw [Finset.mem_singleton] at hw
      omega
    · intro x hx
      obtain ⟨k, hk', rfl⟩ := Finset.mem_image.1 hx
      exact ⟨C.output, Finset.mem_singleton_self _, (hPand k hk').2.2⟩
    · rintro j hj hop _ ⟨w, hw, hjw⟩
      rw [Finset.mem_singleton] at hw
      rw [hw] at hjw
      exact (hJ j).2 ⟨hj, hop, hjw⟩
  -- leaf ledger, one set of OR gates per centre
  obtain ⟨Oc, hOc⟩ : ∃ Oc : Fin n → Finset ℕ, ∀ c j, j ∈ Oc c ↔ j < C.gates.length ∧
      ((gateAt C j).op = GateOp.or ∧
      (∃ e1 ∈ E', ∃ e2 ∈ E', cc (kk e1) = c ∧ cc (kk e2) = c ∧ ww e1 ≠ ww e2 ∧
        OR n C (ww e1).val (n + j) ∧ OR n C (ww e2).val (n + j)) ∧
      ∃ k ∈ P, cc k = c ∧ OR n C (n + j) (bb k)) :=
    ⟨fun c => (Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or ∧
      (∃ e1 ∈ E', ∃ e2 ∈ E', cc (kk e1) = c ∧ cc (kk e2) = c ∧ ww e1 ≠ ww e2 ∧
        OR n C (ww e1).val (n + j) ∧ OR n C (ww e2).val (n + j)) ∧
      ∃ k ∈ P, cc k = c ∧ OR n C (n + j) (bb k)),
      fun c j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hleaf : ∀ c ∈ Z, (E'.filter (fun e => cc (kk e) = c)).card ≤
      (P.filter (fun k => cc k = c)).card + (Oc c).card := by
    intro c _
    refine leaf hG (E'.filter (fun e => cc (kk e) = c)) (P.filter (fun k => cc k = c))
      (fun e => (ww e).val) bb kk ?_ ?_ ?_ ?_ (Oc c) ?_
    · intro e1 h1 e2 h2 h12
      have h1' := Finset.mem_filter.1 (Finset.mem_coe.1 h1)
      have h2' := Finset.mem_filter.1 (Finset.mem_coe.1 h2)
      have h12' : ww e1 = ww e2 := Fin.ext h12
      calc e1 = s(cc (kk e1), ww e1) := (hww e1 h1'.1).1
        _ = s(cc (kk e2), ww e2) := by rw [h1'.2, h2'.2, h12']
        _ = e2 := (hww e2 h2'.1).1.symm
    · intro e _
      exact (ww e).isLt
    · intro e he
      have he' := Finset.mem_filter.1 he
      exact Finset.mem_filter.2 ⟨hPmem e he'.1, he'.2⟩
    · intro e he
      exact (hww e (Finset.mem_filter.1 he).1).2
    · rintro j hj hop ⟨e1, he1, e2, he2, hne, r1, r2⟩ ⟨k, hk', hjw⟩
      have h1' := Finset.mem_filter.1 he1
      have h2' := Finset.mem_filter.1 he2
      have hk2 := Finset.mem_filter.1 hk'
      exact (hOc c j).2 ⟨hj, hop, ⟨e1, h1'.1, e2, h2'.1, h1'.2, h2'.2,
        fun h => hne (congrArg Fin.val h), r1, r2⟩, k, hk2.1, hk2.2, hjw⟩
  have hdis : ∀ c ∈ Z, ∀ c' ∈ Z, c ≠ c' → Disjoint (Oc c) (Oc c') := by
    intro c _ c' _ hne
    rw [Finset.disjoint_left]
    intro j h1 h2
    obtain ⟨_, _, ⟨e1, he1, e2, he2, hc1, hc2, hw12, r1, r2⟩, _⟩ := (hOc c j).1 h1
    obtain ⟨_, _, _, k, hk', hck, rk⟩ := (hOc c' j).1 h2
    apply hne
    have a1 : G.Adj c (ww e1) := by
      rw [← hc1]
      exact hadjc e1 he1
    have a2 : G.Adj c (ww e2) := by
      rw [← hc2]
      exact hadjc e2 he2
    have b1 : G.Adj c' (ww e1) := by
      rw [← hck]
      exact (hcb k hk').1 (ww e1) (OR_trans r1 rk)
    have b2 : G.Adj c' (ww e2) := by
      rw [← hck]
      exact (hcb k hk').1 (ww e2) (OR_trans r2 rk)
    have hc := h4 (ww e1) (ww e2) hw12
    rw [Finset.card_le_one] at hc
    exact hc c (Finset.mem_filter.2 ⟨Finset.mem_univ _, a1.symm, a2.symm⟩) c'
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, b1.symm, b2.symm⟩)
  have hEcount : E'.card ≤ P.card + (Z.biUnion Oc).card :=
    fiber_count E' P Z (fun e => cc (kk e)) cc Oc (fun e he => hZmem _ (hPmem e he)) hZmem
      hdis hleaf
  have h3 := three G hG hF (Z.biUnion Oc) P J ?_
    (fun k hk' => ⟨(hPand k hk').1, (hPand k hk').2.1⟩) (fun j hj => (hJ j).1 hj)
  · have hsz : C.size = C.gates.length := rfl
    omega
  · intro j hj
    obtain ⟨c, _, hjc⟩ := Finset.mem_biUnion.1 hj
    obtain ⟨hj', hop, ⟨e1, _, _, _, _, _, _, r1, _⟩, _⟩ := (hOc c j).1 hjc
    exact ⟨hj', hop, ww e1, r1⟩

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)),
  PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ((G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)) : Set (Sym2 (Fin n)))) T →
  G.edgeFinset.card + T.card ≤ C.size + (G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)).card + 1 := by
  intro n G _ C T h4 hAO hF hT
  have hG : Good n C := ⟨fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩, hAO.2.1⟩
  exact core G C T h4 hG hF _ (fun e => Finset.mem_filter) hT

end PEqualNP.Outside.L_meta_3706_aux

theorem PEqualNP.Outside.L_meta_3706 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)),
  PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ((G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)) : Set (Sym2 (Fin n)))) T →
  G.edgeFinset.card + T.card ≤ C.size + (G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)).card + 1 := by
  exact PEqualNP.Outside.L_meta_3706_aux.main
