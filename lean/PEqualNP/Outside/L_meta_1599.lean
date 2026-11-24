import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1599

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

-- An AND gate true at the pair input has an owner at or below it: the least true AND gate
-- reached by descending through true AND gates of the cone.
lemma and_owner (n : ℕ) (C : Circuit) (u v : Fin n) :
    ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
      gateVal n C k (pairInput u v) = true → ∃ j < C.gates.length, Owns n C j u v := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hop hv
    by_cases h : ∃ i, i < k ∧ InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧
        gateVal n C i (pairInput u v) = true
    · obtain ⟨i, hik, _, hopi, hvi⟩ := h
      exact ih i hik (by omega) hopi hvi
    · refine ⟨k, hk, hk, hop, hv, fun i hik hcone hopi => ?_⟩
      cases hb : gateVal n C i (pairInput u v) with
      | false => rfl
      | true => exact (h ⟨i, hik, hcone, hopi, hb⟩).elim

-- A wire true at the pair input either lies above an owner, or is true at one single end.
lemma trace (n : ℕ) (C : Circuit) (hao : AndOrOnly C) (u v : Fin n) :
    ∀ w, val C (List.ofFn (pairInput u v)) w = true →
      (∃ j < C.gates.length, Owns n C j u v) ∨
        val C (List.ofFn (pairInput u u)) w = true ∨
        val C (List.ofFn (pairInput v v)) w = true := by
  have hx : (List.ofFn (pairInput u v)).length = n := by simp
  have hxu : (List.ofFn (pairInput u u)).length = n := by simp
  have hxv : (List.ofFn (pairInput v v)).length = n := by simp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · right
      have h1 : pairInput u v ⟨w, hw⟩ = true :=
        (val_ofFn C (pairInput u v) ⟨w, hw⟩).symm.trans hv
      rcases (pairInput_true u v _).mp h1 with h | h
      · left
        exact (val_ofFn C (pairInput u u) ⟨w, hw⟩).trans
          ((pairInput_true u u _).mpr (Or.inl h))
      · right
        exact (val_ofFn C (pairInput v v) ⟨w, hw⟩).trans
          ((pairInput_true v v _).mpr (Or.inl h))
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hao _ (gateAt_mem hk) with hop | hop
        · left
          exact and_owner n C u v k hk hop hv
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          rcases ih i hlt hi with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl ((val_or hxu hk hop).mpr ⟨i, hin, hlt, h⟩))
          · exact Or.inr (Or.inr ((val_or hxv hk hop).mpr ⟨i, hin, hlt, h⟩))

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hao : AndOrOnly C) (hfun : circuitFun n C = graphFun G ∅) : EveryEdgeOwned n G C := by
  intro u v huv
  have hx : val C (List.ofFn (pairInput u v)) C.output = true :=
    (congrFun hfun (pairInput u v)).trans ((graphFun_pair G u v).mpr huv)
  rcases trace n C hao u v C.output hx with h | h | h
  · exact h
  · exfalso
    have h2 : graphFun G ∅ (pairInput u u) = true :=
      (congrFun hfun (pairInput u u)).symm.trans h
    exact G.irrefl ((graphFun_pair G u u).mp h2)
  · exfalso
    have h2 : graphFun G ∅ (pairInput v v) = true :=
      (congrFun hfun (pairInput v v)).symm.trans h
    exact G.irrefl ((graphFun_pair G v v).mp h2)

end PEqualNP.Outside.L_meta_1599

theorem PEqualNP.Outside.L_meta_1599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned n G C := by
  intro n G _ C hao hfun
  exact PEqualNP.Outside.L_meta_1599.main n G C hao hfun
