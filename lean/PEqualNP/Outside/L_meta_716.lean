import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_716_aux

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def sh (n i : ℕ) : ℕ := if i < n then i else i + 1

def shG (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh n)⟩

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false = if i < w.length then w.getD i false else
      if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold step
  rcases lt_trichotomy i w.length with h | h | h
  · simp [List.getD, h, List.getElem?_append_left h]
  · subst h
    simp [List.getD]
  · have h1 : ¬ i < w.length := by omega
    have h2 : i ≠ w.length := by omega
    simp only [h1, h2, if_false]
    apply List.getD_eq_default
    simp
    omega

lemma fold_length (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step_len, List.length_cons]
    omega

lemma fold_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by rw [step_len]; omega), getD_step, if_pos hi]

lemma rel_step (n : ℕ) (g : Gate) (W V : List Bool) (h1 : n ≤ W.length)
    (h2 : V.length = W.length + 1) (h3 : ∀ i, V.getD (sh n i) false = W.getD i false) :
    n ≤ (step W g).length ∧ (step V (shG n g)).length = (step W g).length + 1 ∧
      ∀ i, (step V (shG n g)).getD (sh n i) false = (step W g).getD i false := by
  refine ⟨by rw [step_len]; omega, by rw [step_len, step_len, h2], ?_⟩
  intro i
  have hv : (shG n g).op.eval ((shG n g).inputs.map fun i => V.getD i false) =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [shG, List.map_map]
    congr 2
    funext j
    exact h3 j
  rw [getD_step, getD_step, hv, h3]
  have k1 : sh n i < V.length ↔ i < W.length := by unfold sh; split_ifs <;> omega
  have k2 : sh n i = V.length ↔ i = W.length := by unfold sh; split_ifs <;> omega
  by_cases a1 : i < W.length
  · rw [if_pos a1, if_pos (k1.mpr a1)]
  · rw [if_neg a1, if_neg (fun h => a1 (k1.mp h))]
    by_cases a2 : i = W.length
    · rw [if_pos a2, if_pos (k2.mpr a2)]
    · rw [if_neg a2, if_neg (fun h => a2 (k2.mp h))]

lemma rel_fold (n : ℕ) (gs : List Gate) : ∀ (W V : List Bool), n ≤ W.length →
    V.length = W.length + 1 → (∀ i, V.getD (sh n i) false = W.getD i false) →
    ((gs.map (shG n)).foldl step V).length = (gs.foldl step W).length + 1 ∧
      ∀ i, ((gs.map (shG n)).foldl step V).getD (sh n i) false = (gs.foldl step W).getD i false := by
  induction gs with
  | nil => intro W V _ h2 h3; exact ⟨h2, h3⟩
  | cons g gs ih =>
    intro W V h1 h2 h3
    obtain ⟨e1, e2, e3⟩ := rel_step n g W V h1 h2 h3
    exact ih _ _ e1 e2 e3

lemma rel_init (n : ℕ) (x : Fin (n + 1) → Bool) (i : ℕ) :
    (List.ofFn x).getD (sh n i) false = (List.ofFn fun j : Fin n => x j.castSucc).getD i false := by
  unfold sh
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
    rw [List.getElem_ofFn, List.getElem_ofFn]
    rfl
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma tail (W : List Bool) (N a b : ℕ) (p q r : GateOp) (hN : W.length = N) (ha : a < N)
    (hb : b < N ∨ N + 4 ≤ b) :
    (([⟨p, [a, b]⟩, ⟨q, [a, b]⟩, ⟨GateOp.not, [N + 1]⟩, ⟨r, [N, N + 2]⟩] : List Gate).foldl step W).getD
      (N + 3) false = r.eval [p.eval [W.getD a false, W.getD b false],
        !(q.eval [W.getD a false, W.getD b false])] := by
  subst hN
  simp only [List.foldl_cons, List.foldl_nil]
  simp only [getD_step, step_len, List.map_cons, List.map_nil]
  split_ifs <;> first | omega | rfl |
    (rcases hb with hb | hb
     · omega
     · rw [List.getD_eq_default W false (by omega : W.length ≤ b)]
       rfl)

lemma main (n s : ℕ) (h : (Fin n → Bool) → Bool) (hC : HasCircuitSize n h s) (p q r : GateOp)
    (hp : p ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hq : q ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hr : r ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (F : (Fin (n + 1) → Bool) → Bool)
    (hF : ∀ x : Fin (n + 1) → Bool, F x = r.eval [p.eval [x (Fin.last n), h (fun i => x i.castSucc)],
      !(q.eval [x (Fin.last n), h (fun i => x i.castSucc)])]) :
    HasCircuitSize (n + 1) F (s + 4) := by
  obtain ⟨C, hfan, hsz, hev⟩ := hC
  have hsz' : C.gates.length ≤ s := hsz
  let N := n + 1 + C.gates.length
  let b := if sh n C.output < N then sh n C.output else N + 4
  refine ⟨⟨C.gates.map (shG n) ++ [⟨p, [n, b]⟩, ⟨q, [n, b]⟩, ⟨GateOp.not, [N + 1]⟩,
    ⟨r, [N, N + 2]⟩], N + 3⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨a1, a2⟩ := hfan g0 hg0
      exact ⟨a1, by simpa [shG] using a2⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact ⟨hp, by simp⟩
      · exact ⟨hq, by simp⟩
      · exact ⟨Or.inr (Or.inr rfl), by simp⟩
      · exact ⟨hr, by simp⟩
  · show (C.gates.map (shG n) ++ [(⟨p, [n, b]⟩ : Gate), ⟨q, [n, b]⟩, ⟨GateOp.not, [N + 1]⟩,
      ⟨r, [N, N + 2]⟩]).length ≤ s + 4
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  · intro x
    have hy := hev (fun i => x i.castSucc)
    obtain ⟨e1, e2⟩ := rel_fold n C.gates (List.ofFn fun j : Fin n => x j.castSucc) (List.ofFn x)
      (by simp) (by simp) (rel_init n x)
    have L1 : ((C.gates.map (shG n)).foldl step (List.ofFn x)).length = N := by
      rw [fold_length]
      simp [N]
    have L2 : (C.gates.foldl step (List.ofFn fun j : Fin n => x j.castSucc)).length =
        n + C.gates.length := by
      rw [fold_length]
      simp
    show ((C.gates.map (shG n) ++ [(⟨p, [n, b]⟩ : Gate), ⟨q, [n, b]⟩, ⟨GateOp.not, [N + 1]⟩,
      ⟨r, [N, N + 2]⟩]).foldl step (List.ofFn x)).getD (N + 3) false = F x
    rw [List.foldl_append, tail _ N n b p q r L1 (by omega)
      (by simp only [b]; split_ifs <;> omega)]
    have hn : ((C.gates.map (shG n)).foldl step (List.ofFn x)).getD n false = x (Fin.last n) := by
      rw [fold_lt _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      rfl
    have hb : ((C.gates.map (shG n)).foldl step (List.ofFn x)).getD b false =
        h (fun i => x i.castSucc) := by
      rw [← hy]
      show _ = (C.gates.foldl step _).getD C.output false
      rw [← e2]
      simp only [b]
      split_ifs with hh
      · rfl
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [hn, hb, hF x]

end PEqualNP.Outside.L_meta_716_aux

theorem PEqualNP.Outside.L_meta_716 : ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool), (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) := by
  intro n s g
  refine ⟨fun hC => ?_, fun hC => ?_⟩
  · refine PEqualNP.Outside.L_meta_716_aux.main n s g hC GateOp.or GateOp.and GateOp.and
      (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inl rfl) _ ?_
    intro x
    cases x (Fin.last n) <;> cases g (fun i => x i.castSucc) <;> rfl
  · refine PEqualNP.Outside.L_meta_716_aux.main n s _ hC GateOp.and GateOp.or GateOp.or
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) _ ?_
    intro x
    cases x (Fin.last n) <;> cases g (fun i => x i.castSucc) <;> rfl
