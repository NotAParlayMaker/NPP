import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_617_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ### Section 1: Wire evaluation, monotonicity, and graph-edge semantics -/

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

lemma foldl_take_getD (gs : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((gs.take t).foldl step w).length) :
    (gs.foldl step w).getD i false = ((gs.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t gs, List.foldl_append]
  exact foldl_step_getD_lt _ _ _ hi

lemma foldl_step_getD_gate (gs : List Gate) (w : List Bool) (t : ℕ) (ht : t < gs.length) :
    (gs.foldl step w).getD (w.length + t) false =
      (gs[t]'ht).op.eval ((gs[t]'ht).inputs.map fun i =>
        if i < w.length + t then (gs.foldl step w).getD i false else false) := by
  have hsplit : gs = gs.take t ++ gs[t]'ht :: gs.drop (t + 1) := by
    simp [List.take_append_drop]
  have hlen : ((gs.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hval : (gs.foldl step w).getD (w.length + t) false =
      (gs[t]'ht).op.eval ((gs[t]'ht).inputs.map fun i => ((gs.take t).foldl step w).getD i false) := by
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [foldl_step_getD_lt _ _ _ (by simp only [step, List.length_append, List.length_singleton, hlen]; omega)]
    simp only [step]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hlen]
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with h
  · exact (foldl_take_getD gs w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

def W (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

lemma W_eval (C : Circuit) (n : ℕ) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = W C n x C.output := rfl

lemma W_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    W C n x i = x ⟨i, hi⟩ := by
  unfold W
  rw [wires_eq_foldl, foldl_step_getD_lt _ _ _ (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

lemma W_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    W C n x (n + j) = (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i =>
      if i < n + j then W C n x i else false) := by
  have h := foldl_step_getD_gate C.gates (List.ofFn x) j hj
  simpa only [W, wires_eq_foldl, List.length_ofFn] using h

lemma W_ge (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : W C n x i = false := by
  unfold W
  rw [wires_eq_foldl]
  apply getD_of_length_le
  rw [foldl_step_length, List.length_ofFn]
  exact hi

lemma W_mono (C : Circuit) (n : ℕ) (hmono : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ i : ℕ, W C n x i = true → W C n y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hx
    by_cases hin : i < n
    · rw [W_input C n x i hin] at hx
      rw [W_input C n y i hin]
      exact hxy ⟨i, hin⟩ hx
    · by_cases hge : n + C.gates.length ≤ i
      · rw [W_ge C n x i hge] at hx
        exact absurd hx (by decide)
      · have hj : i - n < C.gates.length := by omega
        have hi_eq : i = n + (i - n) := by omega
        rw [hi_eq] at hx ⊢
        rw [W_gate C n x (i - n) hj] at hx
        rw [W_gate C n y (i - n) hj]
        have hop : (C.gates[i - n]'hj).op = GateOp.and ∨ (C.gates[i - n]'hj).op = GateOp.or := by
          simpa using (hmono _ (List.getElem_mem hj)).1
        rcases hop with hand | hor
        · rw [hand] at hx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
          rintro b ⟨k, hk, rfl⟩
          have hkx := hx _ ⟨k, hk, rfl⟩
          split_ifs at hkx ⊢ with hlt
          exact ih k (by omega) hkx
        · rw [hor] at hx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
          obtain ⟨b, ⟨k, hk, rfl⟩, hkx⟩ := hx
          refine ⟨_, ⟨k, hk, rfl⟩, ?_⟩
          split_ifs at hkx ⊢ with hlt
          exact ih k (by omega) hkx

def Computes {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool,
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def zeroIn (n : ℕ) : Fin n → Bool := fun _ => false
def unitIn {n : ℕ} (u : Fin n) : Fin n → Bool := fun w => decide (w = u)
def pairIn {n : ℕ} (u v : Fin n) : Fin n → Bool := fun w => decide (w = u ∨ w = v)
def tripleIn {n : ℕ} (u v z : Fin n) : Fin n → Bool := fun w => decide (w = u ∨ w = v ∨ w = z)

lemma eval_zero {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} (hC : Computes G C) :
    C.eval (List.ofFn (zeroIn n)) = false := by
  cases h : C.eval (List.ofFn (zeroIn n)) with
  | false => rfl
  | true =>
    obtain ⟨u, v, _, hu, _⟩ := (hC (zeroIn n)).1 h
    simp [zeroIn] at hu

lemma eval_unit {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} (hC : Computes G C) (u : Fin n) :
    C.eval (List.ofFn (unitIn u)) = false := by
  cases h : C.eval (List.ofFn (unitIn u)) with
  | false => rfl
  | true =>
    obtain ⟨a, b, hab, ha, hb⟩ := (hC (unitIn u)).1 h
    simp only [unitIn, decide_eq_true_eq] at ha hb
    subst ha; subst hb
    exact False.elim (G.loopless.irrefl _ hab)

lemma eval_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} (hC : Computes G C)
    (u v : Fin n) : C.eval (List.ofFn (pairIn u v)) = true ↔ G.Adj u v := by
  rw [hC]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairIn, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.loopless.irrefl _ hab)
    · exact hab
    · exact hab.symm
    · exact False.elim (G.loopless.irrefl _ hab)
  · intro huv
    exact ⟨u, v, huv, by simp [pairIn], by simp [pairIn]⟩

lemma eval_triple_of_adj {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} (hC : Computes G C)
    (u v z : Fin n) (huv : G.Adj u v) : C.eval (List.ofFn (tripleIn u v z)) = true :=
  (hC (tripleIn u v z)).2 ⟨u, v, huv, by simp [tripleIn], by simp [tripleIn]⟩

/-! ### Section 2: Gate deletion and cleanliness of a minimal circuit -/

def cleanEarlyGate (n M j : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i < n + j then i else M⟩

def remapLateWire (n k r' i : ℕ) : ℕ :=
  if i < n + k then i else if i = n + k then r' else i - 1

def remapLateGate (n k r' : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapLateWire n k r')⟩

def deleteGate (n : ℕ) (C : Circuit) (k r' : ℕ) : Circuit :=
  let M := n + C.gates.length
  let early := (C.gates.take k).mapIdx (fun j g => cleanEarlyGate n M j g)
  let late := (C.gates.drop (k + 1)).map (remapLateGate n k r')
  ⟨early ++ late, remapLateWire n k r' C.output⟩

lemma deleteGate_size (n : ℕ) (C : Circuit) (k r' : ℕ) (hk : k < C.gates.length) :
    (deleteGate n C k r').size = C.size - 1 := by
  simp only [deleteGate, Circuit.size, List.length_append, List.length_mapIdx,
    List.length_take, List.length_map, List.length_drop]
  omega

lemma deleteGate_monotone2 (n : ℕ) (C : Circuit) (k r' : ℕ) (hmono : Monotone2 C) :
    Monotone2 (deleteGate n C k r') := by
  intro g hg
  simp only [deleteGate, List.mem_append] at hg
  rcases hg with hg | hg
  · rw [List.mem_iff_getElem] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    simp only [List.length_mapIdx, List.length_take] at hj
    simp only [List.getElem_mapIdx, List.getElem_take]
    have hmem : C.gates[j]'(by omega) ∈ C.gates := List.getElem_mem (by omega)
    obtain ⟨hop, hlen⟩ := hmono _ hmem
    exact ⟨hop, by simp [cleanEarlyGate, hlen]⟩
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have hmem : g0 ∈ C.gates := List.mem_of_mem_drop hg0
    obtain ⟨hop, hlen⟩ := hmono g0 hmem
    exact ⟨hop, by simp [remapLateGate, hlen]⟩

lemma deleteGate_getElem_lt (n : ℕ) (C : Circuit) (k r' j : ℕ)
    (hk : k < C.gates.length) (hj : j < k) :
    (deleteGate n C k r').gates[j]'(by
      have := deleteGate_size n C k r' hk
      simp only [Circuit.size] at this; omega) =
      cleanEarlyGate n (n + C.gates.length) j (C.gates[j]'(by omega)) := by
  have hlen_e : ((C.gates.take k).mapIdx (fun j g => cleanEarlyGate n (n + C.gates.length) j g)).length = k := by
    simp [List.length_take]; omega
  simp only [deleteGate]
  rw [List.getElem_append_left (by omega)]
  simp [List.getElem_mapIdx, List.getElem_take]

lemma deleteGate_getElem_ge (n : ℕ) (C : Circuit) (k r' j : ℕ)
    (hk : k < C.gates.length) (hjk : k ≤ j) (hj : j < C.gates.length - 1) :
    (deleteGate n C k r').gates[j]'(by
      have := deleteGate_size n C k r' hk
      simp only [Circuit.size] at this; omega) =
      remapLateGate n k r' (C.gates[j + 1]'(by omega)) := by
  have hlen_e : ((C.gates.take k).mapIdx (fun j g => cleanEarlyGate n (n + C.gates.length) j g)).length = k := by
    simp [List.length_take]; omega
  simp only [deleteGate]
  rw [List.getElem_append_right (by omega)]
  simp only [List.getElem_map, List.getElem_drop]
  congr 2
  omega

lemma deleteGate_W_eq (n : ℕ) (C : Circuit) (k r' : ℕ) (hk : k < C.gates.length)
    (hr' : r' < n + k ∨ r' = n + C.gates.length)
    (x : Fin n → Bool)
    (hlate : ∀ j (hj : j < C.gates.length), k < j →
      ∀ i ∈ (C.gates[j]'hj).inputs, i = n + k →
        W C n x (n + k) = if r' < n + k then W C n x r' else false) :
    ∀ w : ℕ, w < n + (C.gates.length - 1) →
      W (deleteGate n C k r') n x w = if w < n + k then W C n x w else W C n x (w + 1) := by
  have hsz : (deleteGate n C k r').gates.length = C.gates.length - 1 :=
    deleteGate_size n C k r' hk
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hwk : w < n + k := by omega
      rw [if_pos hwk, W_input _ n x w hwn, W_input _ n x w hwn]
    · set j := w - n with hjdef
      have hw_eq : w = n + j := by omega
      have hj : j < (deleteGate n C k r').gates.length := by omega
      have hj' : j < C.gates.length - 1 := by omega
      rw [hw_eq, W_gate (deleteGate n C k r') n x j hj]
      by_cases hjk : j < k
      · rw [if_pos (by omega : n + j < n + k)]
        rw [deleteGate_getElem_lt n C k r' j hk hjk]
        rw [W_gate C n x j (by omega)]
        simp only [cleanEarlyGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply]
        by_cases hij : i < n + j
        · rw [if_pos hij, if_pos hij, if_pos hij]
          have hih := ih i (by omega) (by omega)
          rw [if_pos (by omega)] at hih
          exact hih
        · rw [if_neg hij, if_neg hij, if_neg (by omega)]
      · rw [if_neg (by omega : ¬ n + j < n + k)]
        have hw1 : n + j + 1 = n + (j + 1) := by omega
        rw [hw1, W_gate C n x (j + 1) (by omega)]
        rw [deleteGate_getElem_ge n C k r' j hk (by omega) hj']
        simp only [remapLateGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply, remapLateWire]
        by_cases hik : i < n + k
        · simp only [hik, ↓reduceIte, show i < n + j by omega, show i < n + (j + 1) by omega]
          have hih := ih i (by omega) (by omega)
          simp only [hik, ↓reduceIte] at hih
          exact hih
        · simp only [hik, ↓reduceIte]
          by_cases heq : i = n + k
          · simp only [heq, ↓reduceIte, show n + k < n + (j + 1) by omega]
            have hval := hlate (j + 1) (by omega) (by omega) i hi heq
            rw [hval]
            rcases hr' with hlt | heqM
            · simp only [hlt, ↓reduceIte, show r' < n + j by omega]
              have hih := ih r' (by omega) (by omega)
              simp only [hlt, ↓reduceIte] at hih
              exact hih
            · simp only [show ¬ r' < n + k by omega, show ¬ r' < n + j by omega, ↓reduceIte]
          · simp only [heq, ↓reduceIte]
            by_cases hij1 : i < n + (j + 1)
            · simp only [hij1, show i - 1 < n + j by omega, ↓reduceIte]
              have hih := ih (i - 1) (by omega) (by omega)
              simp only [show ¬ i - 1 < n + k by omega, ↓reduceIte] at hih
              have hi1 : i - 1 + 1 = i := by omega
              rw [hi1] at hih
              exact hih
            · simp only [hij1, show ¬ i - 1 < n + j by omega, ↓reduceIte]

lemma deleteGate_computes {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} (hC : Computes G C)
    (k r' : ℕ) (hk : k < C.gates.length)
    (hr' : r' < n + k ∨ r' = n + C.gates.length)
    (hlate : ∀ x : Fin n → Bool, ∀ j (hj : j < C.gates.length), k < j →
      ∀ i ∈ (C.gates[j]'hj).inputs, i = n + k →
        W C n x (n + k) = if r' < n + k then W C n x r' else false)
    (hout : ∀ x : Fin n → Bool, C.output = n + k →
      W C n x (n + k) = if r' < n + k then W C n x r' else false) :
    Computes G (deleteGate n C k r') := by
  intro x
  have hsz : (deleteGate n C k r').gates.length = C.gates.length - 1 :=
    deleteGate_size n C k r' hk
  have hW := deleteGate_W_eq n C k r' hk hr' x (hlate x)
  have hev : (deleteGate n C k r').eval (List.ofFn x) = C.eval (List.ofFn x) := by
    rw [W_eval, W_eval]
    change W (deleteGate n C k r') n x (remapLateWire n k r' C.output) = W C n x C.output
    simp only [remapLateWire]
    by_cases h1 : C.output < n + k
    · rw [if_pos h1]
      have h := hW C.output (by omega)
      rw [if_pos h1] at h
      exact h
    · rw [if_neg h1]
      by_cases h2 : C.output = n + k
      · rw [if_pos h2, h2, hout x h2]
        rcases hr' with hlt | heqM
        · rw [if_pos hlt]
          have h := hW r' (by omega)
          rw [if_pos hlt] at h
          exact h
        · rw [if_neg (by omega)]
          exact W_ge (deleteGate n C k r') n x r' (by omega)
      · rw [if_neg h2]
        by_cases h3 : C.output < n + C.gates.length
        · have h := hW (C.output - 1) (by omega)
          rw [if_neg (by omega)] at h
          have hsub : C.output - 1 + 1 = C.output := by omega
          rw [hsub] at h
          exact h
        · rw [W_ge (deleteGate n C k r') n x (C.output - 1) (by omega),
              W_ge C n x C.output (by omega)]
  rw [hev]
  exact hC x

/-! Cleanliness properties of a minimum-size circuit -/

lemma min_no_const_false {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (k : ℕ) (hk : k < C.gates.length) :
    ¬ (∀ x : Fin n → Bool, W C n x (n + k) = false) := by
  intro hf
  let D := deleteGate n C k (n + C.gates.length)
  have hDm : Monotone2 D := deleteGate_monotone2 n C k _ hmono
  have hDC : Computes G D := deleteGate_computes hC k (n + C.gates.length) hk (Or.inr rfl)
    (fun x _ _ _ _ _ _ => by rw [if_neg (by omega)]; exact hf x)
    (fun x _ => by rw [if_neg (by omega)]; exact hf x)
  have hle := hmin D hDm hDC
  have hsz := deleteGate_size n C k (n + C.gates.length) hk
  change C.gates.length ≤ D.size at hle
  change D.size = C.gates.length - 1 at hsz
  omega

lemma min_no_equiv {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (k r : ℕ) (hk : k < C.gates.length) (hr : r < n + k) :
    ¬ (∀ x : Fin n → Bool, W C n x (n + k) = W C n x r) := by
  intro heq
  let D := deleteGate n C k r
  have hDm : Monotone2 D := deleteGate_monotone2 n C k r hmono
  have hDC : Computes G D := deleteGate_computes hC k r hk (Or.inl hr)
    (fun x _ _ _ _ _ _ => by rw [if_pos hr]; exact heq x)
    (fun x _ => by rw [if_pos hr]; exact heq x)
  have hle := hmin D hDm hDC
  have hsz := deleteGate_size n C k r hk
  change C.gates.length ≤ D.size at hle
  change D.size = C.gates.length - 1 at hsz
  omega

lemma min_used_or_output {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (k : ℕ) (hk : k < C.gates.length) (hne : n + k ≠ C.output) :
    ∃ j : ℕ, ∃ hj : j < C.gates.length, k < j ∧ n + k ∈ (C.gates[j]'hj).inputs := by
  by_contra hno
  push_neg at hno
  let D := deleteGate n C k (n + C.gates.length)
  have hDm : Monotone2 D := deleteGate_monotone2 n C k _ hmono
  have hDC : Computes G D := deleteGate_computes hC k (n + C.gates.length) hk (Or.inr rfl)
    (fun _ j hj hkj i hi heq => absurd (heq ▸ hi) (hno j hj hkj))
    (fun _ hco => absurd hco.symm hne)
  have hle := hmin D hDm hDC
  have hsz := deleteGate_size n C k (n + C.gates.length) hk
  change C.gates.length ≤ D.size at hle
  change D.size = C.gates.length - 1 at hsz
  omega

lemma min_zero_false {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size) :
    ∀ w : ℕ, W C n (zeroIn n) w = false := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨w0, hw0⟩ := hnot
  have hw0_t : W C n (zeroIn n) w0 = true := Bool.eq_true_of_not_eq_false hw0
  have hw0_ge : n ≤ w0 := by
    by_contra hlt
    rw [W_input C n (zeroIn n) w0 (by omega)] at hw0_t
    simp [zeroIn] at hw0_t
  have hw0_lt : w0 < n + C.gates.length := by
    by_contra hge
    rw [W_ge C n (zeroIn n) w0 (by omega)] at hw0_t
    exact absurd hw0_t (by decide)
  let T : Finset ℕ := (Finset.range C.gates.length).filter (fun k => W C n (zeroIn n) (n + k) = true)
  have hTne : T.Nonempty := by
    refine ⟨w0 - n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    have : n + (w0 - n) = w0 := by omega
    rw [this]; exact hw0_t
  let k := T.max' hTne
  have hk_mem : k ∈ T := Finset.max'_mem T hTne
  have hk_lt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk_mem).1
  have hk_t : W C n (zeroIn n) (n + k) = true := (Finset.mem_filter.mp hk_mem).2
  have hk_max : ∀ j, k < j → j < C.gates.length → W C n (zeroIn n) (n + j) = false := by
    intro j hkj hj
    cases h : W C n (zeroIn n) (n + j) with
    | false => rfl
    | true =>
      have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩
      have hle := Finset.le_max' T j hjT
      omega
  have hkne : n + k ≠ C.output := by
    intro hco
    have hz := eval_zero hC
    rw [W_eval, ← hco, hk_t] at hz
    exact absurd hz (by decide)
  obtain ⟨j, hj, hkj, hmem⟩ := min_used_or_output hmono hC hmin k hk_lt hkne
  have hjt : W C n (zeroIn n) (n + j) = false := hk_max j hkj hj
  have hk_all : ∀ x : Fin n → Bool, W C n x (n + k) = true := fun x =>
    W_mono C n hmono (zeroIn n) x (fun _ h => by simp [zeroIn] at h) (n + k) hk_t
  have hgop := hmono _ (List.getElem_mem hj)
  have hop : (C.gates[j]'hj).op = GateOp.and ∨ (C.gates[j]'hj).op = GateOp.or := by
    simpa using hgop.1
  rcases hop with hand | hor
  · rcases hlist : (C.gates[j]'hj).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rw [hlist] at hmem; simp at hmem
    · rw [hlist] at hmem
      have ha : a = n + k := (List.mem_singleton.mp hmem).symm
      rw [W_gate C n (zeroIn n) j hj, hand, hlist, ha] at hjt
      simp only [List.map_cons, List.map_nil, show n + k < n + j by omega, ↓reduceIte,
        hk_t, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true] at hjt
      exact absurd hjt (by decide)
    · rw [hlist] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have handle : ∀ other : ℕ,
          (∀ x : Fin n → Bool, W C n x (n + j) = if other < n + j then W C n x other else false) →
          False := by
        intro other hoth
        by_cases hlt : other < n + j
        · exact min_no_equiv hmono hC hmin j other hj hlt (fun x => by rw [hoth x, if_pos hlt])
        · exact min_no_const_false hmono hC hmin j hj (fun x => by rw [hoth x, if_neg hlt])
      rcases hmem with rfl | rfl
      · apply handle b
        intro x
        rw [W_gate C n x j hj, hand, hlist]
        simp [GateOp.eval, show n + k < n + j by omega, hk_all x]
      · apply handle a
        intro x
        rw [W_gate C n x j hj, hand, hlist]
        simp [GateOp.eval, show n + k < n + j by omega, hk_all x]
    · have hlen := hgop.2
      rw [hlist] at hlen; simp at hlen
  · rw [W_gate C n (zeroIn n) j hj, hor] at hjt
    simp only [GateOp.eval] at hjt
    have hany : ((C.gates[j]'hj).inputs.map fun i =>
        if i < n + j then W C n (zeroIn n) i else false).any id = true := by
      rw [List.any_eq_true]
      refine ⟨true, ?_, rfl⟩
      rw [List.mem_map]
      exact ⟨n + k, hmem, by simp [show n + k < n + j by omega, hk_t]⟩
    rw [hany] at hjt
    exact absurd hjt (by decide)

lemma min_gate_two_inputs {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b : ℕ, (C.gates[j]'hj).inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ a ≠ b := by
  have hgop := hmono _ (List.getElem_mem hj)
  have hop : (C.gates[j]'hj).op = GateOp.and ∨ (C.gates[j]'hj).op = GateOp.or := by
    simpa using hgop.1
  have hz := min_zero_false hmono hC hmin (n + j)
  rcases hlist : (C.gates[j]'hj).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with hand | hor
    · rw [W_gate C n (zeroIn n) j hj, hand, hlist] at hz
      simp [GateOp.eval] at hz
    · exfalso
      apply min_no_const_false hmono hC hmin j hj
      intro x
      rw [W_gate C n x j hj, hor, hlist]
      simp [GateOp.eval]
  · exfalso
    by_cases ha : a < n + j
    · apply min_no_equiv hmono hC hmin j a hj ha
      intro x
      rw [W_gate C n x j hj, hlist]
      rcases hop with h | h <;> simp [h, GateOp.eval, ha]
    · apply min_no_const_false hmono hC hmin j hj
      intro x
      rw [W_gate C n x j hj, hlist]
      rcases hop with h | h <;> simp [h, GateOp.eval, ha]
  · have ha : a < n + j := by
      by_contra hna
      rcases hop with hand | hor
      · apply min_no_const_false hmono hC hmin j hj
        intro x
        rw [W_gate C n x j hj, hand, hlist]
        simp [GateOp.eval, hna]
      · by_cases hb : b < n + j
        · apply min_no_equiv hmono hC hmin j b hj hb
          intro x
          rw [W_gate C n x j hj, hor, hlist]
          simp [GateOp.eval, hna, hb]
        · apply min_no_const_false hmono hC hmin j hj
          intro x
          rw [W_gate C n x j hj, hor, hlist]
          simp [GateOp.eval, hna, hb]
    have hb : b < n + j := by
      by_contra hnb
      rcases hop with hand | hor
      · apply min_no_const_false hmono hC hmin j hj
        intro x
        rw [W_gate C n x j hj, hand, hlist]
        simp [GateOp.eval, hnb]
      · apply min_no_equiv hmono hC hmin j a hj ha
        intro x
        rw [W_gate C n x j hj, hor, hlist]
        simp [GateOp.eval, ha, hnb]
    have hab : a ≠ b := by
      intro heq
      subst heq
      apply min_no_equiv hmono hC hmin j a hj ha
      intro x
      rw [W_gate C n x j hj, hlist]
      rcases hop with h | h <;> simp [h, GateOp.eval, ha]
    exact ⟨a, b, rfl, ha, hb, hab⟩
  · have hlen := hgop.2
    rw [hlist] at hlen; simp at hlen

lemma min_size_pos {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Computes G C) (hedge : ∃ u v : Fin n, G.Adj u v) :
    0 < C.gates.length := by
  by_contra h0
  have hnil : C.gates.length = 0 := by omega
  obtain ⟨u, v, huv⟩ := hedge
  by_cases ho : C.output < n
  · have h1 := eval_unit hC ⟨C.output, ho⟩
    rw [W_eval, W_input C n _ C.output ho] at h1
    simp [unitIn] at h1
  · have h2 := (eval_pair_iff hC u v).2 huv
    rw [W_eval, W_ge C n _ C.output (by omega)] at h2
    exact absurd h2 (by decide)

lemma min_output_last {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length) :
    C.output = n + C.gates.length - 1 := by
  by_contra hne
  have hk : C.gates.length - 1 < C.gates.length := by omega
  have hne' : n + (C.gates.length - 1) ≠ C.output := by omega
  obtain ⟨j, hj, hkj, _⟩ := min_used_or_output hmono hC hmin (C.gates.length - 1) hk hne'
  omega

lemma input_used_of_adj {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length)
    (v u : Fin n) (hvu : G.Adj v u) :
    ∃ j : Fin C.gates.length, v.val ∈ (C.gates[j.val]'j.isLt).inputs := by
  by_contra hno
  push_neg at hno
  have hind : ∀ w : ℕ, w ≠ v.val → W C n (pairIn v u) w = W C n (unitIn u) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwv
      by_cases hwn : w < n
      · rw [W_input C n _ w hwn, W_input C n _ w hwn]
        have hne : (⟨w, hwn⟩ : Fin n) ≠ v := fun h => hwv (congrArg Fin.val h)
        simp [pairIn, unitIn, hne]
      · by_cases hge : n + C.gates.length ≤ w
        · rw [W_ge C n _ w hge, W_ge C n _ w hge]
        · have hj : w - n < C.gates.length := by omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hw_eq, W_gate C n _ (w - n) hj, W_gate C n _ (w - n) hj]
          congr 1
          apply List.map_congr_left
          intro i hi
          split_ifs with hlt
          · exact ih i (by omega) (fun heq => hno ⟨w - n, hj⟩ (heq ▸ hi))
          · rfl
  have hout := min_output_last hmono hC hmin hpos
  have h1 := (eval_pair_iff hC v u).2 hvu
  have h2 := eval_unit hC u
  rw [W_eval, hind C.output (by omega), ← W_eval, h2] at h1
  exact absurd h1 (by decide)

/-! ### Section 3: Fan-out counting, Roots, and branch-free chains -/

def outGates (C : Circuit) (w : ℕ) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => w ∈ (C.gates[j.val]'j.isLt).inputs)

def dout (C : Circuit) (w : ℕ) : ℕ := (outGates C w).card

def roots (C : Circuit) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + C.gates.length - 1)).filter (fun w => 2 ≤ dout C w)

lemma dout_pos_of_lt {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hreg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length)
    (w : ℕ) (hw : w < n + C.gates.length - 1) :
    1 ≤ dout C w := by
  unfold dout outGates
  rw [Finset.one_le_card]
  by_cases hwn : w < n
  · have hne : (G.neighborSet ⟨w, hwn⟩).Nonempty := by
      have hc := hreg ⟨w, hwn⟩
      exact Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨u, hu⟩ := hne
    obtain ⟨j, hj⟩ := input_used_of_adj hmono hC hmin hpos ⟨w, hwn⟩ u hu
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  · have hk : w - n < C.gates.length := by omega
    have hout := min_output_last hmono hC hmin hpos
    have hne : n + (w - n) ≠ C.output := by omega
    obtain ⟨j, hj, _, hmem⟩ := min_used_or_output hmono hC hmin (w - n) hk hne
    have hw_eq : n + (w - n) = w := by omega
    rw [hw_eq] at hmem
    exact ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩⟩

lemma sum_dout_eq {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size) :
    (Finset.range (n + C.gates.length - 1)).sum (dout C) = 2 * C.gates.length := by
  have h1 : ∀ w, dout C w = (Finset.univ : Finset (Fin C.gates.length)).sum
      (fun j => if w ∈ (C.gates[j.val]'j.isLt).inputs then 1 else 0) := by
    intro w
    simp [dout, outGates]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j : Fin C.gates.length,
      (Finset.range (n + C.gates.length - 1)).sum
        (fun w => if w ∈ (C.gates[j.val]'j.isLt).inputs then 1 else 0) = 2 := by
    intro j
    obtain ⟨a, b, hlist, ha, hb, hab⟩ := min_gate_two_inputs hmono hC hmin j.val j.isLt
    have hfilt : (Finset.range (n + C.gates.length - 1)).filter
        (fun w => w ∈ (C.gates[j.val]'j.isLt).inputs) = {a, b} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_range, hlist, List.mem_cons,
        List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl)
        · exact ⟨by omega, Or.inl rfl⟩
        · exact ⟨by omega, Or.inr rfl⟩
    rw [← Finset.sum_filter, hfilt]
    simp [hab]
  simp [h2, mul_comm]

lemma size_formula {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hreg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length) :
    C.gates.length + 1 = n + (roots C n).sum (fun w => dout C w - 1) := by
  have hsum := sum_dout_eq hmono hC hmin
  have hge1 : ∀ w ∈ Finset.range (n + C.gates.length - 1), dout C w = (dout C w - 1) + 1 := by
    intro w hw
    have := dout_pos_of_lt hreg hmono hC hmin hpos w (Finset.mem_range.mp hw)
    omega
  have hsplit : (Finset.range (n + C.gates.length - 1)).sum (dout C) =
      (Finset.range (n + C.gates.length - 1)).sum (fun w => dout C w - 1) +
        (n + C.gates.length - 1) := by
    calc (Finset.range (n + C.gates.length - 1)).sum (dout C)
        = (Finset.range (n + C.gates.length - 1)).sum (fun w => (dout C w - 1) + 1) :=
          Finset.sum_congr rfl hge1
      _ = (Finset.range (n + C.gates.length - 1)).sum (fun w => dout C w - 1) +
            (Finset.range (n + C.gates.length - 1)).sum (fun _ => 1) := Finset.sum_add_distrib
      _ = _ := by simp
  have hroots : (Finset.range (n + C.gates.length - 1)).sum (fun w => dout C w - 1) =
      (roots C n).sum (fun w => dout C w - 1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw hnot
    simp only [roots, Finset.mem_filter, hw, true_and] at hnot
    omega
  omega

noncomputable def nextWire (C : Circuit) (n w : ℕ) : ℕ :=
  if h : ∃ j : Fin C.gates.length, w ∈ (C.gates[j.val]'j.isLt).inputs
  then n + (Classical.choose h).val
  else w

lemma nextWire_spec {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (w : ℕ) (hd1 : dout C w = 1) :
    ∃ j : Fin C.gates.length,
      w ∈ (C.gates[j.val]'j.isLt).inputs ∧
      nextWire C n w = n + j.val ∧
      w < nextWire C n w ∧
      nextWire C n w < n + C.gates.length ∧
      ∀ j' : Fin C.gates.length, w ∈ (C.gates[j'.val]'j'.isLt).inputs → j' = j := by
  have hne : (outGates C w).Nonempty := Finset.card_pos.mp (by rw [← dout]; omega)
  obtain ⟨j0, hj0⟩ := hne
  have hex : ∃ j : Fin C.gates.length, w ∈ (C.gates[j.val]'j.isLt).inputs :=
    ⟨j0, (Finset.mem_filter.mp hj0).2⟩
  set j := Classical.choose hex
  have hj_mem : w ∈ (C.gates[j.val]'j.isLt).inputs := Classical.choose_spec hex
  have hnw : nextWire C n w = n + j.val := by
    unfold nextWire; rw [dif_pos hex]
  obtain ⟨a, b, hlist, ha, hb, _⟩ := min_gate_two_inputs hmono hC hmin j.val j.isLt
  have hwlt : w < n + j.val := by
    rw [hlist] at hj_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_mem
    rcases hj_mem with rfl | rfl <;> omega
  have huniq : ∀ j' : Fin C.gates.length, w ∈ (C.gates[j'.val]'j'.isLt).inputs → j' = j := by
    intro j' hj'
    have h1 : j' ∈ outGates C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩
    have h2 : j ∈ outGates C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_mem⟩
    have hle1 : (outGates C w).card ≤ 1 := by change dout C w ≤ 1; omega
    exact Finset.card_le_one.mp hle1 j' h1 j h2
  exact ⟨j, hj_mem, hnw, by omega, by omega, huniq⟩

noncomputable def chainAux (C : Circuit) (n : ℕ) : ℕ → ℕ → List ℕ
  | 0, w => [w]
  | fuel + 1, w =>
    if dout C w = 1 ∧ w < nextWire C n w
    then w :: chainAux C n fuel (nextWire C n w)
    else [w]

noncomputable def chain (C : Circuit) (n w : ℕ) : List ℕ :=
  chainAux C n (n + C.gates.length) w

lemma chainAux_ne_nil (C : Circuit) (n fuel w : ℕ) : chainAux C n fuel w ≠ [] := by
  cases fuel with
  | zero => simp [chainAux]
  | succ f =>
    unfold chainAux
    split_ifs <;> simp

lemma mem_chainAux_self (C : Circuit) (n fuel w : ℕ) : w ∈ chainAux C n fuel w := by
  cases fuel with
  | zero => simp [chainAux]
  | succ f =>
    unfold chainAux
    split_ifs <;> simp

lemma chainAux_ge (C : Circuit) (n fuel w : ℕ) :
    ∀ z ∈ chainAux C n fuel w, w ≤ z := by
  induction fuel generalizing w with
  | zero => intro z hz; simp [chainAux] at hz; omega
  | succ f ih =>
    intro z hz
    unfold chainAux at hz
    split_ifs at hz with h
    · simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact le_refl _
      · have := ih (nextWire C n w) z hz
        omega
    · simp at hz; omega

lemma chainAux_lt_bound {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size) :
    ∀ fuel w, w < n + C.gates.length →
      ∀ z ∈ chainAux C n fuel w, z < n + C.gates.length := by
  intro fuel
  induction fuel with
  | zero => intro w hw z hz; simp [chainAux] at hz; omega
  | succ f ih =>
    intro w hw z hz
    unfold chainAux at hz
    split_ifs at hz with h
    · simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hw
      · obtain ⟨_, _, _, _, hlt, _⟩ := nextWire_spec hmono hC hmin w h.1
        exact ih (nextWire C n w) hlt z hz
    · simp at hz; omega

lemma chainAux_step_prop {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size) :
    ∀ fuel w z s, z ∈ chainAux C n fuel w → s ∈ chainAux C n fuel w → z < s →
      dout C z = 1 ∧ nextWire C n z ∈ chainAux C n fuel w ∧ nextWire C n z ≤ s := by
  intro fuel
  induction fuel with
  | zero =>
    intro w z s hz hs hzs
    simp [chainAux] at hz hs; omega
  | succ f ih =>
    intro w z s hz hs hzs
    unfold chainAux at hz hs ⊢
    split_ifs at hz hs ⊢ with h
    · simp only [List.mem_cons] at hz hs
      rcases hz with rfl | hz
      · rcases hs with rfl | hs
        · omega
        · exact ⟨h.1, List.mem_cons_of_mem _ (mem_chainAux_self C n f (nextWire C n z)),
            chainAux_ge C n f (nextWire C n z) s hs⟩
      · rcases hs with rfl | hs
        · have := chainAux_ge C n f (nextWire C n s) z hz
          omega
        · obtain ⟨hd, hmem, hle⟩ := ih (nextWire C n w) z s hz hs hzs
          exact ⟨hd, List.mem_cons_of_mem _ hmem, hle⟩
    · simp at hz hs; omega

lemma chainAux_pred_exists (C : Circuit) (n : ℕ) :
    ∀ fuel w s, s ∈ chainAux C n fuel w → w < s →
      ∃ a ∈ chainAux C n fuel w, a < s ∧ dout C a = 1 ∧ nextWire C n a = s := by
  intro fuel
  induction fuel with
  | zero => intro w s hs hws; simp [chainAux] at hs; omega
  | succ f ih =>
    intro w s hs hws
    unfold chainAux at hs ⊢
    split_ifs at hs ⊢ with h
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · omega
      · by_cases heq : nextWire C n w = s
        · exact ⟨w, List.mem_cons_self, hws, h.1, heq⟩
        · have hge := chainAux_ge C n f (nextWire C n w) s hs
          obtain ⟨a, ha, has, hda, hnwa⟩ := ih (nextWire C n w) s hs (by omega)
          exact ⟨a, List.mem_cons_of_mem _ ha, has, hda, hnwa⟩
    · simp at hs; omega

lemma chainAux_last_stops {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size) :
    ∀ fuel w, w < n + C.gates.length → n + C.gates.length - w ≤ fuel →
      let r := (chainAux C n fuel w).getLast (chainAux_ne_nil C n fuel w)
      ¬ (dout C r = 1 ∧ r < nextWire C n r) := by
  intro fuel
  induction fuel with
  | zero => intro w hw hle; omega
  | succ f ih =>
    intro w hw hle
    dsimp only
    by_cases h : dout C w = 1 ∧ w < nextWire C n w
    · have h1 : chainAux C n (f + 1) w = w :: chainAux C n f (nextWire C n w) := by
        simp only [chainAux, h, and_self, ↓reduceIte]
      have hlast : (chainAux C n (f + 1) w).getLast (chainAux_ne_nil C n (f + 1) w) =
          (chainAux C n f (nextWire C n w)).getLast (chainAux_ne_nil C n f (nextWire C n w)) := by
        simp only [h1, List.getLast_cons (chainAux_ne_nil C n f (nextWire C n w))]
      rw [hlast]
      obtain ⟨_, _, _, _, hlt, _⟩ := nextWire_spec hmono hC hmin w h.1
      exact ih (nextWire C n w) hlt (by omega)
    · have h1 : chainAux C n (f + 1) w = [w] := by
        simp only [chainAux, h, ↓reduceIte]
      simp only [h1, List.getLast_singleton]
      exact h

noncomputable def rootOf (C : Circuit) (n w : ℕ) : ℕ :=
  (chain C n w).getLast (chainAux_ne_nil C n (n + C.gates.length) w)

lemma rootOf_mem_chain (C : Circuit) (n w : ℕ) : rootOf C n w ∈ chain C n w :=
  List.getLast_mem (chainAux_ne_nil C n (n + C.gates.length) w)

lemma rootOf_lt {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (w : ℕ) (hw : w < n + C.gates.length) :
    rootOf C n w < n + C.gates.length :=
  chainAux_lt_bound hmono hC hmin _ w hw _ (rootOf_mem_chain C n w)

lemma rootOf_is_branch_or_last {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hreg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length)
    (w : ℕ) (hw : w < n + C.gates.length) :
    rootOf C n w = n + C.gates.length - 1 ∨ rootOf C n w ∈ roots C n := by
  have hlt := rootOf_lt hmono hC hmin w hw
  have hstop := chainAux_last_stops hmono hC hmin (n + C.gates.length) w hw (by omega)
  change ¬ (dout C (rootOf C n w) = 1 ∧ rootOf C n w < nextWire C n (rootOf C n w)) at hstop
  by_cases hlast : rootOf C n w = n + C.gates.length - 1
  · exact Or.inl hlast
  · right
    have hrlt : rootOf C n w < n + C.gates.length - 1 := by omega
    have hdp := dout_pos_of_lt hreg hmono hC hmin hpos (rootOf C n w) hrlt
    have hd2 : 2 ≤ dout C (rootOf C n w) := by
      by_contra hlt2
      have hd1 : dout C (rootOf C n w) = 1 := by omega
      obtain ⟨_, _, _, hnwlt, _, _⟩ := nextWire_spec hmono hC hmin (rootOf C n w) hd1
      exact hstop ⟨hd1, hnwlt⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrlt, hd2⟩

noncomputable def strictBefore (C : Circuit) (n v s : ℕ) : List ℕ :=
  (chain C n v).filter (fun z => decide (z < s))

lemma mem_strictBefore_iff (C : Circuit) (n v s z : ℕ) :
    z ∈ strictBefore C n v s ↔ z ∈ chain C n v ∧ z < s := by
  simp [strictBefore]

/-! ### Section 4: Path independence, cutoff, W1 uniqueness, and vertex cover S -/

lemma path_indep {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (v : Fin n) (s : ℕ) (hs : s ∈ chain C n v.val)
    (x y : Fin n → Bool) (hagree : ∀ u : Fin n, u ≠ v → x u = y u) :
    ∀ z : ℕ, z < s → z ∉ strictBefore C n v.val s → W C n x z = W C n y z := by
  intro z
  induction z using Nat.strong_induction_on with
  | ind z ih =>
    intro hzs hznot
    by_cases hzn : z < n
    · rw [W_input C n x z hzn, W_input C n y z hzn]
      apply hagree ⟨z, hzn⟩
      intro heq
      have hzv : z = v.val := congrArg Fin.val heq
      apply hznot
      rw [mem_strictBefore_iff, hzv]
      exact ⟨mem_chainAux_self C n _ v.val, by omega⟩
    · by_cases hge : n + C.gates.length ≤ z
      · rw [W_ge C n x z hge, W_ge C n y z hge]
      · have hj : z - n < C.gates.length := by omega
        have hz_eq : z = n + (z - n) := by omega
        rw [hz_eq, W_gate C n x (z - n) hj, W_gate C n y (z - n) hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        split_ifs with hlt
        · apply ih i (by omega) (by omega)
          intro hisb
          rw [mem_strictBefore_iff] at hisb
          obtain ⟨hd1, hnw_mem, _⟩ := chainAux_step_prop hmono hC hmin _ v.val i s hisb.1 hs hisb.2
          obtain ⟨j0, _, hnw_eq, _, _, huniq⟩ := nextWire_spec hmono hC hmin i hd1
          have hjeq : (⟨z - n, hj⟩ : Fin C.gates.length) = j0 := huniq ⟨z - n, hj⟩ hi
          have hz_nw : z = nextWire C n i := by
            rw [hnw_eq, ← hjeq]; exact hz_eq
          apply hznot
          rw [mem_strictBefore_iff, hz_nw]
          exact ⟨hnw_mem, by omega⟩
        · rfl

lemma path_cutoff {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (v : Fin n) (s : ℕ) (hs : s ∈ chain C n v.val)
    (x y : Fin n → Bool) (hagree : ∀ u : Fin n, u ≠ v → x u = y u)
    (hWs : W C n x s = W C n y s) :
    ∀ z : ℕ, z ∉ strictBefore C n v.val s → W C n x z = W C n y z := by
  intro z
  induction z using Nat.strong_induction_on with
  | ind z ih =>
    intro hznot
    by_cases hzs : z = s
    · rw [hzs]; exact hWs
    · by_cases hzn : z < n
      · rw [W_input C n x z hzn, W_input C n y z hzn]
        apply hagree ⟨z, hzn⟩
        intro heq
        have hzv : z = v.val := congrArg Fin.val heq
        have hvs : v.val ≤ s := chainAux_ge C n _ v.val s hs
        apply hznot
        rw [mem_strictBefore_iff, hzv]
        exact ⟨mem_chainAux_self C n _ v.val, by omega⟩
      · by_cases hge : n + C.gates.length ≤ z
        · rw [W_ge C n x z hge, W_ge C n y z hge]
        · have hj : z - n < C.gates.length := by omega
          have hz_eq : z = n + (z - n) := by omega
          rw [hz_eq, W_gate C n x (z - n) hj, W_gate C n y (z - n) hj]
          congr 1
          apply List.map_congr_left
          intro i hi
          split_ifs with hlt
          · apply ih i (by omega)
            intro hisb
            rw [mem_strictBefore_iff] at hisb
            obtain ⟨hd1, hnw_mem, hnw_le⟩ := chainAux_step_prop hmono hC hmin _ v.val i s hisb.1 hs hisb.2
            obtain ⟨j0, _, hnw_eq, _, _, huniq⟩ := nextWire_spec hmono hC hmin i hd1
            have hjeq : (⟨z - n, hj⟩ : Fin C.gates.length) = j0 := huniq ⟨z - n, hj⟩ hi
            have hz_nw : z = nextWire C n i := by
              rw [hnw_eq, ← hjeq]; exact hz_eq
            apply hznot
            rw [mem_strictBefore_iff, hz_nw]
            exact ⟨hnw_mem, by omega⟩
          · rfl

lemma path_cutoff_eval {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length)
    (v : Fin n) (s : ℕ) (hs : s ∈ chain C n v.val)
    (x y : Fin n → Bool) (hagree : ∀ u : Fin n, u ≠ v → x u = y u)
    (hWs : W C n x s = W C n y s) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  have hout := min_output_last hmono hC hmin hpos
  have hslt := chainAux_lt_bound hmono hC hmin _ v.val (by omega) s hs
  have hnot : C.output ∉ strictBefore C n v.val s := by
    rw [mem_strictBefore_iff]
    omega
  exact path_cutoff hmono hC hmin v s hs x y hagree hWs C.output hnot

lemma exists_two_neighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (hreg : ∀ v : Fin n, (G.neighborSet v).ncard = 3) (v : Fin n) :
    ∃ w1 w2 : Fin n, w1 ≠ w2 ∧ G.Adj v w1 ∧ G.Adj v w2 := by
  classical
  have hcard : (Finset.univ.filter (G.Adj v)).card = 3 := by
    have h1 := hreg v
    have h2 : G.neighborSet v = ((Finset.univ.filter (G.Adj v) : Finset (Fin n)) : Set (Fin n)) := by
      ext w; simp [SimpleGraph.mem_neighborSet]
    rw [h2, Set.ncard_coe_finset] at h1
    exact h1
  have h1lt : 1 < (Finset.univ.filter (G.Adj v)).card := by omega
  obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp h1lt
  exact ⟨w1, w2, hne, (Finset.mem_filter.mp hw1).2, (Finset.mem_filter.mp hw2).2⟩

lemma exists_neighbor_ne {n : ℕ} (G : SimpleGraph (Fin n))
    (hreg : ∀ v : Fin n, (G.neighborSet v).ncard = 3) (v u : Fin n) :
    ∃ w : Fin n, w ≠ u ∧ G.Adj v w := by
  obtain ⟨w1, w2, hne, h1, h2⟩ := exists_two_neighbors G hreg v
  by_cases h : w1 = u
  · exact ⟨w2, fun h' => hne (h.trans h'.symm), h2⟩
  · exact ⟨w1, h, h1⟩

lemma w1_unique {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (huniqN : ∀ u v : Fin n, u ≠ v → ∃ w : Fin n, G.Adj v w ∧ ¬ G.Adj u w)
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length)
    (v : Fin n) (s : ℕ) (hs : s ∈ chain C n v.val)
    (u : Fin n) (huv : u ≠ v) :
    W C n (unitIn u) s = false := by
  cases hWu : W C n (unitIn u) s with
  | false => rfl
  | true =>
    exfalso
    have hnadj : ¬ G.Adj u v := by
      intro hadj
      have hWuv : W C n (pairIn u v) s = true :=
        W_mono C n hmono (unitIn u) (pairIn u v)
          (fun w hw => by simp only [unitIn, decide_eq_true_eq] at hw; simp [pairIn, hw]) s hWu
      have heq := path_cutoff_eval hmono hC hmin hpos v s hs (unitIn u) (pairIn u v)
        (fun w hw => by simp [unitIn, pairIn, hw]) (by rw [hWu, hWuv])
      rw [eval_unit hC u, (eval_pair_iff hC u v).2 hadj] at heq
      exact absurd heq (by decide)
    have hall : ∀ w : Fin n, G.Adj v w → G.Adj u w := by
      intro w hvw
      have hWuw : W C n (pairIn u w) s = true :=
        W_mono C n hmono (unitIn u) (pairIn u w)
          (fun z hz => by simp only [unitIn, decide_eq_true_eq] at hz; simp [pairIn, hz]) s hWu
      have hWuwv : W C n (tripleIn u w v) s = true :=
        W_mono C n hmono (unitIn u) (tripleIn u w v)
          (fun z hz => by simp only [unitIn, decide_eq_true_eq] at hz; simp [tripleIn, hz]) s hWu
      have heq := path_cutoff_eval hmono hC hmin hpos v s hs (pairIn u w) (tripleIn u w v)
        (fun z hz => by simp [pairIn, tripleIn, hz]) (by rw [hWuw, hWuwv])
      have htr : C.eval (List.ofFn (tripleIn u w v)) = true :=
        (hC _).2 ⟨v, w, hvw, by simp [tripleIn], by simp [tripleIn]⟩
      rw [htr] at heq
      exact (eval_pair_iff hC u w).1 heq
    obtain ⟨w, hvw, hnuw⟩ := huniqN u v huv
    exact hnuw (hall w hvw)

noncomputable def coverS (C : Circuit) (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => W C n (unitIn v) (rootOf C n v.val) = true)

lemma rootOf_mem_roots_of_mem_S {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hreg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length)
    (v : Fin n) (hv : v ∈ coverS C n) :
    rootOf C n v.val ∈ roots C n := by
  have hWt : W C n (unitIn v) (rootOf C n v.val) = true := (Finset.mem_filter.mp hv).2
  rcases rootOf_is_branch_or_last hreg hmono hC hmin hpos v.val (by omega) with hlast | hmem
  · exfalso
    have hout := min_output_last hmono hC hmin hpos
    have hu := eval_unit hC v
    rw [W_eval, hout, ← hlast, hWt] at hu
    exact absurd hu (by decide)
  · exact hmem

lemma rootOf_injOn_S {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (huniqN : ∀ u v : Fin n, u ≠ v → ∃ w : Fin n, G.Adj v w ∧ ¬ G.Adj u w)
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length) :
    Set.InjOn (fun v : Fin n => rootOf C n v.val) (coverS C n : Set (Fin n)) := by
  intro u hu v hv heq
  dsimp only at heq
  by_contra hne
  have h1 : W C n (unitIn u) (rootOf C n u.val) = true := (Finset.mem_filter.mp hu).2
  rw [heq] at h1
  have h2 := w1_unique huniqN hmono hC hmin hpos v (rootOf C n v.val)
    (rootOf_mem_chain C n v.val) u hne
  rw [h2] at h1
  exact absurd h1 (by decide)

lemma coverS_isVertexCover {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hreg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (huniqN : ∀ u v : Fin n, u ≠ v → ∃ w : Fin n, G.Adj v w ∧ ¬ G.Adj u w)
    (hmono : Monotone2 C) (hC : Computes G C)
    (hmin : ∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size)
    (hpos : 0 < C.gates.length) :
    CoverPromise.IsVertexCover G (coverS C n) := by
  intro u v huv
  by_contra hneither
  push_neg at hneither
  obtain ⟨huS, hvS⟩ := hneither
  have hne : u ≠ v := G.ne_of_adj huv
  have hWu : W C n (unitIn u) (rootOf C n u.val) = false := by
    simp only [coverS, Finset.mem_filter, Finset.mem_univ, true_and] at huS
    exact Bool.eq_false_iff.mpr huS
  have hWv : W C n (unitIn v) (rootOf C n v.val) = false := by
    simp only [coverS, Finset.mem_filter, Finset.mem_univ, true_and] at hvS
    exact Bool.eq_false_iff.mpr hvS
  have hlt_case : ∀ a b : Fin n, G.Adj a b →
      W C n (unitIn a) (rootOf C n a.val) = false →
      rootOf C n a.val < rootOf C n b.val → False := by
    intro a b hab hWa hlt
    have hnot : rootOf C n a.val ∉ strictBefore C n b.val (rootOf C n b.val) := by
      intro hmem
      rw [mem_strictBefore_iff] at hmem
      obtain ⟨hd1, _, _⟩ := chainAux_step_prop hmono hC hmin _ b.val
        (rootOf C n a.val) (rootOf C n b.val) hmem.1 (rootOf_mem_chain C n b.val) hmem.2
      have hrb := rootOf_lt hmono hC hmin b.val (by omega)
      rcases rootOf_is_branch_or_last hreg hmono hC hmin hpos a.val (by omega) with hlast | hr
      · omega
      · have hd2 : 2 ≤ dout C (rootOf C n a.val) := (Finset.mem_filter.mp hr).2
        omega
    have hWab : W C n (pairIn a b) (rootOf C n a.val) = W C n (unitIn a) (rootOf C n a.val) :=
      path_indep hmono hC hmin b (rootOf C n b.val) (rootOf_mem_chain C n b.val)
        (pairIn a b) (unitIn a) (fun w hw => by simp [pairIn, unitIn, hw])
        (rootOf C n a.val) hlt hnot
    have hWb : W C n (unitIn b) (rootOf C n a.val) = false :=
      w1_unique huniqN hmono hC hmin hpos a (rootOf C n a.val)
        (rootOf_mem_chain C n a.val) b (G.ne_of_adj hab).symm
    have heq := path_cutoff_eval hmono hC hmin hpos a (rootOf C n a.val)
      (rootOf_mem_chain C n a.val) (pairIn a b) (unitIn b)
      (fun w hw => by simp [pairIn, unitIn, hw]) (by rw [hWab, hWa, hWb])
    rw [(eval_pair_iff hC a b).2 hab, eval_unit hC b] at heq
    exact absurd heq (by decide)
  rcases lt_trichotomy (rootOf C n u.val) (rootOf C n v.val) with hlt | heqr | hgt
  · exact hlt_case u v huv hWu hlt
  · classical
    let common : Finset ℕ := (chain C n u.val).toFinset ∩ (chain C n v.val).toFinset
    have hne_c : common.Nonempty := by
      refine ⟨rootOf C n u.val, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact List.mem_toFinset.mpr (rootOf_mem_chain C n u.val)
      · rw [heqr]; exact List.mem_toFinset.mpr (rootOf_mem_chain C n v.val)
    let M := common.min' hne_c
    have hM_mem : M ∈ common := Finset.min'_mem common hne_c
    have hMu : M ∈ chain C n u.val := List.mem_toFinset.mp (Finset.mem_inter.mp hM_mem).1
    have hMv : M ∈ chain C n v.val := List.mem_toFinset.mp (Finset.mem_inter.mp hM_mem).2
    have hM_min : ∀ z, z ∈ chain C n u.val → z ∈ chain C n v.val → M ≤ z := fun z h1 h2 =>
      Finset.min'_le common z (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr h1, List.mem_toFinset.mpr h2⟩)
    have hMu_ne : M ≠ u.val := by
      intro h
      have h1 := w1_unique huniqN hmono hC hmin hpos v M hMv u hne
      rw [h, W_input C n _ u.val u.isLt] at h1
      simp [unitIn] at h1
    have hMv_ne : M ≠ v.val := by
      intro h
      have h1 := w1_unique huniqN hmono hC hmin hpos u M hMu v hne.symm
      rw [h, W_input C n _ v.val v.isLt] at h1
      simp [unitIn] at h1
    have huM : u.val < M := by
      have := chainAux_ge C n _ u.val M hMu; omega
    have hvM : v.val < M := by
      have := chainAux_ge C n _ v.val M hMv; omega
    obtain ⟨a, ha_ch, haM, hda, hnwa⟩ := chainAux_pred_exists C n _ u.val M hMu huM
    obtain ⟨b, hb_ch, hbM, hdb, hnwb⟩ := chainAux_pred_exists C n _ v.val M hMv hvM
    obtain ⟨ja, hja_mem, hja_nw, _, _, _⟩ := nextWire_spec hmono hC hmin a hda
    obtain ⟨jb, hjb_mem, hjb_nw, _, _, _⟩ := nextWire_spec hmono hC hmin b hdb
    have hja_eq : n + ja.val = M := by rw [← hja_nw, hnwa]
    have hjb_eq : jb = ja := Fin.ext (by omega)
    rw [hjb_eq] at hjb_mem
    have ha_not_v : a ∉ strictBefore C n v.val M := by
      intro hmem
      rw [mem_strictBefore_iff] at hmem
      have := hM_min a ha_ch hmem.1
      omega
    have hb_not_u : b ∉ strictBefore C n u.val M := by
      intro hmem
      rw [mem_strictBefore_iff] at hmem
      have := hM_min b hmem.1 hb_ch
      omega
    have hab_ne : a ≠ b := by
      intro h
      rw [h] at ha_ch
      have := hM_min b ha_ch hb_ch
      omega
    obtain ⟨p, q, hlist, hp, hq, hpq⟩ := min_gate_two_inputs hmono hC hmin ja.val ja.isLt
    have hM_inputs : (C.gates[ja.val]'ja.isLt).inputs = [a, b] ∨
        (C.gates[ja.val]'ja.isLt).inputs = [b, a] := by
      rw [hlist] at hja_mem hjb_mem ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hja_mem hjb_mem
      rcases hja_mem with rfl | rfl <;> rcases hjb_mem with rfl | rfl
      · exact absurd rfl hab_ne
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hab_ne
    have hop : (C.gates[ja.val]'ja.isLt).op = GateOp.and ∨ (C.gates[ja.val]'ja.isLt).op = GateOp.or := by
      simpa using (hmono _ (List.getElem_mem ja.isLt)).1
    rcases hop with hand | hor
    · obtain ⟨w, hwv, huw⟩ := exists_neighbor_ne G hreg u v
      have hwu : w ≠ u := (G.ne_of_adj huw).symm
      have hWwM : W C n (unitIn w) M = false :=
        w1_unique huniqN hmono hC hmin hpos u M hMu w hwu
      have hWuwM : W C n (pairIn u w) M = true := by
        cases h : W C n (pairIn u w) M with
        | true => rfl
        | false =>
          exfalso
          have heq := path_cutoff_eval hmono hC hmin hpos u M hMu (pairIn u w) (unitIn w)
            (fun z hz => by simp [pairIn, unitIn, hz]) (by rw [h, hWwM])
          rw [(eval_pair_iff hC u w).2 huw, eval_unit hC w] at heq
          exact absurd heq (by decide)
      have hWuwb : W C n (pairIn u w) b = true := by
        rw [← hja_eq, W_gate C n (pairIn u w) ja.val ja.isLt, hand] at hWuwM
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hWuwM
        have := hWuwM _ ⟨b, hjb_mem, rfl⟩
        rw [if_pos (by omega)] at this
        exact this
      have hWwb : W C n (unitIn w) b = W C n (pairIn u w) b :=
        path_indep hmono hC hmin u M hMu (unitIn w) (pairIn u w)
          (fun z hz => by simp [unitIn, pairIn, hz]) b hbM hb_not_u
      rw [hWuwb] at hWwb
      have hWwb_f := w1_unique huniqN hmono hC hmin hpos v b hb_ch w hwv
      rw [hWwb_f] at hWwb
      exact absurd hWwb (by decide)
    · have hWua : W C n (unitIn u) a = false := by
        cases h : W C n (unitIn u) a with
        | false => rfl
        | true =>
          exfalso
          have hWuM : W C n (unitIn u) M = true := by
            rw [← hja_eq, W_gate C n (unitIn u) ja.val ja.isLt, hor]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨true, ⟨a, hja_mem, by rw [if_pos (by omega), h]⟩, rfl⟩
          have hWuM_f := w1_unique huniqN hmono hC hmin hpos v M hMv u hne
          rw [hWuM_f] at hWuM
          exact absurd hWuM (by decide)
      have hWvb : W C n (unitIn v) b = false := by
        cases h : W C n (unitIn v) b with
        | false => rfl
        | true =>
          exfalso
          have hWvM : W C n (unitIn v) M = true := by
            rw [← hja_eq, W_gate C n (unitIn v) ja.val ja.isLt, hor]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨true, ⟨b, hjb_mem, by rw [if_pos (by omega), h]⟩, rfl⟩
          have hWvM_f := w1_unique huniqN hmono hC hmin hpos u M hMu v hne.symm
          rw [hWvM_f] at hWvM
          exact absurd hWvM (by decide)
      have hWuva : W C n (pairIn u v) a = false := by
        rw [path_indep hmono hC hmin v M hMv (pairIn u v) (unitIn u)
          (fun z hz => by simp [pairIn, unitIn, hz]) a haM ha_not_v, hWua]
      have hWuvb : W C n (pairIn u v) b = false := by
        rw [path_indep hmono hC hmin u M hMu (pairIn u v) (unitIn v)
          (fun z hz => by simp [pairIn, unitIn, hz]) b hbM hb_not_u, hWvb]
      have hWuvM : W C n (pairIn u v) M = false := by
        rw [← hja_eq, W_gate C n (pairIn u v) ja.val ja.isLt, hor]
        rcases hM_inputs with h1 | h1 <;>
          simp [h1, GateOp.eval, show a < n + ja.val by omega, show b < n + ja.val by omega, hWuva, hWuvb]
      have hWvM_f := w1_unique huniqN hmono hC hmin hpos u M hMu v hne.symm
      have heq := path_cutoff_eval hmono hC hmin hpos u M hMu (pairIn u v) (unitIn v)
        (fun z hz => by simp [pairIn, unitIn, hz]) (by rw [hWuvM, hWvM_f])
      rw [(eval_pair_iff hC u v).2 huv, eval_unit hC v] at heq
      exact absurd heq (by decide)
  · exact hlt_case v u huv.symm hWv hgt


/-! ### Section 5: 3-cube Q3 specialization and lower bound `11 ≤ C.size` -/

def q3Edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)]

def Q3 : SimpleGraph (Fin 8) where
  Adj u v := (u.val, v.val) ∈ q3Edges ∨ (v.val, u.val) ∈ q3Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by revert u h; decide⟩

def decQ3Adj : DecidableRel Q3.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val, v.val) ∈ q3Edges ∨ (v.val, u.val) ∈ q3Edges))

lemma Q3_reg : ∀ v : Fin 8, (Q3.neighborSet v).ncard = 3 := by
  letI : DecidableRel Q3.Adj := decQ3Adj
  intro v
  have h1 : Q3.neighborSet v = ((Finset.univ.filter (Q3.Adj v) : Finset (Fin 8)) : Set (Fin 8)) := by
    ext w; simp [SimpleGraph.mem_neighborSet]
  rw [h1, Set.ncard_coe_finset]
  clear h1
  revert v; decide

lemma Q3_uniqN : ∀ u v : Fin 8, u ≠ v → ∃ w : Fin 8, Q3.Adj v w ∧ ¬ Q3.Adj u w := by
  letI : DecidableRel Q3.Adj := decQ3Adj
  decide

lemma card_ge4_of_four {S : Finset (Fin 8)} {a b c d : Fin 8}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (h4 : ({a, b, c, d} : Finset (Fin 8)).card = 4) : 4 ≤ S.card := by
  have hsub : ({a, b, c, d} : Finset (Fin 8)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  omega

lemma Q3_min_vc (S : Finset (Fin 8)) (hS : CoverPromise.IsVertexCover Q3 S) : 4 ≤ S.card := by
  have h0 : (0 : Fin 8) ∈ S ∨ (1 : Fin 8) ∈ S := hS 0 1 (Or.inl (by decide))
  have h1 : (2 : Fin 8) ∈ S ∨ (3 : Fin 8) ∈ S := hS 2 3 (Or.inl (by decide))
  have h2 : (4 : Fin 8) ∈ S ∨ (5 : Fin 8) ∈ S := hS 4 5 (Or.inl (by decide))
  have h3 : (6 : Fin 8) ∈ S ∨ (7 : Fin 8) ∈ S := hS 6 7 (Or.inl (by decide))
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    exact card_ge4_of_four h0 h1 h2 h3 (by decide)

lemma computes_Q3_of_list (C : Circuit)
    (heval : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ q3Edges ∧ x u = true ∧ x v = true) :
    Computes Q3 C := by
  intro x
  rw [heval x]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨u, v, Or.inl huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases huv with h | h
    · exact ⟨u, v, h, hu, hv⟩
    · exact ⟨v, u, h, hv, hu⟩

lemma Q3_size_lb (C : Circuit) (hmono : Monotone2 C) (hC : Computes Q3 C) :
    11 ≤ C.size := by
  classical
  have hex : ∃ m : ℕ, ∃ D : Circuit, Monotone2 D ∧ Computes Q3 D ∧ D.size = m :=
    ⟨C.size, C, hmono, hC, rfl⟩
  let m0 := Nat.find hex
  obtain ⟨D, hDm, hDC, hDs⟩ := Nat.find_spec hex
  have hDmin : ∀ E : Circuit, Monotone2 E → Computes Q3 E → D.size ≤ E.size := by
    intro E hEm hEC
    rw [hDs]
    exact Nat.find_min' hex ⟨E, hEm, hEC, rfl⟩
  have hDC_le : D.size ≤ C.size := hDmin C hmono hC
  have hpos : 0 < D.gates.length :=
    min_size_pos hDC ⟨(0 : Fin 8), (1 : Fin 8), Or.inl (by decide)⟩
  have hcov : CoverPromise.IsVertexCover Q3 (coverS D 8) :=
    coverS_isVertexCover Q3_reg Q3_uniqN hDm hDC hDmin hpos
  have hvc4 : 4 ≤ (coverS D 8).card := Q3_min_vc (coverS D 8) hcov
  have hS_le_roots : (coverS D 8).card ≤ (roots D 8).card := by
    apply Finset.card_le_card_of_injOn (fun v : Fin 8 => rootOf D 8 v.val)
    · intro v hv
      exact rootOf_mem_roots_of_mem_S Q3_reg hDm hDC hDmin hpos v (Finset.mem_coe.mp hv)
    · exact rootOf_injOn_S Q3_uniqN hDm hDC hDmin hpos
  have hroots_le_sum : (roots D 8).card ≤ ∑ w ∈ roots D 8, (dout D w - 1) := by
    calc (roots D 8).card = ∑ _w ∈ roots D 8, 1 := by simp
      _ ≤ ∑ w ∈ roots D 8, (dout D w - 1) := by
        apply Finset.sum_le_sum
        intro w hw
        have h2 : 2 ≤ dout D w := (Finset.mem_filter.mp hw).2
        omega
  have hsf := size_formula Q3_reg hDm hDC hDmin hpos
  have hDlen : D.size = D.gates.length := rfl
  omega

theorem main_refute :
    ¬ (∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 8, (u.val, v.val) ∈ q3Edges ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hmono, hle, heval⟩
  have h11 := Q3_size_lb C hmono (computes_Q3_of_list C heval)
  omega

end PEqualNP.Outside.L_meta_617_aux

theorem PEqualNP.Outside.L_meta_617 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) :=
  PEqualNP.Outside.L_meta_617_aux.main_refute
