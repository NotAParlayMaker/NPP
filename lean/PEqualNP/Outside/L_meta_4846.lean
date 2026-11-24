import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4846_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

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

lemma mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt gs x i h1] at hi
      rw [val_lt gs x' i h1]
      exact hle _ hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge gs x i h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk] at hi
        rw [val_gate gs x' k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hi hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hi hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = true →
            (if a < n + k then val gs x' a else false) = true := by
          intro a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)
        match ins, hlen with
        | [], _ =>
          rcases hop with rfl | rfl
          · simp [GateOp.eval]
          · simp [GateOp.eval] at hi
        | [a], _ =>
          rcases hop with rfl | rfl
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
        | [a, b], _ =>
          rcases hop with rfl | rfl
          · have h : (if a < n + k then val gs x a else false) = true ∧
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            have h1 := rd a h.1
            have h2 := rd b h.2
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true]
            exact ⟨h1, h2⟩
          · have h : (if a < n + k then val gs x a else false) = true ∨
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq, Bool.or_eq_true]
            rcases h with h | h
            · exact Or.inl (rd a h)
            · exact Or.inr (rd b h)
        | _ :: _ :: _ :: _, h => simp at h

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def pr {n : ℕ} (u v : Fin n) : Fin n → Bool := fun c => decide (c = u ∨ c = v)

-- cone characterisation (cones_len .. inCone_trans) copied from the merged L_meta_2067
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

structure Good (n : ℕ) (C : Circuit) : Prop where
  ao : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  rb : ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma eof_le_pr {n : ℕ} (s p q : Fin n) (h : s = p ∨ s = q) :
    ∀ c, eof s c = true → pr p q c = true := by
  intro c hc
  simp only [eof, pr, decide_eq_true_eq] at hc ⊢
  subst hc
  exact h

-- a true wire inside the cone of gate j, with no true AND gate there, is true at one variable
lemma single {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (x : Fin n → Bool)
    (hown : ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and →
      val C.gates x (n + i) = false) :
    ∀ w, (w < n ∨ ∃ k, w = n + k ∧ InCone n C k j) → val C.gates x w = true →
      ∃ s : Fin n, x s = true ∧ val C.gates (eof s) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    by_cases h1 : w < n
    · rw [val_lt C.gates x w h1] at hv
      refine ⟨⟨w, h1⟩, hv, ?_⟩
      rw [val_lt C.gates _ w h1]
      simp [eof]
    · rcases hw with hw | ⟨k, rfl, hk⟩
      · exact absurd hw h1
      · obtain ⟨hkj, hjl⟩ := inCone_lt n C k j hk
        have hkl : k < C.gates.length := by omega
        have hop := (hg _ (List.getElem_mem hkl)).1
        rw [← gateAt_eq C k hkl] at hop
        rcases hop with hop | hop
        · rw [hown k hkj hk hop] at hv
          exact absurd hv (by simp)
        · rw [val_gate C.gates x k hkl, ← gateAt_eq C k hkl, hop] at hv
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hv
          obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hv
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at hb
            have hcone : a < n ∨ ∃ k', a = n + k' ∧ InCone n C k' j := by
              by_cases han : a < n
              · exact Or.inl han
              · refine Or.inr ⟨a - n, by omega, ?_⟩
                have h1' : InCone n C (a - n) k :=
                  (inCone_iff n C (a - n) k).mpr ⟨hkl, a - n, by omega,
                    by rw [show n + (a - n) = a by omega]; exact ha, Or.inl rfl⟩
                exact inCone_trans n C (a - n) k h1' j hk
            obtain ⟨s, hs, hvs⟩ := ih a hlt hcone hb
            refine ⟨s, hs, ?_⟩
            rw [val_gate C.gates _ k hkl, ← gateAt_eq C k hkl, hop]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨_, ⟨a, ha, rfl⟩, by rw [if_pos hlt]; exact hvs⟩
          · rw [if_neg hlt] at hb
            exact absurd hb (by simp)

-- every input of an owning gate is true at one endpoint of the owned pair
lemma inputs_single {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (u v : Fin n) (hO : Owns n C j u v) :
    ∀ a ∈ (gateAt C j).inputs, a < n + j ∧
      ∃ s : Fin n, (s = u ∨ s = v) ∧ val C.gates (eof s) a = true := by
  obtain ⟨hj, hop, hv, hown⟩ := hO
  have hv' : val C.gates (pr u v) (n + j) = true := hv
  intro a ha
  rw [val_gate C.gates _ j hj, ← gateAt_eq C j hj, hop] at hv'
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hv'
  have h := hv' _ ⟨a, ha, rfl⟩
  by_cases hlt : a < n + j
  · rw [if_pos hlt] at h
    refine ⟨hlt, ?_⟩
    have hcone : a < n ∨ ∃ k', a = n + k' ∧ InCone n C k' j := by
      by_cases han : a < n
      · exact Or.inl han
      · refine Or.inr ⟨a - n, by omega, ?_⟩
        exact (inCone_iff n C (a - n) j).mpr ⟨hj, a - n, by omega,
          by rw [show n + (a - n) = a by omega]; exact ha, Or.inl rfl⟩
    obtain ⟨s, hs, hvs⟩ := single C hg j (pr u v) (fun i hi hc hand => hown i hi hc hand) a hcone h
    refine ⟨s, ?_, hvs⟩
    simpa [pr] using hs
  · rw [if_neg hlt] at h
    exact absurd h (by simp)

lemma gate_true {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (p q : Fin n)
    (h : ∀ a ∈ (gateAt C j).inputs, a < n + j ∧
      ∃ s : Fin n, (s = p ∨ s = q) ∧ val C.gates (eof s) a = true) :
    gateVal n C j (pairInput p q) = true := by
  show val C.gates (pr p q) (n + j) = true
  rw [val_gate C.gates _ j hj, ← gateAt_eq C j hj, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  rintro b ⟨a, ha, rfl⟩
  obtain ⟨hlt, s, hs, hvs⟩ := h a ha
  rw [if_pos hlt]
  exact mono C.gates hg (eof s) (pr p q) (eof_le_pr s p q hs) a hvs

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hM : Monotone2 C) (j : ℕ) (u v a b : Fin n)
    (huv : G.Adj u v) (hab : G.Adj a b) (h1 : u ≠ a) (h2 : u ≠ b) (h3 : v ≠ a) (h5 : v ≠ b)
    (hO1 : Owns n C j u v) (hO2 : Owns n C j a b) :
    ∃ p q : Fin n, ¬ G.Adj p q ∧ gateVal n C j (pairInput p q) = true := by
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    obtain ⟨h1', h2'⟩ := hM g hgm
    exact ⟨by simpa using h1', h2'⟩
  have hj := hO1.1
  have hop := hO1.2.1
  have hI1 := inputs_single C hg j u v hO1
  have hI2 := inputs_single C hg j a b hO2
  have hlen : (gateAt C j).inputs.length ≤ 2 := by
    rw [gateAt_eq C j hj]
    exact (hg _ (List.getElem_mem hj)).2
  -- the same vertex works for every input: take the loop pair
  have loop : ∀ s : Fin n, (∀ w ∈ (gateAt C j).inputs, val C.gates (eof s) w = true) →
      ∃ p q : Fin n, ¬ G.Adj p q ∧ gateVal n C j (pairInput p q) = true := by
    intro s hs
    refine ⟨s, s, SimpleGraph.irrefl G, gate_true C hg j hj hop s s ?_⟩
    intro w hw
    exact ⟨(hI1 w hw).1, s, Or.inl rfl, hs w hw⟩
  generalize hins : (gateAt C j).inputs = ins at hI1 hI2 hlen loop
  match ins, hlen with
  | [], _ => exact loop u (by simp)
  | [w], _ =>
    obtain ⟨_, s, _, hs⟩ := hI1 w (by simp)
    exact loop s (by simpa using hs)
  | [w1, w2], _ =>
    obtain ⟨hl1, s1, hs1, hv1⟩ := hI1 w1 (by simp)
    obtain ⟨hl2, s2, hs2, hv2⟩ := hI1 w2 (by simp)
    obtain ⟨_, t1, ht1, hw1⟩ := hI2 w1 (by simp)
    obtain ⟨_, t2, ht2, hw2⟩ := hI2 w2 (by simp)
    by_cases hss : s1 = s2
    · subst hss
      exact loop s1 (by simp [hv1, hv2])
    · by_cases htt : t1 = t2
      · subst htt
        exact loop t1 (by simp [hw1, hw2])
      · have hadj_s : G.Adj s1 s2 := by
          rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl
          · exact absurd rfl hss
          · exact huv
          · exact huv.symm
          · exact absurd rfl hss
        have hadj_t : G.Adj t1 t2 := by
          rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl
          · exact absurd rfl htt
          · exact hab
          · exact hab.symm
          · exact absurd rfl htt
        have hst : s1 ≠ t1 := by
          rcases hs1 with rfl | rfl <;> rcases ht1 with rfl | rfl <;> assumption
        have hs2t2 : s2 ≠ t2 := by
          rcases hs2 with rfl | rfl <;> rcases ht2 with rfl | rfl <;> assumption
        have hnot : ¬ (G.Adj s1 t2 ∧ G.Adj t1 s2) := by
          rintro ⟨hA, hB⟩
          have hc := h4 s1 t1 hst
          have := Finset.card_le_one.mp hc s2 (by simp [hadj_s, hB]) t2 (by simp [hA, hadj_t])
          exact hs2t2 this
        have build : ∀ p q : Fin n, val C.gates (eof p) w1 = true → val C.gates (eof q) w2 = true →
            gateVal n C j (pairInput p q) = true := by
          intro p q hp hq
          refine gate_true C hg j hj hop p q ?_
          intro w hw
          rw [hins] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact ⟨hl1, p, Or.inl rfl, hp⟩
          · exact ⟨hl2, q, Or.inr rfl, hq⟩
        by_cases hA : G.Adj s1 t2
        · have hB : ¬ G.Adj t1 s2 := fun hB => hnot ⟨hA, hB⟩
          exact ⟨t1, s2, hB, build t1 s2 hw1 hv2⟩
        · exact ⟨s1, t2, hA, build s1 t2 hv1 hw2⟩
  | _ :: _ :: _ :: _, h => simp at h

end PEqualNP.Outside.L_meta_4846_aux

theorem PEqualNP.Outside.L_meta_4846 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → ∀ (x7 : ℕ) (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x10 x11 → x8 ≠ x10 → x8 ≠ x11 → x9 ≠ x10 → x9 ≠ x11 → PEqualNP.EdgeOwnership.Owns x1 x4 x7 x8 x9 → PEqualNP.EdgeOwnership.Owns x1 x4 x7 x10 x11 → ∃ (x20 : Fin x1) (x21 : Fin x1), ¬x2.Adj x20 x21 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x7 (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true := by
  intro x1 x2 x3 x4 h4 hM x7 x8 x9 x10 x11 a1 a2 n1 n2 n3 n4 o1 o2
  exact PEqualNP.Outside.L_meta_4846_aux.main x1 x2 x4 h4 hM x7 x8 x9 x10 x11 a1 a2 n1 n2 n3 n4 o1 o2
