import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3653_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

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

-- mono copied from the submitted L_meta_2780
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


-- Good .. val_or, BW .. notBW_input copied from the submitted L_meta_3652
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

def BW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C.gates x w = true → graphFun G ∅ x = true

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

lemma ones {n : ℕ} {C : Circuit} (hG : Good n C) :
    ∀ w, w < n + C.gates.length → val C.gates (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_lt _ _ _ h1]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨a, b, hin, ha, hb, hop⟩ := two hG j hj
      rcases hop with hop | hop
      · rw [val_and _ j hj a b hin ha hb hop, ih a ha (by omega), ih b hb (by omega)]
        rfl
      · rw [val_or _ j hj a b hin ha hb hop, ih a ha (by omega)]
        rfl

lemma notBW_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ)
    (hw : w < n) : ¬ BW G C w := by
  intro h
  have h2 := h (eof ⟨w, hw⟩) (by rw [val_lt _ _ _ hw]; simp [eof])
  rw [F_eof] at h2
  cases h2

/-! the semantic frame -/

lemma F_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma F_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) (hx : graphFun G ∅ x = true) : graphFun G ∅ y = true := by
  rw [F_iff] at hx ⊢
  obtain ⟨u, v, h1, h2, h3⟩ := hx
  exact ⟨u, v, h1, h _ h2, h _ h3⟩

lemma F_pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (h : graphFun G ∅ (pairInput u v) = true) : G.Adj u v := by
  rw [F_iff] at h
  obtain ⟨p, q, hpq, hp, hq⟩ := h
  simp only [pairInput, decide_eq_true_eq] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · rw [hp, hq] at hpq
    exact absurd rfl hpq.ne
  · rw [hp, hq] at hpq
    exact hpq
  · rw [hp, hq] at hpq
    exact hpq.symm
  · rw [hp, hq] at hpq
    exact absurd rfl hpq.ne

lemma bool3 (a b c : Bool) (h1 : a ≠ c) (h2 : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma mono' {n : ℕ} {C : Circuit} (hG : Good n C) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) (w : ℕ) (hx : val C.gates x w = true) :
    val C.gates y w = true :=
  mono C.gates (fun g hg => ⟨(hG.ao g hg).1, le_of_eq (hG.ao g hg).2⟩) x y h w hx

lemma up {n : ℕ} {C : Circuit} (hG : Good n C) {u : Fin n} {w : ℕ} {x : Fin n → Bool}
    (h : val C.gates (eof u) w = true) (hx : x u = true) : val C.gates x w = true := by
  refine mono' hG (eof u) x ?_ w h
  intro i hi
  simp only [eof, decide_eq_true_eq] at hi
  rw [hi]
  exact hx

def Bad {n : ℕ} (C : Circuit) (s : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ u1 u2 : Fin n, s u1 ≠ s u2 ∧ val C.gates (eof u1) w = true ∧ val C.gates (eof u2) w = true

def Lin (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C.gates x w = true → ∃ u, x u = true ∧ val C.gates (eof u) w = true

def Geg (n : ℕ) (C : Circuit) (g w : ℕ) : Prop :=
  n + g ≤ w ∧ ∀ y : Fin n → Bool, val C.gates y (n + g) = true → val C.gates y w = true

structure Hyp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (g : ℕ) (v : Fin n) : Prop where
  good : Good n C
  bip : ∀ u v : Fin n, G.Adj u v → s u ≠ s v
  fn : ∀ x : Fin n → Bool, val C.gates x C.output = graphFun G ∅ x
  h7 : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ∀ t ∈ (gateAt C k).inputs, ¬ BW G C t
  hL : ∀ h < C.gates.length, (gateAt C h).op = GateOp.or → ¬ BW G C (n + h) →
    ∀ t ∈ (gateAt C h).inputs, ¬ BW G C t
  hg : g < C.gates.length
  hgop : (gateAt C g).op = GateOp.and
  clean : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BW G C (n + k)
  hv : val C.gates (eof v) (n + g) = true
  ho : C.output < n + C.gates.length

lemma struct {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v) :
    ∀ w, w < n + C.gates.length → BW G C w ∨ Lin n C w ∨ Geg n C g w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · right; left
      intro x hx
      rw [val_lt _ _ _ h1] at hx
      refine ⟨⟨w, h1⟩, hx, ?_⟩
      rw [val_lt _ _ _ h1]
      simp [eof]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨a, b, hin, ha, hb, hop⟩ := two H.good j hj
      rcases hop with hop | hop
      · by_cases hjg : j = g
        · right; right
          rw [hjg]
          exact ⟨le_refl _, fun y hy => hy⟩
        · left
          exact H.clean j hj hop hjg
      · by_cases hbw : BW G C (n + j)
        · left
          exact hbw
        · have hna := H.hL j hj hop hbw a (by simp [hin])
          have hnb := H.hL j hj hop hbw b (by simp [hin])
          have hor := fun x : Fin n → Bool => val_or (C := C) x j hj a b hin ha hb hop
          rcases ih a ha (by omega) with h | h | h
          · exact absurd h hna
          · rcases ih b hb (by omega) with h' | h' | h'
            · exact absurd h' hnb
            · right; left
              intro x hx
              rw [hor, Bool.or_eq_true] at hx
              rcases hx with hx | hx
              · obtain ⟨u, hu, hu2⟩ := h x hx
                exact ⟨u, hu, by rw [hor, hu2]; rfl⟩
              · obtain ⟨u, hu, hu2⟩ := h' x hx
                exact ⟨u, hu, by rw [hor, hu2]; simp⟩
            · right; right
              exact ⟨by have := h'.1; omega, fun y hy => by rw [hor, h'.2 y hy]; simp⟩
          · right; right
            exact ⟨by have := h.1; omega, fun y hy => by rw [hor, h.2 y hy]; rfl⟩

lemma unit_of_dirty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v) (w : ℕ)
    (hw : w < n + C.gates.length) (hd : ¬ BW G C w) :
    ∃ u : Fin n, val C.gates (eof u) w = true := by
  rcases struct H w hw with h | h | h
  · exact absurd h hd
  · obtain ⟨u, _, hu⟩ := h (fun _ => true) (ones H.good w hw)
    exact ⟨u, hu⟩
  · exact ⟨v, h.2 _ H.hv⟩

lemma pair_l {n : ℕ} (a b : Fin n) : pairInput a b a = true := by simp [pairInput]
lemma pair_r {n : ℕ} (a b : Fin n) : pairInput a b b = true := by simp [pairInput]

lemma bad_absurd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v) (p q : ℕ)
    (hq : q < n + C.gates.length) (hqd : ¬ BW G C q)
    (hpq : ∀ y : Fin n → Bool, val C.gates y p = true → val C.gates y q = true →
      graphFun G ∅ y = true)
    (hb : Bad C s p) : False := by
  obtain ⟨u, hu⟩ := unit_of_dirty H q hq hqd
  obtain ⟨u1, u2, hne, h1, h2⟩ := hb
  have a1 : G.Adj u1 u :=
    F_pair_adj G _ _ (hpq _ (up H.good h1 (pair_l _ _)) (up H.good hu (pair_r _ _)))
  have a2 : G.Adj u2 u :=
    F_pair_adj G _ _ (hpq _ (up H.good h2 (pair_l _ _)) (up H.good hu (pair_r _ _)))
  exact hne (bool3 _ _ _ (H.bip _ _ a1) (H.bip _ _ a2))

lemma FW {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {s : Fin n → Bool}
    {g : ℕ} {v : Fin n} (H : Hyp G C s g v)
    (nv : ℕ → (Fin n → Bool) → Bool)
    (hin : ∀ w (hw : w < n) (x : Fin n → Bool), nv w x = x ⟨w, hw⟩)
    (hmono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      nv C.output x = true → nv C.output y = true)
    (hgate : ∀ j < C.gates.length, j ≠ g →
      (∀ a b, (gateAt C j).inputs = [a, b] →
        ((gateAt C j).op = GateOp.and → ∀ x, nv (n + j) x = (nv a x && nv b x)) ∧
        ((gateAt C j).op = GateOp.or → ∀ x, nv (n + j) x = (nv a x || nv b x))) ∨
      (Bad C s (n + j) ∧ ∃ i, i < n + j ∧ (∀ x, nv (n + j) x = nv i x) ∧
        ∀ x : Fin n → Bool, val C.gates x i = true → val C.gates x (n + j) = true))
    (hsg : ∀ x : Fin n → Bool,
      (∀ w < n + g, nv w x = true → val C.gates x w = true ∨ graphFun G ∅ x = true) →
      nv (n + g) x = true → val C.gates x (n + g) = true ∨ graphFun G ∅ x = true)
    (hkey : ∀ e1 e2 : Fin n, G.Adj e1 e2 → ∀ u : Fin n, (u = e1 ∨ u = e2) →
      (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y u = true → graphFun G ∅ y = true) →
      (∀ w < n + g, val C.gates (pairInput e1 e2) w = true →
        nv w (pairInput e1 e2) = true ∨ Bad C s w) →
      val C.gates (pairInput e1 e2) (n + g) = true → nv (n + g) (pairInput e1 e2) = true) :
    (∀ x, nv C.output x = graphFun G ∅ x) ∧
    (∀ w, w < n + C.gates.length → ∀ x, nv w x = true →
      val C.gates x w = true ∨ graphFun G ∅ x = true) := by
  have snd : ∀ (x : Fin n → Bool) w, w < n + C.gates.length → nv w x = true →
      val C.gates x w = true ∨ graphFun G ∅ x = true := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hx
      by_cases h1 : w < n
      · left
        rw [val_lt _ _ _ h1, ← hin w h1 x]
        exact hx
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        by_cases hjg : j = g
        · rw [hjg] at hx ih ⊢
          exact hsg x (fun w hw' => ih w hw' (by have := H.hg; omega)) hx
        · obtain ⟨a, b, hin', ha, hb, hop⟩ := two H.good j hj
          rcases hgate j hj hjg with h | ⟨_, i, hi, hnvi, hle⟩
          · obtain ⟨hand, hor⟩ := h a b hin'
            rcases hop with hop | hop
            · rw [hand hop, Bool.and_eq_true] at hx
              rcases ih a ha (by omega) hx.1 with h1 | h1
              · rcases ih b hb (by omega) hx.2 with h2 | h2
                · left
                  rw [val_and _ j hj a b hin' ha hb hop, h1, h2]
                  rfl
                · exact Or.inr h2
              · exact Or.inr h1
            · rw [hor hop, Bool.or_eq_true] at hx
              rcases hx with hx | hx
              · rcases ih a ha (by omega) hx with h1 | h1
                · left
                  rw [val_or _ j hj a b hin' ha hb hop, h1]
                  rfl
                · exact Or.inr h1
              · rcases ih b hb (by omega) hx with h1 | h1
                · left
                  rw [val_or _ j hj a b hin' ha hb hop, h1]
                  simp
                · exact Or.inr h1
          · rw [hnvi] at hx
            rcases ih i hi (by omega) hx with h1 | h1
            · exact Or.inl (hle x h1)
            · exact Or.inr h1
  have pres : ∀ e1 e2 : Fin n, G.Adj e1 e2 → ∀ w, w < n + C.gates.length →
      val C.gates (pairInput e1 e2) w = true →
      nv w (pairInput e1 e2) = true ∨ Bad C s w ∨
        (n + g ≤ w ∧ nv (n + g) (pairInput e1 e2) = false ∧
          val C.gates (pairInput e1 e2) (n + g) = true ∧
          ∀ y : Fin n → Bool, val C.gates y (n + g) = true → val C.gates y w = true) := by
    intro e1 e2 hadj w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hx
      by_cases h1 : w < n
      · left
        rw [hin w h1]
        rw [val_lt _ _ _ h1] at hx
        exact hx
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        by_cases hjg : j = g
        · rw [hjg] at hx ⊢
          cases hnv : nv (n + g) (pairInput e1 e2)
          · right; right
            exact ⟨le_refl _, rfl, hx, fun y hy => hy⟩
          · left
            rfl
        · obtain ⟨a, b, hin', ha, hb, hop⟩ := two H.good j hj
          rcases hgate j hj hjg with h | ⟨hbad, _⟩
          swap
          · exact Or.inr (Or.inl hbad)
          obtain ⟨hand, hor⟩ := h a b hin'
          rcases hop with hop | hop
          · have hvand := fun y : Fin n → Bool => val_and (C := C) y j hj a b hin' ha hb hop
            rw [hvand, Bool.and_eq_true] at hx
            have hcl := H.clean j hj hop hjg
            have hda := H.h7 j hj hop a (by simp [hin'])
            have hdb := H.h7 j hj hop b (by simp [hin'])
            have side : ∀ p q, p < n + j → q < n + j → ¬ BW G C q →
                (∀ y : Fin n → Bool, val C.gates y p = true → val C.gates y q = true →
                  graphFun G ∅ y = true) →
                val C.gates (pairInput e1 e2) p = true → val C.gates (pairInput e1 e2) q = true →
                nv p (pairInput e1 e2) = true := by
              intro p q hp hq hqd hpq hxp hxq
              rcases ih p hp (by omega) hxp with h | h | ⟨hge, hnvg, hgx, hpg⟩
              · exact h
              · exact (bad_absurd H p q (by omega) hqd hpq h).elim
              · exfalso
                rcases struct H q (by omega) with hq1 | hq1 | hq1
                · exact hqd hq1
                · obtain ⟨u, hu, hu2⟩ := hq1 _ hxq
                  have hu' : u = e1 ∨ u = e2 := by simpa [pairInput] using hu
                  have hz : ∀ y : Fin n → Bool, val C.gates y (n + g) = true → y u = true →
                      graphFun G ∅ y = true :=
                    fun y hy hyu => hpq y (hpg y hy) (up H.good hu2 hyu)
                  have hpre : ∀ w < n + g, val C.gates (pairInput e1 e2) w = true →
                      nv w (pairInput e1 e2) = true ∨ Bad C s w := by
                    intro w hw' hxw
                    rcases ih w (by omega) (by omega) hxw with h | h | h
                    · exact Or.inl h
                    · exact Or.inr h
                    · have := h.1
                      omega
                  have h3 := hkey e1 e2 hadj u hu' hz hpre hgx
                  rw [h3] at hnvg
                  cases hnvg
                · have h2 := hpq _ (hpg _ H.hv) (hq1.2 _ H.hv)
                  rw [F_eof] at h2
                  cases h2
            have na := side a b ha hb hdb
              (fun y h1 h2 => hcl y (by rw [hvand, h1, h2]; rfl)) hx.1 hx.2
            have nb := side b a hb ha hda
              (fun y h1 h2 => hcl y (by rw [hvand, h2, h1]; rfl)) hx.2 hx.1
            left
            rw [hand hop, na, nb]
            rfl
          · have hvor := fun y : Fin n → Bool => val_or (C := C) y j hj a b hin' ha hb hop
            rw [hvor, Bool.or_eq_true] at hx
            have side : ∀ p, p < n + j →
                (∀ y : Fin n → Bool, val C.gates y p = true → val C.gates y (n + j) = true) →
                (∀ x : Fin n → Bool, nv p x = true → nv (n + j) x = true) →
                val C.gates (pairInput e1 e2) p = true →
                nv (n + j) (pairInput e1 e2) = true ∨ Bad C s (n + j) ∨
                  (n + g ≤ n + j ∧ nv (n + g) (pairInput e1 e2) = false ∧
                    val C.gates (pairInput e1 e2) (n + g) = true ∧
                    ∀ y : Fin n → Bool, val C.gates y (n + g) = true →
                      val C.gates y (n + j) = true) := by
              intro p hp hle hnle hxp
              rcases ih p hp (by omega) hxp with h | h | ⟨hge, hnvg, hgx, hpg⟩
              · exact Or.inl (hnle _ h)
              · obtain ⟨u1, u2, hne, h1, h2⟩ := h
                exact Or.inr (Or.inl ⟨u1, u2, hne, hle _ h1, hle _ h2⟩)
              · exact Or.inr (Or.inr ⟨by omega, hnvg, hgx, fun y hy => hle y (hpg y hy)⟩)
            rcases hx with hx | hx
            · exact side a ha (fun y hy => by rw [hvor, hy]; rfl)
                (fun x hx => by rw [hor hop, hx]; rfl) hx
            · exact side b hb (fun y hy => by rw [hvor, hy]; simp)
                (fun x hx => by rw [hor hop, hx]; simp) hx
  refine ⟨?_, fun w hw x => snd x w hw⟩
  intro x
  cases hFx : graphFun G ∅ x
  · cases hnx : nv C.output x
    · rfl
    · rcases snd x _ H.ho hnx with h | h
      · rw [H.fn, hFx] at h
        cases h
      · rw [hFx] at h
        cases h
  · obtain ⟨e1, e2, hadj, hx1, hx2⟩ := (F_iff G x).1 hFx
    have hv0 : val C.gates (pairInput e1 e2) C.output = true := by
      rw [H.fn]
      exact F_pair G _ _ hadj
    have h4 : nv C.output (pairInput e1 e2) = true := by
      rcases pres e1 e2 hadj _ H.ho hv0 with h | ⟨u1, u2, _, h1, _⟩ | ⟨_, _, _, hge⟩
      · exact h
      · rw [H.fn, F_eof] at h1
        cases h1
      · have h5 := hge _ H.hv
        rw [H.fn, F_eof] at h5
        cases h5
    refine hmono _ _ ?_ h4
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with hi | hi
    · rw [hi]; exact hx1
    · rw [hi]; exact hx2

/-! circuits from an index function -/

def mk (f : ℕ → Gate) (len : ℕ) : List Gate := (List.range len).map f

lemma mk_len (f : ℕ → Gate) (len : ℕ) : (mk f len).length = len := by simp [mk]

lemma mk_gateAt (f : ℕ → Gate) (len o j : ℕ) (hj : j < len) : gateAt ⟨mk f len, o⟩ j = f j := by
  unfold gateAt mk
  simp [List.getD_eq_getElem?_getD, hj]

lemma mk_good {n : ℕ} (f : ℕ → Gate) (len o : ℕ)
    (h : ∀ j < len, ((f j).op = GateOp.and ∨ (f j).op = GateOp.or) ∧
      ∃ a b, (f j).inputs = [a, b] ∧ a < n + j ∧ b < n + j) : Good n ⟨mk f len, o⟩ := by
  constructor
  · intro gt hgt
    simp only [mk, List.mem_map, List.mem_range] at hgt
    obtain ⟨j, hj, rfl⟩ := hgt
    obtain ⟨hop, a, b, hab, _, _⟩ := h j hj
    exact ⟨hop, by rw [hab]; rfl⟩
  · intro j hj i hi
    have hj' : j < len := by simpa [mk_len] using hj
    rw [mk_gateAt f len o j hj'] at hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h j hj'
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption

lemma mk_val {n : ℕ} (f : ℕ → Gate) (len o : ℕ) (hD : Good n ⟨mk f len, o⟩) (j : ℕ) (hj : j < len)
    (a b : ℕ) (hin : (f j).inputs = [a, b]) :
    ((f j).op = GateOp.and → ∀ x : Fin n → Bool,
      val (mk f len) x (n + j) = (val (mk f len) x a && val (mk f len) x b)) ∧
    ((f j).op = GateOp.or → ∀ x : Fin n → Bool,
      val (mk f len) x (n + j) = (val (mk f len) x a || val (mk f len) x b)) := by
  have hj' : j < (⟨mk f len, o⟩ : Circuit).gates.length := by simpa [mk_len] using hj
  have hga := mk_gateAt f len o j hj
  have hin' : (gateAt ⟨mk f len, o⟩ j).inputs = [a, b] := by rw [hga]; exact hin
  have ha : a < n + j := hD.rb j hj' a (by rw [hin']; simp)
  have hb : b < n + j := hD.rb j hj' b (by rw [hin']; simp)
  constructor
  · intro hop x
    exact val_and (C := ⟨mk f len, o⟩) x j hj' a b hin' ha hb (by rw [hga]; exact hop)
  · intro hop x
    exact val_or (C := ⟨mk f len, o⟩) x j hj' a b hin' ha hb (by rw [hga]; exact hop)

def Res (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∃ D : Circuit, Good n D ∧ D.gates.length ≤ C.gates.length ∧
    (∀ x : Fin n → Bool, val D.gates x D.output = graphFun G ∅ x) ∧
    ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BW G D (n + k)

lemma inplace {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v) (f : ℕ → Gate)
    (hD : Good n ⟨mk f C.gates.length, C.output⟩)
    (hf : ∀ j < C.gates.length, j ≠ g → f j = gateAt C j ∨
      (Bad C s (n + j) ∧ (gateAt C j).op = GateOp.or ∧
        ∃ i ∈ (gateAt C j).inputs, f j = ⟨GateOp.or, [i, i]⟩))
    (hgc : ∀ x : Fin n → Bool, val (mk f C.gates.length) x (n + g) = true →
      val C.gates x (n + g) = true ∨ graphFun G ∅ x = true)
    (hgand : (f g).op = GateOp.and → ∀ x : Fin n → Bool,
      val (mk f C.gates.length) x (n + g) = true → graphFun G ∅ x = true)
    (hkey : ∀ e1 e2 : Fin n, G.Adj e1 e2 → ∀ u : Fin n, (u = e1 ∨ u = e2) →
      (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y u = true → graphFun G ∅ y = true) →
      val C.gates (pairInput e1 e2) (n + g) = true →
      val (mk f C.gates.length) (pairInput e1 e2) (n + g) = true) : Res n G C := by
  obtain ⟨hfun, hsnd⟩ := FW H (fun w x => val (mk f C.gates.length) x w)
    (fun w hw x => val_lt _ _ _ hw)
    (fun x y hxy h => mono' hD x y hxy _ h)
    (by
      intro j hj hjg
      rcases hf j hj hjg with h | ⟨hbad, hop, i, hi, hfi⟩
      · left
        intro a b hin
        have h2 := mk_val f C.gates.length C.output hD j hj a b (by rw [h]; exact hin)
        rw [h] at h2
        exact h2
      · right
        obtain ⟨a, b, hin, ha, hb, _⟩ := two H.good j hj
        have hi' : i < n + j := H.good.rb j hj i hi
        refine ⟨hbad, i, hi', ?_, ?_⟩
        · intro x
          have h2 := (mk_val f C.gates.length C.output hD j hj i i (by rw [hfi])).2
            (by rw [hfi]) x
          simp only [h2, Bool.or_self]
        · intro x hx
          rw [val_or _ j hj a b hin ha hb hop]
          rw [hin] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · rw [hx]; rfl
          · rw [hx]; simp)
    (fun x _ hx => hgc x hx)
    (fun e1 e2 hadj u hu hz _ hgx => hkey e1 e2 hadj u hu hz hgx)
  refine ⟨⟨mk f C.gates.length, C.output⟩, hD, by simp [mk_len], hfun, ?_⟩
  intro k hk hop x hx
  have hk' : k < C.gates.length := by simpa [mk_len] using hk
  rw [mk_gateAt f _ _ k hk'] at hop
  by_cases hkg : k = g
  · rw [hkg] at hop hx
    exact hgand hop x hx
  · rcases hf k hk' hkg with h | ⟨_, _, i, _, hfi⟩
    · rw [h] at hop
      rcases hsnd (n + k) (by omega) x hx with h1 | h1
      · exact H.clean k hk' hop hkg x h1
      · exact h1
    · rw [hfi] at hop
      exact absurd hop (by simp)

/-! first construction: the gate becomes the variable -/

def f1 (C : Circuit) (g v : ℕ) : ℕ → Gate :=
  fun j => if j = g then ⟨GateOp.or, [v, v]⟩ else gateAt C j

lemma x1 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v)
    (hk : ∀ e1 e2 : Fin n, G.Adj e1 e2 → ∀ u : Fin n, (u = e1 ∨ u = e2) →
      (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y u = true → graphFun G ∅ y = true) →
      val C.gates (pairInput e1 e2) (n + g) = true → e1 = v ∨ e2 = v) : Res n G C := by
  have hvl := v.isLt
  have hD : Good n ⟨mk (f1 C g v.val) C.gates.length, C.output⟩ := by
    apply mk_good
    intro j hj
    by_cases hjg : j = g
    · rw [show f1 C g v.val j = ⟨GateOp.or, [v.val, v.val]⟩ from if_pos hjg]
      exact ⟨Or.inr rfl, v.val, v.val, rfl, by omega, by omega⟩
    · rw [show f1 C g v.val j = gateAt C j from if_neg hjg]
      obtain ⟨a, b, hin, ha, hb, hop⟩ := two H.good j hj
      exact ⟨hop, a, b, hin, ha, hb⟩
  have hgv : ∀ x : Fin n → Bool, val (mk (f1 C g v.val) C.gates.length) x (n + g) = x v := by
    intro x
    have h := (mk_val _ C.gates.length C.output hD g H.hg v.val v.val (by simp [f1])).2
      (by simp [f1]) x
    rw [h, val_lt _ _ _ v.isLt]
    simp
  refine inplace H _ hD (fun j hj hjg => Or.inl (if_neg hjg)) ?_ ?_ ?_
  · intro x hx
    rw [hgv] at hx
    exact Or.inl (up H.good H.hv hx)
  · intro hop
    simp [f1] at hop
  · intro e1 e2 hadj u hu hz hgx
    rw [hgv]
    rcases hk e1 e2 hadj u hu hz hgx with h | h
    · rw [← h]; exact pair_l _ _
    · rw [← h]; exact pair_r _ _

/-! the combinatorial case split -/

lemma comb_beta {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin n → Bool)
    (hs : ∀ u v : Fin n, G.Adj u v → s u ≠ s v)
    (h4 : ∀ a b w1 w2 : Fin n, a ≠ b → G.Adj a w1 → G.Adj b w1 → G.Adj a w2 → G.Adj b w2 →
      w1 = w2)
    (v : Fin n) (A B Z : Fin n → Prop)
    (hstar : ∀ a b z, A a → B b → Z z → G.Adj a b ∨ G.Adj a z ∨ G.Adj b z)
    (hZv : ∀ z, Z z → G.Adj v z)
    (z0 : Fin n) (hBz : B z0) (hZ0 : Z z0) :
    s z0 ≠ s v ∧ (∀ u, A u → G.Adj u z0) ∧
      ∀ e1 z, G.Adj e1 z → Z z → (A e1 ∨ A z) → e1 = v ∨ (z = z0 ∧ A e1) := by
  have hN : ∀ u, A u → G.Adj u z0 := by
    intro u hu
    rcases hstar u z0 z0 hu hBz hZ0 with h | h | h
    · exact h
    · exact h
    · exact absurd rfl h.ne
  refine ⟨fun h => hs _ _ (hZv z0 hZ0) h.symm, hN, ?_⟩
  intro e1 z hadj hz hA
  by_cases he : e1 = v
  · exact Or.inl he
  · right
    rcases hA with hA | hA
    · exact ⟨h4 e1 v z z0 he hadj (hZv z hz) (hN e1 hA) (hZv z0 hZ0), hA⟩
    · exfalso
      have h1 := hs _ _ (hN z hA)
      have h2 := hs _ _ (hZv z hz)
      have h3 := hs _ _ (hZv z0 hZ0)
      exact h1 (bool3 _ _ _ h2.symm h3.symm)

lemma comb {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin n → Bool)
    (hs : ∀ u v : Fin n, G.Adj u v → s u ≠ s v)
    (h4 : ∀ a b w1 w2 : Fin n, a ≠ b → G.Adj a w1 → G.Adj b w1 → G.Adj a w2 → G.Adj b w2 →
      w1 = w2)
    (v : Fin n) (A B Z : Fin n → Prop)
    (hstar : ∀ a b z, A a → B b → Z z → G.Adj a b ∨ G.Adj a z ∨ G.Adj b z)
    (hZv : ∀ z, Z z → G.Adj v z) :
    (∀ e1 z, G.Adj e1 z → Z z → (A e1 ∨ A z) ∧ (B e1 ∨ B z) → e1 = v) ∨
    (∃ q, ((∀ u, A u → s u = s v → G.Adj u q) ∧
            ∀ e1 z, G.Adj e1 z → Z z → (A e1 ∨ A z) ∧ (B e1 ∨ B z) → z = q ∧ A e1) ∨
          ((∀ u, B u → s u = s v → G.Adj u q) ∧
            ∀ e1 z, G.Adj e1 z → Z z → (A e1 ∨ A z) ∧ (B e1 ∨ B z) → z = q ∧ B e1)) ∨
    (∃ m, (B m ∧ s m ≠ s v ∧ (∀ u, A u → G.Adj u m) ∧
            ∀ e1 z, G.Adj e1 z → Z z → (A e1 ∨ A z) → e1 = v ∨ (z = m ∧ A e1)) ∨
          (A m ∧ s m ≠ s v ∧ (∀ u, B u → G.Adj u m) ∧
            ∀ e1 z, G.Adj e1 z → Z z → (B e1 ∨ B z) → e1 = v ∨ (z = m ∧ B e1))) := by
  by_cases hK1 : ∀ e1 z, G.Adj e1 z → Z z → (A e1 ∨ A z) ∧ (B e1 ∨ B z) → e1 = v
  · exact Or.inl hK1
  · right
    push_neg at hK1
    obtain ⟨e1, z0, hadj, hZ0, ⟨hgA, hgB⟩, hne⟩ := hK1
    have hstar' : ∀ a b z, B a → A b → Z z → G.Adj a b ∨ G.Adj a z ∨ G.Adj b z := by
      intro a b z ha hb hz
      rcases hstar b a z hb ha hz with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    have hnn : ¬ (A z0 ∧ B z0) := by
      rintro ⟨h1, h2⟩
      rcases hstar z0 z0 z0 h1 h2 hZ0 with h | h | h <;> exact absurd rfl h.ne
    by_cases hAB : A e1 ∧ B e1
    · left
      refine ⟨z0, ?_⟩
      have hZ1 : ∀ z, Z z → z = z0 := by
        intro z hz
        have h1 : G.Adj e1 z := by
          rcases hstar e1 e1 z hAB.1 hAB.2 hz with h | h | h
          · exact absurd rfl h.ne
          · exact h
          · exact h
        exact h4 e1 v z z0 hne h1 (hZv z hz) hadj (hZv z0 hZ0)
      by_cases hAz : A z0
      · right
        refine ⟨?_, ?_⟩
        · intro u hu _
          rcases hstar z0 u z0 hAz hu hZ0 with h | h | h
          · exact h.symm
          · exact absurd rfl h.ne
          · exact h
        · intro e1' z _ hz hg
          have hzz := hZ1 z hz
          refine ⟨hzz, ?_⟩
          rcases hg.2 with h | h
          · exact h
          · rw [hzz] at h
            exact absurd ⟨hAz, h⟩ hnn
      · by_cases hBz : B z0
        · left
          refine ⟨?_, ?_⟩
          · intro u hu _
            rcases hstar u z0 z0 hu hBz hZ0 with h | h | h
            · exact h
            · exact h
            · exact absurd rfl h.ne
          · intro e1' z _ hz hg
            have hzz := hZ1 z hz
            refine ⟨hzz, ?_⟩
            rcases hg.1 with h | h
            · exact h
            · rw [hzz] at h
              exact absurd h hAz
        · have hboth : ∀ e1' z, G.Adj e1' z → Z z → (A e1' ∨ A z) ∧ (B e1' ∨ B z) →
              z = z0 ∧ A e1' ∧ B e1' := by
            intro e1' z _ hz hg
            have hzz := hZ1 z hz
            rw [hzz] at hg
            exact ⟨hzz, hg.1.resolve_right hAz, hg.2.resolve_right hBz⟩
          by_cases hAq : ∀ u, A u → s u = s v → G.Adj u z0
          · left
            exact ⟨hAq, fun e1' z h1 h2 h3 =>
              ⟨(hboth e1' z h1 h2 h3).1, (hboth e1' z h1 h2 h3).2.1⟩⟩
          · right
            push_neg at hAq
            obtain ⟨a0, ha0, hsa0, hna0⟩ := hAq
            refine ⟨?_, fun e1' z h1 h2 h3 =>
              ⟨(hboth e1' z h1 h2 h3).1, (hboth e1' z h1 h2 h3).2.2⟩⟩
            intro u hu hsu
            rcases hstar a0 u z0 ha0 hu hZ0 with h | h | h
            · exact absurd (hsa0.trans hsu.symm) (hs _ _ h)
            · exact absurd h hna0
            · exact h
    · right
      rcases hgA with hA1 | hAz
      · have hBz : B z0 := by
          rcases hgB with h | h
          · exact absurd ⟨hA1, h⟩ hAB
          · exact h
        obtain ⟨h1, h2, h3⟩ := comb_beta G s hs h4 v A B Z hstar hZv z0 hBz hZ0
        exact ⟨z0, Or.inl ⟨hBz, h1, h2, h3⟩⟩
      · have hB1 : B e1 := by
          rcases hgB with h | h
          · exact h
          · exact absurd ⟨hAz, h⟩ hnn
        obtain ⟨h1, h2, h3⟩ := comb_beta G s hs h4 v B A Z hstar' hZv z0 hAz hZ0
        exact ⟨z0, Or.inr ⟨hAz, h1, h2, h3⟩⟩

/-! second construction: two-sided OR gates lose one side, the gate becomes a clean AND -/

def Ro {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (w : ℕ) : Prop :=
  ∀ u : Fin n, val C.gates (eof u) w = true → s u ≠ s v

open Classical in
noncomputable def f4 {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g c q : ℕ) : ℕ → Gate :=
  fun j => if j = g then ⟨GateOp.and, [c, q]⟩ else
    if (gateAt C j).op = GateOp.or ∧ Bad C s (n + j) then
      (if Ro C s v ((gateAt C j).inputs.getD 0 0) ∧ ¬ Ro C s v ((gateAt C j).inputs.getD 1 0) then
        ⟨GateOp.or, [(gateAt C j).inputs.getD 1 0, (gateAt C j).inputs.getD 1 0]⟩
      else if Ro C s v ((gateAt C j).inputs.getD 1 0) ∧
          ¬ Ro C s v ((gateAt C j).inputs.getD 0 0) then
        ⟨GateOp.or, [(gateAt C j).inputs.getD 0 0, (gateAt C j).inputs.getD 0 0]⟩
      else gateAt C j)
    else gateAt C j

lemma f4_spec {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g c q j a b : ℕ)
    (hjg : j ≠ g) (hin : (gateAt C j).inputs = [a, b]) :
    (f4 C s v g c q j = gateAt C j ∧
      ((gateAt C j).op = GateOp.or → Bad C s (n + j) → (Ro C s v a ↔ Ro C s v b))) ∨
    ((gateAt C j).op = GateOp.or ∧ Bad C s (n + j) ∧ Ro C s v a ∧ ¬ Ro C s v b ∧
      f4 C s v g c q j = ⟨GateOp.or, [b, b]⟩) ∨
    ((gateAt C j).op = GateOp.or ∧ Bad C s (n + j) ∧ Ro C s v b ∧ ¬ Ro C s v a ∧
      f4 C s v g c q j = ⟨GateOp.or, [a, a]⟩) := by
  have e0 : (gateAt C j).inputs.getD 0 0 = a := by rw [hin]; rfl
  have e1 : (gateAt C j).inputs.getD 1 0 = b := by rw [hin]; rfl
  unfold f4
  rw [if_neg hjg, e0, e1]
  by_cases h1 : (gateAt C j).op = GateOp.or ∧ Bad C s (n + j)
  · rw [if_pos h1]
    by_cases h2 : Ro C s v a ∧ ¬ Ro C s v b
    · rw [if_pos h2]
      exact Or.inr (Or.inl ⟨h1.1, h1.2, h2.1, h2.2, rfl⟩)
    · rw [if_neg h2]
      by_cases h3 : Ro C s v b ∧ ¬ Ro C s v a
      · rw [if_pos h3]
        exact Or.inr (Or.inr ⟨h1.1, h1.2, h3.1, h3.2, rfl⟩)
      · rw [if_neg h3]
        left
        refine ⟨rfl, fun _ _ => ?_⟩
        tauto
  · rw [if_neg h1]
    left
    exact ⟨rfl, fun h h' => absurd ⟨h, h'⟩ h1⟩

lemma x4core {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v) (c : ℕ) (q : Fin n)
    (hc : c < n + g) (hcv : val C.gates (eof v) c = true)
    (hNq : ∀ u : Fin n, val C.gates (eof u) c = true → s u = s v → G.Adj u q)
    (hZv : ∀ z : Fin n, (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true →
      graphFun G ∅ y = true) → G.Adj v z)
    (hkey : ∀ e1 z : Fin n, G.Adj e1 z →
      (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true → graphFun G ∅ y = true) →
      val C.gates (pairInput e1 z) (n + g) = true → z = q ∧ val C.gates (eof e1) c = true)
    (f : ℕ → Gate) (hfg : f g = ⟨GateOp.and, [c, q.val]⟩)
    (hspec : ∀ j, j ≠ g → ∀ a b, (gateAt C j).inputs = [a, b] →
      (f j = gateAt C j ∧
        ((gateAt C j).op = GateOp.or → Bad C s (n + j) → (Ro C s v a ↔ Ro C s v b))) ∨
      ((gateAt C j).op = GateOp.or ∧ Bad C s (n + j) ∧ Ro C s v a ∧ ¬ Ro C s v b ∧
        f j = ⟨GateOp.or, [b, b]⟩) ∨
      ((gateAt C j).op = GateOp.or ∧ Bad C s (n + j) ∧ Ro C s v b ∧ ¬ Ro C s v a ∧
        f j = ⟨GateOp.or, [a, a]⟩)) : Res n G C := by
  have hql := q.isLt
  have hgl := H.hg
  have hD : Good n ⟨mk f C.gates.length, C.output⟩ := by
    apply mk_good
    intro j hj
    by_cases hjg : j = g
    · rw [hjg, hfg]
      exact ⟨Or.inl rfl, c, q.val, rfl, by omega, by omega⟩
    · obtain ⟨a, b, hin, ha, hb, hop⟩ := two H.good j hj
      rcases hspec j hjg a b hin with ⟨h, _⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
      · rw [h]
        exact ⟨hop, a, b, hin, ha, hb⟩
      · rw [h]
        exact ⟨Or.inr rfl, b, b, rfl, hb, hb⟩
      · rw [h]
        exact ⟨Or.inr rfl, a, a, rfl, ha, ha⟩
  have gv : ∀ j, j < C.gates.length → j ≠ g → ∀ a b, (gateAt C j).inputs = [a, b] →
      (((gateAt C j).op = GateOp.and → ∀ x : Fin n → Bool,
          val (mk f C.gates.length) x (n + j) =
            (val (mk f C.gates.length) x a && val (mk f C.gates.length) x b)) ∧
       ((gateAt C j).op = GateOp.or → ∀ x : Fin n → Bool,
          val (mk f C.gates.length) x (n + j) =
            (val (mk f C.gates.length) x a || val (mk f C.gates.length) x b)) ∧
       ((gateAt C j).op = GateOp.or → Bad C s (n + j) → (Ro C s v a ↔ Ro C s v b))) ∨
      ((gateAt C j).op = GateOp.or ∧ Bad C s (n + j) ∧ Ro C s v a ∧ ¬ Ro C s v b ∧
        ∀ x : Fin n → Bool,
          val (mk f C.gates.length) x (n + j) = val (mk f C.gates.length) x b) ∨
      ((gateAt C j).op = GateOp.or ∧ Bad C s (n + j) ∧ Ro C s v b ∧ ¬ Ro C s v a ∧
        ∀ x : Fin n → Bool,
          val (mk f C.gates.length) x (n + j) = val (mk f C.gates.length) x a) := by
    intro j hj hjg a b hin
    rcases hspec j hjg a b hin with ⟨h, h'⟩ | ⟨h1, h2, h3, h4, h⟩ | ⟨h1, h2, h3, h4, h⟩
    · left
      have h2 := mk_val f C.gates.length C.output hD j hj a b (by rw [h]; exact hin)
      rw [h] at h2
      exact ⟨h2.1, h2.2, h'⟩
    · right; left
      refine ⟨h1, h2, h3, h4, fun x => ?_⟩
      have h5 := (mk_val f C.gates.length C.output hD j hj b b (by rw [h])).2 (by rw [h]) x
      rw [h5, Bool.or_self]
    · right; right
      refine ⟨h1, h2, h3, h4, fun x => ?_⟩
      have h5 := (mk_val f C.gates.length C.output hD j hj a a (by rw [h])).2 (by rw [h]) x
      rw [h5, Bool.or_self]
  have hLc : ∀ w, w < n + g → ∀ u : Fin n, s u = s v → val C.gates (eof u) w = true →
      val (mk f C.gates.length) (eof u) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw u hsu hu
      by_cases h1 : w < n
      · rw [val_lt _ _ _ h1] at hu ⊢
        exact hu
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hjg : j ≠ g := by omega
        obtain ⟨a, b, hin, ha, hb, hop⟩ := two H.good j hj
        rcases gv j hj hjg a b hin with ⟨hand, hor, _⟩ | ⟨hop', _, hra, _, hval⟩ |
          ⟨hop', _, hrb, _, hval⟩
        · rcases hop with hop | hop
          · have h2 := H.clean j hj hop hjg _ hu
            rw [F_eof] at h2
            cases h2
          · rw [val_or _ j hj a b hin ha hb hop, Bool.or_eq_true] at hu
            rw [hor hop, Bool.or_eq_true]
            rcases hu with hu | hu
            · exact Or.inl (ih a ha (by omega) u hsu hu)
            · exact Or.inr (ih b hb (by omega) u hsu hu)
        · rw [val_or _ j hj a b hin ha hb hop', Bool.or_eq_true] at hu
          rw [hval]
          rcases hu with hu | hu
          · exact absurd hsu (hra u hu)
          · exact ih b hb (by omega) u hsu hu
        · rw [val_or _ j hj a b hin ha hb hop', Bool.or_eq_true] at hu
          rw [hval]
          rcases hu with hu | hu
          · exact ih a ha (by omega) u hsu hu
          · exact absurd hsu (hrb u hu)
  have hR : ∀ w, w < n + g → ∀ x : Fin n → Bool, val (mk f C.gates.length) x w = true →
      graphFun G ∅ x = true ∨ ∃ u : Fin n, x u = true ∧ val C.gates (eof u) w = true ∧
        (Bad C s w → s u = s v) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw x hx
      by_cases h1 : w < n
      · right
        rw [val_lt _ _ _ h1] at hx
        refine ⟨⟨w, h1⟩, hx, by rw [val_lt _ _ _ h1]; simp [eof], ?_⟩
        rintro ⟨u1, u2, hne, h1', h2'⟩
        rw [val_lt _ _ _ h1] at h1' h2'
        simp only [eof, decide_eq_true_eq] at h1' h2'
        exact absurd (by rw [← h1', ← h2']) hne
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hjg : j ≠ g := by omega
        obtain ⟨a, b, hin, ha, hb, hop⟩ := two H.good j hj
        rcases gv j hj hjg a b hin with ⟨hand, hor, hiff⟩ | ⟨hop', hbad, hra, hnrb, hval⟩ |
          ⟨hop', hbad, hrb, hnra, hval⟩
        · rcases hop with hop | hop
          · rw [hand hop, Bool.and_eq_true] at hx
            rcases ih a ha (by omega) x hx.1 with h | ⟨ua, hxa, hua, _⟩
            · exact Or.inl h
            · rcases ih b hb (by omega) x hx.2 with h | ⟨ub, hxb, hub, _⟩
              · exact Or.inl h
              · left
                have h3 : val C.gates (pairInput ua ub) (n + j) = true := by
                  rw [val_and _ j hj a b hin ha hb hop, up H.good hua (pair_l _ _),
                    up H.good hub (pair_r _ _)]
                  rfl
                refine F_mono G _ x ?_ (H.clean j hj hop hjg _ h3)
                intro i hi
                simp only [pairInput, decide_eq_true_eq] at hi
                rcases hi with hi | hi
                · rw [hi]; exact hxa
                · rw [hi]; exact hxb
          · have hvor := fun y : Fin n → Bool => val_or (C := C) y j hj a b hin ha hb hop
            have side : ∀ p p', p < n + j →
                (∀ y : Fin n → Bool, val C.gates y (n + j) = true →
                  val C.gates y p = true ∨ val C.gates y p' = true) →
                (∀ y : Fin n → Bool, val C.gates y p = true → val C.gates y (n + j) = true) →
                (Bad C s (n + j) → Ro C s v p → Ro C s v p') →
                val (mk f C.gates.length) x p = true →
                graphFun G ∅ x = true ∨ ∃ u : Fin n, x u = true ∧
                  val C.gates (eof u) (n + j) = true ∧ (Bad C s (n + j) → s u = s v) := by
              intro p p' hp hsplit hle hro hxp
              rcases ih p hp (by omega) x hxp with h | ⟨u, hxu, hu, hbu⟩
              · exact Or.inl h
              · right
                refine ⟨u, hxu, hle _ hu, fun hbad => ?_⟩
                by_cases hbp : Bad C s p
                · exact hbu hbp
                · by_contra hne
                  have hrop : Ro C s v p := by
                    intro u' hu' heq
                    exact hbp ⟨u, u', fun h => hne (h.trans heq), hu, hu'⟩
                  have hrop' := hro hbad hrop
                  obtain ⟨u1, u2, hne12, h1', h2'⟩ := hbad
                  have e1 : s u1 ≠ s v := by
                    rcases hsplit _ h1' with h | h
                    · exact hrop u1 h
                    · exact hrop' u1 h
                  have e2 : s u2 ≠ s v := by
                    rcases hsplit _ h2' with h | h
                    · exact hrop u2 h
                    · exact hrop' u2 h
                  exact hne12 (bool3 _ _ _ e1 e2)
            rw [hor hop, Bool.or_eq_true] at hx
            rcases hx with hx | hx
            · exact side a b ha
                (fun y hy => by rw [hvor, Bool.or_eq_true] at hy; exact hy)
                (fun y hy => by rw [hvor, hy]; rfl)
                (fun hb' h => (hiff hop hb').1 h) hx
            · exact side b a hb
                (fun y hy => by rw [hvor, Bool.or_eq_true] at hy; exact hy.symm)
                (fun y hy => by rw [hvor, hy]; simp)
                (fun hb' h => (hiff hop hb').2 h) hx
        · rw [hval] at hx
          rcases ih b hb (by omega) x hx with h | ⟨u, hxu, hu, hbu⟩
          · exact Or.inl h
          · right
            refine ⟨u, hxu, by rw [val_or _ j hj a b hin ha hb hop', hu]; simp, fun _ => ?_⟩
            by_cases hbp : Bad C s b
            · exact hbu hbp
            · by_contra hne
              apply hnrb
              intro u' hu' heq
              exact hbp ⟨u, u', fun h => hne (h.trans heq), hu, hu'⟩
        · rw [hval] at hx
          rcases ih a ha (by omega) x hx with h | ⟨u, hxu, hu, hbu⟩
          · exact Or.inl h
          · right
            refine ⟨u, hxu, by rw [val_or _ j hj a b hin ha hb hop', hu]; rfl, fun _ => ?_⟩
            by_cases hbp : Bad C s a
            · exact hbu hbp
            · by_contra hne
              apply hnra
              intro u' hu' heq
              exact hbp ⟨u, u', fun h => hne (h.trans heq), hu, hu'⟩
  have hgval : ∀ x : Fin n → Bool, val (mk f C.gates.length) x (n + g) =
      (val (mk f C.gates.length) x c && x q) := by
    intro x
    have h := (mk_val f C.gates.length C.output hD g H.hg c q.val (by rw [hfg])).1
      (by rw [hfg]) x
    rw [h, val_lt _ _ _ q.isLt]
  have hgF : ∀ x : Fin n → Bool, val (mk f C.gates.length) x (n + g) = true →
      graphFun G ∅ x = true := by
    intro x hx
    rw [hgval, Bool.and_eq_true] at hx
    rcases hR c hc x hx.1 with h | ⟨u, hxu, hu, hbu⟩
    · exact h
    · have hsu : s u = s v := by
        by_cases hbc : Bad C s c
        · exact hbu hbc
        · by_contra hne
          exact hbc ⟨u, v, hne, hu, hcv⟩
      exact (F_iff G x).2 ⟨u, q, hNq u hu hsu, hxu, hx.2⟩
  refine inplace H f hD ?_ (fun x hx => Or.inr (hgF x hx)) (fun _ => hgF) ?_
  · intro j hj hjg
    obtain ⟨a, b, hin, ha, hb, hop⟩ := two H.good j hj
    rcases hspec j hjg a b hin with ⟨h, _⟩ | ⟨h1, h2, _, _, h⟩ | ⟨h1, h2, _, _, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨h2, h1, b, by simp [hin], h⟩
    · exact Or.inr ⟨h2, h1, a, by simp [hin], h⟩
  · intro e1 e2 hadj u hu hz hgx
    have main : ∀ e z : Fin n, G.Adj e z →
        (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true →
          graphFun G ∅ y = true) →
        val C.gates (pairInput e z) (n + g) = true → ∀ x : Fin n → Bool, x e = true →
        x z = true → val (mk f C.gates.length) x (n + g) = true := by
      intro e z hadj' hz' hg' x hxe hxz
      obtain ⟨hzq, hce⟩ := hkey e z hadj' hz' hg'
      have hse : s e = s v := bool3 _ _ _ (H.bip _ _ hadj') (H.bip _ _ (hZv z hz'))
      rw [hgval, Bool.and_eq_true]
      refine ⟨up hD (hLc c hc e hse hce) hxe, ?_⟩
      rw [← hzq]
      exact hxz
    rcases hu with hu | hu
    · rw [hu] at hz
      have hg2 : val C.gates (pairInput e2 e1) (n + g) = true := by
        refine mono' H.good _ _ ?_ _ hgx
        intro i hi
        simp only [pairInput, decide_eq_true_eq] at hi ⊢
        exact hi.symm
      exact main e2 e1 hadj.symm hz hg2 _ (pair_r _ _) (pair_l _ _)
    · rw [hu] at hz
      exact main e1 e2 hadj hz hgx _ (pair_l _ _) (pair_r _ _)

lemma x4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v) (c : ℕ) (q : Fin n)
    (hc : c < n + g) (hcv : val C.gates (eof v) c = true)
    (hNq : ∀ u : Fin n, val C.gates (eof u) c = true → s u = s v → G.Adj u q)
    (hZv : ∀ z : Fin n, (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true →
      graphFun G ∅ y = true) → G.Adj v z)
    (hkey : ∀ e1 z : Fin n, G.Adj e1 z →
      (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true → graphFun G ∅ y = true) →
      val C.gates (pairInput e1 z) (n + g) = true → z = q ∧ val C.gates (eof e1) c = true) :
    Res n G C :=
  x4core H c q hc hcv hNq hZv hkey (f4 C s v g c q.val) (if_pos rfl)
    (fun j hjg a b hin => f4_spec C s v g c q.val j a b hjg hin)

/-! third construction: the two-sided operand gate is moved next to the gate -/

def rho (n b0 g v : ℕ) (w : ℕ) : ℕ :=
  if w < n + b0 then w else if w = n + b0 then v else if w < n + g then w - 1 else w

lemma rho_lo (n b0 g v w : ℕ) (h : w < n + b0) : rho n b0 g v w = w := by
  unfold rho
  rw [if_pos h]

lemma rho_b (n b0 g v : ℕ) : rho n b0 g v (n + b0) = v := by
  unfold rho
  rw [if_neg (by omega), if_pos rfl]

lemma rho_mid (n b0 g v k : ℕ) (h1 : b0 ≤ k) (h2 : k + 1 < g) :
    rho n b0 g v (n + (k + 1)) = n + k := by
  unfold rho
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  omega

lemma rho_hi (n b0 g v w : ℕ) (h : n + g ≤ w) (hb : b0 < g) : rho n b0 g v w = w := by
  unfold rho
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma rho_lt (n b0 g v w j : ℕ) (hv : v < n) (hw : w < n + j) : rho n b0 g v w < n + j := by
  unfold rho
  split_ifs <;> omega

lemma rho_lt1 (n b0 g v w j : ℕ) (hv : v < n) (hj : b0 ≤ j) (hjg : j + 1 ≤ g)
    (hw : w < n + (j + 1)) : rho n b0 g v w < n + j := by
  unfold rho
  split_ifs <;> omega

def ren (r : ℕ → ℕ) (gt : Gate) : Gate := ⟨gt.op, gt.inputs.map r⟩

def f3 (C : Circuit) (n b0 g v c m : ℕ) : ℕ → Gate :=
  fun j => if b0 ≤ j ∧ j + 1 < g then ren (rho n b0 g v) (gateAt C (j + 1))
    else if j + 1 = g then ⟨GateOp.and, [rho n b0 g v c, m]⟩
    else if j = g then ⟨GateOp.or, [v, n + g - 1]⟩
    else ren (rho n b0 g v) (gateAt C j)

lemma ren_unch {n : ℕ} (f : ℕ → Gate) (len o : ℕ) (hD : Good n ⟨mk f len, o⟩) (r : ℕ → ℕ)
    (gt : Gate) (k w : ℕ) (hk : k < len) (hfk : f k = ren r gt) (hw : r w = n + k) :
    ∀ a b, gt.inputs = [a, b] →
      (gt.op = GateOp.and → ∀ x : Fin n → Bool,
        val (mk f len) x (r w) = (val (mk f len) x (r a) && val (mk f len) x (r b))) ∧
      (gt.op = GateOp.or → ∀ x : Fin n → Bool,
        val (mk f len) x (r w) = (val (mk f len) x (r a) || val (mk f len) x (r b))) := by
  intro a b hin
  have h := mk_val f len o hD k hk (r a) (r b) (by rw [hfk]; simp [ren, hin])
  rw [hfk] at h
  rw [hw]
  exact h

lemma x3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v) (c d : ℕ) (m : Fin n)
    (hc : c < n + g) (hd : d < n + g)
    (hgv : ∀ y : Fin n → Bool, val C.gates y (n + g) = (val C.gates y c && val C.gates y d))
    (hlin : Lin n C c)
    (hdm : val C.gates (eof m) d = true) (hdv : val C.gates (eof v) d = true) (hsm : s m ≠ s v)
    (hNm : ∀ u : Fin n, val C.gates (eof u) c = true → G.Adj u m)
    (hkey : ∀ e1 z : Fin n, G.Adj e1 z →
      (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true → graphFun G ∅ y = true) →
      val C.gates (pairInput e1 z) (n + g) = true →
      e1 = v ∨ (z = m ∧ val C.gates (eof e1) c = true)) : Res n G C := by
  have hvl := v.isLt
  have hml := m.isLt
  have hgl := H.hg
  have hdn : n ≤ d := by
    by_contra h
    have h1 : d < n := by omega
    rw [val_lt _ _ _ h1] at hdm hdv
    simp only [eof, decide_eq_true_eq] at hdm hdv
    exact hsm (by rw [← hdm, ← hdv])
  obtain ⟨b0, rfl⟩ : ∃ b0, d = n + b0 := ⟨d - n, by omega⟩
  have hb0 : b0 < g := by omega
  have hcd : c ≠ n + b0 := by
    intro h
    rw [← h] at hdm
    exact absurd rfl (hNm m hdm).ne
  obtain ⟨k, hk⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  have hfa : ∀ j, b0 ≤ j → j + 1 < g →
      f3 C n b0 g v.val c m.val j = ren (rho n b0 g v.val) (gateAt C (j + 1)) := by
    intro j h1 h2
    unfold f3
    rw [if_pos ⟨h1, h2⟩]
  have hfb : f3 C n b0 g v.val c m.val k = ⟨GateOp.and, [rho n b0 g v.val c, m.val]⟩ := by
    unfold f3
    rw [if_neg (by omega), if_pos (by omega)]
  have hfc : f3 C n b0 g v.val c m.val g = ⟨GateOp.or, [v.val, n + g - 1]⟩ := by
    unfold f3
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hfd : ∀ j, (j < b0 ∨ g < j) →
      f3 C n b0 g v.val c m.val j = ren (rho n b0 g v.val) (gateAt C j) := by
    intro j h1
    unfold f3
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hD : Good n ⟨mk (f3 C n b0 g v.val c m.val) C.gates.length, rho n b0 g v.val C.output⟩ := by
    apply mk_good
    intro j hj
    by_cases h1 : b0 ≤ j ∧ j + 1 < g
    · rw [hfa j h1.1 h1.2]
      obtain ⟨a, b, hin, ha, hb, hop⟩ := two H.good (j + 1) (by omega)
      exact ⟨hop, _, _, by simp [ren, hin], rho_lt1 n b0 g v.val a j hvl h1.1 (by omega) ha,
        rho_lt1 n b0 g v.val b j hvl h1.1 (by omega) hb⟩
    · by_cases h2 : j = k
      · rw [h2, hfb]
        exact ⟨Or.inl rfl, _, _, rfl, rho_lt1 n b0 g v.val c k hvl (by omega) (by omega)
          (by omega), by omega⟩
      · by_cases h3 : j = g
        · rw [h3, hfc]
          exact ⟨Or.inr rfl, _, _, rfl, by omega, by omega⟩
        · rw [hfd j (by omega)]
          obtain ⟨a, b, hin, ha, hb, hop⟩ := two H.good j hj
          exact ⟨hop, _, _, by simp [ren, hin], rho_lt n b0 g v.val a j hvl ha,
            rho_lt n b0 g v.val b j hvl hb⟩
  have htv : ∀ x : Fin n → Bool, val (mk (f3 C n b0 g v.val c m.val) C.gates.length) x (n + k) =
      (val (mk (f3 C n b0 g v.val c m.val) C.gates.length) x (rho n b0 g v.val c) && x m) := by
    intro x
    have h := (mk_val _ C.gates.length _ hD k (by omega) _ _ (by rw [hfb])).1 (by rw [hfb]) x
    rw [h, val_lt _ _ _ m.isLt]
  have hgnew : ∀ x : Fin n → Bool,
      val (mk (f3 C n b0 g v.val c m.val) C.gates.length) x (n + g) =
      (x v || (val (mk (f3 C n b0 g v.val c m.val) C.gates.length) x (rho n b0 g v.val c)
        && x m)) := by
    intro x
    have h := (mk_val _ C.gates.length _ hD g H.hg _ _ (by rw [hfc])).2 (by rw [hfc]) x
    have e : n + g - 1 = n + k := by omega
    rw [h, val_lt _ _ _ v.isLt, e, htv]
  have hbad : Bad C s (n + b0) := ⟨v, m, fun h => hsm h.symm, hdv, hdm⟩
  obtain ⟨hfun, hsnd⟩ := FW H
    (fun w x => val (mk (f3 C n b0 g v.val c m.val) C.gates.length) x (rho n b0 g v.val w))
    (fun w hw x => by
      show val _ x (rho n b0 g v.val w) = _
      rw [rho_lo n b0 g v.val w (by omega)]
      exact val_lt _ _ _ hw)
    (fun x y hxy h => mono' hD x y hxy _ h)
    (by
      intro j hj hjg
      by_cases h1 : j < b0
      · left
        exact ren_unch _ _ _ hD _ (gateAt C j) j (n + j) hj (hfd j (Or.inl h1))
          (rho_lo n b0 g v.val _ (by omega))
      · by_cases h2 : j = b0
        · right
          rw [h2]
          refine ⟨hbad, v.val, by omega, ?_, ?_⟩
          · intro x
            show val _ x (rho n b0 g v.val (n + b0)) = val _ x (rho n b0 g v.val v.val)
            rw [rho_b, rho_lo n b0 g v.val v.val (by omega)]
          · intro x hx
            rw [val_lt _ _ _ v.isLt] at hx
            exact up H.good hdv hx
        · by_cases h3 : j < g
          · left
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            exact ren_unch _ _ _ hD _ (gateAt C (j' + 1)) j' (n + (j' + 1)) (by omega)
              (hfa j' (by omega) h3) (rho_mid n b0 g v.val j' (by omega) h3)
          · left
            exact ren_unch _ _ _ hD _ (gateAt C j) j (n + j) hj (hfd j (Or.inr (by omega)))
              (rho_hi n b0 g v.val _ (by omega) hb0))
    (by
      intro x ih hx
      have hx' : val (mk (f3 C n b0 g v.val c m.val) C.gates.length) x
          (rho n b0 g v.val (n + g)) = true := hx
      rw [rho_hi n b0 g v.val _ (le_refl _) hb0, hgnew, Bool.or_eq_true, Bool.and_eq_true] at hx'
      rcases hx' with hx' | ⟨h1, h2⟩
      · exact Or.inl (up H.good H.hv hx')
      · rcases ih c hc h1 with h3 | h3
        · left
          rw [hgv, h3, up H.good hdm h2]
          rfl
        · exact Or.inr h3)
    (by
      intro e1 e2 hadj u hu hz hpre hgx
      show val (mk (f3 C n b0 g v.val c m.val) C.gates.length) (pairInput e1 e2)
          (rho n b0 g v.val (n + g)) = true
      rw [rho_hi n b0 g v.val _ (le_refl _) hb0, hgnew, Bool.or_eq_true, Bool.and_eq_true]
      have main : ∀ e z : Fin n, G.Adj e z →
          (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true →
            graphFun G ∅ y = true) →
          val C.gates (pairInput e z) (n + g) = true → pairInput e1 e2 e = true →
          pairInput e1 e2 z = true →
          pairInput e1 e2 v = true ∨
            (val (mk (f3 C n b0 g v.val c m.val) C.gates.length) (pairInput e1 e2)
              (rho n b0 g v.val c) = true ∧ pairInput e1 e2 m = true) := by
        intro e z hadj' hz' hg' hxe hxz
        rcases hkey e z hadj' hz' hg' with h | ⟨hzm, hce⟩
        · left
          rw [← h]
          exact hxe
        · right
          refine ⟨?_, by rw [← hzm]; exact hxz⟩
          rcases hpre c hc (up H.good hce hxe) with h | ⟨u1, u2, hne, h1, h2⟩
          · exact h
          · exact absurd (bool3 _ _ _ (H.bip _ _ (hNm u1 h1)) (H.bip _ _ (hNm u2 h2))) hne
      rcases hu with hu | hu
      · rw [hu] at hz
        have hg2 : val C.gates (pairInput e2 e1) (n + g) = true := by
          refine mono' H.good _ _ ?_ _ hgx
          intro i hi
          simp only [pairInput, decide_eq_true_eq] at hi ⊢
          exact hi.symm
        exact main e2 e1 hadj.symm hz hg2 (pair_r _ _) (pair_l _ _)
      · rw [hu] at hz
        exact main e1 e2 hadj hz hgx (pair_l _ _) (pair_r _ _))
  refine ⟨⟨mk (f3 C n b0 g v.val c m.val) C.gates.length, rho n b0 g v.val C.output⟩, hD,
    by simp [mk_len], hfun, ?_⟩
  intro j hj hop x hx
  have hj' : j < C.gates.length := by simpa [mk_len] using hj
  rw [mk_gateAt _ _ _ j hj'] at hop
  have fin : ∀ w, w < n + C.gates.length → BW G C w → rho n b0 g v.val w = n + j →
      graphFun G ∅ x = true := by
    intro w hw hbw hrw
    have h1 : val (mk (f3 C n b0 g v.val c m.val) C.gates.length) x (rho n b0 g v.val w) = true := by
      rw [hrw]
      exact hx
    rcases hsnd w hw x h1 with h2 | h2
    · exact hbw x h2
    · exact h2
  by_cases h1 : b0 ≤ j ∧ j + 1 < g
  · rw [hfa j h1.1 h1.2] at hop
    exact fin (n + (j + 1)) (by omega) (H.clean (j + 1) (by omega) hop (by omega))
      (rho_mid n b0 g v.val j h1.1 h1.2)
  · by_cases h2 : j = k
    · rw [h2] at hx
      have hx' := hx
      rw [htv, Bool.and_eq_true] at hx'
      rcases hsnd c (by omega) x hx'.1 with h3 | h3
      · obtain ⟨u, hxu, hu⟩ := hlin x h3
        exact (F_iff G x).2 ⟨u, m, hNm u hu, hxu, hx'.2⟩
      · exact h3
    · by_cases h3 : j = g
      · rw [h3, hfc] at hop
        exact absurd hop (by simp)
      · rw [hfd j (by omega)] at hop
        by_cases h4 : j < b0
        · exact fin (n + j) (by omega) (H.clean j hj' hop h3) (rho_lo n b0 g v.val _ (by omega))
        · exact fin (n + j) (by omega) (H.clean j hj' hop h3)
            (rho_hi n b0 g v.val _ (by omega) hb0)

/-! assembling -/

lemma four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : NoFourCycle G) :
    ∀ a b w1 w2 : Fin n, a ≠ b → G.Adj a w1 → G.Adj b w1 → G.Adj a w2 → G.Adj b w2 →
      w1 = w2 := by
  intro a b w1 w2 hab h1 h2 h3 h4
  have hc := h a b hab
  rw [Finset.card_le_one] at hc
  exact hc w1 (by simp [h1, h2]) w2 (by simp [h3, h4])

lemma core {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {s : Fin n → Bool} {g : ℕ} {v : Fin n} (H : Hyp G C s g v)
    (h4 : ∀ a b w1 w2 : Fin n, a ≠ b → G.Adj a w1 → G.Adj b w1 → G.Adj a w2 → G.Adj b w2 →
      w1 = w2) : Res n G C := by
  obtain ⟨a, b, hin, ha, hb, _⟩ := two H.good g H.hg
  have hgl := H.hg
  have hvand := fun y : Fin n → Bool => val_and (C := C) y g H.hg a b hin ha hb H.hgop
  have hla : Lin n C a := by
    rcases struct H a (by omega) with h | h | h
    · exact absurd h (H.h7 g H.hg H.hgop a (by simp [hin]))
    · exact h
    · have := h.1
      omega
  have hlb : Lin n C b := by
    rcases struct H b (by omega) with h | h | h
    · exact absurd h (H.h7 g H.hg H.hgop b (by simp [hin]))
    · exact h
    · have := h.1
      omega
  have hv' := H.hv
  rw [hvand, Bool.and_eq_true] at hv'
  have hstar : ∀ a' b' z : Fin n, val C.gates (eof a') a = true → val C.gates (eof b') b = true →
      (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true → graphFun G ∅ y = true) →
      G.Adj a' b' ∨ G.Adj a' z ∨ G.Adj b' z := by
    intro a' b' z h1 h2 hz
    have hF := hz (fun w => decide (w = a' ∨ w = b' ∨ w = z))
      (by rw [hvand, up H.good h1 (by simp), up H.good h2 (by simp)]; rfl) (by simp)
    rw [F_iff] at hF
    obtain ⟨p, q, hpq, hp, hq⟩ := hF
    simp only [decide_eq_true_eq] at hp hq
    rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;> rw [hp, hq] at hpq
    · exact absurd rfl hpq.ne
    · exact Or.inl hpq
    · exact Or.inr (Or.inl hpq)
    · exact Or.inl hpq.symm
    · exact absurd rfl hpq.ne
    · exact Or.inr (Or.inr hpq)
    · exact Or.inr (Or.inl hpq.symm)
    · exact Or.inr (Or.inr hpq.symm)
    · exact absurd rfl hpq.ne
  have hZv : ∀ z : Fin n, (∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true →
      graphFun G ∅ y = true) → G.Adj v z := by
    intro z hz
    rcases hstar v v z hv'.1 hv'.2 hz with h | h | h
    · exact absurd rfl h.ne
    · exact h
    · exact h
  have hgp : ∀ e1 e2 : Fin n, val C.gates (pairInput e1 e2) (n + g) = true →
      (val C.gates (eof e1) a = true ∨ val C.gates (eof e2) a = true) ∧
      (val C.gates (eof e1) b = true ∨ val C.gates (eof e2) b = true) := by
    intro e1 e2 h
    rw [hvand, Bool.and_eq_true] at h
    obtain ⟨u, hu, hu2⟩ := hla _ h.1
    obtain ⟨u', hu', hu2'⟩ := hlb _ h.2
    simp only [pairInput, decide_eq_true_eq] at hu hu'
    constructor
    · rcases hu with hu | hu
      · rw [hu] at hu2; exact Or.inl hu2
      · rw [hu] at hu2; exact Or.inr hu2
    · rcases hu' with hu' | hu'
      · rw [hu'] at hu2'; exact Or.inl hu2'
      · rw [hu'] at hu2'; exact Or.inr hu2'
  rcases comb G s H.bip h4 v (fun u => val C.gates (eof u) a = true)
      (fun u => val C.gates (eof u) b = true)
      (fun z => ∀ y : Fin n → Bool, val C.gates y (n + g) = true → y z = true →
        graphFun G ∅ y = true)
      hstar hZv with hK | ⟨q, hK | hK⟩ | ⟨m, hK | hK⟩
  · apply x1 H
    intro e1 e2 hadj u hu hz hgx
    have hg2 := hgp e1 e2 hgx
    rcases hu with hu | hu
    · rw [hu] at hz
      right
      exact hK e2 e1 hadj.symm hz ⟨hg2.1.symm, hg2.2.symm⟩
    · rw [hu] at hz
      left
      exact hK e1 e2 hadj hz hg2
  · exact x4 H a q ha hv'.1 hK.1 hZv
      (fun e1 z hadj hz hgx => hK.2 e1 z hadj hz (hgp e1 z hgx))
  · exact x4 H b q hb hv'.2 hK.1 hZv
      (fun e1 z hadj hz hgx => hK.2 e1 z hadj hz (hgp e1 z hgx))
  · obtain ⟨hBm, hsm, hN, hK'⟩ := hK
    exact x3 H a b m ha hb hvand hla hBm hv'.2 hsm hN
      (fun e1 z hadj hz hgx => hK' e1 z hadj hz (hgp e1 z hgx).1)
  · obtain ⟨hAm, hsm, hN, hK'⟩ := hK
    exact x3 H b a m hb ha (fun y => by rw [hvand, Bool.and_comm]) hlb hAm hv'.1 hsm hN
      (fun e1 z hadj hz hgx => hK' e1 z hadj hz (hgp e1 z hgx).2)

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
  (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
  g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) →
  (∃ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput v) = true) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
    PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF G D k := by
  intro n G _ C s g hbip h4 hAO hF hLift h7 hOC hg hgop _ hclean hex
  obtain ⟨v, hv⟩ := hex
  have hG : Good n C := ⟨fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩, hAO.2.1⟩
  have hfn : ∀ x : Fin n → Bool, val C.gates x C.output = graphFun G ∅ x :=
    fun x => congrFun hF x
  have fin : Res n G C → ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
      circuitFun n D = graphFun G ∅ ∧
      ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
    rintro ⟨D, hD, hlen, hfun, hcl⟩
    exact ⟨D, ⟨fun g hg => (hD.ao g hg).1, hD.rb, fun g hg => (hD.ao g hg).2⟩, hlen,
      funext hfun, fun k hk hop => hcl k hk hop⟩
  apply fin
  by_cases ho : C.output < n + C.gates.length
  · have hL' : ∀ h < C.gates.length, (gateAt C h).op = GateOp.or → ¬ BW G C (n + h) →
        ∀ t ∈ (gateAt C h).inputs, ¬ BW G C t := by
      intro h hh hop hnb t ht hbt
      apply hLift
      obtain ⟨a, b, hin, ha, hb, _⟩ := two hG h hh
      rw [hin] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · refine ⟨h, hh, 0, hOC h hh, hop, hnb, ?_⟩
        have e0 : opnd C h 0 = t := by simp [opnd, hin]
        rw [e0]
        exact ⟨hbt, fun _ => true, ones hG t (by omega)⟩
      · refine ⟨h, hh, 1, hOC h hh, hop, hnb, ?_⟩
        have e0 : opnd C h 1 = t := by simp [opnd, hin]
        rw [e0]
        exact ⟨hbt, fun _ => true, ones hG t (by omega)⟩
    exact core ⟨hG, hbip, hfn, fun k hk hop t ht => h7 k hk hop t ht, hL', hg, hgop,
      fun k hk hop hkg => hclean k hk hop hkg, hv, ho⟩ (four G h4)
  · refine ⟨⟨[], n⟩, ⟨fun g hg => by simp at hg, fun j hj => by simp at hj⟩, Nat.zero_le _, ?_,
      fun k hk => by simp at hk⟩
    intro x
    show val ([] : List Gate) x n = graphFun G ∅ x
    rw [← hfn x, val_ge C.gates x C.output (by omega)]
    exact val_ge _ _ _ (by simp)

end PEqualNP.Outside.L_meta_3653_aux

theorem PEqualNP.Outside.L_meta_3653 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
  (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
  g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) →
  (∃ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput v) = true) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
    PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF G D k := by
  intro n G _ C s g
  exact PEqualNP.Outside.L_meta_3653_aux.main n G C s g
