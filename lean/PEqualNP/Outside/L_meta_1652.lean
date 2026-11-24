import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma fin2_sub : ∀ b : Fin 2, (b = 0 ∧ 1 - b = 1) ∨ (b = 1 ∧ 1 - b = 0) := by decide

lemma fin2_ne : ∀ b c : Fin 2, c ≠ b → c = 1 - b := by decide

lemma fin2_ne' : ∀ b c : Fin 2, c ≠ b → 1 - c = b := by decide

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)

def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and

lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega

lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]

lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih

lemma opnd_lt (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) : ∀ b : Fin 2, o b < n + a := by
  obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a ha
  rw [hin] at hab
  simp only [List.cons.injEq, and_true] at hab
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega

lemma top_true (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (x : Fin n → Bool)
    (h : ∀ b : Fin 2, W n C x (o b) = true) : W n C x (n + a) = true := by
  have hlt := opnd_lt n C hA a ha o hin
  rw [W_and n C x a ha hop (o 0) (o 1) hin (hlt 0) (hlt 1), h 0, h 1]
  rfl

open PEqualNP.EdgeOwnership in
lemma sem_adj (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (u v : Fin n)
    (hu : OrR n C (o 0) u.val) (hv : OrR n C (o 1) v.val) :
    W n C (pairInput u v) (n + a) = true := by
  apply top_true n C hA a ha hop o hin
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · refine orR_mono n C hA _ _ _ hu ?_
    rw [W_input n C _ u.val u.isLt]; simp [pairInput]
  · refine orR_mono n C hA _ _ _ hv ?_
    rw [W_input n C _ v.val v.isLt]; simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
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

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma mem_filter' {α : Type*} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w, (w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
  · simp [orStep, List.getD_eq_getElem?_getD, hop]

lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

lemma orReaches_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : ∀ x, x ∈ (orSets n C).getD k [] ↔ x = k ∨ (gk.op = GateOp.or ∧
      ∃ w, (w ∈ gk.inputs ∧ n ≤ w ∧ w < n + k) ∧
        x ∈ (pre.foldl (orStep n) []).getD (w - n) []) := by
    intro x
    rw [hc, orFold_getD_lt n post _ k (by omega)]
    have h := orStep_mem_last n (pre.foldl (orStep n) []) gk x
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have e : n + k - n = k := by omega
  unfold OrReaches
  rw [e, h1 g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, ⟨hw, hn, hlt⟩, h⟩⟩
    · exact Or.inl h
    · right
      refine ⟨hop, w, hw, hn, hlt, hn, ?_⟩
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro (h | ⟨hop, w, hw, hn, hlt, _, h⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨hop, w, ⟨hw, hn, hlt⟩, ?_⟩⟩
      rw [← h2 (w - n) (by omega)]
      exact h

lemma orReaches_orR (n : ℕ) (C : Circuit) :
    ∀ w, w < n + C.gates.length → ∀ g, OrReaches n C w g → OrR n C w (n + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw g hr
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (orReaches_iff n C g k hk).mp hr with h | ⟨hop, c, hc, hcn, hclt, hcr⟩
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hc⟩ (ih c hclt (by omega) g hcr)

lemma orR_orReaches (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ) (hg : g < C.gates.length) :
    ∀ w, w < n + C.gates.length → OrR n C w (n + g) → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hr
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨k, hk1, hk, hop, hc⟩, hcr⟩
    · rw [h]
      exact (orReaches_iff n C g g hg).mpr (Or.inl rfl)
    · subst hk1
      have hle := orR_le n C hA _ _ hcr
      have hclt : c < n + k := by
        obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
        rw [hab] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      exact (orReaches_iff n C g k hk).mpr
        (Or.inr ⟨hop, c, hc, by omega, hclt, ih c hclt (by omega) hcr⟩)

lemma mem_orIn (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n + C.gates.length)
    (u : Fin n) : u ∈ orIn n C w ↔ OrR n C w u.val := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hu⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail (orReaches_orR n C w hw k hr) ⟨k, rfl, hk, hop, hu⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hc, ⟨k, rfl, hk, hop, hu⟩⟩
    · left
      exact h1
    · right
      exact ⟨k, hk, orR_orReaches n C hA k hk w hw hc, hop, hu⟩

lemma ao_of (n : ℕ) (C : Circuit) (h : IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hlen _ hmem)
  exact ⟨hao _ hmem, a, b, hab, hrb k hk a (by rw [hab]; simp), hrb k hk b (by rw [hab]; simp)⟩

lemma opnd_eq (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length) :
    (gateAt C a).inputs = [opnd C a 0, opnd C a 1] := by
  obtain ⟨_, p, q, hpq, _, _⟩ := hA a ha
  simp [opnd, hpq]

lemma orR_input (n : ℕ) (C : Circuit) (u v : ℕ) (hu : u < n) (h : OrR n C u v) : v = u := by
  rcases Relation.ReflTransGen.cases_head h with h1 | ⟨c, ⟨k, hk1, _⟩, _⟩
  · exact h1.symm
  · omega

lemma orIn_input (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n) :
    (orIn n C w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have h1 := orR_input n C w a.val hw ((mem_orIn n C hA w (by omega) a).mp ha)
  have h2 := orR_input n C w b.val hw ((mem_orIn n C hA w (by omega) b).mp hb)
  exact Fin.ext (by omega)

lemma orIn_andGate (n : ℕ) (C : Circuit) (hA : AO n C) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) : orIn n C (n + k) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro u hu
  have h := (mem_orIn n C hA (n + k) (by omega) u).mp hu
  rcases Relation.ReflTransGen.cases_head h with h1 | ⟨c, ⟨k', hk1, _, hop', _⟩, _⟩
  · have := u.isLt
    omega
  · have hkk : k' = k := by omega
    rw [hkk, hop] at hop'
    cases hop'

lemma orIn_orGate (n : ℕ) (C : Circuit) (hA : AO n C) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) :
    orIn n C (n + k) = orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1) := by
  have hin := opnd_eq n C hA k hk
  have hlt := opnd_lt n C hA k hk (opnd C k) hin
  have hlt0 := hlt 0
  have hlt1 := hlt 1
  ext u
  rw [Finset.mem_union, mem_orIn n C hA (n + k) (by omega) u,
    mem_orIn n C hA (opnd C k 0) (by omega) u, mem_orIn n C hA (opnd C k 1) (by omega) u]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h1 | ⟨c, ⟨k', hk1, _, _, hc⟩, hcr⟩
    · have := u.isLt
      omega
    · have hkk : k' = k := by omega
      rw [hkk, hin] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · rw [hc] at hcr
        exact Or.inl hcr
      · rw [hc] at hcr
        exact Or.inr hcr
  · rintro (h | h)
    · exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ h
    · exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ h

def Br (n : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ (orIn n C (opnd C k 0)).Nonempty ∧
    (orIn n C (opnd C k 1)).Nonempty

lemma orIn_sub (n : ℕ) (C : Circuit) (hA : AO n C) (w v : ℕ) (hw : w < n + C.gates.length)
    (h : OrR n C w v) : orIn n C v ⊆ orIn n C w := by
  intro u hu
  have hle := orR_le n C hA _ _ h
  rw [mem_orIn n C hA w hw u]
  exact Relation.ReflTransGen.trans h ((mem_orIn n C hA v (by omega) u).mp hu)

lemma count (n : ℕ) (C : Circuit) (hA : AO n C) :
    ∀ N : ℕ, ∀ (Ws Z : Finset ℕ), (∀ w ∈ Ws, w < N ∧ w < n + C.gates.length) →
      (∀ k, Br n C k → (∃ w ∈ Ws, OrR n C w (n + k)) → k ∈ Z) →
      (Ws.biUnion fun w => orIn n C w).card ≤ Ws.card + Z.card := by
  intro N
  induction N with
  | zero =>
    intro Ws Z hW _
    have hE : Ws = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by
      have := (hW w hw).1
      omega
    subst hE
    simp
  | succ N ih =>
    intro Ws Z hW hZ
    by_cases hN : N ∈ Ws
    · have hNlen := (hW N hN).2
      have hW0 : ∀ w ∈ Ws.erase N, w < N ∧ w < n + C.gates.length := by
        intro w hw
        have h1 := Finset.mem_erase.mp hw
        have h2 := hW w h1.2
        have h3 := h1.1
        exact ⟨by omega, h2.2⟩
      have hZ0 : ∀ k, Br n C k → (∃ w ∈ Ws.erase N, OrR n C w (n + k)) → k ∈ Z := by
        rintro k hk ⟨w, hw, hr⟩
        exact hZ k hk ⟨w, (Finset.mem_erase.mp hw).2, hr⟩
      have hcard : (Ws.erase N).card + 1 = Ws.card := Finset.card_erase_add_one hN
      have hsplit : (Ws.biUnion fun w => orIn n C w) =
          orIn n C N ∪ ((Ws.erase N).biUnion fun w => orIn n C w) := by
        conv_lhs => rw [← Finset.insert_erase hN]
        rw [Finset.biUnion_insert]
      by_cases hn : N < n
      · have h1 := orIn_input n C hA N hn
        have h2 := ih (Ws.erase N) Z hW0 hZ0
        rw [hsplit]
        have h3 := Finset.card_union_le (orIn n C N) ((Ws.erase N).biUnion fun w => orIn n C w)
        omega
      · obtain ⟨k, hNk⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · have hor := orIn_orGate n C hA k hk hop
          have hin := opnd_eq n C hA k hk
          have hlt := opnd_lt n C hA k hk (opnd C k) hin
          by_cases hbr : Br n C k
          · have hkZ : k ∈ Z := hZ k hbr ⟨N, hN, by rw [hNk]; exact Relation.ReflTransGen.refl⟩
            have hW' : ∀ w ∈ insert (opnd C k 0) (insert (opnd C k 1) (Ws.erase N)),
                w < N ∧ w < n + C.gates.length := by
              intro w hw
              rcases Finset.mem_insert.mp hw with hw | hw
              · have := hlt 0
                rw [hw]
                exact ⟨by omega, by omega⟩
              rcases Finset.mem_insert.mp hw with hw | hw
              · have := hlt 1
                rw [hw]
                exact ⟨by omega, by omega⟩
              · exact hW0 w hw
            have hZ' : ∀ k', Br n C k' →
                (∃ w ∈ insert (opnd C k 0) (insert (opnd C k 1) (Ws.erase N)),
                  OrR n C w (n + k')) → k' ∈ Z.erase k := by
              rintro k' hk' ⟨w, hw, hr⟩
              have hle := orR_le n C hA _ _ hr
              have hwlt := (hW' w hw).1
              refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
              rcases Finset.mem_insert.mp hw with hw | hw
              · rw [hw] at hr
                refine hZ k' hk' ⟨N, hN, ?_⟩
                rw [hNk]
                exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ hr
              rcases Finset.mem_insert.mp hw with hw | hw
              · rw [hw] at hr
                refine hZ k' hk' ⟨N, hN, ?_⟩
                rw [hNk]
                exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ hr
              · exact hZ k' hk' ⟨w, (Finset.mem_erase.mp hw).2, hr⟩
            have h2 := ih _ (Z.erase k) hW' hZ'
            have heq : (Ws.biUnion fun w => orIn n C w) =
                ((insert (opnd C k 0) (insert (opnd C k 1) (Ws.erase N))).biUnion
                  fun w => orIn n C w) := by
              rw [hsplit, Finset.biUnion_insert, Finset.biUnion_insert, hNk, hor,
                Finset.union_assoc]
            have h4 : (insert (opnd C k 0) (insert (opnd C k 1) (Ws.erase N))).card ≤
                (Ws.erase N).card + 2 := by
              have a1 := Finset.card_insert_le (opnd C k 0) (insert (opnd C k 1) (Ws.erase N))
              have a2 := Finset.card_insert_le (opnd C k 1) (Ws.erase N)
              omega
            have h5 : (Z.erase k).card + 1 = Z.card := Finset.card_erase_add_one hkZ
            rw [heq]
            omega
          · have hne : orIn n C (opnd C k 0) = ∅ ∨ orIn n C (opnd C k 1) = ∅ := by
              by_cases h0 : orIn n C (opnd C k 0) = ∅
              · exact Or.inl h0
              · by_cases h1 : orIn n C (opnd C k 1) = ∅
                · exact Or.inr h1
                · exact absurd ⟨hk, hop, Finset.nonempty_iff_ne_empty.mpr h0,
                    Finset.nonempty_iff_ne_empty.mpr h1⟩ hbr
            obtain ⟨b, hb⟩ : ∃ b : Fin 2, orIn n C (n + k) = orIn n C (opnd C k b) := by
              rcases hne with h | h
              · exact ⟨1, by rw [hor, h, Finset.empty_union]⟩
              · exact ⟨0, by rw [hor, h, Finset.union_empty]⟩
            have hmemb : opnd C k b ∈ (gateAt C k).inputs := by
              rw [hin]
              rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> simp
            have hW' : ∀ w ∈ insert (opnd C k b) (Ws.erase N),
                w < N ∧ w < n + C.gates.length := by
              intro w hw
              rcases Finset.mem_insert.mp hw with hw | hw
              · have := hlt b
                rw [hw]
                exact ⟨by omega, by omega⟩
              · exact hW0 w hw
            have hZ' : ∀ k', Br n C k' →
                (∃ w ∈ insert (opnd C k b) (Ws.erase N), OrR n C w (n + k')) → k' ∈ Z := by
              rintro k' hk' ⟨w, hw, hr⟩
              rcases Finset.mem_insert.mp hw with hw | hw
              · rw [hw] at hr
                refine hZ k' hk' ⟨N, hN, ?_⟩
                rw [hNk]
                exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hmemb⟩ hr
              · exact hZ k' hk' ⟨w, (Finset.mem_erase.mp hw).2, hr⟩
            have h2 := ih _ Z hW' hZ'
            have heq : (Ws.biUnion fun w => orIn n C w) =
                ((insert (opnd C k b) (Ws.erase N)).biUnion fun w => orIn n C w) := by
              rw [hsplit, Finset.biUnion_insert, hNk, hb]
            have h4 := Finset.card_insert_le (opnd C k b) (Ws.erase N)
            rw [heq]
            omega
        · have hand : (gateAt C k).op = GateOp.and := by
            rcases (hA k hk).1 with h | h
            · exact h
            · exact absurd h hop
          have h1 : orIn n C N = ∅ := by
            rw [hNk]
            exact orIn_andGate n C hA k hk hand
          have h2 := ih (Ws.erase N) Z hW0 hZ0
          rw [hsplit, h1, Finset.empty_union]
          omega
    · have hW0 : ∀ w ∈ Ws, w < N ∧ w < n + C.gates.length := by
        intro w hw
        have h2 := hW w hw
        have h3 : w ≠ N := fun h => hN (h ▸ hw)
        exact ⟨by omega, h2.2⟩
      exact ih Ws Z hW0 hZ

lemma dom (n : ℕ) (C : Circuit) (hA : AO n C) :
    ∀ w, w < n + C.gates.length → ∀ k, Br n C k → OrR n C w (n + k) →
      ∃ k1, Br n C k1 ∧ OrR n C w (n + k1) ∧ orIn n C (n + k1) = orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw k hbk hr
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨j, hj1, hj, hop, hc⟩, hcr⟩
    · exact ⟨k, hbk, hr, by rw [h]⟩
    · by_cases hbj : Br n C j
      · refine ⟨j, hbj, ?_, by rw [hj1]⟩
        rw [hj1]
        exact Relation.ReflTransGen.refl
      · have hin := opnd_eq n C hA j hj
        have hor := orIn_orGate n C hA j hj hop
        have hstep : OrStep n C w c := ⟨j, hj1, hj, hop, hc⟩
        have hclt : c < w := orStep_lt n C hA _ _ hstep
        have hkne : (orIn n C (n + k)).Nonempty := by
          obtain ⟨u, hu⟩ := hbk.2.2.1
          rw [orIn_orGate n C hA k hbk.1 hbk.2.1]
          exact ⟨u, Finset.mem_union_left _ hu⟩
        have hcne : (orIn n C c).Nonempty :=
          hkne.mono (orIn_sub n C hA c (n + k) (by omega) hcr)
        have hceq : orIn n C w = orIn n C c := by
          rw [hin] at hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with hc | hc
          · have h1 : orIn n C (opnd C j 1) = ∅ := by
              by_contra hcon
              exact hbj ⟨hj, hop, by rw [← hc]; exact hcne,
                Finset.nonempty_iff_ne_empty.mpr hcon⟩
            rw [hj1, hor, h1, Finset.union_empty, hc]
          · have h0 : orIn n C (opnd C j 0) = ∅ := by
              by_contra hcon
              exact hbj ⟨hj, hop, Finset.nonempty_iff_ne_empty.mpr hcon,
                by rw [← hc]; exact hcne⟩
            rw [hj1, hor, h0, Finset.empty_union, hc]
        obtain ⟨k1, hb1, hr1, he1⟩ := ih c hclt (by omega) k hbk hcr
        exact ⟨k1, hb1, Relation.ReflTransGen.head hstep hr1, he1.trans hceq.symm⟩

lemma br_notBelow {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hA : AO n C) (k : ℕ) (hb : Br n C k) : ¬ BelowF G C k := by
  intro hbel
  obtain ⟨hk, hop, ⟨u, hu⟩, _⟩ := hb
  have hin := opnd_eq n C hA k hk
  have hlt := opnd_lt n C hA k hk (opnd C k) hin
  have hlt0 := hlt 0
  have h1 := (mem_orIn n C hA (opnd C k 0) (by omega) u).mp hu
  have h2 : OrR n C (n + k) u.val :=
    Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ h1
  have h3 : W n C (pairInput u u) (n + k) = true := by
    refine orR_mono n C hA _ _ _ h2 ?_
    rw [W_input n C _ u.val u.isLt]
    simp [pairInput]
  have h4 := hbel (pairInput u u) h3
  exact G.irrefl ((graphFun_pair G u u).mp h4)

theorem final : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ∀ (c : Fin n) (T M : Finset ℕ) (L : Finset (Fin n)), (∀ t, t ∈ T ↔ t ∈ PEqualNP.TopForm.tops G C ∧ ∃ p : Fin 2, PEqualNP.TopForm.side (n := n) C t (1 - p) = {c}) → (∀ h, h ∈ M ↔ h ∈ PEqualNP.TopForm.lam G C ∧ ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, PEqualNP.TopForm.side (n := n) C a (1 - b) = {c} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h) → (∀ v, v ∈ L ↔ ∃ d ∈ PEqualNP.TopForm.tops G C, ∃ q : Fin 2, PEqualNP.TopForm.side (n := n) C d (1 - q) = {c} ∧ v ∈ PEqualNP.TopForm.side (n := n) C d q) → ∀ (Bc : Finset (Finset (Fin n))), (∀ X ∈ Bc, ∃ k ∈ M, PEqualNP.TopForm.orIn n C (n + k) = X) → (∀ w ∈ L, G.Adj c w ∧ s(c, w) ∈ PEqualNP.TopForm.starEdges G C) ∧ L.card ≤ T.card + M.card ∧ (Bc.Nonempty → Bc.card + 1 ≤ T.card + M.card) ∧ (Bc.Nonempty → (∀ X' ∈ Bc, ∃ X'' ∈ Bc, ¬ X'' ⊆ X') → Bc.card + 2 ≤ T.card + M.card) := by
  intro n G inst C _ _ hLeast _ c T M L hT hM hL Bc hBc
  have hA : AO n C := ao_of n C hLeast.1
  have htop : ∀ d, d ∈ tops G C →
      d < C.gates.length ∧ (gateAt C d).op = GateOp.and ∧ BelowF G C d := by
    intro d hd
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at hd
    exact ⟨hd.1, hd.2.1, hd.2.2⟩
  have hoplt : ∀ d, d ∈ tops G C → ∀ b : Fin 2, opnd C d b < n + C.gates.length := by
    intro d hd b
    have h1 := (htop d hd).1
    have := opnd_lt n C hA d h1 (opnd C d) (opnd_eq n C hA d h1) b
    omega
  have hadj : ∀ d, d ∈ tops G C → ∀ u v : Fin n, u ∈ orIn n C (opnd C d 0) →
      v ∈ orIn n C (opnd C d 1) → G.Adj u v := by
    intro d hd u v hu hv
    obtain ⟨hdl, hdop, hdb⟩ := htop d hd
    have h1 := (mem_orIn n C hA _ (hoplt d hd 0) u).mp hu
    have h2 := (mem_orIn n C hA _ (hoplt d hd 1) v).mp hv
    have h3 := sem_adj n C hA d hdl hdop (opnd C d) (opnd_eq n C hA d hdl) u v h1 h2
    exact (graphFun_pair G u v).mp (hdb _ h3)
  have hadj2 : ∀ d, d ∈ tops G C → ∀ (q : Fin 2) (u v : Fin n),
      u ∈ orIn n C (opnd C d (1 - q)) → v ∈ orIn n C (opnd C d q) → G.Adj u v := by
    intro d hd q u v hu hv
    rcases fin2_sub q with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [h'] at hu
      rw [h] at hv
      exact (hadj d hd v u hv hu).symm
    · rw [h'] at hu
      rw [h] at hv
      exact hadj d hd u v hu hv
  have h1 : ∀ w ∈ L, G.Adj c w ∧ s(c, w) ∈ starEdges G C := by
    intro w hw
    obtain ⟨d, hd, q, hq1, hq2⟩ := (hL w).mp hw
    have hc0 : c ∈ side (n := n) C d (1 - q) := by
      rw [hq1]
      exact Finset.mem_singleton_self c
    have hc : c ∈ orIn n C (opnd C d (1 - q)) := hc0
    have hw2 : w ∈ orIn n C (opnd C d q) := hq2
    refine ⟨hadj2 d hd q c w hc hw2, ?_⟩
    unfold PEqualNP.TopForm.starEdges
    refine Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩
    rcases fin2_sub q with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [h'] at hc
      rw [h] at hw2
      exact Finset.mem_image.mpr ⟨(w, c), Finset.mem_product.mpr ⟨hw2, hc⟩, Sym2.eq_swap⟩
    · rw [h'] at hc
      rw [h] at hw2
      exact Finset.mem_image.mpr ⟨(c, w), Finset.mem_product.mpr ⟨hc, hw2⟩, rfl⟩
  have hchoice : ∀ t, ∃ p : Fin 2, t ∈ T → side (n := n) C t (1 - p) = {c} := by
    intro t
    by_cases ht : t ∈ T
    · obtain ⟨p, hp⟩ := ((hT t).mp ht).2
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose pf hpf using hchoice
  have hTtop : ∀ t ∈ T, t ∈ tops G C := fun t ht => ((hT t).mp ht).1
  have hMmem : ∀ k, Br n C k → ∀ a ∈ tops G C, ∀ b : Fin 2,
      side (n := n) C a (1 - b) = {c} → OrR n C (opnd C a b) (n + k) → k ∈ M := by
    intro k hbk a ha b hab hr
    have hreach : OrReaches n C (opnd C a b) k :=
      orR_orReaches n C hA k hbk.1 _ (hoplt a ha b) hr
    refine (hM k).mpr ⟨?_, a, ha, b, hab, hreach⟩
    have horN : k ∈ orN G C := by
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hbk.1, hbk.2.1, br_notBelow G C hA k hbk⟩
    unfold PEqualNP.TopForm.lam
    refine (mem_filter' _ _ _ _).mpr ⟨horN, hbk.2.2.1, hbk.2.2.2, a, ha, b, ?_, hreach⟩
    rw [hab]
    exact Finset.card_singleton c
  have hMbr : ∀ k ∈ M, Br n C k ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      side (n := n) C a (1 - b) = {c} ∧ OrR n C (opnd C a b) (n + k) := by
    intro k hk
    obtain ⟨hlam, a, ha, b, hab, hreach⟩ := (hM k).mp hk
    unfold PEqualNP.TopForm.lam at hlam
    obtain ⟨horN, hne0, hne1, -⟩ := (mem_filter' _ _ _ _).mp hlam
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at horN
    exact ⟨⟨horN.1, horN.2.1, hne0, hne1⟩, a, ha, b, hab,
      orReaches_orR n C _ (hoplt a ha b) k hreach⟩
  have h2 : L.card ≤ T.card + M.card := by
    have hWs : ∀ w ∈ T.image (fun t => opnd C t (pf t)),
        w < n + C.gates.length ∧ w < n + C.gates.length := by
      intro w hw
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨hoplt t (hTtop t ht) _, hoplt t (hTtop t ht) _⟩
    have hZ : ∀ k, Br n C k →
        (∃ w ∈ T.image (fun t => opnd C t (pf t)), OrR n C w (n + k)) → k ∈ M := by
      rintro k hbk ⟨w, hw, hr⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
      exact hMmem k hbk t (hTtop t ht) (pf t) (hpf t ht) hr
    have hcount := count n C hA (n + C.gates.length) _ M hWs hZ
    have hsub : L ⊆ (T.image (fun t => opnd C t (pf t))).biUnion fun w => orIn n C w := by
      intro v hv
      obtain ⟨d, hd, q, hq1, hq2⟩ := (hL v).mp hv
      have hdT : d ∈ T := (hT d).mpr ⟨hd, q, hq1⟩
      refine Finset.mem_biUnion.mpr ⟨opnd C d (pf d), Finset.mem_image.mpr ⟨d, hdT, rfl⟩, ?_⟩
      by_cases hqp : q = pf d
      · rw [← hqp]
        exact hq2
      · have e1 : 1 - q = pf d := fin2_ne' (pf d) q hqp
        have e2 : q = 1 - pf d := fin2_ne (pf d) q hqp
        have hs1 := hpf d hdT
        rw [e1] at hq1
        rw [e2, hs1] at hq2
        have hvc := Finset.mem_singleton.mp hq2
        rw [hvc]
        show c ∈ side (n := n) C d (pf d)
        rw [hq1]
        exact Finset.mem_singleton_self c
    have h3 := Finset.card_le_card hsub
    have h4 : (T.image (fun t => opnd C t (pf t))).card ≤ T.card := Finset.card_image_le
    omega
  have hBcM : ∀ S : Finset ℕ, (∀ X ∈ Bc, ∃ k ∈ S, orIn n C (n + k) = X) →
      Bc.card ≤ S.card := by
    intro S hS
    have hsub : Bc ⊆ S.image (fun k => orIn n C (n + k)) := by
      intro X hX
      obtain ⟨k, hk, hkX⟩ := hS X hX
      exact Finset.mem_image.mpr ⟨k, hk, hkX⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hTne : Bc.Nonempty → T.Nonempty ∧ M.Nonempty := by
    rintro ⟨X, hX⟩
    obtain ⟨k, hk, -⟩ := hBc X hX
    obtain ⟨-, a, ha, b, hab, -⟩ := (hM k).mp hk
    exact ⟨⟨a, (hT a).mpr ⟨ha, b, hab⟩⟩, ⟨k, hk⟩⟩
  have h3 : Bc.Nonempty → Bc.card + 1 ≤ T.card + M.card := by
    intro hne
    have a1 := hBcM M hBc
    have a2 := Finset.card_pos.mpr (hTne hne).1
    omega
  have h4 : Bc.Nonempty → (∀ X' ∈ Bc, ∃ X'' ∈ Bc, ¬ X'' ⊆ X') →
      Bc.card + 2 ≤ T.card + M.card := by
    intro hne hmax
    obtain ⟨hTn, hMn⟩ := hTne hne
    have hBM := hBcM M hBc
    by_cases hT2 : 2 ≤ T.card
    · omega
    · have hT1 : T.card = 1 := by
        have := Finset.card_pos.mpr hTn
        omega
      obtain ⟨a0, hTa⟩ := Finset.card_eq_one.mp hT1
      have ha0T : a0 ∈ T := by
        rw [hTa]
        exact Finset.mem_singleton_self a0
      have ha0 := hTtop a0 ha0T
      have hp0 := hpf a0 ha0T
      have hMr : ∀ k ∈ M, Br n C k ∧ OrR n C (opnd C a0 (pf a0)) (n + k) := by
        intro k hk
        obtain ⟨hbk, a, ha, b, hab, hr⟩ := hMbr k hk
        have haT : a ∈ T := (hT a).mpr ⟨ha, b, hab⟩
        have haa : a = a0 := by
          rw [hTa] at haT
          exact Finset.mem_singleton.mp haT
        rw [haa] at hab hr
        by_cases hbp : b = pf a0
        · rw [hbp] at hr
          exact ⟨hbk, hr⟩
        · exfalso
          have e1 : 1 - b = pf a0 := fin2_ne' (pf a0) b hbp
          rw [e1] at hab
          have hcL : c ∈ L := (hL c).mpr ⟨a0, ha0, pf a0, hp0, by
            rw [hab]
            exact Finset.mem_singleton_self c⟩
          exact G.irrefl (h1 c hcL).1
      obtain ⟨k, hk⟩ := hMn
      obtain ⟨hbk, hrk⟩ := hMr k hk
      obtain ⟨k1, hb1, hr1, he1⟩ := dom n C hA _ (hoplt a0 ha0 (pf a0)) k hbk hrk
      have hk1M : k1 ∈ M := hMmem k1 hb1 a0 ha0 (pf a0) hp0 hr1
      have hall : ∀ X ∈ Bc, X ⊆ orIn n C (n + k1) := by
        intro X hX
        obtain ⟨k', hk', hkX⟩ := hBc X hX
        rw [← hkX, he1]
        exact orIn_sub n C hA _ _ (hoplt a0 ha0 (pf a0)) (hMr k' hk').2
      by_cases hX1 : orIn n C (n + k1) ∈ Bc
      · obtain ⟨X'', hX'', hns⟩ := hmax _ hX1
        exact absurd (hall X'' hX'') hns
      · have hBe : Bc.card ≤ (M.erase k1).card := by
          apply hBcM
          intro X hX
          obtain ⟨k', hk', hkX⟩ := hBc X hX
          refine ⟨k', Finset.mem_erase.mpr ⟨?_, hk'⟩, hkX⟩
          intro hkk
          rw [hkk] at hkX
          rw [hkX] at hX1
          exact hX1 hX
        have a3 := Finset.card_erase_add_one hk1M
        omega
  exact ⟨h1, h2, h3, h4⟩

end PEqualNP.Outside.L_meta_1652

theorem PEqualNP.Outside.L_meta_1652 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ∀ (c : Fin n) (T M : Finset ℕ) (L : Finset (Fin n)), (∀ t, t ∈ T ↔ t ∈ PEqualNP.TopForm.tops G C ∧ ∃ p : Fin 2, PEqualNP.TopForm.side (n := n) C t (1 - p) = {c}) → (∀ h, h ∈ M ↔ h ∈ PEqualNP.TopForm.lam G C ∧ ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, PEqualNP.TopForm.side (n := n) C a (1 - b) = {c} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h) → (∀ v, v ∈ L ↔ ∃ d ∈ PEqualNP.TopForm.tops G C, ∃ q : Fin 2, PEqualNP.TopForm.side (n := n) C d (1 - q) = {c} ∧ v ∈ PEqualNP.TopForm.side (n := n) C d q) → ∀ (Bc : Finset (Finset (Fin n))), (∀ X ∈ Bc, ∃ k ∈ M, PEqualNP.TopForm.orIn n C (n + k) = X) → (∀ w ∈ L, G.Adj c w ∧ s(c, w) ∈ PEqualNP.TopForm.starEdges G C) ∧ L.card ≤ T.card + M.card ∧ (Bc.Nonempty → Bc.card + 1 ≤ T.card + M.card) ∧ (Bc.Nonempty → (∀ X' ∈ Bc, ∃ X'' ∈ Bc, ¬ X'' ⊆ X') → Bc.card + 2 ≤ T.card + M.card) :=
  PEqualNP.Outside.L_meta_1652.final
