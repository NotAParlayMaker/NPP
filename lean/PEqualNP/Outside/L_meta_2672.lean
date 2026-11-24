import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2672_aux

open PEqualNP.CircuitLowerBounds

/-! Part 0: a generic fold over the gate list (the snoc and gate lemmas follow the evaluation
toolkit of L_meta_1406). -/

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

/-! Part K: counting for straight-line programs approximating disjoint sums -/

def unit {N : ℕ} (a : Fin N) : Fin N → Bool := fun c => decide (c = a)

def Mono {N : ℕ} (g : (Fin N → Bool) → Bool) : Prop :=
  ∀ x y : Fin N → Bool, (∀ a, x a = true → y a = true) → g x = true → g y = true

def Opd {N : ℕ} {ι : Type} (f : ι → (Fin N → Bool) → Bool) (rank : ι → ℕ) (r : ℕ)
    (a : (Fin N → Bool) → Bool) : Prop :=
  (∃ i, rank i < r ∧ a = f i) ∨ (∃ p : Fin N, a = fun x => x p) ∨ (a = fun _ => false) ∨
    (a = fun _ => true)

def Closed {N : ℕ} {ι : Type} (f : ι → (Fin N → Bool) → Bool) (rank : ι → ℕ) : Prop :=
  ∀ i, ∃ a b, Opd f rank (rank i) a ∧ Opd f rank (rank i) b ∧
    (f i = (fun x => a x || b x) ∨ f i = (fun x => a x && b x))

def Bl {N : ℕ} (J : Fin N → Fin N → Prop) (b : Fin N) (g : (Fin N → Bool) → Bool) : Prop :=
  ∀ x, g x = true → ∃ a, J a b ∧ x a = true

lemma closed_mono {N : ℕ} {ι : Type} (f : ι → (Fin N → Bool) → Bool) (rank : ι → ℕ)
    (hcl : Closed f rank) : ∀ r i, rank i = r → Mono (f i) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro i hi
    obtain ⟨a, b, ha, hb, hf⟩ := hcl i
    have hop : ∀ c, Opd f rank (rank i) c → Mono c := by
      intro c hc
      rcases hc with ⟨i', hr, rfl⟩ | ⟨p, rfl⟩ | rfl | rfl
      · exact ih (rank i') (by omega) i' rfl
      · intro x y hxy h
        exact hxy p h
      · intro x y _ h
        exact h
      · intro x y _ h
        exact h
    have ma := hop a ha
    have mb := hop b hb
    rcases hf with hf | hf
    · rw [hf]
      intro x y hxy h
      simp only [Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (ma x y hxy h)
      · exact Or.inr (mb x y hxy h)
    · rw [hf]
      intro x y hxy h
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ma x y hxy h.1, mb x y hxy h.2⟩

lemma opd_mono {N : ℕ} {ι : Type} (f : ι → (Fin N → Bool) → Bool) (rank : ι → ℕ)
    (hcl : Closed f rank) (r : ℕ) (c : (Fin N → Bool) → Bool) (hc : Opd f rank r c) : Mono c := by
  rcases hc with ⟨i', _, rfl⟩ | ⟨p, rfl⟩ | rfl | rfl
  · exact closed_mono f rank hcl _ i' rfl
  · intro x y hxy h
    exact hxy p h
  · intro x y _ h
    exact h
  · intro x y _ h
    exact h

lemma bl_and {N : ℕ} (J : Fin N → Fin N → Prop) (b : Fin N) (α β : (Fin N → Bool) → Bool)
    (ma : Mono α) (mb : Mono β) (h : Bl J b (fun x => α x && β x)) : Bl J b α ∨ Bl J b β := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold Bl at h1 h2
  push_neg at h1 h2
  obtain ⟨x1, hx1, hn1⟩ := h1
  obtain ⟨x2, hx2, hn2⟩ := h2
  have h3 := h (fun a => x1 a || x2 a) (by
    simp only [Bool.and_eq_true]
    refine ⟨ma x1 _ ?_ hx1, mb x2 _ ?_ hx2⟩
    · intro a ha
      simp [ha]
    · intro a ha
      simp [ha])
  obtain ⟨a, hJ, ha⟩ := h3
  simp only [Bool.or_eq_true] at ha
  rcases ha with ha | ha
  · exact hn1 a hJ ha
  · exact hn2 a hJ ha

/-- node `i` qualifies for the pair `(a, b)` -/
def Q {N : ℕ} {ι : Type} (J : Fin N → Fin N → Prop) (f : ι → (Fin N → Bool) → Bool)
    (e : Fin N × Fin N) (i : ι) : Prop :=
  Bl J e.2 (f i) ∧ f i (unit e.1) = true ∧ ∃ a', a' < e.1 ∧ f i (unit a') = true

def Qmin {N : ℕ} {ι : Type} (J : Fin N → Fin N → Prop) (f : ι → (Fin N → Bool) → Bool)
    (rank : ι → ℕ) (e : Fin N × Fin N) (i : ι) : Prop :=
  Q J f e i ∧ ∀ i', Q J f e i' → rank i ≤ rank i'

lemma opd_min {N : ℕ} {ι : Type} (J : Fin N → Fin N → Prop) (f : ι → (Fin N → Bool) → Bool)
    (rank : ι → ℕ) (a b : Fin N) (i : ι) (hq : Qmin J f rank (a, b) i)
    (c : (Fin N → Bool) → Bool) (hc : Opd f rank (rank i) c) (hbl : Bl J b c)
    (hca : c (unit a) = true) : ∀ a', a' < a → c (unit a') = false := by
  intro a' ha'
  by_contra hne
  have hca' : c (unit a') = true := by simpa using hne
  rcases hc with ⟨i', hr, rfl⟩ | ⟨p, rfl⟩ | rfl | rfl
  · have := hq.2 i' ⟨hbl, hca, a', ha', hca'⟩
    omega
  · simp only [unit, decide_eq_true_eq] at hca hca'
    rw [← hca, ← hca'] at ha'
    exact lt_irrefl _ ha'
  · simp at hca
  · obtain ⟨a0, _, h0⟩ := hbl (fun _ => false) rfl
    simp at h0

lemma key {N : ℕ} {ι : Type} (J : Fin N → Fin N → Prop) (f : ι → (Fin N → Bool) → Bool)
    (rank : ι → ℕ) (hcl : Closed f rank) (a1 a2 b : Fin N) (i : ι)
    (h1 : Qmin J f rank (a1, b) i) (h2 : Qmin J f rank (a2, b) i) (hlt : a2 < a1) : False := by
  obtain ⟨α, β, hα, hβ, hf⟩ := hcl i
  have m1 := opd_min J f rank a1 b i h1
  have m2 := opd_min J f rank a2 b i h2
  obtain ⟨⟨hbl, hv1, a1', ha1', hv1'⟩, _⟩ := h1
  obtain ⟨⟨_, hv2, a2', ha2', hv2'⟩, _⟩ := h2
  rcases hf with hf | hf
  · rw [hf] at hbl hv1 hv2 hv2'
    simp only [Bool.or_eq_true] at hv1 hv2 hv2'
    have bα : Bl J b α := fun x hx => hbl x (by simp [hx])
    have bβ : Bl J b β := fun x hx => hbl x (by simp [hx])
    have claim : ∀ c, Opd f rank (rank i) c → Bl J b c → c (unit a2') = true →
        c (unit a1) = false ∧ c (unit a2) = false := by
      intro c hc hb hc2'
      constructor
      · by_contra hne
        have := m1 c hc hb (by simpa using hne) a2' (lt_trans ha2' hlt)
        rw [this] at hc2'
        exact absurd hc2' (by simp)
      · by_contra hne
        have := m2 c hc hb (by simpa using hne) a2' ha2'
        rw [this] at hc2'
        exact absurd hc2' (by simp)
    rcases hv2' with h | h
    · obtain ⟨n1, n2⟩ := claim α hα bα h
      rw [n1] at hv1
      rw [n2] at hv2
      simp only [Bool.false_eq_true, false_or] at hv1 hv2
      have := m1 β hβ bβ hv1 a2 hlt
      rw [this] at hv2
      exact absurd hv2 (by simp)
    · obtain ⟨n1, n2⟩ := claim β hβ bβ h
      rw [n1] at hv1
      rw [n2] at hv2
      simp only [Bool.false_eq_true, or_false] at hv1 hv2
      have := m1 α hα bα hv1 a2 hlt
      rw [this] at hv2
      exact absurd hv2 (by simp)
  · rw [hf] at hbl hv1 hv1'
    simp only [Bool.and_eq_true] at hv1 hv1'
    rcases bl_and J b α β (opd_mono f rank hcl _ α hα) (opd_mono f rank hcl _ β hβ) hbl with hb | hb
    · have := m1 α hα hb hv1.1 a1' ha1'
      rw [this] at hv1'
      exact absurd hv1'.1 (by simp)
    · have := m1 β hβ hb hv1.2 a1' ha1'
      rw [this] at hv1'
      exact absurd hv1'.2 (by simp)

theorem slp_count {N : ℕ} {ι : Type} [Fintype ι] (J : Fin N → Fin N → Prop)
    (hK : ∀ a1 a2 b1 b2, a1 ≠ a2 → J a1 b1 → J a2 b1 → J a1 b2 → J a2 b2 → b1 = b2)
    (f : ι → (Fin N → Bool) → Bool) (rank : ι → ℕ) (hcl : Closed f rank)
    (h : Fin N → (Fin N → Bool) → Bool) (hout : ∀ b, ∃ r, Opd f rank r (h b))
    (hle : ∀ b, Bl J b (h b)) :
    (Finset.univ.filter (fun e : Fin N × Fin N => h e.2 (unit e.1) = true)).card ≤
      Fintype.card ι + N := by
  classical
  set S := Finset.univ.filter (fun e : Fin N × Fin N => h e.2 (unit e.1) = true) with hS
  set S2 := S.filter (fun e => ∃ a', a' < e.1 ∧ h e.2 (unit a') = true) with hS2
  set S1 := S.filter (fun e => ¬ ∃ a', a' < e.1 ∧ h e.2 (unit a') = true) with hS1
  have hsplit : S.card = S2.card + S1.card := by
    rw [hS2, hS1]
    exact (Finset.card_filter_add_card_filter_not _).symm
  have h1 : S1.card ≤ N := by
    have : S1.card ≤ (Finset.univ : Finset (Fin N)).card := by
      apply Finset.card_le_card_of_injOn (fun e => e.2)
      · intro e _
        exact Finset.mem_univ _
      · intro e1 he1 e2 he2 heq
        simp only [hS1, hS, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at he1 he2
        obtain ⟨a1, b1⟩ := e1
        obtain ⟨a2, b2⟩ := e2
        simp only at heq he1 he2
        subst heq
        rcases lt_trichotomy a1 a2 with hlt | heq | hlt
        · exact absurd ⟨a1, hlt, he1.1⟩ he2.2
        · rw [heq]
        · exact absurd ⟨a2, hlt, he2.1⟩ he1.2
    simpa using this
  have h2 : S2.card ≤ (Finset.univ : Finset ι).card := by
    apply Finset.card_le_card_of_forall_subsingleton (Qmin J f rank)
    · intro e he
      simp only [hS2, hS, Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨he1, a', ha', hea'⟩ := he
      have hex : ∃ i, Q J f e i := by
        obtain ⟨r, hr⟩ := hout e.2
        rcases hr with ⟨i, _, hi⟩ | ⟨p, hp⟩ | hp | hp
        · refine ⟨i, ?_, ?_, a', ha', ?_⟩
          · rw [← hi]
            exact hle e.2
          · rw [← hi]
            exact he1
          · rw [← hi]
            exact hea'
        · rw [hp] at he1 hea'
          simp only [unit, decide_eq_true_eq] at he1 hea'
          rw [← he1, ← hea'] at ha'
          exact absurd ha' (lt_irrefl _)
        · rw [hp] at he1
          simp at he1
        · have := hle e.2
          rw [hp] at this
          obtain ⟨a0, _, h0⟩ := this (fun _ => false) rfl
          simp at h0
      obtain ⟨i0, hi0⟩ := hex
      obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i => Q J f e i)) rank
        ⟨i0, by simp [hi0]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hmin
      exact ⟨i, Finset.mem_univ _, hi, hmin⟩
    · intro i _ e1 he1 e2 he2
      simp only [Set.mem_setOf_eq] at he1 he2
      obtain ⟨_, q1⟩ := he1
      obtain ⟨_, q2⟩ := he2
      obtain ⟨a1, b1⟩ := e1
      obtain ⟨a2, b2⟩ := e2
      have hb : b1 = b2 := by
        obtain ⟨⟨hbl1, hv1, a1', ha1', hv1'⟩, _⟩ := q1
        obtain ⟨⟨hbl2, _, _, _, _⟩, _⟩ := q2
        simp only at hbl1 hv1 ha1' hv1' hbl2
        obtain ⟨c1, hJ1, hc1⟩ := hbl1 _ hv1
        obtain ⟨c2, hJ2, hc2⟩ := hbl1 _ hv1'
        obtain ⟨c3, hJ3, hc3⟩ := hbl2 _ hv1
        obtain ⟨c4, hJ4, hc4⟩ := hbl2 _ hv1'
        simp only [unit, decide_eq_true_eq] at hc1 hc2 hc3 hc4
        rw [hc1] at hJ1
        rw [hc2] at hJ2
        rw [hc3] at hJ3
        rw [hc4] at hJ4
        exact hK a1 a1' b1 b2 (ne_of_gt ha1') hJ1 hJ2 hJ3 hJ4
      subst hb
      rcases lt_trichotomy a1 a2 with hlt | heq | hlt
      · exact (key J f rank hcl a2 a1 b1 i q2 q1 hlt).elim
      · rw [heq]
      · exact (key J f rank hcl a1 a2 b1 i q1 q2 hlt).elim
  simp only [Finset.card_univ] at h2
  omega

/-! Part 1: wire values and linear parts, gate by gate -/

def isAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => true
  | _ => false

def ov (k : Bool) (v : ℕ → Bool) : Option ℕ → Bool
  | none => k
  | some a => v a

def o1 (v : ℕ → Bool) : Option ℕ → Bool
  | none => false
  | some a => v a

def bop (k : Bool) (x y : Bool) : Bool := if k then x && y else x || y

def cof (k : Bool) (p0 : ℕ → Bool) (O : Option ℕ) : Bool := if k then ov k p0 O else true

def W (C : Circuit) (zl : List Bool) (w : ℕ) : Bool := (C.wires zl).getD w false

def P (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) : Bool × Bool :=
  (PEqualNP.ReadK.linearParts C isLine zl).getD w (false, false)

def Gp (g : Gate) (ins : List (Bool × Bool)) : Bool × Bool :=
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def pinit (isLine : ℕ → Bool) (zl : List Bool) : List (Bool × Bool) :=
  (zl.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)

lemma W_eq (C : Circuit) (zl : List Bool) (w : ℕ) :
    W C zl w = rv false (fun g l => g.op.eval l) zl C.gates w := rfl

lemma P_eq (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) :
    P C isLine zl w = rv (false, false) Gp (pinit isLine zl) C.gates w := rfl

lemma pinit_length (isLine : ℕ → Bool) (zl : List Bool) : (pinit isLine zl).length = zl.length := by
  simp [pinit]

lemma pinit_getD (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) (hw : w < zl.length) :
    (pinit isLine zl).getD w (false, false) =
      if isLine w then (false, zl.getD w false) else (zl.getD w false, false) := by
  simp [pinit, List.getD_eq_getElem?_getD, hw]

lemma W_lt (C : Circuit) (zl : List Bool) (w : ℕ) (hw : w < zl.length) :
    W C zl w = zl.getD w false := by
  rw [W_eq, rv_lt _ _ _ _ _ hw]

lemma W_ge (C : Circuit) (zl : List Bool) (w : ℕ) (hw : zl.length + C.gates.length ≤ w) :
    W C zl w = false := by
  rw [W_eq, rv_ge _ _ _ _ _ hw]

lemma P_lt (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) (hw : w < zl.length) :
    P C isLine zl w = if isLine w then (false, zl.getD w false) else (zl.getD w false, false) := by
  rw [P_eq, rv_lt _ _ _ _ _ (by rw [pinit_length]; exact hw), pinit_getD _ _ _ hw]

lemma P_ge (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ)
    (hw : zl.length + C.gates.length ≤ w) : P C isLine zl w = (false, false) := by
  rw [P_eq, rv_ge _ _ _ _ _ (by rw [pinit_length]; exact hw)]

lemma W_gate (C : Circuit) (zl : List Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (hlen : C.gates[k].inputs.length ≤ 2)
    (hrb : ∀ j ∈ C.gates[k].inputs, j < zl.length + k) :
    W C zl (zl.length + k) = bop (isAnd C.gates[k])
      (ov (isAnd C.gates[k]) (W C zl) C.gates[k].inputs[0]?)
      (ov (isAnd C.gates[k]) (W C zl) C.gates[k].inputs[1]?) := by
  have h : W C zl (zl.length + k) =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun j => W C zl j) :=
    rv_gate false (fun g l => g.op.eval l) zl C.gates k hk hrb
  rw [h]
  clear h hrb
  generalize W C zl = wf
  generalize C.gates[k] = g at hop hlen ⊢
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl <;> rfl
  | [a], _ =>
    rcases hop with rfl | rfl <;> simp [GateOp.eval, isAnd, bop, ov]
  | [a, b], _ =>
    rcases hop with rfl | rfl <;> simp [GateOp.eval, isAnd, bop, ov]
  | _ :: _ :: _ :: _, h => simp at h

lemma P_gate (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (hlen : C.gates[k].inputs.length ≤ 2)
    (hrb : ∀ j ∈ C.gates[k].inputs, j < zl.length + k) :
    P C isLine zl (zl.length + k) =
      (bop (isAnd C.gates[k])
        (ov (isAnd C.gates[k]) (fun w => (P C isLine zl w).1) C.gates[k].inputs[0]?)
        (ov (isAnd C.gates[k]) (fun w => (P C isLine zl w).1) C.gates[k].inputs[1]?),
       (cof (isAnd C.gates[k]) (fun w => (P C isLine zl w).1) C.gates[k].inputs[1]? &&
          o1 (fun w => (P C isLine zl w).2) C.gates[k].inputs[0]?) ||
       (cof (isAnd C.gates[k]) (fun w => (P C isLine zl w).1) C.gates[k].inputs[0]? &&
          o1 (fun w => (P C isLine zl w).2) C.gates[k].inputs[1]?)) := by
  have hl := pinit_length isLine zl
  have h0 := rv_gate (false, false) Gp (pinit isLine zl) C.gates k hk (by rw [hl]; exact hrb)
  rw [hl] at h0
  have h : P C isLine zl (zl.length + k) =
      Gp (C.gates[k]) ((C.gates[k]).inputs.map fun j => P C isLine zl j) := h0
  rw [h]
  clear h h0 hrb
  generalize P C isLine zl = pf
  generalize C.gates[k] = g at hop hlen ⊢
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl <;> rfl
  | [a], _ =>
    have e0 : ([a] : List ℕ)[0]? = some a := rfl
    have e1 : ([a] : List ℕ)[1]? = none := rfl
    rcases hop with rfl | rfl
    · simp only [List.map_cons, List.map_nil, e0, e1, ov, o1, cof, isAnd, bop, Gp]
      generalize pf a = pa
      rcases pa with ⟨_ | _, _ | _⟩ <;> rfl
    · simp only [List.map_cons, List.map_nil, e0, e1, ov, o1, cof, isAnd, bop, Gp]
      generalize pf a = pa
      rcases pa with ⟨_ | _, _ | _⟩ <;> rfl
  | [a, b], _ =>
    have e0 : ([a, b] : List ℕ)[0]? = some a := rfl
    have e1 : ([a, b] : List ℕ)[1]? = some b := rfl
    rcases hop with rfl | rfl
    · simp only [List.map_cons, List.map_nil, e0, e1, ov, o1, cof, isAnd, bop, Gp]
      generalize pf a = pa
      generalize pf b = pb
      rcases pa with ⟨_ | _, _ | _⟩ <;> rcases pb with ⟨_ | _, _ | _⟩ <;> rfl
    · simp only [List.map_cons, List.map_nil, e0, e1, ov, o1, cof, isAnd, bop, Gp]
      generalize pf a = pa
      generalize pf b = pb
      rcases pa with ⟨_ | _, _ | _⟩ <;> rcases pb with ⟨_ | _, _ | _⟩ <;> rfl
  | _ :: _ :: _ :: _, h => simp at h

/-- the standing hypotheses on the gate list -/
def Good (C : Circuit) (n : ℕ) : Prop :=
  ∀ (k : ℕ) (hk : k < C.gates.length),
    (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) ∧ C.gates[k].inputs.length ≤ 2 ∧
      ∀ j ∈ C.gates[k].inputs, j < n + k

lemma opd_lt (C : Circuit) (n : ℕ) (hg : Good C n) (k : ℕ) (hk : k < C.gates.length) (i a : ℕ)
    (h : C.gates[k].inputs[i]? = some a) : a < n + k :=
  (hg k hk).2.2 a (List.mem_of_getElem? h)

/-! Part 2: the linear parts are below the wire value -/

lemma P_le_W (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (hg : Good C zl.length) :
    ∀ w, ((P C isLine zl w).1 = true → W C zl w = true) ∧
      ((P C isLine zl w).2 = true → W C zl w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < zl.length
    · rw [P_lt _ _ _ _ h1, W_lt _ _ _ h1]
      cases isLine w <;> simp
    · by_cases h2 : zl.length + C.gates.length ≤ w
      · rw [P_ge _ _ _ _ h2]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, w = zl.length + k := ⟨w - zl.length, by omega⟩
        have hk : k < C.gates.length := by omega
        obtain ⟨hop, hlen, hrb⟩ := hg k hk
        rw [P_gate C isLine zl k hk hop hlen hrb, W_gate C zl k hk hop hlen hrb]
        have hO : ∀ O : Option ℕ, (∀ a, O = some a → a < zl.length + k) →
            (ov (isAnd C.gates[k]) (fun w => (P C isLine zl w).1) O = true →
              ov (isAnd C.gates[k]) (W C zl) O = true) ∧
            (o1 (fun w => (P C isLine zl w).2) O = true →
              ov (isAnd C.gates[k]) (W C zl) O = true) := by
          intro O hO
          cases O with
          | none => simp [ov, o1]
          | some a => exact ih a (hO a rfl)
        have hA := hO C.gates[k].inputs[0]? (fun a ha => opd_lt C _ hg k hk 0 a ha)
        have hB := hO C.gates[k].inputs[1]? (fun a ha => opd_lt C _ hg k hk 1 a ha)
        revert hA hB
        simp only [cof]
        generalize ov (isAnd C.gates[k]) (fun w => (P C isLine zl w).1) C.gates[k].inputs[0]? = a0
        generalize ov (isAnd C.gates[k]) (fun w => (P C isLine zl w).1) C.gates[k].inputs[1]? = b0
        generalize o1 (fun w => (P C isLine zl w).2) C.gates[k].inputs[0]? = a1
        generalize o1 (fun w => (P C isLine zl w).2) C.gates[k].inputs[1]? = b1
        generalize ov (isAnd C.gates[k]) (W C zl) C.gates[k].inputs[0]? = va
        generalize ov (isAnd C.gates[k]) (W C zl) C.gates[k].inputs[1]? = vb
        generalize isAnd C.gates[k] = kk
        cases kk <;> cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases va <;> cases vb <;>
          simp [bop]

/-! Part 3: part 0 does not depend on the line inputs -/

lemma P0_indep (C : Circuit) (isLine : ℕ → Bool) (zl zl' : List Bool) (hl : zl'.length = zl.length)
    (hg : Good C zl.length)
    (hag : ∀ w, w < zl.length → isLine w = false → zl.getD w false = zl'.getD w false) :
    ∀ w, (P C isLine zl w).1 = (P C isLine zl' w).1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < zl.length
    · rw [P_lt _ _ _ _ h1, P_lt _ _ _ _ (by rw [hl]; exact h1)]
      cases hw : isLine w
      · simp only [Bool.false_eq_true, if_false]
        exact hag w h1 hw
      · simp
    · by_cases h2 : zl.length + C.gates.length ≤ w
      · rw [P_ge _ _ _ _ h2, P_ge _ _ _ _ (by rw [hl]; exact h2)]
      · obtain ⟨k, rfl⟩ : ∃ k, w = zl.length + k := ⟨w - zl.length, by omega⟩
        have hk : k < C.gates.length := by omega
        obtain ⟨hop, hlen, hrb⟩ := hg k hk
        have e2 := P_gate C isLine zl' k hk hop hlen (by rw [hl]; exact hrb)
        rw [hl] at e2
        rw [P_gate C isLine zl k hk hop hlen hrb, e2]
        have hO : ∀ O : Option ℕ, (∀ a, O = some a → a < zl.length + k) →
            ov (isAnd C.gates[k]) (fun w => (P C isLine zl w).1) O =
              ov (isAnd C.gates[k]) (fun w => (P C isLine zl' w).1) O := by
          intro O hO
          cases O with
          | none => rfl
          | some a => exact ih a (hO a rfl)
        have hA := hO C.gates[k].inputs[0]? (fun a ha => opd_lt C _ hg k hk 0 a ha)
        have hB := hO C.gates[k].inputs[1]? (fun a ha => opd_lt C _ hg k hk 1 a ha)
        simp only [hA, hB]

/-! Part 4: reverse-mode differentiation, at one input -/

def updOpt (c : ℕ → Bool) (O : Option ℕ) (v : Bool) : ℕ → Bool :=
  match O with
  | none => c
  | some a => fun w => if w = a then c a || v else c w

def stepBack (g : Gate) (t : ℕ) (p0 : ℕ → Bool) (c : ℕ → Bool) : ℕ → Bool :=
  updOpt (updOpt c g.inputs[0]? (c t && cof (isAnd g) p0 g.inputs[1]?)) g.inputs[1]?
    (c t && cof (isAnd g) p0 g.inputs[0]?)

def gk (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨GateOp.or, []⟩

def cvec (C : Circuit) (n : ℕ) (p0 : ℕ → Bool) : ℕ → ℕ → Bool
  | 0 => fun w => decide (w = C.output)
  | (k + 1) => stepBack (gk C (C.gates.length - 1 - k)) (n + (C.gates.length - 1 - k)) p0
      (cvec C n p0 k)

lemma gk_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gk C j = C.gates[j] := by
  simp [gk, List.getD_eq_getElem?_getD, hj]

lemma updOpt_sum (c : ℕ → Bool) (O : Option ℕ) (v : Bool) (p1 : ℕ → Bool) (t : ℕ)
    (hO : ∀ a, O = some a → a < t) :
    (∃ w, w < t ∧ updOpt c O v w = true ∧ p1 w = true) ↔
      ((∃ w, w < t ∧ c w = true ∧ p1 w = true) ∨ (v = true ∧ o1 p1 O = true)) := by
  cases O with
  | none => simp [updOpt, o1]
  | some a =>
    simp only [updOpt, o1]
    constructor
    · rintro ⟨w, hw, hu, hp⟩
      by_cases hwa : w = a
      · subst hwa
        simp only [if_true, Bool.or_eq_true] at hu
        rcases hu with hu | hu
        · exact Or.inl ⟨w, hw, hu, hp⟩
        · exact Or.inr ⟨hu, hp⟩
      · rw [if_neg hwa] at hu
        exact Or.inl ⟨w, hw, hu, hp⟩
    · rintro (⟨w, hw, hc, hp⟩ | ⟨hv, hp⟩)
      · refine ⟨w, hw, ?_, hp⟩
        by_cases hwa : w = a
        · subst hwa
          simp [hc]
        · rw [if_neg hwa]
          exact hc
      · exact ⟨a, hO a rfl, by simp [hv], hp⟩

lemma step_inv (g : Gate) (t : ℕ) (p0 p1 c : ℕ → Bool)
    (hA : ∀ a, g.inputs[0]? = some a → a < t) (hB : ∀ a, g.inputs[1]? = some a → a < t)
    (hp1 : p1 t = ((cof (isAnd g) p0 g.inputs[1]? && o1 p1 g.inputs[0]?) ||
      (cof (isAnd g) p0 g.inputs[0]? && o1 p1 g.inputs[1]?))) :
    (∃ w, w < t + 1 ∧ c w = true ∧ p1 w = true) ↔
      (∃ w, w < t ∧ stepBack g t p0 c w = true ∧ p1 w = true) := by
  unfold stepBack
  rw [updOpt_sum _ _ _ _ _ hB, updOpt_sum _ _ _ _ _ hA]
  constructor
  · rintro ⟨w, hw, hc, hp⟩
    by_cases hwt : w = t
    · subst hwt
      rw [hp1] at hp
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hp ⊢
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Or.inr ⟨⟨hc, h1⟩, h2⟩)
      · exact Or.inr ⟨⟨hc, h1⟩, h2⟩
    · exact Or.inl (Or.inl ⟨w, by omega, hc, hp⟩)
  · rintro ((⟨w, hw, hc, hp⟩ | ⟨hv, ho⟩) | ⟨hv, ho⟩)
    · exact ⟨w, by omega, hc, hp⟩
    · simp only [Bool.and_eq_true] at hv
      refine ⟨t, by omega, hv.1, ?_⟩
      rw [hp1]
      simp [hv.2, ho]
    · simp only [Bool.and_eq_true] at hv
      refine ⟨t, by omega, hv.1, ?_⟩
      rw [hp1]
      simp [hv.2, ho]

lemma cvec_inv (C : Circuit) (isLine : ℕ → Bool) (zl : List Bool) (hg : Good C zl.length) :
    ∀ k, k ≤ C.gates.length →
      ((P C isLine zl C.output).2 = true ↔
        ∃ w, w < zl.length + (C.gates.length - k) ∧
          cvec C zl.length (fun w => (P C isLine zl w).1) k w = true ∧
          (P C isLine zl w).2 = true) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [cvec, decide_eq_true_eq, Nat.sub_zero]
    constructor
    · intro h
      refine ⟨C.output, ?_, rfl, h⟩
      by_contra hcon
      rw [P_ge _ _ _ _ (by omega)] at h
      simp at h
    · rintro ⟨w, _, rfl, h⟩
      exact h
  | succ k ih =>
    intro hk
    rw [ih (by omega)]
    have hj : C.gates.length - 1 - k < C.gates.length := by omega
    have e1 : zl.length + (C.gates.length - k) = zl.length + (C.gates.length - 1 - k) + 1 := by
      omega
    have e2 : zl.length + (C.gates.length - (k + 1)) = zl.length + (C.gates.length - 1 - k) := by
      omega
    rw [e1, e2]
    obtain ⟨hop, hlen, hrb⟩ := hg _ hj
    have hp := P_gate C isLine zl _ hj hop hlen hrb
    simp only [cvec]
    rw [gk_eq C _ hj]
    exact step_inv (C.gates[C.gates.length - 1 - k]) (zl.length + (C.gates.length - 1 - k))
      (fun w => (P C isLine zl w).1) (fun w => (P C isLine zl w).2) _
      (fun a ha => opd_lt C _ hg _ hj 0 a ha) (fun a ha => opd_lt C _ hg _ hj 1 a ha)
      (by rw [hp])

/-! Part 5: the derivative as a straight-line program in the point inputs -/

structure Ctx (N : ℕ) where
  C : Circuit
  isLine : ℕ → Bool
  n : ℕ
  wa : Fin N → ℕ
  wb : Fin N → ℕ

def zf {N : ℕ} (K : Ctx N) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  decide (∃ a, K.wa a = w ∧ x a = true) || decide (∃ b, K.wb b = w ∧ y b = true)

def zin {N : ℕ} (K : Ctx N) (x y : Fin N → Bool) : List Bool := (List.range K.n).map (zf K x y)

def OK {N : ℕ} (K : Ctx N) : Prop :=
  Good K.C K.n ∧ (∀ a, K.wa a < K.n ∧ K.isLine (K.wa a) = false) ∧
  (∀ b, K.wb b < K.n ∧ K.isLine (K.wb b) = true) ∧ Function.Injective K.wa ∧
  Function.Injective K.wb ∧
  (∀ w, w < K.n → K.isLine w = false → ∃ a, K.wa a = w) ∧
  (∀ w, w < K.n → K.isLine w = true → ∃ b, K.wb b = w)

lemma zin_length {N : ℕ} (K : Ctx N) (x y : Fin N → Bool) : (zin K x y).length = K.n := by
  simp [zin]

lemma zin_getD {N : ℕ} (K : Ctx N) (x y : Fin N → Bool) (w : ℕ) (hw : w < K.n) :
    (zin K x y).getD w false = zf K x y w := by
  simp [zin, List.getD_eq_getElem?_getD, hw]

lemma zf_a {N : ℕ} (K : Ctx N) (hK : OK K) (x y : Fin N → Bool) (w : ℕ)
    (hw : K.isLine w = false) : zf K x y w = decide (∃ a, K.wa a = w ∧ x a = true) := by
  have h : ¬ ∃ b, K.wb b = w ∧ y b = true := by
    rintro ⟨b, rfl, _⟩
    have h2 := (hK.2.2.1 b).2
    rw [hw] at h2
    exact absurd h2 (by simp)
  simp [zf, h]

lemma zf_b {N : ℕ} (K : Ctx N) (hK : OK K) (x y : Fin N → Bool) (w : ℕ)
    (hw : K.isLine w = true) : zf K x y w = decide (∃ b, K.wb b = w ∧ y b = true) := by
  have h : ¬ ∃ a, K.wa a = w ∧ x a = true := by
    rintro ⟨a, rfl, _⟩
    have h2 := (hK.2.1 a).2
    rw [hw] at h2
    exact absurd h2 (by simp)
  simp [zf, h]

lemma zf_wa {N : ℕ} (K : Ctx N) (hK : OK K) (x y : Fin N → Bool) (a : Fin N) :
    zf K x y (K.wa a) = x a := by
  rw [zf_a K hK x y _ (hK.2.1 a).2]
  have h : (∃ a', K.wa a' = K.wa a ∧ x a' = true) ↔ x a = true := by
    constructor
    · rintro ⟨a', h, hx⟩
      rw [← hK.2.2.2.1 h]
      exact hx
    · intro h
      exact ⟨a, rfl, h⟩
  simp [h]

lemma zf_wb {N : ℕ} (K : Ctx N) (hK : OK K) (x y : Fin N → Bool) (b : Fin N) :
    zf K x y (K.wb b) = y b := by
  rw [zf_b K hK x y _ (hK.2.2.1 b).2]
  have h : (∃ b', K.wb b' = K.wb b ∧ y b' = true) ↔ y b = true := by
    constructor
    · rintro ⟨b', h, hx⟩
      rw [← hK.2.2.2.2.1 h]
      exact hx
    · intro h
      exact ⟨b, rfl, h⟩
  simp [h]

lemma good_z {N : ℕ} (K : Ctx N) (hK : OK K) (x y : Fin N → Bool) :
    Good K.C (zin K x y).length := by
  rw [zin_length]
  exact hK.1

lemma Pz_lt {N : ℕ} (K : Ctx N) (x y : Fin N → Bool) (w : ℕ) (hw : w < K.n) :
    P K.C K.isLine (zin K x y) w =
      if K.isLine w then (false, zf K x y w) else (zf K x y w, false) := by
  rw [P_lt _ _ _ _ (by rw [zin_length]; exact hw), zin_getD K x y w hw]

def p0f {N : ℕ} (K : Ctx N) (w : ℕ) (x : Fin N → Bool) : Bool :=
  (P K.C K.isLine (zin K x (fun _ => false)) w).1

def cfn {N : ℕ} (K : Ctx N) (k w : ℕ) (x : Fin N → Bool) : Bool :=
  cvec K.C K.n (fun w => p0f K w x) k w

lemma Pz_indep {N : ℕ} (K : Ctx N) (hK : OK K) (x y : Fin N → Bool) (w : ℕ) :
    (P K.C K.isLine (zin K x y) w).1 = p0f K w x := by
  unfold p0f
  apply P0_indep K.C K.isLine (zin K x y) (zin K x (fun _ => false))
    (by rw [zin_length, zin_length]) (good_z K hK x y)
  intro w hw hl
  rw [zin_length] at hw
  rw [zin_getD K x y w hw, zin_getD K x _ w hw, zf_a K hK x y w hl, zf_a K hK x _ w hl]

lemma p0f_gate {N : ℕ} (K : Ctx N) (hK : OK K) (j : ℕ) (hj : j < K.C.gates.length)
    (x : Fin N → Bool) :
    p0f K (K.n + j) x = bop (isAnd K.C.gates[j])
      (ov (isAnd K.C.gates[j]) (fun w => p0f K w x) K.C.gates[j].inputs[0]?)
      (ov (isAnd K.C.gates[j]) (fun w => p0f K w x) K.C.gates[j].inputs[1]?) := by
  obtain ⟨hop, hlen, hrb⟩ := hK.1 j hj
  have h := P_gate K.C K.isLine (zin K x (fun _ => false)) j hj hop hlen
    (by rw [zin_length]; exact hrb)
  rw [zin_length] at h
  unfold p0f
  rw [h]

lemma deriv_eq {N : ℕ} (K : Ctx N) (hK : OK K) (x : Fin N → Bool) (b : Fin N) :
    (P K.C K.isLine (zin K x (unit b)) K.C.output).2 = cfn K K.C.gates.length (K.wb b) x := by
  have h := cvec_inv K.C K.isLine (zin K x (unit b)) (good_z K hK x _) K.C.gates.length le_rfl
  rw [zin_length] at h
  simp only [Nat.sub_self, Nat.add_zero] at h
  have hp0 : (fun w => (P K.C K.isLine (zin K x (unit b)) w).1) = fun w => p0f K w x :=
    funext (Pz_indep K hK x (unit b))
  rw [hp0] at h
  apply Bool.eq_iff_iff.mpr
  rw [h]
  unfold cfn
  constructor
  · rintro ⟨w, hw, hc, hp⟩
    rw [Pz_lt K _ _ w hw] at hp
    cases hl : K.isLine w
    · rw [hl] at hp
      simp at hp
    · rw [hl] at hp
      simp only [if_true] at hp
      rw [zf_b K hK _ _ w hl] at hp
      simp only [unit, decide_eq_true_eq] at hp
      obtain ⟨b', hb', hbb⟩ := hp
      rw [hbb] at hb'
      rw [hb']
      exact hc
  · intro hc
    refine ⟨K.wb b, (hK.2.2.1 b).1, hc, ?_⟩
    rw [Pz_lt K _ _ _ (hK.2.2.1 b).1, (hK.2.2.1 b).2]
    simp only [if_true]
    rw [zf_wb K hK]
    simp [unit]

lemma deriv_le {N : ℕ} (K : Ctx N) (hK : OK K) (x : Fin N → Bool) (b : Fin N)
    (h : cfn K K.C.gates.length (K.wb b) x = true) :
    W K.C (zin K x (unit b)) K.C.output = true := by
  rw [← deriv_eq K hK x b] at h
  exact (P_le_W K.C K.isLine _ (good_z K hK x _) _).2 h

def v1 {N : ℕ} (K : Ctx N) (k j : ℕ) (x : Fin N → Bool) : Bool :=
  cfn K k (K.n + j) x && cof (isAnd (gk K.C j)) (fun w => p0f K w x) (gk K.C j).inputs[1]?

def v2 {N : ℕ} (K : Ctx N) (k j : ℕ) (x : Fin N → Bool) : Bool :=
  cfn K k (K.n + j) x && cof (isAnd (gk K.C j)) (fun w => p0f K w x) (gk K.C j).inputs[0]?

def n2 {N : ℕ} (K : Ctx N) (k j : ℕ) (x : Fin N → Bool) : Bool :=
  o1 (fun w => cfn K k w x) (gk K.C j).inputs[0]? || v1 K k j x

def n4 {N : ℕ} (K : Ctx N) (k j : ℕ) (x : Fin N → Bool) : Bool :=
  o1 (updOpt (fun w => cfn K k w x) (gk K.C j).inputs[0]? (v1 K k j x)) (gk K.C j).inputs[1]? ||
    v2 K k j x

def nodeF {N : ℕ} (K : Ctx N) (j s : ℕ) : (Fin N → Bool) → Bool :=
  match s with
  | 0 => p0f K (K.n + j)
  | 1 => v1 K (K.C.gates.length - 1 - j) j
  | 2 => n2 K (K.C.gates.length - 1 - j) j
  | 3 => v2 K (K.C.gates.length - 1 - j) j
  | _ => n4 K (K.C.gates.length - 1 - j) j

def nf {N : ℕ} (K : Ctx N) (i : Fin K.C.gates.length × Fin 5) : (Fin N → Bool) → Bool :=
  nodeF K i.1.val i.2.val

def nrank {N : ℕ} (K : Ctx N) (i : Fin K.C.gates.length × Fin 5) : ℕ :=
  if i.2.val = 0 then i.1.val
  else K.C.gates.length + 5 * (K.C.gates.length - 1 - i.1.val) + i.2.val

lemma upd2 (c : ℕ → Bool) (A B : Option ℕ) (u1 u2 : Bool) (w : ℕ) :
    updOpt (updOpt c A u1) B u2 w =
      if B = some w then o1 (updOpt c A u1) B || u2
      else if A = some w then o1 c A || u1 else c w := by
  have hA : updOpt c A u1 w = if A = some w then o1 c A || u1 else c w := by
    cases A with
    | none => simp [updOpt]
    | some a =>
      simp only [updOpt, o1, Option.some.injEq]
      by_cases h : w = a
      · subst h
        simp
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  cases B with
  | none =>
    rw [if_neg (by simp)]
    exact hA
  | some b =>
    by_cases h : w = b
    · subst h
      simp [updOpt, o1]
    · rw [if_neg (fun h' => h (Option.some.inj h').symm), ← hA]
      show (if w = b then _ else _) = _
      rw [if_neg h]

lemma cfn_succ {N : ℕ} (K : Ctx N) (k w : ℕ) (x : Fin N → Bool) :
    cfn K (k + 1) w x =
      if (gk K.C (K.C.gates.length - 1 - k)).inputs[1]? = some w then
        n4 K k (K.C.gates.length - 1 - k) x
      else if (gk K.C (K.C.gates.length - 1 - k)).inputs[0]? = some w then
        n2 K k (K.C.gates.length - 1 - k) x
      else cfn K k w x := by
  unfold n4 n2
  exact upd2 _ _ _ _ _ _

def Avail {N : ℕ} (K : Ctx N) (k : ℕ) (c : (Fin N → Bool) → Bool) : Prop :=
  (c = fun _ => false) ∨ (c = fun _ => true) ∨
    ∃ j, K.C.gates.length - k ≤ j ∧ j < K.C.gates.length ∧ (c = nodeF K j 2 ∨ c = nodeF K j 4)

lemma avail {N : ℕ} (K : Ctx N) : ∀ k, k ≤ K.C.gates.length → ∀ w,
    Avail K k (fun x => cfn K k w x) := by
  intro k
  induction k with
  | zero =>
    intro _ w
    by_cases h : w = K.C.output
    · right
      left
      funext x
      show decide (w = K.C.output) = true
      simp [h]
    · left
      funext x
      show decide (w = K.C.output) = false
      simp [h]
  | succ k ih =>
    intro hk w
    have e : K.C.gates.length - 1 - (K.C.gates.length - 1 - k) = k := by omega
    have hj : K.C.gates.length - 1 - k < K.C.gates.length := by omega
    by_cases hB : (gk K.C (K.C.gates.length - 1 - k)).inputs[1]? = some w
    · right
      right
      refine ⟨K.C.gates.length - 1 - k, by omega, hj, Or.inr ?_⟩
      funext x
      rw [cfn_succ, if_pos hB]
      show _ = n4 K (K.C.gates.length - 1 - (K.C.gates.length - 1 - k)) _ x
      rw [e]
    · by_cases hA : (gk K.C (K.C.gates.length - 1 - k)).inputs[0]? = some w
      · right
        right
        refine ⟨K.C.gates.length - 1 - k, by omega, hj, Or.inl ?_⟩
        funext x
        rw [cfn_succ, if_neg hB, if_pos hA]
        show _ = n2 K (K.C.gates.length - 1 - (K.C.gates.length - 1 - k)) _ x
        rw [e]
      · have hc : (fun x => cfn K (k + 1) w x) = fun x => cfn K k w x := by
          funext x
          rw [cfn_succ, if_neg hB, if_neg hA]
        rw [hc]
        rcases ih (by omega) w with h | h | ⟨j, h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨j, by omega, h2, h3⟩)

lemma avail_opd {N : ℕ} (K : Ctx N) (k : ℕ) (c : (Fin N → Bool) → Bool) (h : Avail K k c)
    (r : ℕ) (hr : K.C.gates.length + 5 * k ≤ r) : Opd (nf K) (nrank K) r c := by
  rcases h with h | h | ⟨j, h1, h2, h3 | h3⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · refine Or.inl ⟨(⟨j, h2⟩, ⟨2, by omega⟩), ?_, h3⟩
    simp only [nrank]
    rw [if_neg (by omega)]
    omega
  · refine Or.inl ⟨(⟨j, h2⟩, ⟨4, by omega⟩), ?_, h3⟩
    simp only [nrank]
    rw [if_neg (by omega)]
    omega

lemma p0_opd {N : ℕ} (K : Ctx N) (hK : OK K) (w j : ℕ) (hw : w < K.n + j)
    (hj : j ≤ K.C.gates.length) (r : ℕ) (hr : j ≤ r) : Opd (nf K) (nrank K) r (p0f K w) := by
  by_cases h1 : w < K.n
  · cases hl : K.isLine w
    · obtain ⟨a, rfl⟩ := hK.2.2.2.2.2.1 w h1 hl
      refine Or.inr (Or.inl ⟨a, ?_⟩)
      funext x
      unfold p0f
      rw [Pz_lt K _ _ _ h1, hl]
      simp only [Bool.false_eq_true, if_false]
      exact zf_wa K hK x _ a
    · refine Or.inr (Or.inr (Or.inl ?_))
      funext x
      unfold p0f
      rw [Pz_lt K _ _ _ h1, hl]
      rfl
  · obtain ⟨j', rfl⟩ : ∃ j', w = K.n + j' := ⟨w - K.n, by omega⟩
    refine Or.inl ⟨(⟨j', by omega⟩, ⟨0, by omega⟩), ?_, rfl⟩
    simp only [nrank, if_true]
    omega

lemma ov_opd {N : ℕ} (K : Ctx N) (hK : OK K) (kk : Bool) (O : Option ℕ) (j : ℕ)
    (hO : ∀ a, O = some a → a < K.n + j) (hj : j ≤ K.C.gates.length) (r : ℕ) (hr : j ≤ r) :
    Opd (nf K) (nrank K) r (fun x => ov kk (fun w => p0f K w x) O) := by
  cases O with
  | none =>
    cases kk
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  | some a => exact p0_opd K hK a j (hO a rfl) hj r hr

lemma cof_opd {N : ℕ} (K : Ctx N) (hK : OK K) (kk : Bool) (O : Option ℕ) (j : ℕ)
    (hO : ∀ a, O = some a → a < K.n + j) (hj : j ≤ K.C.gates.length) (r : ℕ) (hr : j ≤ r) :
    Opd (nf K) (nrank K) r (fun x => cof kk (fun w => p0f K w x) O) := by
  cases kk
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact ov_opd K hK true O j hO hj r hr

lemma o1_opd {N : ℕ} (K : Ctx N) (k : ℕ) (hk : k ≤ K.C.gates.length) (O : Option ℕ) (r : ℕ)
    (hr : K.C.gates.length + 5 * k ≤ r) :
    Opd (nf K) (nrank K) r (fun x => o1 (fun w => cfn K k w x) O) := by
  cases O with
  | none => exact Or.inr (Or.inr (Or.inl rfl))
  | some a => exact avail_opd K k _ (avail K k hk a) r hr

lemma nf_closed {N : ℕ} (K : Ctx N) (hK : OK K) : Closed (nf K) (nrank K) := by
  rintro ⟨⟨j, hj⟩, ⟨s, hs⟩⟩
  have hgk := gk_eq K.C j hj
  have hA : ∀ a, (gk K.C j).inputs[0]? = some a → a < K.n + j := by
    intro a ha
    rw [hgk] at ha
    exact opd_lt K.C _ hK.1 j hj 0 a ha
  have hB : ∀ a, (gk K.C j).inputs[1]? = some a → a < K.n + j := by
    intro a ha
    rw [hgk] at ha
    exact opd_lt K.C _ hK.1 j hj 1 a ha
  have hk : K.C.gates.length - 1 - j ≤ K.C.gates.length := by omega
  have hr : nrank K (⟨j, hj⟩, ⟨s, hs⟩) =
      if s = 0 then j else K.C.gates.length + 5 * (K.C.gates.length - 1 - j) + s := rfl
  rw [hr]
  interval_cases s
  · rw [if_pos rfl]
    have hf : nf K (⟨j, hj⟩, ⟨0, hs⟩) = fun x => bop (isAnd (gk K.C j))
        (ov (isAnd (gk K.C j)) (fun w => p0f K w x) (gk K.C j).inputs[0]?)
        (ov (isAnd (gk K.C j)) (fun w => p0f K w x) (gk K.C j).inputs[1]?) := by
      funext x
      rw [hgk]
      exact p0f_gate K hK j hj x
    rw [hf]
    refine ⟨_, _, ov_opd K hK (isAnd (gk K.C j)) _ j hA (by omega) j le_rfl,
      ov_opd K hK (isAnd (gk K.C j)) _ j hB (by omega) j le_rfl, ?_⟩
    cases isAnd (gk K.C j)
    · left
      rfl
    · right
      rfl
  · rw [if_neg (by omega)]
    exact ⟨_, _, avail_opd K _ _ (avail K _ hk (K.n + j)) _ (by omega),
      cof_opd K hK (isAnd (gk K.C j)) _ j hB (by omega) _ (by omega), Or.inr rfl⟩
  · rw [if_neg (by omega)]
    refine ⟨_, _, o1_opd K _ hk (gk K.C j).inputs[0]? _ (by omega),
      Or.inl ⟨(⟨j, hj⟩, ⟨1, by omega⟩), ?_, rfl⟩, Or.inl rfl⟩
    simp only [nrank]
    rw [if_neg (by omega)]
    omega
  · rw [if_neg (by omega)]
    exact ⟨_, _, avail_opd K _ _ (avail K _ hk (K.n + j)) _ (by omega),
      cof_opd K hK (isAnd (gk K.C j)) _ j hA (by omega) _ (by omega), Or.inr rfl⟩
  · rw [if_neg (by omega)]
    have key : ∀ A B : Option ℕ, A = (gk K.C j).inputs[0]? →
        Opd (nf K) (nrank K) (K.C.gates.length + 5 * (K.C.gates.length - 1 - j) + 4)
          (fun x => o1 (updOpt (fun w => cfn K (K.C.gates.length - 1 - j) w x) A
            (v1 K (K.C.gates.length - 1 - j) j x)) B) := by
      intro A B hAe
      cases B with
      | none => exact Or.inr (Or.inr (Or.inl rfl))
      | some b =>
        cases A with
        | none => exact avail_opd K _ _ (avail K _ hk b) _ (by omega)
        | some a =>
          by_cases hba : b = a
          · refine Or.inl ⟨(⟨j, hj⟩, ⟨2, by omega⟩), ?_, ?_⟩
            · simp only [nrank]
              rw [if_neg (by omega)]
              omega
            · funext x
              show _ = n2 K (K.C.gates.length - 1 - j) j x
              unfold n2
              rw [← hAe]
              simp [updOpt, o1, hba]
          · have hc : (fun x => o1 (updOpt (fun w => cfn K (K.C.gates.length - 1 - j) w x) (some a)
                (v1 K (K.C.gates.length - 1 - j) j x)) (some b)) =
                fun x => cfn K (K.C.gates.length - 1 - j) b x := by
              funext x
              simp [updOpt, o1, hba]
            rw [hc]
            exact avail_opd K _ _ (avail K _ hk b) _ (by omega)
    refine ⟨_, _, key _ (gk K.C j).inputs[1]? rfl,
      Or.inl ⟨(⟨j, hj⟩, ⟨3, by omega⟩), ?_, rfl⟩, Or.inl rfl⟩
    simp only [nrank]
    rw [if_neg (by omega)]
    omega

theorem side_count {N : ℕ} (K : Ctx N) (hK : OK K) (J : Fin N → Fin N → Prop)
    (hJ : ∀ a1 a2 b1 b2, a1 ≠ a2 → J a1 b1 → J a2 b1 → J a1 b2 → J a2 b2 → b1 = b2)
    (hsem : ∀ x y, W K.C (zin K x y) K.C.output = true → ∃ a b, J a b ∧ x a = true ∧ y b = true) :
    (Finset.univ.filter (fun e : Fin N × Fin N =>
      (P K.C K.isLine (zin K (unit e.1) (unit e.2)) K.C.output).2 = true)).card ≤
      5 * K.C.gates.length + N := by
  have h := slp_count J hJ (nf K) (nrank K) (nf_closed K hK)
    (fun b x => cfn K K.C.gates.length (K.wb b) x)
    (fun b => ⟨K.C.gates.length + 5 * K.C.gates.length,
      avail_opd K _ _ (avail K _ le_rfl (K.wb b)) _ le_rfl⟩)
    (fun b x hx => by
      obtain ⟨a, b', hJ', hxa, hb'⟩ := hsem x (unit b) (deriv_le K hK x b hx)
      simp only [unit, decide_eq_true_eq] at hb'
      rw [hb'] at hJ'
      exact ⟨a, hJ', hxa⟩)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  have e : (Finset.univ.filter (fun e : Fin N × Fin N =>
      (P K.C K.isLine (zin K (unit e.1) (unit e.2)) K.C.output).2 = true)) =
      (Finset.univ.filter (fun e : Fin N × Fin N =>
        cfn K K.C.gates.length (K.wb e.2) (unit e.1) = true)) := by
    apply Finset.filter_congr
    intro e _
    rw [deriv_eq K hK (unit e.1) e.2]
  rw [e]
  omega

/-! Part 6: the two sides of the plane and the count -/

def KL (N : ℕ) (C : Circuit) : Ctx N :=
  ⟨C, fun w => decide (N ≤ w), N + N, fun a => a.val, fun b => N + b.val⟩

def KP (N : ℕ) (C : Circuit) : Ctx N :=
  ⟨C, fun w => !decide (N ≤ w), N + N, fun a => N + a.val, fun b => b.val⟩

lemma good_of (C : Circuit) (n : ℕ) (h1 : PEqualNP.ReadK.AndOrFanInTwo C)
    (h2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) : Good C n := by
  intro k hk
  refine ⟨h1.1 _ (List.getElem_mem hk), h1.2 _ (List.getElem_mem hk), ?_⟩
  intro j hj
  apply h2 k hk j
  simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk, Option.getD_some]
  exact hj

lemma okL (N : ℕ) (C : Circuit) (hg : Good C (N + N)) : OK (KL N C) := by
  refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    show a.val < N + N ∧ decide (N ≤ a.val) = false
    exact ⟨by omega, by simp⟩
  · intro b
    show N + b.val < N + N ∧ decide (N ≤ N + b.val) = true
    exact ⟨by omega, by simp⟩
  · intro a a' h
    exact Fin.ext h
  · intro b b' h
    have h' : N + b.val = N + b'.val := h
    exact Fin.ext (by omega)
  · intro w hw hl
    have hl' : decide (N ≤ w) = false := hl
    have : w < N := by simpa using hl'
    exact ⟨⟨w, this⟩, rfl⟩
  · intro w hw hl
    have hl' : decide (N ≤ w) = true := hl
    have h3 : N ≤ w := by simpa using hl'
    have hw' : w < N + N := hw
    refine ⟨⟨w - N, by omega⟩, ?_⟩
    show N + (w - N) = w
    omega

lemma okP (N : ℕ) (C : Circuit) (hg : Good C (N + N)) : OK (KP N C) := by
  refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    show N + a.val < N + N ∧ (!decide (N ≤ N + a.val)) = false
    exact ⟨by omega, by simp⟩
  · intro b
    show b.val < N + N ∧ (!decide (N ≤ b.val)) = true
    exact ⟨by omega, by simp⟩
  · intro b b' h
    have h' : N + b.val = N + b'.val := h
    exact Fin.ext (by omega)
  · intro a a' h
    exact Fin.ext h
  · intro w hw hl
    have hl' : (!decide (N ≤ w)) = false := hl
    have h3 : N ≤ w := by simpa using hl'
    have hw' : w < N + N := hw
    refine ⟨⟨w - N, by omega⟩, ?_⟩
    show N + (w - N) = w
    omega
  · intro w hw hl
    have hl' : (!decide (N ≤ w)) = true := hl
    have : w < N := by simpa using hl'
    exact ⟨⟨w, this⟩, rfl⟩

lemma unit_ex {N : ℕ} (g : Fin N → ℕ) (a : Fin N) (i : ℕ) :
    (∃ a' : Fin N, g a' = i ∧ unit a a' = true) ↔ i = g a := by
  simp only [unit, decide_eq_true_eq]
  constructor
  · rintro ⟨a', h, rfl⟩
    exact h.symm
  · intro h
    exact ⟨a, h.symm, rfl⟩

lemma zinL (N : ℕ) (C : Circuit) (a b : Fin N) :
    zin (KL N C) (unit a) (unit b) =
      (List.range (N + N)).map (fun i => i == a.val || i == N + b.val) := by
  unfold zin
  apply List.map_congr_left
  intro i _
  show (decide (∃ a' : Fin N, a'.val = i ∧ unit a a' = true) ||
    decide (∃ b' : Fin N, N + b'.val = i ∧ unit b b' = true)) = (i == a.val || i == N + b.val)
  rw [decide_eq_decide.mpr (unit_ex (fun a' : Fin N => a'.val) a i),
    decide_eq_decide.mpr (unit_ex (fun b' : Fin N => N + b'.val) b i)]
  rfl

lemma zinP (N : ℕ) (C : Circuit) (a b : Fin N) :
    zin (KP N C) (unit a) (unit b) =
      (List.range (N + N)).map (fun i => i == b.val || i == N + a.val) := by
  unfold zin
  apply List.map_congr_left
  intro i _
  show (decide (∃ a' : Fin N, N + a'.val = i ∧ unit a a' = true) ||
    decide (∃ b' : Fin N, b'.val = i ∧ unit b b' = true)) = (i == b.val || i == N + a.val)
  rw [decide_eq_decide.mpr (unit_ex (fun a' : Fin N => N + a'.val) a i),
    decide_eq_decide.mpr (unit_ex (fun b' : Fin N => b'.val) b i), Bool.or_comm]
  rfl

lemma range_ofFn (n : ℕ) (g : ℕ → Bool) :
    (List.range n).map g = List.ofFn (fun w : Fin n => g w.val) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

def lyf (N : ℕ) (C : Circuit) (e : Fin N × Fin N) : Bool :=
  PEqualNP.ReadK.lineSingle C (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val)

def lxf (N : ℕ) (C : Circuit) (e : Fin N × Fin N) : Bool :=
  PEqualNP.ReadK.lineSingle C (N + N) (fun i => !decide (N ≤ i)) e.1.val (N + e.2.val)

lemma lyf_eq (N : ℕ) (C : Circuit) (e : Fin N × Fin N) :
    lyf N C e = (P (KL N C).C (KL N C).isLine (zin (KL N C) (unit e.1) (unit e.2))
      (KL N C).C.output).2 := by
  rw [zinL]
  rfl

lemma lxf_eq (N : ℕ) (C : Circuit) (e : Fin N × Fin N) :
    lxf N C e = (P (KP N C).C (KP N C).isLine (zin (KP N C) (unit e.2) (unit e.1))
      (KP N C).C.output).2 := by
  rw [zinP]
  rfl

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1)
    (hao : PEqualNP.ReadK.AndOrFanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
      decide (∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧
        z (Fin.natAdd N l3) = true)) :
    N * q ≤ 32 * C.size + 3 * N + (PEqualNP.ReadK.doubleReread C (N + N)
      (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 =>
        ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map
          (fun l6 => (p5.val, N + l6.val))))).length := by
  classical
  have hg : Good C (N + N) := good_of C _ hao hrb
  have hKL := okL N C hg
  have hKP := okP N C hg
  have hJ1 : ∀ a1 a2 b1 b2 : Fin N, a1 ≠ a2 → I a1 b1 → I a2 b1 → I a1 b2 → I a2 b2 →
      b1 = b2 := by
    intro a1 a2 b1 b2 hne h1 h2 h3 h4
    obtain ⟨l, _, hl⟩ := huniq a1 a2 hne
    rw [hl b1 ⟨h1, h2⟩, hl b2 ⟨h3, h4⟩]
  have hJ2 : ∀ a1 a2 b1 b2 : Fin N, a1 ≠ a2 → I b1 a1 → I b1 a2 → I b2 a1 → I b2 a2 →
      b1 = b2 := by
    intro a1 a2 b1 b2 hne h1 h2 h3 h4
    by_contra hb
    exact hne (hJ1 b1 b2 a1 a2 hb h1 h3 h2 h4)
  have hsem : ∀ g : ℕ → Bool, W C ((List.range (N + N)).map g) C.output = true →
      ∃ p l : Fin N, I p l ∧ g p.val = true ∧ g (N + l.val) = true := by
    intro g hW
    rw [range_ofFn] at hW
    have h2 : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun w : Fin (N + N) => g w.val) =
        true := hW
    rw [hfun] at h2
    simp only [decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd] at h2
    exact h2
  have cL := side_count (KL N C) hKL I hJ1 (by
    intro x y hW
    obtain ⟨p, l, hI, h1, h2⟩ := hsem (zf (KL N C) x y) hW
    have e1 : zf (KL N C) x y p.val = x p := zf_wa (KL N C) hKL x y p
    have e2 : zf (KL N C) x y (N + l.val) = y l := zf_wb (KL N C) hKL x y l
    rw [e1] at h1
    rw [e2] at h2
    exact ⟨p, l, hI, h1, h2⟩)
  have cP := side_count (KP N C) hKP (fun a b => I b a) hJ2 (by
    intro x y hW
    obtain ⟨p, l, hI, h1, h2⟩ := hsem (zf (KP N C) x y) hW
    have e1 : zf (KP N C) x y p.val = y p := zf_wb (KP N C) hKP x y p
    have e2 : zf (KP N C) x y (N + l.val) = x l := zf_wa (KP N C) hKP x y l
    rw [e1] at h1
    rw [e2] at h2
    exact ⟨l, p, hI, h2, h1⟩)
  have hm : (KL N C).C.gates.length = C.size := rfl
  have hm' : (KP N C).C.gates.length = C.size := rfl
  rw [hm] at cL
  rw [hm'] at cP
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let Ey : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => lyf N C e = true)
  let Ex : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => lxf N C e = true)
  let Ed : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun e => I e.1 e.2 ∧ lyf N C e = false ∧ lxf N C e = false)
  -- the number of incidences: adapted from R_meta_1942_1
  have hE_eq : E = (Finset.univ : Finset (Fin N)).biUnion
      (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    ext ⟨p, l⟩
    simp [E]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
      (fun l : Fin N => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    intro l1 _ l2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨p2, _, heq⟩ := Finset.mem_image.mp hx2
    exact hne (Prod.mk.inj heq).2.symm
  have hE_card : E.card = N * (q + 1) := by
    rw [hE_eq, Finset.card_biUnion hdisj]
    have hach : ∀ l : Fin N, ((Finset.univ.filter (fun p : Fin N => I p l)).image
        (fun p => (p, l))).card = q + 1 := by
      intro l
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), hline l]
    simp [hach]
  have hEy : Ey.card ≤ 5 * C.size + N := by
    have e : Ey = Finset.univ.filter (fun e : Fin N × Fin N =>
        (P (KL N C).C (KL N C).isLine (zin (KL N C) (unit e.1) (unit e.2))
          (KL N C).C.output).2 = true) := by
      apply Finset.filter_congr
      intro e _
      rw [lyf_eq]
    rw [e]
    exact cL
  have hEx : Ex.card ≤ 5 * C.size + N := by
    refine le_trans ?_ cP
    apply Finset.card_le_card_of_injOn Prod.swap
    · intro e he
      simp only [Ex, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Prod.fst_swap,
        Prod.snd_swap]
      rw [← lxf_eq]
      exact he
    · intro e1 _ e2 _ h
      exact Prod.swap_injective h
  have hEd : Ed.card ≤ (PEqualNP.ReadK.doubleReread C (N + N)
      (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 =>
        ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map
          (fun l6 => (p5.val, N + l6.val))))).length := by
    refine le_trans ?_ (List.toFinset_card_le _)
    have hinj : Function.Injective (fun e : Fin N × Fin N => (e.1.val, N + e.2.val)) := by
      intro e1 e2 h
      have h1 := (Prod.mk.inj h).1
      have h2 := (Prod.mk.inj h).2
      exact Prod.ext (Fin.ext h1) (Fin.ext (by omega))
    rw [← Finset.card_image_of_injective Ed hinj]
    apply Finset.card_le_card
    intro u hu
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
    simp only [Ed, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hI, h1, h2⟩ := he
    rw [List.mem_toFinset]
    unfold PEqualNP.ReadK.doubleReread
    rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [List.mem_flatMap]
      refine ⟨e.1, List.mem_finRange _, ?_⟩
      rw [List.mem_map]
      refine ⟨e.2, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨List.mem_finRange _, by simpa using hI⟩
    · show (!(lyf N C e) && !(lxf N C e)) = true
      rw [h1, h2]
      rfl
  have hsub : E ⊆ (Ey ∪ Ex) ∪ Ed := by
    intro e he
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [Finset.mem_union, Ey, Ex, Ed, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hy : lyf N C e
    · cases hx : lxf N C e
      · exact Or.inr ⟨he, rfl, rfl⟩
      · exact Or.inl (Or.inr rfl)
    · exact Or.inl (Or.inl rfl)
  have hcov : E.card ≤ Ey.card + Ex.card + Ed.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Ey ∪ Ex) Ed
    have h3 := Finset.card_union_le Ey Ex
    omega
  have hmul : N * (q + 1) = N * q + N := by ring
  omega

end PEqualNP.Outside.L_meta_2672_aux

theorem PEqualNP.Outside.L_meta_2672 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1) → PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true)) → N * q ≤ 32 * C.size + 3 * N + (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))).length := by
  intro q N I _ C _ hN hline huniq hao hrb hfun
  exact PEqualNP.Outside.L_meta_2672_aux.main q N I C hN hline huniq hao hrb hfun
