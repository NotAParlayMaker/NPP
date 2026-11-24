import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2482

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem wires_eq (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    wireVal n C w x = val C.gates w x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → val C.gates (n + j) x = true → val C.gates b x = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hv
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hv
      exact hv
    · rw [gateAt_eq C k hk] at hop hi
      exact (val_or C.gates x k hk hop).2 ⟨i, hi, hlt, ih i (by omega) hr hv⟩

theorem mem_filter' {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

theorem in_two {l : List ℕ} (hl : l.length = 2) {w : ℕ} (hw : w ∈ l) :
    w = l.getD 0 0 ∨ w = l.getD 1 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hw ⊢
    exact hw
  · simp at hl

theorem gate_mem (C : Circuit) {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

def Sh (n M : ℕ) (lw : Fin M → ℕ) (C : Circuit) (w : ℕ) : Set (Fin M) :=
  {m | wireVal n C w (fun k : Fin n => decide (k.val = lw m)) = true}

theorem sh_reach (n M : ℕ) (lw : Fin M → ℕ) (C : Circuit) (b j : ℕ) (h : OrReaches n C b j) :
    Sh n M lw C (n + j) ⊆ Sh n M lw C b := by
  intro m hm
  have hm2 : val C.gates (n + j) (fun k : Fin n => decide (k.val = lw m)) = true := hm
  show val C.gates b (fun k : Fin n => decide (k.val = lw m)) = true
  exact reach_up n C (fun k : Fin n => decide (k.val = lw m)) j b h hm2

theorem sh_in (n M : ℕ) (lw : Fin M → ℕ) (C : Circuit) (k i : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hi : i ∈ (gateAt C k).inputs) (hlt : i < n + k) :
    Sh n M lw C i ⊆ Sh n M lw C (n + k) := by
  intro m hm
  have hm2 : val C.gates i (fun k : Fin n => decide (k.val = lw m)) = true := hm
  show val C.gates (n + k) (fun k : Fin n => decide (k.val = lw m)) = true
  rw [gateAt_eq C k hk] at hop hi
  exact (val_or C.gates (fun k : Fin n => decide (k.val = lw m)) k hk hop).2 ⟨i, hi, hlt, hm2⟩

theorem walk (n : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2) (Q : ℕ → Prop)
    (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → Q (n + j) → ¬ Q b →
      ∃ k, ∃ c : Bool, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        (gateAt C k).inputs.getD (cond c 1 0) 0 ∈ (gateAt C k).inputs ∧
        Q ((gateAt C k).inputs.getD (cond c 1 0) 0) ∧ ¬ Q (n + k) ∧ OrReaches n C b k := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hQ hnQ
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h hnQ ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hQ
      exact absurd hQ hnQ
    · have hself : OrReaches n C (n + k) k := (orReaches_iff n C k k).2 ⟨hk, Or.inl rfl⟩
      by_cases hQi : Q i
      · rcases in_two (hlen _ (gate_mem C hk)) hi with h2 | h2
        · rw [h2] at hi hQi
          exact ⟨k, false, hk, hop, hi, hQi, hnQ, hself⟩
        · rw [h2] at hi hQi
          exact ⟨k, true, hk, hop, hi, hQi, hnQ, hself⟩
      · obtain ⟨k2, c, hk2, hop2, hin2, hQ2, hnQ2, hr2⟩ := ih i (by omega) hr hQ hQi
        exact ⟨k2, c, hk2, hop2, hin2, hQ2, hnQ2,
          (orReaches_iff n C k k2).2 ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr2⟩⟩⟩

theorem climb (n : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2) (Q : ℕ → Prop)
    (a b : ℕ)
    (h : (∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C b) ∨
      (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C b j_1))
    (hQ : Q a) (hnQ : ¬ Q b) :
    ∃ k, ∃ c : Bool, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      (gateAt C k).inputs.getD (cond c 1 0) 0 ∈ (gateAt C k).inputs ∧
      Q ((gateAt C k).inputs.getD (cond c 1 0) 0) ∧ ¬ Q (n + k) ∧ OrReaches n C b k := by
  rcases h with ⟨i, hia, hi⟩ | ⟨j, haj, hr⟩
  · have hi2 : (i : ℕ) = b ∨ ∃ k < C.gates.length,
        OrReaches n C b k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs :=
      ((mem_filter' _ _ _ _).mp hi).2
    rcases hi2 with h1 | ⟨k, hk, hr, hop, hin⟩
    · rw [← hia, h1] at hQ
      exact absurd hQ hnQ
    · by_cases hQk : Q (n + k)
      · exact walk n C hlen Q k b hr hQk hnQ
      · rw [hia] at hin
        rcases in_two (hlen _ (gate_mem C hk)) hin with h2 | h2
        · rw [h2] at hin hQ
          exact ⟨k, false, hk, hop, hin, hQ, hQk, hr⟩
        · rw [h2] at hin hQ
          exact ⟨k, true, hk, hop, hin, hQ, hQk, hr⟩
  · rw [haj] at hQ
    exact walk n C hlen Q j b hr hQ hnQ

theorem count (n N M : ℕ) (C : Circuit) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (hC : IsAO2 n C)
    (hK : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (G : Set (Fin N × Fin M))
    (hG : ∀ e ∈ G, ∃ a F, ((∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C F) ∨
        (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C F j_1)) ∧
      Sh n M lw C a = {e.2} ∧ Sh n M lw C F ⊆ {m | I e.1 m} ∧ 2 ≤ (Sh n M lw C F).ncard) :
    G.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by
  classical
  obtain ⟨_, hrb, hlen⟩ := hC
  have hOf : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun j hj => hj.1)
  have hex : ∀ e ∈ G, ∃ jb : ℕ × Bool,
      jb.1 ∈ {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} ∧
      Sh n M lw C ((gateAt C jb.1).inputs.getD (cond jb.2 1 0) 0) = {e.2} ∧
      (∀ m ∈ Sh n M lw C (n + jb.1), I e.1 m) ∧
      ∃ m1 m2, m1 ∈ Sh n M lw C (n + jb.1) ∧ m2 ∈ Sh n M lw C (n + jb.1) ∧ m1 ≠ m2 := by
    intro e he
    obtain ⟨a, F, hbel, hSa, hSF, h2⟩ := hG e he
    have hnF : ¬ (Sh n M lw C F = {e.2}) := by
      intro hh
      rw [hh, Set.ncard_singleton] at h2
      omega
    obtain ⟨k, c, hk, hop, hin, hQ, hnQ, hr⟩ :=
      climb n C hlen (fun w => Sh n M lw C w = {e.2}) a F hbel hSa hnF
    have hQ1 : Sh n M lw C ((gateAt C k).inputs.getD (cond c 1 0) 0) = {e.2} := hQ
    have hnQ1 : ¬ (Sh n M lw C (n + k) = {e.2}) := hnQ
    have hsub : Sh n M lw C ((gateAt C k).inputs.getD (cond c 1 0) 0) ⊆ Sh n M lw C (n + k) :=
      sh_in n M lw C k _ hk hop hin (hrb k hk _ hin)
    have hl : e.2 ∈ Sh n M lw C (n + k) := by
      apply hsub
      rw [hQ1]
      exact Set.mem_singleton _
    have hex2 : ∃ m ∈ Sh n M lw C (n + k), m ≠ e.2 := by
      by_contra hcon
      push_neg at hcon
      apply hnQ1
      ext m
      constructor
      · intro hm
        exact Set.mem_singleton_iff.mpr (hcon m hm)
      · intro hm
        rw [Set.mem_singleton_iff.mp hm]
        exact hl
    obtain ⟨m, hm, hne⟩ := hex2
    exact ⟨(k, c), ⟨hk, hop⟩, hQ1, fun m' hm' => hSF (sh_reach n M lw C F k hr hm'),
      e.2, m, hl, hm, Ne.symm hne⟩
  choose! f hf using hex
  calc G.ncard
      ≤ (((fun j : ℕ => (j, true)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}) ∪
          ((fun j : ℕ => (j, false)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or})).ncard := by
        refine Set.ncard_le_ncard_of_injOn f ?_ ?_ ((hOf.image _).union (hOf.image _))
        · intro e he
          have hm := (hf e he).1
          rcases hfe : f e with ⟨j, b⟩
          rw [hfe] at hm
          cases b
          · right
            exact ⟨j, hm, rfl⟩
          · left
            exact ⟨j, hm, rfl⟩
        · intro e he e2 he2 heq
          have h1 := hf e he
          have h2 := hf e2 he2
          rw [← heq] at h2
          obtain ⟨_, hS, hI, m1, m2, hm1, hm2, hne⟩ := h1
          obtain ⟨_, hS2, hI2, _⟩ := h2
          have e3 : e.2 = e2.2 := Set.singleton_injective (hS.symm.trans hS2)
          have e1 : e.1 = e2.1 := by
            by_contra hne1
            exact hK e.1 e2.1 m1 m2 hne1 hne ⟨hI _ hm1, hI2 _ hm1, hI _ hm2, hI2 _ hm2⟩
          exact Prod.ext e1 e3
    _ ≤ ((fun j : ℕ => (j, true)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}).ncard +
          ((fun j : ℕ => (j, false)) '' {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}).ncard :=
        Set.ncard_union_le _ _
    _ ≤ {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard +
          {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard :=
        Nat.add_le_add (Set.ncard_image_le hOf) (Set.ncard_image_le hOf)
    _ = 2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by ring

end PEqualNP.Outside.L_meta_2482

theorem PEqualNP.Outside.L_meta_2482 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ a_1 F_1, ((∃ i_1 : Fin n, i_1.val = a_1 ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∨ (∃ j_1 : ℕ, a_1 = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_1) j_1)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_1 : Fin n => decide (k_1.val = lw a_2)) = true} ⊆ {m_1 | I pl.1 m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_4)) = true}).ncard)) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro n N M pw lw I C A hC hinj hK hA
  rw [← Set.ncard_coe_finset A]
  refine PEqualNP.Outside.L_meta_2482.count n N M C lw I hC hK _ ?_
  intro e he
  exact (hA e (Finset.mem_coe.mp he)).2
