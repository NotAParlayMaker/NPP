import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5625
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- THE PLAN.
-- Read at the 16 inputs with one vertex on each side, a wire is a number: bit 4u+v is its value
-- at left vertex u and right vertex v. The eight input wires are the four rows 15, 240, 3840,
-- 61440 and the four columns 4369, 8738, 17476, 34952. A gate of at most two inputs gives the
-- AND or the OR of two numbers already there, a copy, 0 or 65535. So a circuit with s gates
-- gives a chain of s numbers, each one step from the pool before it, and the graph 829 is in it.
--
-- Upper half: seven gates, x0 and (y0 or y2 or y3), or (x1 or x2) and (y0 or y1).
--
-- Lower half, by two restrictions and one small search.
-- 1. Forget row 2 (keep the bits of 61695). The row x2 becomes 0. Some number of the chain is
--    made from x2 itself: without x2 every number that is on at (2, v) is on at (3, v), and 829
--    is on at (2, 0) and off at (3, 0). The first number made from x2 becomes 0 or a number
--    already there, so the restricted chain is one shorter. It reaches 61.
-- 2. Forget column 3 (keep the bits of 28791). The column y3 becomes 0. Some number is made
--    from y3 itself: without y3 every number on at (u, 3) is on at (u, 1), and 61 is on at
--    (0, 3) and off at (0, 1). Again one number goes, and the chain reaches 53.
-- 3. So six gates would give a chain of four numbers from the pool 7, 112, 28672, 4113, 8226,
--    16452, 0, 28791 that reaches 53. A search over sets of numbers, each set once, finds none,
--    and the kernel runs it.

-- One step from the pool Q: a member of Q, or the AND or the OR of two members.
def Step (Q : List ℕ) (c : ℕ) : Prop :=
  c ∈ Q ∨ ∃ a ∈ Q, ∃ b ∈ Q, c = a &&& b ∨ c = a ||| b

-- A chain from Q: each number is one step from Q and the numbers before it.
def Chain : List ℕ → List ℕ → Prop
  | _, [] => True
  | Q, c :: cs => Step Q c ∧ Chain (c :: Q) cs

theorem chain_nil (Q : List ℕ) : Chain Q [] := trivial

theorem chain_cons_iff (Q : List ℕ) (c : ℕ) (cs : List ℕ) :
    Chain Q (c :: cs) ↔ Step Q c ∧ Chain (c :: Q) cs := Iff.rfl

theorem step_mono {Q Q' : List ℕ} (h : ∀ x ∈ Q, x ∈ Q') {c : ℕ} (hc : Step Q c) : Step Q' c := by
  rcases hc with hc | ⟨a, ha, b, hb, hab⟩
  · exact Or.inl (h c hc)
  · exact Or.inr ⟨a, h a ha, b, h b hb, hab⟩

theorem chain_mono : ∀ (cs Q Q' : List ℕ), (∀ x ∈ Q, x ∈ Q') → Chain Q cs → Chain Q' cs
  | [], _, Q', _, _ => chain_nil Q'
  | c :: cs, Q, Q', h, hc => by
    obtain ⟨h1, h2⟩ := (chain_cons_iff Q c cs).mp hc
    refine (chain_cons_iff Q' c cs).mpr ⟨step_mono h h1, chain_mono cs (c :: Q) (c :: Q') ?_ h2⟩
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · rw [hx]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h x hx)

-- FROM A CIRCUIT TO A CHAIN.

-- Input number p: left vertex p / 4 and right vertex p mod 4 on.
def X (p : Fin 16) : List Bool :=
  oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4)

theorem X_len (p : Fin 16) : (X p).length = 8 := by simp [X, oneEach]

-- Every wire of the lists ws, read at the 16 inputs, is a member of Q.
def Inv (Q : List ℕ) (ws : Fin 16 → List Bool) : Prop :=
  ∀ i : ℕ, ∃ m ∈ Q, ∀ p : Fin 16, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem testBit_65535 : ∀ p : Fin 16, (65535 : ℕ).testBit p = true := by decide

theorem gate_vec (Q : List ℕ) (ws : Fin 16 → List Bool) (h : Inv Q ws) (h0 : 0 ∈ Q)
    (h1 : 65535 ∈ Q) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    ∃ c, Step Q c ∧ ∀ p : Fin 16,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · exact ⟨65535, Or.inl h1, fun p => by simp [GateOp.eval, testBit_65535 p]⟩
    · exact ⟨0, Or.inl h0, fun p => by simp [GateOp.eval]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    refine ⟨ma, Or.inl hma, fun p => ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval, ha p]
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    obtain ⟨mb, hmb, hb⟩ := h b
    rcases hop with rfl | rfl
    · exact ⟨ma &&& mb, Or.inr ⟨ma, hma, mb, hmb, Or.inl rfl⟩,
        fun p => by simp [GateOp.eval, ha p, hb p]⟩
    · exact ⟨ma ||| mb, Or.inr ⟨ma, hma, mb, hmb, Or.inr rfl⟩,
        fun p => by simp [GateOp.eval, ha p, hb p]⟩
  | _ :: _ :: _ :: _, hl => simp at hl

theorem inv_step (Q : List ℕ) (ws : Fin 16 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv Q ws) (b : Fin 16 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 16, c.testBit p = b p) :
    Inv (c :: Q) (fun p => ws p ++ [b p]) := by
  intro i
  obtain ⟨m, hm, hmb⟩ := hI i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, List.mem_cons_self, fun p => by rw [getD_snoc, ite_eq_left (hL p).symm, hcv p]⟩
  · exact ⟨m, List.mem_cons_of_mem _ hm,
      fun p => by rw [getD_snoc, ite_eq_right (by rw [hL p]; exact hi), hmb p]⟩

theorem chain_of_gates : ∀ (gs : List Gate) (Q : List ℕ) (ws : Fin 16 → List Bool) (L : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ p, (ws p).length = L) → Inv Q ws → 0 ∈ Q → 65535 ∈ Q →
    ∃ cs : List ℕ, cs.length = gs.length ∧ Chain Q cs ∧
      ∀ i : ℕ, ∃ m, (m ∈ cs ∨ m ∈ Q) ∧ ∀ p : Fin 16, m.testBit p =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (ws p)).getD i false
  | [], Q, ws, L, _, _, hI, _, _ => by
    refine ⟨[], rfl, chain_nil Q, fun i => ?_⟩
    obtain ⟨m, hm, hmb⟩ := hI i
    exact ⟨m, Or.inr hm, hmb⟩
  | g :: gs, Q, ws, L, hg, hL, hI, h0, h1 => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec Q ws hI h0 h1 g hop hlen
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 :=
      fun p => by simp [hL p]
    obtain ⟨cs, hlen', hch, hfin⟩ := chain_of_gates gs (c :: Q) _ (L + 1) hg' hL'
      (inv_step Q ws L hL hI _ c hcv) (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1)
    refine ⟨c :: cs, by simp [hlen'], (chain_cons_iff Q c cs).mpr ⟨hc, hch⟩, fun i => ?_⟩
    obtain ⟨m, hm, hmb⟩ := hfin i
    refine ⟨m, ?_, fun p => ?_⟩
    · rcases hm with hm | hm
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · rcases List.mem_cons.mp hm with hm | hm
        · exact Or.inl (by rw [hm]; exact List.mem_cons_self)
        · exact Or.inr hm
    · have h3 := hmb p
      rw [List.foldl_cons]
      exact h3

def pool0 : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952, 0, 65535]

theorem inv0 : Inv pool0 X := by
  intro i
  by_cases hi : i < 8
  · have key : ∀ j : Fin 8, ∀ p : Fin 16, (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by simp [pool0], fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

theorem chain_of_rep (T : ℕ) (hT : T < 65536) (C : Circuit) (hC : Monotone2 C)
    (hrep : Represents (fun u v : Fin 4 => T.testBit (4 * u.val + v.val)) C) :
    ∃ cs : List ℕ, cs.length = C.gates.length ∧ Chain pool0 cs ∧
      ∃ m, (m ∈ cs ∨ m ∈ pool0) ∧ m % 65536 = T := by
  obtain ⟨cs, hlen, hch, hfin⟩ := chain_of_gates C.gates pool0 X 8 hC X_len inv0
    (by decide) (by decide)
  obtain ⟨m, hm, hmb⟩ := hfin C.output
  refine ⟨cs, hlen, hch, m, hm, ?_⟩
  have hbits : ∀ p : Fin 16, m.testBit p = T.testBit p := by
    intro p
    have h := hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
    have he : T.testBit (4 * (p.val / 4) + p.val % 4) = T.testBit p := by
      rw [Nat.div_add_mod p.val 4]
    exact (hmb p).trans (h.trans he)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (65536 : ℕ) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow]
  by_cases hi : i < 16
  · simp only [hi, decide_true, Bool.true_and]
    exact hbits ⟨i, hi⟩
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_lt_two_pow
    calc T < 2 ^ 16 := hT
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)

-- FORGETTING A ROW OR A COLUMN.

-- At every pair (i, j) of ps, bit i of g on forces bit j of g on.
def impl (ps : List (ℕ × ℕ)) (g : ℕ) : Bool := ps.all fun p => !g.testBit p.1 || g.testBit p.2

theorem impl_and (ps : List (ℕ × ℕ)) (a b : ℕ) (ha : impl ps a = true) (hb : impl ps b = true) :
    impl ps (a &&& b) = true := by
  simp only [impl, List.all_eq_true] at ha hb ⊢
  intro p hp
  have h1 := ha p hp
  have h2 := hb p hp
  simp only [Nat.testBit_and]
  revert h1 h2
  generalize a.testBit p.1 = x1
  generalize a.testBit p.2 = x2
  generalize b.testBit p.1 = y1
  generalize b.testBit p.2 = y2
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> decide

theorem impl_or (ps : List (ℕ × ℕ)) (a b : ℕ) (ha : impl ps a = true) (hb : impl ps b = true) :
    impl ps (a ||| b) = true := by
  simp only [impl, List.all_eq_true] at ha hb ⊢
  intro p hp
  have h1 := ha p hp
  have h2 := hb p hp
  simp only [Nat.testBit_or]
  revert h1 h2
  generalize a.testBit p.1 = x1
  generalize a.testBit p.2 = x2
  generalize b.testBit p.1 = y1
  generalize b.testBit p.2 = y2
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> decide

theorem and_and_right (a b D : ℕ) : (a &&& b) &&& D = (a &&& D) &&& (b &&& D) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  generalize a.testBit i = x
  generalize b.testBit i = y
  generalize D.testBit i = z
  cases x <;> cases y <;> cases z <;> rfl

theorem step_map (D : ℕ) {Q : List ℕ} {c : ℕ} (h : Step Q c) :
    Step (Q.map (· &&& D)) (c &&& D) := by
  rcases h with h | ⟨a, ha, b, hb, hab⟩
  · exact Or.inl (List.mem_map_of_mem h)
  · refine Or.inr ⟨a &&& D, List.mem_map_of_mem ha, b &&& D, List.mem_map_of_mem hb, ?_⟩
    rcases hab with hab | hab
    · left; rw [hab]; exact and_and_right a b D
    · right; rw [hab]; exact Nat.and_or_distrib_right a b D

theorem chain_map (D : ℕ) : ∀ (cs Q : List ℕ), Chain Q cs →
    Chain (Q.map (· &&& D)) (cs.map (· &&& D))
  | [], Q, _ => chain_nil _
  | c :: cs, Q, h => by
    obtain ⟨h1, h2⟩ := (chain_cons_iff Q c cs).mp h
    exact (chain_cons_iff _ _ _).mpr ⟨step_map D h1, chain_map D cs (c :: Q) h2⟩

-- Restricting to the bits of D makes the chain one shorter, when z is a member of the pool that
-- D sends to 0, every other member keeps the rule ps, and no number that hits keeps it.
theorem dropOne (D z T' : ℕ) (ps : List (ℕ × ℕ)) (H : ℕ → Prop) (hz : z &&& D = 0)
    (h1 : ∀ m, H m → m ≠ z) (h2 : ∀ m, H m → impl ps m = false)
    (h3 : ∀ m, H m → m &&& D = T') :
    ∀ (cs Q : List ℕ), 0 ∈ Q → (∀ q ∈ Q, q = z ∨ impl ps q = true) → Chain Q cs →
      (∃ m, (m ∈ cs ∨ m ∈ Q) ∧ H m) →
      ∃ cs' : List ℕ, cs'.length + 1 ≤ cs.length ∧ Chain (Q.map (· &&& D)) cs' ∧
        (T' ∈ cs' ∨ T' ∈ Q.map (· &&& D))
  | [], Q, _, hQ, _, ⟨m, hm, hH⟩ => by
    exfalso
    rcases hm with hm | hm
    · exact absurd hm (by simp)
    · rcases hQ m hm with hq | hq
      · exact h1 m hH hq
      · rw [h2 m hH] at hq
        exact Bool.false_ne_true hq
  | c :: cs, Q, h0, hQ, hch, ⟨m, hm, hH⟩ => by
    obtain ⟨hstep, hrest⟩ := (chain_cons_iff Q c cs).mp hch
    have h0' : (0 : ℕ) ∈ Q.map (· &&& D) := List.mem_map.mpr ⟨0, h0, Nat.zero_and D⟩
    have key : (c &&& D) ∈ Q.map (· &&& D) ∨ impl ps c = true := by
      rcases hstep with hc | ⟨a, ha, b, hb, hab⟩
      · exact Or.inl (List.mem_map_of_mem hc)
      · rcases hQ a ha with hza | hia
        · left
          rcases hab with hab | hab
          · have e : c &&& D = 0 := by rw [hab, and_and_right, hza, hz, Nat.zero_and]
            rw [e]; exact h0'
          · have e : c &&& D = b &&& D := by
              rw [hab, Nat.and_or_distrib_right, hza, hz, Nat.zero_or]
            rw [e]; exact List.mem_map_of_mem hb
        · rcases hQ b hb with hzb | hib
          · left
            rcases hab with hab | hab
            · have e : c &&& D = 0 := by rw [hab, and_and_right, hzb, hz, Nat.and_zero]
              rw [e]; exact h0'
            · have e : c &&& D = a &&& D := by
                rw [hab, Nat.and_or_distrib_right, hzb, hz, Nat.or_zero]
              rw [e]; exact List.mem_map_of_mem ha
          · right
            rcases hab with hab | hab
            · rw [hab]; exact impl_and ps a b hia hib
            · rw [hab]; exact impl_or ps a b hia hib
    rcases key with hk | hk
    · refine ⟨cs.map (· &&& D), by simp, ?_, ?_⟩
      · have hmap : Chain ((c &&& D) :: Q.map (· &&& D)) (cs.map (· &&& D)) :=
          chain_map D cs (c :: Q) hrest
        refine chain_mono _ _ _ ?_ hmap
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; exact hk
        · exact hx
      · rw [← h3 m hH]
        rcases hm with hm | hm
        · rcases List.mem_cons.mp hm with hm | hm
          · right; rw [hm]; exact hk
          · left; exact List.mem_map_of_mem hm
        · right; exact List.mem_map_of_mem hm
    · obtain ⟨cs', hlen, hch', hhit⟩ := dropOne D z T' ps H hz h1 h2 h3 cs (c :: Q)
        (List.mem_cons_of_mem _ h0)
        (by
          intro q hq
          rcases List.mem_cons.mp hq with hq | hq
          · right; rw [hq]; exact hk
          · exact hQ q hq)
        hrest
        ⟨m, by
          rcases hm with hm | hm
          · rcases List.mem_cons.mp hm with hm | hm
            · right; rw [hm]; exact List.mem_cons_self
            · left; exact hm
          · right; exact List.mem_cons_of_mem _ hm, hH⟩
      have hch'' : Chain ((c &&& D) :: Q.map (· &&& D)) cs' := hch'
      have hhit' : T' ∈ cs' ∨ T' ∈ (c &&& D) :: Q.map (· &&& D) := hhit
      refine ⟨(c &&& D) :: cs', by simp only [List.length_cons]; omega,
        (chain_cons_iff _ _ _).mpr ⟨step_map D hstep, hch''⟩, ?_⟩
      rcases hhit' with h | h
      · left; exact List.mem_cons_of_mem _ h
      · rcases List.mem_cons.mp h with h | h
        · left; rw [h]; exact List.mem_cons_self
        · right; exact h

-- THE SEARCH.

-- The ANDs and ORs of a with every member of the list, put before acc.
def row (a : ℕ) : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | b :: l, acc => row a l ((a &&& b) :: (a ||| b) :: acc)

-- The ANDs and ORs of every two members at different places, put before acc.
def pairs : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | a :: l, acc => pairs l (row a l acc)

theorem mem_row (a x : ℕ) : ∀ (l acc : List ℕ),
    x ∈ row a l acc ↔ x ∈ acc ∨ ∃ b ∈ l, x = a &&& b ∨ x = a ||| b
  | [], acc => by
    show x ∈ acc ↔ _
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨b, hb, _⟩)
      · exact h
      · exact absurd hb (by simp)
  | b :: l, acc => by
    show x ∈ row a l ((a &&& b) :: (a ||| b) :: acc) ↔ _
    rw [mem_row a x l]
    constructor
    · rintro (h | ⟨b', hb', h⟩)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr ⟨b, List.mem_cons_self, Or.inl h⟩
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr ⟨b, List.mem_cons_self, Or.inr h⟩
          · exact Or.inl h
      · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', h⟩
    · rintro (h | ⟨b', hb', h⟩)
      · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
      · rcases List.mem_cons.mp hb' with hb' | hb'
        · rw [hb'] at h
          rcases h with h | h
          · exact Or.inl (by rw [h]; exact List.mem_cons_self)
          · exact Or.inl (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        · exact Or.inr ⟨b', hb', h⟩

theorem mem_pairs (x : ℕ) : ∀ (Q acc : List ℕ),
    x ∈ pairs Q acc → x ∈ acc ∨ ∃ a ∈ Q, ∃ b ∈ Q, x = a &&& b ∨ x = a ||| b
  | [], _, h => Or.inl h
  | a :: l, acc, h => by
    have h' : x ∈ pairs l (row a l acc) := h
    rcases mem_pairs x l (row a l acc) h' with h1 | ⟨a', ha', b', hb', h1⟩
    · rcases (mem_row a x l acc).mp h1 with h2 | ⟨b, hb, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨a, List.mem_cons_self, b, List.mem_cons_of_mem _ hb, h2⟩
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', h1⟩

theorem acc_sub_pairs (x : ℕ) : ∀ (Q acc : List ℕ), x ∈ acc → x ∈ pairs Q acc
  | [], _, h => h
  | a :: l, acc, h => acc_sub_pairs x l (row a l acc) ((mem_row a x l acc).mpr (Or.inl h))

theorem pairs_complete (a b : ℕ) : ∀ (Q acc : List ℕ), a ∈ Q → b ∈ Q →
    (a &&& b ∈ Q ∨ a &&& b ∈ pairs Q acc) ∧ (a ||| b ∈ Q ∨ a ||| b ∈ pairs Q acc)
  | [], _, ha, _ => absurd ha (by simp)
  | q :: l, acc, ha, hb => by
    rcases List.mem_cons.mp ha with ha | ha
    · rcases List.mem_cons.mp hb with hb | hb
      · rw [ha, hb, Nat.and_self, Nat.or_self]
        exact ⟨Or.inl List.mem_cons_self, Or.inl List.mem_cons_self⟩
      · rw [ha]
        have h1 : q &&& b ∈ row q l acc :=
          (mem_row q _ l acc).mpr (Or.inr ⟨b, hb, Or.inl rfl⟩)
        have h2 : q ||| b ∈ row q l acc :=
          (mem_row q _ l acc).mpr (Or.inr ⟨b, hb, Or.inr rfl⟩)
        exact ⟨Or.inr (acc_sub_pairs _ l _ h1), Or.inr (acc_sub_pairs _ l _ h2)⟩
    · rcases List.mem_cons.mp hb with hb | hb
      · rw [hb]
        have h1 : a &&& q ∈ row q l acc :=
          (mem_row q _ l acc).mpr (Or.inr ⟨a, ha, Or.inl (Nat.and_comm a q)⟩)
        have h2 : a ||| q ∈ row q l acc :=
          (mem_row q _ l acc).mpr (Or.inr ⟨a, ha, Or.inr (Nat.or_comm a q)⟩)
        exact ⟨Or.inr (acc_sub_pairs _ l _ h1), Or.inr (acc_sub_pairs _ l _ h2)⟩
      · obtain ⟨h1, h2⟩ := pairs_complete a b l (row q l acc) ha hb
        constructor
        · rcases h1 with h1 | h1
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr h1
        · rcases h2 with h2 | h2
          · exact Or.inl (List.mem_cons_of_mem _ h2)
          · exact Or.inr h2

def orRow (T a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => (a ||| b == T) || orRow T a l

def andRow (T a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => (a &&& b == T) || andRow T a l

-- Is T the AND or the OR of two members of Q. Only a member below T can be in an OR that
-- gives T, and only a member above T in an AND.
def lastStep (T : ℕ) (Q : List ℕ) : List ℕ → Bool
  | [] => false
  | a :: l => ((a ||| T == T) && orRow T a Q) || ((a &&& T == T) && andRow T a Q)
      || lastStep T Q l

theorem orRow_of (T a b : ℕ) (h : a ||| b = T) : ∀ (l : List ℕ), b ∈ l → orRow T a l = true
  | [], hb => absurd hb (by simp)
  | x :: l, hb => by
    show ((a ||| x == T) || orRow T a l) = true
    rcases List.mem_cons.mp hb with hb | hb
    · rw [← hb, h]; simp
    · rw [orRow_of T a b h l hb]; simp

theorem andRow_of (T a b : ℕ) (h : a &&& b = T) : ∀ (l : List ℕ), b ∈ l → andRow T a l = true
  | [], hb => absurd hb (by simp)
  | x :: l, hb => by
    show ((a &&& x == T) || andRow T a l) = true
    rcases List.mem_cons.mp hb with hb | hb
    · rw [← hb, h]; simp
    · rw [andRow_of T a b h l hb]; simp

theorem last_of (T a b : ℕ) (Q : List ℕ) (hb : b ∈ Q) (hab : T = a &&& b ∨ T = a ||| b) :
    ∀ (l : List ℕ), a ∈ l → lastStep T Q l = true
  | [], ha => absurd ha (by simp)
  | x :: l, ha => by
    show (((x ||| T == T) && orRow T x Q) || ((x &&& T == T) && andRow T x Q)
      || lastStep T Q l) = true
    rcases List.mem_cons.mp ha with ha | ha
    · rw [← ha]
      rcases hab with h | h
      · have e1 : a &&& T = T := by rw [h, ← Nat.and_assoc, Nat.and_self]
        have e2 : andRow T a Q = true := andRow_of T a b h.symm Q hb
        rw [e1, e2]; simp
      · have e1 : a ||| T = T := by rw [h, ← Nat.or_assoc, Nat.or_self]
        have e2 : orRow T a Q = true := orRow_of T a b h.symm Q hb
        rw [e1, e2]; simp
    · rw [last_of T a b Q hb hab l ha]; simp

-- One level of the search. B holds, as bits, the members of Q and the numbers set aside. A
-- candidate d not in B is tried, and then set aside for the candidates after it, so every set
-- of new numbers is met once.
def go (T : ℕ) (f : List ℕ → ℕ → Bool) (Q : List ℕ) : ℕ → List ℕ → Bool
  | _, [] => false
  | B, d :: ds =>
    if B.testBit d then go T f Q B ds
    else (d == T) || f (d :: Q) (B ||| 2 ^ d) || go T f Q (B ||| 2 ^ d) ds

-- Can T, not in Q, be reached from Q by a chain of at most k new numbers, none set aside.
def srch (T : ℕ) : ℕ → List ℕ → ℕ → Bool
  | 0, _, _ => false
  | 1, Q, _ => lastStep T Q Q
  | k + 2, Q, B => go T (srch T (k + 1)) Q B (pairs Q [])

theorem chain_erase : ∀ (cs Q : List ℕ) (d : ℕ), Chain Q cs → Step Q d → d ∈ cs →
    Chain (d :: Q) (cs.erase d)
  | [], _, _, _, _, h => absurd h (by simp)
  | c :: cs, Q, d, hch, hd, hmem => by
    obtain ⟨hc, hrest⟩ := (chain_cons_iff Q c cs).mp hch
    by_cases hcd : c = d
    · rw [hcd, List.erase_cons_head]
      rw [hcd] at hrest
      exact hrest
    · have hmem' : d ∈ cs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hcd
        · exact h
      rw [List.erase_cons_tail (by simpa using hcd)]
      refine (chain_cons_iff _ _ _).mpr
        ⟨step_mono (fun x hx => List.mem_cons_of_mem _ hx) hc, ?_⟩
      have h := chain_erase cs (c :: Q) d hrest
        (step_mono (fun x hx => List.mem_cons_of_mem _ hx) hd) hmem'
      refine chain_mono _ _ _ ?_ h
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      tauto

-- The first number of a chain that is not in Q is one step from Q.
theorem first_new (T : ℕ) : ∀ (cs Q : List ℕ), Chain Q cs → T ∉ Q → T ∈ cs →
    ∃ c ∈ cs, c ∉ Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, c = a &&& b ∨ c = a ||| b
  | [], _, _, _, h => absurd h (by simp)
  | c :: cs, Q, hch, hTQ, hT => by
    obtain ⟨hc, hrest⟩ := (chain_cons_iff Q c cs).mp hch
    by_cases hcQ : c ∈ Q
    · have hT' : T ∈ cs := by
        rcases List.mem_cons.mp hT with h | h
        · rw [h] at hTQ; exact absurd hcQ hTQ
        · exact h
      have hrest' : Chain Q cs := by
        refine chain_mono _ _ _ ?_ hrest
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; exact hcQ
        · exact hx
      obtain ⟨c', hc', h1, h2⟩ := first_new T cs Q hrest' hTQ hT'
      exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩
    · rcases hc with h | h
      · exact absurd h hcQ
      · exact ⟨c, List.mem_cons_self, hcQ, h⟩

theorem eq_of_mem_short (c T : ℕ) : ∀ (cs : List ℕ), cs.length ≤ 1 → c ∈ cs → T ∈ cs → c = T
  | [], _, hc, _ => absurd hc (by simp)
  | [x], _, hc, hT => by
    rw [List.mem_singleton] at hc hT
    rw [hc, hT]
  | _ :: _ :: _, hlen, _, _ => by
    simp only [List.length_cons] at hlen
    omega

theorem go_sound (T k : ℕ) (Q : List ℕ) (f : List ℕ → ℕ → Bool)
    (hf : ∀ (cs Q' : List ℕ) (B : ℕ), Chain Q' cs → cs.length ≤ k + 1 →
      (∀ q ∈ Q', B.testBit q = true) → (∀ c ∈ cs, B.testBit c = true → c ∈ Q') →
      T ∉ Q' → T ∈ cs → f Q' B = true) :
    ∀ (L : List ℕ), (∀ d ∈ L, Step Q d) → ∀ (B : ℕ) (cs : List ℕ), Chain Q cs →
      cs.length ≤ k + 2 → (∀ q ∈ Q, B.testBit q = true) →
      (∀ c ∈ cs, B.testBit c = true → c ∈ Q) → T ∉ Q → T ∈ cs →
      (∃ c ∈ cs, c ∈ L ∧ c ∉ Q) → go T f Q B L = true
  | [], _, _, _, _, _, _, _, _, _, ⟨_, _, hcL, _⟩ => absurd hcL (by simp)
  | d :: ds, hL, B, cs, hch, hlen, hB1, hB2, hTQ, hT, ⟨c, hc, hcL, hcQ⟩ => by
    have hLds : ∀ d' ∈ ds, Step Q d' := fun d' hd' => hL d' (List.mem_cons_of_mem _ hd')
    show (if B.testBit d = true then go T f Q B ds
      else ((d == T) || f (d :: Q) (B ||| 2 ^ d) || go T f Q (B ||| 2 ^ d) ds)) = true
    by_cases hBd : B.testBit d = true
    · rw [ite_eq_left hBd]
      have hcd : c ≠ d := by
        intro h
        rw [h] at hc hcQ
        exact hcQ (hB2 d hc hBd)
      have hcds : c ∈ ds := by
        rcases List.mem_cons.mp hcL with h | h
        · exact absurd h hcd
        · exact h
      exact go_sound T k Q f hf ds hLds B cs hch hlen hB1 hB2 hTQ hT ⟨c, hc, hcds, hcQ⟩
    · rw [ite_eq_right hBd]
      by_cases hdT : d = T
      · rw [hdT]; simp
      · by_cases hdc : d ∈ cs
        · have e : f (d :: Q) (B ||| 2 ^ d) = true := by
            apply hf (cs.erase d) (d :: Q) (B ||| 2 ^ d)
            · exact chain_erase cs Q d hch (hL d List.mem_cons_self) hdc
            · have := List.length_erase_of_mem hdc
              omega
            · intro q hq
              rw [Nat.testBit_or]
              rcases List.mem_cons.mp hq with hq | hq
              · rw [hq, Nat.testBit_two_pow_self]; simp
              · rw [hB1 q hq]; simp
            · intro c' hc' hb
              by_cases hcd' : c' = d
              · rw [hcd']; exact List.mem_cons_self
              · rw [Nat.testBit_or, Nat.testBit_two_pow] at hb
                have hne : decide (d = c') = false := decide_eq_false (fun h => hcd' h.symm)
                rw [hne, Bool.or_false] at hb
                exact List.mem_cons_of_mem _ (hB2 c' (List.mem_of_mem_erase hc') hb)
            · intro h
              rcases List.mem_cons.mp h with h | h
              · exact hdT h.symm
              · exact hTQ h
            · exact (List.mem_erase_of_ne (fun h => hdT h.symm)).mpr hT
          rw [e]; simp
        · have e : go T f Q (B ||| 2 ^ d) ds = true := by
            apply go_sound T k Q f hf ds hLds (B ||| 2 ^ d) cs hch hlen
            · intro q hq
              rw [Nat.testBit_or, hB1 q hq]; simp
            · intro c' hc' hb
              have hcd' : c' ≠ d := by
                intro h
                rw [h] at hc'
                exact hdc hc'
              rw [Nat.testBit_or, Nat.testBit_two_pow] at hb
              have hne : decide (d = c') = false := decide_eq_false (fun h => hcd' h.symm)
              rw [hne, Bool.or_false] at hb
              exact hB2 c' hc' hb
            · exact hTQ
            · exact hT
            · refine ⟨c, hc, ?_, hcQ⟩
              rcases List.mem_cons.mp hcL with h | h
              · rw [h] at hc; exact absurd hc hdc
              · exact h
          rw [e]; simp

theorem srch_sound (T : ℕ) : ∀ (k : ℕ) (cs Q : List ℕ) (B : ℕ), Chain Q cs → cs.length ≤ k →
    (∀ q ∈ Q, B.testBit q = true) → (∀ c ∈ cs, B.testBit c = true → c ∈ Q) → T ∉ Q → T ∈ cs →
    srch T k Q B = true
  | 0, cs, _, _, _, hlen, _, _, _, hT => by
    have e : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [e] at hT
    exact absurd hT (by simp)
  | 1, cs, Q, _, hch, hlen, _, _, hTQ, hT => by
    show lastStep T Q Q = true
    obtain ⟨c, hc, _, a, ha, b, hb, hab⟩ := first_new T cs Q hch hTQ hT
    have hcT : c = T := eq_of_mem_short c T cs hlen hc hT
    rw [hcT] at hab
    exact last_of T a b Q hb hab Q ha
  | k + 2, cs, Q, B, hch, hlen, hB1, hB2, hTQ, hT => by
    show go T (srch T (k + 1)) Q B (pairs Q []) = true
    obtain ⟨c, hc, hcQ, a, ha, b, hb, hab⟩ := first_new T cs Q hch hTQ hT
    have hcl : c ∈ pairs Q [] := by
      obtain ⟨p1, p2⟩ := pairs_complete a b Q [] ha hb
      rcases hab with hab | hab
      · rw [hab]
        rcases p1 with p1 | p1
        · rw [hab] at hcQ; exact absurd p1 hcQ
        · exact p1
      · rw [hab]
        rcases p2 with p2 | p2
        · rw [hab] at hcQ; exact absurd p2 hcQ
        · exact p2
    refine go_sound T k Q (srch T (k + 1)) (fun cs' Q' B' h1 h2 h3 h4 h5 h6 =>
      srch_sound T (k + 1) cs' Q' B' h1 h2 h3 h4 h5 h6) (pairs Q []) ?_ B cs hch hlen hB1 hB2
      hTQ hT ⟨c, hc, hcl, hcQ⟩
    intro d hd
    rcases mem_pairs d Q [] hd with h | h
    · exact absurd h (by simp)
    · exact Or.inr h

-- The members of a list as bits.
def bitset : List ℕ → ℕ
  | [] => 0
  | q :: l => bitset l ||| 2 ^ q

theorem bitset_mem : ∀ (Q : List ℕ) (c : ℕ), c ∈ Q → (bitset Q).testBit c = true
  | [], _, h => absurd h (by simp)
  | q :: l, c, h => by
    show (bitset l ||| 2 ^ q).testBit c = true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp h with h | h
    · rw [h, Nat.testBit_two_pow_self]; simp
    · rw [bitset_mem l c h]; simp

theorem mem_of_bitset : ∀ (Q : List ℕ) (c : ℕ), (bitset Q).testBit c = true → c ∈ Q
  | [], c, h => by
    have h' : (0 : ℕ).testBit c = true := h
    rw [Nat.zero_testBit] at h'
    exact absurd h' (by simp)
  | q :: l, c, h => by
    have h' : (bitset l ||| 2 ^ q).testBit c = true := h
    rw [Nat.testBit_or, Nat.testBit_two_pow] at h'
    by_cases hq : q = c
    · rw [← hq]; exact List.mem_cons_self
    · have hne : decide (q = c) = false := decide_eq_false hq
      rw [hne, Bool.or_false] at h'
      exact List.mem_cons_of_mem _ (mem_of_bitset l c h')

-- THE TWO RESTRICTIONS AND THE END.

theorem testBit_of_mod (m T i : ℕ) (h : m % 65536 = T) (hi : i < 16) :
    m.testBit i = T.testBit i := by
  rw [← h, show (65536 : ℕ) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow]
  simp [hi]

theorem and_of_mod (m D : ℕ) (hD : D < 65536) : m &&& D = (m % 65536) &&& D := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, show (65536 : ℕ) = 2 ^ 16 from rfl,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < 16
  · simp [hi]
  · have hD' : D.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc D < 2 ^ 16 := hD
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hD']

theorem hitA_ne : ∀ m : ℕ, m % 65536 = 829 → m ≠ 3840 := by
  intro m h h'
  omega

theorem hitA_impl : ∀ m : ℕ, m % 65536 = 829 →
    impl [(8, 12), (9, 13), (10, 14), (11, 15)] m = false := by
  intro m h
  have h8 : m.testBit 8 = true := by
    rw [testBit_of_mod m 829 8 h (by norm_num)]; decide
  have h12 : m.testBit 12 = false := by
    rw [testBit_of_mod m 829 12 h (by norm_num)]; decide
  simp [impl, h8, h12]

theorem hitA_and : ∀ m : ℕ, m % 65536 = 829 → m &&& 61695 = 61 := by
  intro m h
  rw [and_of_mod m 61695 (by norm_num), h]
  decide

theorem hitB_ne : ∀ m : ℕ, m = 61 → m ≠ 32904 := by
  intro m h h'
  omega

theorem hitB_impl : ∀ m : ℕ, m = 61 → impl [(3, 1), (7, 5), (11, 9), (15, 13)] m = false := by
  intro m h
  rw [h]
  decide

theorem hitB_and : ∀ m : ℕ, m = 61 → m &&& 28791 = 53 := by
  intro m h
  rw [h]
  decide

def pool2 : List ℕ := [7, 112, 28672, 4113, 8226, 16452, 0, 28791]

theorem search_false : srch 53 4 pool2 (bitset pool2) = false := by decide +kernel

theorem lower :
    ¬ RepSizeAtMost (fun u v : Fin 4 => (829 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  rintro ⟨C, hC, hs, hrep⟩
  have hs' : C.gates.length ≤ 6 := hs
  obtain ⟨cs, hlen, hch, m, hm, hmT⟩ := chain_of_rep 829 (by norm_num) C hC hrep
  obtain ⟨cs1, hlen1, hch1, hT1⟩ := dropOne 61695 3840 61 [(8, 12), (9, 13), (10, 14), (11, 15)]
    (fun m => m % 65536 = 829) (by decide) hitA_ne hitA_impl hitA_and cs pool0 (by decide)
    (by decide +kernel) hch ⟨m, hm, hmT⟩
  obtain ⟨cs2, hlen2, hch2, hT2⟩ := dropOne 28791 32904 53 [(3, 1), (7, 5), (11, 9), (15, 13)]
    (fun m => m = 61) (by decide) hitB_ne hitB_impl hitB_and cs1 (pool0.map (· &&& 61695))
    (by decide +kernel) (by decide +kernel) hch1
    (by
      rcases hT1 with h | h
      · exact ⟨61, Or.inl h, rfl⟩
      · exact ⟨61, Or.inr h, rfl⟩)
  have hch2' : Chain pool2 cs2 := chain_mono cs2 _ pool2 (by decide +kernel) hch2
  have hT2' : (53 : ℕ) ∈ cs2 := by
    rcases hT2 with h | h
    · exact h
    · exact absurd h (by decide +kernel)
  have hsound := srch_sound 53 4 cs2 pool2 (bitset pool2) hch2' (by omega)
    (fun q hq => bitset_mem pool2 q hq) (fun c _ hb => mem_of_bitset pool2 c hb)
    (by decide) hT2'
  rw [search_false] at hsound
  exact Bool.false_ne_true hsound

theorem upper :
    RepSizeAtMost (fun u v : Fin 4 => (829 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.or, [10, 13]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5625

theorem PEqualNP.Outside.L_meta_5625 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (829 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (829 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  exact ⟨PEqualNP.Outside.L_meta_5625.upper, PEqualNP.Outside.L_meta_5625.lower⟩
