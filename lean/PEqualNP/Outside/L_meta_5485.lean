import Mathlib.Tactic
import PEqualNP.Defs

-- L-meta-5485: the 4-by-4 bipartite graph with mask 279 has representing size exactly 6.
-- Upper half: an explicit circuit of 6 gates, checked by decide.
-- Lower half: the encoding of a 5-gate circuit is unsatisfiable; an LRAT certificate
-- (from Lingeling, converted and trimmed) is checked by the kernel.
-- The LRAT checker, the encoding and its link to circuits are copied, comments removed and
-- namespaces renamed, from PEqualNP/Library/LRAT (Checker, Link, Link2, Promise, PromiseGen)
-- and PEqualNP/MetaComplexity/Helpers/Shannon.lean of this repository (Apache-2.0).



namespace PEqualNP.Outside.L_meta_5485.Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_5485.Helpers




namespace PEqualNP.Outside.L_meta_5485.LRAT

noncomputable section

def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

theorem bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

theorem litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

inductive Trie where
  | nil : Trie
  | node (v : Option Nat) (l r : Trie) : Trie

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  Trie.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := Trie.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ _ r _ _ => r) t

def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel

def All (P : Nat → Prop) : Trie → Prop
  | .nil => True
  | .node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

theorem All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → t.get k = some c → P c
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (r.get _) (l.get _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

theorem All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

theorem All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

theorem All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

theorem All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (.node t.root t.left (Trie.set fuel t.right _ o))
      (.node t.root (Trie.set fuel t.left _ o) t.right) _) (.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie

theorem bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

theorem bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

theorem bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

theorem bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

theorem bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool

def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (db.get x)

def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

def stop : Cont := fun _ _ _ _ _ _ => false

def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

def fuelW : Nat := 1024

def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q (nat_lit 1)))) e

def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))

def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0

def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0

def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0

def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0

def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0

section Soundness

variable (a : Nat → Bool)

def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

theorem witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

theorem stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

theorem tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    ·
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    ·
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) (db.get x) = true at h
      cases hg : db.get x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h

          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

theorem runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

theorem runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

theorem runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

theorem clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

theorem maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

theorem verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q 1)) = true
            at he
          cases hg : db.get (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

theorem loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

theorem loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

theorem check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

theorem checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end

end PEqualNP.Outside.L_meta_5485.LRAT




namespace PEqualNP.Outside.L_meta_5485.LRAT.Link

open PEqualNP.Outside.L_meta_5485.LRAT

structure Model where
  op : ℕ → ℕ
  s1 : ℕ → ℕ
  s2 : ℕ → ℕ
  so : ℕ
  w : ℕ → ℕ → Bool

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

structure Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop where
  op_lt : ∀ j < s, M.op j < 3
  s1_le : ∀ j < s, M.s1 j ≤ n + j
  s2_le : ∀ j < s, M.s2 j ≤ n + j
  so_le : M.so ≤ n + s
  w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)
  out_eq : ∀ r, R r → M.sv n s M.so r = g r

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

instance (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

structure NF (n s : ℕ) (M : Model) : Prop where
  pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j
  padOp : ∀ j < s, M.op j = 2 → M.pad n j
  noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j
  noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i
  ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j
  used : ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)
  out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)

section formula
variable (n s : ℕ)

def wd : ℕ := 2 ^ n + n + s + 1

def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a

def P (v : ℕ) : ℕ := 2 * v + 2

def Q (v : ℕ) : ℕ := 2 * v + 3

def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v

def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)

def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)]

def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l => [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)]

def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s

end formula

def rowFun (n : ℕ) (f : (Fin n → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 1) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha


section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 3) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2, v_pad, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases hp : M.pad n j
  · exact Or.inr (Or.inr hp)
  · have := hn.ord j hj hp
    omega

theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in

theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h

end sound

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5485.Helpers

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model where
  op j := (code n (gateAt C j) j).1
  s1 j := (code n (gateAt C j) j).2.1
  s2 j := (code n (gateAt C j) j).2.2
  so := if C.output < n + C.gates.length then C.output else n + s
  w j r := if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) where
  op_lt j _ := (code_le n _ j).1
  s1_le j _ := (code_le n _ j).2.1
  s2_le j _ := (code_le n _ j).2.2
  so_le := by simp only [ofCirc]; split_ifs <;> omega
  w_eq j hj r _ := by
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun]
  out_eq r hr := by
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model where
  op j := if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j
  s1 j := if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j)
  s2 j := if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j)
  so := rd n d t s M.so
  w j r := if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) where
  op_lt j hj := by
    simp only [mv]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  s1_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  s2_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  so_le := by
    have := hv.so_le
    simp only [mv]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  w_eq j hj r hr := by
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  out_eq r hr := by
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

theorem ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  { M with s1 := fun i => if i = j then M.s2 j else M.s1 i,
           s2 := fun i => if i = j then M.s1 j else M.s2 i }

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) where
  op_lt := hv.op_lt
  s1_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  so_le := hv.so_le
  w_eq i hi r hr := by
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  out_eq r hr := hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

theorem exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas n s M' < meas n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨M, hv, {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf⟩ := exists_nf ⟨_, hv⟩
  exact ⟨val n s M, enc_sat hrows hM hnf⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc n s (rowFun n f) rows)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link n s f rows hrows C hC (by omega) hev)

theorem sat_of_check (a : ℕ → Bool) (F : List (List ℕ))
    (h : F.all (fun c => c.any fun l => litVal a l) = true) : FormulaSat F := by
  refine ⟨a, fun c hc => ?_⟩
  have := List.all_eq_true.1 h c hc
  obtain ⟨l, hl, hv⟩ := List.any_eq_true.1 this
  exact ⟨l, hl, hv⟩

end PEqualNP.Outside.L_meta_5485.LRAT.Link




namespace PEqualNP.Outside.L_meta_5485.LRAT.Link

open PEqualNP.Outside.L_meta_5485.LRAT

def lexWord (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lexWord B a m * B + a m

theorem lexWord_lt {B : ℕ} {a : ℕ → ℕ} : ∀ m, (∀ i < m, a i < B) → lexWord B a m < B ^ m
  | 0, _ => by simp [lexWord]
  | m + 1, h => by
    have ih := lexWord_lt m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    have h2 : (lexWord B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul, Nat.one_mul] at h2
    simp only [lexWord, pow_succ]
    omega

theorem lexWord_congr {B : ℕ} {a b : ℕ → ℕ} :
    ∀ m, (∀ i < m, a i = b i) → lexWord B a m = lexWord B b m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lexWord, lexWord_congr m (fun i hi => h i (by omega)), h m (by omega)]

theorem lexWord_lt_of {B : ℕ} {a b : ℕ → ℕ} {j : ℕ} (hab : ∀ i < j, a i = b i) (hj : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → lexWord B b m < lexWord B a m
  | 0, h, _ => by omega
  | m + 1, hjm, hb => by
    by_cases h : m = j
    · subst h
      simp only [lexWord, lexWord_congr m hab]
      omega
    · have ih := lexWord_lt_of hab hj m (by omega) (fun i hi => hb i (by omega))
      have hm := hb m (by omega)
      have h2 : (lexWord B b m + 1) * B ≤ lexWord B a m * B := Nat.mul_le_mul_right _ ih
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp only [lexWord]
      omega

def lexKey (n s : ℕ) (M : Model) (j : ℕ) : ℕ := M.s1 j * (3 * (n + s + 1)) + M.s2 j * 3 + M.op j

def lexB (n s : ℕ) : ℕ := 3 * (n + s + 1) * (n + s + 1)

theorem lex3 (K x1 y1 z1 x2 y2 z2 : ℕ) (hy : y1 * 3 + z1 < K) (hz : z1 < 3)
    (h : x1 < x2 ∨ (x1 = x2 ∧ (y1 < y2 ∨ (y1 = y2 ∧ z1 < z2)))) :
    x1 * K + y1 * 3 + z1 < x2 * K + y2 * 3 + z2 := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have : (x1 + 1) * K ≤ x2 * K := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega
  · omega

section keys
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

theorem lexKey_lt (hv : Valid n s g R M) {j : ℕ} (hj : j < s) : lexKey n s M j < lexB n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have : M.s1 j * (3 * (n + s + 1)) ≤ (n + s) * (3 * (n + s + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (n + s) * (3 * (n + s + 1)) + 3 * (n + s + 1) = 3 * (n + s + 1) * (n + s + 1) := by
    ring
  unfold lexKey lexB
  omega

def meas2 (n s : ℕ) (M : Model) : ℕ :=
  lexB n s ^ s * muf s (ind n M) + lexWord (lexB n s) (lexKey n s M) s

theorem lexWord_lt_pow (hv : Valid n s g R M) :
    lexWord (lexB n s) (lexKey n s M) s < lexB n s ^ s :=
  lexWord_lt s fun _ hi => lexKey_lt hv hi

end keys

theorem meas2_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas2 n s (mv n s M d t) < meas2 n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := lexWord_lt_pow hv'
  have : lexB n s ^ s * muf s (ind n (mv n s M d t)) + lexB n s ^ s ≤
      lexB n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  unfold meas2
  omega

theorem meas2_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}
    (hv : Valid n s g R M) (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas2 n s (sw M j) < meas2 n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas2
  rw [hind]
  have hk : lexKey n s (sw M j) j < lexKey n s M j := by
    have h1 := hv.s1_le j hj
    have : (M.s2 j + 1) * (3 * (n + s + 1)) ≤ M.s1 j * (3 * (n + s + 1)) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [lexKey, sw, if_pos rfl, ↓reduceIte]
    omega
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (sw M j)) (j := j)
    (fun i hi => by simp [lexKey, sw, show i ≠ j by omega]) hk s hj
    (fun i hi => lexKey_lt (valid_sw hv j) hi)
  omega

def tsw (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

def xsw (n : ℕ) (M : Model) (j : ℕ) : Model where
  op i := if i = j then M.op (j + 1) else if i = j + 1 then M.op j else M.op i
  s1 i := if i = j then M.s1 (j + 1) else if i = j + 1 then M.s1 j
    else if j + 1 < i then tsw n j (M.s1 i) else M.s1 i
  s2 i := if i = j then M.s2 (j + 1) else if i = j + 1 then M.s2 j
    else if j + 1 < i then tsw n j (M.s2 i) else M.s2 i
  so := tsw n j M.so
  w i r := if i = j then M.w (j + 1) r else if i = j + 1 then M.w j r else M.w i r

section xsw
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

theorem sv_xsw_low {i i' k r : ℕ} (hk : k < n + j) (hi : j ≤ i) (hi' : j ≤ i') :
    (xsw n M j).sv n i k r = M.sv n i' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · simp only [if_neg h6, if_pos (show k < n + i by omega), if_pos (show k < n + i' by omega),
      xsw, if_neg (show k - n ≠ j by omega), if_neg (show k - n ≠ j + 1 by omega)]

theorem sv_xsw_early {i k r : ℕ} (hi : i < j) : (xsw n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
        if_neg (show k - n ≠ j + 1 by omega)]
    · simp only [if_neg h6, if_neg h7]

theorem sv_xsw_late {i k r : ℕ} (hi : j + 1 < i) :
    (xsw n M j).sv n i (tsw n j k) r = M.sv n i k r := by
  unfold tsw
  by_cases h1 : k = n + j
  · subst h1
    simp only [if_pos rfl, ↓reduceIte]
    unfold Model.sv
    simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
      if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
      show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega,
      if_neg (show j + 1 ≠ j by omega), if_pos rfl, ↓reduceIte]
  · by_cases h2 : k = n + j + 1
    · subst h2
      simp only [if_neg h1, if_pos rfl, ↓reduceIte]
      unfold Model.sv
      simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
        if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
        show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega, if_pos rfl, ↓reduceIte]
    · simp only [if_neg h1, if_neg h2]
      unfold Model.sv
      by_cases h6 : k < n
      · simp [h6]
      · by_cases h7 : k < n + i
        · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
            if_neg (show k - n ≠ j + 1 by omega)]
        · simp only [if_neg h6, if_neg h7]

theorem tsw_le {i k : ℕ} (hi : j + 1 ≤ i) (hk : k ≤ n + i) : tsw n j k ≤ n + i := by
  unfold tsw; split_ifs <;> omega

theorem tsw_eq_iff {i k : ℕ} (hi : j + 1 < i) : tsw n j k = n + i ↔ k = n + i := by
  unfold tsw; split_ifs <;> omega

variable (hv : Valid n s g R M) (hj : j + 1 < s) (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j)
  (h3 : M.s1 (j + 1) < n + j) (h4 : M.s2 (j + 1) < n + j)
include hv hj h1 h2 h3 h4

theorem valid_xsw : Valid n s g R (xsw n M j) where
  op_lt i hi := by
    simp only [xsw]; split_ifs
    · exact hv.op_lt _ hj
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hi
  s1_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s1_le i hi)
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s2_le i hi)
    · exact hv.s2_le i hi
  so_le := tsw_le (by omega) hv.so_le
  w_eq i hi r hr := by
    by_cases a : i = j
    · subst a
      have e1 : (xsw n M i).s1 i = M.s1 (i + 1) := by simp [xsw]
      have e2 : (xsw n M i).s2 i = M.s2 (i + 1) := by simp [xsw]
      have e3 : (xsw n M i).op i = M.op (i + 1) := by simp [xsw]
      have e4 : (xsw n M i).w i r = M.w (i + 1) r := by simp [xsw]
      rw [e1, e2, e3, e4, sv_xsw_low h3 le_rfl (Nat.le_succ i),
        sv_xsw_low h4 le_rfl (Nat.le_succ i)]
      exact hv.w_eq (i + 1) hj r hr
    · by_cases b : i = j + 1
      · subst b
        have e1 : (xsw n M j).s1 (j + 1) = M.s1 j := by simp [xsw]
        have e2 : (xsw n M j).s2 (j + 1) = M.s2 j := by simp [xsw]
        have e3 : (xsw n M j).op (j + 1) = M.op j := by simp [xsw]
        have e4 : (xsw n M j).w (j + 1) r = M.w j r := by simp [xsw]
        rw [e1, e2, e3, e4, sv_xsw_low h1 (Nat.le_succ j) le_rfl,
          sv_xsw_low h2 (Nat.le_succ j) le_rfl]
        exact hv.w_eq j (by omega) r hr
      · by_cases c : j + 1 < i
        · have e1 : (xsw n M j).s1 i = tsw n j (M.s1 i) := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = tsw n j (M.s2 i) := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_late c, sv_xsw_late c]
          exact hv.w_eq i hi r hr
        · have e1 : (xsw n M j).s1 i = M.s1 i := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = M.s2 i := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_early (by omega), sv_xsw_early (by omega)]
          exact hv.w_eq i hi r hr
  out_eq r hr := by
    have e : (xsw n M j).so = tsw n j M.so := rfl
    rw [e, sv_xsw_late hj]
    exact hv.out_eq r hr

omit hv hj in
theorem ind_xsw : ind n (xsw n M j) = ind n M := by
  funext i
  unfold ind
  have hp : (xsw n M j).pad n i ↔ M.pad n i := by
    by_cases a : i = j
    · subst a
      simp only [Model.pad, xsw, if_pos rfl, ↓reduceIte]
      omega
    · by_cases b : i = j + 1
      · subst b
        simp only [Model.pad, xsw, if_neg a, if_pos rfl, ↓reduceIte]
        omega
      · by_cases c : j + 1 < i
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_pos c, tsw_eq_iff c]
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_neg c]
  by_cases h : M.pad n i
  · simp [h, hp.2 h]
  · have h' : ¬ (xsw n M j).pad n i := fun h' => h (hp.1 h')
    simp [h, h']

theorem meas2_xsw (hlt : lexKey n s M (j + 1) < lexKey n s M j) :
    meas2 n s (xsw n M j) < meas2 n s M := by
  unfold meas2
  rw [ind_xsw h1 h2 h3 h4]
  have hk : lexKey n s (xsw n M j) j = lexKey n s M (j + 1) := by simp [lexKey, xsw]
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (xsw n M j))
    (j := j)
    (fun i hi => by
      simp [lexKey, xsw, show i ≠ j by omega, show i ≠ j + 1 by omega,
        show ¬ j + 1 < i by omega])
    (by rw [hk]; exact hlt) s (by omega)
    (fun i hi => lexKey_lt (valid_xsw hv hj h1 h2 h3 h4) hi)
  omega

end xsw

def LexNF (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ (M.s2 j < M.s2 (j + 1) ∨
      (M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)))

theorem nf_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

theorem lex_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : LexNF n s M := by
  have hnf := nf_of_min2 hv hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)

  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 3 → y * 3 + z < 3 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      ·
        have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [if_neg h6, if_pos hk, if_pos (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, htw⟩ := copy_tgt hv hj (k := n + j) (by omega) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (meas2_mv hv hv' hj (Or.inl hnp1))
      · have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

theorem exists_nf2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas2 n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  exact ⟨M, hv, nf_of_min2 hv hmin, lex_of_min2 hv hmin⟩

section formula
variable (n s : ℕ)

def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

theorem s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hn : NF n s M) (hl : LexNF n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hj1 : j + 1 < s := Nat.add_lt_of_lt_sub hj
  have hj0 : j < s := Nat.lt_of_succ_lt hj1
  have hb1 : ClauseSat (val n s M) (lexBase n s j) ↔
      M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j := by
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2, or_false,
      beq_iff_eq, decide_eq_true_eq]
  have happ : ∀ c', ClauseSat (val n s M) (lexBase n s j) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_right _ hl', hv'⟩
  have hfront : ∀ c', (∃ l ∈ c', litVal (val n s M) l = true) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_left _ hl', hv'⟩
  by_cases hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      exact happ _ (hb1.2 hesc)
  have hnp : ¬ M.pad n j := fun h => hesc (Or.inl h)
  have L := hl j hj1 hnp (fun h => hesc (Or.inr (Or.inl h)))
    (fun h => hesc (Or.inr (Or.inr h)))
  have hop0 := hn.padOp j hj0
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;> apply hfront <;>
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litVal_Q, v_s1, v_s2, v_op, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] <;> omega

theorem enc2_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
    (hl : LexNF n s M) : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn hl c h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc2 n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc2 n s (rowFun n f) rows)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link2 n s f rows hrows C hC (by omega) hev)

end PEqualNP.Outside.L_meta_5485.LRAT.Link




namespace PEqualNP.Outside.L_meta_5485.LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5485.LRAT
  PEqualNP.Outside.L_meta_5485.LRAT.Link PEqualNP.Represents

theorem promise_lower (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hrows : ∀ r ∈ rows, r < 2 ^ n)
    (hU : ¬ FormulaSat (enc2 n s g rows)) (C : Circuit) (hC : Monotone2 C)
    (hev : ∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i) = g r) :
    s + 1 ≤ C.size := by
  by_contra h
  have hv := valid_ofCirc n s g (· ∈ rows) C hC (by simp only [Circuit.size] at h; omega)
    (fun r hr => hev r hr)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact hU ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

def row44 (u v : Fin 4) : ℕ := 2 ^ (u : ℕ) + 2 ^ (4 + (v : ℕ))

theorem row44_eq : ∀ u v : Fin 4,
    (List.ofFn fun i : Fin (4 + 4) => (row44 u v).testBit i) = oneEach u v := by decide

def rows44 : List ℕ :=
  (List.finRange 4).flatMap fun u => (List.finRange 4).map fun v => row44 u v

theorem rep_lower44 (A : Fin 4 → Fin 4 → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ u v, g (row44 u v) = A u v) (hU : ¬ FormulaSat (enc2 (4 + 4) s g rows44)) :
    ¬ RepSizeAtMost A s := by
  rintro ⟨C, hC, hs, hr⟩
  have hrow : ∀ r ∈ rows44, r < 2 ^ (4 + 4) := by decide
  have := promise_lower (4 + 4) s g rows44 hrow hU C hC (by
    intro r hr'
    simp only [rows44, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hr'
    obtain ⟨u, v, rfl⟩ := hr'
    rw [row44_eq, hr, hg])
  omega

def litRow (r : ℕ) : ℕ := r + 16 * (15 - r)

theorem litRow_eq : ∀ x : Fin 4 → Bool,
    (List.ofFn fun i : Fin (4 + 4) => (litRow (tableIndex x)).testBit i) =
      List.ofFn x ++ List.ofFn fun i => !x i := by decide

def litRows : List ℕ := (List.range 16).map litRow

theorem lit_lower4 (f : (Fin 4 → Bool) → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ x, g (litRow (tableIndex x)) = f x)
    (hU : ¬ FormulaSat (enc2 (4 + 4) s g litRows)) : ¬ HasLitSize 4 f s := by
  rintro ⟨C, hC, hs, hr⟩
  have hrow : ∀ r ∈ litRows, r < 2 ^ (4 + 4) := by decide
  have hall : ∀ r ∈ litRows, ∃ x : Fin 4 → Bool, litRow (tableIndex x) = r := by decide
  have := promise_lower (4 + 4) s g litRows hrow hU C hC (by
    intro r hr'
    obtain ⟨x, rfl⟩ := hall r hr'
    rw [litRow_eq, hr, hg])
  omega

end PEqualNP.Outside.L_meta_5485.LRAT.Promise




namespace PEqualNP.Outside.L_meta_5485.LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5485.LRAT
  PEqualNP.Outside.L_meta_5485.LRAT.Link PEqualNP.Represents

def repRow (n u v : ℕ) : ℕ := 2 ^ u + 2 ^ (n + v)

theorem repRow_testBit {n u : ℕ} (hu : u < n) (v i : ℕ) :
    (repRow n u v).testBit i = (decide (i = u) || decide (i = n + v)) := by
  have h : repRow n u v = 2 ^ (n + v) ||| 2 ^ u := by
    have := Nat.two_pow_add_eq_or_of_lt (i := n + v) (b := 2 ^ u)
      (Nat.pow_lt_pow_right (by norm_num) (by omega)) 1
    rw [mul_one] at this
    rw [← this, repRow, add_comm]
  rw [h, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow, Bool.or_comm]
  congr 1 <;> exact decide_eq_decide.mpr eq_comm

theorem repRow_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    (List.ofFn fun i : Fin (n + m) => (repRow n u v).testBit i) = oneEach u v := by
  have hu := u.2
  apply List.ext_getElem
  · simp [oneEach]
  · intro i h1 h2
    rw [List.getElem_ofFn, repRow_testBit hu]
    simp only [oneEach, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
    split_ifs with h
    · have hne : ¬ i = n + (v : ℕ) := by omega
      simp [Fin.ext_iff, hne]
    · have hne : ¬ i = (u : ℕ) := by omega
      have hiff : i = n + (v : ℕ) ↔ i - n = (v : ℕ) := by omega
      simp [Fin.ext_iff, hne, hiff]

def repRows (n m : ℕ) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange m).map fun v => repRow n u v

theorem rep_lower {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ (u : Fin n) (v : Fin m), g (repRow n u v) = A u v)
    (hU : ¬ FormulaSat (enc2 (n + m) s g (repRows n m))) : ¬ RepSizeAtMost A s := by
  rintro ⟨C, hC, hs, hr⟩
  have hmem : ∀ r ∈ repRows n m, ∃ (u : Fin n) (v : Fin m), repRow n u v = r := by
    intro r hr'
    simpa [repRows] using hr'
  have hrow : ∀ r ∈ repRows n m, r < 2 ^ (n + m) := by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    rw [repRow_testBit u.2]
    have := u.2; have := v.2
    simp; omega
  have := promise_lower (n + m) s g (repRows n m) hrow hU C hC (by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    rw [repRow_eq, hr, hg])
  omega

def gMask (n m M r : ℕ) : Bool := M.testBit (m * Nat.log2 (r % 2 ^ n) + Nat.log2 (r / 2 ^ n))

theorem gMask_row {n m : ℕ} (M : ℕ) (u : Fin n) (v : Fin m) :
    gMask n m M (repRow n u v) = M.testBit (m * u + v) := by
  have hlt : 2 ^ (u : ℕ) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) u.2
  have h1 : repRow n u v % 2 ^ n = 2 ^ (u : ℕ) := by
    rw [repRow, pow_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have h2 : repRow n u v / 2 ^ n = 2 ^ (v : ℕ) := by
    rw [repRow, pow_add, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  rw [gMask, h1, h2, Nat.log2_two_pow, Nat.log2_two_pow]

theorem rep_lower_mask (n m M s : ℕ)
    (hU : ¬ FormulaSat (enc2 (n + m) s (gMask n m M) (repRows n m))) :
    ¬ RepSizeAtMost (fun (u : Fin n) (v : Fin m) => M.testBit (m * u + v)) s :=
  rep_lower (n := n) (m := m) (fun u v => M.testBit (m * u + v)) s (gMask n m M)
    (fun u v => gMask_row (n := n) (m := m) M u v) hU

end PEqualNP.Outside.L_meta_5485.LRAT.Promise


namespace PEqualNP.Outside.L_meta_5485
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def formula : List (List ℕ) := LRAT.Link.enc2 (4 + 4) 5 (LRAT.Promise.gMask 4 4 279) (LRAT.Promise.repRows 4 4)

def fk : List ℕ := (List.range 6452).map (· + 1)

def words : List ℕ := [
  0x1836e150a0d78516835613a8000195b1d8e6ddc76b589a000a65900028cb1010e32bc0310cad007a32ec577589b15d4cbcc446b2eb10e2001c42c32e710aa992c2a3a6430a3698fc27780001954001465c0cb6196832ca0db41ae83546dfccb184c336fc3216c4d8aea000e216131f88574c7820e60d484be7f1e1141973803c65c80060000000532b63b1cdbb8ed6195665886429b76001665680051b7309ba655423419610894657c224995d089065642231957088b06284603f7210d8fdb8428283a06ba001000019531640ecd850580031096cb2c02bb2c7006632a80028872000832e47010cb71b8c32d46c58cb31aa232c468c0caf19c032b46548875140e6df42871b7b0a1a6de42861b750a146dc42843c14069a6dfc758c18e11b8a46045b822000026dbc5a69b8115ea088c579996315de32ec577000715da087c46ba61e0b36d39c07bb4e30196d7000600ec6000cba38ca22f6d32863b648750ed721423b5482c8ed320243b447e60ecf1f0e3b347a18ecb1e003b2475f5ab71635626c5878877160b842c581c3a6126054cc1d3bb3a074443d40e13703036edbfc0c1800021c6a95c21ea83f3b38766ca96a62332c231c8a98995fbdde64dc00021d832c000390ec8c6143ae31810ea8c5f43a631790e88c5d439e31710e68c5b439631690e48c59438e31610e28c57438631590ed993fc21664ec000153132be31850ec000e2a6064d90eb87b32a5e0e8ca9199505d36653175999495dde651975799455d1c65117b699435d1865030858b0354b625310ed87b743a61ebe1d585cf2a660e9ca95839f000087510e1152c439487410e721cc439087190e2151e8fc6ecedb811d9b087a9888caf000c3b2617fcecb85653b2a1590ec885623b1e1584ec685608766259e1d2091408780008ecf8afbb9a62bd821d890f00007670ecc2a5554c47628ecd043e6df865745ff1fa832b57bbcc9b80003f6c4c4ccad8bff3f546566f77993700007ed89899fa832b43000fd61958bdde64dc0001faa3f6c4c4cfd4195918027eb8cabdeef326e0000fd51fac3f6c4c4cfd4195818047ec0cab5eef326e0000fd51fae3f587ed89899fa832ae300cfd91955bdde64dc0001faa3f607eb8fd61fb626267ea0cab0c043f686552f77993700007ea8fd91fb03f5c7eb0fdb13133f5065546031fb832a37bbcc9b80003f547ed0fd91fb03f5c7eb0fdb13133f506550004131105bc4c1c16b92ff04b64c34113130b044a4c24112130504444c0c11093010440e49c4eb391a1340e4604c2065800064c4c603931516017bbc57e065b13b2195c4c045c30cef170431d800054aca9509872c7e508eb1cd6389fbb32a6001c87a8bb121e22e808778b9921da2e4c8758b8e21d22e288738b8721ca2e148718b8421ee2beae698af83b3e15ae1d2055f000043c8ec59952001a7eec6039fa717fa7ef4c9d5eef326e00009899fb83f687ec8fd81fae3f587ea8fdb1fa832a2001043a8a4610e627d974d994c5d58650443b8b05c2162c0dda103df76aa0c90a99831f76680c4c000152332a064def770b0bc2142ba66058ae10000bbecca71937bddc2c2f0850ae998162b680002ebb329a64def770b0bc2142ba66058ad30000ba6cca61937bddc2c2f0850ae998162b300002f73329664def770b0bc2142ba66058ac50000bbccca51937bddc2c2f0850ae998162af80002eb332922c0b0850ae998162ad843b8a2d0000ba48ca41937bddc2c2f0850ae998162aac0002f6f328e64def770b0bc2142ba66058aa40000bbbcca31937bddc2c2f0850ae998162a740002eaf328a2c0b0850ae998162a5443b8a110000ba38ca21937bddc2c2f0850ae998162a280002f6d32862c0b0850ae998162a0843b8a030000bbb0ca10b02c2142ba66058a7610ee27f00002eac32822c0b0850ae9981629a843b89f50000ba30ca01937bddc2c2f0850b070000876cc9f9937bddc2c2f0850b06000054ccc9f1937bddc2c2f0850ae998162a297b60a0a000021dcc9e9937bddc2c2c000610b327664def770b0100007ef4c9d1937bddc2c000001315327264def770aff0000196cc9c000410ea291843b8a0a10e627d9da103df76aa0c90a9119365d362b4d7598abe5dde2a917578a9d5d1c2a557b68a8a5d5829d97460a6a9814297e6018a864df821280030aea980a2a1d48c08ba2a562c62c4d0b0804442bc26038a88566824a8a968b1ab56c2c2421f0af698122a256a8099a2a622c78a978b1cb9a42c2832d0afc97e62a125fd8a6f981a29ae6008a6597fe29925fe8a6397f2298a5fb8a6197ea29800005eef326e0024a8d83532a520c58a9383152a4a0c50a9083122a3e0c44a8e8310766c282dd9a09ef10e4001043a99352a662c1b0858b0210ee28280002e9a5d64bbb97572e8f5ed8ba34a95152c2a5c54c0a911936001254841ef151f0754549c1bd952506d254741b295290692546c1a11533160d842c5813b43148ced6c518bb971438ed5c50a88771414f05450380002a44ba697592eee5d5cbdb0a95152c2a5c54c043a99350012548c1ef951f075454841cd152706f654941b4951d06ca54a41a4951b0684ed0c5233b5b1462ece85163b971438ed5c50abc15140e21d00021533160d842c5810873145021dc50500005d34bac9749aeee5d5cbdb0a95152c2a5c54c23f11934,
  0x12a62657d74d994c5d66652574919485dde651975799455d1c65117b6994310ee64f498a993932c62bbc65d8aeeb1362ba8003884a0000195c9871310523254b937e198432cc656c21a99550840fdb84263fcc107cfdb0418000200000014cc0262b07c8990c1d8a67f06fc98fc1b6a61e06b699f019ca61c062e54a8c9a152d069aed0c5233b5b1462ee5c50e3b57142aecd85083c15140eee505013b3413e821d0002087313e11f8c3dac7df0ee320f43a7c7dd0e5a8760cb0153132beba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284ba30ca00877327a658c577d89b15d4b1dc4dbac731336b3444c6ac7112fe001c425391f0538e46c13039790484e46411200004df8195d48c952e2612660c12093060010e5e04c6acd00e9e4c0414c130d04c44c2c130930904c04c1412f130304ba4bfc12dc83c1404e4784dbb91a1336b1d83daac720ee2ee5419cc7e214591f78508267d107cff3421b3b3b073eecdc1ad995c0014654c590262310ce987c425b2cb00aecb1c0198caa000a32d4cc09961085e657c217195b085865642159957085465542148cb9003e32dc00f0cb3003832c400d8caf003432b400cbf8c106ecb9041b000200000014cc0262b07c8990c1d8a67f06fc98fc1b6a63c065054a8c9a996315de32ec577589b15d4001c425152d069a9bf4cbe3b43148ced6c518bb971438ed5c50abc15140eed504fd8874000821cc4fb931332fc8760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac328221dcc9e9315327200023fe29192a5c4c38988065733040028cae8b3432a62cbccb18aefb1362bac65d802065c80074000196032bc6568cac195632a832d4cc08005196601fc658807e195e018865b804b196a0104656803d197200c4655802a19762bbac4d8aea65a622199758871664e21719738855000e21299d28847000098a9321267e4c7c9bf000299800c947ee8638c5e0130eb24039f131332fc8760cb05cd315ec10fc48e21d70e78000153a06572a5d1ff4cbf8c053f6c656ef77993700004c4ccbf19362a62657ca9199505d36653175999495dde651975799455d1c65117b699435d186500a96834d2a560d2c0003c144dfaa464a97197c00104c24121130b04684c1c119130504624c0c1181301045ee5e04c6b938130cb3403a7ac900e7d20f050147fc13f621d0002087313ec8760cb02eec3284bab0ca08877327a4c54c9cbb95067aed5419600002a5ea9d155a065726184c3897f1310262465ec004130704644c2c112930904484c14111130304424c041103938130ce4604bfac900e7cb1c0396c7fc13f71f704fa3b550658ecd418da1d832c0bab0ca0ae8c32804c54c9caa75122ca954487b71d02badbf40a80000261c4c3097f0657262410eca97887526204394cbc800721d607bc87481ee21ce071887781a321da0654872819121ea0604878817d21c605d9b8589666e462545baf893c6e3e24d5bee89270000a98953d2ab654eca4648792b3421ec10f4cbc000721d20548873815121ca05408778b9e6df824521d285643b280030ecb85723b2615c0ec8856f3b1e15b8ec6856d3b166548ecf8afb21ee2bea1e2091b21da0584871815c000043a8ece1d9821e843c021eaa7554aa43c8ecd5cd26e3865d80061d950afc765c2b91d93172476445c89d8f172076345c79d9f15f7734c57bc40412450f1048db75d02dadc740b010f702b6dbf00a980003b38766021eaab554ea7628ecd10eb32ea001c87a818d21c6060c875816021e20558877815521da0550874815221ce054487281506dfc24adb8e09166df8243c0002a7554aaa0e88792a5721ec10eccba0002087624b021f892a087a24a21d3859b8908163c0002b3454ae987937e9d9b32e6000821d892b087e24a821e89276dfe062dbee017f0000acd152ba61e4dfa43cccb8800826220994987826325fe096c9838232261a08989858225261208909828222260608849808220262a64e5c8d099b72702619c8c097f00004c49639ac9158e2a0e930f065732e000104398a0b10ea281d74719445eda650c43b8b05c2162c0dd9b835d2a660d49e0a034d0000a0e948c952d32d232a4656000536fe658c65c803a196e00e465a8038196200d86578035195600cc6599967658c2140002000000062131fb7996632b6659476300061d9a02b476580ac1db22bd2d5b8af232c62bbc65d8aee000e2bb5a8008ab836e150a0d78516835613aa13484d483d213260d484be370212e60c404b3000065501108ece1d90987d42c8ed61da83b487682623b1346ddccb4000a32c21104caf843732ba10b602688487f9a2105fc6883a4dfa136533e84ce4c7a130cdbf0d5132b22cb4cab8b2c32a62ca8cb18aefb1362bac65d80176588004c000000532b43b1e13441e88350655076b0cb332ce0028cb0844a32be1124cae844832b21118cab844532a6110c0003f6f32c46550cad1966000a32b402c0cb1006c32bc01a8cab0066cb28433b2c610960008000000532c832e45a00cb7167232d45998cb3165c32ec577000715db626c5761963084efdb021180001d8e6ddd30f8ed64c46656ccb28005196234606578ce0195a32a4dbf99631956658865c8b40196e2ce465a8b3319662cb865d8aee,
  0x1b56e2bc1a7188be044622e9ae088b700003b5876a0ed21da03b387660eca5074a46011099a401ee3b18cc734e611ae000141fa85950723b5876a0ed21da03b6010f99a3000e43ac0f790e903dc439c0e310ef034643b40ca90e50322dc2c4b3372312a2dd7c49e371f126aa98c1f42a7b076aaadc1c12a7706e2ed0c5233b5b1462ee5c50e3b57142a43c40be90e302ec21d00020873334243ccccc90f5330cba6cca62eb33292bbbcca32eaf328a21dc582e10b160643dc57d37dd124e54cc1b1bb3606c0000152bab342a5ea0e8ecd1d983b39734821e99a20aca76580061d951730764c5cb9d91172c763c5ca9d8d17290e9048a36fd02a843b0ccc10e502badc70cbb10eb32eaaad019eaa740658a95018dbb9413faed504fb3b3413de762c2c310f102fa43ccccc90f5330cbbb0ca12eac3282ba30ca01d9f15f7121449437dd124e000021eaa57566854bd41d1d9a3b307672e690873334266289888257261e095497f824c0000e46548c93064dfae7e0ccf0afb3b3c0030ecd8bb03b322ebcecb8bae3b2a2eb4ec98bac3b222eacec78baa3b1a2ea4ec58ba8b9a62c26d5b8b08b1362c380001d9c21e6666400390ef02c443a40af90e702bcdc70cbb10f102fa438c0bb37dd124e10f000110f5330c10eccba10f715f410fc495000021d843908751d9c3b34766153aab3454aaa95d41d5cd221e4666000390e31d5443d45d910f3175243c45d090ef173443b45ca10e91716439c5c410e5170c43dc57d5cd315f0767c2cfc3a60b2800008751d9c36fe3b1ed5b1d8d332e000c32d99380cb2262c32b89860000b2462f039383322001876780ae1d9a028876580a11d920281a8008a669c0227c0000ec650b2a0e476b0ed41da43b4076c021f331c000410f88bb044622e811088b769c6032dae000c00000a0ed48c0ec7331a00209848242260608c1cbc09927270262e31086598bc2192955a891d54ea2459bae816d6e3a0580875000721e605fc871817621e20558877815521da0550874815221ce054487281506fba2499b7e090f0874000821e8928566a19a552a063b3f740034fd986353f6218d0fd586313f5218c098599882602661e2e0098489081645c8c998a3b3831c0fd786e73f5a1b98fdc86673f6e1994fda86633f4e197098382d7260a0b589888257261e0954986825325fe09322e789d7724e275a350899873f2265d63f87fa58ec1ed563907715aa21d850ea875d59a01d3d648073e58e01cb63f58a458fc428a23ef0a0c917a281a41e09fe8ff827de3ee09f076840f9043900042a5464d887b8afa087e2be443a8a0721ea6618989997e782865f10ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d77619425d586505746194010ee64f4fde993a262a64e6e698b09000098aed5b29190cb29bf4a97152c33160020989997e262a08b49868226261608949848224260a0888981822126020880000130626204c3897f39193314001c879817f21c605d8875816021e20558877815521da0550874815221ce054487281506fba2499b8e09166df8243c21d0002087a24a159a866954a818ecfdd000d21ea661887b8afab9a62bd8fdb86653f4e1970fde863d3f6a18d8fd986353f6218d0fd686323f5618c4fd486300000a9d62e19fae890a10f8fdc46a04dfb1704cc4800721e605fc871817621d60580878815621de0554876815421d20548873815121ca0541bee89266e382459b7e090f0874000821e8928566a19a553a064a54a818ecfdd000d21ea6618fd98be13f622f80fd78bdf3f5a2f78fd58bdd3f522f70fde8b01bdde2bf032d899a5aa226662f0098b8b802610fdb86653f6a198cfd3865c73f20949c9c823472320894000448521ec10f8fdc46a058e6b24563886594dfa4c2ccc4000721e605fc871817621d60580878815621de0554876815421d20548873815121ca0541bee89266e382459b7e090f0874000821e8928566a19a553a064a54a818ecfdd000d3f6618d4fd886343f5618c487a99863f522f20fde8b01bdde2bf032d899a5aa226662f0098b8b802610fdb86653f6a198cfd3865c73f20935c9c822f723208800001fae3f59121487b043e3f711a8163bac9158e2196537e9301330e2bececf000c3b3a2ee8ecd8bb93b322ee0ecb8bb73b2a2ed8ec98bb53b222ed0ec78bb33b1a2ec8ec58bb1b9a62c26d5b8b10000043d4cc3000825fe096c98482247234266dc8c097f58e41dc5638072d8fbc28323ee09f010e4001043a8a07261a08d49858234260e08c89828231260608c0980822f782865f1c9c098659201cf937e19848ff86608989997e43b0658174719445eda650d746194010ee64f498a993900004c4148c952e261c195ccc288857ef4123d969007f19640014cad196632aa11a06568058197200e865b8039196a00e06588036195e00d465580337ee421a196508677edc2131963084b0004000000299804c560f9132183b14c440e7d33f837e4c7e0db530f035b2a5464d0a96834d76862919dad8a31767428b1dcb8a1c76ae2855d9b0a10782a281c43a000410e628323f187b58fbe1dc563b89b758e6266dc8f82977236096c97f0008261a08d49858234260e08c89828231260608c0980822f72702619648073e2612660e3fe1982262665f90ec1960,
  0x1261209bc980826b261e09549868253724e2759c9f89c172f626b1c9d89a573f2265c32c0003262665f898a8b00bdde2bf032d899a0cae25fc983822325fe087c0002c7158fcb2596692c925aa09bf4988391833722459b8e816021d4001d53a19b621e20628877818921da0620874818621ce061487181836dfc24ac21d0002087a66dd53183e854f60ed555b8382566a0d3dda18a4676b628c5dcb8a1c782a281c43a000421ca66bd53b99ad3f7031c043989ef766c0d81d9a831b262266d10ea99b02a5c66b8879999921ea661974d994c5d66652577799465eda650d746194010ee64f487b8afab9a62bdad5b8af0087e245411188c10000e464a96283a4dfaa95cece1fba54a866e0cd5a91932f0766c2c79d990b1a43ccccc90f715f5734c57b043f1255121449400007232ecdcece2a6254f4aad959a3c1454eca0e937e843d336e2759c9302d70cb0000c983198a0cae65ec987822758fe1fe930e85683b3466a897f926e8fd6291d55a891d874a2445bae816d6df8054c875000710e8001043989ef3b321668ecb85993b2a1660ec885963b1e1654878818a21de0624874818621ce061498899b421e6666487a998643b0658174d994c5d18650043b8b05c2162c0c32d8affbdde2bf487b8afa874c24b1b7f092b2a660d8dd9b0360766a0c6c98a822d262608ac9868226000010ed52b90e221d84390ece5cd23f74a951c8caa742a5e66d80069fb917f87edc5fd9fb517f47ecc5fc9fb117f07ebc5fb9fad17ec7eac5fa9fa917e87e9c5f99fbd32757bbcc9b800026227ee8cda0a0778280d2c43a00042a5464d84398a0c2a46654174d994c5d66652577799465d5e651574719445eda650d746194010ee64f4a988c5f2a5e31530858b0bbdde2c2ae698b09b56e2bc011188c18fbe1db400021d5507454b137e99b004644c18ccf39f9132ce4e04c32c900e7c1958001c7fc13f619644cc46a00cceed5419629183352a9d448b2d510ec210e800148bd141010f449a88740008a9dccd6887313deecd418d952e335c8760cb02f6d3286bab0ca0ae8c328021dcc9e865b15ff7bbc57e843f122a7eec33c45c30cea4c54116b71e0322dc740ae80003f72a95152ba83a72327670872952c2621734937e99af000821d4503887313e11f74395bc14069654a8c9b21d618e24c4ccbf153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c328021dcc9e80002a5c54b2e691fba4dfaa950cd7000410ea285443989ef5d5e6515746194010ee2c170858b032a660dd1dab0371766a0c6c000152f54a8a9dccd689ef766a0c6c439000410ea66a552a890f6dfa0540872000721d666a8ecb85993b2a1660ec885963b1e1654878818a21de0624876818821d20618873818521c6060e1d3092c6dfc24ac21d0002087a668952b035f566a0d3ca97193621ee2be821f8af921e6666487a99862a62657ca9199505d36653175999495dde651975799455d1c65117b699435d186502e698b0910ee2c170858b03b56e2bc011188ba2a660d8ca96835d2a560d2c0003b3778287660ecd29185074e464ece26fd33560030ec98b923b1a2e3cec58b8e3b3e2beee698af721ee056db7e015300007658eca1d903b1c7668ecc1d9c21d666a8cc5130f04aa4c1c120b9f9132ee5e04c9065800064bfc8c086571301188432b9fbb0c951780324c5c10c727ee063813110452a2644572839114107a4265418909686de00059b7f09b26df42609b7b09806ddc25f1b75097a6dcc25e1b7109766dbc5a6c269116d06a0453b5c001803b18003285833503b24cd2ad510ec2b3403a7ac900e7cb1c0396c8bd141120f050147fc13f71f704fa3b95067aed541963b3506360878000822133484c4ccbf21d832c0bdb4ca1aeec3284bab0ca0ae8c32803b5c8510ed520b43b4c8098ed11f9a3b3c7c40ecd1e883b2c780a1d518a9842c581865b15ff7bbc57edcd315ec6e0457a8ed915e96adc5782ab5123aa9d448b043f122aa9544878223117454cc1b1bb3606c04c5411690f5031adbf80c2375d02d4dc740aeb6fd02a00000872843b2a5e21d548c283a54ae54b0ece26fd723266a412a930e3314e7e44cb930704641960001b93833224bfc8c08657130f17843241fbb0c77170031d1fb818e04c44cd3a838334d734c57b065b133410fc48a9313045643d40c6b6fe0308000142c283a58e2a95d53a5ab643a854b0ece2a5459224395c8cad504dfa66a03251fba001b1780cc89fbd32747ee45fe1fb717f67ed45fd1fb317f27ec45fc1faf17ee7eb45fb1fab17ea7ea45fa1fa717e77bbc5855cd315ec10fc48e39390470000142c2c9154e84c44cd38255261c6629cfc8997260e08c832c00037270664497f91810cae2600fdd86788b8619d62f086488b8218e4989997e3f7031c2e698af70cb62668988822921ee063c87a818d6dfc06100002838b56c8750a961d9c50b0a0e9638ac9154ae43956a839194dfa669812a930e3314e7e44cb930704641960001b93833224bfc8c0865713007eec33c45c30ceb178432445c10c727ee0638131104524c4ccbf5cd315ee196c4cd2859114ca0e444f90f7031e43d40c6b6fe0308d404055b4e101400000764821fb56c8750a961d9c5074b1c5648aa5721cab541c8ca6fd334a001876480cc1d8e030076c8af4,
  0x132b6123dfbd88870000001530fa61d4c546588caa19d732cc656c21619550840fdb84263f8c106efdb041800000006987531ea61f32c467580000005110e000c41bbf7a091efe34216195a337c98ac16e392713ab17383781fba001a6554cdf9fb717e4988814fa61e04c698f011b261c044e4c38cc51fa70cd67ee43241faf0c847ed431b1fb30c6a7ec431a1fad0c647eac3189fa90c604bfc12d931104704c1c1191fbd16037bbc57e065b13b2e4784dbc5c21338e4684cdc5e0130ee4e04c345c01300e4604bf800058fca98c65c0cb650b0b1dd639ac9158e2001832b99d515ea6e000059b7f16f26df45bc1b7b16ee6de45bb1b7716ea6dd45ba1b7316e66dc45b91b6f16e36adc584589b1618000076b99d1116d09a026cb5c001926df80058ed6331c6dbc26d9b77097c6df425b1b7b096a6de425a1b7509646dcc2589b7109603b540530ed3014a3b44052418a117906a0453c1881140d38044f821e00020884ce70ec7331aa464ce79b8115ea3b6457a022315e6000032ca83b5132a16541cdab6087654bc439a6fd33a0002098593be26124ef498393bc260a4eec98193ba26024ee4fdd86692622095c9878255261a094c97f824c8d422661cfc89975aa21d8645e8a0678280d3d59a092689081644ece19996fb805fc879000721c6060c875816021e20558877815521da0550874815221ce054487281506dfc24adb8e09166df8243d52b035f54e80cb152a031b21ee2be9d9b0a0b76a827d9d9a09ef21ea6618989997e43b0658174719445eda650d75619415d18650098a9939b9a62c7000026fd0cb210eca9788735232673c25a9b7a00166de45b09b7716c06dd45af9b7316bc6dc45aec1881148d3840520ed0339a6dfc26c9b7d09ae6dbc2680ed701923b540638ec7331a6e0457adab715e0088c45d42691170d70445b800004429bf541da89950b2a0e548c19ce000c3b3c05c8ecd01443b2c0508ec901403b4c5b3b5401164d38045241e90995062425a1b7800166dec2601b77097c6dd425e9b7309786dc425dc1a81156d404ce61b8115ea3b6457a000036fc6df0db70ed61da83b18110a89950b2a0e6d5b0ed0339a001876c80b41daa02c476980b01d9e02b876680ad1d9602b076480ab00003b4076b0ec66a0267300069faf22dc7ed43391fb10ce0438800390eb24dc7e9c5e345c21340e46c12d92fe00104c1cce21fad0e087eac3639fbb0d2c7ee434a1fb30d1e7ea4345462f13cb189c4e4c623135ab37c40e2cd70fb0b34c3ca484b14a7210c51bc83f1436ee882053b9a078cee581c110f102ac43bc0aa90ed02a843a40a910e702a243940a82ac212eaaae84acaab6127adbf048a0658000610f00010657338610ec4882c720ee2b3403a7ac900e7ca95018dc7de141920f04ff47fc13eeecd04f7a1d832c04c4ccadaefb329cbbccca52eef328cba38ca22eec3284bab0ca0ae8c328043d45dd1fbd1602196c57fdeef15fa43dc57d043f15f310182dc1315045a4c34113130b044a4c24112130504444c0c110930104400000439c40b88270e90a97a89b2620e46498710f2b9a47674fdb19c5001a7ec43291fb50c8a7ebc5ea1fad17a67eac5e91fa917a27e9c5e81fbd16037bbc57ec620132517804c5b9790482e4e41191315045ae46011180003f747ee0fd9065959a2b244fdb13073388662897f825b260e08c9c8d099b727026180002c735922e464988130e0cae670c0020875143821cc4f7aeef328cba30ca00877160b842c5819533070aee581c03b3506320000a96a838513667080000007111200144438003108afde8247c04d087c000131526fd32b6670043632cb00ae32a80028004000032d45980cb3165632c45938caf164832b45910cbb15dd626c57500031060fdcc2343f6d0840000065c0cb64c46001930e9955337e0028cb0842632be1094cae842432ae1084ca98b217ed820d1962801019580014cac848e196601fc65a8038196200d86578035195600cdfbd888765a62219963085000080000001884c7ede6598cb18aef19762bbac4d8aea000e2224000195a197032d930fa61d4c546550cdf000b36fe2de4db78b711dac001876399bc36f21328dbe84c136f61300dbb84be36ea12f4db984bc36e212ec76880ba1daa02c476980b01d9e02b876680ad1d9602b076480ab37022bd476c8af483d022b9aa008ad8350229da8008a60000a0e144ca8594c3b6ad810f99bd09706df80059b6f169a6e0457adab715e0088c452c1891142d38004f800036f06df0dbd1b7636e86dc8db8021f5070987476399bc0ee31f785082c731338ecdc1af865600061964cdd2a5733704c34113130b044a4c24112130504444c0c11093010440e460cdcac7f0ff4b25c3e3acd30f28b24c3c1ad510ec2b1c0396c7eb148f200c519483f143b1ffc50b48bd14111f704fa45c30cea21d00021fb818e021cc4f7bb3506364c44cda21d5336054b8cd710f5330c8760cb02e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c328021dcc9e865b3271734c57b5ab715e010fc48a82231182000152a283a2a589bf4fdd1d9c3376002098382d7261e095497f824c262665f898a8b00bdde2bf1c9389d60cb62669cfc899700004c30985130826084c089802c7e5aa09bf498806593374002098282d626060aa0985827f,
  0x13298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c328021dcc9e865b32700002d5b5cd2566a9bf421ec3a421e6a0e144c99f000104c44cda130b277c4c249de930727784c149dd930327744c049dc9fbb0cd24c3c12a930d04a64bfc126131332fc4c545805eef15f8196c4cd46a11330e7e44cb80000cb243cd59aa6fdb9a4b540cf786693f740034fdb8bf28d422659cfc0255261c6628fd3866b3f5e1908fdc86393f6a18d8fd986353f6218d0fd686323f5618c4fd4863025fe096c9838232262208a62e1099c7234266e2f009877270261a2e00980723025fd63907715aa21d85648073e58e01cb63ef0a0c917a281a3fe09f78fb827c0439000410ea281de0a034f2a5c67b50ec19605d1c65117b699435d586505746194010ee64f4fde993abdde2c280005ab6b9a4acd537e843d874843cd41c28990cae67b80030ecd024c3b2c0820ed301ce3b4406d8ec901ae3b540638ecf01463b1c04fb4ef11ecd41c470b5431198d40c462b5c1116ed38445102200002087ccdea8580654ed504fdc7fd0e7cb2444c33939046498700ab93063314dbf048a2a540c764c44114c5c01300e4604bfac700e5a4c3c12a92ff04991f704fa39f9132d1a80334a84707cca17c1d9a85b06deecd418ca89b338454b0c9a9fba18e2b5443b0a1d70ebe54ac1a5a91932f8ed0c5233b5b1462ed5c50ac8bd1410f0545038874000821cccf60ed733a24c4ccbf21d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac3282ba30ca00877327a3b6457a0223114a0000a975cd2566a9bf421ec3a421e6195d44cdab6507067b43349fba18e31a844cb2d510ec2875c3afb9f804aa4c38cc548bd140cf0501a592ff04b64c1c1191311045254a8c9b391a1336e4e04c3391812feb1c83b8ac900e7cb1c0396952d06331f7850647fc13ef1f704f83b3413de4c4ccbf21d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bab0ca0ae8c32800000439a8384dfb7348a970657566a67b0cc4c5c2134117004c21faf0dcee46c130391904484c20cdd130b3311173c4ebac7f0ff4b1c83b8ac900e7cb1c0396aa7406584c14938930324e04c04937c7eb148b1f7850647fc13eeed504fb47dc13e07eec334bb4207d04c34129931332fcba6cca62e8e3288bab0ca0ae8c328087606395eef15f810fc57cdcd315ee196c4cd46a11330e7e44cbaa6212cd1210494953106a0f0501a7b70a03dedf740bd10f702b6dbf00a98000087a54bcfdc13105aa0acd443986594dfa43accf500061da6034476a80bc1da202e876680b81d9602dc76480b61d9e028c763809f69c42301aa008b269c222881100001043e22b941d059d5130160d41c856a3b380030ecb85991dae674476c8af4b56e2bc21d309303b321600eca857e3b2215f0ec7857b3b1a15e8ec985636dfe060c00044058748766821eaa5b54af063a0c541e83b14767811110e333d2001876480f81daa034876880d01d9a033876580cd1da602ec76780a31d8e027da7308dc69c42301aa088b069c222881100001043e22f141f05d15074167544c8584507215a8ece000c3b1a1720ecc859a3b2a1660ec885963b1e16561d5094c874c24c1b8181b76dfe060c87100073b3e2bec87b817521d605b476b99d121ea661ae698b091db22bd2d5b8af06eb82488ecb857f3b26158cec5855f000043c087710ec21d0439887243a43b3410f552daa57556b063a0c510f204451010cf4000721c6060c875816d21e20558877815521da0550874815221ce0544872815021ee2f0c87a8bb921e62ec2e698b09b56e2c22c4d8aea6dfc24c1bae09226df824500038835874e166e2028581874a159c000043d54aeaad552aa61e4cf89870ecd99e732f854bc1a780007828acd548ca6fd33cc001876380cb1d9e02e476a80a61da6029476880a41d9a028876580a11d920281a7108c06a8022c9a7008a4044000041118af31db22e0876b8b79b56e2c22c4d8aea043e228000388358316138e0f484cd831212dc000283b5132a0e530f267c4c386dfccf199ba260a0b5898182a8261609fc984826f260209ac9888257261a094dc9389d6727e2705cbd89ac72762695cfc899758fe1fe964b87c759a61e5164987835aa21d863f58a47900628ca41f8a1d8ffe285a45e8a0843b0658174d994c5d66652577799465d5e65157b69943000021d432ca6fd5232678041dbf8d085e658000500040000657c59d995d1674656c59c99591670655c59b9955166c654c59a996315de001c576d89b15d6000c41b0cbb0052cc90013b2e5003c000131e8cb733be001465a8014195e004596208347eda676c0000cb8195432c0cad0cb21958001530e8cba196c67740028caf164632ac5901952001432d4cc08cbb15dd626c5761963084e6584213195f084a657421219590844655c21099550840000065b0cb8196065686590cac7eda676c5901952001432a8002995b08586584213195f084a657421219590844655c2108cb3003832e400b0cb7002a32d400a0cb1002432bc0088cad0020658c5778cbb15dcfe3041bb2e4106cfdb041832c4105e0000caa261d4c7b626800199da0000001442780031060fdb82223f6d0840000130f261d000c6554cec99be197200e865b8039658c2141fb79966,
  0x11358e4ec4d2c6a11330e7e44cbac7f0ff4b25c3e3acd30f28b24c3c1ad510ec2a98c1f42a7b076aaadc1c12a7706e2acd41a7aa5406371fac523bb43148d200c5193b5b146320fc50ebb9714391ffc50b3b57142b22f45043c15140eecd04fa0874000821cc4f847dd0e5a767c57d843f15f2b1c44c245c10c727ee00068ed733a243d4cc321d832c0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca00877327a7ef4c9d1fb717e47ed45f89fb317e07ec45f79faf17dc7eb45f69fab17d87ea45f59fa717d57bbc5855cd316123b6457a5ab715e032ec577589b15d4088c4528007106a987411400002a5e4c3cfdd391850701964d01800721e6680487581ef21d207b887381c621de068c876819521ca0644878817d21c605d8fdc000d21ea661898999543f7a64e8fdb8bf23f6a2fc4fd98bf03f622fbcfd78bee3f5a2fb4fd58bec3f522facfd38beabdde2c2887b8afa6e162599b9189516ebe24f1b8f89356fba249c0002a6254f4aad953b2b34261e7eeae69043d34046664ece93ff00007ee89895cd23f724c3c21e90f3340228523ff078376ac0dc564909a654ec24da2f10685878c16ad42d19ff36ea14d8dbe84d736fe12e0dbb84b336de12bc763809f0cb0000c32b8980832e23de13488b88312228da7088a258e01cb542386ee8b8218e4fdc000d0440000410f99bd3f6e2fc8fda8bf13f662fc0fd88bef3f562fb0fd48beb3f4e2faa3ee09f04c38089c987198a43b0658175799455d186500fde8b010cb62bfef778afdb56e2bc011188a53f5e1b9cfd686e6262a08b4988822900004c1897f1fba8b9ca26542c88732a5ea46141c1d9d087ae464d00000b36f61300db984bc835022ada8099cc36f213acdb884e71da2036c76b99d137022bd6d5b8af0044623220d588c66a0623140001b7436f86df8dbb1b6e1d8c088542ca85a33fe0034fdb8bf23f4e19acfdc86393f6a18d8fd986353f6218d0fd586313f5218c098719c3262266d0fde993abdde2c2ae698b09b56e2bc22e1099c8b802601c8c097f044622940001fba3f5c7eb1639ac9158e2a0e032b99fe337e32e459e995433ae00100000cb733be000cceb196315df626c5750007111298ac16e2622053e9878131a63c046c9870113930e33144bfc12d930704644c44114b92713aae4784dbb91a1336e4e04c3391812fe1958001865b13b219644eb800058fcb1dd639ac9158e2a0e22e799fd000e43a40f710e7038c43bc0d1b70b12ccdc8c4a8b75f1278a98c1f42a7b076aaadc1c13b43148ced6c518bb97143843b40ca90e5032221d0002087313dedc7c49abb35063654b8cfdaa7733f2a95448a36fd33ee43d4cc32e9b3298baccca4aeef328cba30ca00877327a43dc57d000050710e92e6910f221e0438937e843d21d467f0cdf8cb9167a6550ceba62b07c8ed0c522c7ea0ff4b1f8cdd131104524c34113130b044a4c24112130504444c0c110930104400010000000333ac658c577800715dae4604c22d510ec219600018cb733bf626c58c48bd140c195c4c045c10c7698881cfa61e06b6f0501a5a63c0650987018b952a326c7ee8638ac700e5a875c395952d0632ece8513bb361416ed504fb47dc13e0ecd04f78872000821d4cfd131332fc8760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bab0ca0ae8c328021dcc9e865b3270000141c5cd24dfaa950a9719fb33144c1c16b930f04aa4bfc12613110452e49c4eb39f9132ee4604c206580006195c4c045c10c767ee8638ac700e5a875c395c7dc13e8ecd418c952c326ab1fc3fd2d510ec254ac1a5c7eb148f22f45043c15140e4c4ccbf21d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1ae8c3280196cc9c000010eb7348a972a544dfaa0e0cfd098058e01cb432b00038fb827d032c89a68bc41a1e2e0863b766a0c64a9619353f7431c5649878343ae1e04a95834b8ffe2859e0a8a0710e8001043999f82a5e66b4989997e43b06580a98995f2a46654174d994c5d66652577799465d5e65157b699435d18650043b993d0cb664e00002a774dfb734941c2a5433f2675ccaa844d4c560f91da18a457f1e215a3f507fa4c7e0db563f19ba76ae28523ff0783262208a49868226261608949848224260a0888981822126020880002000000066758cb18aef000e2bb564909a6723026116a887610cb0000ec4d8b18917a281832b89808bc41a1e2e0863b4c3c0d6de0a034b4c780ca130e03172a5464d8fdd0c7158e01cb50eb872b2a5a0c65d9b0a0b76a827da3ee09f0766827bca9799ad262665f90ec19602a62657ca9199505d36653175999495dde651975799455d1c65117b699435d58650574619400cb664e00002a7754a8a0e2e6926fd10e667e000390f5330c43dc0ad90f102ac43bc0aa90ed02a843a40a910e702a243940a8000021d443c887136fd33ee64d8a97834f2a560d2ca968319782a2819d9a09ef10e4001043a8a082a62657ca9199505d36653175999495dde651975799455d1c65117b699435d18650043b8b05c2162c110ed87620000a0e159aa6fd917a67ccc9b152f069e54ac1a5952d0632f0545033b3413de21c80020875141122f03b0ad5033de1960001865733dc8760cb0153132be548cca82e9b,
  0x1113e08780008221339c3b1ccc6a83a06baa26019da8580654a0e018c952c00123b5cce8a91932f854c4caf952b0696546c1a11523064854cc18f9529062c549c18a952506285484189151f062254741880000766eee55daabb3578289bf4111152e344065f89890c71b9a62bd821f891c43ae1cf0a97832c00007ee9daac7fd54e8687c00390e903dc439c0f010e50356dc2c4b337e312bedf7c4a1843c000410ec487b6fd33ee43d4cc310f715f5734c57b043f128ca98c1f42b3b07aeacdc1c9aa540636000087510e221dc43c087610f27684ecd5e0d3c162a5e686c41a3f6d084c658000500040000657c59d995d1674656c59c99591670655c59b9955166c654c59a996315de001c576d89b15d6000c4178cbb0052cc90013b2c5002a000065ba61d3430211d9d2002a19540014002000019722cf465a8b3019662cac6588b27195e2c906568b22000620c1fb6842032a8685465d8aeeb1362ba8003884a000032d8986131026084c18987262a25fc1964fdba61d4df8685821a995a32ccfdb84263fcc107c9878339a67c0cab17084d046201324e46c130397904844c20004130b04684c0c118393813171784323263d33b40008000000534284c04d09a61c0c6f17004c22c760f6ab1c83b8acd00e9eb24039f2c700e5b1f8851447de141920f04ff47fc13ef1f704f80872000821d4d09391933148760cb02e923290ba38ca22eec3284bab0ca0ae8c328021dcc9e931518204c4c602deef1615734c584dab71610658c5778cbb15dd626c575000710940000caa26fc26204c10983130e26184bf832c9fb7196c98a8d0a803419586775963884e32b6123c659807f196201f865c8031195600a930f99d732c62bbec4d8aea7ef6221d9698886000e21299d288470000655065b26fc4c5432e930e8005342800d065619dd658e2138cad848f196601fc658807e197200c4655802a4c3e675dfbd888765a622199d288470008000000199da32aa683465b99df4c441abd31e064632c62bbc65d8aeeb1362baa2e309bc8bc0262c003884a723e0a61c9c822f00009bf1315261d3f6eb1dd64886592602684c004130705ae4c1416b130305504c2c13f930904de4c04135930d04a64bfc126392713ace4fc4e0b97b1358e4ec4d2b9f9132eb1fc3fd2c970f8eb34c3ca2c930f06b5443b0c7eb148f200c519483f143b1ffc50b48bd14104c4ccbf21d832c0ba6cca62eb33292bbbcca32eaf328abdb4ca193153272000043a865926204c38d09000d3f4e6824fde863d3f6a18d8fd986353f6218d0fd686323f5618c4fd4863000007eb8fdb1fb83f751704d0819bf19722cf40038aedb1362bb0cb1844b7edc11100000cb64c469874caa9a0d148b1fa83fd21d832c0ba6cca62c7e13af17383763b4207c80000fdb952b10e619653159a0c00104c14118930304604c04117b93833224c4c600931117ee4c3c5f7130d17cc4c2c5ef930917b24c1c5ea131516017bbc57f45e10c847ef431ec5c00c66000097f2c913f5e6828004131317fa4c445f9930f17d44c345f1130b17b64c245ea930717a04c145e6130317924c045e392ff178c4c545805eef15fc7ef431ec5c00c5e0000fd39a09001a7ebc3739fa70cb9173c4ebc6a11330b1fc3fd2d510ec31fac523c8bd14108760cb02e9b3298bdb4ca19fbd32740000fdc1fb63f687ec8fd81fac3f547ea032c9fba10ea681c00186591308195c4bfac700e5b170431c9fb8001b1f70d02952f34088760cb01fbd3274196cc9c1fb717e47ed45f89fb317e07ec45f79faf17dc7eb45f69fab17d87ea45f59fa717d57bbc5855cd316136adc5780223114a98741140000261e7ee941c3918340c64d4a9683192a560c5dd9a09f410e8001043989f02a62657ca9199505d36653175999495dde651975799455eda650d746194010ee64f4000152e4c38a0e23ee1a050ceb17084ce283b1176b1c83b8821e00031f7850802211144ecdc1afb4e30196d38004f8ec6000c3b5482c8ed320243b447e60ecf1f0e3b347a18ecb1e003b2475f2a571256dbfc0c190e233ee43accd51d9d0ad2766c2b39d990acc765c2b29d950ac876442b11d8f0ac243cc0abc3a41220dbf0487843a000410f4d012a6307d0a9ec1daaab70704a9dc1b8ab35069ea95018dbb43148ced6c518bb971438ed5c50abc15140eecd04fa0874000821cc4f847dd0e5a10fc57cac7112fe7ee0006865600061964d018ed733a243d4cc321d832c0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca00877327a7ef4c9d065b32707edc5f91fb517e27ecc5f81fb117de7ebc5f71fad17da7eac5f61fa917d67e9c5f55eef1615734c5848ed915e96adc5780223114a98741140000261e7ee9c8c28382a5e6810425a61e04c6cb1c0198caa000a32e47010cb71b8c32d46c58cb31aa232c468c0caf19c032b4654b91a1340b1c83b8c5c30ceaa0eccc69b7f1d5b1f785083b3706be3b180030ed520b23b4c8090ed11f983b3c7c38ecd1e863b2c7800ec91d7ca95c495b6ff0306764800610e233ee43accd51d8b32a476742b49d9b0ace76642b31d970aca76542b21d910ac4763c2b09d8d0ac043cc0ab800200000014cc043a41220dbf0487a9190cce98ac16e2643055e99fc141263f04e69bf412a843a000410f4d01392713ace4fc4e0b97b,
  0x14c8498f952a2d5043a8767032b9a2e02c043a8cfbb71c122cdbf0487aa740658a95018dbb5413ececd04f7aeac3282ba30ca0000010e654bc21d90f221c468b43339fb8001a7edc5f91faf17dd1a844cb39f804aa4c38cbd93113368aad448f2a75122e7ea43541fbb0cee7ed43391fb30ce27ec43381fad0cdc7eac336c4050afb0f142b8130d04c44bfc12d9d92001917184dc45c21338e4684cdac760f6ab1c83b8ad510ec276742c8a91834571f8851647de142122f45040874000819580018659344a21cc5059d9b0b1e76642b31d970aca76542b21d910ac4763c2b09d8d0ac0ecec1d1bb3706bea96c4a3aa571257121449343a4122010e80011fa734124c4ccbf21d832c0ba48ca42e8e3288bdb4ca19fbd3274196cc9c1d8b17097bbc5850877160b842c5819d9f15f7734c57b043f125410f44939533063ea95018db703036edbfc0c1b7dc02ec000159a3b354dfa54bc8719a2c132d1a80332b9f804aa7ed8006930e00107ec43381fbb0c947ee43241fb50c8a7ecc3221faf0c847eb43209fab0c807ea431f930904c04bfc12d930d046a4c2c11a130704644c14118930304604c041179311334f17084ce391a133717804c3b938130cb1c83b8ad510ec2b24039f47de142122f450447fc13f6ed541960874000821cc505aa75122f0f142bb3b3706be7670d15285934527e9cd04931332fc8760cb02e8e3288bdb4ca1aeac32827ef4c9d1315327221dc582e10b1606a95c4959d990acc765c2b29d950ac876442b11d8f0ac276342b01533063edbfc0c180000cae766a1d2843b21c6ecd537e952f523068ac5f91fb6001a4c38cbd9fb90cea7ec43291fbb0c947ed43229fb30c887ebc3211fad0c827eac3201fa90c7e4c4413292ff04b64c3411ac5c21338e4684cdc620131d17804c3b938130cb1c83b8acd00e9eb24039f47de142120f050147fc13f6ee5419ebb55065821d0002283b331a21cc505aab5123ca9d448bc4050afb0f142b83b3706be76480060ec6344c7e9cd04931332fc8760cb02e8e3288bbb0ca12eac328221dcc9e9fbd3274762c5c25eef1614767c57ddcd315ed6adc578043f1262a95c49582231174dbfc0c180005230195cecd1d983b2c7650ec81d8e3b1810ec871952f3b3868a8638152d06327674d13a899115ca0e44501fa90d507eec33b9fb90cea7ed43391fb30ce27ec43381fad0cdc7eac336c1e90995062425a130105304c44132930d04c44c2c130930904c04c1412f130304ba4bfc12d9b78001717184dc391e136f17084ce391a1336b1d83daac720ee26dfc26c9b7d09826dec2601b77097c6dd425e9b7309786dc425dc7e214591f785084269116d06a0453887400080878000a83b331a6dbc5a688731416088445bbb3b0746ecdc1afb5c001803b18d1421d832c0ba48ca42e8e3288875462a0877160b842c5819b8115eb6adc5782a5b128ea95c4958223117454cc18fb703036edbfc0c190f50300df700bb00005230195e1d2843b21c6ecd537e952f50b268a425a9b7a00166de45b09b7716c06dd45af9b7316bc6dc45aec1881148d3840520ed0339aa260d139fa90d507eec33b9fb50ce47ecc3389fb10ce07eb43371fab0cda4c0414c130d04c44c2c130930904c04c1412f130304ba4bfc12dc5c61370e4784dbc5c21338e4684cdac760f6ab1c83b89b7f09b26df426b9b6f09a03b54063c7e214591f7850842691170d70445b887400080880000821f344621cc505a8380ad2ecec1d1bb3706be7670d130ed733a28760cb02e923290ba38ca20877327a6e0457adab715e0a96c4a3aa571256088c45d3703036edbfc0c1800050b2a46032bc3a50876438d37e952f1d8c68a05f91fb6001a4c380041fb90cae7ebc3289307048318804c73978131ab3403a7c83c1404ee5419e9fa734124c44cda131332fc8760cb02eec32847ef4c9d131532737bbc5855cd315ec10fc491aab5123d10142c180003b3a7ea09801fba3f687ec8fd81fac3f544c30985130826084c0897f065710ea10eca97a898344e001876a90591da640487688fcc1d9e3e1c7668f431d963c007648ebe1dae674487a99861db22bd00000ec6b56c438cece1a26000c3b5482c8ed320243b447e60ecf1f0e3b347a18ecb1e003b2475f1d9d0aeea160cd3ac900e7d1ff04fdbb550658a9d448bc3c534483b1ccc6a83a04cae4684d045c30cee7ee8cda284705bca16c13a931033744c1416b130305504c2c13f930904de4c04135930d04a63b6457a5ab715e0e49c4eb393f1382e5ec4d6393b134ae7e44cb82231174b1fc3fd2c970f8eb34c3ca2c930f06b1c83b8ad510ec2a464cf047eb148f200c519483f143b1ffc50b47de142122f45040874000821cc505bb3706be3b5cce890f5330c8760cb02e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeac328221dcc9eaa571256dbfc0c180003b350e9421d9d8a21c69bf4a978659344a67fcdbb853736ea14d8dbf84d936fa135cdb784d0832e23de13488b80440000410f9a2350b015d941c05693b38003011188ba3b2615c0ecf856b3b321598ecb85653b2a1590ec885623b1e1584ec6856000003b19423285a5230766a1d29d8a4dfb0f14d12198e1db202a476a80a61da6029476880a41dae6745a70089f0000a16541c8ec6043e688c0520ed03398d40045334e0,
  0x1766a0c6c0001310b56c54b141ca85b50bea19d37e261db13421d4872152f3b38438821daa54346e10b8caf000a32b62cb9fc6083b65ca0070659000532b2125ccab847232ba1144caa844d32c21104ca9843a1962021c6578062196a0104656803d197200c4655802a7f362239979888d7f2621c997588717f1e21599738855809a21219d288470008000000199d64c960bad32182af4c7e09cd30f02634c7808d865b9a18261c670ccb18aef19762bb9c8d099b72702618003884a0000e519c9f393a7232195c98826fcb1349875648ac73346c12d4dbd000b36f22d84db98b5e36e22d760c408a469c202907681a3436fe14f0dbb853736ea14d876781271d9a049a0cb88f769de23d942386ee36fa135cdb784d08b9e275613488b8724c0b701100001043e68c131519d71d8e663541d06755130195d41c063900080000fdc1a1032aa683400199d63f6e2fc9311029f4c3c098d30e0227261c002098899b43f5e1944fdd863b25fe096c9838241261a08989858225261208909828222260608849808220723c26de2e1099c7234266e310098e72f026362e00980723025fc32b00030cb268c948c9a2f37022bd41118af358ec1ed5639077159a01d3d638072d196e677c76c90ef1daa41787699017b56e2c20cb18aefb1362baa3f10a2c8fbc284241e0a028fb827d000388584c96184532185dd4c7e16a531e057476760e8dd9b835f772a0cf5d9a831b3b340030eca8b9887a625b21e5895054b6251e1e3893454ae24ad55a891d54aa243d63f87fa5aa21d8554183f954f60ed553b83716e5407f5b9101c96e0606f1b8f01956dfe0621bae816e21d8001db7e99f73b166549db18a4d8fd6291ddad8a3176ae285645e8a08782a281cecf85783b3215ccecb85723b2615c0ec8856f3b1e15b8ec6856d21ee05a0878816321de0588875816021d2057c873815e21ca057443a000410e668b4879999921ea6618989997e43b0658175d994d5d36653175999495d24652175799455d1c65117b699435dd865097461940262a64e432d9938bdde64dd0ea8c54b9a62c7043b8b05c2162c0e1e209176e382458a99833076a80cb4000043b21c454bcece2a75346a12d4dbd000b36e62d48db88b5183102291a7080a11d9400187649a3336f212fe0d488aa50b267341100001043e68c076b99d137022bd476c8af404462bcc0001b7e36ec6dd07670ecc36f86db8763289950723b507695ab61da068d00059b7b096a6dcc2589b71169e6e0457adab715e306204520ed901aad38806634e101400000dbc1b7e36ec6dd0dbe1b6e0442a0e47649a33000c3b3c0938ecd024c3b2c0820ed101b63b2406bb4ef11ecd41c470b503118a0880000821f34603b1ccc6a84705bca17c158a85b04eaa0e8132a898048ea0e0114b92713ace4fc4e0b93b134ae4684d039781324e4604c22c7f0ff4b25c3e3ac930f07170c33bc6210cb3170431d9fba33691fac523c80314651ffc50b131034623b5cce8a1d832c0ba6cca62eb33292babcca2800052303b507690ed80444b1cd668ac714c7a990931f2a565568a95043a86593464001876781271d9a049876581041da2036c76480d769de23d9a8388e16a0623141100001043e68c144c06571d8e66363100992508e1bb942f86c150b61a1541d067572f20914fdc1a075070680ca970c718b84268133e883e3f7618edfe684367236098ccae000a8b80261130f884b32a6107dc8c8227658e00cc65500057eda676d30e99da196a6604cb0842f32be10b8cad842c32b210accab842a32aa10a465c801f19660070658801b195e006865680197f1820dd97208360004000000299804c560b7133f82824dfa66ea2e789d7724e275a2f389c272f626b22f189a658fe1fe964b87c759a61e5164987835aa21d850eb872b261209bc9868235261608d09828231260608c0980822f3f6e2fc8fda8bf13f662fc0fd88bef3f5a2fb4fd58bec3f522fae3f58a47900628ca41f8a1d8ffe285a45e8a088fb81cb9c9d8272727008dc9871a12196e677c76b99d1262665f90ec19605d36653175999495dde651975799455eda650ef778b0ab9a62bd876c8af4b56e2bc0cb18aef19762bbac4d8aea087e245411188ba000e2160000065952303b507692c7359a2b1c531ea6424c7ca95043a93103462001876780b91da2029076680a21d96028476480a01dae6745aa008ad69c0227c00028991d8ca0e476a0ed21db0087cd180c703f72199c98882578d422661cfc89970cb0000c32b9a2e21ea661ad5b8b080cb62668a96834d0000b1dd639acd158e3626931ea64a4c8498f952a2d5078288750ece2919345e10b8caf000a32b62cb9fc6083b65ca0070659000532c21104ca9843a197200c4655802a809a21219d2884732b2125ccab847232ba11446588087195e018865a8041195a00f537e999e73f22659fcd888e65e62235fc9887265d621c5fc7885665ce2156350066700080000caa9a0d00066758fdc0c704c440a7d30f02634c38089c9870008262266d0fdd863b25fe096c9838241261a08989858225261208909828222260608849808220196e677c87a9986262665fad5b8b08262a2c02f778afc32c62bbc65d8aee723c26ddc8d099b0cb62669cbc098d8b802601c8c097f000e2160000152c5232b1dd639acd158e3626931ea64a,
  0x18b8e1ace2e186773f7431c63f58a47900628ca41f8a1d8ffe2859639077143ae1dbc65b9a18262665f90ec19605d36653175999495dde651975799450cb664e2e698af654b6251c21f893154ae24ac003884a6e0606ddb7f8183000010eca97196258ee9bf133ea61d50751f7c43a90e334ce68c076a80a61da60295a70089f043c00041109a601db22bd2d5b8af0044622e8000284650bca26942d29185132a0e47631a6600166ddc2649b7f096e6df425b1b7b096a6de425a1b7509646dcc2589b71096107a04574188114008780009b6f169a6e0457adab715e0088c45d0221116ed70006000004c38a46144ca8391d8e6994ced995b086a32cc0128cb9002c32c40090cad0020ff3041f3324107afdb041832c4105e00080000cb734300014cc00007109498ac1f22643076299fc1bf263f06da9bf41a5a67c0672987018b800076b4ee59dab3c14772aed09d9a952b34c668c076a80a61da60295a70089f043c00041109a601d8e663476c8af4b56e2bc011188ba508e0f9942f83b351360e0142d836f50740d7548c834d51300ced41c03190000ecdddad3b9676acf051dcabb42766a54b4d3080061d9e049c76681261d96041076980e71da2036c76480d71daa031c76b99d11db22bd2d5b8af069de23d9a8388e16a862331a8188c5044622e9ae088b700003b19423285e5134a16948c022134c0663541d035d52320d34000152d7828ecdc7639a5c140ef0501a78874000854b8638887313e0875c396131332fcbdb4ca1ae8c328021dcc9edcd315eeacd0493aa541224df700bb10f702b6dbf00a78000087b1f70fdd10e334a831c50eb872c2a5e0d7c989997eb9a62bd821f893154ae24ad52a09116dfe060db7e014f00010e9421dbb378fb87ee88719a5102da43a8cfbb75c123adbf0487aab4067aa95018d800021c410ec8763b95766aed09e0d3c1621e043b8879152f349e001c878936421de4c44875926e21d2487887391cf21ca460487a9986262665f887b8afa000043c887610e23f75734897f9a4d00104c3ca001309277a4bfc9dc5cd316124c44cda1d9c33324c4ccbf131532736adc58a800026184c28983130426044c00fdd1fb90cae43ccd2584b536f4002cdbc8b6136ee2d80dba8b5f36e62d78db88b5d37022bd6d5b8af18310229076c80b46a0002bda7080a40000a0e4dbf1b7c36dc08847689a46000c3b3c06d0ec701ac3b540530ed3014a3b440520ecd01443b2c0508ec901403b5cce8b5021184d38044f8000043ea0e542d8ed834800a7d31199bf32a866f9c8f09b758ec1ed530f026332b667023f10a2c7234266d639077176760e8d31582dc261c662897f93118fbc2841c9389d554b6251e2e706ee766e0d7db8181bd21dc001d52b99b61972381942308f621e205c0876816e21d605b4874816c21ce05ada7701271d9c0019bae091d55680cf476680a21d96028476480a077282809a7008a4907a1d3e0c484b41da602ecdbc000b59a22639aa088b08c42195cdbd84c036ee12f8dba84bd36e612f0db884bb21ca68e944c99cd835022ad42c0648260e08ca2f009877270261963f87fa59201cf9a8099cc8fd6291e3fe09fb36fe1364dbe84d736de1341daa832c1daa031c43a000454ea68d44399a2d196e686076b99d121e66664763998d21ea66190ec19605d36653174919485d1c651177619425d58650443b993d21ee2beae698af6b56e2bc00038aed087e245411188ba84d222e1ae088b7262608ac98682260000a46141d9b8050723b607681d9c54a8e464871589a3f74088421d93103f7254bd37e86574c3a68ecce729190ccea26032bc6a1132d18804c72d510ec2b3403a7c8bd141120f05013b95067ae7e012a930e32f28760cb02f6d3286bbb0ca112ff23024c4c6035eef15fcaad448e9fbd0c7b170031d375d02d40000872dcd23f744c30988043b2a5e21d541c822150b29bf541d86573f7268e81191306333ce7e44cb3938130d1a8033386560006e460cdc8659134ca46045c45e20d0b09a026ca6fc346e7ee063813113470b1c0396c7dc13e8ecd418dd89b161aa954487ac7f0ff4b25c3e3acd30f28b24c3c1ad510ec2b24039f261c096e54b41959b7e0016dbf4cfb90eb1fa043947e6c7eb148f200c519483f143b1ffc50b48bd14111ff04fd9b7d096c6dec25abb55065821d00022a75346a21ccd1690f3333243d4cc321d832c0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac3282ba30ca00877327a196cc9c21d518a86de45b09b7716c06dd45af9b7316bc6dc45ae9b6f16b9842c585deef1615734c5849b8115eaa19847ea85e11c2a168462a85811530620452350e0266d418083b50201b6d400057b4e101480000768dab6507210eca979d9c21c40884d1c89808b8218ec32b00033f7466d032d89a80cb22695c9d02750000b1c552a285b59244c44d1c018821d866d9b7f092b54ac0d7dd9b0a108fbe1dc56399a36728e2771c9f89c072762691c8c097f0cac000c32c89a6593e202d64b87c759261e0d648073e58e01cb62f706fd8bcc1b062f106853f7618ee2e0063a3f7031c24058a4e900628ca3ff8a168ff827ee3ee09f476aa0cb153a9a3521ea66190ec19605d76653575999495d5e651574719445d58650574619400cb664e10ea8c54c2162c2ef778b0ab9a62bd821f8915,
  0x16fba249c00026fd21d0a98953d2ab654ecacd087b10e2087a69e4d1243c4122f0e9048800003b34762952a8ec654ea9bf5423285a523010ecd3c0002087a249c21d8910874a15a5bee017f3b3866648790c6f3b36163e242998954e8669e2e109a058e41dc5648073e8b8018f152a19fa8fbc28423fe09fb5072228159a8669831212d5daa832a36f4002dd9b9a5c2a5864d635089985aa21d850e9875b36fe1364dbe84cc36ee1324dba84c836e6131cdb884c636f212fca95834b7236099421f8af9917a2821e0a8a07507622ee13488b683d022ba0d488a8043c000548c99e01dae67450ec19602a62657ca9199505d36653175999495dde651975799455d1c65117b699435d586504fdc8bfc3f6e2fecfd78bf736de2d36e698b09bdde2bf4dc08af5b56e2bc011188ac044222a498a824b72f00921a7180cb6b800301a8000aa00003b1d42c131110eaa26432c952e3f77626898726fd34ee002cdbf84d936f21328dbe84c136f61300dbb84be36ea12f4db984bc36e212ee13488b683d022ba0d408a7043c0004db78b4d044222ddae000c01d8c69c0dc08af5044622e800028994dfa9875423285e5134a16948c5ab650b269d4c9a952f067a54b419dbb94140520f43a7a1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeec3284b3444c93979048e0000a95462055684c4432c8875513069ccc9a952f067a54b419d952b0672ee50501483d0e9eb3444c93979048ea264d38a63d33b46554210267d34d08760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2af6d3286bbb0ca15ab715e0088c45d3f6c10600000001d89a50b2987548c284650bca26942d13110cb3188043aaab434e4002cdbc84ca36fe1308dbe84c136f61300dbb84be36ea12f4db984bc36e212ee0f408ae8350229c10f000136de2d3411088b76b8003007631a7037022bd411188ba000098f142ca61d508ca17944d285a52316ad944c9a71337a0878000a83934cc0884d3002231174000144ca8594c3aa11942f289a50b4a462d5b0ec634e06768caa99d94c3e67580010000000a660131583e44c860ec531f836d4c780ca0a9519352a5e0cb0a96832a76862919dad8a3176ae2855daa09fb8ffa1cf964899a743b06580a98995f2a46654174d994c5d66652577799465d5e65157b699435d586504cb18aefb1362ba8003884a00009bf153a261d262221d533f285834de001c87981f421d607bc87481ee21ce071887781a321da0654872819121e205f5b8589666e462545baf893c6e3e24d5bee892754c61bc153d86c3556e1a5953b8687566a19a4fdd19b42620684898782dc4c546850caa84567f9e217533f9a6d196e686087a998619762bbac4d8aea000e212800010e28b9ce49a2f3462272f5178a3500659000a9bf130e90f610ea10f4d37000721d607bc87481ee21ce071887981a621de068c876819521ca0644878817d6e162599b9189516ebe24f1b8f89356fba249d53186f054f61b0d55b869654ee1a1d59a86693f7466d09881a1221ea66189878282000010f487145ce8bcd1889cbd45e28d40196487b08754cfe69b400390eb03de43a40f710e7038c43cc0d310ef034643b40ca90e5032243c40be90e302ecdc2c4b3372312a2dd7c49e371f126adf74493843c000410ecd35aa630de0a9ec361aab70d2ca9dc343ab350cd254bc1969fba3368a9d0cd3931034244c3c14145cf13af179c4e14623135ae5ec4d645e3134d1a844cc06580006195cd352c900e7d1ff04fdbb550654a164453c1a9098498f441db2e5003832c8ceeac7f0ff4b25c3e3acd30f28b24c3c1ad510ec232ac0150cb1002432b400810f715f410fc57cc7eb148f200c519483f143b1ffc50b48bd141099f842eb3a5108ecb1041a2c720ee2656c2118004000043d4cc321d832c0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac3282196cc9c0cb9168432dc59ddcd316136adc5780cbb15dd626c57502231174a46445a80071094000c418426909b0ff3822d99630872ff3021bbf8d085cfdb4212800058ee9bf133e9b7f043e987541d152d8fbe21d4caf9a6c34244c44cda130f05047eecd34b97b1358b34c3ca06580006195cd35483f143ab1c83b890e334ce8760cb02eef328c196cc9c00002a5cb24542c263c4cfe658963ba6fc4cfa987541d47df10ea10ecd3580082612098097f825b262208e09878236261a08d49858234260e08c89828231260608c0980822f262665f898a99397234266dc9c09860000b24542c263c58e6195cd35000721da0620879816421e2058c877816221d60580874815f21ce0578872815d6dfc24adb8e091654ac19dd53a19a78b842681c8d826526206848987828272f626b1669879421ee2bea41f8a1d21ea66190ec19605dde651ae698b09b56e2bc011188ac00007eec871043b5922a16131e267f5074b1cc43a865934d2676ccad84351966009465c8016196200486568010196e6861fe6083e664820f5fb60830658820bc000267d4c3a000cd34043532b46599fb7084c7f9820f8001000032aa683400299804c560b7132182af4c440a7d33f82824c7e09cd30f0263261c68489888265724e2759c9f89c1723c26f1cbd89ac72762695c8d09a00cb0000c32b899c58fe1fe964b87c759a61e516498783,
  0x1000821ccd4321d7350aa9d849b43c60b4a7650cd52ab532ea76642b99d970ae44c4ccbf21d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bbb0ca10877327a196cc9c0ed7214a3b447e81d911722763c5c85cd315ef6adc5782a6212cd0f1048d8223114adc280f7b71d02c043dc0ad90f502b2dbf00a980003b3476288759d9c087aa0e153aa6fd351028b23f187b576760e8563b99fd507e235d648073e043c00063fe09fb04422289daa832a69ce03dda70009f1d8c6a0542c9a754c38089c987198a260e0b5c9888229724e2755c8c097f58fe1fe9638072d508e0f9942f83b350b60dbe3f58a4776862919dad8a3176ae28563ee09f425fe096d44d99c243b0658174d994c5d66652574919485d5e651575619415d186502d5b8af07234266c11188a5766a0c6400028990caf173d48c152d10eaa9d541c26fd58e66a1cceba62b07c80010000196315de001c576bb43148b1fa83fd000334d06554d06ac7e33fa32dccefd89b163117383782622073e98781ada67c067298f0194261c062e54a8c9b1fba18e2b1d83daac720ee2b24039f2c700e5a54bc19e952d06331f885143b3a144f1f785063b361416ee504fec7fc13eeed504fb47dc13e0ecd04f7931332fc8760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca05cd315ec10fc491800043acaad1531a83810e66a180020875142c21cc4ff2eaf328abbb0ca10877160b842c58221db0f091ff83c0c83d0e9a000153baab443ae6a14638a1d70e9a54bc19eaab532ea76742bb43c41236dc740b010ea33ee7eec37836fc3506a988d41131332fc766c2c79d990b1a762c2c3000089089bf62e7283854aa43c087910e2087aa16153abb95907b7348d42000721da2e5c877816221d2057c873815e21ca0574ec9000c6e3865d8ece85693b2e1594eca85643b221588ec785613b1a158087a99863b166548ecf8afb21ee2bea1d2091421d6054c00036fc5070a95421eaa753b30766ae6910f021e44388d41995d3b3a15a61d219fc6dfa67dc87581ef3b16654821f89696e1625980002a62b9a49bf421e90f021e4438941c2a553b307668d411a7921d207b887181766e162599bee89270878000821d9a7a54c60fa153d83b5556e0e0953b8371566a0d3ca95834b21ee2be821f8af976862919dad8a31772e2871dab8a15782a281ca971a805d36653175999495dde651975799455eda650ee698b09b56e2bc011188ac000021d553aa858508ca16948c0ec651329bf4d408569874867c0ece19995668249dbee017f21e469fe2e799fd58ec1ed563907718fc428b23ef0a1076760e85d9b835d507e235d41d88bb69ce03f5a7180d11da40019638072d1daa02f076880ba1d9e02e476680b81d9602dc76480b654a867ea3ee09f46a8022b5648073e766a0c6410f0001507269981109a608ff827ed42f83b351360e01daa832a0878000821d9a7a2a5864d563f87fa592e1f1d669879459261e0d6a887612a560d2c21f8af98fd6291e4018a3276b628c641f8a1d772e28723ff8a16917a2821e0a8a071dae67450ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d75619415d186502e698b091db22bd2d5b8af0044622b0000152e50b0a11942d29181d8c21d553aa6fd51326a00d3f36fc34f8762cca900008b9cb1cd41d2c7154aab24541c043d58fcb2596692c925aa0a9d421f26fd21e469fc0bb10e233eedf74493ab350cd243ac0f7c6a11330dc2c4b32a630de019600019fba3368195c4bfb91904524c40d3e865b13340001648a8388b9cb1cd638ac925aa010f563f2c9659a49bf5b7e90f234fc05d887119f76fba249d59a866921d607be35089966e16259953186f073f00954fdd19fe261c670c32b00030cb266e89868226261608949848224260a0888981822126020881c8c19b90cb62668fd786e73f5a1b9800036fd21e51739639ac715922a0e021eac7e592cb3496492d504dfa4c40d3e858f890a6624ecd195d8d42265953186f03f7218e5cfc02553f7467f898719c38b8426722e009800cac000c32c99ba261a08989858225261208909828222260608849808220723066e49889a7b3b3a15a4ecc85660cb6266a1d209143f5e1b9cfd686e60000762a2e72c735074b1c552aac91507010f563f2c9659a4b2496a82a75087c9bf5b7e1a7c0b1f1214cc49d9a32bb17084d046a11330a98c37845c00c7819600019fba33687ee45fe5eef15f8196c4cd065712fe7ebc373b91b04cae46411480002622a0e141d2c718b9c762952ab6fc3b3076716a82c73087c9bf553a9a7b34c0a17c1d9a89b07000880000821f3460a0e0cfd952c326c3b5482f0ed3202ea954487b6fd02a843b0003952f346a438cd1310f3333276742bb10f702d043c40b190ef02c443ac0b010e902be439c0af10e502ba43d4cc3153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c3281734c5848ed915e96adc57843c4122edc7048b02231158000021da85854ea54a9dcb3b5a4dfaa11942d291851323b18d3d000721d607bc87381c621de068c876819521ca0644879817f21e205f487a99866e162599b9189516ebe24f1b8f8935,
  0x137022bd6d5b8af00446229411088a26b800301a70009f0000a46144ca85950709bf47639a9706beecd8505aa571256dbfc0c190e2345aba38ca200002a5e43c8439843b352c15a4ece1a358748244152a031b0874000821e9a9421c668b153a1a1f8ff827dddaa09f6766827bc43900042a5c31c443a8a08087e24a90eb875e566a67cc989997e5eda650d75619415d186502e698b0910ee2c170858b04b56e2bc011188a543b61d88000065958e27ee941c26fd917a6a54d0028980b06e460d4828583509173c4ebc4041244b1fc3fd29190b22dd740b69d9c351043a8cfbc7eb148aed081f436fc3506a988d412ab4067aa95018d92ff3522a9d0d0fc83c13fcee504fec7fc13eeed504fb3b3413de766c2c79d990b1a762c2c310f302fe43c40be90e302ec4c1cd49a1d832c0ba6cca62eec3284bab0ca0ae8c3281734c57b043f1255121449437dd124e0000a978873566819656389fba50709bf421e9a943504766c2c79d990b1b12144942a6307d0a95018d843c000410ecd1690e3345843cc9de10f126d0ed0c522bb3413df1fa83fd131332fc8760cb02e9b3298ba30ca05cd315ecb1f84eb043f1254e49816b80002a5e21cd59a06593f74a0e137e930735264ee08791a91262665f80001fbab9a4438897f9a92257e43b0d26931332fc00008715cd23f7443c897f9a9133ae00100001955341a000cceb26220d5e9878339a63c0c8d17184de45c2134117804c5b91f053ce46c1313939046a4c3000413090556e4fc4e0ac970f8f200c5183b5a076aa9e84a943ca0bbea178d471b7d09ae6dfc25c1b7709666dbc2578ec7013f09a445c41891146d38445102200002087ccdea8980b064c14938930324e04c04937c4041244dd740b6a858350843a8cfba9190b2243cc0bf90f102ad121449437dd124edbf048a043c000410ec48843a50ad24c2cd478cb734307670638196315df626c57500071112b1d83daac720ee2b24039f262b0dd8987031baab4067aa95018d952d0632438cd162a74343e7ed8d0847e214511f78506483c13fcee504fec7fc13eeed504fb3b3413de7ee431c930f34064c44cda10f5330c4c4ccbf21d832c0baccca4ae923290ba38ca22eec3284bab0ca0ae8c32804c54c9ca1d518a9842c5815cd315ed6adc57808771414bdb450245c0130810fc4950223114a7ebc373bc15069c4c1c11192ff043e0001c8c2c7156689bf62e71fba507054bc43986593520675c002000032aa683400199d64c441abd30f06734c78191865b9a1832c62bbec4d8aea8b8c26f22e109a08bc0262c0038889723e0a75c8d8261727208d0000262a4c3a7edd63bac73592219649859a8f00166dec2601b75097a6dc425dc1a81156d404ce61b790a2e6dcc28a0ed1020e3b5cce89b8115eb6adc578022311c906bc471350711c20000dbe1b7e36ec6db8763022150b2a178d4706393f7068422e0098472326628fdb8665261e095498899b48d422661cfc899700004c1832cac7125fc7ee8fd728384dfab540d46998a260e0b5c9878255724e2759cfc89977230261032c00030cae260163f87fa58e01cb62e086393f7031c23f58a458fb827c0a96831910e400110ea8c5410ea281dda103e878280d3dd9a031c262266d097f926e2a5c31c56a8876143ae1d7cfdd86f08b9e6a2e45e99f3566824a2242058f3b346a20989997e43b0658174d994c5eda650d746194010ee64f432d99383b162e3b0858b0bbdde2c2ae698af7b56e2bc1531096654ac24b811188a56e1407bdb7f018721ee056c87a81596df8054c0001d9c21d6a9d421e90f221c443b152aa8384dfa6a304cc46a00cd21960001865733d87ee8638952f07d0ed0c522c7ea0ff4b1f8cfeac760f6ab24039f2c700e5b1f8851447fc13ef1f704f82d510ec2875c3af8872000821d4d452c72351322f4cf9931332fc8760cb02e9b3298ba48ca42eac3282ba30ca00877327b734c584865b15ff7bbc57f5ab715e0088c4529fbd0de2000159aaa6354aea0e137ec5cf351608a4988198a723025fd638072d260e0b5c987825525fe09323ee09f4724e2755cfc89968d4019a5d9a83190cac000ca9619353f7431c432c89d758fe1fe8a97834f2a560d2e3f58a47782a281d6a8876143ae1d7e45e99f3262665f90ec19602a62657ca9199505d36653175999495dde651975799455eda650d7461940b9a62c2432d8affbdde2bfad5b8af004462294fde86f10001173d59aa8384dfa21d4d45198a723025fd638072d26220998983825f261e095497f824c8fb827d1c8d899d73f2265a2e106788d4019a541d035d766a0c6432b00032a5864d4fdd0c710cb2275d63f87fa2a5e0d3ca95834b8fd6291dd9b0a10782a281c43a000410e628323ef87715aa21d850eb875f917a67cc989997e43b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d746194010ee64f6e698b09b56e2bc032d89a10446229400045cf566aa95d41c26fd58e46a24ce63500114c0878000a85835000884d300ec734b8ecd850847df0ee2b1ccd43a8980676ee50501483d0e9eb3444c70656000619644d345ce0de11788343c6210cb2a11c1f3285f0766a16c1b7a89b3384a464cbe152c326a7ee8638ac930f0654bc1b8952b0696ed0c5233b5b14631ffc50b3b57142af0545038874,
  0x10066cb184280cb1356e32dccefbf6f32cc658c5778cbb15dc0000cae0cac000a6552c4d261f4c3a98f4cad1ab808586568cb33f6e10a0fe3041db2c7006ccb9400d8000000a6588caa261f4c7a32c4d5b80061dae674476c81011daa03f876980fd1da203f076680fa1d9203e076380f700003b3876534e7356a002cdbe850e36f614360c708dc04400004dbc8b6136ee2d80dba8b5f36e62d78db88b5d36de2d70dc08af5b56e2bc010f88d769ce03f0000283f36fc08887689ab332cc656c21619550852fdb84263f8c106e000131ea61f32c4000cd56198a7230261098382328b826840fd79a0a262266d1c9c098b3f6e191c000130e3f704bf832cac9158e27ee931ec5e035560034fd39a093f7a1930fdb86463f6a1914fd986443f5e1908fd686413f561900fd4863f00007ee0fd81fba4c791784d54998a25fe096c9838232262208a498782277234266dc9c0986723025fc0002c735922b1c530e28380cae6aa0c9b152d063254ac18bbb3413de54c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca0000010e6987141c152e354c034076819cc1dae2dded5b8af269c42301a8008ab83161384dc084cf83d0132e0d484c000006ded42c822150763b18d5299e93b3e16160c7850c831613820f484ca0000a96d52bc4058748438cecd043d04447628dbc9aa232fc4c48638a1d70ff07eec37800008b9d1faae69152e54c66a803349fba18e31a844cc21d70ebe1960001865733d8acd0493ad510ec210f0001043f15f322f4503043b121edf700beb6fd02ac43c0d4f2a5433f64c4ccbf21d832c0bdb4ca1865b3271734c584dab715e0088c452bc1406960000a95a83821e43b18439952e4dfa6a7cd411d9b0b1e76642c6c485125010f0001043b353aa98c37845cf13aeb1fc3fd47eb148aed081f2262a33ae001000010e33538658c577800715daacd4334800334d06554d068cb733bf626c58c46a11330b5443b0a622073e98781ada67c067298f0194261c062e7ee8d4d152a326d22f45032c700e5a54b418cbc14344010fc57cbb3a144eecd8505bb9413faed504fb47dc13e0ecd04f786580006195cd4daa5433f68760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca0065b3271734c584dab715e0088c45280004dfaa0e08790ec610e654b88781a9e0c087668cd543b312ca76742b49d990acc765c2b29d950ac876442b11d8f0ac2dc280f790ea33ef0e9048836fc121e00008712a6254aa98ad41c10f208766a7448843a50ad210e80011d9c344d6adc578043f125410f44938223114adf700bb00005668a95541c0ec621c66a704eaac7f0ff517383782a6235051fac522bb4207c8e49816e10e302ec98a8cebb7dd124e76642c69d9b0ad010f0001000400011214cc4996315de001c576843b12211a8433443a50ad2000cd341955341a7ee8cff0cb733be4c38cc51d9c18e1626c58c1faf0c847ee431c9fad0c6498881cfa61e06b699f019ca63c0650987018b92ff04b64c1c1191311045254a8c9b45c21338e4684cdc5e0130ee4e04c345c01300e4604bfac720ee2b24039f2c700e5a8754394952d0632a9d0cbfbb3a144f1f785063b361416ee504fec7fc13eeed504fb47dc13e0ecd04f7843f1254a950cfdab3533d843d4cc321d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c3281734c584dab715e0088c452800021e09bf541c10f210e654b832b9a9b33ae00100001955341a32dccef800333ac658c577d89b15d4001c43a262b07c8990c1d8a622073e98781ada63c0650987018b952a001254bcd4cbb5b146120083e3ac9613851798360a85e351c6dfc26c9b7d09ae6ddc2599b6f095e3b540638ecf014709a445c35c1116f0624451b4e111440880000821f35303b1cd4ba9190ccea26032ba8580c907ee0ce23b43148b1fa83fd1fb30c8843cc9de10f126d043bc98a90ed2586b1f84eb4620132517804c5b92605aee5e4120b93904644c18d469faf3414b3403a7ac900e7c546c1a9952d063254a418b1527062a549418a15210624547c188951d0620ece8513bb36141720f04ff47fc13eeed504fb3b3413de21c8002087534247edc332930f04aa4bfc12646a11330e7e44cbad510ec322f4d4a931133684c4ccbf21d832c054c4caf952332a0ba6cca62eb33292ba48ca42e8e3288bbb0ca12eac3282ba30ca01533327c21dcc9edcd316136adc5780223114a00016389fba50709bf432c9a9a00166de42651b7b09806dd425e9b7309786dc45a7c1e8116506a0455b541016c3b20003350133983b4c8098ed11f9a3b347a20ecb1e02439000390e3344c76742ef90eb03de43a40f710e7038cdc2c4b343cb12a4dc8c4a8843c000410ecd4b285e351c3b5cce890f5330c43dc57d5cd315ec6e0457a8ed915e810fc4aa2a6307d0a9ec1da800076b46df8dbe0ed436ec6db876702211d8ca26542cbb4221dc43c087610f210e76ad8a979a9933983b4405d0ed733a2d500456b500114c0000763289950b2087cd4c000b36fe1364dbc84ca36fa1304dbd84c036ea12f4db984bc36e212ecdbb84b384d222da0f408ae8350229e0c488a1043c0004db78b4d,
  0x1277a4c1c9de130527764c0c9dd130127728758638800715db1fac523c803146520fc50ec7ff142d22f45041fa734124c44cda1d9c33324c4ccbf21d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeec32847ef4c9d13153272196cc9c589b161d7bbc5855cd315ee43dc0ada61c02ae0001b7e843b25fc54b843a9fba21e66b58001043d340410ec488130e00110e94d5d930d277e4c2c9df1309277a4c1c9de130527764c0c9dd13012772766c5d81d99175e76545d69d93175876445d59d8d1752762c5d410f235a64bfcd492a630ff0a9ec3e2aab70f24a9dc3c0ab350ebe438cd6a21d618e2767c57d843f15f31fac523c803146520fc50ec7ff142d22f4504131133684c4ccbf2e9b3298baccca4aeef328cbabcca2af6d32864c54c9cdcd316136adc5780223114a000152a952e10ea7ee941c1ad504c84c38d09391b133c196000186571301170431ca61e06b67ee06383b361420b1cc3b947df0ede76742b4aa5712570e90488043a000410f4493ab350ebe54a8c9ac8bd1410b1c0396a1d50e5254b4d67952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286196cc9c21d818e454c46305eef1615842c582043f15f3734c57bdab715e0088c452a1db0e5f1f7039636ff0306df700bb10f702b643d40acb6fc029e00010eba83854aa54b843a931021c66b50d31bb34063054a8004952d35a4ee505013b5413f720f43a6c7fd0e7898702b39d9a3354aad448eaa75122c76742b49d990acc765c2b29d950ac876442b11d8f0ac2dd740b6b71d02c043a8cfbc3a41220dbf0487843a000410f4d68aa630ff0a9ec3e2aab70f24a9dc3c0ab350ebe54841ef151f0754549c1bd952506d254741b295290692546c1a110f715f410fc57cc7eb148eed0c52348031464ed6c518c83f143aee5c50e47ff142ced5c50ac8bd1410f054503952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeec3284bab0ca0953118c1734c5849533160d842c5825ab715e0088c452a1db0e5f1f70396000021e4875d41c2a552a5c21d48711ad31144d38004f822000023b18d38021f337b6adc5780223114aa11c1f3285f0766a26c1c0285b06dea4641a6a8980676a1601950000772aed5530ea8387684ed69dcb3b56782854b4d69000721d607bc87481ee21ce071887781a321da0654872819121e205f487a99866e162599b9189516ebe24f1b8f89356fba249c00010e221e4a98953d2ab654ecacd087b043d35a228423ef876f766e697152b892b087400087631a9c087a249d59a875f917a2821e0a8a075d1c65117b69943087e2be6e698af76dfe060dbee017621ee056db7e014f000054b50eba83854aa21d48719acf1340b1c83b8c5c30ceee46c132c7de1420a95c495a83b06bcdbfc0c1bb3734b83b18d1310e233eedbf0487aa540c7717004c22c700e5b1f704fa3b35063254b0004952f359aacd43349d9d0c0aa11c16f291904aee46411493103424e49c4eb46a11330e7e44cbac7f0ff4b5443b0952b07c854841ef151f0754549c1bd952506d254741b295290692546c1a110eb03de1960001865735971fac523bb43148ced6c518bb971438ed5c50ac8bd1410f054503b70b12ca10e800121d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca01533327c196cc9c5ab715e010fc4b4843d12ce088c452aa630de000022e743b34c564c38879283810ea7eecd6709a058e41dc5c8d8265507666363ef0a108b8619ddd9b835f1d8c689952b892b3b3a15a5b7f818321c46a761d2091054a86b310ec19605d1c6512d5b8af004462295c8c82290000acd148c13110cb210ed5311fbb4c5643c941c08752a5e6b344fa47dd0e5a8760cb02e8c3280b1c44c245c10c76ecd418d80002a5ee46032c9fbb10eaa950d66072d8fb827d163889808b8218ed52a9a9d766a686c878818a21de0624876818821c6060db7f092b54ac6b28a9719352a560f91da18a46783628fde0b8a2321d607bca969ac943b06580a98995f2a46654174d994c5ee6652d75999495ede651d77799465d5e65157b699435d186501b858965000010ed5311fbb876698ac879283810ea195cd658a108fbe1dc50ec19605d1c6511639899c8b8619ddd9b835f000054bc32b9fbb10eaa958d65099c58e41dc62e186778fbc284152b892b6dfe060dd9b9a5c1d8c689887119f76df8243d52a063b8b802601638072d3b3a181542383e621d607bdda18a46782a281e3ee09f46e16259421d000243b0658174d994c5d1c65117b699435d186502d5b8af0087e25a421e896704462295d9a83190000195d5311fbb876698ac879283810ea54b4d6499fd58ec1ed5639077159201cf9638072d8fc428a23ef0a0c8ff827de3ee09f043b0658174919485d1c651175619415d1865000002c7e8b9ea0e04399ac2326c54bc1f4152b07c854b418cbb43148aecd04f78872000821d4523953132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c328021dc582e10b1608876c3fd80008fd6a0e1315aa6335820030ece85693b2e1594ec7856100010e9541c1d9e3b147640ec61d9a3b287660ec91abb00146584217995f085c656459699571658654c5953f8c1076cb9400e0cb233ba32e401d0cab,
  0x1031443bc0c490ed0310439c0c290e30306dc084a3b6fe1256a968359aa560cef17184de45c21340e47c14bb91b04b64bf8004130904844c3411a930b04684c0c1181301045ee5e04c939381317188432cc5e10c9443cc0fa10eb03de43a40f71fba343edc2c4b2aab5123ca9d448b843a000410f44b3c3b20c0d10142c1c3c50aec76706382c760f6ab1c83b8acd00e9eb24039f152d06551f8851447de141920f04ff47fc13eeed504fb0872000821d4d091fb90ddc4c4416f130f05b84c1c16b930505aca98cd5010f715f410fc57cc5cf13aee49c4eb2c7f0ff487543fb47eb35f843d4cc3131332fc8760cb02e923290ba38ca22eec3284bab0ca08877327a4c54c9cdcd316120000a9706595130a11d42c5ab64c566bf4c9b152b07c854b41953b43148aed504fb0872000821d4523953132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeac3282ba30ca00877160b842c58221db0ff600023f5a8584c5654b8d7e09d758fe1fea2e71aa043b0658000047eab9a454b9531865935f6001876b99d11db202fc76a80bc1da202e876780b91d9a02e076580b71d9202d80000ed21d8cd504d7d1af51da602940000ed41db03b307670ec61da0d384d7b80061dae674476580a11d92028000034e11db03b3076a0ec61d9c3b487681af500020884458821f114107a0265c189096a0000dbda83951300888d7900061dae2dc476a8b691da62d887688b5c1d9e2d5c7668b531d962d407648b4e1d8e2d3476c8af4b56e2bc8dc084b9831012bc0001b6f35e20034fdb8bf23f6a2fc4fd98bf03f622fbcfd78bee3f5a2fb4fd58bec3f522facfd39a093f7a64eaf77993700007ee8fdc130f35d2662897f825b261e08d89838232262208a5c8d099b72702619c8c097f0000b1cd648ac71507098f032b9ae80014656c59719531654658c577d89b15d632ec00bb2c400260000cb0195e32b86560cab195419666b9c0028cb3165c32ac019995a32cc658c5778cbb15dcfdb842632c610960000caa0cb8196832c06570cac000632dac4d261f35cc2215fbd048f65a401fc659000532b46598caa8420195600cc65c8016196a00506588012195e00446568010196e6860cb18aef19762bbac4d8aea000e2225fb7084c658c212dfb60830658820bc000261d000698a930f9ae4099a6df8d70c1e8115c000076328994cf96ad810f9ae300104c2c13f92ff04984c44123930f048a4c34122130904844c1c120930504804c0c11f9301047ce5ec4d639f9132ee5e04c906580006195c4c746210cb24c4c603931516017bbc57e065b1334aad449144050b060001668b75c4cf87674fdd843d58fcb2596692c925aa0a260d71000b36f62da0db78b621da40018dbe84cc36f21328dbb84c936ea1320db984c736e2131876a80bc1da202e876780b91d9a02e076580b71d9202d876b99d137022bd476c8af483d022b9aa008ad00006df810f8ec6b56ca264d70998a260e0b5c97f824c262208a49878227724e2759cfc89977230261032c00030cae2601638072d8b8218ee3ee1a0543b0658032d899a54aa2451b7e815700010e9141c10f33f7610f563f2d502a5c9870d7000092a62657ca9199502a6664f8a968b1a2a562c62c4d0b08000054b8a90151e2a4c5490a8e15282a356adcd6d041f32a40029fb699db32ba10d8cb0842f32be10b8cad842c32b210accab842a32aa10a465c801f19660070658801b195a0065fe6083e7f1820dd97208360004000065b99df000a6600cb18aefb1362ba8003884a4c560f9132183b14cfe0df931f836d4dfa0d2d33e03394c780ca0a9500092a5a6b5ddca0a0276a827ee41e874d8ffa1cf0ec98b928766259555a891d54ea245953187f82a420f78a8f83aa2a4e0deca9283692a3a0d94a9483492a360d09b8501ef6eba05b5b8e816021d467dcec5995243ac31c63f58a4776862919dad8a31772e2871dab8a15782a281cecc85663b2e1594eca85643b221588ec785613b1a15808799ad650706b5497f9a92262665f8a98995f2a46654174d994c5d66652577799465d5e65157b699435dd8650975619412a6664fa1d209106df8243c0005cd221c4a954a9708753f7410ecd6c05cf4c466834caa19d78754252152d07b30008000000199d68fc428b131586044c3c166dd9d83a13b34003065b99df32c62bbec4d8aea507e235c003884a3b3a167410f00014dfa69d531e1a714c3869961d3092c044222dd52b076f69ce03ddae000c01d8c699a3ef0a10508e0f9942f83b351360e0142d836f50760d7948c834d766e69841118af376862919dad8a31772e2871dab8a15782a281d74d994c5d66652574919485dde651975799455d1c65117b69943b56e2c68ecf8afbb9a62bd821f896954c6259144c033b50b00ca9d9a031a0000ee55daac3b23b247628ecc1d963b287640ec71d8c0876875d41c88752a5a6b5c19d952c326aa26432c152b0672ee5050146211322b3443a8483d0e9aaad448eb75d02e299f4d34000200000014cc0262b05b8990c157a67f050498fc139a6fd3374e49c4eb393f1382e5ec4d6393b134a1960001865728007ee00069fb717e47ed45f89fb317e07ec45f79faf17dc7eb45f69fab17d87ea45f5ac7f0ff4b25c3e3acd30f28b24c3c1ad510ec24c38004130d277e4c2c9df1309,
  0x13620001c87381c621ca0645b9189516e3e24d553d83b554ee0dc5dad8a3076ae285240107c78ffc1e0c878936921de4c5964b09c159242695c9f02ab727409bc9840008261a08d49858234260e08c89828231260608c0980822f7270262e2f0864821da6c0cfdc0c704c38159c97f9a91262266d21d2091459201cf90e5873443921c88fdd86ef54ac0d7d55a033d2a3e0c462e71b0b2a5c6bfdb7e99f78fc428a1d9d0a27766c282ddca09fd8ff827dddaa09f68fb827c1d9a09ef43a21fc90e787f1439a1fc10e387ed438a1fb10e187eb10e400108719a2610ea291e3f507fa21d607bc87481ee1d8e6c2163f1b04262665f90ec19605d36653175999495d24652175799455d1c651177619425d586505746194010ee64f498a993921ea2ee48798bb021ee2beae698af6b56e2bc021f89696e16259811188ac00001965423aa554c54766d53121d42a58767142c130e087a6c303e3c8031460b2584e145e60d86ed681daaa7a12a2dc880e310e6000e43c40df10ef037a43940dc370212990eac2e7a623361443b4d81c5c20cf0a9681d1aa5606beaad019ec7e21450ece8513bb361416ee504fea61c0ace21c80020875148f0e9048a47ea0ff5170031e151f0622b1f8d8236fd33ee7ee8cda21d832c0ba6cca62eb33292ba48ca42e8e3288bbb0ca1131018e0874462921cf18a2873462821cb189e872462721c7189a871462621c3189643dc5e190f5177243cc5d85cd316136adc5840877160b842c581d89b15d4001c4449fb90ddc7ebc3739533063eecd018e00008b9ca11cece2a554c548750a961d9b21d043a8871043d2a5e1964d85800519666b9ccb0842632be1094cae842432b21088cab84211956015c65c8016196a00506588012195e004465680106594219dfb60830658820bc0010000000a6c24caa9a0d196e686065d8aeeb1362ba800388890001170e2e09fb83f5c54bc43986594c3a766d315262336141d8645e8a065aa02661e0a034f8d40662559a09288908163d53a032c4df86851daa09f60878000821d9a96196e68610ec19605eda650d756194121e62ec021f8af9b9a62be065d8aeeb1362ba800388893b3e15ae1d20568000065522e1c5c13f707eb8a9788730cb29874ecda62a000a6c24000821f11e60884454b4ef0246d40005500001d8ea1614238222361031c0fdc86ee26220b7887a99868b9e275dc9389d60000b1f832ca84743a96ad8a961d9c3608675c0020000000669a0caa9a0d4c3c166d33e0581196e6861311195e32c62bbec4d8aea874c24c22020922000e2225b8181bc6dfe0621bae816e00009874ecd843d54aeaad4a96151e8fc6eced31521d443a087390e621ca439087190e221c221da6c0c001043f12d210f44b3843b122f0ec830343c50aec00015312a75508ea160ece9b02083e65480053f6d33b6657421b1961085e657c217195b085865642159957085465542148cb9003e32cc00e0cb1003632b400c8cb733beff3041f3f8c106ecb9041b267c048a98f011b39781324e4e04c5acd00e9eb24039f483c14051ff04fdc6210cb317843253b95067aed541962ab5123ca9d448b843a000400080000005330010f44b3c3b20c0d10142c1c3c50aec990c157a67f050498fc1399fba35d24c38d0926fd337476706381fb90ddc4c4416f130505ac4c0c154130b04fe4c24137930104d64c34129c5cf13aee49c4eb393f1382e5ec4d6393b134ae7e44cbac7f0ff4b25c3e3acd30f28b24c3c1ad510ec2a98c1f4152d07cc875462a043f15f31fac523bb43148d200c519483f143b1ffc50b48bd141054b8d8010f5330c8760cb02e9b3298baccca4aeef328cbabcca2af6d3286bbb0ca12eac3283842c585deef1615734c584996315df626c57500071112000131506595130a11d42c5ab610ea6c0448baa740c9410e800145e0131610f44b3c3b20c0d0f142bb3939046c7ee8d74930e342476706381fb90ddc98f4194931105bc54a8c9ac5cf13aee49c4eb2c7f0ff4b24039f21d50e7454b41f32a6335f71fac523bb43148d1ff04fd8874000810fc57c887313eced54d7fa62b35fa43d4cc321d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac328221dcc9edcd31612000032ca898508ea162d5b152e360067ddb7e090f54a818ec879818b21c6060e2e009846dfc24ad638072d54ac19dc87581ef8fb827d22e109a06e1625956390771766a0c5dc8c82270874000930e99da8fbc284021e896787641818caa8429766e0d6dc8d82633f746ba530f9aac261c6848ece0c707f1820dcfdc86ee26220b780010000000a66022e789d7724e275963f87fa43aa1fd932183b14cfe0df931f836d4dfa0d2d5319afb8fd6291ddad8a31772e2871dab8a15782a281c43a000410e66bf865b99df4c780ca0a951936087e2be487a998643b06580a98995f5d36653175999495dde651975799455d1c65117b699435d186502e698b0910ee2c170858b0332c62bbec4d8aea000e2224a9983302a5a0ca8a918324000098a8a970659508ea162d5b3b5535fe675c002000032aa683400199d64c440e7d30f035b4c780ca130e03177674289dd9b0a0b76a827d9d9a09ef5d24652174719445d586505746194032c62bbec4d8aea000e22240000cb62a5698a84399afe000e43940dc10f1,
  0x13273734c57b90f702d0dc700b080003f744c40987130c26144c20982130225fc43b4d9c091b878a15d9b8e816450b26ccc8791ad152321644871817621ee2beae698af6087e24aa24289286fba249d53183e854f60ed555b838254ee0dc559a834f0000a9d4a979d9d7684ed69dcb3b56782898f021e9b3735a243dc57d5cd315ec10fc4952a6307d0a9ec1daaab70704a9dc1b8ab35069e000087910e2087aed09dad3b9676acf050a979b3532e0b1c83b8ac900e7cb1c0396c7de14191ff04fbc7dc13e04c4ccbf21d832c0ba38ca22eac3282ba30ca0000010e6a0e832ba61e3668002098393bc26020a609888265261e098c9868262261609849848260260a0978981825d25fe096cfdd9aca723c26ddc8d099b0cac000c32c9b3258ec1ed563907718fc428b23ef0a1076760e8dd9b835f54b6253152b89306e0606fdb7f818b4c46219d30f884b6596015d96380331954001465c8e02196e371865a8d8b196635446588d18195e33806568ca9875617461d3859d1d8c67307688b61507e236141d88bc831e14320c584e036fe1308001000036f06ca800299808350229da8008a64c5607d132181cd4cfe069931f8199043c00041109b2c21e46b4537e9a7950b616ac87481ee21c605d9b8589666e462545baf893c878e24d9b8f89356fba249d53183e854f60ed555b838254ee0dc559a834f76862919dad8a31772e2871dab8a15782a281c43a000410e66cc076b99d1262665f90ec19605d36653175999495d24652177799465d5e651574719445eda650c43b993d262a64e432d993821ee2beae698af8b56e2bc065d8aeeb1362ba811188ba000e20f0ecf8578878815dc00028593b3a98f0a97843d52306cccd74930e34244c44cda1fbb0cee7ee433ac5c21340e46cd98800058e6a95930f283a10ea1964d991a122622099498782630000196530f283a10eae46cd98884b4c3c062c001000021e467a0002883921de0555963803365c8006065500051972380865b8dc6196a362c6598d51196234606578ce0195a32a5b7f09306df824521d3859d21e205c0876816e21d205b0873816b21ca05aa1d29abb1d8c67307688b616eb8248941d88bc507222822028583831e14320c584e036fe130a0c484b451326cb4dbc1b2a8350229da8008a63b2a169552d03a354ac0d7d55a033d54a80c6c10f000104426cb1d9d0a27766c282ddca09fd766827be1e385aa3b161618ecd85743b3215ccec985703b2215bcec6856d50b66cbc76b99d15d24652174719445dd865097461940b56e2bc065d8aeeb1362ba811188ba000e20f224285903b3e15e21e205770000a46142c9d9d4c7854bc21e8873366026922f10687727409d4fdd19b42620662897f825b261e08d898382327234266dc9c0986723025fc32b00030cb26cb9649878358e41dc5648073e58e01cb63ff8a148fbc28323fe09f78fb827c1dab037143b0658175799455d1c651175619415d18650032d9938b9a62be153b09363b3e16b21e305ab000021ccecea63c2a5e10f542d9b2f36567eec3439fb90d0a7ec433f9fa90cf64c24137930104d7178c4d3393b134a00016492a7750b6b2456389d9d4c79734832c9b2e09946de0d9541e8115d06a04538000043ea16544ca63c365a22ae0d49b2a6a026730dbc84eb1da2036c76380c01dae67460d588c66a062315ae088b70000088548c285a4c78a164d96000d3f6e45c8fd7916e3f6a19c8fd986713f5a19b8fd5866d21c4693487993b821da4afe2e109a058e41dc5c8d825b25fc00223ef0a0c261a08d49858234260e08c89828231260608c0439000410ea6849c9c098b261e6ba62f09aa93f4e682498899b4262665f90ec19605d1c651043b993d3f7a64e898a993900007ee8fd81fa826104c0032cac9158e2767531e5cd23f706cac0059b6f35e26e042621b7f09846df42609b7b09806ddc25f1b75097a6dcc25e1b7109760000dbc263c83526ca8d7d0ed316cf6adc5793540116507a42651b81098906a025f800004423b1944c9b7936521a1cfdd0c718bc626996498783262665f90ec196043ae1e04000152e0cb3734953bc7fe364e22ae0d484c236fc6735a8099cc36de6bc476b99d100006df076a02211d8ca16541ca63c51336ad87681b260cd27ee8638c6a11330b5443b0a1d70ebf22f4503131332fc8760cb02f6d3286acd049444840b22f0501a68000523254b4ece8873087b7348a970659364a05b88761b1021e62ec2e698b09b56e2c22c4d8aea6eb82489b8e091b000e20f22028581878a15d00002ab554ea98f133e10e2087a766cd8d800c3b2e1664ecc85803b2a2e60ec78b953b1a2e521d3093088082489b7f81886eba05b88761b106e386c64ec599523b3e2bec0001d9c6e3ea95d55aaa75b9a47648ec810f221c410f4ecd1b1a0afc76500064404124476642b99d970ae4763c2b71d8d0adadd740b510e43624762cca943c4123643b40b080003b347671b8faab554ea7678ec91d9021e410f5b8e1b190b20a46412bb9f9132d1210494c6a00cd20001bee1d9d2622195cfddad50087aacd4d8b000721ea661887b819c21e2065c877819621d60650874819321ce064887181900000439087610f26e3e6c4800390f5330c43dc0b410f102c643bc0b110eb02c043a40af90e702bc43940ae800021d843c8871371d,
  0x14c3812dcfdb1b3936fc691a0c408a458ec1ed4fdc863a50706a723f10a2c566a0d3d52a031b76766cedda18a46783628fde0b8a23782a281dd9a09f48b822605638872e262266d10ec19605d3665317b9994b5d2465217b799475eda650d746194036de2d72d5b8af121e6059087581606e380570878815621de055487681546df8053c76c80b46a0002bda7080a400011f71c8c952f21c63b18dbe0ed104427ed0fd91fb0261c4c30985130826084c0897f06574c7821d4fdd1faa3f586d1c0bb10e235a243dc57d5cd315ec10fc49537dd124ea9ec1daaab70704a9dc1b8ab35069e00008792a6276b4ee59e0a3b562a5e10f4da31b3b767428b1d9a09f48fc61ed63ee872d21e24d94877931221d649bdda18a46783628fde0b8a2358ee26dd638897f723e0a60980000821e66d108769b3872326628989997e43b0658174d994c5ee6652d74919485ede651d7461940262a64e6e698b1c00004c18982130226144c20986130e26204bf832b952f3f7421d4da28008260e4ef098093b9262665f898a9939000043cee691fba26084c08985130825fc4c30988130e3688000821e9b373b38666421d89166e3a05908791b4155680cf553a032c77282809daa09fb907a1d3e3fe873e76862919dad8a31772e2871e0a8a0759a22635648898672f208f9c9c822f260000209839b42262665f90ec19605d36653175999495dde65197b699435dd865097561941262a64e421f893854ee0dc40002a5726084c08985130810ea195c98612fe261c4c40a97bb564c786d0c001043d366e7670ccc843b122cdc740b210f23682aad019eaa740658ed0c5233b5b1462ee5c50e3c15140eee505013b5413f720f43a7c7fd0e7c8760cb02e9b3298baccca4aeef328cbdb4ca1aeec3284bab0ca0acd1131ab2444c3043f1270a9dc1b8b9790482e4e41190000260ea95c43a865726184bf898713102a5eed5931e1b42124eacd41a7b7dc02ec4388d9abb43148ced6c518bb971438f054503843c000410ecda02e9b3298baccca4aeef328cbdb4ca1843f1270a9dc1b8800021e4aad553aaa5710ea4c3032b930e26204bf9dab152f36826c40871818321da05b9b7f092b6eb82475b8e0916000010ed53aaab554ae4c3043a930e2620195c97f152f21e46d00d6890f30316438c0bb36fe1260df74493843c000410ec49643a70b3a7670638152d06baecd81b021d50edaa95833baa6307d0a9ec1daaab70704a9dc1b8ab35069e54b8d9f1fba367843dc57d043f15f2ed0c5233b5b1462ee5c50e3b57142af054503c7de0ee47ee433a9fb70ce67ed43391fb30ce27ec43381fad0cdc7eac336931104ca4c3c131930d04c44c2c130930904c04c1412f130304ba4bfc12d8874000821ccd9a10f5330c8760cb02e9b3298baccca4aeef328cbabcca2af6d328621dcc9edcd316136adc57845c21338e4684cd82231182000130f283a4c78195d6399b3f0002087cd9682213658a16c1b7a8980676a160195152c326a54ac1943b941404ed504fdc83d0e9f1ff439f2cd1131ab2444c339790482e4e41191306367aed5c50a822311744c34131130b04c24c24130130504bc4c0c12e92ff04b6a464cc2a1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeec3284bab0ca0b91a13360000988130e58e621d531e06572a5c6cf8000821f365a0884d96285b06dea26019da858065454b0004952b34c6ee505013b5413f6ecd04fa483d0e9f1ff439f47dd0e5a54841ef151f0754549c1bd952506d254741b295290692546c1a13b43148ced6c518bb971438ed5c50abc15140eb3444c6ac91130cb1c44bf82231174e5e411f3939045e4c0000439193314a464cc2931332fc8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2af6d3286bbb0ca12eac3282ba30ca01533327c4c54c9c80002a5c4c40987130c26144c20982130225fc21d531e0657260c6cf4000821f365a0884d96285b06dea4641a6a8980676a160195152c001254bcd9d952b34c6ee505013b5413f6ecd04fa483d0e9f1ff439f47dd0e5a547c1d515210734549c1bd952506d254741b295290692546c1a110f3277243c49b290ef262443ac937822315e6ed0c5233c1b147eed6c518bb3a1458f05c511bb971438ed5c50abc15140eb3444c6ac91130cb1c44bfc7e30f6ae5e411f3939045ee464110130000104c1cd9d2c77367243b4d9c131133688760cb0153132be4c4ccad952332a0ba6cca62f733296baccca4ae923290bdbcca3aeef328cbabcca2af6d3286bbb0ca12eac3282ba30ca01533327c4c54c9cdcd316136adc584589b15d4001c41e00003f707ed8fda1fb23f607eb0fd5130e26184c28984130426044bf843aa63c0cae7ee8d9e09476e0606dc21d0002087a69508711a1b087e251952d03a3566e0e4c0003b358fb843c087710ea21e4ecec8761fba7684f069e0b152f36760034fd78bd43f5a2f4cfd58bd23f522f44fd38bd03f7a2c06f778afd262a08b5c8c022300007ee8fdc1fb63f687ec8fd8130736742f50fd7000d260c0020fd486a826020a60fd39a092626656cfde993a262a64e6f7799378b8c26e1c8f09b700007ee8fdc1fb63f687ec8fd81fac3f544c40987130c26144c20982130225fc195d63b9b3900104c1c961930125804c4ccbf1315,
  0x176ae2855e0a8a0710e800104399b4b21e66d108769b383f4e68250ec19605d36653175999495d24652177799465d5e651574719445eda650d0e98c53b9a62c7043b8b05c2162c0cfd786e73f7a18f4fda86363f6618d4fd886343f5218c155a033d2a660cc1daa032d00007ee953a92fe3f584c40986130a26104c1098106573f5517062e73b952a5e4c38dac05833b38003144c99e336fc31bcecd85812a560ce533e883e7f9a10d8cae000a32a6107dfb699db4c3a6768cb0842f32be10b8cad842c32b210accab842a32aa10a465c801f19660070658801b195a006465b99df1dae6744ec5995232c62bbdfc6083765c820d8eca857e0000987ac4d283b50727ed8ecc1d963b247640ec71d8c880a43c8ecf263d43a4ee54987000336ae22920c484b769c26d50dbf0c6f1d9e049c76681261daa031ca959a6369de23d9ae088b73b36159dd9a031c0440000410f9a981d8e699552a09115232164544c058350b015da1d2056a3b386d4530e99dd32b6111dda183e776b60ed1dcb838176ae0dc1e0a834e77280cf8658807e196600dc6568034197200c4655802a1dae67450e98c53c2162c2ef778b0ab9a62bd876c8af419762bbac4d8aea54c6258d53d894e556e24e553b8932087e24a959a89255568247c11188f965a62219fb7884f658e2138003884a674a211ceca857e3b3e15e0ecc85733b2e15c8ec985703b2215bcec7856e3b1a15b5b8581eb6e460711baf819d6e3e0641bae01696df8053c000262a4c3c9bf2d5b284650727eda24210e3880b0f1421d90f2196c54bc987000536ac6d51a7008a4831212dc76781271d9a049876a80c736fc31bda7788f66b8222dc11000014c3a6d4cecd9b524c566d4010f9a231d8e66361d505d25232164542c0576874815a8ece1b51197200c4655802a674a211c0021b4e196e677c76b99d11db22bd2c4d8aea044623e4003884a3b2a15f8ecc85733b2e15c8ec985703b2215bcec7856e3b1a15b4a95835c00009bf2d5b2846507ea0ed41c9fb68908438e202c3c5766c10ec8791d9e4c7a8748987261f36aa6bd476980a51da202900000ed41db03b307670ec669c26d50cee8cad1644656c211bf6d084032cc03f8cb100fc32dcd0c195433ae658c5778cbb15dccb4c44300004c5432e065500054c3f626930e9b53341a6550ceb996315df626c5750007111298882e7a61c0ace000131543ab874a001530f8cb63b366d480028cb51b1632cc6a88cb11a3032bc6700cad19526dfc7591d9a00183b18d130ed733a243d4cc31d8b1709734c57b0cbb15dc10fc498aa571256dbfc0c18000197032aac4d5ab63b287660ecb1d923b207638ec610e3087632d8ecf1d9c36a214f0dbf0c6f832e23dcecd86040440000410f9a981dae6744763998d044622ea1d986055232164544c058350b015d8000262b2a556269423283b3f6d1212202c3c521e487489871d9d36a015a8ece000c874a2444ecd858f54aa0c71d9a9a2c3b3e2beee698af6087e24aa24289266fb805d9b7e014f0000a0e4eca1d983b2c7648ec81d8e3b18438c21d9d8a566854bd37e9b4f3558658c577d89b15d400080000000000c001131ea61f369c00000019ae4000e2224000262a4c3a987c0021b4d00000014da4000335c8001c444a62b0dd89878339a61c0c6e00022e3c5c38b831738fdb9b4c3386e4604bfac720ee2b24039f2c700e5b1f7850647fc13ef1f704f821d832c0ba38ca22eac3282ba30ca0000010e6195c988130e369600000029b4800066b9131586ec4c3c19cd30e06373f6c6840fdc863950726d262e0098083d022c9638072d69ce03f1aa080ba8fb86d1c76819cc6a0022ae0d49b2a36f26ca4dbe84d71d8e03022e309b884d222e1ae088b758ec1ed41100001043e6cb63f10a2c5232164544c058350b015d9d9d83a33b38003152d8947890a2498eca857e3b3615d0ecc85733b2e15c8ec985703b2215bcec7856e3b1a15b5b8181b76fb805d88711b108808247a1e209176e38245955a033d54e80cb1dca0a0276a827ee41e874f8ffa1cf8fda86723f6619c4fd886700874000821e9b463b166548fd78bd43f5a2f4cfd58bd28b9e27562e1099c59a22635648898658fe1fe9639077154c60fa159a834f724c0b5dcbc8241727208c9c8c0223260c6d148799b4421da6ce0fdd9aca04462bce3f58a4776862919dad8a31772e28723ef0a10782a281dd9b835f54ae6d0c76b99d143b0658174d994c5d66652574919485dde651974719445eda650d77619425d586506f778b0ab56e2c20ecf8afbb9a62bdac4d8aea087e24e0003883c54ee0dc400008752620ed58a97930e26184c28984130426044bf832ba63c36946834caa19d74c5614f1311050f4c3c138e0cb88f7831c23720c508c0508e1bb941f06b1507419d4fdc000d3f6e6d200020000000669a065b9a184cf8133530e04b736fc6918db78b5cb56e2bc4cb18aefb1362baa0c408a4000e20f0fd786e73f521aa0fde86793f6a19c8fd986713f6219c0fd6866e3f5619b4fd3866b69c6034076c80b46a0002bda7080a40000a0e4dbe0ed183d24c38986130a26104c1098112fe0cae98f043a9fba8b87171e2e734e604426d24d0c0cb6341a6550ceb996315df626c5750007111298ac37626220d5e98783398000000a98762e3c5ce8b867edcda40638,
  0x1b9a62be065d8aeeb1362ba821d892c000e21461d3859b3b3e15ae1d20568000098f4987a62a3b36987552b952f0cb221cc65b261e36f06bfd3159afcb56e2bc011188ac00011fac32ca84776aaa160a971b77000e43940dc10f1031443bc0c490ed0310439c0c290e30306dc084a3b6fe1256a968359aa560cef17184de45c21340e47c14bb91b04b64bf8dba930d046a4c2c11a130304604c0411790f303e843ac0f790e903dce4e04c5b70b12cb1784325043a00047ee8638843d12ce875c39e131105bc4c3c16e130705ae4c1416b2a753604a98cd5045cf13aee49c4eb06580006195cdba2c7f0ff51fac522bb4207c898a8d7f152a326cb1d83daac720ee2b24039f2c700e5a54b419547e214511f7850647fc13eeed504fb47dc13e054bcdb9131332fc8760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bab0ca0ae8c3280196cc9c10f5177443dc57d043f15f3734c57c1d9f0c0f0ec83030000508e00184398cb8196ca160ece9b7603064388cfbb6fe1256dbf0487aa560ceea95031dc5c2134117004c2391b04c04c20004391933144c4ccbf131532720000986130a26044c0087910ea3f7610ec988130e260c4c1032cac7358e24bf8dba99d559201cf95311b0254e865fd0ec19600000195ca9747fd1970b1cc0032c7158ee32d963f2858508e7674dba00030cae6d2c32c9a0c26222fec9878bf20cb62bfef778afe3f7a1bc62e706ec000098aca9588733f6e6dccd9c130926044c0c96090ec362043cc0bf90e33458df74493ab35069ef05450348bc0ec2b540db8130b351e9bf0d0b262b0dd84c34db8a61c36dc7ed8d0845c01308e464cc512ff36de4c3cd749fbb0de07ee43771faf0dce7eb4373131105bc4c1c16b930505ad173c4ebb92713ac1960001865733aab1fc3fd47eb148adc7048dbb4207d010f00012a62360410ec48bac760f6ab1c83b8ac900e7cb1c0396aa7406591f8851447de14191ff04fbbb5413ed1f704f83b3413de4c4ccbf21d832c0ba6cca62e923290ba38ca22f6d3286bab0ca0ae8c3280196cc9c043f15f3734c57c1d9f0c0f0ec830343c50aec0000a978cb8000ca1614238873196c7674db91b4c8b8c26f22e109a0723e0a79c8d826200007ede2e0c5ce0cb2b1dd639930d36e2685937e8665261a094e350899873f2265c000262a4c3a7edc97f130e26204c189820659196cb540db8000d3f6e45c8fda91713f6645c0fd8916f3f5645b0fd4916b21c46a48989997e3f4e2f18fde8b01bdde2bf498a822d7230087c0001fba3f707eb8fd606593b3ab1c6e6912ff36de6840fdb863700009870fdd1fb83f5d1704db7195d3b36159cecc856687482451b7e99f721d607bdb85896608780008ec59952087e25a55319b6b087668b48719a2621e666640001d9c1d8c54bc65c0873508f6ad8a960006196ca16152aa61c36d8000c32c9b040cae675563f87fa58ec1ed5639077159201cf9638072d8fd629163f10a288fbc28323fe09f78fb827c10ec19605d36653174919485d1c651175619415d18650032d993843aa31530858b032a660fadda103e80000a98ca978873508f6ad8a961d9c1970001942c0cb636d6001043a8a1c10e627d977799465d58650443b8b05c2162c0ca998385772c0e01daa832a0000a26d42c152d36cc002cdba8b6536e62d90db88b6336ee6d90dbc9b291da46be8dc08af56a8022c8dbd84cb36de13140001b7c51336ad81109b7e1d8d07a0db29afa1da62d99aa008b283d213240001b77b56c088544c8ec636c86bd476a80a61da6029476880a400003b607670ec61d98d384db19b541daa2dc076c8af4b56e2bc9a7008a43702136a13404d7831212d80000ece1d980884763283936fa6d880028cb51b1632c468c0caf19c03b5cce88cbb15dc0000dbf0caa196432b065c0cb6b1343b1cdb000cb1d8c6b85a7108bb0000087d41ddab651326df8daf8001044223dc10f88a0832c14f20c484b700006dfd30e262b5072a1181111b5e000a32d46c58cb11a3032bc6700ec636b83b44d59822315e63b5cce8dab7161032ec577000036fca0fd42ca83b5133626865c0cb6195832c86551b5d00166df42609b77097c6dd425e9b7309786dc425dc1a811566de4d949b7b354ad404ce6022000026dbcd78821f35303b5cce89b8115eb6adc57800001da06df941da859513208887631b5c348c3b40ce69b7f0a786df426b8ed5018f065c47bc2691170d70445b822000026dbcd78821f34463b5cce88ec7331b6adc57802231174000141fa83b50b2a11944ca8394c56a460dad800410ea291843989ef5d366531746194010ee2c170858b032a660fadda103e8766a0c6c000152f54a8a98cdac9b513b3a6d40a9583e4197200c4655802a4c546d599d28847000800000019b57b1362ba8003884a4c3e6d5537e9b4fb56e2bc011188f9508e1bb941f06b1507419d541c06393f700034fdb9b4c8b8c26e163b07b58fc428b1d9d83a354b6251e24289263b2a15f8ecc85733b2e15c8ec985703b2215bcec7856e3b1a15b5b8181b76fb805d88711b108b842672202091e8788245db8e091658e41dc421d0002087a6d1865b99df8fbc284153183e8766e0d7d59a834f4c786d2952b9b413b166548ecf8afb087e2be5da18a4676b628c5dcb8a1c,
  0x13f7466d0988198a25fe096c9878245260e08c942c19d5723c26ddc8d099b72f02635c9c0986723025fc32b00030cb26e2832d89d9000e210c0001d9d43a56268a952ab521e4b34465c2c7358e2b24563b8cb64cf8a98ca97843d58fc98acdc5998a7230261097f9b6f8b826840fdc86ee508c18161d909686e1607ac8711b89262266d0fdd86f03f6e1bb0fd786e73f5a1b9898782dc260e0b5ee698b09b56e2c222e789d7724e2758000065958fc874ac4d152a556a99f131590f2087aa98ceceac713714001c875816d21d205b1bae0922880a160d44c88ae043c000411088f7832c14f20f484cd36fc31bcecd860421e207c887781f121da07c087381ed21ca07b1b8509688766181542386ee3f7068422e00984723266281118af325fe6a4476b99d1262266d087b8bc421ea2eeae698b09b56e2c20fdd86f03f6e1bb0fd786e7000043889832c710cb31739531a1d2b13454a8987267c4c56767421eaab521e46e24da2131133684c349df930b277c4bfc9dc1fbb0d0e4c1416b130305504c3c139930904dee49c4eb393f1383178c4d3393b134a19600018657370eb1fc3fd2c970f8eb24c3c1c7eb148b200c51847ff1428a2602c1bb4207d0ed681dabb5606e2a9884b32a7a12a2a9d849ac404124410f0001043b123ab1d83daac720ee2b3403a7ac900e7cb1c0396aab4067b1f8851447de141920f04ff3b9413fb1ff04fbc7dc13e07670ccc931332fc8760cb02e9b3298baccca4ae923290babcca2ae8e3288bbb0ca12eac3282ba30ca0065b327010fc57cb70a03e8dc880e6b71e0332df740bf375d02e20000879a6fc4c8621cc65c0006196c99f0a97a62b4c7f7348dc4059152306d6e2428928508e0b7959a9b16724e27562e706f0507c0a8541d0265507008a56a89b7c3f7466d0988198a25fe096c9878245260e08c942c19d5723c26ddc8d099b72f02635c9c0986723025fc000065759a232e1639800658e2b24563b8cb64cf8a98ca97ac7e6fb810f544ca62b3b3a6e1c0b890f2352cdd7048e8000556a54bc439a67c08766e18cae9d990ae6dbf4cfbc3c4123643ac0f7b71d3620762cca9370b12cc00015311d9c3b3443c8876043d54eaa95421f10e237080028cb0842632be1094cae842432b21088cab842132a62c84cb18aefb1362badfb60834197600ed9630034658a0040000195a000a655130e8cad370667746598025195a00419920842658820d1fe684367eda1090cae000a32be1148cad845032b2113ccab844e7f1c6e04cb0844132a610e8655802a19626adccb18aef19762bbac4d8aea000e212a0268848674a211c0001954000a987d33ea61d4c7a32e065b26fc37040028cad842c32be1094cac842232ae1085fc6083b7ed820d19728019658a00406561b8019660100657803e65cc215d31f1b7e32c62bbccae845132aa1134000196032a432a8002a61f4c3a98f6c4d0cb8196cfe38dc08b3319680014cad1ab819626adccb18aef19762bb80000cb2195c65706551954000a987d30ea63db13432e065b0cac370028523ff078343b065817579945592426922f1068776ac0dc4000393b2a5e7eec32b887354ee6dfc00d0cae000a32cc59732e41076fe34216195a357065742288cb5008232b401e8cb1356e658c5778cbb15dd626c575000710b0fe3c42b32e710aa00006551954000a987d30ea63d197032d931f1b7e044e9874d1b394713b8e4fc4e0393b1348e4604bfac9f1016b25c3e3ac930f06b1c83b8ac900e7cb1c0396c80b1499200c51847ff14291f7850647fc13ef1f704f845ee0dff1798361c5e20d0eed881fcbb5a076aed581b8930e36968760cb02ebb329abaccca4aeaf328aba38ca22eac3282ba30ca02a8212daa9e84a8aa76126adca80feb7220392dc780ca80004df854bc21e9fbb2620195ec4d087321da6df45033c14069e21c80020875141122f03b0ab340cd08760cb02f6d328621dcc9ec6a0132a0000a979fbb0caeb544dbe03e87686291553106ef10e4001043a8a478b9c275163f07f943b0658174d994c10ee2c170858b0443b61fec000152f3f76195e3f59b7b18e07ee43241311047117804c3b938130cb24039f21d50e7454b419547fc13eeed504fb065600061964dbc9d9d36ec43d4cc321d832c0bab0ca0865b32716adc5780223115800000030873197032d942c284736f4281a45e076178280d3d6a80997566824a2242058f73f0095537e0847674800a86551b5300086d3530f1b784c7815d21e2091b6e3a6c409871b0c21da6c0d31586043b346574ecc856687482451b7e99f721d607be1d989676e16259821e00024c386db021d9a2d54c60fa152b035f55680cf553a032c54a80c6ca971b77768629163f507fa58fc6c10ec5995243861d8d0ea873a43961cd10e88726439e1c950e6872443921c890e38721438a1c80a96832a2a3e0c448719a2621e6666421f8af98fc428a1d9d0a278fbc2831d9b0a0b772827f63fe09f776a827da3ee09f0766827bcece9b761d8e6c210ec19605d36653174919485d1c65117b699435dd8650975619415d186502e698b09b56e2bc2c4d8aea044622b00002847000c21cc65c0cb650b01964dbc8a0691781d85e0a034f5aa0265d59a09288908163dcfc02554df8685021e00020008000000199da32aa67650ec19605eda650c21f8af9,
  0x1002632ac007a61f378232dccef996315de32ec577589b15d5013442433a5108e001c41abf6d1066cb144190000196899f537e263d4c380014de1800a32ba10d8caf842e32b22ca4cab8b2832c62bbdfe608427f1820ed992802465ca006c000195432c06568ca900054cfa98f6c4d0cb1378400146588b27195e2c906568b2232a86f0065a9bbf32c21104cad842332a6107c65c80311966004c655800f809a21219d288477eda20cd962883200086d3865b99df19762bbac4d8aea000e20d4000267d4df898f530e261f37820028cae843632be10b8cac842b32ae10a9fe608427f1820ed992802265ca00646560005195e00d59630850196a6efc6589ab7196e677dfb7996632c62bbec4d8aeb0000658065c195a32a432c865500054c3e99f531e8cba32a86f00cb319551660658c577d89b15d6fdb842832c7007032ec01032e4003a0000cad00054c3e32d4ddf873e59226aa23fe09fb58e01cb5daa832a50b26a623ee09f4766a0c6410f0001507269981109a60508e0f9942f83b351360e0142d836f52320d341118af376862919dad8a31772e2871dab8a15782a281d0ec19605d36653175999495dde651975799455eda650d75619415d186502d5b8b08b1362ba800388350000987144cac732a5a195c43a952e1d8c6ef40020875142a21cc4feaeaf328abbb0ca10877160b842c581953306e8ed581b8bb95067a0000a97aab454ee6eec00000031096001c42180051080cb1c01cb324004e000130fa67c196e6ecc25b9b7e36bf062045000005076a26541ca61cb56c087cdd900c01d8c6981ae088b70000a11942f289a50b4a4601109bab0000000c434000510acfdcc2343f8e089a6550dd380004c5499093118cb6000c98f930f9ba810a0cb1c01d0cb8000afdbccb3195b084632c403f0caf00c432d40208cad007a32cc0098cab001ecb4c44332eb10e2cb9c42abf6d1066cb1441900040000000cdd1261d3730658c5778cbb15dd626c57500004c549909311a63e4c3e32d80031954374e0030ecb8eaf3b2a3ab8ec98ead3b223ab0ec78eab3b162e10ecf8afb21c46e8cec6999721ea661ae698b09000043a952a843d54ea3b1ed5b1b7f3b307670ecd1ba4362043b45cbb71c12370f142b81d920018765c2b29d950ac876442b11d8f0ac2762cca943a41228dbf4cfb90f33332767c57d800021c443a952a9d8c3b307670ecd5cd254ea10f4dd19ae6195a016065c803a196a00e06588036195e00d59650867658c212c00000034c4632dac4d19544c3e6e885033c14069a21c8002152c326c21d450448bc0ec254bcdbe21d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca00877327a0000a95065752327eed6a89ba00b027668cbac4041244dd740b680003b387660ec5043d556aa9d533e043e21d66e78cfb90e3030643ac0b010f302aedbf8495b71c122cdbf0487800054aea9d552aa61c08766e74001043d125010ec48844840b1b0e942b300003b32a95559a043e373866fc65c8b3d32a86e6065b9a18b1362ba800388890000987d311a62a32c49874dcc9b4d000a675c00019624c3e98a930e995437306be876981291d8e048c00034ef6a826e5450348bc0ec2f050d2e0ec6344c54b06382d50132ee7e01261d9d36de4388d4912fe3314e4604c21fb90ddc7eb43731fbb0c787ebc319930f05b84c1c16bc5c1371ea950dac952e3541173c4ebb92713acb1c039686580006195cdc9bb3614171f704f82c7f0ff487543fb0872000821d4dc947eb372243d4cc321d832c0ba38ca22f6d3286ba30ca00877327a196cc9c5cd316136adc579284611ee6e0429ec1960a780000988022136fea98d33e262b37281d3e41e09fe59a22635cbc8245261c6d2d0ec19605dd865080000873262099f032b9b93326a54bc1f4152d07cc54ac1f23b43148c54c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca18000508e98ad5318875372464d8a9783e82a5a0f98a95833976862915dca09fd10e4001043a8a472a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd86509746194010ee2c170858b0443b61fec00047eb4cf8a11d5319b91326c54bc1f4152d07cced0c522c7ea0ff454ac19cbb9413fab1f84eb887200091738dc78875342517004c2065800068760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284ba30ca00877327a196cc9c065712fe0001638930e508e98ac9882a634cf8e460dc81a103f761bc0fdc86ee3f6e1bb0fd786e700011705423a62b54c71738dc78001044223dc10f88ae832c14f20f484cd36fc6e3542382de507c0a8541d02655130091c988198a25fe096c9878245260e08c942c19d504462bcdc9389d5723c26ddc8d099b72f02635c9c0986723025fc32b0003b56e2c2032d89d90cb2275c00388430001173d6688cb858e6b1c5648ac77196ca98d63f0cb3b13499f13159b8e36b83b44d598ec71aa2088c5798ed733a36adc5840000507ea0ed44ca85919676268dbf1b8d00020884463021f115d06a8277c1e9099a0000dbfa67c4c7ea26542d02223718265a350066973f0095d48c1b5b5668249d42382de6fb86e1dc9389d58b9c1bc141f02a15074099544c0247507008a56a89b7c,
  0x1c2162c2ef778b0ab9a62be1531096754ec24da1d90604878c16a4ecf856b3b3a15a61d205680000766d30ea62bb56c54b141c263f087a21cca979bfc02d4439000390eb373cdd7049144050b0276742b4c3a40ad07668dfd1d990ae70f1048db71d362043d4cc31d8b32a410fc57cdcd315ee43dc0c790f1031443bc0c490ed031043a40c310e7030a438c0c180006dfea956c4d152a59a232e1639ac71196cb24563b952f4c56987541c2a75087a99f155a90f237f61fe963f1b8b8fd66b0553109666e1407bcece1b9e21d467dc21f8af96df86a0d0ec19603b1665490e98c53b9a62c270858b03b56e2bc011188a52a660c7dd9a031c0000766952a90f021c4a9d4ecc2838b13454a955aacd11970b1cd6388cb6087ab24563b952f4c5699f08791bfa000a32d45980cb3165632c45938caf164832b45910cbb15dd626c57619630896fdb82220000195432e065b195537f01e0e3ff8a1659242695c9d0273261c68490ec19605d5e6514000131010ea98fc32c9bf5000c3b5c5bb8ed516de3b4c5b40ed915e96adc5791b81099f07a026580001d943b307670ed01d903b18dbd9bed36c032cc6a88cad19523b5cce8800036fc32e0655589a196c3b1cdf588a4831212d8dbe000b50706f9da709b6336ee14dcdba853636e61450dbc84eb36e2139cdbf84ce36f6132c76781271d9a049876380b5832e23dda7788f6835e238a0d588c683d222c5aa088b00440000410f9be9507c174544c9be88754253144d85b86e0606dc8710007880e24f542f85df50b616ad55b838221ce07188728191772e286e1e589526e4625461e389366e3e24d641f079454f60ed553b837176b628c1dab8a1459a426b640107c78ffc1e0e3110692592c270964909a64cfc21762f306bf8bc41a0d42386067f9c116c87481ee32bc6604cac8b3232ae2cc4caa8b308766259db8589664c8421c531f085532b6108d53183e865d40195973004119686f0c87592b076862915fb688338fd41fe930e86383f6c6710ec5995221e64ef0878936821de4c5487692c358fc2758fd98644724c0b5e2f01aab260c6629c8c098459a01d3d648073e58e01cb552d03a354ac0d7cdc08af51db22bd01118af37674289dd9b0a0b907827fa3fe09f78fb827c0cb084410cb0000c32b9b4b36de6bc49879ae9262665f90ec19605d36653175999495d24652177799465d5e651574719445dd8650975619415d18650032d993821ea2eead5b8b0821ee2beae698af8b1362ba8003884a809a2120ecf859289081644988825725fe093000045c073f07ee0fdd263d000a21cca97a6fc087a767548ca67d37d46ad476780c41d960309a7308d76b8022d0000021f5232a0fcdf484d836fc6d7e13408b5043c00041109be736f26a8a1d2856950726f9941d059d3b36163ad5b8af0b1362baa1d309300446232000388358908164620205846dfe060c000289a21c6a17942d28464c7e32d530e1d8a4df8a96d52b843d3b3aa46544c9be816e06df00058ed4000c6dd429b1b730a286dec27b9b7f09de6dc42739b7709663b340930ecb02083b4c0738ed101b63b2406b8ecf01463b1c04f9b6f35e23b5cce89b8115ea3b6457a419711eed3bc47b41af11c4d41c470c1eb119ad50c46641ab118cd40c462c1891146d384451000036f0a0e144d285e50b4a11931fdab604426f9c0059b7d36c43b1c6c59b770a6e6dd429b1b730a286dec27b9b7f09de6de42759b7109ce3b3c0938ecd024d065c47bb4ef11ed06bc47141eb119b06ac46302200002087cdd91b6f35e23b5cce89b8115ea088c46400005132a0ed44d285e50b4a11931f8cb54c39626ad5b283937cc2611c8c9bdb8b826840fd79a0a260e6710fdc86673f6e1994987825525fe09300001fb273f01965668ac9158e27eea35029194dfa6f9400519611686657c5a1195d1682656c5a01959167e655c59f1955167a654c59e196315df626c5758cbb0064ce900188000197298f533e800537c8199948c85913f70684224289283f7619a0fd7866000007eda350c5c13b3a10f559a1be033144c4412b92ff04980001cfc2919260c4c39c8c9bdb000a32ec0190cb7006032d40178cb3005c32c40168caf005832b40158000195432e19d29bda0cce7ee0cc4c6a1132ce7e0ccf44840b220000fd713068b871705c8c86575aa0a9d537e9d9d087ca464dea9ab832ba10d86569b834c3c2139fe60842658c00dd9928025000032cd33e8005b1346550cad261d4c7a6f3cc9a952d06de54ac1a5bb57142af054503953132be548cca82e9b3298baccca4aeef328cbabcca2af6d3286000043aa6fd50b654b8de5998132c21098caf842532b22cc8cab8b31b1362badfb6083419760081972001d658a0050000195a32a8001530e8cb5379467dc875819421c6064087981576e3c24c9b7e090f0000a95530e2a7708766f1820f99520014fdb4ced995d086c6584217995f085c656c21619590856655c2151955085232e400f8cb3003832c400d8cad0032ff3041f3f8c106ecb9041b000200000014de18cb733be658c577d89b15d4001c41a80004cfa9bf131ea61c19686f10005195d086c657c21719590856655c592bfcc1084fe3041db3250046cb9400d0cae000a32c4de11955088832b401a3f6f109ecb1c42719610882656c2119953083e32e40188cb3,
  0x10000a260d7143a535767670ccc80053300766c5d8262b03e8990c0e6a63f0332dd740b890f235a29bf4d3ca67f34da764c2ff9d910bfc76542d29d8d0b4276642c69d8b0b0c43a40f710e302ed0ecc4b3b70b12cd0f2c4a9372312a3101c49ec3c7126cdc7c49ac4851250df74493aa630de0a9ec361aab70d2ca9dc343ab350cd3173c4ebc5e71385188c4d6b97b1359178c4d346a11330b1fc3fd2c970f8eb34c3ca2c930f06b5443b0acd00e9e767c57d90f715f51fac523c803146520fc50ec7ff142d22f4504483c14048760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3285734c584dab715e0088c45280071086000032cbb943f76a0e0a96267c087a21d4e07999159201cfa2f0864a8ff827ed53a891b878a15d9daa9ad250b269c50ec19605d586506d5b8af004462295da183e576b60ec9dcb837f76ae0db9e0a834c51300cec000152d7270dc7131e285e5134a16948c261d10eaa118ece9fbb087aa0e1dca9c0d3506dbf4cfb9d9b0c0843cc0fa10eb03df0ecc4b3b70b12cca98c3781fba352443c40be90e302ecdf74493843c00047664dce043b370cacd41a7aab4067aa9d01962a54063654b8c9b3c15140d22f03b0952b067254b418cbb9413faed504fb3b3413deb5404cbb9f8049821c8002087534244bf8cc5130f05b84c1c16b843f15f3173c4ebb92713acb1fc3fd47eb38128760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9edcd316136adc5780223114a00013159fb6723299f0988065943a8a0e0e0519f76df824521d29c0821c67014fdd9c033b166548ecd86043b2617fcec885fe21e607d087581ef8766259db8589660878000821d9b8655680cf552a031b2a5c64d8a9583392a5a0c65dca09fd766827bc43900043b3e2bec43a8a47087e25a55319ac12a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd865097461940b9a62c2443b8b05c2162c12d5b8af0044622950ed87fb00011fad0ea13104c567ed933e39190cb2a0e0e049abb3b321598eca85643b1a15800001d9e3b14764141c1d9a3b250e94e0400cd1d946ad5a7308dc69c423020c7850d83161384dbd000b36e6131cdb884c683d06d94dba853636fa135cdbf84b81d9e028cdbb9b6436f26a8a0cb88f784d222e20c488a369c2228a20205840440000410f9ae31d8e663548c86675130195cfdc1ae98c402649cbc82454c38089c9871c0425fe0932350899873f2265d6a88761508e181941f05d150741674ece000c874a6aee45e8a063b361810ec985ff3b1a1720ecc859a3b2e1664eca85983b221658ec7859578280d3e1d98967875425321d309305668249d52d03a354ac0d7d52a031b0878000821d9a962a5c64d9668074f43a61d25648073e2a560ce4a96831954e8687dd9d0a27766c282e41e09fe772827f63fe09f776a827d9d9a09ef36de6bc50ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d77619425d58650574619403b162e10ecf8afbb9a62bd8dc08af5b56e2bc021f896904462295b8181b76dfe060dbee017621e605c5bae01690000438c43993104c56a988fdb39193f74196533e2838380a700a0cb053c83d21334dbf0c6f3b3618108799b441dae6744983198ab9a62bdac4d8aea087e25a61d98967000e210c9868226261608949848224260a0888981822100004c390e9152a2620e46497f267c4c56a98821eaa7554aab3456489fb60cb2a0e0fdd1c040ec322f45032d5013311a80334bc14069eacd0493b7dc02ec4388cfbb6fc12290e942b49d9c18e07ee431cc5c00c78a95018d952d0632ecd04f790f5330c8760cb02f6d3286ba30ca05ab715e0088c452800021e443a821e952f10e64c4032ca1d450707eece019b8421c66898ece86061d8e027d42308f769c222881100001043e22b944c06573f706710fd9864421da4b0ee698af6b56e2bc231009928bc0262c21f89698766259c11188a572f20904989823b727208c80001307832f07a0ecd10f2087aa9d552aacd15922a988fdb065950707ee8e010241260c66289888bfb261e2fcaf778afd72f0264a3108655262a08b4000391925fc196533e2cd13f6e70043761fb637fd173c4eb80003f5c19656a82b354c56a0e1638ac7e38001cb63ee09f058e225fdc8c822926206e4d0ec19605d186500000267c507021cc32b9bff0c727ee0d0845c01308e464cc5131133687eec334930f05b84c1c16b92ff0498e49c4eb46a11330e7e44cb80003f6c7eb963f2d50566a98ad41c2c710cb26ff87569d9200186df8df58ec6344c43d4cc31d8b17096adc5845cd315ee43dc0adb6fc029e0000ec61d983b2c7650ec81d8e21c676686550cb8b13432d8ecf1d9c37fa281a45e076178280d3d6a809975668249dcfc024c6fb805d88711a9125fc6629c8c09848b8218e498382d7261e09ccfdc0c70724e2759c9d89a50cb0000c32b99fe262266d1649878358e41dc5648073e58e01cb4fdd86f03f5e1b9cfd686e68b9e6b0a3ff8a148fbc28323fe09f78fb827c163f87fa76ac0dc63f59ac143b0658175799455d1c65117b699435d58650574619400cb664e10ea8c5421ea2ee48798bb0,
  0x1874a6aed33f9a6d3b362ec0eca8bad3b262eb0ec88bab3b1a2ea5c9389d672f626b1cfc89976e162599b9189516e3e24d4003884a58fe1fe966987945aa21d862e786ef8bce1b0a31186958bc61a1953183e854f60ed555b838254ee0dc537e817f21e46cd63f58a4776862919dad8a31907e2875dcb8a1c76ae285645e8a083b321634ec5858621c605d843a000410e670710ec19605d36653175999495dde651975799455eda650c43b993d3b3e2bec87b8afab9a62bd821f892a890a24a1bee89278d4219a1e0a834e00001964a97843d3f76a0e159a1c1e063254b0e07bb95067aecd018e2ab5382a99f4d342a541224088c452b6fc02b0000000190f310ea1964a97843d3f76a0e130e9c1d12370f142bb371d02c8a164d98263d33b40008000000534286554ceca9190b22987ce0d8cb734307670ccc8cbb15dd626c5750007109498ac0fa26fd02fe43c8e0d261c3832764c2ff9d910bfca9d01962a54063643ac0f7bb5413ececd04f7c3b312cedc2c4b310f102fa438c0bb2a63382cbab0ca0ae8c3281121449437dd124e000159a06592a5e10f4fdda83810e670700150caa33ba32e459e8cb3165632c45938cad1644ce94423995b0846fdb4210195437300010da68cb73430658c5778cbb15dd626c57500071094000131526fc4c3a987ce0d87c7900628c164b09c28bcc1b0ddad03b554f42545b9101c621cc001c87781bd21ca06e1b81094c8756173d3119b0a21da6c0cfdc86394c561810ecd1a836dfa67dcfd786e78b8419e22e0063c54b40e8d52b035f55680cf553a032c54a80c6ca9683192a3e0c4487581ef21d207b887b8afa8fc428a1d9d0a27766c282ddca09fd76a827d9d9a09ef8766259db8589668b9e1bbd5319c1621ea66190ec19605d66652574919485d1c651177619425d586505746194043aa31510e88c52439e31450e68c504396313d0e48c4e438e31350e28c4c4386312f0858b0bbdde2c2ae698b09b56e2bc011188a53b32163400010f2890821cca9790f021c4a0e032c9fbb087a9874e0d19f721e62ec1b7e0914874a159c87181763b34705ee698af6087e24a9bee892700007648ec810ea54aaacd021ea8384c38706450348bc0ec28760cb02f6d3286b5404cc46a00cd2f0501a780000cb221cca979fbb566a70600ab90f233eedbf048a43a53810762c2c310e302ec767c57ddcd315ec10fc49544851250df7449380003b349870ec91d9021d4a95421ea8385668705c522c7ea0ff48760cb02e9b3298b1f84ebc5ce0de0ed081f400000cb221cca979fbb54c670583b8ac7336651f785083b3706be196000186573594a95c49836ff0316987c425c3a70b3acb1c0198caa36c032e47010cb71b8c32cc6a88cad1952a0ec45d9b7f099ad38c0658ec635c707a0457021e00020884dd5a8470c0ca17c2efa89b0b70a16c2d5a9190b22a2602c1800200007670ccc800533011010491262b03e8990c0e6a67f034c98fc0cca6fd02fedd740b890f2368d0ecc4b3b70b12cd0f2c4a9372312a3101c49eb75f12790f1c49b371f126b121449437dd124ea98c1f42a7b076aaadc1c12a7706e2acd41a7bb43148ced6c518bb971438ed5c50abc15140e3b5cce8a1d832c0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286196c57fdeef15fd6adc578589b15d4001c4219fbd0cb7188032d0000556a54bd33e043d3f76088843a9c1513e91f74396bb35062e9874e08ac7112fea260123b91904524c40004130b04c2e4684cdac720ee31f785083b3706b60008000261f38264bfce090005330098ac1f22643076299fc1bf263f06da9bf41a5952a326a54bc19f2ab40cb24c3c122930d04884c24121130704824c141201303047e4c0411f4620131ce5e04c6acd00e9e19580018659381eed0c5233b5b1462ee5c50e3b57142af054503c83c140421d0002087313fa8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284ba30ca00877327a196cc9c131518244c4c603deef1615734c584dab715e1626c5750223114a001c42180002a5899f021e9fbb5070ee50e0a022926206629c8c097f58e01cb63ee09f4766a0c5d30e9ae443b0658174619400004000000012fe000898a8a95952e261c4c1832b8875000ca0e130f9c13376632d8dd42622073e98781adbb3a1458ecd850847e30f6b1f7c3b8a1d832c0ba48ca42e8e3288b1dc4dbac731336001c421b91f052ee46c12d80004c54990931f152b0cae21d533e12ff38246d707689ab336fe12e141f02a11d8e027dc8f09b78312228da7088a258ec1ed41100001043e6cb542c1a6a8fc428b1648073e76760e7d41d1b3f26206cfa3fe09fb4c46219d639077176aa0ca19658057195400146599ae74c7a676a3ef0a1032c21098caf842532ba1090cac842232ae1084caa8420766e0d6c65c8016196a00506588012195e004465680104c3e6b9065b9a1843b0658174919485d1c6511756194119762bb811188a57ed820c1962082f0000a26400180044c5454aca97130e0cae21d6c4d28384c3a7044d992a571260b1c83b8c3a70b3b1f78508283b1176ecdc1adb6ff0316d38c065a61f35c83b18d71a61c35c054a8c9a952f067c087800082213756aad0490a8470c0ca17c2efa89b0b70a16c2d5a9190b2310102c20002,
  0x101463b1c04fc19711eed3bc47b41ab118cd40c462c1891146d38445102200002087ce18a85b365ea11c303283e0ba2a0e82ce9d9c37fa766c30243b312cea98cd60c7ea0ff476342e41d990b34765c2cc9d950b3076442cb1d8f0b2ab1f8e0043aa12990e984982d510ec2b1c0396aa5a0746a9581afbb3a144eecd8505c8bd140d1f704f83c14069e32ac00c1b6f35e23b5cce8a1d832c0ba48ca42e8e3288bdb4ca1ae8c3280767c57ddcd315ee6e0457a8ed915e96adc5782b34124e088c452b703036edbfc0c1b7dc02ec43dc0adb6fc029ecb9400e0cb9002c32dc00ab2c400260000fd708730cb298ad31e0cb3b13410f530e952f5070438ce1904b836fc002cdbb8b5b83122285a7000a31d9c6ad4db8850836fa1388dbd84e136f21380dba84de36e6137476580cd36de6bc4dc08af5b56e2bc20c708d869cc235e0c508bc69c422ec11188a50000a0fd41da61d5070087ce18834f782a281959a092791781d85bee017621c46a490ec19605eda650d6a8099773f0093000008733f74196421e952fb9a44bfce178022195800146598b2e19762bbac4d8aec66482109fe6843532c6109dfb60423000032b86580cb4197032a8002a67d196c656ce16843532b4676dfe608427ed820d19928023658a00446570005196e68606598037195a00d00000cb0196832e065500054cfa32e930eb2c6385810d4cad19667edc2141fe60842658e00d999280240000987ccaa00054cfa65886589c2b084a657800519591652655c5943f6c1068cb140090cb033ba656c2238cb3006e32b401a0cb734306554cec996315de32ec577589b15d4001c428bf6f109ecb1c427000032b86580ca90cb81954001530ea61e385407bc8751c278766259db85896654c66b063f507fa58fc2759c9302dc4c5470a137e9a9a0cb0000c32b898058ec1ed5639077159a01d3d648073e58e01cb63f10a288fbc283241e09fe8ff827de3ee09f08b8218e4fdc1ae943b0658174919485d1c651177619425d58650574619400cb62bfef778afd262a08b49888229723008a0000130f3f74a0e152a8873087a9874a979c2936b83b44d59a83e0d626dfc25c0ec7013f17184de41891146d384451391f053e0880000821f337a988c433a8980caea16032432cb00ae32a80028cb335cf18804c945e013166584213195f084a657421219590844655c210b979048ae4e411b0cb9002c32d400a0cb1002432bc0088cad002099f4d34263d33b4fdb041832c4105ea0e833a800200000014d0a195533b317084d0391b04c6987ce0d8cb734316adc5780cbb15dd626c5750223114a001c42500004df81964fdc930f58eeb1cd668ac914c3aa0e13151c28378432c0cee995b088e32cc01b8cad0068fdbc427b2c7109c987cdc1263c384ca464333c6a11330b5443b09d9c37fb22f45031d8d0b9076642cd1d970b3276542cc1d8f0b2af0501a7995537f10ea84a643a61260acd049399610882654c21d3703036edbfc0c1b7dc02ec32e40188cab00544388cfbb6fc1229013442433a5108eb24039f2a5a0746a9581af800400010e94e04000334d0762cca91d9f15f6ece8513bb3614171ff04fba67c381432dcd0c10f334028760cb02e923290ba38ca22f6d3286bab0ca0a1d518a84c4c6031fb717e5734c584e10b16077bbc57edab715e032ec577589b15d4088c452800710947eec31e45c10c72766c3021d930bfe76442ff1533063eecd018e1315045ae46011400004c570ec8988283854aa43a84398659261e7ee421e952f4df89874e13864850b26cce2f01991727208d800029183b3a7ee4987ac91087a54bd31e1c2636884c44cda130d277e4c2c9df1309277a4c149dd930327744bfc9dc130f38487eece11931332fd734c57b90f702b6dbf00ac000010e610f530e952f507043cce129ae93f7268040001312b9a410f48799fba261e7090ceb9955337e988814fa61e04c698ac0fa0cb937c84c38cc5370b12cca98c37812ff04b64c1c119131104520010000263c35d0000cd3445cf33fae4784dbb91a1336e4e04c3391812feb1fc3fd2c760f6ab1c83b8ac900e7cb1c0396a67c37ff1facdbd996315de001c576c7e214511f7850647fc13ef1f704f8065600061964e0f8cb734308760cb02e923290ba38ca22eac3282ba30ca0065b3271626c587000021e621cc21ea61d2a5ea0e0fdd9c233550b1c83b8ac900e7cb1c0396c7de14191ff04fbc7dc13e021c8002087538428760cb02e8e3288bab0ca0ae8c328021dc582e10b160654cc18fbb340638000152a86572a5e10f541c261c38446aececd8bb087482450ec985ff3b2217f8eca85a53b1a1684ec585866dfa055cecc9b9c21e46d1a1d98967878e24da242892854c60fa153b8371566a0d3cecf8afb087e2be5da18a4676b628c5dcb8a1c76ae2855e0a8a075d36653175999495dde651975799455eda650ee698b09b56e2bc011188a50000987152a952f087aa0e043a9c21000821d44fa087313df1f74396a1d832c0ba30ca00877327ab1c44c045c10c76ecd418d80000cae54bcfddaa54384000104399c1810ea281de0a034f566870797b6994310ee64f4000043d3f76a0e0a978659383e66289888229261e089dc8c1acc54aa2451b7e81574c3a70740010000000a660098382d725fe093131581f44c86073531f8199,
  0x1724e275963f87fa8fd62915da103e854c470f931588834c46219d969807b6596015c65500054c7a6768caa84201972005865a8014196200486578011195a0041fb60830658820bc001000019762bbac4d8aea000e210ca9583394cfa70ed37e9a9a3f5e682963b07b558e41dc5668074f59201cf9638072d54b40e8d52b035f55680cf497f9c2f21e6709553a1a1f8fc428a1d9d0a278fbc2831d9b0a0b907827f9dca09fd8ff827dddaa09f68fb827c0a9683192a3e0c444390004000a70f065b9a1810ea684898899b443b0658174d994c5d24652174719445dd8650975619415d1865010ea8c5443a6314d0e88c52439e31450e68c504396313d0e48c4e438e31350e28c4c4386312ee698b0910ee2c170858b03b56e2bc011188a52a660c7dd9a031c00001964659261d087aa954a97a8383f744c38e1f8914874a7020ecd9b1b6dfa67dc8719c3d3b2617fcec885fe21d607bcec599523b3e2beee698af6087e25a61d989676e1625980002a6254aea96d0ea21c2439487410e721cc439087190e2151e8fc654b1d9da6220cb28748a95130e4c3a98a9668ac7159227ee88792ab554ea98f133e043d54aaa0e0e1f023126086855c9c098b8bc21918983822372327004fdb0c6f36fe12e20c488a3261a094c1100001043e70c5cfc89975aa21d8541f05d150741674ece000c25fe70bccaa99d9917a2818ec685c83b321668ecb85993b2a1660ec7859578280d3ca97000910e4001130f9c1b4dfa6a6865b9a1810ea684876b99d1262266d10ec19602a62657cecd995e2a4665417b699433b162e1043b8b05c2162c0cecf8afbb9a62bdec4d8aea875425321d309305668249c11188a5000e20f0a9983a72a520e78a93839d2a4a0e70a90839a2a3a0e60a8d83976e0606ddb7f81836fb805d887b815b6df8053c00010e354aea96d0ea21c2439487410e721cc439087190e2151e8fc654b021ebb3b4c447640ec921d22a5443c8987267c4c3a98a941c2cd158e2b24432c9fba4c7870f4dc18cac33ba656c2283f8e370232c4d5ba61e0ce717084d0391b04c24c28004263c36567ec431a1fa90c604c24121130504804c0c11f9301047ce5e04c946210caa7ee431cc5c00c704c1c111b91938027ed86379b7f09710624451930d04a60880000821f3862e7e44cbad510ec2a0f82e8a83a0b3a7670dfec8bd140c76342e43c14069f0ea84a62b34124edc0c0dbb7dc02ec4388cfbb6fc12290e94e041d9b0c08764c2ffc3b312ce76642cd1d970b3276542cc1d910b2c763c2caaa6335830e9849847ea0ff443ac0c3ac7e3868dbfcdfda62a34286554dfc19610882654c2188cb9006232ac010996315de32ec577589b15d5013442433a5108e001c421bfcd1082cc94420152b067299f4e1da6fd35347ebcd051d8b32a4b1d83daac720ee2b3403a7ac900e7cb1c0396aa5a0746a9581afaab4067a4bfce1790f3384aa9d0d0f9d9f15f71f885143b3a144f1f785063b36141720f04ff3b9413fb1ff04fbbb5413ed1f704f80872000832dcd0c087534243b5cce8931133684c4ccbf21d832c0ba48ca42e8e3288bdb4ca1aeec3284bab0ca0ae8c32804c54c9ca1d318a7734c5848877160b842c581dab715e0088c4529533063eecd018e0000000aa95421e952f50707ee8987065919649874e1e1c2a32ba109130f9c2b7ed820d19628012196070e8caa9bf832c21104ca9843a197200c4655802a809a21219d28847000800000019a68196e6860cb18aefb1362ba8003884a00009bf021ea61d54aa54bd41c267d3876008c6571c2d196a2ccd99208427f9a10d4cad1c38196e686065d8aee000032c021ea61d54aaa0e0a97d89a4cfa32e06550005387470d49879c293f76707c32c00030cae6ba1639077159201cf9638072d8fbc28323fe09f78fb827c0439000410ea70dd33f085d7f9c116ccaf1ae732c210e0cae842d32b22cb4cab8b2c7f982109fc6883a664a009531e9bcf1964677531519be4c3c21399631c2c196a6f286569b8332aa6fe065b9a1843b0658174719445d58650574619400cb664e043b8b05c2162c0ec4d8aeb2a660c7dd9a031c000032e865c0cb01954656933e8005087aa0e152aa61d2a5e70e00d310f2368cdd7c49e2a6307d0aadc1c13b43148ced6c518bb971438ed5c50abc15140eba6cca62eb33292bbbcca32eaf328abdb4ca1800010ea10f4a97a67f386e66d098800083f766dee3f507fa26120b6097f82d3262665f90ec1960262a64e5c9309d300004c30985130626084c089800657261c54bd63f9c3612290e94e0436fd33ee766c3021d930bfe76442ff10eb03df0ecc4b3b70b12cca98cd60c7ea0ff4b1f8e1a10e338647ebcd051d8b32a44bfce1790f3384a21c8002087534244c44cda1d9f15f67eece0fa1d832c1734c5848877160b842c581dab715e0088c4529533063eecd018e00000cb2b246c4d263c19669874a97930e4c56a0e021eaa55386a18e4fdc1a108b802611638072d7232662a3ee09f03f6e1bb098382d710e4001043a9a12262266d10ec19605d18650043b993d8b9e275dc9389d600007eb897f1fba0cb24c39315a83858fc70d00030ed516d63b4c5b21b7200166df4287418e11b86decdf6b4e7356a3b2c6a99b750a6c6de42759b7109ce6dfc25c1b7709663b340930ed101b63b2406b8ecf,
  0x104eaa46412ba8473608e4fc4e0b97b1358e4ec4d2b9f9132eb1fc3fd2c970f8eb34c3ca2c930f06b5443b0aa6307d0acd41a786580006195ce2847eb148eed0c5234803146520fc50ec7ff142d22f45043c15140ea9dc49908740008dc7cd890873352c43ccccc931018e076742b490f102ac43bc0aa90ed02a843940a843a41220dbf0487843a000410fc57c9fb90c7254b418c843d389e43d4cc321d832c0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286875462a5cd3161221dc582e10b1606196c57fdeef15fd6adc5780223114a7ef431ec5c00c7854cc18fbb340638000130eaa552a5ea0e0fdd9c521324b3403a7b979048ea264cdea858334f20f05012c900e7d188432cbb95349eed0c5233c1b147ef05c511c7fc13f6aad448ebb550658dd740b690ed02a821d000206580006195ce282a75346a21ccd1690ea33ee43ccccca1d832c0ba6cca62f733296bdbcca3aeec3284bab0ca08877160b842c581865b15ff7bbc57f5ab715e010fc49c36fc121e088c4529fbd0c7b170031e1533063ea95018d8000043e4c44fddaa763b3843c0877043b4c3aecd4a97a83821c471443a7c83c1404b3444c746210cb2aad419f3b95349e438c0c1b6fe1256a958d653b43148cf06c51fbc17144643b40aa0874000821ccd4b21d832c0ba6cca62f733296bdbcca3aeec328421dc582e10b1606dbf04879533063ea95018d80003f76a9d887910f021dc10edd9a952f087c195ce281c473f7470908791c4e261c7134989997eb9a62c26d5b8af004462294000261d54aa54bd41c043d389e6a088719a2c54c61bc159a86693b321634ecd856821e2055a2e799fd8d422659b7e091458fe1fea2428590874a15a548c9bd55aa26df23f59b7b3b3831c0fdc863973f0095498382410cac000d37e1c3b0cb2707d63b07b558e41dc5648073e58e01cb62e106788b8018f152b035f54e80cb1cbc02464cf87120fdd1c293f5e2fb821f8af98fc428a23ef0a0c766c282e3fe09f776a827da3ee09f02a5a0c649888229723008a04390004261c713443a9c4921ea66190ec19605d24652174719445d58650574619400cb664e10ea8c54bdde2c2ae698b0910ee2c170858b03b56e2bc011188a52a660c7dd9a031c000010f530eaa552a5ea0e08791c4e000c3b545b58ed316c86dc80059b7d0a1c6de42861b710a11063846e1b7b37dad39cd5a8ed135663b2c6a98ec91aa46dd429b1b7f09706ddc2598ecd024c3b3c0518ec7013f065c47bb4ef11ed0624451b4e111440880000821f3862a11c303283e0ba2a0e82ce9d9c37fa76342e443aa1298dc0c0db90e233eedbf048a43a53810764c2ffc3b312ce76642cd1d970b3276542cc1d910b2c763c2ca9d9b37f898f8dbf2a6335830e9849847ea0ff443ac0c3a63c386ab1f8e1a36ff37f67ebcd05262a110c9878427152b06720010000267d38764bfce17a6fd3534000c4182c760f6ab1c83b8acd00e9eb24039f2c700e5aa9681d1aa5606beaad019e8cab00301960001bf6d3898195cda5aa74343e762cca9195b165c655459599531654001c576d89b15d71f885143b3a144f1f785063b36141720f04ff3b9413fb1ff04fbbb5413ed1f704f832d200fecb1801bb2e5003832ec00b8cb9002ccb100098872000821d4e248cb2388c43cce2293113368767c57d952d06327eece251b6f35e232dcd0c0ed733a28760cb02e923290ba38ca22eec3284bab0ca0ae8c3280196cc9c5cd3161221dc582e10b16066e0457a8ed915e96adc5780223114a54cc18fbb340638000021ea61d54aa54bd41c130e389a0028cb1842732c21098caf842532ba1090cac842232ae1084caa842000006568ca93f6d389825fd638072d723208a49881b4b8fb827c043900040cac000c43a9c4921e6711c32c9c1f43b06581746194010ee2c170858b030cb62bfef778afe3f7a18f62e0063c2a660c7dd9a031c00007eed30eaa55087a54bc987283838940fa15311b4676862919dad8a31772e2871dab8a15782a281d74d994c5d66652577799465d5e65157b69943000021d421e90f22a5e71240020875382a21ccdffaab4067a19580018659383eee50e0a0877327a196cc9c0223114a0000fdd843d2a5854bd41c267c38900cf555a9c157728705133e9c3b4dfa05fdbee8927566a0d3de0a8a072a5a0c6443a000410e6708d7b6994310ee2c170858b0304462294a99831f76680c700001fbb087a987552a952f507043cce2383e854c46d19da18a4676b628c5dcb8a1c76ae2855e0a8a0710e800104399b4b0cac000c8799c450cb270fc98899b45d36653175999495dde651975799455eda650c32d9938b9a62c2443b8b05c2162c0ed5b8af004462294a99831f76680c700001fba1964987552aa838087a54bc9871c46277c4c28e22131332fc0002e691310261c7ee88799c45277a4c20e21931332fc0002e691310261c4c28fdd10f338884efc9861c42262665f80005cd226104c40987130a3f7443cce2193ba26047104989997e00017348986130826204c389851fba21e671089dd930438804c4ccbf000026057348986130826204c389851fba21e671049dc12fe36884c4ccbf000026057348982130c26104c40987130a3f7443cce201b7126186854fdb1a103f7218e62e009847232662898382d7260a0b5a2e789d7,
  0x151300cec0000ec658e6ee54a9706574c3821d4a969c5e099a6df8005a67d378298782cd9b790994766800626fd352f07a04571d930bfea26019dbb9414050ecc4b3c83d0e9e6dec2601b75097a6dcc25e1b710976a98cd5045cf13aab3444c6c1a8114e76342e41d990b34765c2cc9d950b3076442cb1d8f0b2aa160195392605aee5e412093063314ed504fdc3aa12990e9849847fd0e7ca968359aa560cee4bfc126263c367cb244ce1c5c6137117084ce39f9132cb1d83daac720ee31a803349b7d09af1f8851647de1420acd0493c269116cecec1d0843c000410ece2e1fba35aaecdcd2e291932d254b06381fb90c726ddc259930f044ea950e2dc5c01300e4604bfa83f11aea0ec45dc1891142b1fc3fd2d510ec2b1c0396a1d50e520878000c7dc340b1fac523c8bd1410f05450382211144d38c065b5c00180d38004f952f38b46dbcd78b4e7356a3b18d1321d832c0ba6cca62e923290ba38ca22f6d3286bbb0ca12eac32823b3c7c38ecb1e00762c5c21d9f15f610fc57cdcd315ee6e0457adab715e0088c452b703036edbfc0c1b7dc02ec43dc0ad90f502b2dbf00a7800021c64c4032ba61c10eaa0e0ece1c5d14211f7c3b8bb3734b83b18d13152c18e0f054503ac731339170c33b9d9d0ad28760cb02e8e3288bdb4ca1dab715e0a95c495c3a41220088c452b6ff030643d40acb6fc029e00008719fbb54aa7ee10ea13100cae21d541c043b38b865f89890c71b9a62bd821f891543ae1cacfdd863b000117063ee952e54a8716cd9c9fb90c727edc31b930f044f17004c0391812feb1c0396c7dc13e87ed43391fb30ce27ec43381fad0cdc7eac336bb3506364c34131130b04c24c24130130504bc4c0c12e92ff04b6a954e2cc5c21338e4684cdac760f6ab1c83b8c7e214591f785083b3b0746ecdc1af9fbb3594a96c4a3aa57125610e8001043d124edc0c0dbb6ff0306df700bb10e238b0acd41a7843f15f2f054503a1d832c0ba48ca42e8e3288bdb4ca1ae8c3281734c584dab715e0088c45280002620195d30e0875507054bce2d06753f7031c141d88bb3b3a15a410f00018748244011088a22a5a0c65a7180cb69c0027c21d00021d8c6a710ea8c54c2162c0ed5b8af0087e24a821e892704462294a99831f76680c71bee017621ea0565b7e014f0001170c871ab342a5e4c4141c2a5538b2055c8791c566df8243c21d0002087a708552a1c57087e24a80002b342a5e4c4032ba61c10eaa0e08711c5836744c18cc51fb90c727edc31b9fb50c6c7ecc31a9fb10c684c3c113c5c01300e4604bfac700e5a4bfcd4947dc13e87eece1021d832c0ba30ca05cd315ec10fc48abb350636000152a152f10ea438832ba61c50704c40e2b99aa3b3a15a4ecd85673b2e1594eca85643b221588ec785613b326e7087519f7087e24aa1d209106df8243c000043b21e4438959a261c5070a954e2b000b36fa1304dbd84c036ea12f4db984bc36e212ee0d408ab36f26ca5a8099cc36fe12e0dbb84b31d8e027e0c488a369c222881100001043e66f544c065750b01922310098e8bc0261c32b00030cb27151668074f59201cf93159a9db1362c3e41e0a028ff827ed53183e876aa0cb1dca9a4f3b3466a87688fd076862919e0d8a3f782e288d53a89166e3a0580875000710e800108719c5310e66a5887999993f7031c0ece85693b321598ecb85653b2a1590ec885623b1e1584878815621de0554876815421d20548873815121ca05421d209106df8243c21d0002262266d087b8afa087e2be4a9683193f76714821e9c4f36de6bc476b99d121ea66190ec19605d3665317b9994b5ede651d77619425d58650432d993843aa3152e698b0910ee2c170858b0337022bd6d5b8af004462294a99831f76680c700002a552a5ea0e130e9c55337aa26032ba8580c9118804c945e01316e5e4122b939046c99f4d34263d33b40878000800200000884dd5995533b20014cc0285f0d82a26c34a285b0d0aa464333a643055e99fc141261f3836a11cd8226fd3375179c4e1393f1383188c4d6b97b1359178c4d346a11330b1fc3fd2c970f8eb34c3ca2c930f06b5443b0930d044c4c2c112930904484c14111130304424c041101fb818e11fac523c803146520fc50ec7ff142d22f45043918045098fcdfa930e342443d4cc321d832c0ba6cca62eb33292bbbcca32eaf328abdb4ca1dab715e0088c452800711120001648acd1b13498a898808753b389874a9621d450701964e2a02dc4c546d3530f1b31261c6849c9389d6723426800028847674800a832c000319546d8065c8e02196635446568ca9b1362ba832b899c000e212a2e1867536fe12e137e9a2c507622ee0c488a158fe1fe96390771566a0d3c10f00018fd6291e3ef0a10782a281c11088a269c6032da70009f10e800107631a2610e6282cece8569766e0d7d52b892b8748244021d0002087a713c65b9a181dae67450ec19605d36653174719445eda650c32d993826222ff2f778b0a10ee2c170858b03087e2be6e698af7b56e2bc011188a52a660c7dd9a031c6dfe060c87b815b6df8053c0001fb94c3aa954a97a83821c6714c3b8ac7336651f78508283b1176ecdc1afb4e30196987ce0da6fd34583b18d132a571256dbfc0c190e238a208780008221375698acd66a85f0562a26c142285b,
  0x10a1010f00010ece356a10ec488418e11b0d39846b9d8b0abea0f81d0c3a538d47664dce3b3a14591f8c3daab350cd2b1dc4dbc6a1132caad032cb91f052ee7e012612fe38c67ee8d6ac620131ce5e04c6acd00e9e4c3c113930b044aa950e2daa7432ff20f050147fc13f717004c0391812feb1c0396bb950676ed5419510e338c11f704fa2899115aa1644533b350632a0e4e34b54135f4d404ce61b7d09c46dec2709b7909c06dd426f1b7309ba3b4c0688ed101a03b340670ecb019b062845e34e21176a0e81ae8ec734b8ecd850847df0ee2b1cce34021e00020884dd5ac7f0ff4b5443b0a84707cca17c1d9a89b0700a16c1b7a919069a54b0c9a843f15f26e0457a822315e71fac523bb43148ced6c518bb971438ed5c50ac8bd1410f054503952b38c46dbcd788ed733a28760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca05cd316136adc584589b15d4001c41a80002a5c987032b8875262071ac001043b38ac10f4dd190eb335443cccccdcd315ec10fc4951d9d0ad2766c2b39d990acc765c2b29d950ac876442b11d8f0ac276342b000005668a954871283854ea98721d29c6a16b66dd80058ece35ea6e0425c9b7f096e6dc42580ed901523b540530ed3014a3b440521b6f35e36adc584589b15d5062045034e0113e001c41a800036f86de8dbc1b7436e43b30763021f4c38a0e4e349b4e4c7869a8002883259201cf9962000f19546d8065c8e02196e37186598d51195a32a63fe09fb76aa0ca87631af51d9e2d6d42c88a7835212f8dbb000b36fe12dcdbe84b636f612d4dbc84b436ea12c8db984b136e212c076a80a61da6029476880a41d9a028a0c408a069c0227d41c1a058fba1cb4a96193537022bd476c8af458e225fd30f02637232089c9871c672a567188db79af11dae67450ec19602a62657ca9199505d36653175999495dde651975799455eda650d7561941b56e2c22c4d8aea7234266c00388350000087c988152e4c38195c43aac7338d06574ec599526dfa67dc87599aa21e66664ece85693b36159cecc85663b2e1594eca85643b221588ec78561874871995319aa03f746840fd78bd48b9e2754fdb8637724c0b5d52a1c5b260c662a2e00980723025fd638072d8fb827d0fdc8675766a0c648719c605072699541d88bb51300ceda7180cb1d8c7179dca0a02907a1d3c10f000104426ead668898d58fe1fe96a88761508e0f9942f83b351360e0142d836f72f2718ca961935087e2be63f58a4776862919dad8a31772e2871dab8a15917a282011188ba2616098497f825b2a56718948c998543b06580a98995f2a46654174d994c5d66652577799465d5e65157b699435dd865097461940bdde2c2ae698b09b56e2c22c4d8aea8b842671c8d099b000e20d40002c73262054b930e065710ea4c38e3399f721d607bc8799ae06e162599b7e09140878000821f8969087624400002a623f76a95487128382a5c987163f2d5087487198004131332fc4c54125930d04884c24121130704824c141201303047e4c0411f0000261c4c2897f131072f2718c501483d0e9eee5419ca67d378832d4cc0acd1131a6584217995f085c656c21619590856655c21519550852e5e412093063314fe3041b92ff04b698f0d9f391a1336b1c83b8c7de1420ecdc1ada61f38c24c3c113800200000014cc0391812feb1c0396a62b07c8990c1d8a67f06fc98fc1b6a6fd0696ed0c5233b5b1462ee5c50e3b57142af054503c7dc13e88760cb02e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284ba30ca0589b15d4001c41abb35062e0000988152e4c38195c43a952b38c408c8983000825fe7049c9c09864cfa20f9648073e7f9a10d4cad000a32aa6fe23fe09fb32c21128caf844932ba1120cac844632ae1114ca9844376aa0ca065c803a196e00e465580334c7a6ab0989997e43b06581756194132c62bbdfb7084c658c212c98a822d261a0898985822526120890982822226060884980822000004c39c8c80034c54990931f152b2621626832b88754c3e7184da70005330098ac1f22643076299fc1bf263f06da98781ada6fd069698f0194152a326a54b41aebb3614211f7c3b8a83b0b3cb1cc4ce43a7125ea95c33c45c338beee505013b5413f720f43a7c7fd0e7cb3444c6ac91130ce46812fb9790482e4e4119130633144bfc12639f9132d1a80334ab34124e10f00011fba35aa10ec488130f044ea950e2dc5c01300e4604bfad510ec2b1c0396c7dc340aed0c5233b5b1462ee5c50e3b57142b22f45043c15140f0e942b49d9c38ba54bce2d21d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac328210fc57cdcd315ee001c41ab6ff0306df700bb10f702b6dbf00a780002620195d30e08755070438ce30083d664a0098001000019686f1000299804c560f9132183b14cfe0df931f836d4dfa0d2d33e03392a5464d4a969c5e1d8e6635da18a4676b628c5dcb8a1c76ae2855e0a8a075074167531e1b3e52326614a98995f5d36653175999495dde651975799455eda650d639099d874c24c0003883554ac19dca91833500007675dcab91b087adbf8fdd930e2a5c4c4032ba61c10eb170ce2f9bbd,
  0x12a5ea0e087943a4087c1964e3d1c5a10e80010a971c6c10e66d2c43b993d00004c3898828384c38195ce3b9a103f7218e4fdb863700007eb8fdd28384c391704e3a86575132161220285813f700034fdb9c014cfa6f0531e1b3050b071ccfd886523f661910fd68bd33f562f48fd48bd18c40264a2f0098b727208c8983000810e40011cbc9c6310ea6848fd79a0a3f4e682498899b4262665f843b993d3f7a2c06f778afd52321646242858e262a08b49878227261a089898582252612089098282222606088498082200000987cecd9d9d3f689bf097f1fba0cb210f5668ac9158e254bd30e391938e815d531e1aa93f7219221e2857600011784fd81fa826104c00ecd9d9d3f741965648ac7150b071cc0059b7f099a6de42651b7b09806dd425e9b7309786dc425da67d378298f0d96c1e8115d06a0453a8980caea1603244620132517804c5b9390464e5e4e31930633146df426b9b7709664c3c113930b044ae4604c24269116d0624450a9190ccf170431c821e00027ee063821d518a80884451261e0b36d70006034e0013e7668006152e38de6dbcd788ec6344d842c585deef1615734c57b9b8115eb6adc5780223114a767c2cf9d990b34765c2cc9d950b3076442cb1d8f0b2a762c2c990f702b643d40acb6fc029e0000ec9130c8d409bf098812fe3b1819661d3acd15922b1c4a9610e350709870ece1c7205ae4c18cc5392713acb1fc3fd130f044f1fac522b9181308b1c0396c5c10c72ed081f41fb818e0875462a47dc13e0a9884b3c3b20bfe1960001865738447648d5d952e354c43d4cc321d832c0ba6cca62e8c3280196cc9c610b16177bbc5855cd315f16adc5782a541226088c4529d9f0ad676742b49d9b0ace76642b31d950ac876442b11d8d0ac00000986131025fc10f4439952c3b14a0e130e43a538e209949881c598b842671c8d099b0cac000c32c9b324c3e212c0010000000a20c996380336588003c6551b601972380865b8dc6196635446568ca936fe3ab541d88bb58e41dc410f00013b246aee3ef0a1004422288ece85693b36159ceca85643b221588ec68560766e0d7da7180cb69c0027cecc9b9c1d8c6a7152b892b8748244159a834f0874000821e9c21782a281ca971c6f1dae67450ec19605d1c65117b699430cb664e0ec58b843b3e2bec21f8af9b9a62bded5b8af0b1362ba811188a5000e20d5b7f818321ee056c87a81596df8053c0002a5521c6a0e130e087538e00a7d3119ba84c3c6cc465b8dc6723c26f1c8d09a058ec1ed5639077136fe3ab63f10a2c8fbc2841d9d83a13b246aedd9b9a5c2a5831c141f88d7507622ee2e386b38b8619dcece85693b36159ceca85643b221588ec68560043c000552d894754ae24ae1d2091004422289a7380f769c6032da70009f08740008ecc9b9c1d8c6a70ec58b84087a249d59a86693f7218e531582dc4c860abdb8181b76dfe060dbee017621c471b552a1c5b3f746819c9389d6727e270635089988b80261163f87fa592e1f1d6a887617232089d31f9bf5261c6848ecf8afb087e2be63f58a47900628ca45e8a08782a281d638072d43aa1ca443a00040cb0000c9889c6e0cae71b04399aa68fb8681476b99d121ea66190ec19605d36653175999495d24652174719445eda650c43b993d0cb664e2e698b09b56e2bc2c4d8aea0446229400388350000a0e130e152e38de6ea065b8dc64c560f9132183b14c440e7d31f836d4c3c0d6ca9500092a5a6970dbf8ead767428b1d9b0a108fc61ed63ef87713b246aed63b89bc58e626822e386b38b8619dcece85693b36159ceca85643b221588ec68560723e0a85c8d826554b6251d52b892b8748244141f88d7507622eda7380f769c6032c21d0002043c00041109bab3b326e707631a9c087a249d59a8669508e0b7942f82b151360a1142d82755232095cec58b84724e2759c9f89c172f626b1c9d89a58d422661cfc899758fe1fe964b87c759a61e5164987835aa21d84a9083de2a3e0ea8a93837b2a4a0da4a8e83652a520d24a8d83426e0606ddb7f81836fb805d88711c6d54a8716cecf8afb087e2be63f58a477686291a4018a3276b628c641f8a1d772e28723ff8a1676ae285645e8a08782a281e2e0098458e01cb443a00040cb0000c32b9c6c10e66a9a3ee1a051dae6744fdd19b421ea66190ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650ca99993e10ee64f432d9938b9a62c26d5b8af0b1362ba811188a5000e20d5c8c8229000054b941c261c262271b8001043b38ac10f4d6890f33332a9ec361aab70d2cacd43349d9d0ad30e90e3345e71385188c4d6c6a11330b1fc3fd2c970f8eb34c3ca2d510ec2a9dcd93aa6335f643dc57d043f15f31fac523c803146520fc50ec7ff142d22f4504087400081960001865738d821ccd5321d832c0ba6cca62eb33292bbbcca32eaf328abdb4ca18877327b734c584865b15ff7bbc57f5ab715e0088c4529fbd0c7b170031e000054aa7eeca9728384c384388e368229262071adc8c097f58e01cb443a000410e66a9a3ee1a0543b0658043b993d000054b941c261c0cae71b02ba263d378299f0dcf26fd35187668cba9d9d0aed0f1048db71d362043a8cfba61e09c643b40aa1b7e001643ccd701b7716b6dbf048a1b71,
  0x13f7221cc21e86592a5ea11ce459af51d9e049c76a80a61da6029476880a41d9a02887639a6569de23d944c08b169c0229011000011db22bd2d5b8af0044622e810f88a083d0133a0c484b70000a11933ea9184c38a0e4dbf9c89140d22f03b0bc14069e8760cb02f6d3286b5404cc2b3412511a80333c4840b220000ece9fb910e610f432c952f5232721c00519531640657c2200caa37b4658c577c04c108ace90422000032c06570cad195832ac655065c0003b1349bf4e428a0691781d85e0a034f5aa0266159a09288d40199e2420591523022ddae000c01d8c6bd476781271daa029876980a51da2029076680a269de23d9a7008a40440000410f88a0831212dcdbf0c6f3f6e18de2e0063a3f70720d42386063b380030ec985ff21d607bc87481ee8766259db85896654c60fa1da18a458fd41fe8878936821de4c5487692c33f5a2f4cfd58bd23f522f4563f09d68c40264a2f0098b59a01d3d648073e724c0b5dcfc8250727208c8983000872f2718c97f9c2f3b166548ecf8afb1db22bd01118af3907827fa3fe09f710e400108799c4010ea684876b99d1262266d0989997e43b0658174d994c5eda650d77619425d58650443b993d43a6314f0858b0bb9a62c26d5b8b08bdde2bf6c4d8aea000e20d498a822d261e089c9868226261608949848224260a088898182212602088000039193b207638ecb1d983b287630fdd152a3b34987141c843d0cb254bce42041f32a40029fb699db32ba10d8cb0842f32be10b8cad842c32b210accab842a32aa10a465c801f19660070658801b195a0065fe6083e7f1820dd9720836000400000029c82196a72048719c80196e677d33e06553f6c003531e1aa93f4e6824cb18aefb1362ba800388353f621948fde864c3f6a1914fd986443f5e19080001fb88bc27eb0fd51fa88c42e7e0fdd1d9d508ca0e487910ea21d043b887810ec10e610f432c952f4c38720c0028cb1003632bc00d0cad0032cb9041dbf8d085e6580005195f0880657421f9959087a655c21e404c10926554dfc33a537b4656c2119953083e32cc0098cab001e32e4df226fc378632dccef996315de32ec577589b15d4001c41abf6d1066cb144190000196899f531ea61c000a720800390e7038c43940c8b72312a2dc7c49aaa7b076aa9dc1b8bb5b1460ed5c50a48020f8f1ff83c1ac961384b2484d345e60d7f178834190f715f49908438a63e10aa001000010f5330c8760cb02eb33292babcca2dcd316136adc584589b15d4000c41eb2ea00cacb98020b325004c0000871267d3f6e43a887410ee21e043b043990f2087a1964a978006196a7204d5a8ecf1b1e6dfc25b8ecb0142d39846bc1881140d38044f821e00020884d30289b0b71101c49eaab70704ee5c50dc83e0f28a17c2efa85b0b56b3484d6c3cb12a50f1c49b46220d24a9ec1daaa7706e2ed6c5183b57142899f842ec8020f8f1ff83c1bfce08b63b1ccc6995e3302b2584e12c92134d179835fc5e20d06658421c291937d49908438a63e10aaff3042100040000656c59999591664655c59899551660000c41eb2ea00cacb98020b325004c32d0de226fd0ccaa0f82e8a83a0b3b1a844cc43aa12990e984982d510ec2a9681d1aa5606beece8513bb36141722f45033c14069e3b5cce8a1d832c0baccca4ae923290bbbcca32eaf328aba38ca22f6d3287626c5752b34124e088c47c8007106b170431bb703036edbfc0c1b7dc02ec0000871b9f83f7498f4fdc267d3f6e1964439952f087a7675423261c50727200d5a8ecf1b1e6dfc2718ecb019ad39846bc18a1178d38845d821e00020884d30289b0b71101c49eaab70704ee5c50dc83e0f28a17c2efa85b0b56b3484d6c3cb12a50f1c49b46220d24a9ec1daaa7706e2ed6c5183b57142899f842ec8020f8f1ff83c1bfce08b63b1ccc6995e3302b2584e12c92134d179835fc5e20d06658421c291937d49908438a63e10aaff30421283e0ba2a0e82ce80040000656c59999591664655c598995516610ea84a643a61260000c41ea8470c0cdc0c0dbb6ff0306cba8032b2e60082cc940130cb43788987cde090e233ee43ac95843b312cea98c1f4267c380298f0d549fb63388ed0c522c7ea0ff47ec43291fb30c88b1f84eb4620132517804c5b92605aee7e412839790482e4e411913063314e4604c245c136dc7ebcd0512ff385e9bf4d4d36fc1228b3403a7ac900e7cb1c0396aa5a0746a9581afaa54063610f0001043b352cece8513bb36141720f04ff47fc13ef1f704f83b3413de21c8002087534241960001865738ee43cce22930f35d24c44cda043f15f27eece3f152e38de3b5cce8931332fc8760cb02e9b3298baccca4ae923290bbbcca32eaf328aba38ca22eec3284bab0ca0ae8c328021dcc9e865b3271734c584dab715e1626c5750223114a001c41ac3a50ad20000ece9fb84c38a0e0e3f9a12262208a4987822772306b3043a000410e627bdd9a831b54aa244021d0002087a707c21f8af90cb0000c32b9c7d2a5c71bd746194010ee64f432d9938b9a62c26d5b8af00446229400043a450709870fdd9c7e122010e8001043d3844a950e10043f15f254b8e365cd316136adc5780223114a0000fddc3a45070987032b9c7d000821d4d660873352ca954488043a000410f4e0f8877327a0001c8c1fbb,
  0x10000987832caa5454aca0e8e4d99362a62657ca9199505d36653175999495dde651975799455d1c65117b699435d186500a96835d2a560d6c000152e4c3ca0e9d9b9c9a0ee2b1ccd9947de142021d0002087313de8760cb02e8e3288ba30ca00877327aecdc1afbb350636000130f2a565074196552a152f3932716e3ee072e2a5e72590ec196058e0260e2e0063a0000a0e4fdca8464c38196552a1c9714211f7c3b8bb3706beb1ccd992a571258987c425c3a70b3acb1c0198caa36c032e47010cb71b8c32cc6a88cad1952a0ec45db4e301963b18e349b7f096e6df425b1b7b096a6de425a1b7509646dcc2588ecd0145062045034e0113e0878000800200000884dd580053300a17c360a89b0d28a16c342a9190cce98ac16e2643055e99fc14126fd3372e49c4eb45e71384e4fc4e0c623135ae5ec4d645e3134d1a844cc2c7f0ff4b25c3e3acd30f28b24c3c1ad510ec298fcdfac7eb148f200c519483f143b1ffc50b48bd1410e464113887400084c38da2130d277e4c2c9df1309277a4c149dd930327744bfc9dc087313de7eec31dbb350636a954487843a00047670ccc843f15f2dbf40ab90f2392a10f4e4a0ed733a28760cb02e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c328021dcc9e9313180c4c445fe5cd316137bbc57f5ab715e1626c5752c701306088c47c8007106a7ef431ec5c00c74000130e1fb9508c196541c952f392c001c87599aa3b3a1674ecd859b3b321668ecb85993b2a1660ec885963b1e165487281b821e20628877818921da0620874818621ce061487181836e04251e1d3092c6dfc24ad52d03a354ac0d7dd9d0a2c766c28423f187b58fbe1dc563b89bc58e62681c8f829f72366cc531188674c3e212e2e386b18b8619d59658057658e00cc6551b601972380865b8dc6196635446568ca9507e235d41d88bb69ce03dda7180cb1d8c71a4dbf84b736fa12d8dbd84b536f212d0dba84b236e612c476680a283102281a70089f043c0004001000004426eac002998050be1b0544d869450b61a1548c86674c560b7132182af4cfe0a0937e99b9724e275a2f389c2727e270631189ad72f626b22f189a68d42266163f87fa592e1f1d669879459261e0d6a887617232089d31f9bf5261c684a3f58a47900628ca41f8a1d8ffe285a45e8a0810e800104399a960874000887b8afa087e2be421e9c941dae674487a998643b0658174d994c5d66652574919485dde651975799455d1c65117b6994310ee64f49888bfcb9a62c26f778afeb56e2bc2c4d8aea58e0260c11188f9000e20d4fde863d8b8018e8000152f4c387ee54230659507243c8e4a80061d8e362cdbf84ef1d96041076480d76a0e23860d588c66a06231542f86c150b61a162f389c28bc6269964b87c759261e0e4018a308ffe2851dad03b576ac0dc553d095254ec24da1e505dd878c16a532108714c7c21540020000000620f5975006565cc0105992802619686f1131e05741daa417476990161da23f421e2091b6e3a058133e1b9e21d467ddb7e09144dfa163e1d285673b34724cec5858621c605d8ecc9b9c21e6666624289286fba249d59a834f55680cf553a032c54a80c6cece9c87782a2819dca09fd76a827d9d9a09ef10e4001043a8a0891781d8476781271d9a049821f8af95aa02661a7788f68d40199c1100001043e723d48c1c8e1dae674487a998643b0658175999495d5e65157b699435dd8650975619415d18650043b993db9a62c24dc08af51db22bd2d5b8af0b1362ba811188f9000e20d4000152f4c387ee54230659507210f4e4a0914874a1580ec61ba36dfa67dc87599753b166548879999900004388ecc2ab554eaa954ece043db9a47668e49800b36de6bc4dc084b936fa12d8dbd84b536f212d0dba84b236e612c4db884b000006df8dbb41893920002cdbb84d436fe12dcdbe84b636f612d4dbc84b436ea12c8db984b136e212c0db79af184d022d60c408a00000087d41ca9194c386e00e47835f766c28423ef877154ae19e0fdd1a0158e626808791c4972366cc49871a1210e800104399c8d4c3e212c0010000000a20ca2e186758c42195e2f08648658e00cd962000f19546d8065c8e02196e37186598d51195a32a541d88bb513222b942c88a783d213260d484be69c6032cdbb000b1d8c71a4dbf84b736fa12d8dbd84b536f212d0dba84b236e612c4db884b01d9a028a0c408a069c0227c10f000104427230db79af11dae67450ec19605d1c651043b993d262630189888bfcb9a62c26f778afe37022bd6d5b8af0b1362ba811188ba000e20d4fde863d8b8018e80002918508ca0e530e1fb9087a1964a979c8e38c64c3c131930b04684bfce17b91a1340e5e04c939381316b1c83b8acd00e9eb24039f1fbb0c96a9d019647de141920f04ff47fc13eeed504fb21d832c0ba38ca22eec3284bab0ca080004c3d178231045c2087a54bc9885cd20cb221cce46800b36fe12dcdbd84b536f212d0db984b136e212c20c408a469c26d50dbb853736ea14d8dbe84d71d9e049c76681261daa031c76380c036de6bc4dc08af51db22bd2d5b8af0832e23dda7788f6044622ea13488b86b8222dc00029184c38a11941c8221391829163f507fa76840fa10ec19605d36653163f09d754c4259e2e706ee876418180001d9d,
  0x11611734c57bd89b15d4acd04938007106adc0c0dbb6ff0306df700bb10f702b643cc0abb6fc029e00008719d982a54766832c843d2a5e4c38ecea61c396267162090620881417b14530904513c23a144d08cc6a9c04fdaa301136a84039c7691afab9a62be1aa008b23f6e1954ecf8585880816120f484cd00006dfc110a8998c42e4661d20ec6262021cc879152f261c767533e1cb036b83b44d59800050b2a264763283f50760888dbf1caf1308e464e42283838ff1704db700003f707674fd7043d3b207638ecb1d983b289870a97952a3b347ee8ec6065958e272b8db71faf341517004c21fb9390ee464e4212ff385e7eece0b2a6212ce766c2b39d990acc765c2b29d950ac876442b11d8f0ac276342b0043c000410ecdceac900e7cb1c0396c3b20c0d0e902b52a5606bea9d01962a54063654ac18b9d9c395854b8e54843f15f2ecd8505c7fc13eeed504fb47dc13e0ecd04f7c19611f00880000a918331a8760cb02e8e3288bab0ca0ae8c3281734c584822315e76adc578821f1176d3bc091b4e301963b64054b4e0013e0000763a83b508e4c38439a8390cb29870e5689d658fe1fe9c9302d7260c662a3f58a4572302611da103e68b826db8a960c703f72199e35089985aa21d84fd79a0a262266d245e8a0678280d3c97f9c2f3f76706159a092759201cf9638072d0878000821f8af98ff827de3ee09f06fb805d88711cab08766a58879999921ea66190ec19605d3665317b699435d586505746194043aa31530858b0bbdde2c2ae698b09b56e2c22c4d8aea000e20d40001d9c508e4c38439a9190cb2987141c952f395826122e09b6e72326628fdc86ee260e0b5e2e789d7724e275963f87fa3f5e682898899b48fd62915da103e825fe70bcfdd9c1654c42599b8501ef21d472a9648073e58e01cb553a032c54a80c6c21e0002087e2be63fe09f776a827da3ee09f0766827bc21d9a2d21e666650ec19605d36653175619415d186502e698b09b56e2c22c4d8aea000e20d400010e23b3854bc439a847261c987032c9cab3746766c2b39d990acc76342b043a41228dbf4cfb90f33333734c584dab71611626c5750007106a00008711d9c087aa9d552aa61c21d472a848a43a50acedbf4cfb9d9a18de6dfc29d90eb03de438c0bb262b394a43cccccb70b12ccdf74493843c000410ece541d9d394e7664dce2b350cd27edc31baa5438b67ee8db745c01308e464cc51faf0dce7ee4333930705ae4c4412b92ff0499173c4ebb92713ad1a844cc39f9132eb1fc3fd2d510ec2a98cd7dc7eb148b22f45033b4207ccf050d2e152c326cb1c0396a1d30e4e54ac18b843f15f2ecd8505c7dc13e0ecd04f7a1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca05cd316136adc578d89b15d4001c41a8ed901523b5c053b4e0013e00020cba9191d8ea11c439930e0cb29870a971ca91d5a764800610e233ee43accd51d8b32a46df86379d9f0ad6766c2b39d970aca76542b21d910ac4763c2b09d8d0ac043ccccc90f5330d6adc578d89b15d50e9048836fc121e001c41a8ed901523b5c053b4e0013e0000ece1d9854aa7ed8763a1d22a544c3930e043b395007bc87519f76e162594871817621e6055d5319afb8fd62915bee89266df8243c21d00025d366532e698af6087e24a821e89288764181a242059176840f980002b3454aa54b4a972919508e21cc32ca61c3b3a729ccfbb6fc32ba766c3021d8b0b0c43ac0f790e302ec7664dce10f333330ecc4b3b70b12cd121449437dd124e0000ece262b5668a955531043e087a72940059b770a6e6dc42841b7d09c46dec2709b7909c06dd426f1b7309bb065c47bc18e11b9062846034e701eed38c06582200002087cdaf8ec636b83b44d59a83e0742a26019da858065454b0c9b152b062eece8513bb9413faed504fb3b3413de21c8002087539426dbcd78953132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca00877327a6e0457adab715e0088c47c8000261c54b941d865950729870dbf2846394471a4dbe84b636f212d0dba84b236e612c476680a236f66bc944c9a661d8e66360c408a069c0227d42f82b151360a1142d8275043c00041109c8c52326f6dc9f89c172f626b1c9d89a573f2265d64b87c759a61e5164987835aa21d8498382d7900628ca41f8a1d8ffe285a45e8a08724e0b75c8c022a262068490ec19605d66652577799465d5e65157b699430000a118987283b0cb2a0e530e022210ea72840020875359821cc4f79fba35d2ba30ca00877327aecd418db919044e0000fdc152f54a8196530e130f393e680dc8c82270cb0000c9871b440cae692c98693bf26164ef898493bd260e4ef098293bb26064ee898093b925fe4ee0fdd9c7e26222ff21d285693f7071fca971c6f3b386664989997e0cb664e2f778b0ab9a62c26d5b8af004462294000261c21e6a0e0e4e884b0004000130f1c9b54ae24b00028832874e167596380336588003c6551b601972380865b8dc6196635446568ca9507622ec003883569c6032c76b80a769c0027c000021f0cb2a95021da61c36fc7676c4d0ec739381dc56399b328fbc284043a000410e6282dd9b9c9a2a5e72650ec19605d1c651043b993d,
  0x18796254a203893d878e24da242892854c60fa153d83b5556e0e0953b8371566a0d3dda18a4676b628c5dcb8a1c76ae2855e0a8a0710e800104399cbd1d8e72ed74d994c5d66652577799465d5e65157b6994310ee64f400006592a5e10f4ecea61c0442a0e4e5f1c8c508e181948c9cb88766259cfd7864254c6705a2f0064b8b8018f0fdd1cba54e80cb0a95831776a827d8ecd85673b321598ecb85653b2a1590ec885623b1e1584ec6856076680c70fdc9cb95d58650552a0913874815a8000022150721964a97843d3b3a98704399cbd38d26df425b1b7b096a6de425a1b7509646dcc2588ecd0145062045034e0113e000076328394c38087ce5e00000006212c00288324c3c062d96380336588003c879000719546d8065c8e02196e37186598d51195a32a4dbf84b721de0624876816e21ce05ac872816a6dfc24c1bae0922831022821d3859d880a160c10f00015132699541d998d044222dc87581ef21d207b8878817d21c605d948c9cb86e162599bee89273f5e190959a9c1854c6705a2f0064b8b8018f0fdd1cba54ac0d7d55a033d54e80cb0a9583173f7272e5d9b0a0b772827f5daa09f63b36159cecc85663b2e1594eca85643b221588ec785613b1a1581d9a031c10e4001043a9cb55d1c651177619425d58650443b993d21ea2ee887b8afab9a62be01118af3b56e2bc6c4d8aea54a8244c00388353b3e15ae1d2056a6b80030076c80a91dae029da70009f0000a0e432c952f087a767530e0ec739766db8fd79a0a8b802611648073e58e01cb63fe09f78fb827c1c8c9c84507071fc97f9c2f43b0658175619415d186502e698b09b56e2c22c4d8aea000e20d40001fba10e6767421e9d903b1c7658ecc1d944c3854bca951d9a0cb27630fdc1cba391ca11ce45a919390e0000fdc88733b3a987032c843d2a5ea0e4e5c800d3f72721cfdd9c183f4e682559a09283f7a18f4fdb86373f6a18d8fd986353f6218d0fd686323f5618c4fd48630890816440001fae8b8221cca978659087a767530e291939700000001884b000a20c930f018b658e00cd962000f19546d8065c8e02196e37186598d51195a32a48790c6f36fe12ddb7f0930831022821d3859d043c000541d998d044222dd48c8591890a24a0fdb8637566a70622e0063c3f74721141c05693b2e1594eca85643b221588ec785613b1a158152b035f874872c88719cb104462bcdd9b0a0b2a560c5dae000c010e4001043a9cb51d8c72d076b99d15d1c65110e98c53b56e2c2043b8b05c2162c0ec4d8aea000e20d4a99831f76680c7000039193b30a95432c952f261c766930e1d9d087a72d850847df0ee2ecdc1afac733664a95c49836ff0316987c425b2c7006632a8db00cb91c0432dc6e30cb31aa232b46549b7f096f062045043a70b3a087800080020000a0eccc680053300088445ba9190b2298ac0fa2643039a98fc0cca6fd02fedc2c4b3372312a2dc7c49ac4851250df74493aa6307d0a9ec1daaa7706e2acd41a7bb43148ced6c518bb57142af05450390f2389299fce1ba83838428760cb02e9b3298baccca4aeaf328aba38ca22f6d3286088c579dab715e3626c5750007106ad7000600ed901523b5c053b4e0013e000043aaa553b3a9870763843d2a5e1964e5a9c6936fa12d8dbc84b436ea12c8db984b11d9a028a0c408a069c0227c10f000136f66bc944c9a660442698142382de50be0ac544d828450b609d548c8257724e2759c9f89c172f626b1c9d89a573f2265d63f87fa592e1f1d669879459261e0d6a88761507070849881a1204462bce3f58a47900628ca41f8a1d8ffe285a45e8a0810e800104399cb343b0658174d994c5d66652577799465d5e65157b69943b56e2c2043b8b05c2162c0ec4d8aea000e20d4a99831f76680c700000ec672324c38ecc1d9a0cb2a954a97843d3b3a9870e5a1c6936fa12d8dbd84b536f212d0dba84b236e612c476680a283102281a70089f043c00041109c8c508e181948c85918766259e2428928566a70615319c163f74721141c05693b2e1594eca85643b221588ec785613b1a15821d21cb221c672c41118af32a560c5ed5b8b08b1362ba8003883576680c70000087354aa4c38ecc1d9a72321964a97843d3b3a98707631cb3256243a8cfb930633144c4411490f3393a7ee0e3f92ff385e7eece0f931332fd734c584dab715e0dbf048a0223114aa0e42b500008748a95530e10e22a5e1964439843d3b3a4c39c8c9cb210d89888287bf7308da6578cc0c18e11b8658421c34e7356aff304210ecb019a0010000195b1666656459919571662655459834e21180000c41ec18b09c6cb2c02e3325004c32d0de2261f37823b3c051a67c3960d384451022000026df8e57a63c3660087cd4c28980caea1603244620132517804c5b9790482e4e411926fd35344c18cc539181309170431cc3a50ad2a0e4e47284739163b1ccc6a9190cce7ee0e57283e0ba276342e4283a0b3a765c2cc9d950b3076442cb1d8f0b2a7ebcd05131133691a844cc43aa12990e984982d510ec2b3403a7ac900e7cb1c0396aa5a0746a9581af92ff385e7eece0c022315e6ece8513bb36141722f4503483c13fd1ff04fbc7dc13e0f0501a78872000821d4e24a1d832c0ba48ca42e8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9edab7,
  0x15d1c651175619415d18650000021d73f7410ed30e0873399a1d7d0eb0c71917a281959a092889081645e0a034d3f76732548c1c8c0440000410f9bb250740d7544c033b2a5864d8a95831750706a99d9b0a0b772827f5d9a09ef044623e44390004508e732843a9cc82a5e7310989997e2a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd86509746194010ee64f6e698b09b56e2c22c4d8aea000e20d40001d9d4c3810f4e65998a25fe096c9838232261e089c9889cc27234266dc9c0986723025fd63f87fa0cac000c32c9afb8fd62915da103e62a5864d9639077159201cf9638072d2a560c5e3ef0a0c8ff827de3ee09f0766827bc439000410ea7320a979cc443b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d75619415d18650043b993d0cb664e2e698af854c4259cecf860787641818000043d3b3a98714239cca37b6e7e44cb130704644c3c113ad513740e4e04c3391812fe19580018659364a54b0c9b2c900e7cb1c0396952b062f1ff04fbc7dc13e0ecd04f7c6a00cd221c80020875399054bce6221d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bab0ca0ae8c328021dcc9e865b3271734c57c2b341250767c2c944840b220000fdd843d3b3a987148c9cc90cd31a844cb2b34125112102c8b9f804aea460e63a8473984b1fc3fd2d510ec24c40e35c7eb148f22f4504065600061964e631fba398a54bce6221d832c0ba6cca62f6d3286196cc9c0000087a767530e087539907269d9b0a104c3e212e3ef877100040001639899b000a20c9c8d8265658e00cd962000f19546d8065c8e02196e37186598d51195a32a541d88bb36fe12dda7180cb1d8c72f20c408a0043c00041109c8c507071b09881c6b1dae67450ec19605d1c6512c4d8aea044622e800388350000a11832b88752a5c987148c1cc70ee2b1ccd9947de1420a95c49836ff0316ecdce4d261f10970e9c2ceb2c7006632a8db00cb91c0432dc6e30cb31aa232b4654a83b11766dfc25bb4e3019600080000ec639780014cc04188114098ac0fa2643039a98fc0cc821e00020884dd590f235a29bf4d3ca67f34daa17c2efa89b0b70a4642c890e302ed0f2c4a9372312a3101c49ec4851250df74493aa7b0d86aadc34b2b350cd2a11c303285b0b5643a40f745e71385188c4d6b97b13591a844cc43b312cedc2c4b343c7126cdc7c49aac970f8eb34c3ca2d510ec3173c377c5e30d0ca0e0e37aa77364ea98cd7d822315e71fac523c803146520fc50ec7ff142d22f45041fba398a54bce600ed733a28760cb02e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca190f71789734c584dab71611626c5750007106a000043a843d3b3a987032c9cc63404a9ec3e2aab70f24acd43afaa77364ea98cd7d930e34248758638c7eb148f200c519483f143b1ffc50b48bd14101960001865738d64c44cda131332fcba6cca62eb33292bbbcca32eaf328abdb4ca1865b3271734c584dab71611626c5750007106a000043a952e087a9870fdd1cc533684c40e22930f38487eecd652a571260dbfc0c5a61f10970e9c2ceb2c7006632a8db00cb91c0432dc6e30cb31aa232b4654a83b11766dfc25bb4e301963b18e5e418811400878000800200000884dd580053300a11c303285f0bbea26c2dc285b0b56a4642c8a62b03e8990c0e6a63f03329bf40bfc3b312cedc2c4b343cb12a4dc8c4a8c407127b0f1c49b371f126b121449437dd124ea98c1f42a7b076aaadc1c12a7706e2acd41a7a838393a43c8e24a67f386e088c579bb43148ced6c518bb971438ed5c50abc15140e21d00020656000621cce61865939803b5cce8931332fcba6cca62eb33292bbbcca32eaf328abdb4ca18877327a196cc9c5cd316136adc584589b15d4001c41a8000087a767530e152f398819a63508996566824a2242059173f0095d48c1c8c0440000410f9bb25074099544c0247508e730963f9c365aa26df0fdd19b42620662897f825b260e08c89878227261a08989858225260a0888981822126020881c8d099b72f02635c9c0986723025fd639077159a01d3d648073e58e01cb541c1cc104462bce3ef0a0c907827fa3fe09f78fb827c032b00030cb273010ec19605d1c651177619425d58650574619400cb664e2d5b8b08b1362ba80038835000054bc21e9d9d4c3821cce6186f03f7466d22e789d554c4259e1d90606724c0b780002c7e2622195c21e9d9d508e73080020875389221cc4f7bb35063643cce4eaa553844ba30ca00877327a000032b952f087a987141c1cc10b36987ce3a43a61260dbfc0c19d9a396c4388e591fb50cc676642c6930f044e9bf4d4d39181308b3403a7ac900e7cb1c0396c6a10ccd12142c82a5606bea95018da919390e4bfce17bb36141720f04ff47fc13ef1f704f83b3413de21c800208753893170431c90f3393a7ee0e3f9fbb383f0e942b4a839397e8760cb02e8e3288bbb0ca12eac3282ba30ca00877327b734c584dab71611626c5750007106a0000a97843d3b3a987032c9cc015e608880008221397c087ce5e0ec739776adc584589b15d4001c41a80000cb254bc21e9d9d4c38a0e4e5f9a60508e181942f85df513616e142d85ab523216461d98967,
  0x100051ff0e68843d398ca118e4621d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeec32856adc578043f12d2088c45d42691170d70445bb979048a98f411b80002a5ca46130e130f4cf821d5c9c065954c47eec1108ed050726df8ece9cdb326a54bc1af952b06b6ecd850847df0ee28760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ac731340e46c13180008b84a958987952c10ea196530f1cda3602a164455a89936c8d404ce60ed116c106a425f1b7639203b5cce8dab715e46e0425c9b7f096e00013150ec6508e088541c88750cb298720c49cd914211f7c3b8bb373934b1ccd992a571258987c425c3a70b3a54bc18e32c70066a950e4e0caa36c032e47010cb71b8c32cc6a88cad1952a0ec45d9b7f096ed38c0658ec639783b5cce8a1d832c0ba38ca2589b15d506204500007106aecd418b8000000654acece843b0cb2a46043aa8394c38087ce6c1b324c3e212d6390771000400023ef0a1054ae24b00028832874e167596380336588003c6551b60766e697065c8e02196e37186598d51195a32a541d88bb36fe12dda7180cb1d8c72f20c408a0043c00041109bab508e0f9942f83b351360e0142d836f76862919dad8a31772e2871dab8a151dae67450ec19605d36653175999495dde651975799455d1c6512c4d8aea044622e80038835782a0d300001d9d0876196548c087550729870a969cd71316b24039f393904704c40004130f39a51ff04fdbb55065454b0e6ac5c70d6717843252a5b128ea9d448b370303704390003b71d362043accd521d50eda766c2cd9d990b34765c2cc9d950b3076442cb1d8f0b2a43c40c510ef031243b40c410e9030c439c0c290e303071f7850843a61258dbf8495aa563936ecdce4d262310ce987c425800200007ee4e4ba859114e001441941a9097ccb2c02bb2c70066cb10007aa5539a66dd8e480caa36c032e47010cb71b8c32cc6a88cad1952a0fc46ba83b11766dfc25bb4e701eed38c065843a000410f4e680ec6397906204502a7b0d86aadc34b2b350cd24c1c16b930505ac4c0c154130b04fe4c24137930104d64c3412992ff0498087800082213918e49c4eb45e71384e4fc4e0c623135ae5ec4d6393b134b1a844cc39f9132eb1fc3fd2c970f8eb34c3ca2c930f06b5443b0a84739a8a9dcd93aa6335f643dc57d043f15f31fac523bb43148d200c519483f143b1ffc50b48bd1410a0e0e378ed733a243ccccc90f5330c8760cb02e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeac32824c546091313180f7bbc5855cd316136adc578589b15d4088c45d0007106a000032ca9183f7621d4a97261c3b3873583dac7e21458b1dc4de3b3b073ee47c150952a326a4c4063810f5330c8760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328abdb4ca180008b8c8751311283e3f70767032c88752a5d6ad8a961cd50ff4b1f8d8221d832c087543fb152d07cc0000ece06598fd4ed0ad5b284739a8228010f000183127240dbf8ead36ee3a4011088b06a8002d4ec9000c513269947631a2621c467dc87599aa3b166548ecd85673b2e1594eca85643b221588ec785613b1a1580ecc9b9c21e6666487a99863b3e2beee698af6b56e2bc021f892a87482441b7e090f044622e80001d9c0876acd148c28394c38a954e69800721d666a8ecd859b3b321668ecb85993b2a1660ec885963b1e165487281b821e20628877818921da0620874818621ce061487181836e04251e1d3092c6dfc24ad52d06b354ac6cca2e309bc58ec1ed56390771723e0a7e3f10a2c8fbc284131188674c3e212dd9d83a16596015d963803319546d81d9b9a5c1972380865b8dc6196635446568ca9507e235d41d88bb36fe12dda7380f769c6032c7631cbc8310228010f000104426ead42383e650be0ecd44d838050b60dbc87b8afa76862919dad8a31772e2871dab8a151dae6744879999921ea66190ec19605d36653175999495d24652177799465d5e65157471944b9a62c26d5b8af0b1362ba811188ba000e20d5e0a834c000054b541ca61c5230000c43a930f0cb27eec21d9d9c39a412d0dbc1b2a8350229e0c408a0043c00041109b2c50b60dbd42c032a2a5864d4a95832876ae2855daa09fb4c7a08dc43a000410e627ddc9c898959221cfd41c1c6f43b06580a98995f2a46654174d994c5d66652577799465d5e65157b699435d58650443b993d044622e8000130f0cb2a460a97261c8ff87344d6890f33332438c0bb1d9d399043dc57d5cd315ec10fc49537dd124e000153d2ab65668a9d953108754c3810f4e6802644c3c7269d9b0a107236267941d88bb58e61dca3ef876f69c6032c7631cbc54ae24adb7f8183043c00041109bab21c46b6142f86c151361a5142d86855232199d52a1c973f706ba49871a128bce270a31189ad8bc6269a3508998592e1f1d669879459261e0d6a887610cb0000c32b9c6b900628ca41f8a1d8ffe285a45e8a0810e800104399ccd43ac31c541c1c6f262266d0989997e43b0658175999495dde651975799455d1c65117b6994310ee64f432d9938b9a62c26d5b8af0044623e400028462a5c10ed30e1fba399c6e7552b076f54a81cad53a1a1f8fbc28323fe09f776a827da3ee09f0,
  0x121e443b0fdd930f0cb210ececea61c36fe739c41f3fcd086c6570e42a6fc378899f0cf18cb533026584217995f085c656c21619590856655c2151955085232e400fa61f3558658c577d89b15d4fe3041bb2e4106c001c41a800036fe000d41da8995072987131e9ce60e9f20f05012cd11324ee5419cb979048a99f4de20cb533026584217995f085c656c21619590856655c21519550852fe3041ba63c39c9188432cc5e10c94aad448eaa75122cdd740b6b71d362043a8cfb90f302ae43b40aa36fc121ea950e2dc5c01308b1c0396c7dc13e8ecd418b952a001254bce7110f102fa438c0bb000200000014cc037dd124cacd4334a62b05b8990c157a67f0504e464113a63f37ea7ee8d74930e34247ee4333931104ae9bf4cf0392713ace4fc4e0b97b13591a844cc39f9132eb1fc3fd2c970f8eb34c3ca2d510ec312102c8952107bc547c1d5152706f654941b4951d06ca54b41a695290692546c1a1043a0004a460e70043f15f31fac523bb43148d200c5193b5b146320fc50ebb971438ed5c50ac8bd1410f054503a83839c210f4e6321d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeec3284ba30ca01533327d734c584dab71611626c5750007106a000032c9d9d4c3821d4e7289fb8ffa1cf9648999143b06581756194176aa0ca1c9c823600011780a95930f10ea98f0e721bc44c7808d865a80267270262d992083d59201cf933e02458ff827edcbc099259a01d3e2f0864a76aa0cb241e0a0254ea245a3108659556a0cf9b8e9b10772a693c879815721de0554876815476862919e0d8a3f782e288db7e090f76680c7152a1acc3f74681d0ec19605d3665317b9994b5ede651d77619425d586504fdb8bf23f6a2fc4fd98bf03f622fbcfd68bed3f562fb0fd48bebbdde2c2ae698b09b56e2c22c4d8aea000e20d5c8c8227000043c08710003261e9bf0fdc08750cb210ed30e152f39c4680dc8c8227261c68489888bfc3f7071fcfdd9c7e2a5c71bef778b0ab9a62c26d5b8af0044622961d285690000a0e0ece88750cb29870e708a108fbe1dc5d9b835f2a5c0024a959cd858e66cc930f884b0004000152b892c000a20ca1d3859d658e00cd962000f19546d8065c8e02196e37186598d51195a32a541d88bb36fe12dca9083de2a3e0ea8a93837b2a4a0da4a8e83652a520d24a8d834269c6032ca969cd71d8c72f1da18a4676b628c5dcb8a1c76ae2855e0a8a078310228021d0002043c00041109cdf087a731876b99d143b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650ca99993e087e2be6e698af8b1362ba811188ba000e20d4ecf856b874815a8000291810ea1964ecea61c50727380266c1e8116499f441f3fcd086a6568005195537f0a260d8099610894657c224995d089065642231957088a654c2218cb9007432dc01c8cab0066a164d96263d3558fdb842632c610969878e6d285b118f170c33bc1ab09dcd40c06d1b7e39b8d504d7d0ece35eaa95c4958ed3014a3b440520ecd0144dbfce6f34e0114843ac0f7800200010624e6c80053300dc2c4b2aa630de098ac16e2643055e99fc141263f37ea7ee8d74930e34249bf4cdd1fb90ddc4c4416f130505ac4c0c154130b04fe4c24137930104d64c34129c5cf13aee49c4eb393f1382e5ec4d6393b134ae7e44cbac7f0ff4b25c3e3acd30f28b24c3c1ad510ec254b4e6bc7eb148f200c519483f143b1ffc50b48bd14110ec83030ed5018e3b1c060043a000410f4e63284639188760cb02e9b3298baccca4aeef328cbabcca2af6d328610fc57cdcd315f03b6457a5ab715e0658c577d89b15d4088c45d35c1116e001c41a9d9f0ad70e902b500005072a46043a86593b3a98701109cdf02ae43c8cfbb6fc121ea950e2dc5c01308b1c0396c7dc13e8ecd418b952a326a54bce6ebb43148cf06c51fbc1714468760cb0153132be548cca82e9b3298bdccca5aeb33292bdbcca3aeef328cbabcca2af6d3286ba30ca03919044e43c40c510ef031243b40c410e303060000875130f3f7054b043a865908769871b7f9cde02ae43c8cfbb6fc121ea950e4f800021e043b887610e221d44c3cfdc3b427834f05832c843b4c3854bce6e87b58fc428b163b89bc8b8e1acdd9d83a354b6251db8181b721c467ddb7e090f21e6063152a1acc6dfe24b61d3059e2a5c736d41d08be4cfa20f9fe68435723e0a7da7100cf32b40028caa9bf84c466ea07671af532c21128caf844932ba1120cac844632ae1114ca98443727208d876980a51d9a028865c803a196e00e465580334c7a6ab1a7008a47edc2131963084b21d607bd30f1cda83127364a969cd71da26919b8589658b8619de1d9060636fa135c76a80c71d8e030021d00020004000021e9cc6508c7230db79af13f74681d0ec19605d246520fdb8bf23f6a2fc4fd98bf03f622fbcfd68bed3f562fb0fd48bebbdde2c2ae698af61db22bd2d5b8af032c62bbec4d8aea087e24c411188ba84d222e1ae088b7000e20d5c8c82270000a958002262a4c7c990948c1b7e54c4088541c9d9d3f70987098788750cb273704c92cd00e9f188432cc83c1404aad448f44050b06ee5419ca899364ca160d81152a326aa9d0325152d39af17804c5ac900e7c6df426b8ed5018e3b1c060043a,
  0x121c467dc8758b923b240030ece9ce5197200e865b8039195600cc32c00030cae65fe3fe09fb658c212ddaa83280004000131e9b4e000a660131583e44c860ec533f837e4c7e0db537e834b76862919dad8a31772e2871dab8a15782a281c43a00043b16654843989ef3b3e15acecd85673b321598ecb85653b2a1590ec885623b1e1584ec6856021e6055d53a9cf05d36653175999495dde651975799455eda650d75619415d186502e698b09b56e2c2043b8b05c2162c0c32d8affbdde2bfac4d8aea87482441b7e090f000e20d4fde863d8b8018f0a9983634c3c0d6dd9a83170000a954fdd952e0876ecdd30e152b39e2212d96380390004000065b1ba8000a660131583e44c860ec5311039f4cfe0df931f836d4c3c0d6d37e834b2a5464d0a969cef76862919dad8a31767428b1dcb8a1c76ae2855e0a8a0710e800104398a0c8fc61ed63ef877158ee26e1639899c0cac000c32c9cee8b8e1acd52d89476e0606ddbee01763b38003087119f73b16654a2e186773b2615c0ecf856b3b36159cecc85663b2e1594eca85643b221588ec785613b1a1580875816021e6055d52b9b9d43b06580a98995f5d36653175999495d24652177799465d5e651574719445eda650c43b8b05c2162c0c32d8affbdde2bfa1e209176e38245a1d209106df8243c00388353f7a18f62e0063c2a660d8c0002a553f7654b821dbb374c38a9d4e781cc7508e0f9948c834d76862919e0a8a075d3665317b69943000021d432b952e4c3854b4e7789985aa21d863500669917a281959a092689081645e0a034d523072301100001508e73b410f9bb250740d7544c033b26020a609868262261609849848260260a0978981825d25fe096ca961936723c26f1c8d09a058ec1ed563907712a560c5c1118af38fc428a23ef0a0c772827f5d9a09ef10e400109879cea10ea739541c1c6f43b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd865097461940b56e2c2043b8b05c2162c0ec4d8aea000e20d4a99836300011718eceb7dd8b847eeca97043b766e987032c9cee00104c4416f130705aee49c4eb2c7f0ff51fac522931332fc8760cb02e9b32984c54c9cbb4207cc0000980130c26144c20982130225fc54b4439930e0cb2a11ce769b9d54ac0d7d53a032c54a80c6c0003b3776aaecd421da61c2a5e73b0487aa540636dbf40ab90f2352c54b8638bb3413de875ce66931332fcba30ca05cd316136adc584589b15d4001c41a800010e610ed30e1fba39d624ad52b06776dfe060c87119f78b842681c8d826321d607bd30f9bbf6e16259465a1c8254c66bee3f58a458764181933e04cd76840f9931e1b2a508c23da0f408b2835022accad842369dc049daa09afa1d9c6bd5a8099cc7eda20cc76a80a61da6029476880a41d9a028800200000006739cdbc9b2969c022920c484b71d8e73a4dbf1ce80440000410f9bb250740d7544c033b50b00ca8a9600092a5e6a5941c056921e6055c876815487482441b7e090f54a818ee2e0098458e41dc5638072d2a360d4ca9583172a520c58a9383152a4a0c50a9083122a3e0c44a8e83100874000821f8af91db22bd01118af38fbc2831d9b0a0b772827f5daa09f68fb827c1d9a09ef10e4001043a9ce5087a732c76b99d143b06580a98995f2a46654174d994c5d1c651177619425d58650574619402a6664f843b993db9a62c26d5b8b08b1362ba800388357232089c000130f0cb2767530e1fbb39d46f0533e02454c7808d9cbc09927270262e31086598bc2192955a891d54ea2459bae816d6e3a6c4087519f721c605d9bee8926566a19a537e82558d422661cfc89975aa21d8530f04e3917a281a0c508c07828697141d19692a5864d9668074f59201cf8a9583172a5e6a59d9b0a0b907827fa3fe09f7766827be242059110e4001043a9ce543b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d77619425d586505746194010ee64f548c08b721e6055c876815469c6032dae000c000006dfc110b6fd3f764c3c32c843b3b3a98707639ce90cd2acd0e53c6a11330a11847bad510ec3065829b9b76001722f45031b710a106df42711b7b09c26de42701b7509bc6dcc26ebc1434b9063846e418a1180a46045bb4e701eed38c065b5c001803b18dae0ed13566a0f81d0a83a06baa26019da858065454b0c9b152b062e6e0457a822315e6ece8513bb361416ee504febb5413ececd04f78872000821d4e729b6f35e28760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca00877327b6adc584589b15d4001c41a8000044254b952a9fbb0cb2767530e1b7e39d019a63508998566824996a887616fb805d88711b10917a2819b8e091654e8192a242059152306995e0a1a5c1d8c67322f0098b6a0022ae0d484c2727208d931e9ce650740d7544c033b50b00ca8a96193659201cf8a9583172a5e6a59d9b0a0b772827f63fe09f776a827d9d9a09ef1da20290439000410ea73950ec19602a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd8650975619415d18650043b993d1dae2de6d5b8b08b1362ba9a7008a4000e20d60c484b70000000c110a839,
  0x12a5e73f0ece9ccb8748245021e00023b3e2bec87b8afa087e2be487a998643b06580a98995f2a46654174d994c5d66652577799465d5e65157b699435dd86509756194110ee64f6e698b09b56e2c22c4d8aea0876243c003883521d6054c871814f0000dbf130e1fbb0caea954e7e89f676aa0cb0439000454ea72a843a9c4921e66664875815321c6053db7e9cfb3b3a731152a1c205d58650443b993d000010f530e1fbb0cae54bce7e09d58b9c1bc1c9302de508c723153109666e1407bc110000121d472a88719a26043e688c763998d5074099542c023852326f6c988198a260e08c898782277234266dc9c0986723025fd639077159201cf9638072d54e80cb097f824c04462bce3ef0a0c8ff827dddaa09f68fb827c1cfc899658fe1fea350066910e4001159a1cfa3b3a731043a9c49507070896a89b7c8fd66ded0ec19605d1c651175619415d18650043b993db56e2c22c4d8aea54a82448003883521e6055c000152f087a9870fdd86576dfa73ec0658ec635ead38846034e01149062c271c189096e3b3c0938ecd024c6df8daeb4ef11ec32b400c8cb3002632ac00782200002087ccd1a84705bca0f8150a83a04caa260123a858047032e400fb2e4003acb1400a0cb43788987cde08cb733be4c40cc5392713ab173837826fd0b1e98f02ba12ff04b64c1c119130f044e99f0dcf1d9a32ea3b5482e8ed3202c3b447e8391e136ee4684cdb978131ae4e04c3391812fea9884b343c41236b1d83daac720ee2b3403a7ac900e7cb1c0396aab4067aa9d0196370a03dedc74d8810ea33ef1f8851447de141920f04ff3b9413fb1ff04fbbb5413ed1f704f810e302ec21c80021d9d398821d4e24a83838447664dce0ed915e8088c579c4851250df74493ac7f0ff410f0001043b39f2a950e1047eb36f63b5cce890f5330c8760cb01d8b32a4ba48ca42e8e3288bbb0ca12eac3282ba30ca00877327b6adc584589b15d410fc4950007106a43cc0ab90ed02a80001b7e952f4c387eec32bab3439f47140879815721e20558877815554ee6f19b7e090f76680c7152a1c20087e2be4a971cf8b9a62c26d5b8b08b1362ba8003883500009870fdd8657087673e419ca67d378832d4cc0bb94140520f43a79961085e657c217195b08586564215995708546554214acd1131cfe3041bc6210cb298f01943b5413f6aad448eb75d02da43a8cfbc7fd32fe438c0c1aa75373adbf8495aa560cef17084ce2c720ee243cc0abc7de1420dbf0487bb3739e2a950e2dc5c01300b1c0396800200000014cc047dc13e898ac1f22643076299fc1bf263f06da9bf41a5bb35062e54a8c9a952d39deed0c5233b5b1462ee5c50e3b57142af0545038874000821cce7ba1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca00877327a001c41a800008769870fdd86572a5c73e04c02c700e5b170431daa5539e0a9d0cbfbb3614171ff04fbc7dc13e08760cb02e8e3288bab0ca0ae8c32800000439952e0876987032b9fbb39ee27dc439000410ea73be3fe997f0cac000c32c9cf52a5864da2f0864a3b36159cecc85663b2e1594eca85643b221588ec785613b1a1580a959cf154ea73c0a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d75619415d18650043b8b05c2162c0c32d8affbdde2bfa1d209106df8243cfde863d8b8018f0a9983630000a954fdd843b766e54b930e1cf6378832d46c5a67c048a6dfc756b9781325188432c8ec6344c4388cfb90eb1724aad448f44050afa76480061d9d39d49bf412aa63c046c4c38e7a131104ae4bfc12639f9132eb5443b0c8bd140ca4601a63c1439e64c3411a930b04684c1c119130504624c0c1181301045ee4e04c5ac720ee2b3403a7ac900e7d1f78506483c13fd1ff04fb8872000821d4e790ed733a243d4cc321d832c0762cca92e8e3288bdb4ca1aeec3284bab0ca0dab7161021dc582e10b1606767c57ddcd315ed626c5752c70130610fc48e0007106aa9d4325953306c643cc0ab80002a5b1780ecd1d983b2c7650ec81d8e3b18dbf62e09fbb2a5c10edd9ba61c0cb273d432cc6201324aad448eb75d02dae5e4e3190ea36ea000098812fe26184c28983130426044c01639acd158e219648791fbb08764c38e7a06063b3866aa1d989656e1407bc87519f721c6060db7f092b54ac19de2e109a07236096c97f1ced261e09cc984826f7276269564987838ffe2851dab036f50b4231a0d504ef4c7c2155973004119686f0d33e04cd83d022c800200000006739931e1b266a826be876980a51da20291a7008a4831212dcdbf1caf54c66bee3f58a4558e41dc4dbe84d776840f9941f03a151300ced42c032a1daa031d4231c8c4dfa6881d9d0a278fbc2831dca09fd76a827da13488b86b8222ddd9a031a10e40010110000110ea73c810f9cbc507071bc763998d43b0658174d994c5d24652175799455d1c651177619425d58650443b8b05c2162c0ee698af7b56e2bc011188ba000e20d4a99836350740d7548c834d21ee056c87981570000f051d9b952e4c384c00986130a26084c08a9686593f76dbf4ec71d983b2c7640eca1d9a087673cc1a6a91839acf0545039d9d39cabdb4ca1800010ea54b4fdd952e4c381964e791bfd,
  0x17234266e310098e8bc0261dc9c09868b802601c8c097f58e41dc5668074f59201cf9638072d2a360d4ca9583172a520c58a9383152a4a0c50a9083122a3e0c44a8e83100878000821f8af904462bcdd9d0a278fbc2831d9b0a0b907827f9dca09fd8ff827dddaa09f68fb827c1d9a09ef10e4001043a9d02087673e50ec19602a62657ca9199505d24652174719445dd8650975619415d186500a99993e10ee64f6f778b0ab9a62c26d5b8b08b1362ba8003883500007eec32ba61c21c47410d7a8ec701963b340510ecf1f7ed38846034e01149062c271c189096e6df8dae8cad003232cc0098cab001e0880000822315e632e400fb2e4003acb1400a0cb43788987cde08cb733be087ccd18ed921dc3b5c8528ed520ba3b4c80b0ed11fa16adc584589b15d4001c41a90f502cedc740b000004c7a99f4ecd90eb507ea0ed44ca8595072767130e26fc3a06002cdbe84e236f213820c508c069c6032c763000636fe678cdb9851f36f613dcdb884f25130091c765810f1d920389cbc098d83de23a5aa388e883d62335aa188cc59a01d3d44f82c051360a1141d026590782809cbf89c772f626adc8d099b58e41dc631306d28c441a59dca83394cfa6f1065a99818fbc284155d0959556c24f620505e7880c16cccb0842f32be10b8cad842c32b210accab842a32aa10a5d9b835b4c3e6ab0ecb19aa7f1820dcecd85754c780ca1daa09fb3b2a15c63fe997f878a2468dbb853736ea14d876781271d9a049953a9d013b326e720cb88f769de23d959a86690440000410f9c8f8d422659cfc02575230731d42382de724e27562e71aa01daa417476990161da23f40ec88b913b1e2e4153109666e1407bc001000021d467dc00299804c560f9132183b14cfe0df931f836d4dfa0d2ca9500096df873f4a969cef507071b09881c6b54a8716c87999998b802601638072d21c673fe3ee1cfe2a5e73f0ece9cc858fe1fe966b87d859a61e516a887612a420f78a8f83aa2a4e0deca9283692a3a0d94a9483492a360d0821e0002087e2be4dc08af51db22bd01118af38fd6291dda18a46908628e5dad8a31907e2875dcb8a1c76ae285645e8a08782a281c21d9cf936de6bc476b99d121ea66190ec19602a62657ca9199505d366531779994a5d66652577799465d5e651574719445eda650d77619425d586504a99993eb9a62c26d5b8b0832c62bbec4d8aea000e20d4000261c3f76195c43a9d0200166dfc2719b7d09c46dec270c18a1180d38c0658ec6000c6dcc28a1b7909d66dc42738ecb02083b2406bc1af11c4d41c470c1ab118cd40c462a85f0562a16c13aa83a32e0e4fc4e0393b1348b1c83b8c5e60d871788343c7de1420a9e84a92a76126cb24039f43ca0bb30f182d29b770a6e6dd429b3b3706b63b3c0938ecd024c7650cd547fc13f7065c47bb4ef11ec987c4261d9b0ae8ed5419402200002087ce47a63d3788fdbccb3195b086a65542190cb5004ca460e63bfcc107ccc9041ea84705bc000800000053300e49c4ea9d970ae498ac1f22643076299fc1bf263f06da9bf41a5c5ce354054a8c9a8ed520ba3b4c80b0ed11fa0a9884b343c41236b1fc3fd2c970f8eb24c3c1b70a03dedc740b0152d39de43a8e55283838d84c40e35aa5438b66e0457a8ed915e8088c579c7eb148eed0c52348031464ed6c518bb9714391ffc50b3b57142af054503c5c01300b1c0396a67c3a00438ce7fc7dc39fc54bce7e1d9d39906dbcd788ed733a243d4cc321d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bab0ca09313180f734c584dab716117bbc57f196315df626c5750007106a7ef432645e00c960000ecc1d903b1c21d421ea61c3f76195d53a9d010cb2aad4dcf4620131cb3403a79d990ae6762c5c7483c14050f1048dbb950672dc740b0152a001254b4e7790ea3954a950e2dc5c01300b1c039690e339ff1f70e7f152f39f87674e64152107bc547c1d5152706f654941b4951d06ca54a41a4951b068410f0001043f15f2ed0c5233b5b1462ee5c50e3b57142af054503843b39f28760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2af6d3286bbb0ca11533327d734c584dab71611626c5750007106a000153a88754c387eec32ba67c3a0023cc10f0001508c731c11088b75232095dcfc89965aa21d85a7781236b8003007631a2604462bce45e8a088d4019a4ece9cc8262071aca979c4943b065817b69943b56e2c22c4d8aea5668249c00388356fb805d887981576df8053c0000875087a9870fdd865721c673fcc9a952b062e54b4e77bb3413e821d0002087313e054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1ae8c328021dcc9e80002a5c987032bc7dc39fc001c874816c21ce05ac872816a6eb8248955a06598c402639668074f90782809dca83394cfa6f1065a998132c210bccaf842e32b610b0cac842b32ae10a8caa84297f1820dc0010000000a660131583e44c860ec533f837e4c7e0db537e834b4c780ca0a9519352a5a73bdda18a4676b628c5dcb8a1c76ae2855e0a8a0776a827ec43a000421e22e908778b9d10e627de202857d21da0584ec9000c8ffa65fcec599526e3a246553a9ba321e66664ecd85673b321598ecb85653b2a1590ec885623b1e1584ec68560,
  0x1087e2be41118af376862919e0d8a3f900628c9e0b8a23907e28763ff8a16917a2821e0a8a07766827d23ee872d10e80010ece1d0c10e6741cfdd9d05262665f90ec19605d3665317b9994b5d6665257b799475dde651975799455d1c65117b699435dd8650975619415d18650043b993db9a62c26d5b8b08b1362ba9638897f000e20d4983822325fe087c00006574c38e460e88196632b62ccccaa8b307edc21419638038196872080021b4e32c62bbec4d8aea000e20d4000267d4c7a987130f9d0f099a99f4de0a63c364d07a04590ed10148d504dcab4ee11f0d38045241970a77062425ba62b05b86df8e57a8583604e49c4eac5ce0ddca0f8358a83a0cea6df426b8ed5018ea9d0e86a84639187ee0d74c2691170d70445ba61e04c60880000821f39784c38da28ec734caa260d139fab0cda4c0c12ec5c21338e4684cdac720ee27ed43571fb30d5a7ec43561fad0d547ea4354130d053c4c2c14e930905384c1414d130105311f7850845c61370e4784dbac760f6aa4642c8bb3734a29bf4d1647e2145912144932c7f0ff50e902b52a6307d0acd41a7843a0004a0e0e2d3b3b367610f4d2a13113368088c579c7eb148eed0c5233c1b147ef05c511bc15140eecd04fa087400087670e8608733a0e7eece82952e39fc8760cb02e9b3298bdccca5ae923290bdbcca3ae8e3288bdb4ca1ae8c328021dcc9edab7161010fc57cdcd315ef626c5750007106adf700bb10eb02c0dc700ae10f702b643cc0ab90f102ac43bc0aa90ed02a8dbf00a780008fb84c1897f06574c38438ce87073e8ff827ed64889878bc2192142c857743b065817561941878a2461daa832c00007ee5b8e9d9d087654bc43a865754e874343b8c7de1420b1cc4ce45c30ceaa0ece84bb3734a24388cfb90eb3354766c2b39d970aca76542b21d910ac4763c2b09d9937387ee063843a41220dbf0487aa54063654b4e85283838b4875462a3b3413e91f74396ab35069e10e8001043d3a0c54b8e359311336810fc57cbc15140eb1c44bf88740008e464e8588733a0e7eece8290f3333243d4cc321d832c0ba38ca22f6d3286ba30ca00877327b842c585deef1615734c584dab71611626c5750007106a000032ba61c3b38743039f47fc13f6b2444c33b550658e4e41191306368a4bfcd26aa75346a43b40c410e30306dbf8495aa5606beecd850847df0ee2b1cce8445c00c747ee0638152d3a14875462a043a000410f4e83283838ee54b8e359311336810fc57cbc15140e21d000208733a0e7eece8290f3333243d4cc321d832c0ba38ca22f6d3286bab0ca08877327b842c585dcd316136adc5845eef15fb626c5750007106a4c54116930f044e4c34113130b044a4c24112130504444c0c11080003b38195d30e39193a16734d59a834f52320d3552a031b76680c680001d9c0876a0e4a97bc144c3854b4e85000b36fe3ab4dbb8e8f3b240030ecd85673b2e1594eca85643b221588ec785613b1a15821d2091054a80c6dd9a09f48fba1cb4db8850858e225fe0c708dc507c1ac5c8c9d088b8c26e163b07b558e41dc63f10a2c8fbc28422e0063a3b321634dbe84e236f61384dbc84e036ea1378db984dd76760e8dd9b835f3f7031c152d894754ae24ae2428926831423010ea875d566a0d3ca96834d087400081100001087a7418a971c6b5070717498899b452306634dc08af504462bce45e8a08782a281c10f88bb69c6032c43a000410e6741cfdd9d0536de6bc5a739ab51d8c68990ec19605d24652174719445eda650d746194010ee64f47678f871d963c00ec58b84b56e2c20ecf8afb087e2be6e698af7b1362ba800388356e0606dc87a818e6dfe060dbee017621ee056c87981576df8053c00010e33b38195d30e283b3a126d61dca0a02907a1d3d53a032c76a827ee2e789d559a2263563f87fa8ffa1cf9c9302d7260c0020a971c6772f2718d64899c3262266d23f58a4725fe096c43a000410e6741cfdd9d0543b0658098999585d36653177619425d58650443b993d7234266cfdb86373f5a18c8fd586313f5218c098a822d261e089c9868226261608949848224260a088898182212602088000045c158e6195d30e39193a1025fd638072d7232089c9871b4b262266d23ee09f03f7674150ec19605d18650000006574c3821cce839d023f747314a979c49000010f487906574c3821d4e83099673f06f6d6a89ba0523069947631a268d4019a544c033b260e08c898782272a580024a979cfb3b3a732d41c1aa872702619c8c097f5668249d639077159201cf9638072d2a360d4ca9583172a520c58a9383152a4a0c50a9083122a3e0c44a8e83100878000821f8af98fbc2831d9b0a0b772827f63fe09f78fb827c1d9a09ef6fb805d9b7e014f10e400108711d0410ea740821d9cf943b06580a98995f2a46654174719445dd8650975619415d186500a99993e10ee64f6e698b09b56e2c22c4d8aea000e20d400006574c387eece82899673f06f6d6a89ba05230673a35019898908163d37e1d034c7815d133e1b9e3b3465d4ecc85733f722ff0ec58b8e8788246db8e8160044000048751caa043e6ec8988198a5568196553a064a3f5e190952a063b507c0e8541d035d51300ced42c032a25fe096c9838232261e089ca9600092a5e73f0ece9ccb50706aa22e1099c,
  0x159261e0e3ff8a1476ac0dc553b0936878c16a531f0855260e0b5c0020000724e2758001883d58fe1fe99730041664a009865a1bc48fd6291531e057476840fa133e1b9e54c4259a1e2091b4dfa163db8501ef6e3a05808751caa3b34724cfd79a0a3b16161887181763b3a730097f9c2f3b326e7224289286fba249d648073e58e01cb555a033d54a80c6c21e0002087673ad53a1a1f262266d1dca09fd8ff827dddaa09f68fb827c1d9a09ef10e4001032c00033f76746043a9d170cae744887a998643b0658174d994c5d5e651577619425d586505746194010ee64f432d993843aa31530858b0bbdde2c2ad5b8b08b9a62bdac4d8aea087e24a80038835000054bd30e2b343a3272a887581ef21c605d8ece9cbf50707071b8589666fba249d53a032c54a80c6c21e0002087673b159a9c1854c6705821f8af9766c282ddaa09f6766827bc43900040cb0000c43a9d170cae741574719445d586505746194010ee64f432d9938b9a62c26d5b8b08b1362ba80038835000054bd30e1fbb3a3031bcecd859b2a560d6e1d3092c766c0d8152b1c994c3e212c0010000000a20c996380336588003c6551b601972380865b8dc6196635446568ca936fe12dc7631cbc8310228010f000154aa734d41d9ca104426ead42f82b151360a1142d82755232095c21d0002508e735021e9b4621e66665c9f89c172f626b1c9d89a573f2265d64b87c759a61e5164987835aa21d8553183e8566a0d3cece9ce53f6e2fec21f8af904462bce3f58a477686291a4018a3276b628c641f8a1d772e28723ff8a1676ae285645e8a08782a281c32c0003507074589879d152620745032b9d121dae67450ec19605d36653175999495dde651975799455eda650c32d993843a6314f0858b0bbdde2c2ae698b09b56e2c22c4d8aea000e20d4000152f4c3821d4e8b99f721d666a9b7e090f3b36159cecc85663b2e1594eca85643b221588ec7856108740008ece9c7f874871e88719c70087a707d52a1acc3f7466d0fdc8bfc087e2be5c8c82290cb0000c9881d140cae74488799c9d0cb664e2f778b0ab9a62c26d5b8af00446229400008752a5e987141c1d1633ee43accd536fc121e766c2b39d990acc765c2b29d950ac876442b11d8f0ac210e800110f3393a7674e3fc3a438fc438ce38043d383ea950d661fba33687ee45fe043f15f2a0e4115065800064c40e8a06573a20196cc9c5eef1615734c584dab71611626c5750007106ae464113800010ea54bd30e130f3a2a31c0a969d0a3f72725541c1c7021c467dc87599aa3b36159cecb85653b2a1590ec885623b1e15861d209106df8243cecc9b9c54a86b3021d00023f74744d4239cd4087a6d18879999954c60fa159a834f7232089cece9ce5261c684821f8af98fd6291dda18a4676b628c5dcb8a1c76ae2855e0a8a070cb0000c32b9d1221ea661974d994c5d66652577799465d5e65157b699430cb664e10ea8c54c2162c2ef778b0ab9a62c26d5b8b08b1362ba80038835000021d4a97a61c2620745000186573a201964e4b1fb835d2a0e0d02065b3270e4641138000261ea118a97a61c3f74744c005195d08d8655c2153f7210d8fe3041db2cb00b0cb9400c8cac000a32bc01ab2c610a0fdbccb3195537f032d4ddf9959091c6584220995f086e656c2119953083e32c403f0cb9006232cc0098cab001efdec443b2d3110d013442433a5108eff34420bf6d1066cb14419262b0dd899f4de08004369c32dccefc5cf13aa9888357a61e0ce6e49816ba63c36947ed8d9c930633147ed43391fb30ce27ec43381fad0cdc7eac3369fb90c744bfc12dc5c13a1117184dc45c21338e4684cdac760f6ab1c83b8a6fd34571f8851647de1420a4642c8bb3b0746ecdc1afbb340638a96c4a3aa57125712144932a541222766c2b3b703036edbfc0c1b7dc02ecdbf00a790e23a22b1fc3fd43a40ad4acd41a7843a000410f4e62283838ee54b8e359311336810fc57cc7eb148eed5c50abc15140e4c3c113930d044c4c2c112930904484c141111303044221d000239183a207670e8608733a0e7eece82a1d832c0ba6cca62e923290babcca2ae8e3288bdb4ca18877327b734c584dab71610658c5778cbb15dd626c5750007106a000130e06573a240cb1daa09fb54ea245a3fe873e6e3a6c416488986727208c89831b4521e66d108769b3825fe6a4898899b443b06581756194100004c38986130a26104c10981043b2a5e21d4fdd0657b9a44388e8889ab8c441a51cbd028251346f9933f085d50be1b0542d86857f9c116ccaf19818bce27022f189a432c210e1c9f02af727409cd32108714c7c2155fe6084200080000cad8b3332b22cc8cab8b3132aa2cc0001883d65d401959730041664a009865a1bc44dfa0955cfc89968d40199d48c1c8c0440000410f9bb2507416761d3092c54ac0d7dd9b0a108fbe1dc5639899b7236098d30f9d0f5130195d33e02454c7808d8fdc1ae9261c65edc9c098659201cf898682448ff827ee310098e72f02635668074f508e1819daa832c9078280a1d9896554ea245955a833e6e1407bdb8e9b10772a693c87519f721e6055c878815621de0554876815450707161b7e090f592e1f1d669879459261e0d6a8876154c60fa159a834f54a80c6c21d000221c6743821e9cc42a5c71ac98899b4,
  0x13b166548ecf8afb21ee2be821f8af91db22bd01118af37674289dd9b0a0b772827f5daa09f6766827bc32c000308767490a979d180cae741076b99d121e6666487a998643b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d18650032d9938b9a62c26d5b8b08b1362ba8003883500004c3887108733b387eed30e28473a4a66a8ecd8fbf21d4001cecc859a3b2e1664eca85983b221658ec7859521ca06e0878818a21de0624876818821d2061887381851d9c6bd5b810947874c24b1b7f092b54b41acd52b06771da6029476880a41d9a028a2e309bc8b842681a7008a4831212ddc8f82977236096c76a80c725fc73b4dbf1caf508c7230763998d6b8222dc11000015232748c8719d22043e6ec941f03a150740d7544c033b50b00ca89878227261a089898582252612089098282222606088498082202a5864d9c8c098458ec1ed5639077158e01cb62e0863b2a560c5d52a9cf621ee2be876c8af404462bce3f10a287674289e3ef0a0c766c282ddca09fd76a827da3ee09f0766827bc32c00030cae73dd41c1aa62a5e6a58879999921ea66190ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d77619425d58650574619400cb664e2e698b09b56e2c22c4d8aea000e20d400008733b387eed30e043b3a4805b88761b106eb82475b8e09165568196553a064a8c40264a2f0098b72f20905c9c8232260c6f6dcfc89975aa21d85668074f59201cfa45e8a06907827fa3fe09f743b065817b699435dd86509756194178280d3400010e2261ce46421d952d10e643c8fdd86595232748c0061d9b1d6276647581d971d5e76547571d911d58763c7559d8d1d546df8e5102200002a11ce56821f1176a0e81ae952c326c54ac18b822315e6ecd8505bb3413de764c2b1b4e301961960001865739ee7ee8e75a838354c54bcd4b0ec6344c43d4cc3153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c3280196cc9c1d8b17096adc5841d9f15f7734c57b589b15d410fc48ac3a51222001c41a90f302aedbf00a78000261ca95021d88733b3898708719d22399a21c8002043a000421d4e72843d39968758638865800067670e8f952f3a3a195ce89131332fc21dcc9e865b327010fc57cdcd315ee43dc0adb6fc029e0000871a61c3f747480e6a3b43148d1fac3fb88740008a118e670873399a8758638aa6312c61960001843a000410f4e8f152f3a3a195ce860ec6344c4c4ccbf2e9b329821dcc9e865b32716adc584043f15f3734c57bd89b15d4001c41ab70b03d6df700bb10f702b6dbf00a780003f74438d30e1d9c3a3e64d8a9583172a5a6971d9b0a0b782a2819d9a09ef91781d7c439000410ea73150eb0c712a5e7474989997e2a62657ca9199505d36653175999495dde651975799455d1c65117b699435d18650043b993db9a62bdd59a092721ee06080000ec73f74df7530e043d3a3c158cec91c72874a71c4ec685c8261a094cece9cc025fe70bd37e9a9a8d422661cfc8997875425321d309305aa21d85668074f59201cf9638072d54b40e8d52b035f2a5a0c6421e000208766a5898899b43b162e1021f8af97674289dd9b0a0b917a281a41e09fe8ff827de3ee09f0766827bde0a034f6e0606ddb7f818321e6055db7e014f10e4001032c0003507274708711d1a56687464fdd9d1810ea745c32b9d1243b0658174919485d1c65117b699435dd8650975619415d18650043b993d0cb664e2e698b09b56e2c22c4d8aea000e20d4000261c2a5e7474cb0a6220b9e7668e4239181308a0f81d0c5c136dc7ebcd05152c18e076342e41d990b34765c2cc9d950b3076442cb1d8f0b2a7674e5f92ff385f0ea84a643a61260b24039f2c700e5aa9681d1aa5606be54ac18b843c000410ecd4b1311336810fc57cbb3a144eecd8505c7fc13ef1f704f83b3413dedc0c0dbb6ff030643cc0abb6fc029e21c8002065800067ee4e8d90e23a347eece8c08753a2e195ce8910f5330c8760cb02e923290ba38ca22eac3282ba30ca00877327a196cc9c21d518a9842c585deef1615734c584dab71611626c5750007106a0000a97a61c50727470000821f11e6088445834ef0246d50005aa89934ca3b18d1329190cce7674e45c6a11330b5443b0843c0004a118e4a843b352c10fc57c822315e722f45033c14069e43cc0abb6fc029e21c8002065800064388e8d2b343a3221d4e8a06573a248760cb02f6d328621dcc9e931117f9734c584dab71610196c57fdeef15fd626c5750007106a7ef431ec5c00c74000141c952f4c387ee4e8d8255261c72ad4231c9450706a30fdc19ea4df81638ecd19753b3215ccec58b8e890824a61e2091b6fba05e9b8e816021da0551b7e015321d472a887999993b3a7301cfc89975aa21d8555a033d54a80c6c21e0002087673ad53a1a1f262266d021f8af9917a2819dca09fd8ff827dddaa09f6766827bde0a034f10e4001032c000356687464fdd9d1810ea745c32b9d1243b065817b699435dd8650975619415d18650043b993d0cb664e2e698b09b56e2c22c4d8aea000e20d4000152f4c384388e8d1c94507071d4fdc0c708b802610a9683e5508e72adc8c998a261e09cdc9d89a5,
  0x18ff827dddaa09f6766827bcdb79af11dae67450ec19605d36653174919485d1c65117b699435dd8650975619415d18650087b8bc321ea2ee6d5b8b1ab9a62c5ec4d8b0f21da05840001b7e0442766db8e08732a5a4c3898806593f7610f487910e221d474cc000000510b8000c425a67f09f4cc98025b2c7007232d8dd441eb119a990c28da89b0700ee5c50dc1af11c520f83ca263f09dea17c1d9bb5b1460b3484d641ab118d20083e3a85b06dee5e813f930a38c6ed5c50a2c961384e5e04c945e60d87188432cc7fe364ea9e84a92a76126caad449143ca0bb30f182d2c4050afc76500061d973a567664dce2b350cd29888287a61e09c64c4412b930d04a64bfc12646a11330e7e44cbc18e11b906284602d510ec2d38c0658ec635ead39cd5ac8bd140cf0501a68ecf024e3b340510ecb0142a460e46262b36bcd3bc47b34e01149062425b822000026df8e51021f3346a0f81d0a83a06baa160195152c326ca9504892cd00e9e54ac18b843c0004a0e0d530ed520ba3b4c80b0ed11fa0764c5c91d911722763c5c81d8d171e762c5c71d9f15f610fc57c8ed915e8ece8513bb36141720f04ff3b5413ececd04f7822311f2dd740b6b71d02c0dbf00a98658000643a8e9528473a4a10ece92152f3a30195ce820ed733a243d4cc321d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c3280196cc9c5cd316136adc584589b15d4001c41a8000261c43884399d9c3f769870ecd1d2c0000001442e00031096cc98025b2c7007232d8dd426430a3698fc277c1af11c506ac463285f0766a16c1b7bb5b1460ed5c50a48020f8f1ff83c1ac961382b2484d2a67f09f4e4f8155b93a04de4c2000441eb119aa26c1c0130b04684c1c119130504624c0c1181301045eee5c50db938131720f83ca2c900e7d1ff04fbacd2135b188834b45e10c948760cb02eb33292bbbcca32eaf328abab0ca0931518244c4c603deef1615734c57b2ab6127a10fc48e2a75123710182d9c3c50ae40001b8e261f4c464c4098612fe4c546dfc987043d044254b44399fbb0cb20018ecb9d2b0000001442e0003109699fc27d33260096cb1c01c8cb6375107ac466a6430a36a26c1c03b97143706bc471483e0f2898fc277a85f0766ed6c5182cd2135b06ac46348020f8f188834b285b06deed5c50a2c961384aad849ec5e60d8710182d99d9600191ff8d939d951730763c5caaa7a12a2a9d849ab7220392dc780ca90ec3a527644e942ab40cb2a9d03254620132517804c5b9790482e4e411913063314e4604c245c138b6a95448a43a53a4e764ce931d990b1a43c40bec4851250df74493ab350cd29888287a61e09c64c4412b92ff04987634ccbc6a11330e7e44cbc18e11b906284602d510ec2d38c0658ec635ead39cd5ac8bd140cf0501a68ecf024e3b540530ed3014a3b440520ecd01443b2c050a918391898acdaf34ef11ecd3804524189096e08800009b7e3944087cdd9283e0742a0e81aea898067654b0c9b2cd00e9eb24039f2c700e5a54ac18b843c0004a0e0d531d8b32a4767c57d843f15f23b6457a3b3a144eecd8505c83c13fcee504fec7fc13ef1f704f83b3413de088c47c86580006a11ce92843b3a4854bce8c06573a08dbf4cfb90f333328760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca0065b3271734c584dab71611626c5750007106a0000875261c261c4388ece1d9a3f7621cce95000721d205b0873816b21de2e79bae0922880a15f8eca000c3b2e15c8ec7856e21ca0645b8f9b198788246cec5855f3b2274a21d29d276e3a6c40879999921ea6618ecf8afb21ee2be800010ec54ea7630ece1d983b34764ae69043d556a438887510f03a526c408768b966e38246e1e2856f00007646e69043d54ea43c88711d2832a4762800610f33332767c2b59d990acc765c2b29d950ac876442b11d8f0ac276342b000003b247668ece43a53a4e001c874816c21ce05ac872816a6eb8248955a06598c402649cbc9c63261608d1c9c098b8bc2192832c00030cae73f553a9caa6dfa67dc32d993821ea2ed48798bac21de2e748768b9721ee2beae698af854a8244e202857d3b3e15ae1d205630000764d30e1d9c59224c3898812fe59a27eec21e90e221d443c0e930ba73b30003087800073b2e16cc87781a3880e24f5baf893c556e1a5a31189ad59a61e50ec785d6907e286e1e5895254f61b0cecd85a93b2a1694ec685a1772c0e0087681958bce270a1e389366e3e24d544d08cd592e1f1e0f504fa54ee6c9e4018a308ffe285133f085d7f9c116ddad03b376ac0dbccaf198150bc238942d08c6835c146e0d504ef32c210e0cac8b3232ae2cc4caa8b304c8421c531f08557f982108cad842365d401959730041664a009865a1c827eda20cd33e04cd000800000019ce64c786ca88738f8921ca3e220f408b2835022adaa09afa1d9c6bd5a8099cc3b2617fcec885fe21d607bc87481ee1daa029876980a51da2029076680a236f26ca61d989676e162599a7008a4831212dc110000136fc72bc7639cad043e6ec95319afb8fd62915da103e6507c0e8541d035d51300ced42c032a2a5864d8a9583170878000941c1aa6,
  0x10cb210f4fdd9d4737c832e0dc10000196c987537e261f32a898f533e80053a8c2611c8c8227261c72a62e09c5b54aa24521d285674c3a7511b7e99f721d607bdb85896621c605d95319afb8fd62915bee8927566a19a5da103e68d42266142308f75aa21d860cb053736ec002c0010000917a2818002884736e21420dbe84e236f61384dbc84e036ea1378db984dd674800a86551b5d7828697065c8e02196e37186568ca9831c23720c508c0523022dda7380f769c6032dae000c0044000046599b8d043e6d7c7631b5c1da26accdbf9d4258e01cb541f03a150740d7544c033b50b00ca941c03194dfa74dcdc08af504462bcc0038aed7674289dd9b0a0b772827f5daa09f68fb827c1d9a09ef36de6bc476b99d143b0658174d994c5d24652174719445eda650d77619425d586505746194021e62ec2d5b8b1ab9a62c5ec4d8b0f00007eeca971d9b10e6196421e952d3a8a192a2f0098b54ea246dc9c8236261c74cdb8e9b1021c605d88769d436fba249d59a86692622095c97f824c8d422661cfc89975aa21d8645e8a067828697148c08b76b80030011000011d8c6d7010f9b2d1da26acd639077159a01d3d648073e874e166e1e28574507c0e8541d035d51300ced42c032a4c3e6b9931e99da04462bcdd9d0a278fbc2831d9b0a0b907827f9dca09fd8ff827dddaa09f6880a1604caa84201972005865a8014196200486578011195a004133e9a68196e68610ec19605d24652174719445eda650d77619425d5865048798bb0b56e2c6ac4d8b0fb9a62be1fb60830658820bcecf856b874815a000010ea00066df8a969fbb3b3621cc32c843d4c3a7510e31930b04c24c3c122b91a1340e5e04c945c30cef188432caa571260aad449136ff0310dd740b70000880899f21d3131025fc7eed639acd10cb210f48769d4334463b1ccc6a919116b09a426c021e00029bf4e9b822315e60884ea0dab716340000dbf952d5132a0fcfdd952e3b3621cc32c843d5072a16541d9d4210910130220996000140010000195f1676657459d195b1672656459c1957166e655459b1953166a000c425b2c7007232d8dd426220a1f063846e34e701ee3b18e9da61d38369878e9d26fd3a6e088c579996315de001c42c263f3a80990ce9f262b3a6b6adc58d5cd3162f626c58680000442a0ed41ca89950b2a0fcfdd9b7f2a5a766ca97043d10e61964ea08a1476ac0dbe3ff1b275d5e6516e698af854ec24d942d08c63b3e16b21e305a9835413bc000263f36fe766c110843d2a5a1964a9708733a801f1e4018a30592c270a2f306c376b40ecd0ec19605d66652553d095250bc238a1e505dd835c146c000264336fe766c110843d2a5a7eec43986593a7c0028cae846c32ae10a9fb9086c7f1820ed965805865ca00646560005195e00d596308507ede6598caa9bf8196a6efccac848e32c21104caf843732b6108cca9841f196201f865c80311966004c655800f7ef6221d9698886809a21219d288477f9a2105fb68833658a20c930e9b9900086d3865b99df32c62bbc65d8aeeb1362ba8000267c4c46987d31526fc000c98f4e9e08b283d2133533e9bc14c786c99aa09afa36fa135c76a80a61da6029476880a469c0229213484d8831212dc000261c4c3e0884dbfa89950b2a0e537e5ab61d8c74ece552a5438b717004c23919044e4c38e92952f3a3043ace81a84639129874e9ca67c099aa9d048d2919117307a04592c700e5b0f102bab5c13a7098f0d93354135f4438cd1347dc13e06df426b8ed501a43b4c0688ed101a03b1c065a1d832c0ba30ca05ab71611626c57534e21180001c4251d9d0b3d0e9c2cdc18b09c709a426c00004c3c6dfd31502215132a0e542ca83b507e766d37e0873087a7eec32c9d3a00000014e9b000334d0000130ea67d4c549bf00031d39000c3b5cce88ed901943b4c0630ed1018a3b3c0620ecd01863b2c0610ec90182000076a0ec66b8274e050348bc0ec2f050d103b361416ee504febb5413ececd04f7ad5013311a80334a1d832c0ba38ca22f6d3286bbb0ca12eac3282ba30ca02b34125112102c780004dfa766c111152e087a21ccfdd86593a6e6850caa99d94c3e706c65b9a1819762bbac4d8aea000e212800000054c3a98a937e1d36148aed081f347ea35f6ba6cca62a6212cea11847bc3b20c09065829e00004c566dfcecd8221087a54b6e6906592a5c21cce9a800721de0624873816b21ca05a9b7f09306eb8248952b0677556819662e109a08c402649c8d8260261073b5cbc9c63261608d09818230260208bdc9c098b8bc2192953a891b874e166e2028581878a15d087481ee4cfa69a131e99da32aa6765b8589664c3e212c98282d6000400015319aa08b9e275dc9389d6000a211d63f87fa4dfa163ca97834e21e205f63f58a45890a24a1bee8927566a19a5da103e6261a094c97f824c4c3872b6350899873f2265d42308f75aa21d860cb053736ec002e45e8a0636e21420dbe84e236f61384dbc84e036ea1378db984dd658e00cd9d2002a19546d75e0a1a5c1972380865b8dc6195a32a60c708dc83142301a7380f769c6032c6599b8d1d8c6d707689ab358e41dc5668074f59201cf941f03a150740d7544c033b50b00ca941c031937022bd41118af3000e2bb5d9d0a278fbc2831d9b0a0b907827f9dca09fd,
  0x107d00010000000334d032dcd0c2a6212ceb1d83daac720ee2b3403a7ac900e7cb1c0396c3b20c0898a8e9ca61c3a3aa9d0d0f822315e71f8851447de141920f04ff47fc13eeed504fb47dc13e054b8eaa261e3aa64c44cda131332fc8760cb02e9b3298bbccca52e923290bbbcca32eaf328aba38ca22eec3284bab0ca0ae8c32804c54c9c865b327043cc5d85ab71611734c57c196315de32ec577589b15d4001c4251d9f0b0b10102c100003f7421cd37e1d9b087a99f4eab88cd83d413e8110000136fc6e3410f9b2d507c1ac541d067550b019222e309bc8b8426822f0098b0446233dc8f829e72360989c9c82350000a26944c9fb90cb299fc659a63c58eeb1cd648d89a261a755839f47fc13eeb2444c33939046c4c38da5a1d832c0bab0ca080004c784c4043986573aaa6f9065c1b8200086d38caa9a0d4c440a7d31e02364cf86e4c98719c3723c26ddc9c0986723025fc32b00030cb2753465b9a1850740d7542c032a50700c6530e1d4c2a5864d963b07b558e41dc555a074d59201cf9638072d54a81caca959d4854e8687d0eb0c718fc428a23ef0a0c766c282e41e09fe8ff827dddaa09f68fb827c1d9a09ef4c3c754c98899b4262665f90ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d77619425d58650574619400cb664e2e698b09b56e2c22c4d8aea000e21280001fba10e69bf0ecd843d2a5c755048dc3c50ae8dc740b0263d3a0643a8cfba67c33cedbf048a2a560edeaad03a6aa540e56438ce8faa74343e8758638a83e0742a26019da85806547eecea2a83a3934a0e0d53152c326c54ac18b8658000654bce8e86573a0e7674e65bb3a144f1f785063b36141720f04ff3b9413fb1ff04fbbb5413ed1f704f83b3413df0e942b3a61d3aa44c4ccbf153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca0065b327043cc5d85cd316136adc584589b15d4001c425000010e69bf0ecd843d4c3c754c00186593a8a54b0c9b0657130f1784325152f0658a9d448db71d362043b40c410e30306dbf84982c900e7d0f142ba152b0650a958ea89fba3aa099f4d34263d33b51f785063b36141720f04ff3b9413fb1ff04fbbb5413ec000800000053a9c6554ceca1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca0065b327043cc5d85cd315f032ec577589b15d4001c42543a70b36767c2b5c3a40ad0000130f08734df8766c21ea61d3aa4000c32c9d452a5864d832b899c58e41dc4a97835f2a560d6e3ef0a0c766c282d30f859c43b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d74619400cb664e21d3892f8b8619dc0001fbb10e6766c21eaa563aa2060c8711b1b6dfc24c152b035f55680cf4a970c7143ae753d53a1a1f262665fae698b09b56e2c22c4d8aea000e20f0000263c4cf90e9a3efbb37907aee563febb553b3610f4fdd1d5003064388d8db6fe1260a9583b7aab40e9a000153aa63c4cf90e9a3efc83d3b3610f50eb9d4f1068cb140093f6d389832c0cee995b088e654c21d0cb3006e32b401a0cb9006232ac0150cb73430fdbc427b2c7109d013442433a5108e000130ea61e4df832e80029d4e0002087cea582213a6b09a426c1b7e3a9298a8e0d8cb7343054b0c9b022315e69870ea626fd3a9454acea421d618e36adc5841fbb3a8e4c4ccbf153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c3281626c587dcd315f0767c2cfc3a60b38000141da8595072aad552aaa752a5c766c4398659087a987cea6891b878a15d131e9bc14cf86e79b8e9b1021d467dcecc858d21da05508719d1f3b3a732cec5995221e62ec021f8af9b9a62be1b7e09143b3e167e1d3059c890a163a1d285670000987d37e2ab554aaa9d4fdd1d9b087a9870ea61a231d8e663548c88b5000109a141da8595072087cea588ba0444688148c997c766c282de0a8a06772827f5daa09f6766827be45e075f5d1c65117b699435dd8650975619415d18650159a09288908163c00021d72a5c766c439843d4dfa75282c7c48512509bf0423ab350ebe001000048bd140c000c425b2c70066ce900150caa36baf050d2e0cb91c0432b46548cb3371a3b18dae0ed13566a0f81d0a83a06baa26019da8580654088c579800715daece8513bb361416ee504febb5413ec3b5cce8ae923290ba38ca22f6d3286bbb0ca12eac32836adc58d589b161e000130f8cb62a5a875cecd8873087a6df8ea4875f917a281959a09288908163de0a034b4df875180021b4e32aa683465b99df4c440e7d30f035b4cf80ce531e03284c380c5c0038aed7674289dd9b0a0b772827f5daa09f6766827bd74919485d1c65117b699435dd8650975619415d186502c4d8b0f0000875cecd8873087a54acea41d464dfa74dc0021b4e32aa683465b99df04462bcd311039f4c3c0d6d33e03394c780ca130e03172a5464dad5b8b08000e2bb5d9d0a27766c282ddca09fd76a827d9d9a09ef2a5a7514a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d186502c4d8b0f000054b8ecd8873,
  0x1890a24a130e1d18566a70615319c162a5c751c0001d9b10e610f432c9fbb3ac4229d42c0648043c00062f0098b044222dd48c866783521309c9c822f26000020dbf1beb8d4226616a88761261e0b7098382d7197200c46558018917a2819c9389d6674a211d972883958fe1fe9e0a034f6b800300002000000066e887631a2632aa6835311195e8fd6291559a092776840fa1b8181b76fb805d88711b1b54c4259e1d90604261a0988985826126120980982825e2606097533e9d574c54706dc8d09a08b8619d537e9d603f7031c0ece859d4c3c166e1d309306dfe757d41c1c4e196e6861b8e091b58e41dc5648073e54ac0d7ca96835d55680cf552a031b2a3e0c4541d9d5c4c38747497f9c2f54e8687d0ea8c5443a231490e78c51439a31410e58c4f439231390e38c4d438a31310e18c4b04462bce3f10a287674289e3ef0a0c766c282ddca09fd8ff827dddaa09f6766827bca971d5d262266d0989997e43b0658174d994c5d24652174719445eda650d77619425d5865057461940262a64e487a8bb921e62ec30858b0bbdde2c2ae698b09b56e2c22c4d8aea000e20f21e2857400001964ecd843d10e698f0fdd1d613abc4c3c12a930d04a71a844cc39f9132eb1c83b8ad510ec2b3403a7952d06bb1f785063b36141722f4503483c13fcf0501a7a1d832c0ba38ca22f6d3286bbb0ca121d518a9842c585deef1615734c57bab34125112102c790f702d00000ece283a25fca0e4a97b71d3f741964ecd843d10e76ad937e9d60362043b40c410e303060001b7f90f26e3a757ce481b7f09b26ddc264c269116d07a045741881140a26032bb5c0018008780008ec6344c0884cd20ed520b23b4c8090ed11f983b3c7c38ecd1e863b2c780462013244388003b97938c643b4d9c130b04c24c24130130504bc4c0c12eb91a1341170c33aa9190cce7ee06380ed733a24c44cda10f3333243d4cc30223118243dc0b410f102c643bc0b110eb02c043a40af90e702bc43940ae8000261c4c3235026fd2a58a0e897f283943a8dc74fdd065958e6b346d5b1d9c3abc75290eb0c714df87550989997e000054bae691fba3b3621cc21e9d5d00000014ead000337446554d06a6220b9e98782cdc3aa12990e984983703036edbfc0c190e2000e43b4eadc6a11330e7e44cbad510ec243c40b190ef02c443ac0b010e902be439c0af10e502bb22f4503371c1236a9681d1aa5606bef0501a7a838389ca9d0d0f8cb73430ece8513bb3614171ff04fbbb5413ecacd04942a54122712102c7c3a40ad09bf0eac261c3a3a4bfce17a1d832c0ba48ca42e8e3288bdb4ca1aeac328243dc5e190f5177243cc5d85cd316136adc584589b15d4001c41e43c50ae80000a97a63c3b3610f4439a83b0cb27ee8eae000104426cb010f9a2350b019222f0098b727208d09851b381d8e663542d86855232199c984826f3f706840fd79a0a8bc62699c9d89a58b802611649878359201cf9638072d7232662898392c3260a4b0898192c104462bce3ff8a148ff827de3ee09f076ac0dc498899b443b06580989995b5d5e651575619415d186502d5b8b08b9a62bdec4d8aea54ec24d4003883c3f6e19949878255261a094c97f824c6e3c065487b81686e38058400010ed087a54bc439b9f83f749bf63500659507698f141c9d5b344c3b1ccc6a9190cce7674302a847371e7ee0d0845c01308e464cc5130705af173c4ebb92713acb1fc3fd47eb148aed081f42a6212ce7edc332c3b20c084c3c12aa62a36a47ebcd0546a11330e7e44cbc3aa1298b5443b0ac900e7ca9681d18cb73430ece8513c8bd140d1ff04fbac700e5b0e902b43c14069e9870e8ec7dc34a84c44cda21d832c0ba6cca62e923290bdb4ca1aeac3282acd0493b703036edf700bb000021c6987c0029d9b087a54bc43992fe0cb27ee937ea83bb56c7568333a918331a7ee0638152d07caa11cdc80ec6344ce464cc546a11330b5443b0930f05b84c1c16b9d9d371522f4503392713acb1fc3fd3c14069f1fac522ab34124eed081f437dc02ec4388d8daa6212ceb1c0396c3b20c08aad019e952b065098a8e0daa74343eee504fec7fc13eeed504fb47dc13e099f4eaba61e3aa49870e8e92ff385e4c44cda21d832c0ba6cca62f6d3286bbb0ca12eac3282ba30ca021d518a8874c62990f5177243cc5d8610b16177bbc5855cd316136adc584589b15d4001c41e00004df898f0ecd952f10e610f541d86593f7475600008221119a087c45dc1ea09f4d38c0659b7e37d63b18d1310e2362043b40cab71f126aa9dc1b8bb5714291ff83c1a83a0ceab2484d2c5c21340e4e8137b91b04c04c20004130d3aaca26032bc6201324e5e4e31a89b0d284c0c15b930b04fe4c0413d397f1391188c4d6b97b1358b35c3ec2cd30f29210c51bc83f1436ee681e33b960704aae84acaab6127b10282f544060b6c9a0843ca67e10baff4823fbfce08b66578d739959165a655c5960cb2000a32b4dc19d9d0c0a656ce16a847371e7ee0d0845c0130832bc01ab2c63858e464cc51fb70dd87ebc373995d085a4c3c16e130705ae4c1416b0cb5003a4bfce17c5cf13aee49c4eb371c1236fe3441d32e510730f142ba06580006195ceaaa63d3a8c32c4e15995537f0b1fc3fd1961088232e40188cab00551fac522c04d1090ce94423bb42,
  0x13b0e8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9e865b3270000155a2a7421c410ed33e291921e454b8ec41a122622095c987824573f2265dcbc09920cb0000c32b898e8c421964fdd0c7159a01d3d0eb874d90782809dca83392a5464d56a887612a5a0d3645e8a08782a281c989997e43b06580a98995f2a46654174d994c5d66652577799465d5e65157b699435dd8650832d9938b9a62bd821f8923000054b955a267c523221d4ec3800721ea661887b817521e205c0876816e21d605b4874816c21ce05ac872816a000043b887110f26eba761848dc3c50ada7630e94b71d362043b40cab71f3634764c2b1c3a512267644e942a55392643acdcf1d9b363676742c89d990b1a762c2c310f102fa438c0bb10f33b0610fc49544851250df74493800054aeaad553aa63c4cf8acd148cdcd2087a761049444840b2210f00011d9c333210fc495043b122cdc740b2000054ea98f159a291921e6760ccfb90e3030643cc0b890eb02dadbf8495b75c123adbf0487843a000410f4e0a843f15f2088c579dcd316136adc584589b15d4001c4218000556aa95552b952f10ea7eed33e1d80140520f43a7a1d832c0bbb0ca12cd1131d188432caab5067c0001dca152f10ea7eec32b9d7e3756a11c1f3285f0766a26c1c0285b06dea4641a682200002088c579bb43148ced6c518bb971438ed5c50abc15140e087ceba2e9b3298baccca4aeef328cbabcca2af6d32876adc58a000010ea195c988952d3af81dc56399b3e8fbc2841d9b835b4c7a759d30f9b4d000a660131583e44c860ec533f837e4c7e0db5da18a4676b628c5dcb8a1c76ae285530e1c6243b0658174d994c5d66652577799465d5e6515747194400004c40a9708750cae4c3937e152b3af4718c985829d25fe0a5c000397926204c39c8f9d7634c2ecd85083b3413e91f7c3b8c7dd0e5ab1cc4cdac7112fee46c12e93020010e464cc5130d053c4c2c14e930905384c0414c12ff052ee4784dbac760f6b1f885163b3b0742a0fc46bb4e7356aed0c5233b5b1462ee5c50e3b57142af0545038ecf01723b2c05b93113ae84c4ccbf21d832c0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1ae8c32804c54c9cb540115aee5019e0000260c4c1010f952d2a5c21d432b930e513275d43dac7e21458b1dc4dbbb3b0742e47c150a83f11aed39cd5a8ecf01723b2c05bb540115aa260eb9a1d832c0ba48ca40000043e54b443a8657262275d0501483d0e9e8760cb02eec3284b3444c6bb950676e5e4123800051304c44a96865710ea75cc16ea8473722e4984e9c7ea0ff4b1f8dc70cb233ba32b4dc18cb1356e656c228267d3a8c6554dfc3f8e370265842209953087432e40188cab0055013442433a5108f17383780004369ca9884b3c3b20c0898f02ba262a38370f1048db71d3ae29878ea91d9a39267664eb82ab40cb2a9d03252a540c7718804c745e0130f17004c02c760f6ab1c83b8acd00e9eb24039f2c700e5a32dcd0c47e214511f78506483c13fd1ff04fbc7dc13e09870e821310369643ccccca1d832c0ba48ca42e8e3288bbb0ca12eac3282ba30ca05cd316136adc584196315de32ec577589b15d4001c425000010e64c38ece1fbb21c410f537e06573ae41fea3f58a4558fc2755da103e6724c0b7942308f7832c14f0dbf1b8d196400146569b8332b670b46578035658c70b065a801d0440000410f9b2d2a5864d997288392a560ca065c8031195600a931e9d46196270ad9d28847000800000019a6832aa683531105cf4cf81604a979d658754253220209228b9c1bc152d06b35568196541f02a15074099544c024750b008e22e309b8723c26ddc8d099b8c402639cbc098d72702619531096758ec1ed5639077159a01d3d648073e876418113151c1b196e68601118af38fc428a23ef0a0c907827fa3fe09f776a827d9b8181bc6eba05b930f1d524c3874108761b1043b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d186502d5b8b0832c62bbc65d8aeeb1362ba8003884a0000dc74fdd90e221e410f4ecda6fc2622195c4399d7102a843b0d88371c1236dbf048a43c50ae70e942b3000054eaa95487110f2087a7664eb81be419706e080021b4e32aa683465b99df000e2129311029f4c3c098d33e0245000098f5c8fb91b72f2987537e130f3ada6768caa99d9000400000029d364c3e706ec4d8aea000e2128000263d4c3a9bf13151d6737d63b18dae1b7f0a783b4406dc19711eed40c4628cb9006232ac01502200002087cdf4a91836b6ce94423a84705bc0010000000334d0e49c4eac5ce0de099f02c0a83e0542a260123a8580470e4784dbb978131ae4e04c32a6212cf10104912c760f6ab3403a7ac900e7d0ec8302285b04eaa0e0e27262a3836aad0dddb93b36fe32dcd0c022315e71f88514483c13fd1ff04fbaa76126ab1fc3fd371e032add740b7261e3aa49870e7e2a5438404c40dbec7eb36f643b0d8821d832c0ba48ca42eec3284bab0ca090f317616adc5845cd315ef626c5750007109443dc0b400003b36dc74871043d2a5e7eec439a6fc0caea0eceb29d524c3e706d31586044dfa163e1d98967,
  0x13286bbb0ca12eac3282ba30ca0065b15ff7bbc57f36fe12567ef433cc5c20cf00000fdd8873261e10ed37e10f254ae7688ea700040000987cece800334d032ec577589b15d4001c42500004cfa54b4439930f4df89874ed0892b54ac1dbdb7f9d5f43ac31c5b8e091654e8687c989997e000054ba3efc7fd76aa10eee6910f23f747680eafb6fe1256dc7048b2a560ceea9d032500008bc3170c21d90f23f76767c00000031096001442032c70066cc900108caa36ba32e47010cad195232ccdc68ec636b83b44d599b7f0a79065c47b82200002087cdf4a91836b6a11c1f33b43148b1fa83fd2c7e13ac19600018657131ab3403a7a83e0742a0e81aea8980676a16019528380632088c579bb3a144eecd8505c83c13fcee504febb5413ececd04f7b92605b8e5e4122a67d3b3a98a8e0d8cb734303b5cce8a1d832c0ba6cca62e923290ba38ca22eec3284bab0ca0ae8c32816adc584065b15ff7bbc57ed89b15d4001c4251315045ae46011400004c3a54b4439930f4df8987cecf1b5c1da26acc7638d5136fe14f06590005195a6e0e0cb88f7508e0f98cad9c2d768629163f507fa195e00d59631c2c58fc275865a801d0cb0000c1100001043e6cb432b898665ca20e5c9c82364c7a75186589c2b32aa6fe1648073e507c0e8541d035d51300ced42c032a197200c4655802a04462bcdd9d0a27766c282ddca09fd8ff827dddaa09f6674a211dc9302dc000800013151c1b000669a065b9a181dae67450ec19605d36653174919485d1c651177619425d586506d5b8b080cb62bfef778afd32c62bbc65d8aeeb1362ba8003884a262a08b5c8c02280000987d30e952d10e64c3d37e267d3b3a6f9065c1b8200086d38caa9a0d196e677c003884a4c440e7d30f035b4cf80ce531e03284c380c5c0003b3b766eee55daabb35261e9bf0a959d9c0cef1708e6d261f35c8a95c49580020000dbfcec5267d3a729870e728005330076706381fb90cce98ac16e2643055e99fc141263f37eae49c4eb393f1382e5ec4d646a11330196000186573b34b1fc3fd2c970f8eb34c3ca2d510ec287543ae952d069b1fac523c803146520fc50ec8bd1410f05450390f5330c8760cb02e9b3298baccca4aeef328cbdb4ca1865b32716adc584589b15d4001c425131104aee7e412a00004df84c3cfdd843b523243c843a9d9b33ee43ac0b690e302b8dc74eafb6fe1256dd7048eb6fc121eaad019ebb943afca950e102a56359454b8c9a952b3b3254c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca180002a5821d537e130f3f7610ec87906573b342635668074f72f2091641e0a024cfa0ce9dca9a6376862919dad8a31772e2871dab8a1576680c6130e1d1243b0658174d994c5d66652577799465d5e65157761942782a0d28000065710ea9bf0987952b3b320030ece85913b2e15ca24289268788245d53a064a6fb805d88711d238bc0262d59a8669727208c9c8c0223260c763a350899873f2265d63b07b55aa21d85648073e58e01cb63f10a28917a281a3fe09f78fb827c10ec19603b16654974919485eda650d75619415d186501e0a034d00004c28984130426041964a969fbb10e67668ecc1d943b247640ec71d8c21d410ececf291921e44c38ec781b721c467ddb8109476df8243d52d06b354a8716ca979a968b8c26f22e009848fb81cb9c8f829826000020439000410ea6849c8c998a262665f90ec196010ee64f498a99392622095c986825325fe0930000130e26144c20982130273f01964fddac7758e243a821da91921e44c18ec71b7526160984988825725fe09309878245261a09109838241260a0900981823f260208f9c8d09a073f2265dcbc09925aa21d8432c0003917a281832b898e8b8619de310865978280d34a9619363f7431c5639077159a01d3d0eb874d58e01cb4a9583392a5e6a5a3ef0a0c907827f9dca09fd8fb827c0439000410ea763152b892b21d6061db7f9d8a262665f90ec19602a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd86509746194010ee64f432d9938b9a62bd821f8923000010ed33e291921e4aad0ec69b45262266d0985826125fe096c9878245261a09109848242260e09049828240260608fcfdd9aca7234266dcbc098d0cac000c32c9d8958e41dc5668074f8fbc284241e0a02766e0d7ddca833d2a5c761d0ec19605d1c651177619420cb664e00002ab454ac99f148c88753b186d1497f9a4d262266d09878245261209089868235261608d09838232260a08c498182303f7675f9cbc098d7270261832b00030cb27625668074f59201cfa41e0a028ff827ec43a000410e627d9dca833d76aa0cb0a971d88556a247553a89166eba7619b8e9b1043b0658177619425d58650443b993d0cb664e2e698af721ee063c877818921da06208718183000010ed33e291921e4dbfcec509928c421965cbc82453f746ba49871a123f72199c98882578d422661cfc89975aa21d8645e8a0843b065817b699430000b34443aaab44cf8a46432c9d8938c64c4411512ff043ee464e91a83806324c3c122930b046854b0c9b39781324e4e04c5acd00e9eb24039f46210cb31784325152b067219600019fba343e195ccbfc83c13fcee504fec7fc13eeed504fb3b3413de21c80020875,
  0x1148eed0c52348bd1410f054503a84611ef065829e131104ae6df8df590f5330c8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2af6d3287734c584865b15ff7bbc57edab715e3626c5752918116e001c425131505c2e49816e39f904a8d7000600ed90152d38004f8000044317389878cb84c5632a937e0875196c3b1ced81ae632aa108065c8016196a00506588012195e00446568010196e6861fb60830658820bc000261f4c3b62680019daf0000000c425800710940014423b2c70066ce9001500004c3e9bf06559dae13e91f74396bb350636a954e2aa1d832c0ba30ca02c711301170431c80002a5e195cfdca61d10eaa0e0ed69a2621c468d4ece9a27513222b5aa09afa1da6034476380cb69c422ec000283b54ea54bc32b9fba26144c209821302260021d498612fe3f687ec8fd81fac3f547ea021ddab6043e76b0df58ec633983b445b09b7f0971062425a1b78365506a0453b500114ca1601953b5413f71ff439f2c91130ce4e411b263d3a8c6554dfc0cb9006232ac01533a5108e0010000000334d099f0ed48656000608780008221375619644eb2c7f0ff4a17c1d9a89b0700a16c1b7a919069b1fac523bb5b1462ee5c50e3b57142af054503b92605b898a8e0d8cb734303b5cce8a1d832c0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac3282196c57fdeef15fb6adc578589b15d4088c47c800710944c54116b91804500001423261f4c3a21d4987a6fc2a5a76acdf58ec633983b445b09b7f0971062425a1b78365506a0453b500114ca1601953b5413f71ff439f2c91130ce4e411b263d3a8c6554dfc0cb9006232ac01533a5108e0010000000334d099f0ed4a61e3b50087800082213756a11c1f3285f0766a26c1c0285b06dea464ecd952c3b3432dcd0c022315e6ed0c5233b5b1462ee5c50e3b57142a21d0002065600061964ed3a61c3b4821cced18ed733a28760cb02e9b3298baccca4aeef328cbabcca2aeac328221dcc9e865b32716adc584589b15d4001c4250000261e10ed37e10f23f7676a800000031096001442032c70066cc900108caa36c032e47010cb31aa232b46549b7f099a3b18d71c1e8115ca26019dbb94140520f43a78ed733a28760cb02eec32856adc584589b15d4b3444c680071086e5e412280004c3e087ca968657196c21d4987a67c3b521d3e41e0a0259a22635dca833b72f2091544c9ae34cfa69a07639a5c766c2841e0a8a078fbe1dc40010000000a75390ec19605d1c65117b699435dd8650ad5b8b0819762bbac4d8aea58e6266c003884a7236098c000021f2a5a195d30e8875261e9bf130f1da80676a264d38bb94140520f43a7a84707cca17c1d9a89b0700a16c1b7a858065454b0c9aacd11325188432c952f0658ed504fdaab5123b1ff439f375d3b0cb2444c5aa750c9643bc0c490e302b91784ecfb71d3abedbf8495aa560cef1708ed33979048ae4e411b152b3b4a98f4eb3a67d3a72987cda68005330098ac16e2643055e99fc141263f04e6e49c4eb393f1382e5ec4d6393b134ab1fc3fd2c970f8eb34c3ca2c930f06a464ecdc7eb148eed0c52348031464ed6c518c83f143aee5c50e47ff142ced5c50a887400089870ed208733b468760cb0153132be762cca9152332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeec3284bab0ca08877327b6adc584589b15d4001c42500003f764c3c21da6fc21e41964ed3891654e81929b8e9b1021c6689a2f0098b59201cf8ece858321e605c4876816e8ff827ee202091e6eb8247555a065976aa0caa310099250b22299668074f6a02673241e0a02772a0cec76880d051326b8da7108bb043c00041109a60508e0f9942f83b351360e0142d836f50740d747639a5c76862919dad8a31772e2871dab8a15766c28423ef8771782a0d30a961cda1dae67450ec19605d36653175999495dde651975799455d1c651177619425d58650563989a0044622e952b86787236098dcbc82450000e4e130f267c0cb2a460fdd8875261e10eed5b1d8a8b8476983b8c7de1420b1cc4d045c33b3f1780e7221d832c0ba38ca23b3706b6e46c13180004c78987832c9fbb10ea4c3c21d90f22a567694ecda91839ac7ee8e67284739a87674e72c7eb148eed0c52308740008196000188733b4654bce8e86573a20ba6cca60877327a196cc9c5ab71611626c5750007106ae4641138000261e10ed37e10f24c387690e7b2a5438b717004c23919044e9874ecf261e04c6e4684d00658000654b0c9b06571338b1c83b8ac700e5b170c33baa573b447ee8ed0152b3b38ece8513c7de1418ecd8505bb9413fb1ff04fbbb5413ed1f704f83b3413de54bcd4b21d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c3280196cc9c5cd316136adc584589b15d4001c4250000261e10ed37e10f210e6768ce7b2a5438b717004c23919044e9874ed0a67c048ae5e04c946210cb254b0c9b2ab5123ab3403a7ac700e5a1960001952b3b38dd74ec3065732feece8513bb36141720f04ff3b9413fb1ff04fbbb5413ed1f704f83b3413dea9d432590ef0312438c0ae45e13b3edc74eaf952f352c8760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d,
  0x1369c001c576a8980b06a1602bb1d9c3333626c587261e031698f00b210f23abedbf8495c404123d0f1048bb71c122c088c45d00005230a0ed33ea839556aa9d552b9fbb4c3a10ecee289fb8ffa1cf90ec19605d58650564889878bc21929daa832c00007eec32b952f10eaa9d0ee20001043e688c11099ce1d8e663400029184dfa088941da8995072a164ee199dd19662cac6588b27195a2c88cad84237eda10806559dae32a8751865c9be4196e677c65d8aeeb1362ba8003884a000098f4002a61f4cfa987537e1dc20c74a0e0ed69fb836727edc31c45c136b0b1d83daaa7406591f885163b941404ed504fdc83d0e9f1ff439f3b3b0747173c4eaacd1131ab2444c32a5b128ee49816bb9390464dc0c0db90e23a22e5e4e319306368a7ed43391fb30ce27ec43381fad0cdc7eac336930d04c44c2c130930904c04c1412f130304ba4bfc12dc5c21338e4684cdac720ee31f785083b3706bea95c495b6ff3b7eb1fc3fd043a000410fc57cc7eb148e10f4e2490f3388a4c44cda21d832c0ba6cca62e923290ba38ca22eec3284bab0ca0dcd31638000032b952f261c987443a9fba3b801cfa3fe09fb59222619daa832c727208d4986197b556a247553a89166eba7619b8e9d5f21e6711497f9a92262266d0989997e43b065817561941b9a62bdc87b818f21de06248718183000010ecfdd06572a5e4c3843ab6ff3b7e1810ecd19aa87662595b8501ef21d4001c87999993b3a1674ecc859a3b2e1664eca85983b221658ec7859521ca06e0878818a21de0624876818821d20618873818521c6060db810947874c24b1b7f092b54b40e8d52b035f767428b1d9b0a108fc61ed63ef877158ee26e1639899c8b8e1ac62e18675507e235d41d88bb043c00041109db069ce03dda7180cb087400087631db7087a680a2e789d558fe1fe953183e854f60ed555b838254ee0dc559a834f2a5c64d487b8afa087e2be41118af38fd6291dda18a4676b628c5dcb8a1c76ae2855e0a8a07724c0b7065c80313f700034fdd9db82a5a76d06559dae2a5676653151c1b196e686087a998643b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699433f6e2fc8fda8bf13f662fc0fd88bef3f5e2fb8fd68bed3f562fb0fd48beb3f4e2faae698b09b56e2c20fde8b01bdde2bf2c4d8aea0cb626696a88994000e21299d2884773f2095000000054df8195c43aa61d4c3e4c3cedc8002087a6cdc21d8917878a15d953a032c3b3831c1daa09fb8ffa1cf8fdc8675262209956488986507622ed42c88a783521309c9c8236043c00041109db036fc6fad31e9b8269c6032c7631db74cf876010ea8c548b9e1bbe2e1067854c60fa155a033d772875f952a1c2032aa6fe152b1aca2a5c64d421f8af904462bcdda18a4676b628c5dcb8a1c76ae2855e0a8a07197200c4a969db4195676b8a959d994c54706c65b9a1821ea66190ec19602a62657ca9199505d36653175999495dde651975799455eda650d7561941c2162c2ee698b09b56e2c22f778afcb1362ba832d899a5aa22650003884a674a211dc8d026473f20950000130f000a9bf032b88754c3a987cfdd9db8000410f44b3843b123d0ec830344050b0676706381311048ee5e0123267c3b00a958d652ab4067aee50ebf2a5438407ee8d74a89934607ee43770ed5014c3b4c052a8463b6ad38044f821e00023b6457a022315e6a0e0edb152d3b680884ed9a62a383643d4cc321d518a9842c585dab716117bbc57e589b15d4196c4cd2d51132810fc4b480071094e7e412a000054c454be2e7130f000a9bf032b88754c3a987c7631db738407ee80069fb93b5aa954e2a9fb717e47ed45f89fb317e07ec45f79faf17dc7eb45f69fab17d87ea45f59fa717d47ef4580deef15fa4c54116b91804500000a97930f0cae21d530ea8383b6c14f0dbf1c9036ee2d6e0cb88f569dc049c7671af51daa029876980a51da2029076680a21db22bd20c408a069c0227c0002846043e3b1ad5b262b507276d45233b4207cca118ed5ae9b32980000987a6fc10ea987530f952d3b6807d08791b466e16259821e0002087676c4fdd000d3f7276ca2e789d558fe1fe953183e8087e2be476c8af48fd6291dda18a4676b628c5dcb8a1c76ae2855e0a8a074c3874490ec19605d36653175999495dde651975799455eda650cfdb8bf23f6a2fc4fd98bf03f622fbcfd78bee3f5a2fb4fd58bec3f522facfd38beab9a62c26d5b8b083f7a2c06f778afcb1362ba832d899a5aa22650003884a724c0b71cfc825400003b18110930f4c569bf032b88752a5e76cc45241893920d384db19b7f0a786ddc29b8ecf024e3b3409328383b5b065c47bb4ef11eca11c37700003f731738a9788754c3a195d3158ed81d8c0884ed908a483127241a709b6336fe14f076781271d9a0498dbb9b64832e23dda7788f6508e181944c05833b38666476c8af487662596202091e55680cf5b8501f421e476a9dca1d7e5070714952a1c20b56e2c22c4d8aea000e21280001fbb10ea195d37e130f4c3a54bd531043b4c563b181109db103e843c8ecd370b12ca10e8001043d12510ec830344840b22acd41a7865600067ee8d74952e326a7670638065913acb1fc3fd21d50eba7ee4377152b07c854b41a6aa63372410fc57cc7eb,
  0x15d24652177799465d5e651574719445eda650d77619425d586504a99993eb9a62c26d5b8b0819762bbac4d8aea000e2128000065710ea9bf130f1dd901603b48d7d35401164d400455c1e9099a6df8e57c1a936546de4d948ec7331a088c45d00005072a0fd44ca8590442a0ed31e267c52307760dd5a84707cca17c1d9a89b0700a16c1b7a919069a0000110bb4276b4ee59dab3c142a5a775c0658ec635c6d38845da83a3baaa260eea5ab71611626c57500071078000131e267c4c3c195c43aa6fc043e7758e4d3b3614211f7c3b8952f3ba0b1ccd9fa1d832c0ba38ca200004c78987832b8875507477543a7c83c1404b3444c6bb950672e5e412393103af454a8c9a952d3ba64c3cee8952f3ba08760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2af6d3286bbb0ca10000043e98f133e261e0cae21d537e28983ba87240dbb8b5b8310228141c1c311d9c6ad5a7308d7507c0e85d9d0a2c8fc61ed4dbf84e31d96033563b89b7831422f1a7108bb723e75d941d1c9a766c2841cbc098d8fbe1dc5668074f58e66cfa41e0a022a5e77409889d734c3874490ec19605d24652174719445dd8650ad5b8af0044622cddca833b0000a26010fa63c4c3c4c3832b88752a5a774cd300ec734b8ecd850847df0ee2a11c1f3285f0766a26c1c0285b06dea4641a682200002087ced4152c326a088c579bb43148ced6c518bb971438ed5c50abc15140eb1cc4cdb91b04c654bcee8261f3b9e54acecca61c3a248760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1dab71611626c57500071094000032b88754df84c3cee8832c76a827ed53a89168ffa1cf9b8e9d5f59222619b7f092b54ac0d7dc9c823621e6692d31e99da766c28423ef8771260e097c9868226261608949828222260608849808220087400080010000000a7538fdc1ae9087a6808caa99d958e6266dc8d8263723008a130f9dcf261c7700fdd9dc754c60fa153d83b5556e0e0953b8371566a0d3c21f8af919762bbac4d8aea76862919dad8a31772e2871dab8a15782a281c003884a4dfa773130e1d1243b0658174d994c5d66652577799465d5e651574719445eda650d7561941b9a62c70000065710ea54bcee80000000a76e40019daf4c38744ac4d8aea000e212800026fc261e195c43aa61f3b9e247555a033d6eba05b487519f777282809b7e090f907a1d3d52a1a3b1da268e5668898e8c42195c11000015132770c8719a26043e688c763998d5074772ca96832b50b019222f0098759201cfa3fe09fb76aa0cb0ece9dca54ea77248799a4b37022bd476c8af4b56e2bc011188ba5232199c9838250261a089898582252612089098282222606088498082200874000941c1dad3f706ba421e9a023f6a2fc4fd98bf03f622fbcfd68bed3f562fb0fd48bebb1362c4a350899673f00955c8c0228261c770098899b43f76771d6a8876154c60fa153d83b5556e0e0953b8371566a0d3c21f8af976862919dad8a31772e2871dab8a15917a2821e0a8a074c3874490ec19605d36653175999495dde651975799455eda650d77619425d586506f779937b9a62c70000152f0cae21d537e9dcc14591f8c3dabb3b0746b1dc4dbaa5b1290e47c14fa62337330eacda90004369a9878cb9a62b0c08a9581af9d9a3354ecd850843b312cb1f7c3b8b70a03de43a8cfb996315deb1cc4ce45c30cea765c2b29d950ac876442b11d8f0ac2438cd160cb734307ee0638589b16250e9048836fc121eecd018e130e3b809870e861d993738a950cdd9311336843ccccc90f5330c8760cb02e923290ba38ca221d518a9842c585deef1615734c57b5ab715e010fc495022311820000ece152c4dfa10ecfdd2a62566854bc32b88755074772c50847df0ee2ecdc1afac731338a95c49645c30ceb0e9c2cea83b3b86a1603242898344f17804c3ac900e7c4bfcd2690f328011ff04fd90ed02c2438c0ae130e3b809870e89371d3a1a8760cb02e8e3288bab0ca09313180d7bbc57e5cd315ec196c4cd2d51132a10fc48e022311751a843333b550658000153a29184dfa10ec986130a26104c10981130050727ee4fda1fb23f607eb0fd51fa83f7454bc32b88753b3a7728d13a899339ca1602bb022000027670ee4021f3b583b1ccc6a83a0cea4bfc12dc5c21338e4684cdac720ee31f785083b3706bea95c495b6ff3abe43ccd25a1d832c0ba38ca243c4122edc7048b02231174000148c13064dfa10eed5b130c26144c2098213022600a0e4fdc9fb43f647ec0fd61faa3f507ee8a97865710eaa9d4ee49a3521c668980000ec654ea10eed5b152f3b38772049344840b22df700bfa9183b8a9bf0ee10004369c001c576a83a0b3a7670cccd89b161c98780c5a63c02c843c8eafc3a61258dbf8495b71c122c10e8001043d3b8c99f0ec0283838a4aad019eaa743b88ee50ebf261c3a04a950e102a56359410fc495000054c4a9e955b2a76566854bc32b88753f76771ccc0262b03e8990c0e6a63f03329bf40bfb70b12ccdc8c4a8b71f126adf74493aa6307d0a9ec1daaa7706e2acd41a780040000ed0c5233b5b1462ed5c50abc15140e001c42f90f2389299fce1b800334d0ba6cca62eb33292babcca2af6d3286000133e952f4c3a21d421e9dc63b869bf0ee10004,
  0x1369a0014cc0262b05b8990c157a67f050498fc139a6fd04aa9870ef1b92713ad179c4e1393f1383188c4d6b97b1358e4ec4d2c6a11330e7e44cbac7f0ff4b25c3e3acd30f28b24c3c1ad510ec2a17c1d9a89b0700a16c1b7800715db1fac523c8031464ed6c518c83f143aee5c50e47ff142ced5c50ac8bd1410a11c4799b770992d3bcdcaa91932d2ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac328287606391fb717e47ed45f89fb317e07ec45f79fad17da7eac5f61fa917d7626c5895eef161443dc57d5cd315ed6adc578043f1270088c460c1e8115cd500456953106c4ecdc1aebb9406780000987865958e6a0e810f952d10eaa9d953128993bcc05908791daa6e3824580002a753f7698f137e130f0876779448dc3c50aecdc740b21d9c3a52766cd8d90f235a2764c2ff9d8d0b4276642c690eb03de43b40ca90f102fa438c0bb285934e243dc57d5cd315ed6adc57843b312cedc2c4b343c7126cdc7c49a843f1255121449437dd124e088c452a8980676000155aaa7554f4aad959a1fbb5070e4e133e263c54c4a9d930ea85e5134a16948c3b952a5aa11843a843d3bc869947631cbc507071bc10f00012a5e745c1109bab044622e8000285e5134a16948c2846513221d530e1de33bbc54bce3d43a53810b1c83b89d930bfe76442ff391904530eccd6747de1420a0e4450262a1112ecdc1aec1893920a0ecdaf9d8b32a4766c58790f3161c6dfc586800615d56268ef09d9f15f610fc57cc5cf13aeb1fc3fd285f0766a26c1c0285b06dea4641a69fba3369734c584c7eb148eed6c518bb971438ed5c50abc15140e6ddc264931034248760cb02e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1dab7163507a045700004c7a54b410fa89910ea19649871de200000014ea7000333b46554ceca61f3bb83b18d709b7f099a99f4ef026fd3bbe9870e79152f0748a968359c5c61378b1d83dac7e21458ecec1d0b91f0542a0fc46bb4e7356a7ee8cda284711e63b3c05c8ecb016ed3bcdca931034248760cb02e9232916adc5780cbb15dc001c5768223117507a04573540115a0002c4d285e513454b498706595230a16843a821f513298f4ef09dc24c3c75380020000000669a065d8aeeb1362ba800026fc000c987531ea67d3bc01cfa3fe09fb5922262e2f0864a76aa0ca9c9c823854ea6a007639a7750b269d530e1cf23f7466d09881a1243b06581756194100009bf542f5ab6513454b49870659b134a11942d291810eaa264a971ddf000410ececf843d34fea9d0cd3c5e01316b1c04c1ac900e7d170031e2a5433f51ff04fda8391140b1fc3fd2c970f8eb34c3ca2c930f06b5443b0bb550654e4e411c41893920a164d3ac7eb148f200c519483f143b1ffc50b48bd141117084d0043f12d2a11c479a85f11bca26c464a85b11849bf0425261c106aa98c3781b770992d41c081354301c2d40c06b06580006d3bcdca8ec635c27ee8cda291932d2ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac3282876063910f3161c6dfc586dcd31612196c57fdeef15fb6adc578000615d4195c4cd8223118307a04573540115a54c41b13b3706bae46c13293150496e5e0124000058e6a0e8a9713112a5a087d44cc5ce10eb626ceef0840664800846551b6000086d3865c8e02196e37186598d51195a32a6c4d8aea000e210cdbf84cd1dae02f5aa000b500003b1d30fa63d83d299f0eee1beb36fe6e307631ae351300ceddca0a02907a1d3d668898d72f2718c985826125fe096d33e9b824c7c6df931e1b3e7234266d63907718fbc2841d9b9dda32aa6fe142d836f197200c410f00010442775c9889d7c2a5864d59d288472a560f900020000000676bc6559dae4c54706c65b9a1804462bcdda18a4676b628c5dcb8a1c76ae2855e0a8a074c3c77649879dd12a5e774130e1d1243b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d7761942b56e2c22c4d8aea000e212800008754df8195ceed898d59a01d3dcbc9d7690782809c8f09b758ec1ed5dca833b8fc428b144c88ad76760e8541f9c316a826be876980d1507276d5a7108bb508e0f9941d035d262275d07639a5c2a5864d4a9583e476862919e0a8a072a5e774130e1d1243b06580a98995f2a46654174d994c5d66652574919485dde651975799455eda650d77619420000087d315930e0cae21d6d5b3b373bb4000821d9d9f087a76108799d83566a19a6350899673f0095d48c1dd8507c0a8541c1c11723c26dd63b07b554ac19dd55a06595130091d42c1a6a3f7466d23f10a2c8b842672310098e72f026362f0098758e41dc5668074f59201cf9d9d839f262075e953a197f8fbc284241e0a028ff827ed31188674c560f91d9b835b772a0ce5daa83286596015ca95000919540014a969dd719666b9d6a8876132c21098caf842532ba1090cac842232ae1084a9083de2a3e0ea8a93837b2a4a0da4a8e83652a520d24a8d83421972005865a8014196200486578011195a00401100001043e775941d1dd54cfa69a065b9a184c7a6768caa99d9087e2be41118af376862919dad8a31772e2871dab8a15917a2821e0a8a077ed820c1962082f000400009879dd12a5e77400029d4e4c3874490ec19602a62657ca9199505d3665317599949,
  0x100031f785084485124c0884454bb3706bedf700bb34e30196d4000550ec63b904388d1aaa57125676742bb36ff3abf0f1048bb71c122c1960001843a0004195cee8043d389232dccefa1d832c0ba38ca2065b3270874c629e10b16076adc578043f1254088c45615330660ed5019680004c7aa16153ac6a073f0acd0a97887521e477d46379fb70cca766c2c7930f04aa9bf0ed70caa36c032e47010cb31aa232b46548ed701a8d38c06580002a546df930fc4841d8e43ca35039f8196c874ac4d1df40000000ced7a61e3932a0ec45d80051072cb9000c021e000232a8db00cb91c0432cc6a88cad1952a95c495aa5512200884454b4e30196d4000550ec63b90dbfceafc3a53a4e76742bb1d9b0ae8764c2b810f302c86dfcef8c3c4122edc7048b043a000410f4ef9261c3a323b5cce8dab715e1626c575043f1254088c45600071078acd41a7800050b0a9d432c8cb62a5eed09dad3b9676acf05131e1df3333243c8da31d9d366ea98c1f400004c78a9d4a97bb4276b4ee59dab3c14087a77c8ef70ec63b90762cca91d9d0aec43cc0b25ab715e10f1048bb71c122c088c456000036fe98f142c2a752a5e10ecef8995221e60590ec51dee6e38245821d000254e877bc21e9dc62a5c64d4a9583e44c5474e533e04cd36fc72407631a6683102280dbb84c9507077b60f408ae043c00041109bab50b269c542382de724e275963f87fa2620684821f8af98fd6291dda18a460cb0000ca969deb0cae776d0ec19602a62657ca9199505d36653175999495dde651975799455eda650c32d9938b9a62c26d5b8af0044622e8003883c0000a2649871fbb50b4a46144d285e4df8987443aa63c3be027ee3fe873e5922669d0ec19605d586505daa832c000054bd42c131110eaa9d0ef78eae3b2800308711a353b3e15e0ece85763b3615d0ecc85733b2e15c8ec985703b2215bcec7856e3b1a15b487a9986b56e2bc21e20917044622b00001d8a087654bcdbf8ec750b098f153a9dee02c843c8ecfc5c21340dc7048b2c720ee2e46c132843a000410f4e07a83b36bf1f7850845e00c966dfc266bb3706b699f4e9ca61f369aa9d0d37bb9534c60014cc0262b07c8990c1d8a67f06fc98fc1b6bb34063054a8c9a952f3bd810fc57cbb43148ced6c518bb971438ed5c50abc15140e196000186573bb68760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1dcd31612196c57fdeef15fb6adc57841e8115c088c452800710784c54125b9780490e46411480002a58a16144c821f26229bf0fdda61d10ea98f141c1ded3a2c9874e292a5435980001c8c28380cb27eec43a952f3bd877a48799de74cfc2175fe7045b507277a8caf1ae732b22cb4cab8b2c196400146569b8358ec1ed4cad9c2d8fc428b1d9d83a12a5e0cb46578035658c70b06589c2b32aa6fe153a19a7507e235d648073e32c21104cae842d197200c465a801d195676b930f1d4e69ce6ad63fe09fb809a21219d288477f1a20e9972883936fa1330dbc84ca36ee1324dba84c836e6131cdb884c62a560f91daa832a727208e076780b91d9602dc00200004c5474e542c9a71000669a0fdb8bfb8b9e275e0f408ae6a8022b563f87fa508e0f9810f00014cf877a01109dd72620684a3f58a477686291832c00030cae776c65b9a1843b0658174d994c5d24652175619410cb664e10e98c49bdde2c2ae698b09c2162c0ed5b8af032c62bbc65d8aeeb1362ba811188ba000e20f1dad83b2772e0dfddab836e782a0d30a99834177280cf0000152d51329bf131e285e50b4a460fdd8875261ca26930e9deb14211f7cd363b3734b8a0ec45db4e301963b18eda9b7e3920ba38ca241881140f0541a6000050736ad9423262b2a5cee54dbb29184cfa087d63ba61d10ea54b537e195f3bd46be876980e71d8e027daa188cb69c222860f504fa831012e0dbf0c6f3b3618121d99ace1dae674400028383f7621d62e7262b43a454a8fdb130eb13443c933fa89a36f86dd8dba1b7236e09874dbc021f6a8277a4eafb6fe1260dc7048dc3a70b370f142ba043c000410ececfaa5636647668637c5c21340987c425ac720ee2000800010f33bcea9d0cd3c7de142117804c5a8391140001441cac900e7ce46c132b2c70066cb9000c4189392032a8db03b3734b832e47010cb31aa232b4654c7fc13f6a0ec45d9b7f099a6ddc264bb550654e4e411c34e301963b18d71a85934e307a0457284707cc087800082213bae10fc57cbb43148c54ac19c930f048a32dcd0c0ed733a28760cb02e9b3298ba38ca22eac3282874c6249fb717f7734c584e10b16077bbc57edab715e1626c57502231174001c41e3b5b0764ee5c1bfbb5706dcf0541a615330682ee5019e13150496e5e012400004cf8a26498886592a5a21d531e285e5134a16948c261d3f7677a0001043d381a7670ccc843f15f3734c57b843b122cdc740b210f702b6dbf00ac000021e6a9d443ab9384c78a17944d285a52307eeddcaa61d508c54b541c1de7333276742c210f235a3101449090e302ecaad4ef237dd124e10f0001043b3bcaa9d032545e01316b24039f2a7b0d86aadc34b2b350cd27ee8d03c7fc13f6a0e44501fb90ceaed5419541893920a164d38c5c213406dfc266b91b04c6e4e411b263d3ace99f4e9ca61f,
  0x16dfc24ae202091e6eb8247555a033d54ac726552a9c557728280941d88bc5072228241e874f831613820c484b436f06ca966889928350229e310865772f2091410f00014cfa74e530f9c1b04426cb144c9a71044622e942386ee50be1b0544d869450b61a1548c86674c560b71c8c02283f706ba49871a12262266d10ec19605dd8650ae698b09b56e2c22c4d8aea000e20f00001fba724c9bf235045e28c45179a2e728594c7821d530e952f0cb210ecec51dff3abedbf8495b71c122ca9583b7aa740e7887586389fbb3bfab1c83b8c7de1420b3403a7bb3706b6987cda68005330120f0501393f1382e5ec4d6393b134ae7e44cbac970f8eb34c3ca2c930f06b5443b0a62b07c8990c1d8a67f06fc98fc1b6a67d0674ee54d31bb43148d200c5193b5b146320fc50ebb9714391ffc50b3b57142b22f450447fc13f6f0541a53b550650ecd018c152a3bf832dcd0c131332fc8760cb02e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0dcd316136adc584589b15d4001c41e00002a5c987537e28594c7821d432c843b21e477f82cc9d9600190e984961d9d0b06766c2c09d990b0076542bf1d930afa76442be1d8f0af676342bd2a563665101048f283b1178aad032cc18b09c06de0d954620132506a0453b979048e0878000a8993be00884d96285f0562a26c142285b04eaa46412b93103424767c57d822315e64c3ced39d8b32a5734c584dab71611626c575000710780000fdd90f273f0e4e9cbd393e4c3a9bf142cacd14c7899f043a86594c3cb1cc21d9dfd3b4e7ee8d03930e18de7ee433a9fb70ce6766c2cdc5c213410e984962a563664e46cd98ac720ee2987ced70caa36c032e47010cb31aa232b4654c7de1420ecdcd2e0ec633983b445b0a83b11787eb43731fab0d707ecc3479fb10cfe7ea433d9fb50cc7062c2701b7f09846de0d9521d31893173c4ebc5e71385188c4d6c5e3134d1a844cc41a8114ed4004532c7f0ff4b25c3e3acd30f28b24c3c1ad510ec2087800082213bae54b0c9a822315e71fac523bb43148d200c5193b5b146320fc50ebb9714391ffc50b3b57142b22f45043c15140e3b5cce8a1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3287842c585deef1615734c584dab71611626c575000710780000a95152e50b298f065b08750cb210ec87926fc3bf8676ccad99c07ed820c000100004c566a7552a19fa000a20e4871817665c80060a979dec19546d8065c8e02196635446588d18195a32a5bee89268908163dc8c82291d8c6730ecd0c6f1da22d8541c88a036fe12e20c484b436f06caa0d408a76a00229810f000104426cb0fdd19b450b609d498819ba3f6e199498282d626060aa0985827f261209bc980826b261e09549868253724e2759c9f89c172f626b1c9d89a58d422661cfc899758fe1fe964b87c759a61e5164987835aa21d850e9875b2a560d2e3f58a47900628ca41f8a1d8ffe285a45e8a08782a281c11188ba196e686148c99e01dae67450ec19605d36653175999495dde651975799455eda650ed5b8b08b9a62bdac4d8aea087e24a8003883c00009bf542cab340cb221d553110f2087698f130e9dfb000410f4d9b843b122cdc740b2263d3bf2a98c1f42b35069e10fc57cbb43148ced6c518bb971438ed5c50abc15140e1960001a8583bec195cee8261c3a2e7670cccae9b3298baccca4aeef328cbabcca2af6d3286196cc9c5cd31638000153a952f10ea43ccefd06598c4069cd55a891e880a160d44c9a753f7466d142382de50be0ac544d828450b609d498819ba260a0b5898182a8261609fc984826f260209ac986825352326781c9389d6727e2705cbd89ac72762695cfc899758fe1fe964b87c759a61e5164987835aa21d84a95834b4df877e2d5b8b088fd6291e4018a32907e28763ff8a16917a2821e0a8a070874000821e9df73b3866650ec19605d36653175999495dde651975799455eda650ec4d8b0e087e24a800010f350b2196530eaa62566821d531e9df93bb89878ea741e8115c00100000ec63530a260d39800334e5188432c821e00020884dd59fba3368a17c158a89b0508a16c13aa91904ae4c40d09130f05b8e49c4eb393f1382e5ec4d6393b134ae7e44cbac7f0ff4b25c3e3acd30f28b24c3c1ad510ec2a11c303152b07c8088c579c7eb148eed0c5234803146520fc50ec7ff142d22f450443b312caaad448eb70a03e8dd740b8a67d3bc098a8eb39d9c33328760cb02e9b3298baccca4aeef328cbabcca2af6d32876adc5840cbb15dd626c57500071094000021da63d21e6a16432ca61d54c421d537e1df83ace98ac0fa26fd02fedc2c4b337dd124e000131e90f34c3aa98959a043d3bee759d31581f44dfa05fdb8589666fba249c21e00020876245e1e285763b3866648791df58d422661cfc89975aa21d8553183e8566a0d3d31e1df3196e686021f8af976862919dad8a31772e2871dab8a15917a2821e0a8a070cb0000c32b9dd04c38745d0ec19605d36653175999495dde651975799455eda650c32d9938b9a62c26d5b8af0044622b00002a752a5e21d542c1df60c971784ecf9fba336917084d0391b04ca4c40d09130f16256268efa1b7f098654ac1ae261e3664a0ec45dc1a91150b1c83b8821e,
  0x1513210ed30ea1d22a54a16531e1b7e3c1a73b4984826025fe087dc8c9bdb72342681cfc89975aa21d862e18677917a281952b892b6dfe062d30f9dae19546d75e0a1a5c197238086568ca9508c23dd48c08b7832c14ddae000c036ec002c6599b8d1d8c6c987689a4636e21420dbe84e236f61384dba84de36e61374dbf9e0b831c23720c508c069c67825a739ab51daa02c476780ae1d9602b076480ab6a0022acdbc84bf044000060d49e04043e6cb541f03a150740d7544c033b50700c649878236261a08d49858234260e08c89828231260608c0980822f2a5864d9c9c098b58e41dc5648073e8bc21928a9583283f74687cdc08af504462bcdd9d0a278fbc2831d9b0a0b772827f63fe09f776a827d9d9a09ef4dfa7828db79af1196e686076b99d143b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d186502d5b8b08b9a62bd8cb18aefb1362ba821f891c54ea2458003883c6e3a059000010f34c789874a972859087621cc32c9e0c35f71fac522aa6212cb0ec83033b4207cca11847bc1960a78dc280fa262a37327670cccae9b32989888287a61e09c60000dbfc18b831e658930e90f3044254b4439843bb9a454b832c9e0b0b227670cccc485124cdf700bf90f23c10acd43349fba342117004c2391933144c1c16bb92713acb1fc3fd47eb148aed081f3284611ef065829e262a37306554d06a6220a1e9878271c18e11b9062846034e33c12d39cd5a8ecf015c3b2c0560ec901567ebcd05350011567ee43339fb70cca4c4412b930f04aa4bfc126022000026df8f02c1a93c08087cd96c6a11330e7e44cbad510ec2a0f81d0a83a06baa4601a62898067654b0c9b48bd140cb24039f2c700e5a54ac1943c143440088c579bb3a144eecd8505bb9413fb1ff04fbbb5413ed1f704f83b3413de32dcd0c21d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c32816adc584196315df626c57500071078000137e952e4c7821cc32ca61d50b210ecf0500061dae674476c80d51daa034876980d11da2034076680ce1d96033476380cb00003b3876434e33c12781cecb85653b2a1590ec885623b1e1584ec6856021de055487681543b326e721d209106df8243d52a1c5b8b802611c8c998a260e0b5dc9389d658fe1fea3f58a4576840f9942308f7832c14f0988825704400004dbf1e05043e6cb5638072d32ba10b4ca98428507c0e8541d035d52300d3144c033b196a00746558018782868801118af37674289dd9b0a0b772827f63ee09f0766827bdfc6883a65ca20e40020000000676bd3151b982a5e6a590ec19605d36653174919485d1c651177619425d186502d5b8b0832c62bbec4d8aea087e24a8003883c76a80cac987825525fe0930000261f4c7854b4439b9f80cb27eed37e99544c3aacd0879043b50b27820e26195b1680fdb041a32c5002c32e0f0300003b289bf4cae195432a4987465a000521dd6268ecb0caa3b307640ec72919566843c821da8593b1843b0f0385913b386d4624289263b2615f5bee017621c4761a202091e6eb8247555a1d8d4cfa21099928025196467746588012658820d1fe6843832c00029fb69c4c195a6e0ccaf844032b610f8cac843d32ae10f20260849674a6f6865b9a18b56e2c20ecf8afbb9a62bd8cb18aef19762bb821f892a000032e137e995c32a8654930e8cb4000a43bac4d1d9619547660ec81d8e3b18acd087610f25232765021da8593c0c676ccad99c04c56220dfb6083000040000002883965a601ed972001819546d7465c8e02196234606568ca91d8c6d707689ab304462bcc6599b8d196e686076b99d1b56e2c22c4d8aea000e20f000026fd507ea0ed44ca61d50b298f0dbf1e051181062c27034e3019608800008ec636b8087cd969b7836543b44d59822315e76adc5791b8109886dfc2610000507ea0ed44ca8594c7906a4f021aa08b9e275d63f87fa2a5e0fa15311e018fd6291dda18a460cb0000c32b9e0243b0658174d994c0cb664e2e698b09b56e2c22c4d8aea000e20f0000261d0876a16531e10f210ea780c41cb2e40030001000000033b5e32a8db00cb91c0432cc6a88cad19529878eea8ec633983b445b0a83b1179062c2701b7f0971062425a1b78365506a0453b500114c087800082213658a16cde58cb73430a464cbe022315e6f054503a6fc3bb654bcee8261c3a243b5cce8af6d32876adc584589b15d4001c41e000010eaa16531e06573c0431c50eb875f3f7619a4a97834f566877ed37e1e008b9e275dc9389d68bce270a31189ad8bc62699c9d89a58d422661cfc899758fe1fe964b87c759a61e5164987835aa21d863f58a47900628ca41f8a1d8ffe285a45e8a08782a281c989997e43b0658174d994c5d66652577799465d5e65157b69943b9a62bd821f89690000196542caa6210ea987421d90f24c787804114b9183bd8a0e4450418909686de0d9541a8114e087800082213658a16c13aa91904ae4c40d09130f3b4e088c5799fba3bfe54b8eff1d8b32a56adc584589b15d4001c41e00004df8e49a35045e28c45179a2e7261d087643c9cfc393a50b298f032c88753c0068d553a19b63b3a160c871818321da05b8872816a,
  0x132a0ba6cca62eb33292bbbcca32eaf328abdb4ca18877327a000032b9fbb21e410ed4239e1f3b3f17084ce2c720ee31780325aa7432ff1f7850647fc13ee54bcd4b21d832c0ba38ca22eac328200004398657087643c8fdd9e1e062e54a8c9b3b3413de21c8002152d3c3654bce8c130f39d421d4e72c3b20c0c9874f0e1d9c3c2a54c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca00877327b734c584dab715e0088c45d000050767eed423a91821e410ec32c9e1d13acb1fc3fd392605bc4c40d0947eb148e21d000208733c2454b4f0d930f3b4e001c42543b20c0c9bf4f0c1d9c3c2a8760cb02e9b329821dcc9edcd316136adc57802231174000130ea83b52307eec21d90f2508e1964f0e06b38b8c26f152d8947723e0a5db8181b821c8001c97f1b75261a08d4878818a21de0624873818521da0584871815c6e3a757dc9c098b6dfc24ad52b06778bc2767e2e109a072367868985825226060938980824d73f0786498882de260e0b5c98282d621d607bc87481ee724e2759b85896558fe1fe963b07b558e41dc5648073e58e01cb55319afb2a5e6a5a3f58a458fc428a23ef0a0c8ff827de3ee09f010e4001043a8a4621ea66190ec19605d36653174919485d1c651175619415d18650043b8b05c2162c0c87b8afa2a660fadda103e6000054b6e6943b321e44c39423843b0cb27eecf0d9b75261a09889858261260a0978981825d25fe096c000130021d44c409832c7358e24c3832c9fbb21e410edc8d9e1a36ea4c0414c130304ba4c2c121b9793aece4784de391a1341171c359c5c30ceea96c4a3aa571256dc0c0dbb6ff03064388cfbb6fc121ea950e2d952f352d17004c247dc0e5c21c800208753424e464cc521d832c021dcc9e930d04a64bfc126000021d44c40983130458eeb1cd638930e0cb27eec879043b73f07864d103c15069854b0f0b152f352cecd8505bb9413faed504fb3b3413de21c800208753c2eba38ca22eec3284bab0ca0ae8c328021dcc9e82231174000137ea61d0cb2a0ecfdda84721e410ed48c1e1833744c4416f130505ac4c0c154130b04fe4c24137930104d64c34129b92713ace4fc4e0b97b1358e4ec4d2b9f9132eb1fc3fd2c970f8eb34c3ca2c930f06b5443b0c7eb148f200c519483f143b1ffc50b48bd14108760cb02e9b3298baccca4aeef328cbabcca2af6d3286000043aa6fd508e1964f0b9d9f8b8426822f0098b72360985c9c82342614718dcbc09928c42196555a891e880a160d44c9dc350b06dd898882de261e095497f824c19726f900021b4e000e2bb5c9389d673f2265d63f87fa5aa21d86c4d8b188fd6291645e8a0658e41dc5668074f59201cf9da103e44c3c0d6d33e03394c780ca13151afe50706a7de0a1a202a5464da3ef0a0c766c282e41e09fe772827f63fe09f776a827d9d9a09ef3b387854a979a96196e6860763998d43b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d77619425d5865057461940044622e800008732a58987548c283b4dfaa11c87906593f7610ecf0b1b0458fe1fe90ea87f68fd62915da103e44c546bf8a9519362a5a0d31e0a1a20196e686137e1e144c387490a979a2d766c282ddca09fd76a827d9d9a09ef10e4001043a9e1321c66898763998d43b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d77619425d586505746194010ee64f6d5b8af0044622e80001d9c50767eec879043b523019654239e153c226df8e57a83e0742a26019da8580654ece8513bb9413faed504fb152c3c249870e920ec7331aba48ca42eec3284bab0ca082231174001c42500004df821cd48c1d9c3f76a11c879043b50767850e6a47eb148eed0c5232e9b3298000043adab60cb2a11cece1e1337c832e0dc10004369c6554d06a622073e98781ada67c067298f0194152a326cece8513bb361416ee504febb5413ec54bcd4b0cb7343054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c32800000439843b21e454b130e80064df8784800390f1031443bc0c4b6fe1256a958ca9aa55121edbf4cfb90ed202e43ac80b10e9202a439c80a10e520263b48d7d3540116507a4266a67d3bc098f0d930ed5018ed70445b822000023b44f08021f3446b1fc3fd2c720ee2b1c0396a8980676a0e018cc7eb148b1f785063b9413fb1f704f83b3413de21c800210f715f421d45231b7d096c4c3ced510e3344c43d4cc321d832c0ba6cca62e8e3288bbb0ca12e8c3281734c5848877160b842c581dab715e0088c45d41880970ed081f315330660ed5019580002a5aa46142ca61d000c9bf0dbf8ec63b387eed423843b21e4784400390f1031443bc0c490ed02c2dc74eafb6fe1256a958ca9aa55121edbf4cfb90eb1fa043a47e790e71f9c43947e690f715f443d4cc35cd316120000768dab63b38b1cd6389fbb58fc4c39423843b21e44388f080c6f3f6e1954ecd85818808247a310065a5568763533e9a6800040000002883965c800606551b5d197238086568ca9523022ddae000c0044000047631b5c1da26acc1118af319666e3410f9b2d196e686076b99d1b56e2c22c4d8aea000e20f0000130e3f7643c941fa83b,
  0x191781d856a809968d40199c21e00025230770c21f8af904462bcd41d06755130195d42c064873f0095537e1d6d507067fae698b09b56e2c21c8f09b78b842671c8d099b8c40263a2f009878b80260163b07b558e41dc5668074f59201cf9638072d3f706ba553a1a1f3f6e2fc8fd78bee3f5a2fb6c4d8b128fc428a23ef0a0c907827f9dca09fd8ff827dddaa09f68fb827c1d9a09ef72f0091931e1d554c38741d33e1b93261c6d2c98899b443b0658174919485d1c65117b699435dd8650975619415d186502f779937000021cc21d1fba0cae78b8d6d5ab61612546c1a99529062c549c18a952506285484189151f062254741885cd23b4054bcd4b47de1418ecd8505c7fc13eeed504fb3b3413de21c800208753c58a460f1228463c56ba38ca22eac3282ba30ca00877327a0000fdd10f2087678b4c9a952d069a54ac1a5a6fc3bb654bcee83c15140e195800186593c4654c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1865b3270000148ca8473f7421d4f16032c54ea77cca9719352a5a0ca9daa09fb8ffa1cf8a959ce45922262e2f08648727208d942c9e004c7a759c65b9a184c38769131582dc4dfa0955c9389d68bce270a31189ad8bc6269a350899873f2265d63f87fa592e1f1d669879459261e0d6a887618b9e1bb5c9d82724c7e6fd4fdc1ae9261c684a3f58a477686291a4018a3276b628c641f8a1d772e28723ff8a1676ae285645e8a08782a281c43a00040cb0000c32b9e2a10e6788898899b443b06580a98995f2a46654174d994c5d66652577799465d5e65157b699435d58650443b993d0cb664e2e698b09b56e2bc011188f9000010ec8791fba508c78ace3192ff3522438cd133978131ab3403a78ec734b8ecd8508483c14051f7c3b7bb950676a264ebaaa57125676742bb130b04684c1c11913050462dbfceafb938130d0f1048bb71c122cb24039f2a7432ff1ff04fdbb550654087800082213bae54b0c9aa1d618e254ac1a5a8593c524c3cf1326fc3bb654bcee83b43148ced6c518bb971438ed5c50abc15140e21d000208733c444c44cda131332fc8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca08877327b734c584dab715e0088c47c8000508c10ec8791fba0cae78a83dac7e21458b1dc4dbbb3b0742e47cebb3978131aa0fc46bacd00e9ed39cd5ac83c1404ee5419d8ecf015c3b2c056289934ead400453285f0766a26c1c0021e00020884eeb952c326a54ac1a5a85b3796a464cbe3b43148ced6c518bb971438ed5c50abc15140e9bf0eed952f3ba09870e8921d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2af6d3286bbb0ca15ab715e0088c47c8000261c195c43aa8462620a164f14832a76a827ed42c88a68ffa1cf1a8080ae1d9c6bd553a9a781d8e6971d9b0a108fbe1dbcecd858f1daa029876980a51da2029076680a23b162e1152b892b890a2499a70089f6dfe060dbee0176043c00041109dd721c46b6141c1ad52a5864d559a875f2a560d2d52a1e2550b66f2d48c997c43ac31c5da18a4676b628c5dcb8a1c76ae285645e8a08782a281dc8c02284df87744a979dd04c387448fdc1ae92a62657c98999542a46654174d994c5d66652577799465d5e651574719445eda650d75619413f6e2fc8fda8bf13f662fc0fd88bef3f5e2fb8fd68bed3f562fb0fd48bebbdde2c2ae698b091db22bd2d5b8af0044623e4000065710eaa11821d9fba261e78984c0ac710e5d170031d283833f68760639153118c1842c585deef15fb734c57b043f122b1f743959315045a0000fdcb91943ae9bf4a97065754a878941a5952a00129bf0eed952f3ba054b41f3152107bc547c1d5152706f654941b4951d06ca54a41a4951b0684195800186593c46ed0c5233b5b1462ee5c50e3b57142af0545038874000821ccf111fbb3c4254c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca19533327c21dcc9e865b3271734c584dab715e0088c45d0000523043c821da8473c481fea3f58a4758fc275e2e706ee3f706ba49871a12262266d10ec19605d36653000008753f74a11c32c9e233b411f7850647fc13eeed504fb152f352cba38ca22eac32820000439843bb9a443c8fdd1e2203de43a8f0cb9f9132edc2c4b2ad510ec30ec8303131105bc4c3c16e130705ae4c1416b1d9c360922f4503392713acb1fc3fd3c1406969bf0ea30004369ca98cd7d800715db1fac522bb4207c898a8d7f1955341a32dccefd89b163098881cfa67c067298f0194261c062e9878e4d152a326cb1d83daac720ee287543b6ac700e5a54b41aea83b3c3a54bcd4b47e21450ece8513c7de1418ecd8505bb9413faed504fb47dc13e0ecd04f788720008196000188753c40195cf0fa1d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9e865b3271734c584dab715e0088c45d0000508ea460879043b3f767884d09131105bc4c3ced3b92713acb1fc3fd26fd3c2f1fac52386580006195cf0fa1d832c0ba6cca6065b32700000fdda84721e410ec43a9e20326a54b41f3152b06969bf0eed952f3ba0ed0c5233c15140e21d000208733c3c54c4caf9523,
  0x115e0088c45d28980676a16019500005072ee55daaa918508e9bf4a969e3f369a0014ceb996315de98ac16e1955341b626c589392713ab17383782622053e9878131930e00104c44e610cb734304c4c603deef15f8196c4ecaa6212cf0ec8303131504d24bfc12d800058fc4c18986130a26104c1098113003f76e47dc8d8657087a98754239d9d3c7c770d41d059d5130160d42c0576874c24b2202091e8788245d52b035f55680cf553a032c3b386665d9b0a0b772827f5daa09f621e46a5974719445dd865097561941044622e8000283910e654bd48c28474dfa10ecf1e9c933b326e708719a2c3b36758959a9c183f7466d09880c703b3a1818a9683e655680cf553a032c54a80c6ddca09fd76a827d9d9a09ef087e25a61d9896776860f9d5319e3b21ea661977619425d586505746194043aa31530858b0bbdde2c2ae698b09000010f5423dab63f7021cc32ca6fd2a5e78f000519611686657c5a1195d1682656459f9957167c655459e9953167832e0db9195b3380658c577d89b15d4001c444a62b371f17004c2391933144c1c16b9d9c18e1173c4ebb92713acb1fc3fd2c700e5a54b4195130f35d232dcd0c131133691fac522bb5413ed1f704f828593c709870e8e92ff385e7eece0b10f5330c8760cb02e9b3298bab0ca0ae8c3280875462a5cd31613842c581953307d6ed081f4000054c76ad8a97843d0cb27ee137ea84710e678eccc539181309170431a930705ae7ec8df2b92713ad1a844cc39f9132eb1fc3fd2d510ec31fac522c8bd140ced081f33c14069a54b06381d9d3c6ea460f1a12ff385ea0e0d4d2cd00e9eb24039f2c700e5a10f0001043b3c4443cce22843f15f320f04ff47fc13ef1f704f828983c6c7ee4f1a930f3c604c44cda10f5330c8760cb02e9b3298bdb4ca1aeec3284bab0ca0ae8c3280875462a610b16177bbc5855cd31612088c579800050b254bed5b284710e69bf4fdd06593c706629c8c09848b8218d498382d73f646f95c9389d68d422661cfc899758fe1fe96a8876159a01d3d648073e58e01cb63f58a45917a281a41e09fe8ff827de3ee09f076840fa1e0a19e6262266d10ec19605d3665317b699435dd8650975619415d1865015310967566824a21d90606890816440001d9d5232a11c21e952f10e69bf4fdd1fb8261c4bf832c9e3700104c2498b130326264c0498910ee3b0c438cd162b35069ef05450348bc0ec24c2cd47ad5013311a80332a62b371e4c34db89fb6342117004c2391933144c1c16b930505ad173c4ebb92713acb1fc3fd47eb148aed081f41faf3414a9884b3b75c12450ec830344050b064bfce179d9c18e0b1d83daac720ee2b24039f2c700e5aaad019e952d067610f0001043f15f31f8851447de1418ee504fec7fc13ef1f704f83b3413de10ecf11261c3a3a43cce229311336843d4cc3131332fc8760cb02e9b3298ba48ca42e8e3288bdb4ca1aeec3284bab0ca0ae8c32804c54c9ca1d518a9842c585deef1615734c584800051316ad8fdc28470cb221cd37e952f3f744c38f1b000721da6c0d315860421ce074c87781a321ca0678ecd1c936ec62561baf893c55760f1955b83823b3275c08719a261d8e6635dcd8a37772e286e42107d8907c1e5141d067521e24da966b09c859a426b22e109a072fc0aedcbd027f723609849851c6372f0264a3108657513278d148c9be58d422661cfc89975aa21d8645e8a0678280d3c87581ef21d207b959a1e2f3b3a722c97f9c2f50706a6a1d989676e162599639077159a01d3d638072d54c60fa0a9683e654ac0d7d55a033d54a80c6ca8f83110878000953a1a1f21ee2be821f8af9768629163f10a287674289e3ef0a0c766c282e41e09fe772827f5daa09f68fb827c1d9a09ef8fd41fea3fe073f3f66191021d9e224c3874748799c4521ea66190ec19605d366531779994a5d24652177799465d1c65117b699435dd8650975619415d1865010ea8c5443a231490e78c51439a31410e58c4f439231390e38c4d438a31310e18c4b262630189888bfcc2162c2ee698b09bdde2bf963f09d75920262a2e706ee3f7a19322f0064900007ee542ca8474dfa4c38fdd065910e76ad8a979e35372ad3b8479b540115a087800082213c66088c45d00005230a166d5b284750729bf544c9e34348c3b40ce69b7f09b26df426b8ed5018e3b1c0601b6f35e23b5cce8c2691170d70445b80000442a46137edab65072a16544c9e3333a0a0e82cea8980b067670d1ac3a61259101048f043a000410f4f1790e33458a9581afab35069eaad019ea838352aa9d0d0f843f15f2ecd8505bc15140cee504fec7fc13eeed504fb3b3413deb1c04c148bc0ec2e460114261c3a3a7ee0d74a1d832c0ba38ca22f6d3286bbb0ca12eac3282ba30ca05cd316136adc5782d50132ee7e012a8000261e7ee942388730cb254bc11126fd50b278c0cfb90eb32eadbf0caeaa6307d0aad019eaa740658a95018dbb43148aee504febb5413ececd04f7c7ea0ff4766c2c79d990b1a762c2c310f302fe438c0bb1d9d39168760cb02e9b3298bbb0ca12eac3282ba30ca02c7e13ae10fc49544851250df74493c5ce0ddc000159a1fb9508e21cca97a6fd0cb210f4f17858f3b34724cecc9b9c890a24a155a033d54a80c6cece9be021c668b159a99e62a5c65f1e0a8a06,
  0x1141920f04ff47fc13ef1f704f810f3333243d4cc321d832c0ba48ca42e8e3288bbb0ca12eac3282ba30ca01d9f15f7734c57b043f12544c4412b930f04aa4c3412992ff0498000159a1fbb08768750fdc291973f01966d5b08734dfa7670f299d9f8b8426822f0098b727208c5c8d9e1a26086dd4000130a26044c0087910ea3f7610ec988130e26184bf832cac735922b1c49831e523c324c1c16b930505ac000087910ea3f7610ec988130e73f0196563bac7358e2e498f2882342614718dcbc09927270262e31086598bc2192955a891d54ea2459bae816d6e3a05800001fbb08764c4098712fe0cb2b34564890eb3ca06710983198a72302610fd986448bc06aae2e09a103f5e682897f9c2f3f76793421e0002087e2be6e698b1c4c54222531e083c59a01d3d648073e58e01cb421d9a962a5c64d80030aea907827fa3fe09f78fb827c10ec19602a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd8650975619415d186500a968b1a2a562c60fdc8b1526222c50fdb8b13261e2c48ece8b1121e62c3ac4d0b08000021cc32cdab73c9c0c6d52a9ca5766827bc21f892a566a70615319c165d186500000043d4c5654bcece08730cb27eecf2699362a566bf9315998b2a62657ca9199505d36653175999495dde651975799455d1c65117b699435d1865000000cb6b56c54b0439865952329bf4a971e4a03e843c8f109fba342117004c2370b12ca10e80013919331410f44b39fb90ddd0ec8303131105bc4c1c16b9d9c3609173c4ebb92713acb1fc3fd21d50feca98cd7d9faf34151fac522bb4207c84c3c12a92ff04987edcdb9a62a35fc32dccefb9f9132eb5443b0a63c065054a8c9b48bd140cb24039f2c700e5a54b41a63c14344010fc57cbb361416ee504fec7fc13eeed504fb47dc13e0ecd04f788720008196000186573c9021d4f22952f3c868760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9e865b3271734c584dab715e0088c45d000052309bf54239e490c72a0e4f2145c01300b3403a7ac900e7cb1c0396c83c13fd1ff04fbc7dc13e021c80021fb83c8e21d4f22952f3c868760cb02eec3284bab0ca0ae8c328021dcc9e80005230a11d37e86573c9024421d285690874000821e9df754c66a808791a9f1d8e6a5e2e799fd566a67b0ece0c70262208a541c9e345130791963f87fa43aa1fd955a06593f7468423f58a453f5e1909da103e44c780ca09838232261a0898985822526120890982822226060884980822054a8716cfdb9b734c546bf8a951936723c26ddc8d099b8c402639cbc098d8bc0261dc9c09868b802601c8c097f58ec1ed5639077159a01d3d648073e58e01cb4a96834c50b07911e0a1a20196e686021f8af98fc428a23ef0a0c766c282e41e09fe772827f63fe09f776a827da3ee09f0766827bc439000410ea7914a979e434c38744887a998643b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d18650043b993db9a62c26d5b8af0044622e800006575230a11d37e9fb83c8e247a20285830874000821e9e3e3b3831c021f8af921ea661ae698b09b56e2bc011188b32622091c0002ab53f767ee0983130c26144c2098213022600e47dc8db9790caeb1f90ea261d2a58a11d44c1e46326a54b41f3152b0696ed0c5233c15140e54c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1800010ea9bf5423952e3c8a6f9065c1b7a00086d380038aed196e677ec4d8b184c3c0d6d33e03394c780ca0a9519362a5a0ca9d9b0a0b772827f5daa09f62a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd8650975619415d18650000008732a5ca11d42c1e44361898ac3021d9a39267664eb810e3344c4c3c12a8ec73610e7e44cbc3b312ceb5443b0aa6307d0a164f1c10f33332ed0c522c8bd140d1fa83fd1fbb0cd2f0501a7ab343c5e7674e45ac7e13ae1960001843c0004195cf21152d3c7e10ecf1ea83838aab3403a7ac900e7d173837746a10cccaad019eaa740658a95018d9fb83c8010fc57cc83c13fcee504fec7fc13eeed504fb3b3413de21c800208753c829870e8ea1d832c0ba6cca62f6d3286bbb0ca12eac3282ba30ca00877327a196cc9c21d518a9842c585deef1615734c584dab715e0088c45d00005230a11d37e952f3c8678d144c065750b01922d5b8af08c40263a2f00987044622e8000283959a2b244fdca918508e9bf432b9e4200061964f0b86573b98196cc9c000010ea54bd37ea8473c82770d41d02655130091d42c0238262031c0ece9e3e58fe1fea3f59b7b260e08c89868226261608949848224260a0888981822126020880fdd1e2e723c26ddc8d099b72f02635c9c0986723025fc32b00030cb278f021e00022a5a78fc21d9e3d5070715563b07b558e41dc5668074f59201cf9638072d54a80c6c21f8af98fc428a23ef0a0c907827f9dca09fd8ff827dddaa09f68fb827c1d9a09ef4c38747487a998643b0658174919485d1c651177619425d58650574619400cb664e10ea8c54c2162c2ef778b0ab9a62c26d5b8af0044622e80001fb82a5ea461423a6fd10e67900f1a5ab7,
  0x1328054ccc9f1d931725734c57b043f1238a9d448b130b0468dc280f7b71d02c0000043990eb3f764c38879043b72727671cbc86593cca6bf9315998b2a5464d937e1e632a5a798ad5b9e4e2a5e68b465b9a182a62657ca9199505d36653175999495dde651975799455d1c65117b699435d186500000291926147eec8713979261c1964879261d10e610ecf321e12000e212800010f24c3a21cc21d952c4df8798c18ca83904544c40e31bb3413de4bfc10fb9193a46ba30ca000002a5a21ccfdd865921e4438821da919261ce5e49851e6236b6a0f81d0a83a06baa26019da8580654a0e018cbb3a144eecd8505bb9413faed504fb3b3413de54b0f3028473c48ba48ca42e8e3288bbb0ca12eac3282ba30ca00000523043c930eb70b10e6e4e4ec91d9c08761966e6939794c567984d3aa85f11bca26c464b5070204d50c070a85b34803b18d11821e00020884f19a898048ea16011c283833f64c40cdd2a551220b5443b0c3a53a4f22f45031d9b0c08f0501a5a6fc3a8c0010da7000715db0ecc4b2ac7f0ff4a98cd7d9955341b626c58c47eb148a98881cfa61e06b699f019ca63c0650ed08f2d952a326cece8513bb361416ee504febb5413eca11cf12152f345a32dcd0c21d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c32803b6457a5ab715e0088c45d130904844c3411a930b04684c14118930304604c0411790e303d60000a9610f24c3adc2d31588733b24767021d8659b9a4e4e5cbca9183cc0776131e9d674cfa74e53159b5b000e212948c834d0440000537e9a20043e668de0a8a0691781d8542383e6507c0e8541d035d51300ced42c032a2a580024a959e5b196e68616a809988d4019a530e1d2c1daa417476990161da23f4076c8af404462bcd59a092889081634a8d83532a520c58a9383152a4a0c50a9083122a3e0c44a8e83103b300032d5b9e4e3b36751ca979c1650706a19da18a457674289dd9b0a0b772827f5daa09f6766827bc439000410ea291e3f507fa58fc275e2e706f03b2e15fceca857121c6057076b99d121ea66190ec19602a62657ca9199505d36653174919485d1c65117b699435dd8650975619415d186500a99993e10ee64f4ec98b923b222e44ec78b903b1a2e3cec58b8e3b3e2beee698af654c4259a2028921087e24721e2891a6e1407bdb8e8160000010f553a21d6556876708759fbb0cb243c89871e5c35fc98ac1f20000196ced08439952b3cb6718dcbc09928c42196498582347270262d55a89228bc21929bae9d8654ea6e8c8778b9d880a15f4ec685603b24749e1d209146dfa67dc0002a553b38766087910e23b347eec21e9310261c4bf832cdcd259a2b2448751e5a37306554d06996315df626c575000710b098ac29e26220a1e98fc277a61e09c66df8005c18e11b86df427134e7356b06284601b730a286dec27b8ecb0208d38cf04c1af11c4d41c470c1eb119a6de42759b7109cea17c1d9a89b07003b2406bbb5b1460ee5c50dc1ab118cd40c462c8020f8f20f83ca285b06deed5c50a2c961384b3484d6c5e60d87188834b47fe364ea9e84a8aab6127aa9d849ac4060b66dc880e4b71e032a765800610ec3a5276542bf1d8f0af676342bd1d930ac7101049143a51226dd74f2b9d913a50a954e4990eb32eaaad032caa740c946ddc29b9b750a6c3b3c093c620132517804c5c19711eed3bc47b2cd00e9eb24039f283e0742a0e81aea84739da32dcd0c1d9f15f66e0457abb3a144eecd8505c83c13fd1ff04fb92ff045c4c14111130304424c04110261c3a586dbcd78a1d832c0baccca4ae923290bbbcca32eaf328aba38ca22eec3284bab0ca0dab71635734c58bb9790482e4e4119130d044c4c2c11293090448e4601118000044254b4ece1d983b1443c887810e23b347eec21e930e0cb221cca9713073cb274a4ec98b9d3b1a2e688771d86b9a62bdc87b817521e205c0876816e21d605b40002ab554ea7670ecc10f221c4766821eb75d3cae08c8983198a7270262dc8c09848bc21910fd91be58b826840fd79a0a3f72199cfdb86652622095c987825525fe093000029198d40e7e032cacd15922b1c537e9fba3cac76808799c458fbc28323fe09f776a827d8fdd9e542a5e673d74719445d586506e698b092622095c98782550000875148cc6a073f01966d5b08734dfa10ecf2a891654e81929b8e816221dc761a2f0098b6eb8247555a0659727208c89831e528c40264898182d526020b51c931e5121d67941cbc9c632616662163b07b558e41dc5668074f59201cf9638072d21e605fc87181768fc428a23ef0a0c907827fa3fe09f78fb827c1bee892689081644ece1e5343b0658174919485d1c651177619425d586505746194021ee2beae698af6087e24a959a86693f72199c9888257261e0954986825325fe0930000043b43a8a46635039f80cb36ad8439a6fd3f767950ec79d9b0b1e76542bf1d990ae6764c2b81d910ade763c2b71d8d0adb12144934404123d0f1048baab40cb2a9d032513050444df700bb10e23a4718804c945e01316e4e4119391804464c18f29397938c64c2c16c930905b04c0c16a930105a8e498f2890eb3ca0b1d83daac720ee2b3403a7ac900e7cb1c0396952c18e11f8851447de,
  0x1124f173c377c5c60d69170833c45c00c78a9681d1aa5606bea9d01962a540636a0e0e0e2b353830a98ce0b21d318a6088c579bb3a144eecd8505bb5413ececd04f7952e3cd6766ceb10ed733a28760cb02e923290babcca2ae8e3288bab0ca0ae8c3281842c585deef1615734c584dab71611626c57500071112000021e930e2a5498a930e9d9d21e47eec43986593cdc03007631a236b8222d810f0001044222e213404d94df8759d31e1b3300006dfd48c28392a5e10f4ecea62a4c3a088942c9e6d3b869bf0eb3a63c3666088c45d283a06baa26019da8580654000148c28392a5e10f4ecea62a4c3aecdddcabb552a5a79b000082213bb098f4eb3a67d3a72087cd11a6fd34403b1ccc6a83e0742a0e81aebc150698a26019da8580654a0e018ca919364a54b0c9b022315e6ece8513bb361416ee504febb5413ececd04f7953132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca05cd316136adc584589b15d4001c4448000087a7674a95262a4c3a21cc32c952e3cd66e60caa9a0d32c62bbec4d8aea000e217d315853c4c44143d33f84fa4c3c138cdbf000b36fa1388dbc84e0831c23720c508c069c67825a739ab536ee14dcdba853636e6147cdbd84f736e213c876781271d96043c76480e2832e23dda7788f683de23a5aa388e883d62335aa188cc513e0f1144d83800440000410f99a3773628dddcb8a1b90841f6241f0794508e0f9941f03a150740d7542c032a50700c64a9600092a56796c65b9a1859ac272566909ad8c4c1b4a31106964c3874b076a905d1da640587688fd037022bd476c8af404462bcd55d0959556c24f620505e7880c16cca8d83532a520c58a9383152a4a0c50a9083122a3e0c44a8e83103b2c0032d5b9e4e3b36751ca979c1676862915d9d0a27766c282ddaa09f6766827bc439000410ea291e3f507fa58fc275e2e706f03b321600eca857e54c4259a20209220878000821d891d21c6057155a1e6936de6bc476b99d121e6666487a998643b06580a98995f2a46654174d994c5de6652974919485dde651974719445d58650574619402a6664f843b993d3b262e48ec88b913b1e2e40ec68b8f3b162e38ecf8afb087e2be6e698af76e1407bdbae816d6e3a058087b815b6df8054c0002c9121d64c38fdd86593b3879a8e6b261d0630a46412bbb3534c654a8c9ab9f9132eb5443b0952f067a54b419da89904904c40d093b43148ced6c518bb971438ed5c50ac8bd1410f054503bb94140421d0002087313fce5e44c8483d0e9eb344f33a1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeec328421dcc9e80005568b24487910eb261c1964fdd9d9c3cd274e4003884a0000987533ea6fc4c5479a0dcc1955341a658c577d89b15d4001c42c262b0a789888287a63f09de98782719b7e00166df42711b7b09c3063846e418a1180d38cf04b4e7356a6ddc29b9b750a6c6dcc28a1b7909d66dc42738ecf024e3b2c0820ec901af065c47bb4ef11ed06bc471350711c306ac4633503118aa17c1d982200002087ccd1bb5b146120083e3a84707cca0f81d0a85b06dea0e81aea858065454b0004952b3cb632dcd0c3b571428b2584e145e60d869870e9647fe364e3b5482e8ed3202c3b447e81b8115ea3b6457a022315e6a9e84a92a76126d0f282ecc3c60b4a546c1a99529062c549c18a952506285484189151f062254741881d9400196adcf271d9b3a8e54bce0b2838350ced0c522bb3a144eecd8505bb5413ececd04f78872000821d4523c7ea0ff4b1f84ebc5ce0de0765c2b91d993ae0a9884b343c41236a950489043c000410ec48b2a740c951780f3321d70e9b20f03a810e302b86dbcd788ed733a243d4cc321d832c054c4caf952332a0ba6cca62eb33292ba48ca42eaf328aba38ca22eac3282ba30ca01533327c21dcc9e9d93172476445c89d8f172076345c79d8b171c767c57ddcd315ece5e04c9043f1247188432cb70a03dedc740b036fc02a60001668ac9121e4aad0875930e3b387eec32c9e67099a99f4ef01b7e18df626c57500071094874c3fa1d9b0c0854ac1f2262a3ace9bf4d3ac1e8115c0878000a63c3c029870ef1822137570ecc4b2aa630de0a17c158a89b0508a16c13aa91904ae7edc5fddab715e1173c4ebb93f1382e5ec4d6393b134ae7e44cb822311f2b1fc3fd2c970f8eb34c3ca2c930f06b5443b0a898048ea16011c28473c404c40d0947eb148eed0c5234803146520fc50ec7ff142d22f45040874000821ccf32843a000410f4f2e0ed733a28760cb02e9b3298baccca4aeef328cbabcca2af6d328621dcc9edeef15fae4e04c5843f1238a9d432593150496dc280f780008bc0b2450eb2ab421d67671cbc86593f7643c89871e6600020884eec263d3ace99f4e9ca6fd3440087ccc70ec7331aa0f81d0a83a06baf0541a628980676a1601952838063254b0004952b35fc001c444a62b3cc2546c1a99529062c549c18a952506285484189151f0622547418829193cc832dcd0c0ed520ba3b4c80b0ed11fa03b6457a022315e6ece8513bb361416ee504febb5413ececd04f790e302b96adcf27261c3a4854bcd4b0ed733a243d4cc3153132be548cca82e923290ba38ca22eec3284bab0ca0ae8c,
  0x13b3079f552d06b38b8c26f1c8f829725fc6629c8c09848b82716d52b195354aa24521d29d273b2617fcec885fe26220b7898382d721d207b9c9389d68766259db85896658fe1fe876a80c73b3674d55319afb6dfa67de3f58a456b8222ddda103e608780008110000121d679a821d9e1136fc72bd4231b5b21c6689810f9a23000e212963b07b558e41dc5648073e58e01cb541f03a150740d7544c033b50b00ca941c03191d8e697137e9a2021ee2be821f8af98fc428a1d9d0a278fbc2831d9b0a0b772827f63fe09f776a827da3ee09f0766827bca979e7321ea66190ec19605d36653174919485d1c651177619425d5865057461940b9a62c26d5b8af0044622e9e0a834c000054b5315a61d523021cc98706593f7676708791e7e0018765c5d31d95174a763c5d11d8d1742767c57d90f03cf8762cca95cd31612000152daa573b2476408740ed43b3410f4dbf8ec621d47672d5b10f23b3079f400390ef173443b45ca10e7171043945c310f715f47630f3d90e3344c43d4cc35cd316120000ecc2a5b54ae7648ec810e81da8766821e9b7f1d8c43a8ece5ab621e443c0f3e057f3b2c0030eca8b983b1e2e54ecf8afb880a24848761e7a556a79e08719a263b16654ae698b09000076308780ed41d8d6ad8dbf90e854ae10f552d90ea21e47640ec91d983b347670f3d800721ca06e087381856e042531b7f0930875617321d385983b280030ec79e7921de05bcecf8afb21ee2be9bae8920556a79e0ecb9e7621c6689887a99863b16654ae698b09000043b076a0ec6b56c6dfcec81d923b307668ece1d8c54ae10f552d90e821e043c88751e7a000c3b4c8098ed11f9a3b3c7c40ecd1e883b2c7808ec91dda439000390e3344c43d45d990e717123b5c5bc90f715f5734c57c0ed915e8767c2e9c3aa0b920000ec790e821e043c887510ec21dc7672d5b1b7f1da83b18f3c800c3b1e2e6cec68b9a21dc7619bae0922880a79dcecb9e763b2a15c48768161878a2469b8e891954ea79d4ec599523b3e2bec0002ab521e0a96d52b90e821d410f487910e2b9a47640ec91d983b347670f3c000c3b3e1614ecc85803b2a15f8ec9857d3b2215f0ec7857b3b1a15e80001d963b347670ec544053cee001c87281b821ce061487a8bb721de2e7c87b8afab9a62be1b81094c6dfc24c21d585cd874e1664ecf8585880815fc00010ec21e0a96d52b90e8087a438887510f23b2e79d82bd1d8c3a53101049110ed032add74f2bb71f3634000153a90f23b20a95ee691d9821e010f4ec92ab53b3443a8ece10e23cea79bd41f03a150740d7544c033b50b00ca941c0319523279c8a9619367674289dd9b0a0b772827f5daa09f6766827bca979e733b3a79c0a959afe196e6860a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d186500000261d3f764c3843990f20cb298a8f3a19f76df8657487581ef21c605d8ecd9d623b326e71b8589666fba249d52a031b08780009d9a09ef087e24a959a9c1854c6705821d9a963b166549746194000007670fdd887321e41964a979e733314e4604c245c10c76a954f2d13073cb276642c690f102fa438c0bb44851250df74493ab350cd24c4412b92ff0498766cea2c6a11330e7e44cbad510ec210f00010220000210ecf3890eb3cd4087cdf4c8bd140cb3403a7ac900e7cb1c0396a83e0742f0501a6952c326c10fc57c822315e6ece8513c83c13fd1ff04fbc7dc13e07674f3821d832c054c4caf9d8b32a4548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca05cd316136adc584589b15d4001c44480002a5c54a930ea62a21e421ccfdd930e52321964f3919cc1d8e032c76880ba69c42301aa008b26a0022ae0c584e383d21334dbf1e0d8352781131e9d674c3e706c11000014cfa79a137e9e54043e6fa6350899873f2265d6a88761507c0e8544c033b50b00ca81118af37674289e45e8a06772827f5daa09f62a566bf865b9a181dae674541d196943b0658174919485eda650d77619425d5865050ea8c4a43a63126d5b8b08c2162c0ec4d8aea000e2224a99835278280d34000043b4c3a98a832c9fbb10e64c3887929192a5a43a8f388223260c7949c8c9d2326160b6498182d526020b508718176724c79448759e506fba249959a86692622095c986825325fe0932350899873f2265d6a88761917a281a242059178280d3548c1e6f507c0e8541d035d51300ced42c032a50700c64a9600092a5e6a5963b07b558e41dc5668074f59201cf9638072d2a360d4ca9483162a4e0c54a9283142a420c48a8f83112a3a0c4021d0002087e2be63f10a287674289e3ef0a0c766c282e41e09fe772827f63fe09f776a827da3ee09f0766827bc21e9e6e43b06580a98995f2a46654174919485d1c65117b699435dd8650975619415d186500a99993eb9a62c26d5b8b08b1362ba8003888900007674a95262a4c3a21ccfdd865921e44c38f381dd84c7a759c11000014cfa79a137e9dc3043e688c763998d044622e8000283f5076a26542ca8394c54987548c1e6f0f071ffc50a2c92134d1788343bb5606e2a9d849ab71e032a43b0d88371c12370f142bb28593cda6df8637a9190b22438c0bb1fb73699121449437dd,
  0x10cb664e2e698b0904462bced5b8af1000e20d5a7380f769c6032c76c80a969c0027c00010f23f7621cd30e26fc1d8e7a64e9e267d378298ac29e26220a1e98782719b7e0016001c41a9b770a6e6dc42841b8109ca6df42711b7b09c26de42701b7509bc6dcc26e9b6f09b6000131ec18f8316987137e41963d300551b7e015321d472a88761b1021e66665b8e091b00010f108712a55087a767130e2a753d2e214000200007ede6598cad8b3932aa2cd8001884b658e00e465b1ba84c5614f1321851b4c44143d31f84ef4c3c138cdbf000b36ee14de0cb88f7835e238942383e650be0ecdda18a4576b628c20d588c690041f1d42d836f8fd46beddab8a14592c270a2f306c354c46e123ff1b2721da2e6153d095254ec24da1e505d9878c1694eca000c3b3675150ec19603b16654974d994c5d6665257579945087e2be6e698af832c62bbec4d8aea54e82468ecf85783b3215ccecb85723b2615c0ec8856f3b1e15b8ec6856d36e21420dc084e536fa1388dbd84e136f21380dba84de36e61374db784db0000438a0c7c18b54aa10f4ece10f23f760884a9688730cb254b800343c53d2c1d8645e8a065aa026623500669782869707631a265668249dbee017621c474a88759e6a3b367514ece9ccb0878000821d9e940440000410f9bb250740d7544c033b2a5864d9648073e2a560c5d41c1aa63b3e2bec21f8af9766c282ddca09fd8ff827ddd9a09ef0cb0000ca979d180cae74150ec19602a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd8650975619415d18650032d9938b9a62c241118af3000043c8fdd88734c396ad89871e953918a11cf0ea9193a46a0e81ae90e3029e54b0c9b39181308dbf4488ac700e5b170431d952b062ea954e7b3b3614171f704f83b3413df0e902b5065800067670e92065739eea0e0d53152f352c8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1ae8c3280196cc9c0000261c43c8fdd822110e69870ecf043b3d281d8645e8a065aa0265dcfc1bdb7828697148c08b76b8003007631e9283142301a719e091d9e02b876480ab6a0022ae0d49e04260e08c931e81650440000410f9bb27270262dc8c09846e3a2461648073e58e01cb62f0864a878815dd41f03a150740d7544c033b50b00ca89879cea8b82716cfdd1a1f04462bcdd9d0a27766c282ddca09fd8ff827dddaa09f68fb827c152a890f08740008a979d1c087a732d41c1c9d3b3866650ec19605d24652174719445eda650d77619425d5865057461940b56e2c22c4d8aea087e247000388356dfa055c000261c2a5a21cc32ca6fc54e843ccf499d3b4c3c138c110000136fc72bc10f9a2304462bced5b8af237021394000418b4c38a0fd41da89950b2a0e537e0ec63d24783131e816521e47a40871815c6e3a246021d0002087a246a1e20577507c0e8541d035d51300ced42c032a50700c649868235261608d09838232260a08c49818230260208bcece1e8e261e7a34a9619367270262d648073e8bc21928a959e7f3f74687dd9d0a27766c282ddca09fd8ff827dddaa09f6766827bc32c00030cae7a250ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d77619425d58650574619400cb664e021f891c000021cd37e2a742a5c9874f489e1c508c6d6d48c9e6272f07a3d3151e742a587848003884a0000438821d930e4c3aa0fd41da89950b2a0e4986130a260c4c1098113003f7621cc32ca6fc21e47a40f46131104904c2c12192ff047a0000879043b51324c30983130426044c00fdd88730cb29bf1cbc1e8f02b84388f2d1d9b3a8a7664dce371d123210f00012a5438b610ecdbac5c01308acd4334931104544bfc10f90eb3cd4e464dedc6a11330e7e44cbad510ec24c3411a930b04684c1c119130504624c0c1181301045e4c3cf46c8bd140ce4e04c5ac720ee2b3403a7ac900e7cb1c0396c5e10c94f0501a6a8380632a460f45952f3ce67ee8d0fc7de141920f04ff47fc13eeed504fb47dc13e0ecd04f790f333328760cb02e8e3288bdb4ca1aeec3284bab0ca0ae8c3281734c57b043f1238000130e952d10e6196537e2a743b387a3800000053a9c000cced195533b2987cecf0cbb15dd626c5750007109498f011b00004c3a54b5c9c88734df84c3cf469cf458e41dc5668074f58e01cb63ef0a0c907827fa3ee09f0261e768d0ec19605d1c651177619425d186500000131025fc43c8986130a260c4c1098113003f7621cc32ca6fc08767a30522c7ea0ff4ed081f32c7e13aca11847bc1960a78e49816e022000024c38f3f262a3cde6df8e57821f3446a0f81d0a83a06baa26019da8580654a0e018c8ec734b8ece8513bb361416ee504febb5413ececd04f790f333328760cb02e9b3298ba48ca42e8e3288bbb0ca12eac3282ba30ca002231174f0541a600003b389874a969fbb10e6196548c1e8b3bc0001c425267c067298f0194261c062e0001dcabb55766a9bf0a959e8a13ee21c800208753bb71ff4cbfaeac328221dcc9e80000cae9bf0a972a743d127780003884a4cf80ce531e03280000987537e3b9576aa54acf3f800721ca06e0877818921ce061487681616e3a757c8788ba76e042531b7f09308756173a1d3859a,
  0x10654a0e018c86580006195cf52152b3cfeece8513bb361416ee504febb5413ececd04f7b7dd02fc9bf4f51261c39967670cccae9b3298ba48ca42e8e3288bbb0ca12eac3282ba30ca0065b3271734c58b8000087a43cca97152d3f7621ccf528a458fd41fe9da103e658fc730942308f7832c14f011000014c5479bcdbf1caf043e688c763998d52327a8c988198a25fe096c9838232261e7a35c8d099b72702619c8c097f58e41dc5648073e58e01cb541f03a150740d7544c033b50b00ca941c03192a5679fc1118af37674289e3ef0a0c766c282ddca09fd8ff827dddaa09f68fb827c1d9a09ef4c38732d0ec19605d36653174919485d1c651177619425d5865057461940b56e2c22c4d8aea000e212800037dc4df821cc21e9d9d2a5a7eec32b9ea43740b540d8b2b34125112102c880002622195ca9537dc087a7674fdda9193d4608c8983199e73f22659c9c0986723025fd6a887610cac000c32c9b25917a2819648073e58e01cb548c034c782868801118af3766c282ddca09fd8ff827dddaa09f68fb827c1d9a09ef8d4019a4ece199943b0658174719445eda650d77619425d58650574619400cb664e2d5b8b1ab9a62bdd59a092721ee0609bee017f000021cc21e90f32a5c54b4fdda6fd3d447a8130e9a18000032dcf50817f21e47a55bee8927566a19a4987825508780008fdd1e5608767956350899873f2265d6a8876143aa312a45e8a0652300d31e0a1a202a5864d9668074f59201cf9638072d2a560c5d37e1e9d087e2be41118af3766c282e41e09fe772827f63fe09f776a827da3ee09f0766827bc43900040cb0000c43a9e9f2a5e747432b9d1243b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d77619425d586505746194010ee64f432d9938c2162c2ef778b0ab9a62c26d5b8b08b1362ba8003883500009870f500c7043aa1d74fdc86672622095d48c1cd68d422661cfc89975aa21d84a969cf23b3a739645e8a080cb0000cfdd1e9e2a5e745c32b9d1221ea66190ec19605eda650c32d9938b56e2c22c4d8aea000e20d4000261c10ea7a7ce4baa5535b010e800128473c267674e72843d398aa0e0e379fb835d24c38d09043f15f2196000190e33a4054bce8a06573a244c44cda065b3271734c584dab71611626c5750007106a000043aa61c3f747a78e499d990ae70f10f4b9d9b3aa87674e65aab40e9aa950395843c0004438ce90043b399aa9d0d0fa1d618e210fc57cc83c13fd1ff04fbbb5413ed1f704f81fbb3d3854bce8e931332fcbbb0ca12eac3282ba30ca05cd316136adc584589b15d4001c41a80004c389bf04399e9d11ef0658f4c2847395b063846e34e701ee3b18f49418a118098f00b202200002dc7048b021f1176a0f81d0a83a06baa26019da8580654a9d0f49952c326c10e8001152b3d144c3ce75043d3996a0e0d531d9c333210fc57c822315e6ece8513bb361416ee504febb5413ececd04f786580006d38cf4d90f23d3454bce8c06573a0a54c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c3280196cc9c5cd316136adc584589b15d4001c41a800010e6987137e1fbb3d3826822e186777236096c97f1ced508c722552b892b523222e613484d84cf813349868226261608949848224260a0888981822126020881b7f818b4c3e74ecdbf1b5c723026120f408b251300ced42c032a8b82716ca96193654aa243d41d08be58e41dc5638072d0874000811000012a567a289879cea087a732c10f9cbc50706a98ece1999087e2be63ef0a0c772827f5daa09f68fb827c1d9a09ef6dfa055c32c000321e47a69ae09d382a5e746032b9d056a826be90ec19602a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd8650975619415d18650032d9938b9a62c241118af3b56e2bc476c80d51daa034876980d11da2034076380cb00007eec439a61c4df8d38cf4d8a148ffc1e0ddab036f5924269542d08c6835413bdc9d02734c7c21559730041000800000019ce619686f1131e1b2636fa135c76a80a61da2029133e19e369c0229213484d8831212dd30f9d3b36fc72bd41f03a150740d7544c033b50b00ca8a96193604400004a959d9c043e72f141c1aa604462bcdd9d0a27766c282ddca09fd76a827d9d9a09ef0cb0000c7639e99261c7a54a979d180cae74150ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d77619425d58650574619400cb664e2d5b8b08b1362ba8003883500007eec439a61c4df843c8f4d01ef21d467ddb7e195d6e1625995319afb8fd62915da103e6508c23de0cb1e984c7808d9c9c098b8bc2192953a9e97878a7a5887181763b326e71bee8927566a19a63508998831c23720c508c05aa21d841100001917a281810f88bb507c0e8541d035d3b36751552a1c5b78286970a9619368b802611648073e58e01cb421e00022a56767021d9d243b3a73a821f8af97674289dd9b0a0b772827f63fe09f776a827da3ee09f0766827bdc8c82270cb0000c9871e952a5e746032b9d0543b06580a98995f3b166548a9199505d36653175999495d24652177799465d5e651574719445eda650d77619425d5865057461940,
  0x110e627f541d835e766e7abd0ec19605d36653175999495dde651975799455dd8650843b993d0cb664e011188b3772a0cec000043b2a5a7eed44c1eb13b569878d98930e3424e4684d02c720ee2a11c1f313113d56ed0c52347de14201960001a61c3d3e195ceeda1d832c0ba6cca62e8e3288196cc9c45c30ceea0ec1af0000766c9bf043a952d3f76a958f5802364c7a759dc9c098b8bc2192931582dc261c684898899a754ea245e1e285763b387ab9648073e8ff827eddaa832a724e275942c88a60cb0000c32b9ddb6a02673076880d04dfa7ab5a7108bb58fe1fe9668074f043c00041109dd71d8e69723f58a4776862919dad8a31772e2871dab8a15782a281e41e0a0210e8001043989fd4c387a8076b99d143b0658174d994c5d66652577799465d5e65157b699435dd8650975619410cb664e043b8b05c2162c0ed5b8af0044622cca99836350740d75dca833b0000a26021d952d3f76ecdcf57816221dc7619bae091d6e38245955a065954e8669e310099272f2091c9881a120cb0000c32b9ddb261e76a88719a2621e6666432d99380000b24542c0ec64df8b34443aa89808776ad8fdd9d9c3d5c663942c032a1daa029876980a51da202907639a5c766c2841daa09fb69c0227e3ef8771507067ea3fe997f58e626722e186772a5e6b29e0a8a0754ae24ad53a891654aa243db7f81896e3a0589b7e815510e800108771ea910e627f432b00030cb27ab076b99d143b0658174719445eda650d77619425d58650443b993d0cb664e2e698b091db22bd2d5b8af0044622cddca833b0000087d44c043b2a5a7eed37e9ead13f71ff439f3b550654b244cd3a859331c3b1ccc6a83a06ba3b4c0528ed10148ecd8f55b4e0113f170c33ba83833f43b5482faa571256a9d448b2a55121e76742c1952f067cdbfc0c4b71d02c4dbf40aa90ee3b0d101048f375c123aaad032cc6201324e5e4123931033744c1416b130305504c2c13f930904de4c04135930d04a6e49c4eb393f1382e5ec4d6393b134ae7e44cbac7f0ff4b25c3e3acd30f28b24c3c1ad510ec2b3403a7821e00020884eeba91933c11fac523bb43148d200c5193b5b146320fc50ebb9714391ffc50b3b57142b22f45043c15140f20f05010874000821cc4fe90f302fe438c0bb37dd3d543b5cce890f5330c8760cb02e9b3298baccca4aeef328cbabcca2af6d3286bbb0ca12eac328221dcc9edcd316123b6457a5ab715e0088c459bb950676000137ea898087654b4fdd86593d5828423ef877110e800104398a0b58e62681c8d826543b06581747194410ee64f541d835e0001170898886592a5aecd8f5589a058e41dc5c8d82658fbc28422e1867750760d79d9b9a5c1d8c689952b892b6dfe060c8711d8621e66664ece858388082479bae091d55681966310099272f2091c98819ba260a0b5898182a8261609fc984826f260209ac9868253724e2759c9f89c172f626b1c9d89a573f2265d63f87fa592e1f1d669879459261e0d6a8876159a01d3e3f58a47900628ca41f8a1d8ffe285a45e8a08782a281e41e0a0210e8001043989fd0cb0000c32b9ea943b0658174d994c5d66652577799465d5e651574719445eda650d776194210ee64f432d9938b56e2bc011188b3772a0cec877817c00009bf544c043b2a5a7eedbee9eaa0ee31f785082c731339170c33bbb3734b83b18d132a571256dbfc0c190e23b0c43ccccc9d9d0b07101048f375c123aaad032cc620131cb3403a7bc15140f20f05010874000821cc4fea1d832c0ba38ca22f6d3286bbb0ca10877327b6adc57802231166ee5419d800021dca26021d952d3f76195cf54874f90782809668898d772a0ced44c9d7572f2718c9858234260e08c8982823172702619648073e8ff827eddaa832a50b278a4987825525fe09309889d7473f2265a35006690cac000c32c99ef5668249dbee017f4df87a9d6a88761508e0f9810f00010442775c1118af376862919dad8a31772e2871dab8a15917a2821e0a8a0710e800104399ea543b0658174d994c5d66652577799465d5e65157b699435dd86509756194110ee64f432d9938b56e2c6ae698b17000043cca97152d3f7610f4f5408a08312724141c1c0d36fe1334dbb84c9727208d89871deb83d022b9dca033c51307a99bae81714cfa69a1b8e81640004000131e9df754c66a800029a6e8b9e275dc9389d68bce270a31189ad72f626b22f189a68d42266159a892958fe1fe964b87c759a61e5164987835aa21d862428590508e0f9942f83b351360e0142d836f52320d3432c00030cae776e3f58a477686291a4018a3276b628c641f8a1d772e28723ff8a1676ae285645e8a08782a281c871817621ee056db7e015810e800104399ea54c38732cece199943b0658174d994c5d66652577799465d5e65157b6994310ee64f432d9938b9a62c26d5b8b08b1362ba8003884a6fba05f8000021f087a43cca97152d3f769bf0f539ae258fe1fe964b87c759a61e5164987835aa21d85668074f8fd6291e4018a32907e28763ff8a16917a282241e0a0243b0658174d994c5d66652577799465d5e65157b699435dd86509dca833b0000dd7133e0875087a7674a969fbb51307a98522bb4207cca118dadc7ea35f6a9884b3370a03e898a8f35a919364aa0f81d0a83a06baa26019da858,
  0x10c7717084ce4620131d17804c3c5c01300e4604bfac720ee2b3403a7ac900e7cb1c0396930704a07ee45fe1faf17ee10fc57cc7de141920f04ff47fc13ef1f704f83b3413dee7e012b952d3d704c40da5a1d832c0ba38ca22f6d3286bbb0ca12eac3282ba30ca05eef326f734c58b8000087aa464fdd930e10e69bf432b9ec00b1e7668e499d9d37aa7664dce10e3345854b8c9b043f125512144942b350cd31a84f5b2d51374054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca05cd3162ea95031d8000556aa9d4fd71306262254b22e1c5c17232195c21ea9193f76ecd537e952a3d7e7aed48c1eba5074099544c024750b008e021e000208767af0988198a54ac0d7d55a033d54e80cb097f825b260e08c89868226261608949848224260a08889818221260208809879ebd5070714952a1c202a5c64d9c8f09b77234266dcbc098d72702619c8c097f58ec1ed5639077159a01d3d648073e58e01cb4a959e7f087e2be63f10a288fbc2831d9b0a0b907827f9dca09fd8ff827dddaa09f68fb827c0a969eb84c3874150ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d77619425d5865057461940b9a62c26d5b8b08b1362ba8003884a0000195c4399fbb4df87af8eb6a61c37829878131a67c048a98f011b00004df8e47dc8db97972724c3cf5e81644c7a778130e1d1d4cf86e188791a966e382458003884a000054bd37e152c556aa9d4439843b3d7824a159a8669890816463509eb63b387ad49881b4bb56e2c22c4d8aea000e21280002919261ca0eca9526fc0cae21ccfdd843d3d767ad4ece9cc2508c23de0cb053c0878000821d9eb94c5479bcdbf1caf58fe70d8a971936087e2be541f02a104400004a969eb84c3874149881b4b043e688c763998d2a62657ca9199505d36653175999495dde651975799455d1c65117b699435d186502e698b09b56e2bc011188ba0000a46142ca8995072a9d552baab550764c38a9526fc10e64c18986130a26104c109811fbb723ee46c32b93003d74771530e1d184cf86e1800029185076a0e4a97aa57556aa9d44399fbb08767ae4df20cb837040010da71955341a98880dfa61e031699f00b8a63c02c843c8eafb702128edbf8495b75c123adc7048b043a000410f4f5b930f3d1a54acf3f800710949bf4f5a2a5a0d66a95833baab40cb2a9d03251faf0c844c1c1191301044117184dc391e136f17084ce391a133718804c745e0130ee4e04c345c01300e4604bfac760f6ab1c83b8acd00e9eb24039f2c700e5aa0f81d0a83a06baa26019da8580654a0e018c843f15f31f885143b3a144f1f785063b36141720f04ff3b9413fb1ff04fbbb5413ed1f704f83b3413de32dcf50a61c3a0a8760cb02e923290ba38ca22eec3284bab0ca0ae8c3281734c58b80000cae21ccfdd952d3d7029163f507fa76840f9963f1cc2508c23de0cb053c044000053151e6f36fc72bc10f9a231d8e663548c9eb68d4019a559a09276fb87a901118af33b387ad530e1d0526206d2d0ec19605d366532d5b8b08b1362ba8003884a00004c38a9526fc507ea0ed44ca859507254b49831300723ee46c32b88733f7610f4f5b9ba05aa02659cfc025700011a84988952a0cae7eed48c9eb6132ce7e012bad513740a460cc6c6a00cd23b18d132b34124edf700bb10e23ae44c40da58000087a4c38a9526fcb56ca0ec32b88733f767670f5a817621c4724dbee89273b36163c21e00020876767cecc9b9c21e666662429989566a19a4fdc86673b3a6f5635089965aa21d85cfc199e917a2819e0a034d5230770c21f8af904462bcd0ec19605eda650ed5b8b1ab9a62c5e2f0064b54a818ec000283b5132a16541c952d556aa9d4fd713068b871705c8c865710e67eed37e9eb41338b1c83b8c5c33b3e43cccccc7de142076742bb3b3734b90f1048bc5e00c963b18d3d2a7432ff1ff04fdbb550654a164d3aa85f0766a26c1c0285b06dea4641a6952b0696a11cf22a6fc3bb654bcee83b5b1462ee5c50e3b57142af054503865600061964f5928983d629870f4fa1d832c0baccca4aeef328cbabcca2ae8e3288bdb4ca1aeac3282196cc9c5ab71634000021d952d3f7621d4f599df354e877bca971ddf50b269c6c4d8aea000e20f137e1deb4c7a77889880008261e779963907718fbc2841d9b835d507622eda719e0954c61bc153b8687260e0b5c98282d626060aa0985827f261209bc980826b261a094c97f824c1d9e02e476480b68b9e275dc9389d6727e2705cbd89ac8bc62699c9d89a573f2265daa008ad58fe1fe964b87c759a61e5164987835aa21d8542383e650be0ecd44d838050b60dbd48c834d043c00041109dd704462bce3f58a477686291a4018a3276b628c641f8a1d772e28723ff8a1676ae285645e8a08782a281c65b9ea14c387a7c989997e43b0658174d994c5d66652577799465d5e651574719445eda650c98a9939b56e2c680000875513254b4fdd86593d64264a310865972f2091c9881a12556a24749879da76eba761887999993b3a1674877818921c6060c32c00030cae776e1d3092c6dfc24ad52b1eb04dfa7ab5668074f043c00041109dd776862919dad8a31772e2871dab8a1590782809e0a834c10e8001148c9969,
  0x12a660cc1daa032d00004c4032ca61e5130a0e952baa7550b054bed5b152c10e610f4f6c018b21e4757db7f09306e38246e1d3859d878a15d8000043d4c3ca0e952baa7550b07674f6b9d5f6dfc24c1b8e091b874e16761e2857608780008ece1e73087668b48719a2c21e665c5d9a09ef087e24a959a9c185d18650000006594c3ca0e952baa7550b054bc439a6fd3f767b58f678cb937c80010da71955341a98881cfa61e06b699f019ca63c065098a8d7f000715daece8513bb361416ee504febb5413ec32dcf50a61c3d40ba48ca42e8e3288bbb0ca12eac3283626c58c00005072a460439a6fd2a567b4cf678cb937c80010da7000715da6554d06d89b163098881cfa61e06b699f019ca63c065098a8d7f283833f654a8c9b152f063654b4f653b3a144eecd8505bb9413faed504fb3b3413de32dcf50a61c3d4054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c3281734c57b043f122a000148c08734dfaa950f6909a08b8619ddc8d82655076663552b892b6dfe060c7631a9e21c46a748799999262031c10ea87293f7218e4ece856950727b3c65c9be400086d380038aed54c66beccaa9a0db1362c623f58a454c440e7d30f035b4cf80ce531e03287684796d3151afe2a5464d963907712a5a7b29d9d0a278fbc2831d9b0a0b772827f5daa09f6766827be3ee072e21e2055865b9ea14c387a8087a998643b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d186502e698b09b56e2bc1638098387482441b7e090f044622e952a063b000054ba2e0930e10e69bf548c043b3f761964f68196632b63215fb70850658e00ccdbb1c9019546d806598d51195a32a4dbf84c3835222a1a8000aa50b27b347631db58310228010f000104427b394239e49196e677c76b99d1b56e2bc0cb18aef044622e80000cb8000a6551315d89a4c3e98f548c26fd50727b3c45241893920d384d7b9b770a6e3b3c0938ecd024c3b44d23419711eed3bc47b1b7f09b26df426b8ed5018e3b1c06028473c926dbcd788ed915e96adc5780223117509a445c35c1116e000141ca9184dfa0884f6704d936fc724213488b636ee12f9ae000c01d8c688e0d408a783102280000021f5072a16548c26fd3d9a19663100992556a247a202858372f2091c00028982622767432cacd108767eecf659dc3044622e941d035d51300ced42c032a50700c640002918766eee55daabb354dfa54b4f65092a566a19a421f000208767b223509ec6087a7b0c0001fbb261c21cd37ea9193d92265d6a8876173f079510ea8c4a917a2818a961e4a782865f2d5b9e4e2a5e673c32c00030cae7b1c65b9ea143b065817b699430cb664e30858b0bbdde2c2ae698af6087e24a959a866900011a80fdd88734dfa10ed48c9ec80b227670cccc485124cdf700bf90f23c3cacd433480008d4010ed48c9fbb10e69bf432b9ec704644c18ccf39f9132ce4e04c3391812fe195800186591330b5443b0ac900e7cb1c0396c8bd140d1ff04fbc7dc13e0f050cf321d832c0bdb4ca1aeac3282ba30ca0065b15ff7bbc57f1fbd0cd4acd033400008d427eed37e8873261ca464f631bd53b386664fd78642260e08c88791d9f54e865fe2e1099c8bc0261dc9c0986723025fd6a887610cac000c32c9e4ab56e6b6a45e8a0658e41dc5648073e58e01cb4a8d83532a520c58a9383152a4a0c50a9083122a3e0c44a8e8310782865f23ef0a0c766c282e3fe09f78fb827c1d9a09ef2a5e7b1065b9ea143b0658174719445eda650d75619415d18650032d8affbdde2bf821f892a566a19a4fde863d00011704a96043b52327eec439a6fd8d407b142c89d9c3333121449337dc02fe43c8d4b2b350cd2000235045c10876a464fdd88734dfa54bcf6205913b38724cecc9b9c21c668b2242892855680cf553a032c54a80c6cecd9d62566a7060a971936087e2be5dca09fd76a827d9d9a09ef0cb0000ca969ec22a567b0432b9ec02a62657ca9199505d36653175999495dde651975799455d1c65117b699435dd8650975619415d18650032d9938b9a62c5c00029193f764c38439a6fd087a7b0c4c245c10c76a954f2d3919331443acf3513073cb276742c89d990b1a762c2c3152f069c43cc0bf90f102fa438c0bb44851250df74493ab350cd24c4412b92ff04980880000821f37d31a844cc39f9132eb5443b0acd00e9eb24039f2c700e5aa0f81d09d9b3ac4088c579bb3a144f22f4503483c13fd1ff04fbc7dc13e0196000186573d708760cb02e923290bdb4ca1aeec3284bab0ca0ae8c3280196cc9c5ab71635734c58bbc14069a000021ea9193f764c38439a6fd2a5a7b084c245c10c76a954e52b9193314a98c3781d9d0b224c1c16bc5cf13aee49c4eb44851250b1fc3fd2b350cd24c4412b92ff04991fac522c6a11330e7e44cbad510ec2b1c0396bb423cb698a8d7f043f15f322f450347dc13e0196000186573d8032dcf50a1d832c0ba6cca62f6d3286ba30ca0065b3271734c58bbc140696000021ea9193f764c38439a6fd2a567b040bb10e23926df74493ab350cd2766c2c79d990b1a7674deac48533131a844cb2d510ec322f45033c14069654a8f5faab40cb2a9d03252a54,
  0x126207ba963907718fbc2841d9b9c9a507622f20c584e336fc7240dbb8b5b59a01d3c7671af590782809648073e772a0cec76a80a61da6029476880a41d9a028944c9a668ff827ee0c408a069c0227d42f83b376aa0ca810f0001508e79141109dd750b66f2d44d9b66523265f0a96193558fe1fe964b87c759a61e516a887612a560d2d53a1ee82a5e7b9e3f58a477686291a4018a3276b628c641f8a1d772e28723ff8a1676ae285645e8a08782a281c43a000410e67b9887b8afa087e2be4002000000067b9487a998643b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d77619425d58650443b993d0cb664e2e698b091db22bd2d5b8af0044622b000388510000a0e476328584dfa9878f759c63261e098c97f825b261608d1c8d099b72f02635c9c09860cac000c32c9ee90cb664e00002c7359a2b24443aa61e4dfa4c40f750761917a28216a8099773f009549871a1243b065817b6994300004c4043aa6fd0cb27ba412a930e34244c44cd3b9f9132eb24039f06580006195ccbfc7fc13f6ed54195152c326ab5443b0952b069722f45043c15140e54bcf73a1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac3282196cc9c000010eaa16137eaa743dd009549871a1273f2265d6a88761262277be45e8a080cb0000d53a9df60cae77310ec19605eda650c32d9938000021d542c26fd2a5e7b9c2719b7e39206ddc5adc18a1178a0e8f6c8ece35eaa264d18152e326c54ac1ad952d06543b540530ed3014a3b440520ecd0144ecd8505bb5413ed062045034e0113e087800082213dc854c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bab0ca0ae8c32803b6457a5ab715e0088c4560000000a987941c8ec650b09bf44399ee6002c32e0cedbf6c1060cb10417995b087c32cc0170cb1005a32b40158cb73d429870f50404c108ace90422000000069bf4f7299dd196201f8655801865a6221997288394c5614f131e84c336fc72420c408a469c26d8cdbb85371d9e049c7668126832e23dda7788f6508e6de8cad8447196600dc656803419727b8065b9ea14c387a8076c8af4b56e2bc065d8aeeb1362ba811188ac835222a800388517ede213d963884e000098781108ec65072a16043980053dc800000029ee0000676bc65c1b7a508c7b8465b9ea14c387a800038aed0001626876329195072a160439a61f3dc6000410f88bb044622b011088a969c6032da8000aa0000a0ed42c0ec73dc400606551b5365ca20e5315853c4c7a130cdbf1c908310229065c9ee069c26d8cdbb85371d9e049c7668126000800000019daf832e23dda7788f6835222a81100001043e7b7d30e1ea01db22bd2d5b8af0000e2bb411188ac0000a11ac4d261f5232a0e542c0ec63dc20028cb08b4332be2d08cae8b4132b62d00cac8b3f32ae2cf8caa8b3d32a62cf0cb18aefb1362bac65d8032674800c4000000519727b800530ed43a70d70045a34e0113e000010fa83952323b607631edf0a1e988cdccc18e11b0a0f82e8a61e09c66df8637c3aa12987edc332930f04aadc0c0db90e23620658c577d89b15d51a844cc39f9132e001c444ad510ec243b40bd86580006195cf6e262b3b6aa164d118ec7331b22f450337dc1253062845e283a0b3af0501a7821e0002acd0f6e952b3da60884f672838389d0e984981d9b0b1e21c800228473c86dbfceafa61c398821d4e248ed733a28760cb02f6d3286196cc9c21d318a621dc582e10b16076adc5780223117512142c81533063ea95018d80006e3a7674879043d54b6a95d55aaa752a5eecd537ea9183dbc68c0763998d5074167544c0583874c24c220209226eba05b9b7f9d5f21d86c41b8e091b878a15d876a80a61da6029542c9ecd3b38724da70089f3b36163c10f000104427b38ecc9b9c21c668b2e698af61db22bd2d5b8af0087e24aa2428928044622e800010f2087aa95d55aaa752a5ea0e552aa918766a9bf559a1edd3d9e32e4df2262a37300010da7196315de001c5769955341b626c5892622053e9878131a67c37264c38cc512ff04b64c4411c1307046498f0d35391e136ee4684cdb938130ce4604bfac760f6ab1c83b8ac900e7cb1c0396c7e214511f7850647fc13ef1f704f80cb73d429870e83a1d832c0ba48ca42e8e3288bab0ca0ae8c3280000142c2839523021cd37e86573db80954987198a73f2265a350066925fe096c9888238260e08c8fdd1e2e7234266dc9c0986723025fc32b00030cb267bc21d891758e41dc56a8876159201cf9638072d54e80cb23ef0a0c917a281a3fe09f776a827da3ee09f0878a15d9e0a034f3b3866650ec19605d1c65117b699435d58650574619400cb664e2e698af75668249c87b81826fb805fc000043d50b054bc439a6fd21e67b6cccc9d9d0aec43c8d4b43c4122e000153aa8582a5e21cc21d9eda031643c8cba36fe125610e8001043d3db04c44cda1fbb3daca9581afaa740658a95018d90f715f410fc57cbb361416ed504fb3b3413de196000186573668ba38ca22eac3282ba30ca0065b3271734c584dab715e0088c45600005130a0e942c152f2a5821cd37ea61e3db272362e186758c42195e2f086483f7031c0ece9ed721ea66190ea8c54b9a62c270858b03,
  0x13f6e1994fda866369ce03ddae000c01d8c7bd0fd79a0a262266d235089985aa21d8497f9c2f3f76706245e8a0678280d3d59a1edd21e67b6c21e000208767b6942c9ecd8310228163b07b559a01d3d648073e54b40e8d52b035f55680cf553a032c043c000552a1ed204427b390ea8c54087e2be63f10a287674289dd9b0a0b907827f9dca09fd8ff827dddaa09f6766827bc11188ba52327bfad5b9e4e21ea66190ec19605d24652174719445eda650d77619425d5865057461940c21664eee698b1c000021cca96152f0cb2a0e537e930e3dfe724cece85913b36163e24289283b326e708719a2c566a6799e0a8a0691781d856a81efd59a01d3d648073e58e01cb555a033d54a80c6c21e000254e8687c21f8af9907827f9dca09fd8ff827dddaa09f68fb827c1d9a09ef3f767b2421d99cf43b065817b699435dd8650975619415d186502e698b1c00004c38439952f0cb29bf548c9efe3cad1a844cc39f9132e0000fdd291959a2b24563886594dfab540f7e9ed352327928a951936196e7a84a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d74619400000196541c952c10e76ad937e952e3df6747530e9c5554a80c6c000152f766aa0e0f7b86443f6400362f01aab3f72195cfd886523f5a1940fd5864f3f52193a310099272f27bccfdb86653f6a198cfd79a0a8d4226616a8876125fe70bcfdd9c18917a2819e0a034f56687b748799edb507e236131e0839831e143d97200180878000821d9eda36fc724065519dd36ee2d6c6598b2b19622c9c6568b2254ac0d7d55a033d54e80cb065c9ee04c466e64caa1b9800086d347671af5513268c0cad99c02a5c64d8cb18aef19762bbac4d8aea000e222563b07b559a01d3d648073e58e01cb476a80a61da6029476880a41d9a0288a969eca4c5676d421f8af98fc428a1d9b0a0b907827f9dca09fd8ff827dddaa09f68fb827c1d9a09ef83102281a70089f0cb0000c10f0001261e7bc930f1eeb0cae7b70a959ed354a87b481109ece196e7a8530e1ea0508e7924fd39a0943b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d186500fde993a0cb664e2e698b091db22bd2d5b8af0044622b000028391d8c21cc98828584dfaa460f7a06b13f700034fd98be13f622f80fd68bde3f562f74fd48bdc8b8c26f1c8f9d762614718cfd39a093f7a2c06f778afd262a092c0001fb63f68a0f8fd712fe3f7419649872c772620e5e4f79834f56687b748799edb782a281a45e07610878000821d9eda5aa0265d52b035f55680cf553a032c2a5c002432c00030cae7b70a959ed354a87b48a8d83532a5a0ca8a9483162a4e0c54a9283142a420c48a8f83112a3a0c4148c9ee3087e2be5d9b0a0b772827f5daa09f6766827bd30f1eeb43b06580a98995f2a46654174719445eda650d77619425d58650574619402a6664fac4d8b12b9a62c2432d8affbdde2bf6d5b8af0044622b098a825a73f0095400028391d8c21cd42c26fd261e7bc814f930e3aece4784dbac760f6b1f885163b3b0742a0fc46c418f0a1e6df8e481b7716b6e5e04c6acd00e9e988cdcc8ece35ea658c577d89b15d520f050100071112ee5419d8ed5014c3b4c0528ed101483b34051262b3b6aa264d40152c326b062045034e0113e54ac1a5821e00020884f67285b3796a464cbe3c15140e4c44f77a61e3dd6a9d0f7428473c8a54bcee6261c3a248760cb0153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328abdb4ca1aeec32843b6457a5ab715e0088c45600000caea0e4763285819709bf443a9ef0326a54ac1a5952f3b9854b4ebe3c15140e21d0002087313ef1ff439f2c91130c195800186593ddc8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2af6d3286bab0ca08877327a196c57fdeef15fae4e411c1315045ae46011500002622a0e476328584dfa7bbc5750007107898f411bd89a3dc64c38f64a91804ac21c800239f83dda21d4f76261e3dd67ee8cda0877327ae4e411c00002622a0e476328584dfa1964f770002087a7b6c21d9a7854e8669ca9719363b362ec0ec58ba859201cf8a959ed354a87b48a969eca21e479d13159db550b6690021f8af9766c282ddca09fd8ff827dddaa09f6766827bc4390004043c000443a9eec04427b3930e1ea0508e7924fdd19b443b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d77619425d586505746194010ee64f6e698b091db22bd2d5b8af0044622b148c8257261e095400006592622a0e476328584dfae7e0f769a7921d207b887181766e162599bee892754f61b0d55b8696566a19a421e000208767acca9619358bce270a31189ad8d42266164b87c759a61e516a887612a560d2d53b9b2754c66bec87b8afa087e2be63f58a47900628ca41f8a1d8ffe285a45e8a08782a281ca979ee743b06580a98995f2a46654174d994c5d66652577799465d5e65157b69943b9a62c26d5b8af0044622b000006593f76a16137e88753dd869e48748f8a21c63e1d53d86c3556e1a5959a86693b3a7b5d52b1b3254ee6c9d5319aa08b9e275e2f389c28c4626b635089980cb0000c21e000208767ab4fdd19b40cae2619c9c8238,
  0x159201cf9638072d00080002e698b09b56e2c20cb18aef000e2bb63f10a288fbc283241e09fe8ff827de3ee09f0260e0941c8c022800067b9465b9ea14c38741d0ec19605d24652174719445dd8650975619415d186500fdb8bf23f5e2fbac4d8b12bdde2bf032d899a8d422659cfc02550000a0e56a82a5554ea21cc32ba6fd261e7c38cfb90eb03de438c0bb10f33beedc2c4b337dd124edbf048a043c0004a98cd5045cf13aa10ec4882c7f0ff50e942b4b92605b84c38cc51d9c18e11fac5229fb90c724bfc12d930704644c44114bb423cb698a8d7f263c35d054a8c9b391a1336e4e04c345c01300e4604bfac720ee2b24039f2c700e5a8754394952d0632acd4cf6043f15f31f7850647fc13ef1f704f83b3413de21c800208753e1832dcf50a61c38d8a950cfd90f5330c8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeac3282ba30ca00877327b734c584dab715e0088c45280000cae54b937ea8383e1a675ccaa99bf4c560b71311029f4c3c098dc9389d5723c26ddc8d099b58ec1ed5639077119726f922e71aa054c46a0a3f10a2c8fbc2840ecd858f76760e85d9b835d4cf80914878817d21c605d800200003b326e70cb18aef000e2bb5cbc098d890a24a1bee8927507e235d41d88bb59a01d3d59a866969c67825a739ab5b1362c4a41e0a028d422659cfc02551d9e02b876580ac1d9202ac9871e294c787809dca9ad26a002299daa032b50b07c2c8799ea80878000810f000108767acc1109dd7262275f0a961935087e2be563f87fa5aa21d84a95834b3f746b5552a19fab9a62c26d5b8af08fd6291dda18a4676b628c5dcb8a1c76ae285645e8a08782a281c11188a550727c240019ee5196e7a854239e454c3874490ec19602a62657ca9199505d36653175999495d24652177799465d5e651574719445eda650d7761942000021d4a9726fd0cae7c30cc5130f04aa4bfc12613070464e7e44cb3938130ce4604bfad510ec2b24039f2c700e5b22f450447fc13f71f704fa46a00cd2acd0f852a743dd04c44ebe21d832c0bdb4ca1aeac3282ba30ca03b550654ecd418c800021e410f4fddaa55507054b443a86574dfaa160f85891b878a15d9b8e9b103b386a2087519f721da0551b7e1a833b36163c878817d21c605d8ecc9b9c3b16654ae698af6087e24aa24289286fba249c0002a7550b043c821eaa5550709bf559a1f0a337e6550cb33f6e10a0988814fa61e04c6656c642b91e136ee4684cdac760f6ab1c83b8b2c700666dd8e480caa36c032cc6a88cad19531f8851647de14206dfc261bb3b074298f011b3b3734b8e4e04c3283f11af06a44542c900e7cd39c07bb50001543b18f780cb93dc11ff04fdbb5506540010000152c326a658c577800715db0620450152b06960878000a8593e040884f67291932f9626c5893c15140e088c464130e3e10000cf728cb73d429870e89285b37963b5cce8a1d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeac3282000043a86572a5c9bf541c9f09369a0014ceb9955167a658c577d89b15d4001c4448cb83de09878f75a62b3b6a3b1cd2e3b3614211f7c3b8ac731336e46c12d92fe38c6e5e04c6acd00e9f20f05013b950676a264eba930b04684c1c11913050462e4e04c32c900e7d1ff04fdbb5506544c44eba152c326a54ac1a5821e0002a164f8102213d9ca464cbe5ab715e0f05450382231190a11cf22a61c3a24a16cde5a1d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282000141c88750cae54b937e930e3e107bb0fdd19b450b27c089881ee910e800104399f0652327c14a979f0410ee64f400026fd50721964f839efb2a5a7b29d9b0a0b772827f5daa09f6766827bd48c9f052a5e7c12d5b9e4e5d1c651177619425d58650574619400000196541ca6fd10e67c1812a930e3d927ee8f2b46a11330e7e44cbad510ec2b3403a7ac900e7cb1c0396c8bd140d20f04ff47fc13ef1f704f80872000821d4cf03c1432f88760cb02f6d3286bbb0ca12eac3282ba30ca00877327a0000a9706594dfaa464f828761917a28196a8099778280d35cfc0255261c7bf948c1dc304462bcd41d035d51300ced42c032a2a587c06d5b9e4e766c282ddca09fd76a827d8439000410ea7c0d0ec19605d1c65117b699435dd86509756194110ee64f400028394dfa1964a979f043e04a160f73a91933c0000043a952f0cb2a0e537e9f0300020884f67021f3d9a088c45d000050729bf548c28593e04724cece85913b36163e24289280878000821d99cf52307c00ecc9b9c21c668b159a834f782a281a45e076155680cf553a032c54a80c6c21f8af9772827f5daa09f6766827bd6a8099773f009549871eff43b065817b699435dd8650975619415d186502e698b1c000054b0a97865950729bf44399f013dba43ccf6d843c000410ecf6d2a5606beaad019eaa740658a164f66bb361416ee504febb5413ececd018e021e0002a950f6902213d9cba38ca22eec3284bab0ca0843f1254088c45d0000566821cca97a8394dfaa460f80091b878a15d9b8e9ede3b3831c0fdc8657513222ba0f484c936ec7242310099236fe1365cbc9ef3507e235e13488b6,
  0x13a3a43ccccca83b331a43d4cc321d832c0ba6cca62e923290ba38ca22eac3282ba30ca0589b16256adc57802231174088445b9d930bfed39c07bb5c001800000763a9183f724c3e1d9065910e654bc21e9d9c3e5476b930f19d94dfa7c6130e1ea019546fe065c8b3d196e2cd80038aedb1362bb0cb1844b7edc111000019553e526e90ecc859a36fc6fac7631a26874c24c1b7f818321c46e10ece9f278796254953d83b576b628c240107c721da065564b09c1878e24d9b8f893554ee0dc5c9f02af19646775dab8a144c8421ca3ff07833b361811fc9047521d607bccae000a195a6e0d64909a58766259db85896632b61140cac844f32ae113953183e8727409cdfc71b814c7c6df86589ab7768629163f507fa32c21104caf843732a610c465c9ee0195676b930f1d4e58fc275a02688487f9a2105c9302dc0008000133e9de04c54759c00199da087e7c88cb19f1c19767c6c0039f194dfa7c1130e1d1b196e677d0ec19605d36653175999495d5e6516c4d8b12b56e2bc011188ba0000655131e930f5230a26541c9fb92a5e196443990f254aea9d552a843d3e50286e41f0794772c0e0966909ad556c24f63110694880c16e144d1a661d8e3544dbf9b8c1dae67450ec19605dde651ac4d8aea044622e80038843508e181942f85df50b616ac0001d9d878d0f2a1d9267c4c7e32cd48c283951327ee421e86592a5e21ccf939de04c78755533e1b9310e4001043a9ddb000e7c6537e9f184c38744843b993d00004c4032b9f253e3b6ad8584dcd215f60000ecf9f243e3b6ad8584dcd215f4000087b9f233e3b6ad8584dcd215f2000021f9f223e3b6ad85848000b9a67c84f8d589a16116ad857a800037027c80f8d589a16116ad8579800004467c78f8d589a16100002d5b9f1d3e356268577800032c67c70f8d589a15dc000065d9f1b3e3200185750000b1367c68f8c26fc109400000039f1933327674a0010f2352c7ee0d081fb717e47ebc5f745c01300b1c0396843a3c5c4c38da5c7dc13e021c800208753b98195800186593e084c44cda5cd316387eecf8ba8383e2c54b8f8a931332fc8760cb02e8c328021dcc9e865b32717bbcc9b80004dfa7c60f8128583db8a464f64930f3e1ca9d01963b5413ec21c800208753b98a950e102d5136f8195800186593e08a0e0f8b152e3e2abab0ca08877327a196cc9c00004dfa7eecf8b822926207ba5c8c1acc3f746a69638072d0cb0000c32b9dcc8fb827d043a000410e627bdd9a9ef754aa7154a971f154c387a810ec19605d18650043b993d0cb664e000026fd50707c5800186593e28195cf87865b3270000137e952e3e2a001043a9eb251307ab04399e8b2a5831c10ea87293b3a15a49888229723008a09871f10874824423ee072e3f7218e421d0002087e2be563809838b8018f021e9f1254a867eee698b09b56e2bc011188a53f747c4d41c9f0752327c1530e1ea021ea66190ec196010ee64f400026fd2a5c1964f8a072d58e26a6a3ee09f010e4001141c9f0710ea7ba432c00030cae7c3c98899b443b06581746194010ee64f432d9938000054b937e9fba3e2605d88711a796fba249d53d86c3556e1a5959a866921d207ba2f389c28c4626b635089986e16259964b87c759a61e516a8876154ee6c9d5319afb8fd6291e4018a32907e28763ff8a16917a282043a000410e627bdd9a831950727c1ca96193621ee2be832c00032a567c4432b9f0f43b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d746194010ee64f432d9938b9a62c5c000043d2a5c9bf4fdd9f1233eedbf048a43a50ad243ac0f790e302ec43ccefb9d9c394adc2c4b337dd124eacd4334aa6335f71fac522c6a11330b5443b0a63c0650ed08f2da62a35fca950cfdc8bd140ced504fb08720008a0e4f83843f15f221d450386580006195cf878cb73d429870f5021d832c0ba6cca62f6d3286bab0ca0865b3271734c58b8877160b842c581953306a4f0501a580003f7610f4a9726fd2a567c44c9a952b069654b4f59bc15140e21d000208733da1170031e1fba3c5643ccccc9d9d0ad30e9048828473c92a950cfddcd316136adc5780223114aa0e4f83a9193e0a196000186573e1e54c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca18877327a196cc9c0000261c54b937e843b3e207b2548c1dc33f7466d141d02655130091d42c0238262000209879f0e5aa21d8645e8a06782868801118af325fe096c9838232261a0898985822526120890982822226060884980822054a8716ed5b9ada7234266dcbc098d7270261a2e00980723025fd639077159a01d3d648073e58e01cb4a8d83532a520c58a9383152a4a0c50a9083122a3e0c44a8e831054e865fe3ef0a0c766c282e41e09fe772827f63fe09f776a827da3ee09f0766827bc439000450707c3443a9f0c262665f90ec19605d1c65117b699435dd8650975619415d18650043b993d262a64e400026fd2a5c195cf87817621c4724dbee8927566a19a555a06593b36163cecc858d0878000821d9ec52a5a7ae0ece9bd53f74684224299893f72199d48c1ecf4c54675ccaa99bf4c440a7d30f02634c7808d865c9ee0087e2be5c8f09b78b842671c8d099b8c402639c9c09868b80260163b07b558e41dc5668074f,
  0x1772827f63fe09f776a827d9d9a09ef508e23cd41f88d78b8619d410f00014c547cd0ecd9f2f32aa7ca6c4d9f1a000e7c6537e9f18196e7a8530e1d1d507666350ec19605d24652174719445dd8650975619415d1865010e98c532626301b0858b0bbdde2c2ae698b09b56e2bc011188ba044222dda77812369ce03ddae000c000003b1e1d9043d2a5e21cd48c1fb90cb27cdc266a67d3bc098f0d38c1e8115ca26032ba8580c9118804c945e01316e4e411913063e5ae5e4e31930b04c24c1412f391a1340a11c479a85f11bca26c464a85b1185170c33a821e0002001cf8ca6fd3e309870f50283b331a4c445fe5eef1615734c584dab715e0088c45d0221116ed3bc091b5070204d50c070b50301acd700060000036fe4bf87639fb95230196563bac7359a2b2449871f36099a99f4d3441e8115ca26032b800200000014ea71b7e18df18804c926fd3e309870f50397938c643ccda20ed733a24c445fe5cd316136adc5845eef15fa32ec577589b15d4001c428931504d24c3c131930d04c44c2c130930904c04c1412f130304ba0000fdb12fe72367ee810fa1d23f72766832cacd12a549878f9a86488bc0262d42c88a7727208c89831f2d83526ca8dbc84b4261e098c982825e25fe70bdc8d09a083102280fdd86788b8619d410f00015070713d41d998d044222dd63b07b558e41dc5648073e54ac0d7d52a031b6b8003007631f332a5c7cc931e9d674cfa74e530f9b4d000a68523f10a287674289e3ef0a0c766c282ddca09fd8ff827dddaa09f6766827bccaa9f294dfa7c6065b9ea14c387a810ec19605d24652174719445dd8650975619415d186502e698b09b56e2bc065d8aeeb1362ba811188ba000e22240001fb95230766821e865910e698a8f9a1c2659201cf8ece1f2c8ff827dc9871f3143b06581756194100003b18439a61e0cb299f0ecd043d52307ee531e152f3e6679bd41f03a151300ced42c032a50700c64a9600092a5679fd41d1c9a4c3e6d340029a1432aa7ca537e9f15196e7a8530e1ea02a62657c65d8aeeb1362ba800388892a360d4ca9183242a660c7ca9483162a4e0c54a9283142a420c48a8f83112a3a0c40000262a5230ecedd9bbb9576aaecd4a971f3201a23b48d7d34e21180d50045928980cae0880000c6201324087c45e418b09c707a4266b97938c66df86379fb70ce64c2c11a10f3388a4bfce17b9381317170833b1fbb0c971784324283a3daea164d981d9c3e60b3403a7ac900e7ca9581afaab4067aa9d01962a54063654acf3fbb36141720f04ff3b9413fb1ff04fbbb5413ececd04f7a6fd3e309870e8e8ed733a28760cb02e8e3288bbb0ca12eac3282ba30ca021d318a64c445fe610b16177bbc5855cd316136adc578589b15d4088c45d000710780000a97a9184c7821cc21e930e3b34196533e261e3f723b18f989d703b30724c8719a26b9a67c86d5b9f1d21e666640002ab554eaa9547631d9a087a7670f981d524c3e6d340029a1432aa7ca537e9f18196e7a8530e1ea019762bbac4d8aea000e222531586040000766e1d90873087a1964f9788a483127241a709af71da26918dbb853736fa135c76781271d9a049876a80c736fe6e520cb88f769de23da13488b86b8222dc1100001043e76d53151d674c78758533e9d573b34724c8719a261d8e7cb542386ee260e0b5c98282d68b9e275dc9389d658fe1fe963b07b558e41dc555a033d54e8687e3f58a458fc428a23ef0a0c772827f63fe09f776a827d9da103e8261e7cb137e9f044c38746c97f9c2f3f76705952a1b5936de6bc50ec19605d36653174919485d1c651177619425d5865049888bfcbdde2bfae698af81db22bd2d5b8af054c4259c11188ba3f7a18f62e0063a3b3e181cecc860200010ecca979fb952301964ece0873087aa0e4f97029826000021c8f09bc8b8e1ac4986826226160984984826026060975c8d09a0507e235e2e18675043c000541d998d262a30449898c0626222ff2f778b0ab9a62c26d5b8af0044622e811088b769ce03ddae000c000004c18982130e25fc7ee548c065958eeb1cc7639f2d331aa0e833a8ec6344d17084d0391b04c64388dd1a61f369a0014d0a10eb32ea766c301a62b05b8e49c4eb2c7f0ff51fac522bb4207d0a9884b39d990c0476342fe43b23e56b1c83b8aab4067aa95018daa74343e762cca947de1418ee504fec7fc13eeed504fb3b3413de6554f948cbb3e369bf4f8c0cb73d427eecf39a61c3a3a43ccccca1d832c0ba6cca62e8e3288bbb0ca12eac3282ba30ca05cd316136adc578022311740000987952f10e610f4ece065952307ee4f9606044c54759d31e1d613b34724cecc9d7021c668987639f2a4dfa7c1141c1ef73f7679cd30e1d1d21e66666e698b09b56e2bc011188ba76680c7000043b2261ea460fdc952f54aaa9d555a9d9c10e610f432c9f2b3748766475810eb02c0dc700ae10e23708a98c1f410ed02a86df8df5bb43148adbf048a47ea0ff432e4f7043a53a4eb1f84eb1d9b0c08e49816e0004000032aced70003374498a8dcc2622053e9878131b91e1378e4684d02c760f6ab1c83b8c5c70d62a95018daa74343f1f8851447de14191ff04fbbb5413ececd04f7a83f11af170c33a821e00026554f94843f3e44658cf8e00073e329bf4f8c0cb73d427eecf39a61c,
  0x121e67d080039f194dfa7c4130e1ea043b06580a98995f2a46654174d994c5d66652577799465d5e65157b699435dd8650843b993d00007eec21d952e3b34a46032c930e3e886d6d41f03a150740d7542c032a50700c6544c1eaf2a587849d9d0a27766c282ddaa09f6766827bc439000410ea7d040039f194dfa7c5530e1ea0508e788574919485d1c651175619415d18650043b993d000043c8fdd843b2a5ca4613159f4335f71fac522aa6212cb0ec83033b4207cca118dada83e0742a0e81aea8580654a0e018ca8983d5e54b0c9b152b3cfeece8513bb361416ee504febb5413ececd04f7b70a03e821c800208753e8298a8fa026fd3e209870f501d9c333254c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9edcd316136adc5780223117400009871fbb087654b948c065921e67d081f2152a326aed0c523152d3d6654c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca180004c567eec21d952e10ea7d04d39284705bca17c158a89b0508a16c13aa85834dee49c4eb393f1382e5ec4d6393b134a99fc42cac7f0ff4b25c3e3acd30f28b24c3c1b327008a32a80028cb335ce4c40d0947eb148f200c519483f143b1ffc50b46210cb26584213195f084a657421219590844655c2108cb9002c32d400a0cb1002432bc0088cad002021d000208733d22aad448eaa75122cfdb041832c4105edd740b8b71d02c80008000263d3ace99f4e9c800534286554f94a6fd3e2032dcf50a61c3d408760cb02e9b3298baccca4aeef328cbabcca28877327a32ec577589b15d4001c444800021e64c38fdd843b2a5ca46032ca62a3e806d1098693bf26164ef898493bd260a4eec98193ba25fe4ee2e699f2121e478b49879ae9262266d0989997e00007ee8fdc043b3e7e6cc952b893058e41dc61d3859d50767b8942c9b2d1d8c6b8d44c1ae28fbc2841668074f766e0d6db7f818b043c00041109bab4c3e6b9241e0a02508e181942f85df513616e142d85ab772a0ce531581f46eba05c4ece000c2a54002400100002a5a7aa131e9df721e46b440029a6e3b1e1758ecb85b33b321634ec5858621c605da1e58952880e24f624289286fba249d53d86c3556e1a5959a86693b2617fcec885fe3b2a1694ec685a1724e275a2f389c28c4626b5cbd89ac8d4226621d989676e16259a1e3893658fe1fe964b87c759a61e5164987835aa21d862e786ef8bc61a18a9083de2a3e0ea8a93837b2a4a0da4a8e83652a520d24a8d834254ee6c9d5319afb8fd6291dda18a46900628c9dad8a31907e2875dcb8a1c8ffe2859dab8a15917a2821e0a8a073b3e7c9087b9f234dfa7c4930e1e9f43b06580a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d77619422a6664fae698b09b56e2bc011188ba000e210c000267c10ea10f4a971d9a52301964fdd9f3d02ec4388d68b7dd124ea9ec361aab70d2cacd43349fba340e7edc3761fad0dcc7eac35c1fb30d1e7ec433f9fa90cf67ed4331c5cf13af179c4e14623135b178c4d346a11330b1fc3fd2c970f8eb34c3ca2c930f06b5443b0c7eb148f200c519483f143b1ffc50b48bd141043cc0fa21d832c0ba6cca62eb33292bbbcca32eaf328abdb4ca190f715f5734c57b370b12cc10fc49c000054c4a9d843a843d3f7019653159f3c1228a950395b6fd33ee87586389fbb3cfd0e94e9390e3344c76743031d930bfe4c3c16e10f303e843ac0f7b92713ad0ecc4b3b70b12ccb1fc3fd1d9b3a6aa98cd7dc7eb148aed081f3022000026df8e57a84636b6087cd118ec7331aa0f81d0a83a06baa26019da8580654a0e018c952c326c98a8f99152b3cfeece8513bb361416ee504febb5413ed1f704f83b3413de9bf4f8a261c3d404c4ccbf21d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c3281734c584dab715e0088c45d000010e654b821ea9183f701964f9d87fa8fd6291563f09d78b9c1bb9da103e6508c6d6d41f03a150740d7544c033b50b00ca941c03192a5864d8a979f394c547cd0ecd9f2f2a5679fdd9d0a27766c282ddca09fd76a827d9d9a09ef0cb0000c32b9f254dfa7c6130e1ea043b06580a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d18650032d993826222ff2f778b0ab9a62c26d5b8af0044622e80002918876410f44399fb93e7475c0ecc1c9321c6689887999993b3a181955a033d54e80cb152a031b508c7ce141c1ef7772827f5daa09f6766827bc7639f374c547cd0ecd9f2f5dd8650975619415d186502e698b09b56e2bc011188ba00007ee548c43b2087a1964439952f3e7222920c49c9069c26d8cdbf853c36ee14dc76781271d9a049a0cb88f769de23d81100001043e76d476c8af4044623e40005ab6507298ac76328463e70264a310865751327ca1cbc9d6d4c787098ece1f2a21e668049871f3636fc6fac65c9ee0000800000019daf195676b930f1f353f6e1bb097f9c2f723c26f1c8d09a058ec1ed5639077159a01d3d648073e8b9e1bb62e386b13f7619e152b035f54e80cb152a031b50707bdca959e7f8fc428a23ef0a0c766c282e41e09fe,
  0x12a5679fdd9d0a27766c282ddca09fd76a827d8caa9f29b9a67c84cb19f1c19767c6c0039f194dfa7c5065b9ea14c387a80a98995f2a46654174d994c5d66652574919485dde651975799455d1c65117b699435dd8650975619415d186502c4d8b0e000010ec110865910e654b88799f4e00166dfc29e1b770a6e6dc42841b7d09c46dec2709b7909c06dd426f1b7309bb065c47bc18e11b9062846034e701eed38c0658ec63e70a11ce76930105a8e498f28930b04c24c24130130504bc4c0c12e931104ae4c3412992ff04980880000821f37d2e4684d039f9132eb1d83daac720ee2b5443b0ac700e5aa0f81d0a83806331f885143b3a144f1f7850648bd140d1f704f83b3413de43ac0b0065800066e04f9002233e3c195cf0f45c33b3e6dbcd78a83a32d28760cb02e923290ba38ca22f6d3286ba30ca05ab71634196c57fdeef15fcdc7048b1fbd0c991780325bc14069a0000987043b523254b553a88734c567eec8791f4d3314e4604c245c10c76a954f2d13073cb276642c690f102fa438c0bb44851250df74493ab350cd24c4412b92ff04991a844cc39f9132eb5443b08220000243acf35021f37d2762cca948bd140ca0f81d0bc14069a4c3cfa590f33d4a766cea29d9d364a54b0c9b2cd00e9eb24039f2c700e5a196000186573d7ca9d0f48952b3cfeece8513c83c13fcee504fec7fc13eeed504fb47dc13e0088cf8f26fd3e249870f5021d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c3280196cc9c5cd3162e000148c88732a5c7eec21e9f4c3b08a95833bab350cd2aad032cc5c213411a844cc46201324b1c83b8ad510ec2b3403a7b91b04c6e5e4122a63d046ee4e4f46a67d3b42987cecf47de141922f4503483c13fc1960001a6fd3e2e195cf5c261c3d408760cb02e8e3288bdb4ca1aeec3285734c58b865b15ff7bbc57f1fbd0c991780325bc14069a000021ea9192a5aa9d44399fbb261e7d2cec22a560ceeaad032c843c000410ececfc5c2134118804c9391b04c6e5e4122930e3ce443ccec1ab350cd31a844cc2d510ec322f45033c14069a54b0c9b2c720ee2b3403a7c5e00c961960001a9183e64195cf5f2a743d2298f4eb3a67d3a72987cda6952b35fc0014d0a3b3a144f1f785063b36141720f04ff3b9413faed504fb3b3413de21c800208753e926554f94843f3e449bf4f8a8cb73d429870f5021d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9e865b3271734c584dab7161032ec577589b15d4001c44480004c5454b8fdd9f4a000410ececd90f33b0610f44942a740c9512102c8c5e039c84c38d091d9c18e0acd43349fb90cce4c4412b952a326b1a844cc39f9132eb5443b0a1d50eba54b41a686580006195ceeca63d3ace987cda68005342922f45043c15140ea460fa419553e5210fcf9126fd3e2a32dcf50a61c3d3e43d4cc321d832c054c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1865b32716adc5840cbb15dd626c575000711120001315152e3f7621d4fa4817621c46b45bee892754f61b0d55b8696566a19a553b9b2754c66a822e789d78bce270a31189ad8d42266163f87fa592e1f1d66987945aa21d8432c0003087800088799f4508767acc32b9dd94cfa74e530f9b4d000a68523f58a47900628ca41f8a1d8ffe285a45e8a082a587d1ccaa9f2921ee7c8c21f9f224dfa7c5465b9ea14c387a7d0ec19605d36653175999495dde651975799455eda650c32d9938b9a62c26d5b8af019762bbac4d8aea044622e80038889000021d5315152e3f76a460fa4017621c46b45bee89270878000821d9f4659201cf953d86c3556e1a5959a866954ee6c9d5319aa08ff827ee2e789d78bce270a31189ad8d42266163f87fa592e1f1d66987945aa21d85daa83280cb0000c8799f450cae776531e9d674cfa74e530f9b4d000a6850a9519358fd6291e4018a32907e28763ff8a16917a2820caa9f2921ee7c8c21f9f224dfa7c5465b9ea14c387a7d0ec19602a62657ca9199505d36653175999495dde651975799455eda650d75619410cb664e2e698b09b56e2bc065d8aeeb1362ba811188ba000e2224000291810ea98a8a971fbb2a587d1c48bc3c50ae87668fa22a7434de4c40d09267f06fc1960001a8593c06195ceec930f3b54987cda68005342854a8c9abb97143898acfa099553e529bf4f8a952d3d6632dcf50a61c3d3e54c4caf952332a0ba6cca62eb33292bbbcca32eaf328abdb4ca1865b327032ec577589b15d4001c41e0000592243c948c08754c7854b8fdd843b3e8c736a2e18677261c7d08a969eb354ae24ac21d0002087a7cf432c00030cae776421f9f224dfa7c5432d99383b362ec2e698b09b56e2bc011188ba6dfe062c000291810ea987933e152e3f7643ccfa29e778808247955a06593b2e15c8ece9ecb8c40264a1e2091759a01d3dcbc8247513277c153a1a6f9078280933f837e772a0ce542f82b151360a1142d82752a5464d5c9f89c172f626b1c9d89a5592e1f1d669879459261e0ca969eb350b277f89881a12900628ca41f8a1d772e28723ff8a1610e800104399e744c7a759d33e9d393b1665493159f43,
  0x155680cf553a032c566a70615319c163b386665dca09fd76a827d88791f5e2a5a7d64a971f50087e7c8937e9f174c387a8177619425d58650400006593f7621ccfaf800721de062487381856dfc24c21d3859d507666347631f384c54759d31e1b3050b015da1e2091b6e3a6c4142386065232164487581ef21d207b8878817d21c605da1d989676e16259a24289286fba249c876819521ca0644ece1e73566a70615319c166e3e24d552b035f54e80cb032c000354ee7d7541c1ef70cae7af9d9b0a0b76a827d9d9a09ef10e4001043a9c490878000821d9f5c2a5c7d4487b9f23087e7c8ad5b9f1d4dfa7c5d30e1ea021ea661974719445d586505746194010ee64f432d993800007eec8791f5e134cb24c3c186580006195cf5f47ff1428ed581b8952e3ea09bf4f8ba1d832c0babcca2865b15ff7bbc57f1fbd0d111788343800010e67eed53b9f5d0cb31880d39aab5123add74ec310ef0312438c0ae371d3abedbf8495aa5606beecd8fadb91b04caa0ec45da899115cd38c065c1e93bb83b18edaa61e3a9ca0e0d66821e00020010000267d3bc098a8eb382213756000cced152b0652a17c158a89b0508a16c13aa91904ae98f0f0028583bde4c40d09392713ace4fc4e0b97b1358e4ec4d2b9f9132eb1fc3fd2c970f8eb34c3ca2c930f06b5443b0c5cf0ddf179c36146230d2b178c34346a10cd0a98c1f42a7b076aaadc1c12a7706e2acd41a786580006a11cf1006573b891fac523bb43148d200c5193b5b146320fc50ebb9714391ffc50b3b57142b22f45043c15140e21d0002130f3b5421cc4fb3b550658a9d4fad152e3ea26554f9482233e3d6adcf8e8cbb3e37626cf8d00073e329bf4f8ba61c3d408760cb02e9b3298baccca4aeef328cbabcca2af6d3286bab0ca08877327a196cc9c000021e47eec21d9f5c1340b1c83b886580006195cd6547de142021d000208731417170c33baa5706c054b8fa8a1d832c0ba38ca20877327a196cc9c000072347eedd9b1f5b3e70a0e0d668ec7331aa0e8132a91904ae98a8eb393103424e4684d039f9132eb1c83b8ad510ec2a98c1f42b35069e1960001a8473c4098f0f01a8583bec195cd653b43148d1f7850848bd1410f054503bb3706be21d0002130f3b5421ccd4b2a570cf054b8fa8dab73e3a9bf4f8ba61c3d41170cecfa1d832c0ba6cca62e8e3288bdb4ca18877327a196c57fdeef15fc7ef432645e00c96000021d90f23f76a9d4fad1f5821e67d5c0001fbb2a5a7d64f5c08720008195800186593ea621d4fa90877327a196cc9c00003f7654b48791f58122ca9d0196371d02c898f4ef0267c370ced504fb2ab4067aee5019e0872000821d4f59a8983d6210e8001043d3eac54b8fa8843f3e44001cf8ca6fd3e2e9870f502eac328221dcc9e80002a5a7eec8799f57069cf0501a6a9183ea8acd4e0c06580006195cf5237dd02fc21c800208753eaa9bf4f8b952e3d507670ccc8877327a196cc9c000021e654b4fdd843d3eac7ac944c1ea66eba05c432c00030cae774133e9dc62a5c7aa130e1cc83b38666432d9938000010f4879952d3f7621d4faa83e776840f994231f384c5479b141c1c1c54c670587639a5c766c282ddca09fd76a827d959a834f2a5c7a9530e1ccb3b38666574719445dd865097561941b56e2bc011188ba782a0d3000029180cb210f4879952d3f7621ccfaa1d674c566d6d31e1b30508e0f9948c834d76860f9d41f03a150740d75e0a834e51300ced42c032a0878000941c1ef73b3879cd59a9c1854c6705821d9a967674289dd9b0a0b772827f5daa09f6766827bc439000410ea7d48a971f51087e7c8937e9f174c387a8174919485d1c651177619425d586505746194010ee64f400006592a5a7eec8791f53389210f0001152e3ea210fcf91043b3d660000879152d3f7621d4fa91a1226222ff098782dc3f707cf153b9b2754c66a822e789d7724e275963f87fa0cb0000c21e000208767d0432b9ddb8fd6291e3ff8a1610e800104399f504c547d2821f9f224dfa7c550ec19605d366531757994510ee64f432d9938bdde64dee698b1700007eeca971f513e8443c8f0d930f05b810e8001392713ac10f44b3ac7f0ff4a98cd7dc7eb148b0ec83033b4207cca118dada83e0742a0e81aea8980676a160195283806327670f45952c326c196000186573d7c54acf3fbb3a144eecd8505bb9413faed504fb3b3413dea464fa7a62a3e9410fcf9126fd3e2a9870f5021d832c054c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c3280196cc9c5cd3162e0000a971fbb10e67d40fa6930f3b4643ccfa702200002087cdf4a83e074254b0c9b06580006195cf5f2a743d2254acf3fbb3a144eee504febb5413ec10e8001043d3e9898a8fa5043f3e44088cf8f26fd3e2a9870f50153132be548cca82e9b3298baccca4ae923290bbbcca32eaf328aba38ca22f6d3286bbb0ca12eac3282ba30ca0065b32700000439952e3f76a464fa78510831e782d311086a83141391965005b36fc6e3465919dd195a6e0ccad84507f1c6e046589ab732c21104ca9843119727b806559dae4c3c753a02688487f9a210400200004cfa778000199da507c0e8541d035d51300ced42c032a4c780590a9619366e38245953a1e91,
  0x104624c0c1181301045ee4e04c5c3a612604c34129c5e13ed6dbfceaf9faf3414e7e44cbb71c1236b1c83b8ad510ec2b3403a7ac900e7cb1c0396c3c50aeca9581afa8593edaa0e0f7b9fb9390e43cce2292ff385ea9d0d0fc7de1418ecd8505c8bd140d20f04ff47fc13eeed504fb47dc13e0ecd04f7bc14069e4c3cfb486583ecc4c44fb21fbb3ec64c4ccbf21d832c0ba38ca22f6d3286bbb0ca12eac3282ba30ca013153273734c57c589b15d4acd049400071078767c2c944840b220000ece8873087a98f0a97a9193edc000411088f7043e229e0cb053c83521308dbf1beb1d8c7ce142386068766259d53183e819727b81da18a458fd41fe80020000195676b80019a6858fc275d30f06734cf819562e71b4c4c546854fdb1a108b8c26f22e109a08c40264a2e00984723e0a71c8d826026100021cbc9c63723266289858234260e08c89828231260608c0980822f3f5e6829c9c098b261a094e2f09f6b3f72721c97f9c2f52306cc1cfc899758ec1ed563907715aa21d85668074f59201cf9638072d0878000941c1ef7087678888799c458fc428a23ef0a0c917a281a41e09fe8ff827de3ee09f0766827bcece1f6c261e7da432c1f6626227d90fdd9f6332aa7ca421f9f2204467c7937e9f18196e7a8530e1d1d262665f90ec19605d36653174919485d1c65117b699435dd8650975619415d18650098a9939b9a62c26d5b8b08b1362ba8003883c0000f05531e08732a5ea164fb683e67686291542308f78fd41fea0cb053c36fc002cdbb996858fc275d31106af4c3c19ce2e71b4c4c546854fdb1a108b8c26f22e109a08b802610db8850836fa1388dbd84e136ea1378db984dd723e0a71c8d826026100021c8c998a831c23720c508c036f212fc9858234260e08c89828231260608c0980822f044000060d49e047270262c10f88bb507c0e8544c033b8bc27dad41d19692a5831c0fdc8667261a094da7380f769c6032c76780ae6a0002a876a80a61da6029476880a41d920281a70009f52307da87631f303f5e682a350899873f2265d63b07b558e41dc56a8876159a01d3d648073e58e01cb555a033d54a80c6cecd9d6125fe70bd53a1a1f8fc428a1d9d0a278fbc283245e8a06907827f9dca09fd8ff827dddaa09f68fb827c1d9a09ef087800089879f690cb07d989889f643f767d78caa9f29087e7c88dc09f2004467c7937e9f18196e7a84db79af108766a5876b99d121e6666487a9986262665f90ec19605d36653174919485d1c65117b699435dd8650975619415d18650098a993943aa3152e698b09b56e2c230858b03b1362ba8003883c2a660d480002859782a98f0439952f3b387db0ce213063314b2404c539181309170431a1fb0001a1960fb313113ec87eecfb19fa734127ef43261fb70c8c7ed43229fb30c887ebc3211fad0c827eac3201fa90c7e0000fdc130e25fc98f1668ac718bc27dacf9bc3b33e5ca0e0f7b9fb818e0ecd04f786583ecc4c44fb210f5330cba30ca021d518a9842c581dab715e0088c45d153306a454b41a600001d8e7671e0a843d10e654bd48c1f6a3e587674d9829190ccf1a844cc2d510ec322f45033c14069eacd0fb428580c9010f0001043b352d17804c5ac900e7c43ccfb3aa74343f1ff04fbbb5413ec7ee000686583ecc7eecfb1843f3e448760cb02f6d3286bab0ca09fbd32747edc5f91fb517e27ecc5f81fb117de7ebc5f71fad17da7eac5f61fa917d67e9c5f55eef1615734c584dab71611626c57500071078e4e411b00004c7821cca97930f3ed26cc148c85913b38724c87181763b36758624289286fba249c21e00023b326e7021d9a9655680cf552a031b21e67d9d53a1a1f772827f63fe09f776a827d9d9a09ef0cb07d98fdd9f635dd8650975619415d186502e698af6087e24a800028594c7821cca97ab343ed070909871b44261a4efc98593be26124ef498293bb26064ee897f93b8087800089889f643f767d8c21f9f22262665fae698b09b56e2c22c4d8aea08762458003883c6e3a059000010f34c78a9d4fb380030cae7d9432d993800001960fb31f6426207c9400006573eca7d8cfdd19b400004c44fb2000410e67af843a9dd00cac000c32c9f622a5c7d4537e9f1710ee64f432d993800007eecfb18229723077b141c88a0831212d0dbc1b2a8350229c10f00014c7a77e01109bab508e0b7942f82b151360a1142d82755232095d42c02382620002021d0002261e7d8421e9f607270262d648073e260e0b5c98282d626060aa0985827f261209bc980826b261a094c97f824c8ff827edc9389d6727e2705cbd89ac72762695cfc899758fe1fe964b87c759a61e5164987835aa21d862f0864a54c60fa159a834f76aa0cb153a9dfa8fd6291dda18a46900628ca41f8a1d8ffe285a45e8a08782a281c43a000410e67d7c8791f5e2a5c7d4421f9f2204467c7937e9f174c387a80989997e43b0658174d994c5d66652577799465d5e65157b699435d58650443b993d262a64e40001fbb0cb27d88eb3a6fd3e309870f50262b05b898f011b00007272e4989879f6134244c44cd3a8590aee4c3c11b263d3bee9870e631d9c3332b2404c4c3c512340001c9caa625668a9d043a865921e610f4fb0057650b26cc21e2091b52321645b8e81644c7a77de24289280878000821d9ebc,
  0x1809a2121fe688410008000133e9de04c54759c00199da43a6314c7639f7d4c787dd432c1f6626227d90fdd9f6332aa7ca421f9f22b56e7c74cb19f1c19767c6ec4d9f1a000e7c6537e9f18196e7a8530e1d1d43b0658177619425d586505746194010ee64f7085993bb9a62c70000152f3f006629c8c0984261e767a2e09b8f2a586c1098393158b9e275d63f87fa43aa1fd88771d864c3c754a3f59b9154c4259dbae09228764181220285813b347cc043900040878000821d9e2d10ea784c32c1f6626227d90fdd9f5e087e7c8937e9f184c387a808719a2621e66664989997e43b0658043b993db9a62c26d5b8b08b1362ba800388430000a11c76312fe556aa9d5638aa554c5699f0ece1f7f3b0c43bc0c490e302b8dc74eafb6fe1260dd7049143a70b3b10142c1a83b1176a264457021e00020884fbe2a5606beaad019e843c000410ecf0910f3388a4c3cd749d9c18e0ecd8505bb9413fa21c8002152d3ef67ee4fbd087537ea6df8df5a63e36fc32e4f7041e93bb832aced7261e3a9c0010000267d3bc098a8eb3800333b498f0fba86583ecc4c44fb21fbb3ec66554f94843f3e4432ecf8dd89b3e34001cf8ca6fd3e3032dcf50a61c3a3a43d4cc32e8e3288bbb0ca10877327a875462a610b16177bbc5855cd31612088c579dab715e2d38c0658ed90152d38004f80002a5e3b1cfbe9b9454c4259e1d9060626227d9142308f7832c14f00001d9d36fe10f5315a67c04427df01f3bb4207cca98cdca284611ee0880000821f115ca26019dbb9413fa21c800208753425065829e262a3ace4c3cd749fb93ef498f0fba86583ecc4c44fb21fbb3eb2088cf8f26fd3e309870e8eaeec328421dcc9ea67d099c00020f41b7f2a5e54b4fbd9f793b3a7ddc21e000208766e1955a033d50707bdddca09fd766827bc439000410ea6fd531f1b7e19727b806559dae4c3c753800200004cfa778000199da52327de131e1f750cb07d989889f6432aa7ca421f9f2219767c6c0039f194dfa7c6065b9ea14c38747577619425d18650043b993db1362c340001b7f2a5e7ee4fbd1f3987667cb8000152f087a196541c88733b387ee548c1f79394a7674df0043c000410ecdc32b35069eaad019eaa540636f0545033b9413faecd04f7c5c00c7421c80022a63372821d45042838114722f03b08220000299f4ef0262a3aceb5404cc021f116a7edc332426909b1062025c263c3eea1960fb3043f3e44088cf8f00073e329bf4f8c261c3a3a8760cb02f6d3286bbb0ca12e8c328021dcc9e931117f97bbc57f1fbd0cd51a8033380003f726dfca97a9193ef018161d91f39508e722d48c9c87000021cca978659087a7ee4ece9f770c90a164effb92713ad179c4e14623135b178c4d346a1133117804c5ac7f0ff4b25c3e3acd30f28b24c3c1ad510ec2b24039f45cf0ddaa11cf11c7eb148f200c519483f143b1ffc50b48bd14111ff04fdb939046c21d0002130e36884c349df930b277c4c249de930527764c0c9dd12ff2770762c5d4087313eced541962a753ece7ee0f9f90f23c5a10e8001043d3ee81960fb313113ec87eecfb1843f3e449bf4f8c261c3a3a4c4ccbf21d832c0ba6cca62eb33292bbbcca32eaf328abdb4ca1aeac328221dcc9edcd316136adc584589b15d4001c41e00002a5e98f0fba9c4921e670909871a1210e800104399f730cb07d989889f643f767d8c989997e10ee64f6e698b09b56e2c22c4d8aea000e20f0000152f4c7810f4fba1f711d8c7cc0fdc0c7058e41dc5648073e55680cf4a96832a54a80c6cecd9d6125fe70bd53a1a1f8fbc2831dca09fd8ff827dddaa09f6766827bd42c9f723b3a7dc09879f690cb07d989889f643f767d8c87a998643b0658174719445dd8650975619415d1865010ea8c54c2162c2ef778b0ab9a62c26d5b8b08b1362ba8003883c000010f531e152f10e67dcc1a7bc153ed8acd0fb400003b3821cd31e152f50b27dc813013080010e4684d045c30cea4c3411a930b04684c1c119130504624c0c1181301045e1960fb3283b3dc4e4e0cc8931518224c4c603131117f97bbc5855cd316136adc57802231159178432400003f723b1d639ac9125fc4c3942c1f713e7098a8f9a284739167ee0fb78ec7331aa0e82cec3a61260dbfceafb71c12370f142bb2a5606bea0e0f7b9d9b3ac243cce2292ff385ea164d982a74343eecd8505c7fc13eeed504fb3b3413dea464fb7130f3ed21960fb313113ec87eecfb1ae8e3288bab0ca0ae8c3281734c584dab71611626c575000710780000439843d4c7854bcece9f7000000014f700cb836e4000cd34267c0caaa118f9c262a342a7ed8d084620132517004c2397938c6e464cc5130d046a4c2c11a130704644c14118b93813171784fb59faf341454b8c9b1d9c18e0b3403a7ac900e7c875439d2c700e5a54b4195152b3cfe4c3cd74c83c13fcee504fec7fc13eeed504fb47dc13e01960fb313113ec87eecfb199553e529bf4f8c0cb73d429870f5010f5330c8760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c32816adc57802231158001c41e00001d8ca16141c92fe10e698f0fdc1f6f0ce67ed8d0845c2134117004c2391b04c04c20004261f3dc63b1cf7139193314a0e82ce930b04684c1c1191305,
  0x2724c8719fe93b327f80ece9fb955687ea552a1fa43b367e5d53a1f9608787e22e699f2100007facfef37dc02ec00008719fe93fbf12102c680003b327f804942b353fb410f0fc40000890a7f7c493ab353fb410f0fc400006fba7f783afc8bd3fb08758fc08000566a7f685033c143f9c21c8fc5af6d3286000245e9fd8069aa460fe6952c3f620001e0a1fce331a3b18fdda83a3f6a000148c1fcd3ae07660e4990e3344c43ccfdd1d9d3f72aad0fd4aa543f48766cfcbaa743f2c10f0fc45cd33e436adcf8e80001d8c7eecfdc9d9c333200008799fba3f0c98a8f35952b3f4c21c8fc5843c3f1054bcfc006583ecc9870f5000003b3a7ee41ae952c3f62ecd8fc9000050747ed4004951b3f5654acfd315293f3a549cfce15253f365484fcd151f3f325474fcc152f3f0054c4caf952332a054ccc9f00002a587ec4fc93b3706a60000a8d9fab0e9b20f0fc8a1d63f02000155a1fa937c832e0dc10004369c98781ada67c067298f01943b363f24ee50fc83b543f1c6554f9480073e329bf4f8c0cb73d429870f5000002a567e98395c7dc3f1a8758fc0800054a87e90fc63b35062c0000a949f9d3f18ecd418a80002a4e7e70fc63b3506280000a929f9b3f18ecd418900002a427e68fc63b3506220000a8f9f993f18ecd418800002a3a7e60eaa08723f1610f0fc4152f3f007eecfb1a6fd3e300000ecd9f970e791ff0fc7a1d63f02000153a1f96141621c8fc5ae8e32880001d9b1f9213fc21c8fc5aeec3284000241e1f9113fa21c8fc5aeec32840001dca1f9013ee21c8fc5aeac328200023fe1f8f13ec21c8fc5aeac32820001daa1f8e13e021c8fc5ae8c328000023ee1f8d13de21c8fc5ae8c32800001d9a1f8c000821d4fc50877327a00004391f8b3404a9ec3e2aab70f24acd43afaa77364ea98cd7d930e34251fac523c803146520fc50ec7ff142d22f4504043c3f108758fc0952f3f001960fb313113ec87eecfb1dcd33e42ba6cca62eb33292bbbcca32eaf328abdb4ca1800010ea7e28001043b3f0e10fcf91000008787e20f46952c326ce4e011ba63c3ece54acece2a74343eece8513bb361416ee504fec7fc13eeed504fb3b3413de21c8002130e368821d4d6b130d277e4c2c9df1309277a4c149dd930327744bfc9dc36fc02b043c8f16952f3f004c44fb21fbb3ec7734cf90a6fd3e309870f50131332fc54c4caf952332a0ba6cca62eb33292ba48ca42eef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9e800008767e1cc9b152d07cc54acf2dbb43148a21c8002087537251fa8d7daa6212cf0ec830328463f0a54bcfc006583ecd734cf908cb73d4254c4caf952332a0ba6cca62eb33292bbbcca32eaf328aba38ca22f6d3286ba30ca00877327a0000ecea62b087a7e18f9d9fb93e74a464d92952c326c54acf3fbb9413faed504fb0872000821d4d09130f05b8e49c4eb2c7f0ff51fac3fbaa633f088758fc0952f3f001960fb313113ec89bf4f8c261c39968760cb0153132be548cca82e9b3298baccca4aeef328cbabcca2ae8e3288bdb4ca1aeec3284bab0ca0ae8c328021dcc9edcd316136adc578022311f30ecc30280004c56767421ea8463f0a7cecfdc9f3a52326c94a9619362a56796dda18a4510e4001043a8a478fd41fe10eb1f812a5e7e0032c1f66196e7a84a98995f2a46654174d994c5d66652577799465d5e651574719445eda650d746194010ee64f6e698b09b56e2bc011188f9876618140002a634c56a118ece843d3f0831c4a979f803f767d8ee699f21262665f800021d63f021fea3f59b9158fc6e29531096787641818ece1f7f25fe70bc21e000221e66e2021d9b864c8421c9638072d7f2411d555a033d54a80c6ccae000a508c7ce141c1ef72a5679fd53a1a1f772827f63fe09f776a827da3ee09f0766827bccad845032b2113ccab844e10e4001043a9bf57f1c6e0531f1b7e32c21104caf843732a610c465c9ee0195676b930f1d4e]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem accepted : LRAT.checkW formula fk 15 words = true := by
  decide +kernel

theorem unsat : ¬ LRAT.FormulaSat formula :=
  LRAT.checkW_sound _ fk 15 words accepted

def upper : Circuit := ({ gates := [⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [10, 12]⟩], output := 13 } : Circuit)

theorem upper_ok : Monotone2 upper ∧ upper.size ≤ 6 ∧
    Represents (fun u v : Fin 4 => (279 : ℕ).testBit (4 * u.val + v.val)) upper := by
  refine ⟨?_, by decide, by decide⟩
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5485

theorem PEqualNP.Outside.L_meta_5485 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (279 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (279 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨⟨PEqualNP.Outside.L_meta_5485.upper, PEqualNP.Outside.L_meta_5485.upper_ok⟩, PEqualNP.Outside.L_meta_5485.LRAT.Promise.rep_lower_mask 4 4 279 5 PEqualNP.Outside.L_meta_5485.unsat⟩
