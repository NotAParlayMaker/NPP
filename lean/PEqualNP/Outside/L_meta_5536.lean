import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5536

namespace Helpers

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

end Helpers

namespace LRAT

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

def lgStep (U : Nat) (acc : Nat) (b : Nat) : Nat :=
  Bool.rec (Nat.add acc b) acc (Nat.beq (Nat.shiftRight U (Nat.add acc b)) (nat_lit 0))

def lgU (U : Nat) : Nat :=
  lgStep U (lgStep U (lgStep U (lgStep U (lgStep U (lgStep U (lgStep U (lgStep U (lgStep U
    (lgStep U (lgStep U (lgStep U (lgStep U (lgStep U (lgStep U (lgStep U 0 (nat_lit 32768))
    (nat_lit 16384)) (nat_lit 8192)) (nat_lit 4096)) (nat_lit 2048)) (nat_lit 1024))
    (nat_lit 512)) (nat_lit 256)) (nat_lit 128)) (nat_lit 64)) (nat_lit 32)) (nat_lit 16))
    (nat_lit 8)) (nat_lit 4)) (nat_lit 2)) (nat_lit 1)

def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (stepUnit k db id C F (Nat.xor D (Nat.land D F)) (lgU (Nat.xor D (Nat.land D F))))
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

theorem stepUnit_ok {Q : Prop} {k : Cont} (hk : Good a Q k) (db : Trie) (id C F P x : Nat)
    (hdb : db.All (MaskSat a)) (hinv : HintInv a C F P) (hP : P ≠ 0)
    (h : stepUnit k db id C F P x = true) : Q := by
  change Bool.rec false (k db id true C (setBit F (neg x)) 0)
    (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
  cases hu : Nat.beq P (Nat.shiftLeft 1 x)
  · rw [hu] at h; exact absurd h (by simp)
  · rw [hu] at h
    refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
    obtain ⟨hF, hPw⟩ := hinv hC
    rcases hPw with hP0 | ⟨w, hw, hwv⟩
    · exact absurd hP0 hP
    · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
      subst hw
      intro l hl
      rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
      rcases hl with hl | rfl
      · exact hF l hl
      · rw [litVal_neg, hwv]; rfl

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
        change Bool.rec (stepUnit k db id C F (Nat.xor D (Nat.land D F)) (lgU (Nat.xor D (Nat.land D F))))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine stepUnit_ok a hk db id C F _ _ hdb
            (fun hC => ⟨(hinv hC).1, Or.inr (witness_U a (hinv hC).1 hD)⟩) ?_ h
          intro h0; rw [h0] at hU; exact absurd hU (by decide)
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

end LRAT

namespace LRAT.Link

open PEqualNP.Outside.L_meta_5536.LRAT

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
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5536.Helpers

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

end LRAT.Link

namespace LRAT.Link

open PEqualNP.Outside.L_meta_5536.LRAT

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

end LRAT.Link

namespace LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5536.LRAT
  PEqualNP.Outside.L_meta_5536.LRAT.Link PEqualNP.Represents

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

end LRAT.Promise

namespace LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5536.LRAT
  PEqualNP.Outside.L_meta_5536.LRAT.Link PEqualNP.Represents

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

end LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

set_option maxRecDepth 100000 in
def fk : List Nat := [
  34, 14, 7, 23, 8, 179, 130, 89, 118, 116, 346, 236, 244, 171, 1534, 1445, 715, 1002, 1628, 1771, 1629, 2031, 0, 0, 1293, 825, 865, 1155, 866, 0, 1286, 0, 0, 0, 1663, 2033, 2032, 1630, 1271, 0,
  0, 0, 0, 0, 0, 0, 2984, 1436, 0, 0, 0, 748, 498, 406, 606, 691, 576, 559, 1976, 0, 422, 0, 910, 1077, 638, 0, 1168, 0, 0, 643, 0, 955, 1156, 828, 829, 2758, 0, 0, 2953, 950,
  2954, 2955, 2975, 0, 0, 2558, 0, 365, 636, 3036, 787, 3037, 719, 723, 0, 0, 2071, 0, 905, 2796, 0, 906, 2797, 0, 0, 0, 0, 1672, 0, 0, 0, 1395, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 3301, 3302, 3303, 1396, 1071, 3304, 3305, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2700, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  360, 450, 1123, 1607, 1559, 2395, 1857, 0, 0, 0, 1453, 553, 743, 940, 769, 2118, 1910, 1659, 0, 0, 0, 1954, 835, 938, 1896, 1054, 1367, 1618, 2830, 0, 0, 0, 3089, 2193, 0, 0, 1130, 2194, 2180, 3076,
  0, 0, 0, 305, 822, 246, 317, 1162, 391, 415, 428, 0, 0, 0, 283, 975, 417, 435, 381, 1196, 581, 870, 0, 0, 0, 673, 3146, 1345, 1346, 891, 1050, 1742, 1561, 0, 0, 0, 2467, 157, 2453, 2468,
  0, 0, 0, 588, 0, 0, 0, 567, 203, 657, 522, 690, 744, 1254, 791, 0, 0, 0, 0, 0, 520, 0, 0, 521, 0, 0, 0, 0, 0, 0, 0, 1699, 0, 0, 0, 672, 0, 0, 0, 0,
  0, 0, 1745, 0, 0, 0, 0, 2102, 0, 0, 0, 0, 0, 0, 433, 370, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1567, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1568, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1361, 0, 0, 0, 0, 0, 0, 0, 1593, 315, 335, 485, 942, 464, 701, 733, 2902, 0, 0, 0, 0, 0, 766, 745, 1058, 504, 0, 1713, 2097, 1732, 0, 0, 0,
  0, 2702, 1007, 907, 3166, 505, 1099, 0, 0, 1733, 0, 0, 0, 0, 0, 2272, 0, 0, 1665, 2151, 1740, 0, 0, 0, 0, 0, 0, 183, 1392, 303, 282, 997, 519, 571, 486, 442, 3171, 0, 0, 0,
  277, 2042, 537, 392, 232, 1768, 543, 797, 481, 3128, 0, 0, 0, 627, 2719, 813, 1127, 434, 771, 0, 1864, 882, 0, 0, 0, 0, 2940, 224, 3347, 3348, 2261, 0, 2903, 198, 0, 274, 0, 0, 0, 201,
  300, 1170, 250, 759, 319, 373, 361, 408, 2217, 0, 0, 0, 2924, 2935, 294, 2932, 1735, 235, 0, 0, 0, 613, 0, 0, 0, 2133, 2936, 868, 2919, 2920, 0, 426, 0, 0, 662, 0, 0, 0, 0, 0,
  1537, 0, 0, 0, 0, 2114, 0, 0, 0, 0, 0, 2925, 0, 0, 367, 209, 3298, 0, 0, 0, 527, 0, 0, 0, 0, 0, 2933, 3340, 0, 2407, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2922,
  0, 0, 0, 2408, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2347, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1145, 1119, 622, 1339, 1791, 465, 1237, 586, 827, 0, 419, 0, 2454, 0, 0, 1711, 932,
  669, 846, 446, 3338, 855, 765, 540, 2050, 656, 2804, 0, 0, 0, 0, 1570, 1131, 1357, 807, 591, 0, 1273, 795, 0, 782, 0, 0, 0, 0, 0, 0, 0, 0, 1691, 2409, 1889, 0, 1778, 0, 3053, 0,
  0, 0, 0, 170, 3375, 216, 288, 2000, 217, 271, 667, 255, 1308, 177, 1454, 2560, 0, 0, 328, 0, 436, 1066, 275, 1504, 903, 659, 220, 1190, 292, 2092, 0, 0, 0, 625, 0, 1125, 1245, 626, 1126, 0,
  1274, 350, 0, 421, 0, 0, 0, 0, 3180, 241, 3181, 0, 0, 3182, 3183, 221, 0, 164, 2439, 187, 0, 0, 0, 329, 301, 1763, 384, 1390, 339, 385, 593, 186, 1211, 175, 0, 0, 0, 0, 1803, 0,
  545, 2229, 2230, 302, 1473, 2908, 0, 264, 0, 377, 0, 0, 0, 0, 0, 2579, 0, 0, 0, 668, 2904, 0, 396, 0, 454, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 886, 0, 0, 0, 3258,
  0, 0, 0, 0, 0, 0, 565, 293, 0, 0, 0, 0, 240, 0, 320, 0, 0, 0, 0, 0, 0, 0, 0, 2136, 0, 0, 0, 0, 0, 1139, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2131,
  0, 0, 0, 0, 1140, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1334, 0, 0, 0, 1138, 0, 0, 0, 2482, 210, 211, 212, 0, 213, 214, 215, 524, 0, 225, 2483, 172, 1991, 0, 0, 0,
  0, 0, 0, 0, 243, 0, 0, 0, 425, 2870, 290, 0, 182, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 607, 0, 509, 0, 248, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 1215, 0, 1183, 0, 814, 0, 0, 0, 0, 234, 0, 0, 0, 0, 0, 0, 0, 155, 1159, 226, 661, 113, 953, 0, 0, 0, 327, 0, 0, 0, 0, 0, 0, 0, 263, 1095, 134, 2165,
  105, 1431, 0, 0, 0, 341, 0, 0, 0, 0, 0, 0, 0, 833, 2871, 382, 0, 238, 0, 0, 0, 0, 0, 69, 0, 0, 0, 0, 0, 70, 1324, 126, 1769, 152, 3219, 84, 0, 0, 0, 444,
  0, 0, 0, 0, 0, 0, 0, 208, 460, 259, 1200, 90, 1169, 0, 0, 0, 0, 0, 62, 0, 0, 63, 0, 0, 0, 158, 0, 227, 0, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66,
  0, 0, 252, 0, 298, 0, 151, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674, 0, 1167, 0, 1234, 0, 0, 0, 0, 0, 0, 64, 65, 0, 0, 0, 0, 159, 0, 206, 0,
  102, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1602, 0, 1354, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2697, 0, 1916, 0, 1355, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2675, 0, 1917, 0, 1117, 0, 0, 0, 0, 0, 1297, 2756, 0, 1433, 1669, 1627, 0, 0, 1093, 693, 2034, 969, 2058, 794, 1174, 0, 0, 2061, 2078, 2764, 2062, 1175, 0,
  1666, 0, 0, 0, 0, 0, 0, 2985, 1435, 0, 0, 751, 526, 749, 605, 480, 635, 574, 685, 0, 3256, 2556, 876, 1079, 784, 2557, 610, 1671, 0, 2714, 0, 1437, 2715, 1285, 641, 1213, 2716, 0, 0, 686,
  2972, 2973, 2144, 0, 2974, 538, 0, 788, 717, 0, 720, 0, 688, 721, 722, 0, 2795, 0, 558, 0, 0, 754, 1704, 2800, 0, 0, 0, 1443, 0, 0, 0, 904, 0, 0, 0, 0, 1428, 0, 0, 0,
  0, 3261, 0, 3306, 0, 0, 1070, 1001, 3307, 3308, 3309, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2710, 0, 0, 0, 0, 0, 2015, 0, 0, 0, 0, 0, 1928,
  1047, 1048, 934, 1929, 1242, 1124, 768, 2083, 0, 0, 1464, 1938, 1609, 1575, 939, 2854, 1248, 1142, 1091, 3167, 0, 1953, 0, 0, 2413, 1894, 1356, 2500, 2488, 1092, 0, 0, 0, 0, 0, 0, 0, 1888, 1885, 0,
  2085, 0, 0, 624, 3276, 550, 508, 947, 989, 892, 357, 378, 286, 0, 755, 1501, 629, 592, 383, 924, 650, 596, 386, 920, 0, 1560, 0, 1243, 1347, 812, 738, 1743, 1244, 611, 0, 0, 0, 281, 2469, 0,
  0, 0, 0, 218, 1828, 163, 0, 941, 1583, 1100, 1584, 679, 1902, 1563, 438, 459, 689, 0, 0, 0, 670, 0, 0, 736, 0, 0, 0, 461, 0, 0, 0, 1351, 0, 0, 0, 1121, 0, 0, 831, 0,
  0, 0, 3257, 0, 0, 0, 0, 0, 0, 1657, 0, 0, 0, 0, 737, 449, 0, 0, 0, 0, 307, 0, 0, 0, 0, 0, 0, 2423, 0, 0, 0, 0, 0, 0, 0, 0, 2957, 0, 0, 2424,
  0, 0, 0, 0, 0, 0, 0, 1746, 0, 0, 0, 2425, 0, 2669, 0, 1932, 845, 1239, 735, 1933, 548, 531, 587, 1008, 0, 467, 0, 0, 0, 1858, 1913, 2811, 936, 2448, 1115, 1597, 908, 0, 630, 1789,
  0, 2703, 0, 0, 2705, 2706, 1227, 2704, 1673, 951, 0, 708, 3208, 0, 0, 0, 0, 0, 0, 3235, 3052, 0, 1434, 0, 1249, 0, 0, 447, 2024, 487, 448, 2025, 431, 289, 432, 343, 1631, 128, 599, 0,
  853, 0, 1101, 925, 445, 3055, 644, 931, 409, 1520, 138, 1794, 0, 2396, 2827, 2390, 2391, 1349, 1855, 0, 1557, 758, 0, 354, 3024, 0, 0, 546, 0, 0, 0, 0, 0, 503, 1521, 394, 1098, 141, 0, 375,
  369, 1290, 376, 1083, 340, 299, 336, 342, 1817, 96, 634, 0, 0, 0, 842, 0, 0, 700, 0, 0, 2255, 514, 2130, 325, 0, 0, 0, 0, 0, 0, 0, 1041, 0, 0, 1013, 2917, 507, 0, 0, 0,
  2346, 0, 0, 0, 0, 3074, 0, 3260, 0, 1720, 0, 0, 0, 0, 1042, 885, 0, 0, 0, 3297, 473, 1476, 245, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2930, 1569, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2921, 1353, 0, 0, 0, 0, 2348, 0, 0, 0, 0, 0, 0, 0, 1279, 0, 2575, 2349, 1539, 1847, 2576, 1340, 1120, 1848, 2056, 0, 437, 0, 196, 1940, 0, 0, 0,
  0, 0, 1852, 0, 1851, 2365, 965, 0, 655, 0, 228, 2803, 0, 0, 0, 0, 0, 0, 2364, 0, 0, 966, 0, 899, 0, 334, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2055, 0, 0, 0,
  1438, 0, 0, 767, 0, 847, 848, 0, 808, 890, 809, 362, 1277, 194, 718, 56, 820, 0, 1890, 0, 1891, 1892, 1045, 0, 1878, 1893, 792, 0, 284, 1515, 71, 1316, 0, 1859, 0, 1860, 1861, 1862, 1348, 0,
  1863, 1017, 0, 573, 0, 199, 3241, 0, 0, 398, 0, 0, 0, 0, 0, 399, 0, 609, 1446, 333, 1056, 49, 0, 1578, 1547, 0, 1579, 1644, 1580, 1246, 1581, 560, 3349, 190, 598, 51, 992, 0, 0, 0,
  411, 0, 0, 412, 0, 0, 2913, 878, 2066, 492, 3239, 91, 0, 0, 0, 2586, 0, 0, 0, 400, 0, 2907, 1689, 2065, 819, 3240, 129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 1721, 0, 0, 0, 0, 389, 401, 0, 0, 0, 0, 869, 3028, 439, 2241, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1683, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 1684, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1685, 0, 0, 0, 0, 2313, 2314, 2315, 0, 2316, 2317, 2318, 0, 0, 2178, 0, 752, 1612, 59, 1979, 0,
  0, 0, 0, 0, 2319, 0, 0, 0, 0, 0, 3059, 0, 1049, 0, 67, 2743, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3060, 0, 1154, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 854, 0, 0, 2320, 0, 0, 0, 0, 0, 0, 0, 1722, 0, 1158, 1407, 658, 1402, 22, 1011, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1202, 0,
  851, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3091, 0, 988, 3023, 73, 0, 0, 0, 1837, 0, 0, 0, 0, 0, 1838, 0, 0, 0, 1157, 2125, 371, 0, 6, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 830, 0, 493, 3022, 24, 1760, 0, 0, 0, 1839, 0, 0, 1840, 0, 0, 0, 0, 0, 1408, 2129, 549, 2910, 27, 0, 0, 0, 0, 0, 0, 0, 1841,
  0, 0, 0, 0, 1409, 2915, 589, 2905, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 844, 0, 0, 0, 0, 1842, 1843, 0, 0, 0, 0, 0, 0, 1410, 2926,
  490, 2890, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2929, 0, 0, 779, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2918, 0, 0, 780, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 702, 0, 785, 1269, 0, 1491, 0, 961, 0, 786, 663, 0, 3246, 0, 877, 0, 1153, 1444, 0, 0, 0, 1176, 0, 0, 0, 0, 0,
  0, 1287, 0, 457, 716, 0, 528, 479, 684, 0, 495, 1010, 0, 0, 2555, 557, 0, 577, 874, 0, 2757, 1212, 660, 0, 2971, 2970, 0, 949, 470, 2952, 2530, 222, 575, 0, 3035, 0, 499, 0, 0, 2794,
  0, 824, 471, 2072, 0, 0, 0, 2698, 1270, 823, 0, 0, 0, 0, 0, 0, 1281, 0, 0, 3299, 3300, 0, 1003, 863, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2699, 0, 0, 0, 0,
  0, 0, 0, 0, 2014, 0, 0, 304, 671, 0, 1926, 1927, 628, 0, 296, 1057, 3169, 1299, 1463, 551, 0, 491, 1944, 0, 1952, 1951, 776, 0, 1488, 0, 0, 3090, 0, 1129, 0, 249, 202, 1489, 862, 555,
  257, 0, 272, 356, 1310, 1026, 725, 269, 0, 566, 466, 0, 1479, 1741, 651, 0, 1598, 2470, 631, 185, 95, 0, 2381, 145, 468, 1422, 595, 424, 310, 0, 0, 0, 2009, 414, 280, 0, 0, 0, 0, 0,
  649, 535, 0, 0, 0, 0, 0, 1301, 1426, 0, 0, 0, 0, 991, 338, 205, 0, 0, 0, 0, 2420, 1883, 0, 0, 0, 0, 0, 2421, 1884, 2956, 0, 0, 0, 0, 2422, 1744, 1427, 0, 0, 314,
  533, 0, 1265, 1931, 316, 0, 368, 852, 0, 0, 1788, 413, 0, 429, 893, 0, 2701, 2035, 547, 0, 3327, 1886, 0, 0, 0, 962, 0, 136, 278, 1268, 1280, 747, 192, 0, 180, 143, 0, 1016, 1103, 140,
  0, 403, 324, 0, 2720, 2101, 297, 0, 0, 1191, 372, 110, 101, 1472, 2322, 160, 184, 1706, 915, 510, 132, 0, 0, 0, 774, 169, 195, 1475, 0, 0, 0, 1565, 265, 359, 2916, 0, 0, 0, 2840, 1337,
  1235, 0, 0, 0, 0, 742, 165, 166, 2135, 0, 0, 0, 2405, 3339, 2004, 2931, 0, 0, 0, 2406, 0, 1649, 2923, 0, 0, 0, 0, 2345, 1118, 0, 0, 266, 295, 0, 1382, 2574, 806, 0, 242, 355,
  0, 1442, 2802, 268, 0, 331, 513, 0, 0, 0, 380, 0, 1251, 2695, 0, 0, 0, 1292, 0, 109, 114, 1645, 2091, 1073, 74, 0, 131, 174, 3325, 1712, 2243, 76, 0, 237, 309, 0, 0, 0, 254, 0,
  0, 1511, 191, 48, 43, 1906, 2307, 115, 142, 1151, 3319, 896, 72, 0, 0, 0, 572, 81, 61, 2912, 0, 0, 0, 1263, 127, 79, 2906, 0, 0, 0, 3259, 887, 2113, 0, 0, 0, 3221, 420, 80, 53,
  0, 0, 0, 0, 0, 995, 1679, 0, 0, 0, 0, 0, 996, 1680, 0, 0, 0, 0, 0, 888, 1681, 0, 0, 112, 168, 0, 0, 0, 121, 0, 88, 167, 0, 0, 0, 139, 0, 133, 193, 0,
  0, 0, 258, 0, 618, 1178, 0, 0, 0, 1250, 0, 124, 77, 0, 0, 0, 46, 0, 82, 92, 0, 0, 0, 47, 0, 137, 260, 0, 0, 0, 125, 0, 0, 0, 93, 13, 18, 0, 1835, 87,
  86, 0, 0, 0, 52, 0, 0, 0, 173, 19, 35, 0, 0, 0, 0, 534, 20, 37, 0, 0, 0, 0, 984, 1425, 1727, 0, 0, 0, 0, 147, 17, 29, 0, 0, 0, 0, 2137, 552, 859, 0,
  0, 0, 0, 2132, 536, 860, 0, 0, 0, 0, 1336, 554, 861, 0, 0, 2311, 2298, 2299, 2300, 2301, 2302, 2303, 0, 0, 0, 0, 181, 2304, 0, 0, 0, 2305, 0, 0, 0, 0, 0, 0, 233, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 532, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1887, 0, 2306, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 707, 0, 0, 0, 2532, 2382, 2323, 2308, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 161, 0, 0,
  0, 0, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 1845, 0, 0, 0, 0, 0, 0, 94, 0, 0, 0, 0, 0, 0, 740, 0, 0, 0, 0, 0, 0,
  741, 0, 0, 0, 0, 0, 0, 734, 60, 2545, 0, 0, 2531, 2546, 2547, 144, 0, 0, 1854, 323, 337, 930, 0, 0, 120, 154, 379, 2329, 0, 0, 111, 149, 276, 1836, 0, 0, 119, 285, 1533, 2548,
  83, 55, 58, 2533, 2534, 2535, 2536, 2383, 2384, 2537, 2538, 2385, 2386, 2324, 2325, 2539, 2540, 2387, 2388, 2326, 2327, 2309, 2310, 683, 0, 753, 1420, 2659, 1164, 2017, 0, 2761, 2018, 1078, 1653, 1005, 871, 1397, 1667, 3134,
  1651, 1668, 2655, 1288, 2019, 1675, 2006, 2020, 1652, 1664, 1421, 2589, 2590, 2591, 2592, 2593, 2594, 2595, 2596, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1241, 815, 489, 937, 1899, 1052, 709, 1362, 1133, 652, 1572, 1360,
  1573, 1358, 935, 1566, 1587, 1352, 2414, 1252, 1564, 772, 1051, 1247, 1253, 1132, 1881, 1128, 2427, 2428, 2429, 2430, 2431, 2432, 2433, 2434, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 579, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 982, 810, 488, 1558, 1596, 1060, 1122, 1374, 1912, 1059, 805, 1044, 1256, 1061, 983, 1535, 1400, 1264, 1384, 1536, 843, 2340, 1849, 2350, 2351, 2341, 2342, 2343, 2392, 1678, 2393, 2394, 1372, 1599, 1594, 2191, 2562,
  2563, 2564, 2565, 2566, 2567, 2568, 2569, 1978, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1009, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 764, 2368, 2370, 2359, 2371, 1543, 2354, 2372, 0, 0, 1542,
  2373, 1544, 1545, 1341, 2356, 2374, 2357, 2369, 2378, 2358, 2355, 2375, 0, 0, 2353, 0, 1865, 1228, 1116, 1229, 1335, 1230, 1231, 1232, 1233, 952, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 1401, 476, 674, 675, 676, 568, 654,
  677, 678, 826, 306, 2331, 2332, 2333, 2334, 2335, 2336, 2337, 2338, 2561, 894, 2339, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2297, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1726, 478, 0, 2321, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 2549, 1869, 986, 1844, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1461, 351,
  197, 150, 0, 0, 0, 0, 0, 0, 0, 3005, 0, 0, 0, 3001, 0, 0, 0, 0, 3002, 0, 3008, 0, 0, 0, 3003, 0, 0, 0, 0, 0, 2707, 3000, 0, 2039, 0, 0, 0, 0, 0, 3004,
  0, 3009, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3014, 3015, 0, 2164, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1974, 348, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2651, 0, 0, 0, 0, 0, 2650, 0, 0, 0, 0, 0, 0, 2652, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2551, 458, 2648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2552, 363, 1650, 2949, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 1975, 407, 2649, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2553, 474, 2005, 0, 2732, 2733, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2734, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 2554, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2728, 0, 0, 2724, 0, 0, 0, 2726, 0, 0, 0, 0, 2725, 0, 0, 2498, 2609, 0, 2723, 0, 0, 0, 0, 0, 0, 2722, 0, 0, 0, 0, 0, 0, 0,
  2727, 0, 0, 2497, 3047, 0, 0, 0, 0, 1634, 2582, 1983, 2583, 1984, 1985, 2584, 1413, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 455, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 2835, 0, 0, 0, 0, 2108, 0, 0, 0, 0, 0, 0, 2109, 0, 0, 0, 0, 0, 0, 0, 2110, 0, 0, 0, 0, 0, 0, 2103, 3080, 1180, 3079,
  2107, 3081, 1815, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 711, 405, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 3048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1482, 2172, 0, 0, 0, 3286, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 945, 511, 811, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 944, 494, 648, 1495, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 2186, 2187, 3098, 3263, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1147, 477, 706, 1490, 1106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3054, 0, 0, 3324, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1146, 687, 850, 3094, 1781, 1311, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  909, 497, 987, 1641, 1415, 1416, 1642, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1635, 1670, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3289, 0, 0, 2419, 2632, 2633, 2636, 2634, 2630,
  2635, 1998, 2068, 2776, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2597, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2397, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2618, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1388, 0, 0, 0, 1694,
  1963, 2773, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1135, 713, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1898, 0, 0, 0, 2960, 2889,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1258, 746, 1582, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 775, 475, 739, 1053, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2643, 2644, 2642, 1643,
  1962, 1622, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1606, 681, 1577, 1729, 1134, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 1474, 2896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1611, 714, 1359, 1730, 901, 1165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 2124, 2894, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1381, 783, 1656, 2126, 1152, 1654, 2127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 2013, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1997, 2622, 2623, 2624, 2625, 2626, 2627, 2012, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1088, 1296, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
def words : List Nat := [
  0x1003a00e800a002500340014017007800380090011001100d0001c047006f037802ac079813903ce04e802c01ae037e07980df01e5023204b805b0115010e0f60302018500ba01a4031806001cc02d003b003b00720250037003602f402640001fb63f7043d087910ec21d47670ecd1d96b9a410eca97a1d926204c3898610ee0e7200dc055004905f602a40c80184031e066c0cd018e031a045801a004e007800a800b0138002e0074019802e00b201a004f80b30190045002c02dc03c8053809d013909aa005400a002500340014016801c00480088008800700f601c00c2805d00d2018c050006001cc024403b003b0072044c04a006e000043d087910ec21dc43a887b043b2a5e8764988130e26197bb8fdc1fb654ac0f6005502fb032006100c7819b033406380c681160068013801e002a002c14f4301803a00f002ac00a8014004a0068002802d003800900110011000e01ec038018500ba01a40318060012202d003b003b0072044c04a006e000054bd0ecaa5626204c389865eee3f707ed952a04d50a7802a803a82fe01521cdc22f853b0e6c180849604d403a014e8136845e00e201b00930109030a044c04a000058e2b1cc988130e26187ee0fdb1fbabddc195c29e80a90092045800b0126006e030c0002a5454acb1c432d2d52592cb35963f1310261c4c50986131258e67eec3018075037a13500e8053a04da11780788109002c0458021008a016a05bc26982fd0028009400d000500380090011001100ba01a4031806001d000ec01c809400dc00d80001fbab9a410eca97887543b2b1c4988130e26184c48872853e00ea049011a029b025a0880078004f00fc014001780005aa4b25966b2c7e26204c3897f130c26244c5032c8116006e02a802482fb015201d40c80184031e066c0cd012404680a6c0968220031c06340780034009c00f0027807e00a000a801780160270005c00e80150028009400d0005006600b8016801c00480088008800700de01640340070015602dc04701150428053c1d101af0494061402e806900c6028003000e6012202d003b003b0072044c04a006e000010eca97a1d926204c389865eee3f707ed8ecc860401e606f00d7008b017e0f5408a00b600b014e420906010e6a24ac49509290c0007d811080c501be117449404d20a700190036800606f01170268853707ae0af41a5837706ec0058084805300d001c007b80b5007402ac02e005100f6021002b80a700de001c0088005124e02a826804cf099c133429b04cc08b6132c29a837501b80a6817e024905ba1cd003000e60122084c07400b400ec00ec01c811300dc00d80bd009907420000fdc1fb643b254bc21f10f421e47670ecd130d09ae1328079822207ac0c900fc017a0001734821eaab53b187670ecd1d983b2c7638ec810eb0a72016005b01f7017e0670090045a0000a9d421eaa5721c843d087910f021d843b887310e821ec765c209021201e604ec1a505ff0bfc073c0bd0000b9a410f552a9d8c3b387668ecc1d8e3b2043b430080f3124c2494492092302f40002e691d8c3b387668ecc1d8e3b2043bc39a8058016c07dc16e02bc039e07900a7013a010e05bc09c800054aaa9d552b90f421e443d821d837800b002d80fb82dc0578073c0f2014e0274021c0b78139000c042803800b50156019404b0074005a022803c00100026004800380a700600054021003a017c01b00788109002c00bc02e806900c6024407400b400ec00ec01c806e006c02641d080007230e4e1c8d39fb43b27eeca979d9c3b3410f887a10f25aa4249c1ea80f300b00dd020880d002dc10400d482bb069203a809281f60442031406f80a50148059808400c201500190036817a0132000159b2a7a5574a98887a10f23b38766ae69043d021402a849109211240247c48f091d1238246c48d011300017bb8fdc1fb62626061417d80aa00ea06400c201240468063c14d819b033404b4110018e031a03700780034009e013803f003c00a000a801780160270005c00e8015006600b801681bb028c03a400a00250034001403980950a681cc83988040007e1cc0020872f0e5c00f801e872d0e580114022001c002000900098022002400440060007123201740348063014001800730091023801d801d80390226025048c0917122c245448a0913122401dc4888000980930090ea21d22a5854a8988130e3f707ed821f895400ea04b0089029a021c036008f80d7015201c8041006c0000b1cd649ac7726244c4098713140cae04e02fe8733122017f0000610a438887590ea21d243a087390e621ca43908718a9885340e6617f4039890f01d22438079090d1218242c48509091210035806a80d401a60348068804c00f6029802b80a700de024407400b40bf8047001d80002a5c54b0a9521d643a8874b0850873123201cc07480f201ac035406a00d301a4034403d805700de001c483811c0e561ca802e806900c6018004880e8016824184828904120601b84810901120023fc47f08fd11f823ec47d08f90001301a6024c0243a487590ea152e2a5854a832d891711f017f403987320e62010001f873000821cbc397003e007a1cb43960045008800700080024002600880090011001817f008e072b0e5400017b72eb25de4ba68a98152e2a5854a90ec21d643a8874843a8907,
  0x1011e0000ece10f45234a17944f284636fc088941ca83b1dac439c41480f312b225600bd0000b9a47660ece1d9a3b147650ecb1d8c3b2443c42ae005812ae17f8230861506520f5404c8000b9a443d087910ee21d4762c11c04d801d602040e002e002e206c023002df053a081c06c8118013803300a88216022e067402f00b802a00508000291a50bca2794230ed61da83b487681b7eb56c088439f80f30c281cf84ab095500007670ecd1d8a3b2c7630ec91d9e880e0c0429a03d90c26184830886100c1e183830682c0007200d81d0895412a625484a88950129e25384a6873d12980002601152a261c7ed88791d9a43a4088c4f600f302e006f00d78120035c06fc0f301be016e023808a80060214010c02d0030010000c802300370154011c025804905f605200a380a9002e007400a8116006600b801681900308063c0cd819a031c063406e01bb028c03a401a004e007800a80178073002c0050020003f004a010400d003e007a001402280440322007000800240026008800900110018001c0ab8350012a061402e806900c6028003000e6012203a005a011c00ec00ec01c8113012801b801b017a07420000a96152a26204c38fdc1fb621e843c821f1d9c3b3454c0160007301d203c806b00d501a8034c06900d100f6015c03780005d1abab574795322a5854a8a97153010e6055c09c0017003a0054019802e005a06ec0a300e900e6010001f8041007c00f402280440020004c009000c0000bdb97592ef25d3454c8a96152a2a5c54c1747aeaf5d26876432b931226284c40987087503220200027060b004a005c00e806a0084085402a805b0180029804b000702cc0524003060c002c14fc00a83a400741054208012004241cf026b80690140039810980e800ec00ec01c806e006c0e84000043e3b3443d08791d9c43b24c409871fb63f7054bc1a804d50428045400043a6874854bd0ec9fb626204c389865eee3f7010ec30600a6000e01080a480f1000c06f408a81f9006e02a40e8026d0a7a01c40360109002a0e9001d04150240084839e04d7030a03a003b003b0072025001b03a100007ee0fdb1310261c10f8a979d9a21e843c8ece21d90cae14fc08a8070000c00b40a480070098024403b003b007200d81d080003b3443d08791d9c087c54be1d347de0748085000300ab029201e000380a7016801d801d8039006c0e840001d9a21e843c8ece152f087d0e923ee041507aa03cc02c02bb069203a809280c201500afc0d501f60442031406f806400da0af81ba041101a005b805280a4050c182c00b0138002e007400a806a008400e802a805b0098030005300a7000e0524003094b09ae061402e8063014001800730091042603a005a0076007600e404a006e006c05e804c83a1000010f8988130e3f6c7ee0a97a1d921e843c8ece1d9a3b2c1cf000d003c0158016803a00002a5e7eec439aeb20cb2876553d82bf000a00a802e003000a60000a979fbb10e6bdb832ca1d9566e0af800a00340124010c03280002a5e7eec439ae9a0cb2876553182860154182820a032806f20c9c1a7834e008e012c02482fb0290051c0548609002c04e00c28113012801b80002cd158e24c316489310261d7bb9639ac9358ee7ee0fdb1fba0c16252814e03a30216252439d894804dc251c0c2800059a2b1c4fdc1fb63f757bb832cac9126204c3898612fe0c1201d44a309451288250c4a1094101280002f771310261c4bf898613123f5209b80fc826d064a2500304073601280002f77065958e24c4098712fe26184c48fd689470154117c29d8602064a24fc22f093e127a0614089809400004c30988130e25fcb245668deee0cb2b1c4fdc1fb63f507eb8fdd1fac129006f40fc81d004da042c192893c0e6e0001638865959224c40987131425fc4c309891fb5127a24ec0bd893a0c0e0c9849c8938126e0001638930c26204c3898012febddcb244fdd1fb83f6c7eb0fd71fa859a21964fda093e0154117c29d83250c0c24d8136811300017bb832cac713f707ed8fd61fb43f5c7ea0fdd13031270117c0550325126a24d049981d002260002f77065958e27ee0fdb1fac3f687eb8fd41fba261224dc03a8932126202a822f853b0c040c940fc818502260250000065958e27ee0fdb1fac3f687eb8fd41fbabddc4c08988130e260c4c0097f130c261024e403a84d40a741178000130826204c38981130625fc4c309891314723207e41a68075021624c029e073b01280002f77065959224c009841310261c4c0897f130c26247ebc4a5073a0154042c30281bd02260002f77065959227eb8fd51fb83f6c7ed0fd81fac3f507ee8983893a0214019404b007400a60040009801200180174034806300c000ec01c8036000054bc21edcd221e843c8ece1d9a10ea052407983d608261ce40d701bf03cc06f81030115010e135449781aa0c0800d80bd00003f6c7ee087a10f2261854bd0ec9310261d7348ece1d9a3b2c10ec4a580f307ac0c9039c822305bc13581a601cf042804e40d50604006c05e80001fb63f7043d0879130c087654bd0ec9310261d7348ece1d9a3b2ca954497837800e002d4055807b00ae01bc0002e8d5d5aba3ca97843b21ec43d0879087302961cd4497092d0e700002e691d9c3b34766087781aa028e012c08b0016024c0118061853e,
  0x10018001c126818500ba01a403180600584024403b003b007202500370036013201dc029015002840000db71b7e36f86dd8dba1b70b56c3b5876a0ecc1d9c3b201109d9d21e47ed8a97a1d93f707ee8988130e26186dc83ac860c00fe07480800273030c1858040846708c61d58075819f0a8a001809e8065012c01d0029801000260048006018500ba01a40318060007600e401b007700a405400a1000036dc6dc8dbf1b7c36ec6dd0db808750caf6ad876b0ed41d983b3876402213b3a54bc98621d93f6c4c409871fb836f02588075846309b209cc0e9060c00fe04000cf841b075003d40e0803600a405400005ab6087654bc98621d93f6c4c409871fb83b3a0884dbf1b7c36ec6dd0db80ecb0a8a03ac1bd83dc00006db8dbf1b7c36ec6dc8dba1b703701062c0cf80eb08ce0c0c040875605be0a741040207022e0674003013d00ca025803a00530020004c009000c00ba01a40318060007600e401b007700a405400a10000261c0884ece952f10ea876432b931226203b5876a0ecc1d9c3b22d5b1b7e36f86dd8dba1b7050bc1d5c09c0017003a0054019802e005a01640340070016e023808a805f011201fc09a810c02001868144837b01d6136011b011a026002800730091007600e404a003600a405400005ab636f06df8dbe1b7636e46dd0db802213b3a10eca97887543b2195c9891310261c3b1c3ab01c201e8051004601fa014a030803201660000aae959b2a7a54c476741109b7e1dad6ad821e813d010203280be01ab033c061809e00f50260024008780f800be022403f8083011602fc00680c8022802d80e1005801a005b807a01a901d404940a200c501be02300fd00a4014a042005400c200da01900b3000606f001640340070016a02ac019802e005a022803c0017003a0054021003a011a02b40388162024c13743aa83790e74117c0670065012c01d0029801000260048006005d00d2018c050006001cc024407400b4007600e401b009900ee01480a1008f0000195d0ec88752a5e43c8dbf02223b3a3b58fd9847c01e61d503a987520ea21d403a7874e0e9a0d400bd0077000054bc8791fb8262087649871fb6b9a47668ece037e01540bec0c80184031e066c0cd018e031a045801a004e007800a80c28113012800016a92c9659acb1f8988130e26197bb8fdc1fb63f741964182053407b21d3030986120c221840307860e0c1a000308521d22a6227b405502fb032006100c7819b033406380c681160068013801e002a0028009400d0005003800900110011000e093400b0961012a0f64062018500ba01a4031806000ec00ec01c8113012801b801b0052011e0000a95152e04446df8ecd0ed621e44c40987130c3f707ed8fdd03580c16005c00e801500d4010801d005500b6013006000a6014e02800730091042603a005a003b007200010ec930c26204c3af771fba3f6c7ee0439824d0a7a005401d004c014e001c4b0009507b203100c28091016801d801d8039006c014804780002a5454b81111b7e3b343b588791fba26204c389861fb83f6c195c4b086190e96257c03a8748015409b83a305430e8a1d103a1874208ca09c426e046404e004d0076004800f805f44af000d0384033409480e2012e07a4126022402e4064400e00100048004c01100120022003004a83d90188061402e806900c6028003002c201cc024408e003b0072044c04a0036013201dc029008f000054a8a97022236fc766876b06573f744c40987130c3f707ed8879087512c003ac233841a0e94136c170832b0a84136830b861808320de80e8823502a0000076b21d9043e54b432b9fba26204c389861fb83f6c21d6d5b1b7e5136257802c027201a005b80d480ea024a031406f812801480420054006d000c050c1ed807c02c205f4000152d3b3a21d5777a1d7087cacd953d2aba54c443d087910f651341864075846708341d2826d82e10656150826d06170c3010640e8823502fa01f04ae8749000c04280f4824c044805c800e00240044004404a83d900ba01a4031806005840398074003b007200d80bd007700a4054000021d721e843c8ecd0ed6043e54b432b9fba26204c389861fb83f6c21d6d5b1b7e3b381d2c180895c03ce01d402c0748035402a81370747060406c4233032c04e418502a2095b0e8c150c3a287440e861d08232827109b811901380192028604d007603db009002541ec81850072044c04a003602f4026400021d708767ee0fdb10f421e44c40987130c3f75734832b9d9c3b3520fc4ae8015005a14f4070803a019201e01bd80e001d604bc0f401670102136c170832b0a84136830b85410a800a800e88235012202d001d8039006c01480a8014200003b5876a0ed21da03b3ad5b1b7e043e54b432b9fba26204c389861fb83f6c21d50eca89b0e940c041aa045a074e1d040a1808e06a60f6c1a9041800f800b8045017d010a048411a810f024e0de80be03000000087ca96aead5d5e21d5777a1d708767670ecd1d9e1d9e1d2439f829f0410092c144019d0170000148d285e513ca11876b5ab636fc08840e103a601d60204137813005fe118c26c83a5082e10583a0095a0c2c11880e08167019203e014f012f02a00508000283950763b58dbf5ab6043e075004081300382059c07c012f001a1cfc1ed035105820a1c1950142,
  0x126197bb8fdc10f021e843c887710e821c443b087210f6087643a83b60236010204d420d054f0ed418b80a10000b56c088541f8ed61da83b407660ec836e2154c05b0058010e1da41ec00aa0a9c0b88316860600ea0f741ab862c0c5618a83050629030005480bf812c0290023403900ce002c0c1000a00250034001400e002400440044003824d030a0174034806300c001d801d803902260250037003601320000fd91fb62a5e8764988130e26187ee0fdd5cd23b3a10ec87810f221c8b1dc3b580aa0a78181c0898000bddc7ed0fd31fb83f6c7eb0fd41fb03f647ee898383dd00ea11b43140094006c0000fdd5cd226104c28988130e26084c0097f130c262443b41ab80810c4413782a3846c0836136813a09700ed0189c06c81180496027002f00b8000c04f4032809600e8014c008001300240030003824d00ba01a4031806000ec00ec01c803600ee01480a1000021e46dfad5b02213f747674a97a1d926204c389861fb83f6c7ec876b291a12e2189414582c412de189c003013d00ca025803a00530020004c009000c000e093402e806900c6018003b003b007200d803b805200007ecad5b0ed61da83b208791fb63f707ee8dbf1b7c26186dc01109d9d2a5e8764988130e36e425c004083030c3a13602a2862512dc1da03138006027a019404b007400a6004000980120018001c126805d00d2018c0300076007600e401b007700a405080001fb221e47ee8db9152f26188764fdb1310261c7ee0ece822136fc6df0db85ab61dac3b507640ecc12de0204311076609c825b42a1024f12d8189800b03040028009400d0005003800900110011000e09340c2805d00d2018c03000e6042603a003b003b00720250037003600a405080005ab604427ee8ece843b2a5e8764988130e26187ee0fdb1fb21dac3b507660ece1d906dd44b706250a9a18903118000b56c3b5876a0ec821e47ed8fdc1fba36fc6df0dbb130c36e00884ece952f43b24c409870ecf0ed001d40a3824e06ac06f41a6829c074602080a500f1003a01a8021002e0202022803400f7016a02381be035301120b0c13a810c060e08980d90767075602043b3062208d6138c1d3032b02fc1d941d5001606080050012801a000a007001200220022001c126818500ba01a4031806001cc084c0740076007600e404a006e006c01480a10000b56c7ee8fdc1fb63f643b5876a0ec80442767421d952f43b24c40987130c36ee189c03a8147049c0d580de834d05380e8c041014a01e200740350042005c0404045006801ee02d4047037c06a60224161827502180c1c11301a007520b9800041a883d008860d51d9d087654bd756aeed10eababd0ec865726204c38986131226283b2c3b300aa04dc150c3b204140ec61d883b08147026802b40410048003a01f001700ed00d0050c047016101120a2808602a0023400581820014004a0068002801c004800880088007049a061402e806900c6018016100e600ec00ec01c811300dc00020d5022183d4767421d952f43b37bb8988130e26187ee0fdb1fb23f743b1c311007504e01d8012703260a9811a831080ec09c40528024035500d401f0270810101da0cb407b81430eba0df00b084e005860a28234030705c21d7c2a580eb12d60de80be0469083a0c003ac896a033e034017280f412d2001809e80ce002c0c102a50549002801940128096003401d00028053042e089c00e00100048004c011001200220030003824d030a0b90171805d00d2018c03002c201cc1d7810980e800ec00ec01c809400dc00d804c807700a405400005ab61dac3b5076410f23f6c7ee0fdd1b6e36fc6df0db91b7436e00884ece952f43b24c40987130c36ec189403a814712d00d580de834d05380e8c04104e201e200741aa8042005c13840450068065a02d4047075d06a602242700275021811a011302890eb8137c00035006b800885a811d9d087654bd756af6d10eababd0ec865726204c38986131226286dec4b583d812ce25984b28964022a1520310007f0eb61d68080061f0c3c04f0000418a044276755412ac221e843c8fdb10ea21ec10eca97a1d926204c389865eee3f703b344b500810606187426c075912c61514075030502881d5c0e002e002e206c00660151000c04f400b0304002801940128096003401d0002805300380040012001300440048008800c000e09340c2805d00d2018c0300076007600e4037003600ee01480a1000026186df8dbe1b70044276748791fb62a5e8764fdc1fba26204c3ad5b0ed61da83b21423096900ea044808700d8010401b000e8015005c107017101da060c00b403403d800e0023808a808900fe06a408601000c38046809801fa0102085826f05470a8c09d011280ce002c0c1000a0025012c0068002801c0048004c0110011000e09340c2805d00d2018c03000e6012201d801d8039012801b801b009900a405080005ab61dac3b507660eca1d9c3b201109d9d21e47ed8876043b3f7054bcfdd21d926204c389861b7312c601d413881da021c036008f80d7015203b01ec006c00900af000a807c027200b407684d500e0050c08a816100fe0a2808002a0026002043ac061b05c225880cf854501d40c140a20757000c04f40670016060800500328025012c006803a000500a600700080024002600880090011,
  0x13b387edae6928585070876541f2d5226184c3963b93100ee006f40fc826d02160c94021003a014c029c0002e8d5d5a87662e006598bc04c20988130e26244c5098612fe10e61dbc003009f021400c8021808000b400c00238034009c00f00150016015401c809882a505480a3411b82a305440a840ed80ae0028009400d00050c66007001200220022001c1978017061202bc04a805d00d2018c0300076007600e4089806e006c01dc029008f00006df0a98152a04446df876b283a50b4a268986130e507c7ed88791d9c3b34dc08a970984013e001802c81490518010001f8041007c00f402280440066004000980120018001c02a80af00ba01a403180a000c0047003b003b007200d803b80002a6054a941f1d9ab9a443c8ece37028fc40c2402c016802e804f800010f421e443a887410e621c4439087b370303420058039002f04a003700002d5258ee1968986810d060206f0095017002ec050c04700b7018c011800300fd0096042813801470086020002d0030022c00d0027003c0054005809c0048003a005403e002e005a00c80be808501c2070c1ac02c0030a0c2000b803305180050020003f004a010400d003e007a0014022804400380040012001300440048008800c015e025402e806900c6028003002c201cc024408e003b00720250037003602f401dc029008f0000a0f8a98152a04446df876b1fb62a5ca0e942d289a10ea4c4098710f23b3476709860633038602f41be809400dc0002f77283e5aa4b25966b130c26204c3963bac7e3f720c2007987540ea61d483a887500e9e1d383a6817a00017348ecd1d9c21ea02bc03981020376000141f15322a385498a94152a2a485488a90151e2a5c54c1d9d828c0290011c08b0016011a000032d2d52592cb3589891310261c4c509862c7e8b8cb1dc0e180eb0754118c26c83a5082e089813981e8065c08a00b3876e001a07500fe0102010a038409080e002ae0158028807b0108015c03780a001cc024410980e80168047001d8039006c01480a8008f000054c0a95152e04443b58dbf1b7c10e60cbc2a986320aa215480ba806b0000a26541ca85b50b2a0ecdbf1b7cb56c088541f8ed61d901db80980081020013782a3862408d8106c112814200016ad8110a83b1dac3b507641b7302ea0ea80cf8100044c0a2c162013c0756260c0a800005132a0fd41c8ec850b63b5ad5b28590442a0ecdbf1b7c36e06dc82a9008102340b98086022608d6138c1d3017e075418c403581420000a26541f9b705072a0ecdb91b7e36f96ad942c822150b63b587640ecc1306067c1d2810004e60ea007a81c113040540000285951323b2141f8ed61d996ad941c822150766dc8dbf1b7c36e06dd83188193026a1534317863009cc01ac0a801420000a0ed42ca89936fc6dd8db81b7c36e56ad8110a83f1dac3b307640eca1304064c09a8623075805080005ab60442a0fc76b0ed41d983b207651b6f09cc03ac2a584df060e089820e8300010206780c301300200067c000283b1dac3b507640ecc1d943b6142c822151326df8dba1b7636e06df0db91b8036dc18c00758981130025fc4bf097d12f825ec4bd015000016ad8dbf0ed500d602fc038007f005a032400a822500d825e406b841e002e00cc02c808300be0364048027603d0032804e008c00c800581820014004a006800280530038009001100110018001c126805d00d2018c050006001cc024403b003b007201b801b005202a00002d5b370226204c38fd9130c3f707ed8fdd371e36fc876410f9d9d2a5e10f5b7f0ec913ac03ac4bc097712ec07004ba897412e60f78145846c0aa20b102a8061f0c3c06c00a80000b56ca11943328a6043ea498dbf0ecd066202040be019e030c04c008780f8011201fc04580bf00d001c0017002d003a0054041006c0366035c000065743b2ba3c43aaeaf2a5edbf821eb71e3b3a087c76b0ed41d983b207650ed8260629a007583a60c4818683b6862f0c5c0eb00c981d3012005400a10000043e3b5876a0ecc1d903b2ad5b1b7e36f8a0fc11c897204dc00d80001310261c4c30fdd1312b9a4438cece9fa9148c0f7403a862c0c5618a83050629030005480bf812c0290023403901850128000032b9310261c4c089865eee3f707ed8fdd1fb258ee10780bf019f03f609bc0b180c9011201fc04580bf00d001c0017002d003a0054041006c0366035c000065743b2ba3c43aaeaf2a5edbf821eb71e3b3a087cdb91b7e36f86e00db8130312f2020427282e7046c000076b0ed41d943b387660ec81db0d39c0c980aa08280ca0193834f069c0bf80568071003a0054017002d00d001c004580bf011201fc08780f8034003d4000021f3b3adbf821eb71e2a5eba3c43aaeaf43b2195cfdc1fb63f507ec8fdd1fbc1d96194803a824e06ac06f40a500f100d40108080808a01ee02d40d6016f08380b880ed030603f007dc3b60174027c03e4064009f00b200cc00b876b018a037c0b9808c12e2001809e80ce002c0c1000a0065004a025800d0074000a014c00e00100048004c011001200220030003824d030a017403480630140018010980e800ec00ec01c809400dc00d804c807700a40000dbf5ab61dac7ec8ece9fb63f7043c8fdd152f43b24c40987130c044215b0097008700b00f600001fb62a5e8764988130e,
  0x10c6c00e803c01100156030c09c814e00b007100a7812a02a605dc0b8017602d005d009f00f90256032005b809f0064011c00302510292001c1c084e8046e076c05701a206a002bc05000b400ec00ec01c806e006c026403b80005070a0f89871fb60cb37348ecd1d9c21e454bd0ec9fb80ee808e00798412035403400b70374082203a809282bb0692031406f81f60442029005280a8018401b4032000600e002d415f82be050c052c03d8057015e01740318060012203a005a003b007200d80bd009900ee000032c9fbb43b254bcecd1d9cb9a443c8439838106a006880da0109024c00e84c580070aaa02bc04a80b400ec00ec01c803600ee0000986283a2a6054a941f5cd250707668a9790f23b384c38fdb0657131806840e200c8037c0c241d20017002a01c803600ae01600d404c501e4029c04e809c80ab0494084811182de069801e020a80060028009400d0005029200700120022002202bc04a805d00d2018c03000b4007600e401b009900ee000043a930c261c7ed941d06572a5e54c0a95283eb9a47668ece10f28fb8262c0e201a1037c03201d20309002a005c0388308018204c40578095006c026403b80005074b54964b2c7e59ac4c3898606572a6054a941f152f21e4439087410e6b9a47660ecb1d9a3b187650ec81d9c3f72262805502a505480a3415182a205420d400898000087c7668a9790f221e876710ec930ebddc7e98fdb1fba3f5c7ee0274063400740380053806f0000ba350ec865750707668a9510f4261c7670fdb153021e410f8439855507001dcc000285a51347670987283a3f6ca0e08791d9a36f8088876b1b7e507c54c0a95152e0abe0058192812600011701c8c065a58e20440019801705180434020003f008200f801e8005008a01100080013002400440060007065e025402e806900c60280030011c00ec00ec01c806e006c0148047800036f8088876b1b7e261a54c0a95283e2a5c0e001bc00b5015601c00450078005a010801d001501e204240360016131202a809882a505480a3411b82a305440a840ed80ae01600a3c0d10988000c052400389870ee602bc04a809101d002d003b003b0072044c0370036013201dc029008f00006df01111b7e1daca16944d291a2a6054a941d285850704c3941f1fb63b387668879130c0ac000e803c03250156030c09c814e0ee407100a7812a02a605dc0b8017601f204ac06400b7013e00c80238251000c00140a48011015e028003000b4007600e401b00770000e47942c283826184c3941f1fb6b9a47670ecd10f23f7654bdc8c087543b219644c480f307ac139c0bd0000b9a47660ecb1d9a3b187650ec81d8a3b3843ac0e2005907be00cc1bf80170000876432c88755d267eeca97ac7604a20684183046e022c005831a83df00b203e409580c800660c240da028e017a03041be801706fc1dc00030014004a00680028149003800900110011015e025402e806900c60280030009101d002d001d8039012801b801b009900ee0000fdb283a50b0a0e0a98152a507c7668ece08752a5e4c389865cd221e44c404c4037800e002d4055802d011401e000a8042007401c40b10126000117022f045c243b2ba3575688755d1e54bc21d90f621e843c832b863501e60f5420901aa0ee403a809282bb0692031406f81f604421dc4068016e06e8104405400c200da019020f80a4014a0afc15f0286015404c415282a4051a08dc15182a20542076c4c30985002c18d00030017002a01c002100b5007403800a58055009801ec0530057014e01bc057809500ba018c0500060012203a005a003b0072044c037003602f4026403b80002a5454c141d291a50b0a0e0986130e507c7ed8a9790f2b9a47668ece0873130e07e40de80d801ae02a4192810b009206d014700c106fa0b0000b0634012801b8000152c2a5443d0ece1fb62a6043c821f1d9abddca0e942c283858e6b245638930e26184c404c282c00368068809301090000b1c541c152c2a5443d09871d9c3f6c54c0879043e3b34195c31a00f307ac139c0d08554029e04a80a9817702e005d805b80060214010c040005a006000c801a004e007800a8023801600e4005c01980aa051804c415282a4051a08dc15182a20542076c05700b003440050020003f004a010400d003e007a001402280440c6600700080024002600880090011001803e409580c8000e261019780af012a017403480630140018004880b4023801d801d8039022601b801b017a013201dc029008f00006df01111b7e1daca16944d130c261ca0e941f1fb6507054a8a9810f23b347670a97077300e603a4070002d00f0005401d0049064a00dc0618087027204b80a7000008767eedc8c06597234876574688755d1ea0e0a99151c2a4c54a0a9515242a445480a8f152e2a60439c2aa00ea00b002a00d502bf018a053c003806d01060524003009f006400c0023802a002c02a80390131054a0a90146823705460a8815081db015c1dc00d080af00c601d801d8039022601b801b009900ee000142c283826184c3941f1fb658ee54bd0ecdcd23b38766887910ea21d0439887110e45aa41dc81840014004a006800e00240044001c3b781520290011c00b008d03680a3805e837d06fc0174034806301d002d003b003b00720250037003600007668879152f,
  0x1000043aae692a7754b6a9d421e90e621e4439152b90ec3b34767087404eb0ab8156c02c01aa029e04a80a9817002ec020c0d080af0132000152d843d21e443a087210e621d843aae691d9a3b38438827500dc022c00bc00b0359002a010801d002d011401e003800b50156021c0b7813908dc04b8174014e00b007100a7812a02a605dc0b80176016e01640030014004a006800280330ab4052400e0024004400440b40174027c03e409580c8000e0c2402a8017015e025402e806900c60280030009101d002d003b003b007202500370036013201dc00015302a54a0f8ecd1d9c21e57348a979312261c4c4163b038303f206f414d00d801ae0424078806c0000b1cd648ac71261c4c4898a12fe2620195c1ac80420114042c05a80e3051e05bc21002e8075401601f001c4074a053c095015302ee05c00bb016802e804f807c812b01900a7805b809f001a00c819800470ee8013c03f0050005e0058039055a000c0050012801a000a052400e00100048004c011001200220030003855901540a94152028d046e0a8c15102a103b602b81a800af012a0174034806300c003a003b003b0072044c0370036013201dc0290150011e000141f152a261c7ed8a980ed604447668ece1b7e36dc6dc0dbe1b7221e454bcfdc07790c6a00dc07180c3010e05bc09c812e05d0053802c01c4029e04a80a9817702e005d805b805902d005d009f00f90256032000b00330612094400b8006029202bc04a80a0012203a005a003b007201b801b009900ee0000a98152a507d7348ecd1d9c3f7621d4879152f58ec15680390016002e0e0402a80a0007600e4037003600007eec879152f3b347672e6921d9723c21cc2ac83080262263400b803305180050020003f004a010400d003e007a0014022804400380040012001300440048008800c000e0e00197809500ba01a403180a000c0047003b003b007200d8029008f00003b287660ec804443b58fdb1b7e36e06df0db91d9a3b3843c8a951530507c4c38a97099300e603a4090802d011400540210049021600dc071808702de04b817400580388053c095015302ee05c00bb016802e804f807c812b01900a3c05b809f084000181d5010a07c0020002d0030008600c81d280aa008e0a780ed80ae016015602ab8776001a0cc00c7819b033406380c681900308013c027007e007801400150034005e005831b801700660a3000a0040007e0094020801a007c00f400280450088007000800240026008800900110018001c1c0032f04ee02bc035809500ba01a403180a000c00244074011c00ec00ec01c811300dc00d804c807700a4054004780001d943b3076402221dac4c3941f1fb636fc6dc0dbe1b723b347670879152a2a5c54c0fdc098d038407140bc00ba027e0b0008280af00ee01480003c1676b4ee69da11fb82a544c38ece1fb62a6043c8ecd392673f4e4f9cbf1b7e1dad6ad811083300384033409480e2012e0001e0b3b5a7734ed081109b7e1dad6ad8a968105074c067c04081fb033c061809800c901f009dc03581500284000141d8ed61d943b307641b7236fc6df0db85ab6043e1dd80e201a1029e04a80a9817702e005d807c812b0190155005b809f000c0428040005a0060010c01900aa008e06880ed80ae0160155c0c7819b033406380c681900308013801e002a0068005c019828c0028010001f80250082006801f003d000a0114022001c0020009000980220024004400600af012a017403480630140018004880b4023800ec01c8113006c026403b8052011e00001111b7e1dac4c30987283e3f707ed941c08750cb254a8a97153021e47668ece283a0ab0016009701c4010e053c095015302ee05c00bb016802e804f807c812b019000dc05b809f0092001800a810a005a00c8040005a0060010c07080a903860d601600116030a013801e002a00680050012801a000a00700120022002202bc04a805d00d2018c0300091007600e404a006e006c026403b8052011e0000a98152a04446df876b152e3f6c7ee09862c77261ca0e843a86593b34767087913100aae075007080e0005a01e000a803a00d8042406b826d00ea11bc00681c2019a04a407100970580061405e80ae030005480bf812c0290023403900100026004800600af00d6025402e806900c601800730091042603a005a003b0072025001b007700a40508047800058eea0f8a951d9c3f6c54c08791d9a04443b287660ec8261c4c3043a8ed636fc195c31b8081023415583ba8300021e07a8093808503f804840170101011400740350042010405280788112064c06f4000065743b2bab577688755d5e54b410f8ed61da83b287660ec81db04c1c23780810606187431184d802840002d5b0ed61da83b287660ec836de09dc075846309b20000db71b7e36e86dd8db81b7c36e46e020c483e00342032018304e908dc134c1848251002e070c08b0014004a0068002801c0048008800880070c6c06d01c100bd01820df40988774002c2630057809500ba01a403180a000c0024410980b400ec00ec01c809400dc00d804c80003f6ca0e944c2838261c54bca98152a507c7668ece5cd221e44c303cb01f901520c980e8026d009205ec192801500d400e802600c0014e0001746aeed5d1e87662e046208b841964988130e26244c509860873,
  0x100a40540047800054a8088876b130e507c7ed8dbf1b7c3b347670879152a2a6054b84cc00460166012c10c001d00b000b80e20085029e04a80a9817702e005d80b40174027c03e40958163016e027c0bf0006033e07ec112810a0192051c021808000b400c02ab81160068013801e002a002c049801d007801c004bc0068105018600c83be83580610070c0e301e8065c059c2b10643002e00cc1460380057a0c2c1850014008000fc0128041003400f801e8005008a01101ae022906b6085c1ad022700380040012001300440048008800c000e19080578122012a0b7417202e300ba01a403180a000c0039805a011c00ec00ec01c809400dc00d804c807700a405400478000507ca950a98152a04443b58a971fb6261c6df8dbe1d9a3b3843c89880997001a0cc42398472027e0cc023883e307c4013c03f005006ee00bc00b0072015c04c43be82c5015e01b801b007700a4023c0003b627744f088986283e58eeb5496af2c9659acb1f964f2cde782ced69dcd3b422a544c38ece1fb62a6043c8ecd0ed636fc0888766864305800c200005eee507cb54964b130c58eeb1f966b152c2a5443d09871d9c3f6c54c0879043e3b344c403be800d066204143be077b0c820334047800076c4ee89e113c1676b4ee69da10ed61d9a6df8111152d058a158420b8416053c156007c013001020d44160828700b007100a7812a02a605dc0b8017602d005d009f00f90256032005b809f000c0428021808000b400c0019000d008e02a819800ae0262076c4cb01900308063c0cd819a031c06340278034009c01f801e0050005400bc00b06370c80005c019828c07000050020003f004a010400d003e007a0014022804400380040012001300440048008800c015e01ac04a805d00d2018c0500060023800ec01c811300dc00d804c807700a40508047800010ea54b87641fb61dac0888dbf130e36f8a0f8a98152a3b3476708790ecc0ac4153c3bd0081044a06780c30130019203e000683300aae0c20027807e00a000bc00b06370c80005c019828c07000050020003f004a010400d003e007a0014022804400380040012001300440048008800c00d6025402e806900c60280030011c007600e4037003600a4050804780002a5c21d47660ec83f6c3b581111b7e36f8a0f8a98152a261c76708791d9a262026582b0841b0ed4023c0000ecc1d907ed876b022236fc4c38dbe283e2a6054a8ecd1d9c21e43b2c32000ab065e01bc05a003b007200d8029008f000054c0a951b7c04443b58dbf2a5410e619080c2837d00017bb8fdb1313024401d405481bd132a092426a01d00a7409b422f006c01e2042400a8042007400b4045007801c2048407000f8024e04bc07a82e6038208e400681050c7e004000980120018001c19780af00d6025402e806900c6018004880e8016801d801d8039012800d803b8052011e0000ece1fb621e47668a9515302a5c08887660ed61d90a0fcdbe1b7e54a84c3898806570f040df40c882c0012a01740348063014001800730091023800ec01c8094000043d0ece1fb621e410f8ecd08752a544c40a98130e0cae54baf77152c0c7e157031f055b00017348ecc1d8a3b347630ecb1d9c21e22ecc00b0047011a0e0c05e837d026209403bc85600abe049c31e8235021e03e0097800d04a40ea014809940a80068007a82e603821de8037003600a4023c0000ecc1d907ed876b022236fc6dc0dbe1b722a6054a8ecd1d9c21e44c3941f056103860050012801a000a007001200220022001c2380250030005480bf812c0290011c00b008d070602f41be81310ef2264c13b806b012a0174034806300c001d801d8039012801b801b0052011e00007660ec83f6c3b581111b7e36e06df0db915302a54a0f8ece10f23b344c38765077a01e60e9c1250212044613580ce013b03ce0ca417e813a084a13b01ab800600b201a003800f7016a02ac1c0814b00ac014403d808400ae01bc05780a001cc024410980e8016800ec01c803602f4026403b80000cb28764a97931226104c28980130e26084bf8988130c21e57348ecd1d9c10e611c027581f7029c067009d863c049426481f08000556aa956e692a7754b6a9d421e90f23b38a95c8761d9a21c8109431d899109d608e04c8063a035413b01f080af0000766952aaab521c8a9dd52daa75087a43c8ece2a5721d97348ecc09920a72139c2098000b9a47658ecc1d9c3b34764155a843d21d626400a70412027618e410900990001734952aaa75087a43b887a10f221d0439152b90ec3b2e18e82758539029c1de009d898f0446263827603e10000762952a9d8c3b30aad48725cd254eea96d53a843d21e4767152b90ec3b3476584c884eb029c04e809d842405bc0f840002a55b9a4a9dd52daa75087a43c8ece2a5721d87668ec884ec074e03cc0ce042305d013ac2af01c407c205e80002a5554eea96c8792a5721d9734821eaa753b307658ecd1d8c3b287628ece1d90131c03cc1d384d6033804ec17e813a0000a95421eaa753b307658ecd1d8c3b207650ec51d9c3b3c43942af00f3074e09281090223033804ec21107770aba118421081e402f40002e692a55087aa9d4ecd1d9c21d20f840798170037806bc0d701bf03cc1048041808b017e0b7015e03d50190045005b063809d402bc0bd0099,
  0x104da030c08481260074001803c0149000e01bc05580af058403a005a0076007600e404a003602f401dc0002a54261c4c30988131243b254bee6910f23b34767032b84260388104c02c01e5040c046409700b60354021c0d78120035c06fc0df0070074800b40030149015e024401d8039006c026403b800010ea54bc87910e4b9a47668ece47de038e0160274856408dc0c1832281aa066606bc03803a4005a005402480a9022c092400b0110024c03040da00f8025e065016300f5038208e40da82090194074c0480014004a0068002801c0048008800880af00d60174034806300c0024401d8039012801b801b009900ee01480000ed6507e6dfad5b1fb958e24c3898821d910ea54bcece1d9a262443c810f878400e60384074802d002a012405481160182037007c002f01ea005811c8782036a082406501d30120003423b0014008000fc0128041003400f801e8005008a011000e00100048004c01100120022003000385630f0613b4091006b012a0174034806300c0024408e0076007600e404a006e006c014804780003b387ed88791d9a0444a95076b1b7e261c4c40a9515302a5c266c0e101b6066407ac0a60034009c00f001500160322041400a00250034001400e00100048004c01100120022003004a805d00d2018c050006001cc024408e003b00720250037003600a4000043a952a262454c098713102a5c7ee4dbf0ed6b56c088423b078102ae024407400b4023800ec01c803600a4023c00015302a5454b8dbf0ed60444a0fc439856300b0039c0f2823a040c046409700b3010e011800306030096042800e80150074051c021808000b400c0017002d00f004581ac008501c2038006e010f01f004bc01a004e007800a80178194058c068007a81c1002c08e43c101b50194074c048000d00280b140828025003400141148217044e007000800240026008800900110018001c3c082c006a013b4057812200d6025416e82e405c60174034806300c0039804880b400ec00ec01c809400dc00d804c807700a4023c00015302a540888dbf0ed63f6c7670ecd130e2620a9508791fb80f06064c18004620382059c09a822604e6003414f01b508ea0bfc09080e0065e015c037806b01d002d001d8039006c01480a1008f000054c0a95152e36fc54b4111283f1dac21cc3c0800d06600a78027807e00a000bc0d100160220049806180aa007404c415282a4051a08dc15182a20542076c03c077e01561e0000a00250034001400e00100048004c011001200220030003877f09b6094c0b202ff1334025402e806900c6028003000e80168047003b003b0072044c037003600a4023c0002a542a544c38ece1fb62a6043c8ecd1b7e1dac088941f04ed0ab0032414f000d0660013c03f0050005e005803900ae02622664086801701f40050012801a000a007000800240026008800900110018025402e806900c60280030011c00ec00ec01c806e006c01480478000835507aa0c4418a04446df876b130e507c7ed8ece08752a5454c08791d9a2a5c1e001840644021a01b801b0052011e00020c541aa83d454c0a95022236fc3b58fdb1d9a3b3843c941f2d52592cb1dd63f130e59ac4c404cc828c01e402ac06b00d501a8034c06900d100ac015c03780005d1abab5749aa542a6054c8a95283e10e61dfc081015700ac001c23a001701f4025402e806900c60280030009101d002d008e0076007600e40005eee26204c30fdc930e2a6054a941f152e0c920c2000a00250034001400e00240044004402e806900c6018001d803900008766f77283e58ee4c30fdc930e262021d423a028c008000fc020803e007a011402200330020004c009000c000e015400008765edcbac97792e9a5d2654c0a99152a2a5ca0fa3f100fa0c6607440b180c9021a003400b8105000a00cc008001300240044006000700ac04081600350015e025402e806900c602800300076007600e4037003600ee01480478000831506aa0f515302a540888dbf0ed63f6c4c4141f1d9c261c43c8ecd1fb80c88158420b841602ce0a78097800d0660013c03f0050005e068800b0643022004982ad00c309ae13a0098823703b61df801d00780156266015e830b06140050012801a000a0d70114835b042e0d68113801c0020009000980220024004400600070c8402bc04a82dd05c80b8c02e806900c6018005a0076007600e4037003600ee0148047800054a87ed876b022236fc4c3941f15302a547668ece10f236f826680e1810d017a0e0c1bf0122012a0250037003600007ed8a98152a3b3476708795cd22a5ea0f96a92c96261cb1f966b13100efc0074025802e008c0518059812300e608600b180e000b005f803c01c4033e07ec112803a029e04a80a9817702e005d80b40174027c03e409580c9022002dc04f855803440018097810a001a00c80218080066001680180047009e00d0027007e00780140015002f002c030c03900aa015c04c415282a4051a08dc15182a20542076c4cb81c603d00cb80b385620c86005c019828c07000af4185830a0028010001f80250082006801f003d000a0114022035c04520d6c10b835a044e007000800240026008800900110018001c32100af012a0b7417202e300ba01a403180a000c0039805a011c00ec00ec01c811300dc00d804c8077,
  0x104a00e0c05e85600abe269432201d102c60324210029e1348136813a02250c90105c091003600a4023c000021f04446df876b1b7c3f6c54c0a95283e3b3476708791310261c1964db989a7008e02f4128038306fc15802af863d046a043c07c0127025e268c2a081b202780eac2310122012a00d8029008f0000087c1111b7e1dac6df0fdb15302a547668ece10f226204c3941f06591d9a269802380bd04a00e0c1bf05600abe18f411a810f01f02688150011a02600204210029e083418c82a78791082c19002b0812200d6025401b00520284023c0001b721d90087c1111b7e1dac6df0fdb15302a547668ece10f226204c3941f06591d9826a011c81c1036a0328097833103a60240006847108e611c809f833006ee0f8c1f1004f00fc014001781a2002c0440093003a057a0c2c1850014004a0068002807806b80d6c1ad001c00200090009802200240044006000700de02ac4d080c3015404c415282a4051a08dc15182a20542076c3c784ed00d6025416e82e405c60174034806300c002d003b003b0072044c037003600a4023c000152a261c7670fdb153021e476681110ed636fca9501d7005801ce079411d0206023202cc0438046006e012c024801d002a00b8016814601d201cc07000780074155008801230160068808780f8025e065016301a001ea070411c81b50194001819881d301200428006847108e611c809f804301000cc002d003006ee0f8c1f1004f0068013803f003c00a000a801780160f200af4185830a0028010001f80250082006801f003d000a0114022035c06b60d6800e00100048004c0110012002200300038563018602a809882a505480a3411b82a305440a840ed878f09da02bc035809505ba0b90171805d00d2018c03000e6012202d008e0076007600e4089806e006c026403b8052011e000152a130e3f6c0888ecd0ed636fc7670a95153021e454b84d08193019405f009e00f5026a043008001b504a605903c70032018c06900230123006e02c0046813401d802b4041007100d8005c024001d002a00cc03e002e005a06ec0aa014601d201cc082800d0f1a01e001d01260028010001f80250082006801f003d000a0114022001c0020009000980220024004400600070ac6030c035809500ba01a403180a000c00b0807300910168047003b003b007200d80290142011e0000111152a2a5c54c152a10f226227eecece1d9a36fca0fc76b06570f2005f80cf810c02000a2c2a882c4036404f023b8175134001ac0a800005aa4b25966b2a5421e44c4432bac7e3f76767155b9d9a54eea95d52da83f51363b5ad5b283b50b60884dbf1b7c0f1c039c10500b3000c267c0330030017c02e809a80b8038c0cb8065009c015e026403b805202a00002d5b283f5aa4b25966b2a5436fc6df011093110caeb1f8fdd9d9c556e766953baa5754b643c876489a00602048009400bf065804b8323816e082202900528043034604fc06601c004f0267806281f604421e303c583ad00da01903c504f000cc05e803b8000592cb35952a2b3636dc6df8dc01b7c831e0884988865758fc7eec87910e2b9a4a96d52baab73b34767021e899f025403cc041834a09de068402c01aa015e05e804c800021e043c887210e821d4438ae692a5b087a7648ecd1d903b187660ec51d9c21cc191c4ce808000b413b811d81c502f0085808b8546053a019803b800004424c4564b065759ac7eed52baa5b54a8acd88751d9a3b3843cae6910e236e62678003009f00da04ac06f8000566ca96c21f10e500cc108802c00f303521040075012505760d2406281f604421e303c5810802cc02a0061006d00c81e28003020a015e05e804c80770000a95d52daa54566ca9e955d1d9a3b3843c887510e2b9a443904ce81a1023204b804f80870000a95d52d90f421e4439087510e221ec10ec105008103400468086046b09c60e980bf027807581e24213817500d605400a100005076a0fd44d9b7e36f96ad942d82211dac3b30764047707c00e9413983a8038226702a982e7026a0a9803581500000a0fc76b0ecc1d90a16d44ddab650720884dbf1b7236f906383c480eb05c20a24145010c0a9a0de80be019304ee01ac0a8014200003b587660ec869cf6ad942da89b04426df8db81b7636f86dc8765099c033e07ec08000f50aa6064c173813504f01e203c386460f0c1e140ba806b02a005080005ab61d903b58766283f50760884dbf1b7c5070109c075861a0eda18bc317000036dc6df8dbb1b7c36e46e020c78278005a0054074806c00e602c007000f8025e03d40e08239036a082406501d30120010001f8041007c00f402280440020004c009000c00d6025402e806900c60180048811c007600e401b005200003b5941fdab636fcecd4988952a2a5c54c032b8875043e1e3412484260212005812a000d0f0800e800a00250034001403c001c00480088008800700de02ac4cd878309da048804a805d00d2018c03000b400ec00ec01c806e006c014804780003f6c54c0a95022236fc3b5952a130e3b3843c8ecd13100f1e07080db033203d6053001a004e007800a80002d52592cb35963f1fb904426df876b5ab60cb209501808143047003b40fb845a074e1d0403e016f06a6012005a80ec01140e10138804203f20d64054806c002a071c29f01d0,
  0x104436ad8dbf0ed6262054a89871d9c3f6c54c08791d9a10ea26f4081015700ac0001749ae8d5d5aba3ca9915302a5454b941f08730668135c3cb09b9026226e00e980c90f2e0a780da84db04a605904db82ff136c02bc04a803600ee0148047800004446df876b130e2a6054a8fdb1d9a21e4767010f864d01c0055c03780070f00024407400b4023801d801d8039006c01480478000835507a941f418a04446df876b130e83107ed8ece1d9a21e454c0a9528382a5c26e400b0047011a09401c18796136a02f40da0644075c0488037003600a4023c00041aa83d40888dbf0ed683147ed941c2898507454c0a951d9a3b3843c941f130e262026e0088003a0492192c32480c40f260254037003600004c4ae691fb92620a0f898715302a54a9562e0152e136a00540e3806c000e02c02aa80f8025e065007a81c10472082406500900f2a00584da09b3015404c415282a4051a08dc15182a20542076c3ca03ae015e01ac04a80b400ec00ec01c811300dc00d803b8052011e00001110ed636fc087ca95130e3f6c54c08791d9c3b346df04db055a000e01c82ac80ae012a01d801c803600004c4432b95302a557348ecd1d9c2a5e7eec879283e0f2a011c05700320472027c0e302c6019001601c2833105b80af00e781e4029c04e8125021204460b781a6047108e611c809f813904280ddc1f183e2009e001815e830b06140050128814906b80d6c1ad001c000e0e04057806b05ba0b90171805d014001d801d8039006c026403b8052000054bd0ecaa553b3443c8ece0ed6043e6df2d5b1b7e3f764c4432c89b40ac408e40e302c600b00e1416e02bc039e07900a7013a0494084811182de069804e410a000606620428238847308e404fc021808000b400c01bb83e307c4013c01a004e007800a800b0428057a0c2c1850014004a0068002835c06b60d6800e002400440044003832f015404c415282a4051a08dc15182a20542076c3ca03ae015e01ac04a82dd05c80b8c02e806900c6018003b003b0072044c0370036013201dc029008f0000087c8791fb61dac0888dbf130e36f854c0a951d9a3b3854b84d981c406480002e691d903b2c7668eca1d8c3b3076708758385034404244d9003a00e601e04d8878d0618010001f8041007c00f402280440020004c009000c012a017403480630140018005a011c00ec00ec01c803600a4000076b5ab636fc087c43a952a2a5c54c09888657085001c800b80ae01f4000043b2f6e5d64bbc974d2e932a6054c8a95152e2622876432ba83e0618045823c010d0aca0050012801a000a1e1000e00240044004400389b006fe00584d780c1070406d012a837e135c043c07c01ea024e04bc0ca02c6034003d41d482e6038208e410480ca012026b4057812200d6025402e806900c601800488213016801d801d8039012801b801b0052011e0000dbe02222a547ed8a980ed636fc087c8791d9c3b344c3898807940220092401d0636014e0001746aeed5d1f188098945c20cb24c38988131443b3170032d08731360071c00a800700e215540578095016801d801d8039006c01dc00028382a544c38fdb15308b844390a9790f23b397348ecd0657135e016027485640c9411b818306450f2606d04d6011601b800bc00b09ab0028009400d0005003800900110011000e0cbc1d700af0244025402e806900c6018003b003b007202500370036013201dc029008f00006df142c283a2a6054a81111b7e1dac4c38fdb131050b47670ecd283821e44390871152e135c039c02c00b305b80af00e781e4029c011809c804b000c0074085002e0086020002d0030010a0d601600147022c037001a004e007800a80178014004a0068002801c0048008800883ae015e048804a805d00d2018c03000e6007600e404a0036013201dc029008f000054c0a95152e04446df876b130e3f6c4c4142d08753b38766832c90f221c84388fdc09ac01520d640360015008400e8016808a00f0038409080e00c7e048804a809101d002d001d80390128000087a1d9c3f6c43c821f1d9a2a5c54a8a985eee5070a16141d0875261c4c4032b89ab011a02f41c1837e135400583c90122012a01b801b0052011e000076b022236fc6df010f9fb62a6054a8ecd1d9c21e44c40987283e135a06f40fc826d01e20424021003a011401e009080e0024e04bc11401670ac405480a402c500e418fc1148217044e004000980120018005c003838001f40cbc00b0792015e048804a82dd05c80b8c02e806900c6028003000e80168047003b003b00720250037003600ee0148047800021e47ed876b022236fca0f8dbe15302a547668ece021f261c4c40a9709aa000e11d02380250030005480bf812c0290011c05e838306fc26a40e309a8134e26980578122012a01d801c803600a4023c000021f36f80888dbf0ed63f6c54c0a951d9c21e4766941f1310261c19643c901c402ec06840f2014e0494084811182de069802dc04f813904280018033010a0064010c040005a0060070c01a004e007800a800a0025003400141ac001c004800880088649002e001c1c000fa065e0eb80578122012a017403480630140018008e0076007600e404a006e006c026403b8052011e0000dbe283e2a6054a81111b7e1dac7ed832c930e262043c88711d9a3b3854b84d48047,
  0x10096042c088038606ac13504e100c100921e74104020705be0a740ce8117025a07ac028003c002c04e000b801d002a010801d005500b6013005300a700d60280073009101d002d001d8039012801b801b005202a0050800021d910e64c48980130c261c7668988152f3b3843c8fdca83f1dac3b22d5b022136fc6df0db82c96138a03ac1d3054d02a00002d5b1b6e36fc6df0db81b7236f06de8767856802fc159808602c4036411dc11e011b01fa012c3ce079b018201243ce80160270005c024001d002a0154081805b0098028016100e6012200ec01c809400dc00d8029000043b221cc989130826004c309871d9a262054bcece10f23f72a0fc76b5ab636fc08847641b7c261427083cd010e002c04e000b801d002a015402d804c01400398048803b00720250037003600008764986131226104c00439930e3b344c40a979d9c21e57349c8d879d04f005d44e089c0026a030404084e6032601c423d01c607600b181d7847901e6005402c0238038e0e1416e02bc039e07900a7013a0494084811182de09ac0d3000b0139042826fc0030025003405240120022000a1940057806b00d2018c01d803900dc00d80bd009900ee01480a8014200004c48987131054aa54bc87921d93b347ee541f9d9cb56c088476b1b7e10ea2710300856709de07d8110842500c80198029800600b201a003800f7016a01700a5805600a201ec0420057000e004405780a000c00398048821301d002d003b003b007200d804c8077000054bc8795cd23b34a954ece48bf0ca005f82b3010c058806c823b823c01fa1e7008d804b0f360304024879a0090007400a810300b6013000380d90138007002f00b8002803c00a60254005e00a8086829b00fc04b4028037f04aa017416100e6012201d801d803900dc00d8029000059acb2590ec9312261c7668988152f3b3843c832c9fb9507e3b5ad5b1b7e0442b5484df847009b809c0000065943b221cc989130826144c00987130c262054bcece10f2b9a47669cbd879c08e010a40a380000cb28764439931226104c28980130e26184c40a979d9c21e57348ecd393b0f3611c008f80a9000019650ec887326244c209851300261c4c30988152f3b3843cae691d9a72361e6800a064e004a0068002801c002000900098022002400440060016000e1e542ac84e8015c04c411b81db137c02bc04a805d00d2018c0300076007600e4037003600ee0148000152fb56c54a89871d9c3f6c54c08791d9a1dac0884dbf283e0f44001c238047404a006000a9017f025805200238016011a02f41c18350015e048804a8076007201b801b007700007ed8a98152a507c4c38a979d9c21e57348ecd1310137c064c0be04620382059c09a810c04e606d412982ff0c9e1e640d20123016000c80630046006e0c30076008200d8023409a00ad00e2005832700170090007400a803300f800b801681bb02a8051807480aa00e604c415282a4051a08dc15182a20542076c00a0105008000fc0128041003400f801e8005008a01104de801c002000900098022002400440060007028a003432683ae00d6025402e806900c6028003002c201cc024408e0076007600e4089806e006c01480a1008f000008889871fb62a6054a8dbf10f23b38766876b152e138c001805200b301a0039c4de0043034604fc01800cc017c070005d064c01700718197009c08ee26ec057807700a4000144da85b1daca0eed5b283f36fcb25966b2d5204424c4432bac7e3f76a95c8791d9c54b6a95555b9d9a54ee6df03278301042404a009d832c029c191c11c01aa06e810440b700c503ec088405280a400da0190003020a00cc02bc0bd009900ee000152bab3654c443c88715cd254b6a95555b9d9a3b3843a84de017e0c98043016201b20000a26d42d8ed650776ad941f9b7c36fc195d64b2cd654ae76708792a77556e7668110aa5b26227eed6a90ecd1376064c065013c01ea04d408001b502c8193032307880f0e1e143c3006b0284000144da85bb56c6df832bac9659aca95cece10f254eeaadcecd2a5b26227eed6a9283b0442a0fc76b28380f3202f801800ba00cc02e04dd009c0acc01dc02900005136a16c76b283bb56ca0fcdb71b7e36ecb25966b2a573b3843c953baab73b34088552d93113f76b54832b9b7c0c9804000cf828b0aa204f00ba847700d60540000283f5136a16c76b5ab636fc6df0db71b76507608847640566060210400940166000c02cc1eb0413064806c4073879801000168277023b038a05e010b01170060151814e80be04f002e809a80b8038c032804e00af02f401dc029015000016ad941f9b6e36fc6df0dbb2d5204424c4564b065759ac7eed52baa5b21c843c953baab73b34767076489ba0378022c0798422030e08e002c01a9082003a809282bb069203140fb02210210059805400c200da0190003020a015e05e804c80770000a95d52dab3654f4aae887210e221e57348ecd1d9c54ee43a83cc0330009e01f8028002f0000b54964b2cd658fcf059dad3b9a76856ad8a95130e3b387ed8a9810f23b347ee01109b7e1dac196432703340ac6028004880e80168047001d8039006c0148047800036fc3b5811115302a5454b843981450580041423b00100026004800600af02440174034806300c000ec01c803600ee0148000152e,
  0x1007c00f402280440452085c1138010002600480060007028a0488035809505ba0b90171805d00d2018c050006001cc024407400b4023801d801d8039012801b801b0052011e0000ecd1fb621e4088876b1b7e2a6054a898713102a5c1ec00d080e7023204b805b009f0166021c0190046006e037c0e1804b009205cc00b801d002a0018019802e005a01900dd814601d200c0046007306b002e00828476001a0240065009c1392051c054811601b800bc01504f10028010001f80250082006801f003d000a0114022001c002000900098022002400440060007028a03381538122012a01740348063014001800730091023801d801d8039012801b801b009900ee0148047800004446df8ecd0ed63f6c54a8a971530261c4c4087906591394023802300890096043000e800602f800b80320193028c00c0046013c01ea01cc1ac013500bc04000828476001a03240da80d904a605904e407a5028e045806e002f005413c400a0040007e0094020801a007c00f400280450088007000800240026008800900110018001c0a282a7024401ac04a805d00d2018c03000e6023801d801d8039012800d803b80520284023c000022236fc7668879130e3f6c4c40a95152e2a603b5832c8ec8139206840738119025c02d804f80b3010e0018033013d0064011801b804301000168018035808ec00343d381c30096012400b801d002a00cc017002d0376051807480730f4c1e940a380a9022c037001a004e007800bc01504f10028010001f80250082006801f003d000a01140220229042e089c00e00100048004c0110012002200300038145019c0a9c091009505ba0b90171805d00d2018c050006001cc024408e0076007600e404a006e006c026403b8052011e000032c8ec82a6054a8a9702223b344c38fdb131036fc3b588791b7c139008242b480900000a0fcdbf0ec836f83b5941ddab6043e1e9c2b4800d058a0414047800076c4ee89e113c1676b4ee69da1022236fc3b20dbe0ed6507654b43d30058016c03400b701a901d404940628066017e029008400a800da07f40030115006e010c040005a00600d600608049002a00b409b007f0152045806e0034009c00f0017802a04f213c400a0040007e0094020801a007c00f400280450088007000800240026008800900110018001c0a280ce054e048804a805d00d2018c0300091023801d801d8039012800d804c807700a4023c00015300cb254a8a97022236fc766876b130e3f6c4c40879283a0f4a01cc07080e90000a0e8a99151c2a4c54a0a9515242a445480a8f152e2a60ecdc09b01a101a0049405200a80086016801a003c002c11ec07c812b0190020c00300b700640d600e18308021a005c07d005f0028009400d0005003800900110011000e051406702a70244025402e806900c60280030011c00ec00ec01c809400dc00d804c807700a4023c0001d9a3f6c54a8a98152e04446df89880ed6261c43c941f04f106b20054021003a005a022803c00e1024203800648420053c059023a82ff0f480b1c006815202900b140828072032204340028229042e089c0080013002400440060007028a025416e82e405c60174034806301400180073009101d002d008e0076007600e404a006e006c014804780002a5454c0a97022236fcb1dc76b130e26244c4032b847b037a07e413680f10212010801d008a00f004840700127025e08a00b38000043e54b574688755d5a876432b9308261c4c4898a130c25fc4c4076482c7021e0680042846f005c01d400e80d7027001b000a802d01c215a40c0015202fe04b00a40072021a0014008806b00c00398048821301d000ec01c809400dc00d8029014200006df8dbe5ab658ee4c3898813120cae876443a8ed61d9854b410f8ec80f48153c0408776033c061807a8130044a03e0064806b02840000dbf1b7c043e3b587660ec8b56ca0ec2b48193060011880e08167026a089813981b508ea0bfc215012301600c341478555010401b00a500f1002c007400a806a00840e0402d804c0180029800389c709d004c411b81db0f461e884e3000d0c9a0eb8057806b012a0398048821301d002d003b003b007201b801b007700a40508047800004447668a95130e3f6c54c08791b7e1dac767015383aa07c00e9420b822604e607a0197022802ce1db80a800005132a16d41fa83b1dad6ad941ca85904426df8dbe042a006e021c03880b6002a01600e3838505b80af00e781e4029c04e8125021204460b781a600160272085032700060028009400d01490038004001200130044004800604e8026208dc0ed87a3000a19403d100af012a0174034806300c000ec01c806e006c026403b805200016ad8a95130e3f6c54c076b022136fca954a979d9c3b3443c843a89c70abc0928109013b03ce0ca409d042509d803a815d80a8018401d0056001a138a036408c009c00bc02e0078014c005e00a800b0138021a001800b8059003a01a000a807001ee02d40a5805500ac016c028804c00f6021002b800713880d400028650015e048803180a001cc024410980e8016801d801d8039012801b801b017a013201dc02900003f6c4c3941f8ed6b56c0884dbf21d92a5e43c952a9d9a3b384c403d183aa01d6089814583ab010215a032887a113861e803cf879e0aa4046c14701b4,
  0x1012801b801b007700a4023c00043a73f6c08881109b7e1dac76750ec952f21e44c389882a560cac0058017806c01b80a680002c735aa4196898680c700b0061c10c0114016611fc1c2006806ae01d4017012c003a01c809c042b04aa15b808700d8023e035c054806c002c09503d58014004a0068002801c0048008800880ce02440174034806300c0039801d8039012801b801b009900a4023c0001fb604440884dbf0ed63b3ab1cd0ec8875261c4c40a979fba087643c887510e4261827400d080c805d20b2004f807500b215b4019847e002e028001d8039012800d804c800043b2195e2e388752a5e4c20981130a261c4c1097f130c262010ecfdd1312b9a443d087910ea21c8b1d8215803300b2005c05b830800be0050012801a000a007001200220022017403480630140018001d803900007676f77130c26204c38fdc843b43b254bc43aa83e0adc11f000b056c06080050012801a000a0070012002200220174034806300c000ec01c806e006c0148047800026187ed8fdd022126204c3843aa1d92a5e76748791b7e04443b58fdc07ab0ad204f00b200f801920000dbf0ec81daca0eed5b021f01b407500e9000d042815b026a800605d4095801b007700a4023c0002a563f647ed8fdd10f2261854bd0ec9310261c0888ecea83b1dac6df8fdc09d7006e11f400380aa002203040028049005e00580360015036e134026784ce099a14d8266045b0996037014d09cf00fe033802e8060012201d801d8039022601b801b009900ee01480478000261c4c401110ed61d906df8ece9fb62a5e8764879283a13a803b8038006500a600b4008000c000e013000008765edcba69747952f087d0e9887b10f421e51f780db80ac003401d001e00c203d605104e701b001b20ec80a8805e045400341d880f4014a01940a600920054005011e011b000a013c07e804b00b80490138811203a4014c2b5013b00cc1ea809d00580ca6047c06b80a900920304126847d03ca08e81030119025c02d800b00bf0270001800b80590090007400a807000d4010801d00ab0296015402b010300b6013003d80c0014c029c0378007139a017c279007f019c048802e80630140018016100e60122084c07400b400ec00ec01c809400dc00d804c807700a4023c00010f23f6c4c38988022250743b587641b7e3b3a54bd0ec930c139e09e02730789040e0a740ce811700d60540000285b5136a0e6d5b02211d983b58764283f36fc6df0dbb285e139c08e40e081b5041204bc0e9809000d6000141c8ed61d90a0fed5b1b7e043e0ec42b507a903b4047c06b80a90092030409100360001734821e9fb93b3ab3456389fb63f74b24541d2c73261c1964986131021d6194c07702be050c000174d08730cb254bd7b721d9087d0e9952b90f621e843c8fdd847d015400dc06081900308063c0cd819a031c06340248034009c00f0015001600d80bec05489cc002a00b403800ee00280194012801a000a014c00e001000480088008800c00fe033802e806900c60180048803b0072044c0370036013201dc029008f00000888879130c261c4c4076b0ec836fc7674a97a1d950747ed843a89cd0ca4001808a00b604720f6002c01b5041215ac18702c90550076817482c803a6024003a800d01540f742b6003701820ca0193834f069c0bf808700d8023e035c038806c08f800581370116002a00b403800ee00280194012801a000a014c00e001000480088008800c00be13c803f80ce024401ac02e806900c601800730091007600e4089809400dc00d804c807700a4023c000283a044443c8986130e26203b587641b7e3b3a54bc43aa1d93f6c4bf84e600aa006e030402482fb015204580c80184031e066c0cd00dc031c063401a004e007800bc015001613960054016807001dc0050032802500340014029801c0020009001100110018001c3d4007f019c048802e806900c601800488076007600e4089809400dc00d804c807700a4023c0001b7e04443b58ece90f243b254bc987131050747eda1d504f201060018064005907b00160019856b061c0b2415401da05d20b2000b8075083c0f74055026e006e03041940327069e0d3817f029a021c036008f80d7015201c4036047c002a00b403800ee00ca014c008000c000e1ea003f80ce024401740500060012201d801d80390226025001b009900ee0148047800036fc088876b283a3b3a43c8fdb21d9261c4c40a97c3aa0cae272c02c00d001be079411d0206023204b805b00a400da02fc0030115000010fa1d32b3654c443d087910f654ae03b806080aa0092134026784ce0998116c265829a0ad406400c201240068013c00a041c05c407681830092050c019405200d0034204ac08c812e016c005804180bf0270001800b8059003a0054038006a008400e80a5805500ac016c026007b01800298053812200ba02800730091042603a005a003b0072044c04a006e006c026403b8000874d0ea887a10f22a5f73490ec930e26207ed941d08730f5001d408700d800920304304812201280001668ac713f6c7eeaf772c91507419656399302260c4c38980130425fc4c40986056a06b2010801d00a9011401e0036012101c00054093812f005a0b980e0813604721e980da80ca03a6024000682c5020a064400b09ca09e2010001f8041,
  0x104443b58fdb1310261c43c8ecea1d92a5e195c98605710cac09583d6035d066a0f9c000130c0cae7ed8111131036fc3b58ecea1d92a5e43c8987022113b21dac00b81e50066021c02c89d7016e13c802f8090001a1eac12b80ca07ce0488050003b007200d8029008f00006df81110ed610ea7ec8fdb152f43b24c40987130c3f7410ecece90f23f70276823a001713ac00cc11580590106032008a00b600be016004800d002dc06a40750125018a037c00680a4021002a0036813d00ca025803a005308f8004000980120018001c04980ca07ce0338091005d00d2018c050006001cc024403b003b0072025001b009900a4023c0000ed6044443c832b9fb636fc54bcecea1d926184c40987043d13b004e000b801d002a015402d804c0000ba3d757ae9343b2195c989131426204c38439809300220014003802f0f5c03703d6865604ac0d7400687af066a0f9c04a806000ec00ec01c803600a4023c00015302a540888987131021e47ed8ece9b7e1dac54bc32c8570034204500fb81e4029c04e8041808b033804ec003005900d002d43bf814b00ac014402b800713aa02240b1817e01d605901bd83dc03f6089406484f204ea074802f8127025e02400f4032e019408a00b383e7019c025405000e6012203a005a011c00ec00ec01c8036013201dc0290150011e00001110ed636fc767432c9fb626204c38a98152a2a5e43c810f87af0154011823a004b002e0074019802e00b201a0041808b0190045002c00d002dc06a40750125018a037c0520108015001b4003065705f6051c08b01900308063c0cd819a031c063406e0034009c00f0015002f002801940128096003401d0002805300380040012001300440048008800c00be048802e806900c6028003000e6007600e408980940000767421f10f421e443da1e3152f0cb28766f77283e26204c38fdb087513aa070c1288032015402dc2b702fb022c06400c2018f033606680c7018d01b800d0027003c005400bc00a00250034001400e00240044004402f812200ba01a403180a000c000ec01c8113012801b80001d9dbddca0f8fdb21d910ea1964a97930e262010ec32b816f016a07dc045020a00cc02d80210059010e03c40198006002c005c09e802f021a019404b0074000a014c00800130024004400600070f5c037017e07ad0cac003406d025613a8033802e806900c6028003000e800ec00ec01c806e006c026403b8052011e0000111130e26207ed8ece9b7e1dac8764879152f1d900f9c012804e042a020004b013d050c0afc02980aa00b80f980028016018e042400300150074052c02600a709a0133c26704cd0a6c133022d84cb0492033802e806900c6018004880e8016800ec01c811300dc00d804c807700a40000879130d3f6c0884ecedab636fc3b58a97a1d910e61eb800e804b005c011803400b301ce08280330032038609440a38304022c095000b07ac016c021c003013d002801940128096003401d0002805300380040012001300440048008800c000e1950067012200ba01a403180a000c0039803b003b007202500370036013201dc029008f00000888ece822136fc3b58fdb130e262043c952b952f43b24c303d68075049c0d580a500f100d40108080808a01ee02d40d6016f0caa1070171030603b407e00fb805804ae15b01d9847c03ca08e81030119025c02d80438006027a019404b007400a6004000980120018001c32a00ce0244017403480630140018010980e800ec00ec01c8094006c026403b8052011e00001112a5736fc3b58fdb022121e47674a97a1d9261c4c3098806570f5801e0055803a027214f809d00b4007600e401b0000262573489861fba261c4c4021da1d92a5e21d487282570084058804500e3016a05bc0fb820a00cc08ac05b00870000ba4c21f2b3621e843c887b2a57087654bc43aaead0cae8764fdd83b3002e00cc046805900640000fdd952f0cae21d5749a1d954b408ac012804e042a020004b013d057c0a1815f824d07cc005809c0006002e007400a814b00aa016c02600ce02440174034806301400180073009101d002d001d8039012801b801b009900ee014800010f226204c389861fb604427676d5b1b7e1dac54bd0ec88730ca802480328014014a00d007a01b603840230032005300b800144e9842c07ca0174034806300c000ec01c803600a400001109b7e1dad6ad8ece8659087a8764a9788733f720f98052806501e802480e1001402982748015042c07ca01740348063007600e401b005200001964fdca1d904426df876b5ab610e67674a97843d5aa4274c056001a00e800f006101eb02880000ece9fb9087a1964a97a1d910e6bac942f842c018401d00a200ac038400680db09d10068053001503e500d2018c01d8039006c01480002d520cb27ee50ec822136fc3b5ad5b08733b3a54bc21eac7e13a408540128096009c059819901fa00007674fdc843d0cb254bd0ec88735de4a27c1f28166012c07e810a81c2004a07ac12a003c036c00d00a6002a00d200ec01c803600a4000163f2d520cb27ee50ec822136fc3b5ad5b08733b3a54bc21eac9613a202a408b0049002c01c401b89d0018e005400a0025003400141f2056f005a00700120022002213cc003800600f60ba8038012200ba01a40318060012201d801d8039,
  0x1037002500508000262a00b003700a10000196c00c8036003c0002f7780a102f400780001d9f02b4026400f000021ee009c03b801e000010fc002005200300002e69801e02a000600001b810176050800c00001db2026c39e80180000088c00709f300a80002d5b801813e40150000196302b027c402a0000197602c44f800200001626c02a001500e200b401b80700766001809e8065012c01d002980100026004800600070cb200584f787b4001a27b83d980aa02620a94152028d046e0a8c15102a103b6096c06702a7012a27b402e806900c60280030009101d001d801d8039022601b801b009900ee014804789ec13d627a84f489e813ce27984f289e413c627884f08000000e0080139816705fe096421500ae0348048c186828f034401c80760082029403c4084801700900074035004200740154081805b0180029805380a00584039810980e8016800ec01c803600a400010ec865726236ad8dbf283b1dac08844398659004a013810a8080012c04f400302be050c0afc0a5800704b4033802e806900c6018004880e8016801d801d8039006c026403b805200004c4487902213b3b6ad8dbf0ed62a5e7eed0ec865913de070809f81c502f002e8027807e00a000bc00a00250034001400e00240044004402e806900c6018001d8039006c014800021d90cb24c441109b7e1dad6ad843a825a0f64019402980100018001c3d88037009200580360015036e02c003f80003b3a4c4443b2f6e5d34ba3ca97843e0cb443d887a10f243b27eed41d07b4002e011c00b0033006408ac02c80f6015c017c04800ca01b41ec8032809600e8014c00800130024003000389e0019c01740348063014001800488076007600e40370036013201dc029000036fc3b5ad5b1d9d262243c8a979fbb43b2087c4f70058019003400b701a901d40494062808301480420054006d000c02dc0330000087cacd953d2aba54c50ea887a10f221eca96c07b0016009201b001b801501dc06dc058007f0000767498888765edcba69747952f087ca98959b10f621e843c90ec9fbb0cb4a0e83d90058019007dc041819c05b80af00e781e4029c04e802f82750276024009381d2019408a00ea00da0f62001802c801500e002d4055814b00ac013003d805700de033802e80a000c0024407400b4007600e40370036013201dc0290000262254bd0ec9fbbb56c3b58dbf021f3b3a43c843989e0002c01b023e80b000fe0000ece93115d3421cd52b952f5edc876421f1fbb21e443d887a2c730cb4a0e83d881c2027e07140bc00ba009e01f8028002f002c277c00b8048003a0054019807c005c00b40dd8154028c03a40398105001a277800a0040007e0094020801a007c00f400280450088007000800240026008800900110018001c0a2809500ba01a403180a000c00b080730091023801d801d803900dc00d8029008f00000888a98152a21e47674fdd931136fc3b58a9707b30060019005f008c017402e004e0259000c09600d20046024600c801b80b001d802b4041008d00e201b018600ce012a017403480630140018008e0076007600e401b009900ee014800015302a5454b9639ac775926b34c8795ab636fc3b5811093113b3ab548fdd865713be064c0be013c01ea04d40860100036a094c0b2065800d605080005ab636fca26d41da85b507e088476b0ec804b205f82b3010c058806c823b8000507e3b2076b5ab636fc088544da83b50b66df032c005801ce04ac0f2823a040c046409700b60166027c043800054aea96d53b90f421e443d821d8258008e00c800b80b701f402b802f8090019403684ee800613b8010c0180034005400582140014008000fc020803e007a0014022804400380040009801200220030067009500ba01a403180a000c0024408e0076007600e40370036013201dc029000021e421d4dbf0ed6b56c767498895302a5454b8fdd821f13bc012400a8037005a03b809b00b000fe0000ece93112a6054c8a8e15262a5054a8a9215222a405478a97043e54c4acd887b10f421e421d57479fbb43b2196541d09dd008e00c800b808301f402b802f8090019403684ed80c8016c0160068016e035203a809280c501be029008400a800da010c040005a006000d0027003c005400582140014008000fc0128041003400f801e8005008a011000e00100048004c011001200220030067009500ba01a403180a000c0024408e0076007600e403700360132014800010f210ea6df876b5ab6043e767498895302a5454b8fdd843d13b8012400a8037005a02fc09b00b000fe0000ece93112a6054c8a8e15262a5054a8a9215222a405478a9736fe087a21d57479fbb43b2196541d09db0106032002f8058012003400b701a901d40494062800d01480420054006d027a00181bc0066016a02ac02c8070011401e0019802d008400e800b801501e2042408680c705f809242b88065012c01d000280530020004c00900110018001c04980160ae003281f387b0019c0a9c091009500ba01a403180a000c0039804880e8016801d801d8039012801b801b009900ee014804780003b3454c0a951fb6261c6df876b022221e44c4012d822b13b402dc2b7005f012000344ec800613b011f0003809301940f9c09100a001cc024403b003b0072025001b007700a4023c0001b7e,
  0x108769878fdd283a0cb2766887a1d9c36fc3b5865c0cb61954000d52a0a130f760c1829f036206720eb806e002f00740050012801a000a01e000e002400440044003814b015600d400f80000046000800480030002002c0130028001e0284013801e001c0000a951d9a36fca950ece0ed60cb254bc21d9fba21e8438887410f021cc4c3850880fe00920458060813101540d880c2018f033606680c7018d0068013801e00c700540050012801a000a007001200220022283c5070478000e28342b28015014e1ee82bc82ef003e0000001000900060004014000f037000b000c80a10000a95152b9fba5074196530f21d70f78045819c8578003e00b005080005aa4b1f964b130c59ac4bf832c9fb706c404d804d0040005a004000380a705220bbc06200ab01ac035406a00d301a40344506001f0046000800580280052003c00f00000cb27668ece1fba54a8987941d2a561420045807f00a9009203040988a0b002a00b403800dc018800bc1778014004a00680028078003800900110011000e01bc00f8000000400240018001001600a0007802c014200780002a5454ac7668ece1fba5074987832cbb34141802a82bc03b7141406400c2018f033606680c7018d0068013801e002a03700284000152f3b34767032ca61e58e6b54963f2cd6592c7ee8fdc0a0b01520458024833902d228240c80184031e066c0cd018e031a037001a004e007800a8017801f005802840001fba2a5e7668ece1fb84c3cb1cd6a92c7e59acb25832c930e1414076c055037e006a00000dc00a1003c0000987152f3b347670fd61fb83f607eb8fd51fa83f687ec8fdd1fb6141203cc3dc8a08140e28185028a0414062808500815a003c0000ece10f3006a15d41db03ef044404ec1f7013a00b01ee00f2823a040c046409700b6017e055827b8006029603dc05a80ab00d00164038005600a201ec042005700de0020005000b00700098014002700080000a9788733b38987887a0cb8196c000c65510f2150202c827b036109040d8019c048006220ed81c58222033807e00fb80b10000a9d421eaab53b36000c65c0cb6195443ac3dc027302ce0bfc12c842a001a07500be808503f804840700102001c00600003b3b766aed55dcabb57772e6df941d8ed62a5a19942af024a0424088c09d81e7065204e821284ec07da056800f0000556aa9dd52daa5721e4a95421eaa753b38766827b824a0c0204ec2b384ef0aee073c00f00003b3410f552a9d9c21da0fb404082ae03fc07b40ca009b0030000087a1d9c1dac3b507630ed01d9043940ff81590ae80fb00ac005400006578cae195432b06548cb00cb3077206141be8a0001420000989801f0214093011200c4024408bc04680170066033c32f01a605d404dc003009e01f6027403e809a0aec04d8016835f008000fc020803e007a011402200100048004c01100120018000001180020012000c0040001001600a40508004003c000141d131010ea195cfdd152e566c43d08792a623b38a9583e409ff018801b014880150000007800006573f7454b952b47df06be15d412f020b020201e024082ef035804e41c5014e00b00e140b4017401f203200aa814f0254054c0bb8170013e02dc03301ec06ae0310091022f017206000a9017f025805200468072021a005c3db822e006607200678021034c0fac09b809e01f6027403e809a026c010001f8041007c00f40028045008800400098012002200300000023000400240018008000200e00140029003202840138004003c0080000283a0cae54b8fdd1310566c767087a10f2087621d5d9b85760556008415601c813fc0bac01000004dfc9909341262a4c3e32ac09b857402b202c8166027b055808f413d025c05d80bb83db822e047e09740ca823e01ba0b2c0e4002107d6056005880540040000137f26424d0498a930fa62319540698059042e0ae615c81c4838813fa0ed41f504f5066e0ed005880004dfc9909341262a195400141f580b20cba197032d83e90594120018800b10000987533e8cb8196c32a8001857502b20fa02168387045a27f04fd835e066c07584fd002103900bb415502eb02b0015001000004dfc987d32126824c54658065589fe0042075427a02190cb40080000261d4dfc65843f580b213f227e03db09f713ec1ed44fa80b100a80000dbf0ed619543b1c10d0159055a0c3c156023d04f4097017601d504580aac01081c805540694175815800a80080000261f4c7e9bf865582ed00b019283228027003c0000fdd131221d043d087910e221cc43c087510e425fe1eec05504d0099e133829b04cc099606e005080003f6c7ea0fdc1fae3f744c343e100950142008c00021d8000014d01ec874c13e8184c30906110c20183c307060d03100000a98802305ba0aa40002f7b04820b9015480005df6097c17182a90000baec13e005d0552000174d80020e680aa40002f7305e801a415480005de6002403182a90000bacc00180a005520001749000800c00aa40002f6f00020b0815480005ddc00ac07302a90000bab8005009105520001747000b0ebc0aa40002f6c039a084c15480005dd800e007402a90000bab001300b4055200017460028023806200001533005201d80c4000010ee003c01d8188000130281548039014200030858188022602840001fbd,
  0x143aa10ec988152e3f7421d4ece10f40caf1f783e1800d0e960414062053f03ae004000980120018001c0d680af006a007c00000020012000c000800f00080078007001800006df8ecd1fb62618195cfdd1310261c7670fdc152d145a03ac5160a2b145428a45140a27144c289405d801800006df876b81d701e628900f3805803b401d405503dd03ca08e81030119025c02d80d78120035c06fc0f301be06500de4193834f069c0bf808700d8023e035c04380ee00e201b01af8015000c042811201e9049805c8062053f04dc007001200220022001c0d680af006a007c00000020012000c000800f037000b0050815a004e001000f00003f6c7ee0986131025fc4c38fdd06573b3476723ef866402b2288c5110a211440287c50f0a1d1438056002a0000197202f0059027b06780cec24183ba01ba090005c815d008e03f405e823c012008d40068a1b001c02c40001b7f5926d409aa134e63f72b34c32cac77261e000c65b0caa19702ac008d810c0096060406d81ee071a02c81dc82d105a00abc16782cc06260b38189027b047c03742be80b10000b1dda730cb8196c32a8001930f36fe1965649b5023f72088450d80bd026a011c0e500b900004c3cdbf865958ee0885a731fb94c4415f427b80f7016a02ac02c806800e0031050d000602ca015402b005b00a2013003d80c00108029802b80a700de00d400f80080014002c01c00260050001000f000021e87ee8ece1d9a10e606b427b81ec06a4120420c02ef052200d400047df8fbb1ff641ec7ff8fc610f4ece1d9a43ae286808b0014004a0068002801c00480088008801f000000080048003000200b0000130c26204c3897f065910ea08c83e104cd08b618243e080a10000b345638ac91261c4bf832c9fba3f707ed856100aa054a0a90146823705460a8815081db037002840001fb63f707ee898887c101540a340ed824d0cc6001c011001a032006102be0034031e2864027018e031a0370015002f0000000c00781b80142000130f2d520cb24bf966b130e3f707ee963f0ad0143005a4000261e5aa4196563f2cd6261c4bf8fdb8663043415ec0b5838c0cc4057001a801800007ee887a1d9c3b3432a897f869106f0106017782910188052c02600a6014e007c00580260050009c00f00003f7410ec87a10f210e605941b1042f01b800bc0001fb8261c7ee96a92cd658fc4bf832cac960af803cc50b87c00f7e28583df0a150cc205ac1c6023802b80c183250035003e056800f001800007ee876b10f436fe7668ece12ff0af606840f2014e00cc0e14184813900b20928109022305bc0d3010580ab0066105403c00170074011c08800b906740374188027b059402f40590090036806580b501c902b603280ea00da0182012450a00530cc0003412a00aa076e03f83de8362032006100c7819b033406380c680dc0068013801e002a005e0050012801a000a0070012002200220030003865f02b805ac10d006b006a000001180020012000c00400010050003c0dc00190142009c002001e001c0060058805400009878fdd0ed6197032d865500030cb210ececd1d9c21e86df85550139142604e816681c70860005433000aa076e1ef41b101900308063c0cd819a031c063406e0034009c00f0015002f0028009400d0005003800900110011000e197c0ae016b043401ac01a8000000400240018001001e06e0050801e0030000130f1fba00061964ecd10f43b386df876b0cb8196c32a821dac721428082c07d0078002e00e8023811001720ce806e831004f60b2805e80b2012006d00cb016a0392056c06501d401b40304024857a001a095007f0014004a0068002801c004800880088000004600080048003001000040140029001e0064007001801620150000261e36fc3b5865c0cb619547ee4001930f0cb221d4a970660026c0268166802d08600054020003f008200f801e80450088004000980120018000001180020012000c000800b0052000032c88753f729878a972c720af402680a2814b00f6008c00580260050009c007000021e810ec8791b7e1dac9878439865f002a0130024800701b0008803a801a024808d01b1004f0536284803f00dc01e000bc19c801f0000000c005800f005802840002d5259ac7edc98712fe8b84196563f0a18026210bc03a812404680a6c096822001e0031c027807e00a000bc00a8014004a0068002802d003800900110011000e01ec04d02a7006a007c00000230004002400180010016003c0160019014200380001d9c1dac6df8ecd261e25fc4c38fdd06593f6c1ef43dd84d3060c13a42b2046e003e00780001fba21e843c887112ff02b8076c18200aa032006100c7819b033406380c68034009c00f001501b8014200016a92c962618b1f89872cd63f747ed832c9fb8085e020423d03b008f2071816303af0136006000010f43b383b5876a0ec621c605ac19d031002200b280da00b2025e06580b501c902b6059c0ff81dc038e0054006804904a803040550578076e03f850881900308063c0cd819a031c063401a004e007800a801d0014004a006800280780038009001100110134001c1dc014b015603103de01e5023204b805b0087142008680358035003e000000100090006000400580260050003c0dc00190142009c00f000e003002c402a0000,
  0x102bc00d400e00100048004c01100120022003000380930304007c0000023000400240018008000200280058029001e062001600270008007800c00003b387ee09871fba0cae43d0a96058300cc07b002c003303ca081808c812e016c057c0438169000c19900f781aa021402a40d78120035c06fc038806c018e03b800a8291044807a41260172006a001400e00100048004c01100120022003000380930304007c00000020012000c00400010014002c007802c0032009c002001e00007670fdc47df261c7ee832b952b21e8875cecd0a3603ba19980af00e10f8e01f00170101011401e0019802d0090007403500420074005c00a80ec010405280788109021a031c27c829209f00bf01248a3507e013e80028011000e024c0c1001f00000020000802b0014002c01c00260050003c0c4002c0032007800c00003f704c38ece1fba0cae6df82c1001700661e9008102ff07620a78070007800741f2816380d8015201b000a802d01c228d000682c5020a05780ee8a3307e013e80eb806b0452085c11380100026004800600070126060800f80000482097c13e00020012000c00400010014002c0130028001e0620016001e001c00600001fb83b387ee8dbf130e0cae4c3051a812702420b98045046f008407e41ac8109058e036006b80a900d8001c049801f00000020005000b00700098014000f0058026c0002c7326184c4098706571dac3b50766152d043eb1c43e5010903a000e8163807802b803800e301d401b4003408281d7006a004000980120018001c049801f00000008004800300100004005000b004c00a0007802c001c00600001b7e3b387ee887a152d26184c409870657507628d0090808a024e01081730359047200e80da807803a61f1407d001708f6121807080da058e055806c00a901dc01b01af80151464003416281050ccc07a40b900c407e013e80eb806b006a08a410b82270038004000980120022003000380930304007c00000230482097c13e00020012000c00400010014002c01300280052003c016002700080078007001800007670fdc1fba26186df898706572a5c28cc02c00ea01a005b80d48363018a037c0e300a80148042003680da000c03843e2002d001a0414333022403d209300b900c407e013e80eb803500380040012001300440048008800c000e024c0c1001f00000008004800300100004005000b001e00b00138004003c003800c00002a5c195cfdc1fba26184c38dbf1d9c8fbc28c819e80330120057c065015601b403b8242835f0f9200340e105810b0015fc242019102bc07a40b900c407e013e80eb803500380040012001300440048008800c000e024c0c1001f0000008c001000900060020000800a001600a4007802c004e001000f000e00300000fdc130e3b3854b8fdd065736fc54b033307c80afc15e40f48172018800d400e0011003e0008000801e0000875498808752a5c7ee887a1d9c0caf1f783e487c1067202840001fba3f704c440c1015f013404d80ee815e01c21f1c03e002e0202022803c0033005a012000e806a008400e800b801501d802080a500f10212043406384f9052413e017e02491462010001f8041007c00f400280450088004000980120022003000381ad015e000001180020012000c0040001005600280058038004c00a0014800f0310006400f001800007ee89871d9a0cae6df8ece1fb8262013e80af06650afc075c00c00008fbcecedd9abb55772eed5ddca9b7e262043d0ece1fb850761f1c518016b01e603ac13b805804700bfc23184d9074a105c20b01c102ce0e1414f012f001a0b7015e01cf03c80538125021204460b7826b034c04ae03801628105027208503e3000602bc10980a481dd145e075c0358229042e089c00800130024003000381ad015e00d400f80000482097c13e00020012000c000800f031005680138004003c02ec00700180000195cfdc13103f744c38dbf1d9a3b384c30518800d020a1f140c8815f00f000cc17781ec0272019809d005803de079411d0206023204b805b01af024006b80df816901b002a404380ee00e201b01af80150f880018085022403d209300b900c4145c075c00e00100048004c01100120022003000381ad015e00d400f800000460008004800300100004005000b005000a4007802c004e001000f000e00300000fdc1fba3b3876689861310261c195cdbf152e145e069809b80cf013c03ec04e807d0000f059dad3b9a7684eced30f952b02be0ec407002c701f406440eb801f0000008c001000900060020000800a001600980140029001e00b000c00008fc454b843a930825fc4c30988130e0caeecd4dbf021f2a541f141c28413003c0000ec81d963b307650ecd1d9c21d607bc08481d000740b1c03c015c01c007180ea00da001a04140af05760f8600b40b900c403ae004000980120022003001a801f0000000800480030002002c0130028005800780070018000010eca971fb836fc7670fdd10f410ea4c30988130e0caf1f783e200a900d8199000a87c302bc28b4003010a044807a41260172018814fc00e00240044004400381ad015e00d400f8000000400240018001001e001000f001800006df8ece1fb826184c409871fba3b34195cfdb0a2e0aec15f801681720188004401a801f0002002c00f0000,
  0x100060020000800a0016003c0dc002c0142009c002001e0136056002a00200000a0e8a961fb80cae4c38fdd130c1dac3b30764022125fc2940059027d071a0b48167031204f607b806e802107d602f0058802000009bf9321262a4d04988d31f8caa062a00b404d03bb0322007000880070126007c0000023000400240018008000200280058029001e00b0000152c261c4c408791fba0caf0e9887a261e2a5c291003a8a421482290051f8a3e147a007c016001e00007ee897f131026184c38879831400b2027c01980c8002e0160039030e05920aa0174812c0910162027d8257000c04f4032809600e8014c2b883bb021c036008f80d700d8005451e026e00fe033813f001c0020004c00900110018001c0498182003e0000001000900060020000800a0016003c01600a1004e001000f000e0030000141d1fb804426df876b12fe26184c38fdd065721e4290c02c0114084202cc0b78068016a00b8045001d00840208078847f070804480de807506ae162012b80070126007c00000080014002c013000f0058009c00f000026084c2898112fe26104c40986130e3f74195ca97843b21e843c8875130009100108078808a037a02d403a816f05900ba00038093003e0000004000a00160098007802c003c0000fdd043b26084c2898112fe26104c40986130e2a5e195c873858800ea19a80ed001f005800780001fba3f6e7674982130a26044bf8984131026184c3887584fb01dc07a40b9035f0188007c0138004003c00023ef9fba0caf22fa3f510f221e90e98a9703bb0ed2016005502e20c0c10780b40174027c03e4064022f0c581374315862a0c52027c033008d03d8005c0030033034c04f40af8137044807a412601720134027807d809d00fa031009b01b7005a01fc067027e008000fc020803e007a0114022001c0020009000980220024004400600070126060800f800000460008004800300100004005000b0052003c0dc002c0142009c002001e0030000141d022136fc3b58987130c0cae7ea0fdc10f23f751f7851e00af07e028ec00f00003f70195c9871fba3b3809f803a830e08fe016033485870b0c19a01ed01f00718121c2c2800d1474043806c011f01ae02a4333806c018e005401680e10f96160c1210582006a001400880070126060800f800000100004005000b001e00b000c8027003c003800c00003f70195cece1fba261c43d051d8359008400e8045007802420380093812f07561188054806c000e024c00f80000010002800580260050003c0160000043e54b49872c732620195c766858503260c00048012702040484019808a002e010803900f102580e8c03a846f038204bc070007800741f2808700d8023e035c054806c018e001400880070126007c0000008000200280058038004c00a0007802c0032026c0002c7326204c3832b952d043e3b5876a0ec81d98121c02c030e05920aa00ed02e9059028e403a858401540f743320169010204740b881b0053e0820103824b04540544144019d017009b81940379064e0d3c1a702fe021c036008f80d70152199c038806c018e005401680e10f96038804b8129019a160c1210582006a001400800130024004400600070126060800f800000040024001800800020028005800f037000b000c80a1004e007804d80180000195cfdc1d9c261c7ee887a02211474064c1800167035604f007a8090024e04bc07c000d086204840700102011401e001980420074005c0788109021a0bf01248a3801c4025c09480cd0b0609082c100050020004c00900110018001c0498182003e0000001000900060020000800a00160098014000f0058006404d800e00300000ece10f4261c7ee0fdd065750761f2c178015901640c3c13e83f103dc06040860085005c0ab011e827a04b80bb0177022e047e09740ca801d05960720041002103660fac20f0137045e13740bc808d0200005c08d0130006602041580102026405c40d8029f067c082010381cc0144092c0d38431019805441440216033a045c02f00b8001a28dc33380e2012e04a40668583048416080080013002400300038093030402f000f800000040024001800800020028005800f0058028404d800e00300560058805400400000ece10f450764c38fdc1fba0cae4c3051c003a00f0042407001d0025e0b1c006815c0170071804e0167012e00d400600070126007c00000080002002800580260050003c016000e00300000ece1fba21e84c30988130e2a5a195c764866700ea09381ab034d05380e8c0a500f100d40108080808a03f804840f50127083a0c000ae046f010205ac0d5819e030c04f007a813001f000d40038093003e0000004000a001600e0013000f0058026c000283b3b383b587641fba21e854b432b931026184c3810f8a37032603280d5813c01ea02403a480f8001a10c407100970252033412100100026004800600020012000c000802b001400980ad009b001c00600001b7f507610ececd21d72a5a21d4ece283f0db404dc0d301790394040009a813003260204099017103600a7c19f0208040e0730051024b013803300a88288042c067408b805e0170090804d80180000a46942f289e508ca0fd41d9b7f044210c407b015503d8072c019815f02ac28d80770291044807a4126017203221f2406201dd,
  0x1010404f4052010808ba19c03e980a500da11fc1c202710224001803a848806ae06000bf812c03ae01ac22e054a0a92019404b007400a60c500670229042e089c0080013002400300038093003e0000120825f04f80008004800300100004015800a0016003c01600270008007805d809b001c0060000130226104bf8988130c261c7ee832b90ea2a5e7674dbf391f14ac03b4094007c02c2012011a813406f4150c0c980aa0ca41d903aa84140ec61d883b080ad003a00b8034008b0112043c219031604120328048000d046009c808a00b600b003a80b701a906c603d00fd0144018a023005400a4021002940b300c200da01900030a550cde047452a02420b14017c07b006600b200cc00b84fd00ca025803a00530cdc0c501370243019c09f800800130024003000380930304007c00000020012000c004000100560028005800f037000b005080270008007804d800e00300000a96130226104c389861fba3f70195cfdb0a64032605f00d003160412032804d80001dacd39da818432086208a8000418b5234a17944f284636fea0fc110823000ea0e18214801f00580000980130626044c2097f131026184c39c9d83670ed805a00ba013e01f2032004f80000142009c0002a5b3f704c38986152f262043d087910e421d47ed821d8a550154294c5290a510a781820303860509140768137024304fc060800f81b801420078000152f26044c20986130e0cae7ed8fdd1fb821d619bc52801b0066a05441ae800d0fa4022404580f400d01624052802e022802d8003001d00b010ac056830e05920aa00ed02e9059019ac20a007501541f381940379064e0d3c1a702fe021c047c038806c002a1f44121058a00be03d803300590066005c27e8065012c01d0029866e062809b812180ce04fc004000980120018001c0498182003e0000001000900060020000800a0016003c0dc002c0142009c002001e001c0060000130826047ed8a961fb80cae4c38fdd130c4c3c2950040817c062c13941738209019408d8329010f01200000005000b0370026c000283f50b6dc78eceb6fe087a7ed8fd908753f5054bcfdc1fba0cae3b5810f87d202240208245001d03b400b80d08068025c03e40640258010e027c003058900fe01c00db802d00be03d80330065012c01d00298314019c004000980120018001c049801f00000008004800300100004005000b001e00b00138004003c0000ecea61e36fea96cfdd152f26044c2097f131026184c3832bc7de0fa219b407a01fa028802300528166018401900002b3654f4aae95311d9d4c3ca0ecdbfa83f087a16242b881d7000000380001fb62a5e43c8986130e3b3a4c4032b9b7e0b140034064843102f20038000261e5234a17944f2846507ea0ecdbf866d005c0074034008201660e1800300750148107006800e700ca00400038093003e000000100080014002c007802c000800780001fba26004c18981130825fc4c40986130e0cae54bc875848a00b003a80d480c50150042003680060414019801380040000a95d52dab365574a9e887a10f221cc43a087110ea072a0054038802d02d202680af87d0149e064400800130024003000380930304007c0000023000400240018008000200280058029001e00b0000152c3f744c08984130c261c7ee032b952e0cdc02341178017039600cc0000008000021d4a959fb70caeece83e80006010e13c005b063800b015ac18702c90550076817482c8015401d41940379064e0d3c1a702fe021c047c038806c06be0054016809a02be00cc00b84fd0c9600e808481f9149c031018a026e0486033813f00100026004800600070126060800f800000040024001800800020028005800f037000b0050802700080078000152b2a5c195c981130826184c38fdc1fba3f6c293c26e841e011a06080508000261c7ee0fdb130226187ee832bac7709fa02341178017039600cc0af816900e200545268a4c0f9e004000980120018001c0498182003e0000001000900060020000800a0016003c0160000261c7ee0981130c3f7454ac32b9307149c13f004d066c005a0fc8000000b000021d432bb91b2a567ede3ef0a4d09ba107804680170066057c04d002d002a01c43e7026e048609f800800130024003000380930304007c00000020012000c00400010014002c007802c01420000983952b261c7ee0981130c3f74195cfdb0a4c07ba0ca01bc83270c10181405080003f6c4c1cfd41fba3f71170c3e7005802dc037c052006d004e000159b2a6221e043d087910ec21dc43a887310e2087a0ef00550a4b149429245240a470f9a2918522815c0f980bec0670182003e06e0050801e00004c389861d9d3f747ee097f824302b20fa0216838705e208b410c82ad06bc0cd80eb01d5004207b815501a5062a060408601ca023404d4040819302640a7c19f0208040e0730051024b011203301440216033a045c02f00b8011603d00fd0144011801a002f80a502cc0308032002e022803d8003001d00b0016421580ad0ad60c3816482a803b40ba416400330cd6105003a801701540f7420f016906500de4193834f069c0bf808700d8023e035c038806c002a06dc032809600e8014c522011d14860c50137048906ba08a803f80ce04fc004000980120018001c0498182003e00000010009,
  0x1001a04f40eb80bb001c00600002a7a566caae9531043d3b3aa26d41d9b7e0b1c001805201ac01a007e03ed007f00b203b407b80ab036e019404b007400a606440af8676006601f00808078002e012000a806a007401c8076006c0294042433a848c02a4119406c024e03a003380080013002400300038093003e000001180020012000c0040001005600280058038005000a4007802c004e001000f00003f7454b098713100cae43c8ece9309077a032806d0090001a04f40eb82d302c204a013903bc01d40d8c07a01fa028802300540108014a05980610064000c083002f80f600cc03380138004003c003800c000054b6a95487810f221dcaadd53d2b365574a988ecea83b21d41f680c9837a01ea0c5810480ca046a03e0048000d0862090804d800e0030000148d285e513ca11941fa83b51366dfc16981f8041806b000302b300be03d8033007f00b203dc05581b700ca025803a00530322026801680ce0020004c009000c000e024c00f800000460008004800300100004005000b0052003c016002700080078000152c261c4c4032bc7de766aee55d9d9d9d21e4987833b00ca01b40240006813d03ae162400700180000987953d2b365574a988ecea83f507610f4159848a0cd407685328a640cdc090c13f0182003e0078000152c3f707ee8981130c261c195c9840a6600b2027c01980c8002e0160039030e05920aa0174812c09101620087011f00d800540168070010e026012b800614c60c5006700070126007c00000080014002c007802c004e001000f00003f6e767498112fe26104c40986130e3f74195ca9790ea14ca01600f2823a040c046409700b6004e000087a10f221d44391b7f8098071c0984187843604320aac11601d5004207202458a62071a065413f8a6104c002f80780367062e04480568082003a00b8034008b0112043c2190090001a08c002f80f614c0047452f827202280ef007501a906c603d00fd0144018a02300540108014a0598061006d00c809083ec8065012c01d00298314019c001400800130024004400600070126007c00000020012000c00400010014002c007802c004e001000f000e00300150010000021d47ee8ece952f261c4c0898412fe26204c3032b9fb7087a298c3ec02070398064c0eb017105e20f781dc826102640864116038f03aa00840f703660ce810d413e82ed062c082406502420136006002a002000009bf930fa63f508cd39cdbf821f50bc32cc53083b400420ed421980b2045c08fc12e87d705da02f00588020000032b930fa63f4dfc32c813f8434016408b03398a5e061e0e3811e825c05d8086415682ab03aa00840e402b203e20bb405e00b100a8008000026fe4c3e98fc65732c60fae02c813d827d045c08fc12e819501ba07b80e40021071e0bb405102760138020420c818106ca09100d9011a046a058c0878161011204a004580ed00d00ac4148007c005c16341b20048003a00340d180ec0104069c092027102240ac003a822f030005fc096008d00e4005c13c803303fa016404600640484014c00a001c0018001c04980bc003e00000010008000200ac005000b001e00b004d800e003002c4010000026044c2097f131026184c3832b9fb72a5edc7821eb75e3b3a6dfd30faa5a14c002c8117023f05560e3852e8a5c0fac0fa0216842e0ae6086415683b506bc0fa80ea83b4017802c400026fe4c54987c6550005071e056413d02ee02b00000caf195632c06568cac19547ede0e3811f80b20556163011e80bc0162015000000054c3e32c06570cac195432c8caf8a5d02b208f413d02ab0b1606540ac00540000001530f995632c06568cac1954195e297005907d50ce4122c05e00b100a800006580cac195432c8cab87d6045e0ac004681a7002e003401980c90b12016403f87d1036e0054038816902f2019404b007400a60c5006700100026004800600070126007c00000020012000c00400010014002c007802c004e001000f000e00007ee8981130825fc4c40986130e2a5e767421e865736fe7edd30f0a5f04b805641558a5b14b42964245858b032a02c810c82ad076a07541da002108660bb413000be062e03c00568075003a05a4087011f005c01c40360068002a09e004581b70fa829603388a570836022403f8239021e03680da83ac0864032808a01d301200cc41de000d01d406a41b184fe0a90188007a00c5027a02a0084045d0ce01f4c052806d000c083002f80ab01ec019803c0059007400cc084801703f201c82b68a5603ae01ac22e054a0a92019404b007400a60c5006700050452085c113801000260048008800c000e024c05e001f0000090412f827c000400240018008000200280058028001e00b00138004003c02ec007001802b002c402a002000007ee88751d9d2a5e4c0898412fe26204c3098706573f6e6df83ec82f002b202c818782ac047a09e812e02ec05dc06541f882cb039002f00ac00b100a8000130fa63f196032d865a0caa1964000c2198058029c05a00ba013e01f2032009c809f004e000152daa5521e843c887510e4087608300f400eb01020b8420c8253051205f8127827405e409100be01a00234074411a8163021e05840448128011603b40340272022801f0017033100b0012000e800d02dc0d8c27f05480c4003d006f80ec,
  0x104920740084803a00f00368070000d07e604140eb867b086e09f800800130024003000380930304007c00000020012000c00400010014002c0130028001e00b0007001800007ee0fdd130e0cae6df83ef8359008400e8045007802420380093812f0cf41d0024382c70b0a0034115011d048419e408700d8023e035c121806c018e0eec00a8486005a1978070807f0a02037821b80ce04fc001400e0011000e024c0c1001f0000000800400010014002c0130028001e00b000c801e001c00600001fb83f744c3832ba83a0cf613ec3ec825b03ae0378011800e00007668a95152f0cae7ee89821d9d26044c2898412fe261c4c409861b7e0cf20b1c121824903a0042401d007801b4038000683f3020a075c1b40a6e01c4025c09480cd086e09f800800130024003000380930304007c00000020012000c00400010014002c0130028001e00b0007001800007ee0fdd130e0cae98782808081026005c40d8029f0410081c125809c02000544144019d0170003406481790484026c00700180000987948d285e513ca11941d9b7f06d000340ea010503ae003800c0000782ced69da13b9a2a5aa0e541d9b7e07e629b411201e9049805c806200de003800900110011000e024c00f800000040024001800800020028005800f005800780001fba2a5a4c38988065750769878ece952e15ca05641c382f103be1f782c98219055a0cd80eb01de0fba14000ea802103dc0aa80d28315030204300e5011a026a02040c98a6c026405c40d80678053e0cf8104020703980288125809c0b2403300a88591051008580ce811700bc02e000687d2010a00b800e8102022802b401980580828090800b816e035203a809280c501be02a82c5066f09fa13fc0520108015001b40b4832806f20c9c1a7834e05fc036006b826e04860ee0032809600e8014c038806c018e0eec00a8006005a29ac070807f01bc1df024700e2012e04a40668437019c09f80028229003800402c800130024004400600070126060800f80000482000817a000900060020000800a0016003c0dc002c003202840138004003c026c007001802b001500100000261c7ee0fdd06574c3ca0e853703140fb61f3000f801e00007ee8987131021e603780f600f601f4017c336848d0188026814a00e2012e04a406680ce0020004c009000c000e024c00f800000460008004800300100004005000b0052003c0160027000800780001fba2a5a4c38988065750769878eceab3654f4aae88792a622a5c29b404800ca01f4036800b800d08f604140eb80100026004800600070126007c0000023000400240018008000200280058029001e00b00070018000054b498713100caea0eca97152a36fc1234335842b015419bc27e831404dc05a41940379064e0d3c1a702fe021c036008f80d704ae090c038806c018e0d7c00a802d022a038403f8437019c09f80028011000e024c0c1001f00000020000800a0016003c0dc002c0032028400f00004c3c7ee032b930e08767ee941d0a6b0fb403400d480a4021000181bc007f00b202d40768070015606dc032809600e8014c0c8815f0cec01f0080808a00f000cc016804800d4010801d0017002a03b00a500f102121f703e1010d018e1f6c266845b09f213e017e024914d4033813f00050020004c00900110018001c0498182003e000001180020012000c0040001005600280058038004c00a0014800f005800640508027000800780001fb83f744c3832b952c086e0ee41400261052608b01b30435067609f413f81950630086415681d5004229a40510276013829a00c08262035604f007a816303a203e000682f3048416380b080890250022c139011400b002601b180f403f4051006f808c021002940b300c200da0190003037800fe01a005a80ed00e002ac0db8065012c01d002981910b1e299c03e002e005a040404500780090007400a806a008400e8076008200d8052807881090c5019dc2a7062d05c411900d980d708d40a701368a66077a0c5012180ce04fc004000980120018001c0498182003e000001180020012000c0040001005600280058038004c00a0014800f0058009c002001e0136003800c005400400000fdc1fba2a584c3832b930c14d40c3c116038e047a0970245838d05561f5c10c82ad03aa015000026fe4c3e001531fb2c6063009fc19d819504800720000267f4dfc987d31f800314d209f413f81ee032a06040e4010c004204681c78081026e04c80b881b0053e0cf8104020703980288125809c019805441440216033a045c02f00b80484026c00c00200000a46942f289e508ca16cdbfa61f04420bcc1170575039000841c7813704bc082c04f00fb013a01f405e00200000f059dad3b9a7684ecd5dcaa61f2a56163c040813002e206c014f8208040e092c04e010002a20a200ce80b8001a03240bc82420b1c0584094027200b00d8c07a01fa0288037c0460108014a0598061006d00c800181bc007f016a03b403800ab036e019404b007400a6064404d002d019c004000980120018001c049801f0000008c001000900060020000800a001600a4007802c004e001000f009b001c0060000152c261c4c4032bc7de766aee5ddaa90f021e443b087410ea21dc767530f0a6701d607a0195816406f60f700fd822504de03680e880c9,
  0x102b400780002ab554eea9d552aaa5b3b3810f555b9d9a07200c04109012802760cb00a7023809d405d006403ed026600d40ad001e0000a96c87410e421d4a95421eaab73b187648ecd1d9c6e0629d418081bc02aa04a80b801760286023805b815a0000a96d53baab74c44767021d8597077219d002a000032b06570ca9195e32c032cc1328156036e071c09980350fcc0198038022b00a601cc04d00e9008000fc020803e007a0114022002d0020004c009000c000e013000a806c0160000001180020012000c0040001001600a4007802700080078000152c0cae4c4541d1fbb4c3c29e005f8006037204543da007f019c000000100010016003c00c802700080078000152f2622a0e8fdda61e54ae76743f3015501ec0a9c099803503ae008c0138004001c0000fdb152a36fc4c3959b2a7a54c4a96d55d26223b3823300af809a006600b400b8015021a031c28181910fca00140080013002400440060007012610e000f800000460008004800300100004005000b0052003c016001900007ee141d152c0cae4c389880a7704fa09fc0f701e001160224281005f032a020c0e40197004206981c7813702220a54132020e037201b408400a8014802fc00300ee022a01c019f8068077c05103f2007f019c098c1158065012c01d002981dd0020004c009000c000000080048003001000040c4002700080078010000026207ee0a96283a10ea195cfdd952f0fca10c80878090001a04f40eb867d011807e807a006402cc029400700180000a17930fa62254f4a98955d1d9d087aacd941fa85b0a04074c00681ca05e60038000291a50bca279423261f50b6988941f9b7f0cfa01c401b8015077000b4000000b000021d4a979fbb0caeecd819f80ad008c00742cb002e0000002800008752a5e7eec32bbb56077c02c83f187e1017802c402a0000196832b86590cac1954656453f80b20fc41f8005e00b100a8000065a0cae196432b06551953150005643f087e001640e1c2b9033609ea02f00ac00b100a800000028cb4195c32c86560caa32b86558cb0195a32a89a0853f058f020201e0035003a02940424235026d00ea16540c0015202fe04b00a400720042005c1c78033026e057c2ca009e01f6027403e80100026004800600070126007c00000020012000c00400010014002c01c0028001e00b001000003f7654b0988130c261c195ca9585030502041812f01a8005c0404045001d00d40108041014a01e2044819301bd0000002801c00260000195c43a952b00064c1c2ca8159085a0e1c178822d0432077c106835e066c07580ea81de00420374155016c14e8036006b80a900d8005401680cf013429cc04f00fb013a01f40080013002400300038093003e0000001000900060020000800a0016003c016015800a800800001fbb2a584c30988152b261c195d30f059400f000e81058109062007e41f48112016402081dc801d05a20b4015782cf05980c4c16902ce062409ec017023e01ba0418010831507d6027807d809d00fa004000980120018001c04980bc003e0000001000900060020000800a001600a0007802c01620080000262326104c08986131025fc4c3832b952b195429d000a8071005a00dc0380115000c030803a00120000000c005800400010f2e1d31fbb10ea195ca9787e402b20aa81c382f103be1f782c98219055a0fac19b01d603bc1f7428001d500420a0412f01a8020202280350042029403c40830326037a00b803a801d01ae04e00360015005a02685390a71013c03ec04e807d03221240019018002a405fc0960148011a01c800b8033045200402c80013002400300038093003e0000011824100040bd0004800300100004005000b00700098014800f0058056002a002000007eeca96131026184c3832ba61e767429cc05904f60670123c13e8434071a0694240031103dc02f005880004c7e98f533e800305020578099801800004c410ea152c3f70767013181c20b0216002bf848403ae006000048be9005210a3f5022136fc87543ff80af07e000780001d9c21ea04cc169817d020401f00198048002e03b008684f914e01f7c33d80e2012e04a40668437000a004000980120022003000380930304007c00000020012000c004000100560028005800f005800640001fb8261c195cfdd043800ea04480d9818002a405fc096008200e4007400b802e0066021408102f30862003433e024304841f7c33d850101c4025c09480cd086e09f800800130024003000380930304007c00000020012000c00400010014002c007802c001c00600001fb83f74195c987130c14e000e803c010901c0074009782c702ce29bc0d5819e030c04f007a813001f0001c049801f00000020005000b004c00a0007802c0000a0ec76b12fe26184c40987152d0cae087c33e0367049c0a701d18082029403c400e806a008400b8080808a010a07f0090810f03d4049c0be041d0600020423780070126007c00000080014002c01c0026001e00b004d80001d943b587680ec61da43b3076a021f2a5a195c98712fe26204c307640a6f03d803d8019805f02040b4c30c822403d209300b900e2012e04a406680ce00380040012001300440048008800c000400240018008000200ac0138004003c0000dbfa83b2a5a767443a90f243ae20641638243,
  0x14c3c21ccecdaa5554ea10f40018a8202b2098421b022c055406943f681df05640bc411683890710086415683b503bc083c0eb033703aa0ed0010828103300ed81c5808b0444067007381f803ee02600c4806600c800100ac00540040000152d90f46dfe43c953aaab5087aa9dcecda6424c3cacd8665048201640db02c6031902b22a0053f80bc02b002c402a000032b86558cb0195a32a8001531e8cb4195c32c86560caa0fda10d81160159055406941c38a7e066c056002a0000196832b86590cac32b86558cb0195a32a8001531fa68210080ecc0298073008000fc020803e007a011402202660926004000980120018001c1c8803700e200542490a7d026600d4000002300040024001800800020098014800f004e00100001d9c2a58195cfdd843b04620da801900e3018602340b10126002e010801d0055014c029c0000008004c00a000006573f7610ec87a10f210e60e4403803b3067e014c03987ec14f8124c020003f008200f801e80450088004000980120018001c3f48133006a000001180020012000c0040001004c00a4007802700080000ece152c0876195cfdda61e14fa0564156828004c20c3c21b036b03aa0a4c116002105540a080d28281062a0d00083007c005c1fac024001d04bc06a01058134015a04040450078018c011803500420074050c047020002c404982a201bc029a038c06180f3035805bc09c81e707dc0bf409d009803de05580d78120035c06fc0f301be010e045401b8071002a00b404d009e01f6027403e8010002600480060133006a0000001000900060004015800a001600e0013002802b400780ac00540040000130f1d9c08767eec32b88754c4654ac3f6009a00e600b431a801501c601c40b7803701860ba0105020c034207bc0aa814f0254054c0bb80f90256032005b809f0fd4124c020003f008200f801e80450088004000980120018001c3f48133006a000001180020012000c000800b004c00a0014800f004e0000ece1fbb0876195ca96261e4c4429f00198017019e023403980320456010001f8041007c00f402280440020004c009000c0000008c001000900060020000802900007eeca8d152c0cae988843aaa5a0fd409600190046006e02340568071002e007400a8033005c00b40dd814601d20000004000a0016009c00008750cae7eec21d90f421e4546c249809a02ae052c03d8023001600980140029004e000087a043b21e454b130f08730fd2031c2ca0005002a0644008857e03ba001c131809307ec10e000f800000460008004800300100004005000b0052003c0c4002c00320000ece1fb82a58987832b930e262020c80cb836a013e001853d80e30344030c0b10109024c010801d0123011401e004101a8041600741888310005c0ce01650106016410cc13280ae055808f413d025c05dc08b811f825d032a01c816581c8002e00840e58033071e04dc0af809e01f6027403e813614f429e403f80ce092429e000a0040007e0094020801a007c00f40028045008800b400e00100048004c011001200220030003804c002a01b00580a77087002f00000023000400240018008000200280058026005000a40078004003c02c401000003f704c38a96065750740fd80180064017c023005d0a76077e0fd41a0800058fcb35964b261f4c44a16d41ca83f262276756a906573f7610f453d805a047603080bc014400007674988843d0caeb258fdda85f077e02000b304ee03f4071400013113b3a195d66b043d3f76a27c1fa8043014a068c07a013f00004c44ece865758fc10f4fdda847068203281d88090001a07080eb867d001c0060000261f4c44a16d42f289e5234a0fd41ca84614ec08300fb812b02de027c0002a7521e443d152aaa5b08760da804581e0011210cc281026500be0ab011e827a04b80bb8117023f04ba020c16581c8032e00840d3038f026e083814a82640222029008400a800da00180a2011500d01f900db8070077c019404b007400a6033801680100026004800600070098000800480030002002c00780270008007801000008fbc195cfddc3a654b6987cece952f14f400cc00b815f011a04d8019022b008000fc020803e007a011402200100026004800600000046000800480030010000401480003f76ecdd41d06574c3e21d552d0a79026e06980ec03f4040206240aa80a502cc030803201c7000c03d803303b300e008ac032809600e8014c0398266026600d40748040007e010401f003d008a011001680100026004800600070098000001180020012000c004000100160098014800f004e001000f00002a58195cfddc7de4c3e76702490058029c05a00ba013e01f204ac064013b01060fbc0aa87b8072000182cb80c6026801200a680e3018601f01000162024c0d000350042007401181b48101011401e0056850404bc06a0105801d071c12001888310005c0bc033f033805940418059043304ca00c8156023d04f4097017602ee045c08fc12e8195011a0b2c0e400170042072c019838f026e057c04f00fb013a01f409980350020004c009000c01780000001000900060020000802b001400e00130028004e001005880540040000130f88750cae7eecece152b04cc04a01808272025405d82750083092229d41f2056f0fd01f9c27f82ea09ee0f841f68035,
  0x102a802f0011802901620000a8e15262a5054b8a9215222a405478a963b95000632d9dcb8c4f00e605180d4002e0114007402100ad02c40118071808b08240a0c54c04ff05b80af00e781e4029c039c1f203ad152e2a5814b04f40b182a541c383190d080524020003f008200f801e8045008800400098012001800181188133006a000001180020012000c000800a004c00a40138004003c0150000283b4c3ca96c0019d9c3b344390fdd865710ea54b0caf86890d10088829c814d040001a808087f500f8012009a00c602500c041eb042409ce104c19201b103f00524020003f007c00f40228044042e00400098012001800181188133006a000012f80020012000c000802b00700568002001e000054b065b3fd37fb6000c43a86573f7643acecd1d9c3b2c2a6009500830fe6118407c8a940a102a4c0030231026600d4002001e000032d9fe9bfdb00064390871261c2a587668ece1fbb0cae21d531e2a5b21d42a5c0cf87f6152408680bc816403f605d4080000d01f004c013b80810cc40e300e303af076011e823c82c6026602ec04d800e003001500001d9c50769878caf90e3152c01cc074820b005a01e000a803a00e2049801b80c3017e04ec090021201e61a202650a91152008882118615071405381e1850801300524020003f008200f801e8045008800400098012001800181188133006a000001180020012000c000800b005000a40ad0004003c000087510e454b643a155a9d9a3b387eec32b88754c3854b08710a940fe804a82ff008309d406840998035004e00780001d9c21c443a88722a5b087a43a0ecd10e607860c042a20128018c04d0024007c0fea0cb03fa07f30a1004040350a8f151c2a3410007f2151805340a48040007e00f801e80450088085c0080013002400300030231026600d4000025f000400240018001005600e00ad0004003c000131e10ea21c8a96ca960cb67fa6ff6c00188750cae7eececd1d9c55682a4c059028209ec197433f0a8b0d0e09002400a8a15120d0012f0a8801f601cc0aa00410178008c01480b100005470a94152e2a485488a90151e2a58ee69dd13b957fa6ff6c0018cb6772e1fd40398146035000b8045001d008402b40b1004601c6022c0ce01bc074e03cc0a78153010610883bb80f9030e10840a48040007e010401f003d008a01100080013002400300030231026600d4000002300040024001800100140098014815a000800780002a5b3b147630ecb1d9a3b387eec32b88754c7854b087487f301e6053c1a505ff0ace13bc04184ea03421420099803502b4009c00f000021cc438887510e454b610f4ec51d963b34767087407f40342020c2ae863b02e0009c00f000054b610f487a10e421c443a88791d8d0a1000cc00b81bb011a1fa8019000000100000fdda6222a58195c43aaa5a0b3e056416882d0059e0c4c0ac000032b86568cab19547ee610f40ac82800d0c098421b036b052608b017a81980250022c0d880e701302a1c0ef820d03bc008424d02aa02d80a080d2859e023204b805b00bf02ac0e4003800ed00d001642ce814d01c6030c0ab8a8604000588093009a06aa01a8021003a00ac0220028807b0932030005300a7000c08c409980350000008c004002b0014002c0e68038004c00a0014800402b0015001000002a589878ece1fbb0caea0ec98888730d1600340e8811704c4073024c017804760068056007400b4030810081d6052608b42ce015905a20b4015782cf03e40554041868502560e400d200ed00d001640a680e3018603b01000162024c0120035004200740158081808800a2030005300a70266000000180080056002801c00260050003800c015800007671965195232b465519930005087a7eeca97865750764c4443990e5150e003432c81d40344042401d00a7000000a000700180000195d41d93111dac21ccdbf0498034204ac0738083011605540cc00dd03dc009c00032e66594766d53baa5b087a43d087110e821cc43c8001849a02b2196834203c007de04ec09d0098150a141c34186720d04166c27b065c15082a0c0ef820d056407c40ef020f00422a081c5819c0784046409700b6017e05581c8007001da01a002c80560110014403d8133006a0020015800a0016056002a0020000054bcece087354ea987955aab35087aa954655059e02b216683408506092e16641db03c104441a000fc01580000aad421eab353b36cc90002b3a432a46570cab195832b465508758a85013007e009d022202760ed81f78497078012582cc0159092a0c643f8836c0916162c3f8036007d2056002a00004c7a6568caa00053b36a95421eaab521e8dbfc8790caf150606840fc013a0106088809d8155076c0fbc0f9049707800c483f7865b016419fc15784960b3010e415a036c092802f001380b100a80000cad19544c7a32d06560cb219540014ecdaa55556aa96c21e90f421c443a087310f2195c2a1004c01f705fa000087a36ff21e4dc741e1049506d81fb424a000032b86558656195a32a832c865a0cae1954001531e84390164141424100bc0162000065a0cae195832c865532e5092806840fb813a0106067009d815507160fbc06e831106200b4828287ee1502046409700b6017e0558038005900ac01ec0998035017800200058027000054bc6551d9c,
  0x10d201a3c3470034009e013803f003c00a000a801782bd06160c2800a0025003400141ae035b06b4007001200220022001c0d68133003602f0000024104be09f000100090006000400781b8014202ec04d801802b00150010000026209878fdd1d9c0cb2766821d821f36fc32a83fe81d7048400600000ed70036068c09f80430198029409901d80000766cdbf843d04427eec988865758fc98ac2f7003700e202fc00a8120005a1fe00cc82660ff82aa4020003f008200f801e80450088052400800130024003000387fb013007840030231026600d400000020012000c000800b001e001000f000021c8a0eca961d9c21d4195cfdd9d9a0d6a01c400a8037005a02fc074812000e62aa0020003f008200f801e80450088052400800130024003000387fb013000181188133006a000001180020012000c000800b0052003c002001e000043908751d9a3b3854b0fdd86572a541ff01080120037c02fc01b8071002a00b40cc82660ff4005c21d0509011a07f40190040007e010401f003d008a01100a48010002600480060006046204cc01a80000004002400180010016001000f00002a5821d432b9fbb6dfc7670ecd1d8c54b42aa421283ed0064011801b814d01c6030c04680ad00e208000b10126002e007400a806a008400e802a805b0098030005300a7006a0000004000a001600e00130028003c000032b9fbb087a4390ecd1d9c10e61fec0398154008000fc020803e007a0114022007c0292004000980120018001c08180480268031821d8032011a005c3fd0006046204cc01a8000004600080048003000200ac014800f0008007800010e421d47658fdd86573b347670a96152a155001cc0dd8040007e010401f003d008a011001981490020004c009000c000e0154099803500460008004800300100004014800f003c0000ecd043d3b3854a8a9647e20ff4003455380f801d619840980277154c2a945520aa315442a840b58662071807181d802c600b01a3439c05770826157431d81e7026600d4013801e0176003800c000050767670ec681e101641a2817802b5050014102ce033c0676120c1dd028206d20900344802101c8027807d809d00fa01cc0c5015400f8012009a00c6072404a009d02f603620eb455002670292010001f8041007c00f402280440020004c009000c000e1a2c0030231026600d405e0000004600080048003000200ac014800f00080078058805400400000ec51d96261c4c4541da61e2a587670ecd1fbb0cae763028a864f0f1c003412280ae0348048c03900ec0104005c024001d006601f001700cf0314041806e824003dc05b014101a50d180084072009e01f6027403e82a702f2059010100ba017c00c054f83f700cc1a140f801dc03280ab80f681fe153c1fe43fc0a9d006e01c400a802d0332052400a0040007e0094020801a007c00f400280450088007000800240026008800900110018001c3458339000c08c409980350000008c001000900060020000802b0014002c00780a100080078007001800400000ec51d8c3b2c4c3930f152c50764c4432b9d9a3b387eec8750aa001941e9c048001800006df141f8ed636fca0ec10f8245002e00cc03900cf015c0374048027b001a02c805c016a03b206580e4815b019402700ff821a0d0a07c00ee013301780000004000e003002c402a000021ca7670dbf291a00064c44a95865710ea32a834600810260027008000b8001a032404d800e0000a46941d8ed21dac3b287680ecc1d9c3b520c5020201641a2817802b5050014102ce033c0676120c1dd028206d20900344802101c8027807d809d00fa01cc0c5015400f8012009a00c608760524020003f008200f801e8045008800400098012001800181188133006a02f00000023000400240018001005600a4002001e01620150010000021d4765941da61e2a587670ecd2a5b3f76195c43a90e40ff01578125022305bc04ec07180c302c40498021003a011401e00d4020b06220c401b003e90164099416882d0055e0b3c18982d2059c0c4813d816c047c037401080e40274026005f8210013c03ec04e807d00e606ec019801708741424046859f03fa00c801b8071002a00b40cc8149008000fc020803e007a01140220010002600480060006046204cc01a80bc0000008c001000900060020000800b004c00a0014815a000800780588020000054b0875261e10ea195cfdd9d8a3b187658ecd1d9c54b42a740ac842d05540e1c178822d0432077c106835e07d60cd80eb01d503bc056002a00004c3c9bf932126824c54001407200f3035e06b80df815a00007648ec51d8e3b187658ecd1d9c874e0840039809a01d2008c01480004c3c5470a9315282a5c5490a9115202a3c54b1d9b819902e0099c041812807aa032013907f7003c000087210ea556ea96c21e9d9c3b34765821d82670250118423303c3153814200998035003c00008722a5b21d410f555b9d963b38766887107f704ce04a030a832c003c000021eaab73b187658ece1d9a21ce2a70039834002a8008c01480004cfc5470a9315282a5c5490a9115202a3c54b1dcb818a02b22a6c54d0a9902b00000caf195c32b46558caa3fcf056a0c042a2015a00007628ec61d963b3476722038267016419f819e033b09060ee81410480048009781a00073,
  0x1004c003c050801e0176003800c002000007ee8ecea61e08761964dbf0ab901540edc1b1023202b806e405b008700e000b400a80490d2e06400c2018f033606680c7018d01b800d0027003c005400bc00a002500340014101801c00480088008804d0000000800480030002002c0dc00a1000054bc21da61e21e821d432c9fba3f7020080f600fa016e06a002f8801048a16840b2008a156c032420c0232001a05bc0ae0254078406e405b0697010e01241488015005a066434b00c40d2a06400c2018f033606680c7018d01b800d0027003c005400bc00a0040007e0094020801a007c00f400280450088080c00e00100048004c0110012002200300038800019c013400d801f0000008c001000900060020000800b004c00a4007801e001c0060000261e3f741964dbf1d9d087654b855b82ef00f0085007001d207e600400098012001800080048003000200a0000283b36fc767421d887543ae54b434b00aa02d20bf80dc00004c3c7eb0fd91fb83f547eb8fd41fb03f687eea2e1869700e004d804d002d002a0454024807f0b4006400c2018f033606680c7018d0068013801e002a0028010001f80250082006801f003d000a0114022020300380040012001300440048008800c009a000001180020012000c000800b00520000fdd1d9d0cb210ec43aa61e50741a540380087028a06e404d016500f6006c011800b001c000087a1fba4c3c6df821d887310000da00db033203d6053005503b706c408c82bd8ab5156806400c2018f033606680c7018d01b800d0027003c005400bc00a00250034001400e00240044004400381ad0266013400d8000000400240018001001e06e005080000876766832c9fba4c3c767055c015e0ffe041412a000d15660050012801a000a007000800240026008800900110018001c0d68133009a006c00000020012000c000800f001c00600001d9a4c3c7ee821d86593b386df855a80bd03a6011c00681ca017215f406e8ab2054004680ff819309362ac400e802e009001a003e001700420238076803301c806f00a18059014603bc0c5810701e6099c03301f003b806500f681fe04ae079c0d78120035c06fc0f301be04c6071c0db805303ba0664070802d002a01242d001900308063c0cd819a031c063406e0034009e013803f003c00a000a80178014008000fc0128041003400f801e8005008a0110101801c002000900098022002400440060007035a04cc01a804d0036007c00000020012000c004000100560028005800f031005680138004003c026c00700180040000130f1d9a08767ee8ece065950742ad055802d202d802f00001b7f5926d409aa134e63f72b34c32c8003261eb1dd9658ab2001a09503ff026303ba0664070802d002a01242d001900308063c0cd819a031c063401a004e007800a800a0040007e0094020801a007c00f400280450088080c00e00100048004c01100120022003000381ad0266013400d80000004002400180010016003c0c4000e0030000141d261e3b38766821d9fba0cb26df85588182026202840001fba262201342cb806800b203b40c50085006601f001700170090007402380fd009602e40ae80db01ba09000f70021017a039011e011b0154028c077818b020e0edc0e8816306c408c8195817e02b802400cf816403f608940e301e8065c032806480da0ffc05b014101a50ffa06400c2018f033606680c7018d01b800d0027804e00fc00f0028002a005e0050020003f004a010400d003e007a0014022804400380040012001300440048008800c000e06b4099803500360000001000900060020000802b0014003c0dc00a10176006001000003b346df810f9fba4c3c1964ece043b26202acc55780dd0480008407200a301de062c0838257038e066404d00e1005a005402485a0040605b014107fd032006100c7819b033406380c680dc0068013c027007e00780140015002f0028010001f80250082006801f003d000a0114022001c002000900098022002400440060007035a04cc01a801f0000000800480030002002c007801e0040000010fa61e36fc7668988043b3f74767032ca83a0ffc02a8060816905fc06e0000261e50747eb0fd91faa3f5c7ea0fd81fb43f75170c2d001930194024005e8047002e00cc02c80b900cc06500f68257038e0054024833101821a503498692036c098c02981dd155c080c03580dc0d201a3c3470034005e0af4185830a002800141ae035b06b40070008800c000e06b409980350036007c000024104be09f000100080002003c0c40004003c026c00c00002a5499f930f283a36fc7668988043b3f7476713110659043e54b0557823201fc02a406e002f000a004400000010000987898808750cb2e46c101826702860d3009001be07b60850077007c0f780a440f48172005a06280620136008000fc020803e007a0114022001c0020004c00900110018001c0d68133006a007c01180020012000c000802b001600a4007802700080078000152a2a5899f930f1fba5074196421d9d9c3b3454b855700eb155a119c3ac046b09c8137820d008104ee05645560aab0fa807642c6067f0ce61f8c3ea868a0fc42aa819880210d281a4c34901b607d602a805180ef0316041c1db836204640868348806b032006100c7819b033406380c680dc,
  0x13b3a10f4439880e017e01c003f8136004600a4000151c2a4c54a0a8f15242a445480a951d9d766e10f5b7f283a06dc059012280c9001a0870046005f02c2022403f8064010604a004580bf00a60164076806800e0051402b008800a201ec00d8023001000ac005000b001c0000439952a782cdbf9b8f375e6e0410f4ece9b7e0d3c027005c025900360060000289b50b6a0fd41d9b7e5234088410e0075025809c402380fd045e0fe00f90293055e0a0056601df041a0778010869c003e00b001000004cfa98f4ca9261e5926cb9999332ca3f6eb34c32cac7726044c28988130826184c1097f130e32ac2b3c15a8261052608b01fc031701fa012c138811200ea04b0023822f03e410f400f802c0000cb2963b930226144c40984130c26084bf89872c930cb2b34cfdbb2e6000acc98cab195a32a86570566015906321a0424b080d1596203014b05a302b0000133ea63d32a46558001869c0d34142c03a880602581418023859a045e05640f90681087a125c28386830d040b382cd84f61594202c0ef820d056407c40ef020f00422b241e2010b052e0f140bd83c6003e00b00ac005400400001648acd159269879638acd358ee7edc981130a26204c20986130425fc4c3832cad5119542b381b0043906d8202418c869907f003f413881f90220201c405080b003e00b000c800058e24c20981130c25fc4c38988065959a67edd33e8cac32b465506590005195498f465a0aca0fac2b2002a0000195832c86551957101610f40f90507059c202802a00004cfa987531e8cac196432a8002a62332a86568cab06a508720fa440483c006321a1056380004cfa9874cab0cac32b465506590005195498f465a080a0164196c1f483c00b302b185628ac40d3202f005880004cfa98f4cab195432b4001530e8cb4195832c8655195e158e056432d0ac30780162c1f4843902b001500000cb4195832c8655263d000a9874cab195432b46578cae0ac600ea06f41d1801f00580000981130a26204c20986130425fc4c39c9c829700ea0c98310801f00580000981130a26204c20986130425fc4c39cbc83c605020c5c1e283c4009605ec0858112064c06f4404000026144c10984130226184bf8987131058e232a9648acd10cb2b24cfdb800315921fb82ba8310078a201c0bd81100c4207e403a80bc003e00b000c800026144c10984130226184bf8987131058e2b34432c9fb7000632a89830808049211e01268ac200d4010801d00c0014c029c0f1004d000000e001300280142000032c88733f707ee8fdb02f8092806942cd8360045814181b602610b340c6434d82f70432077c10682b203e207540ef020f00420a041fc0317100c0f141e200fd0096142c0bd810b04e2044834d0326037a01d408700d8023e035c024816904c0090c12680f0018e00a80178048003a00541aa806a0084040c02d804c0932030005300160a020788026801f000000ac005000b039a00e0013002c00320284010000010e67ee0ece9fba4c3cb54856681a5092808b01b6067209160dac15a0054000098f4002a63f196432b0cab82f7056a0a0014982820d32142800019604c7a99f46590cac000a99fccaf195a32a8655834d80b20fde1fc024b867f092c201405e00b100a8000133fa63d32ac6578cad1954000a99f465a0cac196432a834c829307740ad421c8000195432b06590cb44c7a6558caf195a32a8001533f995c100a200c341805400006580cab195e32a8656865a850a05260a0014108040164200c216857306bc0fa81c385a20ae41a1c19b04f5017802c40000cb219586550cb0268232b498fc002a67f4c5432f40ac85070d04056002a000032b06558caf195432b4658065a8803056a0984149822c0504069421c82f1045a0e241c401d6066e00006560cb24c7a98fc002a67f32b4655132106a6021408900f4824c02e403100a4801c004800880088007035a00c400f80020012000c000800f003c0000fdd1d9a21e410f4ece01ce015e033800f00003b3443d4018813706c81a601b68260085e1a4412180dc0068013801e057c005400bc00a00250034001400e002400440044003816501bc0788142004d0000000800480030002003c000043b3b347ee0fdd065921e81b78055057815822b0055f8abe157a2af055d83b7037002840001fb83f744c3c0f1002d002a066402488020d2e10f010201900308063c0cd819a031c063401a004e007800a800a0040007e0094020801a007c00f4002804500881a54101801c00200090009802200240044006000715742ae40670ab8009a0000001000900060004005800f003c0000ecd043b3f74196530f028406d006d819901eb0298000235145e68c4d173941d9b7f4c3c7ee421e036801c4025c09480cd0000ed09dcd3c1676b4a0ecdbfa61e2a5a081006200700522021c0dc8165009801ec00f800b003c000087a261e08767ee84398aba01b60a04025831a043600740bd810b005c01a8021006802020228010808e01ee02d4072008902360df01a980ef0316041c051816307040b0c13a828e0cae05f80f50127048a03ac0f40342045005901bd83dc03f6089413780da019200340b48254059a200855b8695009e01f8028002f0028009400d0005003800900110011000e2000067004d003600000010009000600040050038,
  0x110e654b83518014012400d006681b6000000080001fb92a5a1964439a84709380f1c1f3000d00c203d005280650124053000a011b0054013c02580050248044802e005f00ea014c04187aa00cc04ac04c0ad5021c036008f80d700b210b01f28049026c0db8060801d002a026807900d601aa035006980d201a2015802d804c00f6015c037800704640378026801b003e000001180020012000c00400010014002c01300280052003c0160004003c003800c000021e87ee898612fe261c10f4ece86593f72987941d08120864043c048001b0000a0fd42d821f00c205b018a80dd030207280860021026a04680720193010206c0099020803980a7c351033e0912092c04e00a202a203300ce8117051008581ae80b800bc006c04d80200000a46941d289e50bca11930f283f50b66dfc11083c709f6194c08700d8023e035c02480c1002a01a8021003a0098030005300a7000e08c80268000001600e00130028001e0078000043d3f72a0e832c9fba3b3a4bf8987130c21d62b5400304f00c70021c3258058013000e856a01da061c0b2415402e90590042403a81f906be0310087011f01ae14380360595077a00540108294005a039004d009e01f6027403e86a104ac2b4c2868010002600480060007012603780f9804d0062007c00000020012000c00400010014002c007802c004e001000f002000006558ecd261e26184bf89871fba0cae2b58245065505c4076804c008704ae00181c980700a1c0194029809600e806441de820404b609580b482cd0a1a004000980120018001c04980de03e60134018801b003e000001180020012000c00400010014002c014800f0058001000f000e0000766930f1d9d25fc195c986130e3f7454a8350836801e802300fd0144014a01900b300c20000a9e955d2b3654c47674dbfa83b4c3c10f41c983c202de021c0002a5754ea43d0879043b07f401c8096042b09100f9012a84f304ae15b8087011f01ae001803602ea002a0ee0016800701260378026801f00000020005000b001e00b00508004003c0000ecec3a73f724c20a97930e25fc4c3087a1fba0caeecd828700cf006608f800b843d00e41258406880c0258168c03a8ad2021c036008f80d700d8165400a8021005a039004d009e01f6027403e86a002d20b342868010002600480060007012607cc026801f00000008004800300100004005000b001e00b001000003f749878ecd130c25fc4c3832b99563b382b4c1fc880f000e024c06f01f3009a00c400f800000100028005800f00580000fdd1d9a261c4c3130f0657507414340cc80e1036e00b400a807100fe0304020003f008200f801e804500880040009801200180000001000900060004005800f004e00100001fb93b3a195c43a90f421e4987941d03f9049c0a5c1a6829c029403c403500420202022812f01a80d402b440038093009a007c00000080014002c01c0026001e00b00001fb64c3c7ee8ecd263c4cf8195c98612fe261c76705700058070a05ac125021204460b7816e02bc039e07900a701ab0260085009c810004ae10980068191019208100bc825b03c2203c00301ce0020004c009000c000e024c06f004d0062006c00f800000460008004800300100004005000b0052003c01600270008007800700003f6c987832b930e26187ee8ece1d9a2a541a800168015013401c434f80c1000e024c0f9804d003e0000004000a0016003c01600003f747668ece130e2618195d30f283a101e071c12b807304081a7c12d80e9035000b40450015008401b0078810e06ac00180e70040007e010401f003d008a0110008001300240030003809301bc07cc026801b003e000001180020012000c00400010014002c0130029001e00b0002001e001c000131e1fb60cae9878987130c3f747668ece130b15a20da802c80b5084c01cc102069f0376096c019825e002e02280808072008401a809600f1029401d414b83c6000c0738020003f008200f801e80450088004000980120018001c04980de03e60134018801b003e000001180020012000c00400010014002c01c00260052003c0160004003c0038000130226084c2098312fe4cf87ed8fdd261e26184c38ece1d9a0cae4c285690257038e04d8016801500e2030400301ce008000fc020803e007a0114022001000260048006000701260378026801f0000008c001000900060020000800a001600a4007802c000800780001fb90cae54a8ecd1d9c261c4c30fdd283a0d3e090c06e0ad0005e00500128005003800900088007101c07380030284002c037828081e2009a00c4000000200120004007801900080000ecd261e3f747ee00f9807400e603080710144022e0034064836e039805e434f00c804e4045002c00980d3a0c3816482a805d20b2005600750034044801e004b06da0c5c0eb02f700420a5811682b4159e0d8416502aa02d80a080d2850c0b482b381e2010b052e0f140bd83c609f60a6808700d8023e035c054804902d20be002e0005159a005c024001d002a0268074835500d40108079003a01ac035406a00d301a4034402a810300b6013003d84990180029802b80a700de005806f050103c4013400f80000046000c00400010056002800581cd00700098014002900580064013801e001c015001000003f707ee887a261e,
  0x1012c01d0029843e0034004c0110012001803f8000000900060004015800a001600e00130027001c008000019563b3a43d0879152f10ea987898786573f7210ec56e843d055e07c80b606a503be083415901f103bc083c010828103020c6819d010c029404240be006a007408080808078011803dc0558173035804e406f83ee0274026017b06a904f202f405c808d00e4005c2480033035606780c3013c01ea040000680c902f21aa81ca028e0436058807880420114021c1b78070005a00540360053087c003007f001b00000020000800b00700098014000e00400000fdc90f421e410eca979d9d10ea195c987a61e32acece856e027808ea192009a8226065c03281140259047804d00e00048019801f000680f401da0184172819200be03400d880f6072a016456d8394023204b805b008700ca025803a00530020004c009000c003600000010009000600040158027000802ec00700180000a95c87a10f2087654bcece88750cae7ee541da85936fc1aa821503820368080009300d900d400e802f010100f0023007b80ab02e606b009c80df07dc04e804c02f6001a1aa40308279017a023400b849000660e50029800c003600000040001007000a00070018000043d087936ff087654bcece88750cae7ee542c9b7e5076ece856d802e00d0007404700ad0112046c000000a00007ee4ece8657087654bc43aa85a07280374067816c01f400cc33001ec03b203d806d002100be003407202b3027a10f0077818b020e028c0030034009e013803f003c00a000a80178284002c01b000a881a03d209301120172018810f800a00250034001400e00240044004400385a901fc07cc018801b0178007c0000023000400240018008000200a40078019004e001000f000e0030015001000003b347ee8ece90f24c3c4c3ca97081c0d2c001840c82ea033215e40168256008000fc020803e007a011402200100026004800600020012000c000800b00080000a97261e21e4a0ed0eb88753b3b1f7840d01b7002a15e8024801600fe0fe4060800000040004005800f0032009c00200003b3ae46843aa61e3f7243d0879283a087c01700028053005401900a6008c0b4c16a040c00c1009200580360006002a059402600000002002c00c80040000e468fdd10f221e89878ece9fb910e616a40d081f701900670041827503c8053809d005f024e04ec122822803a4059006d01d4019200341f30059016a02ac02b005700de006c0000008004c00a0013800e00300000a9788730cb27ee541d9d9d087a43d08791b7e0b5005e40a286a3013401ec00d8023001600380001fba3f72196541d843d3b3a21cd30f152e103000e803c012601c006d01f98204026c066456d009a005a00540360016008000fc020803e007a011402202840020004c009000c000c001c0e701ad006a03f835401f30062000001180020012000c000800b005000a4007801900080000fdd1d9a32ac9878ece081b056a0a003538293102e205814106a60d4a077c10682b203e2077810780210502036c0ae808206340ce8076001d017205280848048005c01c8035003a00f801a000b810100f0086c076808e006603dc05580f1028606f002c81ac0272010813380f300cc079c1f7013a011406bc09001ae037e07980df01c706de0e90029802d002a01b0006003501fc00c40000008000200ac005000b00700098014015a0008007801000003b38766821d88750cae4c3d30f19562a5e2b6804600640b4c014c351817904b601700608169000a01240638016000c005404d009302ca013003d80070b4e1a9014d0ad901bc07cc02680310036007c000002300100004005000b001e00b000c8004001c0000cab1d9a3f74987898706a80408096c33b0169020201e004d02cd00d400e8019802d07f205280848017002a005808680c7005e001400800130024004400600dc09f00924018801b0000008c001000900060020000800b007000a000c800e00004c34fdc9d9d21e44c389881d9a4c3c21d42d38204091a04d80cc836f013402280168042002a03c40638016008000fc020803e007a00140228044050800400098012002200300030007039c06b417e00de009a00c4000002300040024001800100160098014800f003200100001d9a3f744c34987261e3b381a901fd0070016a0001daabb37087643c887a152f06de001c40a81ad1028057056c00de009a00c4007800032ac7ee930f130e3b344c3056c8284002c001856b881303e6007c00c8004003c000087192ff3b347ee930f1d9d1028026812d802d02d20054166806c0a1a005814200060af6073805480de03e60134018801b0000008c00580190008003800012ff3f744c3043a930e3b349878ece081500b80014029802a00c8053004605a60d4605e412d8169059a204804d007b039c001c00302320508005856b00de03e60134018801b0000008c000800b001e0064002000e00006558986130e3b347ee930f12fe15b002480328014014a00d007a043c06d01694408881008580f9400000020012000c0001b7f50767ee530f1d9d0cb210f4a978873523416980b9005c00c8025c046020202e2054424e0157018806ac0cf0186027803d4080000d0192006c00f80230002002c01300280052007800700003f7454a8fdc86598314a0ecece843d,
  0x1068607282218442104404d4183822604e603281a1022802ce0204574001b01360080000285b51363b487650ed01d983b1876a283950b2a264110a83f36fe987932103fb0d380c4c288023e09e8000130ea6234cfa98f400183430d4c077c10682b203e207781078021050209880c0844308840a280860307044c0de80be041d0600008000028595132a16c110a89b36fe98793210ecf15d00a100030016087e143c06f0ae7088207cc026801f0032001000f00003b349878fdd00fc03d6045c11d81cc020e075801086aa052c0a3810d816201e20108006808a00c20dbc1ca000605660e58038002d002a01b007f0ae607f200584108065012c006803a00530020004c01100120018001c2d506ab0a22110411682b4093a07cc01880000004002400180010016009800780190008003801000003b347ee930f10f215ce00cc00b8059011a03d805e805f00ca025803a00530020004c009000c00000008004800300100004013800400007674fdc90f421e4195ca978875507c0e5828703bd01340810350858a0b4e05a412b02cd07f2005841080100026004800600070b541aac288844103e6013401880020012000c000800f00320000ecd261e21e47ee89870ae600f8012007680fd0250057413903690778008411e016101a006a40750125018a07582c700a4021002a0036843c087c041c0030034009c00f0028002a04062080142001400ca009404b001a00e80014029801c0020009000980220024004400600070b541aac2888441045a167024e81f3009a00c400000020012000c000802b001e001001000003f74766930f10f20cb2208400b081f06b203f80030015008400e82d4816500980298053804d003e00000058026005000b000c800400004bf8fdd10f221e89878ece9fb910e616a80350101029409781e305a3021c047c06b802100d807581de8015013a2b9440d06a107f2169c009000701260058410081c01881444220822d103a12740f9804d0062007c0000003001000280058038001e00b000c801e00400000ecd261e3f7443c8a9706ab0464169c003881f000c0a10288844103e60134018800f00080000fdd10f24c3c76689870659104020500ae044100620000879261e3b347ee897f851100b80014029802a00c8053004605a60b50206040900fe053402a42d4800000020000fdd10f221e89878ece9fb9087a1964439881f09e8008410581d60f8c027421306a00d482b900b481e1059a2b8c40f0016050800480030007039c06b401a822d0a2012740f9804d0062007c0000003001e0064002001e0040000130f1fba3b34767022082f703e2036c10780820042007414b002e043601a0078808e008406f00450210024007980df036f074800b400a806c01fc00d41f602b400620000005000b004c001002a002000007630ece1d9a087654bc43a86574c3c655c9878ae403e20bdc10780db0042020814b001d043600b8286806805f8023807881bc008403cc04501e7035e04800d701bf03cc06f81b781c7074800b400a80710182207800b0284000c001c0e701ad006a0fb015a049d03e600c4000000a00160098007801902b4001000f005400400000ece1fba3b34987941d0ae3093607fc02c038503ca08e81030119025c05ac10801af024006b80df81e6037c021c0d5818602600eec1488100005a00340cc80c9040805e457101e10880031000b0040007e010401f003d008a0110142001c0020004c00900110018001800381ce035a00d40f980310036007c001000900060004005800f0032009c002001e001c0060000261e3f747668ece152e103c00e80930078036803801f98199005a005403600fe15c205a41668440002c010001f8041007c00f402280440508004000980120018001800381ce035a00d40f980310000000800480030002002c014000f003200100001fba3b347670a97261e36fc2b8857005a3052c00840eb009d102a096c3520016050800480030007039c06b401a822d103a0ad024e804d0062006c0118003001e0064002000e00400000dbf261e3f747668ece1fb6261c2b8400a802d00e215d806081720188004401a804d003e0000000800b003c0000fdc843b21e854b8ece1fba0cae21d541d04400508001800b043f0a1e2b7c40d86a803e6007c00c8004003c0000ecd1fba4c3c655824e80b204f605b006e80b9008e005c019816a03b206580e4815b00b2036807b000d004202f402f81c201c80acc0db00ef08780cc80c581eb020e053005180060068013c027007e00780140015002f0508005856f0065012c01d0029881c087c0050012801a000a007000800240026008800900110018001c2d4881b01fc1aa00f98031003602f000000020012000c0040001001e00640138004001c0060058805400400000cab1d9a3f7498788790adf0066005c02c808d01ec02f402f82b3000c2b74032809600e8014c21f00100026004800600fe00000008004800300100004013800400006558987a61e3b3a7ee487a10f22a5e21d432b8ade03d6045c11d81cc020e1a980ef820d056407c40ef020f00420a040ae831a01d80528024006a01b601f0080808201da03dc00e8192035800b80d881f800d00e5412c005915b8003406481790d540a3810d816201e2010808c812e016c0228043836f00e000b400a806c,
  0x1008a011000e00100048004c011001200220030003849f006a03f000d80bc003e000001180020012000c0040001001600a4007802c0032003800c00b100a8008000006593b38766930f1310261cb1c857b082906d0068805801100092030c01b820c041406840e200f90190053c095015302ee05c00bb009f01ec01980190047015c2bd401d00780416007427a002e002e1660083003302b207b806782aa034a08f8059050a04d014141b0848206c00ce024a831907901fc415a044406220a5801080e40350027807d809d00fa2bd000a802d03320484579813f038a05e005d00b50cc608c857906ae01142bc42d08042000c0428021808000b400c006e0034009e013803f003c00a000a80178014008000fc0128041003400f801e8005008a011000e00100048004c011001200220030003849f006a03f0018801b01780000001000900060020000800a00160098014000f0032009c002001e001c05600588054004000009871d9a0cb29878ece2c9015f0059012280c9001a096833680b00b5c04fc0e281780174013c03f0050005e0050012801a000a007001200220022006c00000020012000c000800e003000016399d9c3b34b24d30f08752622196541f8af5078e096800680610246012c023008e037808400f3809803de06bc09001ae037e07980df008701dc00dc2d68049027e07140bc00ba000c0428021808000b400c001a004f009c01f801e0050005400bc00a00250034001400e00240044004401a80fc0062006c00000020012000c00080270008007800700180000b1ccece1d9a592621d49888659507e9879c8d05ae001a144804805ac03260204057049b008e084001901dc03280ab80f681fe03e0079c1ca809803de046409700b6035e04800d701bf03cc06f804380ee006e012400b80b000660da00dd82a700e600540168199027e07140bc00ba000c0428021808000b400c001a004f009c01f801e0050005400bc00a0040007e0094020801a007c00f400280450088007000800240026008800900110018001c24f803501f800c400d8000004600080048003001000040058029001e009c002001e0136003800c00002a5c54b0fdb130e4c3c766832c9d9c2622a160a950af4056a0a0018c83c808880da414b002101c806a004f00fb013a01f4039818a02a8010001f8041007c00f40228044004600a401000002a5c54b1e0b3b5a7734ed09daaa61e32acee5c42381ef08481e600230037009601240a380a90b5620a035681a9082007d806280df01d4049415d834902100598032006d015003080030af0006003c0015002f000a01701ba80800536025c1bb004e00fc08081a5802502f80f5c10a810c091c04a40c08591042c0bdc33c033e03e2140019b020f00420a581f605930b440ad03560443060e0d102210226063601680bc012d044000f0028001a0158038808b81cc07f605ac0d5819e030c04f007a81300200003406481e102fa021424f01fc024203800bc813602ae0cd00a280170090007400a809a00d40108079003a01ac035406a00d301a403441c080550206022002d8051009801ec13480c00108029802b80a700de00d407e00310036000001182f40012000c00400010056002800581cd0070009801400290008007800700540040000130f130e0cb27668ece0873093e0eb427807f707200318023014d01c603f4025817b021609c40890326037a0001648acd1592619656699fbb21c4439152d9d963b38766821e9307105010880798058047010e817b01fd072400d4018815a004e0078000043d21d843c087710e421cc4388ecc1d963b1c7650ec61d9c3b34a9683568390006403180a680e30186011802380fd02f6042c088004b02fe13702a6034d03f20d9c03a801f00580064000130a26004c20981130c25fc4c409872c9358e2b245668acd30cb2b1dcfdd843d3b38766898305ab04b000c80230037008e012c0248148028e02a441380350062009c000130026044c28988130826184c39648acd33b347630ece2c735926196563b9fbb08762bc0133835408b4050c0470353018c011807180fd0096042c1388112052e01d408f8826006a00c400f802c0000b1cc980130226144c40984130c261cb245649865959a67eec21d9d8c3b38766897f082701c6042c1fd034d006e01d402487cf003e00b00002c7326044bf8988130026184c28984130e087643c887a2c910cb27eedc8d08260d362bbc353882504c42090145046806f411a40408aee03be083415901f103bc083c0108aed0036026c01000004c3ca0e541f8ed21d943b407660ec61da8a464110a89b36fe990d31ea67d32ac1ab01b6031906c02014059082315d82bac40b081705e202f005880004c869bf533f8cac19646568caa1956000a98f5fc90825056a166814985060678166c00026fd000a99fccab195a32a8657065a882302d807c835281ca104404d413980ca02ce09a000028390442a0fcdbfa67d32ac98f4659195432b432b00028ec915dc10f4157800032ac6550cad3f7304d02ba8574869c000099f4cab263d4c86000c5768081083a0d0800d809b00003b487650ed01d983b1876a35410688020418002280036026c0000ed21d943b407660ec61da8d40418d81f202d810f421c838907100bc411681df041a0ac80f8833703ac07781078021,
  0x104a2077401a8031003602f000000080310007800c00b100a800009881fb8507c4c3c0019d9a10ea7670dbf021f72341964fdd952f15fe0874132851305a20b4015782cf06260b48167031202d808f806e80b9008e00c80330afc04c60cf400b80fa006000a800280110062000001180020012000c00400010052003c0020000507c4c40fdc021f2a5421d5c8d1d9a3f76196498780033b386df8a97083103de02600d78120035c06fc04380ee006e012400a802d01c22bec003010a0086020002d00300068013801e002a0028009400d0005003800900110011006a00c400000020012000c000800b004e001000f000036fc087d63b80032a5454b8987952d10eae46832c9fbb3b3476708720afc050402c812002ca02ba0c4007e833a018c15500a1805804ce07100b40174027c03e40a7812a02a605dc0bb009f01ec00c802380b901ba0874024007c02fa0744195819f02d407640cb01c902b607180f4016403f6089413780da03a803240f080060214010c040005a006000d0027003c00540050020003f004a010400d003e007a0014022804400380040012001300440048008800c006a00c400d80bc0000008c001000900060004015800b005000a40138004003c02ec00c00b100a80000dbf021f2a5ab1dcece1d9a21c854a8a97087572347eec32c930f0006a0ec57d80b204f605b005e00b1000032c86580cb6195c32d1965821d015800680710050022e041c0e603fb035606780c3013c01ea04c0080000d00c205e40fe012101c002140be8145051804d80cc809a01e4035806a80d401a60348068838100ac0220028807b0108015c037803501f8006c000002300060020015800a001600e001300280052007800700003b38766930f130f0cb221cc1e4834a01e6016011c08300d6007dc21082e805fa18f022d03a715f41de00b7835301c6042c1478127038c08a006d000d04b40da00f080b0105e04fc0e2817801742be457c00060214010c040005a006000d0027804e00fc00f0028002a005e0050012801a000a007001200220022001c24f803501f800c400d8000000400240018001001e05680138004003c003800c00003f70987832c9d9c3b344c38250800d03a60b500e50397105c06940f701cb020c1114415802e0d5e00742d70af70042039004f00fb013a01f4416882c008c02380de021003b8065015701fe03e0079c14780320130042c1ca81ef01c6046409700b6035e04800d701bf03cc06f81fd008701dc00dc02485af000c0428021808000b400c001a004e007800a800a00250034001400e00100048004c01100120022003001a80fc006200000010009000600040050027000800780070018004000016489d9c3b34987843a93110cb2e46841781270636003410d025a003600000070018000021d4988865919543b487650ed01d983b5142c9b7e105c00340b181a703020ac028981230164012c132801d05a20b4015782cf06260b48167031204f605b0223002e047c037422280cf0066005c02380ae0042039004f00fb013a01f400800130024003005e00000004002400180080002002800700b1004000022e3261e10ea54ac32cc5e22622767087a10e5507c2bdc0ff815b043407700f8001b003001500000caa195e43d08729d9c36fc144c2d7001d015c00b8023806804a202380de021003ce00c804c039503de046409700b6035e04800d701bf03cc06f804380ee006e01242d780060214010c040005a006000d0027003c00540050012801a000a00700120022002200d407e0031000000080048003001000040050027000800780001d9c3b34e46843a93110cb29878a97882c00e602140a3082b005c1abc00e85ae094000c81ca81ef023204b805b01af024006b80df808701dc00dc02485af000c0428021808000b400c001a004e007800a800a0040007e0094020801a007c00f40028045008800700080024002600880090011001800d407e00310000008c0010009000600040050029004e001000f00003b387669c8d261e0cb221d4988952a2a5c20b400b804701f402b80000023000400240018008000200a40078000262254b8a9506598b8ca0f8250013600e002682d68333005a20a82180015008000fc020803e007a011402200100026004800600000046000800480030002002c01480000cb221d4fdd93114c3cb1c82d7800d00c20f1c1020085019a04a407100970612096c0398445005c007402580460376023801981bc002e084002381e7025600c804c039503de046409700b6035e04800d701bf03cc06f804380ee06fc00dc0b4804915ec05200a381160406001808500430100016801800dc0068013801e002a005e0050020003f004a010400d003e007a0014022804400380040012001300440048008800c000e127c01a80fc0062006c00f8000004600080048003001000040050029001e00b00138004003c00380001fb80cb24c38ecd1d9c4c3c4c4057c80dd02d8008418a80e4020c033c04f00fb013a01f40100000782ced69dcd3b427676ed5d30f152b088a02c813d816c01ba08bc0e1801701f409140b501d9032c07240ad81640042036806480e4001a0d90130036d0d3004141538204026c01cc038009a01d20ccc0168430002a037001a004e007800a80178014008000fc0128041003400f801e8005,
  0x107220154081805b01800298053803500620000004002b001400e001300280008000032b9fbb3b3876684398140001a04144198199160e00b400a806c01fc2c18020003f008200f801e80450088004000980120018001c359001607f803f000d80000004002400180010016003c00c800e00300000fdc261e2a547668ece1b7e0b64019802981c70456003001a800000100004002001e0000195cfdd9d9a8fbc21d4ece152f160e0e4000300c6008c0da809a00ad029a038c024001d04000588019007c005c030c0350042011a05f404281260202022800b81d102c600e80fe012101f40cac0bf007803d4049c12280eb01c007a01a1022802c80dec1ee01fb044a09bc1f980da0192066409b0040007e010401f003d008a011000800130024003000386b2006a03f0018801b0000008c001000900060020000802b001400e001300280052003c00200bb00300001d9ba61e36fc54a810f86573b387668a970833091a01c0070802d002a0ccc038883202d20ce415380070d6400581fe003501f8006c00000230016003c00c80a1001c0000ecd1d9c3f709878a951b7e261c2c181c800f70156016405a800601da01a00a2865f00ac0220028808400ae01bc01a80310036008c004002b001400e0013002800080038000261e2a546df8ece1d9a10e61ac80d4080101141684021082d105820bc5828007079203f82508000004c003c0001fb83b38766930f065907f802380de0046042004800f3004b01dc036c00e8037088c00b80248445002a072c016839801342c10019006603ce0ca42d805b1000c0428021808000b400c001a004e007800a800a00250034001400e00100048004c01100120022003000383c901fc128401a80fc00620000001000900060004005000b001e009c002001e00007ee130f06593b3876689880b0500e00ccc15b0430005a0fc858185b10020004c009000c000e0f2425080fc0000000800480030002002c007800026207ee0ecd1d9c0cb29878a950b04001a04000648b02026007fc24d8210024007980770037009200540ee01f003ce0ca42d801790b62010c018003400540050002801c0022001c1e480fe094200d407e0031003600000010001001e009c002001e001c0060000065926207ee130f1d9a2a5476723ef8b03062a05b006d80dd009602e400e8047005c005c0428309021e02400068b0104c6121408d004603fe023824d81bc042004800f300ee006e012400a81f4006407700ca01ed03fc07c003301e7065204ac2d805b1000c008408500e4008603bc040018b00b4041c01800a30068013c027007e00780140015002f0028009400d0005003800900110011000e0f2407f04a1006a03f0018801b0000008c001000900060004005000f004e001000f000e0030008000047df26207ee130f1d9a2a54767032ca83a1604012c06d801d072e00b816a0085078e2c00066812901c4025c0190066025616c0018002a000a004000980120022003000383c901fc03f000000020012000c000800a001e00100001d9a2a54767141d261e2a5a6dfc98786598bc4088458080b9008e0ac000b81a7061200d40000023003c0000ecd37022a5476701109b7f0cb31718987a83e1600081009b0199008000fc020803e007a0114022002300520000a97152a36fef059dad3b4277349879d9b82b6040804d80cc809a038e00b400a8049006e1ac4003010a0086020002d00300068013801e002a0028010001f80250082006801f003d000a0114022001c00200090009802200240044006003501f800c40000023000400240018001001600a4002001e0000e46832c9d9a10ea7670dbfa61e21c816c04188aff012007d00ca01ed03fc2bf8006844715fa01ac01080e401de062c08380a3009e01f8028002f0028009400d000500380040012001300440048008800c000e0f2407f04a101f800c400000020012000c000800f001c006001000004c3c4c40fdc1d9a0cb27670dbf05b10326032800d809b00003b507660eca1d9cd39c0fa0164048a03244188136038e00b400a8049006e1ac40068447000c0428021808000b400c001a004e007800a800a0040007e0094020801a007c00f40028045008800700080024002600880090011001800d4018801b0000008c001000900060004005802900080078007000026207ee0a95087572347668fdd8659261e000cece1b7e21c82bf80f78098035e04800d701bf010e03b801a8031004e00100002a62566c10ec8721d9a3b38a95c3588263020a1ffc00d8018000122fa40148428fd4f059dad3b4277346df89881d9c3f70088422382650164144c16882d0055e0b3c18982d2059c0c4813d816c047c03741cc003200b00e540f781e50474081808c812e016c06bc09001ae037e021c077003700920054016809a000c008408500e4008603bc040018b00b4041c01800a30068013c027007e00780140015002f0028009400d0005003800900110011000e0f2407f003501f800c405e00000004002400180010016003c0138004003c02c401000004c3c766898786593b386df8a958afd002e011c01980b9019e000000400002a564c3c43a86598b8c98881cc003707700124070801501b4071c0ad85130164099416882d0055e0b3c18982d2059c0c4813d816c047c037405c8047006412400810263,
  0x103dc14141b0848206c00ce024a83c8056811100830311052c00b80d4001d011402b4021004602c4022c07182830d1218e828a839209e00af00e781e406480bd807383ad0d6a0018118829403c202c001b80fe00e201b000a8021005a039004d009e01f6027403e8010002600480060007028000d407e003101780000001000900060004005000b004c003c002001e0162008000013114c3c7670ecd06572a56439041c8487058e00341628447106401ac07f00d80152031c03600050452085c113801c00200090009802200240044006001b003e0000120825f04f80008004800300020098014002c0032003800c00004c3c7ee0ece1b7e10eab1cc32b9310107007bc0d78120035c06fc04c0115010e00d4018800054ae4390ecd1d9c08760e741d9800600e0014c0a4833f0018001c0a00035006200000040001004c003c0138004003c0000ecd1d9c0cae7eeca9784480a2a08100580b1001e002f80a7812a02a605dc018008300cc079c194812b161e001814286b4006e03f8038806c002a00b415b05b2000a00400098012002200300038140002c0ff007e00000004002400180010016003c00c8004003c0000a951fb84c3c7670ecd152e106e0bc015a80b205000cf0130830f06d6123c13e8434071a06941b4824007e207b801080e404c40604099033e03980288145010c0198085808b805e054004680068081090e20d8079837402fa0214052807c005c010c024001d034603b0041012404e20448066812901c4025c03a82c003b8065015701ed03fc07c00f3832902d203f808700d8023e035c05480c700e201b02d90014000a00700080013002400440060007028000581fe003501f800c400d80bc003e000001180020012000c000802b0014003c016001902b4001000f009b001c0060058805400400000a951fb8260010f4ec81d963b287660ecd1d9c21cab1cd30f13101620011804580ad0506007428a802e0648039c0a306b500e608100f080b0161c001814286b4006e03f8038806c002a00b415b05b2008000fc020803e007a01140220010002600480060007028000581fe00fc0000008c001000900060004005000b0052003c00c8004003c0000fdc152e2a549878ece1d9a21c82c3c586848703d41614163800d161807f0080806a02940b001e3016901fc043806c011f01ae02a4063807100d8005401682b60b6400140080013002400440060007028000581fe003501f800c400d801f0000008c0010009000600040058038004c00a0007802c0032001000700003f707670ecd10e42a549878a971310161c005c07d0072078e04b00428075005c049000e81a3015a010c02300a4011603400738098017e0a0c0900b0b00420a800720081032606c019f01cc0264028841a829f0410081c244833502a2085808b80cc00bc1450144019d06ba0810066848e0252038804b8006050a1ad001b80fe021c036008f80d70152031c038806c002a00b415b0014000a0070008059000260048008800c000e050001a80fc0062006c00f80000046000817a000900060020000800a001600a4007802c0032001004d802000007670ecd10e4262054b4dbfa61e0cae54b8a9502211618087416900dd039404d407d001700e404b003a833c0676120c1dd01240480068c1310043051402940be837400f808400240b0a026820d0063043b03de06bc0d701bf03cc06f85848006050a005000e00070280007c0000023000400240018008000200ac014800f005800100002a5721c8a96cece1d9a2a5ad508fdd930226204c10987130c26144bf898406572a5c54a9a73022136fe000cecb0b0b043a0b4806e833c0676120c1dd01ca048004d413100fa0514005c0be807200f804b002400750268049006301a30250010c13380a4064803400d88098017e1f9c00a001c000e050001a8031003e000001180020012000c0040001005600a4007802c003c000152b90e43b2c7670ecd043d3f764c089881304261c4c3098512fe2610195ca96b5422a5c54a9a73022136fe000e1d30b0903de082809581af024006b80df80b6013e045404380350062009c0002a5754b67668ece043b050a00b800e8085015a0f1c023000d011c02400de01f4042006500f681fe03e0079c04c01ef035e04800d701bf03cc06f808a8087000c2c200580204019a04a4071009700e606ec07d0033002e0234019003701fc043806c011f01ae02a4063807100d8005401682b6008000fc020803e007a001402280440020004c00900110018001c0a0003501f800c40000023000400240018008000200280058029001e0064002001e001c0060000152e2a547670ecd1b7f4c3c195d52d06b4003a02080170112010a01d41e380f0001a02f8048003003e801b40ca01ed03fc07c006f86b30874142417b049103fa0e4810200cd0252038804b80050020004c00900110018001c0a000fc0062007c00000020012000c000800a001e00b000700180000a96952b9d9a3b386dfd30f283f26044c40982130e26184c2897f13082a5a195c21e8b080cc205ac1c600580d1a15dc2ae81aa042006bc09001be017e026001a80310036009c00f0018000010f552b9d8e3b24766887510e63b386dfc87206b3072000c80630046029a038c061808d026802b41000162024c001800b8048003a01a8021003a,
  0x100080001d9b952f76aa43d152daaba54f4a98941dab364c3c76748790b1c06dc00180dc811508fa01fc04d00f201ac035406a00d301a4034403d805700de0000001000100160098014002700080000a9790f40cb221ccfddaa574c3c767541d0b1b015800680710050022e041c0e603fb035606780c3013c01ea04c0080000d019205f404281fc024203800bc813602ae051419a009a01e4035806a80d401a60348068808800a201ec042005700de006c000002300060020015800a001600e0013002800520038000261e261e1964439952e108806e4043814b000c0e4c2da87e607fa016415f0286057e01c0421833916321ae404d0056009801ec15b80fc00620000001000300100004005802600500284013800400001964ecd08734c3c4c3858d021d01ba05a80ec81960392056c0cb802101b4020c072000d00be0a541070264022204f41598108014802a00368006010e06e42da02b700360010007001800a8008000021d23f6c54a89871d9a54aea9e95312aba566c987952da83b36fc16d400d0050015805e0071011703980fec0d5819e030c04f007a813002000034064817d010a07f009080e002f204d80ab81450668026807900d601aa035006980d201a20220028807b0108015c037801b0000008c0018008005600280058038004c00a0014800e0000987898888730cb254b8421821d01ba05a80ec81960392056c0cb80da01060034010805f027a03901598393052a0838132011106dc042005200a800da001804381b916300ff402c82be050c0afc0380842013403c806b00d501a8034c06900d100ac01ec02b806f00360000001000300100004005802600500010007001800a8008000008733f7643d098706594c3c76749880b190726001803f857006de11f41fe816906660af814302bf00e0210804d007b00ae006c00000230004000c000800b004c009c002000e000021ccfdd90f426204c3832ca61e3b3a43c858c0025042a013804b0080000000240001fbb2a5e1964439aabb07fa016008a01f7084202cc0b7804601c6012c0858112052e01d408f80a90b66037c0b9803001e000a801788410352001458b861c00b81ae01ba80800536023004b884006ec013803f0202069600940be026401d404941eb821502180c1435b848e03f404a40c080060b22085817b80c20cf00cf80f8805a025a08802800336041e00f0028002100340a5805603ec0b26168815a014401c41ab008b844308840730183822607f60d1018d81ab033c061809e00f50260040000680c902fa021424f01fc024203800bc813602ae051419a0017003a005404d004201e4035806a80d401a6034806880550110016c028804c00f609a404200a600ae01bc00d801f0000008c17a000900060020000802b0014002c0e68038004c00a0014802c004e001000700540040000130f1d9d10e64c3898806593f7643d0a97084204b000c80230047009605200a38037104c0124013800058e64c08980130a26184c2098713105922b24c32cac773f7643c887a043b723416cc00681051066066415b009a005a005403600fe162c03040b48b150890005858a0040007e010401f003d008a0110008001300240030003883e02621ad801a80fc00360000001000900060004005800f00320284007001800009878ecd1d9c056e16500638191002a0a50016883f000a004000980120022003007e001f0000008c001000900060020000800a001600a40160019000076688791fb6507621d4a970657262098789870b1604b60ad804d001b00460038000261e2a5cf059dad3b4277344c388791fb626207669d9b883f01c20664016801500e20b34020003f008200f801e80450088004000980120018000000100090006000400580003f72195c43a952e4c3d170858a8070005a15e800a833300922c4c1018034009c00f00150014004a0068002801c004800880088007107c04c435b00fc0000000800480030002002c00780a100007670ecd261e0cb22c500758b1203d007ec112826f107a20f041d80da0404084000681dc03280ab80f681fe024007980df01c200d61ac4077043c03c200dc06080060214010c0db0080066401680f5803002981ad801a80fc0062006c0138004003c02ec00700180001179a2e746268d449878ecd1d9c8b862c4c24f83c9002c050007e001900009878ece1d9a10e620f804081301074040028a800d03b8065015701ed03fc07c019480c90408078441c80b0094405e458880fe021c036008f80d70152031c0360015004200b4072009a013c03ec04e807d106e1120002801000260048008800c000e050000b03fc01f800c400d80000004002400180010016003c00c801e0136003800c002000009878ecd1d9c3f701ad80678343041600cc0d4025e00f0005c0450101007401c8021006a021204b0078814a03f201d414b83c60b2a007c000000800700098014002c00004c10985130826044c3097f130e0cae21d4001952b262012880b600dd0d18167c05d0083017c04a8018051500da0ca409580df10720018118829403c202c041c00fe00d80054010802d01c8026804f00fb013a01f441b8448000a00400098012002200300038140002c0ff007e00000004002400180010016003c00c8004003c00800001fb84c3c7668ece1b7e16220694059050a,
  0x100380090011001101780000001000900060020000802b0014009c00200b100a8000043a9b7e3b3aa0ec87a10f254ae10ecfdd8659261e000ca8d8b27033e07ec137810007960a98158829001b204600d3825200bc0964046016102e6050c06f80c6013005d407e80e7011200340ae80b3011c0368120004602b60ee8025821d01b6099418a821a05a20b4015782cf06260b48167031202d808f806e806b003602ec007001800a8000137f26824c5499096498003261eb34c32c90f421e4dbfcfdd843b566c767541d9b7e4c462c98040819e030c04f000d809b00003b287670ec81d8c3b51a7183cb033e0400145813c01020dc059285b7108a16d82890175001a0368035801b0176026c007001800003b287670ec81d8ca0ecdbe1b7636e06df942c086501d6119c27200bb00300000db71b7836ec6dc0dbe1b7236fc3b4c1b800fa0566005c00301c3010e00c80dc85b5107e081014a0073164800dc0b48049010000c002d004304060138015003c0068005828b06b9018e0fc81e502b80028010001f80250082006801f003d000a0114022001c00200090009802200240044006000705aa0adc07e0031003e000001180020012000c00400010052003c016001900080000ecd13104c3c54b8a95130e165206e40438258000c0e4c2da8032008c070c0258017003a00cc01701bb028c051c08b008000600168021804e005400f001a0014004a0068002801c00480088008800705aa0adc07e0031003e0000001000900060020000800a001e00b000c80270008000032c930c26208748fdb152a3b344c3941daa574c3c546c59202940b28026835d00fe00d8031c00280110000000400c800058e621d4a9713103f76987941d86570a2c081024681910020004c009000c003e000001180020012000c00400010014002c014802c000021d4988130e0cae54b941da61e2a541ae800b030c0b5e2c8c00e802e00d4010804281010114005c0b182c303f809d4090838000be03e80bf021d03d4049c12280eb02d407640cb01c902b607a01a1022802c80dec1ee01fb044a09bc01d00da019201e000680e003a404141f98199056c0268016801504ac0050020003f004a010400d003e007a0014022804400380040012001300440048008800c0036000001180020012000c00400010014002c01c0026005000a400780190176003800c00540000767541d88753f769878a972c72079409a017b81df041a07c40f901de041e008406e80db043602e404100f100e4123400b043006660ba80030b2200320010010000087890e9220243aa58e24c3164b2cd65aa4b1f9668c3a73f76b1c8a96952a36fca0eca972c775922b24d30f32ca19644c4059180210686039005c831a043603bc051818b020e011c0bd810b009e00bc03f0050067400580e1811002c400c80a680c301c602dc1be021406a6007c0160019004000021e243a488090ea8fddac7126184c4164b2cd65aa4b1f9648acd158ee987821d8b2201c2066401680151642010001f8041007c00f402280440020004c009000c0000000800480030002002c0001d9d21e87eec43a952e4c3ca0e815c01b9017e2c800030115006e0ff803f8004000054b8ecea83a21e87eec43aa61e58e62c8405802030092005803880190000b1cc43aa61e507517081ff00b00406012401b80ee0060010c0150034002c2c7c03f8014000a007000880000004000400c802700080000a971d9d087a43d0fddac7310ea987941d10f2164001980180098017c039c078008b00ea011808900ad010400740170089010a07f41e38279163c128801080e4067c028809901cc042c01780660117020a00342520129012e033407100bf07ec00dc05800fe021c036008f80d701520fe4038806c018e01fc00a00250034001400e00100048004c01100120022003000d801f0000000800480030002002801600190008003800c00200000b1cca97283a4c3c767443a843d21e843c8fdd8657163e029002180d003460260092012b00ea020c096003200e4070c00b805f01f4007c0000023000400240018008000200a4007802c00320000a97152a3b3ab54966b2c9626044c20982131026184c2897f130e21e843c9b7f865758fc7eec21ea83e163c19e82438127058e1614090808a008403c414b810e01b0047c06b80a900d8031c00280110036007c0000001004c00a00160019000021d4988130e2a5ab1cc32b821f0948055c0710074015800681df80c2000c128c0a2011703980fec0d5819e030c04f007a8130020000340bc80610930048c058030d051e06880d200ae06b200dc07f00a901c601c8076008200e201b00a5016201e2042400b0b1d002e012000e8015013401a8021003a00aa040c02d804c00f6030005300a7056e03f0018801b003e00000118003001000ac005000b00700098014002900580064002000e0000766930f087305aa06e404383fa0000a9d487a2a574c3c10ec251821d01ba05a80ec81960392056c0cb802101b4020c072000d00be0a541070264022204f41c982b302100290054006d000c021c0dc8b1c16360ff402c82be050c0afc4220037009203f858d001500ac013003d8057056e03f0018801b0000000800180080002002c0130004001c006002a002000007668439a61e0cb22c74159805f000c03d81b78027,
  0x1001c0000986131054ae987843a952b36fe1964fdd90f4507676749870b3402a205c407a019301940b9409a80d000be082805b80660064070c00b80330394033c05b00870028009400d00050038009001100110036007c00000020012000c004000100580064013800401360000a959b7f10ea4c30988130e3f76acd887a10f254aea98821d8ed41d983b28ece82214c442cc410e82d2062400006590cb4195ccb2c15c80830064065c1cc00dd043a05a80ec81960392056c06d000d00be04f41598006010e06e45980b2f0042039004f00fb013a01f401b8049010000c002d004304060138015003c0068005828b03ca05700050012801a000a007000800240026008800900110018006c00000020012000c00080190008003800c005400400000a97131021e89878ece952b10ea7eecdbf0b33008c012c12c00db006407b81cc01a5047c1250134050a06c20d8019c049506320f2015a044406220a5842300e30946001859706bb0042039004f00fb013a01f4008001300240030001000900060004013800400400000ecea83b36fc9878a958875261ea95c87a06593f7643c859800420216022810d81a800000098000152b261e21d62f006594c78211808304a5005c1abc00e80000014000032c8875261e54ad64906bb01ba08741cc016a03b206580e4815b0064036807b000d00be04f4159802101c8027807d809d00fa0200018005a00860138015003c00680050012801a000a007000800240026008800900110018006c00000020012000c00080270008003800c00540040000130f1d9d21e443d141d9fbb36fc4c3ca95865910ea10f459702f001640ad4140033c06d209000c5007c009003f4130830f06d6123c13e8434071a069406303f103dc064808301b1005c0828033001d006416cc0e1801700662cb40dc80b6010e001859605a104e0051c357011600420a50072009a013c03ec04e807d006e0124040003000b4010c078029b025a0880101804e005400f001a002f00fc014000b0516018e0f2815c0014008000fc0128041003400f801e8005008a011000e00100048004c01100120022003005e001f00000008004800300100004015800a0058006401380040162015001000004c3c6df8ece931021e854acfdd88752a5c4c38597819f03f609bc08003cb05620a401530252034e09640b0814301b20460063005e01fa0230024017302ea01f006f800d0680026006d024001ce02240ad83ba0166023810e804604ca086802582d105a00abc167831305a40b38189016c003a08f806e802e019e11140dc806b0042039004f00fb013a01f4018002a000a004000980120022003000d80000004002400180010056002805d800e0030015001000004c3ce4e887a36ff2a5621d5cbd06593f7610ececea83b36fcecec5968197010603d801901c3002e00cc06780dd043a05a80ec81960392056c06d000d00be04f4159802101c8027807d809d00fa0050012801a000a007000800240026008800900110018006c00f8000000400240018008000200b000c80270008003800c00540040000130f1d9d50766df8a95887526184c409871fbb566ca9e955d10f454c410f459602f0056a02c8140033c04c20c3c1b5848f04fa10d01c681a506d209001f881ee02ba036c07e804b018c01180c900b30362039c04c00df02e602301010b2b002e012000e81ab033c061809e00f5037200cc03e002e0200021c0dd8154028c0034003007301920e4c10201791654008407200ef0146062c0838b29006e0124040003000b4010c101804f009c00a801e0034005e01f802800160a2c0f2815c0014008000fc0128041003400f801e8005008a011000e00100048004c01100120022003000382d5056e03f0018801b0178000001180020012000c004000100560028014800f0032001000700b100a800800001d9a262054b930f152a1664023804480460218012c0c080db062a05b006e80b9008e00c81ca80d005ca03d00a8817102f8046409700b6010e00015312b3621e443d152baaba54f4b1dc001a6fe4d0498a9321130f36feb24c32c82213f76767421d8ecf1656065c04180f60064011c05c80dd043a05a80ec81960392056c06d0017001a017c07d013d05660018594002101c803bc051818b020e0200018005a0086013c027002a007800d0017807e00a00ae000a00250034001400e00240044004400d800000460008004800300100004014800f004e0010007001800a80080000087554ae9878a97152a3b3a4c3c32c9fbb21e86df85950047006402e407b001701ba017c07d021d048a05a80ec81960392056c0b200da019200340828073164e06e4043802101c803bc051818b020e0200018005a0086013c027002a007800d0017807e00a00ae000a0040007e0094020801a007c00f400280450088007000800240026008800900110018006c0000023000400240018008000200a400780270008003800c00540040000130f087554ae6df8a97152a3b3a43d09879fbb0cb210ec59402f0056a02c8140033c06d209000ae8261061e0dac247827d08680e340d280fd07e207b806300db0324012c0d88046041409600330032008e02e4593001700900074019807c005c06ec0aa0146016c021c07780a30316041c018004f005400bc03f00500028009400d0005,
  0x1004203740720197052a09901070111010603d808400a8014801b401380040040000159b2a7a557443d153143aa087a98799652a5b168002e40e180470064020c0cb80dd0042039014a8264041c044459f837504a20dd810e816a03b206580e4815b02d20368199805f001a0ba8159813d021002a0052006d04ac16e404b007400a6019420000140696009400d00050038004035f00240026008800900110018001c16a82b701f800c400d801f0000000817a000900060020000800f00580064007001800a800800001b7e2a54766930f043d262019645a080dd0172008402380e4006403bc051818b020e03d82da0251009e00bc03f0050012c01d002980650d7a100000a00250034001400e00100048004c01100120022003000382d501f800c400d80000004002400180080002003c0c400270008015001000003f6c6df8a951d9a8754987832cb2ca21e42cfc0dc836e000c03b81dc01150b7001fc0298065008000fc020803e007a011402200100026004800600020012000c000802700080000fdd88752a5e43d0a951d9d4c3ca0e82dc8015005a0ff803800370000002c0001fbb2a5ea0e930f087554ac16e01a08151000c05c42530202089202e805f0030167c06ac0cf0186027803d4080000d002c03241ff817910922cf435e02b80028009400d0005003800900110011000e0b5415b80fc0062006c00000020012000c000800f0032001000700003b349878a97040001180da0032034107ea0efc0030848006e01c400b03ff10920a5004d03ca05700050012801a000a007001200220022000000100090006000400c8004000054aca97087521e84c44fdda61e3b3aacd859f0033002e033c03900dd015c0874122816a03b206580e4815b02c80368064800d03840d041fa83bf000c129822480ba017c0058015003016780084072009e01f6027403e82b80028009400d000500380040012001300440048008800c0036000000100090006002000080190008003800c005400400000a97261e21e87674fdd93112a5621d4dbf08490106065c00300f6016e00c802380170066033c06e80ae00be0874122816a03b206580e4815b02c80368064800d01000168021825a009c00f001a001616760084072009e01f6027403e82b80028009400d001c0020009000980220024003000d8000000400240018008000200640138004001c006002a0020000054b930f1b7e3b3a4c44a9588753f7643d159b0b3c0066005c067807201ba02b810e824502d407640cb01c902b6059006d00c9001a0708046006406820fd41df8006109000dc03880210528039004d009e01f6027403e83ca05700050012801a00380040012001300440048006001b00000008004800300100004002000e0030015001000002a5c987887a1fbb566c7674dbf13112a5621d432b8b3b032406c4063020a00cc04d02cf8048047c01f0134084707900ad02220296035002280210162037202d8071808709460084072009e01f6027403e801000260048006000000040024001800100560098013800400400000a95952e4c3c54b043a8657566c43d152b9fbb087621201a08151000c05c42530202089202e805f0030167400581ff81ab033c061809e00f502000034064817916721af015c0014004a0068002801c00480088008800705aa0adc07e0031003600000010009000600040078019000800380001d9a2a5c9878a950b3d06d004fc05d01c502f0013c017807e00a0000164b2cd65aa4b1f89889b7f5076987832c83ff0372021c24980061670069001b80ec061801c4024007c02a801cc10203ca05700050020003f004a010400d003e007a0114022001c002000900098022002400300000023000400240018008000200ac014800f00080000a97152a2622acd8ece9b7f10ea43d0fdda61e0cae2ce804602d300c80d041fa83bf0000b25966b065758fc4c44fddab365136a0fcdbfa83b3b3a10f459c02ea000c16d405b80320940017c122816401920034040003000b4010c12d004e005400f001a0016166e06e43d980fe0b5a0ce435e06b907e40f2812b02b80028009400d0005003800900110011000e0b5415b80fc0062006c0000023000400240018001001e00640508004001c0060000152e3b349878a951b7e167200c003200be011802e80e1034107ea0efc0030087001a00dc21400710028009400d00050038009001100110036000001180020012000c0008004001c00600002c732a5c21d4a9536fe36fc4c44ece9fbb0cae2cdc0d8819204140198063003201fa0e600ae8048047c2cd803e0268108e0f2015a0444052c2cd44230b34037202d80718087094600181c98b3300420a50072009a013c03ec04e807d166400dc0248080006001680218203009c00a801e0034002c145806383ca05700050012801a000a007000800240026008800900110018001c16a82b701f800c400000020012000c000802b001e0064013800400400000ecd152e4c3c4c4035e008c02e6080806f817c01300430073808901660238023004b03020074223002e088a072c5988147022c06ac0cf0186027803d40dc8100010e003400300c9072605e4040003000b4010c027002a007800d000a00250034001400e00100048004c01100120022003000d801f000000080048003000200280160004,
  0x110e67ee887a1d9d36fc16f0006821c03a8058404481d20250022c09d832c0430053800d800e0030000152aaa77087aaadcecea83f5076a468dbf10e70d84016036086c016a20378026801f004e0078000130e26184c0032cac9336fcaadd41fa83b523410f4fdc9d9d3f7443d087510e821c443c087210e616a8003410e01d402c202240e90128011604ec233018703c8006c00700180000a95553b843d556e767541fa83b52346df88748b5300b011b41c20b50079a0378026801f004e00780001304261c4c30980065959266df955ba83f5076a46821e9fb93b3a7ee887a10e621d4438887810e421d02d4402c06280a9c007c013801e00007ee887410f421cc43a887110f221e0439098183cd001a08700308161011204a00458272022800380002a77087aaadcecea83f5076a468dbf10e3094e01605a7848c169c0378026801f004e00780001304261c4c08983130c260019656499b7e556ea0fd41da91a3f7410f4fdc9d9d21e8439887510e821e043908710b5004380584006812800c20c0808d805800962d341b380750b760378026801f0058009c00f000e00004c109871302260c4c309801fba0cb2b24c87110f421cc43a887410f021c87ee421eaab73b3aa0fd41da91a36fc4c205a700750f520b8802c0b4c085c15cc1f403ea06bc02780490014169605d007c80c801060d5c02f818002a405fc12a80470b7600180b280de00420d0c12f01a80416033c0f6001700aa0158042005700de013400f80000004002001c0026005000b00138004003c0080000065943ae21cca9590f421e04390fdd1d9d3f724c00986130e8b8c212813402cc03e408742b90389071008b427a833703ac03ec04e821501580930112010801500d8c0928021068609780d4020b019e0158042005700de00240018008007000980140020000010f50eb88732a5632c0659195a21ce2d300680b4a014804900f4804f169203e4041805f02fe095402380000000875c32cac7726004c309872a5b3f7410f4fdc9d9d21e917188722c7e1696204c0ae001f003c000087910f4087a7674fdc9fba25fe16ec0d080c81690020c03a805f030005480a40255008e0378026801f0058009c00f00000cb2b1dc982130026184c189872a5b3f7410f4fdc9d9d21e843a087210ea8b8c2d2804c00bf0ca601fc06f004d003c0000fdc930c59a2b1c49871fba592276756399fb60cb2a95c21e90f421c8a0e85a902b5092c0c64149849706d815d01f6033b0cba0d8413f82ad032a075418c0054000098fd30fa63d4cfa001533fa6fe04660014017805c014601f40000001000054ac98788730cb29bfc1cc827302ce0bfc12c842a001a075005e811b070406d011e00c1051c078809a0200024c02b40b1007102700234026801b003e00b000700180000b1dd639ac915926b1c5668acd33f746df832b851701340ee02dc85b8168e2d18200000705aa0adc07e0031001e0000ecd261e00f20a04010831a01c805ec10d80a30316041c06d813200d416cc02580cc0202007407a00f7029a00b817281ac00d0011806801f804b008280330032168a042c021008a037202d805a80e30860021c25183330798080c0780375053604b4110025107fe00bc1bb007e00a000582dd000d000c03241c98179012c01d0029806500280d2c012801a000a007000806be0048004c011001200220030000000205e8002400180080002002801c00260032009c002000e00400000a979d9d10ea7eec87a1b7f4c3ca0ec5a3849406c20d80167027b02d80c4406e802101c8086c07780a30316041c05c81c3008e013c017807e00a0007c01600190040000032cad522618b35963bac962620b1f9c9ca61e8b8c2d140190047016e02b802f824502c80324006800604b40ba8101825104ac012400b05b8006e005419f83b8005a02685a20400000e0b5415b80fc00360000004000b001e0064002000e00300000ecd261e36fc2d180190047016e02b802f824502c80324006825a04060f3004381b91686094400b05ba000c1afc2dc8400000e0b5415b80fc0062006c0000008001e0064002000e00300000ecd261e36fc54a85a205b40cc603f805483cc168400582dd00060d7e1af42000014004a001400e00240022001c16a80fc0062006c00000020012000400781880032001002a00004c3c6df8a951d9a21e42d0c00e802e009601a002302580064036c02381ee0172069411f00b204d01428282836109040d8019c049506320f2015a044406220a5810d80210216039002100ef0146062c083808a0b68038c1b7816909460ee01998251009e00bc03f0050002c16e800306bf0d7a100000a00250034001400e00240044004400382d501f800c400d80bc000000080048003001000040050026001e062000c8027000802c402a002000006df8a951d9a4c3c43c952b8b42002a00b40248070006e000000580003f7654bc32cb91a10eaa9581e601b90766021c038033f00a600300000008000200980138004000021d487a043b2a5e7eed30f06570b7402b80238b41002e0058019822b00b200c85a0021d02d407640cb01c902b6036802f800d056604f42dc809600e8014c03284000020004c009000c000e0b5415b80fc0062006c00000020012000c0040001001e0064007001800a80000dbf152a3b34987821e86bf,
  0x100840154081805b00a2013006000a6009a007c0000008000200ac005000b0070009801600190008007800700004c3e43d0987152e3f7421ccece9fb816f80084119828107f00c5c1e283c401fa012c0bd810b09f20a4827c02fc00400001648acd1592619656699fb74c3e9bf898685c516f0090c17c00160270005c00e801500aa016c026004d003e0000004000a001600b000c80003f707ee887a022136fe54b8a969d9d26004c109811306261c21cc21e930c16f40084119828107f00c5c1e283c401fa012c0bd810b09b810a42a6034d00400001648acd1592619656699fb74c3e9bf898284a8004208cc14083f8062e0f141e200fd009605ec0858464036611a814e00200000b245668ac930cb2b34cfdba61f4dfc4c0c2e2002104660a041fc0317078a0f1007e804b02f6042c1388112064c06f401000005922b345649865959a67edd30fa6fe260e146002e0005012e00a802f026001440000000800036fe7edc11086592a5a21cd37f885910aa2ddc5bb0b750188013400f801e00007ee887a022136fe54b8fdb93023b3a4c10980130c25fc4c38439843d2a5a4c185bc06c516e81b185b98b720b842dc4428864101c42dc042c085001580c2800d03e200a0215c096807516de2db800b01380188005c00e801500aa016c026004d003e000013e000300100028005802c003200780001302260c4c10980130c25fc54b487a130e044210f44399b7f2a5c7674fdb9fba21c82dd42e18856019a2db40490014009e049042a8b6c10a82dac00b0138002e007400a805500b6013000f800000040020005000b00580064000130226084c0098612fe261c4c40439a1d72a5a10f4ece90e316dc2da85b48b680d8a1dec5b38b6610a82d94429884f061600941f1807e10a40a6c00b01380188005c00e801500aa016c026004d003e000012f80080014002c0160019003c0000a9690f4261c0884872087336fe54b8fdb9fba3b3a10f49858b6f000a00a802e026000fa08cc0108343020c09780d4020b019e06280ab80f201ac035406a00d301a4034402b008800a2021002b806f0000008c0040001005600280058038004c00a00148020000054b930f9fb710e61964a960b7910a21708071085001580068028012d00ea0a6c03f0025109e005809c0017003a005402a805b0098007c000000300100028005802c00320001bb11302260c4c10980130c25fc4c38988087343ae10f5b911d9d2a5a21545b20b6302522d8810a8009000021cd0eb952d087add88ecec843109e01d44270675109a0c3823f86770fb82d840ae00de009a007c016001e0000439887a10e8044243a8872043d10e66dfca971d9d3f6e7ee898710e20d8a038808b8073039802745b00b5f16bc02b05ae822401500aa02e0846d0d8003a802c0b5c079a057000b00de0270031000b801d002a03a407900d601aa035006980d201a2015402d804c00f6015c037804d003e00000118003001000280058026005000a40160019004e007800010e621e843a087110ea21c87674fdd043d10e64c38fdb9b7f2a5c08848780b6100ea2d6c2e0001f00580000981130626084c0098412fe261c4c41c9f8b5e012e01cc22480fb0b7e2d68426005c16b2001410a8b58018e2d5c12600750210212c24603840d820b240d48b56002c04e00620017003a005407480f201ac035406a00d301a4034402a805b009801ec02b806f009a007c000002300120020000800a0016009801400290058006400f00003f744c0897f130e10e67edc21e9d9d2a5c43bc5ae010602ae0e5c04282d400a2008c005000b004c00a0014800004426dfca97087350b41010225022200b00b0c18e021e030e086008a01ea01160d1007a8089062c13941738209046c03e00308090004e000141fa83b54ee767487a10f221d4439021eaab5043e12a8045808901ce018404c000d017e08a803f800e0001062d52b90f421c843c941f9d9d087aa9dd41d04a9109402f417c026001e000a80178399002c16f8063800500b801f41198021068605a00958340020c09780d4020b019e020c19a005f000c16f40f600c4002e007400a805500ac022002d80510098021002b806f003e00000118008000200ac005000b0070009801400290032001000f0020000054b930f887321e87ee8ecea83e0d8e078805e8138011a013400f802c0000b24d639ac77507c7ee832b85be00b8001404b802f00bc01cc05180a2073208cc00b000d0042143c030834303c4078004486c40d860dc402f8b55032e0378059808e035804e40b78192013e02dc0b285bc06a41204177841807b607b006200e901e4035806a80d401a6034806880550206016c03d80c0014c015c053806f009a007c000002300100004015800a001600e001300280052006400f000e0040000087a1d9d3f74987ca970873087616f4006821c00c205840448128011606c40738b540d842d4c25380bd10942d48062808c05f001b4032026001e00018033002a005e031c0b28172000a037802e039900fa08cc00b051700420d0c1a0010604bc06a010580cf028a0d4814882ef07b607b006200170090007400a806a008400e802a80560206022002d80510098030004200a600ae029c037804d0036007c000002300100004015800a001600e001300280032001000f000e00400000a97261f,
  0x101ca00841cd0b8305f00f98003014b01bc00581350059048c0158026801b000000080018008001600980140019004e001000c005400400000fdd26fe4c3e43d0ece822136fc21cc98706ca04fe09f40ca81ee0390000131fa6fe4c3e000c1cd069e00b809c808a00050282016004c002f061c0b2415402c80d3a03c01b3812d00a00068056007410ba05c40d801c002a20330068016e01e8029005280650124005001a036401ca008442e038600960c5c08302430b8a12a02e2051805f00f98003014b01bc00581350059048c005c024001d00d4010801d005500ac040c02d805101800298053804d0036007c000000200060020000802b0014002c01c0026005000640138004003c006001000004c3e9bf8110930e3f7443d0dbf08733b3a98f85c18278036a0eb009a805f010605040fa029d040e045c0ce8125028802a0061006b017600600000ecc1d9c43d087910e821d410f552d9d9d04426dd8dbf2a7a10ba068409580c8004e000087a10f221cc43a8874370302820d9c0a9012c00004c18981393b26184bf89871310723e12f40a90047101008bc17581040390000130f930a26087edc981130c260c4bf89882c7159a24c3832cac77000621705c100de10b60c4419c00b20866099406782ac047a09e812e02ee045c08fc12e819505d6041016581c800422e0400b026a048c005c024001d00d401080d6805500ac040c02d80c0014c013403c803101780000004002b001400e00130019016200800001d9a10e67ee8dbf26fe043e2e14030811b017a012c02380db017207880001fba4c4498f963b86595926087c987885b02a40a5c1c30147008e042c025822f0788171425405c4062e1ebc00d8023001c0000879152a36fc087ca979d9d4c7cb345669a6fe4c3e98f13112c935922196563b9310261c2e080cb809f02ca00004399fba21e8a96d311043b10bc10fc0f100de1700063000306c901ca03b403400f7016a09180d6808800a2021002b804d00f200c400f802b001400e00130004003c000137f1d9a10e6087cdbf1fba000a2e0402f808304721b201d582e6045011d406801270840029013a8065033802481e1011900280db802785a801de07885bf806b002c09a802c80b50156091807900d601aa035006980d201a206b402b007b00ae01bc02680790062006c00000020010002c0130028003200600001d9a3f7498ac439952a043e6df821e90f2170008cc1a0010604bc06a00003b55772aed5ddcba61f000a9bf8a95818c027404ec04c01d206dc0ec412280ca036a02400e9805f01061b20068016e01480194049001400680d9012d8059015603c806b00d501a8034c06900d100ac01ec02b806f0062006c00000230004002000580260050003800c0000261c4c40ecd262b0cb221cca97821f36fc7674879043d2a542dfc0e901d402760db80a70098034204ac064001b004e006000010e821e843a8879151c2a4c54a0a8f15242a445480a953b37087aa95410f9b7e3b3adc0c36402330d860dc436201e0016606b00b7819202ca00004399fba21e8aadd53aaab554ee987c002a6fe08761b2402e000500a602f8032014c0118017805180a2000c08cc006814b00420184287810402360c680ae80db0436078805c85be0a2e02b40a500ec010403c409c0072048c005c024001d002a01a8021003a00aa040c02d804c01800298053804d003e00000040001005600280058038004c00a0016002700080078007002000007ee887a261f3b3a21cc32b826a00b8001404b802f00bc028c05100e502640330010800d03ea018424e008510b400585bf043f03c42df436380060b7a16f00620051003e0000000800a0032001000f000e00400000fdd10f43b3a987c439952e048c055c03e809700b805c8032008c00bc0288119800d00420184082011b0634057406d821b017202b40a500ec010403c4039001700900074035004200aa040c02d80c0014c00000118008000200ac005000b007000980140029001c0080000130f3f72a0fd30f9b7f3b3a10f50eb952e10e6195c5bf017200b8019004b808c00bc0288072802103ea04c8066000d00c21270042885a16f8005806f01380d8e00182de85bc0188005c00e801500aa016c028804c009a007c000000800020028005802c0032001000f000e00400000fdd152e21e8987cece8873261c2df40860181086410cc09a826503940ab011e827a04b80bb8117023f04ba0bac08202cb03900034030801b001c000141fa61f36fea16c00181f5071c08f417602ab05d6086415683e8085a0e3c0ea835e00009bf9315261f000a03941dc80b2032a0b4416802af059e0b3018982d2059c0c4813d816c039008f806e80bc01620001311a61f0006041004580e7011212a8030800d00bc12a40a60066005405c8002805c00fa028811980210686041812f01a80416033c0c50157023a0d48148848103d803c806b00d501a8034c06900d100aa0158044005b00a20130060008400ae01bc000002300100004015800a001600e00130028005200100070020000054b930f9b7f10e6875c32c9fb9507e43d08791d9d087a54b042d0449012e16fc426005c16f60014362802f05d20b2034e81da01e02de82e284a80b88146042c800d00c202145bc82f8002c04e036380060b7a16f006200170090007400a806a,
  0x10108015c037804d00360000011800300100004015800a001600e001300280032009c00200bb001c0060000152a21e87ee930fa6ff000a4c384399d9d36fc43a85cb808108d60e985c9021a05d6219c1c403370da21540368036d0b241b3c28a003c073612ac27f06b700340b50200845d09a402b010e045c09a201d00b084e00586074829b83d7015004a01e0822202760af41a580ea0604219822501cf06ee0dd802c053506ea21885c883cd0da4057043084a700be020c0a08b900138036408c00b800bc0314046006d00c80198029805c000a00a8130000602960378035801604d401640768068065a03dc055824600ac02200288269010801bc026801b0000090417a000300100004015800a0016073401c00260050006401380040136006000010ea21e87ee930fa6ff21d00014fdb930e10e6767541d9b7e044243985ca046808d21d7043280eb0c6213980ba806b003602ec00c000050723b3144ca83f36e86de07650ec81d8ca0ecdbe1b7036fc088548c9b761724017c253808300b0050409280a800e802b000d00500b821230096800602960164076806800ac0220028801f0000000c004002b0014002c0130028004e001000f00003f747edc32c88732a5e43d087910f021d043a8872283b52346df8ece93091720017c253808310c8050406f004d00004c2087a130c21e043a087510e43f744c28987130454b6a9dc21eaab75076a468dbf1d9d21cc2e4434f00f908cc061c000152a6dfcf05821e9b7e10e676748748b9304ee18c00d802e002a2033007a00a500ca024800a004f024801d40bf8047045e07c816602b910c60e2419b837505360db4096837600fc00f0028034b004a00681eb821501580a4015304d1012c01d0161827504a4069c29c0108015008880ce06c2171e0b203000363024a0e28174015c028203205c7027a05560ac80f881750138036408c00b800bc0230032005300b800140150260000c052c06f006b002c09a8076806801ee02d40558246002e015404400510108015c037804d0036007c000000205e800240018008000200ac005000b00700098014002c0032009c002001e0176026c00c000021d443d0fdd261f4dfecb1865700053f6e4c384399d9d0442a0ecdbf10e810ce07c816602b910c60e2419b836d007808bc00d00470158094003a007501500aa02e0846d01d4016043106d210c20f340ae04a700be020c248827a05560ac80f880c5011801b4032006600a60170002802a04c000180a580de002c09a802c80ed00d0091800b805500ac0220028804d003e00000018008000200ac005000b004c00a00160019004e001000f000004426df941d90f421d043a8ece9fba261c21ccfdba61f4dfecb1865700056e042e3804084e3074c2e3436885500da01648367851409fc1adc22e84d208b8134429b83d70f401e8436706cd057a0d2c3cf079f0d9817181bb83760aa4096429a83750112138013a81d200ea022c1e0819c027612301c202c9043c1b2c35802bc02ea027006c8118017001780358068065a02d4055805104d2015c037804d0036007c000024105e800280e68026005000b000f009b00300000fdd130425fc4c08985130e507e1964439952f087a7674dbf283b52340884877886208d211a0101061b0ebe067c07581750138036408c00b800bc01ac00d80bb00300000dbd1b7436dc6df87690eca1d98a0ed48d022152326dd85c680580d821b0000f8027003c0000fdd10e221e843c887310f021d043a887213050da401d41c202c900b021801e6815c01bc013400f802c004e007800010e221e8439887810e821d44390fdd130c26104c28987130410c80d5c154004d003e0078000130426184bf8984130a261c7ee8876886005400a28040832b0ad003ac2730b8c0c3e118014f86a2073612ac5c5875b042c0a2016a04010a9007e810e067002cc05842a500960250214c10a83020616009402c03e300fc212c429029b094e05d404e00d9023002e002f0006029601ac07680680110014400d801f0000097c004802b0014002c0130028004e001000f00bb013600600001fba3f6e196487a10f221cc43c087410ea21c821cca97a83b5234767541f9b7e04424c2c430805807080d5c03a818002fe0f340ae00de009a007c0160027003c0000986130826004c38fdd10e221e8439887810e821d44391c8f887101642e285c48b88170e19cc42f8159055808f412e02ec05dc0aac15900bc02b002c402a00004c3e6570caa00054dfe32d065632c610c603ac179054b08ea137c1d506260c901e440b18797084002241618275011608880ce00e703f007dc5c300bb0000439152d90f421e454a8a8e15262a505478a9215222a40ecdd52aaa75556a10f553b9d9d36fc087c36986c801f2020c02f84aa06dc02600002a77556a439152d90f421e454a8a8e15262a505478a9215222a407675d9b843d54aa087cdbf10ea170c0410010885e0d9200181f301e20d9400345c2801604d40164076806801ee02d412301ad00ac0220028808400ae01e4018801b00000020015800a0070009800c8004001c006001000003b346df84399fba4dfc2e84056001a00e800f042e836d02e207000eb015101980bc4068016e01e8099405200a504c20194116009217080d9821a827d002809fc01a019504320d9018c01d5,
  0x10108015c037804d003e000000100080014002c01c0026005000640138004003c003800010f421c86dfd30f88733f747674987283e10da21ac128018002a40bcc02381b6017a10b01f2801700aa000000480030010000141f45ce50b60884dbf9d9d087a54bc4399fba0cb2987c97f130226004c38fdc8ba60124019400a00a5006803d00db02f308580f9417c0ba5014401784358375053604b4110037600fc01401a5802500340f5c10a80ac09a2025803a00890a700420054008b059018001b18125043001a0024001d00d40108081805b00a20300053004d003e000000102f40012000c015800a0070009800f000025fc4c38fdd022136fe987cece8659087a54bc43990e710d801d42540518003e00b00002c9159a2b24c32cacd34dfc987c98512fe26044c309801308261c4c40fdb8ba500ea12a028c026005f00530015000500b8014c032008c0090007403500420206016c06000a6009a007c00000010056002801c002600580000ece843d2a5e21ccfdd06594c3e4c2897f130226184c00984130e523621ac18d81c1024e04bc13a81d2033804ec17e813a17480c5827282e7041208d8048005f01060bd836a800054b6aad48792a5721e8a9de0c5aa55087aa9d4ece821f080412a4255000021d4aad410f90f254ae43d153ba83f087a76760c590e41748049c18d8275035606780c3013c01ea04c00ce00f805d001fc0a080bf07c8172007c812b0000aad553baa5721e843c821eaa753b3a087db8186d502340d102ab010f03d419e83ba83ab05cc022416181270116088813a80e703f0067004c03c2000043d087210f254eaaad421eaa773b3a087db7f85c8011808700b9808902c2017c03f8111011c050c05b811502ca00181f3000d17460198029805c000a00bc1cc80a303c42e885d0801604d40164076806800e003dc05a80ab048c03c806b00d501a8034c06900d1035a0158044005100f6021002b806f00f200c400d800000100004015800a001600e00130028003200100070018000076684399fba36fc2eb00ea01d200fe085008a80061740006c002001800004c3cfdd10e454b643d0a8e15262a505478a9215222a40ecdd53aaab52a54a9dd52baa553b3a6df810f8ba30da610fc0f1001f003c00009879fba21c8a96c87a021f36fc5470a9315282a3c5490a911520766ea95553aaab52a54a9dcece843d1740017003e8005173e21a8010851a002c09a8123000000020064010000021e8987cfdd1b7e3b3a9bfc439930e17440bc00590b9e071c0ab0117023f04ba06541758b9d10be2e705cd8b9a059607205cc80bc01620150000261f4dfe000c28d005f012013c800680ca0b5019501f382f804c000a806380060296037800a804c009a006c000000b004c00a000c80270008003800c00004dfe7ee832c887321e84c38dbf152f3b3ab548435086805620a9812901a704382e601f4042e06bc0fa81b2003400280248032816101120b0c13a80a40250022c111019c0cd4076820e02e2060c03400d880e703f007dc5cb809c01b2046005c005e001a0230369806400cc014c02e0005005409802b800060296037800b026a00b203b403400f7016a02ac12300f201ac035406a00d301a4034402b008800a201ec042005700de013400d801f0000008c0010008000200ac005000b007000980140019004e001000f000e000043d130fa6ff3f744c3800288733b3a6df8a950b9f01d6152c26f8626060e089820d83a807520b9828c886910d012241d9035d045402ec00c0000260c4bf8981195a26004c1098713100cb232c8fdb800510e654bc21e9d9d50b63b2142c822151326dc0dbe1b7e50742e6013c013508d80b1010480bb00300000110a83f36f86dd8dbf0ecd10d20468040810c09bc151c13a0278026a064c13b806b003602ec04d80180000a0fcdbe1b7636fc088542d8eca1d9c3b2076605190234020408604e40516093c36a0208033a05100610074015800685cb0b950520112c12901a700d6005c02a801b0000000c004009b0030000098312fe260465689801304261c4c4032c8cb23f6e0014439952f087a767542c9b7e36e06df0dbb022150b63b38764283e10d0137c075822605880eac2e382df022e02ec00c000050bc3b2942d8ece1d90088542c9b7236e06df0dbb1b7e36e81b5013402cc03e408bc15c8047045a0e241c4018003ac0cdc03a836d025a00f0028001f0058000098312fe26044c309801304261c4c4032cac7719647edc002995a592c2e5813402cc03e40ae411683890710075819b836d007800680560074018405102e386d10aa0164836784fe08ba117029b82bd045e0ddc023853504a0005c02a80000482000c004000036ec6df0db91b7036fc3b2942d8ece1d900884ece843d2a5e21cc32c9fb719640014cad130d172a0468086008105120dc007582df0410045c0ce827700d6006c05d809b00300000dba1b7636f86dc8db81b7e1d943b307670ec80442a16d42f05c7033e07ec137810007960868175886707100cdc1b6803c003402b01588290054c01d012901a701501b080928b94172605d41b700980138036408c00b800bc003404606d300c80198029805c000a00a81300570000c052c06f006b002c09a802c80ed00d003dc05a80ab048c03c806b00d501a8034c06900d100ac0220028807b,
  0x10cae21d4a97843b3b347658ece10ea21c8766036d814c017c0870051811b176402b400000054c3e4c3d44da83f0442a0ecdbf06575aa47ee5649887201e606f0226015a00007640eca1d8a3b2c7660ec61d9c3b350f1c108827f02d4065412c83180236036c05680820036006002a00000cae4c3cfdc80055136a0fd41d822136fc9bf930fac931764035c244006c03de0054125021204460b780e38214030005480bf812c0290095c2130072021a005c0198059176212b000301ce006a00140088007043e0134018801f00000020000800f0032001000f00003b34767032b9fba261c147021300c7041800540f781c7029e04a80a9817700cc02dc0298035000a00440060031003e0000000801900080078000087508764c40987152f3b34195cece2a5b17621b6803980fa02be06ec01981ec050a0d7c1f9066c0a362ec036c82cd0880031018e8006039c00d4020003f008200f801e80450088004000980120018001c10f80790062007c0000023000400240018008000200a40078004003c000032b9fba3b347670a9704ac0db4064407d015f00662ebc36c844001880c7400301ce006a004000980120018001c10f804d00f200c400f800000460008004800300100004005000b0052003c0160004003c0000fdd06572a5c7668ece130e176004042c7848100f006b0177838a0418064443881ef0db405a007c80c8029e04a80a9817702a404b01840066013e02dc039010d03d8005c36c81720880031018e8006039c00d400a00250034001400e00100048004c011001200220030003821f009a01e4018801f0000008c001000900060020000800a001600e00140029001e00b000c80a1000800780001d9a3b387ee898706572a5d1f8c5d7807302be06ec01981ec050a0d7c1f9066c0a362eb8082800d10e00b3422000c4063a00180e70035008000fc020803e007a01140220010002600480060007043e01e4018801b003e000001180020012000c00400010052003c002001e001c006000006573f747670ecd152e36fc1b6404101b3003a1288017018002a405fc0830072021a0e6800b8691004200cc09b80e5013a03ec04f015f00fa11d80068870063a00180e70035000a0040009801200220030003821f009a01e4018801b003e000001180020012000c00400010014003c00c8004001c006001000002a5c6df8ece1d9a3f74195c9870bae03c409f800006573b387ee8fdc031d02be03e80198017011a02f412281640192110000800130024003000d800000460008004800300100004014800f000010ec87a1d9c3f74087cdbf065710ea54b930f9fb910e015f41580252034e1b5c0068402087e00185d681e20db004745d6001604d40164034007001ee02d40558246002e06b402a805600a201ec042005700de01e4018801f00000020005000b0070009801400190008007800700003b347ee8439821f00a601700b98005011800bc02f011101460288364800d00420184082008900be217804700b702ca1b6000b026a00b203b403400f7016a091802b008800a2021002b800000100004015800a0070009800c800e00400000fdd10f44c3e6dfcece887308762eb40238180045e2170082002101ca2eac25405180b881b5806382f8000a1b5c02e005f00a6020c03304d3025621bc0068402000c052c06f011d002c09a802c806800e003dc05a80ab048c005c024001d002a01a8021003a00aa0158081805b00a2013003d80c00108029802b80a700de013400f800000100004015800a001600e001300280032009c002001e001c008000010f43f746dfcece88734c3e4c3836c00650124029400a00f4006803301b20132000000080001b7f3f6e088432c9d9d087a21cca97a62b175621b05d502430b8a1b5817c06d710da003420100060296037808e801604d40164034007001ee02d4055824600900074035004200ac040c02d805100f6030004200a600ae01bc0268000001000ac005000b007000980140019004e0010007000021e821cc9871fba36fe987cece90e410de01700028053005401900a6008c046021b821603e500000024001800100006dfe0c58221507e767421e86592a5e21ccfdc86d70124019400a00a5006803d00db000000040000fdc9d9d0cb210f4a978873508e21b803280a5012403d000a00cc006804c81b200e50dac00840fa8ba910da003420100060296037808e801604d40164034007001ee02d40558246003a015802d805100f6021002b806f009a000000100080014002c01c0026005000640138004001c0080000130e261843d08721fba21cc987cdbf9d9d10e67edc5d5005300b80190002808c0054017813000a2000000040001b7f3f6e088432c9d9d087a21cca97a6ff0dac2ea028303b9086a2e9c156827f0fd6075402a00004c3a98fc657261f32b06578002a6fd4dfc12d01c308640b82012c3690058062e0c7010f00e7030e04501cb808b05a8022406f004d003e009c00f0000044210f553b9b7f0cb2b24cfdb9d9d261843d08721fba21cc4c3942d0ba909f609400c00152008e08bc17c0ba60068005004900650112029004581da08380b8806800e700b021b00ae016802e804f807c80c80560020c0d3805f001a1008003014b01bc047400b026a00b201a003800f7016a02ac123001700aa0158028807b,
  0x108980d5020a808e007401a0088002e036800741d8885b01940dfc04802551792121803800c405222f2019d038e06200bc016500b204ca036c156023d04f4097017602ee045c08fc12e819507340b2c0e400b90042069810d03f201ca04dc41500ef0316041c051851b178e003412a06de009e01f8028002f002c1b7400301ce006a0050012801a000a007001200220022001c10f80790062006c05e001f00000008004800300020028007801902b4001000f000e003002c402a002000007ee8ece1d9a36fc2f281f0041604a605f8127827405e40a780b181b402360440025803a003a01e001700ab00d0083004701ef0422053c095015302ee05c00bb00b7025601641848033002e011c05e800d04a800d400a00250034001400e002400440044018801b0000008c001000900060020000800a0050006400f00bb001c0060000391e2a547668ece043b2a5e21d5c9d065972307ee4dbf283e179203ac5e30bc510e620f441e083b03d00cb807981ff03b8079c0d78120035c06fc0f301be073a045403580310036056800f00bb00300150000043b1d8c7668ece021f195a656cdbf2a57179000cc0af801704b60c2027e00900182064c06d02c6075e07180ae01160662003412a006b0d281a4c34901b601b81b78348068f0d1c00d001780160dba00180e70035057a0c2c1850014004a0068002835c06b60d6800e00100048004c011001200220030003821f009a01e4018801b003e0000011824104be09f0001000900060020000800f0058006405080040136003800c00003f747670dbf1d9a261c2f1c2cb80ed00d0016403e002e0066012000e801701d80208039015d01b602e40f1839a0208008407286dc095a00345e20bc30a3812b018e8006039c00d400a000500380044003821f00f200000010008000200ac005000f0008003801000003f747668ece06570dba06d806601a3026403bc000130f36fe195d63f02213f7298ac36e02f001640ad4282033b047a09e8176022e047e09740ca82eb06d2090016581c8017802c402a00004c3e99fc00181e30298017805f00a2014600009879b7f0caeb5481109fb94dfe12b41a5005801e6078418e021e01ce061c10c03a2050606f01ce044c06a80304059808e00e201a000a802e038e00740ff816b015a0c5817380ca046c046c0480061178400d4018801b000000280ad0027003c0000dbf88752a5e195c21d9fb93b38766810f8bc4025e059c0da0081024c04c02e4803a01f003cc03c00c107b40d44160832a050e108c05580710282083000a81ef038e053c095015302ee05c00bb00f900cc02dc184805902be00cc00b808d017a014c01a80100026004800600790062006c0000023000400240018008000200a00ad0004003c026c00c0000087654bc43a9d9a3b386dfc32b9fb9043ea0f85e1019f03f609bc06c8118040401780a602a608960a4005f01a704a4028c36d823300420a0418d021b001a052807881d402ba01a802101b401b603b0080808a024c020802400f7016a00e800e807c035805bc03c002e018203b41a882c106540a1c1c502e8015601a0038814302820830047001504ce07bc10881c701f2053c095015302ee05c00bb0066013e02dc02c8033002e2f04035851c00a612b018e8006039c00d400280110018001c10f80790062006c0000008000200ac0050038004c00a00078004003c02ec007001800400000fdd1d9a3b38195cdbf0bc305980e3812e02ec03e40aac3fb0bc0177e05b01758278043405d40ff83ce080210a85df0382051c06d00da83ac04000588093013500d4010801d000d0202022803c009001ee02d405581f4035805bc09c81dc032807b40ff03ee05fa04e85de8021020802e405e8072011a01ac28e04ac063a00180e70035000e087c03c80310036000001c00260050003c00200bb001c006002a002000007ee8ecd06573b386df963b8bc1059805640f90bbc17762ee85dc8bb8176e0aa80b6021a03fe09e019a83b206ba08a80da83ac03b801ac00d80bb0030056002a00000443063c87a10e53b386df9311800550742ef806d01c6001a016036d82dc039e07900a701aa03de04e4125021204460b78055841500f000e85db00c100e200540e38021020802e405e8072011a1470256031d000c073801a8007043e01e4018801b000000a000780270008007800700180040000163b9fba0cae7668ece1b7e21c82ef402c0747060406c4233032c04e40648076807c009004d011e0872003a00b80340bb503542ed000681d4036804980608071002a071c0108104017202f4039008d0a3812b018e8006039c00d40028011000e087c03c803100360000000802b0014003c0138004003c003800c00200000b1dcfdd1d9a3b386df832b90e458e22ed836d80e7050602cc0470000000a4c3cfdca83f04426df832b88752a5e10ececd10e43b38766153b8bb50a2e012000e806a008401f00170101011403b403400f7016a050c047037c06a618501d106880c780000015800a00700098000043b2a5e21d563bac7358e26df832b9fba3b322ed002c034a030e086008a0211073802cc0470068005c0074439023c0268012003e00ed02862ecc1338238035407840608071002a071c01a8005002201e40188000000200ac0050027003c0000002930f3f72a0fc1109b7e,
  0x100c206d819901eb029800d0027003c0054006c00700180000a0fd311261f3f72b54963f0659592cb35942d85cd00e602140a3002e003a012c08d8040007e010401f003d008a01100080013002400300000023000400240018001001400a40001fb97274196443a952a2a5ca16843a801701f4011c1cc00bd0172000001180020012000c00400010052003c0001fb94c444c3c43a86592a5ca0f85ec01f5072815c4003010d004207f400b80e5092000cc3e8009e02be01f45eb8279072c173000b04ae01bc0b582018014004a0068002801c002000900098022002400440060007043e013403c803100360000001000900060020000800f00320010007002000007668fdd130e17c2122832a82e20130021c038050e02a404b00a4025700e404345eb0256045404745ea800d00c20e5000306e1072c173000b04ae01bc0b582018014004a0068002801c004800880088007043e013403c8031003e000000100090006000400780190008007800700003b344c38fdd152a17ae0768215836705240e182148082077a007443a002e00d002cc0c1815c02d005d009f00f90190027c03300590ada1b88019847e002e0e5012a839600a6037816b0014004a0068002801c00480088008800c009a007c00000020012000c00400010014001000f00003b3a195c43a952f08764c3887a1fba58ec2f5804c008705c401c033c850e030005fc0a4025700e404345ea025601820ef427e010504b600340308394000c1b841cb05cc002c12b806f02d608060050012801a000a007000800240026008800900110018001c10f804d00f200c400d801f0000008c001000900060004007801900080078007001800007668a95130e3f746df85ea867905240e182148082003a00b803400b3030605700b40174027c03e4064009f00cc0164371003308fc005c1de8105001a01841ca00060dc209541cb00530b98005825700de05ac100c00a00250034001400e00100048004c011001200220030003821f009a00c400d80000004002400180080002002800780190008003800c00003b3454a8fdd1b7e261cb1d85ea005801ce0860013800021d843d087710e821e0438887210f26e3e060c0170068003a022c0568089023601840068230023a096c2e5811410202f4c02c08110b4a06a40fd00d002dc03d007501250288031404600660210059805200a501500308036806403fa09e412a839600ca025803a00530020004c009000c00f200c400d8000004600080048003000200280138004001c0000879152a26204c38ecd1fb93b3a195ca978875087a1b8409b81a60d300db41300364045e00022e3c5ce8d45179a313261f3f6e172c041001d036600b82510106030005fc0a4039a00e4043401083bd002e03942578033013c057c03e8bd20b94005825700de05ac100c00a00250034001400e00100048004c011001200220030003821f009a01e400000020012000c00400010014003c00c802000007668fdd130e2a5c17301dd802d00fe04d840c8bd1000c2f405e78619032209e42e5024c03d208900b900c4002c12b806f02d608060050020003f004a010400d003e007a0014022804400380040012001300440048008800c000e087c02680790062007c0000023000400240018008000200ac005000b0052003c0160019004e001000f0000261c7668a971fba2a542f4806084fc0d2c096c03c801b0046003800010f22a544c409871d9a0876875ca969d9d10ea7ee4dbf0bd100ea09c4232018002a405fc09600ec00e404340240017179c2f342dd883403fa0378026801f000000b000c80008757101c87a1fb93b3a7ee90ebad520cae4c3821e8bd002be03e80198017011a02f40080013002400300000023000400240018008000200a400780003f72195c43a952e4c3ea0f82e5011b0096018400e800d005c08c003406571798047412d86e0013e02cc04380060f9a032008a00b60b7605700a38116036c0cc80f5814c01b800d0027003c005400bc06f02d608060050012801a000a007001200220022001c10f804d00f200c400d801f0000008c001000900060004005000f00580284002001e001c0000ecd1fba261c1964257037f0dbe09540f606490188013400f80000046028400f00003f744c30987152a54b47ee432c952e179807b0062003300e0057c243001000260048006001f00040024001800800020078000261f54ac21d4fdd2a5a2a561b8012180dc0af800bc00b043803c400640002c965aa4b1f966b1d9d3f747ee016b0211029e04a80a9817702ec023805b806800b200b8019801d01f4005c02583980afa046c05e81e104a40bcc118022a001a2f2c131015d0302036c0f1839a039400840d300e5026e03bc0c58107014608c82bd811d179406d819901eb0298037036f004f0068013803f003c00a000a801780160dba00180e700350028009400d0005003800900110011000e087c02680790062006c000002300040024001800800020028014800f00320010007002000007ee8ecd1d9c0806165c076806800b201f001700330090007407d001701fa012c1cc00470478046c05e81d102c6074c05c800000460008004800300100004015800a0052003c000418e835507a8fdc930f72741965cbd08754c4410ecece021f179603cc111834c07440a0c0de039c,
  0x101a403440a0005500ac022002d80510108015c037808600f20000011800200060020000802b0014002c01c0026005000a400c8004003c0080000285a2622a0f8a9708733b34767021e8be50506022c0e204240648060c0a080c817c606a801a8031003c000152d90e621d843c08721d8c3b307650ece1d9a087aa9dc874044d096008b41c4838803ac0cdc000262a4c46001532100ff0116084408a012a02a605dc11c03c301060bd824881aa006a00c400f000021d0a96c8721d9a3b307630ece043d54eedc085f183cb05400f3807c02350a3a003443d839708081b940d100b0022001240d200c3006e03f409d80bf018c088c108043b04220a0c04583da06a20b041950287084605380c18141027c03205f10098047003400b7037408220290052813f0086013c01a01aa018a07d8110806d00c801980190047015c00c005d002a005e001402e007d03180118010804b03c60418091818a02ae021400b00170090007400a80f20074035806a80d401a60348068814000aa040c044005b00a201300420057014e01bc01a808600f200c4000002300100004015800a001600e0013002800520064002001e001c006001000003b3410f4988a83e10e654b8ece285a58fc2f900cf820204ee0a4022581c005c0027006c811804a4069c06600b800bc00340ea001b0176003800c00005072a11941f0ed41da43b4141d8ece1d98a468dbf06e50116084408a012a02a6191c0418491047006a801a8031003c000087810e854b6764887510e43b207668ecc1d8c3b3810f553bb70217c409a016601f205720fa0217035e07d4000065a0cae4c460014cab262a0960046c2e6804b017a0074023802e002e01a001980b300b2036c0f0009f063c02e40cb81a6026e03bc0c5810701461b8c027807e00a000bc00b00060a1e10fc43d0be105ac100c00a00250034001400e002400440044003821f00f200c400f8000000400240018008000200280078019000800780001d9a3f74021807280210db812b40fa8be0001a018443c001610ee1b905ef82d60028009400d000500380090011001100000008004800300020064007002000007ee887a1d9d10ea4c3d30f90f210f40c1c3b2838204f0080014e806a022e04040a200f7060a06b0075044a030608780c38114016601a0017001d0104036c13f81b50146031406f8135017c05cc0b5015b065c03281a1014c0118096410e0bde17ba001843c800d00c221e000b08770dc8019404b007400a60014008001300240044006001b0000000800480030002002801c0019000802ec007001800a8000130f930f21e843c8a979d9d10ea7ee4dbf0be000f803b402401430268058411e000000560000fdc9d9d0cae10eca97887551342f78059022e047e09745ee0bdb076a0c605ed03b400420bb41cd00bc0162008000026224c7e987d37f031e04e60f801d401c102ea1464213809c01b2046005c005e00d60034030801b0176003800c0000507e3b38766285b50766dd0dbb1b7e5234101c00a81b700e201fc060800000040004005800f004e00100001fb93b3a195c87a152f21e4a0e85ee82f303f403d00a2008c027a059805280c200c8006c00c000054f4a98959b2aba3b3aa16c110a61f087a21e408a008b077801a00d480d001d40494062802e02100290054006d003a001805683940112046c032809600e8014c00800130024003000000020012000c000800a00080000fdc9d9d0cae21d4a9790f421e4a16843c0183022806a40b700ea018a01980458108014802a003681fd000c0238034002e003a012c06d808902360e682e68021034c039409b80ef0316041c051804f00fc014001782790dc8019404b007400a60050012801a000a007000800240026008800900110018000000100090006000400500040040000130f9fb93b3a4c3c43a952f21e843c832c88770172011c0d30017026e00cc077818b020e028c02c804f00fc014001780f6002c017c05e839600ca025803a00530028009400d000500380040012001300440048008800c0000000800480030010000400c802700080000fdc9d9d21e443d0a9788754c3e4c3d41f06e400e4005c05c80330396057c5ec80160dc60b5800a00250034001400e00100048004c01100120022003000000020012000c004000100320000fdd10f421e4767530f8875261e54b85ef82d303f403d00a2008c027a059805280c200c808f0003013404b001fc0f6004806a40eec148803300f800b801681bb02a80518074807306e4003403088760b9409300f4822402e4031016b0014008000fc0128041003400f801e8005008a011000e00100048004c01100120022003000d801f0000008c001000900060020000802b0014002c01480270008007800700180000987c43a952e3f7443d087906573b3a54a85ec82f3020a04a407100cd012e006c00c0000782ced69da13b9a50b6088530f952d06e401cc0428146005c0074056811b008000fc020803e007a011402200100026004800600000046000800480030002002801480003f72195c43a952a2a5ca16843b06bb009621d408d85cd17b0036c1cd0021034c039409b80ef0316041c051804f00fc01400178014004a0068002801c0048008800880000004002400180010040000130f9fb92a5c21d498786590dc60950006867d,
  0x10014002c01c00260032001005d801800400000ecd1d9c5234a0e942d9b7e2a5621cc988822117e222000ff01e710fe00dc02480b0002c00540a0004c010c00c4000000b0032007800c000004427668ece291a507454acdbf285b262221cc8728bf0013c024807f8014013a00d0056004300340f3c028000602f00e740ce8194040e00c0015000500b801f40c600210208033c00b014000ac0220028808400ae021803c8031000000080018008000200ac0050038004c006400200180040000011093113b34a95cece08732a563b2c43f809d01fe02b004f001a0124014000a017800682fbc02181f6079e0190003028500cc00c802380ae0a320ec804e00d9045402e002f044f006e012405800300054001402e007d0318008408200cf002c005c024001500d4010801d014000aa0158081808800a201300600084014c015c053808600f20000001000300100004015800a001600e0013002800320010010000004427668ec61d9c5234a0e87661b7e50b64c44439952b1d942200006810f06ba05f0244800e0000a0e942d8ecf089e04680860081049e0dc02e3827705be082022583b20138036408c0117033a069c11500b800bc003443f006b0036026c007001800007669648acd158e24c4432cacd354ae439152d9d8c3b30767148d283a507ca178dbf0ecc1d94a16c7670bef042004800f301be06e803b8052822100c800d401880270008000021eaa57566c7670ecd2a62079e0710212032408762fb8063063a089c03f41f083ed09ee0690061814d01c60744088017b02160b840d1030d051e03ac09781ea024e07a00b383440636020425902440234094c144817e049e09d0179010f02c606a8003028500d600d4043003100360064002001e0176026c00c000050b63b387660eca36fcb245668ac7126221965669aa5721c8a96cec61d983b38766810f887e01d6186c31900bb00300000dbd1b7236ec6df0dba1b6e36fc3b44259008108d203d41048236079c173c07c00900a3a00345f6839708080b5c09f804f0028024804f00ff01602fb004e80490a1602b001b859d0034068805f83c1007804400900beb00b4030c07980a80b0e14781f6834a0bfe159c27780ea10cc026011c018301ce061c08a0bea0354031406f81f6044201b4032000610f81b9801800ba005400bc002805c00fa063001081e3020c033c0c5015702bc02142588016002a0d54079003a01ac035406a00d301a403440a000560110016c028804c0932021002b80a700de00d404300790062006c00000230004000c00400010056002800581cd00700098014002900320568002001e0136003800c002000007ee0ecd08732a5c767142d045007c009cc1d401c110fa05d40b881b003800b80255809c01b204600a880cc080202e002f000d03a8006c05d800e0030000142d28461da4a0ed48d0ed450726df816b819f04ee080800d80bb003000007690ed01d9ca0ed48d0ed41d983b20db91b7c36e06dd8dba1b7e1d9421f404801f4001a21ec2020be9061a06880bd8110029a030c111013b07b40ca8143838a029c0ef05f400b00092034001b80a401dc04fc021804f00680050049009e01fe0274056001a0078016806102bb0994088c1080211050606f01ce044c06a8022c37381aa018a07d8110806d00c8001843e06e6006002e8015002f000a017003e818c008c008402581e3019e048c0c50157010a005800e801500d403c801d00d601aa035006980d201a2050002b008800b6014402600c00108015c053806f006a021803c80310000008c001000300100004015800a001600e00130028005200640138004003c003800c002000007668988a85a10e654b8ece371e17d42f9c07588650b6e16b02db05120c6205d40e002e00736027006c811801980b5005c005e001a07501ed032a050e006c05d800e0030000148d285a508ca0e544ca83f5076767087a1d9521ce6df85f481c0033e154c06601fb044a0034101027701b42f983df816b076011e823c82c6075e0e300e3001b0176003800c00003b3843d0ecaa83b5234a11941f90e317d00a28150032b010218c004e0118080802e002f028f02c807ec112826f001a042c101009001c60c3405801a403e805bc0bd804901fa07c00ee0194055c07b40ff02fd029a00dc063018306f804540a1834a0994084013382110b9c0c7010f018702280e8814181bc073811301aa00b3011c1b9805d002f000a017003e818c008c008402581e3024606280ab8085002c012000e801500d4010807900d601aa035006980d201a20500081808800b6014402600c00108029802b806f006a021803c8031003600000118001005600280058038004c00a00148019003c02ec04d800e003000800001d9a3b384c4542d08732a5c10ec43e01830aee079c18e021e030e045000f000021e8dc7c8791d8d0b9c050407381870430027c059800617ca00c802380ae008c012c0918016002e00740a0005500b600d404300310000002000500190008000142d13113b3854b84399d9a507c1b981088283011610882308187089a03a809282bb0150030802d003c003402b004e80ff013c024800a0be4018a07d8110806d00c801980190047015c00c0015000500b801f40c600460042012c0f180cf024606280ab8085002c005c00e80f201ac035406a00d3,
  0x11da8a9dc21e9b7f3b347650ecc1d9c3b18438c5fc8120087602fc1d6811903c8113401900c6008e03f40a4027017ee011802582d8010c00009802c9359a24c20987130c26044c41638ac9159a6196563b9d9421cc43b08781d8c3b30a95c21e90e43b3876689830886089a0f8401900e30186011c085811003000d580fc85ab008c012c16c0086003e00b000c801e00004c01649acd159a64c20987130c26044c189882c715922196563b9d9421cc43b087810e43b187660ece1d9a087a4bf85fb8367028e0000986130826004c0898713062620e4ec16c045a01e60670211042100b02214075012505760d2405400c200b400f000d00ac01c4045c0e600ff02640330066809200280118071804f0096042c0920112052e01d411c010e01b0047c06b80a90fd00f9002482ea09fe00dc0d500060dd80058024001d002a01080a0010300b601300530035010c00c400f80000004000c015800a00160098016001902b4009c002001e00004c00986130e2620001531182212a5a21cc76a1b7f21e04390ecc1d8c3b38766952b0bf804221ef83e0008b02d60450018801b0030000076a2a77087a6dfcecd1d8a3b307650ec61d9c21c62214413810e01b0035c0548049006e0e74043000021c8b1cc986130e26004c416489d8c0cb2b34d6499d9a3b3810ec376005c090801f41318157004600040058026005000a4000152e26207ee0ece26ff523621cca96088700ea04b014d010e0152011c0248032006e027c1ce80060dd604b41100050003402b00710141033a0b0422885d103b80820040816b0488046844200ef024808d0027801401240334066017d093c04c803980e50318005800b8048003a0054074806a008403c801d00d601aa035006980d201a2050002a81030110016c028804c00f609a40600084014c015c053806f006a021803c80310036007c00000230004000c004002b0014002c0e68038004c00a0014802c0032001004d8018000054b942d800536fe3b507650ece1d983b2011088733b38766898826fe0ddc16ac12801800258052002380320786021800010e221cc43a087510e426104c08ecd130e260cb24d638ac9159a2b34c9882c770cb2767021e86eb05400a28040826211060a4c234028010480ee425a0261045817481b30435067609f4375027f032a0c600c0810c0956086415681d50036026c02a000050b6987d37f2919000a6dfc76a0eca1d9c3b3076402215136d408442015e02040cf400c00008fc6ecec98810f43f70767141f06ed005e02e8002827600b8028803e818c0042041004e0263019e0ae81b2817c0340040819e833401f0043c030805500ac0220028808400ae00000118008000200ac005000b0070009801400290040000142da83b2a5c7ee0ece261f36fe21cc32c821f096e00181e18285058211442e881dc006402040b58047006e0cd41b282440364068008d00ae00921740087806101600034131822a089e03842428015010c00c400d80000008026c007001800011f7dd9b9fb850b7062c32cac773b34767141d04b60cca03840af048401742fd8017800500b801f40c600210208033c0a28450002c050002b008800a201ec042005700de021803c8031003600000118008000200ac005000b007000980140019001c006001000002a5c76684399fb83b386df825a817e033e07ec08601000750068007a8882096605785fa81750138036408c00b800bc00341028bf40dd001f40c600210208033c03580160280015402b008800a2030004200a600ae029c04300790062006c004002b001400e00130028003202ec007001800400000ecd1fb83b3854ac439a85b36fca4685fb017e033e0430080028b058806c809e000d040a02ec00700180000a0ed42d9b7236f86dc0dbf0ecd0966027407f80ac013c00680490050002805e00278117027e0b7c0a8856802e21ba436706cd0d98171810e051f04ee05d404e00d9023002e002f000d040a033c03580560036000000100030010003800c00005076a46942d8eca36fc4c4432c8873000a54ac76608820234020408604e302fc1464035801b013600600001b7c507e6df8110a85b1d983b487650ec81d9c1ba40cf81fb02000ae815882a604a4069c0ba806b003602ec00c00001d943b20110a83b36f86db8db81b7e507c147c1e5813000003b2876a0ece1d90d38c15d0552067a2fcc5f9088102ea0034102806b0036003800c00008fbb1ff641ec7e336e06df141d8ec836fca16d0ea8bf5033e07a0129817e049e09d017900c901b4058c00d80bb0030000142da83b36fc087c102887e03ec08840320006050a0198019004703640680057010f00c200345f8844f006e0124058015e090a1ba0018002a000a017003e818c004204100678016002e012000a806a008400e80a0005500ac040c04400510098030004200a600ae029c0430079006200000040001005600280058038004c00a000c8004001c006001000003f70a468a95887350b67668dbf1d9c50742fd0028001a02f002b008b809d05be03fc075809e051202480860014051611b016201b2006822000218221079e0190003039d17e021fc1d900d9023008a802f0037009202c0018002a000a017003e818c004204100678016002a050002b008800a201300420057010c01e4000000200060020000802b,
  0x10278300c32303351120059c4478c020bae008425c000d096e078425b011d096a114000b001702800154026007b010c01e40000008001600640070020000054b8fdc1d9a10e67670988130e21c8301401b8049110c222041400f00d5a00bc6008841082006a415d834901d4049400284d20a70059808400c20150017035c0375010001680968220012e21001bb004e0078014002f034b004a006805103d7042a02b0119848e0252038813101810886110828a0288033a0a280860307044c0b1836806a2040e15000d003a905cc00182ea817d03f8048400b00170090007400a806a008400e80a000550206022002d804c018002100530057014e021803c803100000bd0004800300100004015800a001600e001300280032001000c000050b60014dbf82212a5a21cc98713103b184390ecd1d9c1d9630082e9803001e000a801780c7000a017004b81ca017004d404e01f4111e175c37680210970003425b81e1096c047425a8450002c005c00a814000aa0158026007b010c01e40188000001000040058019001c0080000152e3f703b387660ed410e64390ece1310261c76687650c040668033c0fa810400ac008c004000b004c00a0014800036fe987d42d88732a5c000c25c055c111c18e431f055b04700b643348586111630005ff8bfe111a175c01081f50dda003425b81e1096c047425a8450002c005c0a0005500ac013003d8035010c01e401880000010002c00c801e001c006001000001d9421cc764152e3f707670ecd1310111e0604446010c0a8206c83b383ab0000a16ca97130f4c3e21cc00282210cb26dfc7668c0003022230086037a02f81074180000050b654b8987a61f10e60014110865936fe3b3c5ff888b03e007b40ff00310030000076508731d9054b8fdc1d9c3b344c40872888d03882228444842406480f0c14385d602d600c80fa0209046c011c09a815203942ff42e982d9035403140fb006d00c800c0078002a005e031c002805c012e01780510bfc000c175401081f5002c005c024001d002a010801d014000aa040c02d804c014c029c04300790062006c0000008000200ac005000b004c00a000c8004003c006001000002a5ca16c764152d10e64c409870221507e3b28dbf9d8c3b3876688720bfe00b0161c1ed05860cd00e3001a802700300000ece10f421dc43c08720ed505b2035c02486eb006e03401e780a40248010c0278034002802480668151050e17580b8816b03e8082411b01350394174c00305d5002c005c024001d002a01a8021003a02800154081805b0098030005300a7010c00c400d800000040020015800a001600e001300280032001000c0000000a4c009861d8c36fea0fc76502212a5a21cd59b130821c876689871d9c26203b505fe86ee06540a1c3758bfb049602e004b805c000a00bc07808880534036006b8049006e02fc377809801a005b81ba00a4014a0490021804f0068005004900cd019804c807280060baa005800b8048003a005403500420074050002a810300b6013006000a6014e00d40430079006200000010008000200ac005000b007000980140019000800600001d8c2a5a4390987152e50b60014dbf8eca26203b2011088733b38766937f0bfc0ddc0ec01d7803100300000a97285b000a6dfc76a0eca26209bf8764022110e67670ecd10e317f6084009001e6037c0000ec91d8c3b38766a1d386ef0b560438054808600004c08980130826184c18ecd130e087ab24d638ac9159a2b34c9882c770cb27671c8d888800bc221c051018c02ae0220028808400ae008c015800a001600e0013002800520000002a61f36fe54b89881fb83b3821cc110952c0bae01700028097005e017805180a204660988221844205140c1c113017d03f8048403985d401d203c806b00d501a8034c06900d1011001ec042005700de000001180010056002c01c0026005000a4000152e6a00d501aa1261f4c7e0014dbf82210cb221cc987888c0732063004400510108015c015800a0070009800000054c3e4c3c32c88732a5617501b500320186038c0238110021604b022f02970dd80a6808700d8023e035c0548049006e0e7401a8086006200640001d9c58e64390ec62cd3592676689882c9158e2196563b843b261c17543b780c301c605480a4013902de011c003003200da019806f82fd0274174c01800a301e000a801780c7000a017004b888700bc028837701ca026a07d001081f50dda003425b81e1096c047425a8450002c005c00a814000aa0158026007b010c01e4018801f00000020000800b004c00a001600190008003801000001d943b30764152e3f70767076a1d9a262021cc767088b074e1acc0ce03ad084207905fd0bf9008c038c025810b022406f444300ea024a0aec1a480a80184016809682200078014000d00ac01c4045c0e600ff026403300668092002800d002183cf17f003140fb006d00c800183760016002e012000e801500d4010801d014000aa040c02d804c018002980538086000000080018008005600280058038004c00a000c80040000acd8002a623044254b44399300261c4c309880ed43b187668dbf9d9c21c8174c3568412089a06a801a8031004e00780002a7754eaa95c87110e621e07650ec710ec3b1810f48721d983b3476708740bfa110a0f5400f0000,
  0x1001c006001000003f7054b832b9d9a3b3854b060d02d318240cf42c0057f0908160424280008fbf1faa45f480290851f8e41f9b7f43aa305044b009c014402e002f00ba017c00c044a8021001a07d403081e10348048c18603f6032200c80630046011a04d007600ad0104005c024001d006601f001701bb02a8051803986f304cc0050020003f008200f801e8005008a011000e001000260048008800c000e0c7c0430079003e000001180020012000c0040001005600280058029001e00b0007002000007ee0a97152c0cae7668ece130e18261cf82268128039e07900a701b1075a1ff00fb00c500cc019003680060462021800200002a5854a832baab754b67630ece1d9a54eeacd844a88841822046860801ff03e007700ca01ed03fc1ad406800a40086068c09f80cc026403940030231010c01e4018801b00080060000131158fc54b141d86573b34767142da89b000a6dfc76402214dfc225813982ff02ce193c12c8799006403180d200460246023409a00ec015a020801b801700900074038803300f800b800a81bb02a8051824900730160041428d800d054e1e4018604280672303c1330014008000fc0128041003400f801e8005008a011000e00100048004c011001200220030003831f006a021803c801b0000008c001000900060020000802b001400a400780a1001c00600001fb82a5c195cece1d9a36fc1bcc13403c80a200db01e00338059402c844a015d01d8012019d021b00f8042416882d0059e0b30078817d007407c802101d100f0008404502e101c0041009082b901d604bc05c812702d407640cb01c902b607a00b380720636020425900170488068008d0253051205f8127827405e403e8227810f02c60184042802e003a303844902c5181a1bc8006844700d609981148217044e007000800240026008800900110018001c18f808600f2006c05e00000046090412f827c000400240018008000200ac0050026005000a400780bb0136003800c00b100a800800001fb83b347670a971b7e0cae4c406078504071c0bb014982ab05040bac000261f000a99fccac195e32c06550655889403780840090008b017e11840c38119089a0aec1a480ea024a0308054005a0476041c07f80ef0346010c0fb0221018a0f3c033006400da00c005f00a311260018142803201720234039001701f430300108160008c036c0568082006e01c400a802d01c2224813300140034001400e00220022021803c8000004600080048003001000040058029001e001000f0020000054b8dbf021f10ea54b498786573b3876696498c0e0102220c44884690b9e1278270835509c41bc425a026104581748338816a06cc09f4375027f032a086818c02ed00420580162806b0452085c113801000260048006001b0000090412f827c000400240018001039a026c007001800a800800001b7e4c3e98fc987865710ea54b410fa6fe112608841080120037c019005f8030013002f817b043a0a12028c1c901fd046610940ae814d0634038c10d83ed01d808000a5016201e2030c024006a0084049803e0101011400e80be81fc024201e0003023503d4049c070039d0a800ea417303b103fe08e40da82e7019408d80e9809000420580162806b000a08a410b82270020004c0090011001800d404300790062006c000024104be09f00010009000600040158038004c00a0002001e001c0060010000036fc087ca96887554ee98fc987865754ae7670ecd283f18180e6828d00004c3e98fc001816007200018063036a02680534071804804000588019007c00d40108061808d02fa0118080808a024c005c0e880ad03f8048401d00fa065600740f5012700f00914075802e03d00d0811400e002c80dec1ee01fb044a09bc04280da03a803241028266006a021803c80310036000001180020012000c00400010056002801c0026005000a40078004017600600001b7e2a5c087ca9688750cae7670ecd283b112412c4102802e090a0518249026300e600342238266008000fc020803e007a0114022001c002000900098022002400440060023000400240018001001400a400700002a5c4c40fdc06573b387eed30f887536fc54b0606802d002a0384252048d0322007c000002300040024001800800020028005802900580000a951b7e2a5c4c4010f865710ea4c38379005c000a025c017805e0146028807286f01816175c25c80210970003425b84b6023a12d42280016002e050002a804c00f6021803c8000001000040058019001c00800001d9a2a5c7ee0ece0873063e024800a00cd009e03300778132000000080001b7f261e088432c952d10e698ac3780005005e017005d009700bc02880728132019830280398c0901d203c806b00d501a8034c06900d100f6015c0378000004600040058026005000a4000152e4c3e0014dbf822110e6196498884b90028013c049013f019a000000100002a5a4c444398659508e302801780ba000a017802e00a200fa063004400510108015c00000010056002801c00260000001530f9b7f10e6088498886592a5630240798c08106c301c41d0c06093622340ca0329180a078425b011d096a114000b001702800154026007b010c01e401880000010002c00c815a003c0060000130e10e654b8fdc1d9c3b344c406058c04,
  0x1080a0af4185830a0028009400d000506b80d6c1ad001c002000900098022002400440060007063e00d404300790062006c05e00000046090412f827c00040024001800800020028013000f0032009c002001e001c00600588020000054b89871fb836fc7670ecd152c183c024005701f4008e06500f680320306027c1a501410422173818e021e01ce061c10c03a205060e701aa00b3011c0118198804b08e211cc239013f02460578258801d00d600d404300310000007800c00008ffe54b0fdc3926728ce619d031b7e3b3410ec8711d9c0cb2b1dc10fa85a183a070c2e58339003e00b000c80a10001189a2e746a28bcc987c9862c775aa4b3589872c7e592c7edc44d007302be06ec020003f008200f801e80450088008c01480007734ed69da13c164c3e54b0a973b3b06e60968223801c00200090009802200240044006001b000000080048003000200600001d9c3f706df832c88750442101825a03660de20ce825e00b209c40424117023f04ba065425d83b506aa00e818c02ed023c0ed027080780144127807002760b9e04bc04e089002ce0ae80be0181021e058c60e0032011a005c60d8021020806ac07a85d801f0003444c85d903c22260066812901c4025c60d011d0de60998008001300240030003831f010c01e405e0000000400240018001039a00a0007800e0162015001000003f7054b8ecd1d9c0cae1014079888a111230641eb042409ce0c901e180060dec0a1c2eb01ff07960f3828e8397008c036c0568082003a00b8042814d01c608000b1006a0084040404501fc024207a80938344063605ac0d5819e030c04f007a8130006a0218018801b0000002801c002602b4001000f0018000054b443a8657261e087da71aa5b36fe7630ece1d9a50b430700d5005801d407d806282f6015001900368392000c1bd802d0030047602f808380a301fe03940230132015a0f7800e82870bac05c40ff802e03e8032804283df0120018423f00fa0dbe0534071820002c401a80210101011407f009081ea024e00841a2031b02d612e808201ab033c061809e00f50260176007c000d1132176444c00cd0252038804b811d04cc00680028010002600880090011001800d404300790062006c00000230004002400180080002002801c00260052003c0138004003c003800c0020000054b8a96887536fe195cece1d9a8fc4306c0c1844a10601ac005981ac02de000153aaab554ee438887a10e821c843c821d86f6017201c81580017034e03e8118000000460008004800300100004014800f0001062d48d289e508ca178a95152e36fe195c98782211132018404280fa005c005c00e80720104052016c03c6049c0a3c17e0356037a0d3414e03a3029403c40350042020202280fe012103d4049c1a2031b035606780c3013c01ea04c007c000d0dea000001180020012000c0040001001400e00130029001e0038000261f36fea0ec32b88752a5454b8a96930e0bb20d9c08901b302a404b00a40082021a01c800e8017005c03e8186008504600dc8066812901c4025c08e80050020004c00900110018000001180020012000c0040001001400a400780190000987cdbf952d2a5454b843a8657261c088437a842507da01180a680e3018602b41000162024c00740350042007400b8080808a00f002140fe012101c0043c0f50127025e06500d003a905cc070460c0006050a00c80468017182e12e82ec04a4016000dc244833500d801c42e80015001a00b411500e1023a099801a808600f200c4000000a001600e00130028000800780070018000054b8dbf952d10ea195cecd1d9c507422601e182c108a217440ee008102d60d9412201b20234043c60b0006050a00c400d8004013600600001b7f4c464c3c32baa5710ea54b410f8ece1d90766952d9d9c1d9430601e186f4182a0d4404081ff02d618602a082a0046a05f403e0048112e12ac28e8397008c036c0568082003a00b80428006050a005000d00050038008800880860062006c000000200060004015800a0008026c00c000036fe988c987865754ae21d4a96821f1d943b387641d9a54b6767142d0c16024010ec05f83ad0232079022682bb01d4049406100a800b408ec08380ff01de068c02181f6044203141e7806600c801b401800be01460478063015d026803b0003028500420410043007900080080000263f5aa4b1f9311930f0caeb25953baa5754b67670ecd2cd3112e0ad41400261052608b02ba03ec067609f413f82ad032a075418c00540000987d31f80054cfe9bf808f06b305ec124421d0509072407f4003039d03fe0c58173823607be024023f00fa0dbe0218018801b0000008c0010009000600200008029001e0010000152a2a5c195dc8f821f1d90766952b9b7f3b391f8860b801701f401c80e980b90394000001180020012000c00400010052003c0001b7f261e087c32b952a2a5c98882ec009c112c02e005180ba017c00c0006889500c207840d2012301600c300af0c140042058006d8c1300640318023008d026803b00568082002e012000e806c006601f00170015037605500a3049200e61bcc1330014008000fc020803e007a0014022804400380040012001300440048008800c000e0c7c04300790062000001180020012000c004000100560028014800f,
  0x18b8c0f4018a831e026e036c077818b020e028c16c0124025a088006e00f000004c41cfd393e72fce49930fb93b048e099c0a1828306a8031804700fd008c069002582d303c2048c09f81c502f002e8058015e00920120258801d002a01f0017002d02a80518074803700e60e740e581ff03940c5817380ca046c074c04800611846003444e83730a400018085004301000168018004f0068013803f003c00a000a80178016080a0050020003f004a010400d003e007a0014022804400380040012001300440048008800c000e0c7c01a808600f200c400d8000004600080048003000200ac005000b0052003c00c8004003c003800c00002a5c7ee0ece1d9a2a583098010811e02c009880c081d102c6069009180fd0096012000e807c005c05500a300730b1e040403c006a007405ec08800a2061a068813b01ea025e02701a10167113c17240a680f30358030c063004606a20b04195028708460e281060143011c016016c81c404ce08440b40174027c03e40640037029e04a80a9817702e005d804f828501ec01980190047015c02e80af033d001a227400b803306e61480003010a0086020002d00300068013801e002a005e00582028014008000fc0128041003400f801e8005008a011000e00100048004c011001200220030003831f006a021803c80310000008c001000900060020000802b001400e00140029001e00640ad002700080078007001800400000fdc1d9a3b3854b0a97283e18460c7808301cb00fa04d8017002d003a00540258049024602c008780f802340ae80408040007e010401f003d008a011000800130024003000d8000004600080048003000200280058029013600007680ecc1da43b2876a0ece043e4c462e106598bc421d4a973b3a4c3e3b2044f0c220410092c04e019d017005e005d015e067a30840198373023a1480027807e00a000bc00b04050028009400d000500380040012001300440048008800c000e0c7c03c803100000008004800300100004007801900300000fdc152e2a587668ece0221113a08c009f81c502f002e80af089c003000023f548be90052108a9610f43f707671cfd393e72fce498dbfc18b0442a0fc61082300b0015fc242058100011faa45f480290846dfe0c5a83f0442875444e01a40514226c13101e300420a800728081026406c014f80a201980544144005e015c04fc0e280ba05620a400af0252067a00cc1b98520009e01f80178016080a00500128005003800400120013002400440060007063e01e4018801b0000000800480030010000400780190136006001000003f703b507680ec82a5c54b0ecd1d9c0442a0f861103e0082c094c0bf024f04e80bc814f016301c0021403c002e00740074088004b01860118106008e038808440a7812a02a605dc0b8017601ec01980190047002e00cc08106f711360ce818802ca0164099406d815d055808f413d025c05dc08b811f825d032a02e40b001e3059607200d3021a004204dc07280ef0316041c0518c20001a101803580060214010c040005a0060013c01a004e00fc00f0028002a005e00582028014004a0068002801c004800880088007063e00d404300790062006c05e000000040024001800800020028014000f0032009c002001e0176003800c00b100400000fdc152e3b387668dbf0520069403cc0c185ce063808780c383a2050606f01ce044c06a802cc0470046009600740ff802e05ce0328042809000c205ac003010a0086020002d00300068013801e002a0028009400d0005003800900110011006a0218018801b000000080048003000200280ad0004003c000010f952d10ea3b50763065972747670ecd283f0dee099c095017002ec050c07b00c6006403f40238048002e01f0019818a06e600180850043010001680180034009c00f00150014008000fc0128041003400f801e8005008a011000e00100048004c01100120022003001a808600f200c400000020012000c00400010056009c002001e000099f8a970875723c1965cbd1d9c3b3454b044d815905e021cc156023d04f4097017602ee016403ac165816a03b206580e4815b03d005901bd83dc03f60894137802101b4032409b80e501c203ec04e809e00fa1218153889a002e00cc60f8c1e001a1018003010a0086020002d003001b800d0027003c005400bc00b04050028009400d000500380040012001300440048008800c000e0c7c01a808600f200c400d80bc0000008c001000900060020000800f0032001000f00bb001c00600ac00b100a800800001fb82a5c7670ecd1b7e261c30801ce81ff006e0b9c065023609f80240326828c02be01ac020003f008200f801e8045008800d404300790062006c0118029001c00600003b9a76b4ed09e0b152e261c6df810f843b3b387669d9d8c1f05d001600e2016f02d005d009f00f9029e04a80a9817702e005d8071809f01ec01980858032051e011c41700ae0964057812201b20340094c144817e049e09d0179033d021e058c0308c1d008402280d40311067002c813282ac047a09e812e02ee045c08fc12e8195005c05ac16581c8020c0868010831e026e03940e580fb013a027803e82a71134005c0198373001a101803580060214010c040005a006003701bb83e307c4013c01a004e007800a80178016,
  0x12a58195c9881fbb261c30b0018006d017c04440518183023c022c0ae804601b603b005680820090007403e002e02a8051803980210396041005c8072002e00cc1b98040007e010401f003d000a0114022001000260048008800c0000008c001000900060020000802b001400a401000002a5854b843ac3c64c3e438887a10e821d843c087210ee0cae10f4fdd930f0df408700460161011201fc0b98143011c0454003006d022230ac00685db1854019801800be000a0170051807d023c008401900c6008c00dc082008d026802b40388340020c033c00b8048003a00540a2809300aa0158081808800b60144026001b003e00000118008000200ac005000b00580010007002000004c40a97261f0cae7eec87a1d9d36fc21cc37c840703800b800b880cc02a212cc0ba80f400fe029407700430346005004900ef013c03fc37c005a018405101900c290138036408c00b800bc0230062806400da00181c88066006400dc0468071019e005c00a805500ac0130035801b00000008004000b004e001000c0000000a54ac98788730cae7eec87a2b363b3a088541f9b7e21e430ac2b406e90d9c1b3413b86cc0b8c12cc32c0c2805be0a741038117033a01ac00d80180000a16c7640221507e6dc0dbe1b7e50bc0c8043485190764113c11500001d903b2942d822136f8a0fcdbf283a18500dc018181c005ae033007a00a50086068c00a009201de027807f86f802ea01680e9007f015004ec05f80ea039e02600c1821e01ce061c08a039b01160b50044809c01b2046005c005e000c0e440230037018602b40388126019e007400a803a00ac016c02600a700d6006c00000020010002800580280008006000010f021e8439087900052a564c3c43986573f767674110a91a36fca168614809801ce044405f808b00da01fc00300da011c0328044809000c2006c00200180000a0fcdbf1d9d566ca9dd52ba6ff21e8439010f85db0028068c04900ef013c03fc37c004301dc01fc1cf005a0bb40ac414802a60896027006c8118011209480d380b800bc022c00681830daa05d009f00f90190023008880c5010601900368006016e017c0330030017c001402e00a300fa00c80230037029a038c04680ad00e208000b100cf002e007400a806a0084015402b005b00980300053000000040020000800a001600e001300270008003800026ff36fc767487a1fbb000a54ac98788730caea0f8615001a015808ec04e81070000000c000130f2a56195e2f388734c861be0137851f02000ae8158829004a401ac00c00001d906dc0dbe0221507c6df941d839e0234020408604e40516093c36a0275033808200fb819d0282051009280c2015003e4035801b0136006000010f46e0643c821eaa753b3a6dd8db91b7036f86df8110a85b1d9c3b287642a7a0bb41bdc11b0123012001840068230184e228029080cd0252038804b8c26023a148000b04050020004c009000c000e0c7c03c80020012000c000800f003200380001fb82a5c7668ece0c8e011c0118108804b029e04a80a9817702ec007407b002e0064048c04281e1008e0bcc1150017001a00cc057089f0204228029080cd0252038804b811d000c0428021808000b400c001a004e007800a800a00250034001400e00100048004c01100120022003001a808600f200c400000020012000c00400010014009c002001e001c0000a971b7f2a5a21d432c9d9a3b38a0f861382360dee024044f800d184a091c290804f00fc01400178014004a0068002801c004800880088079000000080048003000200380001b7f2a5c21d4a9686593b34767098808a002a608441d1028307380d5007b008e006401181e8004b002e0074019802e020402140f0823005e608a812380cd0252038804b811d000c0428021808000b400c00278034009c01f801e0050005400bc00a00250034001400e00100048004c01100120022003001a808600f200c400000020012000c00400010014009c002001e00006dfca9688750cb24c40ecd1d9c044230942ae088e0c7218f82ad868d04700160334858707b4161833401f0071800d40188027003c00600001d9c3b343b54290803a00f0044007001a2025e059c44f05c901e6030c1a882c106540a1c21180460418050404701c4042203e401b814f0254054c0bb817002ec027c14280f600cc00c802380ae1848005c0198102000c0428021808000b400c001a004e007800a800a00250034001400e00240044004401a808600f200c400000020012000c0040001005000640ad00270008007800c0000507c7668ece1b7f0cb254b810f952d10ea3b5044f81d102fa098803e011e0090028807e827604e002701190021010212940b0011a0302043c0b18085005c172400e80f300960d44160832a050e108c06300460282050c04701c404ce084407c814f0254054c0bb817002ec027c07b003207a0091c04b80060214010c040005a006003700278034009c01f801e0050005400bc00a00250034001400e0024004400440060035010c01e4018801b000000080048003000200ac005015a004e001000f009b003000800002c773b34767076a065910ea6dfca96821f2620309009b81a601de062c08380a30172070c02380dc009e01f8028002f003e00b000c80000cb2b1dd6a92cd62620b1f964b261f,
  0x1013e00c82910124009e00d004300790062006c0000023000200ac0050038004c00a00078019001c00800001d9a2a586df8a9745e226204c3832c90f20876b1f84520106005c0c7800e807d0396012c3d802470b96013803f003c00a000a8017802500340014012002200220030003805600f2006c00000230012000c00400010014003c00700008b9d171dc93152e262043c89871d9a36fc19662f13b3a0dfa12f414901b3028e011c0258017003a015402d800702da0b6800000080014003c000152e2a58987e2f10659260c4c3898845c60a44036428f83a90684017820d03030ca2003416b81d403a404ec0a7014100fe034007a00ee0148029402180340028024804f00ff013a02b000d0037018601400248110025a03600e80075070c044821481b3028e012c023008b030605d009f00f90190020c618808c0222031406f806400da00c0078010d005400bc002805c00fa06300108160019e005c00e8106002a00e80a280550110016c028804c0108015c053800702da114800308a300be022400b03d100d6006c00f8000004600080018008000200ac005000b00700098014000f005800640138004001c006001000002a5854b930f930e26207eec87a1d9d50b46df941f0c32030608780c381140116011802580ea022402a003a805a044000f0028001a0158027407f809e012400506180098030005480bf814805ec011c1c90032002e007400a803a00aa016c02600a70112007c000000200060020005000b005000b00001b7e3b3aa16948d283e4c460014a95887326004c3098713100cb27eec21e90f421e043908792a5a1862036428f83a90684017820d03030ca2003416b81d403a404ec0e78183043c045003f808b017e011801b80c30096012408801b301ae09b40b700f400ea029005281240086013c01a008900d6006c00f802c0032003800c000026104c10980130c26144bf8987131058e2b1cc32cac933f76dbf887a10f021c843c821e9d9d50b4a46941f1b7e58fc30c00d30137041c0a540cb811104c8029008400f6015001b4021808000b400c001a004e007800a800a002500340014041801c004800880088032000e0b6802b00000004002400180080002003c013800400004c4032c9fbb21e90ea821ea61f7674114825e8292022406cc0a380470096005c00e805500b6001c0b682da0064011805b808e00000020005000f00010f1a1d51fbb2a5c54b130f8659261c4c4021d88a306e60040009801200180008004800300020001d9d952c4c3e54b843a816d07a0005c00a002500340014019801c00480088008800700ac0000001000900060020000800f0000196530fc5c62620ece816d021c0118058403f817302860454003006d022222884508c2f006002f8051811e018c057402300db006e04d007600ad010401c4024001d002a01f0017002d02a8051807480730042072c08200b9185c00346168032021a02340390017006600501b98040007e010400d003e007a001402280440038004000980220024004400600070df2000001180020012000c0040001005600280058029001e0064002000e00400000988152c2a5c987cfdd90f43b3a6df832b83d1080e0700170017101980544259817501e801fc05280ee0086068c07780ff020e08ec02d00c202880c8004e00d9023002e002f008c00c8001812c006b0036009c00200180000a9dd52dac964c460014987865758fc7eec87a2a57566c7674110a83f50b66df887908a2051203ac086028b036402041b805b70b5816d828902df04101bf008b819d0df605102ed00c200b408ec08380ff01de068c02180ee00fe0e7804e00d9023002e002f008c0222020c032006d000c0ac414802a6089602dc12901a700be01ac00d8027000802ec04d80180000a96d37faa57566cb1f93118005261e195d64b1fbb21e87674110a85b36fca0f8450837006060b5c21381c0036003300a880f4014a010c0d180ef01fe041c11d817500b4017c03f80a8010602fc06c80ea0282026002f06fa043c039c0c382180228023008880c5011601900368006079c0e6c2ee008e08020b500448066006002f8051811e02ba011806d803701d802b404100710090007400a807c005c00b40aa014601d201cc01081cb020802e4019008d00e4005c019801406e6010001f8041003400f801e8005008a011000e0010002600880090011001801ac00d800000460008004800300100004015800a001600a4002001800400000a96152e10ea987c87a130f0cae7eecece822136fca168617850308f6006c00f8023001c000163b9b7e2a5c4c30a96065726207eec9870c2e03a20584170812801d606c40f40098010212c805f82440364068008d0253051205f8127827405e401fc227810f02c6081404486fa022205a00ba013e01f203200368083000c02dc02f85db00cc00c005f00a3023c03180ae804601b600dc09a00ec015a02080388048003a005403e002e005a05500a300e900e600840e58104017230b0019010d011a01c800b803306e6010001f8041007c00f400280450088004000980120022003000386f900d6006c0000023000400240018008000200ac005000b0052003c00c80040176026c00c002000004c40a96152e4c3e195cfdd90f436fc767410f8c2d0a061bc8000021f2a5c21d4dbf130c,
  0x10d0e0cd827a83e806bc0150000262a4c469bf4002a67f4d04130003a818002fe052000f802c00004c08983130c26104c009871310723e12fc203839e03800b800b881b00138036408c00cc02a202e002f000d040a01fc05f80370130012406800f404d6029005282340086013c01a000e00004c18980130c26204c20987065958e643d087210f23f7610f4ecea91a50b66df963f0c3e05fa1bd80b7814d01c605ec0858326037a17780c0017f0290011c019009f0282039c0c38218022802cc0002c7726184c20980130e2620b1cd648865959a27eed53b90f421e410ec29200e307f4042c01b829c009201d4135801f0058000097f130426144c309841300261c4c416398659592210ec87910f43f764c182ef014101ce061c10c009f0166001809e800d00c2017c02300f60dfa010c040005a006000c80278034009c00f001502da0028009400d000502da0070012002200221bfc00b03d1010c01e4018801b000000080048003000200640138004001c0060000152c2a5c4c409871d9a36fc767487908751880008407281e300fa02780c500f201ac035406a00d301a4034402e0092028a022002b806f0028001c01a001100860014452802f0dfc03701490249187830ec044801607a2021803c8031003600000118002000200ac0130028001e0064007002000007668ece9310261c6df8a96152e50b41bfc2ee811200960118047000600da04b401800f000a000a8017801a000a02b002e009d00fa044407f818c0042078c04f00cf0314007407900d601aa035006980d201a202480a280560110016c028808400ae01bc003801c002830e8044801b0000008c001000300100004015800a00700098014000f0008003801000003b3aa168dbf152c2a5c987c8799fbb0cb24c38988130c18780dc0235830305ae05d407a00d9079c0e6c2ee02e500bc100416a020e001a03fc0ea009d00fe074805601150428023000d0037018605cc02800490220001809680d803a001b416c003001e000a8017800500b801f4088818c0042078c067818a002a03c801d00d601aa035006980d201a2051402b008800a201300420057014e01bc00382320366051c45281240086013c01a008900d6006c000002300060020000802b0014002c01c00260050003c00c8004001c006001000002a5854b930f930c26204c3832c9fbb21e6767542d1b7e58fc30e803e805c028a001c0088005005400c0036811101ca00840b001e00116011861c820e0148001861c001b0000008c000800f000800380100000260c4c409872a622a590f1930f90f33f761964dbf152e727422940398106028c010001f8041007c00f40228044005c004000980120018001c02d8c37003a0fdc02585230000008c0010009000600040050029001e0000fdd8659727410f4879952c2a5d178861c8073028c072c020003f008200f801e8045008800b80b68010002600480060197000e027c02d8032003a14880258046011c000001180020012000c000800a0052003c00043c672744c1832c9310261c7eec879a61f2a5854b821d8c3805b004480258046011609b007500a800b4088001e0050003402b004e80ff013c024800a0c36186a03140368066006003c0086802a005e001402e007d031800840b000cf003a041800a81450110016c028804c0108015c003816d18680dfc1ef81fd000c30cc13c8c32011200581e8808600f200c400d8000004600080018001005600280058038004c003c00c8004001c00800001d9a2a5854b8dbf1d9d50b44c4098710f21876060c10f01870228000087a10ec21e04390879371f04d80dc018182d7084e05d40e001b001b20f381cd85dc0198054402f040105a801fc00680ee0bb600dc024826b008c012c2ee80f4014a049011a0043009e00d0046006400cc07f413c806b0036009c002000e0030000021eac9326004c309881308261c19656399fbb4dfe43d08792b363b3aa0fd42d1b7e58fc30d803a810e01ae02a400f802c00004c10980130c260c4c209871310723609ac16c01b300004c30980130626104c40987393b0bba0dc018182d7084e05d40e001b001b20f381cd85dc0198054402f040105a8003417c807f01e803b8052804300680050049009e01fe0274056001a006e0140024812d01b002300320015009801ac00d80000004000c00580270008003800c00004c460014a9588730cb27eec21e90f421e4acd8ecea83f50b46df89848c3501940368048001b0030000141fa83b36fc087c17c81140778022c06801a901d40494062804601480420054006d0dfa010c040005a0060013c01a004e007800a800a00250034001400e0024004400440038056010c00c400000020012000c0040001001e00022e3952e26204c38ecd1b7e0cb30f18879043d767430d016c012d01e00140017801a000a02b002e009d00fa03fc0c60292022406cc010804b02c00278067801d020c02480a280560110016c028808400ae001c00e001411480118047008600f2006c00000230004000c00400010056002801c0026001e00380100000878c7668a9610f236fc54b832c9310261c10ec61981f8035808300a680c302f6044012701d005b003c0017800500b801f40c60292036600840258160003a0418035003a028a022002d80510180021002b80a7000e05b437e812b,
  0x1049204900de86fe18900034190801b0000008c001000900060020000802b0014073401c00260050003c00200bb001c00600100000261c4c40a96152e4c3e43cc32c9fbb3b3aa16cdbf0ec818980c8006c811800be017805b808c028800c80b98305008e001825f806d00b404b4110003001e000f0028010d005400bc00d000501580170132009d00fa044407f818c0042078c04f001708a6062807900d601aa035006980d201a202480a2805500ac0220028808400ae01bc003801c0028311c006832100360000011800200060020000802b001400e00130028001e0064002000e00400000a96152e4c3e43cc988130e0cb27eecece8ec850b66df89830c4804b2058403f8143022a031801b80fd0092119406c0c4600be02dc45480d9023001780460173006003c0086802a005e001402e08a800fa044400b8453009006280c6001501e4035806a80d401a60348068814500aa0158081808800a20130042005700de001c62280060e00008462202340086013c01a000d0642006c000002300100004015800a001600e00130028001e0064002000e00300080000152c4c3e54b8983130e262043cc32c9fbb3b3a3b2142d9b7e58fc311c20381c005c005c4066015101e80b9410704c001f60854012807e053601d4232027001fa03180a18161096609640ba807f022a00dc024826b00be02dc45480d90230017845404be002e012000a805502060130134800d064201ac00d801f00000024004002b00160734016000e003000007641fbb26084c309801306261c4c4032c88732a5699fd311800521e6a98821d9d9d5234a16cdbf1308188c00dc08a804900fe09ac1cf015204f2011c35480320000dc0d63b822136f83b20db81b7e26004c309821310260c4c38ece865958e610ecfddaa5a115209640b0807f02860454063003701fa0124024001500f800b40aa00e900e6072c02f8197016e027c13800a900640458086801705b4010001f80250082006801f003d000a0114022003302da0040012001300440048008800c001a0c8400d801f0000008c001000900060020000802b001600a40160019001c0060000261f58fc4c3898810f32a5854b832c9fbb08767674764285b36fc21d4622807d00b805140038011000a00a8018006d0222039410700a4003600000118001001e00380002a624c3e00148799fbb0cb26df8a97043d0e0004f4040005a0060013801e002a004a0068002802400440044003805608a6001862181e0032e0580082001b0000002400180080002003c0020018000043cc9871306262054b130f952e0cb27eec110aa6236fc76740018c44028a001c067816d0036008c007800e000054b130fa62236fc54b9d9d84530a44011801900b3013e0001b81371e3f7654b8a96261f260c1964988130e0876310c203839e03800b800b881b00138036408c00cc02a202e002f00f401180294032000618840034102807f01dc010c01a00140124027807f809d0158006801b8050009200c809680d8008e0b6025e81120366051c620803001e0031c015002f000a017003e818c0042058000b80cf0314041800a80f201ac035406a00d301a403440a2805500ac0220028804c0108015c037800718801bfc00b03d1010c01e4018801b0000008c001000300100004015800a001600e00130028001e00640138004001c00800001d9a2a5854b8988130e3b3a6df88790c4b008c096045200860062009c0001d9a2a586df8a972c7e26204c3832caa5754b643c821d8c4201d60a2c16204c1054c069c1900460053e0b7c14e80d902300858144011700bc003419088a70bc007e80a201660184020002d004e0078009400d0215015803ec217009d09800fa807f809e012400500278124187e023006f806400da001829200460096177c00b80cf003a041800a84be00d401080d4020b00aa015802d8051009809a406000a600ae01bc00000020012000c004000a0016073401c00260050001005d800e0030000159b131026184c0098710f421e499fca9588730cb27eecece800550b66df9c9d0c410218046812780810b8e0a9822781a7073c0c8014e8208040e045c0ce800d064201ac00d809b001c00600001b7c36e0a178dbf0ed21d90a16c76604c1010212c8122017c0364068008d0253051205f8127827405e4043c0b1806b0036026c00c000050b66df8764021f064212c00cb015b003601500001b7e32ac001531526231d92229c16503c005ee14400000cb24c7e98f4002a61d32ae178016503c005ee1440258019602b60204259024402f806c80d0011a04a60a240bf024f04e80bc80878163001a22980fd016601000138012821501f613000190047097e0168110003c00a00068056042e013a0fa807f809e0124005061f0017019e041800a84be0350082c02a805600a20130134805700de01ac00d80000004002400180080014002c0e680260050026c007001800a80000872131026184c20980130e4cfe54ac43986593f76a46887a10f2087a767542d9b7e000a4c1861f828b01d602042db85ac0b6c144837e06fb0bb40ac4153008304a4069c02f832008c00a7c16f829d0410081c04e00d9023008581440117033a02e002f0144018401ac00d80bb01360060000291a513ca96c87a10f254f4a16c21e9d9d36fc088445308230a0e30f425805a2,
  0x10222078014c008b008c012c00e802e0112021406f80a4021002a00368043010001680180034009c00f00150014004a0068002801c00480088008800000040024001800100140000a969d9d10ea1965c9d1fbb087a43d130fa85a0a4a00c805b82da00be040803088ad048e013c03f0050005e0050012801a000a00700120022002200000010009000600040000875043e54b4ece86594c3e4c40fdd843b0e06012c023001d011c00b8044808500000028000152d3b3a21d421d9fbb0cb2e4e942d08ad01c2199402b008800a201ec042005700de006c004002b0014002c01c002600500000dbf152d10e6092002181a3014803bc10700e5004204100cb88aa0204018426101e011260f4800308ac18ac0c88381000d00280414002801c0020004c00900110018001c37c801b0000000800480030002003c002000e00300080000131021e854b8dbf152d3b3a987cfdd865718b000c003680be0222028c000130f21e6195d6a9043d3f769bfc1e9008d0064005c05b80fa00be0184455800000460008004800300100004014800f000054b443a821f3b3a54a8a971fbb0cae10ec4560072002e02e401981cb02be004000980120018000000100090006002000080004c3e21d498786572a560c880468032002e02dc07d005f00c222ac0030c55001a041400800130024003000d800000460008004800300100004014800f0008003800c000036fc43d0879152d10ea7674a971fbb0cae54a862b00ad008c0074047002e01120214000000a000054b4ece887508767eec32ba85a115604ec09d00c3095204981d9003a006e09e003c007108360748070001504720ec401683f7036a0eb006500e10984074c04802f900c20a304550c54001a0b14020003f020a010401f003d008a01101148217044e00400098012001801ac00d80000046090412f827c000400240018001001600a001480bb001c0060000152a2a5c54b443a9b7e0cae43d08791d9d3f7610f462a8032011a020c00b805f006612bc0000008000054b443a9d9d6e0410f432b9fbb767422a82e4014d01c602fc1000162006e01a802100710202022800a81fc024200b40f5012701c201fc1a10228089c081419087010984060c0b40174027c03e409580c8001a041400800130024003000d8000000400240018001001600e0013000e00300000dbf152d10ea195cfdd90f4087a43c8eceb70318a802b4023001d011600b8044808500000028000152d3b3a21d5b8f043d3f76195d42d04c20cf805200868072002e00cc070815f090c1bc80068105000a004000980120022003000d8000000400240018008000200640070018000054b8dbf261f10ea4c4032b952d261c1c0828100890288017c04580c208a4001805981e018a601180258c52034c04dc25280ef048e010c040018b00b4041c01800a30064013c01a004e00fc00f0028002a005e0b6800a0025003400140b6801c00480088008800718a2314000b03d1010c01e40188000000400240018001001e006400200003b3454b8dbf13103b3a54b062b814600e600b835d801d008000fc020803e007a011402200100026004800600000046000800480030002002801480000cb24c3c43a952c2a5cb248629026c02d004f8059809f000c04f4006806101120a6002f80f600cc006c0138004001c00600002a7a54c4acd955d1b7e3b3aa96c87a10f254ee314c13600ea018a022c054006d000c02380020000566ca9e953b90f421c843ca1e302980042078c2ea018a01e4035806a80d401a6034806881450110015c037801b004600ac0130028001c00800001b7e2a5854b898786594c3e21cc628833806d802c81e4089404d00b4416802cf059807c82f000210350082c08304530314313c07900d601aa035006980d201a2051402b008800a2021002b806f000e31380030c4d057205a80ec81960392056c04e0c4c18961bfc00b03d1010c01e4018801b0178008c004002b001400e00130028001e0064002000e0162015001000003b344c40ece952c2a5c6df89870c5001660780023027f0096044400e8173005c02300a300b800e600340e58061032e017c04f80b7048e00c0019004f00fc0140015002f05b40050020003f004a010400d003e007a0014022804402da007000800240026008800900110018000001180020012000c000800a00520038000131050b654b0a9735c33b3a19646590cae4c3e7eec879843b10ea31382c700430100016801805c606ba00d0027003c0054003400a002500340014030801c00480088008805f000e114802b0c4a18920cd400b03d1000000080048003001000040078019001c0000a96152e21e63b2498810f44c3ea16cfdd9b7e3b3a10f46268014012400d004f0043114e1c002f001a804160418010814500a2015c0378104000e114c0b6816a00360000011800200140098014000f001c015001000002a5810f530f952e21e66df87649fbb0cb2ecec62500eb054c0a2c16201a709820c80230029f01b2046016f829d042c0a2002f011703f402300a2061c02e60c14003006d01000168018004e007800a8012801a000a0854056005c052a03ec132009d00fa044426000ff031800840f1809e097c114c0c500f201ac035406a00d301a40344049014500ac022002882690108015c0378007002808c802786ae,
  0x101fa13cc024025600f808a80aa000d00e6008403081cb02080780044819700be02cc047009f016e31881918043010001680180034009c00f00150014008000fc0128041003400f801e8005008a01100b6801c00200090009802200240044006011d0000008c0010009000600040158029001c0080000152c2a5c21d432cb97a3f76987cdbfaa7721e8a96cece843b18c609b00b4013e0166027c0030879001a0184044805f053003d80330027000800380002a7a566ca98955d1d9d4c3ea96d53b90f421e40c8c18f01cb00fa04180398146008a0110011802900005498a8f15242a405488a96152e782cece930fbb570532140c0c8801f0000008c001000900060020000800a001600a4016000010ea54b8986130e2a584c40fdd86570e0a0f18138076001fa142c063059d049c15302350128078205ec0d88680029a02602e400bf1162044406280df0df601b4227000618c2058427002c30df8074811a85cf03d43180097807f083222442ab08450c2c03e004083cb01380d94122017c0364068008d0276021e003402f008c0e0800c0078002a005e0e6400b08b00e02317c063800500b8028803e811e0042078c62f0106002e01200c5001d002a0d540350042035003c801d00d601aa035006980d201a2055c02a81030110016c028804c093203000530057014e01bc08e801b0000008c00400010056002800581cd0070009801400290032001004d800e00400000dbf952e2a58987cece90f43f764c4043985e100b009c8365844a18ba0e2809403c1044403182ce814d01fa142c0bd82710d340f1803a810e01b0047c06b80a907c8012427f8037003e00b0013800058e64c00986130e2620b3456a8865959a67eee2024484087b101887a10f021c843c952b08b10c6c0534061803706f8085008a801f0000002c01c0028005800021d343a488087eec987130c26201964439843b18c2021c01b80980092039c06c00b30a480118457811101be05cc00300640008000159b26ff592654b8a96261f58e2b1dc986130059a24c41648930e0cb2b1cc87a1fbb890e1c100fc01ac04180534061817b022000c812701d00a440b6008901b3009600640002c9326184c00a97152c4c3e4c389882c710cb2b344fdd90e421e843c821dc5e2115e0178006808c080401901e90006073e00c005f0032006e053407180c3008c028c04680710400058809300ad0126005c00e801500d4010801d005500b6013006000a6014e007c00000080014002c01c0026005000b0002000e000021cc988285b5aa49bfcfdd90f483167676135865711600178046000d02e60184088805f04b002dc013800e0000a95d53b90f454b69bfd42dab363b3b09ac21d839f080400c801b814d01c6030c023008d00e208000b1012607a402b4049801618b8001862d84ab079c147400680890808001402e007d023c00841cb81e3020c005c0c5001d002a01a802100f20074035806a80d401a60348068815700aa022002d8051009803000530057014e01bc08e801f0000008c0040001005600280058038004c00a0014802c003200100070020000054b8a96261f36fe21cc9881fbb21e8767542d0c5f057403d40b880f807bc01fc07a00ee014a010c01a0014012404c804f00ff013a02b000d003700a0012409680d805b004480d98c5a18b2092c13b0111011801b4032003001e000a80178399018e001402e00a200fa0ac0067801500ac0130000000200060020000800b0032009c00200004dff0f1a0c59310000a54acdbf88733f7610f487a1d9d043e3b2032c8c5c01ea03e00fa04a902e200dc1ef004901e809ac05281240468010c027803400280248099009e01fe0274056001a0078016814c00460096177c104809001be01b4067801d002a015802d804c0000000800180080014002c0002b36878c0014a959b7f10e64c009861310261c1964fdd843d21e8a0fc879418b3b3a3b5010fb93a18b4024804f001401fe00d004e8043015803b800d003700a0012409680d805b004480d988ae00fe03e015d02b10520163402f80cf002a015802600000004000c004000b004e0010000418f1da83b2010f9d9d878c10f4986130026204c3887a2b3621e47eec32c80052a5621cd41f0c5900280248027809e024803fc135817f013a012402380ac006e00c800d00bf010600f004c014100b4039c0c382180530022c023004b0bbe037c0368017019e007400a805500ac016c02600000004000c004000a0016000159b43c621e843ca1d5043d874c7eec980130c26204c38002952b0cb221cdc9d08ae068807040f5012f058607481be0214029a030c18b04e5041208d80bd8110012009380e8005f05b004480d980f01146012c0178399002c02b4023008e018e001402e007d023c00840f181060314007400a806a01e400e806b00d501a8034c06900d102ae022002d80510098030002b80a700de00000118001005600280058038004c00a0014801900400000439952e2a58987e1e313103f76767410f8ed00876316c229005f0204018429280060e06091c027807e001a01400178014004a041400d000500380040012001300440048008800c000e092000b0c5818ae021803c80310036000000100090006000400780190008003800c00003b3454b8ece931036fc31d818a82ed063c083814a8264,
  0x1049c07402ef05c0116a22d0385070b01be05cc00300640118017805100e502640330459803001e0031c015002f001a018400b801d010a005403500420074015402d80510098030005300a70204102000000080014002c01c002600500064002000e000054b4439a61f000a6dfcece9310261c1964fdd90f421e4b548635004b008c044829208b2025a000163b930c08764c01668931021e4b245639930e21e87eec32cac93727c1c2c10600660064030c023811002a407402ef05c00e1422c806802e5000c029409202340086013c01a00140124033407a0017003a005403500420074015402d804c01800298053800000040020005000b00700098014001900080000ece952d10e64c309801310261c1964fddab3621e843c942388b30096011816c0524025a08800002c770876b3448792c9158e643d09861300260c4c409871fbb0cb2b24dc9f08b20864043009a818103940c78006806100360038000261f4dfc6dfd41fa85b4c4432080b184c20302078008f03d20e12130c00681a700420ac0082019718d205200390168027c04ac00b008308a4001805b80320bc4043400b80050066004402f8007095e015800000080002003c00c8004001c008000010f42620987cdbf9d9d2a5a7eedd9d0408008603b80d1803701de01c407f8015039800b43ec00e100fe082007c0081079600c004e00be04ec028c051011e0e1202e4261802102c00d94122017c0364068008d0181021e058c00682f3098409b00a40014019a04a40710005012e0070008001300240044006001b0000000800480030002002c013800401360038010000021c843c0876043d26204c31c8fa61f3b3a54b443a9b7f0cae43d0fdd90f218d201f00be804803a203b0131015d000000ac000130f36fe195c10f952d10ea99f8384802d01c2005433e04a40036000000580002620087c97f0657261854b443a930e0986022404581f5008c0780010804b094a039402f824701de028c229004f00fc0140017801618d0001863387080e0c007401702990028010001f80250082006801f003d000a05b400e00100048004c01100120022003000385e100000008004800300020028007801900080080000152e21e84c40fdda61f36fe7674a96052601d80574024011e00f800840aa010400e6036c05c83d206440208039001d005c0a6400b8033008000fc020803e007a0014022804402da00400098012002200300000023000400240018008000200ac00500290040000021e90f33f7654b0a9708754c3e4c3c32b8c68002c023416d00190000ece930f931058ef17182f10197034c027c09b80ef0316041c01900a3009e01f802802da005e005863307080e0c0050012801a000a05b400e00240044004400385e10000000800480030002003c00c80002a5854b8dbf90f43b3a4c40fdda61f0876319c01800be073e028c051011e02ba00dc07600710090005403e002d011200840aa00e9011c0410039804601b602e40190322015a0208039008d003a00b814c80170066010001f8041007c00f40028045008805b4008001300240044006000000460008004800300100004015800a001600a401000002a5854b843aa61f36fe4c3c87a043b3b3a7eec32b8c66092600180398c65064400583838706003a00b814c8014008000fc0128041003400f801e8005008a01100b6801c0020009000980220024004400600070bc2000001180020012000c000800a0052003c00c800400004c40dbfa61f3b3a54b0a9710f43f7643c8384004600960c8c1238043010001680190030009e00d0027007e0078014016d002a005e00016a93b3a592cb35963f13103b3a987c87910f459267eec32c870702c204a011a830206f409b01e5808b01ea08d804480f8012001842548c640496027013b000d00bc0314046006d00c8019801800be0146028808f00c602ba00dc09a00ec00e2012000a807c005a00840aa00e905600410039804601b602e40190322015a0208039008d003a00b814c80170066010001f8041007c00f40028045008805b4008001300240044006011d0000008c001000900060020000802b0014002c0148004001c00800001b7f2a5c21d530f930f2a587eec87a10f2087a767432b8c6502c208d409404190362020404c02440364046805f810f00fe022407c06fa057405d009f00f901900ac414800830b1a017c062806d00cc00c005f00a3023c03180ae8037026803b00388048002a01f0016802102a803a4082007301b602e40190322010401c8046801d005c0a6400b8033008000fc020803e007a0014022804402da004000980120022003000d800000460008004800300100004015800a001600a4002009b004000020c7952e10ea987c98786572a587eec87a10f21da83b2021e821f3b3aa0f863201d3039400340d30230026e083807a029503f409900a2005f0222023005200a50210059805400c208a401b4032000618c60c8c023004b0086020002d0270028e00c001a004e007808c8015001600641c140e1801d005c0a64086801700660050020003f004a010400d003e007a00140b6801c0020009000980220024004400600070bc2047400f800000040024001800800020028007802c0032001000700002a5854b89881fbb21e8767530f9b7f261c1c181cf80a2023c0dc40c900c6,
  0x10000002c0078018000043d0a96152e4c3e7674fdd9b7e04424c4432b8c800060019005f008c017407081a083f5077e001845c8014004a0068002801c00480088008801b0000000800480030002001000c000021e854b0a97261f04426df89889d9d0cae7eec43a8c7c02e600c008880be04fe023005d016a02b6087012c81a4016003b00360048002a01f0016815401d201cc0e581e0032e09b00b4013e025602cc04f8123008c0208056801d005c0a64020003f008200f801e8005008a01100b6801000260048008800c015c00c8039008d002e0b6c00d8000004600080048003000200ac005000b0052006002a000021e854b0a97087504426df89889d9d4c3e195cfdd843b117200cc0b6800700aa002000780002a5c54b130fc7e205b60c7818a813703c0083814a826402220c8c22a00a4021002a003681fd000c0238023004b0112048c030827911700074021808000b400c001700170068013801e002a053200cc00a0040007e0094020801a007c00f4002816d00380040012001300440048008800c000e31ec00b0c7a00000008004800300100004005000f003200100001fb82a5854b8dbf13113f76767487a261f043e31fc08201970042020c380000601ec02dc019004700be02b80138004004000009889d9d58eeaae959b10f454f454b95311fbb0cb26df930fa83e117004ec06180060274044008a85db03a4068802300370762012c02480ca024602c003f809000c20be463c80300054001402e007d031800840b00017003a041800a806a008400e80ab80550110016c028804c018002100530057014e006c000002300100004015800a001600e0013002800520064002001800400000a96152e4c3e19649889d9d043e6df887a1fbb10e631ec2e4014d01c602fc0bd810b006e0c34147804903d4049c058007f068408a0227020506421c0422a026c027c0444062808300da001805b80660064011c02f80ae0008000163bab364dfeb24cdbf2c732622b24432cacd13f7643d010f9d9d507c31e4023008b0096022409180002622767432cac93087adc78fdda85a08a801b00580015093001300038c7800360000005800f000054b930f952c3f70087cdbf13110cae31e805702f900e40fd800b8322006610a00b6801b0000008c0040018000054b930f952c3f70195c10f9b7e262221d463c005c000a025c017805e0146028807280210970101037800070e18003445b801618ee178c08104080a4c047463b008600f200c40000001001e0064007002000007668ece952e262022f811800cd0252038804b80100026004800600020012000c00080002a5a6dfe0c58221507e21d438602470a4a013c03f0050005e001800a002500340014381801c00480088008800700a2021403080000004002400180010014003c0020000507e767432c952d3f7643d130f9310043e22dc02e0097000a017845800a2023c057406d800d004203b004100610970012000e80850206016c0288007116c178c08104080a4c0474000000100560028007800e00400000a97261f36fe4c40fdd90f43b3a195c63b8071002a00dc01684a901c203e007a81f402e20f7809900ff020e08ec02d029800cc00c005f03d20146047806d808207ee007401084c203fa00b80820006062c082404480850e121760456009000c2003411800cd025200680710005012e0c88008001300440048008800c04f2047400000020012000c000800a001600100070020000054b930f930f36fe54b487a283f3b3a7eec32b8875116c005401684a401c200342ec86f502be004000980120018001c049801618ea1020293001f00000008004800300100004005000b001e00b000c800e000043d0ece9fbb4c3e6dfca971310261c178c00305250e0601840068247009e08c003f0050005e00500668025025200680710005012e007000800240026008800900110018001c63a01020810149808e8000000400240018001001e001000700002a5c4c38dbf93103b3a7eed30f90f40cb231d40150030000a05cc02e008c012e017808880a201ca31cc0030c7218e200340108061097002140288102081014980000001001400100070020000054b887a130e2620987cdbf9d9d3f7619644398c7400680050021809205ca033407a00cc041c04c8000000200006dfc87982213b3a54b421d88733f7619653158c73000a00a802e0030012e01b402f01110144039463800000002000130f800536fe43cc110952d3f7621cc32c843d18e4005001a00920086033405200cc041c04c8000000200006dfc8798221087a54b4fdd88730cb298ac638036a0064038c06180470216044012802fc049231bc6370c6d18d831ac3b8841f094c001805280430068005004900cd01e8033009900e501440178224809700b80014635000d00c2005c04280420074015402880a6014e0408204000000040020000800a004c00a000c8004001c000130f800536fe7674a968873261c4c4032c9fbb21e843c8638836a0064038c061804702160440096029703f222cc00300a5024808d0021804f0068005004900cd01e8005c021003a00aa0298053801f000000080040026005000b000c800400007674a968873566ca11c981130826144bf898713100cb27eec87910f4261831bc0fc020c035800c80a680c3008e05ec0880152,
  0x1009e01f8028002f0028009400d0005003800900110011000e12e4010800d03ea0184644870f002c179408e8c880000000800480030002003c00c800e00400000fdc10f43f767674a97261f262254b0204830d190e05ec3f9014d0954179004c011100cc01b4018002a000a017003e818c07ee039c010845402c0003400e8106002a01a820201570110016c028804c0180021002b8007190c07f400308bc04f21c3c00b05e50000008c000802b0014002c01c0026005000a400780190008003801000002a586dfca97261f21e87eecece931150b432240d301370394083814a82640222074c13600ea018a003422a00a4021002a0033006d0460007409f80430100071402d0178006002e8017004f0068013803f003c00a000a801782990028010001f80250082006801f003d000a05b400e00100048004c0110012002200300fe8006117809e438780160bca047400000020012000c000800a0032001000700002a5c54b09889d9d50b47eec87a1b7f4c3e21d46430061001a1310118001d027e07140bc00ba005c013c03f0050005e0a6400a0040007e0094020801a007c00f4002816d00380040012001300440048008800c000e321408e80000004002400180010014003c00700002a5c54b130f9b7f2622767432c9fbb507e10ec45e000d0972018401084c402c00074083015700b6014400000230014002c01300280052003801000002a58767421d9fbb507e54b930f865936fe4c444398c85029a05ec111030d058607a82ab008103f009100d9011a0130043c2f2045401f009b015d0111049602700368276006002e8015002f000a0ac4148005c0b1a028803e800d0318069c01082b002c0033c00e8106002a01a80ab80560110016c028804c0180021002b80070e1c05a009f012b010600c800300470e1a017c05700160bca005c16d801b0000008c0040001005600280058038004c00a0014800f0032001004d800e00400000a96152e4c3e6dfc87a1d9d26227eed41f070f034c04dc0cb820e052a099008880f601480420054006d0086020002d00300068013801e002a0028009400d000500380090011001101060000001000900060004013800400001964fdd843d54b70ea887a261f10ea1c3805f003001740e7c02f00a2023c0dc40c900c60268012003e015400e6072c0f001970166096004f80061908008400681f500c2048c0230082015a007401702990028010001f80250082006801f003d000a0114022016d00380040012001300440048008800c000e320c01b8071002a22ec057003200e4023408e801705b6000001180020012000c000802b001400a400780270008003801000002a5854b930f9b7f21e876749889fbb0cae17940180064017c023005d023006820fd41df8000592cb35963f1b7f8316a0fc11093113b3a195d6a91fbb087a32100030064073e00c005f008c0174001402f005c001a028803e80610318048c0230021010402b40b0001d020c055c044005b00a2021002b803700e2005445d80ae006401c8046801705b600000118001005600280058038004c00a00148004001c0080000152c2a5c987cdbf93110cae7eec87a1d9d10e6320c0918c820104072c03e801d00e600b80748299008000fc020803e007a0114022002d02da004000980120018001c02600ae00e4005c16d8000004600080048003000200280058029001e0000a96152e0cae987cdbf93118fbc22ec06300fd028606900b0821c098822e83868006190202e8017800500b801f40c6002102c0114c024018a003a041800a80f201ac035406a00d301a403440ab80560206022002d80510098021002b806f000e096800b0c80001a31fc00b82db003600000118008000200ac005000b007000980140029001e0064002000e003000800001fb82a5c54b130f90f43b3a4c44fdd9b7e19100118047004b0112048c00013113b3a1965649843b3f76a168262003700920454058007f00007674988843b0cb2b1ccfdda83a117400c805b804700be02b800013113b3a196563b843b3f76a0f838685e4080e02600b881b003800b8006801510198029009f8043009e00d000a0092013c03fc04e80ac003401400bc032018fc31f408880df00da036408c009c00bc02e001800ba005400bc002805c00fa0054026000704b4006c000000200060004005800f0030000137fac774cfe0015311952b044243d0dbf1d9d26227eec32c843d19020dc018182d7084e05d42f201b003800544066013f009e0050049009e01fe0274056001a0078016814c009807ee039c1cd845405a8022406f806d01b2046004e005e0170007400a805b0098001c12d006b0036000000100030014002c00780180000acd887910f4000a988ca959d9d262210f4fdd8659507e088548d1b7e50b431f801b8049017e02c003f80003b3a4c4421eb6fe0cb2b1ccfdda83a0bc822980e2805a00fc00f0012801a042a02b007d809d098003fc04f0092002800d022a004304d803b809f00370106012401900b000fe011c1cf005f015c031406f806d01b2046004e005e017012f800e801500b60130134800704b4006c00000020012000c005000b039a003c01380040030000163bab364cfe0015311952b0cb27eec988a91a21e810f4879022136fc767541f0c7d00d802c000a86590098001c63e001b,
  0x10172057406d831a043601c80760082029403c4049801700b2012000e806800e001a807b8042016a02ac02a80560206016c028807b01800210053005700de007c000000200060020015800a001600e0013002800580010007002000004c4130f90f43b3a21ccfdd952f0cae32542f382c304ea074803f839f06f80d4c10a01150000a95553aaab554ae43d152dab3654ee767537fa85b507e10ec2f40014034602480218065014a03d038880ef014403fc02f0107001a08ec0e904aa003404ec1b700ac039e026002d007404d8039c14c008c018a022c1e9006400da00180470089117e179803e8066083e324820500a3017201c800b805900d003dc07900ab01ac035406a00d301a4034402a805600a201ec042005700de00000010003001000280058038004c00a0002000e000043d0002a6ff261e7674a979fbb10e6195d42d0c9306e00c0c0e002d7019805d41cd80d90230092c04e02d400bc02e000d80180000088541ca83b5234a168dbf28460e22005004908a100ca006807700ac00fe01d01cf05da01b2046004e02b105200ac0153044b0112017805c0252034e022c006826c0daa04f804600c501060f48032006d000c02dc02f85e600cc107c20500a3017201c800b805900d001c007b80b500aa0158028807b0108015c000000200060020005000b007000980138004001c0000a97a6ff000a4c3cfdd90f43b3a195c439a83e117e001405f005c0060014c0000001000054bcfdd88730caee7ed59b840a0854028806c800d00c2006c007001800009bfd41ca83b5132a0fd42da85984d4179c10e008c014405cc1cf8111023c0dc40b0819202861318006802100c204100f00089032e02cc047009f000c115402f8529064601a003803be067e08ac3f280160e20019404b007400a6004000980120018000000100090006002000080190008003801000003f7054b0988152f3f76987c87a1d9d10ea2304024013400f80318076800000560000a979fbb10ea195d55b04c6011602240f00502063c069809b8144041c0a5413201110184029008400a800da000130faa62566ca9e941faaba21e6767553b843d08aa069809b8197041c0a5413201110106029008400a800da001805b80040000acd953d2aba54c4a96c879a61f875414a4045808903c0140818f01a6026e0510107029504c8044406100a4021002a0036800619220c8c1e9805f098a00c812383d0009e01f8028002f04a200500328025012c006803a000500a60070008002400260088009001100180000001000900060020000800400004c40a979fbb10ea43d130f9d9d0cb21c4010e008c014405cc1cf8111023c0dc40b08192028614a003f8115079809c01358232001a008425280610208078004481970166023804f832307a6017c2628032024808d0123812d01e004341e8004f00fc01400178251002801940128096003401d0002805300380040012001300440048008800c0000000800480030010000400c800e00400000988152f3f7621d432ca61f21e8767421d8c91009003f403e00c601da000001580002a5e7eec43a865972f4aad8294001d009600b8023006800000028000152f3f7621d432cb93a54ec0f4c003070e016e001000006593f76a96c43aa61f21e90ea8262801d009600b80230068011c08440a7812a02a605dc0b8017601ec00c812383d0009e01f8028002f000c00500328025012c006803a000500a609440a4801c002000900098022002400440060007070200582240035010c01e40188000000400240018008000200280078019004e001000f000026207668a979d9c08ac12e4010800d03ea01840428051000e324000b0c8f0a4e22f420488be191c021803c80310014003c00c800e00400000ecd1fb82a5c1c480030525115a048c030800d0e18149c08e8004001c0000dbf93113b3a1964a969fbb4c3e43d043a8c90002a01b001680b001c217640af88b60020004c009000c000e32342578527117a0000001000900060004005800f000043d0ece9fbb4c3e54b8a9693110cae323c00280be00b800c005d0097073e017805102330d8607801b886c402de02cc0c901ac04b000186460032018c0118010800d006e0534071808d026802b40fa806100e208000b1001700900074042801500d4010802a810300b6014402600c0014c149c0000008000200ac005000b007000980138004001c0080000261f36fe43d0ece952d26227eec32b8873191a02f8018000500c8017004600ba012e017805100e50264033064580000002000130f800536fe0884a9693113b3a21ccfdd8657087a32300490014019a0d040000002000010f432b93113b3a7eeca968873508e322c3870032000c011c386801600e4005c019800700ac017c057010200000020007801900080000a9693113b3a7eed30f90f4507c149c00305251174005400b002d0850048c070815f00c20be42578c8a001a041400800130024003000382480036000001180020012000c000800b001e0064002000e00300000a9713113b3a54b4fdda61f21e86df845e88b80086020002d00300068013801e002a002c01c800b8033015c040800a00250034001400e0024004400440038248000000080048003001000040078019000054b49889d9d21e854b8fdda61f36fca0f86450230027e07140bc00ba,
  0x10ba80478010825002a405fc0960104008e0d0008300cf002c005c0810048003a00541aa806a008400e819a014000aa0158081808800b60144026049901800298053800719400f7c05e8456006a04c4205808600f200c4000002300100004015800a0016073401c0026005000a400780190142001000f002000007670ecd283e0a540448291004b0000b24ca97152c4c3e4c3832cc5c626211788650828c02be0b6800b0040007e010401f003d008a01102e500100026004800600bd0262008c001000900060004014801901420000fdca61f507c54b843a8ca0043802300510173073e044408f002102c00dc40b081e000fe06480a180b3022a0018006845500c2017c294832300d001c011584c6077c0cfc00b08c800ca025803a00530020004c009000c000e231c64f88c6118a1c48043007900620000001000900060020000800f00320010007002000007668fdc040b05e609680068061193c04fc0e281780174013c03f0050005e0050012801a000a007001200220022001c463801b0000000800480030002003c007001800007674a979fbb21e84c4542da61f0cb223202f483a000be02b800013113b3a54bcfdd90f40cb2987d41f0c9e004204780b0037103c017a00c900b3000c115402f83230bd20a1815f82be07fa005864e805901da01a003800f7016a02ac02b008800a201ec042005700de0000001000300100004015800a001600e00130028003200100100000262254bcfdd90f43b3aa16d30f8873118e02e802f040a0bce17a008f037103c00648059814b000c3270010800d03ea018424c00ae01600c3414781a200e401b00a500f10212005c02c80ed00d00054038006a01ee010805a803a0156015402b008800a2013003d80c00108029802b80a700de006c0000008005600280058038004c00a00138004001c0080000261f21e8767542d952f3f7621cc9888657193a0190205008c017401782f380e50264033064d8021001a07d40308498015c02c0186828f034401c8036014a01e2042400b801500d4010801d00550098030005300a700360000004000b00700098014000e0040000130fa85b26227674a979fbb10e6195c21e8c9c00ca0248052801401e80d0400000020000195c9889fbb3b3a10f4439952f508e326c08801a2007404bc03c0167018602ac15d020c01f00710058014f0254054c0bb817002ec0f3003305e9050a0e800be01a0015c043c030800d193404fc0e281780174013c03f0050005e001800a00250034001402981490038009001100110018001c1c080160a42112001a88c6118a1c48043007900620000001000900060004014000f0032001000f000e00007ee0ecd1d9c193e0bcc203000010ea7ee032c9d9c50bca11942da91a513c987c1108c9a000c1154047032300d00a1815f82be07fa01440038c99002c23100448c98192e1c50091808600f200c4000000200060004005000f003200100001d9a262254bd42d08c6000c1154047032300ca025803a005307a6004000980120018005846200020012000c000801900080000fddb93a2a5ea96c87a43c64c3e767541f88751932001822a808e064601a0032809600e8014c1df001000260048006000700b6007404100000004002400180010014003c002000072747eeca97aa5b21e90f1930f9d9d507e195c46200070702230c00b0448006a0218000000f00320078000285a262254bcecd1d9c193000180fe84c404f2230c461052307a60058115800700ac016438a0123010c0000004000f003200100001d9a2a5ea168988aa5a192e0b5c0d102d30220069005802ae0074030c29403cc04d8105410a0143022a0d2811182670dde03cc2e7031c07440a0c0de039c08980d50059808e000c05242908035038a05e005d013f00fc014001783d3009e0050012801a000a0070012002200221c5009180860062000000100090006000400c815a0008007800c00003b3454bc43a86592622a168ece08c30a5203d8032809600e8014c008001300240030003805b003a020800b05e90740017c64b00ae010c01e401880000004002400180010014003c00c8027000800009889d9a727454bd41f07140a5203d814302bf057c0ff400384c5000000080018001001e009c00200002a5e7eec87a2a5b8754987c32c85e9008e005c00b00330456001c02b003200b20000004000f00320000a979fbb723ca9681d00211029e04a80a9817702e005d814c00f600cc019404b007400a600c800800130024003002383d304a2001c00b0559089000d40430031000000080048003001000040078019004e001000f00007274e478a979d9a3b383258006837200c204080428490077c08ac00b08c10e20004000980120018001c38984560e24021803c8031000000080048003001000040078019001c0000ecd1fb82620231408f00210bd004101b881e00112065c0c900b3011c027c003045500be14a41918286057e0af81fe8016192a0164076806800e003dc05a80ab00ac0220028807b0108015c03780000004000c0040001005600280058038004c00a000c800400400000988152f3f7643d0ecea61f10e61c4c03288c00124325000a08a2003402b003a00c202880c8005100d90230027002f00b801180f4803200060bd000340308c93117e179820f840a014608cc0108160,
  0x1727498786570cb6196832c0659152a195c0018061070b00b403c04218050007800bc42200161958031c002805c0e2c025c15d020202f804300cc018105ee07c41078021052c00681f602b401581ab007104420886045c11303070398080418d834407f606ac0cf0186027803d40980100001a05e4030849e03f804840700145026c0cd000b817d003a021400a8199013401a802100f201ac035406a00d301a4034402a808800b60144026007b04d2030004200a600ae01bc17d01560094019c031001b0000008c0018008000200ac005000b039a00e0013002800520064002000e0030015001000003b3854b930f0873068c039c04c008b017e01180030037015a0e44038801d002a016c026004a00ce0000005000b000800004399fbb874d0f1887206571958026819a08cb00f6001c2f68cab004600200058026005000a400780002a5c9878fdd02fa002c080c1fc843e05ac0050012801a000a007001200220022095802681560094019c031000000040024001800100320000fdd1d9d4c3c21d42f6800d05f20708066812901c4025c15b0199013400b43e403bb01dc00580f48040007e010401f003d02e4011402208ca0038004000980120022003000388cb1954031002681560094019c031001b003e000800480030002002c0078019004e001000f000e00300000fdd152e4c3c767065580ac01c4089008b80c2039808041fd81ab033c061809e00f502600400006817900c207f009080e0028a04d8003017d010a066404d00f201ac035406a00d301a403440b2808800a201ec042005700de0310025006700c4006c00f8023000600ac005000b0070009801400290008007800700003f7454b941fa61e10e6232c04d033400f6001c46500161952008c004000b004c00a0014800f00320000ece1fba2a5c987941f0caa01b40718006815c020a0ad809b057c03c4066404d057a005a0fc814880ee03d20050020003f004a010400d003e007a05c80028045008800700080024002600880090011001803100ab004a00ce018800d801f0000008c0010009000600040058029004e001000f000e0030000032c952e4c3c7ee8ece087511940eec016801c0022026800380fa00aa005c04680bd063a0558025006700c4000001180020012000c0040001001600a400780003b38a0f930f1fba2a5c195c65483f0003c018800010f500941ee400f0062000043cc033800d03840184169811b018208f02918333017a32a0034007007be06d819901eb029813181df033f045623006538ca6083e0058032809600e8014c38800100026004800600070e2622f865281310816021803c803100360000001000900060020000800f003202840070018000076680310097068a0170002802a0b4a00c065200e901ac035406a00d301a40344044005100f6021002b806f000e1c5400b05eb08ac04c4205808600f20000000802b0014002c01c00260050003c00c80a100007668ece0ca504d603600248037079e049011a0043009e00d000a0092013c03fc04e80ac003400f00f580f00640043401780a207320014010852b00b8078c0678345031401cc2f600d90230027002f00b80298107c0030ca3001a0184464801501d203c806b00d501a8034c06900d100ac0220028804c00f6021002b806f000e1c541bf80160bd6095429504560262102c04300790000008c001000300100004015800a001600e001300280052003c00c80a10008003801000003b34767159b0ca401ca04c801080cc014407d424e0248001a01840070020000019644399fb9507ea16e135261f2a5a17b0010818c03c601f40c5007301e4008c014802000005468a8f151c2a4c54a0a9015242a5cf059daabb9776ae987ddca952c068a08440a7812a02a605dc0b80176011c02dc02305ea119200c812a852a081602180001d9a3b3810ec6518092013c005007f8034013a010c05603cf003400dc0280049000c04b406c08af06ce01980780030005e00a8002805c00fa175008f002103c6033c0830292022406cc0a3818a00e6012c042811b003a0054074806a01e400e806b00d501a8034c06900d100ac022002d8051009801ec0600057014e01bc0038715002c17ac01902550a54115801a81310816021803c80310000008c001000300100004015800a001600e001300280052003c00c80a1000800800001d9a3b38a1684648299095e00b80af801d10ea012c2f5004605300198123805a00600844027807e00a000f0017802a029e04a80a9817702e005d800a0040007e0094020801a007c00f400284c500380040012001300440048008800c002c17ac01902550a54115801a81310816021803c80310000000800480030002002800c80a100080000ecd1d9c10ea1c5406d8897010400dc024001d017201c403e002e00e400540aa0146002e12480c8807305b60dc8006804600c217a800a0040007e010400d003e007a0014022804410ec099800e00100026008800900110018001c0a0003204aa14a822b01310816021803c801f0000008c001000900060020000802b0014002c014800f0058028400700003b34767032b85eb11623288265026704220a0c1ce08ae022409ac0248037017e026011c06ef05ec031406f843a072401b40fe80060a48011865081aa03ec088438200300054001402e007d,
  0x1086c0dac65b81a506d20fc424d02b90094019c03100bc02b002c402a000021c443a08732a5b087aa9dd31fa67f196432d865a0cb0195c000c46804a201fc043806c011f01ae02a40360016119e031c010801501c800b404f00fb013a01f404d0cb6000a0040009801200220030003834605f40000001000900060004005800f00320080000152e3b389878988071a01fc01b065a8016119e005401687190a58004000980120018001c1a302fa0000000800480030002002c0078019000054b8ece13104c3c54a865b003701dc01240218030040600d00150014000a007000881560094019c031000000040004013800400004c4043aa61e58e67eec32c88cf001a0be40e100cd0252038804b82b6026c0664020003f008200f801e80450088006c0118029001c0060000152a2a5c9879e0b3b5a7734ed0941fbb370e3200c003300be030603c0045826b03fa01180890718015a02080e50198003a04d40f2823a040c046405b0397005c07d005f82d4010a05c430f0835040e00181e381510eb414500ce8838022a003406c011f018200dc252006c00e2031c00a802d01c21904066848e0252038804b86ba032214b0002822700201640009801200220030003834605f40558025006700c4007c000002304f8000817a000900060020000800a001600a4007802c0032001000700002a5454b8ece261e2620195c9870cb50174080805f01790060144c03301f003b8065015701ed03fc060c04582b903ca08e81030119016c011813280bf03fa02b416882d0055e0b3c18982ce02d800180cc001d006e0fd811f00dd0fd812e838c0446005c01c408100cf088a008400a803301c800b400b809e01f6027403e809a00e40c3005701311968005838b80050020004c00900110018001c1a302fa02ac012803380620036000001180020012000c00400010014002c014800f00320284002001800400000a971d9c4c3ca0f829604a201fc043806c011f01ae02a403600c700420054072002d013c03ec04e807d013432cc00b0717000a004000980120022003000383460000000800480030002002c007801900400000ece152e507c98789880cb40d8c026009585c2017e020c00300b7006e23380aa83fe03980ac000a8117034e00b400682b61964130c35d047b196203880af00bd006405200468072021a0cf400b80fa002c1c5c002801000260048008800c000e0d1817d01560094019c031001b003e000001180020012000c0040001001600a400780190008003800c00003b384c40a97283e4c3c54a865982f704d0086c0ef820d03e203c40f901de041e010806d80210114020806e8121003a0ae4093802e02d406580ad8228010a0368102800d03840ad809b002d002a01b005c80fe019a04a40710097008000fc020803e007a0114022001000260048006001b0000008c001000900060004005000b004c00a4007001800a80080000391f2a5454b8a9688754c3c195c9878cb101a002900a080f9024a010c04180a80346001809200b704d6055403602b0002a069c016800d056c130c23d803202a405fc0960148011a01c8086801701f40050002801c0020004c009001100180be8025006700c4006c00f8000004600080048003001000040058029001e0064002000e000054b4a95152e4c3c21d541f13100caea9e89870cb201fe076010080a501840018010836a01ba038c06188cc0216044001900fe051e068825005ad067232c0021008a0242007415c8127005c05a80ec81960392056c1140085007403681028078001a03800e1001707e6033409480e2012e0ad807d0136033202686578043010001680180034009c00f00150014008000fc0128041003400f801e8005008a011000e00100048004c011001200220030003834605f4012803380620036000001180020012000c0040001001400980140029001e00640508004001c006002a00200000a0f8a97261e3b38196438b8046011c012c00305dd0184041c100819803ac08b0116836b034a09a005901df041a07c40f901de041e008406e88cd05720490096805a01b803c00278050007800bc03100bc000802c40100000592cb54963f2c7759ac98786570cb6196832c0659065959267eec9880cb00172070c023803201ec0554021808000b403700180034009c00f0017802a0094019c031001f00580064013800400007eec32cac965aa44c4163bacd658fc98884668047002e00c801980f6019e055406e802101c8027807d809d00fa32b815c816a03b206580e4815b02460368102800d04b40ffc0570362040603f8054829400920ff800a802d006e03b8021808000b403700180034009c00f0017802a0028009400d000500380040012001300440048008800c000e0d1817d01560094019c031001b00000008004800300100004005800f004e0010007001800a80080000283e2a5c767130f0659766c32bc656850c05ee09a0059019803be08340f8829803e4077810780460042012c06e801d119801980170032028c128003982b90086020002d00300068013801e002a0028010001f80250082006801f003d000a0114022001c002000900098022002400440060007068c0be8025006700c402f00000023000400240018001001400a4007800401620080000152c2622a0f8a97130e36fc7ed8ece0659,
  0x1014e01bc0268015036e07741a381560094019c031001b000000080018008000200ac005000b039a00e00130028001e062000c80270008003800c005400400000fdd261e10e66df86668367022400009861302261c4c2098012fe2620e4ec263828002b21a18130843605260bdc11602f5033004a004581b1030602600f2823a040c046405b004a00ce01880ac00006dfea9dc21eaab765cc32c8656263d000acc98ca9195432b4439046b05aa101c057005b00bf000c01c00a5807b068e0558025006700c4002c0130028004e001000008733f749878ece88d5001a058c08b8181039833300f5803c003402b003a00c20bc0080425800ff02aa020c15701fe028202600ec00d0014a029003280920028046c027804b051c0490089010b04d60a5c2e900fe021c036008f80d70042012424d03610cb80fa40a600c102d8069428605a402bc167807080f0005e00a8063800500b8014c38d838b03380f0808c812e016c02fc003005901da00740340070065a03dc02100b50156052c02b008800b6014403d82690108029802b806f002a06dc0ee834702ac01280338062000000080018008000200ac005000b039a00e00130028001e062000c80270008003800c00200000987897f131010e6196541d1d9c11ae130406c8335199601781ae822a001a17c4007000050b2a0e948d0ecc1da4a17942d9b7e199808a019081270000a164dbf285b043e17c435388250d360bdc10c81df041a0ac80f881d503bc083c010828105ea16641db019802500f04111008b03621a000fc018903060260032006619940e2c0ce03c203ca08e81030119016c01280338062000800800002a7554b6dbfd53baab5566a10f555ba61e566c1c6c09b009a01e4035806a80d401a60348068807b00ae01bc00382b804ac332417d015600940188011800b004c00a0014800f00009878a9703470174080805f01ab033c061809e00f50060040046888d3017e003400300c9022a02c001b806c00e200586640179198e008400a80e4005a027807d809d00fa0268663071a0a5800140080013002400440060007068c0be80ab006200360000001000900060004005800f003200100070020000054b930f1d9c199200dc07703fe008600c01ff803400540050012801a000a0070012002200220558025006700c40000001000900060004013800400006dfc988ac7310ea9878fdd86591990167c24d00dd02d806941fb868c0ff2026005d08d4017c16fc01808d3023204b805b00bf000c0a5008a80b0006e01b0038801611a4008400a80e40be000b404f00fb013a01f404d0131000a00400098012002200300ab004a00ce018800000020012000c000800b0032028400200200000987941f93112a56767043a9fbb36fc331c19e08d004803314247827d08680e3422701ee0bde33102e103920d8c0bd80d8809801be01b408c812e016c233804e80120094019c03100030000dbfca9588750cae7eec21e8003566c234c09a00c6009004a003e02f506800188000002b000054ac43a843d6ebc7eec32ba67e198a02b4023001d053000b80cc01060094019c031000000140000a958875566ca9e88721fbb0cae98f866203fe006e0be4077000d008600c0203003400540050002801c00220558025006700c400000010001004e001000700003f707670dbf283f3f76b1cc43aa61e0cb2234800682f9080c0ffc1ff003701dc010c0180034005400586618015005a1c64098871a0a580050012801a000a007000800240026008800900110018001c1a302fa02ac012803380620000000800480030002002c00780190142009c002000e000054b930f1d9c2a54331866101df041a0ac80f881de041e00846608198011600c00c180be03941c5805d0135057408080fa08d1198006ac0cf0186027803d408005ee02f232fc0068061006403180d200460246023409a00ec015a020800b8048003a00cc03e002e03ca08e81030119016c06ec0aa0146017e01cc0030294022a02c001b806c00e2005401687190e3414b000a0040007e0d2c0128041003400f801e8005008a011000e00100d7c00900098022002400440060007068c0be80ab004a00ce018800d80000046000817a000900060020000802b0014002c014800f0008003800c0020000054a8a971d9c4c3c195c661826805980c3c1b5823e07e2000131fa6230006330404c0cbe03da0128033806200300000ece1b7f0442dbfc76788d1197a0bd410c81980250075404581b10312060c04c006400cc079411d0206023202d8025006700c400100002a5b6dfea9dc21eaab719646550cad0cac000a9a093152b36198413b80e28080042c059819f03f400c40000dbf843d04427eec988865759ac9a0c660080419780bc411681df041a07c428001d603bc083c01088d019760fd010084d202cc030835c008000b432e8277023b197207140bc0591042c045c65c0546053a09e00e000cc05ea04fc0cc01280346022c0d88043030602600770066036a00c009a80be02d407640cb01c902b60cb806500ba04b20870006806103ca08e81030119025c02d805f8006022a0558025006700c4006c01380040176003800c00540040000141da89b50b6b54941faa5758fcaadc988ac9659ac195d6ab1fbb54b6a9dd30f1b7e197e0bc00ac80b205001a18130830f,
  0x100080078000152e3f74a0e866e80a9022c0124371801600e203040638014004a0068002801c00480088008807a003e000000100090006000401600190000a0e843a952e58e64c40fdc8cd700c806240b9052b00b80d14003013601c203a407900d601aa035006980d201a20594044005100f6021002b806f018801e8025006700c4007c0118001005600280058038004c00a00148004003c0000fdd283a2a5c21cc66b0167057404bc07c000d19aa0a1c16c83721052170c04280e0019a04a4071009703b00d1407f807c02020228017020107b6120420c035200420c140c901ac02de02cc0820078024a0cb01c502e803060554177814102d005d009f00f9019002dc106009f19a8334c1f2056f09e603a401f8041044800f801e804500880018016801000260088009000c05d4001c2bc804c0188103003d004a00ce018800d801f000400240018001005600280058038004c00a00078004003c003800c002000007ee8a9747de11b40b4c16b817d01c001f003c03db05de064809c851e0604073c16c808903060c7010f0187022802380598352005c02141a400cd0252038804b80fa05b61b800f6056f09e6001800800130024003017500c4081801e80250067003e008c001000900060020000802b001400a0014800f0008007800c000054ac7ee8a9708755076a96866a000d00c20dc803d000e0000ed08a96bc167734ed6941fa85b0690055405b81cb0dc005b409b00e1008000fc020803e007a011402200060020004c009000c05d4103003d0062004600080048003000200a40020000766e54b843aaa563f74a0e8669865e00c401e800043a608181a2c12b06e8016002e825e811201fc0a6806b80a908140208039006c00a6005838d847d017e001800b805901da00740340070065a03dc05a814b00aa0158044005b00a201ec134808400ae001c66908d9002a06dc1a381560094019c031000000040020000802b0014002c0e68038004c00a00078019004e0010000261e00f408b00d2836b016409a00ef820d03e207c80ef020f0042066006e829802aa0ae41e980f600cc05a80e481d9032c056c09183a001b40814057000d11a409681ff815e002c0a5012b02cd067e16e001b807001dc00500328025012c006803a000500a6007000800240026008800900110018236400a81b703ba0d1c0ab004a00ce018800d80bc0000000800480030002002c00781880032009c002000e003002c402a00200000987843a8cd20270005c00e8033005c01640340083011605540cc00fe01ba07b8036016c034a005810d02540b08003407c0130004205ac0a080e4077809b016c81d801a005b81fa01a9040203a80928189018a037c05280a402cc042006100a800c801b40030cd102bc0a5046c007001dc00500328025012c006803a000500a617b400e00100048004c011001200220030003852d009a00540db81dd068e0558025006700c4006c00f800000040024001800800020028005800f031000b000c80270008003800c002000009878fdd08d90114010805a80f102de0a5c0fb80fe021c036008f80d7015233400360016199e031c0028011000e14b40268015036e0d1c0ab004a00ce018800000020002002c013000f0032009c00200003f74987821d8cd10066005c02c8047016e02e40aa80dd00420390077818b020e028c11902b902b805a80cb015b038c02f406d02f9001a095021e004f006801f80270050007800bc015015e0528236003800ee018e005003280250034001402985ed00380040012002200220030003852d009a00540db81dd068e0558025006700c4006c00000020012000c00400010016003c0c40019004e0010007001800a800800001fba4c3c10ec32c8ccf0066016400b809f00e40504174812c0b10122007f010e01b0047c06b80a900d8031c0028011000e14b40268015036e0d1c0ab004a00ce018800f800000040020000800b001e00640138004003c000130f1fba21d410ec32b8cd0085e00580f1031d018205a41ff00c70028009400d00050bda007001200220022001c2968015036e0d1c0ab004a00ce018800000020012000c000800b001e0064013800400009878fdd283a11b00ae80800716001a03246670179199a07c00ca01ed11ac077c10681de004212681b082ca055405b014101a50a1816902cf08d5071606700ae03c2023204b805b00bf000c0164076806800e00cb407b80b50156052c02b008800a201ec134808400ae01bc026834702ac01280338062001000ac005000b039a00e00130028004e0010007001800a800800001fba4c3c21cc2968071018200580af08d701c201ec00a81b703ba0d1c0ab004a00ce018800000020002002c00781880032009c00200180000987897f08733b384c4141d0cce0640147c04e01180170017800682050236012c263816404de0808083812d044007ac078014c00a000f046b802f005400580af0517049000680560074018408040eb022d04d007c80aa808303e007700ca02ae03da07f809588d603be08340ef002109340d8416502aa02d80a080d2850c0b48167846a80c7000a0170029871b071606700ae03c2023204b805b00bf000c005c02c804801da00740340070065a01a807b8042016a00e8055814b00aa0158081808800b6014403d8269018002100530057,
  0x1010401e800c800058fcb3596a9283f4c44b2596499fb9727433d016b015e03ba06e8026804a03100060000152c592cb35963f2d523f747ee0680031505da0c780ec03f403300804052816605300308032809600e800400098012000e1c7c0340cf30312031406f806400da06e803d004a00ce018800100090006003c000152c3f74acd821e8cff002c21b813505c319e433c4678001a015801d0054008308da0aa00750141079a060c10f00e70430045046e8cef19dc008446e01d80e3c00500490065081a005c02c80ed003a0054196805500ac022002d804c04d206e803d004a00ce018800f80000004000c004002b0014002c0e68019003c0080000152c54ee439087826fe3f7410f4439871f001a12a8365086f02bc078807b808403ba06e8026807a0094019c01c0188001c0060000152c4dfc21ccfdd10e4507ea9dc875283b087a7ee0678815e00be23780ee81ba009a01280c400180000b259639ac933f74b1f89832c774c564c0898043ab2a58a0f8678011e05ea0660094008b08cc061c03d00620000a9dc21eaab7000a9bf88748cef002c020802780db01de33b446f001a0158047803a02f5015004a023682a801d40c0816c83cd02b8060c10f00e70430045046e802111b81c7800a009200ca103400b805901da007400a832d00aa0158044005b009809a40dd004d00f401280338062003e00000010003001000ac005000b039a006400f00200000a9dcece10e421e010f537f1fba10e67ee48740cf2098e0a48025811b00c2003438e812d03d606d8028003c00680058049801d00b6007c00000080014002c0160019001c0000439ac7e592c98ac76a283f3f724c0897f130026204c386768278036a0eb009a81f4026407000b881b0053a081c0660151022e067405d800050bca1193158ed4507e088438e84bf04a004b4077804700a0013c00b05be017a013400c80003f72b1cd6499fba58fcb25963ba62b26044c00983283e11bc16641e084b40d96174802c03660dd406c4196027204fe12f0094019509760bd418c011e0330022c373807a0094019c031002700a8000153baab721e043a087226fe000a10f559ab71e11ba0bb40cc08db01160160023826c03b40b2016482e90e38218003a829a021c036006b80a901de049011a0049009e005803880c104c601fc0ee81ba009a103003d004a00ce018800f818800580064013801e0000b1f9639a62b3f74b1dc21eaa7721c843c0a9626fe507433b813280b204b809746760ceb19d433a46740ce719cc339467202cb0390338c671007a017802c4000262b00062370045819804d80580670802110ac0394670007a0094019c031002000009bf953190e421e010f553ba62a0e3c008408200e5017203bc25f812c024801e8010000026104c089861310724c9bf9c8f871c06580504094008305ea05540f18104004203940ec00d002dc0294052007a0094019c031002000009bf952d843d556ea98820680bd05ac09e446d85e2002e00cc02c808302aa069809b814107780760068016e07e806a41008125014a02900b30108018402a000a0065004a025800d0074000a1b9c00e00100048004c011001200220fdc003859600a2062406280df00c801b40ee81ba009a01e8025006700c40000001000900060020000800a001e06200002b36087a54b0fdd3b5619e600340480584017a08680fa026307600ebc0b582c605b20128031001b001c006000010ee21c843c0a9621d4262032aa2e390e33b38236c1a40085020400b816d803306a407b00458083033005540b001a6004204dc072814104d80760068016e07e8080407501250312031406f80a50148059806100a800c801b40030cdf03d20930112017200380040012001300440048008800c000e337866e829111b4031003d004a00ce018800f80020012000c00400010014003c002001e00400000fdd152e03740c6c0d5819e030c04f007a8130024e03e00068372010a33700908cdb011410601fd001000260048006007a0094019c001000900060004013000e000054b952ba1d710eaa0ec21d8cdf0e181c44070000d00f00240177820203e804e408101f003b8065015701ed03fc04e80198089030607b004700b304b00d4843a002e019a025c0f2823a040c046405b0087002000300250067003600080040001001400a0013800e0030000152b843b43aea0eca96887576ac33701a9002e04b00a640f6016d05b6010001f8041007c00f400800130024003003d004a00ce000800480030002002801380002a5c10ed52b887543ae54b066d805c012e05c802f0064014406240728cda001a008403081f5020402141240cd9000c059402b0051018801e8025006700c4007c00400010014001000f000e00400000fdd152e10e6337804900cd03d20330052813203b000340308102010a092002b005100c40008004000a001c000021ea1d72a5a21cd3158cda00c806240b9052b00b80d1403980e901e4035806a80d401a60348068808800a201ec042005700de01e80310023000200ac005000b007000980140029000054b8439a1d7087a54b066c8006010e336005b015c085e045800b01e2063a335c0638014004a0068002801c00480088008800719ac01fc148801511b40310026840c0094019c031001f0000000800480030002003c0160019,
  0x1507e1c8003a00ac015000680928050079a0b88110000602ca06e80250067003e00000018004003c000087810e821c84388fdd065910e64c0c4708075109c19d4426847f0cee1590026801f005800780001fba26184c0098710f109901008064800d0d9421a836c007f002c04e0003001700b20074034001500e003dc05a80ab02ca015402b005b00a2013003d808400ae01bc0dd004d081801e80250067003e0000004000a001600e0013002800580064002000e0000b54898708733f7476743910071002a0304016840700e0070017001710360021c0660151013006d806801a305ca03bc0ec00ff020e08ec0f5832001b2046004e005e0170053006f80be02e612b40518189023c238000680610236036c05680821a0a02e443d0d04030005480bf812c029001c800b0d03021a340812a8d01004217c8680001400ca009400d00050038004001200220022001c0b2800619fe06e8026807a0094019c03100000004002400180010016003c00c8004001c0080000152c3f74acd82fa007c009003b4076014302ba0bd4031000000560000987843b0cae54bc43aa67e11c012d01b306f1067412f005904e2021208b811f825d032a12ec1da835500740c60176811e0768138403c0189065a02ac0b98cfe0272037c46f813a19fa17a867e04a5033002380598068005c007403d00620178000000501cd005002c402a00004c467ee4ece043b566c54bc43a8657261e00156490d0505400d101d481b0046a07a81ef000d026433ec36e02d7029802f8051811e036c08f00ae8382036803040d1813401d80800093007101de0120035003a002a03fc03e010100f000b410080ed01ee02ac0380305032406b009c80870a3c03a8181044a039e0b6404c03d406380878073801400e8001400e0012002201e8025006700c400000010003000200ac00580380050003800c00006e3e54bc43aa6234c7e001542d130f3f72195cece043b21c833f426381b301040074017006801660f501ab8257000e05940dd004d0094019c00f80000014003c00f000026084c28fdd043b0cae4bf8986130026104c386820183063808780c381140094019c00010e421d8dc7c1ea00e5014603bc67d002f009e00842f90014000a0070008800702ca06e8026807a0094019c00000020002003c010000026187ee821da83f3f7219646818254001a0b4c030823c0236030407e804b0092012000e801500f800b801680ed00d001c00c900b3010e09c808a00b602b809c01358116066403c00a60247025a07ac0920234036c01f8027002f0054014001e004f00680050012801a000a007001200220022001c0b281ba009a01e802500670036007c00000020012000c000802b0014002c007802c001c0060000130c3f7410ed41f86593f724c3867d003a021201e00e800ab0856083067c8292070c10a4041001d005c01a005984ba04d805700aa8168027c03202b686e201ec027c033047e00b20058019837f002e019404b00740020004c009000702ca06e8026804a00ce018800f8000000400240018008001400a00078019004e001000f0000566c10ee2e39fba58ec34080350101029403dc12701ac091407680fc000702ca06e8026804a00ce007c0000038001e0078000130c25fc4c3898113063f7410ec32b90eb19f2060c0b40174027c03e406400b3013e01980340059005c00cc00e801719f0023400b0cf7017a001c0b281ba0094019c00000080014003c00c800400007ee4fdd2b360876a0f86808232097405700aa80c801ec027c02c80dc19ec0f4016d002f002801940128096003401d0002801c0020009000980220024004400381650374013403d004a00ce018800000020012000c000800f004e001000045c60876acd8fdd065919ee053037280be095a028c00682330a5c06d80ae831a04360a380d180ec029403c40b100ef01b60304024006a008407e40e801b400e201f0080808a0212049800a80ed01ee02d401d002d032406b00b7807800e00d44160832a050e0cb01c502e8015608280a0820c01a00b940ec0cf505b205540b4017401f2032007b009f00cc01640198017052404480d9814702360e580468082015a02f401085f20028019404b0074000a007000800130024004400381650374013403d004a00ce018800f8000000400240018008000200ac0058038004c00a0007802c004e0010007001800400001649ab363f7410ed41f1fb90cae33e014586d40982036408c009c054c0ac414e8207095a017805c01a704a4045c0ce800d0a5c07ac0a6023b017c041c05184c7049c0a380a5016200d40108080808a01ee02d40d6016f0de811440ed01f803ee05040928305040203fc07280f9013e01640198017052406cc0a38396011a02f401085f2003401d000280220024004400381650374013403d004a00ce018800f8000000600200008038004c003c00f000e0030008000026233f7410edc9d8ed4507c195cfdca85b4c5433d418d81b203400468093810f0000a16d42c8ed41da43b4010f852e00e4005825e811601b604480d9814719e802f42f1010d003a005c017003300d0016404700b7033005540b001040028009400d000500380090011001100f4018800f8000000400240018008000200280160019000010eca9788753f724c4000185f20236012c2e68016,
  0x1015211e068804c80298098c39100f0005e00a800b0138018e0014003001700900074034001500b8059402a810300b6014402600070018014c2fa01dd0374013402500670036007c0000008000200ac005000b001e06200160019000800780070018000054b0fdd130e1a220a5c14e018002fe042c023828e017a14b8030800d1a1e046c02585df1a1c00841a181550b320ed81c583ef01060f04111019c027607c00ee02ae0256237c1f702fd027434340a602630e4403c0017802a002c04e00638005000c005c02c8048003a005419680f7008402d4055805c02ca015402b010300b601301348084014c015c03780070018014c2fa01dd03740134025006700c4007c0000008000200ac005000b039a00e00130028001e062001600190008003800c0020000054b0fdd130e25fc34401b304b4097802c8117023f04ba065425d83b505da0c6008f03b4030202883748d0c051205f8127827402180a8008d01ff01b2027002f00b803e007700ca02ae03da07f803d004a003602f000c00b100a800008729d9c58ee988d48d2c7359a64c00984130c261c4c40fdc865950b69874002a6fd0442343c07e8271047809ac145004905c20304075887d02fe0ac002381a7017a09dc06c81180138017805c001b017600600002c774c463b30765291a1da83b487680ece36f46dd0dbb1b7258e6d508110930026104c3098713103f721965669a83e1a1806d801a00cc002804c8049027800ca0cac052828a03b00a8007f81ff040202700610135017001d00b2022504de003405602020120006811e00c1017a014007e8049008e04b423280d8097a17cc08901b300420d0c0aa83b607160fbc0fa00830444067009d81f003b8065015701ed03fc04ac1f702fd0274005809c001700b2012000e801501ee02d4055805500ac040c02d804c0108015c037804a00c4006c00f80000004000c004002b0014002c01c0026005000b000c80bb001c0060010000026004c3097f130e2620a4688729d9c087a54bc4399fb9727634380aa808301fe05040ec00d0014a02900328092002800d00db071104b2028804e005e017000344728d0b0402049468500c20150152403a085801580c2800d00bd04780e082b501b405b20f88028004701fa05ec1a6829c02201bf82460857025a0548232824e1a120740684002104c0146838f84c80298098c39100f0005e00a800b0138018e0014003001700b2012000e8068002a01a8021003a00b8059402a80560206016c028804c0180029805380070018014c2fa01dd0374013403d004a00ce018800d801f000009f0001000300100004015800a001600e00130028001e062001600190142001000f000e00300080000152c25fc4c38fdd10e41a1a0d100cf0186027803d409801ea01f0000141da8991da8087c47288e3001a179c06d00c107040a380da01c6009205ec085811011c2035c235029c04da341c05108e40236012c2f980d002dc0290032809200281c8426400160270001800b801d002a01a8021003a02ca015402d804c0180029805381ba009a0128033801b003e000000100080014002c01c0026005000b000c8004001c0060000291a4dfe767097f130c26004c38fdd1fb910e643909840d08058221c4040816b008e02701b2824402f806c80d0011a017a09d80878061001a0178264004a0036026c00700180000a16d48d1fb90cb2b1dc98410e8260043a8872130e26187ee8ece426b11c8030803a0201015803fc00d01550078020c0f581410640238806c81180138017805c000d00c2341808d804b0be60760068016e014a0290032809200281c84010851a002c04e0003001700b2007400a816500aa015802d804c0374013403d004a00ce018800f80000004000c004000a001600b000c8004001c008000026ff26007ee8872130226104c3097f130e52347670fdc887336fc341c085828e052e17c40c0017f001a011c47180bd0236012c2f980160270005c00e80150084015402d804c014c013400f800000100028005802600580064007000052349bfcece13003f7421cc8721b7e26044c2098612fe261c7ee541f0d06098e06cc00012fe26104c30980130e2620e4ec2f982ec055612c017587b60f6a08680aa816b010601600a088e20236012c1c204c704d6035c02480c1073c028806c81180496027002f00b806ae06000bf8047017a0760068016e014a0290032809200281c84010851a0990005809c0006002e016400e801502ca015402b005b009806e8026807a0094019c031001b003e000000100080014002c0160019004e001000f00540040000148d26ff507c4bf8984130c26004c38fdd1fb910e64390ece022111c6006801e00ac03d601d026080a806a20ca8092804a0000000c00c00003b3810f4dbe1b7e50b63b20db8152f3f7221cc32c90e711c400342c2052e0dca0a380da03b008f411e41d7816b05b2042c08808e10a9c18b414e026d097e011c05e87200236030402580490bba09ac0920234036c013c01a04c8002c04e000b801d002a010801d005500b6013005300a7009a0128031001b003e0000004000a00160098014002c00320078007001800009bfc9841300261c4c304399fba21c87ee548d1d9c58fc1c8420381c005c005c40d800a20198054402f000d00c2003800028464dfea16d41da91a,
  0x10004000c004002b0014002c01c0026005000a400c80270008003800c002000007ee0a96285a262221cd6a90d1f03121034032000606de0a1802c80ed00ac022003d805701960128033806200000008004002b00160098002000010e6196559b152f0e4a03940ec0189014a019000305f6004201980820032119a0f4068f0596008c012c12380430060013c01a007e00a000bc01500161a3a007400a002500340014017001c00480088008800700a2021468e00cb00f4018800000020012000c000800a001e0064002002000007ee142d130e2620348809f03d4013e02cc0002a7754b6439021d85f6001a041445b85e31a3604081ef803306fe005c008001300240030065807a0094006c00000020012000c0040001001c00600002a7710ea4c38a970659262054b563b0d1e02fa0b4c03e00e1009000b407e8015018c180c0c90139010e0c080e7809807a8039c059800603fa1c600ff81ca062c0b9c065023603a602400068230023a23b82b2827008f009ac08b0124046804b406e00f0009e01400178014019a0094094801a01c4001404b801c0020009000980220024004400600cb00f4012803380620036007c00000020012000c000802b001600b000c8004001c000152d2a77261c4c4032c8875507e54b4ece0d1b01ce02600598087000c01900c485f5006e01240cc00150ce20a60016823903fe03840da82e7019408d817c81d301200034162810500d60168018003c005400680028229042e089c008001300440048008800c01960128033806200360000120825f04f8000800480030002002c002000e00300150000152d3b38a0fc43a86597234a9dcdbf08ee032a09fc18c002102c001e801000004c7e32c937f05f50dea099800685e309861c081490147077c020800e802e000e0144065807a00940000005000f001c0001dab13102a5a4c3832b8d1d02bc1c1c00b04b1003a1c14017010d0532005c0b682db0e480050020003f004a010400d003e007a001400e00100048004c0110012002200300038d1a019601e8025006700000008004800300020028007801900300000987285a3f704c40a960d1c02bc23040ee80cb00f401280c40018000021d4fdc152c262054bc392010600e617bc389808902bc12c407480f201ac035406a00d301a4034402d805100f6015c03780cb00f4012803100230014002c0130028005200600001fb850b44c40a9608731a34001402e002f012e028c02f0723001a17b00308016020434641240056000e23b447601e211d614bc026807a00000020000800f003200380001fba0196005c2f10033017a04081a400100026004800608ec00f4000000100090006002000080002a5a7ee4988087511da025c2d2805c0bcc001447300170090007400a806a008400e802a810300b6013006000a6014e0788475852f00000020000802b0014002c01c002600500000fdd065710e63464123804b009e01f8028002f002c02b400e8014004a0068002802e003800900110011000e014408d808500f40000001000900060004005000f00320000a969fb92620a168476001d005c239c04288e904a0001c0390093002c23a868c08e80a5e013400f800000100028005800f005800640001fba261c23ac39187200bd8025c04280e100b81270124005100f6001c00880bd000a011c08682501a2e01e800000010014002c007801900004c409872c773f7254b432c88ea000a00a802e014c012e1c8039185ec0204038424e024800ac01ec00388e91a2c01e800000080002002c00780002620b1dc987152d3f7219649860d17069011d000800130024003000000020012000c00080a100004c309882c773f724c3942d952d10ea23a40258147003a08c8017000700a2046c04280000014003c000152d3f724c3098713100cb2a16868b0014006802481b2006501ca103442c800d004201840fa800602040164076808505f009200b28056011001440038d15002c10e029781ba00f40128033800000040020015800a001e0064002000e004000009871fba3f7034602e5842f0068013801e002a07a0043400a00250034001400e00240044004400b043811d0013403d0000000400240018001003200009871fb83f7421d468a842f1a28095406e037f005e0058473801d005c02140aa834801ec040802c801400ca009404b001a00e80014029803300380040012001300440048008800c000e015400b852f03740128033806200000008004800300100004005000f0032009c0020000261c7ee963b08e8023602b421c0000261c7ee9649a85a0cae239c25d071c02aa013c04180140282024846a0d131a2401942df840d0be0028c017801611cc036006b851b1a22031c0028006002e016402400ed003a00540350042007401700b2805500ac040c044005b0098030005300a7000e003002985f40374013403d004a00ce0188000000200100004015800a001600e00130028001e006400200003f7454b029784ad0466003401080610208057408d80db0634086c05c80ec015a02080a500f10a2e01c82df01e200f40038010000058e6b1c563b9fba5922b345649acd35aa44c3c32b88e60cb0003405101640120239010101f4017a08f008d80c10e3e0ec023d0479075e0718163038c008e03f4025804903a0134c18304e902b805201380147,
  0x102ae17e000b0d2a0a62005c00a80e901e4035806a80d401a60348068805501100144026007b0108015c037840f019601e8025006700c4006c000002300100004015800a001600e001300280052006401380040136003800c002000004c384399fb82a5834c40bf019f074a043008002730750068007a81c1084e22082598175073c34a404e00d9023002e002f000d0e4c01ac01081e3002a010802600a600f4006c000000b004c02ec0070018004000008721d9c087699fd48d152b0cb24c44439a85b36fc34ac075846005be0a2c23602c4042c045c26081c502f001f802800250034085405600fb013a130007f8d280de8034004c0087006e0ec8024822a01600034393002103c612f80678015008401580260269014c032c03d004a00ce000000480030010002c0e680260176003800c002000004390ece043b4cfe54ac439865926223b2142d9b7c36e06df941d0d2900680050021809205ca02780ec00cb00c4000000100002a56dc2c21d88730cb298ac69403fa01c600dc0858049051e02c02f8820501960128033800036fca16c988ac730cb2b24421d821f0e4c01700028345017c102805d003000bc019005101891a4e0034010806103ea00180570498072201c81fb0531002e03a406b00d501a8034c06900d100aa0220028807b0108015c037840f019601e8025006700c4006c0000008000200ac005000b007000980140004001c00800001fb8261c54b043986571a54024800a00650bdc103407285f9000c031801903910268023400b804800aa040c065807a0094019c0310000000400200158004000054b0002822136fe195c98888734dfc349c38200f0006000bc01500c7000a062402e05f9068a17e000b0093002e007400a80e900d4010801d00d601aa035006980d201a20154044005b00a2013003d80c00108029802b80a700de032c03d004a00c4007c0000008000200ac005000b00700098014002c00320000439930e2a584c402988725057c032c000000100001964439952f0bf014ac1a2815701d2035806a80d401a60348068808800a201ec042005700de01e8011802b0014002c01c0026005000a400008732a589bf8a9705f907bc05c409901f401fe07040e50209025e34980e98090001a3494692020101860c1409c80ea039e0b641ea00df02e606242fb84a00064008404f844602c005040cc031c043c039c0c382180988023805980060b2c1038023004301000168018004b0068013801e002a002c020800e8014019a009400d00e2000a025c017001c002000900110012002200300038051010a348c0918d22019601e8025006700c40000001000900060004005000f00320010007002000004c38fdc285a081e028812d005e0036000000c00005234196443a93114dfe0884692803a022001e00d100e0000000a000c80002a5a4c4443ac5c05070349005802f911dc0000a96aa773b3821d432c821f507e4c44dbf0d26001a0be420302d3034802c029403cc0324021c181009807a8037c0b981890bee02b81d0009f0282066007381870430131004700b3000c2308207052307a6348409f8043038a02000bc005a017400c0027803400fc0138028003c005e00a800b05300028009400d0005003800900110011000e348009180cb0094019c0310000000400240018001001e0064002000e0000a1689889fb82a58348c00682f9080c0b4c0d200b001fa012406300370324021c181009807a8037c0b981890bee012000a807c005a12800aa00e9006401cc04f8446028206600738187043002380598006081c0118025801d005c1324204813f00860714040017800b402e8018004f006801f80270050007800bc01500160a600050020003f004a010400d003e007a0014022804400380040012001300440048008800c019601e8025006700c4000001180020012000c000802b0014002c014801900080038000393a2a584c4443a9fb82a5c348400680900e3a07d00f8019403da07f81ea00ea060a08040eb02f1077212f025d821906cc19d021a811e03aa03942fa802102c001e80250062001c006002a0020000098fc21daa7a6e3e7671423285e507e9bf82fb831e0330069809b829803b00fd0100818901be02940b300c200c801b403d004a00ce01880002aba54c4a9e953bab36087a10380c4840d00c800181d984c6045601940298070067e1324017001d0104004000600cb0094019c031000000040020000800a004c009c0020000727454b043a86570a600a640b68040007e010401f003d0020004c009000c00f4000800480030002000043abb572a5854b8264872500a60d1402e00051a3e0058041001d01d2035806a80d401a60348068808800b6014403d808400ae01bc091807a00000004015800a001600e0013002800320000fdc285a262254b04398d200078006802d00ac060a027410080ff013c024800a004f027e0b5c202000d11ca0c340d100b002f60440024814d018600dc0d60139010e1478075044a039e0b6404c005801be0c7010f00e7030e086008a01730166001803200210312078c29580cf03140d140ab84090e4a02e8018002f0054011802580160104007400a80e900d403c801d00d601aa035006980d201a20158044005b00a2013003d80c00108015c053806f0246032c03d004a00ce01880000023,
  0x1723c21d4a960ed21d983b187650ed41d9c98fcdbf821f26221964a970d3c083208d404081a4066a23c42e800b00036026c000418b723c438843a952e0cb254b09888ed41d9c3b487650ecc1d8c087d41d0d3b001a018444e033d02bc0b6c3840724023a007001200220022032c03d004a00ce000800480030002003800c000010ea7ee0a961b7f50b64c4047900fd018c012022c007c000c05f40d20032008600c039301d1008e00d00150042002a0b8400b008a005a03ac039012103d00384129828902fc093c13a02f2002e17c4190820502c600cc0068102015c0dc81a40d3a0e4e0050002801c0020004c00900110018001c22b840f019601e800000020012000c00400010056002c013000f0032001005d800e003000009871fb836fc35000d8819204140018033045807400f3029408f10348074417080eb038c07a0058007f04a60a240bf024f04e80bc80570321040a058c030800d008600c012d00340054005869c87270028001400e0011000e115c20780cb08180128033801b00000008000800f0032009c00200bb001c0060000130e3f706df8a960d3a03620648105000608b0031801b80fd0092012000a807c005a055009b00730396055403304c50064011c00b82db02da010c018003400540050020003f008200f801e8005008a011000e001000260048008800c019601e8025006700c4000001180020012000c000802b001600a401380040000e478a96283a10eae46832cb97a21c454b847880660bec08ac45c8231000c34e069b85fa001a08141fb0727000e115c20780cb00f401280000008001e00100070000261c7ee0a961b7e0cae34e402400ec00f806900aa021c00e60c3013300ba081202f80298030001a0814020003f008200f801e8005008a011000800130024004400600cb00f401280000023000400240018008000200ac014800f001c0000fdc152c50766df942d931110ea195d59b8d3708b00194263022b1a6c00400658000000400200001fb82a58a0ed42d9b7e262221d432b843d566c34e011d817800b41c7414c013f0330068c2fa871e008605a822c0259018c069009a00ec009001f00190154011a01cc186001704cc0b6c20480c501be062403680640bf40034102806b0028010001f8041003400f801e80450088007000800130044004800600cb00f4012803380620036000001180020012000c0040001005600a4007800e003001500001fb82a5821d541da85b36fc10f559b13110cae54b869b0068099200b800e80ad008c032c000000a0000195ca96087554ec17e800e8707005c00580b684c907a21c902238105001a34d400a00250034001400e00100048004c0110012002200300038457019601e8025006700360000001000900060004005000f0032003800c0000261c7ee0dbf13100e4e06c41050192000c1160063003700cc03f402480320090005416d007c005a04080be80e104c622043dd056504e011e01358116024808d0021812d01b803c0018004f00680140017802a002c34d00e882e1025e03ac0e301e802ce01fc129828902fc093c13a02f2064208140b180610028009400d0005003800900110011000e115c20780cb081801e80250067003e0000001000900060004015800b001e00b000c8027000802ec00c000036fc4c38fdc1310043e34d40c4840d00c801880002b36556ea96d531043d08b00cfc38100e107ec001c22b80cb00f4003c0001fb850744c389881b7e0cae34d025c85f8002c34cc699000d004201840fa8102049034c402b040f00f4002000c800e00400000fdc130e10e6115c002805c017c02e804b803000bc0190051018901ca34c000303910490032c03d004a00ce018800000010008000000282212a5a4c4443986571a6602480668014019817b8099000607220920065804a00ce018800000020008000032b9311044254b4439a62b1a6006b00a681f802f623c012705de0b8022d445a070a0e1603c0018002f0054031c002805c012e01780510d2f000c23bc00b00930490005c00e801500d4010801d005500b6013006000a6014e032c0250067003e000000400010014002c01c0026005000b000c800400000014110952d10e64c389880d320b660bf01ab029c0216038c1fd0037009234b869688f001a00b94021804f0068005004900cd019804c80ec04a601ca17c000308ef002c024c1240017003a0054021003a00aa016c02600a6014e032c03d004a00ce018800f800000040020005000b004c00a001600190008000000282212a5a21cc98713104dfc34bc1b500c30064038c0880047021607e438e02970534043806b80a9024808d0065804a00ce007c01600190000e49937f130826204c39648865958eeb1c421db91b1a5a083003300320186011c088015203a0032c0250067003200100002c710cb2b1dd59b10ea08764c24478000500b800a804b803000bc0190051018901ca34b012400cb00f40188000000100000014110952d0cb221cc21e88ef0028024801a00cd00860330052813203b00920065806200000008000043d044254b432c88734c5634b0105003708a200c8024808102d6011c058024402f806c80d0011a015c092c04e04b7021e018413b000d014412e469580df02e6001803200ba006000bc0150021000a06240f1805c081217e40c50345,
  0x10346170c10c80ef03b0075407285f0004235201910014019a0068071001c0020004c01100120018001c2990459019601e8025006700c4000001180020012000c0040001001400a4007800400a80080000130f0cae9bf86a5001500e200b401b8136041401980b5820500640d9408d0181011a043c0b18017001a03e81b9034800d00214017001d0104023806d81980644010001f8041007c00f402280440020004c009000c000e14c822c80cb00f4012803380620036000001180020012000c00400010014002c014800f004e00100070000261e767159b10ea0876195d31f0d4906900214081002e0066007400b808200e4036c05c81600208004000980120018001c299045900f40000001000900060020000800a001e000098786570006352002e0097000a017805f00a2014604780ae80db006003b004108f5002c351c010800d03ea01840810048003a021412400560206016c0288459019601e80000008000200ac0050019001c0080000130f10e614c802e0097000a017801780a2014603943780021001a07d40308102010a092002b005108b201e8000000800020028007002000004c3c43986591a8e03b0024015d00f804780aa00a3004201cc05f016000a600c006d8d460a600c8800b0d45008000fc020803e007a001402280440020004c00900110018001c39480cb00f4000001180020012000c000802b0052003c00c802000004c3ca960459002e0b6c02383a00064131405c8155034c04dc077818b020e028c027807e00a000bc00a00250034001400e0024004400440038729019601e802500620000000800480030002003c000130f2a5819646a280430346029407781d801ca0624032000611ec00840b000db0a600c8800a001c000e1ca4065807a00c40000001000f00080080000152c566c4c3c32b8d46076601c019f80730926010001f8041007c00f402280440020004c009000c019601280338000004600080048003001000040130029004e0010000152a2a5821d559b0657087623d802e0005068a02f820500a3023c0084082003002ba036c05c88f501d8020803900161a88005c024001d01d2035806a80d401a6034806880550206022002d805100f6021002b806f019601e80000008000200ac005000b00700098014001900400000987952c10e61ca41cc85f902ae17e0011800b004c00a001480002a5821cc98786591a8804780c4802100c80410003015d01b602e41c880ec010401c800b8048003a0154081805b019601e8025006700c40000004002b00140010010000010e64c3d59b065711ea028813b011e0138098804081d10e5006900b40174027c03e447a009f000c350c03300320086020002d0030008e00d0027003c00540058039016b015c149c6a1002102c017bc1b2824402f806c80d0011a0302005c08781630066003408103720690025c6a08d400028009400d000500380040012001300440048008800c000e115c20780cb00f40128031001b0000000800480030010000400780190008026c007002000007ee09870d4d081c113800043c75574acd95312a7a087a350c207044e000c23d013800430100016801802320068013801e002a002c34fc0190408038617bc086801700660050012801a000a007001200220022032c03d004a00c4007c00000020012000c004000100580064002000076744c3876a0ece1da43b287660ec64c7e6dfc10f952d10ea4c406a1004800f803f40be80c603a2050c13102f5023c028813b009c01021ca00b40174027c03e404f8066006000a80b5802102c0025c00280110018032c03d004a00c4006c00000010056001004d80200000a96cece0ed41d9c3b487650ecc1d8c98fcdbf821f2a5a1965cbd0875087623d002c02c108a20128033802700300000ece10ee21d043b087110f021c83b443940148098601c808680050022000000080190000b1dc98808752a5a087c98706571a7e00182fb045800cc1318115806500a634f82fd001611e6004000600cb000000080040001003200100001fb836fea16c43a952c1a8202f805d003000bc0190051018901ca17b8010800d03ea0184003030c04620998204801611e623c800a000500380044065807a009401880000023000400240018008000200a400780190008003801000003f7021d4a96285b36fe54b869f05280286069000301d1014a098817a81d8023c0394051027601380ae807c0d3d0740232069e002102c00d94122017c0364068008d0181015c043c0b18061001a0bcc09f8043038a05e005d004f006801f8028002f11e4047400a00250034001400e002400440044065807a0094018800000020012000c0008004001c00800001fb82a58a16cdbf88750cb223cc1ca85d105821144040833507981740058016b01000168018004e007800a8012801a000a0090011001101960128033801b000000240018001013600600001311043f062c43a952f0cb23b507670ed21d943b307631d9c54b6a0e869e80c601fa050c0d2000603a2029413102f503b0047807280a204ec027015d00f81a76012003e015400e605ac2230409099200840b00043017400d0017811d0028010001f8041007c00f400280450088007000800130024004400600cb00f40128031001b0000008c0010009000600040158029000800800001fb8,
  0x223a800b00170126015400388ed1aa017ec47b8533003e0000004000a0016003c016001900003544003040e11ec025803a006500a6140c38282920bf414c000b0d4f0020004c009000c000e14c42fd85330196000800480030002003c00c8004000054b06a8016d05b40e80019009f0282039c0c382180166001820700461a9c12fc0920043010004b4110005a01b803c0018004f00680138028003c005e00a800a00250034001400e00240044004400385310bf614cc065807a0094019c00000020012000c000800f00080000a9606591a9e00b8264801d07a6012c2918247009e01f8028002f0028009400d0005003800900110011000e14c42fd8533019601e800000020012000c000800a001e000032c952c8bc4353809880a111ee000098885fb1a9a14cc0001fb811ee0018207008e008c012c00e802e010a0d2007d0017008e0e601d0003201ec036c0cc00b902aa05800d30021026e0394077804303160200083805a014600c0027803400fc0138028003c005e00a800b0d4c0028009400d000500380040012001300440048008800c000e14c822c80cb00f4012803380620000008c001000900060020000800a0052003c00c802700080080000130f0a66030c093036a0074038c03c016201c00108097808a02ce0484040852e0e5005d009f00f9013e00c80b5808d06ca09100be01b20340046800b810f0066003408103720690352c06280df02e600180320030017c112405181891a940c8800280970020004c00900110018001c2990459019601e8025006700c4006c00000020012000c0040001004c00a0007800401360038000130f0cae353016b82d302fa0380070807c00f000b4024003a002a04d0093007101f403180618037002e064809c8087011a147818101cf05b2026001903d4043c039c2fb00b3008c02b400e83be005c0214066812901c4025c008001300240030065804a00ce000001180020012000c00400010056002800580280052003c00c000021e04390ece043b2a54195c43a952d50b4352c056801d008c00b805980850bee0d2007d0017011a00c804f8141024a0c1402d023b020e08040eb02f104ca12f047004bb06cc10d408f05f51a9203400b702e5094c00180528043]

set_option maxHeartbeats 0 in
theorem unsat : ¬ LRAT.FormulaSat
    (LRAT.Link.enc2 (4 + 4) 5 (LRAT.Promise.gMask 4 4 383) (LRAT.Promise.repRows 4 4)) :=
  LRAT.checkW_sound _ fk 15 words (by decide +kernel)

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (383 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.and, [9, 1]⟩, ⟨GateOp.or, [10, 0]⟩,
    ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (383 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  LRAT.Promise.rep_lower_mask 4 4 383 5 unsat

end PEqualNP.Outside.L_meta_5536

theorem PEqualNP.Outside.L_meta_5536 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (383 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (383 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_5536.upper, PEqualNP.Outside.L_meta_5536.lower⟩
