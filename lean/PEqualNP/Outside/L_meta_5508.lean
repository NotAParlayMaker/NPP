import Mathlib
import PEqualNP.Defs

-- The LRAT checker, the encoding link and the promise lemma below are copied from
-- PEqualNP/Library/LRAT (Checker.lean, Link.lean, Link2.lean, Promise.lean) and the wire
-- helpers from PEqualNP/MetaComplexity/Helpers/Shannon.lean, renamed into this namespace.
-- Certificate: CaDiCaL LRAT for enc2 8 4, trimmed, 450 steps, 11044 hints.

namespace PEqualNP.Outside.L_meta_5508_aux.LRAT

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

end PEqualNP.Outside.L_meta_5508_aux.LRAT

namespace PEqualNP.Outside.L_meta_5508_aux.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

end PEqualNP.Outside.L_meta_5508_aux.Helpers

namespace PEqualNP.Outside.L_meta_5508_aux.LRAT.Link

open PEqualNP.Outside.L_meta_5508_aux.LRAT

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
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5508_aux.Helpers

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

end PEqualNP.Outside.L_meta_5508_aux.LRAT.Link

namespace PEqualNP.Outside.L_meta_5508_aux.LRAT.Link

open PEqualNP.Outside.L_meta_5508_aux.LRAT

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

end PEqualNP.Outside.L_meta_5508_aux.LRAT.Link

namespace PEqualNP.Outside.L_meta_5508_aux.LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5508_aux.LRAT
  PEqualNP.Outside.L_meta_5508_aux.LRAT.Link PEqualNP.Represents

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

end PEqualNP.Outside.L_meta_5508_aux.LRAT.Promise

namespace PEqualNP.Outside.L_meta_5508_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  refine ⟨⟨[⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [8, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

open LRAT LRAT.Link LRAT.Promise

def gT (r : ℕ) : Bool := [18, 33, 65, 129].contains r

theorem hg : ∀ u v : Fin 4, gT (row44 u v) = (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) u v := by decide

def F : List (List ℕ) := enc2 (4 + 4) 4 gT rows44

def Kw : List Nat := [
11235582092889474423308157832700734813046143682409967644399271814378363599314890268324451537197104002158382254674456540768774425829700350441750854571183848267006966132465672397947709971243953801219072088102736954395340661018273793340733993116520696982750715512696293670427336380108948380497066030420216315905,
11235582092889474423308157442431404585112356118389416079600343402764583739167353852576672053530759684732556079359234943097327637567193289755128036811165148606664924834219648044395354593574486839554382064191781917841953313363685177103243381633265428827131702676014902750894568258306112407029013605532326428672,
11262327753473359442812692252111794217963939129307486744277406451912610892125537443629634095849257462990065909371864962161247158500926646877807732018577329764417338395604947441218096683517843636709391512048563676802594635983421617252993381139153287235532364271644743155906237451230369065405771882710895165440,
11235582092889475349112988525431317218683682966532305612830931543903594582691508202954515020096194430332551548772853276320000192466202709060622068061331933059210776269509157815036164782610040488474993879348017713871885383061231521054258661133032654649892331385156522600176207557698032882493773121437615784015,
11272957443249035388362901481523901382767745616067594820598848810311523985239275756062440196865533562553587221582802831575736841439702382135339806916328846875282161091769036249893482306919647615107001876423383546218355441814174135151606637813908351985775276639777236968988843633012758375499396510950291931136,
11235583589234502036943187008813559301748155408144647081957446833071933103395296529300569989533455638847826813702896959915893751267548594222128242838901528772276625562038699615964432818806875837508351632367787655129366246018459132245626308928334254122606816254486148292506048538281604323459332201967726821376,
11235582092889474423308157442431405903735505833009872111421190709070202700224082470171190375879011874704686086134632717380537161356296335564979392304475034104223570802554266311153869998325889572675466907551949678231733662677211496271940140496041205091481930928083880917047011812365991783632695270322957451264,
11235582092889476070266225369031249164833980991826170952832234667694133906458960964578961030885724732034710531782712047632467203180446526539282173344079703137448969189379322509328778318411172559561930504880174433884552677716324803255841607248497041404669142828993071444856257479092704431744311738526759550976,
11304160726075694630104590569176872008019456730695357508639487525019926941396444758294761406650353055924319946194298890087615344032747556608779791511548226604572409683398189545502894762712425735107318711408803215723651008283818555693285779209895698744437939900056305983204118957879441317027568105565513056426,
11235582092889474423308157442431404585168076374794966560760640756407113262291516217136470667813749254242469716878995493835753553218149365969316594356872298056860815619155322759393683617906032834000590297245587320417452059912865243343490652804789146665473940434797934132911679056419650719985630400895105630208,
11235584468206408571869064011921881672910476925046156536406971077612592529464888210645158677256382005367558627048795023655535566354397169398941777185857274197059820747150662498597805791303907785366045149069992234849118079924086463421040461852394016666757867022433821928817249242867986112247945367080214200320,
11235582092967713741298537240648110001688702831783586473712735683485436523226923550692086423496036328765733066036112222255885757432869503434490068788048886844700900725980718329781057254496799031663385578772988761303089418524765150244348648550554468257681747159492268812157384089874857104531151215048483930112,
11235582092889474423308157442431404585112356118389416079648671553127009930962333459406966021757732331038107982530204551123737646922178486693036455123567734724087809705237168953678298777582871618184419322052496091455882535014166127514224972453076981002472154852173145829607789762632582136977241409186936061952,
11334678222591669910784709516348155284510932982064930282447609208954441705917614263343847886343336399638442145866048428615780092414044153573725110567680627550935234608082431471564152401105700507422816102639400474751112581149124899636593702671917275421673265125521672163737708513696691571774059266811086503936,
11235582092889477561299272026725671879791981809767807934352425418870044317823129040226030808368991487567419288712271319809466962211550096737273383070526949270840298918657131138065159296601871869046327250563419306954554795867183382438466126133624788101184244618603997526053487022043313978839811531212674138402,
11235582092889477756205549341325539728719891751995556144702782368493598533582089800525263906895224883913320425760801421611047973564261844711919554348003328918951941293174218914626405375755350259528866101024008894255504897326934162646393874624143488789600397012176647649928676900630073017983263163631108489539,
11365195718924347236816858136504413935184366356198211069306979367257434645443110048865543405730016865671126975638707803350093299054337736190319012031487736458675355285061062266272140607148378191670774386522079298116520701163540975492591316388089245753603963303672003355299524728697622842959930141975630577664,
11235586330789727454931838927901569324481547053658084198116600649036265631186013154155990356473277501231953251114896222877536459663340824556797294010641180980739560012950431825681873346601266332264860184622660055944547649261165655317028668448505756710499476404271954927016708206693059966085548473538412675451,
11235582092889474423308157442431404585112356118389419122186532371138170595295415309409121086928040652730131845412023511864368979955149746977266449585451697690451197436510578115607803891238969001675930138336371149192474667996197480006139208516874401674025767941771620824442638952157022725400401423426861924352,
11235582092889474423308157442431404585223538674783663026893199997084415748060874225555610399565258819028073681012675619060219344978863872225612786786868668187626778763113364947785985004827319567531062427601765004693419386270105713711473387082591259599525318029651319785476446930409642137932207773791216992256,
11235586707491976456792108964831845990022466720772292026655768534219428975089228085987723591169189480309663608896529812764239095704727056526194857298339877776622205080403113329773583106178006766123026986077655074771460097567316704057728470157045972962475767382269717741430735545708521330627737932923324596224,
11235582092889474423308157442431404585112359629391493040789317432995838907780087278444753726981313333422011197026381657889098717592315310980997982956853839114114953182462429741065068896754023775194992565532084505474292174878793764723267831272301968051625419069274707002851232605829123540527029128845833797632,
11394341642622883282459129019304995103358279926649547260549051774505499061434114009968658339960878604019384153597955096115942979151551188577868932556602237088164511379377532210400341897822624196666497544401842722183092742440185993980776607485041573048320175994210398101130905231617338967831636872887088971776,
11235582092889474423308157442431404585237722887008524140979632579911726509006594508840027364304276911584637419254547203483910393979223348890680167248895347289611873534804514868917835179962092780862335751291603533627760635332977788510674991729566235487620648127729433819198987287193927142391519939709400252416,
11413200769644238811987318619166646684011007896120113983742874648763145631285367296890727149722070504259009360997322320900799490570934228342264920013989150180380444609939452826567250844958751243701787239096323020387931491807232898381498860363734401602508404770843656042869734559266355134530936065031751598567,
11235587890095054471474855061366158829903273493728294913974918812841574158955181568510018304459745962058307437286312929511208355894319473940569835729385245476857403073024735020138930936679445817753151305199432979891946479794271952914603151505727774595055338856157620119570502570313488349475784429703851409927,
11235582092889480134236154401524832642014639988298484595369192949476902567428096732776677785963615084443280071835338199498428016548541416739663517271394987428933168327822177415264766570993105182977521183373265252648234051971317128641354229943923103599393187696151928858167050880795984604605743976214326280747,
11445426338520833015624416006634176253008308640391623627157513848373542299026738244121762822344237381832510486394585493754671592294438400751988002927859395355908706876797774151942321402907585150934526908562222566845966442979422031476153576722664599964940748790143759054158732996361559124845816200590925332480,
11454690848887814795159663712022258934818383492116259672876945899307422931046296998800217474733496328136776640387790292296440997600346918010463135310606970884780833986914935508352127455737678226825472605177487917537411626337597124386990422696231427993868032049388965945986994875324214318775749810409459318784,
11235582092889474423308163468915945779252698512880985730065282948071023572432441032550357493027632811082701311164898928245066602383800002925232515956343332714641227260082052243587949147558486652495867529275320834726377788608613458096901917282748765296280052806202503442531467014302766462609400173201572496000,
11235589156056562809347626584881684847682202238413666153721478962539407724827108318325966271515613599781482931492861798165408782111547916228934501956133848037621548319816654636563754211641849219962398979385290862520914476194413088139938518213421619145790312536261483407213091223623064330227741942290281660416,
11484522559106843723553218969911003547256383127170246399536263792738900996476410680482784121814044874311829491344785781795107162185168897796774910084579374930457662659130666603348385447843266178533900390553842637484018858831241188127911633905325450770656649139515558203436804236373607330881238946288653828096,
11235590275948753515716621616908748008187531716505114982671364532773353603583307153698795051273254005585701838476077770645938549319654839411710716775841093480575664545436584350110730741578137754207545527522376274855002411849851717492168552175304591129425191182563605955312202842998028151172862701891499066071,
11235582092889474423557091660703731658899297219028225456667789744232316280244651192108374901679315695705213666980500304742860634343945989945611994934240640752562777769052295308286778014622298520503859167168713458922628968971472809131307670532657968726274169780960808706674538848743163789247020294405527437312,
11524983958898126354918628148981453213109455192042070235920200140026380037785858975558375254246091821184528714900862827758153451081747839104156870552626716576660571668396325660954940127186284956539111162209900097352377446655293375298382042287298312461053951379561895491351237384248618414571648699294172577792,
11235582092889474423308157442431404585334972417398250088652408438415982815013650102122680491990209668522773570148431767629608487250528614001782366471585549360153131539020000560715793873317183868910493545381708532266082338513216018676538227891459010965034527999762314592148039820124159210357435565794692367181,
11235582092889474423308165338819012800970248046567656357945421067617297004621853790063837618279273566251283767852987390698850695740191513559307951424038662265052488896735119879541755369920838263844993719801476276393582835132117761872304766194490019069804520551811117567377010535321290850382301680014691663872,
11235582092889474423308157442431404585112356118389416079589380072358292238013427967779168153006146373770954690855059560896787785475306708708002357061631142572136870098248295209949853737968922907683673537105635936768043294309921624863411822371191957493693572351839164465095576606977572976940388921572105125888,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084973332775108034685847425133952609808781769437413371741899005278572759665310832012842822224098126934306769217221240714601530447823158867282255174816103213617310522325183904951329023219204096,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773613259292584604643685246068556744694565976266638288170948616177131377240074329365715632476557604302611079902787153441533178325102094512979528822816768,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882467914996964952714152865190331737430316152459570849247866020728818516085804717369607530390579074330948360376156160,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930093708013341577746621107848984168157495376234262595152355192254694543190917120,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423577902309629274432703924655553808041197190672939306392892349885190818629555012970521836978353871707717484760047825971954909214120947082449210463269842215184192988738299846097339964834605511400719902952380806587946556846513442235980441093379236037358898283225978725690710526504115890028544,
11235582092889474423308165692795021447613121894119056213464053960641189567251729353734706465619305351225759299014414778900756230642306086559770872691536193894772001914066317725397200599398254534092563729610275347777502344793913376984617087673332317597606576898429826287278083584410647918655109873290430119936,
11235582092889474423308165720023952881630947063832073861648140259970972217255709944561827790830308147672740181171555448585379303769586030942074747231732563223697678785111658175443434122940359903687384162766157382934588022029606119759565460596196131000279228008401232601903644620861995940979773162890169679872,
11235582092889474423580587244886006506143141442432098227293314719755762130646312503820100323467287630261521995353231268954836061414118600472401759641461371337662852315642440741111452450273299827680946552641901306854516999632113084342997481121393851038915675233580559054521217413399196311949864276418927525888,
11235582093183590417283406281704846208808666660829045834633111340972901555706408916468859834560711453469095612310332472894776421585942656020188699557568809177643153476444194108953787894544906249135858095303981170318319227899408395388860730813330030778965007643861989263992752706225631836900340485869975633920,
11553101202820882081799666846737713823551852208199013882998246725163140829981385380922620189280844088740866767053348448861509055060288092743552786521173425662066700779072173784035637719742616343129345110324326021444972789666714377846024383946604438828846746655128862925598212819263708621641367363149147144192,
11554129882180560598027301336117969029622458753544343191808575646800924804628632026022667941315109083267892743183615599667259098359935801611279934048131199075965276235566113502962816968786035889545412833328336202359064295467535434234251543193004882381372045776822117068985751571454886422014956791919517107103,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982270129071283924225852322,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786684671134218406357274665059134843382401073152,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
95268205270873786358080970147496530326800480428008152797215483387004752771599292606210513399154418065180265231976520474104247304665780191232]

noncomputable def K : List Nat := unpack 15 Kw

def Pw : List Nat := [
15501735664421386285319592621370336697388279536374593173065275739313386829676501814252393615690931808162027101066682358420354494394100474491955684339402793237037958665190478173251401725035742706359650123229732141137135075989645299431304339169564791120585014202462834256633627514363656254897772514622652842926,
14014994455036711228970175834827722594529518805733699953361290467317430974030755067947382874120103937026318745984555817518505828417892323323506513586739251871079636309057138035263509789801723548864966262772117039348144157100719837611720041703153271636851241794640735496632813046408903083319785458082576663137,
11559956384012994544874652311898420587904822605754859772132870245908899854615427921466534391367889002896741328517815888739781675422047560826413531772474793078509120261303501987712542431356866933812541903870137792055684251848924399455059854910090933440000569446060864454069172366773975458152640029111467606666,
11235684169039450198036923041473675560909232647331982498468262943362088807872990165537284870495021697843247756282011954948504176698035924206399926899990219990381524910905272528869647411026526566983837986397058870792132723670072935911702444846332745031423401412390559800520469864012241520591387357150456060239,
11470113903015970604119506461128911366641141535773599899744085762663410215136634208214445254265245280740037442182584650224760369699708805405275440422320777341635773743120450152348723954765931185512505118268294580652885877500348255261973776629875765928636370251165852072244264226934397548444135231588897260468,
15861758938844160013649186126477997672430127308405985544859888280567381382240409372538742442545987956346981904694296486203863127988845685051366013119972186745688663050349855418250370196083814033948252368882025565652498684669652300552129044177547653900273247910671124684260431171471920154252244267154776558769,
14048266267857869997284702686756310804668115105714309511129055067865698101708128519575809047999266888106420975608783451708417812087557813801179102023618038443316742966861723483911848732862556387892777357948000777956034174933368707643558985763773050270714308788929731459923999936268804404995982074099936625096,
11399137198227990130144130705981735743554876538946672983448058297749914001653636015081314943740108074831872119050795804794519661363377254097523759966149612351716992051874057346731343991370450436098104803131276809713449612992966176975692852202799976228207661554936791463148903098797534029589650252547050545099,
18062044717815319548010529526491512556288854866186515626194736206587664874944168326401854874534966080055304685200888851003804161831120116865069091607080149653751232810374992082997073026821001955151498236876368267528941945735858746166601612542138895730861284950569774261395965660605674063717037836074051698693,
11370745547661205094855664304976470264116048000640052108584439281466991110412792757589457986186350462582634225907018077332315038446652122994410339340481089365760856293801600773211388321736438547204540278002541678850394590675595974014632476163301845730716916571966184288880967726436371525314780377324387139980,
11274024420966728060055612221455479898185194744589951285846658488296525942385518223300878169317806261928585575528994692140809994524200182329451535335802333201410042572748404432117523652463331474824401400673282912365043523687819112469600301203500056599549645734981211726946996960603177995338562210895545899325,
13452323454507196908598997006684535635895300864516256461132643817989341949617824143878916793427709902277930466467656396300911164670841675566413248835877700364875245754596236273024886492887738259002678867331050342855891233808332743583038196778606717596795838520188272150275448426022070541336845454107892813501,
13083776499126393201907777743860522428013412362926459814571021503851268641494517001263732200466608764901391455638018330574601662730743863168474603407014467129214833971532894610185118238351816244693176970625987301984665404757104849734807701909680613570917460665096849586864194649624145133873357516771006874160,
11485229032545049450442588162232435492555698476404779819633783942957263955140131063256827301147239482296768036435569790521326896210824663775743811770155679201385158638020689905108897094260087126101867979313960894493452624997435622530117343231174494852745402443461307376478448632039016341326602677276224014736,
11341594862978532476721425965376168393482594757668535924303158775298595132912602811840203997156496181477432497751356555399320654684303350712463338966342994246838542203796323981522061448966137844230326450537757561292069669155757285590584837803349477511623785542766984155884399496653952093305780930452694799633,
11304546615733506086442223272749565668671921172432121884656512749316842856611377523929471122789238163676623856129765953632765129039269112421497994931064329895872067958094710588414154492809082144869150149397252812517073450832415178701581023656906166396573171683261505878276766909468003838786136594360197191457,
11439064015681049644407867430433208359006562709678044096307609872147697240941681497719831583317918758504655809216585178361458594039688425318703769960439381134969346874608062398408278894224315568993154524351471079493442990160723943537055936297794576531704393452952431148417236280026608939749801989018944442589,
14199553441028999985634824789042435884997737515754247858162467062345072625300490445626325944298632607248464994878552892585131368298217975520895308869372945349614588519107497860320691963897195754597168897475801543788745138447565310610136514353151036885931636668474995938939834237165848461888112830010083326193,
13636798823668275275036964206998511312438744711903801894192283210650542794287322241237134079693221330739485798453730231776168020235368224638465582299602314492010318740684629833692181287801961096971650698772302476671775742415095777510217660232310300601517369678941367728152873236311837529375656133338717178794,
12344129774950585948077879298056407717918792504728553313473125220634143857327167253582571607173666796649942426339293560561848792761447405975395346746945250195946444320535589978233866495563031618471374698721419626700184170104229713504126493135240122218151258985220029632961934083514476969228089401540116120394,
14646246887972446184586002206937247024137815609362034008749985453849741307858121001102644520580228827794994604440060550882642822502550591036157125913634756872768138968391480675890638791524503254310037484461069098085506785174281546660615310538049305469912017619662161368436438865170373171062298790635081138917,
14199896334243750977649898975378083042182234846287582929200818162077978558124864772222951741931072198790022898165068842922210591834938038191989702675281073779365551266756520046417591150369229348714767236420321759299990303236559992650034834887725705857492371594618825320389087770724847372628269960824946131904,
15317264260228916909950660286397660104779033282121425983513363170194904055367193121058450704361869140106219154290727260586175140063992749055912168461463877868289372885901794269775743292881580923468959479203303979149645139963665577083269212534144211616725169325992228612005209489778962069993930996892123008714,
11297346140669896444987989720064469359084305265885831013153826790808036951676832923265604393267510476188250002967327574232876051736273875022790443692441153200402461843818339038965687613920515593840671667777857461694999272414651993161023565635360512533708598311384643946786529412026976174520659779781251826227,
12349615325137376840678018562612691223700444637430823809384952269485014742644821132338240364500997636455968604042293770763858354543085574335534190277576582179942231796061782128726111678213771741987239054266844390734392362545679810782012945808154375805482621210314389354131255912914027618405168827977682292959,
12162403397364883340140186512901955355040959626021613689844730987715327440684559123026811405146146712372899565654857133655702227120163932321583669230853751211866665071584826853773286778795847827842651131591737638676528805259484253444440584105455925367337008006833476806232494872746546708808654848750416790252,
12716494856762785254707720187614665598230191841788973010092896253477811181845002646317594045075063436683624911112347615279360204410853412388028665428977982265854157633289635266627012644822994480902047344996202308377082264389371897854667076112681295205980910378194023880182930748556415668356059418788234822519,
11533232524245767457519819879505537156823470782120881030225770251310837955622807804663925780507800942967242785228058754909180369341230675543902378811291477818164721127706759438095843571234798196081346725727705449950523341597225851581486107428550541353274017037418454900304363925092580070701445467464315994550,
15502764452156159645448843708082387824793591548673681796453955139117040683212820902662065477682284929315763888154197680325848828674912979512964220515243029903804979732340749437513093100068906766602657935923251776209466245362943500625461276727716655426133318998110797943109543763931613266235357199346626169481,
11422460341898982059817156687101755726432960007585683409487201243527604439644639054330105362790329210081031393294838886427823169882818484900675572901636970995747613110334136468525402979706125919129459777101267642742607117361736866322118549001827889907662655879232092741093656242597438105131334363179878613614,
12717871574958412473718475421966896317001309689172583111685628576103046235434371929596267078788256203354016263544398054414021171280761472838906341235690405174403143317282832036657946884607361442549070889582006604048020094750438478202935988837047653188012364664933091205813480575565920467870311895339930779918,
12715808890876925861710911547210452003570631066549182652319867909064107466735768893962137724756590157628342607986109165074309928989913040273818200243068089572775286257496707983550148536902726679668794654810474856442302202665894560751073647478399883695315009913323485012296276969456410691452259694378284876254,
11369801657393227359739887729401672505207312112870386568720979177201846797101544273581566362182124043328719073242718136821876869908106458414150504617480382726929244013868822847532606186620590009269191996951700516052285701288410820667007617363018449239158549878987835795290407571874680267853973468972191416511,
11384460836899942239189244567313678999262016525952536958187370660227785529324398032693430756040304093251479260023440634270407475673384437594311695857622909618480415934589741540603501228434384980026262508743122151041677594935247592179014173400285497968783896178233327040565119293319857986493385174205239572805,
14569098236862223168986815225191709253518206876850972238263217327102149682146602516325247083290159200982487098574388106622529117971472293319292016689289688856580028783811138294840605524052208966546912028029657428643115605071820847228718762570298459097637633027205001998525008672666253974732335479825399096288,
12718207199358187740813142751839230759405345709988970829655374249577337450443472725080492530174102871940087428193293068892128166476274336702387653442094789057951287417931424353368385230382501340768706973906474865566117636146503887838361398437659843821349108407870200179993086745477388626308639314004680147894,
12349615323440429456704157319190329645077555999631565361996816773422915439830912639189350254796589283350988930699822715356981978137578599144041207422888148610900391917955899188698665783869422902530991970574742697417915094302476637025528792420267955993827750855916255951667363614598450870690290449565705338935,
11421424559016318114056231535886667149284020048858335225660017808511450162979968989451207796537088470266306208375444049283129980163990438472725091602183096228729486554145987268833240530989243811420034877620593321660144126060146986884373411794041760031420058275961710661460171840628446082652181077553163829931,
11411914279152104915122311082056372270116571228338685469120361038551347581408422499861559740072083123719514872273471337279843378696996269461740081017014277757800384324049556765075777138384846725692922348166902895180877881036252668952707258252728261494798837322599996760527316388133077945760178449960404255248,
11235649869797296236977005021622719302675428053834079391009321827775259567485759180072583847958964271326418949200853766417688362616445452658101854080955933328848650543330650447325548375350288908903479273112213411319582691137190061330961313347913266153646106390175068482091524585405951264729173324175643910599,
12344815568334212831907144136854294435927795459684441014760874676790794039025621599085304982189736528596340510369411960323139869330975985269924811378722543611368044563782062069549234430416530154522361000846569635158689807373221835536575668068173281941041508382128464863234648196857538848858677085087274795951,
15339208833208870569407982569917581300099828473967230063344266086801105346430793324514657871026321530633370679221893456978803666189496793140608860780668751094411596163358022090761416784984490137320166348032686346562298779542248810922289749400150588519569645570985440875791380832693283817206584299798456107328,
11237724244184445159803996386980806736859097948855621064661706691578599675273898803769805757420769707091961353831746452715339890316277513484689159151924748415539718109227275439836323213256635480491757897369132130809318596336241057659975143733782976676564101929932712798695223417912989600335533369629120332212,
13641257849007864139447344273818808645892122277010618891722689316317062616908147026942388703276893889252433655172594988476676884995833546825484464373729297340506581854559270829050485461599424298112232798417705660318755263805700092465842543491827663557691621830177575193205852959963500263714197557884911747072,
16239959661675954435515555072627784942939838910071528765055771934731650659585616416664566425421346857489937344732759820861144283167572327749601447131133056792344681493060829182073518483054168675905794297133625243265553222321672253263191703211113010463464282003021814362677265191759694535192215226339508978608,
11606933996006379863336125323330006036912196903493955378916324652242877663627974350504629573213473931586726108035526036182237234457905326175049482485864330970275968748518462429229655894655424296015615822350763695045052168372384806687183811896786874381663961018976201748378549924212460023898009111196574318976,
11447299092996802109034384802793685528414726117747189770514033419010627026738654246999226889264818545978886202528841285482886943180207522356545085873583398687599521158116065174973769767338079455373168262974892637781153533994318714504494634974477013567815462801352006864775304945679554845365988404981452407729,
11559679711100348232796559326302247863129802777647016441883311390897603037033692328327964575350620588247954229017415003537492708190168254377372634460108330627195234384644211447692778287312169582568128629212735990933737252332492836141676370174404022383974680072694384313284012439185499296730962370962092571390,
11432150995779777174432766204343021496725512300958641624548331324997808228917189249524319812705482108107929833528380609118056488939314481480194754166274946172359975499411316234720318774305198689830427511787828874203472300493870506553407423940614143284094622305231840617414024246296098172974759863537077522125,
11386610885961980729658946047986748830951288636055762313460104738423983922112841769650881295923687939268321802051226089078199864196516154739850297274570276195456659076806830733841976956177127729375859345264749941255115488793264258110165893790501385014417225899296693737780358567448191901296824230874598583906,
11288768463126551981067910466395630053405063047250258121779603408855548050578936259657890546884398702248741395845963144648446156107934433862619549715272498489318731990849225028046859383099156475848773508956149471847362039393601717115490043569527800138247198148680912401123371692301015172140444309685986010305,
12347910690354949029897239851044782466959699328910074602888589503820927247940279506387360408336632395889601714378136417885924340210510920940200934273248306549962602972182092891826860986394051305754697546228941875415986596106299440600696104059397655205742015038178143677850121572824729564115845873622011776709,
11405342854831971919993298647854599977050546821357061218182358115324325341441842903990201731903057917279716428983077676697293513412045432118067978186219513949762586821858089754961228659952005388880434404083329198581419766655067714973921660104427980561804922052453143497820310172546638765598828442262422424746,
11421086896149864081385911116880061020416884369923969258514216050557657862106944798357178931348040871168565758065090302612726205551483092790323430957484522301931691201004242083087800600406264296015978049133009967172884394010650526892126681403970875079548468064625736425933951064152479094207190353787682925639,
15339547038577279936074855832171893943143672530090477652113132053119702101459831692472277922278894441260661552565905240021208434195666805134057987899796725552355918863645697929556534206555388383095647211658744653381122041787201568741183228724741630562652608911990409457683178139224380609043390683702095511558,
15502074111849462138495889973598102967855849645191752137617071799083261623342442798287703974323238438933502169497590379373577009191351160693558814045284695191810181816896395097460448100596819950642721276635108901349765925870695814233985679899737205415085670040593673263688370927112508902340797344260410016304,
12528975396170603486469787652925064980476169871235098178948604076645566740612970672407700532889157484226810338605144062158463465611851962831079794133791073257552364851976135207245653891126807103429262741647539026688712449173654912800827544875885933758170418282946380770330893661421460539733207897952164610408,
12531346727215301897596489206676695072498444347438667063022471959384164767386675278760288969673176261035651223141431295285878985027463862664716317596132954385911973453899243494421451311488475912218118584308453522137988028677184526505681267887422348877714648431361177211936532947200174347515187717037195467085,
11451351582446389274262407388484594971001248244783682390147370063436768322520481620381958483619889854502406585075488528759564544427521587284851654277282321904692530421363874969986055451917389796494932292239093186441206471580194781975800501568487280609204815936636837305365954262218656589436204778175273796608,
11407029120573272529804767452375380134660757352084521606808194732666063245915146089240780254605268862084911637718179757777359476330487835395403739062771730731789558381533860298109007672401697815106559854098121308920370678109865734586416918628522411067141081811666840521324981167304073862061239847391695026947,
11346822914620797265743350432484664863300346984608804630472735727432421522488021857428851506625248915155257309678373085007413951798076982660106419690576464579524801835754594011890309299434663043172648739552554476841903857631209437372132684276010901682210986599772150227697200161591930774204010673028284064229,
11307975568846520117415546578903168202166910761910835631207944382615525568964823617868490339773753408107526424659642151911221336951650489296527296833923484634092764304745362967695693932824579732912693380002530265706460403421296242602922457364349521346481270013060677282850998754180779313736170797468467115758,
11433892919325819497291032228839074037965574063431893427731768265917506498297983708103821449756023718416415477449308272201819620231413767645912916758923401157209635863844943193416817227679118967526649487389834160331049900252273863330219027768310342822503951208004114887172629398313514956317849473892669526231,
11574795851341916402568962659331472960651928104195527691870567344189010256652783186210201920034000746696151339631945402998078591135058637030603107434105921458949985326083722867588422604696235809082742816933714742492943382289266163496671188496054081547891876692162194749346488034343700743872973963561277861571,
11426664024136712406181212237697418023665480795892724954258475629246789930516584200844844195344693469477640834807491233380210267379476281799355430278624813412393937742737768545959799181530121325657265272444276839544391876109532879770134095664309433701937013542843095264831036360871903892986788784285220805480,
11300197441877332533328454805170772532373979002134030386555156374670665614239099413941016495103589902620996420454294024534451487407905602094602790675885450987850640372980628573653944193782578495910311542016439238837715224801303176743712237579222009347353232678318553790321738601502638892991169264582240743009,
11443374745066599393039739087128717215216019025761743896116800616083714075201133533646958959074765616904084234556006305378622753909051211047880603771724032701413930207367169988721981647012743889988820737180934187744893824317445978031748620515314306616101446568806543673364139866716905117073829961524642328795,
12719246131438005329810608371146262492244713886404697869304239718761685630923166529406353724410365178531536699329131980843261721482647772708117486838077155784657074496978470586109843677223622875872273287701708505796698454201950402679563794149018263454430524006294595923405209082779995890426113243550514720922,
11589784451020322123831367066153309458423952394645679861859395514932612262282711372902350970684821999697415036821833721274682847184723967996318139341873621681113713654294762332582196262846050399893380165917839798762277357813105023242751755856158915886348705211802855156373149974906847053926842710802261869497,
12527908254505125928704128886975358294966461815823490057695588730492022190965319654287421208059177002652736907892886630511291287506691154413535244139815291410532982934473864202500897331092813140460071553143635088725605649537291215615442674840398476834246887365578948827260457014033339993267835369484823017730,
11422460345350344836925826307081805020360411255126416810804105436127913792568155625021353959801416410153193077758678140956984276124903592942922104789626644029511923788487000729844703252141494249797456320679273747550578547746171385578309383418438173235479563069944446405863855133351389475050870630446629159017,
16429233893089876396526335128547903459198128935512144561471772104614925180880868721468750774599325952915251750815746527871752229564640579467851640069402127367511304282425140635883116849492326612678025060119215557185828712135019250343828822734248817389989035122407873872572150356065426585236994210453915009860,
12532023514655004395886770898210494136008768373119123714297986731033632350236808233513531521789812356783103030152245567491319965583930759209713001781396272706900874789751968296022779621268325652434112422799804762558439742117324813287172409878859221472181794787359007131316135887992929554051454518451841171904,
11589476743539705092937255235336298890063321827151392841776250042829950410367235673150684545463355932570769542575142092926057295118821561589931545040740391191165992058160026527636832055663971594976159711228285351689769650175768317406677454223101070026466097066294893243259645546221597177335160661081642632193,
11271624220755453970246897235393340220888168829989740208770504356058021224841810758748530937568303878140115359355427937353723009693282340296331616308838282942295413109297558956897263452736998997117736846059904639492379254517751188855482789405742249333284553898729442644480264515820422897104599881485664784610,
11448637536852322234057136792787411760505913582331625612152247312795774972877913055175721806804347527237354924049265249004089317758672764858299439909065973935888802106857211463918609632429618359950497997716861911736033893491992544101958095903474611313733754424405268783788964168889264261409753501068006133441,
14938035002338927418367046680705559884448082475331709893031876759670553388233209878274927920215753197941522509945845886630744793512168145303302529119023265685036117729132998478400162353264475052183000623701988197369019172658767081147755163581754775944737435728474164950886717015529615351822815108734709218143,
12530651523223950921370130935716659863417890766946430145679474709474645870245037437514169670070117906977671687988149362767274507825125790498982087941625009366261149305095044212713676076005260982601686846353270130103597047502967936939042923266135555482413629001662224413753572539636147743045062316241849811403,
11593551741731066505978108041646675577811501840898578956104958030865898201266385382425160786131003545712330272464865172401229816371022743845013996227478255341109989805355044806126721026209418091235314433042186589264031973911986708966749913472119223300312478178001054030869820161005680096588991056038674268280,
11359222581860413255354771768720098996368503410286796925158919005820202994556281503365431222188760492073774396180243178877768963448312783114362726329308989354225228040362237182018023064731418035653354132938149066670381684234132376493412773917933772150308888201300912746336022455364718661640977796627160080868,
11247954093331963088453318486675706458138711436204104836951842675635738451020222673227409067364045079366202640989288366602704186931529970063172252954987294899511178829443333965912682982218896826211733101120897419686738701450244020312753132181530314770594616480212154593194202452583834355712477639413728688387,
11408057789764073811039561021913034518953942494290464625413351985592595932020901222796375082769314578085686027974523225368211014939965057824889359079584001326598500477995054971062627397538095551688712115646252791443339206862766313253733120229151028004927882065027492675489063608609300660640144145030540855947,
11476027745433198323221107481290774605262243171177245713179213841229989873529731844932162969855694868032024983517790404384483056385702838472872635607403893749442249105857833628759788747307584760471628223391831087014696452547429818452570502206554344795809878701766653805198017603049091709498733562528494496870,
11582321388793727379084255145823264472339456379757762816744690347458473256084220668859942126559723888916434965227005345482987056657626125981024225145066605865615981433604298899668538515709964802412412142451100160867099682554056349412272969808742603208050832157996995522586401077493975272531292564317254437265,
11236953623907635284546946918254943661429913277342560670036380480175841443182555672398121366026388881601913010322269176245860975884109031440998347698370401992595384909648507162900437794763220063540240032964460955777735980557733470922060373457662148943680376011353224930003537351773584266608709294968619140119,
12346556141986227597581974564789879047113023443911047555850693650021301065768609177393923107433448427151144331668450073848130478037937419076712523357722293117768996088210278200508577084045951269919424538564337582417807465641197105067326050661938213372714256649618669576770694133151641073529094501618880610775,
13086813200558876130479397194849851925624710327424289355727976199537573282803776176134965094159119207795610673442381943237567506765352357727729447193764434154518440221771280943619590815779245466094501509765083618749879057126784610204714729387497725722010833330393718704113808146648750403873336711242455649446,
11443408669245357949583902201544111940358315022943489599318350749363819572065334834613133117236714850783138312331349648289271507402986379978531774830133750854579667174708215274313241264993263383006004495087601730486757916126227819770434419513887290125621200423430617850872433304164405628040999771562425156262,
13456495808395968432883452880281230450287249433389761405786239183318260207378219100916264222828441970911517633742609840782098273566721780984831137870199741546142672716463792009068738706958444004908504563495310516786194157892508599697247301028468425080873360545593635461753959468903378120584559072215221383322,
11432863915282855719843298722792478548460558030070144586951453133146396718680862530418019822548877256719332535436325304143635798881580025488066609030627605716465939601808626957248923330590164490379939857537363886331706301654566520921726618471664366138399252733377404976154120955002984113125967986225147510784,
11562451078111044699910923242755890175140821828951985661559662672096000540200259584935440784221625434413602686099490510296639125802203165802992785660391096241682234335010322045569243967644693391919594677120186480891359816426207635012950305408513119982639490477092772227378389253585927373160745933561990819459,
11407063034275731410681299463703892494025609082051846137424899125194204584366442704032858717335880829279693441366052101947865771635792478308142168235836425491682589714234023436927341378170865469139235723494203132776042940604562435009651785293750122735499757213390194484322435113542596278807113835682865260056,
11493121018134653235450325413943719237568708870778346687186737816315078418178174061618051232925471278652890412839243150711368177023272626708762414339075282383650544273679124084187811772581142378484499884752045647714971448087372101648603970771911369269513529143818462688702198034314006124448872151640822546973,
11533232524245830723850625185249117557720158690401213001939171929150345478373679074230201302474813515729081954613204504061668723889988284741963018291636011349866539781312409327708263713684486538482205222509732522170995532931669139426294218867483121468120213091458118975281444569722048844893652983173724376231,
11606249395769940901805168809559759614415363218321306601689948390683225360724740759692665871398163702977237376778289877997522547881599514584253717126762226870993875873416797221280465310632796567357136624014953206186244074301867938507285578484182076568394683896187203545781778165290220928853159513687655156361,
14384278852047206793052634718974337619623131311789486344889573783084545846090833310817418138464135409394148604836287238240654647320339002105716144719383548883674097129966921282602545544605538077912364133563177889843251120518220084409293345418417576019082621979608831375746561738851568418085657011253271003138,
15491449279438804525531126301769346210710130392088742633211727010609301677229919295221636398122482005078847681314073345254696130697581135981235412615538841944851823086509504323888638645673926950262272644125616101272886767578205288861910215647162125043396446876347504873692290534628423851885023064333908705389,
12531337299197778653834552995448083111795571594985287211812409796107556053237467208011768505971711608950146925260138951559337099069169478748498691009227259599767455915008112671486404685709895068028663495897656332962679603416379521792696312957420847762494497781212865734424835253225480141857197539215106048616,
11442357324406219969782625521189168678690269484485738500263845628611161005930693345539566428850418952588204551062399098968097320726332642652713390332759556211592487376822272779987813200107680667427830140502935927212144597395108987752598997600222108522546731055343975400837912067917748513033535521096671723652,
11362578914984533116140537815853815033389230167058389237385746958670317503711089345085077249909353328154155077735644133443253660986287933485165795015622256401953442517527149417392493848494269097527520124112395793513732527627415154575213916003890411437708484514213671662512658213610655462108358418945901736059,
11567891976895695534546497133813805366708008945203339776429005206159270201246071428970023509114854606713473261550796192888874135438635582650710715866058917416260011258246743501032078450355304467716617133029121814029905234974836007808115912808483345267421653694948171130015760898293850154742813431265247508803,
15495906995028147705037377666760785655483499998682631879694941662168238666090316988544107648408277981032370333356077097619021802484767948775133319836132828099559794911893116355470387208863648442491796505809001035367159868960061788340270205198365423881171907862657042309739328217436536552208235554213946856711,
14210443354588041149453023522427104499663207154488618498528430194487193024559907321590977981386301190208055912467483109454829228658335026797510409075422190607172514724646842443446076676692968416261887510597688422415599179802864899776566457823979006484875128728874152877587135529645454073498436445495561126892,
12718207197104002821077251239400252852265072233413915577591298576435492792310707501750719689387685980026059415464258305312698707786439550091502004831434038512429230469458625495168269157216836288375362632563807164224137235296089291213213533103237173971313092228335770161572655739069460892982980045775518630249,
11559022731914036434152727368071221683326897377114182929138845196026908119804007514409633459045770737435245710665848821761587510265499553196743499518936564834629556586837598103987152136975712556415408951076855930703885038901233548239141396384275577889216772363823587462322736234104758598746630783353840861372,
11293574493165969389951436418864573242446224134542118337753794967480023298732873363676283559885636290498780397654537340813593366293238555960810345146414614649187380809484702886863839256438479682811128953257896549569268160070344482116591315388263474904491608096871323290286730644316209389996712403509469629893,
11280626305839058928011080067190343670763149769395675804974853783633945623074353382354856180217147356227528427430462402871436062682505001317491610130312562114307503786333655371223015476770011073587908557058739311014611434106228373647335389936336627682646950735933594274340732503696826123553397998619367575771,
11298825241164024574486395511969685025092772281560579768147476202056972516160688132508427074645391855437083263148303072551466351896019928528421241103724445254764610653952564412303437289359630871833374624927189281022857735975461611306674722334748909485654989600711228111910556480974607022145615194847774379717,
15491106266781160941045706809976218026645238192675787638755985993277391910423179351838533598152082900045642397081428983503258357452940638476065651913129566531022997097330146292897704440769515970353231333925343781808189660167519508976988666124023755260297136601337355793862377581278772320232865152232174432411,
14277297206502979135906244899428266783760136570370270642369770001435066603931381053206591884585900916979778417755889666451383004918548972022560084426573550305710079050559340063189340463174112202575512541131004964663509248778273474071702110595249656550464469656526549731835052563320137081172830544811519803996,
15311435612629302909877021078351451258813467304167947574588388458576633786931374763573143851526807715904777231410110708176170243103376618739746568732891339935637726579303959459713022677142146281946354283810942498798846195891200095638716204214330108010758309977661918462856406698156856068439152285657545146596,
14601329194839441648214773435145547418610365561806651688148902080331828002628920220615509990931312383879636740523480068227877333202232352160859632829692378334449054699011368011779634847107267167180130439704582948822630929093455712816437922288325149154723625648722093996684123730250059472655188947614380917309,
11563482059836108360643798487662215488875055975024514819008339588480026759173269725337201357823748934663888960639066634250893640309808228837353420316126917016675826579507284831459946862130693087221549505584087388181088502993683338015579698554908263991723643942791071026685868360780230846412618957638771934173,
11280539318869905736702653451049462348375364413085279827236391855338128176974764900727272479711145772845997575207581064664526601229154301351519891148771611324100293130675848010149452783732120701513525776746994599131457908415666087752905500732107700027625596744324299782471674184738282123401093887180546156026,
11359174615003922602976875545200866255652438671548607619252116255932225360653645459982248712228121377217621059666343717211231946940242378348806142515120938165597153716622393250606489122676935367320082183258318949978781528058382974064499453280664458246279729039102861866278849826148252587517018008534242168517,
11318015070840957674542104176055343192038388710634604820715152476019106305178611634275127771476427295779692016906943583315340722056413222756012313841316138651523553043618204915020030625287637758117730844305689815116014865961134189372259151277450303382807898371153813687379726912877455729489610048913209178371,
14016103232797716500993122044802941533015203504843755910479575902940009218090021405191427463598090769549351187084084658640343320383645798626857986153608701442679887986783885436100074517727908117172690033407164490376068603577268320343025943825070573022043300878830083102578977695066055572997022865691911566607,
11566222851194683628284729215528625034550681655742360188435173015461379602586076616953822219943169616024578313930504020505417056326206814608506575104829983611573047248801460534294477025473226375336320097307367135960719800930845375320899143938688209016819825998199101242907236554864059940170055803759683960838,
11449013538164012071827094531402347237416603028313363002729656948828938540851719590653786865926279687405597056137809168021447753976183300968870905273327053526055770015037512763368967130109530568693912736317145176845111648600795535939693745332147013253850993262001921118700235583710045395738116938801665058311,
11605609017212092310705232432934578615442074832997269238387152313825361844545820614400084801152040720572289182410725095081160499719810064529847433079056136948168794490963546565996430201866699743459969187641936659139016095562445054244921148032238474457014147509491309573573693910634203964964778343610736750813,
16121321518887641049443570446304858436105418894349362746577725499595045985902030506337186754096262640933913972965437743698785893583378403970063792077394914579490095350713234680783223068052476926730491701968268915522886537746031735945400518168137881098862270763737227561193419214109064181135205460828957185291,
13085102533762639697913675360331925613465403228370344263596799815522004016015437105662232973954320532220750588254036262363530320547547937951511023331568822629316403116127989436190214470091816908023857234524364578646211729421147262233410428513541291747202351923338217708592591768472399655553846541293420118313,
12534087831459362902169013934194842706630954690731364010798814910646872393040339781702565644742017099168049871145996924917459520451817440193325955192152033341064416499580687965287108383233512164895272944177065796456751120361004472285668816911541932214137210272082284448636511178164397336845069850243215360235,
12161717624837306831134404569175261051539845085832960059035748849074734501877006747652394952838227947692134239426865304577876343845195125987017245827002098211518755007887109770424611486425418372223385873471685511772586001073343424578441803140950254377678622236283292703515888956064222251747573052669708895219,
11585704844914703943750490363172221432231468906389408298389206017541946074007050197662271180433406663853145558743523428086012002405630390907633732491527088346313142388708834946758627116476009191274175095096554277553490900162511569181791926580106335992043024352747358078906807677726013233934593706653598712264,
12532023294911389076195403298428162317193247647402714568663593234236281214469728794136704677845511059096197517298775524265237999704209483720986588339210319204055124582276644734016085396486459973816510225717938617498477081890208275441284255008366116245811799265507514283813913635264733694966321444563458133693,
11385175064363583862288982821974582144369587217123289925357226937059859569086158156379242156488577561267596070302602847109627076691339563900043094030342525133246324761090084456432344642842843042742739524311303374701513623602690592712133594277150697288487800737433293746952352760270235746948210024529715757203,
16044889508933079920177036627085201815969222784678205264969275317253796256355229541514171575343269039329954452727232446692780913269193259157237276387215456685337436483689588935700509960666232913885724648067297699878940530126703867418225991304273492290937927896265732568972238754484027785889402468797614072833,
11411177690341195028569773576068523377357802610461855360022660745975827044627599340834188595863164303426919710931209789063124145600478175946550130114577756146836396588145303936894846934888409166912582381903137695210891121141062265889639782746864536209165200875815023303190812211446563489589178591633097570088,
11559617628463316898755735459202000343344706566040209288930704447115836599193951632599008182696248618426816099286161087483232660777855985127642898381393954915781648484966950924631999611011389430944075066631142549708311032485880472228393547853475970657440728896990560427127148582234650526252075887549298541085,
11272995835485539510442498750821357550960070461783847506770263696320595515575564377825331448971484643801003308675552783112400513491582499998006167285185061160888816823277914465143629020997642126376619550202666846021357001838646100724842842853953213621061523613060807277119345160890281025382022076123102187213,
17693100342084226427348673271014588849878117696073627056593138438668549881944156768838890579083975887745059081813041791506273381772367811298583116482349998475278620904513169471586648503284013995431156011155553251232148792132322040990054373640083559906389259585938440587574276562133083405454164797781207748297,
13271081204055797059394910686530815050524844804237224160464293673619955695568456943263471391075927196607874232898982882575382285126932460273663529031353836479281957488872043965417882165088006373536217383506692615099278879417095986830225296979067460598571142336517768860860018702455417401693661711265243038374,
13083388160108498137634376159443948565559125405493158120207685915139202734844920696457300734310178719829326785294025062426596961865970010741348641169148996776980300620236993527261370734563040834022404125202102998460123585956602820225120540875531717320306514675819758017693243940139384890187652657818804164941,
11443385951741216321665016111821916787720115737310249119550716213274602259041677191091871081625070731839783698224755349197812844012786028057082756083153139198364316313205762565816301301240193045094951668870451995856303731142861346537858124526970006373414516349691815549500113962137450511776872596897567802396,
11595980131126018266216189303965006913554091711126334493116953872891188991769992553822418352229766780945347296166123337635443521759141599452257709325579111202386108746928185177273652652094326442067608780292792957080042946303667668395218093189558219833653771279613207772113245686190530715625954520135562670234,
11791404967898900616789652111165342810844192611849997063638786864779021086891949142872162090856905059661226135324515877771775811649987696491663923348861041368192016173688389395962910207934605960849574911686314472958827053956628022005087750860705116368397208449971322457130541283544583342589916960022797519503,
15491454298664558280053394079561188060748054506452064398811074328133683466874898311758036199125631806945000723129800379421440366197766950019301101012685424506497242871741496871290641930546298147366008813714098532453465427130770307477953218330761135212759286592701293608411441014121874684536131046733044810680,
11564853622246437876010095582980069570590484335544670847663237111497448045677573286891981562073443230264976931119179978570466908572032333397301114270523236819089067990109451951974907520985231306120222241203307863754688839712368053586894433778560627060008575444617121269364268496224758821055362433711772106943,
11238078509271929357694245156120015235737177041895118819017504890170590639981371199781917275982975856330936483740888387130185949838062910415344216342845604483943937682449824842670319085307219191465364261064350286462415690744240963177789142411945224101912691130365477805198621564464733443885663238635282114047,
11367340525592569169951040030375680331181495075569441772477157491365408888881598104902059752250947896670553618335009994214661325602751078053238915241220933620724854337440518313801136030639390876741548891374862154255510212038227973015452499278521261177769215751971282690459985209125275312795592498772762497252,
11611792228562818108866142207184752042754932816916458770203530012672673906746164907310998072158959252439551785783407369510835425667546658984580763038980455197997084061034805870354786775539166151768568152957132159415893342171222058532452457943062507985610833509492307752595781810612167625704352768731262105829,
11280882159770316419708414715148783057729523075925857380387491522930697842040238705097384375874206345898953240576273817008673110269439520847439423468487578339055212067076928899720820867217616326389080367569662834784010384149848461727211519420943871285654560076258883021736502646302974878096353080904302010282,
11258589140980871707536457618552810241404049301591376342825611900462114070111721711180488324741350597419247934326410778537505883190727823116072999692199288806467601322578380489979952505641252539642536868876045811962793853341362340503099467498850825843691516819082007154753871033133638599652243391209624997561,
11301171123023757132453013112714512510570276964161248442324070067400345396087559927074789398607585052800205169714725003038795664429171096367178652824211749992022281308760086539729761267124483270313300051046278640095940199624412832458301369516670603501350053125509316719576499647424843736369557950535286664359,
16239697866040260824635375563067805946272554475852833910058347327858475736578237946767144122776640466064699233851547274036542081872949635667260511098129067433330558156499541955818943220278247515909425807521280808528330481473762091829571173918763722977957471083565572907755300863679344299336745286501481910483,
14026315995686622375390170240901539689052492673115651226479245358700400864788281094778729736260742626297068923280837276579770018213850486770012902720793984698248097536057031780284816065776896438542711991846279461619916845722858566375605443788270621058335651440076368846096650194134367052836555690680268241218,
11306003951285648542609190265345357185696859031475190229253303351734073536359297604528903358707756252126971943019783263703538711854982664130110263729594218808971125651893087210922431435179633827758387291176645348496574424362347648610237769719504874165618268342381575755758541060974109976285515477228909854902,
11238381587323684676730492591886013251361947470068590055877974654874378003006456425076528459261468274291385563133460482566657630270302331675336630801974076571509748522707513685901217862913983851834719755855564283031423794867390925267696962449270869434933616106861280911699612198358574493144510171032786866399,
11363905085064330254825179672830369639468576504185675277629207928000891440444994532519522874349779603782971665619748709612299738898352390253406316633786519690622274318005249708770466727133021789863454235820310914709758660530655337892702952193232107977102497140046190138114712599852499026173106666495858115666,
11433892919325745003944182912138316830509956429125742101270816951827267160116591799098274851103995966159649746628716394860203811417992269278682327887767755295397051981294525255067743862174940157434038078169656353589696835471699045679489473422512481333989396821928271618170018916382711369154402688079853763011,
11238353334667465783181167160782098244506806504332423934473101583953716035222263491641970661162119690191968036026722274952231884708630379646114520007589770908405296423671660167698893193673860944168876087672078114636881403631949642750640495057823820249086480471848188527958010728636444283101831751774423396035,
11449357080089064329439653698897535586381560553649048589264944850223604106110960398795181716089538297835706697487114970190780596264489104433501404658516205507277475742523358861534128144607863723997066328191310454162329110815708144863701152115644665432202447718535924977218776308407927651927546249435428721936,
11575412837238264638487767770899161738559081390417128042208187739522732971472571132514516824305221795871730836981999519645974228929174218958091584480964734409691833413373979145118911850682063317048766063693348336768379736678050600758040638610151787211338897178975299300109299956219630587937336363856334784083,
12719246131438005332408724440699477369185758903047111995547972330901512819553466471308745230877543052452459173630032357234293519907135256687778225873487918513429431473710625622670475967023987611132433155945563650469552694365034517281090561655131244766506862670379427888311871583433986450225740599441025797295,
12713065716352502750807634906897506574515093712035045440508902384785786778004797843727921649913877890513781289000451807101443285379710692821217195412431835986167185876058036295038394492078821115764207094081950069063603115485088291292869044114577200246716321301061427702881095423880792169194891740030024057784,
12532022991456164465711691614678501373124407000912943142934474334844143051983592204503032722553770081287292938378820687267545542270797994990826545065290390832488497567701056363011068094672005506755518175337046262776753499175343862974921562522036156028695341389957650459614278903258895298828626150544481419440,
12161393804127084519233759810655627955484086372110730264245454926988038167141347519367619022821667318928377593142760114713775024681101350576668202260742364206141898197389356695265794490939670448131748624239539705383731093736368506272806099297506005187652952682929095175533558843613637606204784195281963155572,
14026992713334837299061853987929865843109705992842431143599029303786213290099682049838941736445713591968011076902656174107685448376069231598590507252643857168069057023484680589514913550712685108177513275501485215904490934351981860871186128632147863262104956922559368678781888871327782618832125877665733378591,
14025963855791955530819471417956388404731678800436704178751561256992463031988623530285673952672843773213238398991930322122091088100887421432555426380835234874694420735911883916420734620315598838876527309845683562989093029741412101619508530801815958690027643625335297999905236395070004213244361585627412398683,
14568755315475161084193291067570833941668062148287877753017752035547948263210427719733682048166042814216605740901475762448744967355547489587063117793192272335031015528654570131995294112469295475310779683067206133641910376612013578697361548951011684272948388745568922479977347012155865011154441161126671909840,
14015686936183909877896357693172181422774441126417544146366885022339215730855650727790134176766601652741741465567598396269778378502189878609029461338134927473644816107380533479521387389669683664461334068672296006132561251612398964309803714356423136431220152417061332075418853587027809168843140478046322918320,
12347558864021151358866074562638772591789436625963447028355962362772743549521231694379139847441029603605458243808437768192948743646714070070171775055691395973050780618780084341425968246362215476247709428817595828148995444015862854188218908705428676825478101233200298296959828431388565307333226769413231772075,
12160679806706871013187500118530612515306113271902227807084033666634009506485638918805084395865423667148692514731095222912368494388301979455402915257006447334451249962538225146481747342299727964282945266299778352331673947964686087639790223233807695957856667460801326381306132094084846597776742146159595127555,
12345505236895990246282418767916974685659091488656722250595014431975495471551116239835250332828502583366946043457110979532147398361199978521479688741495345941091891647369905311146675259966991095946652295418800469079932180366576150547263902988458729152149456764650370326744242832194604583600392411620143693841,
14026732597324245801166396812386044263783041913369422116699295119126815588630514704181523433880053631182473377687514224263089080004331865457335780154577970157280608205827415680729084429575306612592309909971846174460639065021635184056045645969095788308638584925660207400757040594194651986984621005823843370024,
12164458581034092514147895829149674758359852594872533965760902482685180733381240030451319835290698014127887518639536592038451042369632988355013511529577784093750273212691859820919288395507459712117136402910985142977312258915631378150525191728463617215600792547080012530694070470142324370317009660645275077268,
11448940060168395095537320988563587134588545845065511311650870216775999896998629807584886950233892704015808649960430354653303045357748664075836451368303877270520529269645491909844614072652305930645308569886642054550370531202454815464881597726292465306217713460118863987673768066860826305668185631955439879220,
12345848202328842025915310485269153439392120440262248968895571647815061227636423168334323339800969006878623983445655665488993584029100209527480855133108192527597445688373703908095432087960327817953569282858338700772094200920142650556563469101042702358484523004959871842704591027454691641896061071888851874013,
11382077871042156918858913406425818358753733014981962600283239991460541134086010223713732652534098876511674661236877304603858673138863069200547798968858728271041077947108225896698829421596003251821924972148725376215083780861340654282534426552392805182439591261043590339375235079138141553480052305304850174179,
13269950710169824095147448694675972111902964197180152511182351000235582937341589827822221120991439120250837410959685316081430919806597412567735116187659556819471172627615560331339309933090376431004748200032239868759567232973626750259504648143253383160426818470127132970840208143288226095136269878409679190813,
11258331298425648661508230310119340316041536520385026146306912698341074820962557152916560679717262946994040332124897240523451759125460588791518981892530916317322850742465451908646429631806591864116405786319314347399493301099264833683862737320857392858285381099200157202266062489865996741197404711745913001776,
11564509400106059329483320904695052158624317357816137289644270102807075149707475174669174233404984983633163576456787123283405892742048124355527295109727166022797234718636773919161305015050047139647461171381903370636685359654290789591612497392129569585624659142586911006098601719391271562757635323996442602663,
11238027508190403680690434004898856512468659131510230269179767817825487698031788154147611786880368664112054225591887691593240059246533844834812076647571516967928522756326397480782317950717680815443855182179090377450832289884918769220207259060852735518531508265960933327836312510520429109503118743650263115483,
13269231126703306620462804248423800688532569025752185584308998042854369047345781597382605768175186139431429035627159147218088109880559365275026214843890493494143961852507601300988306258910913556230065377612730466773238633246516505924954818312916529450813361963519208556924662517703443250629966450646615298276,
12717180653683675616214160996155240770049710390884974083299805474800701437648706006887663600004994700040629646934921695075786077007621281624856535857882789409596685961145615538955966466860861792293441222238467799474659175113451684386555503837325028413087692958613971841740472330456337454292798389277481272264,
12529280285198664858124645401657321697547271350522684428699148524890191794542628051264683130324639271804282830900725755201597708690724987988902988149330177815242500643836361396535642039600805380685174792168238996633555522169010345035894979024100706639586075258353703362301388421218731825564821250669807698360,
14580413378187724598853619435506994537449938725873210516639989429573498478396829478958319566127205212395364766978950220780819817977039595516288476447921524170051752036238489973790669178295321371648269624365168302626980304739601016526219933199062847794812802230809165389170015030963667083380514824531036045471,
16055487925392587037729543100121351887657261457219939211549678423380789550882955310877311534944416621497858938211771487887214756548836112788755303972064165333487414232770176578339199692605981616064546543036988486541638263923646424297363644976993674788636416952298695035866786376211262066925434780975434138559,
11559365143787561034368163266209921489515889939220403122313548722865161345924496293434060008411669514917893846809850078055530429003926034976977065790006789436204025545790059440203362683576834484985720554061456003831509589254739204312944860327845812368387167966684951459224993870756945236925555962221038109663,
11380711948510961594071684168982410698575899060195009728901941413033656245793511071132926121883516552590381736664965370021730955885265529637369655681519169304840510348959962126049673605979493174624749015106523649551053699799559705198647663505124570920246877400290375888367584032510890117443305802414214087739,
13265801012096224403374604219259007123664167834692215567440810347663536608904984032936845011870267904814191095205192019774644825089107246404935163212945631915984923420353761387217469696402850821149536856494074500114673519999795832041488655928449916514624107407237010492817901915716562426427308684327974282207,
14048945977026741518097673884610673251165667496508679881033108032730479081921176068117825398642093838624494249288421514006618470533862075411250819308643897901745364407438232005452586097311012815757750371701821891715011561759583070702470544396508976413548332126502265914155838617427599078397623114692583392359,
13085805605768128535559385630380170725238399784112836846056724845682119935942019233882201488424716942200818867507886983414516806320446466029285521782490918510634357330764102822773585974791766631329755992674705572804778396294171832841110229832779207697356671037056541843783994784031770569417193329041573315571,
11470659477007816524397941975045635512290696290976097312200714754324070609513524297038305679697831956790297376646580322354061811213262713129330702429803023992267554204855165077659373533010452032601429964206906334143027332069656527560787690379495967179137368895192361300063871098234233106934347035529997295755,
11445522439587778358802585139152532180596957813875807451676645530479920766436310968918624315233378023036421951897572635062864005081934760104021365793679482831806229702534932424672581162334331529125843425046994908115563733069499599810096197907747642306577073783061626518442899681914435348844557947601249670963,
11412600410865264018116100217856010467320979239694209092234594336479244904424584739391292710149288293958603428786251663647831471685088247792645152931160150151988448907563690960610132678879794768932777621685532651856230067089763834574122202902944220112520461985234901391375286228701258143371194558853203013978,
15133142221158734980635784993965071354068563750351158460814600959742748881291997385687259304573578404213420773721746482133009257836320379414917099469965104884588432893568234446999369111744622646166090504454288639635166446214247213549854993945866484103408603313309156956447864871835383562558223737775674993769,
14384621854554485639644343902149598941529035702004484292994060235603313746087748163987019523125147126218600085629934386706380487427605937183472907042055256395801439318637037452388080641190530474273468745665352401922957460715544926767076514821480245708782405467728923531912150808512847671577193434939972026871,
12527908578878034506868406696844271148392401004744974418254130073110411350093614121969773886580907600197863034546960212133405192802656400874038951133491575066460828023113885005406573787026716885348273774847711007172971351783047040184703915858229231084729641125082247593951795028387417515632492642866884903519,
11235930657932790568495730846039468895683809795449926930583088817184302295475138552430320302198336659481934589991387153156227832479788690004768948755745700595776227957288167880011983571919764311443602966955466086623899320975848908377968961022056328001806471276029470316690951883747714209711433730691684204679,
15871016517758334940609712141996999607123025180727247070263637030282191017814734158988234005173653952417896426629953288355102430421851169990254045220339392991614229443956778575288158132821897973440713633232901669451595142148700375162495119469140068916196690027618876125317100180966229226658407104853239792156,
12348244710656983987556451325616649636788015624553780759473106933403026783804918102352897856251766942146073562295396811247397626701981724114625135009877675618067417534792242511497679332804287796081915203401010739538336690257371210950421375256272592212487741553699467826082085192860836480742573780118777889026,
15154743328093828264518843338954642589004862882988082380717042220606829440244667979843586137184605233109101888158642824478847792560339791114499698638998242142531223274766039708642254987359937333717804005713731663019486329034115228681145337857848511160657059363737444433847851058351301518166915168345584369980,
14026316781346456875231541565038354399240829755827561208187246584341509908712640158739305843020711609188115004857534046084277796782309735012215286543057253028800281465231290613636269688496913434827403945633998860122418937750050166320500496430416765050295962801204958504698742916482876003072147991580503835235,
17693100342443470014312919652939303216740640523481488312225445299516369331384497946870902083188647234996456028186632524358288133185676990125671086737599912245576816481785258313667444707816149573728338828259814585522889626462083260241831987565791127947087495047380832128541635552909497252366009275092619329718,
11790029851719869601729354561891660122183607853214119959523665078629742356745551100424519402449140341846309871956343479123691238430732590827597766862601541740877468461259420280384532090706143057839519571679182289541777570787916312767419485700111279133407199701910625643011821091879907459675671016242814354086,
17693100342432612340914204564926418975849840188965625861779803378550997025800584416570318531937686481867508384839187637052597263552555376083598173868754600440060223996895034069252642652209278322774354780506883465073576070027141044591504924032391180520260784678799273390235829299807896231861149210844875784195,
14646246885354542279666782578156470641415714468227871203919588027299284718041768886573154272825957341295097553616861276460201153150729655570850086911240005715419544989330485300265990178844101600036411169619957113436641664055269706248029845971048187483076363921432690606072134813750140580732067974785234338470,
11606244445029292610901526975136478447729989558288090962209528686512358835392987487791806379256536330197814146095555935122059033285777489687017216033226002985261682446760433492543879053885941252413634667804659192757740371871168908786532756594375376989542807417925614786281035485451471951022500033934946829232,
13641257849037881555614894613932527928183977523973840801610786218460683175763558843023746024855936539249143333623986419918296539525593697396176989238459336674948811729528451578676917279040868817385610141567122157896306218073697253833800353212301211577477484954881475453454445513050517660297873991308460883970,
15491106267300079979907013095629138269098326197469413662292628970315652818785928203245757948368269674629498310653044832265360307387074484653526889696822024133610274878120653682800511830326579316891667022525960208342741991339272758058262223243171888327261715960876890696371272853281173227340573668298160407659,
11790366421254459631806294964844559399732315729093104219319401552403016150695631079512982797961271917925020680110543120490664010786207794773233702022748544071197663913990953823700950767835889466542005290043354207469292034925317795299478197128532809940818685001380684401350616377200965896766706923132121612459,
12345494166036843210288672565998062108868734841400406038323018562795848720459201558810077765937998908794541029219147046926441749087978198890222923085442537438659186289110548844979272971078560375610876578445071902336149635412774406760247519908668773375914145422583891899048370667394871749355784020891473412704,
13268545057739482448064757025813111874872956227519138303291671702276616003402705054099361911025657561685583248819208976963751670643009853142026415125070343784375496468403106117068791315305503318638047645832476889589242505799664031135563265437612553377013299327772727039910752731897925472327241420624312238136,
16077432505379371725616781216435456644901387256559846842818017715977168128666283088838591710874169802566122048605357817361247221387706455690540033157199416077045662969925950219749751106459258972478105193690243022254206738874154862830969439977578292130952797341355877191606863471901386490813986518114357183509,
11311789260516548870369544824220572221759313386330008595008485989313044303540029731194713458795493774099286592922094447670227039544035212999178183137502360689687106959355474938577002878138281338912311863353747871014067154526847494401361615987205131330747925521970864722313436041905114802887380556853934523359,
12349615319988428970532539195120279268778351793756029443531176345704491633976155233834446721505826679849610124449626111516593480544698220671570030729916463673806159329195376359455715090124318551352956024818856631205811287236784910600123792995951802543417443876666681642492768879220134010416088231195996561337,
15122163295302875547211727987448832971897722647411183564069904125949186136565625396140859335852023570458927608169835832873059787422581592120585335754973746736745602196802397630768524943783012172335661741603205243202939825302796576128055556963106156505093912268361726515440897746556467746410615338448804938411,
11298133846025010060502210956170315630547223030745284988579483423452336246700484741910133036658486090383173956033512227522279455065525558614496705212315856179000239795939050857512474414267153478598259364340395162913945463338627548400172491853586472370381817371135529072794289527782103112080260320970696589828,
14579384688070936904592580402206326661380817396852591747399414625666165629499647488229948985466265989857521910901543132675865328438251379395284916375475807776795814434654049692021881421263849348680315831084530974106351407017008834384843902945993313102916316053416427230505615367103524696866716426384984518811,
12345494375314590888970489958996865962915772191931413086644134237438829911070207534844559479422685897104067582444033033002623555556581215044420731243220123206025964868657510687510317607998069045279617736365578620779069786181980125428244494529826508535746984648828094849745583130524946811494498259660463932381,
15132792741799345056081236324891656010416759784922214972442819808809809382052850680065555289482462918986823693426297976075091783100948355822502729837436817532698845056773496414620436481792693397157382305956499353122411881721252901061817415628365416374690890630926407627914236748072742723604000118972515385423,
11562451433887062539018427842757554464873353332967944730774158679197664563667482461604826338198639579460958584020079292975219404566527845755017600444531991438175612618939080860393779866510967019392657810908367897841154303737057136481025834034177929040422134146732975095495783489068759846674973345942953427005,
11369116875491516556403289375168439457398152766821302426261618231640499742364191742873377229076274392134356733769683405973082386831534493170960808419459173627262341863367586141807424305485809682331436133662823640194354491222858917073820770608753056777223153238945510685176424811332370797072688666397162415640,
15491787787888179959234283718637810315296178419987480235500966315286373704127379173262984244999815431791459548748169736521833943202667413683245958538100807810020681759123215989020860799632574196512874917797813287156965805659720132675475755388564701469654392716524625488220679150445961166266819287497181903108,
11569589522827612789298788735321417753515897320390038238197270696490065454887463999707147678166840367066950505156314689631651137526282883792614509807334196400818990480850109670609000943879285178009029167194942901354096782427655003511045463399761616124572080377460088326242286072304613110360939854641148003337,
11468798693572360781051010856842308404448758433330806235490494945839686658100458733722059064472501995869558445144695738041365704736710934369287007276830531778141186427623122636340449985166060481178213922873154656241198114011559875496355413623077191739804508031671694651703024783203515503900409617944829140939,
11412628213623630931068789948317967260626402297780177513360563277411050880452148722221790536890001994954047824868125408245492871651315116614334223159948372248977866401112567264770917204573501358938957463003206869794569712395971094266950280344155099393090840676630544355879613757000937836200986947649287689495,
11247611168721298733962078069348963389330192917249633598523448097979969887220009507107425852068415541846435607908467566939356926368781588392599529810163075677072919134711199684081481586733252584874865358181251200151466771669084970466151957443070331335869187386099484048081035709692719389251977294781590285417,
11572664187426782100804579515926767130955378445273788314605795736694855409813129332073419661606811049966451467887236760509905293503984121176215849061923464972486065895373760279626794059196501958071945770699041720630226398151894369036059878635246276485113371846786450207995564080538289226141042398073325750921,
13456450612869969339253855385048213802416639952813498094490807980584771399718408270905869810330396937487284177558992243349711793365234466446794579905744973115678198108038737912780225573743661743253990874749834559997299512599932228626589016015787127703211192856551436632896676397242635014047157095088951268617,
11632370855011869850830124769515054674285770281785220860202556506890092098387580388310628220305725917479604118754749966822812646638642041907910445253727126152482835390258583894767721698873782821311356716823863911887370433128202721813482497901437941346037997997327047003801672585105802523999175146413489979392,
12528975334095825682187784892245009197108832900750174440351273900580398534801046910965640618230957238811812376408271845296908904722393592912268821666374865133749659472999663359639135025105225403449439187561655385486342427205138659192269255272372246782122238895201732723519643953351537229215372990229480834643,
11362601433463751829130805102997155437723002026376074224407675880927121835023872708280507166706803504438850514958247395041087335262859107137124563373509540769567820508723090103997619533561439903033231937384387944751246629673570325192303468602380792738440548808587533649502917409424004251377107415813563188281,
15122163282239857436878445353291847796740340897873974437316516204403876832213966461723235684903541904409975280619146899156341246788005872873220477078781537378873140128746359216839168836847207428936709551148125159245040579049378967563920924099381304206156992191104676333285674933046100002865288990034918717763,
15317264285534578991879199248356115465275634393890146664024247185044444503891236948231902289491300267555333392974317500918245154468002476507868726342597941793137723885405904465229668523730488665052062451836099698597826032932707668961145231140927040311094942973316911997788891891672565323400254728803408117812,
11632696796625340692222100390941664062332467754392600206356097014329900979830730163587639067372360028001880363748409339161720461271415906724743183796201150494637292575256095670847069913055648250271849297003104271721655247231578173011619246014717210951589541986082344628975677588681630903791812508104691548730,
11311848873683178887954314139575271544587946053002389681117677330546697803204397757139752540558233365889996302428393603145475010997001846664711269852993450763065462027095396812955994600225601040017579032641540716822722543286095317078111440117368705957272091917999386097271661492851575668931696573431912043789,
14568755312293951456864888363087169568055796790785442871842364609634730317556199710360108297320751855624485915928756516312861786284247418250530795225639910309171644736296733416383061907174347307822173191377258797583995962911149710610342263112414469809270987998222261376955552942842975754921273498036353904776,
12163765918921331340405236928829088905451814517568335660393947710819472411925742871985471868423528879311780738335426893390159934430931454586846929821522768442387360116394888040110929104338586715277477329795442562737103782135201482961360399366381290413005781372241213735111430154864485478891389257120238175151,
14201866340246153821177381193954840332150831413603119539479954852515424954098804183073280829434324159109382829285101764095912603596785711284800768405450382168089099948260096190988940587547308593343390625417273034114942316434504719708098542707831888410384236947730215547230369910927227300229529651431851820169,
12343436806727338068646808789105586732409140752845301424948365747270916099324689202428266300113401944487993412249417476534910731713234496684491957785328423117658896344538266652026763307008821501111727646110033972014535344667300228885447640526026474646035199978918512629884141061362389082126723723074259419538,
12529280381961797456597327614062883412074401265429806771120875507331523425928860584515303082920483440879910350288351144882005104831281191452778389688177741608208372752205222631650306427989556468019480706194397735067946094379114886087943633984985547936072162264958286064014610489229223843003257262940235071835,
16446034813169309721199855730880266700730083456568187244955145932806806625944048693775113928186201681161771086480254083638344861843546969986213025932008191888113141133800371160863468426090681164824635793759856912539408036071865396982229709955582915058907188272454924417334726538164765951405122644686103576582,
13453008500586583375725223188481675598694956747731816951784425872005275509125778454792469799223307198908128067983756294481952681447248594613324568693766779141708519572504616572381690319836988816286598578352351092188733396305841453282981098218326696578424142740153985633598386463366788738829559818827606196653,
14461770535069662784967121845328884405780863008229498886448594630540567421543413443278800759912006671022461655066102498997075460968716860150313226505863464432608769396310689234799721742298722423761757609175254233754649054233464019954656538359134383588193332482100616422967917364258681282885368599844554441054,
11235582145582585122912140000896563553842008087381915740596786055531057324185399181840690712778745743057395022571766293137646689137414679445804468902146577272887224487949777400542824516157914724912074975896918319774845784539926604810105663496441927756445583292495555146876906795114935752059339363304984576402,
12713065713736510698673423213820567197624410434903532625199162478333611182304867677909198257803946464477267713116536610202520352614761613499004199829275306639090011426865288999713935516273020129414852369804692789309034676897574647016450027882041003356185496896447531195841930534148623989014098837734551093250,
12348237269928322380131408368220561474642200143385419313109700037747560820518745710574572871073390877161833179477366031708088293232242028918069058493040561529346406629028011343435195216461001528796969796408360853467069193693792842104119182271401942655773633296068367521460359124145103919273478511227755856053,
12344808599342679114479030360260517087689240043970322838520889640944059323731041923271372765481972852293770715687480566063063958254272815265716126303598890682505331917302745025646090842146665288323901906030515535096112834769594862479066405573096997478059313043243013947145050386065122267189449230780180432019,
12713751489707783728724484490212602699390792990991766000808096372906710829969215139034338520449843255362689049395786886455551176782127321208618953906774607836219741491173021780899690150847613799636355026133580133484930079651295668878791741234813491928857852822859550792670490103102672636336762862055615070282,
13086122853750532244559276150059401480376499152610866241324308998517087701471581250829335087808068850851191698121492832938616737221335999419721333977579381954461431199462698727783209199934088371123471108751090010844951143374438926132749280727599870761227427923352367692529282604031089472766404703898598965857,
11790034820894744403244956444037356798927762776011828687313193727064452420168428395558233352334243086292686386726464558788989650187867954942758716388303035371224072099653771284449924758883634888286784490183149484762736088476658166713255316253211465286370192084818083596141766970923870742051130701683637879287,
14579384688099357607494926121838202969655056430912498376449830061478294259660742391377827172191094910904346014680325482935309374892303979719004941454527370065366470019274003707294513106174572553667378413915943229756791538884108406992330654225572544589411864163332449231059782547513720303085103025826318784845,
14383937385716187791086540536487488196591582516952563818794015816322636198657141828300745813046484284498731889348867477370068631597964162048491654362182613642914587613617773949239646568207364205299499140636037403337255070761403508410179799710332532446442692516712439820472328274870769107799323452914460820408,
11446889324531963999508607204882726735460600632460686372790022115259675587659167841462610604764041978914635612136787759015185618860019757630765112266317795673128745382826108182898415973899339358607883991523584917971566699809853264259466874295613806407613759897675977107261608745993102287249655232673712341594,
11237695780018357370593819624862795853085372000961121222990870984776921601345630529359825476443365849296649398945741420492874012705774332498314024651843713879456868171760417839685856168310883783159538528284865230424447030458322468281294524072665704612668593212983926854927337162334371826719861350567513766654,
13270946147732370183021214304258275183766615228484617647157109101850952427288342372108143754688423208809065372954668255738533455418961205034982486031272258908983860440531855226837599906226916398506223562464032817672899783843841581223827655438140967212098988197001813761194115759719069752980899736391996673736,
12529279898028636540330426947946859395092344617712933750927096232926116717939369251829680214803720010092084234355560192823755745017317433752766584551234295155945722150814181051930896956814939193499103468499284616221532615067382540277669021191701342841267248747137416950967841011061348615626617736459869618791,
13083175521671191257245268367626235458423272897452551513216370955928782412705681088461790729797351858912065870291503071998894356928221236071681983698421687699742056129835555165473055910601233454575470693373377228689041670654523802923207876575018120470021147779551464771416309807621055924830529725624699814001,
11640583016029559048937802404376129706741135663428356821637561930401005873850992669561195855428129262601998186373323041539843070523762674131689160286913450597633143685252131487115780236840329817167232188049718397118437241787034581195370294828613441387127484221144041545099052720526627423020022646323861263630,
11236279149378357475538831102940577138185938886225112809413136790328953958848408215385622600069655311102261774820956994691966404806489630736385234229279379786780478370595200251768558235970411049539365548889006767067551031922594770438995703621554318797624890237905757064820048205073617582043009813976959648928,
12715808890875648494676272476490464704377176072608993100334605420551990677221955795188770183729064123277572767781170607580616562251561851000239668041172969734094435537847977385360802535932253416161452219597538573990824695786288658840894182035774854825794838122493354081371810153275641221634837319862027322424,
12713065975335291898607011665637445904340377839174984497073950246546934949823898896421069013422373217731246361587833678107905826998157739333092849681225627472083631567194885626181558702194469977021445001429910369484835915723403429226491585709768024948078720934284020502970480720709650325382647762419448381631,
16239959662908582254981524186379634861888572000874605913519920031575998034890845233682179196017075536237944597027736564377045052321412076396865325747590747612240843653000530860921163141779708082985360241527503413053091579309183767645952906248132482336089050301185176671586809779813622035157269169948196766321,
13082015876547097548019956874878982196781784111348443221318324595041031127641351761207341132111196916571949620828972906758818455677261836852806511178600477733304228298314836044380507344720234280331502838476439713839085623747255995103976498457739770932834439367670658288129941369475575705429684753198310326456,
11563480751843081244468662589069695866528269606855704360327743471565892002649836306279458055344107558482466229758178318235984095255519238270803433749568303500509115237536511065769293937838935000768350214144575813480316299705913409415024797120796567902019302581642121584189665871838152426449195295802764395470,
11579991129708059343272329089338916333946071387860672787532462200316807362792237593995740876736416489117182838669599357109253754721914188390306719826700296208136827271348786175747364195422462835808630219308454164612731467863901504018267439189147799475724633921014092566407842750395001357908011495834252748282,
11435952224932171640734846812879859467698011394116142368204654051846761429935583047027824094606936800182419060097720815758371614470926895817221483815672347310011190361859858980597958479778656523627803344939487404335042639282355678405574027457262138863054204658294489931632586422667778795800283852599930200523,
11564853622246437876010095582980069570590484335544670847177850606850184214824664977376033543424891235141703161474153702216322960610623405659821791991765238196036209084268860477238467513040122110791016848360213324400227296094408193558879191085400035566665684139255370451286043350488621322522784028254393675367,
11235930637020849690512910022231648869397183029336387032713454903146600532550470607442598656038855367546598972420890207740142503351739733839860882126516444966073513387932180143943469418285643019962395345322744769266201344285390712763765642569754433840770720806326035558011196383175918198846441393671832217087,
14026052463328859553707688025429534136537828410280569321941867493951170290332825271105797300603393539300120036179083698252592225755331866619393425670951873229561816974819663562231463436872917938793399867378393084136159831435788677523268107573978554430647973866837548801625434332589905999358217471513514836510,
15155766088609931333584102074925997043562965921056913929871080409393347915182798007995389915303110825163801267434314889074716120237860356422531391239063137585471426090456133943604752968791676049652900762265567315235273094265713650406122932925336450231275283659697107487664784239261480665648968361828558064554,
13268876921096350505188966535860224865383812414011736495738803590754669952698757345417939286546355965997738810434784119849379685834997730771161348848236308994839323829164745502598859194625213362746692156082976804661331829080160751088162052419557752609634080909412808082688146885777896032198900483893983085089,
11311146313633321302812399347482759463998831210826780574853409525122034336191865534255158937375628478426351879443321862348366691931176863656506530693416386867138895141053114249221394736020467040053198135066553358429017545012383249835427697333641529905982604715166910660303616903425314626835943401684848673525,
11366648157535418914785564843417781340691325595625854028440037037430737075058309718217322419649023960563135949445265334366776373431545093657693061723639786992178200883920285949698474628524152336518691422281266453383394699867527784469780496184920131879594336123759124101330176416371523334031020235216112980185,
11470518736949245114605316430502363170735659958961021859604874456667788112108346689485838154425549589322476576266543516886867052692995504943496789301034732554770816883696033512931255067114301324553239792682967284007273160585028868591100758409410959069998351262743099156937650341553103582818277805983011158245,
11790366421254459639777309541054075965444309040333379252315261220513541804363261094714465107802852509261793856215504167259581278800714364613272070419886277303222774976325884496690128930668888394802747079301905466214183410579990642387065723748679616952656548853315229909616860336305386456975234348641387190067,
13083090817328720968793830790919344851378550074861852485048236745826196416250806946555295449941940406146370629877301702098791502097816870150477534388237897775131052985068830180768841763043828998541530065210461226560775462291900856253559737895833157334396105871528308203399254860208952969683739861236389872255,
11365945126304289302044276349112765069336876176370299603570262228057727997349833472895388557679121718943005932818102328981668260566801910492724476981708178699183472159260946100333617858339207917502250774268887542066008050095088278587028733304256418556125263053375955656218157171398396267598633517122394136490,
11312433075980034095966848625381148776482337218848595186204246251297456575745144068104144723618645109419584395613826785792922976882401167279323172666077272568960835328442531424073808685033960410759708406249761652406339982387517140862055662049470076755990288507376004852455915468901351776323262880162509035847,
13453415451530654810211275120154075821098925509752024120324473947645166796113427444595536776071849563061274389182896680520676720385210972179962617200266433344279569422860281711330714651777185423734835165153551003571983545053446627396830296275699542270874406455050548912279544926140651476793914331344688095699,
14026732536276147306214584924232555013570071098381916275963880123963177435720297988951153934549919756781463199359471886880108046370533600756674977285150406732375960813926678386084627372659404461349335685390880039150681384685622237448751401620844709339989431270378340363139098961991666161678271416330893596992,
11385237345864222525008903774345582803393065993086541751655826095741257061507073692619249188704090468653487227553730393329778425514635913546507968383140797598263107611084040054618955599785641071486204105650784385960494897599884893624360121287320847175961317328178632914814020697277595176995987629793954594816,
11237987247368685273562984679596520539409335386725168373498815255432124768097378621455585200490552589156555027073147896202995207975059901624176655698896685674151746245953173930523698593297129698120067218918245213108526552624120396198849893647521783137973821611493990188371255568566309035930851201720442528769,
13270946671454591330805205766608491637953809171173532697005313929794336445336831955744943909818498903814884245548603923318787036295428767828955759699103451852157975093107265927502188753830079362520896267750152740965551926787013612032912028577026422165233981634649193801386636499163450652847746052468075168421,
14233153582405251907177676934505400662419814320087060003122014283097233941136690498736834461408085705871897992950446043332220355357586780278766765250728821194468427752796739663337303092698590054261039091396302625818106083513202310263301641853452450315283261227787856709033154143355764997008784966517733688077,
11426692360410411179868550598559474413788410868748330963774318057363508365632680926311257485475160286305180007096214209051529889143448307812634531727475831064381535545169831888737827798800248313656663034747318640656834323233297181161338705677892839111619066938121730848214639771994404248110525273859450997934,
12530662927907159264946778769449213617984357673893466552067107932419541203640328240046681248971032114143637520119454861167385937740319478078045845653573015856866246662177708831688102313243464038600059411370393538934393498379064666687674913958383779452353783364143274583909686365507206065600419309546634740793,
11422942896606958906088820406621545827056595067013471808362596940587975319857004196025719085792855268187895115607473686338197100609628775971413580699698482625766032844045914793222094696274035016944729590230753824337512964142488017164522260514120012771210572598887535923982381806581960872123318726510316037183,
11422460341898982060617763809635369525214100108904092042897819961209118683672313871837135953622781121378879384673653388148704745404918277472214078795673889808973230961013202272741213555171960855256809589081329112870427523259317460245157818959441289521798193645094724022870526030075857787843648085481071687383,
12343779208139242297219283541710092498190820795478910104878474537549133296183713120454140512293098611852687755108479048803271412766043299607643817175863183344774814480440503843756911668021885289702216499894196115490184858739444148263658830299829982837379699178631146696953480965996998925833607120613604721255,
15124220969379071226933245238764777870100250979837610183310143737707653206205695426626227988709641401747869504076112319136223181412775222560023682537141559277089123075538661674400470147647458881611125153566194011775494124794271206846926122244875805651764178930704233338905626323660571361393883640416573816887,
14016103168682384940689707244207520358219636317122026788900517808274225426538679690150437545295912468402605731770976561814502028008237664635894536633118506192896364435875559282024805771464361083737671902393002176003213756465047955388434292864525389195682944330378912203854469621007816888479718789762874311202,
12715123041654800668519960731714060024783897730804245098165152949822565247255365197085921342276420680238605018725805156412825195142575300818610811482127792719296692488031267623628828502108911053512370123937880935452303275600317790248750501203885510536871722325515154265682460737514854447234821528497854717900,
11566222851194681425841679935081410872259854339226326918728436865700751626321713305871591086035307211878468165690082919675227077989306419782535605855745704242553162297729086476367568422692313015441313793679201764769486326581438542182805089678268135640192575244050955988500148418970193097568361937398003433649,
11442127389737193350547308716915626576738865496415670585037743985496268299155129391477269754791925794031699345753351771476619325019843941353261507494908183386462393405175767829778852513435134209106484308274967788458244964702503401040086528252230891321737584822251519991302896958954097067817978687614474593799,
11238027507895417898340826508596108148287709041351611502408464648122677899977921035235369397402903448551222353263523011704771660690511452096957410122027291656617069760186781629964361989661850639148042630051356092228197471491947201272444805748905874863635530033260349385630258563649063454692329117457374097531,
15491449274760236214187077917797541543374438812155130169114235555048219651169751066754563942075105197164813712867575553137409407963431578323174979090866182212424979519279619467851586340165358346927087828193940375815688578544491910593666627880862544522233048175149379419985125174498553941460146697319420399844,
16046232673038728161971272894028613870860006195617223952016778709402696640101190812059663634901504969159010435520202554713874541655831969672083963070756925352913633188732476399470415081248186338274462799710605611308114049217071293268140149244718715386700829061001410891480568088924610401296394847441753047231,
14017394079219011553551088507674725666011565216502271896378937392088785808899960659798895212919518423273180467262406985536731186292688704737479321574897735248931525516870895277871128081858123787445867902219104922687613291590131606878338777602054739372083058652623068497386299061717544585255395147263219269954,
11790153723995551136646598951815868017808602314355521432317442169834444602592808836102527369904222448373427643415244245425431456993070125201894625451776430452653414432121489444147659403073735139319150116791398143157344325696109517130190328654368540371036228219673255331154979763836521192813266725041895211220,
14199805315965195635021754797322203133103586857678404568236864533144318928242287543962578050539918220374466479495888693748932020893276759866234802689070569881732005207490735209893192280955987465793054262650339923222620483593314622236714281978888190293809725744696921396795831115537704365362172517939855492153,
14602357884937708018541799047909207569198358111191213934057338482722501453764982334362473808086427241963404589857965428031712400348471848488991550867251489983942987779567003597417535402345649601394866341950070571847194857196930232010108229220272462240979092177821720936245144225630843226192447784428180275398,
15491449279479679364306339397712065964933272012319501641637561667198152721955143352451430231220605633075813025682831669156426831885674164110661432298370947304473806107190913804958530765102007373249094799352223270346083803610085536609323724954535554044868210491502513561126385776746209805841382429446223266751,
12347560513881112259850816045589633385321571115596009505462174425919295876034310917027624159726779388197776401773131966327934954995694392085275282512471183676240807077600909615998014754433353719244326112334990421810277044639293781913783347763778032591914994483772690146757956805772863296400438780025526714986,
13268191156448997837694591598498313629621520213946795103962660999547033557119828771428507909280752343681402485260460988247814285591029502462979242793695876023560450700518927643519149937822494378362135173290207047184938698904407340930049741987974412612535855208833320125926781843596276018267308273786296894368,
12158975930135551179037886008608461585914496489079510690993454749850528461406707517102454151570704806795333672588568610145520147693509623675163265070599771018994490074573132973240021188104538392444330784345730242092371970676398054017418639778027376124844395132644615300994416768503945188241613666487560700968,
11405455813342451635415064775463226843197165248916852822745337791823200879021610661041828251415383725629609755291768732787336004074575106791524000649459072335312464195138192431680148574291418734594305890858307988631693144532567853785053864943615214631744845771084170034024349672763064528053744433958574392344,
15383779196399032787567257150680313632711864766411125806988605031296866231670086992361126480663203177484342118339017179305214488251856215016102489721212249668360557915178382331147552334094351969864753385140625821917074869690960174163638525609681108542528771759261251510989863363728716743365293884997631683655,
12714437265679695500800132551607584360674573703770876035981999361050669441752838828570387846854766200478099876827003308273498347520777092987082084490800454651794829692926686076011511410867228316888511104036750177410663324687144917711730578516702334475802635919928504436136485723005720995458951530720006439069,
12344808473773986738013314604276030801281166619637861791408280444398808087152930399960811509744990768922053443953266669962161769775755468325942060426645683277076436688146861709259464625307731870968011011546137762543265284175416196604117192351025376031833601212046030157923575074888108141607961635439522971826,
14568755311357982476670986496241983738966927667221320265200434789229095356965481804218778977137423427034296657670832108049322771989429289788501477735399292567537204305448955652246692111290184902929562141446868447867275777237900384209681426063988682549066233722143203161728798308963371315091737687902035017793,
12713751489706506371456870131949792482120827136323879146694006369905995796229290261678943639946364484793646739909135159184448804595423544407879503320858936324842709698257354600982270324310124304377064199490345841358599139457378780222321483688981689938222735655142671484855691912092620399486255957693275866038,
12718207197109111979770566644176369079848889297398144361558678905291464501985615267101800604187075009841146985349230247743817283782937984586979525332130505618394065240295321452687327295099911011502373029842146690124809261853468297764842718434549894062411054396026737886731063326036602178807338358701858521265,
13271969940372221257102558484423469338658686848477394230488287327243791283453443388557475823567028019203193418060912017418334289818573636396418643351754859367621917665889494992023177832126684194018991766054427891719973869593172879970236876827986091077767598575331636098425887782009624306426521694520705450990,
11274373121958537507437274056579549267035061407937914251886379381704787191416621400306578520262554622418703716208389098140504948979457092051602975277750405783456772452858464990900364193819300431244179149057606506151959768017672807541167106481961679135991778623535670824664529531189934526110896648147204342444,
11296660354233075395855348116255317127712622556742808052376501367186254965011594403293075741254497055716083540706562294079322634958706877404570563556681934290121490184857232278278115124969726997672852376751055704115918482318623933536763976179104009070617462029592937325081867722165674598071194508747488374401,
11303564333234744543692234864592213461237987771778011252114315453379978167786959252392437770864630547855553019733217059159145768118171926675022702944700486108254858866373238808854275511875372300349435934678200006050055680814908866628618545531365537155892954792090970746552572219028505428176707088487850578139,
11660756740130489413404604354725288889552034897048941727531255135557435926671914315692377516786264179929388475589336188740926981139510200551208113723870134666740237333077363487978656758389826164273469473414949522844694068207228923813829134812863172222076431194484429272409087671211469258714883917700302021062,
13641257845903375723263430018629453725177954140747854804050497503887731214235635767317438263095866645622493737537540222413037540724425827775950434635897663970692823378136430143711450009083843610146912126360693564400862649148516499897441746863978376649616161441201518474966539321173549100989855634921854471870,
11235740582842136429152996941741517072033629864767448286623348860702877855147346343370515063499708814817108404173211455895291258143005808151134668387240665142051961914043531966052678047732555020925215365346128249015811415454783189342065292802930185853811487916259983219205651614764107166077548502430268719533,
11444843287462270869817995149029389900358933387882183847713954575557512171441710284106682561328507744146205691502864501890424364659506117686594734540851556329927079692738345347567318768508289072137917738269552848568668343505593677401358941089929702697617075320015374988502972367302607418579560108346255344605,
11672421212632058839202768129358510004242859143804618828303431216740225483172191147865614556368528831557937617288572013039280262992959026429727767049015421287162784584568373783623029862725792689209814503547484709076088991870630812258741248086954657416358567226011981019082272892641485248381600433391000225009,
11235740507164342846814211103232118174721420650364659306958741274516476197232320148789276676868350222895670398190901647454299473507991033991950715117512971795249645771956428427561935960975381314380836340475358736423480791209347129961365501383804431470842314536616132616547304602557504528116763694169773289693,
18062044715746405453409548829053197474615216340416005188572526995120480428547174777470865114647298597053075031232851462287775944066842305486821584418508183147768621658554593546201722052376501831839538836835037254232031058854175717544519016573296035099807127581749151659388838688354771378511236986449301570497,
11235649785397475508994903506495285633890585663095011175558058337680357272556089818597868203827414445964402587279573432731644717789890717551511882814053192467525945901269385410704399242514239557256449734360984985502934886676052059651157759537635038415786924884285300486356788294923734374012438283167906300700,
12534092812392629138217763870561159008583595429766440578447270019891246819660604660524976390155219305980318583088166327991905805256371898365265379923304043625461667681327915368105255716209061939220946501515535825089257767642161005885544034462349519274179958592672597788946438808310147367037740831549109207983,
13456446134126083226401138623104451806955036004490268060413003799129114420617726757096786005326529003016251559887754199042437242857863846324981543070651737922080725835517522526396711639542396412210860492385362892830878945551155158391437081438682571486070929483360993412928609802536540495180112666495767550283,
13456446134126083226401143505262317634953002142538344443091565318173603058453724363385467143206586898748614327679690061875015644141844215400518437004848500344836678844193945388269604324620724732467055324194572435342729070308078381526767936498903330039853552652502829108781644438161568642478603753614977762183,
12532224474668733502861736144714870968632690937691993764707235739870665463477622095392608249207736699451877384770720020660034936624610471364787280184487131393344122230566134111924812916299181319467579640066239623784813472571531654557811928044388962730219354205208773997028506868943095828907530019435462460308,
11297346203454641120629763441285689841044990756814909208744751547628062736025499713716943251718350064168680801199252128083791084229470286614863064618043513730369304524069951135750192653490912874865172350443608139491286413713906438814627343655246178811412696318472040181142227147993346731964955520100240199370,
17877254988903507212564480582435506752509049257094482039626585368033834512044950531183561831886641973348861211766829212990741712456973369051791261840064990696665494460274882681878896997752079399651311247797375018777589045097997410480002402632061369248776597453976658342374961055309614327613345808044711809247,
11693679103167769095580647425813868611206156762164872824743313598409065360328941685503976735927287909288206315733486353247615467029038220615678198953686795029033264736231314726222052044214662687121219372909677559511839199453080620779268371672166077365654245211433747886945122187698574021151913813820658519214,
11681740247949682593353795974445526984032255960581544391889279942729240715507739070525131680538079906703548492132219021506405728614489925568875129354344094130397146736020393373373055988702556773935672769637746139690727796724117542315978378209540415767552585540896011311471866033299669434322701575056980255174,
11303259874475624573957125441962260548538031751352147654288664189299131125910980263261902567991041389274426703656681406500404478696442750864145124929797247517928937616437282027801716486651544995708687424033432486417643777581406305169831865830955737157159123885280577903154304245900388147870169107841860376899,
15524715811935203399136783305528632268135958151796897226086118554425418760664333730753828990125839246118004339111866353003596105339828366912311595430264076631121351386089579732349034115004534786294893544459556863365002554183521690141090710293410425237655119036215473562564271003826100050974553600865990254508,
14026396308756062055296715484491261421124438492867174026904307159736260891040488994353524913289387839753553204224275311283342328887407458904207289403207578600469290584886432479925160795354625401264383657589701763259785697388999437125707553316616846262894553572264354159838943560717897402745751501204767016189,
14047962804215557017468553667278748808264546431342924556590417530538870833626008655920426919819921872851687791655088861912576468372910098973178547057648894609653693009581174793000444673597238071863874253143195288926370124078590745929474070829140909155408098701899215436260781694753857554289830715484481429421,
14199831675385520658446894793813297333560509879630278124024496493150324741693709651361811771189561091846314753389951335821172602609505270154277846596670351135427289783599238420650320537593696939534911096959369707944685684104554585687898688700012824480562649551574555089019271967887016936336585465646000775082,
13270248455557246057521989937501603409038047598868861816204132374416497143659654158564873655437200754762403343124195637484513575915837878809174480700985983038916440213165622885854053513661101248842115603945229095126658482411553413369778531832894978648178961891137242958249463523486292637416747387517391670436,
16413810731969736940787040273440596159494914333925461214281112934822844217025045866525850826125439788668350150295204545131177998330091571446619498777710638061588825799441566239016302456596652916881713925491641848531287901848490016499680938273846628674364280206114464719416726067199884689385960544997598200081,
13266479841765955017169557775895695933874293706444170850653221234727801581534103672541871688643159533306377342247491165355915869669946987245016960564637253120767571277462126528433881233184574965823745756669782311762499295467980585458506349965885294449969541526623015723741978469152038626274909089697245594607,
11475319262846182404119065237771775600788575666495412127819507609921206990027161518886988368627215620662433689272611826192815435767647459187501930301860019871887264662134741746103372231331265348705336116727700768874787444889941731005124156880878449752352138888134922856872902323084734982602686619720407744819,
12344122907083016006199964965056623094140055929313653514087596214396894640823753989216612537087763216219598484880105973875708425709823364260120110755316602877641328949028919667814613278483936059701166275627078979089517633322930774112696131190384806343270671723153900498054121790340113678647443013822351546699,
15892961034961492059369687535441591054130444828916169615351465842695580346416109962855311100004955789149365537265747570615501733020686284392923722616701378088661016603356675388639587497206577051581039320798944013783433686748890397768808678816644301275499546169227217702044090184254849382775702400362774823611,
13082019894706290513839247163465365291161661592867017908326672373931753125759838989406000091079787895433120178361091338889634615249515674428314839061353182689729392736752519416841415691124384752007326071835701411130270883625822636808437635142467487846963020959208582787928197713518828773530003818163250790663,
15137936458311926142909207942601419126072258387526405201080718934675205895112186951871395326373055535737725754599707836681838237314057849191692686563166000814885971847166277091790565222763899281888662918880397658070278444673419115505519806697912291113003435231179997585074876291475801919694085619782607503368,
13452332652317153875670176933474753860385955566366914707758294500000823571598783549362231691928447182244737866395993704809740405624224548880609594969005748100310712475985372298623062142312121737479337619765846444068113862810290705679044429583041674677931118096465253400799392606742318690642483973963858083924,
16229332527074675972080587556749776206689316816582520161672370824150342947341382852225110107437457908628191715590295997226753261259992068293735448047358773038187317290042652877648203629256374991638850077594517180116034208502558047061417345248952193162439902246894178122974094860167209756484720214268063089936,
14031107545684169073777552927373497324792484215990913820157043276674431038683141091485962928528147270512033111673092037227528201559622879961208070700025571516267577815661965714369918747528618956035298323229015950631715955491335928156050631068000632820517977240620445721230680107081082337126852233199446360436,
13266479539165588212341824063991052375363362054225027226395410132615767065454742433504051391346995330287261517086969858449964906632629471364986323605582749931614241245938874052433944833678335814698203397759631379870021134159590478355819967366443900642553928678912865572715772391664290564827964887550592909483,
11406686237818972924503648440927755514014149724964799926944611653064093368582134172346567247618475619189048179776542806767074563248065979010959373577515686557465996943971527082400768265526165893743052045919660097478097278348857508444270938110684207560854056856787697419756289222510472131150376205720336105749,
11672802819421333120375409962640044718045206976603927770551333136729651511179871658035425018997831247798737277607387403832066465636721555441743298947934117731565403871839566018017101244008522849497688688507283150136128599478462121766500505829906398031216770848758759725471251528643693842044666161491980594278,
11663505452610181586635258860874829375216478545943651014132521970165403630447520204638351398967279961640294739263516136424883922486776423196728400628753779848933304758025586472795124125253623083791783347855234719587104839107233908516126289333616410053689553202867132915987787836519113659014565363119888445661,
11300089297219307007144057848429411784255624627592466703729137501034755936230227350037806264990370716043560420058775185779459898296669422940391182370810855246257595429452604642424384255974355267087517228188799774439455708168503890345006687034473170791262959295793290187609584912563308868839492709966537603839,
11235621710612192146609663509929613460885582760582950978450090370276331406291377245110626592476641405638206801398956214065893315863443702194374738172484965333688699043319857144906266698541441817957696917491630248305403635773271573922491539833256990567728894905759417096311366919593329833304433624676419576356,
14232379334071674627543237485772586502198160998327000322836578460925896926295081327945647974668333274686043344852903978212759862160337405849483435048789947754290511831775216103312309196545640388792052412984193651584576607445261423458478251621401985618814093442650993091747495890998549753569957878482206229179,
11235930636802665168851579917237919293253510796157849399979386310438414865188508655761330200892611908347299805976590129765853987240299223690779789118159218583376045503618819926557031893328421034750886903517442423811020943661157654503731239749274969761456306733546464510054727133190885925710545925058005762246,
11575441027315522953716319663198579282383037235926634212411086149477000945037668814112755826788603706759531778958461985701985148510312965986533403954972578150235926156257236897549963966795285762032998768482425327953541779905676662906016680134848938090011246301179766279209140651513376543029756320886246704472,
16415525256467900399528704740866873404570751807638602473648768926976701455403003398638082650011283476128889233308834664002836706790658985676715463098260507469789995888140723909194883472352705799621716979110468396205432389799326657328988572630313244317697770211886954744486829513681471288985435520170506718383,
14397317086451460162827030839876707772085775586454757226723680519600917442875461090281870693218436451647988153663684342246212483701979781955636354563823224190608210726969824836449868057325427135771847968996867593061326290058660516644848604792201314776855961731511971475884387045049898169767707521536192840932,
11308060285337734562332709648884818962646022057461422824820627428742582894681905333944785437034730283588945608031883209519672866538689465527912038434673710694030070966406325082362386460497724457750101611175857782601144120952223301292659280884022279884263579161178976209075812302030861162784400885479302464766,
11338452569713351421505554921558373485219735073939917062252926873672209882088949199454904088257012057700497975099101923006623012015835674755091026307234071715944270259807602362578621601494575479699433536847329750775919406953465303399066178484382905470009125990908585368914975274243887838951060720487218548951,
13450961079444141539088714558038139162417033867343432314298152546629917994328709692594776436404955096543395651261581716745774409283321972775925885991379595246037861579456018612920655776734707012604510108678793176316545462268460437611443257961366617177260268258208924009089766794353043847606620232393888380619,
11706388314902392778400657172020952160111139259051959706783298364120874814965052096138705971711067562665744178244172772935660420182011015388056553742072859192124469353858497611341617480625956735556497722783389361742792366564643523971752020396937661437707554610409138383555264775086243579719118767525426464012,
11669144915388863131512912200184520644567457294128649952660977468231876984471634290059092959951351365195226185106019731953953754799855864030139289139017884917173336359256302038657656421494839285708346343200088816762841012248611376827657383885823508995544151893026825176474011566629661791343339499898371025548,
11474656204324329516712312034482829465364679816184696223588498036441036725656619711012629898000029553942536754472365153365971920130454742730172203410819387400130228600180268041691929284409090750816287742400446199393852723706534260212300759286966054194791692229246046027512192982189981148145751494530570094161,
11670174903038216648908272941503379908972331889216638342162297400829551570028887932572408641252589959916294489349456396800043240523687215001739030817761823122259189803726361203223575637145528392670029226077352552398268831486611056363840605363928233951819647989970849355157694534930649939687509424114592303505,
17877571194423327895451429090110981292134322925637069582965049332675135640214989394836043050820240283679588803368977933013037147578945722647854083269259531197208359191728858684382265959079706082555354862759522780197844388963018056508697486026701569975473382099448711503195979299108876214609463600849327436122,
13455075965488935438779328407214319405723219791670190168440655659697189862857352430706627333389668503107609463395488837922013345548782240027083220867346321239868697324227638715672101727167820144091851404151485506183130406814614393324182176112590884448945715152765475864279939095865406702401339547476915946156,
12527578721331744679822478562410771968664386781075027402898487695125454053296046537931327281279177415177330216000044526932194932157371239968487938758813566728263259521451795053013962326197410271299443266586565849521567787707210836060409341165944770913067188184112884818460370157315349130360685963678969070888,
12343093444529090880351866944467537368313135530387162188833305524944562311698253460706329304237803660999964426655394916052492958054934313646923269509517784489074765865559537486311144147621013699521551416058137818969291255736763113576563181935598849330806827181221298097976583280464876353346147352621469499524,
17877571052723135198740411716193183342664682495102384793699032866932976001359229029214952358475356795460300163765408049619525731714399049420722130192960932003145823674304909802421943180539986321075463916862112178049791680182755971653659790190002016550684466662868759409505501667719127621500008386445762822145,
11235649763704767067886781832503385795462402911736788105614457004927860456931540872268858448371967646604384694962227183026870362694391751817675590345605861649326189659730151930062553350868264415634962957455255677027599014733864226048352758320221929772238170579281721266718025077287888302384610237120466026669,
5724744365704303777835963625128709931307718855204218232418465668202218770229554035454142251584458293720808834063871043196769601443493289678528780255297672984859747910567015457740350036357888114045084374170963529762149]

set_option maxRecDepth 100000 in
theorem unsat : ¬ FormulaSat F := checkW_sound F K 15 Pw (by decide +kernel)

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) 4 := rep_lower44 _ 4 gT hg unsat


end PEqualNP.Outside.L_meta_5508_aux

theorem PEqualNP.Outside.L_meta_5508 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  ⟨PEqualNP.Outside.L_meta_5508_aux.upper, PEqualNP.Outside.L_meta_5508_aux.lower⟩
