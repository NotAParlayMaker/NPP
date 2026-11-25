import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5601_aux

open PEqualNP.CircuitLowerBounds

-- Exhaustive search over truth tables on the 16 rows j = 4 u + v (bit j of a table is the
-- value at the input oneEach u v). Adapted from extra/submitted/L_meta_5445.lean: monotone
-- gates only (AND, OR of at most two wires, constants included), no complement.
-- A table list is kept newest first. M is the all-true table, F the target table.

def mem (t : ℕ) : List ℕ → Bool
  | [] => false
  | a :: r => Nat.beq t a || mem t r

def pairsWith (a : ℕ) (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | b :: r => (a &&& b) :: (a ||| b) :: pairsWith a acc r

-- every table one new monotone gate can have (up to tables already present or zero)
def prs (M : ℕ) : List ℕ → List ℕ
  | [] => [M]
  | a :: r => pairsWith a (prs M r) r

def c0 (F : ℕ) (L : List ℕ) : Bool := Nat.beq F 0 || mem F L

-- the tables 0 and those of L, as a bit set
def zset : List ℕ → ℕ
  | [] => 1 <<< 0
  | a :: r => zset r ||| (1 <<< a)

-- the tables of ts that are not marked in Z, without repetition
def nwb (Z : ℕ) (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | t :: r => if Z.testBit t = true then nwb Z acc r else nwb (Z ||| (1 <<< t)) (t :: acc) r

def nw' (L P : List ℕ) : List ℕ := nwb (zset L) [] P

def orHit (F t : ℕ) : List ℕ → Bool
  | [] => false
  | c :: r => Nat.beq (t ||| c) F || orHit F t r

def andHit (F t : ℕ) : List ℕ → Bool
  | [] => false
  | c :: r => Nat.beq (t &&& c) F || andHit F t r

-- can a gate reading the new table t and one old table give F
def newOK (F t : ℕ) (L : List ℕ) : Bool :=
  (Nat.beq (t ||| F) F && orHit F t L) || (Nat.beq (t &&& F) F && andHit F t L)

-- at most two gates from L (P is prs M L)
def two (F : ℕ) (L P : List ℕ) : Bool := c0 F L || mem F P || P.any (fun t => newOK F t L)

-- at most two gates from t :: L that use the new table t (P is prs M L)
def twoNew (F t : ℕ) (L P : List ℕ) : Bool :=
  Nat.beq F t || newOK F t L ||
    L.any (fun d => newOK F (t &&& d) (t :: L) || newOK F (t ||| d) (t :: L)) ||
    ((Nat.beq (t ||| F) F || Nat.beq (t &&& F) F) && P.any (fun s => newOK F s [t]))

def can (M F : ℕ) : ℕ → List ℕ → Bool
  | 0, L => c0 F L
  | 1, L => c0 F L || mem F (prs M L)
  | 2, L => two F L (prs M L)
  | 3, L => two F L (prs M L) || (nw' L (prs M L)).any (fun t => twoNew F t L (prs M L))
  | k + 4, L => c0 F L || (nw' L (prs M L)).any (fun t => can M F (k + 3) (t :: L))

theorem mem_iff (t : ℕ) (L : List ℕ) : mem t L = true ↔ t ∈ L := by
  induction L with
  | nil => simp [mem]
  | cons a r ih => simp [mem, ih]

theorem pairsWith_mem (a x : ℕ) (acc r : List ℕ) :
    x ∈ pairsWith a acc r ↔ x ∈ acc ∨ ∃ c ∈ r, x = a &&& c ∨ x = a ||| c := by
  induction r with
  | nil => simp [pairsWith]
  | cons b r ih =>
    simp only [pairsWith, List.mem_cons, ih, or_and_right, exists_or, exists_eq_left]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | (h | h) | h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

theorem prs_cons (M t x : ℕ) (L : List ℕ) :
    x ∈ prs M (t :: L) ↔ x ∈ prs M L ∨ ∃ c ∈ L, x = t &&& c ∨ x = t ||| c := by
  simp only [prs, pairsWith_mem]

theorem M_mem (M : ℕ) (L : List ℕ) : M ∈ prs M L := by
  induction L with
  | nil => simp [prs]
  | cons a r ih => exact (prs_cons M a M r).2 (Or.inl ih)

theorem pair_mem (M a b : ℕ) (L : List ℕ) (ha : a ∈ L) (hb : b ∈ L) :
    (a &&& b ∈ L ∨ a &&& b ∈ prs M L) ∧ (a ||| b ∈ L ∨ a ||| b ∈ prs M L) := by
  induction L with
  | nil => simp at ha
  | cons x r ih =>
    rcases List.mem_cons.1 ha with ha1 | ha1 <;> rcases List.mem_cons.1 hb with hb1 | hb1
    · rw [ha1, hb1]
      simp
    · rw [ha1]
      refine ⟨Or.inr ((prs_cons M x _ r).2 (Or.inr ⟨b, hb1, Or.inl rfl⟩)),
        Or.inr ((prs_cons M x _ r).2 (Or.inr ⟨b, hb1, Or.inr rfl⟩))⟩
    · rw [hb1]
      refine ⟨Or.inr ((prs_cons M x _ r).2 (Or.inr ⟨a, ha1, Or.inl (Nat.land_comm _ _)⟩)),
        Or.inr ((prs_cons M x _ r).2 (Or.inr ⟨a, ha1, Or.inr (Nat.lor_comm _ _)⟩))⟩
    · obtain ⟨h1, h2⟩ := ih ha1 hb1
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ((prs_cons M x _ r).2 (Or.inl h1))
      · rcases h2 with h2 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h2)
        · exact Or.inr ((prs_cons M x _ r).2 (Or.inl h2))

theorem and_in (M a b : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) (hb : b = 0 ∨ b ∈ L) :
    a &&& b = 0 ∨ a &&& b ∈ L ∨ a &&& b ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; simp
  rcases hb with hb | hb
  · subst hb; simp
  exact Or.inr (pair_mem M a b L ha hb).1

theorem or_in (M a b : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) (hb : b = 0 ∨ b ∈ L) :
    a ||| b = 0 ∨ a ||| b ∈ L ∨ a ||| b ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; rw [Nat.zero_or]; tauto
  rcases hb with hb | hb
  · subst hb; rw [Nat.or_zero]; tauto
  exact Or.inr (pair_mem M a b L ha hb).2

theorem zset_bit (L : List ℕ) (t : ℕ) (h : (zset L).testBit t = true) : t = 0 ∨ t ∈ L := by
  induction L with
  | nil =>
    simp only [zset, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at h
    exact Or.inl h.symm
  | cons a r ih =>
    simp only [zset, Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · rcases ih h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)
    · exact Or.inr (by rw [h]; exact List.mem_cons_self)

theorem nwb_acc (Z : ℕ) (acc ts : List ℕ) (t : ℕ) (h : t ∈ acc) : t ∈ nwb Z acc ts := by
  induction ts generalizing Z acc with
  | nil => simpa [nwb] using h
  | cons s r ih =>
    simp only [nwb]
    split
    · exact ih Z acc h
    · exact ih _ (s :: acc) (List.mem_cons_of_mem _ h)

theorem nwb_mem (ts : List ℕ) (t : ℕ) (h : t ∈ ts) :
    ∀ (Z : ℕ) (acc : List ℕ), (Z.testBit t = false ∨ t ∈ acc) → t ∈ nwb Z acc ts := by
  induction ts with
  | nil => simp at h
  | cons s r ih =>
    intro Z acc hZ
    simp only [nwb]
    split
    · rename_i hs
      rcases List.mem_cons.1 h with h1 | h1
      · subst h1
        rcases hZ with hZ | hZ
        · rw [hZ] at hs; exact absurd hs (by decide)
        · exact nwb_acc Z acc r t hZ
      · exact ih h1 Z acc hZ
    · rename_i hs
      rcases List.mem_cons.1 h with h1 | h1
      · subst h1
        exact nwb_acc _ (t :: acc) r t List.mem_cons_self
      · apply ih h1
        by_cases hts : t = s
        · exact Or.inr (by rw [hts]; exact List.mem_cons_self)
        · rcases hZ with hZ | hZ
          · left
            simp only [Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow, hZ,
              Bool.false_or, decide_eq_false_iff_not]
            exact fun e => hts e.symm
          · exact Or.inr (List.mem_cons_of_mem _ hZ)

theorem nw'_mem (L P : List ℕ) (t : ℕ) (h : t ∈ P) (h0 : t ≠ 0) (hL : t ∉ L) : t ∈ nw' L P := by
  apply nwb_mem P t h
  left
  cases hb : (zset L).testBit t
  · rfl
  · rcases zset_bit L t hb with h1 | h1
    · exact absurd h1 h0
    · exact absurd h1 hL

theorem orHit_iff (F t : ℕ) (L : List ℕ) : orHit F t L = true ↔ ∃ c ∈ L, t ||| c = F := by
  induction L with
  | nil => simp [orHit]
  | cons c r ih => simp [orHit, ih]

theorem andHit_iff (F t : ℕ) (L : List ℕ) : andHit F t L = true ↔ ∃ c ∈ L, t &&& c = F := by
  induction L with
  | nil => simp [andHit]
  | cons c r ih => simp [andHit, ih]

theorem newOK_complete (F t : ℕ) (L : List ℕ)
    (h : ∃ c ∈ L, F = t &&& c ∨ F = t ||| c) : newOK F t L = true := by
  unfold newOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, orHit_iff, andHit_iff]
  rcases h with ⟨c, hc, h | h⟩
  · right
    refine ⟨?_, c, hc, h.symm⟩
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_land]
  · left
    refine ⟨?_, c, hc, h.symm⟩
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_lor]

theorem newOK_ex (F t : ℕ) (L : List ℕ) (h : newOK F t L = true) :
    ∃ c ∈ L, F = t &&& c ∨ F = t ||| c := by
  unfold newOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, orHit_iff, andHit_iff] at h
  rcases h with ⟨_, c, hc, h⟩ | ⟨_, c, hc, h⟩
  · exact ⟨c, hc, Or.inr h.symm⟩
  · exact ⟨c, hc, Or.inl h.symm⟩

theorem newOK_sound (M F t : ℕ) (L : List ℕ) (h : newOK F t L = true) :
    F ∈ prs M (t :: L) := (prs_cons M t F L).2 (Or.inr (newOK_ex F t L h))

-- a gate built only from old tables adds nothing new
theorem absorb (M t x : ℕ) (L : List ℕ) (ht : t = 0 ∨ t ∈ L) (hx : x ∈ prs M (t :: L)) :
    x = 0 ∨ x ∈ L ∨ x ∈ prs M L := by
  rcases (prs_cons M t x L).1 hx with h | ⟨c, hc, h | h⟩
  · exact Or.inr (Or.inr h)
  · subst h; exact and_in M t c L ht (Or.inr hc)
  · subst h; exact or_in M t c L ht (Or.inr hc)

theorem c0_iff (F : ℕ) (L : List ℕ) : c0 F L = true ↔ F = 0 ∨ F ∈ L := by
  simp [c0, mem_iff]

theorem two_of_c0 (F : ℕ) (L P : List ℕ) (h : c0 F L = true) : two F L P = true := by
  simp [two, h]

theorem two_of_mem (F : ℕ) (L P : List ℕ) (h : F ∈ P) : two F L P = true := by
  simp [two, mem_iff, h]

theorem two_of_new (F t : ℕ) (L P : List ℕ) (ht : t ∈ P) (h : newOK F t L = true) :
    two F L P = true := by
  simp only [two, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨t, ht, h⟩

theorem tn_eq (F : ℕ) (L P : List ℕ) : twoNew F F L P = true := by
  simp [twoNew]

theorem tn_new (F t : ℕ) (L P : List ℕ) (h : newOK F t L = true) : twoNew F t L P = true := by
  simp [twoNew, h]

theorem tn_and (F t d : ℕ) (L P : List ℕ) (hd : d ∈ L) (h : newOK F (t &&& d) (t :: L) = true) :
    twoNew F t L P = true := by
  simp only [twoNew, Bool.or_eq_true, List.any_eq_true]
  exact Or.inl (Or.inr ⟨d, hd, Or.inl h⟩)

theorem tn_or (F t d : ℕ) (L P : List ℕ) (hd : d ∈ L) (h : newOK F (t ||| d) (t :: L) = true) :
    twoNew F t L P = true := by
  simp only [twoNew, Bool.or_eq_true, List.any_eq_true]
  exact Or.inl (Or.inr ⟨d, hd, Or.inr h⟩)

theorem tn_c (F t s : ℕ) (L P : List ℕ) (hs : s ∈ P) (h : F = s &&& t ∨ F = s ||| t) :
    twoNew F t L P = true := by
  simp only [twoNew, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, Nat.beq_eq]
  refine Or.inr ⟨?_, s, hs, newOK_complete F s [t] ⟨t, List.mem_singleton_self t, h⟩⟩
  rcases h with h | h
  · right
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_land]
    cases Nat.testBit t i <;> cases Nat.testBit s i <;> rfl
  · left
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_lor]
    cases Nat.testBit t i <;> cases Nat.testBit s i <;> rfl

-- the new table t as the first of two gates
theorem twoNew_two (M F t : ℕ) (L : List ℕ) (h : twoNew F t L (prs M L) = true) :
    two F (t :: L) (prs M (t :: L)) = true := by
  unfold twoNew at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, List.any_eq_true] at h
  rcases h with ((h | h) | ⟨d, hd, h | h⟩) | ⟨_, s, hs, h⟩
  · exact two_of_c0 F _ _ (by rw [c0_iff, h]; exact Or.inr List.mem_cons_self)
  · exact two_of_mem F _ _ (newOK_sound M F t L h)
  · exact two_of_new F _ _ _ ((prs_cons M t _ L).2 (Or.inr ⟨d, hd, Or.inl rfl⟩)) h
  · exact two_of_new F _ _ _ ((prs_cons M t _ L).2 (Or.inr ⟨d, hd, Or.inr rfl⟩)) h
  · obtain ⟨c, hc, hF⟩ := newOK_ex F s [t] h
    rw [List.mem_singleton] at hc
    subst hc
    exact two_of_new F s _ _ ((prs_cons M c s L).2 (Or.inl hs))
      (newOK_complete F s (c :: L) ⟨c, List.mem_cons_self, hF⟩)

-- at most two gates from t :: L: either they do not need t, or twoNew finds them
theorem step3 (M F t : ℕ) (L : List ℕ) (h : two F (t :: L) (prs M (t :: L)) = true) :
    two F L (prs M L) = true ∨ twoNew F t L (prs M L) = true := by
  unfold two at h
  simp only [Bool.or_eq_true, mem_iff, List.any_eq_true, c0_iff, List.mem_cons] at h
  rcases h with ((h | h | h) | h) | ⟨x, hx, h⟩
  · exact Or.inl (two_of_c0 F _ _ (by rw [c0_iff]; exact Or.inl h))
  · subst h; exact Or.inr (tn_eq F _ _)
  · exact Or.inl (two_of_c0 F _ _ (by rw [c0_iff]; exact Or.inr h))
  · rcases (prs_cons M t F L).1 h with h1 | h1
    · exact Or.inl (two_of_mem F _ _ h1)
    · exact Or.inr (tn_new F t L _ (newOK_complete F t L h1))
  · obtain ⟨c, hc, hF⟩ := newOK_ex F x (t :: L) h
    rcases (prs_cons M t x L).1 hx with hx1 | ⟨d, hd, hx1 | hx1⟩
    · rcases List.mem_cons.1 hc with hc1 | hc1
      · subst hc1; exact Or.inr (tn_c F c x L _ hx1 hF)
      · exact Or.inl (two_of_new F x L _ hx1 (newOK_complete F x L ⟨c, hc1, hF⟩))
    · subst hx1; exact Or.inr (tn_and F t d L _ hd h)
    · subst hx1; exact Or.inr (tn_or F t d L _ hd h)

theorem can_of_c0 (M F k : ℕ) (L : List ℕ) (h : c0 F L = true) : can M F k L = true := by
  rcases k with _ | _ | _ | _ | k <;> simp [can, two, h]

-- a found table F one gate away
theorem can_of_prs (M F k : ℕ) (L : List ℕ) (h : F ∈ prs M L) : can M F (k + 1) L = true := by
  rcases k with _ | _ | _ | k
  · simp [can, mem_iff, h]
  · exact two_of_mem F L _ h
  · simp [can, two, mem_iff, h]
  · by_cases hc : c0 F L = true
    · exact can_of_c0 M F _ L hc
    · rw [c0_iff] at hc
      push_neg at hc
      show (c0 F L || (nw' L (prs M L)).any (fun t => can M F (k + 3) (t :: L))) = true
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨F, nw'_mem L _ F h hc.1 hc.2, can_of_c0 M F _ _ (by simp [c0, mem_iff])⟩

theorem two_can (M F k : ℕ) (L : List ℕ) (h : two F L (prs M L) = true) :
    can M F (k + 2) L = true := by
  rcases k with _ | _ | k
  · exact h
  · simp [can, h]
  · unfold two at h
    simp only [Bool.or_eq_true, mem_iff, List.any_eq_true] at h
    rcases h with (h | h) | ⟨t, ht, h⟩
    · exact can_of_c0 M F _ L h
    · exact can_of_prs M F (k + 3) L h
    · have hF := newOK_sound M F t L h
      by_cases h0 : t = 0 ∨ t ∈ L
      · rcases absorb M t F L h0 hF with h1 | h1 | h1
        · exact can_of_c0 M F _ L (by simp [c0, h1])
        · exact can_of_c0 M F _ L (by simp [c0, mem_iff, h1])
        · exact can_of_prs M F (k + 3) L h1
      · push_neg at h0
        show (c0 F L || (nw' L (prs M L)).any (fun t => can M F (k + 3) (t :: L))) = true
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨t, nw'_mem L _ t ht h0.1 h0.2, can_of_prs M F (k + 2) (t :: L) hF⟩

theorem mono (M F : ℕ) : ∀ (k : ℕ) (L : List ℕ), can M F k L = true → can M F (k + 1) L = true := by
  intro k
  induction k with
  | zero =>
    intro L h
    exact can_of_c0 M F 1 L h
  | succ k ih =>
    intro L h
    rcases k with _ | _ | _ | k
    · simp only [can, Bool.or_eq_true, mem_iff] at h
      rcases h with h | h
      · exact can_of_c0 M F 2 L h
      · exact can_of_prs M F 1 L h
    · exact two_can M F 1 L h
    · have h' : (two F L (prs M L) ||
          (nw' L (prs M L)).any (fun t => twoNew F t L (prs M L))) = true := h
      simp only [Bool.or_eq_true, List.any_eq_true] at h'
      rcases h' with h' | ⟨t, ht, h'⟩
      · exact two_can M F 2 L h'
      · show (c0 F L || (nw' L (prs M L)).any (fun t => can M F 3 (t :: L))) = true
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨t, ht, two_can M F 1 (t :: L) (twoNew_two M F t L h')⟩
    · show (c0 F L || (nw' L (prs M L)).any (fun t => can M F (k + 1 + 3) (t :: L))) = true
      have h' : (c0 F L || (nw' L (prs M L)).any (fun t => can M F (k + 3) (t :: L))) = true := h
      simp only [Bool.or_eq_true, List.any_eq_true] at h' ⊢
      rcases h' with h' | ⟨t, ht, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨t, ht, ih (t :: L) h'⟩

-- one new gate whose table t is new
theorem can_step (M F k t : ℕ) (L : List ℕ) (ht : t ∈ prs M L) (h0 : t ≠ 0) (hL : t ∉ L)
    (h : can M F k (t :: L) = true) : can M F (k + 1) L = true := by
  rcases k with _ | _ | _ | k
  · simp only [can, c0_iff, List.mem_cons] at h
    rcases h with h | h | h
    · exact can_of_c0 M F 1 L (by simp [c0, h])
    · subst h; exact can_of_prs M F 0 L ht
    · exact can_of_c0 M F 1 L (by simp [c0, mem_iff, h])
  · simp only [can, Bool.or_eq_true, c0_iff, List.mem_cons, mem_iff] at h
    rcases h with (h | h | h) | h
    · exact can_of_c0 M F 2 L (by simp [c0, h])
    · subst h; exact can_of_prs M F 1 L ht
    · exact can_of_c0 M F 2 L (by simp [c0, mem_iff, h])
    · rcases (prs_cons M t F L).1 h with h1 | h1
      · exact can_of_prs M F 1 L h1
      · exact two_of_new F t L _ ht (newOK_complete F t L h1)
  · rcases step3 M F t L h with h1 | h1
    · show (two F L (prs M L) || (nw' L (prs M L)).any (fun t => twoNew F t L (prs M L))) = true
      simp [h1]
    · show (two F L (prs M L) || (nw' L (prs M L)).any (fun t => twoNew F t L (prs M L))) = true
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨t, nw'_mem L _ t ht h0 hL, h1⟩
  · show (c0 F L || (nw' L (prs M L)).any (fun t => can M F (k + 3) (t :: L))) = true
    simp only [Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨t, nw'_mem L _ t ht h0 hL, h⟩

-- every wire i (also a missing one) is matched on rows j < N by zero or a table of L
def Inv (N : ℕ) (L : List ℕ) (w : ℕ → List Bool) : Prop :=
  ∀ i, ∃ a, (a = 0 ∨ a ∈ L) ∧ ∀ j < N, a.testBit j = (w j).getD i false

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eq_of_bits (N a b : ℕ) (ha : a < 2 ^ N) (hb : b < 2 ^ N)
    (h : ∀ j < N, a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · exact h i hi
  · have hp : 2 ^ N ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem gate_tab (N M : ℕ) (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N)
    (L : List ℕ) (hb : ∀ a ∈ L, a < 2 ^ N) (w : ℕ → List Bool) (hI : Inv N L w) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ t, (t = 0 ∨ t ∈ L ∨ t ∈ prs M L) ∧ t < 2 ^ N ∧
      ∀ j < N, t.testBit j = g.op.eval (g.inputs.map fun i => (w j).getD i false) := by
  have hz : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
  have hbd : ∀ a, (a = 0 ∨ a ∈ L) → a < 2 ^ N := by
    intro a ha
    rcases ha with ha | ha
    · rw [ha]; exact hz
    · exact hb a ha
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with hop | hop <;> subst hop
    · exact ⟨M, Or.inr (Or.inr (M_mem M L)), hMb, fun j hj => by simp [GateOp.eval, hM j hj]⟩
    · exact ⟨0, Or.inl rfl, hz, fun j _ => by simp [GateOp.eval]⟩
  | [i], _ =>
    obtain ⟨a, ha, haw⟩ := hI i
    rcases hop with hop | hop <;> subst hop
    · exact ⟨a, by tauto, hbd a ha, fun j hj => by simp [GateOp.eval, haw j hj]⟩
    · exact ⟨a, by tauto, hbd a ha, fun j hj => by simp [GateOp.eval, haw j hj]⟩
  | [i1, i2], _ =>
    obtain ⟨a, ha, haw⟩ := hI i1
    obtain ⟨b, hb', hbw⟩ := hI i2
    rcases hop with hop | hop <;> subst hop
    · refine ⟨a &&& b, and_in M a b L ha hb', Nat.and_lt_two_pow _ (hbd b hb'), fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_land, haw j hj, hbw j hj]
    · refine ⟨a ||| b, or_in M a b L ha hb', Nat.or_lt_two_pow (hbd a ha) (hbd b hb'),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_lor, haw j hj, hbw j hj]
  | _ :: _ :: _ :: _, h => simp at h

theorem getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_pos h, List.getElem?_append_left h]
  · subst h
    simp
  · rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem inv_snoc (N m : ℕ) (L L' : List ℕ) (w : ℕ → List Bool) (v : ℕ → Bool) (t : ℕ)
    (hw : ∀ j, (w j).length = m) (hI : Inv N L w) (hLL : ∀ a ∈ L, a ∈ L')
    (ht : t = 0 ∨ t ∈ L') (htv : ∀ j < N, t.testBit j = v j) :
    Inv N L' (fun j => w j ++ [v j]) := by
  intro i
  by_cases h1 : i < m
  · obtain ⟨a, ha, haw⟩ := hI i
    refine ⟨a, ?_, fun j hj => ?_⟩
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (hLL a ha)
    · simp only [getD_snoc, hw j, if_pos h1]
      exact haw j hj
  · by_cases h2 : i = m
    · refine ⟨t, ht, fun j hj => ?_⟩
      simp only [getD_snoc, hw j, if_neg h1, if_pos h2]
      exact htv j hj
    · refine ⟨0, Or.inl rfl, fun j hj => ?_⟩
      simp only [getD_snoc, hw j, if_neg h1, if_neg h2, Nat.zero_testBit]

theorem sound (N M F : ℕ) (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N)
    (hF : F < 2 ^ N) :
    ∀ (gs : List Gate) (k m : ℕ) (L : List ℕ) (w : ℕ → List Bool),
      (∀ a ∈ L, a < 2 ^ N) → (∀ j, (w j).length = m) → Inv N L w →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      gs.length ≤ k → ∀ o : ℕ,
      (∀ j < N, (gs.foldl stp (w j)).getD o false = F.testBit j) → can M F k L = true := by
  intro gs
  induction gs with
  | nil =>
    intro k m L w hb _ hI _ _ o ho
    obtain ⟨a, ha, haw⟩ := hI o
    have hab : a < 2 ^ N := by
      rcases ha with ha | ha
      · rw [ha]; exact Nat.two_pow_pos N
      · exact hb a ha
    have hEq : a = F := eq_of_bits N a F hab hF (fun j hj => by
      rw [haw j hj]; exact ho j hj)
    exact can_of_c0 M F k L (by rw [c0_iff, ← hEq]; tauto)
  | cons g gs ih =>
    intro k m L w hb hw hI hg hk o ho
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hk' : gs.length ≤ k := by simp at hk; omega
    obtain ⟨t, htm, htb, htv⟩ :=
      gate_tab N M hM hMb L hb w hI g (hg g List.mem_cons_self).1 (hg g List.mem_cons_self).2
    have hw' : ∀ j, (stp (w j) g).length = m + 1 := by
      intro j; simp [stp, hw j]
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' h' => hg g' (List.mem_cons_of_mem _ h')
    have ho' : ∀ j < N, (gs.foldl stp (stp (w j) g)).getD o false = F.testBit j := ho
    by_cases hold : t = 0 ∨ t ∈ L
    · have hI' : Inv N L (fun j => stp (w j) g) :=
        inv_snoc N m L L w _ t hw hI (fun a h => h) hold htv
      exact mono M F k L (ih k (m + 1) L _ hb hw' hI' hg' hk' o ho')
    · push_neg at hold
      have htp : t ∈ prs M L := by
        rcases htm with h | h | h
        · exact absurd h hold.1
        · exact absurd h hold.2
        · exact h
      have hI' : Inv N (t :: L) (fun j => stp (w j) g) :=
        inv_snoc N m L (t :: L) w _ t hw hI (fun a h => List.mem_cons_of_mem _ h)
          (Or.inr List.mem_cons_self) htv
      have hb' : ∀ a ∈ t :: L, a < 2 ^ N := by
        intro a h
        rcases List.mem_cons.1 h with h | h
        · rw [h]; exact htb
        · exact hb a h
      exact can_step M F k t L htp hold.1 hold.2 (ih k (m + 1) (t :: L) _ hb' hw' hI' hg' hk' o ho')

-- the 16 rows: row j is the input with left vertex j / 4 and right vertex j mod 4 on
def L0 : List ℕ := [0x000F, 0x00F0, 0x0F00, 0xF000, 0x1111, 0x2222, 0x4444, 0x8888]

def row (j : ℕ) : List Bool :=
  PEqualNP.Represents.oneEach (n := 4) (m := 4) ⟨j / 4 % 4, Nat.mod_lt _ (by norm_num)⟩
    ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩

theorem row_len (j : ℕ) : (row j).length = 8 := by
  simp [row, PEqualNP.Represents.oneEach]

theorem row_tab : ∀ i < 8, ∀ j < 16, (L0.getD i 0).testBit j = (row j).getD i false := by
  decide

theorem L0_mem : ∀ i < 8, L0.getD i 0 ∈ L0 := by
  decide

theorem inv0 : Inv 16 L0 row := by
  intro i
  by_cases hi : i < 8
  · exact ⟨L0.getD i 0, Or.inr (L0_mem i hi), row_tab i hi⟩
  · refine ⟨0, Or.inl rfl, fun j _ => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [row_len]; omega)]

theorem low_gen (F T K : ℕ) (hT : T < 2 ^ 16) (hFT : ∀ j < 16, F.testBit j = T.testBit j)
    (hs : can 0xFFFF T K L0 = false) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => F.testBit (4 * u.val + v.val)) K := by
  rintro ⟨C, hmono, hsize, hrep⟩
  have ho : ∀ j < 16, (C.gates.foldl stp (row j)).getD C.output false = T.testBit j := by
    intro j hj
    rw [← hFT j hj]
    have h1 := hrep ⟨j / 4 % 4, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩
    have e : 4 * (j / 4 % 4) + j % 4 = j := by omega
    simp only [e] at h1
    exact h1
  have h2 := sound 16 0xFFFF T (by decide) (by decide) hT C.gates K 8 L0 row (by decide) row_len
    inv0 hmono hsize C.output ho
  rw [hs] at h2
  exact absurd h2 (by decide)

-- a circuit of 5 gates (wires 0 to 3 are the left vertices, 4 to 7 the right ones)
def Cup : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem up : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (53 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  refine ⟨Cup, ?_, by decide, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl

-- no circuit of 4 gates: the table search finds none
theorem search : can 0xFFFF 0x0035 4 L0 = false := by
  decide +kernel

theorem low : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (53 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  low_gen 53 0x0035 4 (by decide) (by decide) search

theorem both : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (53 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (53 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  ⟨up, low⟩

end PEqualNP.Outside.L_meta_5601_aux

theorem PEqualNP.Outside.L_meta_5601 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (53 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (53 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  exact PEqualNP.Outside.L_meta_5601_aux.both
