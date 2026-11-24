import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4932_aux

def columns : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
def row (r : Nat) (i : Fin 14) : Bool := (columns.getD i.val 0).getLsbD r
def positive : List Nat := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
def negative : List Nat := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

theorem positiveBits : ∀ p : Fin 21, ∀ i : Fin 14,
    (positive.getD p.val 0).testBit i.val = row p.val i := by decide +kernel
theorem negativeBits : ∀ q : Fin 37, ∀ i : Fin 14,
    (negative.getD q.val 0).testBit i.val = row (21+q.val) i := by decide +kernel

def covered (m : Nat) : Bool :=
  positive.any (fun p => (p &&& m) == p) || negative.any (fun q => (m &&& q) == m)
theorem audit : ((List.range 128).all fun h => (List.range 128).all fun l =>
    covered (128 * h + l)) = true := by decide +kernel
theorem complete (m : Nat) (hm : m < 16384) : covered m = true := by
  have ha := List.all_eq_true.mp audit (m / 128) (List.mem_range.mpr (by omega))
  have hb := List.all_eq_true.mp ha (m % 128) (List.mem_range.mpr (by omega))
  rwa [show 128 * (m / 128) + m % 128 = m by omega] at hb

def bits (x : Fin 14 → Bool) : BitVec 14 :=
  (BitVec.ofBoolListLE (List.ofFn x)).cast List.length_ofFn
theorem inputBit (x : Fin 14 → Bool) (i : Fin 14) :
    (bits x).toNat.testBit i.val = x i := by
  change (bits x).getLsbD i.val = x i
  simp only [bits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
theorem leBit {u v : Nat} (h : u &&& v = u) (i : Nat) : u.testBit i ≤ v.testBit i := by
  have e := congrArg (fun t : Nat => t.testBit i) h
  change (u &&& v).testBit i = u.testBit i at e
  rw [Nat.testBit_and] at e
  cases ha : u.testBit i <;> cases hb : v.testBit i <;> simp_all

theorem proof (x : Fin 14 → Bool) (hx : ∀ p : Fin 21, ¬ row p.val ≤ x) :
    ∃ q : Fin 37, x ≤ row (21+q.val) := by
  let m := (bits x).toNat
  have hm : m < 16384 := (bits x).isLt
  have hc := complete m hm
  rw [covered, Bool.or_eq_true] at hc
  rcases hc with h | h
  · obtain ⟨p, hp, he⟩ := List.any_eq_true.mp h
    obtain ⟨j, hj, hjp⟩ := List.getElem_of_mem hp
    have hj' : j < 21 := hj
    let ji : Fin 21 := ⟨j, hj'⟩
    apply False.elim
    apply hx ji
    intro i
    have hh := leBit (beq_iff_eq.mp he) i.val
    have hjr : positive.getD ji.val 0 = p := by simpa [ji, List.getD_eq_getElem?_getD, hj] using hjp
    rw [← positiveBits ji i, hjr, ← inputBit x i]
    exact hh
  · obtain ⟨q, hq, he⟩ := List.any_eq_true.mp h
    obtain ⟨j, hj, hjq⟩ := List.getElem_of_mem hq
    have hj' : j < 37 := hj
    let ji : Fin 37 := ⟨j, hj'⟩
    refine ⟨ji, fun i => ?_⟩
    have hh := leBit (beq_iff_eq.mp he) i.val
    have hjr : negative.getD ji.val 0 = q := by simpa [ji, List.getD_eq_getElem?_getD, hj] using hjq
    rw [← negativeBits ji i, hjr, ← inputBit x i]
    exact hh
end PEqualNP.Outside.L_meta_4932_aux

theorem PEqualNP.Outside.L_meta_4932 : have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; have x2 : ℕ → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 : Fin (14 : ℕ)) => (x1.getD ↑x3 (0 : BitVec (58 : ℕ))).getLsbD x2; ∀ (x3 : Fin (14 : ℕ) → Bool), (∀ (x4 : Fin (21 : ℕ)), ¬x2 ↑x4 ≤ x3) → ∃ (x5 : Fin (37 : ℕ)), x3 ≤ x2 ((21 : ℕ) + ↑x5) := PEqualNP.Outside.L_meta_4932_aux.proof
