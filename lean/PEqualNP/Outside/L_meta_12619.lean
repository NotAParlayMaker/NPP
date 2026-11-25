import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12619

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

lemma nat_land (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma nat_lor (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nat_xor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nat_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma nat_add (a b : ℕ) : Nat.add a b = a + b := rfl
lemma nat_sub (a b : ℕ) : Nat.sub a b = a - b := rfl

lemma nat_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hb) h

lemma bv_toNat_not {n : ℕ} (w : BitVec n) : (~~~w).toNat = Nat.xor w.toNat (2 ^ n - 1) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [nat_xor, BitVec.testBit_toNat, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat]
  by_cases hk : k < n
  · simp [hk]
  · simp [hk, BitVec.getLsbD_of_ge w k (Nat.le_of_not_lt hk)]

def elemN (w : ℕ) : List ℕ → Bool
  | [] => false
  | x :: xs => Nat.beq x w || elemN w xs

lemma elemN_map_false {n : ℕ} {w : BitVec n} {r : List (BitVec n)} (h : w ∉ r) :
    elemN w.toNat (r.map BitVec.toNat) = false := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.map_cons, elemN, Bool.or_eq_false_iff]
    exact ⟨nat_beq_false (fun he => h.1 (BitVec.eq_of_toNat_eq he.symm)), ih h.2⟩

abbrev W4 := BitVec 110
def M4 : ℕ := 0x7fffffffffffff
def A4 : ℕ := 0x3fffffffffffffffffffffffffff
def G4 : ℕ := 0x3fffffffffffff80000000000000
def goal4 : W4 := BitVec.ofNat 110 G4
def ops4 (x y : W4) : List W4 := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps4 (a b : W4) : Finset W4 := (ops4 a b).toFinset
def sep4 (x : W4) : BitVec 55 := ((x >>> 55) ^^^ x).setWidth 55
def cuts4 (ws : List W4) : BitVec 55 := ws.foldr (fun w v => sep4 w ||| v) 0
def k4inputs : List W4 := [BitVec.ofNat 110 0x2add5bab756ead800000003ff800, BitVec.ofNat 110 0x336e6dcdb9b736800001ffc00000, BitVec.ofNat 110 0x3c778ef1de3bc7000ffe00000000, BitVec.ofNat 110 0x3f87f0fe1fc3f87ff00000000000]

lemma hM4_pow : M4 = 2 ^ 55 - 1 := by decide
lemma hA4_pow : A4 = 2 ^ 110 - 1 := by decide

def sep4N (w : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight w 55) w) 0x7fffffffffffff

lemma sep4_toNat (w : W4) : (sep4 w).toNat = sep4N w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [sep4N, show (0x7fffffffffffff : ℕ) = 2 ^ 55 - 1 from hM4_pow, nat_land, nat_xor, nat_shr]
  rw [BitVec.testBit_toNat, Nat.testBit_land, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat]
  by_cases hk : k < 55
  · simp [sep4, hk, Nat.add_comm]
  · rw [BitVec.getLsbD_of_ge (sep4 w) k (Nat.le_of_not_lt hk)]; simp [hk]

def cuts4N : List ℕ → ℕ
  | [] => 0
  | w :: r => Nat.lor (sep4N w) (cuts4N r)

lemma cuts4N_map (ws : List W4) : cuts4N (ws.map BitVec.toNat) = (cuts4 ws).toNat := by
  induction ws with
  | nil => simp [cuts4, cuts4N]
  | cons w r ih =>
    simp only [List.map_cons, cuts4N, cuts4, List.foldr_cons, BitVec.toNat_or, sep4_toNat, ih]
    rfl

def differs4 (i : Fin 55) (w : W4) : Prop :=
  w.getLsbD (55 + i.val) ≠ w.getLsbD i.val

theorem ops4_differs (i : Fin 55) (a b z : W4) (hz : z ∈ basicOps4 a b)
    (hd : differs4 i z) : differs4 i a ∨ differs4 i b := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs4 at ha hb
  simp only [not_not] at ha hb
  have hi : 55 + i.val < 110 := by omega
  have hi' : i.val < 110 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts4_spec (ws : List W4) (i : Fin 55) :
    (cuts4 ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs4 i w := by
  induction ws with
  | nil => simp [cuts4]
  | cons a rest ih =>
    change (sep4 a ||| cuts4 rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep4, i.isLt, differs4, Nat.add_comm, bx]

theorem cuts4_full {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) {k : ℕ} {ws : List W4}
    (h : live basicOps4 g k ws.toFinset) : cuts4N (ws.map BitVec.toNat) = M4 := by
  rw [cuts4N_map]
  have hd : ∀ i, differs4 i g := by rcases hg with rfl | rfl <;> unfold differs4 <;> decide +kernel
  have hall : cuts4 ws = -1 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    have hw := live_separates (differs4 ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops4_differs ⟨j, hj⟩) h
    have hbit := (cuts4_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
    change (cuts4 ws)[j] = (BitVec.allOnes 55)[j]
    rw [BitVec.getElem_allOnes]
    simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
  rw [hall]
  decide

theorem ops4_swap (a b : W4) : basicOps4 a b = basicOps4 b a := by
  ext z
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices4 (a b : W4) (r : List W4) : List (List W4) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept4 {ws r : List W4} {a b : W4} {needed : Finset W4}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices4 a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices4], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices4], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices4], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices4], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list4 {g : W4} {ws : List W4} (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def tryW4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (sa sb base : ℕ) (r : List ℕ) (w : ℕ) : Bool :=
  if Nat.beq w a || Nat.beq w b || elemN w r then false
  else
    let v := Nat.lor (sep4N w) base
    if Nat.beq v 0x7fffffffffffff && next extra (w :: r) then true
    else if Nat.beq extra 0 then false
    else if Nat.beq (Nat.lor v sa) 0x7fffffffffffff && next (Nat.sub extra 1) (w :: a :: r) then true
    else if Nat.beq (Nat.lor v sb) 0x7fffffffffffff && next (Nat.sub extra 1) (w :: b :: r) then true
    else if Nat.ble 2 extra && Nat.beq (Nat.lor (Nat.lor v sa) sb) 0x7fffffffffffff && next (Nat.sub extra 2) (w :: a :: b :: r) then true
    else false

def disp4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) : Bool :=
  let base := cuts4N r
  let sa := sep4N a
  let sb := sep4N b
  tryW4 extra next a b sa sb base r (Nat.land a b) ||
  tryW4 extra next a b sa sb base r (Nat.lor a b) ||
  tryW4 extra next a b sa sb base r (Nat.land a (Nat.xor b 0x3fffffffffffffffffffffffffff)) ||
  tryW4 extra next a b sa sb base r (Nat.land b (Nat.xor a 0x3fffffffffffffffffffffffffff))

def pickB4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a : ℕ) (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | b :: rest =>
    disp4 extra next a b (pre ++ rest) || pickB4 extra next a (b :: pre) rest

def pickA4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | a :: rest =>
    pickB4 extra next a pre rest || pickA4 extra next (a :: pre) rest

def opt4 : ℕ → ℕ → List ℕ → Bool
  | 0, _, ws => match ws with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false
  | k + 1, extra, ws =>
    (match ws with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false) ||
    pickA4 extra (opt4 k) [] ws

lemma pickB4_exists (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : W4) (pre ys : List W4)
    (hb : b ∈ ys) :
    ∃ r : List W4, (pre ++ ys).Perm (b :: r) ∧
      (disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true →
        pickB4 extra next a.toNat (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) := by
  induction ys generalizing pre with
  | nil => simp at hb
  | cons y rest ih =>
    rcases List.mem_cons.mp hb with rfl | hbr
    · refine ⟨pre ++ rest, List.perm_middle, fun hd => ?_⟩
      simp only [List.map_cons, pickB4, List.map_append] at hd ⊢
      rw [hd]; rfl
    · obtain ⟨r, hp, himp⟩ := ih (y :: pre) hbr
      refine ⟨r, List.perm_middle.trans hp, fun hd => ?_⟩
      have h := himp hd
      simp only [List.map_cons] at h
      simp only [List.map_cons, pickB4, h, Bool.or_true]

lemma pickA4_exists (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : W4) (pre ys : List W4)
    (ha : a ∈ ys) (hb : b ∈ ys) (hne : a ≠ b) :
    ∃ r : List W4, (pre ++ ys).Perm (a :: b :: r) ∧
      ((disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true →
          pickA4 extra next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) ∨
       (disp4 extra next b.toNat a.toNat (r.map BitVec.toNat) = true →
          pickA4 extra next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true)) := by
  induction ys generalizing pre with
  | nil => simp at ha
  | cons y rest ih =>
    rcases List.mem_cons.mp ha with rfl | har
    · have hbr : b ∈ rest := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      obtain ⟨r, hp, himp⟩ := pickB4_exists extra next a b pre rest hbr
      refine ⟨r, List.perm_middle.trans (hp.cons a), .inl fun hd => ?_⟩
      simp only [List.map_cons, pickA4, himp hd, Bool.true_or]
    · rcases List.mem_cons.mp hb with rfl | hbr
      · obtain ⟨r, hp, himp⟩ := pickB4_exists extra next b a pre rest har
        refine ⟨r, List.perm_middle.trans ((hp.cons b).trans (List.Perm.swap a b r)), .inr fun hd => ?_⟩
        simp only [List.map_cons, pickA4, himp hd, Bool.true_or]
      · obtain ⟨r, hp, himp⟩ := ih (y :: pre) har hbr
        refine ⟨r, List.perm_middle.trans hp, himp.imp (fun f hd => ?_) (fun f hd => ?_)⟩
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA4, h, Bool.or_true]
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA4, h, Bool.or_true]

theorem disp4_complete {k extra : ℕ} {a b z : W4} {r kept : List W4}
    (next : ℕ → List ℕ → Bool)
    (hz : z ∈ basicOps4 a b) (hza : z ≠ a) (hzb : z ≠ b) (hzr : z ∉ r)
    (hk : kept ∈ keepChoices4 a b r) (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts4N ((z :: kept).map BitVec.toNat) = M4)
    (ht : next (k - kept.length) ((z :: kept).map BitVec.toNat) = true) :
    disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true := by
  have htry : tryW4 extra next a.toNat b.toNat (sep4N a.toNat) (sep4N b.toNat)
      (cuts4N (r.map BitVec.toNat)) (r.map BitVec.toNat) z.toNat = true := by
    unfold tryW4
    have hna : Nat.beq z.toNat a.toNat = false := nat_beq_false (fun heq => hza (BitVec.eq_of_toNat_eq heq))
    have hnb : Nat.beq z.toNat b.toNat = false := nat_beq_false (fun heq => hzb (BitVec.eq_of_toNat_eq heq))
    have hnr : elemN z.toNat (r.map BitVec.toNat) = false := elemN_map_false hzr
    rw [hna, hnb, hnr]; simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    have hM4v : (0x7fffffffffffff : ℕ) = M4 := rfl
    simp only [hM4v]
    simp only [keepChoices4, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with hkeq | hkeq | hkeq | hkeq
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      have h1 : Nat.beq (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) M4 = true :=
        Nat.beq_eq.mpr hc
      have h2 : next extra (z.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using (show next extra ((z :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [h1, h2]; rfl
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N a.toNat) (cuts4N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 1) (z.toNat :: a.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) ((z :: a :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N b.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N b.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N b.toNat) (cuts4N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 1) (z.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) ((z :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have hge2 : Nat.ble 2 extra = true := Nat.ble_eq.mpr (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) (sep4N b.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) (sep4N b.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N a.toNat) (Nat.lor (sep4N b.toNat) (cuts4N (r.map BitVec.toNat)))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 2) (z.toNat :: a.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 2) ((z :: a :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, hge2, h1, h2]
      split_ifs <;> simp_all
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold disp4
  have hnot_b : (~~~b).toNat = Nat.xor b.toNat 0x3fffffffffffffffffffffffffff := by
    rw [show (0x3fffffffffffffffffffffffffff : ℕ) = 2 ^ 110 - 1 from hA4_pow]; exact bv_toNat_not b
  have hnot_a : (~~~a).toNat = Nat.xor a.toNat 0x3fffffffffffffffffffffffffff := by
    rw [show (0x3fffffffffffffffffffffffffff : ℕ) = 2 ^ 110 - 1 from hA4_pow]; exact bv_toNat_not a
  rcases hz with rfl | rfl | rfl | rfl
  · rw [BitVec.toNat_and, ← nat_land] at htry; simp only [htry, Bool.true_or]
  · rw [BitVec.toNat_or, ← nat_lor] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_b] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_a] at htry; simp only [htry, Bool.or_true]

theorem opt4_complete {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) (n : ℕ) (ws : List W4) (extra : ℕ)
    (hn : ws.Nodup) (room : extra + ws.length = n + 1) (h : live basicOps4 g n ws.toFinset) :
    opt4 n extra (ws.map BitVec.toNat) = true := by
  have hdone : ∀ (u : List W4), u.Nodup → u.toFinset = {g} →
      (match u.map BitVec.toNat with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false) = true := by
    intro u hun hu
    rw [singleton_list4 hun hu]
    rcases hg with rfl | rfl <;> decide
  induction n generalizing ws extra with
  | zero => exact hdone ws hn h
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp only [opt4, hdone ws hn done, Bool.true_or]
    · obtain ⟨r, hp, hpick⟩ := pickA4_exists extra (opt4 k) a b [] ws
        (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      simp only [List.nil_append] at hp
      have go {u v : W4} (perm : ws.Perm (u :: v :: r))
          (hset : ws.toFinset = insert u (insert v needed)) (hop : z ∈ basicOps4 u v) :
          disp4 extra (opt4 k) u.toNat v.toNat (r.map BitVec.toNat) = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept4 perm hn hset
        have hzu : z ≠ u := fun he => hout (hset ▸ he ▸ Finset.mem_insert_self _ _)
        have hzv : z ≠ v := fun he => hout (hset ▸ he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have hzr : z ∉ r := fun hr => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
        have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps4 g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply disp4_complete (k := k) (extra := extra) (opt4 k) hop hzu hzv hzr hk (by omega) (by omega) (cuts4_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [opt4, Bool.or_eq_true]
      right
      rcases hpick with h1 | h2
      · exact h1 (go hp hs hz)
      · exact h2 (go (hp.trans (List.Perm.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops4_swap a b ▸ hz))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4_exact : opt4 6 3 [0x2add5bab756ead800000003ff800, 0x336e6dcdb9b736800001ffc00000, 0x3c778ef1de3bc7000ffe00000000, 0x3f87f0fe1fc3f87ff00000000000] = false := by decide +kernel

lemma k4_nd : k4inputs.Nodup := by decide +kernel

lemma k4_sep_only : ∀ i : Fin 4, ∃ p : Fin 55,
    differs4 p (k4inputs.getD i.val 0) ∧
    ∀ j : Fin 4, j ≠ i → ¬ differs4 p (k4inputs.getD j.val 0) := by
  unfold differs4; decide +kernel

lemma k4_all_mem {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) {k : ℕ} {s : Finset W4}
    (hsub : s ⊆ k4inputs.toFinset) (hl : live basicOps4 g k s) : s = k4inputs.toFinset := by
  apply Finset.Subset.antisymm hsub
  intro w hw
  have hw' : w ∈ k4inputs := List.mem_toFinset.mp hw
  have hidx : ∃ i : Fin 4, k4inputs.getD i.val 0 = w := by
    simp only [k4inputs, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨i, rfl⟩ := hidx
  obtain ⟨p, hpi, hpj⟩ := k4_sep_only i
  have hdg : ∀ q : Fin 55, differs4 q g := by rcases hg with rfl | rfl <;> unfold differs4 <;> decide +kernel
  obtain ⟨u, hu, hdu⟩ := live_separates (differs4 p) (hdg p) (ops4_differs p) hl
  have hu' : u ∈ k4inputs := List.mem_toFinset.mp (hsub hu)
  have hju : ∃ j : Fin 4, k4inputs.getD j.val 0 = u := by
    simp only [k4inputs, List.mem_cons, List.not_mem_nil, or_false] at hu'
    rcases hu' with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨j, rfl⟩ := hju
  by_cases hij : j = i
  · subst hij; exact hu
  · exact False.elim (hpj j hij hdu)

theorem k4_no_build6 {g : W4} (hg : g = goal4 ∨ g = ~~~goal4)
    (hb : build basicOps4 g 6 k4inputs.toFinset) : False := by
  obtain ⟨s, hsub, hl⟩ := compress hb
  have heq := k4_all_mem hg hsub hl
  rw [heq] at hl
  have hit := opt4_complete hg 6 k4inputs 3 k4_nd (by decide) hl
  have hmap : k4inputs.map BitVec.toNat = [0x2add5bab756ead800000003ff800, 0x336e6dcdb9b736800001ffc00000, 0x3c778ef1de3bc7000ffe00000000, 0x3f87f0fe1fc3f87ff00000000000] := by decide
  rw [hmap] at hit
  exact Bool.noConfusion (k4_exact.symm.trans hit)

def holds4 (av : Finset W4) (z : W4) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds4_mono {av av' : Finset W4} (sub : av ⊆ av') {x : W4} (h : holds4 av x) :
    holds4 av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

theorem holds4_not {av : Finset W4} {z : W4} (h : holds4 av z) : holds4 av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable4 (av : Finset W4) (z : W4) : Prop :=
  holds4 av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps4 a b, holds4 (insert w av) z

theorem reachable4_not {av : Finset W4} {z : W4} (h : reachable4 av z) : reachable4 av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds4_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds4_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach4 {av : Finset W4} {x y : W4} (hx : holds4 av x) (hy : holds4 av y) :
    reachable4 av (x &&& y) := by
  have const : holds4 av (0 : W4) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W4) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable4 av (BitVec.allOnes 110 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W4) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable4 av (x &&& BitVec.allOnes 110)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W4) (hw : w ∈ basicOps4 a b) (z : W4) (hz : z = w ∨ z = ~~~w) :
      reachable4 av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps4, ops4] : a &&& b ∈ basicOps4 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps4, ops4] : a &&& ~~~b ∈ basicOps4 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps4, ops4] : b &&& ~~~a ∈ basicOps4 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps4, ops4] : a ||| b ∈ basicOps4 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach4 {av : Finset W4} {x y : W4} (hx : holds4 av x) (hy : holds4 av y) :
    reachable4 av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable4_not (and_reach4 (holds4_not hx) (holds4_not hy))

theorem mem_ops_reach4 {av : Finset W4} {x y z : W4} (hx : holds4 av x) (hy : holds4 av y)
    (hz : z ∈ basicOps4 x y) : reachable4 av z := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach4 hx hy
  · exact or_reach4 hx hy
  · exact and_reach4 hx (holds4_not hy)
  · exact and_reach4 hy (holds4_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_const4 {av : Finset W4} {x y z : W4} (hx : holds4 av x) (hy : holds4 av y)
    (hc : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0)) (hz : z ∈ basicOps4 x y) : holds4 av z := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds4 av (0 : W4) := .inl rfl
  have h1 : holds4 av (~~~(0 : W4)) := .inr (.inl rfl)
  have h0and (v : W4) : (0 : W4) &&& v = 0 := BitVec.zero_and
  have hand0 (v : W4) : v &&& (0 : W4) = 0 := BitVec.and_zero
  have h0or (v : W4) : (0 : W4) ||| v = v := BitVec.zero_or
  have hor0 (v : W4) : v ||| (0 : W4) = v := BitVec.or_zero
  have hand1 (v : W4) : v &&& (~~~(0 : W4)) = v :=
    (congrArg (fun u : W4 => v &&& u) (BitVec.not_zero (n := 110))).trans BitVec.and_allOnes
  have h1and (v : W4) : (~~~(0 : W4)) &&& v = v :=
    (congrArg (fun u : W4 => u &&& v) (BitVec.not_zero (n := 110))).trans BitVec.allOnes_and
  have hor1 (v : W4) : v ||| (~~~(0 : W4)) = ~~~(0 : W4) :=
    (congrArg (fun u : W4 => v ||| u) (BitVec.not_zero (n := 110))).trans (BitVec.or_allOnes.trans (BitVec.not_zero (n := 110)).symm)
  have h1or (v : W4) : (~~~(0 : W4)) ||| v = ~~~(0 : W4) :=
    (congrArg (fun u : W4 => u ||| v) (BitVec.not_zero (n := 110))).trans (BitVec.allOnes_or.trans (BitVec.not_zero (n := 110)).symm)
  rcases hc with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [h0and, hand0, h0or, hor0, BitVec.not_not,
      hand1, h1and, hor1, h1or] <;>
    first | exact h0 | exact h1 | exact hx | exact hy | exact holds4_not hx | exact holds4_not hy

lemma ops4_const_both {x y z : W4} (hx : x = 0 ∨ x = ~~~0) (hy : y = 0 ∨ y = ~~~0)
    (hz : z ∈ basicOps4 x y) : z = 0 ∨ z = ~~~0 := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;> decide

def SignedBuild4 (k : ℕ) (av : Finset W4) (z : W4) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps4 z k av ∨ build basicOps4 (~~~z) k av

theorem sb4_not {av : Finset W4} {z : W4} {k : ℕ} (h : SignedBuild4 k av (~~~z)) :
    SignedBuild4 k av z := by
  rcases h with h | h | h | h
  · exact .inr (.inl (by rw [← BitVec.not_not (b := z), h]))
  · exact .inl (by rw [← BitVec.not_not (b := z), h, BitVec.not_not])
  · exact .inr (.inr (.inr h))
  · exact .inr (.inr (.inl (by simpa only [BitVec.not_not] using h)))

theorem sb4_zero {av : Finset W4} {z : W4} (h : holds4 av z) : SignedBuild4 0 av z := by
  rcases h with h | h | ⟨a, ha, rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb4_wait {av : Finset W4} {z : W4} {k : ℕ} (h : SignedBuild4 k av z) :
    SignedBuild4 (k + 1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb4_le {av : Finset W4} {z : W4} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild4 k av z) :
    SignedBuild4 l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb4_wait ih

theorem sb4_step {av : Finset W4} {t a b z : W4} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps4 a b) (h : SignedBuild4 k (insert z av) t) :
    SignedBuild4 (k + 1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩) (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩)))

theorem sb4_advance {av : Finset W4} {z t : W4} {k : ℕ} (hz : reachable4 av z)
    (next : ∀ av' : Finset W4, av ⊆ av' → holds4 av' z → SignedBuild4 k av' t) :
    SignedBuild4 (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb4_wait (next av (fun _ h => h) h)
  · exact sb4_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem k4_no_signed6 : ¬ SignedBuild4 6 k4inputs.toFinset goal4 := by
  intro h
  rcases h with c | c | run | run
  · exact (by decide : goal4 ≠ 0) c
  · exact (by decide : goal4 ≠ ~~~0) c
  · exact k4_no_build6 (.inl rfl) run
  · exact k4_no_build6 (.inr rfl) run

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

def opsN {M : ℕ} (x y : BitVec M) : List (BitVec M) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

def basicOpsN {M : ℕ} (x y : BitVec M) : Finset (BitVec M) :=
  (opsN x y).toFinset

lemma opsN_swap {M : ℕ} (a b : BitVec M) : basicOpsN a b = basicOpsN b a := by
  ext w
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm, BitVec.or_comm]
  tauto

lemma index_of_opN {M : ℕ} (a b z : BitVec M) (hz : z ∈ basicOpsN a b) :
    ∃ o : Fin 4, (opsN a b).getD o.val 0 = z := by
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

def holdsN {M : ℕ} (av : Finset (BitVec M)) (z : BitVec M) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

lemma holdsN_mono {M : ℕ} {av av' : Finset (BitVec M)} (sub : av ⊆ av') {x : BitVec M}
    (h : holdsN av x) : holdsN av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

lemma holdsN_not {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} (h : holdsN av z) :
    holdsN av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachableN {M : ℕ} (av : Finset (BitVec M)) (z : BitVec M) : Prop :=
  holdsN av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOpsN a b, holdsN (insert w av) z

lemma reachableN_not {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} (h : reachableN av z) :
    reachableN av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holdsN_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holdsN_not hw⟩

lemma bv_zero_and {M : ℕ} (x : BitVec M) : (0 : BitVec M) &&& x = 0 := by simp
lemma bv_and_zero {M : ℕ} (x : BitVec M) : x &&& (0 : BitVec M) = 0 := by simp
lemma bv_zero_or {M : ℕ} (x : BitVec M) : (0 : BitVec M) ||| x = x := by simp
lemma bv_or_zero {M : ℕ} (x : BitVec M) : x ||| (0 : BitVec M) = x := by simp
lemma bv_allOnes_and {M : ℕ} (x : BitVec M) : (~~~(0 : BitVec M)) &&& x = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
lemma bv_and_allOnes {M : ℕ} (x : BitVec M) : x &&& (~~~(0 : BitVec M)) = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
lemma bv_allOnes_or {M : ℕ} (x : BitVec M) : (~~~(0 : BitVec M)) ||| x = ~~~(0 : BitVec M) := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
lemma bv_or_allOnes {M : ℕ} (x : BitVec M) : x ||| (~~~(0 : BitVec M)) = ~~~(0 : BitVec M) := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
lemma bv_getLsbD_zero {M : ℕ} (i : ℕ) : (0 : BitVec M).getLsbD i = false := by simp

lemma and_reachN {M : ℕ} {av : Finset (BitVec M)} {x y : BitVec M}
    (hx : holdsN av x) (hy : holdsN av y) : reachableN av (x &&& y) := by
  have base (a b : BitVec M) (ha : a ∈ av) (hb : b ∈ av) (op : BitVec M)
      (hop : op ∈ basicOpsN a b) (same : a = b → holdsN av op) : reachableN av op := by
    by_cases h : a = b
    · exact .inl (same h)
    · exact .inr ⟨a, ha, b, hb, h, op, hop, .inr (.inr ⟨op, Finset.mem_insert_self _ _, .inl rfl⟩)⟩
  rcases hx with rfl | rfl | ⟨a, ha, hxa⟩
  · exact .inl (.inl (bv_zero_and y))
  · simpa only [bv_allOnes_and] using .inl hy
  · rcases hxa with hxa | hxa
    · rw [hxa]
      rcases hy with rfl | rfl | ⟨b, hb, hyb⟩
      · exact .inl (.inl (bv_and_zero a))
      · exact .inl (.inr (.inr ⟨a, ha, .inl (bv_and_allOnes a)⟩))
      · rcases hyb with hyb | hyb
        · rw [hyb]
          exact base a b ha hb (a &&& b) (by simp [basicOpsN, opsN]) fun h => by
            subst h; exact .inr (.inr ⟨a, ha, .inl BitVec.and_self⟩)
        · rw [hyb]
          exact base a b ha hb (a &&& ~~~b) (by simp [basicOpsN, opsN]) fun h => by
            subst h; exact .inl (BitVec.and_not_self a)
    · rw [hxa]
      rcases hy with rfl | rfl | ⟨b, hb, hyb⟩
      · exact .inl (.inl (bv_and_zero (~~~a)))
      · exact .inl (.inr (.inr ⟨a, ha, .inr (bv_and_allOnes (~~~a))⟩))
      · rcases hyb with hyb | hyb
        · rw [hyb]
          exact base a b ha hb (b &&& ~~~a) (by simp [basicOpsN, opsN]) (fun h => by
            subst h; exact .inl (BitVec.and_not_self a)) |> fun r => by simpa only [BitVec.and_comm] using r
        · rw [hyb]
          have h := base a b ha hb (a ||| b) (by simp [basicOpsN, opsN]) fun h => by
            subst h; exact .inr (.inr ⟨a, ha, .inl BitVec.or_self⟩)
          simpa only [BitVec.not_or] using reachableN_not h

lemma or_reachN {M : ℕ} {av : Finset (BitVec M)} {x y : BitVec M}
    (hx : holdsN av x) (hy : holdsN av y) : reachableN av (x ||| y) := by
  have h := and_reachN (holdsN_not hx) (holdsN_not hy)
  simpa only [BitVec.not_and, BitVec.not_not] using reachableN_not h

lemma mem_ops_reachN {M : ℕ} {av : Finset (BitVec M)} {x y z : BitVec M}
    (hx : holdsN av x) (hy : holdsN av y) (hz : z ∈ basicOpsN x y) : reachableN av z := by
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reachN hx hy
  · exact or_reachN hx hy
  · exact and_reachN hx (holdsN_not hy)
  · exact and_reachN hy (holdsN_not hx)

lemma mem_ops_constN {M : ℕ} {av : Finset (BitVec M)} {x y z : BitVec M}
    (hx : holdsN av x) (hy : holdsN av y)
    (hc : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0)) (hz : z ∈ basicOpsN x y) : holdsN av z := by
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hc with (rfl | rfl) | (rfl | rfl)
  · rcases hz with rfl | rfl | rfl | rfl
    · exact .inl (bv_zero_and y)
    · simpa only [bv_zero_or] using hy
    · exact .inl (bv_zero_and (~~~y))
    · simpa only [bv_and_allOnes] using hy
  · rcases hz with rfl | rfl | rfl | rfl
    · simpa only [bv_allOnes_and] using hy
    · exact .inr (.inl (bv_allOnes_or y))
    · simpa only [bv_allOnes_and] using holdsN_not hy
    · exact .inl (by rw [BitVec.not_not, bv_and_zero])
  · rcases hz with rfl | rfl | rfl | rfl
    · exact .inl (bv_and_zero x)
    · simpa only [bv_or_zero] using hx
    · simpa only [bv_and_allOnes] using hx
    · exact .inl (bv_zero_and (~~~x))
  · rcases hz with rfl | rfl | rfl | rfl
    · simpa only [bv_and_allOnes] using hx
    · exact .inr (.inl (bv_or_allOnes x))
    · exact .inl (by rw [BitVec.not_not, bv_and_zero])
    · simpa only [bv_allOnes_and] using holdsN_not hx

lemma opsN_const_both {M : ℕ} {x y z : BitVec M} (hx : x = 0 ∨ x = ~~~0) (hy : y = 0 ∨ y = ~~~0)
    (hz : z ∈ basicOpsN x y) : z = 0 ∨ z = ~~~0 := by
  have h := mem_ops_constN (av := ∅) (hx.imp_right Or.inl) (hy.imp_right Or.inl) (.inl hx) hz
  rcases h with h | h | ⟨a, ha, _⟩
  · exact .inl h
  · exact .inr h
  · exact False.elim (Finset.notMem_empty a ha)

def SignedBuildN {M : ℕ} (k : ℕ) (av : Finset (BitVec M)) (z : BitVec M) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOpsN z k av ∨ build basicOpsN (~~~z) k av

lemma sbN_not {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} {k : ℕ}
    (h : SignedBuildN k av (~~~z)) : SignedBuildN k av z := by
  rcases h with h | h | h | h
  · exact .inr (.inl (by rw [← BitVec.not_not (b := z), h]))
  · exact .inl (by rw [← BitVec.not_not (b := z), h, BitVec.not_not])
  · exact .inr (.inr (.inr h))
  · exact .inr (.inr (.inl (by simpa only [BitVec.not_not] using h)))

lemma sbN_zero {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} (h : holdsN av z) :
    SignedBuildN 0 av z := by
  rcases h with h | h | ⟨a, ha, rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not, build] using ha)))

lemma sbN_wait {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} {k : ℕ}
    (h : SignedBuildN k av z) : SignedBuildN (k + 1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

lemma sbN_le {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} {k l : ℕ} (hkl : k ≤ l)
    (h : SignedBuildN k av z) : SignedBuildN l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sbN_wait ih

lemma sbN_step {M : ℕ} {av : Finset (BitVec M)} {t a b z : BitVec M} {k : ℕ}
    (ha : a ∈ av) (hb : b ∈ av) (hne : a ≠ b) (hz : z ∈ basicOpsN a b)
    (h : SignedBuildN k (insert z av) t) : SignedBuildN (k + 1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩) (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩)))

def proj {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) : BitVec M :=
  (BitVec.ofBoolListLE (List.ofFn fun r : Fin M => w.getLsbD (src r).val)).cast List.length_ofFn

lemma proj_getLsbD {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) (j : ℕ) (hj : j < M) :
    (proj src w).getLsbD j = w.getLsbD (src ⟨j, hj⟩).val := by
  simp only [proj, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

lemma proj_eq_iff {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) (v : BitVec M) :
    proj src w = v ↔ ∀ r : Fin M, w.getLsbD (src r).val = v.getLsbD r.val := by
  constructor
  · intro h r; rw [← h, proj_getLsbD src w r.val r.isLt]
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro j hj
    rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj, proj_getLsbD src w j hj]
    exact h ⟨j, hj⟩

lemma proj_and {N M : ℕ} (src : Fin M → Fin N) (a b : BitVec N) :
    proj src (a &&& b) = proj src a &&& proj src b := by
  rw [proj_eq_iff]
  intro r
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and, proj_getLsbD src a r.val r.isLt, proj_getLsbD src b r.val r.isLt]

lemma proj_or {N M : ℕ} (src : Fin M → Fin N) (a b : BitVec N) :
    proj src (a ||| b) = proj src a ||| proj src b := by
  rw [proj_eq_iff]
  intro r
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, proj_getLsbD src a r.val r.isLt, proj_getLsbD src b r.val r.isLt]

lemma proj_not {N M : ℕ} (src : Fin M → Fin N) (a : BitVec N) :
    proj src (~~~a) = ~~~(proj src a) := by
  rw [proj_eq_iff]
  intro r
  rw [BitVec.getLsbD_not, BitVec.getLsbD_not, proj_getLsbD src a r.val r.isLt]
  simp only [r.isLt, (src r).isLt, decide_true, Bool.true_and]

lemma proj_ops {N M : ℕ} (src : Fin M → Fin N) (a b z : BitVec N) (hz : z ∈ basicOpsN a b) :
    proj src z ∈ basicOpsN (proj src a) (proj src b) := by
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · exact .inl (proj_and src a b)
  · exact .inr (.inl (proj_or src a b))
  · exact .inr (.inr (.inl (by rw [proj_and, proj_not])))
  · exact .inr (.inr (.inr (by rw [proj_and, proj_not])))

def isConstB {M : ℕ} (u : BitVec M) : Bool := (u == 0) || (u == ~~~0)

lemma isConstB_iff {M : ℕ} (u : BitVec M) : isConstB u = true ↔ u = 0 ∨ u = ~~~0 := by
  simp [isConstB]

def constCount {N M : ℕ} (src : Fin M → Fin N) (s : Finset (BitVec N)) : ℕ :=
  (s.filter fun w => isConstB (proj src w) = true).card

lemma live_transport_const_save {N M : ℕ} (src : Fin M → Fin N)
    {k : ℕ} {t : BitVec N} {s : Finset (BitVec N)} {av : Finset (BitVec M)}
    (hnc : isConstB (proj src t) = false)
    (hl : live basicOpsN t k s)
    (hcov : ∀ w ∈ s, holdsN av (proj src w)) :
    ∃ k', k' + constCount src s ≤ k ∧ SignedBuildN k' av (proj src t) := by
  induction k generalizing s av with
  | zero =>
    change s = {t} at hl
    subst hl
    have hcnt : constCount src {t} = 0 := by
      simp [constCount, hnc]
    exact ⟨0, by omega, sbN_zero (hcov t (Finset.mem_singleton_self t))⟩
  | succ k ih =>
    rcases hl with skip | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, heq, tail⟩
    · obtain ⟨k', hle, hsb⟩ := ih skip hcov
      exact ⟨k', by omega, hsb⟩
    · have hpa : holdsN av (proj src a) := hcov a ha
      have hpb : holdsN av (proj src b) := hcov b hb
      have hpz : proj src z ∈ basicOpsN (proj src a) (proj src b) := proj_ops src a b z hz
      have hrest_sub : rest ⊆ s := fun u hu => heq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
      have hz_nrest : z ∉ rest := fun hu => hzout (hrest_sub hu)
      by_cases hca : isConstB (proj src a) = true
      · have hconst_z : holdsN av (proj src z) :=
          mem_ops_constN hpa hpb (.inl ((isConstB_iff _).mp hca)) hpz
        have hcov' : ∀ w ∈ insert z rest, holdsN av (proj src w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hr
          · exact hconst_z
          · exact hcov w (hrest_sub hr)
        obtain ⟨k', hle, hsb⟩ := ih tail hcov'
        have hdrop : constCount src s ≤ constCount src (insert z rest) + 1 := by
          by_cases hcb : isConstB (proj src b) = true
          · have hcz : isConstB (proj src z) = true :=
              (isConstB_iff _).mpr (opsN_const_both ((isConstB_iff _).mp hca) ((isConstB_iff _).mp hcb) hpz)
            have h1 : (s.filter fun w => isConstB (proj src w) = true) ⊆
                insert a (insert b (rest.filter fun w => isConstB (proj src w) = true)) := by
              intro w hw
              rcases Finset.mem_filter.mp hw with ⟨hws, hwc⟩
              rw [heq] at hws
              rcases Finset.mem_insert.mp hws with rfl | hws
              · exact Finset.mem_insert_self _ _
              · rcases Finset.mem_insert.mp hws with rfl | hwr
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hwr, hwc⟩))
            have h2 : ((insert z rest).filter fun w => isConstB (proj src w) = true) =
                insert z (rest.filter fun w => isConstB (proj src w) = true) := by
              ext w
              simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨rfl | hwr, hwc⟩
                · exact .inl rfl
                · exact .inr ⟨hwr, hwc⟩
              · rintro (rfl | ⟨hwr, hwc⟩)
                · exact ⟨.inl rfl, hcz⟩
                · exact ⟨.inr hwr, hwc⟩
            have hcard1 := Finset.card_le_card h1
            have hcard_ins1 := Finset.card_insert_le a (insert b (rest.filter fun w => isConstB (proj src w) = true))
            have hcard_ins2 := Finset.card_insert_le b (rest.filter fun w => isConstB (proj src w) = true)
            have hzn : z ∉ rest.filter (fun w => isConstB (proj src w) = true) :=
              fun hu => hz_nrest (Finset.mem_filter.mp hu).1
            have hcard2 : constCount src (insert z rest) =
                (rest.filter fun w => isConstB (proj src w) = true).card + 1 := by
              dsimp only [constCount]
              rw [h2, Finset.card_insert_of_notMem hzn]
            dsimp only [constCount] at hcard1 hcard2 ⊢
            omega
          · have h1 : (s.filter fun w => isConstB (proj src w) = true) ⊆
                insert a ((insert z rest).filter fun w => isConstB (proj src w) = true) := by
              intro w hw
              rcases Finset.mem_filter.mp hw with ⟨hws, hwc⟩
              rw [heq] at hws
              rcases Finset.mem_insert.mp hws with rfl | hws
              · exact Finset.mem_insert_self _ _
              · rcases Finset.mem_insert.mp hws with rfl | hwr
                · exact False.elim (hcb hwc)
                · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hwr, hwc⟩)
            have hcard1 := Finset.card_le_card h1
            have hcard_ins := Finset.card_insert_le a ((insert z rest).filter fun w => isConstB (proj src w) = true)
            dsimp only [constCount] at hcard1 ⊢
            omega
        exact ⟨k', by omega, hsb⟩
      · by_cases hcb : isConstB (proj src b) = true
        · have hconst_z : holdsN av (proj src z) :=
            mem_ops_constN hpa hpb (.inr ((isConstB_iff _).mp hcb)) hpz
          have hcov' : ∀ w ∈ insert z rest, holdsN av (proj src w) := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hr
            · exact hconst_z
            · exact hcov w (hrest_sub hr)
          obtain ⟨k', hle, hsb⟩ := ih tail hcov'
          have h1 : (s.filter fun w => isConstB (proj src w) = true) ⊆
              insert b ((insert z rest).filter fun w => isConstB (proj src w) = true) := by
            intro w hw
            rcases Finset.mem_filter.mp hw with ⟨hws, hwc⟩
            rw [heq] at hws
            rcases Finset.mem_insert.mp hws with rfl | hws
            · exact False.elim (hca hwc)
            · rcases Finset.mem_insert.mp hws with rfl | hwr
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hwr, hwc⟩)
          have hcard1 := Finset.card_le_card h1
          have hcard_ins := Finset.card_insert_le b ((insert z rest).filter fun w => isConstB (proj src w) = true)
          have hdrop : constCount src s ≤ constCount src (insert z rest) + 1 := by
            dsimp only [constCount] at hcard1 ⊢; omega
          exact ⟨k', by omega, hsb⟩
        · have hsub_cnt : (s.filter fun w => isConstB (proj src w) = true) ⊆
              ((insert z rest).filter fun w => isConstB (proj src w) = true) := by
            intro w hw
            rcases Finset.mem_filter.mp hw with ⟨hws, hwc⟩
            rw [heq] at hws
            rcases Finset.mem_insert.mp hws with rfl | hws
            · exact False.elim (hca hwc)
            · rcases Finset.mem_insert.mp hws with rfl | hwr
              · exact False.elim (hcb hwc)
              · exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hwr, hwc⟩
          have hcnt_le : constCount src s ≤ constCount src (insert z rest) := Finset.card_le_card hsub_cnt
          rcases mem_ops_reachN hpa hpb hpz with hhold | ⟨u, hu, v, hv, huv, w, hwu, hzw⟩
          · have hcov' : ∀ x ∈ insert z rest, holdsN av (proj src x) := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hr
              · exact hhold
              · exact hcov x (hrest_sub hr)
            obtain ⟨k', hle, hsb⟩ := ih tail hcov'
            exact ⟨k', by omega, hsb⟩
          · have hcov' : ∀ x ∈ insert z rest, holdsN (insert w av) (proj src x) := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hr
              · exact hzw
              · exact holdsN_mono (Finset.subset_insert _ _) (hcov x (hrest_sub hr))
            obtain ⟨k', hle, hsb⟩ := ih tail hcov'
            exact ⟨k' + 1, by omega, sbN_step hu hv huv hwu hsb⟩

def differsBit {N : ℕ} (r0 r1 : Fin N) (w : BitVec N) : Prop :=
  w.getLsbD r0.val ≠ w.getLsbD r1.val

lemma opsN_differsBit {N : ℕ} (r0 r1 : Fin N) (a b z : BitVec N) (hz : z ∈ basicOpsN a b)
    (hd : differsBit r0 r1 z) : differsBit r0 r1 a ∨ differsBit r0 r1 b := by
  by_contra h
  rw [not_or] at h
  obtain ⟨ha, hb⟩ := h
  simp only [differsBit, not_not] at ha hb
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  apply hd
  rcases hz with rfl | rfl | rfl | rfl
  · simp only [BitVec.getLsbD_and, ha, hb]
  · simp only [BitVec.getLsbD_or, ha, hb]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, r0.isLt, r1.isLt, decide_true, Bool.true_and, ha, hb]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, r0.isLt, r1.isLt, decide_true, Bool.true_and, ha, hb]

def projEqB {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) (v : BitVec M) : Bool :=
  (List.finRange M).all fun r => w.getLsbD (src r).val == v.getLsbD r.val

lemma proj_eq_of_projEqB {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) (v : BitVec M)
    (h : projEqB src w v = true) : proj src w = v := by
  rw [proj_eq_iff]
  intro r
  have h1 := List.all_eq_true.mp h r (List.mem_finRange r)
  exact beq_iff_eq.mp h1

def projConstB {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) : Bool :=
  ((List.finRange M).all fun r => !w.getLsbD (src r).val) ||
  ((List.finRange M).all fun r => w.getLsbD (src r).val)

lemma isConstB_proj_of_projConstB {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N)
    (h : projConstB src w = true) : isConstB (proj src w) = true := by
  rw [isConstB_iff]
  simp only [projConstB, Bool.or_eq_true] at h
  rcases h with h0 | h1
  · left
    rw [proj_eq_iff]
    intro r
    have hr := List.all_eq_true.mp h0 r (List.mem_finRange r)
    simp only [Bool.not_eq_true'] at hr
    rw [hr, bv_getLsbD_zero]
  · right
    rw [proj_eq_iff]
    intro r
    have hr := List.all_eq_true.mp h1 r (List.mem_finRange r)
    rw [hr, BitVec.getLsbD_not, bv_getLsbD_zero]
    simp [r.isLt]

def projHoldsB {N M : ℕ} (src : Fin M → Fin N) (av : List (BitVec M)) (w : BitVec N) : Bool :=
  projConstB src w || av.any fun a => projEqB src w a || projEqB src w (~~~a)

lemma holdsN_proj_of_projHoldsB {N M : ℕ} (src : Fin M → Fin N) (av : List (BitVec M)) (w : BitVec N)
    (h : projHoldsB src av w = true) : holdsN av.toFinset (proj src w) := by
  simp only [projHoldsB, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with hc | ⟨a, ha, heq⟩
  · exact ((isConstB_iff _).mp (isConstB_proj_of_projConstB src w hc)).imp_right Or.inl
  · rcases heq with h1 | h2
    · exact .inr (.inr ⟨a, List.mem_toFinset.mpr ha, .inl (proj_eq_of_projEqB src w a h1)⟩)
    · exact .inr (.inr ⟨a, List.mem_toFinset.mpr ha, .inr (proj_eq_of_projEqB src w (~~~a) h2)⟩)

lemma sbN_k4_false {k : ℕ} (hk : k ≤ 6) {t : W4} (ht : t = goal4 ∨ t = ~~~goal4)
    (hsb : SignedBuildN k k4inputs.toFinset t) : False := by
  have hsb6 : SignedBuild4 6 k4inputs.toFinset t := sbN_le hk hsb
  rcases ht with rfl | rfl
  · exact k4_no_signed6 hsb6
  · exact k4_no_signed6 (sb4_not hsb6)

def row4Tbl : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15]

def insBit4 (d : Fin 5) (val : Bool) (r4 : ℕ) : Fin 32 :=
  let lo := r4 % (2 ^ d.val)
  let hi := r4 / (2 ^ d.val)
  ⟨(lo + (if val then 2 ^ d.val else 0) + hi * (2 ^ (d.val + 1))) % 32, Nat.mod_lt _ (by decide)⟩

def srcK4 (d : Fin 5) (r : Fin 110) : Fin 32 := insBit4 d true (row4Tbl.getD r.val 0)
def srcDK4 (d : Fin 5) (r : Fin 110) : Fin 32 := insBit4 d false (15 - row4Tbl.getD r.val 0)
def srcM5 (d : Fin 5) (val : Bool) : Fin 110 → Fin 32 := if val then srcK4 d else srcDK4 d

def in32 : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def v32 (i : Fin 5) : BitVec 32 := in32.getD i.val 0

lemma in32_index : ∀ w ∈ in32, ∃ i : Fin 5, v32 i = w := by
  intro w hw
  simp only [in32, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

lemma goal_differsBit {N : ℕ} {g t : BitVec N} (ht : t = g ∨ t = ~~~g)
    {r0 r1 : Fin N} (hd : g.getLsbD r0.val ≠ g.getLsbD r1.val) : differsBit r0 r1 t := by
  rcases ht with rfl | rfl
  · exact hd
  · simp only [differsBit, BitVec.getLsbD_not, r0.isLt, r1.isLt, decide_true, Bool.true_and, ne_eq, Bool.not_inj_iff]
    exact hd

lemma constCount_ge_two {N M : ℕ} (src : Fin M → Fin N) {s : Finset (BitVec N)}
    {u v : BitVec N} (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v)
    (hcu : isConstB (proj src u) = true) (hcv : isConstB (proj src v) = true) :
    2 ≤ constCount src s := by
  have hsub : ({u, v} : Finset (BitVec N)) ⊆ s.filter (fun w => isConstB (proj src w) = true) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_filter.mpr ⟨hu, hcu⟩
    · rcases Finset.mem_singleton.mp hw with rfl
      exact Finset.mem_filter.mpr ⟨hv, hcv⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hc
  exact hc

lemma constCount_ge_one {N M : ℕ} (src : Fin M → Fin N) {s : Finset (BitVec N)}
    {u : BitVec N} (hu : u ∈ s) (hcu : isConstB (proj src u) = true) :
    1 ≤ constCount src s := by
  have hmem : u ∈ s.filter (fun w => isConstB (proj src w) = true) := Finset.mem_filter.mpr ⟨hu, hcu⟩
  exact Finset.one_le_card.mpr ⟨u, hmem⟩

lemma goal4_nc : isConstB goal4 = false ∧ isConstB (~~~goal4) = false := by decide +kernel

lemma proj_goal_sign {N M : ℕ} (src : Fin M → Fin N) {g t : BitVec N} {gM : BitVec M}
    (ht : t = g ∨ t = ~~~g)
    (hpg : projEqB src g gM = true ∨ projEqB src g (~~~gM) = true) :
    proj src t = gM ∨ proj src t = ~~~gM := by
  rcases hpg with h | h
  · have h' := proj_eq_of_projEqB src g gM h
    rcases ht with rfl | rfl
    · exact .inl h'
    · exact .inr (by rw [proj_not, h'])
  · have h' := proj_eq_of_projEqB src g (~~~gM) h
    rcases ht with rfl | rfl
    · exact .inr h'
    · exact .inl (by rw [proj_not, h', BitVec.not_not])

lemma live_transport_reach_step {N M : ℕ} (src : Fin M → Fin N)
    {k : ℕ} {t z : BitVec N} {rest : Finset (BitVec N)} {av : Finset (BitVec M)}
    (hnc : isConstB (proj src t) = false)
    (hl : live basicOpsN t k (insert z rest))
    (hrest : ∀ w ∈ rest, holdsN av (proj src w))
    (hz : reachableN av (proj src z)) :
    ∃ k', k' + constCount src (insert z rest) ≤ k + 1 ∧ SignedBuildN k' av (proj src t) := by
  rcases hz with hhold | ⟨u, hu, v, hv, huv, w, hw, hzw⟩
  · have hcov : ∀ x ∈ insert z rest, holdsN av (proj src x) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hr
      · exact hhold
      · exact hrest x hr
    obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc hl hcov
    exact ⟨k', by omega, hsb⟩
  · have hcov : ∀ x ∈ insert z rest, holdsN (insert w av) (proj src x) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hr
      · exact hzw
      · exact holdsN_mono (Finset.subset_insert _ _) (hrest x hr)
    obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc hl hcov
    exact ⟨k' + 1, by omega, sbN_step hu hv huv hw hsb⟩

lemma constCount_ge_flags {N M : ℕ} (src : Fin M → Fin N) {z vd : BitVec N} {rest : Finset (BitVec N)}
    (hne : vd ∈ rest → z ≠ vd)
    (hcd : isConstB (proj src vd) = true)
    {bz bd : Bool}
    (hbz : bz = true → isConstB (proj src z) = true)
    (hbd : bd = true → vd ∈ rest) :
    bz.toNat + bd.toNat ≤ constCount src (insert z rest) := by
  cases bz <;> cases bd
  · simp
  · simpa using constCount_ge_one src (Finset.mem_insert_of_mem (hbd rfl)) hcd
  · simpa using constCount_ge_one src (Finset.mem_insert_self _ _) (hbz rfl)
  · have hmem := hbd rfl
    simpa using constCount_ge_two src (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hmem)
      (hne hmem) (hbz rfl) hcd

def flipBit5 (d : Fin 5) (r : Fin 32) : Fin 32 :=
  ⟨Nat.xor r.val (2 ^ d.val) % 32, Nat.mod_lt _ (by decide)⟩

lemma flipBit5_agree : ∀ (d q : Fin 5) (r : Fin 32), q ≠ d →
    (v32 q).getLsbD r.val = (v32 q).getLsbD (flipBit5 d r).val := by decide +kernel

def hasSep5 (g z : BitVec 32) (d : Fin 5) : Bool :=
  (List.finRange 32).any fun r =>
    let r' := flipBit5 d r
    (g.getLsbD r.val != g.getLsbD r'.val) && (z.getLsbD r.val == z.getLsbD r'.val)

lemma mem_rest5_of_hasSep5 {g t z : BitVec 32} (ht : t = g ∨ t = ~~~g)
    {k : ℕ} {rest : Finset (BitVec 32)} (hsub : rest ⊆ in32.toFinset)
    (hl : live basicOpsN t k (insert z rest)) (d : Fin 5)
    (hsep : hasSep5 g z d = true) : v32 d ∈ rest := by
  simp only [hasSep5, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hsep
  obtain ⟨r, _, hdg, hdz⟩ := hsep
  obtain ⟨w, hw, hdw⟩ := live_separates (differsBit r (flipBit5 d r))
    (goal_differsBit ht hdg) (opsN_differsBit r (flipBit5 d r)) hl
  rcases Finset.mem_insert.mp hw with rfl | hwr
  · exact False.elim (hdw hdz)
  · obtain ⟨q, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hsub hwr))
    by_cases hqd : q = d
    · subst hqd; exact hwr
    · exact False.elim (hdw (flipBit5_agree d q r hqd))

def srcK4NPN (d : Fin 5) (val : Bool) (negMask : ℕ) (r : Fin 110) : Fin 32 :=
  insBit4 d val (Nat.xor (row4Tbl.getD r.val 0) negMask)

lemma kill5_from_k4 {g t z : BitVec 32} (ht : t = g ∨ t = ~~~g)
    {k : ℕ} {i j : Fin 5} {s rest : Finset (BitVec 32)}
    (hz : z ∈ basicOpsN (v32 i) (v32 j))
    (hzout : z ∉ s) (he : s = insert (v32 i) (insert (v32 j) rest))
    (hrest : rest ⊆ in32.toFinset)
    (tail : live basicOpsN t k (insert z rest))
    (d : Fin 5) (val : Bool) (negMask : ℕ)
    (hpg : projEqB (srcK4NPN d val negMask) g goal4 = true ∨ projEqB (srcK4NPN d val negMask) g (~~~goal4) = true)
    (hin : ∀ q : Fin 5, projHoldsB (srcK4NPN d val negMask) k4inputs (v32 q) = true)
    (hcdB : projConstB (srcK4NPN d val negMask) (v32 d) = true)
    (hbound : k + (if ((d == i) || (d == j)) then 0 else 1) ≤
      6 + (projConstB (srcK4NPN d val negMask) z).toNat + (hasSep5 g z d).toNat) : False := by
  let src := srcK4NPN d val negMask
  change k + (if ((d == i) || (d == j)) then 0 else 1) ≤
    6 + (projConstB src z).toNat + (hasSep5 g z d).toNat at hbound
  have hpg' : proj src t = goal4 ∨ proj src t = ~~~goal4 := proj_goal_sign src ht hpg
  have hnc : isConstB (proj src t) = false := by
    rcases hpg' with h | h <;> rw [h]
    · exact goal4_nc.1
    · exact goal4_nc.2
  have hcd : isConstB (proj src (v32 d)) = true := isConstB_proj_of_projConstB src (v32 d) hcdB
  have hne : v32 d ∈ rest → z ≠ v32 d := fun hm eq =>
    hzout (eq ▸ (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)))
  have hcnt : (projConstB src z).toNat + (hasSep5 g z d).toNat ≤ constCount src (insert z rest) :=
    constCount_ge_flags src hne hcd
      (fun h => isConstB_proj_of_projConstB src z h)
      (fun h => mem_rest5_of_hasSep5 ht hrest tail d h)
  have hrest_cov : ∀ w ∈ rest, holdsN k4inputs.toFinset (proj src w) := by
    intro w hw
    obtain ⟨q, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hrest hw))
    exact holdsN_proj_of_projHoldsB src k4inputs (v32 q) (hin q)
  by_cases htouch : ((d == i) || (d == j)) = true
  · simp only [htouch, ite_true] at hbound
    have hci : (proj src (v32 i) = 0 ∨ proj src (v32 i) = ~~~0) ∨ (proj src (v32 j) = 0 ∨ proj src (v32 j) = ~~~0) := by
      simp only [Bool.or_eq_true, beq_iff_eq] at htouch
      rcases htouch with rfl | rfl
      · exact .inl ((isConstB_iff _).mp hcd)
      · exact .inr ((isConstB_iff _).mp hcd)
    have hcov : ∀ w ∈ insert z rest, holdsN k4inputs.toFinset (proj src w) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwr
      · exact mem_ops_constN
          (holdsN_proj_of_projHoldsB src k4inputs (v32 i) (hin i))
          (holdsN_proj_of_projHoldsB src k4inputs (v32 j) (hin j))
          hci (proj_ops src _ _ _ hz)
      · exact hrest_cov w hwr
    obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail hcov
    exact sbN_k4_false (by omega) hpg' hsb
  · simp only [Bool.not_eq_true] at htouch
    simp only [htouch, Bool.false_eq_true, ite_false] at hbound
    have hzr : reachableN k4inputs.toFinset (proj src z) :=
      mem_ops_reachN
        (holdsN_proj_of_projHoldsB src k4inputs (v32 i) (hin i))
        (holdsN_proj_of_projHoldsB src k4inputs (v32 j) (hin j))
        (proj_ops src _ _ _ hz)
    obtain ⟨k', hle, hsb⟩ := live_transport_reach_step src hnc tail hrest_cov hzr
    exact sbN_k4_false (by omega) hpg' hsb

def goal5_0 : BitVec 32 := BitVec.ofNat 32 0xfeeee888
lemma goal5_0_nc : isConstB goal5_0 = false ∧ isConstB (~~~goal5_0) = false := by decide +kernel
lemma f5_0_in_not_goal : ∀ i : Fin 5, v32 i ≠ goal5_0 ∧ v32 i ≠ ~~~goal5_0 := by decide +kernel
def tag5_0 (i j : Fin 5) (o : Fin 4) : ℕ :=
  match i.val, j.val, o.val with
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 0
  | 0, 2, 2 => 0
  | 0, 2, 3 => 0
  | 0, 3, 0 => 0
  | 0, 3, 1 => 0
  | 0, 3, 2 => 0
  | 0, 3, 3 => 0
  | 0, 4, 0 => 0
  | 0, 4, 1 => 0
  | 0, 4, 2 => 0
  | 0, 4, 3 => 0
  | 1, 2, 0 => 0
  | 1, 2, 1 => 0
  | 1, 2, 2 => 0
  | 1, 2, 3 => 0
  | 1, 3, 0 => 0
  | 1, 3, 1 => 0
  | 1, 3, 2 => 0
  | 1, 3, 3 => 0
  | 1, 4, 0 => 0
  | 1, 4, 1 => 0
  | 1, 4, 2 => 0
  | 1, 4, 3 => 0
  | 2, 3, 0 => 0
  | 2, 3, 1 => 0
  | 2, 3, 2 => 0
  | 2, 3, 3 => 0
  | 2, 4, 0 => 0
  | 2, 4, 1 => 0
  | 2, 4, 2 => 0
  | 2, 4, 3 => 0
  | 3, 4, 0 => 0
  | 3, 4, 1 => 0
  | 3, 4, 2 => 0
  | 3, 4, 3 => 0
  | _, _, _ => 0
lemma tag5_0_lt : ∀ (i j : Fin 5), i.val < j.val → ∀ o : Fin 4, tag5_0 i j o < 1 := by decide +kernel
lemma f5_0_r0_goal : projEqB (srcK4NPN 2 true 0) goal5_0 goal4 = true ∨ projEqB (srcK4NPN 2 true 0) goal5_0 (~~~goal4) = true := by decide +kernel
lemma f5_0_r0_in : ∀ q : Fin 5, projHoldsB (srcK4NPN 2 true 0) k4inputs (v32 q) = true := by decide +kernel
lemma f5_0_r0_const : projConstB (srcK4NPN 2 true 0) (v32 2) = true := by decide +kernel
lemma f5_0_r0_chk : ∀ (i j : Fin 5), i.val < j.val → ∀ o : Fin 4, tag5_0 i j o = 0 → 6 + (if ((2 == i) || (2 == j)) then 0 else 1) ≤ 6 + (projConstB (srcK4NPN 2 true 0) ((opsN (v32 i) (v32 j)).getD o.val 0)).toNat + (hasSep5 goal5_0 ((opsN (v32 i) (v32 j)).getD o.val 0) 2).toNat := by decide +kernel
lemma no5_0_ord {t z : BitVec 32} (ht : t = goal5_0 ∨ t = ~~~goal5_0)
    (i j : Fin 5) (hlt : i.val < j.val) {s rest : Finset (BitVec 32)}
    (hz : z ∈ basicOpsN (v32 i) (v32 j)) (hzout : z ∉ s)
    (he : s = insert (v32 i) (insert (v32 j) rest)) (hrest : rest ⊆ in32.toFinset)
    (tail : live basicOpsN t 6 (insert z rest)) : False := by
  obtain ⟨o, ho⟩ := index_of_opN _ _ _ hz
  have hlt_tag : tag5_0 i j o < 1 := tag5_0_lt i j hlt o
  interval_cases htag : tag5_0 i j o
  · exact kill5_from_k4 ht hz hzout he hrest tail 2 true 0 f5_0_r0_goal f5_0_r0_in f5_0_r0_const (ho ▸ f5_0_r0_chk i j hlt o htag)

theorem no5_0 {t : BitVec 32} (ht : t = goal5_0 ∨ t = ~~~goal5_0)
    (run : build basicOpsN t 7 in32.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 6) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, he, tail⟩
  · have htin : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := in32_index _ (List.mem_toFinset.mp (hs htin))
    rcases ht with rfl | rfl
    · exact (f5_0_in_not_goal i).1 hi
    · exact (f5_0_in_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg v32 eq)
    have hrest : rest ⊆ in32.toFinset :=
      fun w hw => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    rcases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hlt | hgt
    · exact no5_0_ord ht i j hlt hz hzout he hrest tail
    · rw [opsN_swap] at hz
      have he' : s = insert (v32 j) (insert (v32 i) rest) := by
        rw [he, Finset.insert_comm]
      exact no5_0_ord ht j i hgt hz hzout he' hrest tail

lemma sbN_f5_0_false {k : ℕ} (hk : k ≤ 7) {t : BitVec 32} (ht : t = goal5_0 ∨ t = ~~~goal5_0)
    (hsb : SignedBuildN k in32.toFinset t) : False := by
  have hsbK := sbN_le hk hsb
  have hne0 : goal5_0 ≠ 0 := by decide
  have hne1 : goal5_0 ≠ ~~~0 := by decide
  rcases hsbK with h0 | h1 | run | run
  · rcases ht with rfl | rfl
    · exact hne0 h0
    · exact hne1 (by rw [← BitVec.not_not (b := goal5_0), h0])
  · rcases ht with rfl | rfl
    · exact hne1 h1
    · exact hne0 (by rw [← BitVec.not_not (b := goal5_0), h1, BitVec.not_not])
  · exact no5_0 ht run
  · refine no5_0 ?_ run
    rcases ht with rfl | rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not

def goal6 : BitVec 64 := BitVec.ofNat 64 (4276676840 * 2 ^ 32 + 4001925256)

def in6 : List (BitVec 64) :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def v6 (i : Fin 6) : BitVec 64 := in6.getD i.val 0

lemma in6_index : ∀ w ∈ in6, ∃ i : Fin 6, v6 i = w := by
  intro w hw
  simp only [in6, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

def insBit5 (d : Fin 6) (val : Bool) (r5 : ℕ) : Fin 64 :=
  let lo := r5 % (2 ^ d.val)
  let hi := r5 / (2 ^ d.val)
  ⟨(lo + (if val then 2 ^ d.val else 0) + hi * (2 ^ (d.val + 1))) % 64, Nat.mod_lt _ (by decide)⟩

def flipBit6 (d : Fin 6) (r : Fin 64) : Fin 64 :=
  ⟨Nat.xor r.val (2 ^ d.val) % 64, Nat.mod_lt _ (by decide)⟩

lemma flipBit6_agree : ∀ (d q : Fin 6) (r : Fin 64), q ≠ d →
    (v6 q).getLsbD r.val = (v6 q).getLsbD (flipBit6 d r).val := by decide +kernel

def hasSep6_1 (g z : BitVec 64) (d : Fin 6) : Bool :=
  (List.finRange 64).any fun r =>
    let r' := flipBit6 d r
    (g.getLsbD r.val != g.getLsbD r'.val) && (z.getLsbD r.val == z.getLsbD r'.val)

lemma mem_rest6_of_hasSep6_1 {g t z : BitVec 64} (ht : t = g ∨ t = ~~~g)
    {k : ℕ} {rest : Finset (BitVec 64)} (hsub : rest ⊆ in6.toFinset)
    (hl : live basicOpsN t k (insert z rest)) (d : Fin 6)
    (hsep : hasSep6_1 g z d = true) : v6 d ∈ rest := by
  simp only [hasSep6_1, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hsep
  obtain ⟨r, _, hdg, hdz⟩ := hsep
  obtain ⟨w, hw, hdw⟩ := live_separates (differsBit r (flipBit6 d r))
    (goal_differsBit ht hdg) (opsN_differsBit r (flipBit6 d r)) hl
  rcases Finset.mem_insert.mp hw with rfl | hwr
  · exact False.elim (hdw hdz)
  · obtain ⟨q, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hsub hwr))
    by_cases hqd : q = d
    · subst hqd; exact hwr
    · exact False.elim (hdw (flipBit6_agree d q r hqd))

lemma kill6_step1 {M : ℕ} (src : Fin M → Fin 64) (av : List (BitVec M)) (gM : BitVec M) (lim : ℕ)
    (hno : ∀ {k' : ℕ}, k' ≤ lim → ∀ {u : BitVec M}, (u = gM ∨ u = ~~~gM) → SignedBuildN k' av.toFinset u → False)
    (hpg : projEqB src goal6 gM = true ∨ projEqB src goal6 (~~~gM) = true)
    (hgM_nc : isConstB gM = false ∧ isConstB (~~~gM) = false)
    (hin : ∀ q : Fin 6, projHoldsB src av (v6 q) = true)
    (d : Fin 6) (hcdB : projConstB src (v6 d) = true)
    {t z1 : BitVec 64} (ht : t = goal6 ∨ t = ~~~goal6)
    {k : ℕ} {i j : Fin 6} {s rest1 : Finset (BitVec 64)}
    (hz1 : z1 ∈ basicOpsN (v6 i) (v6 j)) (hz1out : z1 ∉ s)
    (he1 : s = insert (v6 i) (insert (v6 j) rest1))
    (hrest1 : rest1 ⊆ in6.toFinset)
    (tail1 : live basicOpsN t k (insert z1 rest1))
    (hbound : k + (if ((d == i) || (d == j)) then 0 else 1) ≤
      lim + (projConstB src z1).toNat + (hasSep6_1 goal6 z1 d).toNat) : False := by
  have hpg' : proj src t = gM ∨ proj src t = ~~~gM := proj_goal_sign src ht hpg
  have hnc : isConstB (proj src t) = false := by
    rcases hpg' with h | h <;> rw [h]
    · exact hgM_nc.1
    · exact hgM_nc.2
  have hcd : isConstB (proj src (v6 d)) = true := isConstB_proj_of_projConstB src (v6 d) hcdB
  have hne : v6 d ∈ rest1 → z1 ≠ v6 d := fun hm eq =>
    hz1out (eq ▸ (he1 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)))
  have hcnt : (projConstB src z1).toNat + (hasSep6_1 goal6 z1 d).toNat ≤ constCount src (insert z1 rest1) :=
    constCount_ge_flags src hne hcd
      (fun h => isConstB_proj_of_projConstB src z1 h)
      (fun h => mem_rest6_of_hasSep6_1 ht hrest1 tail1 d h)
  have hrest_cov : ∀ w ∈ rest1, holdsN av.toFinset (proj src w) := by
    intro w hw
    obtain ⟨q, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hrest1 hw))
    exact holdsN_proj_of_projHoldsB src av (v6 q) (hin q)
  by_cases htouch : ((d == i) || (d == j)) = true
  · simp only [htouch, ite_true] at hbound
    have hci : (proj src (v6 i) = 0 ∨ proj src (v6 i) = ~~~0) ∨ (proj src (v6 j) = 0 ∨ proj src (v6 j) = ~~~0) := by
      simp only [Bool.or_eq_true, beq_iff_eq] at htouch
      rcases htouch with rfl | rfl
      · exact .inl ((isConstB_iff _).mp hcd)
      · exact .inr ((isConstB_iff _).mp hcd)
    have hcov : ∀ w ∈ insert z1 rest1, holdsN av.toFinset (proj src w) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwr
      · exact mem_ops_constN
          (holdsN_proj_of_projHoldsB src av (v6 i) (hin i))
          (holdsN_proj_of_projHoldsB src av (v6 j) (hin j))
          hci (proj_ops src _ _ _ hz1)
      · exact hrest_cov w hwr
    obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail1 hcov
    exact hno (by omega) hpg' hsb
  · simp only [Bool.not_eq_true] at htouch
    simp only [htouch, Bool.false_eq_true, ite_false] at hbound
    have hzr : reachableN av.toFinset (proj src z1) :=
      mem_ops_reachN
        (holdsN_proj_of_projHoldsB src av (v6 i) (hin i))
        (holdsN_proj_of_projHoldsB src av (v6 j) (hin j))
        (proj_ops src _ _ _ hz1)
    obtain ⟨k', hle, hsb⟩ := live_transport_reach_step src hnc tail1 hrest_cov hzr
    exact hno (by omega) hpg' hsb

lemma f6_in_not_goal : ∀ i : Fin 6, v6 i ≠ goal6 ∧ v6 i ≠ ~~~goal6 := by decide +kernel
def src6_r0 (r : Fin 32) : Fin 64 := insBit5 2 true r.val
lemma f6_r0_goal : projEqB src6_r0 goal6 goal5_0 = true ∨ projEqB src6_r0 goal6 (~~~goal5_0) = true := by decide +kernel
lemma f6_r0_in : ∀ q : Fin 6, projHoldsB src6_r0 in32 (v6 q) = true := by decide +kernel
lemma f6_r0_const : projConstB src6_r0 (v6 2) = true := by decide +kernel

def tag6_s1 (i j : Fin 6) (o : Fin 4) : ℕ :=
  match i.val, j.val, o.val with
  | 0, 1, 0 => 0
  | 0, 1, 1 => 0
  | 0, 1, 2 => 0
  | 0, 1, 3 => 0
  | 0, 2, 0 => 0
  | 0, 2, 1 => 0
  | 0, 2, 2 => 0
  | 0, 2, 3 => 0
  | 0, 3, 0 => 0
  | 0, 3, 1 => 0
  | 0, 3, 2 => 0
  | 0, 3, 3 => 0
  | 0, 4, 0 => 0
  | 0, 4, 1 => 0
  | 0, 4, 2 => 0
  | 0, 4, 3 => 0
  | 0, 5, 0 => 0
  | 0, 5, 1 => 0
  | 0, 5, 2 => 0
  | 0, 5, 3 => 0
  | 1, 2, 0 => 0
  | 1, 2, 1 => 0
  | 1, 2, 2 => 0
  | 1, 2, 3 => 0
  | 1, 3, 0 => 0
  | 1, 3, 1 => 0
  | 1, 3, 2 => 0
  | 1, 3, 3 => 0
  | 1, 4, 0 => 0
  | 1, 4, 1 => 0
  | 1, 4, 2 => 0
  | 1, 4, 3 => 0
  | 1, 5, 0 => 0
  | 1, 5, 1 => 0
  | 1, 5, 2 => 0
  | 1, 5, 3 => 0
  | 2, 3, 0 => 0
  | 2, 3, 1 => 0
  | 2, 3, 2 => 0
  | 2, 3, 3 => 0
  | 2, 4, 0 => 0
  | 2, 4, 1 => 0
  | 2, 4, 2 => 0
  | 2, 4, 3 => 0
  | 2, 5, 0 => 0
  | 2, 5, 1 => 0
  | 2, 5, 2 => 0
  | 2, 5, 3 => 0
  | 3, 4, 0 => 0
  | 3, 4, 1 => 0
  | 3, 4, 2 => 0
  | 3, 4, 3 => 0
  | 3, 5, 0 => 0
  | 3, 5, 1 => 0
  | 3, 5, 2 => 0
  | 3, 5, 3 => 0
  | 4, 5, 0 => 0
  | 4, 5, 1 => 0
  | 4, 5, 2 => 0
  | 4, 5, 3 => 0
  | _, _, _ => 0
lemma tag6_s1_lt : ∀ (i j : Fin 6), i.val < j.val → ∀ o : Fin 4, tag6_s1 i j o < 1 := by decide +kernel
lemma chk6_s1_r0 : ∀ (i j : Fin 6), i.val < j.val → ∀ o : Fin 4, tag6_s1 i j o = 0 → 6 + (if ((2 == i) || (2 == j)) then 0 else 1) ≤ 7 + (projConstB src6_r0 ((opsN (v6 i) (v6 j)).getD o.val 0)).toNat + (hasSep6_1 goal6 ((opsN (v6 i) (v6 j)).getD o.val 0) 2).toNat := by decide +kernel
lemma no_K_f_ord {t z1 : BitVec 64} (ht : t = goal6 ∨ t = ~~~goal6)
    (i j : Fin 6) (hlt : i.val < j.val) {s rest1 : Finset (BitVec 64)}
    (hz1 : z1 ∈ basicOpsN (v6 i) (v6 j)) (hz1out : z1 ∉ s)
    (he1 : s = insert (v6 i) (insert (v6 j) rest1)) (hrest1 : rest1 ⊆ in6.toFinset)
    (tail1 : live basicOpsN t 6 (insert z1 rest1)) : False := by
  obtain ⟨o, ho⟩ := index_of_opN _ _ _ hz1
  have hlt_tag : tag6_s1 i j o < 1 := tag6_s1_lt i j hlt o
  interval_cases htag : tag6_s1 i j o
  · exact kill6_step1 src6_r0 in32 goal5_0 7 sbN_f5_0_false f6_r0_goal goal5_0_nc f6_r0_in 2 f6_r0_const ht hz1 hz1out he1 hrest1 tail1 (ho ▸ chk6_s1_r0 i j hlt o htag)

theorem no_K_f {t : BitVec 64} (ht : t = goal6 ∨ t = ~~~goal6)
    (run : build basicOpsN t 7 in6.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 6) hl with endcase | ⟨a, ha, b, hb, hab, z1, hz1, hz1out, rest1, he1, tail1⟩
  · have htin : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := in6_index _ (List.mem_toFinset.mp (hs htin))
    rcases ht with rfl | rfl
    · exact (f6_in_not_goal i).1 hi
    · exact (f6_in_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg v6 eq)
    have hrest1 : rest1 ⊆ in6.toFinset :=
      fun w hw => hs (he1 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    rcases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hlt | hgt
    · exact no_K_f_ord ht i j hlt hz1 hz1out he1 hrest1 tail1
    · rw [opsN_swap] at hz1
      have he1' : s = insert (v6 j) (insert (v6 i) rest1) := by
        rw [he1, Finset.insert_comm]
      exact no_K_f_ord ht j i hgt hz1 hz1out he1' hrest1 tail1

def step6 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def bit6 (k : Fin 64) (w : BitVec 64) : Bool := w[k.val]

lemma read_bit6 (w : List (BitVec 64)) (i : ℕ) (k : Fin 64) :
    (w.map (bit6 k)).getD i false = bit6 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit6]

def action6 (w : List (BitVec 64)) (g : Gate) : BitVec 64 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
lemma action6_spec (w : List (BitVec 64)) (g : Gate) (hg : legal g) (k : Fin 64) :
    step6 (w.map (bit6 k)) g = (w ++ [action6 w g]).map (bit6 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : BitVec 64)[k.val] = false := by change (BitVec.ofNat 64 0)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step6, List.map_cons, List.map_nil, read_bit6, List.map_append] <;>
    simp only [action6, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit6, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

lemma available_read6 {av : Finset (BitVec 64)} {w : List (BitVec 64)}
    (hw : ∀ u ∈ w, holdsN av u) (i : ℕ) : holdsN av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
lemma gate_reach6 (w : List (BitVec 64)) (av : Finset (BitVec 64)) (hw : ∀ u ∈ w, holdsN av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachableN av (action6 w g) else holdsN av (action6 w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action6, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : BitVec 64, x ||| (0 : BitVec 64) = x from fun x => BitVec.or_zero,
    show ∀ x : BitVec 64, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read6 hw _)
    | exact holdsN_not (available_read6 hw _)
    | exact and_reachN (available_read6 hw _) (available_read6 hw _)
    | exact or_reachN (available_read6 hw _) (available_read6 hw _)

set_option maxRecDepth 4000 in
theorem compile6 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (BitVec 64)) (av : Finset (BitVec 64)) (hw : ∀ u ∈ w, holdsN av u)
    (he : ∀ k, (gs.foldl step6 (w.map (bit6 k))).getD out false = bit6 k goal6) :
    ∃ t, (t = goal6 ∨ t = ~~~goal6) ∧ build basicOpsN t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal6 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit6, bit6] using he ⟨i, hi⟩
    have h := hv ▸ available_read6 hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal6 ≠ 0) zero)
    · exact False.elim ((by decide : goal6 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action6 w g
    have stepOK := action6_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step6 ((w ++ [z]).map (bit6 k))).getD out false = bit6 k goal6 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset (BitVec 64)) (hold : ∀ u ∈ w, holdsN A u) (new : holdsN A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach6 w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holdsN_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def targetF (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676840 * 2 ^ 32 + 4001925256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

lemma spec_f6 : ∀ k : Fin 64, targetF (fun i => bit6 k (v6 i)) = bit6 k goal6 := by decide +kernel

theorem binary_lb (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = targetF x) :
    7 < binaryCost gs := by
  by_contra hlow
  have low : binaryCost gs ≤ 7 := by omega
  have init : ∀ u ∈ in6, holdsN in6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step6 (in6.map (bit6 k))).getD o false = bit6 k goal6 := by
    let x (i : Fin 6) : Bool := bit6 k (v6 i)
    have same : List.ofFn x = in6.map (bit6 k) := by
      apply List.ext_getElem
      · simp [in6]
      · intro i hi hj
        have hlt : i < in6.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, v6, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (in6.map (bit6 k)) = bit6 k goal6
    rw [← same, he]
    exact spec_f6 k
  obtain ⟨t, ht, run⟩ := compile6 gs o hg in6 in6.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOpsN t a in6.toFinset) :
      build basicOpsN t c in6.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_K_f ht (lift low run)

def witGates : List Gate :=
  [ { op := GateOp.and, inputs := [3, 4] }
  , { op := GateOp.or, inputs := [1, 0] }
  , { op := GateOp.and, inputs := [5, 2] }
  , { op := GateOp.or, inputs := [8, 6] }
  , { op := GateOp.and, inputs := [9, 7] }
  , { op := GateOp.and, inputs := [6, 8] }
  , { op := GateOp.or, inputs := [10, 11] }
  , { op := GateOp.and, inputs := [1, 0] }
  , { op := GateOp.or, inputs := [13, 12] } ]

def witCirc : Circuit := ⟨witGates, 14⟩

lemma witCirc_mono : Monotone2 witCirc := by
  intro g hg
  simp only [witCirc, witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

lemma witCirc_eval : ∀ x : Fin 6 → Bool, witCirc.eval (List.ofFn x) = targetF x := by decide +kernel

lemma main_proof (s : ℕ) (h : HasCircuitSize 6 targetF s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetF x := by
  obtain ⟨C, hFan, hSize, hEval⟩ := h
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨gNot, hgNot, hopNot⟩ := hasNot
    have hbc_lt : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨gNot, hgNot, by simp [isBinary, hopNot]⟩
    have hleg : ∀ g ∈ C.gates, legal g := fun g hg => by
      obtain ⟨hop, hlen⟩ := hFan g hg
      exact ⟨by simpa using hop, hlen⟩
    have hlb : 7 < binaryCost C.gates := binary_lb C.gates C.output hleg (fun x => by
      simpa [Circuit.eval] using hEval x)
    have hwit_le : witCirc.size ≤ s := by
      have hcs : C.gates.length ≤ s := hSize
      have hwl : witCirc.size = 9 := rfl
      omega
    exact ⟨witCirc, witCirc_mono, hwit_le, witCirc_eval⟩
  · refine ⟨C, ?_, hSize, hEval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hFan g hg
    refine ⟨?_, hlen⟩
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hop
    rcases hop' with h1 | h2 | h3
    · simp [h1]
    · simp [h2]
    · exact False.elim (hasNot ⟨g, hg, h3⟩)

end PEqualNP.Outside.L_meta_12619

theorem PEqualNP.Outside.L_meta_12619 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4001925256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4001925256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_12619.main_proof
