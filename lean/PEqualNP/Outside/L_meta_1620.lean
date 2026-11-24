import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1620

abbrev F := (Fin 14 → Bool) → Bool
abbrev S := Nat × Nat

def cnt : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n+1, f => cnt n f + (f n).toNat

lemma cnt_congr {f g : Nat → Bool} (n : Nat) (h : ∀ i < n, f i = g i) : cnt n f = cnt n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cnt, ih (fun i hi => h i (by omega)), h n (by omega)]

lemma cnt_add (a b : Nat) (f : Nat → Bool) : cnt (a+b) f = cnt a f + cnt b (fun i => f (a+i)) := by
  induction b with
  | zero => simp [cnt]
  | succ b ih => simp [cnt,ih,Nat.add_assoc]

lemma cnt_gate (f g : Nat → Bool) (n : Nat) :
    let a := cnt n f
    let b := cnt n g
    let m := cnt n (fun i => f i && g i)
    let j := cnt n (fun i => f i || g i)
    m ≤ a ∧ m ≤ b ∧ a ≤ j ∧ b ≤ j ∧ j ≤ n ∧ m+j = a+b := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    dsimp only at ih ⊢
    simp only [cnt]
    cases f n <;> cases g n <;> simp_all [Bool.toNat] <;> omega

def slow (n x : Nat) : Nat := cnt n x.testBit
def digit (x : Nat) : Nat := (0x76656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110 >>> (4*(x%128))) &&& 15

lemma digit_correct (x : Nat) : digit x = slow 7 x := by
  have table : ∀ i : Fin 128, digit i.val = slow 7 i.val := by decide +kernel
  let i : Fin 128 := ⟨x%128, Nat.mod_lt _ (by decide)⟩
  have eq : digit x = digit i.val := by simp [digit,i]
  rw [eq, table i]
  apply cnt_congr
  intro j hj
  change (x % 2^7).testBit j = x.testBit j
  rw [Nat.testBit_mod_two_pow x 7 j]
  simp [hj]

def pc : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, x => digit x + pc k (x >>> 7)

lemma pc_correct (k x : Nat) : pc k x = slow (7*k) x := by
  induction k generalizing x with
  | zero => simp [pc,slow,cnt]
  | succ k ih =>
    rw [pc,digit_correct,ih]
    unfold slow
    rw [show 7*(k+1) = 7+7*k by omega,cnt_add]
    congr 1
    apply cnt_congr
    intro i _
    simp [Nat.testBit_shiftRight, Nat.add_comm]

def meet (a b : S) : S := (a.1 &&& b.1,a.2 &&& b.2)
def join (a b : S) : S := (a.1 ||| b.1,a.2 ||| b.2)

def limit : Nat → Nat → Nat → Bool
  | 2,p,n => (p ≤ 2) || (p ≤ 3 && n ≥ 2) || (p ≤ 4 && n ≥ 5) ||
      (p ≤ 7 && n ≥ 8) || (p ≤ 9 && n ≥ 9) || (p ≤ 12 && n ≥ 11)
  | 3,p,n => (p ≤ 4) || (p ≤ 7 && n ≥ 2) || (p ≤ 9 && n ≥ 4) ||
      (p ≤ 14 && n ≥ 8) || (p ≤ 18 && n ≥ 9) || (p ≤ 21 && n ≥ 11)
  | 4,p,n => (p ≤ 9) || (p ≤ 14 && n ≥ 2) || (p ≤ 18 && n ≥ 4) || (n ≥ 8)
  | 5,p,n => (p ≤ 18) || (n ≥ 2)
  | _,_,_ => true

def box (a : S) : Bool := limit 2 (pc 3 a.1) (pc 2 a.2)

def posRows : Array Nat := #[0x81,0x101,0x401,0x82,0x202,0x2002,0x104,0x1004,0x2004,0x88,0x808,0x1008,0x410,0x810,0x2010,0x220,0x420,0x1020,0x140,0x240,0x840]
def negRows : Array Nat := #[0xf4,0x13a,0x21d,0x44e,0x827,0xe84,0x1053,0x1390,0x1d02,0x2069,0x2708,0x29a0,0x34c0,0x3a01]
def rawProfiles : Array S := #[(0x7,0x2254),(0x38,0x15a),(0x1c0,0x3d),(0xe00,0x60e),(0x7000,0xc7),(0x38000,0xa13),(0x1c0000,0x1249),(0x209,0x18a1),(0x40042,0xd82),(0x88010,0x24a4),(0x11004,0x1528),(0x102400,0x2930),(0x20880,0x31c0),(0x4120,0x3e00)]
def part0 : List S := [(0x0,0x3),(0x0,0x5),(0x0,0x6),(0x0,0x9),(0x0,0xa),(0x0,0xc),(0x0,0x11),(0x0,0x12)]
def part1 : List S := [(0x0,0x14),(0x0,0x18),(0x0,0x21),(0x0,0x24),(0x0,0x28),(0x0,0x30),(0x0,0x41),(0x0,0x42)]
def part2 : List S := [(0x0,0x44),(0x0,0x48),(0x0,0x50),(0x0,0x81),(0x0,0x82),(0x0,0x84),(0x0,0xa0),(0x0,0xc0)]
def part3 : List S := [(0x0,0x102),(0x0,0x108),(0x0,0x110),(0x0,0x120),(0x0,0x140),(0x0,0x180),(0x0,0x201),(0x0,0x202)]
def part4 : List S := [(0x0,0x204),(0x0,0x208),(0x0,0x210),(0x0,0x240),(0x0,0x402),(0x0,0x404),(0x0,0x408),(0x0,0x420)]
def part5 : List S := [(0x0,0x480),(0x0,0x500),(0x0,0x600),(0x0,0x801),(0x0,0x802),(0x0,0x810),(0x0,0x820),(0x0,0x880)]
def part6 : List S := [(0x0,0x900),(0x0,0xa00),(0x0,0xc00),(0x0,0x1001),(0x0,0x1008),(0x0,0x1020),(0x0,0x1040),(0x0,0x1080)]
def part7 : List S := [(0x0,0x1100),(0x0,0x1200),(0x0,0x1400),(0x0,0x1800),(0x0,0x2004),(0x0,0x2010),(0x0,0x2020),(0x0,0x2040)]
def part8 : List S := [(0x0,0x2080),(0x0,0x2100),(0x0,0x2200),(0x0,0x2400),(0x0,0x2800),(0x0,0x3000),(0x1,0x0),(0x2,0x0)]
def part9 : List S := [(0x4,0x0),(0x7,0x2254),(0x8,0x0),(0x10,0x0),(0x20,0x0),(0x38,0x15a),(0x3f,0x235e),(0x40,0x0)]
def part10 : List S := [(0x80,0x0),(0x100,0x0),(0x1c0,0x3d),(0x1c7,0x227d),(0x1f8,0x17f),(0x200,0x0),(0x209,0x18a1),(0x20f,0x3af5)]
def part11 : List S := [(0x239,0x19fb),(0x3c9,0x18bd),(0x400,0x0),(0x800,0x0),(0xe00,0x60e),(0xe07,0x265e),(0xe09,0x1eaf),(0xe38,0x75e)]
def part12 : List S := [(0xfc0,0x63f),(0x1000,0x0),(0x2000,0x0),(0x4000,0x0),(0x4120,0x3e00),(0x4127,0x3e54),(0x4138,0x3f5a),(0x41e0,0x3e3d)]
def part13 : List S := [(0x4329,0x3ea1),(0x4f20,0x3e0e),(0x7000,0xc7),(0x7007,0x22d7),(0x7038,0x1df),(0x7120,0x3ec7),(0x71c0,0xff),(0x7209,0x18e7)]
def part14 : List S := [(0x7e00,0x6cf),(0x8000,0x0),(0x10000,0x0),(0x11004,0x1528),(0x11007,0x377c),(0x1103c,0x157a),(0x111c4,0x153d),(0x1120d,0x1da9)]
def part15 : List S := [(0x11e04,0x172e),(0x15124,0x3f28),(0x17004,0x15ef),(0x20000,0x0),(0x20880,0x31c0),(0x20887,0x33d4),(0x208b8,0x31da),(0x209c0,0x31fd)]
def part16 : List S := [(0x20a89,0x39e1),(0x20e80,0x37ce),(0x249a0,0x3fc0),(0x27880,0x31c7),(0x31884,0x35e8),(0x38000,0xa13),(0x38007,0x2a57),(0x38038,0xb5b)]
def part17 : List S := [(0x381c0,0xa3f),(0x38209,0x1ab3),(0x38880,0x3bd3),(0x38e00,0xe1f),(0x39004,0x1f3b),(0x3c120,0x3e13),(0x3f000,0xad7),(0x40000,0x0)]
def part18 : List S := [(0x40042,0xd82),(0x40047,0x2fd6),(0x4007a,0xdda),(0x401c2,0xdbf),(0x4024b,0x1da3),(0x40e42,0xf8e),(0x44162,0x3f82),(0x47042,0xdc7)]
def part19 : List S := [(0x51046,0x1daa),(0x608c2,0x3dc2),(0x78042,0xf93),(0x80000,0x0),(0x88010,0x24a4),(0x88017,0x26f4),(0x88038,0x25fe),(0x881d0,0x24bd)]
def part20 : List S := [(0x88219,0x3ca5),(0x88e10,0x26ae),(0x8c130,0x3ea4),(0x8f010,0x24e7),(0x99014,0x35ac),(0xa8890,0x35e4),(0xb8010,0x2eb7),(0xc8052,0x2da6)]
def part21 : List S := [(0x100000,0x0),(0x102400,0x2930),(0x102407,0x2b74),(0x102438,0x297a),(0x1025c0,0x293d),(0x102609,0x39b1),(0x102e00,0x2f3e),(0x106520,0x3f30)]
def part22 : List S := [(0x107400,0x29f7),(0x113404,0x3d38),(0x122c80,0x39f0),(0x13a400,0x2b33),(0x142442,0x2db2),(0x18a410,0x2db4),(0x1c0000,0x1249),(0x1c0007,0x325d)]
def part23 : List S := [(0x1c0038,0x135b),(0x1c0042,0x1fcb),(0x1c01c0,0x127d),(0x1c0209,0x1ae9),(0x1c0e00,0x164f),(0x1c2400,0x3b79),(0x1c4120,0x3e49),(0x1c7000,0x12cf)]
def part24 : List S := [(0x1c8010,0x36ed),(0x1d1004,0x1769),(0x1e0880,0x33c9),(0x1f8000,0x1a5b)]
def catalogue : List S := part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9 ++ part10 ++ part11 ++ part12 ++ part13 ++ part14 ++ part15 ++ part16 ++ part17 ++ part18 ++ part19 ++ part20 ++ part21 ++ part22 ++ part23 ++ part24
def okPair (a b : S) : Bool := box (meet a b) && box (join a b)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell0 : part0.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell1 : part1.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell2 : part2.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell3 : part3.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell4 : part4.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell5 : part5.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell6 : part6.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell7 : part7.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell8 : part8.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell9 : part9.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell10 : part10.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell11 : part11.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell12 : part12.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell13 : part13.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell14 : part14.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell15 : part15.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell16 : part16.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell17 : part17.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell18 : part18.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell19 : part19.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell20 : part20.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell21 : part21.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell22 : part22.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell23 : part23.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell24 : part24.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
lemma allPairs : catalogue.all (fun a => catalogue.all (okPair a)) = true := by
  change (part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9 ++ part10 ++ part11 ++ part12 ++ part13 ++ part14 ++ part15 ++ part16 ++ part17 ++ part18 ++ part19 ++ part20 ++ part21 ++ part22 ++ part23 ++ part24).all (fun a => catalogue.all (okPair a)) = true
  simp only [List.all_append, cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15, cell16, cell17, cell18, cell19, cell20, cell21, cell22, cell23, cell24, Bool.and_self]

def graph : F := fun z => (z 0 && z 7) || (z 0 && z 8) || (z 0 && z 10) || (z 1 && z 7) || (z 1 && z 9) || (z 1 && z 13) || (z 2 && z 8) || (z 2 && z 12) || (z 2 && z 13) || (z 3 && z 7) || (z 3 && z 11) || (z 3 && z 12) || (z 4 && z 10) || (z 4 && z 11) || (z 4 && z 13) || (z 5 && z 9) || (z 5 && z 10) || (z 5 && z 12) || (z 6 && z 8) || (z 6 && z 9) || (z 6 && z 11)

def onRows (rs : Array Nat) (f : F) (i : Nat) : Bool :=
  f (fun v => (rs[i]?.getD 0).testBit v.val)

def Rep (f : F) (s : S) : Prop :=
  (∀ i : Fin 21, onRows posRows f i.val = s.1.testBit i.val) ∧
  (∀ i : Fin 14, onRows negRows f i.val = s.2.testBit i.val)

def raw (v : Fin 14) : S := rawProfiles[v.val]?.getD (0,0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma projections : ∀ v : Fin 14, Rep (fun x => x v) (raw v) := by
  unfold Rep
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstPairs : ∀ i j : Fin 14, meet (raw i) (raw j) ∈ catalogue ∧ join (raw i) (raw j) ∈ catalogue := by
  decide +kernel

lemma rep_meet {f g : F} {a b : S} (hf : Rep f a) (hg : Rep g b) :
    Rep (fun x => f x && g x) (meet a b) := by
  constructor
  · intro i
    change (onRows posRows f i.val && onRows posRows g i.val) = (a.1 &&& b.1).testBit i.val
    rw [hf.1 i, hg.1 i, Nat.testBit_and]
  · intro i
    change (onRows negRows f i.val && onRows negRows g i.val) = (a.2 &&& b.2).testBit i.val
    rw [hf.2 i, hg.2 i, Nat.testBit_and]

lemma rep_join {f g : F} {a b : S} (hf : Rep f a) (hg : Rep g b) :
    Rep (fun x => f x || g x) (join a b) := by
  constructor
  · intro i
    change (onRows posRows f i.val || onRows posRows g i.val) = (a.1 ||| b.1).testBit i.val
    rw [hf.1 i, hg.1 i, Nat.testBit_or]
  · intro i
    change (onRows negRows f i.val || onRows negRows g i.val) = (a.2 ||| b.2).testBit i.val
    rw [hf.2 i, hg.2 i, Nat.testBit_or]

def bounded (k : Nat) (f : F) : Prop :=
  limit k (cnt 21 (onRows posRows f)) (cnt 14 (onRows negRows f)) = true

lemma of_box {f : F} {a : S} (h : Rep f a) (hb : box a = true) : bounded 2 f := by
  have ep : cnt 21 (onRows posRows f) = slow 21 a.1 :=
    cnt_congr 21 (fun i hi => h.1 ⟨i,hi⟩)
  have en : cnt 14 (onRows negRows f) = slow 14 a.2 :=
    cnt_congr 14 (fun i hi => h.2 ⟨i,hi⟩)
  unfold bounded
  rw [ep,en]
  simpa only [box,pc_correct] using hb

set_option maxHeartbeats 0 in
lemma lift_limits {k a b c d u v w z : Nat} (lo : 2 ≤ k) (hi : k ≤ 4)
    (h1 : limit k a b = true) (h2 : limit k c d = true)
    (hp : u ≤ a ∧ u ≤ c ∧ a ≤ w ∧ c ≤ w ∧ w ≤ 21 ∧ u+w = a+c)
    (hn : v ≤ b ∧ v ≤ d ∧ b ≤ z ∧ d ≤ z ∧ z ≤ 14 ∧ v+z = b+d) :
    limit (k+1) u v = true ∧ limit (k+1) w z = true := by
  interval_cases k <;> norm_num [limit] at * <;> omega

lemma bounded_step {k : Nat} (lo : 2 ≤ k) (hi : k ≤ 4) (f g : F)
    (hf : bounded k f) (hg : bounded k g) :
    bounded (k+1) (fun x => f x && g x) ∧ bounded (k+1) (fun x => f x || g x) := by
  exact lift_limits lo hi hf hg (cnt_gate (onRows posRows f) (onRows posRows g) 21)
    (cnt_gate (onRows negRows f) (onRows negRows g) 14)

def level : Nat → Set F
  | 0 => {f | ∃ v : Fin 14, f = fun x => x v}
  | 1 => {f | ∃ a ∈ catalogue, Rep f a}
  | k+2 => {f | bounded (k+2) f}

lemma closed (k : Nat) (f g : F) (hf : f ∈ level k) (hg : g ∈ level k) :
    (fun x => f x && g x) ∈ level (k+1) ∧ (fun x => f x || g x) ∈ level (k+1) := by
  match k with
  | 0 =>
    obtain ⟨i,rfl⟩ := hf
    obtain ⟨j,rfl⟩ := hg
    exact ⟨⟨_,(firstPairs i j).1,rep_meet (projections i) (projections j)⟩,
      ⟨_,(firstPairs i j).2,rep_join (projections i) (projections j)⟩⟩
  | 1 =>
    obtain ⟨a,ha,hfa⟩ := hf
    obtain ⟨b,hb,hgb⟩ := hg
    have hp := List.all_eq_true.mp (List.all_eq_true.mp allPairs a ha) b hb
    have ok : box (meet a b) = true ∧ box (join a b) = true := by
      simpa only [okPair, Bool.and_eq_true] using hp
    exact ⟨of_box (rep_meet hfa hgb) ok.1,of_box (rep_join hfa hgb) ok.2⟩
  | j+2 =>
    by_cases h : j+2 ≤ 4
    · exact bounded_step (by omega : 2 ≤ j+2) h f g hf hg
    · have hj : 3 ≤ j := by omega
      obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hj
      change bounded _ _ ∧ bounded _ _
      rw [show 3+r+2+1 = r+6 by omega]
      exact ⟨rfl,rfl⟩

set_option maxHeartbeats 0 in
lemma end_check : ¬ bounded 5 graph := by
  unfold bounded
  decide +kernel

end PEqualNP.Outside.L_meta_1620

open PEqualNP.Outside.L_meta_1620

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1620 : ¬ (∀ T : ℕ → Set ((Fin 14 → Bool) → Bool), (∀ i : Fin 14, (fun x : Fin 14 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 14 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 14 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 14 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 14 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 14 → Bool => (z 0 && z 7) || (z 0 && z 8) || (z 0 && z 10) || (z 1 && z 7) || (z 1 && z 9) || (z 1 && z 13) || (z 2 && z 8) || (z 2 && z 12) || (z 2 && z 13) || (z 3 && z 7) || (z 3 && z 11) || (z 3 && z 12) || (z 4 && z 10) || (z 4 && z 11) || (z 4 && z 13) || (z 5 && z 9) || (z 5 && z 10) || (z 5 && z 12) || (z 6 && z 8) || (z 6 && z 9) || (z 6 && z 11)) ∈ T 5) := by
  intro universal
  have start (i : Fin 14) : (fun x : Fin 14 → Bool => x i) ∈ level 0 := ⟨i,rfl⟩
  have up (k : Nat) (f : F) (hf : f ∈ level k) : f ∈ level (k+1) := by
    simpa using (closed k f f hf hf).1
  exact end_check (show graph ∈ level 5 from universal level start up closed)
