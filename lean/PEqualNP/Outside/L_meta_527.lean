import Mathlib
import PEqualNP.Defs

namespace P527

-- The low and high halves evaluate a signal on 48 pairs of inputs.
-- In each pair the desired outputs differ, so some live wire must separate them.
abbrev T := BitVec 96

def target : T := 281474976710655

def inputs : List T := [2588468336438474776376947, 31147410679154614878656153727,
  40562412792052272745989771164, 24815623546640349326736887776,
  54391996652302177207391875072, 79225565212699040763619573760]

def ops (a b : T) : List T := if a = b then [~~~a] else
  if a < b then [a &&& b, a ||| b] else []

-- Read the circuit backwards. Replace a needed gate output by its operands,
-- retaining each operand separately if another gate also needs it.
def plan : ℕ → Finset T → Prop
  | 0, S => S = {target}
  | n+1, S => ∃ (a b z : T) (R : Finset T), z ∉ R ∧ z ≠ a ∧ z ≠ b ∧
      z ∈ ops a b ∧ S = insert a (insert b R) ∧ plan n (insert z R)

lemma cardPlan {n S} (h : plan n S) : S.card ≤ n+1 := by
  induction n generalizing S with
  | zero => change S = {target} at h; simp [h]
  | succ n ih =>
    obtain ⟨a,b,z,R,hz,_,_,_,rfl,h⟩ := h
    have h₁ := ih h
    rw [Finset.card_insert_of_notMem hz] at h₁
    have := Finset.card_insert_le a (insert b R)
    have := Finset.card_insert_le b R
    omega

lemma distinguish {n S} (h : plan n S) (i j : Fin 96) (hij : target[i.val] ≠ target[j.val]) :
    ∃ a ∈ S, a[i.val] ≠ a[j.val] := by
  induction n generalizing S with
  | zero => change S = {target} at h; exact ⟨target, by simp [h], hij⟩
  | succ n ih =>
    obtain ⟨a,b,z,R,_,_,_,hop,rfl,h⟩ := h
    obtain ⟨w,hw,hd⟩ := ih h
    rcases Finset.mem_insert.mp hw with rfl | hw
    · by_contra! bad
      have ha := bad a (by simp)
      have hb := bad b (by simp)
      unfold ops at hop
      split at hop
      · simp_all
      · split at hop <;> simp_all
        rcases hop with rfl | rfl <;> simp_all
    · exact ⟨w, by simp [hw], hd⟩

def sig (w : T) : BitVec 48 := (w ^^^ (w >>> 48)).setWidth 48

def sep : List T → BitVec 48
  | [] => 0
  | w :: ws => sig w ||| sep ws

lemma bitSep {w : T} {ws : List T} (hw : w ∈ ws) (i : Fin 48)
    (hd : w.getLsbD i.val ≠ w.getLsbD (i.val+48)) : (sep ws)[i.val] = true := by
  induction ws with
  | nil => simp at hw
  | cons a l ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · have h1 : i.val < 96 := by omega
      have h2 : i.val+48 < 96 := by omega
      simp only [sep, BitVec.getElem_or, Bool.or_eq_true]
      left
      change ((sig w).getLsbD i.val) = true
      simpa [sig, BitVec.getLsbD_setWidth, i.isLt, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, Nat.add_comm] using hd
    · simp [sep,ih hw]

lemma sepPlan {n} {l : List T} (h : plan n l.toFinset) : sep l = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hj : i+48 < 96 := by omega
  have hh : ∀ k : Fin 48, target.getLsbD k.val ≠ target.getLsbD (k.val+48) := by decide
  obtain ⟨w,hw,hd⟩ := distinguish h ⟨i,by omega⟩ ⟨i+48,hj⟩ (hh ⟨i,hi⟩)
  have hone : ∀ j : Fin 48, ((-1 : BitVec 48).getLsbD j.val) = true := by decide
  exact (bitSep (List.mem_toFinset.mp hw) ⟨i,hi⟩ hd).trans (hone ⟨i,hi⟩).symm

def tails (l : List T) (a b : T) : List (List T) :=
  [l.filter (fun x => x != a && x != b), l.filter (· != a), l.filter (· != b), l]

lemma memTails {l : List T} {a b : T} {R : Finset T} (he : l.toFinset = insert a (insert b R)) :
    ∃ u ∈ tails l a b, u.toFinset = R := by
  by_cases ha : a ∈ R <;> by_cases hb : b ∈ R
  · exact ⟨l, by simp [tails], by simpa [ha,hb] using he⟩
  · refine ⟨l.filter (· != b), by simp [tails], ?_⟩
    ext x
    have hm := Finset.ext_iff.mp he x
    simp_all
    grind
  · refine ⟨l.filter (· != a), by simp [tails], ?_⟩
    ext x
    have hm := Finset.ext_iff.mp he x
    simp_all
    grind
  · refine ⟨l.filter (fun x => x != a && x != b), by simp [tails], ?_⟩
    ext x
    have hm := Finset.ext_iff.mp he x
    simp_all
    grind

def live (r : ℕ) (l : List T) : Bool := decide (l.length ≤ r+1) && (sep l == -1)

def kids (r : ℕ) (l : List T) : List (List T) :=
  l.flatMap fun a => l.flatMap fun b => (ops a b).flatMap fun z =>
    if z ∈ l then [] else ((tails l a b).map (z :: ·)).filter (live r)

def check : ℕ → List T → Bool
  | 0, l => l.contains target
  | r+1, l => l.contains target || (kids r l).any (check r)

lemma livePlan {n S} (h : plan n S) {r} (hr : n ≤ r) {l : List T}
    (hn : l.Nodup) (he : l.toFinset = S) : live r l = true := by
  subst S
  have hc := cardPlan h
  rw [List.toFinset_card_of_nodup hn] at hc
  simp [live,sepPlan h,show l.length ≤ r+1 by omega]

lemma checked {n S} (h : plan n S) : ∀ r, n ≤ r → ∀ l : List T,
    l.Nodup → l.toFinset = S → check r l = true := by
  induction n generalizing S with
  | zero =>
    change S = {target} at h
    intro r _ l hn he
    have hm : target ∈ l := List.mem_toFinset.mp (by rw [he,h]; simp)
    cases r <;> simp [check,hm]
  | succ n ih =>
    intro r hr l hn he
    cases r with
    | zero => omega
    | succ r =>
      obtain ⟨a,b,z,R,hz,hza,hzb,hop,rfl,hh⟩ := h
      have ha : a ∈ l := List.mem_toFinset.mp (by rw [he]; simp)
      have hb : b ∈ l := List.mem_toFinset.mp (by rw [he]; simp)
      have hz' : z ∉ l := fun hl => by have := List.mem_toFinset.mpr hl; rw [he] at this; simp_all
      obtain ⟨u,hu,heu⟩ := memTails he
      have hnu : u.Nodup := by
        simp only [tails,List.mem_cons,List.not_mem_nil,or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl <;> first | exact hn.filter _ | exact hn
      have hzu : z ∉ u := fun hl => hz (heu ▸ List.mem_toFinset.mpr hl)
      have hnd := List.nodup_cons.mpr ⟨hzu,hnu⟩
      have he' : (z::u).toFinset = insert z R := by simp [heu]
      have hm : z::u ∈ kids r l := by
        simp only [kids,List.mem_flatMap]
        refine ⟨a,ha,b,hb,z,hop,?_⟩
        rw [if_neg hz']
        simp only [List.mem_filter,List.mem_map]
        exact ⟨⟨u,hu,rfl⟩, livePlan hh (by omega) hnd he'⟩
      simp only [check,Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨_,hm,ih hh r (by omega) _ hnd he'⟩)

lemma close {r l ks} (h₀ : l.contains target = false) (hk : kids r l = ks)
    (h : ks.any (check r) = false) : check (r+1) l = false := by rw [check,h₀,hk,h]; rfl

def pool : List T := 0 :: (-1) :: inputs

open PEqualNP.CircuitLowerBounds

def avail (w : List T) : Finset T := insert 0 (insert (-1) w.toFinset)

def bit (i : Fin 96) (a : T) : Bool := a[i.val]

lemma readMem (w : List T) (j : ℕ) : w.getD j 0 ∈ avail w := by
  by_cases h : j < w.length
  · rw [List.getD_eq_getElem _ _ h]; simp [avail]
  · rw [List.getD_eq_default _ _ (by omega : w.length ≤ j)]; simp [avail]

lemma readBit (w : List T) (j : ℕ) (i : Fin 96) :
    (w.map (bit i)).getD j false = bit i (w.getD j 0) := by
  by_cases h : j < w.length
  · simp [h]
  · simp [Nat.le_of_not_gt h, bit]

def good (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def lift (g : Gate) (w : List T) : T :=
  let a := w.getD (g.inputs.headD w.length) 0
  let b := w.getD (g.inputs.getD 1 w.length) 0
  match g.op with
  | .not => ~~~a
  | .and => if g.inputs.isEmpty then -1 else if g.inputs.length = 1 then a else a &&& b
  | .or => a ||| b
  | _ => 0

lemma liftBit {g : Gate} (hg : good g) (w : List T) (i : Fin 96) :
    bit i (lift g w) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨op,l⟩ := g
  obtain ⟨hop,hl⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change l.length ≤ 2 at hl
  have hone' : ∀ j : Fin 96, (79228162514264337593543950335 : T).getLsbD j.val = true := by decide
  have hone : (79228162514264337593543950335 : T)[i.val] = true := hone' i
  have hread (j : ℕ) : (w[j]?.getD 0)[i.val] = ((w[j]?).map (bit i)).getD false := by
    cases w[j]? <;> simp [bit]
  rcases hop with rfl | rfl | rfl <;>
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩ <;>
    simp_all [lift, GateOp.eval, bit, List.getD, List.headD]

lemma binCase {w : List T} {a b z : T} (ha : a ∈ avail w) (hb : b ∈ avail w)
    (hz : z = a &&& b ∨ z = a ||| b) :
    z ∈ avail w ∨ ∃ a ∈ avail w, ∃ b ∈ avail w, z ∈ ops a b := by
  by_cases he : a = b
  · subst b
    have : z = a := by simpa using hz
    exact Or.inl (this ▸ ha)
  by_cases h : a < b
  · exact Or.inr ⟨a,ha,b,hb,by simpa [ops,h,he] using hz⟩
  · have hne : a.toNat ≠ b.toNat := fun e => he (BitVec.eq_of_toNat_eq e)
    change ¬ a.toNat < b.toNat at h
    have h' : b < a := show b.toNat < a.toNat by omega
    refine Or.inr ⟨b,hb,a,ha,?_⟩
    simpa [ops,h',Ne.symm he,BitVec.and_comm b a,BitVec.or_comm b a] using hz

lemma liftCase {g : Gate} (hg : good g) (w : List T) :
    lift g w ∈ avail w ∨ ∃ a ∈ avail w, ∃ b ∈ avail w, lift g w ∈ ops a b := by
  obtain ⟨op,l⟩ := g
  obtain ⟨hop,hl⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  let a := w.getD (l.headD w.length) 0
  let b := w.getD (l.getD 1 w.length) 0
  have ha : a ∈ avail w := readMem _ _
  have hb : b ∈ avail w := readMem _ _
  rcases hop with rfl | rfl | rfl
  · by_cases h : l.isEmpty
    · left; simp [lift,h,avail]
    by_cases h' : l.length = 1
    · left; simpa [lift,h,h',a] using ha
    · exact binCase ha hb (Or.inl (by simp [lift,h,h',a,b]))
  · exact binCase ha hb (Or.inr rfl)
  · exact Or.inr ⟨a,ha,a,ha,by simp [lift,ops,a]⟩

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun j => u.getD j false)]) w

lemma extractPlan {gs : List Gate} {o : ℕ} (hg : ∀ g ∈ gs, good g) (w : List T)
    (he : ∀ i : Fin 96, (run gs (w.map (bit i))).getD o false = bit i target) :
    ∃ n ≤ gs.length, ∃ S ⊆ avail w, plan n S := by
  induction gs generalizing w with
  | nil =>
    have eq : w.getD o 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      exact (readBit w o ⟨j,hj⟩).symm.trans (he ⟨j,hj⟩)
    exact ⟨0,by simp,{target},Finset.singleton_subset_iff.mpr (eq ▸ readMem w o),rfl⟩
  | cons g gs ih =>
    have hgood := hg g List.mem_cons_self
    let z := lift g w
    have hv : avail (w ++ [z]) = insert z (avail w) := by ext; simp [avail]; tauto
    obtain ⟨n,hn,S,hS,hp⟩ := ih (fun g' h => hg g' (List.mem_cons_of_mem _ h)) (w ++ [z]) (by
      intro i
      simpa [run, z, liftBit hgood] using he i)
    rw [hv] at hS
    by_cases hs : S ⊆ avail w
    · exact ⟨n,by simp; omega,S,hs,hp⟩
    have hz : z ∉ avail w := fun h => hs (by simpa [Finset.insert_eq_of_mem h] using hS)
    have hzS : z ∈ S := by
      by_contra h
      apply hs
      intro x hx
      rcases Finset.mem_insert.mp (hS hx) with rfl | hm
      · exact False.elim (h hx)
      · exact hm
    obtain ⟨a,ha,b,hb,hop⟩ := (liftCase hgood w).resolve_left hz
    let R := S.erase z
    have hR : R ⊆ avail w := by
      intro x hx
      obtain ⟨hne,hh⟩ := Finset.mem_erase.mp hx
      exact (Finset.mem_insert.mp (hS hh)).resolve_left hne
    refine ⟨n+1,by simpa using hn,insert a (insert b R),Finset.insert_subset ha (Finset.insert_subset hb hR),?_⟩
    exact ⟨a,b,z,R,Finset.notMem_erase _ _,fun e => hz (e ▸ ha),fun e => hz (e ▸ hb),
      hop,rfl,by simpa [R,Finset.insert_erase hzS] using hp⟩

-- The finite calculation is split at each surviving state. Each child list
-- below is recomputed from the gate rules and checked by the kernel.
def w0 : T := 2588468336438474776376947

def w1 : T := 31147410679154614878656153727

def w2 : T := 40562412792052272745989771164

def w3 : T := 24815623546640349326736887776

def w4 : T := 54391996652302177207391875072

def w5 : T := 79225565212699040763619573760

def s0 : List T := [w0,w1,w2,w3,w4,w5]

def w6 : T := 79225574045927899118767573388

def s1 : List T := [w6,w1,w2,w3,w4,w5]

def s2 : List T := [w0,w1,w2,w3,w4,w5]

def w7 : T := 48080751835109722714887796608

def s3 : List T := [w7,w6,w2,w3,w4,w5]

def w8 : T := 79225568833460566455480633471

def s4 : List T := [w8,w6,w1,w2,w3,w4]

def w9 : T := 38665749722212064847554179171

def s5 : List T := [w9,w6,w1,w3,w4,w5]

def w10 : T := 54412538967623988266807062559

def s6 : List T := [w10,w6,w1,w2,w4,w5]

def w11 : T := 24836165861962160386152075263

def s7 : List T := [w11,w6,w1,w2,w3,w5]

def w12 : T := 79225571388899540942532374528

def s8 : List T := [w12,w6,w1,w2,w3,w4]

def w13 : T := 79225574045927901074017880460

def s9 : List T := [w13,w6,w1,w2,w3,w4]

def w14 : T := 2597301565296829924376575

def s10 : List T := [w14,w6,w1,w2,w3,w4]

def s11 : List T := [w6,w0,w1,w2,w3,w4,w5]

def w15 : T := 1955250307072

def s12 : List T := [w15,w6,w1,w2,w3,w4]

def w16 : T := 31147410679154616266836559999

def s13 : List T := [w16,w6,w2,w3,w4]

def w17 : T := 54391996652302177238496833536

def s14 : List T := [w17,w6,w1,w2,w3]

def s15 : List T := [w13,w0,w1,w2,w3,w4]

def w18 : T := 567069917299

def s16 : List T := [w18,w0,w1,w2,w3,w4,w5]

def w19 : T := 40562412792052273313059688447

def s17 : List T := [w19,w0,w1,w3,w4,w5]

def w20 : T := 24815623546640349876626935795

def s18 : List T := [w20,w0,w1,w2,w4,w5]

def w21 : T := 54391996652302177224705962099

def s19 : List T := [w21,w0,w1,w2,w3,w5]

def w22 : T := 79225565212699040763619590259

def s20 : List T := [w22,w0,w1,w2,w3,w4]

def w23 : T := 31149999147491052786362613375

def s21 : List T := [w23,w18,w2,w3,w4,w5]

def s22 : List T := [w23,w0,w1,w2,w3,w4,w5]

def w24 : T := 31147407058393090574975500288

def s23 : List T := [w24,w0,w1,w2,w3,w4]

def s24 : List T := [w16,w0,w2,w3,w4]

def s25 : List T := [w18,w23,w2,w3,w4,w5]

def s26 : List T := [w8,w23,w0,w2,w3,w4]

def w25 : T := 1955250323571

def s27 : List T := [w25,w23,w2,w3,w4]

def w26 : T := 151134466930978452506128

def s28 : List T := [w26,w0,w1,w2,w3,w4,w5]

def w27 : T := 40564850125921780242313641983

def s29 : List T := [w27,w26,w1,w3,w4,w5]

def s30 : List T := [w27,w0,w1,w2,w3,w4,w5]

def w28 : T := 40562256889028817174906535936

def s31 : List T := [w28,w0,w1,w2,w3,w4]

def w29 : T := 54411717254734641120648622080

def s32 : List T := [w29,w0,w1,w2,w3]

def s33 : List T := [w26,w27,w1,w3,w4,w5]

def w30 : T := 7304800258175

def s34 : List T := [w30,w0,w2,w3,w4,w5]

def w31 : T := 2418442097169233707271776

def s35 : List T := [w31,w0,w1,w2,w3,w4,w5]

def w32 : T := 24815793572879618567805992947

def s36 : List T := [w32,w31,w1,w2,w4,w5]

def s37 : List T := [w32,w0,w1,w2,w3,w4,w5]

def w33 : T := 274603062194176

def s38 : List T := [w33,w0,w1,w2,w3,w5]

def w34 : T := 24813202447590538685496426496

def s39 : List T := [w34,w0,w1,w2,w3,w4]

def w35 : T := 36110051168672836257852049535

def s40 : List T := [w35,w0,w2,w3,w4]

def s41 : List T := [w31,w32,w1,w2,w4,w5]

def w36 : T := 1924147572736

def s42 : List T := [w36,w0,w1,w2,w3,w4,w5]

def w37 : T := 31147410679154616253047896191

def s43 : List T := [w37,w0,w2,w3,w4,w5]

def w38 : T := 40562412792052273570625617820

def s44 : List T := [w38,w0,w1,w3,w4,w5]

def w39 : T := 24815623546640351250882363360

def s45 : List T := [w39,w0,w1,w2,w4,w5]

def w40 : T := 79225565212699040763621797888

def s46 : List T := [w40,w0,w1,w2,w3,w4]

def w41 : T := 54394585120638613758020679283

def s47 : List T := [w41,w36,w1,w2,w3,w5]

def s48 : List T := [w41,w0,w1,w2,w3,w4,w5]

def w42 : T := 54391990476101677059584032768

def s49 : List T := [w42,w0,w1,w2,w3,w4]

def s50 : List T := [w17,w0,w1,w2,w3]

def s51 : List T := [w36,w41,w1,w2,w3,w5]

def s52 : List T := [w12,w41,w0,w1,w2,w3]

def w43 : T := 1955252531200

def s53 : List T := [w43,w41,w1,w2,w3]

def s54 : List T := [w15,w0,w1,w2,w3,w4]

def w44 : T := 79228162514264335638293643263

def s55 : List T := [w44,w0,w1,w2,w3,w4]

def s56 : List T := [w16,w0,w2,w3,w4]

def w45 : T := 48080751835109721326707390336

def s57 : List T := [w45,w0,w2,w3,w4]

def s58 : List T := [w6,w16,w2,w3,w4]

def s59 : List T := [w9,w16,w0,w3,w4]

def s60 : List T := [w10,w16,w0,w2,w4]

def s61 : List T := [w11,w16,w0,w2,w3]

def s62 : List T := [w16,w0,w1,w2,w3,w4]

def s63 : List T := [w16,w15,w0,w2,w3,w4]

def w46 : T := 40562412792052273600923144092

def s64 : List T := [w46,w16,w0,w3,w4]

def w47 : T := 24815623546640351251922423776

def s65 : List T := [w47,w16,w0,w2,w4]

def s66 : List T := [w17,w16,w0,w2,w3]

def s67 : List T := [w46,w15,w0,w1,w3,w4]

def s68 : List T := [w16,w46,w0,w3,w4]

def s69 : List T := [w47,w46,w0,w1,w4]

def s70 : List T := [w17,w46,w0,w1,w3]

def s71 : List T := [w47,w15,w0,w1,w2,w4]

def s72 : List T := [w16,w47,w0,w2,w4]

def s73 : List T := [w46,w47,w0,w1,w4]

def s74 : List T := [w17,w47,w0,w1,w2]

def s75 : List T := [w17,w0,w1,w2,w3]

def w48 : T := 24836165861962160355047116799

def s76 : List T := [w48,w0,w1,w2,w3]

def s77 : List T := [w6,w17,w1,w2,w3]

def s78 : List T := [w7,w17,w0,w2,w3]

def s79 : List T := [w9,w17,w0,w1,w3]

def s80 : List T := [w10,w17,w0,w1,w2]

def s81 : List T := [w17,w0,w1,w2,w3,w4]

def s82 : List T := [w17,w15,w0,w1,w2,w3]

def s83 : List T := [w16,w17,w0,w2,w3]

def s84 : List T := [w46,w17,w0,w1,w3]

def s85 : List T := [w47,w17,w0,w1,w2]

def s86 : List T := [w6,w15,w1,w2,w3,w4]

def s87 : List T := [w7,w15,w0,w2,w3,w4]

def s88 : List T := [w17,w7,w0,w2,w3]

def s89 : List T := [w9,w15,w0,w1,w3,w4]

def s90 : List T := [w16,w9,w0,w3,w4]

def s91 : List T := [w17,w9,w0,w1,w3]

def s92 : List T := [w10,w15,w0,w1,w2,w4]

def s93 : List T := [w16,w10,w0,w2,w4]

def s94 : List T := [w17,w10,w0,w1,w2]

def s95 : List T := [w11,w15,w0,w1,w2,w3]

def s96 : List T := [w16,w11,w0,w2,w3]

def s97 : List T := [w15,w0,w1,w2,w3,w4,w5]

def s98 : List T := [w16,w0,w2,w3,w4,w5]

def s99 : List T := [w46,w0,w1,w3,w4,w5]

def s100 : List T := [w47,w0,w1,w2,w4,w5]

def s101 : List T := [w17,w0,w1,w2,w3,w5]

def w49 : T := 79228153681035477283145643635

def s102 : List T := [w49,w15,w1,w2,w3,w4]

def s103 : List T := [w49,w0,w1,w2,w3,w4,w5]

def s104 : List T := [w15,w49,w1,w2,w3,w4]

def s105 : List T := [w7,w0,w2,w3,w4,w5]

def s106 : List T := [w1,w0,w2,w3,w4,w5]

def w50 : T := 48078158154305951576824479744

def s107 : List T := [w50,w7,w0,w2,w3,w4]

def s108 : List T := [w6,w7,w2,w3,w4,w5]

def s109 : List T := [w15,w7,w0,w2,w3,w4]

def s110 : List T := [w9,w7,w0,w3,w4,w5]

def s111 : List T := [w10,w7,w0,w2,w4,w5]

def s112 : List T := [w11,w7,w0,w2,w3,w5]

def s113 : List T := [w12,w7,w0,w2,w3,w4]

def s114 : List T := [w14,w7,w0,w2,w3,w4]

def s115 : List T := [w7,w0,w1,w2,w3,w4,w5]

def s116 : List T := [w50,w0,w1,w2,w3,w4]

def s117 : List T := [w8,w7,w0,w2,w3,w4]

def w51 : T := 6737730340892

def s118 : List T := [w51,w0,w1,w2,w3,w4,w5]

def w52 : T := 2588468336445212506717823

def s119 : List T := [w52,w1,w2,w3,w4,w5]

def s120 : List T := [w8,w52,w2,w3,w4]

def w53 : T := 24815623546640355927028273148

def s121 : List T := [w53,w0,w1,w2,w4,w5]

def s122 : List T := [w8,w53,w0,w2,w4]

def w54 : T := 54391996652302177348052056092

def s123 : List T := [w54,w0,w1,w2,w3,w5]

def w55 : T := 79225565212699040763619969052

def s124 : List T := [w55,w0,w1,w2,w3,w4]

def w56 : T := 71709823471206880886915583999

def s125 : List T := [w56,w51,w0,w3,w4,w5]

def s126 : List T := [w8,w51,w0,w2,w3,w4]

def s127 : List T := [w52,w8,w2,w3,w4]

def s128 : List T := [w53,w8,w0,w2,w4]

def s129 : List T := [w56,w0,w1,w2,w3,w4,w5]

def s130 : List T := [w51,w56,w0,w3,w4,w5]

def w57 : T := 11296204117469490739086245888

def s131 : List T := [w57,w0,w1,w2,w3,w4,w5]

def w58 : T := 79225566471689323794309464064

def s132 : List T := [w58,w0,w1,w2,w3,w4]

def w59 : T := 74243203213987301346961782911

def s133 : List T := [w59,w57,w0,w2,w3,w5]

def s134 : List T := [w59,w0,w1,w2,w3,w4,w5]

def w60 : T := 79225573750670783603703543935

def s135 : List T := [w60,w0,w1,w2,w3,w4]

def w61 : T := 1955252531315

def s136 : List T := [w61,w1,w2,w3,w4]

def s137 : List T := [w57,w59,w0,w2,w3,w5]

def w62 : T := 31147407058393089186795094016

def s138 : List T := [w62,w0,w1,w2,w3,w4,w5]

def s139 : List T := [w8,w62,w0,w2,w3,w4]

def s140 : List T := [w8,w0,w1,w2,w3,w4]

def w63 : T := 2593680803771138063316864

def s141 : List T := [w63,w0,w1,w2,w3,w4]

def s142 : List T := [w25,w0,w1,w2,w3,w4]

def w64 : T := 54391996652302177238496833651

def s143 : List T := [w64,w0,w1,w2,w3]

def s144 : List T := [w23,w25,w2,w3,w4]

def s145 : List T := [w6,w8,w1,w2,w3,w4]

def s146 : List T := [w23,w8,w0,w2,w3,w4]

def s147 : List T := [w7,w8,w0,w2,w3,w4]

def s148 : List T := [w51,w8,w0,w2,w3,w4]

def s149 : List T := [w9,w8,w0,w1,w3,w4]

def w65 : T := 36112469905953938062589186047

def s150 : List T := [w65,w8,w0,w2,w3,w4]

def w66 : T := 147578314690460

def s151 : List T := [w66,w8,w0,w3,w4]

def s152 : List T := [w10,w8,w0,w1,w2,w4]

def s153 : List T := [w11,w8,w0,w1,w2,w3]

def s154 : List T := [w8,w0,w1,w2,w3,w4,w5]

def s155 : List T := [w62,w8,w0,w2,w3,w4]

def s156 : List T := [w9,w0,w1,w3,w4,w5]

def s157 : List T := [w2,w0,w1,w3,w4,w5]

def s158 : List T := [w6,w9,w1,w3,w4,w5]

def s159 : List T := [w15,w9,w0,w1,w3,w4]

def s160 : List T := [w7,w9,w0,w3,w4,w5]

def s161 : List T := [w8,w9,w0,w1,w3,w4]

def s162 : List T := [w10,w9,w0,w1,w4,w5]

def s163 : List T := [w11,w9,w0,w1,w3,w5]

def s164 : List T := [w12,w9,w0,w1,w3,w4]

def s165 : List T := [w14,w9,w0,w1,w3,w4]

def s166 : List T := [w9,w0,w1,w2,w3,w4,w5]

def w67 : T := 40542541055079695490952429568

def s167 : List T := [w67,w0,w1,w2,w3,w4,w5]

def w68 : T := 79225569981182383817555935232

def s168 : List T := [w68,w0,w1,w2,w3,w4]

def w69 : T := 54411868389274754462429216668

def s169 : List T := [w69,w67,w0,w1,w3,w5]

def s170 : List T := [w69,w0,w1,w2,w3,w4,w5]

def s171 : List T := [w67,w69,w0,w1,w3,w5]

def w70 : T := 272919434891136

def s172 : List T := [w70,w0,w1,w2,w4,w5]

def s173 : List T := [w12,w70,w0,w1,w2]

def s174 : List T := [w12,w69,w0,w1,w2,w3]

def s175 : List T := [w70,w12,w0,w1,w2]

def w71 : T := 40562256889028816319973163008

def s176 : List T := [w71,w0,w1,w2,w3,w4,w5]

def w72 : T := 54411717254734641090348969984

def s177 : List T := [w72,w0,w1,w2,w3,w5]

def w73 : T := 79225721115722497189636181916

def s178 : List T := [w73,w71,w0,w1,w3,w4]

def s179 : List T := [w73,w0,w1,w2,w3,w4,w5]

def s180 : List T := [w71,w73,w0,w1,w3,w4]

def w74 : T := 19850564319841026142803855456

def s181 : List T := [w74,w0,w1,w2,w3,w4,w5]

def w75 : T := 79225567574467750150012930144

def s182 : List T := [w75,w0,w1,w2,w3,w4]

def s183 : List T := [w65,w74,w0,w2,w4,w5]

def s184 : List T := [w65,w0,w1,w2,w3,w4,w5]

def s185 : List T := [w66,w0,w1,w3,w4,w5]

def s186 : List T := [w8,w66,w0,w3,w4]

def s187 : List T := [w8,w65,w0,w2,w3,w4]

def s188 : List T := [w74,w65,w0,w2,w4,w5]

def w76 : T := 140978023305088

def s189 : List T := [w76,w0,w1,w2,w3,w4,w5]

def w77 : T := 2588468336579452799680499

def s190 : List T := [w77,w1,w2,w3,w4,w5]

def w78 : T := 31147410679154755719240503295

def s191 : List T := [w78,w0,w2,w3,w4,w5]

def w79 : T := 54391996652302177447910047616

def s192 : List T := [w79,w0,w1,w2,w3,w5]

def w80 : T := 79225565212699040763636354944

def s193 : List T := [w80,w0,w1,w2,w3,w4]

def w81 : T := 65378036338692481094703353852

def s194 : List T := [w81,w76,w0,w1,w4,w5]

def s195 : List T := [w81,w0,w1,w2,w3,w4,w5]

def s196 : List T := [w76,w81,w0,w1,w4,w5]

def s197 : List T := [w10,w0,w1,w2,w4,w5]

def s198 : List T := [w3,w0,w1,w2,w4,w5]

def s199 : List T := [w6,w10,w1,w2,w4,w5]

def s200 : List T := [w15,w10,w0,w1,w2,w4]

def s201 : List T := [w7,w10,w0,w2,w4,w5]

def s202 : List T := [w8,w10,w0,w1,w2,w4]

def s203 : List T := [w9,w10,w0,w1,w4,w5]

def s204 : List T := [w11,w10,w0,w1,w2,w5]

def s205 : List T := [w12,w10,w0,w1,w2,w4]

def s206 : List T := [w14,w10,w0,w1,w2,w4]

def s207 : List T := [w10,w0,w1,w2,w3,w4,w5]

def w82 : T := 272678916718592

def s208 : List T := [w82,w0,w1,w2,w3,w4,w5]

def w83 : T := 2588468336711153690998387

def s209 : List T := [w83,w1,w2,w3,w4,w5]

def s210 : List T := [w12,w83,w1,w2,w3]

def w84 : T := 31147410679154782004444022911

def s211 : List T := [w84,w0,w2,w3,w4,w5]

def w85 : T := 40562412792052404687401357212

def s212 : List T := [w85,w0,w1,w3,w4,w5]

def s213 : List T := [w12,w85,w0,w1,w3]

def w86 : T := 79225565212699040763652603904

def s214 : List T := [w86,w0,w1,w2,w3,w4]

def w87 : T := 79207620198942253855212044256

def s215 : List T := [w87,w82,w0,w1,w2,w5]

def s216 : List T := [w12,w82,w0,w1,w2,w3]

def s217 : List T := [w83,w12,w1,w2,w3]

def s218 : List T := [w85,w12,w0,w1,w3]

def s219 : List T := [w87,w0,w1,w2,w3,w4,w5]

def s220 : List T := [w82,w87,w0,w1,w2,w5]

def w88 : T := 24813202447590536760310890496

def s221 : List T := [w88,w0,w1,w2,w3,w4,w5]

def w89 : T := 36110051168672834882556545151

def s222 : List T := [w89,w0,w2,w3,w4,w5]

def w90 : T := 79227986311748853330045571040

def s223 : List T := [w90,w88,w0,w1,w2,w4]

def s224 : List T := [w90,w0,w1,w2,w3,w4,w5]

def s225 : List T := [w88,w90,w0,w1,w2,w4]

def s226 : List T := [w11,w0,w1,w2,w3,w5]

def s227 : List T := [w4,w0,w1,w2,w3,w5]

def w91 : T := 24833574736597363735140499456

def s228 : List T := [w91,w11,w0,w1,w2,w3]

def s229 : List T := [w6,w11,w1,w2,w3,w5]

def s230 : List T := [w15,w11,w0,w1,w2,w3]

def s231 : List T := [w7,w11,w0,w2,w3,w5]

def s232 : List T := [w8,w11,w0,w1,w2,w3]

def s233 : List T := [w9,w11,w0,w1,w3,w5]

def s234 : List T := [w10,w11,w0,w1,w2,w5]

def s235 : List T := [w14,w11,w0,w1,w2,w3]

def s236 : List T := [w11,w0,w1,w2,w3,w4,w5]

def s237 : List T := [w91,w0,w1,w2,w3,w4]

def s238 : List T := [w12,w11,w0,w1,w2,w3]

def w92 : T := 54391990476101677028479074304

def s239 : List T := [w92,w0,w1,w2,w3,w4,w5]

def s240 : List T := [w12,w92,w0,w1,w2,w3]

def s241 : List T := [w12,w0,w1,w2,w3,w4]

def w93 : T := 2591125364796651011575807

def s242 : List T := [w93,w0,w1,w2,w3,w4]

def s243 : List T := [w43,w0,w1,w2,w3,w4]

def w94 : T := 31147410679154616266838767743

def s244 : List T := [w94,w0,w2,w3,w4]

def s245 : List T := [w41,w43,w1,w2,w3]

def s246 : List T := [w6,w12,w1,w2,w3,w4]

def s247 : List T := [w41,w12,w0,w1,w2,w3]

def s248 : List T := [w7,w12,w0,w2,w3,w4]

def s249 : List T := [w9,w12,w0,w1,w3,w4]

def s250 : List T := [w69,w12,w0,w1,w2,w3]

def s251 : List T := [w10,w12,w0,w1,w2,w4]

def s252 : List T := [w82,w12,w0,w1,w2,w3]

def s253 : List T := [w11,w12,w0,w1,w2,w3]

def s254 : List T := [w12,w0,w1,w2,w3,w4,w5]

def s255 : List T := [w92,w12,w0,w1,w2,w3]

def s256 : List T := [w14,w0,w1,w2,w3,w4]

def s257 : List T := [w5,w0,w1,w2,w3,w4]

def w95 : T := 31150004359958386016719470591

def s258 : List T := [w95,w0,w1,w2,w3,w4]

def w96 : T := 54394587777666973858403450879

def s259 : List T := [w96,w0,w1,w2,w3,w4]

def w97 : T := 2588468336436519526069875

def s260 : List T := [w97,w0,w1,w2,w3,w4]

def s261 : List T := [w6,w14,w1,w2,w3,w4]

def s262 : List T := [w7,w14,w0,w2,w3,w4]

def s263 : List T := [w9,w14,w0,w1,w3,w4]

def s264 : List T := [w10,w14,w0,w1,w2,w4]

def s265 : List T := [w11,w14,w0,w1,w2,w3]

def s266 : List T := [w14,w0,w1,w2,w3,w4,w5]

def w98 : T := 0

def s267 : List T := [w98,w0,w1,w2,w3,w4,w5]

def w99 : T := 79228162514264337593543950335

def s268 : List T := [w99,w0,w1,w2,w3,w4,w5]

def s269 : List T := [w6,w98,w1,w2,w3,w4,w5]

def s270 : List T := [w15,w98,w0,w1,w2,w3,w4]

def s271 : List T := [w16,w98,w0,w2,w3,w4]

def s272 : List T := [w17,w98,w0,w1,w2,w3]

def s273 : List T := [w7,w98,w0,w2,w3,w4,w5]

def s274 : List T := [w8,w98,w0,w1,w2,w3,w4]

def s275 : List T := [w9,w98,w0,w1,w3,w4,w5]

def s276 : List T := [w10,w98,w0,w1,w2,w4,w5]

def s277 : List T := [w11,w98,w0,w1,w2,w3,w5]

def s278 : List T := [w12,w98,w0,w1,w2,w3,w4]

def s279 : List T := [w14,w98,w0,w1,w2,w3,w4]

def s280 : List T := [w99,w0,w1,w2,w3,w4,w5]

def s281 : List T := [w98,w0,w1,w2,w3,w4,w5]

def s282 : List T := [w6,w99,w1,w2,w3,w4,w5]

def s283 : List T := [w15,w99,w0,w1,w2,w3,w4]

def s284 : List T := [w16,w99,w0,w2,w3,w4]

def s285 : List T := [w17,w99,w0,w1,w2,w3]

def s286 : List T := [w7,w99,w0,w2,w3,w4,w5]

def s287 : List T := [w8,w99,w0,w1,w2,w3,w4]

def s288 : List T := [w9,w99,w0,w1,w3,w4,w5]

def s289 : List T := [w10,w99,w0,w1,w2,w4,w5]

def s290 : List T := [w11,w99,w0,w1,w2,w3,w5]

def s291 : List T := [w12,w99,w0,w1,w2,w3,w4]

def s292 : List T := [w14,w99,w0,w1,w2,w3,w4]

def s293 : List T := [w98,w99,w0,w1,w2,w3,w4,w5]

lemma d2 : check 5 s2 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d3 : check 5 s3 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d4 : check 5 s4 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d5 : check 5 s5 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d6 : check 5 s6 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d7 : check 5 s7 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d8 : check 5 s8 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d9 : check 5 s9 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d10 : check 5 s10 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d1 : check 6 s1 = false :=
  close (r := 5) (ks := [s2,s2,s2,s3,s3,s3,s4,s5,s5,s5,s6,s6,s6,s7,s7,s7,s8,s9,s10,s10,s10]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d2,d3,d4,d5,d6,d7,d8,d9,d10,Bool.or_self])

lemma d13 : check 4 s13 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d14 : check 4 s14 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d12 : check 5 s12 = false :=
  close (r := 4) (ks := [s13,s14]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d13,d14,Bool.or_self])

lemma d15 : check 5 s15 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d11 : check 6 s11 = false :=
  close (r := 5) (ks := [s12,s15]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d12,d15,Bool.or_self])

lemma d17 : check 5 s17 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d18 : check 5 s18 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d19 : check 5 s19 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d20 : check 5 s20 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d21 : check 5 s21 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d16 : check 6 s16 = false :=
  close (r := 5) (ks := [s17,s18,s19,s20,s21]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d17,d18,d19,d20,d21,Bool.or_self])

lemma d24 : check 4 s24 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d23 : check 5 s23 = false :=
  close (r := 4) (ks := [s24]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d24,Bool.or_self])

lemma d25 : check 5 s25 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d27 : check 4 s27 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d26 : check 5 s26 = false :=
  close (r := 4) (ks := [s24,s27]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d24,d27,Bool.or_self])

lemma d22 : check 6 s22 = false :=
  close (r := 5) (ks := [s23,s25,s26]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d23,d25,d26,Bool.or_self])

lemma d29 : check 5 s29 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d28 : check 6 s28 = false :=
  close (r := 5) (ks := [s29]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d29,Bool.or_self])

lemma d32 : check 4 s32 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d31 : check 5 s31 = false :=
  close (r := 4) (ks := [s32]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d32,Bool.or_self])

lemma d33 : check 5 s33 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d34 : check 5 s34 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d30 : check 6 s30 = false :=
  close (r := 5) (ks := [s31,s33,s34]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d31,d33,d34,Bool.or_self])

lemma d36 : check 5 s36 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d35 : check 6 s35 = false :=
  close (r := 5) (ks := [s36]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d36,Bool.or_self])

lemma d38 : check 5 s38 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d40 : check 4 s40 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d39 : check 5 s39 = false :=
  close (r := 4) (ks := [s40]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d40,Bool.or_self])

lemma d41 : check 5 s41 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d37 : check 6 s37 = false :=
  close (r := 5) (ks := [s38,s39,s41]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d38,d39,d41,Bool.or_self])

lemma d43 : check 5 s43 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d44 : check 5 s44 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d45 : check 5 s45 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d46 : check 5 s46 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d47 : check 5 s47 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d42 : check 6 s42 = false :=
  close (r := 5) (ks := [s43,s44,s45,s46,s47]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d43,d44,d45,d46,d47,Bool.or_self])

lemma d50 : check 4 s50 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d49 : check 5 s49 = false :=
  close (r := 4) (ks := [s50]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d50,Bool.or_self])

lemma d51 : check 5 s51 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d53 : check 4 s53 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d52 : check 5 s52 = false :=
  close (r := 4) (ks := [s50,s53]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d50,d53,Bool.or_self])

lemma d48 : check 6 s48 = false :=
  close (r := 5) (ks := [s49,s51,s52]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d49,d51,d52,Bool.or_self])

lemma d55 : check 5 s55 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d57 : check 4 s57 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d58 : check 4 s58 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d59 : check 4 s59 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d60 : check 4 s60 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d61 : check 4 s61 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d56 : check 5 s56 = false :=
  close (r := 4) (ks := [s57,s57,s57,s58,s58,s58,s59,s59,s59,s60,s60,s60,s61,s61,s61]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d57,d58,d59,d60,d61,Bool.or_self])

lemma d62 : check 5 s62 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d64 : check 4 s64 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d65 : check 4 s65 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d66 : check 4 s66 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d63 : check 5 s63 = false :=
  close (r := 4) (ks := [s64,s65,s66]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d64,d65,d66,Bool.or_self])

lemma d68 : check 4 s68 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d69 : check 4 s69 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d70 : check 4 s70 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d67 : check 5 s67 = false :=
  close (r := 4) (ks := [s68,s69,s70]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d68,d69,d70,Bool.or_self])

lemma d72 : check 4 s72 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d73 : check 4 s73 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d74 : check 4 s74 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d71 : check 5 s71 = false :=
  close (r := 4) (ks := [s72,s73,s74]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d72,d73,d74,Bool.or_self])

lemma d76 : check 4 s76 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d77 : check 4 s77 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d78 : check 4 s78 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d79 : check 4 s79 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d80 : check 4 s80 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d75 : check 5 s75 = false :=
  close (r := 4) (ks := [s76,s76,s76,s77,s77,s77,s78,s78,s78,s79,s79,s79,s80,s80,s80]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d76,d77,d78,d79,d80,Bool.or_self])

lemma d81 : check 5 s81 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d83 : check 4 s83 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d84 : check 4 s84 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d85 : check 4 s85 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d82 : check 5 s82 = false :=
  close (r := 4) (ks := [s83,s84,s85]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d83,d84,d85,Bool.or_self])

lemma d86 : check 5 s86 = false :=
  close (r := 4) (ks := [s13,s14]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d13,d14,Bool.or_self])

lemma d88 : check 4 s88 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d87 : check 5 s87 = false :=
  close (r := 4) (ks := [s88]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d88,Bool.or_self])

lemma d90 : check 4 s90 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d91 : check 4 s91 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d89 : check 5 s89 = false :=
  close (r := 4) (ks := [s90,s91]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d90,d91,Bool.or_self])

lemma d93 : check 4 s93 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d94 : check 4 s94 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d92 : check 5 s92 = false :=
  close (r := 4) (ks := [s93,s94]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d93,d94,Bool.or_self])

lemma d96 : check 4 s96 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d95 : check 5 s95 = false :=
  close (r := 4) (ks := [s96]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d96,Bool.or_self])

lemma d54 : check 6 s54 = false :=
  close (r := 5) (ks := [s55,s55,s55,s56,s62,s63,s67,s71,s75,s81,s82,s86,s86,s86,s87,s87,s87,s89,s89,s89,s92,s92,s92,s95,s95,s95]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d55,d56,d62,d63,d67,d71,d75,d81,d82,d86,d87,d89,d92,d95,Bool.or_self])

lemma d98 : check 5 s98 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d99 : check 5 s99 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d100 : check 5 s100 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d101 : check 5 s101 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d102 : check 5 s102 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d97 : check 6 s97 = false :=
  close (r := 5) (ks := [s98,s99,s100,s101,s102]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d98,d99,d100,d101,d102,Bool.or_self])

lemma d104 : check 5 s104 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d103 : check 6 s103 = false :=
  close (r := 5) (ks := [s104]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d104,Bool.or_self])

lemma d106 : check 5 s106 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d107 : check 5 s107 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d108 : check 5 s108 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d109 : check 5 s109 = false :=
  close (r := 4) (ks := [s88]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d88,Bool.or_self])

lemma d110 : check 5 s110 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d111 : check 5 s111 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d112 : check 5 s112 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d113 : check 5 s113 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d114 : check 5 s114 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d105 : check 6 s105 = false :=
  close (r := 5) (ks := [s106,s106,s106,s107,s108,s108,s108,s109,s110,s110,s110,s111,s111,s111,s112,s112,s112,s113,s114,s114,s114]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d106,d107,d108,d109,d110,d111,d112,d113,d114,Bool.or_self])

lemma d116 : check 5 s116 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d117 : check 5 s117 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d115 : check 6 s115 = false :=
  close (r := 5) (ks := [s116,s117]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d116,d117,Bool.or_self])

lemma d120 : check 4 s120 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d119 : check 5 s119 = false :=
  close (r := 4) (ks := [s120]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d120,Bool.or_self])

lemma d122 : check 4 s122 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d121 : check 5 s121 = false :=
  close (r := 4) (ks := [s122]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d122,Bool.or_self])

lemma d123 : check 5 s123 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d124 : check 5 s124 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d125 : check 5 s125 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d127 : check 4 s127 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d128 : check 4 s128 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d126 : check 5 s126 = false :=
  close (r := 4) (ks := [s127,s128]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d127,d128,Bool.or_self])

lemma d118 : check 6 s118 = false :=
  close (r := 5) (ks := [s119,s121,s123,s124,s125,s126]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d119,d121,d123,d124,d125,d126,Bool.or_self])

lemma d130 : check 5 s130 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d129 : check 6 s129 = false :=
  close (r := 5) (ks := [s130]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d130,Bool.or_self])

lemma d132 : check 5 s132 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d133 : check 5 s133 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d131 : check 6 s131 = false :=
  close (r := 5) (ks := [s132,s133]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d132,d133,Bool.or_self])

lemma d136 : check 4 s136 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d135 : check 5 s135 = false :=
  close (r := 4) (ks := [s136]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d136,Bool.or_self])

lemma d137 : check 5 s137 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d134 : check 6 s134 = false :=
  close (r := 5) (ks := [s135,s137]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d135,d137,Bool.or_self])

lemma d139 : check 5 s139 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d138 : check 6 s138 = false :=
  close (r := 5) (ks := [s139]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d139,Bool.or_self])

lemma d141 : check 5 s141 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d143 : check 4 s143 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d144 : check 4 s144 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d142 : check 5 s142 = false :=
  close (r := 4) (ks := [s24,s143,s144]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d24,d143,d144,Bool.or_self])

lemma d145 : check 5 s145 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d146 : check 5 s146 = false :=
  close (r := 4) (ks := [s24,s27]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d24,d27,Bool.or_self])

lemma d147 : check 5 s147 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d148 : check 5 s148 = false :=
  close (r := 4) (ks := [s127,s128]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d127,d128,Bool.or_self])

lemma d149 : check 5 s149 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d151 : check 4 s151 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d150 : check 5 s150 = false :=
  close (r := 4) (ks := [s151]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d151,Bool.or_self])

lemma d152 : check 5 s152 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d153 : check 5 s153 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d140 : check 6 s140 = false :=
  close (r := 5) (ks := [s141,s141,s141,s142,s145,s145,s145,s146,s147,s147,s147,s148,s149,s149,s149,s150,s152,s152,s152,s135,s153,s153,s153]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d135,d141,d142,d145,d146,d147,d148,d149,d150,d152,d153,Bool.or_self])

lemma d155 : check 5 s155 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d154 : check 6 s154 = false :=
  close (r := 5) (ks := [s155]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d155,Bool.or_self])

lemma d157 : check 5 s157 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d158 : check 5 s158 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d159 : check 5 s159 = false :=
  close (r := 4) (ks := [s90,s91]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d90,d91,Bool.or_self])

lemma d160 : check 5 s160 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d161 : check 5 s161 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d162 : check 5 s162 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d163 : check 5 s163 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d164 : check 5 s164 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d165 : check 5 s165 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d156 : check 6 s156 = false :=
  close (r := 5) (ks := [s157,s157,s157,s158,s158,s158,s159,s160,s160,s160,s161,s162,s162,s162,s163,s163,s163,s164,s165,s165,s165]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d157,d158,d159,d160,d161,d162,d163,d164,d165,Bool.or_self])

lemma d166 : check 6 s166 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d168 : check 5 s168 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d169 : check 5 s169 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d167 : check 6 s167 = false :=
  close (r := 5) (ks := [s168,s169]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d168,d169,Bool.or_self])

lemma d171 : check 5 s171 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d173 : check 4 s173 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d172 : check 5 s172 = false :=
  close (r := 4) (ks := [s173]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d173,Bool.or_self])

lemma d175 : check 4 s175 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d174 : check 5 s174 = false :=
  close (r := 4) (ks := [s175]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d175,Bool.or_self])

lemma d170 : check 6 s170 = false :=
  close (r := 5) (ks := [s171,s172,s174]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d171,d172,d174,Bool.or_self])

lemma d177 : check 5 s177 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d178 : check 5 s178 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d176 : check 6 s176 = false :=
  close (r := 5) (ks := [s177,s178]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d177,d178,Bool.or_self])

lemma d180 : check 5 s180 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d179 : check 6 s179 = false :=
  close (r := 5) (ks := [s180]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d180,Bool.or_self])

lemma d182 : check 5 s182 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d183 : check 5 s183 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d181 : check 6 s181 = false :=
  close (r := 5) (ks := [s182,s183]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d182,d183,Bool.or_self])

lemma d186 : check 4 s186 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d185 : check 5 s185 = false :=
  close (r := 4) (ks := [s186]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d186,Bool.or_self])

lemma d187 : check 5 s187 = false :=
  close (r := 4) (ks := [s151]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d151,Bool.or_self])

lemma d188 : check 5 s188 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d184 : check 6 s184 = false :=
  close (r := 5) (ks := [s185,s187,s188]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d185,d187,d188,Bool.or_self])

lemma d190 : check 5 s190 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d191 : check 5 s191 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d192 : check 5 s192 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d193 : check 5 s193 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d194 : check 5 s194 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d189 : check 6 s189 = false :=
  close (r := 5) (ks := [s190,s191,s192,s193,s194]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d190,d191,d192,d193,d194,Bool.or_self])

lemma d196 : check 5 s196 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d195 : check 6 s195 = false :=
  close (r := 5) (ks := [s196]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d196,Bool.or_self])

lemma d198 : check 5 s198 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d199 : check 5 s199 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d200 : check 5 s200 = false :=
  close (r := 4) (ks := [s93,s94]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d93,d94,Bool.or_self])

lemma d201 : check 5 s201 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d202 : check 5 s202 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d203 : check 5 s203 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d204 : check 5 s204 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d205 : check 5 s205 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d206 : check 5 s206 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d197 : check 6 s197 = false :=
  close (r := 5) (ks := [s198,s198,s198,s199,s199,s199,s200,s201,s201,s201,s202,s203,s203,s203,s204,s204,s204,s205,s206,s206,s206]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d198,d199,d200,d201,d202,d203,d204,d205,d206,Bool.or_self])

lemma d207 : check 6 s207 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d210 : check 4 s210 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d209 : check 5 s209 = false :=
  close (r := 4) (ks := [s210]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d210,Bool.or_self])

lemma d211 : check 5 s211 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d213 : check 4 s213 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d212 : check 5 s212 = false :=
  close (r := 4) (ks := [s213]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d213,Bool.or_self])

lemma d214 : check 5 s214 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d215 : check 5 s215 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d217 : check 4 s217 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d218 : check 4 s218 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d216 : check 5 s216 = false :=
  close (r := 4) (ks := [s217,s218]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d217,d218,Bool.or_self])

lemma d208 : check 6 s208 = false :=
  close (r := 5) (ks := [s209,s211,s212,s214,s215,s216]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d209,d211,d212,d214,d215,d216,Bool.or_self])

lemma d220 : check 5 s220 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d219 : check 6 s219 = false :=
  close (r := 5) (ks := [s220]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d220,Bool.or_self])

lemma d222 : check 5 s222 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d223 : check 5 s223 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d221 : check 6 s221 = false :=
  close (r := 5) (ks := [s222,s223]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d222,d223,Bool.or_self])

lemma d225 : check 5 s225 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d224 : check 6 s224 = false :=
  close (r := 5) (ks := [s225]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d225,Bool.or_self])

lemma d227 : check 5 s227 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d228 : check 5 s228 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d229 : check 5 s229 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d230 : check 5 s230 = false :=
  close (r := 4) (ks := [s96]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d96,Bool.or_self])

lemma d231 : check 5 s231 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d232 : check 5 s232 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d233 : check 5 s233 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d234 : check 5 s234 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d235 : check 5 s235 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d226 : check 6 s226 = false :=
  close (r := 5) (ks := [s227,s227,s227,s228,s229,s229,s229,s230,s231,s231,s231,s232,s233,s233,s233,s234,s234,s234,s235,s235,s235]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d227,d228,d229,d230,d231,d232,d233,d234,d235,Bool.or_self])

lemma d237 : check 5 s237 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d238 : check 5 s238 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d236 : check 6 s236 = false :=
  close (r := 5) (ks := [s237,s238]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d237,d238,Bool.or_self])

lemma d240 : check 5 s240 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d239 : check 6 s239 = false :=
  close (r := 5) (ks := [s240]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d240,Bool.or_self])

lemma d242 : check 5 s242 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d244 : check 4 s244 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d245 : check 4 s245 = false :=
  close (r := 3) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d243 : check 5 s243 = false :=
  close (r := 4) (ks := [s244,s50,s245]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d50,d244,d245,Bool.or_self])

lemma d246 : check 5 s246 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d247 : check 5 s247 = false :=
  close (r := 4) (ks := [s50,s53]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d50,d53,Bool.or_self])

lemma d248 : check 5 s248 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d249 : check 5 s249 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d250 : check 5 s250 = false :=
  close (r := 4) (ks := [s175]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d175,Bool.or_self])

lemma d251 : check 5 s251 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d252 : check 5 s252 = false :=
  close (r := 4) (ks := [s217,s218]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d217,d218,Bool.or_self])

lemma d253 : check 5 s253 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d241 : check 6 s241 = false :=
  close (r := 5) (ks := [s242,s242,s242,s243,s246,s246,s246,s247,s135,s248,s248,s248,s249,s249,s249,s250,s251,s251,s251,s252,s253,s253,s253]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d135,d242,d243,d246,d247,d248,d249,d250,d251,d252,d253,Bool.or_self])

lemma d255 : check 5 s255 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d254 : check 6 s254 = false :=
  close (r := 5) (ks := [s255]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d255,Bool.or_self])

lemma d257 : check 5 s257 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d258 : check 5 s258 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d259 : check 5 s259 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d260 : check 5 s260 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d261 : check 5 s261 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d262 : check 5 s262 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d263 : check 5 s263 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d264 : check 5 s264 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d265 : check 5 s265 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d256 : check 6 s256 = false :=
  close (r := 5) (ks := [s257,s257,s257,s258,s259,s260,s261,s261,s261,s262,s262,s262,s263,s263,s263,s264,s264,s264,s265,s265,s265]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d257,d258,d259,d260,d261,d262,d263,d264,d265,Bool.or_self])

lemma d266 : check 6 s266 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d0 : check 7 s0 = false :=
  close (r := 6) (ks := [s1,s1,s1,s11,s16,s22,s28,s30,s35,s37,s42,s48,s54,s97,s103,s105,s105,s105,s115,s118,s129,s131,s134,s138,s140,s154,s156,s156,s156,s166,s167,s170,s176,s179,s181,s184,s189,s195,s197,s197,s197,s207,s208,s219,s221,s224,s226,s226,s226,s236,s239,s241,s254,s256,s256,s256,s266]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d1,d11,d16,d22,d28,d30,d35,d37,d42,d48,d54,d97,d103,d105,d115,d118,d129,d131,d134,d138,d140,d154,d156,d166,d167,d170,d176,d179,d181,d184,d189,d195,d197,d207,d208,d219,d221,d224,d226,d236,d239,d241,d254,d256,d266,Bool.or_self])

lemma d268 : check 6 s268 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d269 : check 6 s269 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d271 : check 5 s271 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d272 : check 5 s272 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d270 : check 6 s270 = false :=
  close (r := 5) (ks := [s271,s272]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d271,d272,Bool.or_self])

lemma d273 : check 6 s273 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d274 : check 6 s274 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d275 : check 6 s275 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d276 : check 6 s276 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d277 : check 6 s277 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d278 : check 6 s278 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d279 : check 6 s279 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d267 : check 7 s267 = false :=
  close (r := 6) (ks := [s268,s268,s268,s269,s269,s269,s270,s273,s273,s273,s274,s275,s275,s275,s276,s276,s276,s277,s277,s277,s278,s279,s279,s279]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d268,d269,d270,d273,d274,d275,d276,d277,d278,d279,Bool.or_self])

lemma d281 : check 6 s281 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d282 : check 6 s282 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d284 : check 5 s284 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d285 : check 5 s285 = false :=
  close (r := 4) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d283 : check 6 s283 = false :=
  close (r := 5) (ks := [s284,s285]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d284,d285,Bool.or_self])

lemma d286 : check 6 s286 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d287 : check 6 s287 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d288 : check 6 s288 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d289 : check 6 s289 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d290 : check 6 s290 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d291 : check 6 s291 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d292 : check 6 s292 = false :=
  close (r := 5) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma d280 : check 7 s280 = false :=
  close (r := 6) (ks := [s281,s281,s281,s282,s282,s282,s283,s286,s286,s286,s287,s288,s288,s288,s289,s289,s289,s290,s290,s290,s291,s292,s292,s292]) (by decide) (by decide +kernel) (by simp only [List.any_cons,List.any_nil,d281,d282,d283,d286,d287,d288,d289,d290,d291,d292,Bool.or_self])

lemma d293 : check 7 s293 = false :=
  close (r := 6) (ks := []) (by decide) (by decide +kernel) (rfl)

lemma noPlan {l : List T} (hl : l ∈ pool.sublists) (hv : live 7 l = true) : check 7 l = false := by
  have hm := List.mem_filter.mpr ⟨hl,hv⟩
  have hs : pool.sublists.filter (live 7) = [s0,s267,s280,s293] := by decide +kernel
  rw [hs] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact d0
  · exact d267
  · exact d280
  · exact d293

end P527

theorem PEqualNP.Outside.L_meta_527 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5)) s → 8 ≤ s := by
  intro s ⟨C,hg,hs,he⟩
  by_contra! hsmall
  have hoff : ∀ i : Fin 96, (P527.run C.gates (P527.inputs.map (P527.bit i))).getD C.output false =
      P527.bit i P527.target := by
    let x (i : Fin 96) (j : Fin 6) := P527.bit i (P527.inputs.getD j.val 0)
    have hx : ∀ i : Fin 96, List.ofFn (x i) = P527.inputs.map (P527.bit i) := by decide
    have hy : ∀ i : Fin 96, ((x i 0 && x i 1) || (x i 1 && x i 2) || (x i 2 && x i 3) ||
        (x i 3 && x i 4) || (x i 0 && x i 4) || (x i 0 && x i 5)) = P527.bit i P527.target := by decide
    intro i
    rw [← hx]
    exact (he (x i)).trans (hy i)
  obtain ⟨n,hn,S,hS,hp⟩ := P527.extractPlan (gs := C.gates) (o := C.output) hg P527.inputs hoff
  let l := P527.pool.filter (· ∈ S)
  have hl : List.Sublist l P527.pool := List.filter_sublist
  have hnod : P527.pool.Nodup := by decide
  have heq : l.toFinset = S := by
    ext a
    have : a ∈ S → a ∈ P527.pool := fun ha => by simpa [P527.pool,P527.avail] using hS ha
    simpa [l] using this
  have hn7 : n ≤ 7 := by change C.gates.length ≤ s at hs; omega
  have hb := P527.checked hp 7 hn7 l (hnod.sublist hl) heq
  rw [P527.noPlan (List.mem_sublists.mpr hl) (P527.livePlan hp (by omega) (hnod.sublist hl) heq)] at hb
  contradiction
