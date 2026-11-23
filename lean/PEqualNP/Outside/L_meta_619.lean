import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Fold
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.Wheel619
abbrev W := BitVec 128
def op (b : Bool) (a c : W) := if b then a ||| c else a &&& c
def sep (w : W) : BitVec 64 := (w >>> 64).truncate 64 &&& ~~~(w.truncate 64)
def covers (S : Finset W) (t : W) : Prop :=
  ∀ i : Fin 64, (sep t).getLsbD i → ∃ w ∈ S, (sep w).getLsbD i = true

inductive Live (t : W) : Finset W → Nat → Prop
| done : Live t {t} 0
| step {A a b k} (o : Bool) (da : a ≠ op o a b) (db : b ≠ op o a b) (u : op o a b ∈ A) (h : Live t A k) :
    Live t (insert a (insert b (A.erase (op o a b)))) (k+1)

theorem Live.small {t S k} (h : Live t S k) : S.card ≤ k+1 := by
  induction h with
  | done => simp
  | @step A a b k o da db u _ ih =>
    have h1 := Finset.card_erase_add_one u
    exact (Finset.card_insert_le ..).trans (by have := Finset.card_insert_le b (A.erase (op o a b)); omega)

theorem sep_op (o : Bool) (a b : W) (i : Fin 64) (h : (sep (op o a b)).getLsbD i) :
    (sep a).getLsbD i ∨ (sep b).getLsbD i := by
  cases o <;> simp [op,sep,BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_setWidth,i.isLt] at * <;> tauto

theorem Live.cover {t S k} (h : Live t S k) : covers S t := by
  induction h with
  | done => intro i hi; exact ⟨_, Finset.mem_singleton_self _, hi⟩
  | @step A a b k o da db u _ ih =>
    intro i hi
    obtain ⟨w,hw,hit⟩ := ih i hi
    by_cases e : w = op o a b
    · subst w
      rcases sep_op o a b i hit with ha | hb
      · exact ⟨a, by simp, ha⟩
      · exact ⟨b, by simp, hb⟩
    · exact ⟨w,by simp [hw,e],hit⟩
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
def mask (S : Finset W) := S.fold (fun a b : BitVec 64 => a ||| b) 0 sep
theorem mask_iff (S : Finset W) (i : Fin 64) :
    (mask S).getLsbD i = true ↔ ∃ w ∈ S, (sep w).getLsbD i = true := by
  induction S using Finset.induction_on with
  | empty => simp [mask]
  | insert a S ha ih => simpa [mask,Finset.fold_insert ha] using
      (or_congr (Iff.rfl (a := (sep a).getLsbD i = true)) ih)

theorem mask_ok {S t} (h : covers S t) : sep t &&& mask S = sep t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have q := h ⟨i,hi⟩
  have p := (mask_iff S ⟨i,hi⟩).2
  simp only [BitVec.getLsbD_and]
  cases e : (sep t).getLsbD i
  · simp
  · simpa using p (q e)

def next (S : Finset W) (a b : W) (o ka kb : Bool) : Finset W :=
  let R := if ka then S else S.erase a
  insert (op o a b) (if kb then R else R.erase b)

def tick (t : W) (n : Nat) (S : Finset W) (go : Finset W → Bool) : Bool :=
  if S.card > n+1 || sep t &&& mask S != sep t then false else
  if t ∈ S then true else
  decide (∃ a ∈ S, ∃ b ∈ S, ∃ o ka kb : Bool,
    op o a b ∉ S ∧ go (next S a b o ka kb) = true)

def search (t : W) (fuel : Nat) : Finset W → Bool :=
  Nat.rec (fun S => decide (t ∈ S)) (fun f go S => tick t (f+1) S go) fuel
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
theorem restore {A : Finset W} (a b : W) (o : Bool) (h : op o a b ∈ A) :
    next (insert a (insert b (A.erase (op o a b)))) a b o
      (decide (a ∈ A)) (decide (b ∈ A)) = A := by
  ext x
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;>
    simp [next,ha,hb] <;> grind

set_option maxRecDepth 4096 in
theorem search_yes {S t k} (h : Live t S k) (fuel : Nat) (le : k ≤ fuel) :
    search t fuel S = true := by
  induction h generalizing fuel with
  | done =>
    cases fuel with
    | zero => exact decide_eq_true (Finset.mem_singleton_self _)
    | succ f =>
      change tick t (f+1) {t} _ = true
      have c := mask_ok (Live.done (t := t)).cover
      simp [tick,c]
  | @step A a b k o da db u h ih =>
    cases fuel with
    | zero => omega
    | succ f =>
      have lv := Live.step o da db u h
      have small := lv.small
      have bound : ¬ (insert a (insert b (A.erase (op o a b)))).card > f+1+1 := by omega
      have cover := mask_ok lv.cover
      change tick t (f+1) _ _ = true
      unfold tick
      simp only [bound,decide_false,Bool.false_or,cover,show (sep t != sep t) = false by simp,
        Bool.false_eq_true,if_false]
      split
      · rfl
      · apply decide_eq_true
        refine ⟨a, by simp, b, by simp, o, decide (a ∈ A), decide (b ∈ A), by simp [Ne.symm da, Ne.symm db], ?_⟩
        rw [restore a b o u]
        exact ih f (by omega)
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
@[simp] theorem and_ones (x : W) : x &&& (340282366920938463463374607431768211455#128) = x := BitVec.and_allOnes
@[simp] theorem ones_and (x : W) : (340282366920938463463374607431768211455#128) &&& x = x := BitVec.allOnes_and
@[simp] theorem or_ones (x : W) : x ||| (340282366920938463463374607431768211455#128) = -1 := BitVec.or_allOnes
@[simp] theorem ones_or (x : W) : (340282366920938463463374607431768211455#128) ||| x = -1 := BitVec.allOnes_or
theorem ones_bit (i : Fin 128) : (340282366920938463463374607431768211455#128).getLsbD i = true := by
  change (BitVec.allOnes 128).getLsbD i = true
  rw [BitVec.getLsbD_allOnes]; exact decide_eq_true i.isLt

open PEqualNP.CircuitLowerBounds
def gate (g : Gate) (w : List W) : W := match g.op with
  | .and => (g.inputs.map fun j => w.getD j 0).foldr (· &&& ·) (-1)
  | .or => (g.inputs.map fun j => w.getD j 0).foldr (· ||| ·) 0
  | _ => 0

def good (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem good_of {C : Circuit} (h : PEqualNP.MetaComplexity.Monotone2 C) :
    ∀ g ∈ C.gates, good g := by
  simpa [PEqualNP.MetaComplexity.Monotone2,good] using h

def bits (i : Nat) (w : List W) := w.map (fun v => v.getLsbD i)
theorem bit_read (i j : Nat) (w : List W) :
    (w.getD j 0).getLsbD i = (bits i w).getD j false := by
  simp only [bits,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> simp

theorem gate_bits (g : Gate) (hg : good g) (w : List W) (i : Fin 128) :
    (gate g w).getLsbD i = g.op.eval (g.inputs.map fun j => (bits i w).getD j false) := by
  rcases g with ⟨o,l⟩
  have ho := hg.1
  clear hg
  change o = _ ∨ o = _ at ho
  rcases ho with rfl | rfl <;> induction l with
  | nil => first | exact ones_bit i | simp [gate,GateOp.eval]
  | cons a l ih =>
    first
    | exact congrArg₂ Bool.and (bit_read i a w) ih |>.trans' (BitVec.getLsbD_and ..)
    | exact congrArg₂ Bool.or (bit_read i a w) ih |>.trans' (BitVec.getLsbD_or ..)
    | simp only [gate,List.map_cons,List.foldr_cons,BitVec.getLsbD_and,BitVec.getLsbD_or,
        GateOp.eval,List.all_cons,List.any_cons,id_eq] at *
      rw [bit_read,ih]

def run (gs : List Gate) (w : List W) := gs.foldl (fun ws g => ws ++ [gate g ws]) w

theorem run_bits (gs : List Gate) (hg : ∀ g ∈ gs, good g) (w : List W) (i : Fin 128) :
    bits i (run gs w) = gs.foldl
      (fun ws (g : Gate) => ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)]) (bits i w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change bits i (run gs (w ++ [gate g w])) = _
    rw [ih (by aesop)]
    simp only [bits,List.map_append,List.map_cons,List.map_nil,List.foldl_cons,gate_bits g (hg g (by simp))]

def known (P : Finset W) (v : W) : Prop := v = 0 ∨ v = -1 ∨ v ∈ P

theorem known_read {P : Finset W} {w : List W} (hw : ∀ v ∈ w, known P v) (j : Nat) :
    known P (w.getD j 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases e : w[j]? with
  | none => exact Or.inl rfl
  | some a => exact hw a (List.mem_of_getElem? e)

theorem known_op (P : Finset W) (o : Bool) (a b : W) (ha : known P a) (hb : known P b) :
    known P (op o a b) ∨ (a ∈ P ∧ b ∈ P) := by
  rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb <;>
    cases o <;> simp only [op,Bool.false_eq_true,if_false,if_true,known,and_ones,ones_and,or_ones,ones_or, BitVec.and_zero,BitVec.zero_and,BitVec.or_zero,BitVec.zero_or] <;> first | tauto | simp_all [known,and_ones,ones_and,or_ones,ones_or]

theorem gate_fact {P : Finset W} {w : List W} (hw : ∀ v ∈ w, known P v)
    (g : Gate) (hg : good g) :
    known P (gate g w) ∨ ∃ a ∈ P, ∃ b ∈ P, ∃ o, gate g w = op o a b := by
  rcases g with ⟨o,l⟩
  obtain ⟨ho,hl⟩ := hg
  change l.length ≤ 2 at hl
  change o = _ ∨ o = _ at ho
  cases l with
  | nil => rcases ho with rfl | rfl <;> simp [gate,known]
  | cons i l =>
    cases l with
    | nil => rcases ho with rfl | rfl <;> simpa [gate, and_ones] using Or.inl (b := _) (known_read hw i)
    | cons j l =>
      have : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst l
      rcases ho with rfl | rfl
      · rcases known_op P false _ _ (known_read hw i) (known_read hw j) with hk | ⟨ha,hb⟩
        · exact Or.inl (by simpa [gate,op,and_ones] using hk)
        · exact Or.inr ⟨_,ha,_,hb,false, by simp [gate,op,and_ones]⟩
      · rcases known_op P true _ _ (known_read hw i) (known_read hw j) with hk | ⟨ha,hb⟩
        · exact Or.inl (by simpa [gate,op,and_ones] using hk)
        · exact Or.inr ⟨_,ha,_,hb,true, by simp [gate,op,and_ones]⟩

theorem extract (t : W) (nz : t ≠ 0) (no : t ≠ -1)
    (gs : List Gate) (hg : ∀ g ∈ gs, good g) (w : List W) (P : Finset W)
    (hw : ∀ v ∈ w, known P v) (j : Nat) (out : (run gs w).getD j 0 = t) :
    ∃ A ⊆ P, ∃ k ≤ gs.length, Live t A k := by
  induction gs generalizing w P with
  | nil =>
    have hh := known_read hw j
    change w.getD j 0 = t at out
    rw [out] at hh
    have ht : t ∈ P := hh.resolve_left nz |>.resolve_left no
    exact ⟨{t},by simpa using ht,0,by simp,Live.done⟩
  | cons g gs ih =>
    let v := gate g w
    have hgs : ∀ z ∈ gs, good z := by aesop
    change (run gs (w ++ [v])).getD j 0 = t at out
    rcases gate_fact hw g (hg g (by simp)) with old | ⟨a,ha,b,hb,o,eq⟩
    · obtain ⟨A,sub,k,le,live⟩ := ih hgs (w ++ [v]) P (by intro z hz; rcases List.mem_append.mp hz with h|h; exact hw z h; simpa [List.mem_singleton.mp h,v] using old) out
      exact ⟨A,sub,k,by simp; omega,live⟩
    · by_cases vp : v ∈ P
      · obtain ⟨A,sub,k,le,live⟩ := ih hgs (w ++ [v]) P (by
          intro z hz; rcases List.mem_append.mp hz with h|h; exact hw z h
          exact Or.inr (Or.inr (List.mem_singleton.mp h ▸ vp))) out
        exact ⟨A,sub,k,by simp; omega,live⟩
      obtain ⟨A,sub,k,le,live⟩ := ih hgs (w ++ [v]) (insert v P) (by
        intro z hz
        rcases List.mem_append.mp hz with h | h
        · rcases hw z h with h | h | h <;> simp [known, *]
        · have : z = v := by simpa using h
          simp [known,this]) out
      by_cases mem : v ∈ A
      · have ea : v = op o a b := eq
        have sub' : insert a (insert b (A.erase (op o a b))) ⊆ P := by
          intro z hz
          simp only [Finset.mem_insert,Finset.mem_erase] at hz
          rcases hz with rfl | rfl | ⟨hv,hz⟩
          · exact ha
          · exact hb
          · exact (Finset.mem_insert.mp (sub hz)).resolve_left (ea ▸ hv)
        exact ⟨_,sub',k+1,by simpa using le,Live.step o (by intro e; exact vp (by rwa [ea, ← e])) (by intro e; exact vp (by rwa [ea, ← e])) (ea ▸ mem) live⟩
      · exact ⟨A,fun z hz => (Finset.mem_insert.mp (sub hz)).resolve_left (by aesop),k,
          by simp; omega,live⟩
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
def stock : List W := [0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def target : W := 0xfffffffffffffff0000000000000000
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
def lmask (s : List W) : BitVec 64 := s.foldr (fun w m => sep w ||| m) 0
theorem lmask_eq (s : List W) : lmask s = mask s.toFinset := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply Bool.eq_iff_iff.mpr
    rw [mask_iff _ ⟨i,hi⟩]
    change ((sep a ||| lmask s).getLsbD i = true) ↔ _
    simp [ih,mask_iff _ ⟨i,hi⟩]

def residual (s : List W) (a b : W) (ka kb : Bool) :=
  s.filter (fun x => (ka || x != a) && (kb || x != b))
theorem next_eq (s : List W) (a b : W) (o ka kb : Bool) :
    (op o a b :: residual s a b ka kb).toFinset = next s.toFinset a b o ka kb := by
  ext z
  cases ka <;> cases kb <;> simp [residual,next] <;> tauto

def fastTick (t : W) (n : Nat) (s : List W) (go : List W → Bool) :=
  if s.length > n+1 || sep t &&& lmask s != sep t then false else
  if t ∈ s then true else
  s.any fun a => s.any fun b =>
    if a < b then [false,true].any fun o =>
      let c := op o a b
      if c ∈ s then false else [false,true].any fun ka => [false,true].any fun kb =>
        go (c :: residual s a b ka kb)
    else false

def fast (t : W) (fuel : Nat) : List W → Bool :=
  Nat.rec (fun s => decide (t ∈ s)) (fun f go s => fastTick t (f+1) s go) fuel

theorem next_swap (s : Finset W) (a b : W) (o ka kb : Bool) :
    next s b a o kb ka = next s a b o ka kb := by
  ext z
  cases o <;> cases ka <;> cases kb <;> simp [next,op,BitVec.and_comm,BitVec.or_comm] <;> tauto

end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
theorem fast_yes (fuel : Nat) (t : W) (s : List W) (nd : s.Nodup)
    (hit : search t fuel s.toFinset = true) : fast t fuel s = true := by
  induction fuel generalizing s with
  | zero => simpa [search,fast] using hit
  | succ f ih =>
    change tick t (f+1) s.toFinset _ = true at hit
    change fastTick t (f+1) s _ = true
    unfold tick at hit
    unfold fastTick
    rw [lmask_eq, ← List.toFinset_card_of_nodup nd]
    split at hit
    · contradiction
    rename_i guard
    rw [if_neg guard]
    simp only [List.mem_toFinset] at hit
    split at hit
    · rename_i e
      simp [e]
    · rename_i miss
      rw [if_neg miss]
      obtain ⟨a,ha,b,hb,o,ka,kb,fresh,h⟩ := of_decide_eq_true hit
      have use_pair (p q : W) (kp kq : Bool) (hp : p ∈ s) (hq : q ∈ s) (lt : p < q)
          (nc : op o p q ∉ s) (cont : search t f (next s.toFinset p q o kp kq) = true) :
          (s.any fun a => s.any fun b =>
            if a < b then [false,true].any fun o =>
              let c := op o a b
              if c ∈ s then false else [false,true].any fun ka => [false,true].any fun kb =>
                fast t f (c :: residual s a b ka kb)
            else false) = true := by
        apply List.any_eq_true.mpr; refine ⟨p,hp,?_⟩
        apply List.any_eq_true.mpr; refine ⟨q,hq,?_⟩
        rw [if_pos lt]
        apply List.any_eq_true.mpr; refine ⟨o,by cases o <;> simp,?_⟩
        dsimp only
        rw [if_neg nc]
        apply List.any_eq_true.mpr; refine ⟨kp,by cases kp <;> simp,?_⟩
        apply List.any_eq_true.mpr; refine ⟨kq,by cases kq <;> simp,?_⟩
        apply ih
        · exact List.nodup_cons.mpr ⟨fun h => nc (List.mem_filter.mp h).1, nd.filter _⟩
        · rwa [next_eq]
      have comm : op o b a = op o a b := by cases o <;> simp [op,BitVec.and_comm,BitVec.or_comm]
      rcases lt_trichotomy a.toNat b.toNat with lt | eq | lt
      · exact use_pair a b ka kb ha hb lt fresh h
      · have ab : a = b := BitVec.eq_of_toNat_eq eq
        subst b
        have : op o a a = a := by cases o <;> simp [op]
        exact False.elim (fresh (by rwa [this]))
      · apply use_pair b a kb ka hb ha lt (comm ▸ fresh)
        rwa [next_swap]
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
theorem essential (w : W) (hw : w ∈ stock) :
    ∃ i : Fin 64, (sep target).getLsbD i = true ∧ ∀ z ∈ stock, (sep z).getLsbD i = true → z = w := by
  simp only [stock,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨2, by decide, ?_⟩
    intro z hz
    simp only [stock,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨0, by decide, ?_⟩
    intro z hz
    simp only [stock,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨8, by decide, ?_⟩
    intro z hz
    simp only [stock,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨12, by decide, ?_⟩
    intro z hz
    simp only [stock,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨19, by decide, ?_⟩
    intro z hz
    simp only [stock,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨30, by decide, ?_⟩
    intro z hz
    simp only [stock,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem full {A k} (h : Live target A k) (sub : A ⊆ stock.toFinset) : A = stock.toFinset := by
  apply Finset.Subset.antisymm sub
  intro w hw
  obtain ⟨i,ht,only⟩ := essential w (List.mem_toFinset.mp hw)
  obtain ⟨v,hv,z⟩ := h.cover i ht
  exact only v (List.mem_toFinset.mp (sub hv)) z ▸ hv
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
def possible (t : W) (fuel : Nat) (s : List W) :=
  decide (s.length ≤ fuel+1) && (sep t &&& lmask s == sep t)

theorem fast_possible (t : W) (f : Nat) (s : List W) (h : fast t (f+1) s = true) :
    possible t (f+1) s = true := by
  change fastTick t (f+1) s _ = true at h
  unfold fastTick at h
  split at h
  · contradiction
  · rename_i e
    simpa [possible, Bool.or_eq_true, not_or, bne_iff_ne] using e

theorem tick_mono (t : W) (n : Nat) (s : List W) (f g : List W → Bool)
    (sub : ∀ r, f r = true → g r = true) (h : fastTick t n s f = true) : fastTick t n s g = true := by
  unfold fastTick at *
  split at h <;> simp_all only [ite_true,ite_false,Bool.false_eq_true]
  split at h
  · rename_i ht; rw [if_pos ht]
  · rename_i ht; rw [if_neg ht]
    obtain ⟨a,ha,y⟩ := List.any_eq_true.mp h
    obtain ⟨b,hb,y⟩ := List.any_eq_true.mp y
    refine List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
    try dsimp only at *
    split at y
    · rename_i lt
      rw [if_pos lt]
      obtain ⟨o,ho,y⟩ := List.any_eq_true.mp y
      refine List.any_eq_true.mpr ⟨o,ho,?_⟩
      try dsimp only at *
      split at y
      · contradiction
      · rename_i fresh
        rw [if_neg fresh]
        obtain ⟨ka,hka,y⟩ := List.any_eq_true.mp y
        obtain ⟨kb,hkb,y⟩ := List.any_eq_true.mp y
        exact List.any_eq_true.mpr ⟨ka,hka,List.any_eq_true.mpr ⟨kb,hkb,sub _ y⟩⟩
    · contradiction

def allow (t : W) (n : Nat) (rejects : List (List W)) (r : List W) :=
  possible t n r && !rejects.contains r

theorem certify (t : W) (n : Nat) (s : List W) (rejects : List (List W))
    (children : ∀ r ∈ rejects, fast t (n+1) r = false)
    (computed : fastTick t (n+2) s (allow t (n+1) rejects) = false) :
    fast t (n+2) s = false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  have mono := tick_mono t (n+2) s (fast t (n+1)) (allow t (n+1) rejects) (by
    intro r h
    have m : r ∉ rejects := fun mem => by have := children r mem; simp_all
    simp [allow,fast_possible t n r h,m]) hit
  simp_all
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
def s0_0 : List W := [0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_0 : List W := [0x41041041041041, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_1 : List W := [0x82082082082082, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_2 : List W := [0x104104104104104, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_3 : List W := [0x208208208208208, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_4 : List W := [0x410410410410410, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_5 : List W := [0x3f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_6 : List W := [0xfc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_7 : List W := [0x3f0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_8 : List W := [0xfc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_9 : List W := [0x3f0000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_10 : List W := [0xfc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_11 : List W := [0x3f0000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_12 : List W := [0x3ffff000fff03cf3cf3cf3cf3cf, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_13 : List W := [0xfc00000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_14 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_15 : List W := [0xfff00003ffff075d75d75d75d75d, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_16 : List W := [0x3f0000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_17 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_18 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_19 : List W := [0x3ffc0000ffffc005d75d75d75d75d7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_20 : List W := [0xfc00000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_21 : List W := [0xfc0000ffffc003f06db6db6db6db6db, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_22 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_23 : List W := [0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_24 : List W := [0xfff00003ffff000079e79e79e79e79e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_25 : List W := [0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_26 : List W := [0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_27 : List W := [0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_28 : List W := [0xfffffffff00003f08e38e38e38e38e3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s1_29 : List W := [0xffffffffffc00000e38e38e38e38e38, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_0 : List W := [0x0, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_1 : List W := [0xc30c30c30c30c3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_2 : List W := [0x186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_3 : List W := [0x30c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_4 : List W := [0x451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_5 : List W := [0x618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_6 : List W := [0x3f0000000000000000, 0x3f000ffffff03f01c71c71c71c71c7, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_7 : List W := [0x3f0000000000000000, 0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_8 : List W := [0x3f0041041041041041, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_9 : List W := [0x3f0082082082082082, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_10 : List W := [0x3f0104104104104104, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_11 : List W := [0x3f0208208208208208, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_12 : List W := [0xfc00000000000000000, 0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_13 : List W := [0xfc00000000000000000, 0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_14 : List W := [0xfc00041041041041041, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_15 : List W := [0xfc00104104104104104, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_16 : List W := [0xfc00208208208208208, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_17 : List W := [0xfc00410410410410410, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_18 : List W := [0xfff0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_19 : List W := [0x3f0000000000000000000, 0xfc0fff03ffff04d34d34d34d34d3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_20 : List W := [0x3f0000000000000000000, 0x3f000ffffff03f01c71c71c71c71c7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_21 : List W := [0x3f0000041041041041041, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_22 : List W := [0x3f0000082082082082082, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_23 : List W := [0x3f0000104104104104104, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_24 : List W := [0x3f0000410410410410410, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_25 : List W := [0x3ffc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_26 : List W := [0xfc00000000000000000000, 0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_27 : List W := [0xfc00000000000000000000, 0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_28 : List W := [0xfc00000082082082082082, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_29 : List W := [0xfc00000104104104104104, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_30 : List W := [0xfc00000208208208208208, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_31 : List W := [0xfc00000410410410410410, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_32 : List W := [0xfff0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_33 : List W := [0x3f0000000000000000000000, 0xfc0fff03ffff04d34d34d34d34d3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_34 : List W := [0x3f0000000000000000000000, 0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_35 : List W := [0x3f0000000041041041041041, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_36 : List W := [0x3f0000000082082082082082, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_37 : List W := [0x3f0000000208208208208208, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_38 : List W := [0x3f0000000410410410410410, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_39 : List W := [0x3f00003f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_40 : List W := [0x3ffc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_41 : List W := [0xfc00000000000000000000000, 0xfffffffff00003f08e38e38e38e38e3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_42 : List W := [0xfc00000000041041041041041, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_43 : List W := [0xfc00000000082082082082082, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_44 : List W := [0xfc000003f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_45 : List W := [0xfff0000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_46 : List W := [0xfff00003f01c71c71c71c71c7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_47 : List W := [0xfff00003f02cb2cb2cb2cb2cb, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_48 : List W := [0xfff00003f04d34d34d34d34d3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_49 : List W := [0xfff000fff00c30c30c30c30c3, 0xfc00000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_50 : List W := [0xfff000fff00c30c30c30c30c3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_51 : List W := [0xfff000fff00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_52 : List W := [0xfff03f03f00c30c30c30c30c3, 0x3f0000000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_53 : List W := [0xfff03f03f00c30c30c30c30c3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_54 : List W := [0xfff03f03f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_55 : List W := [0xffffc003f00c30c30c30c30c3, 0xfc00000000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_56 : List W := [0xffffc003f00c30c30c30c30c3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_57 : List W := [0xffffc003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_58 : List W := [0x3f0000000000000000000000000, 0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_59 : List W := [0x3f0000000000104104104104104, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_60 : List W := [0x3f0000000000208208208208208, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_61 : List W := [0x3f00000003f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_62 : List W := [0x3f000000fc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_63 : List W := [0x3f000000fff034d34d34d34d34d, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_64 : List W := [0x3f000000fff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_65 : List W := [0x3f000000fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_66 : List W := [0x3f00003ffff030c30c30c30c30c, 0x3f0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_67 : List W := [0x3f00003ffff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_68 : List W := [0x3f00003ffff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_69 : List W := [0x3f000fc0fff030c30c30c30c30c, 0xfc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_70 : List W := [0x3f000fc0fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_71 : List W := [0x3f000fc0fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_72 : List W := [0x3f03f000fff030c30c30c30c30c, 0x3f0000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_73 : List W := [0x3f03f000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_74 : List W := [0x3f03f000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_75 : List W := [0x3ffc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_76 : List W := [0x3ffc0000fff030c30c30c30c30c, 0xfc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_77 : List W := [0x3ffc0000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_78 : List W := [0x3ffc0000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_79 : List W := [0x3ffff00003f00c30c30c30c30c3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_80 : List W := [0x3ffff00003f00c30c30c30c30c3, 0x3f0000000000000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_81 : List W := [0x3ffff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_82 : List W := [0x3ffff000fff03cf3cf3cf3cf3cf, 0xfc0fff03ffff04d34d34d34d34d3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_83 : List W := [0x3ffff000fff03cf3cf3cf3cf3cf, 0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_84 : List W := [0x3ffff000fff03cf3cf3cf3cf3cf, 0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_85 : List W := [0x3ffff000fff03cf3cf3cf3cf3cf, 0xfffffffff00003f08e38e38e38e38e3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_86 : List W := [0xfc00000000000000000000000000, 0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_87 : List W := [0xfc00000000000041041041041041, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_88 : List W := [0xfc00000000000410410410410410, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_89 : List W := [0xfc0000000fc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_90 : List W := [0xfc000003f0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_91 : List W := [0xfc000003ffc004d34d34d34d34d3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_92 : List W := [0xfc000003ffc00555555555555555, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_93 : List W := [0xfc000003ffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_94 : List W := [0xfc000003ffff0451451451451451, 0x3f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_95 : List W := [0xfc000003ffff0451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_96 : List W := [0xfc000003ffff0451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_97 : List W := [0xfc0000ffffc00451451451451451, 0xfc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_98 : List W := [0xfc0000ffffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_99 : List W := [0xfc0000ffffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_100 : List W := [0xfc003f03ffc00451451451451451, 0x3f0000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_101 : List W := [0xfc003f03ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_102 : List W := [0xfc003f03ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_103 : List W := [0xfc0fc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_104 : List W := [0xfc0fc003ffc00451451451451451, 0xfc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_105 : List W := [0xfc0fc003ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_106 : List W := [0xfc0fc003ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_107 : List W := [0xfc0fff00003f00c30c30c30c30c3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_108 : List W := [0xfc0fff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_109 : List W := [0xfc0fff00003f00c30c30c30c30c3, 0xfc00000000000000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_110 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0x3f0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_111 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0x3f0000000000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_112 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0x3ffff000fff03cf3cf3cf3cf3cf, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_113 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0xfff00003ffff075d75d75d75d75d, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_114 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0x3f000ffffff03f01c71c71c71c71c7, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_115 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_116 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_117 : List W := [0xfc0fff03ffff04d34d34d34d34d3, 0xfffffffff00003f08e38e38e38e38e3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_118 : List W := [0xfff0000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_119 : List W := [0xfff000000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_120 : List W := [0xfff000000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_121 : List W := [0xfff000000fff030c30c30c30c30c, 0xfc00000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_122 : List W := [0xfff00003ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_123 : List W := [0xfff00003ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_124 : List W := [0xfff00003ffc00451451451451451, 0x3f0000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_125 : List W := [0xfff00003ffff075d75d75d75d75d, 0xfc0fff03ffff04d34d34d34d34d3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_126 : List W := [0xfff00003ffff075d75d75d75d75d, 0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_127 : List W := [0xfff00003ffff075d75d75d75d75d, 0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_128 : List W := [0xfff00003ffff075d75d75d75d75d, 0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_129 : List W := [0xffffff03ffff07df7df7df7df7df, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_130 : List W := [0x3f0000000000000000000000000000, 0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_131 : List W := [0x3f0000000000000082082082082082, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_132 : List W := [0x3f0000000000000104104104104104, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_133 : List W := [0x3f00000003f0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_134 : List W := [0x3f000000fc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_135 : List W := [0x3f000000fff00001c71c71c71c71c7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_136 : List W := [0x3f000000fff000038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_137 : List W := [0x3f000000fff0000596596596596596, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_138 : List W := [0x3f000000fff03f0186186186186186, 0x3f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_139 : List W := [0x3f000000fff03f0186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_140 : List W := [0x3f000000fff03f0186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_141 : List W := [0x3f000000ffffc00186186186186186, 0xfc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_142 : List W := [0x3f000000ffffc00186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_143 : List W := [0x3f000000ffffc00186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_144 : List W := [0x3f00003ffff0000186186186186186, 0x3f0000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_145 : List W := [0x3f00003ffff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_146 : List W := [0x3f00003ffff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_147 : List W := [0x3f000fc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_148 : List W := [0x3f000fc0fff0000186186186186186, 0xfc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_149 : List W := [0x3f000fc0fff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_150 : List W := [0x3f000fc0fff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_151 : List W := [0x3f000fff00003f00c30c30c30c30c3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_152 : List W := [0x3f000fff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_153 : List W := [0x3f000fff00003f00c30c30c30c30c3, 0x3f0000000000000000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_154 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0x3f0000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_155 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0x3f0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_156 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0xfc0fff03ffff04d34d34d34d34d3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_157 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_158 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0xfc0000ffffc003f06db6db6db6db6db, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_159 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0xfff00003ffff000079e79e79e79e79e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_160 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_161 : List W := [0x3f000ffffff03f01c71c71c71c71c7, 0xfffffffff00003f08e38e38e38e38e3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_162 : List W := [0x3f03f0000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_163 : List W := [0x3f03f000000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_164 : List W := [0x3f03f000000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_165 : List W := [0x3f03f000000fff030c30c30c30c30c, 0x3f0000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_166 : List W := [0x3f03f000fff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_167 : List W := [0x3f03f000fff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_168 : List W := [0x3f03f000fff0000186186186186186, 0x3f0000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_169 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0x3f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_170 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0xfc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_171 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0xfff00003ffff075d75d75d75d75d, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_172 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0x3f000ffffff03f01c71c71c71c71c7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_173 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0x3ffc0000ffffc005d75d75d75d75d7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_174 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_175 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_176 : List W := [0x3f03f000ffffff038e38e38e38e38e, 0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_177 : List W := [0x3f03ffffffffff03cf3cf3cf3cf3cf, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_178 : List W := [0x3ffc00000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_179 : List W := [0x3ffc000003ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_180 : List W := [0x3ffc000003ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_181 : List W := [0x3ffc000003ffc00451451451451451, 0x3f0000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_182 : List W := [0x3ffc0000fff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_183 : List W := [0x3ffc0000fff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_184 : List W := [0x3ffc0000fff0000186186186186186, 0xfc00000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_185 : List W := [0x3ffc0000ffffc005d75d75d75d75d7, 0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_186 : List W := [0x3ffc0000ffffc005d75d75d75d75d7, 0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_187 : List W := [0x3ffc0000ffffc005d75d75d75d75d7, 0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_188 : List W := [0x3ffc0000ffffc005d75d75d75d75d7, 0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_189 : List W := [0x3ffc0fffffffff05d75d75d75d75d7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_190 : List W := [0x3ffff000ffffff07df7df7df7df7df, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_191 : List W := [0xfc00000000000000000000000000000, 0xffffffffffc00000e38e38e38e38e38, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_192 : List W := [0xfc00000000000000208208208208208, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_193 : List W := [0xfc00000000000000410410410410410, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_194 : List W := [0xfc0000000fc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_195 : List W := [0xfc000003f0000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_196 : List W := [0xfc000003ffc00000659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_197 : List W := [0xfc000003ffc0000069a69a69a69a69a, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_198 : List W := [0xfc000003ffc0000071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_199 : List W := [0xfc000003ffc003f0618618618618618, 0x3f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_200 : List W := [0xfc000003ffc003f0618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_201 : List W := [0xfc000003ffc003f0618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_202 : List W := [0xfc000003ffc0fc00618618618618618, 0xfc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_203 : List W := [0xfc000003ffc0fc00618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_204 : List W := [0xfc000003ffc0fc00618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_205 : List W := [0xfc000003ffff0000618618618618618, 0x3f0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_206 : List W := [0xfc000003ffff0000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_207 : List W := [0xfc000003ffff0000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_208 : List W := [0xfc0000fc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_209 : List W := [0xfc0000fff00003f00c30c30c30c30c3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_210 : List W := [0xfc0000fff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_211 : List W := [0xfc0000fff00003f00c30c30c30c30c3, 0xfc00000000000000000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_212 : List W := [0xfc0000ffffc00000618618618618618, 0xfc00000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_213 : List W := [0xfc0000ffffc00000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_214 : List W := [0xfc0000ffffc00000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_215 : List W := [0xfc0000ffffc003f06db6db6db6db6db, 0x3f000ffffff03f01c71c71c71c71c7, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_216 : List W := [0xfc0000ffffc003f06db6db6db6db6db, 0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_217 : List W := [0xfc0000ffffc003f06db6db6db6db6db, 0xfffffffff00003f08e38e38e38e38e3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_218 : List W := [0xfc0000ffffc003f06db6db6db6db6db, 0xffffffffffc00000e38e38e38e38e38, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_219 : List W := [0xfc003f0000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_220 : List W := [0xfc003f000000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_221 : List W := [0xfc003f000000fff030c30c30c30c30c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_222 : List W := [0xfc003f000000fff030c30c30c30c30c, 0xfc00000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_223 : List W := [0xfc003f03ffc00000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_224 : List W := [0xfc003f03ffc00000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_225 : List W := [0xfc003f03ffc00000618618618618618, 0x3f0000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_226 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0xfc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_227 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0xfc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_228 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0x3ffff000fff03cf3cf3cf3cf3cf, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_229 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_230 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0xfc0000ffffc003f06db6db6db6db6db, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_231 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_232 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_233 : List W := [0xfc003f03ffc0fff071c71c71c71c71c, 0xffffffffffc00000e38e38e38e38e38, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_234 : List W := [0xfc003fffffc0fff07df7df7df7df7df, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_235 : List W := [0xfc0fc00000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_236 : List W := [0xfc0fc000003ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_237 : List W := [0xfc0fc000003ffc00451451451451451, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_238 : List W := [0xfc0fc000003ffc00451451451451451, 0xfc00000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_239 : List W := [0xfc0fc003ffc00000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_240 : List W := [0xfc0fc003ffc00000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_241 : List W := [0xfc0fc003ffc00000618618618618618, 0xfc00000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_242 : List W := [0xfc0fc003fffffc00659659659659659, 0xfc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_243 : List W := [0xfc0fc003fffffc00659659659659659, 0x3f0000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_244 : List W := [0xfc0fc003fffffc00659659659659659, 0xfc0fff03ffff04d34d34d34d34d3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_245 : List W := [0xfc0fc003fffffc00659659659659659, 0x3ffc0000ffffc005d75d75d75d75d7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_246 : List W := [0xfc0fc003fffffc00659659659659659, 0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_247 : List W := [0xfc0fc003fffffc00659659659659659, 0xfff00003ffff000079e79e79e79e79e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_248 : List W := [0xfc0fc003fffffc00659659659659659, 0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_249 : List W := [0xfc0fc003fffffc00659659659659659, 0xffffffffffc00000e38e38e38e38e38, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_250 : List W := [0xfc0fc0fffffffff06db6db6db6db6db, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_251 : List W := [0xfc0fff03fffffff075d75d75d75d75d, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_252 : List W := [0xfff0000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_253 : List W := [0xfff000000fff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_254 : List W := [0xfff000000fff0000186186186186186, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_255 : List W := [0xfff000000fff0000186186186186186, 0xfc00000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_256 : List W := [0xfff00003ffc00000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_257 : List W := [0xfff00003ffc00000618618618618618, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_258 : List W := [0xfff00003ffc00000618618618618618, 0x3f0000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_259 : List W := [0xfff00003ffff000079e79e79e79e79e, 0x3f000ffffff03f01c71c71c71c71c7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_260 : List W := [0xfff00003ffff000079e79e79e79e79e, 0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_261 : List W := [0xfff00003ffff000079e79e79e79e79e, 0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_262 : List W := [0xfff00003ffff000079e79e79e79e79e, 0xffffffffffc00000e38e38e38e38e38, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_263 : List W := [0xfff000ffffff03f07df7df7df7df7df, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_264 : List W := [0xfff03f03fffffff079e79e79e79e79e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_265 : List W := [0xffffc003fffffc007df7df7df7df7df, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_266 : List W := [0xfffffffc00000000861861861861861, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_267 : List W := [0xfffffffc000000008a28a28a28a28a2, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_268 : List W := [0xfffffffc00000000924924924924924, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_269 : List W := [0xfffffffc00000000a28a28a28a28a28, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_270 : List W := [0xfffffffc00000000c30c30c30c30c30, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_271 : List W := [0xfffffffc000003f0820820820820820, 0x3f0000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_272 : List W := [0xfffffffc000003f0820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_273 : List W := [0xfffffffc000003f0820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_274 : List W := [0xfffffffc0000fc00820820820820820, 0xfc00000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_275 : List W := [0xfffffffc0000fc00820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_276 : List W := [0xfffffffc0000fc00820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_277 : List W := [0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0x3f0000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_278 : List W := [0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0x3ffff000fff03cf3cf3cf3cf3cf, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_279 : List W := [0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003ffff075d75d75d75d75d, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_280 : List W := [0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_281 : List W := [0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_282 : List W := [0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_283 : List W := [0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfffffffff00003f08e38e38e38e38e3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_284 : List W := [0xfffffffc003f0000820820820820820, 0x3f0000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_285 : List W := [0xfffffffc003f0000820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_286 : List W := [0xfffffffc003f0000820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_287 : List W := [0xfffffffc003ffc00c71c71c71c71c71, 0xfc00000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_288 : List W := [0xfffffffc003ffc00c71c71c71c71c71, 0xfc0fff03ffff04d34d34d34d34d3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_289 : List W := [0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003ffff075d75d75d75d75d, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_290 : List W := [0xfffffffc003ffc00c71c71c71c71c71, 0x3ffc0000ffffc005d75d75d75d75d7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_291 : List W := [0xfffffffc003ffc00c71c71c71c71c71, 0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_292 : List W := [0xfffffffc003ffc00c71c71c71c71c71, 0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_293 : List W := [0xfffffffc003ffc00c71c71c71c71c71, 0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_294 : List W := [0xfffffffc003ffff0f7df7df7df7df7d, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_295 : List W := [0xfffffffc0fc00000820820820820820, 0xfc00000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_296 : List W := [0xfffffffc0fc00000820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_297 : List W := [0xfffffffc0fc00000820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_298 : List W := [0xfffffffc0fff00009a69a69a69a69a6, 0x3f0000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_299 : List W := [0xfffffffc0fff00009a69a69a69a69a6, 0x3f000ffffff03f01c71c71c71c71c7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_300 : List W := [0xfffffffc0fff00009a69a69a69a69a6, 0x3f03f000ffffff038e38e38e38e38e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_301 : List W := [0xfffffffc0fff00009a69a69a69a69a6, 0x3ffc0000ffffc005d75d75d75d75d7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_302 : List W := [0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003ffff000079e79e79e79e79e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_303 : List W := [0xfffffffc0fff00009a69a69a69a69a6, 0xfffffffc003ffc00c71c71c71c71c71, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_304 : List W := [0xfffffffc0fff00009a69a69a69a69a6, 0xffffffffffc00000e38e38e38e38e38, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_305 : List W := [0xfffffffc0ffffc00df7df7df7df7df7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_306 : List W := [0xfffffffc0ffffff0baebaebaebaebae, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_307 : List W := [0xfffffffff0000000820820820820820, 0x3f0000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_308 : List W := [0xfffffffff0000000820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_309 : List W := [0xfffffffff0000000820820820820820, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_310 : List W := [0xfffffffff00003f08e38e38e38e38e3, 0xfc00000000000000000000000, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_311 : List W := [0xfffffffff00003f08e38e38e38e38e3, 0x3ffff000fff03cf3cf3cf3cf3cf, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_312 : List W := [0xfffffffff00003f08e38e38e38e38e3, 0xfc0fff03ffff04d34d34d34d34d3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_313 : List W := [0xfffffffff00003f08e38e38e38e38e3, 0x3f000ffffff03f01c71c71c71c71c7, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_314 : List W := [0xfffffffff00003f08e38e38e38e38e3, 0xfc0000ffffc003f06db6db6db6db6db, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_315 : List W := [0xfffffffff00003f08e38e38e38e38e3, 0xfffffffc0000fff0b2cb2cb2cb2cb2c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_316 : List W := [0xfffffffff00003f08e38e38e38e38e3, 0xffffffffffc00000e38e38e38e38e38, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_317 : List W := [0xfffffffff000fff0befbefbefbefbef, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_318 : List W := [0xfffffffff03ffff0cf3cf3cf3cf3cf3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_319 : List W := [0xffffffffffc00000e38e38e38e38e38, 0xfc00000000000000000000000000000, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_320 : List W := [0xffffffffffc00000e38e38e38e38e38, 0xfc0000ffffc003f06db6db6db6db6db, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_321 : List W := [0xffffffffffc00000e38e38e38e38e38, 0xfc003f03ffc0fff071c71c71c71c71c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_322 : List W := [0xffffffffffc00000e38e38e38e38e38, 0xfc0fc003fffffc00659659659659659, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_323 : List W := [0xffffffffffc00000e38e38e38e38e38, 0xfff00003ffff000079e79e79e79e79e, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfffffffc00000000820820820820820]
def s2_324 : List W := [0xffffffffffc00000e38e38e38e38e38, 0xfffffffc0fff00009a69a69a69a69a6, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_325 : List W := [0xffffffffffc00000e38e38e38e38e38, 0xfffffffff00003f08e38e38e38e38e3, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618]
def s2_326 : List W := [0xffffffffffc003f0efbefbefbefbefb, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_327 : List W := [0xffffffffffc0fff0f3cf3cf3cf3cf3c, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_328 : List W := [0xffffffffffff0000fbefbefbefbefbe, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_329 : List W := [0xffffffffffff03f09e79e79e79e79e7, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
def s2_330 : List W := [0xfffffffffffffc00e79e79e79e79e79, 0xfff00003f00c30c30c30c30c3, 0x3f000000fff030c30c30c30c30c, 0xfc000003ffc00451451451451451, 0x3f000000fff0000186186186186186, 0xfc000003ffc00000618618618618618, 0xfffffffc00000000820820820820820]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_0 : fast target 6 s2_0 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_1 : fast target 6 s2_1 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_2 : fast target 6 s2_2 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_3 : fast target 6 s2_3 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_4 : fast target 6 s2_4 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_5 : fast target 6 s2_5 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_6 : fast target 6 s2_6 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_7 : fast target 6 s2_7 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_8 : fast target 6 s2_8 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_9 : fast target 6 s2_9 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_10 : fast target 6 s2_10 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_11 : fast target 6 s2_11 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_12 : fast target 6 s2_12 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_13 : fast target 6 s2_13 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_14 : fast target 6 s2_14 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_15 : fast target 6 s2_15 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_16 : fast target 6 s2_16 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_17 : fast target 6 s2_17 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_18 : fast target 6 s2_18 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_19 : fast target 6 s2_19 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_20 : fast target 6 s2_20 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_21 : fast target 6 s2_21 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_22 : fast target 6 s2_22 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_23 : fast target 6 s2_23 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_24 : fast target 6 s2_24 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_25 : fast target 6 s2_25 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_26 : fast target 6 s2_26 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_27 : fast target 6 s2_27 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_28 : fast target 6 s2_28 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_29 : fast target 6 s2_29 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_30 : fast target 6 s2_30 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_31 : fast target 6 s2_31 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_32 : fast target 6 s2_32 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_33 : fast target 6 s2_33 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_34 : fast target 6 s2_34 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_35 : fast target 6 s2_35 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_36 : fast target 6 s2_36 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_37 : fast target 6 s2_37 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_38 : fast target 6 s2_38 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_39 : fast target 6 s2_39 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_40 : fast target 6 s2_40 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_41 : fast target 6 s2_41 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_42 : fast target 6 s2_42 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_43 : fast target 6 s2_43 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_44 : fast target 6 s2_44 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_45 : fast target 6 s2_45 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_46 : fast target 6 s2_46 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_47 : fast target 6 s2_47 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_48 : fast target 6 s2_48 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_49 : fast target 6 s2_49 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_50 : fast target 6 s2_50 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_51 : fast target 6 s2_51 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_52 : fast target 6 s2_52 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_53 : fast target 6 s2_53 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_54 : fast target 6 s2_54 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_55 : fast target 6 s2_55 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_56 : fast target 6 s2_56 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_57 : fast target 6 s2_57 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_58 : fast target 6 s2_58 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_59 : fast target 6 s2_59 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_60 : fast target 6 s2_60 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_61 : fast target 6 s2_61 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_62 : fast target 6 s2_62 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_63 : fast target 6 s2_63 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_64 : fast target 6 s2_64 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_65 : fast target 6 s2_65 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_66 : fast target 6 s2_66 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_67 : fast target 6 s2_67 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_68 : fast target 6 s2_68 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_69 : fast target 6 s2_69 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_70 : fast target 6 s2_70 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_71 : fast target 6 s2_71 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_72 : fast target 6 s2_72 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_73 : fast target 6 s2_73 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_74 : fast target 6 s2_74 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_75 : fast target 6 s2_75 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_76 : fast target 6 s2_76 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_77 : fast target 6 s2_77 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_78 : fast target 6 s2_78 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_79 : fast target 6 s2_79 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_80 : fast target 6 s2_80 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_81 : fast target 6 s2_81 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_82 : fast target 6 s2_82 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_83 : fast target 6 s2_83 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_84 : fast target 6 s2_84 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_85 : fast target 6 s2_85 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_86 : fast target 6 s2_86 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_87 : fast target 6 s2_87 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_88 : fast target 6 s2_88 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_89 : fast target 6 s2_89 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_90 : fast target 6 s2_90 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_91 : fast target 6 s2_91 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_92 : fast target 6 s2_92 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_93 : fast target 6 s2_93 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_94 : fast target 6 s2_94 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_95 : fast target 6 s2_95 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_96 : fast target 6 s2_96 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_97 : fast target 6 s2_97 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_98 : fast target 6 s2_98 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_99 : fast target 6 s2_99 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_100 : fast target 6 s2_100 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_101 : fast target 6 s2_101 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_102 : fast target 6 s2_102 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_103 : fast target 6 s2_103 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_104 : fast target 6 s2_104 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_105 : fast target 6 s2_105 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_106 : fast target 6 s2_106 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_107 : fast target 6 s2_107 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_108 : fast target 6 s2_108 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_109 : fast target 6 s2_109 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_110 : fast target 6 s2_110 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_111 : fast target 6 s2_111 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_112 : fast target 6 s2_112 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_113 : fast target 6 s2_113 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_114 : fast target 6 s2_114 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_115 : fast target 6 s2_115 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_116 : fast target 6 s2_116 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_117 : fast target 6 s2_117 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_118 : fast target 6 s2_118 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_119 : fast target 6 s2_119 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_120 : fast target 6 s2_120 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_121 : fast target 6 s2_121 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_122 : fast target 6 s2_122 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_123 : fast target 6 s2_123 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_124 : fast target 6 s2_124 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_125 : fast target 6 s2_125 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_126 : fast target 6 s2_126 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_127 : fast target 6 s2_127 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_128 : fast target 6 s2_128 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_129 : fast target 6 s2_129 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_130 : fast target 6 s2_130 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_131 : fast target 6 s2_131 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_132 : fast target 6 s2_132 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_133 : fast target 6 s2_133 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_134 : fast target 6 s2_134 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_135 : fast target 6 s2_135 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_136 : fast target 6 s2_136 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_137 : fast target 6 s2_137 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_138 : fast target 6 s2_138 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_139 : fast target 6 s2_139 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_140 : fast target 6 s2_140 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_141 : fast target 6 s2_141 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_142 : fast target 6 s2_142 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_143 : fast target 6 s2_143 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_144 : fast target 6 s2_144 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_145 : fast target 6 s2_145 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_146 : fast target 6 s2_146 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_147 : fast target 6 s2_147 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_148 : fast target 6 s2_148 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_149 : fast target 6 s2_149 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_150 : fast target 6 s2_150 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_151 : fast target 6 s2_151 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_152 : fast target 6 s2_152 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_153 : fast target 6 s2_153 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_154 : fast target 6 s2_154 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_155 : fast target 6 s2_155 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_156 : fast target 6 s2_156 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_157 : fast target 6 s2_157 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_158 : fast target 6 s2_158 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_159 : fast target 6 s2_159 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_160 : fast target 6 s2_160 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_161 : fast target 6 s2_161 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_162 : fast target 6 s2_162 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_163 : fast target 6 s2_163 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_164 : fast target 6 s2_164 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_165 : fast target 6 s2_165 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_166 : fast target 6 s2_166 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_167 : fast target 6 s2_167 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_168 : fast target 6 s2_168 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_169 : fast target 6 s2_169 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_170 : fast target 6 s2_170 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_171 : fast target 6 s2_171 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_172 : fast target 6 s2_172 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_173 : fast target 6 s2_173 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_174 : fast target 6 s2_174 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_175 : fast target 6 s2_175 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_176 : fast target 6 s2_176 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_177 : fast target 6 s2_177 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_178 : fast target 6 s2_178 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_179 : fast target 6 s2_179 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_180 : fast target 6 s2_180 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_181 : fast target 6 s2_181 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_182 : fast target 6 s2_182 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_183 : fast target 6 s2_183 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_184 : fast target 6 s2_184 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_185 : fast target 6 s2_185 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_186 : fast target 6 s2_186 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_187 : fast target 6 s2_187 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_188 : fast target 6 s2_188 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_189 : fast target 6 s2_189 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_190 : fast target 6 s2_190 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_191 : fast target 6 s2_191 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_192 : fast target 6 s2_192 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_193 : fast target 6 s2_193 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_194 : fast target 6 s2_194 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_195 : fast target 6 s2_195 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_196 : fast target 6 s2_196 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_197 : fast target 6 s2_197 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_198 : fast target 6 s2_198 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_199 : fast target 6 s2_199 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_200 : fast target 6 s2_200 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_201 : fast target 6 s2_201 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_202 : fast target 6 s2_202 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_203 : fast target 6 s2_203 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_204 : fast target 6 s2_204 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_205 : fast target 6 s2_205 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_206 : fast target 6 s2_206 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_207 : fast target 6 s2_207 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_208 : fast target 6 s2_208 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_209 : fast target 6 s2_209 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_210 : fast target 6 s2_210 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_211 : fast target 6 s2_211 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_212 : fast target 6 s2_212 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_213 : fast target 6 s2_213 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_214 : fast target 6 s2_214 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_215 : fast target 6 s2_215 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_216 : fast target 6 s2_216 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_217 : fast target 6 s2_217 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_218 : fast target 6 s2_218 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_219 : fast target 6 s2_219 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_220 : fast target 6 s2_220 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_221 : fast target 6 s2_221 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_222 : fast target 6 s2_222 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_223 : fast target 6 s2_223 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_224 : fast target 6 s2_224 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_225 : fast target 6 s2_225 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_226 : fast target 6 s2_226 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_227 : fast target 6 s2_227 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_228 : fast target 6 s2_228 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_229 : fast target 6 s2_229 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_230 : fast target 6 s2_230 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_231 : fast target 6 s2_231 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_232 : fast target 6 s2_232 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_233 : fast target 6 s2_233 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_234 : fast target 6 s2_234 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_235 : fast target 6 s2_235 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_236 : fast target 6 s2_236 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_237 : fast target 6 s2_237 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_238 : fast target 6 s2_238 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_239 : fast target 6 s2_239 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_240 : fast target 6 s2_240 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_241 : fast target 6 s2_241 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_242 : fast target 6 s2_242 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_243 : fast target 6 s2_243 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_244 : fast target 6 s2_244 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_245 : fast target 6 s2_245 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_246 : fast target 6 s2_246 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_247 : fast target 6 s2_247 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_248 : fast target 6 s2_248 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_249 : fast target 6 s2_249 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_250 : fast target 6 s2_250 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_251 : fast target 6 s2_251 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_252 : fast target 6 s2_252 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_253 : fast target 6 s2_253 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_254 : fast target 6 s2_254 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_255 : fast target 6 s2_255 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_256 : fast target 6 s2_256 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_257 : fast target 6 s2_257 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_258 : fast target 6 s2_258 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_259 : fast target 6 s2_259 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_260 : fast target 6 s2_260 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_261 : fast target 6 s2_261 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_262 : fast target 6 s2_262 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_263 : fast target 6 s2_263 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_264 : fast target 6 s2_264 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_265 : fast target 6 s2_265 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_266 : fast target 6 s2_266 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_267 : fast target 6 s2_267 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_268 : fast target 6 s2_268 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_269 : fast target 6 s2_269 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_270 : fast target 6 s2_270 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_271 : fast target 6 s2_271 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_272 : fast target 6 s2_272 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_273 : fast target 6 s2_273 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_274 : fast target 6 s2_274 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_275 : fast target 6 s2_275 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_276 : fast target 6 s2_276 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_277 : fast target 6 s2_277 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_278 : fast target 6 s2_278 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_279 : fast target 6 s2_279 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_280 : fast target 6 s2_280 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_281 : fast target 6 s2_281 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_282 : fast target 6 s2_282 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_283 : fast target 6 s2_283 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_284 : fast target 6 s2_284 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_285 : fast target 6 s2_285 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_286 : fast target 6 s2_286 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_287 : fast target 6 s2_287 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_288 : fast target 6 s2_288 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_289 : fast target 6 s2_289 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_290 : fast target 6 s2_290 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_291 : fast target 6 s2_291 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_292 : fast target 6 s2_292 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_293 : fast target 6 s2_293 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_294 : fast target 6 s2_294 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_295 : fast target 6 s2_295 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_296 : fast target 6 s2_296 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_297 : fast target 6 s2_297 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_298 : fast target 6 s2_298 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_299 : fast target 6 s2_299 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_300 : fast target 6 s2_300 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_301 : fast target 6 s2_301 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_302 : fast target 6 s2_302 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_303 : fast target 6 s2_303 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_304 : fast target 6 s2_304 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_305 : fast target 6 s2_305 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_306 : fast target 6 s2_306 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_307 : fast target 6 s2_307 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_308 : fast target 6 s2_308 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_309 : fast target 6 s2_309 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_310 : fast target 6 s2_310 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_311 : fast target 6 s2_311 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_312 : fast target 6 s2_312 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_313 : fast target 6 s2_313 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_314 : fast target 6 s2_314 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_315 : fast target 6 s2_315 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_316 : fast target 6 s2_316 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_317 : fast target 6 s2_317 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_318 : fast target 6 s2_318 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_319 : fast target 6 s2_319 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_320 : fast target 6 s2_320 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_321 : fast target 6 s2_321 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_322 : fast target 6 s2_322 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_323 : fast target 6 s2_323 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_324 : fast target 6 s2_324 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_325 : fast target 6 s2_325 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_326 : fast target 6 s2_326 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_327 : fast target 6 s2_327 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_328 : fast target 6 s2_328 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_329 : fast target 6 s2_329 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject2_330 : fast target 6 s2_330 = false := by
  decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_0 : fast target 7 s1_0 = false := by
  apply certify target 5 s1_0 [s2_0, s2_63, s2_135, s2_196, s2_266]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_63
    · exact reject2_135
    · exact reject2_196
    · exact reject2_266
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_1 : fast target 7 s1_1 = false := by
  apply certify target 5 s1_1 [s2_0, s2_64, s2_91, s2_197, s2_267]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_64
    · exact reject2_91
    · exact reject2_197
    · exact reject2_267
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_2 : fast target 7 s1_2 = false := by
  apply certify target 5 s1_2 [s2_0, s2_46, s2_92, s2_198, s2_268]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_46
    · exact reject2_92
    · exact reject2_198
    · exact reject2_268
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_3 : fast target 7 s1_3 = false := by
  apply certify target 5 s1_3 [s2_0, s2_47, s2_93, s2_136, s2_269]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_47
    · exact reject2_93
    · exact reject2_136
    · exact reject2_269
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_4 : fast target 7 s1_4 = false := by
  apply certify target 5 s1_4 [s2_0, s2_48, s2_65, s2_137, s2_270]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_48
    · exact reject2_65
    · exact reject2_137
    · exact reject2_270
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_5 : fast target 7 s1_5 = false := by
  apply certify target 5 s1_5 [s2_0, s2_94, s2_95, s2_96, s2_138, s2_139, s2_140, s2_154, s2_169, s2_199, s2_200, s2_201, s2_271, s2_272, s2_273]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_94
    · exact reject2_95
    · exact reject2_96
    · exact reject2_138
    · exact reject2_139
    · exact reject2_140
    · exact reject2_154
    · exact reject2_169
    · exact reject2_199
    · exact reject2_200
    · exact reject2_201
    · exact reject2_271
    · exact reject2_272
    · exact reject2_273
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_6 : fast target 7 s1_6 = false := by
  apply certify target 5 s1_6 [s2_0, s2_49, s2_50, s2_51, s2_141, s2_142, s2_143, s2_202, s2_203, s2_204, s2_226, s2_242, s2_274, s2_275, s2_276]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_49
    · exact reject2_50
    · exact reject2_51
    · exact reject2_141
    · exact reject2_142
    · exact reject2_143
    · exact reject2_202
    · exact reject2_203
    · exact reject2_204
    · exact reject2_226
    · exact reject2_242
    · exact reject2_274
    · exact reject2_275
    · exact reject2_276
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_7 : fast target 7 s1_7 = false := by
  apply certify target 5 s1_7 [s2_0, s2_52, s2_53, s2_54, s2_66, s2_67, s2_68, s2_110, s2_155, s2_205, s2_206, s2_207, s2_284, s2_285, s2_286]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_52
    · exact reject2_53
    · exact reject2_54
    · exact reject2_66
    · exact reject2_67
    · exact reject2_68
    · exact reject2_110
    · exact reject2_155
    · exact reject2_205
    · exact reject2_206
    · exact reject2_207
    · exact reject2_284
    · exact reject2_285
    · exact reject2_286
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_8 : fast target 7 s1_8 = false := by
  apply certify target 5 s1_8 [s2_0, s2_55, s2_56, s2_57, s2_69, s2_70, s2_71, s2_97, s2_98, s2_99, s2_170, s2_227, s2_295, s2_296, s2_297]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_55
    · exact reject2_56
    · exact reject2_57
    · exact reject2_69
    · exact reject2_70
    · exact reject2_71
    · exact reject2_97
    · exact reject2_98
    · exact reject2_99
    · exact reject2_170
    · exact reject2_227
    · exact reject2_295
    · exact reject2_296
    · exact reject2_297
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_9 : fast target 7 s1_9 = false := by
  apply certify target 5 s1_9 [s2_0, s2_72, s2_73, s2_74, s2_100, s2_101, s2_102, s2_111, s2_144, s2_145, s2_146, s2_243, s2_307, s2_308, s2_309]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_72
    · exact reject2_73
    · exact reject2_74
    · exact reject2_100
    · exact reject2_101
    · exact reject2_102
    · exact reject2_111
    · exact reject2_144
    · exact reject2_145
    · exact reject2_146
    · exact reject2_243
    · exact reject2_307
    · exact reject2_308
    · exact reject2_309
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_10 : fast target 7 s1_10 = false := by
  apply certify target 5 s1_10 [s2_0, s2_76, s2_77, s2_78, s2_104, s2_105, s2_106, s2_148, s2_149, s2_150, s2_212, s2_213, s2_214, s2_310]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_76
    · exact reject2_77
    · exact reject2_78
    · exact reject2_104
    · exact reject2_105
    · exact reject2_106
    · exact reject2_148
    · exact reject2_149
    · exact reject2_150
    · exact reject2_212
    · exact reject2_213
    · exact reject2_214
    · exact reject2_310
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_11 : fast target 7 s1_11 = false := by
  apply certify target 5 s1_11 [s2_0, s2_79, s2_80, s2_81, s2_122, s2_123, s2_124, s2_166, s2_167, s2_168, s2_223, s2_224, s2_225, s2_277]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_79
    · exact reject2_80
    · exact reject2_81
    · exact reject2_122
    · exact reject2_123
    · exact reject2_124
    · exact reject2_166
    · exact reject2_167
    · exact reject2_168
    · exact reject2_223
    · exact reject2_224
    · exact reject2_225
    · exact reject2_277
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_12 : fast target 7 s1_12 = false := by
  apply certify target 5 s1_12 [s2_2, s2_14, s2_37, s2_75, s2_112, s2_129, s2_177, s2_228, s2_234, s2_278, s2_311, s2_317]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_2
    · exact reject2_14
    · exact reject2_37
    · exact reject2_75
    · exact reject2_112
    · exact reject2_129
    · exact reject2_177
    · exact reject2_228
    · exact reject2_234
    · exact reject2_278
    · exact reject2_311
    · exact reject2_317
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_13 : fast target 7 s1_13 = false := by
  apply certify target 5 s1_13 [s2_0, s2_107, s2_108, s2_109, s2_119, s2_120, s2_121, s2_182, s2_183, s2_184, s2_239, s2_240, s2_241, s2_287]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_107
    · exact reject2_108
    · exact reject2_109
    · exact reject2_119
    · exact reject2_120
    · exact reject2_121
    · exact reject2_182
    · exact reject2_183
    · exact reject2_184
    · exact reject2_239
    · exact reject2_240
    · exact reject2_241
    · exact reject2_287
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_14 : fast target 7 s1_14 = false := by
  apply certify target 5 s1_14 [s2_18, s2_19, s2_22, s2_33, s2_38, s2_82, s2_103, s2_125, s2_129, s2_156, s2_189, s2_244, s2_250, s2_288, s2_312, s2_318]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_18
    · exact reject2_19
    · exact reject2_22
    · exact reject2_33
    · exact reject2_38
    · exact reject2_82
    · exact reject2_103
    · exact reject2_125
    · exact reject2_129
    · exact reject2_156
    · exact reject2_189
    · exact reject2_244
    · exact reject2_250
    · exact reject2_288
    · exact reject2_312
    · exact reject2_318
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_15 : fast target 7 s1_15 = false := by
  apply certify target 5 s1_15 [s2_5, s2_8, s2_23, s2_113, s2_118, s2_129, s2_171, s2_190, s2_251, s2_279, s2_289, s2_294]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_5
    · exact reject2_8
    · exact reject2_23
    · exact reject2_113
    · exact reject2_118
    · exact reject2_129
    · exact reject2_171
    · exact reject2_190
    · exact reject2_251
    · exact reject2_279
    · exact reject2_289
    · exact reject2_294
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_16 : fast target 7 s1_16 = false := by
  apply certify target 5 s1_16 [s2_0, s2_151, s2_152, s2_153, s2_163, s2_164, s2_165, s2_179, s2_180, s2_181, s2_256, s2_257, s2_258, s2_298]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_151
    · exact reject2_152
    · exact reject2_153
    · exact reject2_163
    · exact reject2_164
    · exact reject2_165
    · exact reject2_179
    · exact reject2_180
    · exact reject2_181
    · exact reject2_256
    · exact reject2_257
    · exact reject2_258
    · exact reject2_298
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_17 : fast target 7 s1_17 = false := by
  apply certify target 5 s1_17 [s2_6, s2_10, s2_20, s2_21, s2_40, s2_114, s2_147, s2_172, s2_177, s2_189, s2_215, s2_259, s2_263, s2_299, s2_313, s2_329]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_6
    · exact reject2_10
    · exact reject2_20
    · exact reject2_21
    · exact reject2_40
    · exact reject2_114
    · exact reject2_147
    · exact reject2_172
    · exact reject2_177
    · exact reject2_189
    · exact reject2_215
    · exact reject2_259
    · exact reject2_263
    · exact reject2_299
    · exact reject2_313
    · exact reject2_329
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_18 : fast target 7 s1_18 = false := by
  apply certify target 5 s1_18 [s2_7, s2_9, s2_25, s2_26, s2_30, s2_126, s2_157, s2_162, s2_177, s2_185, s2_190, s2_229, s2_264, s2_280, s2_300, s2_306]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_7
    · exact reject2_9
    · exact reject2_25
    · exact reject2_26
    · exact reject2_30
    · exact reject2_126
    · exact reject2_157
    · exact reject2_162
    · exact reject2_177
    · exact reject2_185
    · exact reject2_190
    · exact reject2_229
    · exact reject2_264
    · exact reject2_280
    · exact reject2_300
    · exact reject2_306
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_19 : fast target 7 s1_19 = false := by
  apply certify target 5 s1_19 [s2_1, s2_15, s2_31, s2_173, s2_178, s2_189, s2_190, s2_245, s2_265, s2_290, s2_301, s2_305]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_1
    · exact reject2_15
    · exact reject2_31
    · exact reject2_173
    · exact reject2_178
    · exact reject2_189
    · exact reject2_190
    · exact reject2_245
    · exact reject2_265
    · exact reject2_290
    · exact reject2_301
    · exact reject2_305
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_20 : fast target 7 s1_20 = false := by
  apply certify target 5 s1_20 [s2_0, s2_209, s2_210, s2_211, s2_220, s2_221, s2_222, s2_236, s2_237, s2_238, s2_253, s2_254, s2_255, s2_319]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_0
    · exact reject2_209
    · exact reject2_210
    · exact reject2_211
    · exact reject2_220
    · exact reject2_221
    · exact reject2_222
    · exact reject2_236
    · exact reject2_237
    · exact reject2_238
    · exact reject2_253
    · exact reject2_254
    · exact reject2_255
    · exact reject2_319
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_21 : fast target 7 s1_21 = false := by
  apply certify target 5 s1_21 [s2_4, s2_11, s2_28, s2_158, s2_208, s2_230, s2_234, s2_250, s2_263, s2_314, s2_320, s2_326]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_4
    · exact reject2_11
    · exact reject2_28
    · exact reject2_158
    · exact reject2_208
    · exact reject2_230
    · exact reject2_234
    · exact reject2_250
    · exact reject2_263
    · exact reject2_314
    · exact reject2_320
    · exact reject2_326
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_22 : fast target 7 s1_22 = false := by
  apply certify target 5 s1_22 [s2_12, s2_17, s2_27, s2_29, s2_39, s2_83, s2_174, s2_216, s2_219, s2_234, s2_246, s2_251, s2_264, s2_281, s2_321, s2_327]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_12
    · exact reject2_17
    · exact reject2_27
    · exact reject2_29
    · exact reject2_39
    · exact reject2_83
    · exact reject2_174
    · exact reject2_216
    · exact reject2_219
    · exact reject2_234
    · exact reject2_246
    · exact reject2_251
    · exact reject2_264
    · exact reject2_281
    · exact reject2_321
    · exact reject2_327
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_23 : fast target 7 s1_23 = false := by
  apply certify target 5 s1_23 [s2_13, s2_16, s2_32, s2_34, s2_35, s2_115, s2_186, s2_231, s2_235, s2_250, s2_251, s2_260, s2_265, s2_291, s2_322, s2_330]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_13
    · exact reject2_16
    · exact reject2_32
    · exact reject2_34
    · exact reject2_35
    · exact reject2_115
    · exact reject2_186
    · exact reject2_231
    · exact reject2_235
    · exact reject2_250
    · exact reject2_251
    · exact reject2_260
    · exact reject2_265
    · exact reject2_291
    · exact reject2_322
    · exact reject2_330
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_24 : fast target 7 s1_24 = false := by
  apply certify target 5 s1_24 [s2_3, s2_24, s2_36, s2_159, s2_247, s2_252, s2_263, s2_264, s2_265, s2_302, s2_323, s2_328]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_3
    · exact reject2_24
    · exact reject2_36
    · exact reject2_159
    · exact reject2_247
    · exact reject2_252
    · exact reject2_263
    · exact reject2_264
    · exact reject2_265
    · exact reject2_302
    · exact reject2_323
    · exact reject2_328
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_25 : fast target 7 s1_25 = false := by
  apply certify target 5 s1_25 [s2_44, s2_58, s2_84, s2_89, s2_127, s2_132, s2_175, s2_192, s2_232, s2_292, s2_294, s2_306, s2_315, s2_317, s2_327]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_44
    · exact reject2_58
    · exact reject2_84
    · exact reject2_89
    · exact reject2_127
    · exact reject2_132
    · exact reject2_175
    · exact reject2_192
    · exact reject2_232
    · exact reject2_292
    · exact reject2_294
    · exact reject2_306
    · exact reject2_315
    · exact reject2_317
    · exact reject2_327
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_26 : fast target 7 s1_26 = false := by
  apply certify target 5 s1_26 [s2_42, s2_62, s2_86, s2_116, s2_128, s2_133, s2_187, s2_193, s2_248, s2_282, s2_294, s2_303, s2_305, s2_318, s2_330]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_42
    · exact reject2_62
    · exact reject2_86
    · exact reject2_116
    · exact reject2_128
    · exact reject2_133
    · exact reject2_187
    · exact reject2_193
    · exact reject2_248
    · exact reject2_282
    · exact reject2_294
    · exact reject2_303
    · exact reject2_305
    · exact reject2_318
    · exact reject2_330
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_27 : fast target 7 s1_27 = false := by
  apply certify target 5 s1_27 [s2_43, s2_59, s2_90, s2_130, s2_160, s2_176, s2_188, s2_194, s2_261, s2_293, s2_305, s2_306, s2_324, s2_328, s2_329]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_43
    · exact reject2_59
    · exact reject2_90
    · exact reject2_130
    · exact reject2_160
    · exact reject2_176
    · exact reject2_188
    · exact reject2_194
    · exact reject2_261
    · exact reject2_293
    · exact reject2_305
    · exact reject2_306
    · exact reject2_324
    · exact reject2_328
    · exact reject2_329
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_28 : fast target 7 s1_28 = false := by
  apply certify target 5 s1_28 [s2_41, s2_61, s2_85, s2_87, s2_117, s2_131, s2_161, s2_195, s2_217, s2_283, s2_317, s2_318, s2_325, s2_326, s2_329]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_41
    · exact reject2_61
    · exact reject2_85
    · exact reject2_87
    · exact reject2_117
    · exact reject2_131
    · exact reject2_161
    · exact reject2_195
    · exact reject2_217
    · exact reject2_283
    · exact reject2_317
    · exact reject2_318
    · exact reject2_325
    · exact reject2_326
    · exact reject2_329
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject1_29 : fast target 7 s1_29 = false := by
  apply certify target 5 s1_29 [s2_45, s2_60, s2_88, s2_134, s2_191, s2_218, s2_233, s2_249, s2_262, s2_304, s2_316, s2_326, s2_327, s2_328, s2_330]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject2_45
    · exact reject2_60
    · exact reject2_88
    · exact reject2_134
    · exact reject2_191
    · exact reject2_218
    · exact reject2_233
    · exact reject2_249
    · exact reject2_262
    · exact reject2_304
    · exact reject2_316
    · exact reject2_326
    · exact reject2_327
    · exact reject2_328
    · exact reject2_330
  · decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem reject0_0 : fast target 8 s0_0 = false := by
  apply certify target 6 s0_0 [s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6, s1_7, s1_8, s1_9, s1_10, s1_11, s1_12, s1_13, s1_14, s1_15, s1_16, s1_17, s1_18, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reject1_0
    · exact reject1_1
    · exact reject1_2
    · exact reject1_3
    · exact reject1_4
    · exact reject1_5
    · exact reject1_6
    · exact reject1_7
    · exact reject1_8
    · exact reject1_9
    · exact reject1_10
    · exact reject1_11
    · exact reject1_12
    · exact reject1_13
    · exact reject1_14
    · exact reject1_15
    · exact reject1_16
    · exact reject1_17
    · exact reject1_18
    · exact reject1_19
    · exact reject1_20
    · exact reject1_21
    · exact reject1_22
    · exact reject1_23
    · exact reject1_24
    · exact reject1_25
    · exact reject1_26
    · exact reject1_27
    · exact reject1_28
    · exact reject1_29
  · decide +kernel
theorem eight : fast target 8 stock = false := reject0_0
end PEqualNP.Outside.Wheel619

namespace PEqualNP.Outside.Wheel619
def input (i : Fin 128) (j : Fin 6) := (stock.getD j 0).getLsbD i
theorem agree (i : Fin 128) : target.getLsbD i = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ input i u = true ∧ input i v = true := by
  decide +revert
theorem input_eq (i : Fin 128) : List.ofFn (input i) = bits i stock := by
  rfl
end PEqualNP.Outside.Wheel619
namespace PEqualNP.Outside
open PEqualNP.Outside.Wheel619
set_option maxHeartbeats 2000000 in
theorem L_meta_619 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, mono, size, spec⟩
  have good := good_of mono
  have out : (run C.gates stock).getD C.output 0 = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let k : Fin 128 := ⟨i,hi⟩
    have h := (spec (input k)).trans (agree k).symm
    have ev : C.eval (List.ofFn (input k)) = ((run C.gates stock).getD C.output 0).getLsbD i := by
      rw [bit_read, input_eq, run_bits C.gates good stock k]
      rfl
    rw [ev] at h
    exact Bool.eq_iff_iff.mpr h
  obtain ⟨A,sub,k,le,lv⟩ := extract target (by decide) (by decide) C.gates good stock stock.toFinset
    (by intro v hv; exact Or.inr (Or.inr (List.mem_toFinset.mpr hv))) C.output out
  have hs := full lv sub
  rw [hs] at lv
  have yes := fast_yes 8 target stock (by decide) (search_yes lv 8 (le.trans size))
  exact Bool.noConfusion (eight.symm.trans yes)
end PEqualNP.Outside
