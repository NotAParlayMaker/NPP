import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Insert
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_652_aux
namespace L652
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Row := Fin 6 → Bool
abbrev Table := Row → Bool
def zero : Table := fun _ => false
def one : Table := fun _ => true
def inputTables : List Table := List.ofFn (fun i : Fin 6 => fun row => row i)
def tnot (a : Table) : Table := fun r => !a r
def tand (a b : Table) : Table := fun r => a r && b r
def tor (a b : Table) : Table := fun r => a r || b r
inductive Op where
  | neg (i : Nat) | meet (i j : Nat) | join (i j : Nat)
  deriving DecidableEq, Repr
def Op.valid (n : Nat) : Op → Prop
  | .neg i => i < n
  | .meet i j | .join i j => i < n ∧ j < n ∧ i ≠ j
def Op.value (w : List Table) : Op → Table
  | .neg i => tnot (w.getD i zero)
  | .meet i j => tand (w.getD i zero) (w.getD j zero)
  | .join i j => tor (w.getD i zero) (w.getD j zero)
def Available (w : List Table) (v : Table) : Prop := v = zero ∨ v = one ∨ v ∈ w
inductive Built : List Op → List Table → Prop
  | start : Built [] inputTables
  | snoc {p w} (old : Built p w) (g : Op) (valid : g.valid w.length)
      (fresh : ¬ Available w (g.value w)) :
      Built (p ++ [g]) (w ++ [g.value w])
def f0 : Table := fun x => (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)
def f1 : Table := fun x => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)
def f2 : Table := fun x => (x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4)
def Realizable (s : Nat) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ ∃ o0 o1 o2 : Nat, ∀ x : Row,
    (C.wires (List.ofFn x)).getD o0 false = f0 x ∧
    (C.wires (List.ofFn x)).getD o1 false = f1 x ∧
    (C.wires (List.ofFn x)).getD o2 false = f2 x
private def zz0n0 : Circuit := ⟨[
  ⟨.and,[0,3]⟩, ⟨.and,[1,4]⟩, ⟨.and,[2,5]⟩,
  ⟨.and,[0,4]⟩, ⟨.and,[1,5]⟩, ⟨.and,[2,3]⟩,
  ⟨.and,[0,5]⟩, ⟨.and,[1,3]⟩, ⟨.and,[2,4]⟩,
  ⟨.or,[6,7]⟩, ⟨.or,[15,8]⟩, ⟨.or,[9,10]⟩,
  ⟨.or,[17,11]⟩, ⟨.or,[12,13]⟩, ⟨.or,[19,14]⟩], 16⟩
set_option maxRecDepth 8000 in
theorem upper : Realizable 15 := by
  refine ⟨zz0n0, ?_, by decide, 16, 18, 20, ?_⟩
  · intro g hg
    simp [zz0n0] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst g <;> simp
  · intro x
    unfold f0 f1 f2
    rw [show List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] by rfl]
    generalize x 0 = a
    generalize x 1 = b
    generalize x 2 = c
    generalize x 3 = d
    generalize x 4 = e
    generalize x 5 = f
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide
abbrev Possible (w : List Table) (v : Table) : Prop :=
  Available w v ∨ ∃ g : Op, g.valid w.length ∧ g.value w = v
private theorem zz0n1 {a : Table} {w : List Table} (h : a ∈ w) :
    ∃ i, i < w.length ∧ w.getD i zero = a := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi, he]⟩
private theorem zz0n2 {orig w : List Table}
    (h : ∀ f ∈ orig, Available w f) (i : Nat) : Available w (orig.getD i zero) := by
  by_cases hi : i < orig.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem ..)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : orig.length ≤ i),
          Available]
theorem neg_possible {w : List Table} {a : Table} (ha : Available w a) :
    Possible w (tnot a) := by
  rcases ha with rfl | rfl | ha
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inl rfl)
  · obtain ⟨i,hi,he⟩ := zz0n1 ha
    exact Or.inr ⟨.neg i,hi,by simp only [Op.value,he]⟩
theorem binary_possible {w : List Table} {a b : Table}
    (ha : Available w a) (hb : Available w b) (u : Bool) :
    Possible w ((if u then tor else tand) a b) := by
  classical
  have andZero (x : Table) : tand x zero = zero := by funext r; simp [tand,zero]
  have andOne (x : Table) : tand x one = x := by funext r; simp [tand,one]
  have orZero (x : Table) : tor x zero = x := by funext r; simp [tor,zero]
  have orOne (x : Table) : tor x one = one := by funext r; simp [tor,one]
  have andZeroL (x : Table) : tand zero x = zero := by funext r; simp [tand,zero]
  have andOneL (x : Table) : tand one x = x := by funext r; simp [tand,one]
  have orZeroL (x : Table) : tor zero x = x := by funext r; simp [tor,zero]
  have orOneL (x : Table) : tor one x = one := by funext r; simp [tor,one]
  have selfAnd (x : Table) : tand x x = x := by funext r; simp [tand]
  have selfOr (x : Table) : tor x x = x := by funext r; simp [tor]
  rcases ha with rfl | rfl | ha
  · left; cases u <;> simp_all [Available]
  · left; cases u <;> simp_all [Available]
  rcases hb with rfl | rfl | hb
  · left; cases u <;> simp_all [Available]
  · left; cases u <;> simp_all [Available]
  by_cases e : a = b
  · subst b
    left; cases u <;> simp [selfAnd,selfOr,Available,ha]
  · obtain ⟨i,hi,ea⟩ := zz0n1 ha
    obtain ⟨j,hj,eb⟩ := zz0n1 hb
    have hij : i ≠ j := by rintro rfl; exact e (ea.symm.trans eb)
    right
    cases u
    · exact ⟨.meet i j, ⟨hi,hj,hij⟩, by simp only [Op.value,ea,eb,Bool.false_eq_true,
        ite_false]⟩
    · exact ⟨.join i j, ⟨hi,hj,hij⟩, by simp only [Op.value,ea,eb,ite_true]⟩
private def zz0n3 (w : List Table) (g : Gate) : Table :=
  fun x => g.op.eval (g.inputs.map (fun i => (w.getD i zero) x))
private def zz0n4 (w : List Table) (g : Gate) : List Table :=
  w ++ [zz0n3 w g]
private theorem zz0n5 {orig w : List Table}
    (h : ∀ f ∈ orig, Available w f) (g : Gate)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) : Possible w (zz0n3 orig g) := by
  rcases g with ⟨op,args⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases args with _ | ⟨a,_|⟨b,_|⟨c,l⟩⟩⟩
    · exact Or.inl (Or.inr (Or.inl rfl))
    · left; convert zz0n2 h a using 1; funext x; simp [zz0n3,GateOp.eval]
    · convert binary_possible (zz0n2 h a) (zz0n2 h b) false using 1
      funext x; simp [zz0n3,GateOp.eval,tand]
    · simp at hlen
  · rcases args with _ | ⟨a,_|⟨b,_|⟨c,l⟩⟩⟩
    · exact Or.inl (Or.inl rfl)
    · left; convert zz0n2 h a using 1; funext x; simp [zz0n3,GateOp.eval]
    · convert binary_possible (zz0n2 h a) (zz0n2 h b) true using 1
      funext x; simp [zz0n3,GateOp.eval,tor]
    · simp at hlen
  · rcases args with _ | ⟨a,l⟩
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact neg_possible (zz0n2 h a)
private theorem zz0n6 {p w orig v} (hp : Built p w)
    (ho : ∀ f ∈ orig, Available w f) (poss : Possible w v) :
    ∃ q z, Built q z ∧ q.length ≤ p.length + 1 ∧
      ∀ f ∈ orig ++ [v], Available z f := by
  classical
  by_cases hv : Available w v
  · refine ⟨p,w,hp,by omega,?_⟩
    intro f hf
    rcases List.mem_append.mp hf with h | h
    · exact ho f h
    · simp only [List.mem_singleton] at h
      exact h ▸ hv
  · obtain ⟨g,hg,he⟩ := poss.resolve_left hv
    subst v
    refine ⟨p ++ [g],w ++ [g.value w],.snoc hp g hg hv,by simp,?_⟩
    intro f hf
    rcases List.mem_append.mp hf with h | h
    · rcases ho f h with hz | hu | hm
      · exact Or.inl hz
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr (List.mem_append_left _ hm))
    · exact Or.inr (Or.inr (List.mem_append_right _ h))
private theorem zz0n7 (gs : List Gate) (p : List Op) (w orig : List Table)
    (hp : Built p w) (ho : ∀ f ∈ orig, Available w f)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ q z, Built q z ∧ q.length ≤ p.length + gs.length ∧
      ∀ f ∈ gs.foldl zz0n4 orig, Available z f := by
  induction gs generalizing p w orig with
  | nil => exact ⟨p,w,hp,by simp,ho⟩
  | cons g gs ih =>
    obtain ⟨ha,hb⟩ := legal g (by simp)
    obtain ⟨q,z,hq,hsize,hcover⟩ := zz0n6 hp ho (zz0n5 ho g ha hb)
    obtain ⟨q',z',hq',hsize',hcover'⟩ := ih q z (zz0n4 orig g) hq hcover
      (fun x hx => legal x (List.mem_cons_of_mem _ hx))
    exact ⟨q',z',hq',by simp only [List.length_cons]; omega,hcover'⟩
private theorem zz0n8 (w : List Table) (i : Nat) (x : Row) :
    (w.map (fun f => f x)).getD i false = (w.getD i zero) x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl
private def zz0n9 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
private theorem zz0n10 (gs : List Gate) (w : List Table) (x : Row) :
    (gs.foldl zz0n4 w).map (fun f => f x) =
    gs.foldl zz0n9 (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, ih,zz0n4,zz0n9,List.map_append,List.map_cons,List.map_nil,
      zz0n3,zz0n8]
private theorem zz0n11 (C : Circuit) (o : Nat) (x : Row) :
    ((C.gates.foldl zz0n4 inputTables).getD o zero) x =
    (C.wires (List.ofFn x)).getD o false := by
  rw [← zz0n8, zz0n10]
  have hi : inputTables.map (fun f => f x) = List.ofFn x := by
    simp [inputTables]
  rw [hi]; rfl
private theorem zz0n12 {f : Table} (lo : f (fun _ => false) = false)
    (hi : f (fun _ => true) = true) {w : List Table} (h : Available w f) : f ∈ w := by
  rcases h with rfl | rfl | h
  · contradiction
  · contradiction
  · exact h
theorem simulate {s : Nat} (existsC : Realizable s) :
    ∃ p w, Built p w ∧ p.length ≤ s ∧ f0 ∈ w ∧ f1 ∈ w ∧ f2 ∈ w := by
  obtain ⟨C,hC,hs,o0,o1,o2,ho⟩ := existsC
  obtain ⟨p,w,hp,hsize,ha⟩ := zz0n7 C.gates [] inputTables inputTables .start
    (fun _ h => Or.inr (Or.inr h)) hC
  have out {f : Table} (o : Nat)
      (correct : ∀ x : Row, (C.wires (List.ofFn x)).getD o false = f x) :
      Available w f := by
    have he : (C.gates.foldl zz0n4 inputTables).getD o zero = f := by
      funext x
      exact (zz0n11 C o x).trans (correct x)
    rw [← he]
    exact zz0n2 ha o
  refine ⟨p,w,hp,?_,zz0n12 (f:=f0) rfl rfl (out o0 (fun x => (ho x).1)),
    zz0n12 (f:=f1) rfl rfl (out o1 (fun x => (ho x).2.1)),
    zz0n12 (f:=f2) rfl rfl (out o2 (fun x => (ho x).2.2))⟩
  simpa [Circuit.size] using Nat.le_trans (by simpa using hsize : p.length ≤ C.gates.length) hs
end L652
namespace L652
abbrev Word := BitVec 64
def inputRow (r : Fin 64) : Row := fun j => r.val.testBit j.val
def pack (f : Table) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun r : Fin 64 => f (inputRow r)))).cast (by simp)
theorem pack_bit (f : Table) (i : Nat) (hi : i < 64) :
    (pack f).getLsbD i = f (inputRow ⟨i, hi⟩) := by
  simp only [pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl
theorem inputRow_surjective (x : Row) : ∃ r : Fin 64, inputRow r = x := by
  let bs := List.ofFn x
  let r := BitVec.ofBoolListLE bs
  have h : r.toNat < 64 := by
    have h' := r.isLt
    simpa [r, bs] using h'
  refine ⟨⟨r.toNat,h⟩,?_⟩
  funext i
  change r.getLsbD i.val = x i
  simp only [r, bs, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt]
  rfl
theorem pack_inj {a b : Table} (h : pack a = pack b) : a = b := by
  funext x
  obtain ⟨r, rfl⟩ := inputRow_surjective x
  simpa only [pack_bit _ _ r.isLt] using congrArg (fun w : Word => w.getLsbD r.val) h
theorem pack_meet (a b : Table) : pack (tand a b) = pack a &&& pack b := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, pack_bit _ i hi, tand]
theorem pack_join (a b : Table) : pack (tor a b) = pack a ||| pack b := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_or, pack_bit _ i hi, tor]
theorem pack_neg (a : Table) : pack (tnot a) = ~~~(pack a) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_not, pack_bit _ i hi, hi, decide_true, Bool.true_and, tnot]
def rawWords : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc,
  0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
theorem pack_inputs : inputTables.map pack = rawWords := by decide +kernel
def possibleWords (ws : List Word) : List Word :=
  (ws.map (fun x => ~~~x)) ++
    (ws.flatMap fun x => ws.flatMap fun y => [x &&& y, x ||| y])
private theorem zz1n0 {w : List Table} {i : Nat} (hi : i < w.length) :
    pack (w.getD i zero) ∈ w.map pack := by
  apply List.mem_map.mpr
  refine ⟨w[i], List.getElem_mem _, ?_⟩
  simp [List.getD_eq_getElem?_getD, hi]
theorem possible_of_valid {w : List Table} {g : Op} (hg : g.valid w.length) :
    pack (g.value w) ∈ possibleWords (w.map pack) := by
  cases g with
  | neg i =>
    rw [Op.value, pack_neg]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨_, zz1n0 hg, rfl⟩
  | meet i j =>
    rw [Op.value, pack_meet]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_, zz1n0 hg.1,
      List.mem_flatMap.mpr ⟨_, zz1n0 hg.2.1, by simp⟩⟩
  | join i j =>
    rw [Op.value, pack_join]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_, zz1n0 hg.1,
      List.mem_flatMap.mpr ⟨_, zz1n0 hg.2.1, by simp⟩⟩
def freshWords (ws : List Word) : List Word :=
  (possibleWords ws).filter fun v => v != 0 && v != ~~~0 && !(ws.contains v)
private theorem zz1n1 : pack zero = 0 := by decide +kernel
private theorem zz1n2 : pack one = ~~~0 := by decide +kernel
theorem fresh_of_valid {w : List Table} {g : Op} (hg : g.valid w.length)
    (hn : ¬ Available w (g.value w)) :
    pack (g.value w) ∈ freshWords (w.map pack) := by
  apply List.mem_filter.mpr
  refine ⟨possible_of_valid hg, ?_⟩
  have nz : pack (g.value w) ≠ 0 := fun e => hn (.inl (pack_inj (e.trans zz1n1.symm)))
  have nu : pack (g.value w) ≠ ~~~0 :=
    fun e => hn (.inr (.inl (pack_inj (e.trans zz1n2.symm))))
  have notmem : pack (g.value w) ∉ w.map pack := by
    intro hm
    obtain ⟨f, hf, e⟩ := List.mem_map.mp hm
    exact hn (.inr (.inr (pack_inj e ▸ hf)))
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
  exact ⟨⟨nz,nu⟩, Bool.eq_false_iff.mpr (fun e => notmem (List.contains_iff_mem.mp e))⟩
end L652
namespace L652
inductive LogicalGate where
  | neg (a : Word)
  | meet (a b : Word)
  | join (a b : Word)
  deriving DecidableEq
def LogicalGate.out : LogicalGate → Word
  | .neg a => ~~~a
  | .meet a b => a &&& b
  | .join a b => a ||| b
def LogicalGate.args : LogicalGate → List Word
  | .neg a => [a]
  | .meet a b | .join a b => [a,b]
def wiresOf (gs : List LogicalGate) : List Word := rawWords ++ gs.map LogicalGate.out
inductive History : List LogicalGate → Prop where
  | empty : History []
  | push {gs g} (h : History gs) (args : g.args ⊆ wiresOf gs)
    (fresh : g.out ≠ 0 ∧ g.out ≠ ~~~0 ∧ g.out ∉ wiresOf gs) : History (gs ++ [g])
def asGate (w : List Table) : Op → LogicalGate
  | .neg i => .neg (pack (w.getD i zero))
  | .meet i j => .meet (pack (w.getD i zero)) (pack (w.getD j zero))
  | .join i j => .join (pack (w.getD i zero)) (pack (w.getD j zero))
theorem asGate_out (w : List Table) (g : Op) :
    (asGate w g).out = pack (g.value w) := by
  cases g <;> simp [asGate, LogicalGate.out, Op.value, pack_neg, pack_meet, pack_join]
theorem asGate_args {w : List Table} {g : Op} (v : g.valid w.length) :
    (asGate w g).args ⊆ w.map pack := by
  have read (i : Nat) (hi : i < w.length) : pack (w.getD i zero) ∈ w.map pack := by
    apply List.mem_map.mpr
    exact ⟨w[i], List.getElem_mem _, by simp [List.getD_eq_getElem?_getD, hi]⟩
  cases g with
  | neg i =>
    intro x hx
    simp [asGate, LogicalGate.args] at hx
    exact hx ▸ read i v
  | meet i j | join i j =>
    intro x hx
    simp [asGate, LogicalGate.args] at hx
    rcases hx with rfl | rfl
    · exact read i v.1
    · exact read j v.2.1
theorem history_of_built {p w} (h : Built p w) :
    ∃ gs, History gs ∧ gs.length = p.length ∧ wiresOf gs = w.map pack := by
  induction h with
  | start => exact ⟨[], .empty, rfl, by simp [wiresOf,pack_inputs]⟩
  | @snoc p w h g v fresh ih =>
    obtain ⟨gs,hh,hlen,hw⟩ := ih
    have hn := (List.mem_filter.mp (fresh_of_valid v fresh)).2
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at hn
    refine ⟨gs ++ [asGate w g], .push hh (hw ▸ asGate_args v) ?_, by simp [hlen], ?_⟩
    · rw [asGate_out, hw]
      refine ⟨hn.1.1, hn.1.2, fun hm => ?_⟩
      have ht := List.contains_iff_mem.mpr hm
      rw [hn.2] at ht
      contradiction
    · simp only [wiresOf, List.map_append, List.map_cons, List.map_nil,
        ← List.append_assoc, asGate_out]
      rw [show rawWords ++ List.map LogicalGate.out gs = w.map pack from hw]
end L652
namespace L652
def sources : LogicalGate → Finset Word
  | .neg a => {a}
  | .meet a b | .join a b => {a,b}
theorem mem_sources {a : Word} {g : LogicalGate} : a ∈ sources g ↔ a ∈ g.args := by
  cases g <;> simp [sources, LogicalGate.args]
theorem sources_small (g : LogicalGate) : (sources g).card ≤ 2 := by
  cases g with
  | neg a => simp [sources]
  | meet a b | join a b => exact Finset.card_le_two
def prior (g : LogicalGate) (need : Finset Word) : Finset Word :=
  if g.out ∈ need then (need.erase g.out) ∪ sources g else need
def demand (gs : List LogicalGate) (need : Finset Word) : Finset Word :=
  gs.foldr prior need
def cost : List LogicalGate → Finset Word → Nat
  | [], _ => 0
  | g :: rest, need => (if g.out ∈ demand rest need then 1 else 0) + cost rest need
theorem demand_card (gs : List LogicalGate) (need : Finset Word) :
    (demand gs need).card ≤ need.card + cost gs need := by
  induction gs with
  | nil => simp [demand,cost]
  | cons g gs ih =>
    change (prior g (demand gs need)).card ≤ need.card + _
    by_cases use : g.out ∈ demand gs need
    · have positive := Finset.card_pos.mpr ⟨_,use⟩
      have erased := Finset.card_erase_of_mem use
      have small := sources_small g
      have union := Finset.card_union_le ((demand gs need).erase g.out) (sources g)
      simp only [prior,use,ite_true,cost] at *
      omega
    · simpa [prior,cost,use] using ih
theorem cost_le_length (gs : List LogicalGate) (need : Finset Word) : cost gs need ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [cost,List.length_cons]
    split <;> omega
def agree (xs : Finset Word) (i j : Fin 64) : Prop :=
  ∀ v ∈ xs, v.getLsbD i.val = v.getLsbD j.val
def Determines (mask : Word) (features : Finset Word) (target : Word) : Prop :=
  ∀ i j : Fin 64, mask.getLsbD i.val = true → mask.getLsbD j.val = true →
    agree features i j → target.getLsbD i.val = target.getLsbD j.val
theorem sources_determine (g : LogicalGate) {i j : Fin 64} (h : agree (sources g) i j) :
    g.out.getLsbD i.val = g.out.getLsbD j.val := by
  cases g with
  | neg a =>
    have e := h a (by simp [sources])
    simp only [LogicalGate.out, BitVec.getLsbD_not, i.isLt, j.isLt, decide_true,
      Bool.true_and, e]
  | meet a b | join a b =>
    have ha := h a (by simp [sources])
    have hb := h b (by simp [sources])
    simp only [LogicalGate.out, BitVec.getLsbD_and, BitVec.getLsbD_or, ha, hb]
theorem agree_prior (g : LogicalGate) (need : Finset Word) {i j : Fin 64}
    (h : agree (prior g need) i j) : agree need i j := by
  by_cases used : g.out ∈ need
  · simp only [prior,used,ite_true] at h
    intro v hv
    by_cases eq : v = g.out
    · subst v
      exact sources_determine g (fun x hx => h x (Finset.mem_union_right _ hx))
    · exact h v (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hv⟩))
  · simpa [prior,used] using h
theorem agree_demand (gs : List LogicalGate) (need : Finset Word) {i j : Fin 64}
    (h : agree (demand gs need) i j) : agree need i j := by
  induction gs with
  | nil => exact h
  | cons g gs ih => exact ih (agree_prior g _ h)
def scheduled : Finset Word → List LogicalGate → Prop
  | _, [] => True
  | base, g :: rest => sources g ⊆ base ∧ scheduled (insert g.out base) rest
def availableAfter (ws : Finset Word) (gs : List LogicalGate) : Finset Word :=
  ws ∪ (gs.map LogicalGate.out).toFinset
theorem available_cons (ws : Finset Word) (g : LogicalGate) (gs : List LogicalGate) :
    availableAfter ws (g :: gs) = availableAfter (insert g.out ws) gs := by
  ext v
  simp [availableAfter, or_left_comm, or_assoc]
theorem demand_available {gs : List LogicalGate} {ws need : Finset Word}
    (valid : scheduled ws gs) (has : need ⊆ availableAfter ws gs) : demand gs need ⊆ ws := by
  induction gs generalizing ws with
  | nil => simpa [demand,availableAfter] using has
  | cons g gs ih =>
    rw [available_cons] at has
    have mid := ih valid.2 has
    change prior g (demand gs need) ⊆ ws
    intro v hv
    by_cases used : g.out ∈ demand gs need
    · simp only [prior,used,ite_true,Finset.mem_union,Finset.mem_erase] at hv
      rcases hv with ⟨hne,hkeep⟩ | hsrc
      · exact (Finset.mem_insert.mp (mid hkeep)).resolve_left hne
      · exact valid.1 hsrc
    · simp only [prior,used,ite_false] at hv
      exact (Finset.mem_insert.mp (mid hv)).resolve_left (fun e => used (e ▸ hv))
end L652
namespace L652
def produced (gs : List LogicalGate) : Finset Word := (gs.map LogicalGate.out).toFinset
def readBy : List LogicalGate → Finset Word
  | [] => ∅
  | g :: rest => sources g ∪ readBy rest
def boundary (gs : List LogicalGate) (t : Word) : Finset Word :=
  (insert t (readBy gs)) \ produced gs
def productive (gs : List LogicalGate) (t : Word) : Prop :=
  produced gs ⊆ insert t (readBy gs)
theorem mem_readBy {w : Word} {gs : List LogicalGate} :
    w ∈ readBy gs ↔ ∃ g ∈ gs, w ∈ sources g := by
  induction gs with
  | nil => simp [readBy]
  | cons g gs ih => simp [readBy,ih]
theorem mem_produced {w : Word} {gs : List LogicalGate} :
    w ∈ produced gs ↔ ∃ g ∈ gs, g.out = w := by simp [produced]
theorem card_readBy (gs : List LogicalGate) : (readBy gs).card ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [readBy]
  | cons g gs ih =>
    have hu := Finset.card_union_le (sources g) (readBy gs)
    have hs := sources_small g
    simp only [readBy,List.length_cons]
    omega
theorem boundary_card {gs : List LogicalGate} {t : Word} (used : productive gs t)
    (unique : (gs.map LogicalGate.out).Nodup) : (boundary gs t).card ≤ gs.length+1 := by
  have n : (produced gs).card = gs.length := by
    simp only [produced,List.toFinset_card_of_nodup unique,List.length_map]
  have bound := card_readBy gs
  have insertBound := Finset.card_insert_le t (readBy gs)
  have sub := Finset.card_sdiff_of_subset used
  dsimp [boundary]
  omega
theorem demand_subset (gs : List LogicalGate) (goals : Finset Word) :
    demand gs goals ⊆ goals ∪ readBy gs := by
  induction gs with
  | nil => simp [demand,readBy]
  | cons g gs ih =>
    change prior g (demand gs goals) ⊆ goals ∪ (sources g ∪ readBy gs)
    intro v hv
    by_cases used : g.out ∈ demand gs goals
    · simp only [prior,used,ite_true,Finset.mem_union,Finset.mem_erase] at hv
      rcases hv with ⟨_,hm⟩ | hs
      · have := ih hm
        simp only [Finset.mem_union] at *
        tauto
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hs)
    · simp only [prior,used,ite_false] at hv
      have := ih hv
      simp only [Finset.mem_union] at *
      tauto
def cone : List LogicalGate → Finset Word → List LogicalGate
  | [], _ => []
  | g :: gs, goals =>
    if g.out ∈ demand gs goals then g :: cone gs goals else cone gs goals
theorem cone_sublist (gs : List LogicalGate) (goals : Finset Word) : (cone gs goals).Sublist gs := by
  induction gs with
  | nil => exact .slnil
  | cons g gs ih =>
    unfold cone
    split
    · exact .cons_cons g ih
    · exact .cons g ih
theorem scheduled_mono {gs : List LogicalGate} {a b : Finset Word}
    (valid : scheduled a gs) (incl : a ⊆ b) : scheduled b gs := by
  induction gs generalizing a b with
  | nil => trivial
  | cons g gs ih =>
    exact ⟨valid.1.trans incl,ih valid.2 (Finset.insert_subset_insert _ incl)⟩
theorem cone_schedule (gs : List LogicalGate) (goals : Finset Word) :
    scheduled (demand gs goals) (cone gs goals) ∧
    goals ⊆ (demand gs goals) ∪ produced (cone gs goals) := by
  induction gs with
  | nil => simp [demand,cone,scheduled,produced]
  | cons g gs ih =>
    let m := demand gs goals
    let q := cone gs goals
    change scheduled (prior g m) (if g.out ∈ m then g :: q else q) ∧ _
    by_cases use : g.out ∈ m
    · have avail : m ⊆ insert g.out (prior g m) := by
        intro v hv
        by_cases eq : v = g.out
        · exact Finset.mem_insert.mpr (.inl eq)
        · exact Finset.mem_insert.mpr (.inr (by
            simp only [prior,use,ite_true,Finset.mem_union,Finset.mem_erase]
            exact .inl ⟨eq,hv⟩))
      refine ⟨?_,?_⟩
      · simp only [use,ite_true,scheduled]
        exact ⟨by simp [prior,use], scheduled_mono ih.1 avail⟩
      · intro v hv
        change v ∈ prior g m ∪ produced (if g.out ∈ m then g :: q else q)
        simp only [use,ite_true,produced,List.map_cons,List.toFinset_cons,Finset.mem_union,
          Finset.mem_insert]
        rcases Finset.mem_union.mp (ih.2 hv) with hm | hq
        · rcases Finset.mem_insert.mp (avail hm) with e | hp
          · exact .inr (.inl e)
          · exact .inl hp
        · exact .inr (.inr hq)
    · change scheduled (prior g m) (if g.out ∈ m then g :: q else q) ∧
          goals ⊆ prior g m ∪ produced (if g.out ∈ m then g :: q else q)
      simpa [prior,use] using ih
theorem cone_touches (gs : List LogicalGate) (goals : Finset Word) :
    demand gs goals ∪ produced (cone gs goals) = goals ∪ readBy (cone gs goals) := by
  induction gs with
  | nil => simp [demand,cone,produced,readBy]
  | cons g gs ih =>
    by_cases use : g.out ∈ demand gs goals
    · simp only [demand,List.foldr_cons] at use ⊢
      simp only [cone, demand, use,ite_true,prior,produced,List.map_cons,List.toFinset_cons,readBy] at ih ⊢
      ext x
      have hi := Finset.ext_iff.mp ih x
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at hi ⊢
      by_cases eq : x = g.out
      · subst x; tauto
      · tauto
    · change prior g (demand gs goals) ∪ produced (cone (g::gs) goals) = _
      simpa [cone,prior,use] using ih
theorem cone_productive (gs : List LogicalGate) (t : Word) :
    productive (cone gs {t}) t := by
  intro v hv
  have h : v ∈ demand gs {t} ∪ produced (cone gs {t}) := Finset.mem_union_right _ hv
  rw [cone_touches] at h
  simpa using h
theorem boundary_determines {gs : List LogicalGate} {raw : Finset Word} {t : Word} (mask : Word)
    (valid : scheduled raw gs) (ht : t ∈ availableAfter raw gs)
    (disj : Disjoint raw (produced gs)) : Determines mask (boundary gs t) t := by
  have av := demand_available valid (show ({t} : Finset Word) ⊆ availableAfter raw gs by simpa using ht)
  intro i j _ _ same
  apply agree_demand gs {t} (i := i) (j := j) _ t (by simp)
  intro x hx
  apply same
  apply Finset.mem_sdiff.mpr
  refine ⟨?_,fun h => Finset.disjoint_left.mp disj (av hx) h⟩
  simpa using demand_subset gs {t} hx
end L652
namespace L652
def exceptFor (chosen : Finset Word) (gs : List LogicalGate) :=
  gs.filter (fun g => !(g.out ∈ chosen))
def tips (chosen : Finset Word) (gs : List LogicalGate) :=
  chosen \ readBy (gs.filter (fun g => g.out ∈ chosen))
def prefixClosed (raw chosen : Finset Word) (gs : List LogicalGate) :=
  ∀ g ∈ gs, g.out ∈ chosen → sources g ⊆ raw ∪ chosen
theorem mem_except {p gs g} : g ∈ exceptFor p gs ↔ g ∈ gs ∧ g.out ∉ p := by
  simp [exceptFor]
theorem produced_except (p : Finset Word) (gs : List LogicalGate) :
    produced (exceptFor p gs) = produced gs \ p := by
  ext x
  simp only [mem_produced,mem_except,Finset.mem_sdiff]
  constructor
  · rintro ⟨g,⟨hg,hp⟩,rfl⟩
    exact ⟨⟨g,hg,rfl⟩,hp⟩
  · rintro ⟨⟨g,hg,rfl⟩,hp⟩
    exact ⟨g,⟨hg,hp⟩,rfl⟩
theorem scheduled_except (p : Finset Word) {gs : List LogicalGate} {raw : Finset Word}
    (ok : scheduled raw gs) : scheduled (raw ∪ p) (exceptFor p gs) := by
  induction gs generalizing raw with
  | nil => trivial
  | cons g gs ih =>
    have rest := ih ok.2
    by_cases hp : g.out ∈ p
    · have eq : (insert g.out raw) ∪ p = raw ∪ p := by
        ext x; simp only [Finset.mem_union,Finset.mem_insert]
        constructor
        · rintro ((rfl | h) | h)
          · exact .inr hp
          · exact .inl h
          · exact .inr h
        · tauto
      rw [eq] at rest
      simpa [exceptFor,hp] using rest
    · simp only [exceptFor,List.filter_cons]
      simp only [hp,decide_false,Bool.not_false,ite_true,scheduled]
      exact ⟨fun _ ha => Finset.mem_union_left _ (ok.1 ha), by
        simpa [exceptFor, Finset.insert_union] using rest⟩
theorem read_available {raw : Finset Word} {gs : List LogicalGate} (ok : scheduled raw gs) :
    readBy gs ⊆ availableAfter raw gs := by
  induction gs generalizing raw with
  | nil => simp [readBy]
  | cons g gs ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hs | hs
    · exact Finset.mem_union_left _ (ok.1 hs)
    · rw [available_cons]
      exact ih ok.2 hs
theorem productive_except {chosen raw : Finset Word} {gs : List LogicalGate} {t : Word}
    (used : productive gs t) (ok : prefixClosed raw chosen gs)
    (disj : Disjoint raw (produced gs)) : productive (exceptFor chosen gs) t := by
  intro v hv
  rw [produced_except,Finset.mem_sdiff] at hv
  rcases Finset.mem_insert.mp (used hv.1) with he | hr
  · exact Finset.mem_insert.mpr (.inl he)
  · obtain ⟨g,hg,hs⟩ := mem_readBy.mp hr
    have outside : g.out ∉ chosen := by
      intro hin
      rcases Finset.mem_union.mp (ok g hg hin hs) with h | h
      · exact Finset.disjoint_left.mp disj h hv.1
      · exact hv.2 h
    exact Finset.mem_insert.mpr (.inr (mem_readBy.mpr ⟨g,mem_except.mpr ⟨hg,outside⟩,hs⟩))
theorem boundary_covers_tips {chosen : Finset Word} {univ coneG : List LogicalGate} {t : Word}
    (sub : coneG ⊆ univ) (used : productive coneG t) (allIn : chosen ⊆ produced coneG) :
    tips chosen univ ⊆ boundary (exceptFor chosen coneG) t := by
  intro v hv
  obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hv
  apply Finset.mem_sdiff.mpr
  refine ⟨?_,by rw [produced_except]; exact fun h => (Finset.mem_sdiff.mp h).2 hp⟩
  rcases Finset.mem_insert.mp (used (allIn hp)) with he | hr
  · exact Finset.mem_insert.mpr (.inl he)
  · obtain ⟨g,hg,hs⟩ := mem_readBy.mp hr
    have outside : g.out ∉ chosen := by
      intro hide
      exact hn (mem_readBy.mpr ⟨g, List.mem_filter.mpr ⟨sub hg, by simpa using hide⟩, hs⟩)
    exact Finset.mem_insert.mpr (.inr (mem_readBy.mpr ⟨g,mem_except.mpr ⟨hg,outside⟩,hs⟩))
theorem boundary_in_base {gs : List LogicalGate} {raw : Finset Word} {t : Word}
    (ok : scheduled raw gs) (ht : t ∈ availableAfter raw gs) : boundary gs t ⊆ raw := by
  intro v hv
  obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp hv
  have hav : v ∈ availableAfter raw gs := by
    rcases Finset.mem_insert.mp hr with rfl | h
    · exact ht
    · exact read_available ok h
  exact (Finset.mem_union.mp hav).resolve_right hn
theorem slice_spec {gs : List LogicalGate} {raw : Finset Word} {t : Word}
    (ok : scheduled raw gs) (ht : t ∈ availableAfter raw gs) :
    scheduled raw (cone gs {t}) ∧ t ∈ availableAfter raw (cone gs {t}) := by
  have first := cone_schedule gs {t}
  have sub := demand_available ok (show ({t} : Finset Word) ⊆ availableAfter raw gs by simpa using ht)
  refine ⟨scheduled_mono first.1 sub,?_⟩
  rcases Finset.mem_union.mp (first.2 (show t ∈ ({t} : Finset Word) by simp)) with h | h
  · exact Finset.mem_union_left _ (sub h)
  · exact Finset.mem_union_right _ h
theorem produced_mono {a b : List LogicalGate} (h : a ⊆ b) : produced a ⊆ produced b := by
  intro x hx
  obtain ⟨g,hg,rfl⟩ := mem_produced.mp hx
  exact mem_produced.mpr ⟨g,h hg,rfl⟩
theorem available_except (p raw : Finset Word) (gs : List LogicalGate) :
    availableAfter raw gs ⊆ availableAfter (raw ∪ p) (exceptFor p gs) := by
  intro x hx
  change x ∈ (raw ∪ p) ∪ produced (exceptFor p gs)
  rw [produced_except]
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  · by_cases h' : x ∈ p
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,h'⟩)
def gatesFor (gs : List LogicalGate) (t : Word) := produced (cone gs {t})
def shared (gs : List LogicalGate) (t u : Word) := gatesFor gs t ∩ gatesFor gs u
theorem prefix_feature_set (mask : Word) {gs : List LogicalGate} {raw chosen : Finset Word} {t : Word}
    (ok : scheduled raw gs) (ht : t ∈ availableAfter raw gs)
    (unique : (gs.map LogicalGate.out).Nodup) (disj : Disjoint raw (produced gs))
    (closed : prefixClosed raw chosen gs) (sub : chosen ⊆ gatesFor gs t) :
    ∃ features : Finset Word, features ⊆ raw ∪ chosen ∧ tips chosen gs ⊆ features ∧
      Determines mask features t ∧ features.card ≤ (gatesFor gs t \ chosen).card + 1 := by
  let c := cone gs {t}
  let r := exceptFor chosen c
  have sublist : c.Sublist gs := cone_sublist ..
  have hsub : produced c ⊆ produced gs := produced_mono sublist.subset
  have cvalid := slice_spec ok ht
  have rvalid : scheduled (raw ∪ chosen) r := scheduled_except chosen cvalid.1
  have tr : t ∈ availableAfter (raw ∪ chosen) r := available_except chosen raw c cvalid.2
  have d : Disjoint (raw ∪ chosen) (produced r) := by
    apply Finset.disjoint_left.mpr
    intro x hx hr
    obtain ⟨hin,hn⟩ := Finset.mem_sdiff.mp ((produced_except chosen c) ▸ hr)
    rcases Finset.mem_union.mp hx with hraw | hchosen
    · exact Finset.disjoint_left.mp disj hraw (hsub hin)
    · exact hn hchosen
  have cc : prefixClosed raw chosen c := fun g hg => closed g (sublist.subset hg)
  have productiveR : productive r t :=
    productive_except (cone_productive gs t) cc (Finset.disjoint_left.mpr
      (fun _ hx hm => Finset.disjoint_left.mp disj hx (hsub hm)))
  have rsub : r.Sublist gs := (List.filter_sublist ..).trans sublist
  have nodupR : (r.map LogicalGate.out).Nodup := unique.sublist (rsub.map _)
  refine ⟨boundary r t,boundary_in_base rvalid tr,?_,boundary_determines mask rvalid tr d,?_⟩
  · exact boundary_covers_tips sublist.subset (cone_productive gs t) sub
  · have hn : (produced r).card = r.length := by
      simp only [produced,List.toFinset_card_of_nodup nodupR,List.length_map]
    have bound := boundary_card productiveR nodupR
    rw [← hn,show produced r = gatesFor gs t \ chosen from produced_except chosen c] at bound
    exact bound
theorem pair_feature_bound (mask : Word) {gs : List LogicalGate} {raw chosen : Finset Word} {t u : Word}
    (ok : scheduled raw gs) (ht : t ∈ availableAfter raw gs) (hu : u ∈ availableAfter raw gs)
    (unique : (gs.map LogicalGate.out).Nodup) (disj : Disjoint raw (produced gs))
    (closed : prefixClosed raw chosen gs) (sub : chosen ⊆ shared gs t u) :
    ∃ a b : Finset Word, a ⊆ raw ∪ chosen ∧ b ⊆ raw ∪ chosen ∧
      tips chosen gs ⊆ a ∧ tips chosen gs ⊆ b ∧
      Determines mask a t ∧ Determines mask b u ∧
      a.card + b.card + 2 * chosen.card ≤ gs.length + 2 + (shared gs t u).card := by
  have p1 : chosen ⊆ gatesFor gs t := fun x hx => (Finset.mem_inter.mp (sub hx)).1
  have p2 : chosen ⊆ gatesFor gs u := fun x hx => (Finset.mem_inter.mp (sub hx)).2
  obtain ⟨a,ha,sa,da,ba⟩ := prefix_feature_set mask ok ht unique disj closed p1
  obtain ⟨b,hb,sb,db,bb⟩ := prefix_feature_set mask ok hu unique disj closed p2
  refine ⟨a,b,ha,hb,sa,sb,da,db,?_⟩
  have uBound : gatesFor gs t ∪ gatesFor gs u ⊆ produced gs :=
    Finset.union_subset (produced_mono (cone_sublist gs {t}).subset)
      (produced_mono (cone_sublist gs {u}).subset)
  have cnt := Finset.card_le_card uBound
  have cnt1 := Finset.card_sdiff_of_subset p1
  have cnt2 := Finset.card_sdiff_of_subset p2
  have bound1 := Finset.card_le_card p1
  have bound2 := Finset.card_le_card p2
  have both := Finset.card_union_add_card_inter (gatesFor gs t) (gatesFor gs u)
  have total : (produced gs).card = gs.length := by
    simp only [produced,List.toFinset_card_of_nodup unique,List.length_map]
  unfold shared
  omega
end L652
namespace L652
theorem same_producer {gs : List LogicalGate} (h : (gs.map LogicalGate.out).Nodup)
    {a b : LogicalGate} (ha : a ∈ gs) (hb : b ∈ gs) (e : a.out = b.out) : a = b := by
  induction gs with
  | nil => simp at ha
  | cons g gs ih =>
    simp only [List.map_cons,List.nodup_cons] at h
    rcases List.mem_cons.mp ha with ha0 | ha1
    · rcases List.mem_cons.mp hb with hb0 | hb1
      · exact ha0.trans hb0.symm
      · exact False.elim (h.1 (List.mem_map.mpr ⟨b,hb1,e.symm.trans (congrArg _ ha0)⟩))
    · rcases List.mem_cons.mp hb with hb0 | hb1
      · exact False.elim (h.1 (List.mem_map.mpr ⟨a,ha1,e.trans (congrArg _ hb0)⟩))
      · exact ih h.2 ha1 hb1
theorem shared_closed {gs : List LogicalGate} {raw : Finset Word} {t u : Word}
    (ok : scheduled raw gs) (ht : t ∈ availableAfter raw gs) (hu : u ∈ availableAfter raw gs)
    (unique : (gs.map LogicalGate.out).Nodup) : prefixClosed raw (shared gs t u) gs := by
  have side {a : Word} (ha : a ∈ availableAfter raw gs) {g : LogicalGate} (hg : g ∈ gs)
      (hout : g.out ∈ gatesFor gs a) {v} (hv : v ∈ sources g) :
      v ∈ raw ∪ gatesFor gs a := by
    obtain ⟨q,hq,eq⟩ := mem_produced.mp hout
    have he := same_producer unique ((cone_sublist gs {a}).subset hq) hg eq
    subst q
    exact read_available (slice_spec ok ha).1 (mem_readBy.mpr ⟨g,hq,hv⟩)
  intro g hg hin v hv
  obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hin
  have p1 := Finset.mem_union.mp (side ht hg h1 hv)
  have p2 := Finset.mem_union.mp (side hu hg h2 hv)
  by_cases r : v ∈ raw
  · exact Finset.mem_union_left _ r
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨p1.resolve_left r,p2.resolve_left r⟩)
def kept (chosen : Finset Word) (gs : List LogicalGate) :=
  gs.filter fun g => g.out ∈ chosen
theorem produced_kept (chosen : Finset Word) (gs : List LogicalGate) :
    produced (kept chosen gs) = produced gs ∩ chosen := by
  ext x
  simp only [mem_produced, kept, List.mem_filter, decide_eq_true_eq, Finset.mem_inter]
  constructor
  · rintro ⟨g,⟨hg,h⟩,rfl⟩
    exact ⟨⟨g,hg,rfl⟩,h⟩
  · rintro ⟨⟨g,hg,rfl⟩,hp⟩
    exact ⟨g,⟨hg,hp⟩,rfl⟩
private theorem zz6n0 {chosen raw seen : Finset Word} {gs : List LogicalGate}
    (ok : scheduled (raw ∪ seen) gs) (closed : prefixClosed raw chosen gs) :
    scheduled (raw ∪ (seen ∩ chosen)) (kept chosen gs) := by
  induction gs generalizing seen with
  | nil => trivial
  | cons g gs ih =>
    have eq : raw ∪ insert g.out seen = insert g.out (raw ∪ seen) := by
      ext x; simp [or_left_comm]
    have tail := ih (seen := insert g.out seen) (eq ▸ ok.2)
      (fun a ha => closed a (List.mem_cons_of_mem _ ha))
    by_cases hg : g.out ∈ chosen
    · have ha := closed g (by simp) hg
      simp only [kept,List.filter_cons, hg, decide_true, ite_true, scheduled]
      refine ⟨?_,?_⟩
      · intro x hx
        rcases Finset.mem_union.mp (ok.1 hx) with hr | hs
        · exact Finset.mem_union_left _ hr
        · rcases Finset.mem_union.mp (ha hx) with hr | hc
          · exact Finset.mem_union_left _ hr
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hs,hc⟩)
      · have e : raw ∪ (insert g.out seen ∩ chosen) = insert g.out (raw ∪ (seen ∩ chosen)) := by
          ext x
          simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_inter]
          by_cases h : x = g.out
          · subst x; tauto
          · tauto
        rw [e] at tail
        exact tail
    · simp only [kept,List.filter_cons,hg,decide_false,ite_false]
      have e : raw ∪ (insert g.out seen ∩ chosen) = raw ∪ (seen ∩ chosen) := by
        ext x; simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_inter]
        by_cases h : x = g.out
        · subst x; tauto
        · tauto
      rw [e] at tail
      exact tail
theorem kept_schedule {chosen raw : Finset Word} {gs : List LogicalGate}
    (ok : scheduled raw gs) (closed : prefixClosed raw chosen gs) :
    scheduled raw (kept chosen gs) := by
  have h := zz6n0 (seen := ∅) (by simpa using ok) closed
  simpa using h
theorem subset_prefix_closed {p gs : List LogicalGate} {raw : Finset Word}
    (unique : (gs.map LogicalGate.out).Nodup) (sub : p ⊆ gs) (valid : scheduled raw p) :
    prefixClosed raw (produced p) gs := by
  intro g hg hin w hw
  obtain ⟨q,hq,eq⟩ := mem_produced.mp hin
  have he := same_producer unique (sub hq) hg eq
  subst q
  exact read_available valid (mem_readBy.mpr ⟨_,hq,hw⟩)
theorem shared_history {gs : List LogicalGate} {raw : Finset Word} {t u : Word}
    (ok : scheduled raw gs) (ht : t ∈ availableAfter raw gs) (hu : u ∈ availableAfter raw gs)
    (unique : (gs.map LogicalGate.out).Nodup) :
    let h := shared gs t u
    scheduled raw (kept h gs) ∧ produced (kept h gs) = h := by
  refine ⟨kept_schedule ok (shared_closed ok ht hu unique),?_⟩
  rw [produced_kept,Finset.inter_eq_right]
  exact fun x hx => produced_mono (cone_sublist gs {t}).subset (Finset.mem_inter.mp hx).1
end L652
namespace L652
theorem available_wires (gs : List LogicalGate) :
    availableAfter rawWords.toFinset gs = (wiresOf gs).toFinset := by
  simp [availableAfter,wiresOf]
theorem scheduled_append {gs ts : List LogicalGate} {base : Finset Word} :
    scheduled base (gs ++ ts) ↔ scheduled base gs ∧ scheduled (availableAfter base gs) ts := by
  induction gs generalizing base with
  | nil => simp [scheduled,availableAfter]
  | cons g gs ih =>
    simp only [List.cons_append,scheduled,ih,available_cons,and_assoc]
theorem history_schedule {gs : List LogicalGate} (h : History gs) :
    scheduled rawWords.toFinset gs ∧ (gs.map LogicalGate.out).Nodup ∧
      Disjoint rawWords.toFinset (produced gs) := by
  induction h with
  | empty => simp [scheduled,produced]
  | @push gs g h args fresh ih =>
    obtain ⟨ok,unique,dis⟩ := ih
    have out : g.out ∉ gs.map LogicalGate.out ∧ g.out ∉ rawWords := by
      have hn := fresh.2.2
      simp only [wiresOf,List.mem_append,not_or] at hn
      exact ⟨hn.2,hn.1⟩
    refine ⟨scheduled_append.mpr ⟨ok,?_,trivial⟩, ?_, ?_⟩
    · rw [available_wires]
      intro x hx
      exact List.mem_toFinset.mpr (args (mem_sources.mp hx))
    · rw [List.map_append]
      exact List.nodup_append.mpr ⟨unique,by simp,by simpa using out.1⟩
    · apply Finset.disjoint_left.mpr
      intro x hx hx'
      rcases mem_produced.mp hx' with ⟨q,hq,rfl⟩
      rcases List.mem_append.mp hq with left | last
      · exact Finset.disjoint_left.mp dis hx (mem_produced.mpr ⟨q,left,rfl⟩)
      · have eq : q = g := by simpa using last
        exact out.2 (eq ▸ List.mem_toFinset.mp hx)
theorem projections_of_prefix {raw : Finset Word} {gs p : List LogicalGate} {t u : Word}
    (ok : scheduled raw gs) (ht : t ∈ availableAfter raw gs) (hu : u ∈ availableAfter raw gs)
    (unique : (gs.map LogicalGate.out).Nodup) (disj : Disjoint raw (produced gs))
    (sub : p ⊆ kept (shared gs t u) gs) (valid : scheduled raw p) (mask : Word) :
    ∃ a b : Finset Word, a ⊆ raw ∪ produced p ∧ b ⊆ raw ∪ produced p ∧
      produced p \ readBy p ⊆ a ∧ produced p \ readBy p ⊆ b ∧
      Determines mask a t ∧ Determines mask b u ∧
      a.card + b.card + 2*(produced p).card ≤ gs.length + 2 + (shared gs t u).card := by
  have whole : p ⊆ gs := fun _ h => (List.mem_filter.mp (sub h)).1
  have inside : produced p ⊆ shared gs t u := by
    intro x hx
    obtain ⟨g,hg,rfl⟩ := mem_produced.mp hx
    exact of_decide_eq_true (List.mem_filter.mp (sub hg)).2
  have cut := subset_prefix_closed unique whole valid
  obtain ⟨a,b,ha,hb,sa,sb,da,db,bound⟩ := pair_feature_bound mask ok ht hu unique disj cut inside
  have eq : readBy (kept (produced p) gs) = readBy p := by
    ext x
    simp only [mem_readBy]
    constructor
    · rintro ⟨g,hg,hx⟩
      obtain ⟨hg,hp⟩ := List.mem_filter.mp hg
      obtain ⟨q,hq,he⟩ := mem_produced.mp (of_decide_eq_true hp)
      exact ⟨q,hq,same_producer unique hg (whole hq) he.symm ▸ hx⟩
    · rintro ⟨g,hg,hx⟩
      exact ⟨g,List.mem_filter.mpr ⟨whole hg,decide_eq_true (mem_produced.mpr ⟨g,hg,rfl⟩)⟩,hx⟩
  have te : tips (produced p) gs = produced p \ readBy p := by
    change produced p \ readBy (kept (produced p) gs) = _
    rw [eq]
  exact ⟨a,b,ha,hb,te ▸ sa,te ▸ sb,da,db,bound⟩
end L652
namespace L652
def operandPair (w : List Word) (g : LogicalGate) : Nat × Nat :=
  match g with
  | .neg a => (w.idxOf a, w.idxOf a)
  | .meet a b | .join a b => (min (w.idxOf a) (w.idxOf b), max (w.idxOf a) (w.idxOf b))
def operation : LogicalGate → Nat
  | .neg _ => 2
  | .meet _ _ => 0
  | .join _ _ => 1
def gateKey (w : List Word) (g : LogicalGate) : Nat :=
  let p := operandPair w g
  (p.2*32+p.1)*3+operation g
theorem idxOf_mono_snoc (w : List Word) (a v : Word) : w.idxOf a ≤ (w++[v]).idxOf a := by
  by_cases has : a ∈ w
  · simp [List.idxOf_append,has]
  · rw [List.idxOf_append,if_neg has,List.idxOf_eq_length has]
    omega
theorem gateKey_mono (w : List Word) (v : Word) (g : LogicalGate) :
    gateKey w g ≤ gateKey (w++[v]) g := by
  cases g with
  | neg a =>
    have h := idxOf_mono_snoc w a v
    simp only [gateKey,operandPair,operation]
    omega
  | meet a b | join a b =>
    have ha := idxOf_mono_snoc w a v
    have hb := idxOf_mono_snoc w b v
    have h1 := min_le_min ha hb
    have h2 := max_le_max ha hb
    simp only [gateKey,operandPair,operation]
    omega
theorem key_ready (w : List Word) (g : LogicalGate) (short : w.length ≤ 32) :
    sources g ⊆ w.toFinset ↔ gateKey w g < 96*w.length := by
  cases g with
  | neg a =>
    simp only [sources,Finset.singleton_subset_iff,List.mem_toFinset,gateKey,operandPair,operation]
    by_cases h : a ∈ w
    · have ha := List.idxOf_lt_length_of_mem h
      constructor <;> intro <;> first | exact h | omega
    · rw [List.idxOf_eq_length h]
      constructor <;> intro <;> first | contradiction | omega
  | meet a b | join a b =>
    simp only [sources,Finset.insert_subset_iff,Finset.singleton_subset_iff,List.mem_toFinset,
      gateKey,operandPair,operation]
    constructor
    · rintro ⟨ha,hb⟩
      have h1 := List.idxOf_lt_length_of_mem ha
      have h2 := List.idxOf_lt_length_of_mem hb
      omega
    · intro h
      constructor
      · by_contra missing
        rw [List.idxOf_eq_length missing] at h
        omega
      · by_contra missing
        rw [List.idxOf_eq_length missing] at h
        omega
theorem scheduled_erase (g : LogicalGate) {raw : Finset Word} {gs : List LogicalGate}
    (ok : scheduled raw gs) : scheduled (insert g.out raw) (gs.erase g) := by
  induction gs generalizing raw with
  | nil => trivial
  | cons a gs ih =>
    by_cases he : a = g
    · subst a
      simpa using ok.2
    · simp only [List.erase_cons,beq_eq_false_iff_ne.mpr he, Bool.false_eq_true,ite_false]
      exact ⟨fun x hx => Finset.mem_insert_of_mem (ok.1 hx), by
        simpa only [Finset.insert_comm a.out g.out] using ih ok.2⟩
inductive KeyOrdered : List Word → Nat → List LogicalGate → Prop where
  | nil {w last} : KeyOrdered w last []
  | cons {w last g gs} (ready : sources g ⊆ w.toFinset) (min : last ≤ gateKey w g)
      (tail : KeyOrdered (w++[g.out]) (gateKey w g) gs) : KeyOrdered w last (g::gs)
theorem order_with_min (gs : List LogicalGate) (w : List Word) (last : Nat)
    (bound : w.length + gs.length ≤ 32) (ok : scheduled w.toFinset gs)
    (lo : ∀ g ∈ gs, last ≤ gateKey w g) :
    ∃ qs, qs.Perm gs ∧ KeyOrdered w last qs := by
  classical
  match gs with
  | [] => exact ⟨[],List.Perm.nil,.nil⟩
  | a::rs =>
    let available := (a::rs).toFinset
    have memA : a ∈ available := by simp [available]
    obtain ⟨g,hg,hmin⟩ := available.exists_min_image (gateKey w) ⟨a,memA⟩
    have hgm : g ∈ a::rs := List.mem_toFinset.mp hg
    have short : w.length ≤ 32 := by omega
    have ready : sources g ⊆ w.toFinset :=
      (key_ready w g short).mpr (lt_of_le_of_lt (hmin a memA) ((key_ready w a short).mp ok.1))
    have perms := List.perm_cons_erase hgm
    have cnt := perms.length_eq
    simp only [List.length_cons] at cnt
    have sched : scheduled (w++[g.out]).toFinset ((a::rs).erase g) := by
      simpa using scheduled_erase g ok
    have nextMin (v : LogicalGate) (hv : v ∈ (a::rs).erase g) :
        gateKey w g ≤ gateKey (w++[g.out]) v :=
      le_trans (hmin v (List.mem_toFinset.mpr (List.mem_of_mem_erase hv))) (gateKey_mono w g.out v)
    obtain ⟨qs,hp,ord⟩ := order_with_min ((a::rs).erase g) (w++[g.out]) (gateKey w g)
      (by simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at *; omega) sched nextMin
    exact ⟨g::qs,(hp.cons g).trans perms.symm,.cons ready (lo _ hgm) ord⟩
termination_by gs.length
decreasing_by
  have n := (List.perm_cons_erase hgm).length_eq
  simp only [List.length_cons] at *
  omega
theorem canonical_order {gs : List LogicalGate} {w : List Word} (len : w.length+gs.length ≤ 32)
    (ok : scheduled w.toFinset gs) : ∃ qs, qs.Perm gs ∧ KeyOrdered w 0 qs :=
  order_with_min gs w 0 len ok (fun _ _ => Nat.zero_le _)
end L652
namespace CyclicMatchings.ReadOnce
abbrev Table := UInt64
def leaves : List Table :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def matching (shift : Nat) : Table :=
  ((leaves.getD 0 0) &&& (leaves.getD (3 + shift % 3) 0)) |||
  ((leaves.getD 1 0) &&& (leaves.getD (3 + (1 + shift) % 3) 0)) |||
  ((leaves.getD 2 0) &&& (leaves.getD (3 + (2 + shift) % 3) 0))
def pick {α : Type} : List α → List (α × List α)
  | [] => []
  | x :: xs => (x,xs) :: (pick xs).map fun (y,ys) => (y,x::ys)
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | x :: xs =>
      ((pick xs).map fun (y,ys) => (x,y,ys)) ++
      ((pairs xs).map fun (y,z,ys) => (y,z,x::ys))
def next (ws : List Table) : List (List Table) :=
  (pairs ws).flatMap fun (a,b,rest) => [(a &&& b) :: rest, (a ||| b) :: rest]
inductive Built : Nat → List Table → Table → Prop
  | done {ws x} (h : x ∈ ws) : Built 0 ws x
  | merge {n ws zs x} (h : zs ∈ next ws) (later : Built n zs x) : Built (n+1) ws x
end CyclicMatchings.ReadOnce
namespace CyclicMatchings.ReadOnce
def combine (join : Bool) (a b : Table) : Table :=
  if join then a ||| b else a &&& b
theorem pick_erase {α : Type} [DecidableEq α] {x : α} {ws : List α} (h : x ∈ ws) :
    (x,ws.erase x) ∈ pick ws := by
  induction ws with
  | nil => simp at h
  | cons a as ih =>
    by_cases e : a=x
    · subst x; simp [pick]
    · have hm : x ∈ as := by simpa [Ne.symm e] using h
      simp only [pick, List.mem_cons, List.mem_map]
      exact Or.inr ⟨(x,as.erase x), ih hm, by simp [e]⟩
theorem pair_complete {α : Type} [DecidableEq α] {a b : α} {ws tail : List α}
    (h : (a::b::tail).Perm ws) :
    ∃ zs, ((a,b,zs) ∈ pairs ws ∨ (b,a,zs) ∈ pairs ws) ∧ tail.Perm zs := by
  induction ws generalizing tail with
  | nil => simp at h
  | cons u us ih =>
    by_cases ea : u=a
    · subst u
      obtain ⟨hm,hr⟩ := List.cons_perm_iff_perm_erase.mp h.cons_inv
      refine ⟨us.erase b, Or.inl ?_, hr⟩
      exact List.mem_append_left _ (List.mem_map.mpr ⟨(b,us.erase b),pick_erase hm,rfl⟩)
    by_cases eb : u=b
    · subst u
      have h' : (b::a::tail).Perm (b::us) := (List.Perm.swap _ _ _).trans h
      obtain ⟨hm,hr⟩ := List.cons_perm_iff_perm_erase.mp h'.cons_inv
      refine ⟨us.erase a, Or.inr ?_, hr⟩
      exact List.mem_append_left _ (List.mem_map.mpr ⟨(a,us.erase a),pick_erase hm,rfl⟩)
    have hm : u ∈ tail := by simpa [ea,eb] using (h.mem_iff.mpr List.mem_cons_self)
    have h' : (a::b::tail.erase u).Perm us := by
      simpa [List.erase_cons, Ne.symm ea, Ne.symm eb] using h.erase u
    obtain ⟨zs,hz,hp⟩ := ih h'
    refine ⟨u::zs, ?_, (List.perm_cons_erase hm).trans (hp.cons _)⟩
    rcases hz with ha|hb
    · exact Or.inl (List.mem_append_right _ (List.mem_map.mpr ⟨_,ha,rfl⟩))
    · exact Or.inr (List.mem_append_right _ (List.mem_map.mpr ⟨_,hb,rfl⟩))
theorem next_complete (join : Bool) {a b : Table} {ws tail : List Table}
    (h : (a::b::tail).Perm ws) :
    ∃ zs, zs ∈ next ws ∧ (combine join a b :: tail).Perm zs := by
  obtain ⟨zs,hz,hp⟩ := pair_complete h
  refine ⟨combine join a b :: zs, ?_, hp.cons _⟩
  rcases hz with ha|hb
  · apply List.mem_flatMap.mpr
    exact ⟨_, ha, by cases join <;> simp [combine]⟩
  · have comm : combine join a b = combine join b a := by
      cases join
      · exact UInt64.and_comm a b
      · exact UInt64.or_comm a b
    rw [comm]
    apply List.mem_flatMap.mpr
    exact ⟨_, hb, by cases join <;> simp [combine]⟩
def directedPairs : List (Nat × Nat) := [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
def goodPair (x : Table) (ij : Nat × Nat) : Bool :=
  let f := matching ij.1
  let g := matching ij.2
  x == g || ((x &&& f) != (g &&& f) && (x &&& (~~~f)) != (g &&& (~~~f)))
end CyclicMatchings.ReadOnce
namespace CyclicMatchings.ReadOnce
private def zz11n0 (x g f n expectedF expectedN : Nat) : Bool :=
  x == g || ((x &&& f) != expectedF && (x &&& n) != expectedN)
private def zz11n1 (x : Nat) : Bool :=
  zz11n0 x 0xfeeefcccfaaaf000 0xfefcfaf0eeccaa00 0x0103050f113355ff 0xfeecf8c0ea88a000 0x0002040c10225000 &&
  (zz11n0 x 0xfefaeeaafcf0cc00 0xfefcfaf0eeccaa00 0x0103050f113355ff 0xfef8eaa0ecc08800 0x0002040a10304400 &&
  (zz11n0 x 0xfefcfaf0eeccaa00 0xfeeefcccfaaaf000 0x0111033305550fff 0xfeecf8c0ea88a000 0x0010023004440a00 &&
  (zz11n0 x 0xfefaeeaafcf0cc00 0xfeeefcccfaaaf000 0x0111033305550fff 0xfeeaec88f8a0c000 0x0010022204500c00 &&
  (zz11n0 x 0xfefcfaf0eeccaa00 0xfefaeeaafcf0cc00 0x01051155030f33ff 0xfef8eaa0ecc08800 0x00041050020c2200 &&
  (zz11n0 x 0xfeeefcccfaaaf000 0xfefaeeaafcf0cc00 0x01051155030f33ff 0xfeeaec88f8a0c000 0x00041044020a3000 && true)))))
private def zz11n2 : Nat → List Nat → Bool
  | 0, ws => ws.all zz11n1
  | k+1, ws => (pairs ws).all fun (a,b,rest) =>
      zz11n2 k ((a &&& b)::rest) && zz11n2 k ((a ||| b)::rest)
private def zz11n3 (a b c d : Nat) : Bool :=
  [(a&&&b&&&c&&&d),
   ((a&&&b&&&c)|||d),
   (((a&&&b)|||c)&&&d),
   ((a&&&b)|||c|||d),
   ((a|||b)&&&c&&&d),
   (((a|||b)&&&c)|||d),
   ((a|||b|||c)&&&d),
   (a|||b|||c|||d),
   (((a&&&c)|||b)&&&d),
   ((a&&&c)|||b|||d),
   ((a|||c)&&&b&&&d),
   (((a|||c)&&&b)|||d),
   (((b&&&c)|||a)&&&d),
   ((b&&&c)|||a|||d),
   ((b|||c)&&&a&&&d),
   (((b|||c)&&&a)|||d),
   ((a&&&d)|||(b&&&c)),
   ((a|||d)&&&b&&&c),
   ((a&&&d)|||b|||c),
   ((a|||d)&&&(b|||c)),
   ((a&&&c)|||(b&&&d)),
   ((b|||d)&&&a&&&c),
   ((b&&&d)|||a|||c),
   ((a|||c)&&&(b|||d)),
   ((a&&&b&&&d)|||c),
   (((a&&&b)|||d)&&&c),
   (((a|||b)&&&d)|||c),
   ((a|||b|||d)&&&c),
   (((a&&&d)|||b)&&&c),
   (((a|||d)&&&b)|||c),
   (((b&&&d)|||a)&&&c),
   (((b|||d)&&&a)|||c),
   ((a&&&b)|||(c&&&d)),
   ((c|||d)&&&a&&&b),
   ((c&&&d)|||a|||b),
   ((a|||b)&&&(c|||d)),
   ((a&&&c&&&d)|||b),
   (((a&&&c)|||d)&&&b),
   (((a|||c)&&&d)|||b),
   ((a|||c|||d)&&&b),
   (((a&&&d)|||c)&&&b),
   (((a|||d)&&&c)|||b),
   (((c&&&d)|||a)&&&b),
   (((c|||d)&&&a)|||b),
   ((b&&&c&&&d)|||a),
   (((b&&&c)|||d)&&&a),
   (((b|||c)&&&d)|||a),
   ((b|||c|||d)&&&a),
   (((b&&&d)|||c)&&&a),
   (((b|||d)&&&c)|||a),
   (((c&&&d)|||b)&&&a),
   (((c|||d)&&&b)|||a)].all zz11n1
private theorem zz11n4 (a b c : Nat) : a &&& (b &&& c) = b &&& (a &&& c) := by
  rw [←Nat.and_assoc,Nat.and_comm a b,Nat.and_assoc]
private theorem zz11n5 (a b c : Nat) : a ||| (b ||| c) = b ||| (a ||| c) := by
  rw [←Nat.or_assoc,Nat.or_comm a b,Nat.or_assoc]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zz11n6 (a b c d : Nat) (ok : zz11n3 a b c d = true) :
    zz11n2 3 [a,b,c,d] = true := by
  simp only [zz11n3,List.all_cons,List.all_nil,Bool.and_eq_true, and_true,
    Nat.and_assoc,zz11n4,Nat.and_comm,Nat.or_assoc,zz11n5,Nat.or_comm] at ok
  rcases ok with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51⟩
  simp only [zz11n2,pairs,pick,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.all_cons,List.all_nil,Bool.and_true,Nat.and_assoc,zz11n4,Nat.and_comm,
    Nat.or_assoc,zz11n5,Nat.or_comm,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51]
  all_goals rfl
private def zz11n7 : List Nat → Bool
  | [a,b,c,d] => zz11n3 a b c d
  | ws => zz11n2 3 ws
private def zz11n8 : Nat → List Nat → Bool
  | 0, ws => zz11n7 ws
  | k+1, ws => (pairs ws).all fun (a,b,rest) =>
      zz11n8 k ((a &&& b)::rest) && zz11n8 k ((a ||| b)::rest)
private theorem zz11n9 (k : Nat) (ws : List Nat) : zz11n8 k ws = true →
    zz11n2 (k+3) ws = true := by
  induction k generalizing ws with
  | zero =>
    intro ok
    change zz11n7 ws=true at ok
    unfold zz11n7 at ok
    split at ok
    · exact zz11n6 _ _ _ _ ok
    · exact ok
  | succ k ih =>
    intro ok
    apply List.all_eq_true.mpr
    rintro ⟨a,b,rest⟩ hm
    obtain ⟨p,q⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok _ hm)
    exact Bool.and_eq_true_iff.mpr ⟨ih _ p,ih _ q⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem zz11n10 : zz11n8 2 (leaves.map UInt64.toNat) = true := by decide +kernel
theorem checkFast : zz11n2 5 (leaves.map UInt64.toNat) = true :=
  zz11n9 2 _ zz11n10
private theorem zz11n11 (f : α → β) (ws : List α) :
    (pick ws).map (fun p => (f p.1, p.2.map f)) = pick (ws.map f) := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    simp only [pick,List.map_cons,List.map_map,Function.comp_def, ←ih]
private theorem zz11n12 (f : α → β) (ws : List α) :
    (pairs ws).map (fun p => (f p.1, f p.2.1, p.2.2.map f)) = pairs (ws.map f) := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    simp only [pairs,List.map_cons,List.map_append,List.map_map,Function.comp_def]
    rw [←zz11n11 f xs,←ih]
    simp only [List.map_map,Function.comp_def]
private theorem zz11n13 {n ws x} (proof : Built n ws x) :
    zz11n2 n (ws.map UInt64.toNat) = true → zz11n1 x.toNat = true := by
  induction proof with
  | done hx => exact fun h => List.all_eq_true.mp h _ (List.mem_map.mpr ⟨_,hx,rfl⟩)
  | @merge n ws zs x step later ih =>
    intro check
    obtain ⟨⟨a,b,rest⟩,hm,next⟩ := List.mem_flatMap.mp step
    have member : (a.toNat,b.toNat,rest.map UInt64.toNat) ∈ pairs (ws.map UInt64.toNat) := by
      rw [←zz11n12 UInt64.toNat]
      exact List.mem_map.mpr ⟨(a,b,rest),hm,rfl⟩
    have good := Bool.and_eq_true_iff.mp (List.all_eq_true.mp check _ member)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at next
    rcases next with rfl | rfl
    · exact ih (by simpa only [List.map_cons,UInt64.toNat_and] using good.1)
    · exact ih (by simpa only [List.map_cons,UInt64.toNat_or] using good.2)
private theorem zz11n14 (x g f n ef en : UInt64) :
    zz11n0 x.toNat g.toNat f.toNat n.toNat ef.toNat en.toNat =
      (x == g || ((x &&& f) != ef && (x &&& n) != en)) := by
  have eqb (v w : UInt64) : (v.toNat == w.toNat) = (v == w) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, UInt64.toNat_inj]
  simp only [zz11n0,←UInt64.toNat_and,bne,eqb]
private theorem zz11n15 (x : Table) :
    zz11n1 x.toNat = directedPairs.all (goodPair x) := by
  change (zz11n0 x.toNat (0xfeeefcccfaaaf000 : UInt64).toNat (0xfefcfaf0eeccaa00 : UInt64).toNat (0x0103050f113355ff : UInt64).toNat (0xfeecf8c0ea88a000 : UInt64).toNat (0x0002040c10225000 : UInt64).toNat &&
      (zz11n0 x.toNat (0xfefaeeaafcf0cc00 : UInt64).toNat (0xfefcfaf0eeccaa00 : UInt64).toNat (0x0103050f113355ff : UInt64).toNat (0xfef8eaa0ecc08800 : UInt64).toNat (0x0002040a10304400 : UInt64).toNat &&
      (zz11n0 x.toNat (0xfefcfaf0eeccaa00 : UInt64).toNat (0xfeeefcccfaaaf000 : UInt64).toNat (0x0111033305550fff : UInt64).toNat (0xfeecf8c0ea88a000 : UInt64).toNat (0x0010023004440a00 : UInt64).toNat &&
      (zz11n0 x.toNat (0xfefaeeaafcf0cc00 : UInt64).toNat (0xfeeefcccfaaaf000 : UInt64).toNat (0x0111033305550fff : UInt64).toNat (0xfeeaec88f8a0c000 : UInt64).toNat (0x0010022204500c00 : UInt64).toNat &&
      (zz11n0 x.toNat (0xfefcfaf0eeccaa00 : UInt64).toNat (0xfefaeeaafcf0cc00 : UInt64).toNat (0x01051155030f33ff : UInt64).toNat (0xfef8eaa0ecc08800 : UInt64).toNat (0x00041050020c2200 : UInt64).toNat &&
      (zz11n0 x.toNat (0xfeeefcccfaaaf000 : UInt64).toNat (0xfefaeeaafcf0cc00 : UInt64).toNat (0x01051155030f33ff : UInt64).toNat (0xfeeaec88f8a0c000 : UInt64).toNat (0x00041044020a3000 : UInt64).toNat &&
      (true))))))) = _
  simp only [zz11n14]
  rfl
theorem checked_nat_directed {x : Table} (built : Built 5 leaves x) :
    directedPairs.all (goodPair x) = true :=
  (zz11n15 x).symm.trans (zz11n13 built checkFast)
end CyclicMatchings.ReadOnce
namespace L652
namespace RO
open CyclicMatchings.ReadOnce
theorem prior_bound (g : LogicalGate) (n : Finset Word) : (prior g n).card ≤ n.card+1 := by
  by_cases hg : g.out ∈ n
  · have hp := Finset.card_pos.mpr ⟨_,hg⟩
    have he := Finset.card_erase_of_mem hg
    have hu := Finset.card_union_le (n.erase g.out) (sources g)
    have hs := sources_small g
    simp only [prior,hg,ite_true]
    omega
  · simp [prior,hg]
private theorem zz12n0 {a b : Word} {s : Finset Word}
    (h : (insert a (insert b s)).card = s.card+2) : a ≠ b ∧ a ∉ s ∧ b ∉ s := by
  have bnd := Finset.card_insert_le b s
  constructor
  · intro e
    subst b
    simp only [Finset.insert_idem] at h
    omega
  constructor
  · intro ha
    rw [Finset.insert_eq_of_mem (Finset.mem_insert.mpr (Or.inr ha))] at h
    omega
  · intro hb
    rw [Finset.insert_eq_of_mem hb] at h
    have bnd' := Finset.card_insert_le a s
    omega
theorem tight_gate (g : LogicalGate) (n : Finset Word) (tight : (prior g n).card = n.card+1) :
    ∃ a b : Word, ∃ j : Bool,
      g.out ∈ n ∧ a ≠ b ∧ a ∉ n.erase g.out ∧ b ∉ n.erase g.out ∧
      prior g n = insert a (insert b (n.erase g.out)) ∧
      (UInt64.ofBitVec g.out) = CyclicMatchings.ReadOnce.combine j (UInt64.ofBitVec a) (UInt64.ofBitVec b) := by
  by_cases hg : g.out ∈ n
  · have hp := Finset.card_pos.mpr ⟨_,hg⟩
    have he := Finset.card_erase_of_mem hg
    cases g with
    | neg a =>
      simp only [prior,hg,ite_true,sources,Finset.union_singleton] at tight
      have h := Finset.card_insert_le a (n.erase (LogicalGate.neg a).out)
      omega
    | meet a b | join a b =>
      simp only [prior,hg,ite_true,sources,Finset.union_insert,Finset.union_singleton] at tight ⊢
      have hh := zz12n0 (a := a) (b := b) (s := n.erase _) (tight.trans (by omega))
      first | exact ⟨a,b,false,trivial,hh.1,hh.2.1,hh.2.2,rfl,rfl⟩
            | exact ⟨a,b,true,trivial,hh.1,hh.2.1,hh.2.2,rfl,rfl⟩
  · simp [prior,hg] at tight
theorem tight_build (gs : List LogicalGate) (t : Word)
    (tight : (demand gs {t}).card = gs.length+1) (ws : List UInt64)
    (perm : ((demand gs {t}).toList.map UInt64.ofBitVec).Perm ws) :
    CyclicMatchings.ReadOnce.Built gs.length ws (UInt64.ofBitVec t) := by
  induction gs generalizing ws with
  | nil =>
    exact .done (perm.mem_iff.mp (List.mem_map.mpr ⟨t,by simp [demand],rfl⟩))
  | cons g gs ih =>
    let n := demand gs {t}
    have ht : (prior g n).card = gs.length+2 := tight
    have bnd := demand_card gs {t}
    have bnd' := cost_le_length gs {t}
    simp only [Finset.card_singleton] at bnd
    have bnd2 := prior_bound g n
    have sat : n.card = gs.length+1 := by dsimp [n] at *; omega
    obtain ⟨a,b,j,hg,hab,ha,hb,he,hval⟩ := tight_gate g n (by omega)
    let tail := (n.erase g.out).toList
    have ht₀ : (a :: b :: tail).Nodup := by simp [tail,hab,ha,hb,Finset.nodup_toList]
    have hperm : (a :: b :: tail).Perm (demand (g::gs) {t}).toList := by
      apply List.perm_of_nodup_nodup_toFinset_eq ht₀ (Finset.nodup_toList _)
      change (a :: b :: tail).toFinset = (prior g n).toList.toFinset
      simp [he,tail]
    have hout : (g.out :: tail).Perm n.toList := by
      apply List.perm_of_nodup_nodup_toFinset_eq _ (Finset.nodup_toList _)
      · simp [tail,hg]
      · simp [tail,Finset.nodup_toList]
    obtain ⟨zs,hn,hp⟩ := next_complete j ((hperm.map UInt64.ofBitVec).trans perm)
    apply CyclicMatchings.ReadOnce.Built.merge hn
    rw [←hval] at hp
    exact ih sat zs ((hout.symm.map UInt64.ofBitVec).trans hp)
end RO
end L652
namespace L652
open CyclicMatchings.ReadOnce (leaves matching checked_nat_directed goodPair directedPairs)
def matchWord (k : Fin 3) : Word := (matching k.val).toBitVec
def domainWord (k : Fin 3) (b : Bool) : Word := if b then matchWord k else ~~~(matchWord k)
def equalOn (m a b : Word) : Prop := ∀ i : Fin 64, m.getLsbD i.val = true →
  a.getLsbD i.val = b.getLsbD i.val
def flipIndex (r : Fin 64) (k : Fin 6) : Fin 64 :=
  ((BitVec.ofFin r : BitVec 6) ^^^ (1 <<< k.val)).toFin
def differsAt (m t : Word) (k : Fin 6) (r : Fin 64) : Bool :=
  let s := flipIndex r k
  m.getLsbD r.val && m.getLsbD s.val && (t.getLsbD r.val != t.getLsbD s.val)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem essential_rows : ∀ (f j : Fin 3), f ≠ j → ∀ (b : Bool) (k : Fin 6),
    ∃ r : Fin 64, differsAt (domainWord f b) (matchWord j) k r = true := by decide +kernel
theorem flip_agrees : ∀ (k : Fin 6) (r : Fin 64),
    ((rawWords.erase (rawWords.getD k.val 0)).all (fun w =>
      w.getLsbD r.val == w.getLsbD (flipIndex r k).val)) = true := by decide +kernel
theorem raw_required {m t : Word} (f j : Fin 3) (neq : f ≠ j) (b : Bool)
    (hm : m = domainWord f b) (ht : equalOn m t (matchWord j))
    {features : Finset Word} (within : features ⊆ rawWords.toFinset)
    (det : Determines m features t) : features = rawWords.toFinset := by
  subst m
  apply Finset.Subset.antisymm within
  intro x hx
  have mem := List.mem_toFinset.mp hx
  obtain ⟨idx,hidx,eq⟩ := List.mem_iff_getElem.mp mem
  have hi : idx < 6 := hidx
  let k : Fin 6 := ⟨idx,hi⟩
  have he : rawWords.getD k.val 0 = x := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hidx]
    exact eq
  by_contra missed
  obtain ⟨r,delta⟩ := essential_rows f j neq b k
  simp only [differsAt,Bool.and_eq_true,bne_iff_ne] at delta
  have ag : agree features r (flipIndex r k) := by
    intro y hy
    have diff : y ≠ rawWords.getD k.val 0 := by
      intro same
      exact missed ((same.trans he) ▸ hy)
    exact beq_iff_eq.mp (List.all_eq_true.mp (flip_agrees k r) y
      ((List.mem_erase_of_ne diff).mpr (List.mem_toFinset.mp (within hy))))
  exact delta.2 ((ht r delta.1.1).symm.trans ((det r (flipIndex r k) delta.1.1 delta.1.2 ag).trans
    (ht (flipIndex r k) delta.1.2)))
theorem demand_full {gs : List LogicalGate} {t : Word}
    (ok : scheduled rawWords.toFinset gs) (has : t ∈ availableAfter rawWords.toFinset gs)
    (f j : Fin 3) (neq : f ≠ j) (b : Bool) (val : equalOn (domainWord f b) t (matchWord j)) :
    demand gs {t} = rawWords.toFinset := by
  apply raw_required f j neq b rfl val (demand_available ok (by simpa using has))
  intro i k _ _ h
  exact agree_demand gs {t} h t (by simp)
theorem equalOn_and {m x y : Word} (h : equalOn m x y) : x &&& m = y &&& m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  cases e : m.getLsbD i with
  | false => simp
  | true => simp [h ⟨i,hi⟩ e]
theorem five_extends {gs : List LogicalGate} {t : Word}
    (ok : scheduled rawWords.toFinset gs) (has : t ∈ availableAfter rawWords.toFinset gs)
    (f j : Fin 3) (neq : f ≠ j) (b : Bool) (val : equalOn (domainWord f b) t (matchWord j))
    (small : gs.length ≤ 5) : t = matchWord j := by
  have all := demand_full ok has f j neq b val
  have count : (demand gs {t}).card = 6 := by rw [all]; decide
  have db := demand_card gs {t}
  have cb := cost_le_length gs {t}
  simp only [Finset.card_singleton] at db
  have len : gs.length=5 := by omega
  have nd : rawWords.Nodup := by decide
  have perm : ((demand gs {t}).toList.map UInt64.ofBitVec).Perm leaves := by
    rw [all]
    exact (List.toFinset_toList nd).map UInt64.ofBitVec
  have built := RO.tight_build gs t (by omega) leaves perm
  rw [len] at built
  have pair : (f.val,j.val) ∈ directedPairs := by
    exact (by decide : ∀ f j : Fin 3, f ≠ j → (f.val,j.val) ∈ directedPairs) f j neq
  have bonus := List.all_eq_true.mp (checked_nat_directed built) _ pair
  simp only [goodPair,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at bonus
  rcases bonus with yes | bad
  · exact congrArg UInt64.toBitVec yes
  · have h := equalOn_and val
    cases b
    · exact False.elim (bad.2 (UInt64.toBitVec_inj.mp h))
    · exact False.elim (bad.1 (UInt64.toBitVec_inj.mp h))
end L652
namespace L652
def makeWord (f : Fin 64 → Bool) : Word :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)
theorem makeWord_bit (f : Fin 64 → Bool) (r : Fin 64) : (makeWord f).getLsbD r.val = f r := by
  simp only [makeWord,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos r.isLt]; rfl
abbrev SymIndex := Fin 36
def coordMap (s : SymIndex) (j : Fin 6) : Fin 6 :=
  let v := j.val % 3
  let rev := if s.val / 9 % 2 = 0 then v else (3-v)%3
  let shift := if j.val < 3 then s.val % 3 else s.val / 3 % 3
  let side := if s.val / 18 = 0 then j.val / 3 else 1 - j.val / 3
  ⟨3*side + (rev + shift)%3, by dsimp [side]; split <;> have hj := j.isLt <;> omega⟩
def rowMap (s : SymIndex) (r : Fin 64) : Fin 64 :=
  let bits := List.ofFn (fun j : Fin 6 => r.val.testBit (coordMap s j).val)
  let w := BitVec.ofBoolListLE bits
  ⟨w.toNat,by have h := w.isLt; simpa [w,bits] using h⟩
def relabel (s : SymIndex) (w : Word) : Word := makeWord (fun r => w.getLsbD (rowMap s r).val)
theorem relabel_bit (s : SymIndex) (w : Word) (r : Fin 64) :
    (relabel s w).getLsbD r.val = w.getLsbD (rowMap s r).val := makeWord_bit _ _
theorem relabel_eq (s : SymIndex) {a b : Word} (h : ∀ r : Fin 64,
    (relabel s a).getLsbD r.val = b.getLsbD r.val) : relabel s a = b :=
  BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i,hi⟩)
theorem rowMap_bit (s : SymIndex) (r : Fin 64) (j : Fin 6) :
    (rowMap s r).val.testBit j.val = r.val.testBit (coordMap s j).val := by
  change (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 6 => r.val.testBit (coordMap s k).val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos j.isLt]; rfl
set_option maxRecDepth 10000 in
theorem inverse_coord : ∀ s : SymIndex, ∃ z : SymIndex, ∀ j : Fin 6,
    coordMap z (coordMap s j) = j := by decide +kernel
theorem rowMap_surj (s : SymIndex) : Function.Surjective (rowMap s) := by
  obtain ⟨q,hq⟩ := inverse_coord s
  intro r
  refine ⟨rowMap q r,Fin.ext (Nat.eq_of_testBit_eq (fun k => ?_))⟩
  by_cases hk : k < 6
  · simpa only [rowMap_bit _ _ (⟨k,hk⟩ : Fin 6),rowMap_bit,hq] using
      (rowMap_bit s (rowMap q r) ⟨k,hk⟩)
  · have left := (rowMap s (rowMap q r)).isLt
    have right := r.isLt
    have bnd : 64 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ k)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le left bnd),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le right bnd)]
theorem relabel_injective (s : SymIndex) : Function.Injective (relabel s) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨r,hr⟩ := rowMap_surj s ⟨i,hi⟩
  simpa only [relabel_bit,hr] using congrArg (fun w : Word => w.getLsbD r.val) h
def mapGate (s : SymIndex) : LogicalGate → LogicalGate
  | .neg a => .neg (relabel s a)
  | .meet a b => .meet (relabel s a) (relabel s b)
  | .join a b => .join (relabel s a) (relabel s b)
theorem mapGate_out (s : SymIndex) (g : LogicalGate) : relabel s g.out = (mapGate s g).out := by
  apply relabel_eq
  intro r
  cases g <;> simp only [mapGate,LogicalGate.out,relabel_bit,BitVec.getLsbD_and,BitVec.getLsbD_or,
    BitVec.getLsbD_not,r.isLt,(rowMap s r).isLt,decide_true,Bool.true_and]
theorem mapGate_args (s : SymIndex) (g : LogicalGate) :
    (mapGate s g).args = g.args.map (relabel s) := by cases g <;> rfl
theorem raw_bit : ∀ (j : Fin 6) (r : Fin 64),
    (rawWords.getD j.val 0).getLsbD r.val = r.val.testBit j.val := by decide +kernel
theorem relabel_raw (s : SymIndex) (j : Fin 6) :
    relabel s (rawWords.getD j.val 0) = rawWords.getD (coordMap s j).val 0 := by
  apply relabel_eq
  intro r
  simpa only [relabel_bit,raw_bit] using rowMap_bit s r j
end L652
namespace L652
def rawAt (j : Fin 6) := rawWords.getD j.val 0
def matchFrom (raw : Fin 6 → Word) (j : Fin 3) : Word :=
  (raw 0 &&& raw ⟨3+j.val,by omega⟩) |||
  (raw 1 &&& raw ⟨3+(j.val+1)%3,by omega⟩) |||
  (raw 2 &&& raw ⟨3+(j.val+2)%3,by omega⟩)
theorem matchFrom_eq : ∀ j, matchFrom rawAt j = matchWord j := by decide +kernel
theorem relabel_meet (s : SymIndex) (a b : Word) :
    relabel s (a &&& b) = relabel s a &&& relabel s b := mapGate_out s (.meet a b)
theorem relabel_join (s : SymIndex) (a b : Word) :
    relabel s (a ||| b) = relabel s a ||| relabel s b := mapGate_out s (.join a b)
theorem relabel_neg (s : SymIndex) (a : Word) : relabel s (~~~a) = ~~~(relabel s a) :=
  mapGate_out s (.neg a)
theorem relabel_zero (s : SymIndex) : relabel s 0 = 0 := by apply relabel_eq; intro r; rw [relabel_bit]; simp
theorem relabel_one (s : SymIndex) : relabel s (~~~(0 : Word)) = ~~~(0 : Word) := by rw [relabel_neg,relabel_zero]
theorem relabel_from (s : SymIndex) (k : Fin 3) :
    relabel s (matchWord k) = matchFrom (fun j => rawAt (coordMap s j)) k := by
  rw [←matchFrom_eq]
  have cv (j : Fin 6) : relabel s (rawAt j) = rawAt (coordMap s j) := relabel_raw s j
  simp only [matchFrom,relabel_join,relabel_meet,cv]
set_option maxRecDepth 10000 in
theorem all_matchings_preserved : ∀ s : SymIndex, ∀ k : Fin 3, ∃ j : Fin 3,
    matchFrom (fun i => rawAt (coordMap s i)) j = matchWord k := by decide +kernel
theorem matchings_survive (s : SymIndex) (k : Fin 3) :
    ∃ j : Fin 3, relabel s (matchWord j) = matchWord k := by
  obtain ⟨j,h⟩ := all_matchings_preserved s k
  exact ⟨j,(relabel_from s j).trans h⟩
theorem rawAt_mem (j : Fin 6) : rawAt j ∈ rawWords := by
  exact (by decide : ∀ j : Fin 6, rawAt j ∈ rawWords) j
theorem exists_rawAt (w : Word) (h : w ∈ rawWords) : ∃ j, rawAt j = w := by
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp h
  refine ⟨⟨k,hk⟩,?_⟩
  simp [rawAt,List.getD_eq_getElem?_getD,hk]
theorem mapped_raw : ∀ (s : SymIndex), (rawWords.map (relabel s)).Perm rawWords := by
  intro s
  have perm : ∀ s : SymIndex, ((List.finRange 6).map (fun i => rawAt (coordMap s i))).Perm rawWords :=
    by decide +kernel
  rw [show rawWords = (List.finRange 6).map rawAt by rfl,List.map_map]
  apply List.Perm.trans _ (perm s)
  apply List.Perm.of_eq
  apply List.map_congr_left
  intro i _
  exact relabel_raw s i
theorem perm_wires (s : SymIndex) (gs : List LogicalGate) :
    ((wiresOf gs).map (relabel s)).Perm (wiresOf (gs.map (mapGate s))) := by
  simp only [wiresOf,List.map_append,List.map_map]
  refine (mapped_raw s).append (List.Perm.of_eq ?_)
  exact List.map_congr_left (fun i _ => mapGate_out s i)
theorem relabel_history (s : SymIndex) {gs : List LogicalGate} (h : History gs) :
    History (gs.map (mapGate s)) := by
  induction h with
  | empty => exact .empty
  | @push gs g hist args fresh ih =>
    simp only [List.map_append,List.map_cons,List.map_nil]
    apply History.push ih
    · intro v hv
      rw [mapGate_args] at hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
      exact (perm_wires s gs).mem_iff.mp (List.mem_map.mpr ⟨a,args ha,rfl⟩)
    · rw [←mapGate_out]
      refine ⟨fun eq => fresh.1 (relabel_injective s (eq.trans (relabel_zero s).symm)),
        fun eq => fresh.2.1 (relabel_injective s (eq.trans (relabel_one s).symm)),?_⟩
      intro hv
      obtain ⟨a,ha,eq⟩ := List.mem_map.mp ((perm_wires s gs).mem_iff.mpr hv)
      exact fresh.2.2 ((relabel_injective s eq) ▸ ha)
theorem map_determines (s : SymIndex) {m t : Word} {pool : Finset Word} (det : Determines m pool t) :
    Determines (relabel s m) (pool.image (relabel s)) (relabel s t) := by
  intro i j hi hj ag
  simp only [relabel_bit] at hi hj ⊢
  apply det _ _ hi hj
  intro w hw
  simpa only [relabel_bit] using ag _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
end L652
namespace L652
theorem five_le_cone {gs : List LogicalGate} {t : Word}
    (ok : scheduled rawWords.toFinset gs) (ht : t ∈ availableAfter rawWords.toFinset gs)
    (f j : Fin 3) (neq : f ≠ j) (b : Bool) (val : equalOn (domainWord f b) t (matchWord j)) :
    5 ≤ (cone gs {t}).length := by
  obtain ⟨sub,has⟩ := slice_spec ok ht
  have h := demand_full sub has f j neq b val
  have card : (demand (cone gs {t}) {t}).card = 6 := by rw [h]; decide
  have cap := demand_card (cone gs {t}) {t}
  have costCap := cost_le_length (cone gs {t}) {t}
  simp only [Finset.card_singleton] at cap
  omega
theorem gatesFor_card {gs : List LogicalGate} {t : Word} (nodup : (gs.map LogicalGate.out).Nodup) :
    (gatesFor gs t).card = (cone gs {t}).length := by
  have hh := nodup.sublist ((cone_sublist gs {t}).map LogicalGate.out)
  simp [gatesFor,produced,List.toFinset_card_of_nodup hh]
theorem disjoint_extends {gs : List LogicalGate} {t u : Word}
    (ok : scheduled rawWords.toFinset gs) (nd : (gs.map LogicalGate.out).Nodup)
    (ht : t ∈ availableAfter rawWords.toFinset gs) (hu : u ∈ availableAfter rawWords.toFinset gs)
    (f j k : Fin 3) (nj : f ≠ j) (nk : f ≠ k) (b : Bool)
    (vt : equalOn (domainWord f b) t (matchWord j)) (vu : equalOn (domainWord f b) u (matchWord k))
    (dis : shared gs t u = ∅) (budget : gs.length ≤ 10) :
    gs.length = 10 ∧ t = matchWord j ∧ u = matchWord k := by
  have tj := five_le_cone ok ht f j nj b vt
  have uk := five_le_cone ok hu f k nk b vu
  have su : gatesFor gs t ∪ gatesFor gs u ⊆ produced gs :=
    Finset.union_subset (produced_mono (cone_sublist gs {t}).subset)
      (produced_mono (cone_sublist gs {u}).subset)
  have bound := Finset.card_le_card su
  have calcU := Finset.card_union_add_card_inter (gatesFor gs t) (gatesFor gs u)
  have empty : (gatesFor gs t ∩ gatesFor gs u).card = 0 := by change (shared gs t u).card=0; rw [dis]; rfl
  rw [empty,gatesFor_card nd,gatesFor_card nd] at calcU
  have size : (produced gs).card = gs.length := by
    simp only [produced,List.toFinset_card_of_nodup nd,List.length_map]
  have jt : (cone gs {t}).length ≤ 5 := by omega
  have kt : (cone gs {u}).length ≤ 5 := by omega
  exact ⟨by omega, five_extends (slice_spec ok ht).1 (slice_spec ok ht).2 f j nj b vt jt,
    five_extends (slice_spec ok hu).1 (slice_spec ok hu).2 f k nk b vu kt⟩
theorem last_gate_target {p : List LogicalGate} {g : LogicalGate} {t : Word}
    (unique : ((p++[g]).map LogicalGate.out).Nodup)
    (belongs : g.out ∈ gatesFor (p++[g]) t) : g.out = t := by
  have sub := cone_sublist (p++[g]) {t}
  obtain ⟨q,hq,hout⟩ := mem_produced.mp belongs
  have same := same_producer unique (sub.subset hq) (by simp : g ∈ p++[g]) hout
  subst q
  have endUse (gs : List LogicalGate) (avoid : g ∉ gs) (hg : g ∈ cone (gs++[g]) {t}) :
      g.out = t := by
    induction gs with
    | nil =>
      by_contra miss
      simp [cone,demand,miss] at hg
    | cons a gs ih =>
      have ne : g ≠ a := fun h => avoid (by simp [h])
      apply ih (fun h => avoid (List.mem_cons_of_mem _ h))
      simp only [List.cons_append,cone] at hg
      split at hg
      · exact (List.mem_cons.mp hg).resolve_left ne
      · exact hg
  have no : g ∉ p := by
    intro h
    have z : g.out ∉ p.map LogicalGate.out := by
      simp only [List.map_append,List.map_cons,List.map_nil,List.nodup_append] at unique
      intro hm
      exact unique.2.2 _ hm _ (by simp) rfl
    exact z (List.mem_map.mpr ⟨_,h,rfl⟩)
  exact endUse p no hq
theorem shared_lt {gs : List LogicalGate} {t u : Word} (unique : (gs.map LogicalGate.out).Nodup)
    (nonempty : gs ≠ []) (distinct : t ≠ u) : (shared gs t u).card < gs.length := by
  obtain ⟨p,g,rfl⟩ : ∃ p g, gs = p++[g] := ⟨gs.dropLast,gs.getLast nonempty,(List.dropLast_concat_getLast nonempty).symm⟩
  have size : (produced (p++[g])).card = (p++[g]).length := by
    simp only [produced,List.toFinset_card_of_nodup unique,List.length_map]
  have incl : shared (p++[g]) t u ⊆ produced (p++[g]) := fun v hv =>
    produced_mono (cone_sublist _ _).subset (Finset.mem_inter.mp hv).1
  rw [←size]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨incl,?_⟩
  intro all
  have yes : g.out ∈ shared (p++[g]) t u := all ▸ mem_produced.mpr ⟨g,by simp,rfl⟩
  obtain ⟨ht,hu⟩ := Finset.mem_inter.mp yes
  exact distinct ((last_gate_target unique ht).symm.trans (last_gate_target unique hu))
end L652
namespace L652
inductive BuiltFrom (raw : List Table) : List Op → List Table → Prop
  | start : BuiltFrom raw [] raw
  | snoc {p w} (prev : BuiltFrom raw p w) (g : Op) (valid : g.valid w.length)
      (fresh : ¬ Available w (g.value w)) :
      BuiltFrom raw (p ++ [g]) (w ++ [g.value w])
noncomputable def internal (raw wires : List Table) : Finset Table := by
  classical
  exact wires.toFinset \ insert zero (insert one raw.toFinset)
private theorem zz17n0 {raw w : List Table} {x : Table} :
    x ∈ internal raw w ↔ x ∈ w ∧ ¬ Available raw x := by
  classical
  simp [internal,Available]
theorem BuiltFrom.raw_subset {raw w p} (h : BuiltFrom raw p w) :
    ∀ v ∈ raw, v ∈ w := by
  induction h with
  | start => simp
  | snoc _ _ _ _ ih => exact fun v hv => List.mem_append_left _ (ih v hv)
theorem BuiltFrom.card {raw w p} (h : BuiltFrom raw p w) :
    (internal raw w).card = p.length := by
  classical
  induction h with
  | start => simp [internal]; intro x hx; simp [hx]
  | @snoc p w old g valid fresh ih =>
    let v := g.value w
    have nf : ¬ Available raw v := by
      rintro (h | h | h)
      · exact fresh (Or.inl h)
      · exact fresh (Or.inr (Or.inl h))
      · exact fresh (Or.inr (Or.inr (old.raw_subset _ h)))
    have nmem : v ∉ internal raw w := by
      intro hm; exact fresh (Or.inr (Or.inr (zz17n0.mp hm).1))
    have eq : internal raw (w ++ [v]) = insert v (internal raw w) := by
      ext x; simp only [zz17n0,List.mem_append,List.mem_singleton,Finset.mem_insert]
      grind
    change (internal raw (w ++ [v])).card = _
    simp [eq,Finset.card_insert_of_notMem nmem,ih]
end L652
namespace L652
inductive Cmd where
  | lit (b : Bool)
  | copy (j : Nat)
  | gate (g : Op)
  deriving DecidableEq, Repr
def Cmd.refs : Cmd → List Nat
  | .lit _ => []
  | .copy j | .gate (.neg j) => [j]
  | .gate (.meet i j) | .gate (.join i j) => [i,j]
def Cmd.act (get : Nat → Bool) : Cmd → Bool
  | .lit b => b
  | .copy i => get i
  | .gate (.neg i) => !get i
  | .gate (.meet i j) => get i && get j
  | .gate (.join i j) => get i || get j
private theorem zz18n0 {A B : Nat → Bool} (c : Cmd)
    (h : ∀ j ∈ c.refs, A j = B j) : c.act A = c.act B := by
  cases c with
  | lit b => rfl
  | copy j => exact h j (by simp [Cmd.refs])
  | gate g => cases g <;> simp_all [Cmd.act,Cmd.refs]
abbrev Graph := Nat → Cmd
def wire (raw : List Table) (P : Graph) (x : Row) (i : Nat) : Bool :=
  if i < raw.length then (raw.getD i zero) x
  else (P i).act (fun j => if _h : j < i then wire raw P x j else false)
termination_by i
theorem wire_local {raw P Q x i} (op : P i = Q i)
    (args : ∀ j ∈ (P i).refs, j < i → wire raw P x j = wire raw Q x j) :
    wire raw P x i = wire raw Q x i := by
  rw [wire.eq_def raw P x i, wire.eq_def raw Q x i]
  split
  · rfl
  · rw [← op]
    apply zz18n0
    intro j hj
    split <;> simp_all
theorem wire_outside {raw P Q x} (S : Nat → Prop)
    (ops : ∀ i, ¬ S i → P i = Q i)
    (closed : ∀ i, ¬ S i → ∀ j ∈ (P i).refs, j < i → ¬ S j) :
    ∀ i, ¬ S i → wire raw P x i = wire raw Q x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    apply wire_local (ops i hi)
    intro j hj lt
    exact ih j lt (closed i hi j hj lt)
def bop (join : Bool) (a b : Nat) : Cmd :=
  .gate (if join then .join a b else .meet a b)
def combine (join a b : Bool) : Bool := if join then a || b else a && b
theorem wire_bop {raw P x i a b u} (internal : raw.length ≤ i)
    (ha : a < i) (hb : b < i) (kind : P i = bop u a b ∨ P i = bop u b a) :
    wire raw P x i = combine u (wire raw P x a) (wire raw P x b) := by
  rw [wire]
  rcases kind with e | e <;> cases u <;>
    simp [Nat.not_lt.mpr internal,e,bop,Cmd.act,ha,hb,combine,Bool.and_comm,Bool.or_comm]
def pin (P : Graph) (S : Nat → Prop) [DecidablePred S] (v : Bool) : Graph :=
  fun i => if S i then .lit v else P i
end L652
namespace L652
def wireTable (raw : List Table) (P : Graph) (i : Nat) : Table := fun x => wire raw P x i
def Cmd.paid : Cmd → Bool
  | .gate _ => true
  | _ => false
def paidIndices (base n : Nat) (P : Graph) : Finset Nat :=
  (Finset.range n).filter (fun j => (P (base+j)).paid)
private theorem zz19n0 (base n : Nat) (P : Graph) :
    (paidIndices base (n+1) P).card =
      (paidIndices base n P).card + if (P (base+n)).paid then 1 else 0 := by
  cases h : (P (base+n)).paid <;>
    simp [paidIndices, Finset.range_add_one, Finset.filter_insert, h]
def fetch (raw : List Table) (P : Graph) (i j : Nat) : Table :=
  if j < i then wireTable raw P j else zero
private theorem zz19n1 {raw P i z} (prev : ∀ j < i, Available z (wireTable raw P j))
    (j : Nat) : Available z (fetch raw P i j) := by
  unfold fetch
  split
  · apply prev; assumption
  · exact Or.inl rfl
private theorem zz19n2 {raw P i z} (hi : raw.length ≤ i)
    (prev : ∀ j < i, Available z (wireTable raw P j)) :
    Possible z (wireTable raw P i) := by
  have av := zz19n1 prev
  have hf (x : Row) : wireTable raw P i x = (P i).act (fun j => fetch raw P i j x) := by
    rw [wireTable, wire.eq_def, if_neg (by omega)]
    congr 1
    funext j
    by_cases h : j < i <;> simp [fetch,h,wireTable,zero]
  cases hg : P i with
  | lit b =>
    cases b
    · exact Or.inl (Or.inl (by funext x; simp [hf,hg,Cmd.act,zero]))
    · exact Or.inl (Or.inr (Or.inl (by funext x; simp [hf,hg,Cmd.act,one])))
  | copy j =>
    have eq : wireTable raw P i = fetch raw P i j := by funext x; simp [hf,hg,Cmd.act]
    exact eq ▸ Or.inl (av j)
  | gate g =>
    cases g with
    | neg j =>
      have eq : wireTable raw P i = tnot (fetch raw P i j) := by
        funext x; simp [hf,hg,Cmd.act,tnot]
      rw [eq]; exact neg_possible (av j)
    | meet a b =>
      have eq : wireTable raw P i = tand (fetch raw P i a) (fetch raw P i b) := by
        funext x; simp [hf,hg,Cmd.act,tand]
      rw [eq]; exact binary_possible (av a) (av b) false
    | join a b =>
      have eq : wireTable raw P i = tor (fetch raw P i a) (fetch raw P i b) := by
        funext x; simp [hf,hg,Cmd.act,tor]
      rw [eq]; exact binary_possible (av a) (av b) true
private theorem zz19n3 {raw P i z} (hi : raw.length ≤ i)
    (prev : ∀ j < i, Available z (wireTable raw P j)) (h : (P i).paid = false) :
    Available z (wireTable raw P i) := by
  cases hg : P i with
  | lit b =>
    have eq : wireTable raw P i = fun _ => b := by
      funext x; rw [wireTable,wire.eq_def,if_neg (by omega),hg]; rfl
    rw [eq]; cases b
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | copy j =>
    have eq : wireTable raw P i = fetch raw P i j := by
      funext x; rw [wireTable,wire.eq_def,if_neg (by omega),hg]
      by_cases h : j<i <;> simp [Cmd.act,fetch,h,wireTable,zero]
    rw [eq]; exact zz19n1 prev j
  | gate g => simp [hg,Cmd.paid] at h
theorem compressGraph (raw : List Table) (P : Graph) (n : Nat) :
    ∃ q z, BuiltFrom raw q z ∧ q.length ≤ (paidIndices raw.length n P).card ∧
      ∀ j < raw.length+n, Available z (wireTable raw P j) := by
  classical
  induction n with
  | zero =>
    refine ⟨[],raw,.start,by simp,?_⟩
    intro j hj
    have hj' : j < raw.length := by omega
    have eq : wireTable raw P j = raw.getD j zero := by
      funext x; simp [wireTable,wire.eq_def raw P x j,hj']
    rw [eq]
    right; right
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
    exact List.getElem_mem ..
  | succ n ih =>
    obtain ⟨q,z,hq,hlen,hcovers⟩ := ih
    let i := raw.length+n
    have hi : raw.length ≤ i := by dsimp [i]; omega
    by_cases avail : Available z (wireTable raw P i)
    · refine ⟨q,z,hq,by rw [zz19n0]; omega,?_⟩
      intro j hj
      by_cases he : j = i
      · simpa [he] using avail
      · apply hcovers; dsimp [i] at he; omega
    · have paid : (P i).paid = true := by
        cases hv : (P i).paid
        · exact False.elim (avail (zz19n3 hi hcovers hv))
        · rfl
      obtain ⟨g,hg,ge⟩ := (zz19n2 hi hcovers).resolve_left avail
      refine ⟨_,_,.snoc hq g hg (by simpa [ge] using avail),?_,?_⟩
      · rw [zz19n0]
        change _ ≤ _ + if (P i).paid then 1 else 0
        simp [paid,hlen]
      · intro j hj
        by_cases he : j=i
        · right; right; simp [he,ge]
        · have old := hcovers j (by dsimp [i] at he; omega)
          rcases old with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (List.mem_append_left _ h))
theorem cost_of_exempt {base n : Nat} {P : Graph} (free : Finset Nat)
    (bound : free ⊆ Finset.range n)
    (unpaid : ∀ j ∈ free, (P (base+j)).paid = false) :
    (paidIndices base n P).card + free.card ≤ n := by
  have disj : Disjoint (paidIndices base n P) free := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    have h := (Finset.mem_filter.mp hj).2
    simp [unpaid j hj'] at h
  have subset : paidIndices base n P ∪ free ⊆ Finset.range n := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact bound h
  simpa [Finset.card_union_of_disjoint disj] using Finset.card_le_card subset
end L652
namespace L652
def graphOf (base : Nat) (p : List Op) : Graph := fun i =>
  match p[i-base]? with
  | some g => .gate g
  | none => .lit false
theorem Built.wire_count {p w} (built : Built p w) : w.length = inputTables.length + p.length := by
  induction built with
  | start => simp
  | snoc _ _ _ _ ih => simp [ih,Nat.add_assoc]
private theorem zz20n0 (raw : List Table) (P Q : Graph) (x : Row) (cut : Nat)
    (same : ∀ j, raw.length ≤ j → j < cut → P j=Q j) :
    ∀ j < cut, wire raw P x j = wire raw Q x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases inp : j < raw.length
    · rw [wire.eq_def raw P x j,wire.eq_def raw Q x j]
      simp [inp]
    · apply wire_local (same j (by omega) hj)
      intro i hi hlt; exact ih i hlt (by omega)
theorem Built.indexed {p w} (built : Built p w) :
    ∀ i < w.length, ∀ x, wire inputTables (graphOf inputTables.length p) x i =
      (w.getD i zero) x := by
  induction built with
  | start =>
    intro i hi x
    rw [wire.eq_def]
    simp [hi]
  | @snoc p w old g valid fresh ih =>
    let raw := inputTables
    let P := graphOf raw.length p
    let Q := graphOf raw.length (p++[g])
    have size : w.length = raw.length+p.length := old.wire_count
    have earlier (j : Nat) (hl : j < w.length) (x : Row) :
        wire raw Q x j = (w.getD j zero) x := by
      have eq : wire raw Q x j = wire raw P x j := by
        apply zz20n0 raw Q P x w.length _ j hl
        intro k lo hi
        have hk : k-raw.length < p.length := by omega
        simp [Q,P,graphOf,List.getElem?_append_left hk]
      exact eq.trans (ih j hl x)
    have code : Q w.length = .gate g := by
      simp [Q,graphOf,size]
    intro i hi x
    change wire raw Q x i = _
    by_cases hl : i < w.length
    · rw [earlier i hl x]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hl]
    · have he : i=w.length := by simp at hi; omega
      subst i
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl w.length),
        Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
      rw [wire.eq_def,if_neg (by omega),code]
      cases g with
      | neg i =>
        change i<w.length at valid
        simp only [Cmd.act,dif_pos valid,Op.value,tnot,earlier i valid x]
      | meet i j =>
        obtain ⟨h1,h2,_⟩ := valid
        simp only [Cmd.act,dif_pos h1,dif_pos h2,Op.value,tand,earlier i h1 x,earlier j h2 x]
      | join i j =>
        obtain ⟨h1,h2,_⟩ := valid
        simp only [Cmd.act,dif_pos h1,dif_pos h2,Op.value,tor,earlier i h1 x,earlier j h2 x]
theorem Built.output_index {p w} (built : Built p w) {v : Table} (hv : v ∈ w) :
    ∃ i, i < inputTables.length+p.length ∧
      (fun x => wire inputTables (graphOf inputTables.length p) x i) = v := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hv
  refine ⟨i,by simpa [← built.wire_count] using hi,?_⟩
  funext x
  rw [built.indexed i hi]
  simp [List.getD_eq_getElem?_getD,hi,he]
end L652
namespace L652
theorem BuiltFrom.toBuilt {q z} (h : BuiltFrom inputTables q z) : Built q z := by
  induction h with
  | start => exact .start
  | snoc _ g a b ih => exact .snoc ih g a b
def ResidualExtends (k : Nat) (F A B : Table) (bit : Bool) : Prop :=
  ∀ q z, Built q z → q.length ≤ k → ∀ U V,
    Available z U → Available z V →
    (∀ x, F x = bit → U x = A x ∧ V x = B x) →
    U = A ∧ V = B
def marked (base : Nat) (offsets : Finset Nat) (i : Nat) : Prop :=
  base ≤ i ∧ i-base ∈ offsets
instance (base : Nat) (offsets : Finset Nat) : DecidablePred (marked base offsets) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))
end L652
namespace L652
def ResidualFloor (k : Nat) (F A B : Table) (bit : Bool) : Prop :=
  ∀ q z, Built q z → ∀ U V, Available z U → Available z V →
    (∀ x, F x = bit → U x = A x ∧ V x = B x) → k ≤ q.length
private def zz22n0 (u : Bool) (a b : Nat) (va vb : Option Bool) : Cmd :=
  match va,vb with
  | some v, some w => .lit (combine u v w)
  | some v, none => if v=u then .lit u else .copy b
  | none, some v => if v=u then .lit u else .copy a
  | none, none => bop u a b
def simplifyCmd (known : Nat → Option Bool) : Cmd → Cmd
  | .gate (.meet a b) => zz22n0 false a b (known a) (known b)
  | .gate (.join a b) => zz22n0 true a b (known a) (known b)
  | .gate (.neg j) => match known j with
    | some v => .lit (!v)
    | none => .gate (.neg j)
  | .copy j => match known j with
    | some v => .lit v
    | none => .copy j
  | other => other
private theorem zz22n1 (u : Bool) (a b : Nat) (known : Nat → Option Bool)
    (read : Nat → Bool) (ok : ∀ j v, known j = some v → read j=v) :
    (zz22n0 u a b (known a) (known b)).act read = combine u (read a) (read b) := by
  cases ha : known a with
  | some v =>
    have h := ok a v ha
    cases hb : known b with
    | some w => simp [zz22n0,Cmd.act,h,ok b w hb]
    | none => cases u <;> cases v <;> simp [zz22n0,Cmd.act,combine,h]
  | none =>
    cases hb : known b with
    | some v =>
      have h := ok b v hb
      cases u <;> cases v <;> simp [zz22n0,Cmd.act,combine,h]
    | none => cases u <;> rfl
theorem simplify_correct (c : Cmd) (known : Nat → Option Bool) (read : Nat → Bool)
    (ok : ∀ j v, known j = some v → read j=v) :
    (simplifyCmd known c).act read = c.act read := by
  cases c with
  | copy i =>
    cases hi : known i with
    | none => simp [simplifyCmd,hi]
    | some v => simp [simplifyCmd,hi,Cmd.act,ok i v hi]
  | lit b => rfl
  | gate g =>
    cases g with
    | meet a b => exact zz22n1 false a b known read ok
    | join a b => exact zz22n1 true a b known read ok
    | neg i =>
      cases h : known i with
      | none => simp [simplifyCmd,h]
      | some v => simp [simplifyCmd,h,Cmd.act,ok i v h]
private theorem zz22n2 (u : Bool) (a b : Nat) (ka kb : Option Bool)
    (h : ka.isSome ∨ kb.isSome) : (zz22n0 u a b ka kb).paid = false := by
  rcases ka with _ | (_|_) <;> rcases kb with _ | (_|_) <;> cases u <;>
    simp_all [zz22n0,Cmd.paid]
theorem simplify_unpaid (c : Cmd) (known : Nat → Option Bool)
    (h : ∃ j ∈ c.refs, (known j).isSome) : (simplifyCmd known c).paid = false := by
  cases c with
  | copy i => cases hi : known i <;> simp [simplifyCmd,hi,Cmd.paid]
  | lit b => rfl
  | gate g =>
    cases g with
    | meet a b =>
      apply zz22n2
      simpa [Cmd.refs] using h
    | join a b =>
      apply zz22n2
      simpa [Cmd.refs] using h
    | neg i =>
      have hi : (known i).isSome := by simpa [Cmd.refs] using h
      cases hv : known i <;> simp_all [simplifyCmd,Cmd.paid]
private theorem zz22n3 (u : Bool) (a b j : Nat) (ka kb : Option Bool)
    (h : j ∈ (zz22n0 u a b ka kb).refs) :
    (j=a ∧ ka=none) ∨ (j=b ∧ kb=none) := by
  rcases ka with _ | (_|_) <;> rcases kb with _ | (_|_) <;> cases u <;>
    simp_all [zz22n0,Cmd.refs,bop]
theorem simplify_refs {c : Cmd} {known : Nat → Option Bool} {j : Nat}
    (h : j ∈ (simplifyCmd known c).refs) : j ∈ c.refs ∧ known j = none := by
  cases c with
  | lit b => simp [simplifyCmd,Cmd.refs] at h
  | copy k =>
    cases hv : known k <;> simp_all [simplifyCmd,Cmd.refs]
  | gate g =>
    cases g with
    | neg k => cases hv : known k <;> simp_all [simplifyCmd,Cmd.refs]
    | meet a b =>
      obtain (⟨rfl,hv⟩ | ⟨rfl,hv⟩) := zz22n3 false a b j (known a) (known b) h <;>
        simp [Cmd.refs,hv]
    | join a b =>
      obtain (⟨rfl,hv⟩ | ⟨rfl,hv⟩) := zz22n3 true a b j (known a) (known b) h <;>
        simp [Cmd.refs,hv]
def clipped (known : Nat → Option Bool) (i j : Nat) : Option Bool :=
  if j < i then known j else some false
def simplifyGraph (P : Graph) (known : Nat → Option Bool) : Graph := fun i =>
  match known i with
  | some v => .lit v
  | none => simplifyCmd (clipped known i) (P i)
def Removable (P : Graph) (known : Nat → Option Bool) (i : Nat) : Prop :=
  (known i).isSome ∨ ∃ j ∈ (P i).refs, j < i ∧ (known j).isSome
theorem removable_unpaid (P : Graph) (known : Nat → Option Bool) (i : Nat)
    (h : Removable P known i) : ((simplifyGraph P known) i).paid = false := by
  cases hi : known i with
  | some v => simp [simplifyGraph,hi,Cmd.paid]
  | none =>
    obtain ⟨j,hj,lt,m⟩ := h.resolve_left (by simp [hi])
    simp only [simplifyGraph,hi]
    apply simplify_unpaid
    exact ⟨j,hj,by simpa [clipped,lt] using m⟩
theorem simplifyGraph_correct (raw : List Table) (P : Graph) (x : Row)
    (known : Nat → Option Bool) (ok : ∀ j v, known j = some v → wire raw P x j = v) :
    ∀ i, wire raw (simplifyGraph P known) x i = wire raw P x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases inp : i < raw.length
    · rw [wire.eq_def raw _ x i,wire.eq_def raw P x i]; simp [inp]
    · let read := fun j => if j<i then wire raw P x j else false
      have eqInputs : (fun j => if j<i then wire raw (simplifyGraph P known) x j else false) =
          read := by
        funext j; by_cases hj : j<i <;> simp [read,hj,ih]
      cases hi : known i with
      | some v =>
        rw [wire.eq_def raw (simplifyGraph P known) x i]
        simp [inp,simplifyGraph,hi,Cmd.act,ok i v hi]
      | none =>
        rw [wire.eq_def raw (simplifyGraph P known) x i,wire.eq_def raw P x i]
        simp only [inp,ite_false,simplifyGraph,hi]
        rw [show (fun j => if _ : j < i then wire raw (simplifyGraph P known) x j else false) = read
          from eqInputs]
        apply simplify_correct
        intro j v hj
        by_cases lt : j<i
        · simp [read,lt]; exact ok j v (by simpa [clipped,lt] using hj)
        · simpa [read,clipped,lt,eq_comm] using hj
end L652
namespace L652
def matchTable (j : Fin 3) : Table := if j=0 then f0 else if j=1 then f1 else f2
theorem pack_match : ∀ j, pack (matchTable j) = matchWord j := by decide +kernel
theorem agree_of_fiber {f j : Fin 3} {b : Bool} {v : Table}
    (h : ∀ x, matchTable f x = b → v x = matchTable j x) :
    equalOn (domainWord f b) (pack v) (matchWord j) := by
  intro i hi
  have e : matchTable f (inputRow i) = b := by
    rw [domainWord,←pack_match] at hi
    cases b
    · simpa only [Bool.false_eq_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,
        pack_bit _ _ i.isLt,Bool.not_eq_true'] using hi
    · exact (pack_bit (matchTable f) _ i.isLt).symm.trans hi
  simpa only [←pack_match,pack_bit _ _ i.isLt] using h (inputRow i) e
theorem realized_mem {w : List Table} {f j : Fin 3} {b : Bool} {t : Table}
    (hq : Available w t) (ne : f ≠ j) (eq : equalOn (domainWord f b) (pack t) (matchWord j)) : t ∈ w := by
  rcases hq with e | e | hm
  · subst t
    have det : Determines (domainWord f b) ∅ (pack zero) := by
      intro r s _ _ _
      simp only [pack_bit _ _ r.isLt,pack_bit _ _ s.isLt,zero]
    have bad := raw_required f j ne b rfl eq (Finset.empty_subset _) det
    exact False.elim ((by decide : (∅ : Finset Word) ≠ rawWords.toFinset) bad)
  · subst t
    have det : Determines (domainWord f b) ∅ (pack one) := by
      intro r s _ _ _
      simp only [pack_bit _ _ r.isLt,pack_bit _ _ s.isLt,one]
    have bad := raw_required f j ne b rfl eq (Finset.empty_subset _) det
    exact False.elim ((by decide : (∅ : Finset Word) ≠ rawWords.toFinset) bad)
  · exact hm
def NoResidualShare (f j k : Fin 3) (b : Bool) : Prop :=
  ∀ gs, History gs → gs.length ≤ 10 → ∀ t ∈ wiresOf gs, ∀ u ∈ wiresOf gs,
    equalOn (domainWord f b) t (matchWord j) → equalOn (domainWord f b) u (matchWord k) →
    shared gs t u = ∅
theorem residual_of_splits (f j k : Fin 3) (nj : f ≠ j) (nk : f ≠ k) (b : Bool)
    (noShare : NoResidualShare f j k b) :
    ResidualFloor 10 (matchTable f) (matchTable j) (matchTable k) b ∧
    ResidualExtends 10 (matchTable f) (matchTable j) (matchTable k) b := by
  have aux {p w} (h : Built p w) (small : p.length ≤ 10) {t u : Table}
      (mt : Available w t) (mu : Available w u)
      (v : ∀ x,matchTable f x = b → t x = matchTable j x ∧ u x = matchTable k x) :
      p.length = 10 ∧ t = matchTable j ∧ u = matchTable k := by
    have vt := agree_of_fiber (fun x hx => (v x hx).1)
    have vu := agree_of_fiber (fun x hx => (v x hx).2)
    obtain ⟨gs,hist,len,ws⟩ := history_of_built h
    have ht : pack t ∈ wiresOf gs := ws ▸ List.mem_map.mpr ⟨_,realized_mem mt nj vt,rfl⟩
    have hu : pack u ∈ wiresOf gs := ws ▸ List.mem_map.mpr ⟨_,realized_mem mu nk vu,rfl⟩
    have cap := len.trans_le small
    have no := noShare gs hist cap _ ht _ hu vt vu
    obtain ⟨sched,nd,_⟩ := history_schedule hist
    have av {w} (mem : w ∈ wiresOf gs) : w ∈ availableAfter rawWords.toFinset gs := by
      rw [available_wires]; exact List.mem_toFinset.mpr mem
    obtain ⟨ten,et,eu⟩ := disjoint_extends sched nd (av ht) (av hu) f j k nj nk b vt vu no cap
    exact ⟨len.symm.trans ten,pack_inj (et.trans (pack_match j).symm),
      pack_inj (eu.trans (pack_match k).symm)⟩
  constructor
  · intro p w h t u ht hu v
    by_cases short : p.length ≤ 10
    · exact (aux h short ht hu v).1.symm.le
    · omega
  · intro p w h short t u ht hu v
    exact (aux h short ht hu v).2
end L652
namespace L652
def AllowedWord (ws : List Word) (x : Word) : Prop := x=0 ∨ x = ~~~(0:Word) ∨ x∈ws
def FiberPresent (m : Word) (ws : List Word) (x : Word) : Prop :=
  ∃ y, AllowedWord ws y ∧ equalOn m x y
inductive FiberFresh (m : Word) : List LogicalGate → Prop
  | empty : FiberFresh m []
  | push {gs} (prev : FiberFresh m gs) (g : LogicalGate)
      (newOnFiber : ¬ FiberPresent m (wiresOf gs) g.out) : FiberFresh m (gs++[g])
theorem equalOn_refl (m a : Word) : equalOn m a a := fun _ _ => rfl
theorem equalOn_symm {m a b : Word} (h : equalOn m a b) : equalOn m b a :=
  fun i hi => (h i hi).symm
theorem equalOn_trans {m a b c : Word} (h : equalOn m a b) (k : equalOn m b c) :
    equalOn m a c := fun i hi => (h i hi).trans (k i hi)
private theorem zz24n0 (p : List LogicalGate) (g : LogicalGate) :
    wiresOf (p++[g])=wiresOf p++[g.out] := by simp [wiresOf,List.append_assoc]
private theorem zz24n1 {ws : List Word} {x y : Word}
    (a : AllowedWord ws x) : AllowedWord (ws++[y]) x := by
  rcases a with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (List.mem_append_left _ h))
private theorem zz24n2 (g : LogicalGate) (ws : List Word)
    (args : ∀ a∈g.args,AllowedWord ws a) :
    AllowedWord ws g.out ∨ g.args ⊆ ws := by
  have nz : ~~~(~~~(0:Word))=0 := by decide
  have all : ~~~(0:Word)=BitVec.allOnes 64 := by decide
  have met0 (a : Word) : (a &&& 0)=0 ∧ (0 &&& a)=0 := ⟨BitVec.and_zero,BitVec.zero_and⟩
  have met1 (a : Word) : (a &&& ~~~(0:Word))=a ∧ (~~~(0:Word) &&& a)=a := by
    rw [all]; exact ⟨BitVec.and_allOnes,BitVec.allOnes_and⟩
  have uni0 (a : Word) : (a ||| 0)=a ∧ (0 ||| a)=a := ⟨BitVec.or_zero,BitVec.zero_or⟩
  have uni1 (a : Word) : (a ||| ~~~(0:Word)) = ~~~(0:Word) ∧
      (~~~(0:Word) ||| a) = ~~~(0:Word) := by
    rw [all]; exact ⟨BitVec.or_allOnes,BitVec.allOnes_or⟩
  cases g with
  | neg a =>
    rcases args a (by simp [LogicalGate.args]) with eq|eq|hm
    · left; exact Or.inr (Or.inl (by simp [eq,LogicalGate.out]))
    · left; exact Or.inl (by simpa [eq,LogicalGate.out] using nz)
    · right; simpa [LogicalGate.args] using hm
  | meet a b =>
    have ha := args a (by simp [LogicalGate.args])
    have hb := args b (by simp [LogicalGate.args])
    rcases ha with eq|eq|ha
    · left; exact Or.inl (by simpa [eq,LogicalGate.out] using (met0 b).2)
    · left; simpa only [LogicalGate.out,eq,(met1 b).2] using hb
    rcases hb with eq|eq|hb
    · left; exact Or.inl (by simpa [eq,LogicalGate.out] using (met0 a).1)
    · left; exact Or.inr (Or.inr (by simpa only [LogicalGate.out,eq,(met1 a).1] using ha))
    · right; simp [LogicalGate.args,ha,hb]
  | join a b =>
    have ha := args a (by simp [LogicalGate.args])
    have hb := args b (by simp [LogicalGate.args])
    rcases ha with eq|eq|ha
    · left; simpa only [LogicalGate.out,eq,(uni0 b).2] using hb
    · left; exact Or.inr (Or.inl (by simpa [eq,LogicalGate.out] using (uni1 b).2))
    rcases hb with eq|eq|hb
    · left; exact Or.inr (Or.inr (by simpa only [LogicalGate.out,eq,(uni0 a).1] using ha))
    · left; exact Or.inr (Or.inl (by simpa [eq,LogicalGate.out] using (uni1 a).1))
    · right; simp [LogicalGate.args,ha,hb]
private theorem zz24n3 (m : Word) (ws : List Word) (g : LogicalGate)
    (args : ∀ a∈g.args,FiberPresent m ws a) :
    FiberPresent m ws g.out ∨ ∃ g' : LogicalGate, g'.args ⊆ ws ∧ equalOn m g.out g'.out := by
  have chooseGate (g' : LogicalGate) (leg : ∀a∈g'.args, AllowedWord ws a)
      (eq : equalOn m g.out g'.out) :
      FiberPresent m ws g.out ∨ ∃ g' : LogicalGate, g'.args ⊆ ws ∧ equalOn m g.out g'.out := by
    rcases zz24n2 g' ws leg with avail | real
    · exact Or.inl ⟨_,avail,eq⟩
    · exact Or.inr ⟨g',real,eq⟩
  cases g with
  | neg a =>
    obtain ⟨v,hv,eq⟩ := args a (by simp [LogicalGate.args])
    apply chooseGate (.neg v) (by simpa [LogicalGate.args] using hv)
    intro i hi
    simp only [LogicalGate.out,BitVec.getLsbD_not,eq i hi]
  | meet a b =>
    obtain ⟨v,hv,ev⟩ := args a (by simp [LogicalGate.args])
    obtain ⟨z,hz,ez⟩ := args b (by simp [LogicalGate.args])
    apply chooseGate (.meet v z) (by simp [LogicalGate.args,hv,hz])
    intro i hi; simp only [LogicalGate.out,BitVec.getLsbD_and,ev i hi,ez i hi]
  | join a b =>
    obtain ⟨v,hv,ev⟩ := args a (by simp [LogicalGate.args])
    obtain ⟨z,hz,ez⟩ := args b (by simp [LogicalGate.args])
    apply chooseGate (.join v z) (by simp [LogicalGate.args,hv,hz])
    intro i hi; simp only [LogicalGate.out,BitVec.getLsbD_or,ev i hi,ez i hi]
theorem normalize_fiber (m : Word) {gs : List LogicalGate} (hist : History gs) :
    ∃ q, History q ∧ FiberFresh m q ∧ q.length ≤ gs.length ∧
      (∀ t∈wiresOf gs,FiberPresent m (wiresOf q) t) ∧
      (q.length=gs.length → FiberFresh m gs) := by
  classical
  induction hist with
  | empty =>
    refine ⟨[],.empty,.empty,le_refl _,?_,fun _ => .empty⟩
    intro t ht; exact ⟨_,Or.inr (Or.inr ht),equalOn_refl _ _⟩
  | @push gs g old args fresh ih =>
    obtain ⟨q,hq,hfresh,le,cover,tight⟩ := ih
    by_cases redundant : FiberPresent m (wiresOf q) g.out
    · refine ⟨q,hq,hfresh,by simp; omega,?_,by simp; omega⟩
      intro t ht
      rw [zz24n0] at ht
      rcases List.mem_append.mp ht with old | new
      · exact cover t old
      · simpa [List.mem_singleton.mp new] using redundant
    · obtain ⟨g',ok,eq⟩ := (zz24n3 m (wiresOf q) g
        (fun a ha => cover a (args ha))).resolve_left redundant
      have newFiber : ¬ FiberPresent m (wiresOf q) g'.out := by
        rintro ⟨v,hv,ev⟩; exact redundant ⟨_,hv,equalOn_trans eq ev⟩
      have global : ¬ AllowedWord (wiresOf q) g'.out :=
        fun h => newFiber ⟨_,h,equalOn_refl _ _⟩
      have global' : g'.out ≠ 0 ∧ g'.out ≠ ~~~(0:Word) ∧ g'.out ∉ wiresOf q := by
        simpa [AllowedWord] using global
      refine ⟨q++[g'],.push hq ok global',.push hfresh g' newFiber,by simpa using le,?_,?_⟩
      · intro t ht
        rw [zz24n0] at ht ⊢
        rcases List.mem_append.mp ht with old | new
        · obtain ⟨v,hv,ev⟩ := cover t old
          exact ⟨_,zz24n1 hv,ev⟩
        · obtain rfl := List.mem_singleton.mp new
          exact ⟨g'.out,Or.inr (Or.inr (by simp)),eq⟩
      · intro len
        apply FiberFresh.push (tight (by simpa using len))
        rintro ⟨v,hv,ev⟩
        rcases hv with rfl | rfl | hm
        · exact redundant ⟨0,Or.inl rfl,ev⟩
        · exact redundant ⟨_,Or.inr (Or.inl rfl),ev⟩
        · obtain ⟨t,ht,et⟩ := cover v hm
          exact redundant ⟨t,ht,equalOn_trans ev et⟩
def FreshNoResidualShare (f j k : Fin 3) (b : Bool) : Prop :=
  ∀ gs, History gs → FiberFresh (domainWord f b) gs → gs.length ≤ 10 →
    ∀ t ∈ wiresOf gs, ∀ u ∈ wiresOf gs,
    equalOn (domainWord f b) t (matchWord j) → equalOn (domainWord f b) u (matchWord k) →
    shared gs t u = ∅
private theorem zz24n4 {ws : List Word} {f j : Fin 3} (neq : f≠j) (b : Bool)
    {v : Word} (hv : AllowedWord ws v) (eq : equalOn (domainWord f b) v (matchWord j)) :
    v∈ws := by
  rcases hv with rfl | rfl | hm
  · have dt : Determines (domainWord f b) ∅ (0:Word) := by simp [Determines]
    have contra := raw_required f j neq b rfl eq (Finset.empty_subset _) dt
    exact False.elim ((by decide : (∅ : Finset Word) ≠ rawWords.toFinset) contra)
  · have dt : Determines (domainWord f b) ∅ (~~~(0:Word)) := by
      have all : ∀ i : Fin 64,(~~~(0:Word)).getLsbD i.val=true := by decide
      intro i j _ _ _; exact (all i).trans (all j).symm
    have contra := raw_required f j neq b rfl eq (Finset.empty_subset _) dt
    exact False.elim ((by decide : (∅ : Finset Word) ≠ rawWords.toFinset) contra)
  · exact hm
theorem noShare_of_fresh {f j k : Fin 3} (nj : f≠j) (nk : f≠k) (b : Bool)
    (num : FreshNoResidualShare f j k b) : NoResidualShare f j k b := by
  intro gs hgs size t ht u hu et eu
  obtain ⟨q,hq,fresh,le,cover,tight⟩ := normalize_fiber (domainWord f b) hgs
  obtain ⟨t',ta,te⟩ := cover t ht
  obtain ⟨u',ua,ue⟩ := cover u hu
  have vt := equalOn_trans (equalOn_symm te) et
  have vu := equalOn_trans (equalOn_symm ue) eu
  have mt := zz24n4 nj b ta vt
  have mu := zz24n4 nk b ua vu
  have short : q.length≤10 := by omega
  have dis := num q hq fresh short t' mt u' mu vt vu
  obtain ⟨sched,nd,_⟩ := history_schedule hq
  have av {v} (mem : v ∈ wiresOf q) : v ∈ availableAfter rawWords.toFinset q := by
    rw [available_wires]; exact List.mem_toFinset.mpr mem
  have ten := (disjoint_extends sched nd (av mt) (av mu) f j k nj nk b vt vu dis short).1
  exact num gs hgs (tight (by omega)) size t ht u hu et eu
end L652
namespace L652
def exportKnown (P : Graph) (e : Nat) (S : Finset Nat) (b : Bool) (j : Nat) : Option Bool :=
  if j ∈ (P e).refs ∧ j ∈ S then some b else none
def cutExport (P : Graph) (e : Nat) (S : Finset Nat) (b : Bool) : Graph := fun i =>
  if i=e then simplifyCmd (exportKnown P e S b) (P e) else P i
theorem cut_unpaid {P : Graph} {e : Nat} {S : Finset Nat} (b : Bool)
    (edge : ∃ j ∈ (P e).refs, j ∈ S) : ((cutExport P e S b) e).paid=false := by
  simp only [cutExport,ite_true]
  apply simplify_unpaid
  obtain ⟨j,hj,hs⟩ := edge
  exact ⟨j,hj,by simp [exportKnown,hj,hs]⟩
private theorem zz25n0 {raw P x e S b i} (before : i < e) :
    wire raw (cutExport P e S b) x i = wire raw P x i :=
  wire_outside (fun j => e ≤ j) (fun j hj => by simp [cutExport]; omega)
    (fun j hj k hk hlt => by omega) i (by omega)
private theorem zz25n1 {raw P x e S b} (early : ∀ j ∈ (P e).refs, j < e)
    (equal : ∀ j ∈ (P e).refs, j ∈ S → wire raw P x j=b) :
    ∀ i, wire raw (cutExport P e S b) x i = wire raw P x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases he : i=e
    · subst i
      rw [wire.eq_def raw (cutExport P e S b) x e,wire.eq_def raw P x e]
      split
      · rfl
      · simp only [cutExport,ite_true]
        have getEq : (fun j => if _ : j<e then wire raw (cutExport P e S b) x j else false) =
            (fun j => if _ : j<e then wire raw P x j else false) := by
          funext j; by_cases hj : j<e <;> simp [hj,ih]
        rw [getEq]
        apply simplify_correct
        intro j v hv
        unfold exportKnown at hv
        split at hv
        · rename_i h
          cases hv
          simp [early j h.1,equal j h.1 h.2]
        · contradiction
    · exact wire_local (by simp [cutExport,he]) (fun j _ hlt => ih j hlt)
def triple (r a b : Nat) : Finset Nat := {r,a,b}
theorem cut_root {raw P x R A B E} (u : Bool)
    (rd : raw.length ≤ R) (ar : A < R) (br : B < R) (ne : R ≠ E)
    (root : P R = bop u A B ∨ P R = bop u B A)
    (early : ∀ j ∈ (P E).refs, j < E) :
    wire raw (cutExport P E (triple R A B) (!u)) x R = wire raw P x R := by
  classical
  let S := triple R A B
  let Q := cutExport P E S (!u)
  have root' : Q R = bop u A B ∨ Q R = bop u B A := by simpa [Q,cutExport,ne] using root
  by_cases allagree : ∀ j ∈ (P E).refs, j ∈ S → wire raw P x j=(!u)
  · exact zz25n1 early allagree R
  · push Not at allagree
    obtain ⟨j,hj,hs,bad⟩ := allagree
    have eq := zz25n0 (raw:=raw) (P:=P) (x:=x) (S:=S) (b:=!u) (early j hj)
    have absorbed : wire raw P x j=u := by cases u <;> cases h : wire raw P x j <;> simp_all
    change wire raw Q x R = wire raw P x R
    simp only [S,triple,Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with hs | hs | hs <;> subst j
    · exact eq
    · rw [wire_bop rd ar br root',wire_bop rd ar br root]
      change wire raw Q x A = wire raw P x A at eq
      rw [eq,absorbed]; cases u <;> simp [combine]
    · rw [wire_bop rd ar br root',wire_bop rd ar br root]
      change wire raw Q x B = wire raw P x B at eq
      rw [eq,absorbed]; cases u <;> simp [combine]
theorem cut_forced {raw P x R A B E} (u : Bool)
    (rd : raw.length ≤ R) (ar : A < R) (br : B < R)
    (root : P R = bop u A B ∨ P R = bop u B A)
    (early : ∀ j ∈ (P E).refs, j < E) (fixed : wire raw P x R=(!u)) :
    ∀ i, wire raw (cutExport P E (triple R A B) (!u)) x i = wire raw P x i := by
  apply zz25n1 early
  intro j hj hs
  have parents := fixed
  rw [wire_bop rd ar br root] at parents
  simp only [triple,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with hs | hs | hs <;> subst j
  · exact fixed
  · cases u <;> cases h : wire raw P x A <;> simp_all [combine]
  · cases u <;> cases h : wire raw P x B <;> simp_all [combine]
theorem cut_outside {raw P x e S b} (pinValue : Bool)
    (sole : ∀ i, i ∉ S → i ≠ e → ∀ j ∈ (P i).refs, j<i → j ∉ S) :
    ∀ i, i ∉ S → wire raw (cutExport P e S b) x i =
      wire raw (pin (cutExport P e S b) (· ∈ S) pinValue) x i := by
  apply wire_outside (· ∈ S)
  · intro i hi; simp [pin,hi]
  · intro i hi j hj lt
    by_cases he : i=e
    · subst i
      simp only [cutExport,ite_true] at hj
      obtain ⟨hj,none⟩ := simplify_refs hj
      intro hs; simp [exportKnown,hj,hs] at none
    · exact sole i hi he j (by simpa [cutExport,he] using hj) lt
theorem cost_absolute {base n : Nat} {P : Graph} (W : Finset Nat)
    (inRange : ∀ i ∈ W, base ≤ i ∧ i < base+n)
    (free : ∀ i ∈ W, (P i).paid = false) :
    (paidIndices base n P).card + W.card ≤ n := by
  let offsets := W.image (·-base)
  have card : offsets.card = W.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj hij
    have a := inRange i hi; have b := inRange j hj
    change i-base=j-base at hij; omega
  rw [← card]
  apply cost_of_exempt
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have := inRange i hi
    apply Finset.mem_range.mpr; omega
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have := inRange i hi
    rw [show base+(i-base)=i by omega]
    exact free i hi
theorem shrink_any_export (P : Graph) (n R A B E out₁ out₂ : Nat) (u : Bool)
    (size3 : (triple R A B).card=3)
    (bounds : ∀ j ∈ insert E (triple R A B), inputTables.length ≤ j ∧ j<inputTables.length+n)
    (eout : E ∉ triple R A B) (aout : out₁ ∉ triple R A B) (bout : out₂ ∉ triple R A B)
    (oa : out₁ < inputTables.length+n) (ob : out₂ < inputTables.length+n)
    (ar : A<R) (br : B<R)
    (root : P R = bop u A B ∨ P R = bop u B A)
    (early : ∀j∈(P E).refs,j<E)
    (uses : ∃ j ∈ (P E).refs, j ∈ triple R A B)
    (sole : ∀ i, i ∉ triple R A B → i ≠ E → ∀ j ∈ (P i).refs,j<i → j ∉ triple R A B)
    (extend : ResidualExtends (n-4) (wireTable inputTables P R)
      (wireTable inputTables P out₁) (wireTable inputTables P out₂) (!u)) :
    ∃ q z, Built q z ∧ q.length+1 ≤ n ∧ Available z (wireTable inputTables P R) ∧
      Available z (wireTable inputTables P out₁) ∧ Available z (wireTable inputTables P out₂) := by
  let S := triple R A B
  let Q := cutExport P E S (!u)
  let Z := pin Q (· ∈ S) (!u)
  have ri := bounds R (by simp [triple])
  have re : R ≠ E := by rintro rfl; exact eout (by simp [triple])
  have eq (j) (hj : j ∉ S) : wireTable inputTables Q j = wireTable inputTables Z j := by
    funext x; exact cut_outside _ sole j hj
  obtain ⟨qz,zz,hz,nz,coverZ⟩ := compressGraph inputTables Z n
  have saved : (paidIndices inputTables.length n Z).card + (insert E S).card ≤ n := by
    apply cost_absolute (insert E S) bounds
    intro j hj
    rcases Finset.mem_insert.mp hj with h | h
    · subst j
      simpa [Z,pin,show E ∉ S from eout] using cut_unpaid (!u) uses
    · simp [Z,pin,h,Cmd.paid]
  have cz : qz.length ≤ n-4 := by
    rw [Finset.card_insert_of_notMem eout, size3] at saved
    omega
  obtain ⟨ea,eb⟩ := extend qz zz hz.toBuilt cz _ _ (coverZ out₁ oa) (coverZ out₂ ob) (by
    intro x hx
    have agree := cut_forced (x:=x) u ri.1 ar br root early hx
    have h (j) (hj : j ∉ S) : wireTable inputTables Z j x = wireTable inputTables P j x :=
      (congrFun (eq j hj).symm x).trans (agree j)
    exact ⟨h out₁ aout,h out₂ bout⟩)
  obtain ⟨q,z,hq,nq,keep⟩ := compressGraph inputTables Q n
  refine ⟨q,z,hq.toBuilt,?_,?_,?_,?_⟩
  · have h := cost_absolute (P:=Q) (base:=inputTables.length) (n:=n) {E}
      (fun j hj => by simpa [Finset.mem_singleton.mp hj] using bounds E (by simp))
      (fun j hj => by simpa [Finset.mem_singleton.mp hj] using cut_unpaid (!u) uses)
    simp only [Finset.card_singleton] at h
    omega
  · have h : wireTable inputTables P R = wireTable inputTables Q R := by
      funext x; exact (cut_root (x:=x) u ri.1 ar br re root early).symm
    rw [h]; exact keep R ri.2
  · rw [← ea, ← eq out₁ aout]; exact keep out₁ oa
  · rw [← eb, ← eq out₂ bout]; exact keep out₂ ob
end L652
namespace L652
def Window (base n : Nat) (P : Graph) : Prop :=
  ∀ i, base ≤ i → ∀ j ∈ (P i).refs, j < i ∧ i < base+n
theorem Built.ops_valid {p w} (h : Built p w) :
    ∀ k (hk : k < p.length), (p[k]).valid (inputTables.length+k) := by
  induction h with
  | start => simp
  | @snoc p w prev g hv fresh ih =>
    intro k hk
    by_cases lt : k < p.length
    · simp [List.getElem_append_left lt,ih k lt]
    · have eq : k=p.length := by simp at hk; omega
      subst k
      simpa [prev.wire_count] using hv
theorem Built.window {p w} (h : Built p w) :
    Window inputTables.length p.length (graphOf inputTables.length p) := by
  intro i bound j hj
  by_cases lt : i-inputTables.length < p.length
  · have v := h.ops_valid _ lt
    simp [graphOf,List.getElem?_eq_getElem lt] at hj
    have eq : inputTables.length+(i-inputTables.length)=i := by omega
    rw [eq] at v
    refine ⟨?_,by omega⟩
    generalize p[i-inputTables.length] = g at v hj
    cases g <;> simp_all [Op.valid,Cmd.refs] <;> grind
  · simp [graphOf,List.getElem?_eq_none (Nat.le_of_not_gt lt),Cmd.refs] at hj
noncomputable def exterior (base n : Nat) (P : Graph) (S : Finset Nat) : Finset Nat := by
  classical
  exact (Finset.range (base+n)).filter fun i => base ≤ i ∧ i ∉ S ∧
    ∃ j ∈ (P i).refs, j<i ∧ j ∈ S
theorem mem_exterior {base n P S i} : i ∈ exterior base n P S ↔
    i < base+n ∧ base ≤ i ∧ i ∉ S ∧ ∃ j ∈ (P i).refs, j<i ∧ j ∈ S := by
  classical
  simp [exterior]
theorem consumer_budget {n k : Nat} (P : Graph) (F : Table) (bit : Bool)
    (out₁ out₂ : Nat) (oa : out₁ < inputTables.length+n) (ob : out₂ < inputTables.length+n)
    (floor : ResidualFloor k F (wireTable inputTables P out₁) (wireTable inputTables P out₂) bit)
    (S : Finset Nat) (val : Nat → Bool)
    (rng : ∀ i ∈ S, inputTables.length ≤ i ∧ i<inputTables.length+n)
    (fixed : ∀ x, F x=bit → ∀ j ∈ S, wire inputTables P x j = val j) :
    k + S.card + (exterior inputTables.length n P S).card ≤ n := by
  classical
  let known := fun i => if i∈S then some (val i) else none
  let Q := simplifyGraph P known
  let T := exterior inputTables.length n P S
  have ok x (h : F x=bit) : ∀ j v, known j=some v → wire inputTables P x j=v := by
    intro j v hv
    dsimp [known] at hv
    split at hv
    · rename_i hs
      cases hv; exact fixed x h j hs
    · contradiction
  obtain ⟨q,z,built,count,keep⟩ := compressGraph inputTables Q n
  have lower := floor q z built.toBuilt _ _ (keep out₁ oa) (keep out₂ ob) (fun x hx =>
    ⟨simplifyGraph_correct _ P x known (ok x hx) out₁,
     simplifyGraph_correct _ P x known (ok x hx) out₂⟩)
  have charge := cost_absolute (base:=inputTables.length) (n:=n) (P:=Q) (S∪T) (by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact rng j h
    · exact ⟨(mem_exterior.mp h).2.1,(mem_exterior.mp h).1⟩) (by
      intro i hi
      apply removable_unpaid
      rcases Finset.mem_union.mp hi with hs | ht
      · exact Or.inl (by simp [known,hs])
      · obtain ⟨j,hj,lt,hs⟩ := (mem_exterior.mp ht).2.2.2
        exact Or.inr ⟨j,hj,lt,by simp [known,hs]⟩)
  have disj : Disjoint S T := by
    rw [Finset.disjoint_left]; intro i hs ht
    exact (mem_exterior.mp ht).2.2.1 hs
  rw [Finset.card_union_of_disjoint disj] at charge
  change k + S.card + T.card ≤ n
  omega
theorem four_private {n : Nat} (P : Graph) (F : Table) (bit : Bool) (a b : Nat)
    (oa : a < inputTables.length+n) (ob : b < inputTables.length+n)
    (floor : ResidualFloor 10 F (wireTable inputTables P a) (wireTable inputTables P b) bit)
    (S : Finset Nat) (val : Nat → Bool) (four : S.card=4) (small : n ≤ 14)
    (rng : ∀ i ∈ S, inputTables.length ≤ i ∧ i<inputTables.length+n)
    (fixed : ∀ x, F x=bit → ∀ j ∈ S, wire inputTables P x j = val j) :
    exterior inputTables.length n P S = ∅ := by
  have h := consumer_budget P F bit a b oa ob floor S val rng fixed
  apply Finset.card_eq_zero.mp; omega
def Optimal (n : Nat) (f g h : Table) : Prop :=
  ∀ q z, Built q z → q.length < n → Available z f → Available z g → Available z h → False
theorem binary_private (P : Graph) (n R A B a b : Nat) (u : Bool)
    (small : n≤14) (window : Window inputTables.length n P)
    (three : (triple R A B).card=3)
    (rng : ∀ j ∈ triple R A B, inputTables.length ≤ j ∧ j<inputTables.length+n)
    (aout : a ∉ triple R A B) (bout : b ∉ triple R A B)
    (oa : a < inputTables.length+n) (ob : b < inputTables.length+n)
    (ar : A<R) (br : B<R) (root : P R=bop u A B ∨ P R=bop u B A)
    (floor : ResidualFloor 10 (wireTable inputTables P R)
      (wireTable inputTables P a) (wireTable inputTables P b) (!u))
    (extend : ResidualExtends (n-4) (wireTable inputTables P R)
      (wireTable inputTables P a) (wireTable inputTables P b) (!u))
    (minimal : Optimal n (wireTable inputTables P R) (wireTable inputTables P a)
      (wireTable inputTables P b)) :
    exterior inputTables.length n P (triple R A B) = ∅ := by
  classical
  let S := triple R A B
  let T := exterior inputTables.length n P S
  have rr := (rng R (by simp [triple])).1
  have fixed (x) (hx : wireTable inputTables P R x=(!u)) :
      ∀ j ∈ S, wire inputTables P x j = !u := by
    intro j hj
    have hr : wire inputTables P x R=(!u) := hx
    have parts := hr
    rw [wire_bop rr ar br root] at parts
    simp only [S,triple,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with he | he | he <;> subst j
    · exact hr
    · cases u <;> cases h : wire inputTables P x A <;> simp_all [combine]
    · cases u <;> cases h : wire inputTables P x B <;> simp_all [combine]
  have ct := consumer_budget P _ (!u) a b oa ob floor S (fun _ => !u) rng fixed
  change 10+S.card+T.card ≤ n at ct
  have s3 : S.card=3 := three
  have one : T.card≤1 := by omega
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro E eext
  change E∈T at eext
  obtain ⟨emax,emin,eout,used⟩ := mem_exterior.mp eext
  have bound : ∀ j ∈ insert E S, inputTables.length ≤ j ∧ j<inputTables.length+n := by
    intro j hj
    rcases Finset.mem_insert.mp hj with eq | hm
    · subst j; exact ⟨emin,emax⟩
    · exact rng j hm
  have early : ∀ j ∈ (P E).refs, j<E := fun j h => (window E emin j h).1
  have uses : ∃ j ∈ (P E).refs,j∈S := by
    obtain ⟨j,hj,_,hs⟩ := used; exact ⟨j,hj,hs⟩
  obtain ⟨q,z,hq,save,c1,c2,c3⟩ := shrink_any_export P n R A B E a b u
    three bound eout aout bout oa ob ar br root early uses (by
      intro i hi ne j hj lt hs
      have hbase := (rng j hs).1
      have imin : inputTables.length ≤ i := by omega
      have imax := (window i imin j hj).2
      have imem : i∈T := mem_exterior.mpr ⟨imax,imin,hi,j,hj,lt,hs⟩
      exact ne (Finset.card_le_one.mp one i imem E eext)) extend
  exact minimal q z hq (by omega) c1 c2 c3
end L652
namespace L652
theorem Built.distinct {p w} (h : Built p w) : w.Nodup := by
  induction h with
  | start =>
    apply List.nodup_ofFn_ofInjective
    intro i j eq
    have h := congrFun eq (fun k => decide (k = i))
    simpa [eq_comm] using h.symm
  | snoc old g valid fresh ih =>
    rw [List.nodup_append]
    refine ⟨ih,by simp,?_⟩
    intro f hf b hb e
    have e' := List.mem_singleton.mp hb
    exact fresh (Or.inr (Or.inr ((e.trans e') ▸ hf)))
theorem Built.no_alias {p w} (h : Built p w) {i j : Nat} (hi : i<w.length) (hj : j<w.length)
    (same : wireTable inputTables (graphOf inputTables.length p) i =
      wireTable inputTables (graphOf inputTables.length p) j) : i=j := by
  apply h.distinct.getElem_inj_iff.mp
  have eq : (w.getD i zero) = (w.getD j zero) := by
    funext x
    rw [← h.indexed i hi x,← h.indexed j hj x]
    exact congrFun same x
  simpa [List.getD_eq_getElem?_getD,hi,hj] using eq
def Varies (F : Table) (bit : Bool) (v : Table) : Prop :=
  ∃ x y, F x=bit ∧ F y=bit ∧ v x ≠ v y
def fiberRaw (F : Table) : Prop := ∀ b, ∀ v ∈ inputTables, Varies F b v
theorem varying_not_fixed {F v} {b : Bool} (var : Varies F b v) (t : Bool)
    (fixed : ∀ x, F x=b → v x=t) : False := by
  obtain ⟨x,y,hx,hy,ne⟩ := var
  exact ne ((fixed x hx).trans (fixed y hy).symm)
theorem internal_of_fixed (P : Graph) {F : Table} {i : Nat} {bit t : Bool}
    (rawVar : fiberRaw F)
    (fixed : ∀ x, F x=bit → wire inputTables P x i=t) : inputTables.length ≤ i := by
  by_contra! h
  have look : inputTables.getD i zero ∈ inputTables := by
    simp [List.getD_eq_getElem?_getD,h]
  apply varying_not_fixed (rawVar bit _ look) t
  intro x hx
  have eq := fixed x hx
  simpa [wire.eq_def inputTables P x i,h] using eq
theorem choose_minimal {s : Nat} (hc : Realizable s) :
    ∃ p w, Built p w ∧ p.length ≤ s ∧ f0 ∈ w ∧ f1 ∈ w ∧ f2 ∈ w ∧
      Optimal p.length f0 f1 f2 := by
  classical
  let good := fun n => ∃ p w, Built p w ∧ p.length=n ∧ f0 ∈ w ∧ f1 ∈ w ∧ f2 ∈ w
  obtain ⟨p₀,w₀,hp₀,hlen,h₀,h₁,h₂⟩ := simulate hc
  have bound : good p₀.length := ⟨p₀,w₀,hp₀,rfl,h₀,h₁,h₂⟩
  have ex : ∃ n,good n := ⟨_,bound⟩
  obtain ⟨p,w,hp,hn,h0,h1,h2⟩ := Nat.find_spec ex
  refine ⟨p,w,hp,by rw [hn]; exact le_trans (Nat.find_min' ex bound) hlen,h0,h1,h2,?_⟩
  intro q z hq less a b c
  have req (f : Table) (lo : f (fun _ => false)=false) (hi : f (fun _ => true)=true)
      (v : Available z f) : f ∈ z := by
    rcases v with rfl | rfl | h <;> first | contradiction | assumption
  apply Nat.find_min ex (hn ▸ less)
  exact ⟨q,z,hq,rfl,req f0 rfl rfl a,req f1 rfl rfl b,req f2 rfl rfl c⟩
end L652
namespace L652
theorem bop_refs (u : Bool) (a b : Nat) : (bop u a b).refs=[a,b] := by cases u <;> rfl
structure PrivateBlock (P : Graph) (n R : Nat) where
  center : Nat
  left : Nat
  right : Nat
  join : Bool
  left_lt : left < center
  right_lt : right < center
  binary : P center = bop join left right ∨ P center = bop join right left
  outer : center=R ∨ (center<R ∧ P R = .gate (.neg center))
  bounds : ∀ j ∈ insert R (triple center left right),
    inputTables.length ≤ j ∧ j < inputTables.length+n
  at_least_three : 3 ≤ (insert R (triple center left right)).card
  closed : exterior inputTables.length n P (insert R (triple center left right)) = ∅
def PrivateBlock.nodes {P n R} (b : PrivateBlock P n R) : Finset Nat :=
  insert R (triple b.center b.left b.right)
def PrivateBlock.boundary {P n R} (b : PrivateBlock P n R) : Finset Nat :=
  ((P b.left).refs.toFinset ∪ (P b.right).refs.toFinset) \ b.nodes
theorem PrivateBlock.root_mem {P n R} (b : PrivateBlock P n R) : R ∈ b.nodes := by
  simp [nodes]
theorem PrivateBlock.center_mem {P n R} (b : PrivateBlock P n R) : b.center ∈ b.nodes := by
  simp [nodes,triple]
theorem PrivateBlock.left_mem {P n R} (b : PrivateBlock P n R) : b.left ∈ b.nodes := by
  simp [nodes,triple]
theorem PrivateBlock.right_mem {P n R} (b : PrivateBlock P n R) : b.right ∈ b.nodes := by
  simp [nodes,triple]
theorem PrivateBlock.boundary_card {P n R} (b : PrivateBlock P n R) : b.boundary.card ≤ 4 := by
  have two (c : Cmd) : c.refs.toFinset.card ≤ 2 := by
    apply le_trans (List.toFinset_card_le _)
    cases c with
    | lit v => simp [Cmd.refs]
    | copy i => simp [Cmd.refs]
    | gate g => cases g <;> simp [Cmd.refs]
  have h := Finset.card_union_le (P b.left).refs.toFinset (P b.right).refs.toFinset
  have lo := two (P b.left); have hi := two (P b.right)
  have up := Finset.card_le_card (Finset.sdiff_subset :
    b.boundary ⊆ (P b.left).refs.toFinset ∪ (P b.right).refs.toFinset)
  change _ ≤ 4
  exact le_trans up (by omega)
theorem PrivateBlock.internal_source {P n R} (b : PrivateBlock P n R) {i j : Nat}
    (hi : i ∈ b.nodes) (src : j ∈ (P i).refs) : j ∈ b.nodes ∨ j ∈ b.boundary := by
  by_cases hj : j ∈ b.nodes
  · exact Or.inl hj
  right
  rw [boundary,Finset.mem_sdiff]
  refine ⟨?_,hj⟩
  have cent (h : i=b.center) : False := by
    rcases b.binary with hb | hb <;> rw [h,hb] at src <;>
      simp only [bop_refs,List.mem_cons,
        List.mem_nil_iff,or_false] at src <;> rcases src with h | h <;> subst j <;>
      first | exact hj b.left_mem | exact hj b.right_mem
  simp only [nodes, triple, Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with hr | hc | hl | hr
  · rcases b.outer with he | ⟨_,he⟩
    · exact False.elim (cent (hr.trans he.symm))
    · rw [hr,he] at src
      simp only [Cmd.refs,List.mem_singleton] at src
      exact False.elim (hj (src ▸ b.center_mem))
  · exact False.elim (cent hc)
  · rw [hl] at src; simp [src]
  · rw [hr] at src; simp [src]
private theorem zz28n0 {P : Graph} {x y : Row} {i : Nat}
    (internal : inputTables.length ≤ i)
    (sourcesEqual : ∀ j∈(P i).refs,j<i → wire inputTables P x j = wire inputTables P y j) :
    wire inputTables P x i = wire inputTables P y i := by
  rw [wire.eq_def inputTables P x i,wire.eq_def inputTables P y i]
  simp only [Nat.not_lt.mpr internal,ite_false]
  have eq (j) (h : j∈(P i).refs) :
      (if _ : j<i then wire inputTables P x j else false) =
      (if _ : j<i then wire inputTables P y j else false) := by
    split <;> simp_all
  generalize h : P i = c at *
  cases c with
  | lit b => rfl
  | copy k => exact eq k (by simp [Cmd.refs])
  | gate g => cases g <;> simp_all [Cmd.refs,Cmd.act]
theorem PrivateBlock.determined {P n R} (b : PrivateBlock P n R) (x y : Row)
    (agree : ∀ k∈b.boundary,wire inputTables P x k = wire inputTables P y k) :
    wire inputTables P x R = wire inputTables P y R := by
  suffices each : ∀ i, i∈b.nodes → wire inputTables P x i = wire inputTables P y i by
    exact each R b.root_mem
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    apply zz28n0 (b.bounds i hi).1
    intro j hj lt
    rcases b.internal_source hi hj with inside | outside
    · exact ih j lt inside
    · exact agree j outside
theorem PrivateBlock.forward {P n R} (b : PrivateBlock P n R) {j i}
    (source : j ∈ b.nodes) (atGate : inputTables.length≤i ∧ i<inputTables.length+n)
    (edge : j∈(P i).refs) (lt : j<i) : i∈b.nodes := by
  by_contra h
  have hc : i∈exterior inputTables.length n P b.nodes := mem_exterior.mpr
    ⟨atGate.2,atGate.1,h,j,edge,lt,source⟩
  have closed : exterior inputTables.length n P b.nodes = ∅ := b.closed
  simp [closed] at hc
theorem PrivateBlock.disjoint {P n r s} (a : PrivateBlock P n r) (b : PrivateBlock P n s)
    (separate : s ∉ a.nodes) : Disjoint a.nodes b.nodes := by
  rw [Finset.disjoint_left]
  intro j hj hm
  have fromCenter (hc : b.center∈a.nodes) : False := by
    rcases b.outer with eq | ⟨lt,op⟩
    · exact separate (eq ▸ hc)
    · exact separate (a.forward hc (b.bounds _ b.root_mem) (by simp [op,Cmd.refs]) lt)
  have reach {k} (kf : k=b.left ∨ k=b.right) (inside : k∈a.nodes) :
      False := by
    apply fromCenter
    have edge : k∈(P b.center).refs := by
      rcases b.binary with hb|hb <;> rcases kf with hk|hk <;> simp [hb,bop_refs,hk]
    apply a.forward inside (b.bounds _ b.center_mem) edge
    rcases kf with hk | hk
    · rw [hk]; exact b.left_lt
    · rw [hk]; exact b.right_lt
  simp only [nodes,triple,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with eq | eq | eq | eq
  · exact separate (eq ▸ hj)
  · exact fromCenter (eq ▸ hj)
  · exact reach (Or.inl eq) hj
  · exact reach (Or.inr eq) hj
end L652
namespace L652
theorem Built.gate_at {p w} (h : Built p w) {i} (lo : inputTables.length≤i)
    (hi : i<inputTables.length+p.length) :
    ∃ g, graphOf inputTables.length p i = .gate g ∧ g.valid i := by
  have k : i-inputTables.length<p.length := by omega
  refine ⟨p[i-inputTables.length],by simp [graphOf,List.getElem?_eq_getElem k],?_⟩
  have v := h.ops_valid _ k
  rwa [show inputTables.length+(i-inputTables.length)=i by omega] at v
theorem wire_neg {P : Graph} {R C} {x : Row} (lo : inputTables.length≤R) (lt : C<R)
    (g : P R=.gate (.neg C)) : wire inputTables P x R = !wire inputTables P x C := by
  rw [wire.eq_def inputTables P x R]
  simp [Nat.not_lt.mpr lo,g,Cmd.act,lt]
private theorem zz29n0 {P : Graph} {C A B} {x : Row} (u : Bool)
    (lo : inputTables.length≤C) (al : A<C) (bl : B<C)
    (g : P C=bop u A B) (h : wire inputTables P x C=(!u)) :
    wire inputTables P x A=(!u) ∧ wire inputTables P x B=(!u) := by
  rw [wire_bop lo al bl (Or.inl g)] at h
  cases u <;> cases ha : wire inputTables P x A <;> cases hb : wire inputTables P x B <;>
    simp_all [combine]
private theorem zz29n1 {c a b} (al : a<c) (bl : b<c) (ab : a≠b) :
    (triple c a b).card=3 := by
  have ca : c≠a := by omega
  have cb : c≠b := by omega
  simp [triple,ca,cb,ab]
private theorem zz29n2 {F : Table} {P : Graph} {S : Finset Nat} {v : Nat → Bool}
    {b : Bool} {o : Nat}
    (var : Varies F b (wireTable inputTables P o))
    (fix : ∀ x, F x=b → ∀j∈S,wire inputTables P x j = v j) : o∉S := by
  intro om
  exact varying_not_fixed var (v o) (fun x hx => fix x hx o om)
private theorem zz29n3 (P : Graph) (n R A B a b : Nat) (u : Bool)
    (small : n≤14) (window : Window inputTables.length n P)
    (rlo : inputTables.length≤R) (rhi : R<inputTables.length+n)
    (oa : a<inputTables.length+n) (ob : b<inputTables.length+n)
    (al : A<R) (bl : B<R) (ab : A≠B) (g : P R=bop u A B)
    (raws : fiberRaw (wireTable inputTables P R))
    (var₁ : Varies (wireTable inputTables P R) (!u) (wireTable inputTables P a))
    (var₂ : Varies (wireTable inputTables P R) (!u) (wireTable inputTables P b))
    (floor : ResidualFloor 10 (wireTable inputTables P R)
      (wireTable inputTables P a) (wireTable inputTables P b) (!u))
    (ext : ResidualExtends (n-4) (wireTable inputTables P R)
      (wireTable inputTables P a) (wireTable inputTables P b) (!u))
    (opt : Optimal n (wireTable inputTables P R) (wireTable inputTables P a) (wireTable inputTables P b)) :
    ∃ v : PrivateBlock P n R, a ∉ v.nodes ∧ b ∉ v.nodes := by
  let S := triple R A B
  have fixed x (h : wireTable inputTables P R x=(!u)) : ∀j∈S,wire inputTables P x j = !u := by
    have both := zz29n0 u rlo al bl g h
    intro j hj; simp only [S,triple,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with he|he|he <;> subst j <;> first | exact h | exact both.1 | exact both.2
  have rng : ∀j∈S, inputTables.length≤j ∧ j<inputTables.length+n := by
    intro j hj
    refine ⟨internal_of_fixed P raws (fun x hx => fixed x hx j hj),?_⟩
    simp only [S,triple,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  have aout := zz29n2 (v:=fun _ => !u) var₁ fixed
  have bout := zz29n2 (v:=fun _ => !u) var₂ fixed
  have closed := binary_private P n R A B a b u small window (zz29n1 al bl ab)
    rng aout bout oa ob al bl (Or.inl g) floor ext opt
  have self : insert R (triple R A B)=S := by simp [triple,S]
  let v : PrivateBlock P n R :=
    ⟨R,A,B,u,al,bl,Or.inl g,Or.inl rfl,by simpa only [self] using rng,
      by rw [self]; exact (zz29n1 al bl ab).ge,
      by rw [self]; exact closed⟩
  exact ⟨v,by simpa [v,PrivateBlock.nodes,self] using aout,by simpa [v,PrivateBlock.nodes,self] using bout⟩
private theorem zz29n4 (P : Graph) (n R C A B a b : Nat) (u : Bool)
    (small : n≤14) (rlo : inputTables.length≤R) (rhi : R<inputTables.length+n)
    (clo : inputTables.length≤C) (cr : C<R) (rg : P R=.gate (.neg C))
    (oa : a<inputTables.length+n) (ob : b<inputTables.length+n)
    (al : A<C) (bl : B<C) (ab : A≠B) (g : P C=bop u A B)
    (raws : fiberRaw (wireTable inputTables P R))
    (var₁ : Varies (wireTable inputTables P R) u (wireTable inputTables P a))
    (var₂ : Varies (wireTable inputTables P R) u (wireTable inputTables P b))
    (floor : ResidualFloor 10 (wireTable inputTables P R)
      (wireTable inputTables P a) (wireTable inputTables P b) u) :
    ∃ v : PrivateBlock P n R, a ∉ v.nodes ∧ b ∉ v.nodes := by
  let S := insert R (triple C A B)
  let val := fun j => if j=R then u else !u
  have rc : R≠C := by omega
  have ra : R≠A := by omega
  have rb : R≠B := by omega
  have four : S.card=4 := by
    have out : R∉triple C A B := by simp [triple,rc,ra,rb]
    simp [S,Finset.card_insert_of_notMem out,zz29n1 al bl ab]
  have fixed x (h : wireTable inputTables P R x=u) : ∀j∈S,wire inputTables P x j=val j := by
    have neg := wire_neg (x:=x) rlo cr rg
    have rr : wire inputTables P x R=u := h
    have hc : wire inputTables P x C=(!u) := by
      cases u <;> cases h : wire inputTables P x C <;> simp_all
    have both := zz29n0 u clo al bl g hc
    intro j hj
    simp only [S,triple,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with he|he|he|he <;> subst j <;> simp_all [val,Ne.symm rc,Ne.symm ra,Ne.symm rb]
  have rng : ∀j∈S, inputTables.length≤j ∧ j<inputTables.length+n := by
    intro j hj
    refine ⟨internal_of_fixed P raws (fun x hx => fixed x hx j hj),?_⟩
    simp only [S,triple,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  have aout := zz29n2 var₁ fixed
  have bout := zz29n2 var₂ fixed
  have closed := four_private P _ u a b oa ob floor S val four small rng fixed
  let v : PrivateBlock P n R :=
    ⟨C,A,B,u,al,bl,Or.inl g,Or.inr ⟨cr,rg⟩,rng,by change 3 ≤ S.card; omega,closed⟩
  exact ⟨v,aout,bout⟩
theorem Built.output_block {p w} (built : Built p w) (P : Graph)
    (sameGraph : P=graphOf inputTables.length p) (R a b : Nat)
    (small : p.length≤14) (rhi : R<inputTables.length+p.length)
    (oa : a<inputTables.length+p.length) (ob : b<inputTables.length+p.length)
    (raws : fiberRaw (wireTable inputTables P R))
    (var₁ : ∀ bit, Varies (wireTable inputTables P R) bit (wireTable inputTables P a))
    (var₂ : ∀ bit, Varies (wireTable inputTables P R) bit (wireTable inputTables P b))
    (floor : ∀ bit, ResidualFloor 10 (wireTable inputTables P R)
      (wireTable inputTables P a) (wireTable inputTables P b) bit)
    (ext : ∀ bit, ResidualExtends (p.length-4) (wireTable inputTables P R)
      (wireTable inputTables P a) (wireTable inputTables P b) bit)
    (opt : Optimal p.length (wireTable inputTables P R)
      (wireTable inputTables P a) (wireTable inputTables P b)) :
    ∃ v : PrivateBlock P p.length R, a ∉ v.nodes ∧ b ∉ v.nodes := by
  have window : Window inputTables.length p.length P := sameGraph ▸ built.window
  have rlo : inputTables.length ≤ R := internal_of_fixed P (bit:=false) raws (fun x hx => hx)
  obtain ⟨root,op,hv⟩ := built.gate_at rlo rhi
  rw [← sameGraph] at op
  cases root with
  | meet l r =>
    exact zz29n3 P _ R l r a b false small window rlo rhi oa ob hv.1 hv.2.1 hv.2.2 op
      raws (var₁ _) (var₂ _) (floor _) (ext _) opt
  | join l r =>
    exact zz29n3 P _ R l r a b true small window rlo rhi oa ob hv.1 hv.2.1 hv.2.2 op
      raws (var₁ _) (var₂ _) (floor _) (ext _) opt
  | neg C =>
    change C<R at hv
    have clo : inputTables.length≤C := by
      apply internal_of_fixed P (bit:=true) (t:=false) raws
      intro x hx
      have eq := wire_neg (x:=x) rlo hv op
      change wire inputTables P x R=true at hx
      cases hc : wire inputTables P x C <;> simp_all
    obtain ⟨g,cop,valid⟩ := built.gate_at clo (by omega)
    rw [← sameGraph] at cop
    cases g with
    | meet l r =>
      exact zz29n4 P _ R C l r a b false small rlo rhi clo hv op oa ob valid.1 valid.2.1
        valid.2.2 cop raws (var₁ _) (var₂ _) (floor _)
    | join l r =>
      exact zz29n4 P _ R C l r a b true small rlo rhi clo hv op oa ob valid.1 valid.2.1
        valid.2.2 cop raws (var₁ _) (var₂ _) (floor _)
    | neg D =>
      change D<C at valid
      have duplicate : wireTable inputTables P R=wireTable inputTables P D := by
        funext x
        change wire inputTables P x R=wire inputTables P x D
        rw [wire_neg rlo hv op,wire_neg clo valid cop]
        simp
      rw [sameGraph] at duplicate
      have count := built.wire_count
      have impossible := built.no_alias (by omega : R<w.length) (by omega : D<w.length) duplicate
      omega
end L652
namespace L652.Residual
abbrev Row := Fin 6 → Bool
def rowOf (n : Nat) : Row := fun i => n.testBit i.val
def flip (r : Row) (j : Fin 6) : Row := fun i => if i = j then !r i else r i
def edge (shift i : Fin 3) (r : Row) : Bool :=
  r ⟨i.val, by omega⟩ && r ⟨3 + (i.val + shift.val) % 3, by omega⟩
def matching (k : Fin 3) (r : Row) : Bool := edge k 0 r || edge k 1 r || edge k 2 r
end L652.Residual
namespace L652
abbrev target (s : Fin 3) : Table := Residual.matching s
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem zz31n0 : ∀ (k : Fin 3) (v : Bool) (j : Fin 6), ∃ m n : Fin 64,
    target k (Residual.rowOf m)=v ∧ target k (Residual.rowOf n)=v ∧
    Residual.rowOf m j ≠ Residual.rowOf n j := by decide +kernel
theorem target_fiberRaw (k : Fin 3) : fiberRaw (target k) := by
  intro b f mem
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
  obtain ⟨m,n,hm,hn,ne⟩ := zz31n0 k b j
  exact ⟨_,_,hm,hn,ne⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem zz31n1 : ∀ (i j : Fin 3), i ≠ j → ∀ v : Bool, ∃ m n : Fin 64,
    target i (Residual.rowOf m)=v ∧ target i (Residual.rowOf n)=v ∧
    target j (Residual.rowOf m) ≠ target j (Residual.rowOf n) := by decide +kernel
theorem target_other_varies {i j : Fin 3} (ne : i≠j) (v : Bool) :
    Varies (target i) v (target j) := by
  obtain ⟨m,n,hm,hn,diff⟩ := zz31n1 i j ne v
  exact ⟨_,_,hm,hn,diff⟩
theorem ResidualExtends.mono {k l F A B bit} (h : ResidualExtends k F A B bit) (le : l≤k) :
    ResidualExtends l F A B bit := by
  intro p w hp pc U V hu hv correct
  exact h p w hp (Nat.le_trans pc le) U V hu hv correct
end L652
namespace L652
def forwardShift (i : Fin 3) : Fin 3 := ⟨(i.val+1)%3, by omega⟩
def backShift (i : Fin 3) : Fin 3 := ⟨(i.val+2)%3, by omega⟩
def MatchingResiduals : Prop := ∀ (i : Fin 3) (b : Bool),
  ResidualFloor 10 (target i) (target (forwardShift i)) (target (backShift i)) b ∧
  ResidualExtends 10 (target i) (target (forwardShift i)) (target (backShift i)) b
structure ThreeBlocks (p : List Op) where
  root : Fin 3 → Nat
  correct : ∀ i, wireTable inputTables (graphOf inputTables.length p) (root i)=target i
  block : ∀ i, PrivateBlock (graphOf inputTables.length p) p.length (root i)
  disjoint : ∀ i j, i≠j → Disjoint (block i).nodes (block j).nodes
theorem blocks_of_small (hc : Realizable 14) (numeric : MatchingResiduals) :
    ∃ p w, Built p w ∧ p.length ≤ 14 ∧ Nonempty (ThreeBlocks p) := by
  classical
  obtain ⟨p,w,hp,small,h0,h1,h2,minimal⟩ := choose_minimal hc
  obtain ⟨r0,b0,e0⟩ := hp.output_index h0
  obtain ⟨r1,b1,e1⟩ := hp.output_index h1
  obtain ⟨r2,b2,e2⟩ := hp.output_index h2
  let P := graphOf inputTables.length p
  let r := fun i : Fin 3 => if i=0 then r0 else if i=1 then r1 else r2
  have cases3 : ∀ i : Fin 3, i=0 ∨ i=1 ∨ i=2 := by decide
  have bound (i : Fin 3) : r i<inputTables.length+p.length := by
    rcases cases3 i with hi|hi|hi <;> subst i <;> first | exact b0 | exact b1 | exact b2
  have goal (i : Fin 3) : wireTable inputTables P (r i) = target i := by
    rcases cases3 i with hi|hi|hi <;> subst i <;> first | exact e0 | exact e1 | exact e2
  have opt (i : Fin 3) : Optimal p.length (target i)
      (target (forwardShift i)) (target (backShift i)) := by
    rcases cases3 i with hi|hi|hi <;> subst i
    · exact minimal
    · intro q z hq l a b c; exact minimal q z hq l c a b
    · intro q z hq l a b c; exact minimal q z hq l b c a
  have n1 : ∀ i : Fin 3, i≠forwardShift i := by decide
  have n2 : ∀ i : Fin 3, i≠backShift i := by decide
  have make (i : Fin 3) : ∃ b : PrivateBlock P p.length (r i),
      r (forwardShift i) ∉ b.nodes ∧ r (backShift i) ∉ b.nodes := by
    apply hp.output_block P rfl _ _ _ small (bound _) (bound _) (bound _)
    all_goals simp only [goal]
    · exact target_fiberRaw i
    · exact target_other_varies (n1 i)
    · exact target_other_varies (n2 i)
    · exact fun v => (numeric i v).1
    · exact fun v => (numeric i v).2.mono (by omega)
    · exact opt i
  choose B h1 h2 using make
  refine ⟨p,w,hp,small,⟨⟨r,goal,B,?_⟩⟩⟩
  intro i j ne
  apply (B i).disjoint
  have others : ∀ i j : Fin 3, i≠j → j=forwardShift i ∨ j=backShift i := by decide
  rcases others i j ne with e|e
  · simpa [e] using h1 i
  · simpa [e] using h2 i
theorem ThreeBlocks.boundary_source {p w} (h : Built p w) (B : ThreeBlocks p) (i : Fin 3)
    {j} (hj : j ∈ (B.block i).boundary) :
    j < inputTables.length+p.length ∧ ∀ k, j ∉ (B.block k).nodes := by
  let b := B.block i
  have parts : j ∈ ((graphOf inputTables.length p b.left).refs.toFinset ∪
      (graphOf inputTables.length p b.right).refs.toFinset) ∧ j∉b.nodes := by
    exact Finset.mem_sdiff.mp hj
  have src : ∃ c, c ∈ b.nodes ∧ j ∈ (graphOf inputTables.length p c).refs := by
    rcases Finset.mem_union.mp parts.1 with hl | hr
    · exact ⟨b.left,b.left_mem,List.mem_toFinset.mp hl⟩
    · exact ⟨b.right,b.right_mem,List.mem_toFinset.mp hr⟩
  obtain ⟨c,hc,ref⟩ := src
  have lim := b.bounds c hc
  have lt := (h.window c lim.1 j ref).1
  refine ⟨by omega,?_⟩
  intro k hin
  by_cases eq : k=i
  · subst k; exact parts.2 hin
  · have also := (B.block k).forward hin lim ref lt
    exact Finset.disjoint_left.mp (B.disjoint k i eq) also hc
end L652
namespace L652
def PrefixObstruction : Prop :=
  ∀ gs, History gs → gs.length ≤ 5 → ¬ (∀ i : Fin 3,
    ∃ K ⊆ (wiresOf gs).toFinset, K.card ≤ 4 ∧ Determines (~~~(0 : Word)) K (matchWord i))
private theorem zz33n0 : ∀ i, pack (target i)=matchWord i := by decide +kernel
theorem ThreeBlocks.prelude {p w} (h : Built p w) (small : p.length≤14) (B : ThreeBlocks p) :
    ∃ gs, History gs ∧ gs.length ≤ 5 ∧ ∀ i : Fin 3,
      ∃ K ⊆ (wiresOf gs).toFinset, K.card ≤ 4 ∧ Determines (~~~(0 : Word)) K (matchWord i) := by
  classical
  let P := graphOf inputTables.length p
  let S := fun i => (B.block i).nodes
  let U := (S 0 ∪ S 1) ∪ S 2
  have full {j} : j∈U ↔ ∃ i, j∈S i := by
    constructor
    · intro mem
      rcases Finset.mem_union.mp mem with m | m
      · rcases Finset.mem_union.mp m with m | m
        · exact ⟨0,m⟩
        · exact ⟨1,m⟩
      · exact ⟨2,m⟩
    · rintro ⟨i,m⟩
      have cases3 : ∀ i : Fin 3,i=0 ∨ i=1 ∨ i=2 := by decide
      rcases cases3 i with e|e|e <;> subst i <;> simp [U,m]
  have d01 : Disjoint (S 0) (S 1) := B.disjoint _ _ (by decide)
  have d02 : Disjoint (S 0) (S 2) := B.disjoint _ _ (by decide)
  have d12 : Disjoint (S 1) (S 2) := B.disjoint _ _ (by decide)
  have d012 : Disjoint (S 0 ∪ S 1) (S 2) := Finset.disjoint_union_left.mpr ⟨d02,d12⟩
  have enough : 9≤U.card := by
    have a : 3≤(S 0).card := (B.block 0).at_least_three
    have b : 3≤(S 1).card := (B.block 1).at_least_three
    have c : 3≤(S 2).card := (B.block 2).at_least_three
    dsimp only [U]
    rw [Finset.card_union_of_disjoint d012,Finset.card_union_of_disjoint d01]
    omega
  let Q := pin P (· ∈ U) false
  have bound {j} (hj : j∈U) : inputTables.length≤j ∧ j<inputTables.length+p.length := by
    obtain ⟨i,hi⟩ := full.mp hj
    exact (B.block i).bounds _ hi
  have untouched {j} (hj : j∉U) : wireTable inputTables P j = wireTable inputTables Q j := by
    funext x
    apply wire_outside (· ∈ U) (fun i he => by simp [Q,pin,he]) _ j hj
    intro i ho k hk lt affected
    obtain ⟨g,hg⟩ := full.mp affected
    have klo := (bound affected).1
    have ilo : inputTables.length ≤ i := by omega
    have ihi := (h.window i ilo k hk).2
    have inside := (B.block g).forward hg ⟨ilo,ihi⟩ hk lt
    exact ho (full.mpr ⟨g,inside⟩)
  have savings := cost_absolute (P:=Q) (base:=inputTables.length) (n:=p.length) U
    (fun i hi => bound hi) (fun i hi => by simp [Q,pin,hi,Cmd.paid])
  obtain ⟨q,z,hq,hlen,cover⟩ := compressGraph inputTables Q p.length
  obtain ⟨gs,hgs,gl,gw⟩ := history_of_built hq.toBuilt
  refine ⟨gs,hgs,by omega,?_⟩
  intro i
  let b := B.block i
  let ts := b.boundary.image (wireTable inputTables P)
  let keep := ts.filter (· ∈ z)
  let K := keep.image pack
  have bounded : K.card≤4 :=
    (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans
      (Finset.card_image_le.trans b.boundary_card))
  have subset : K⊆(wiresOf gs).toFinset := by
    intro v hv
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
    rw [gw]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,(Finset.mem_filter.mp ht).2,rfl⟩)
  refine ⟨K,subset,bounded,?_⟩
  intro r s _ _ same
  rw [← zz33n0,pack_bit _ _ r.isLt,pack_bit _ _ s.isLt]
  rw [← B.correct i]
  apply b.determined
  intro j hj
  obtain ⟨jmax,privateFree⟩ := B.boundary_source h i hj
  have outside : j ∉ U := by
    rintro m; obtain ⟨g,hg⟩ := full.mp m; exact privateFree g hg
  have available : Available z (wireTable inputTables P j) := by
    rw [untouched outside]; exact cover j jmax
  rcases available with hz | ho | hm
  · exact (congrFun hz (inputRow r)).trans (congrFun hz (inputRow s)).symm
  · exact (congrFun ho (inputRow r)).trans (congrFun ho (inputRow s)).symm
  · have included : wireTable inputTables P j ∈ keep := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,hm⟩
    have byWord := same (pack (wireTable inputTables P j)) (Finset.mem_image.mpr ⟨_,included,rfl⟩)
    simpa only [pack_bit _ _ r.isLt,pack_bit _ _ s.isLt,wireTable,P] using byWord
theorem exact_from_residuals_and_prefix (residuals : MatchingResiduals) (obst : PrefixObstruction) :
    Realizable 15 ∧ ¬ Realizable 14 := by
  refine ⟨upper,fun small => ?_⟩
  obtain ⟨p,w,h,hlen,⟨B⟩⟩ := blocks_of_small small residuals
  obtain ⟨gs,hg,glen,supports⟩ := B.prelude h hlen
  exact obst gs hg glen supports
end L652
namespace L652
theorem target_eq_matchTable : ∀ i : Fin 3, target i = matchTable i := by
  intro i
  have cases3 : ∀ k : Fin 3,k=0 ∨ k=1 ∨ k=2 := by decide
  rcases cases3 i with h|h|h <;> subst i <;> rfl
def ResidualObstruction : Prop :=
  ∀ i b, NoResidualShare i (forwardShift i) (backShift i) b
theorem exact_from_two_obstructions (residual : ResidualObstruction)
    (prefixProof : PrefixObstruction) : Realizable 15 ∧ ¬ Realizable 14 := by
  apply exact_from_residuals_and_prefix _ prefixProof
  intro i b
  simp only [target_eq_matchTable]
  have distinct : ∀ i, i≠forwardShift i ∧ i≠backShift i := by decide
  exact residual_of_splits _ _ _ (distinct i).1 (distinct i).2 _ (residual i b)
end L652
namespace L652
abbrev renamedSet (s : SymIndex) (P : Finset Word) := P.image (relabel s)
theorem in_renamed {s : SymIndex} {w : Word} {p : Finset Word} :
    relabel s w ∈ renamedSet s p ↔ w ∈ p  := by
  constructor
  · intro h
    obtain ⟨a,ha,e⟩ := Finset.mem_image.mp h
    exact (relabel_injective s e) ▸ ha
  · intro h
    exact Finset.mem_image.mpr ⟨_,h,rfl⟩
theorem renamed_sources (s : SymIndex) (g : LogicalGate) :
    renamedSet s (sources g) = sources (mapGate s g) := by
  cases g <;> simp [renamedSet,sources,mapGate]
theorem renamed_prior (s : SymIndex) (g : LogicalGate) (p : Finset Word) :
    renamedSet s (prior g p) = prior (mapGate s g) (renamedSet s p) := by
  by_cases h : g.out ∈ p
  · have member := (@in_renamed s g.out p).mpr h
    simp only [prior,h,ite_true,←mapGate_out,member]
    rw [←renamed_sources]
    unfold renamedSet
    rw [Finset.image_union,Finset.image_erase (relabel_injective s)]
  · have absent := mt (@in_renamed s g.out p).mp h
    simp only [prior,h,ite_false,←mapGate_out,absent]
theorem renamed_demand (s : SymIndex) (gs : List LogicalGate) (p : Finset Word) :
    renamedSet s (demand gs p) = demand (gs.map (mapGate s)) (renamedSet s p) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change renamedSet s (prior g (demand gs p)) = prior (mapGate s g) _
    rw [renamed_prior,ih]
    rfl
theorem renamed_cone (s : SymIndex) (gs : List LogicalGate) (p : Finset Word) :
    (cone gs p).map (mapGate s) = cone (gs.map (mapGate s)) (renamedSet s p) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,cone,←renamed_demand,←mapGate_out,in_renamed]
    split <;> simp [ih]
theorem renamed_produced (s : SymIndex) (gs : List LogicalGate) :
    produced (gs.map (mapGate s)) = renamedSet s (produced gs) := by
  ext x
  simp only [mem_produced,List.mem_map,renamedSet,Finset.mem_image]
  constructor
  · rintro ⟨_,⟨g,hg,rfl⟩,rfl⟩
    exact ⟨_,⟨g,hg,rfl⟩,mapGate_out s g⟩
  · rintro ⟨_,⟨g,hg,rfl⟩,rfl⟩
    exact ⟨_,⟨g,hg,rfl⟩,(mapGate_out s g).symm⟩
theorem renamed_gates (s : SymIndex) (gs : List LogicalGate) (t : Word) :
    gatesFor (gs.map (mapGate s)) (relabel s t) = renamedSet s (gatesFor gs t) := by
  have h := renamed_cone s gs {t}
  simp [renamedSet] at h
  unfold gatesFor
  rw [←h,renamed_produced]
theorem renamed_shared (s : SymIndex) (gs : List LogicalGate) (t u : Word) :
    shared (gs.map (mapGate s)) (relabel s t) (relabel s u) = renamedSet s (shared gs t u) := by
  simp only [shared,renamed_gates,renamedSet,Finset.image_inter _ _ (relabel_injective s)]
theorem renamed_kept (s : SymIndex) (gs : List LogicalGate) (p : Finset Word) :
    kept (renamedSet s p) (gs.map (mapGate s)) = (kept p gs).map (mapGate s) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [kept,List.map_cons,List.filter_cons,←mapGate_out,in_renamed] at ih ⊢
    split <;> simp only [List.map_cons,List.cons.injEq,true_and,ih]
theorem equalOn_relabel_iff (s : SymIndex) (m v w : Word) :
    equalOn (relabel s m) (relabel s v) (relabel s w) ↔ equalOn m v w := by
  constructor
  · intro h r hr
    obtain ⟨k,rfl⟩ := rowMap_surj s r
    simpa only [relabel_bit] using h k ((relabel_bit _ _ _).trans hr)
  · intro h r hr
    simpa only [relabel_bit] using h (rowMap s r) ((relabel_bit _ _ _).symm.trans hr)
theorem renamed_fresh {gs : List LogicalGate} {m : Word} (s : SymIndex) (fresh : FiberFresh m gs) :
    FiberFresh (relabel s m) (gs.map (mapGate s)) := by
  induction fresh with
  | empty => exact .empty
  | @push gs old g new ih =>
    simp only [List.map_append,List.map_cons,List.map_nil]
    apply FiberFresh.push ih
    rw [←mapGate_out]
    rintro ⟨y,hy,eq⟩
    have lift (y : Word) (hy : AllowedWord (wiresOf (gs.map (mapGate s))) y) :
        ∃ z, AllowedWord (wiresOf gs) z ∧ relabel s z = y := by
      rcases hy with rfl | rfl | hm
      · exact ⟨0,Or.inl rfl,relabel_zero s⟩
      · exact ⟨_,Or.inr (Or.inl rfl),relabel_one s⟩
      · obtain ⟨z,hz,e⟩ := List.mem_map.mp ((perm_wires s gs).mem_iff.mpr hm)
        exact ⟨z,Or.inr (Or.inr hz),e⟩
    obtain ⟨z,hz,rfl⟩ := lift y hy
    exact new ⟨_,hz,(equalOn_relabel_iff ..).mp eq⟩
end L652
namespace L652.PrivateCertificate
abbrev W := UInt64
def raw : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def key (a b op : Nat) : Nat := (32*b+a)*3+op
def value (ws : List W) (c : Nat) : W :=
  let a := ws.getD (c/3 % 32) 0
  let b := ws.getD (c/3/32) 0
  if c % 3=0 then a &&& b else if c % 3=1 then a ||| b else ~~~a
def pairs (n : Nat) : List Nat :=
  (List.range n).flatMap fun b =>
    (List.range (b+1)).flatMap fun a =>
      if a=b then [key a b 2] else [key a b 0,key a b 1]
def next (min : Nat) (ws : List W) : List Nat :=
  (pairs ws.length).filter fun c =>
    let x := value ws c
    decide (min ≤ c) && x != 0 && x != ~~~0 && !(ws.contains x)
theorem mem_next_of_operands {ws : List W} {a b op min : Nat}
    (hb : b < ws.length) (hab : a ≤ b)
    (hop : (a=b ∧ op=2) ∨ (a<b ∧ (op=0 ∨ op=1)))
    (hm : min ≤ key a b op) (nz : value ws (key a b op) ≠ 0)
    (nu : value ws (key a b op) ≠ ~~~0) (fresh : value ws (key a b op) ∉ ws) :
    key a b op ∈ next min ws := by
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨b,List.mem_range.mpr hb,List.mem_flatMap.mpr ⟨a,List.mem_range.mpr (by omega),?_⟩⟩
    rcases hop with ⟨rfl,rfl⟩ | ⟨hlt,rfl | rfl⟩
    · simp
    · simp [Nat.ne_of_lt hlt]
    · simp [Nat.ne_of_lt hlt]
  · have nn : value ws (key a b op) ≠ -1 := by simpa using nu
    simp [hm,nz,nn,fresh]
inductive Path : Nat → List W → List Nat → List W → Prop
  | nil (min ws) : Path min ws [] ws
  | cons {min ws c cs dst} (step : c ∈ next min ws)
      (tail : Path c (ws++[value ws c]) cs dst) : Path min ws (c::cs) dst
def firstKeys : List Nat := [key 0 0 2,key 0 1 0,key 0 1 1,key 0 3 0,key 0 3 1]
end L652.PrivateCertificate
namespace L652
theorem key_decode {w : List Word} {g : LogicalGate} (args : sources g ⊆ w.toFinset)
    (small : w.length ≤ 32) :
    let p := operandPair w g
    let c := gateKey w g
    c/3 % 32 = p.1 ∧ c/3/32 = p.2 ∧ c % 3 = operation g ∧ p.1 ≤ p.2 ∧ p.2 < w.length := by
  cases g with
  | neg a =>
    have ha : a ∈ w := List.mem_toFinset.mp (args (by simp [sources]))
    have bound := List.idxOf_lt_length_of_mem ha
    simp only [gateKey,operandPair,operation]
    omega
  | meet a b | join a b =>
    have ha : a ∈ w := List.mem_toFinset.mp (args (by simp [sources]))
    have hb : b ∈ w := List.mem_toFinset.mp (args (by simp [sources]))
    have h1 := List.idxOf_lt_length_of_mem ha
    have h2 := List.idxOf_lt_length_of_mem hb
    simp only [gateKey,operandPair,operation]
    omega
theorem get_word_at {w : List Word} {a : Word} (h : a ∈ w) :
    (w.map UInt64.ofBitVec).getD (w.idxOf a) 0 = UInt64.ofBitVec a := by
  have hi := List.idxOf_lt_length_of_mem h
  simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem_idxOf hi]
theorem eval_gate_key {w : List Word} {g : LogicalGate} (args : sources g ⊆ w.toFinset)
    (small : w.length ≤ 32) :
    PrivateCertificate.value (w.map UInt64.ofBitVec) (gateKey w g) = UInt64.ofBitVec g.out := by
  obtain ⟨ha,hb,ho,_,_⟩ := key_decode args small
  unfold PrivateCertificate.value
  rw [ha,hb,ho]
  cases g with
  | neg a =>
    have ma : a ∈ w := List.mem_toFinset.mp (args (by simp [sources]))
    simp only [operation,operandPair,get_word_at ma]
    rfl
  | meet a b | join a b =>
    have ma : a ∈ w := List.mem_toFinset.mp (args (by simp [sources]))
    have mb : b ∈ w := List.mem_toFinset.mp (args (by simp [sources]))
    by_cases order : w.idxOf a ≤ w.idxOf b
    · simp only [operation,operandPair,min_eq_left order,max_eq_right order,get_word_at ma,get_word_at mb]
      rfl
    · have rev : w.idxOf b ≤ w.idxOf a := by omega
      simp only [operation,operandPair,min_eq_right rev,max_eq_left rev,get_word_at mb,get_word_at ma]
      first | exact UInt64.and_comm _ _ | exact UInt64.or_comm _ _
def FreshSeries (base : List Word) (gs : List LogicalGate) : Prop :=
  (gs.map LogicalGate.out).Nodup ∧ ∀ g ∈ gs, g.out ≠ 0 ∧ g.out ≠ ~~~0 ∧ g.out ∉ base
theorem history_fresh {gs : List LogicalGate} (h : History gs) : FreshSeries rawWords gs := by
  refine ⟨(history_schedule h).2.1,?_⟩
  induction h with
  | empty => simp
  | @push gs g old args fresh ih =>
    intro q hq
    rcases List.mem_append.mp hq with before | last
    · exact ih _ before
    · obtain rfl := List.mem_singleton.mp last
      exact ⟨fresh.1,fresh.2.1,fun h => fresh.2.2 (List.mem_append_left _ h)⟩
theorem FreshSeries.perm {base gs qs} (fresh : FreshSeries base gs) (h : qs.Perm gs) :
    FreshSeries base qs := ⟨(h.map _).nodup_iff.mpr fresh.1,fun g hg => fresh.2 g (h.mem_iff.mp hg)⟩
theorem FreshSeries.tail {base g gs} (fresh : FreshSeries base (g::gs)) :
    FreshSeries (base++[g.out]) gs := by
  obtain ⟨unq,good⟩ := fresh
  simp only [List.map_cons,List.nodup_cons] at unq
  refine ⟨unq.2,?_⟩
  intro q hq
  obtain ⟨z,o,baseOk⟩ := good q (List.mem_cons_of_mem _ hq)
  refine ⟨z,o,?_⟩
  simp only [List.mem_append,List.mem_singleton,not_or]
  exact ⟨baseOk,fun e => unq.1 (List.mem_map.mpr ⟨q,hq,e⟩)⟩
def encodeGates (base : List Word) : List LogicalGate → List Nat
  | [] => []
  | g::gs => gateKey base g :: encodeGates (base++[g.out]) gs
theorem key_operands {w : List Word} {g : LogicalGate} (args : sources g ⊆ w.toFinset)
    (fresh : g.out ∉ w) :
    let p := operandPair w g
    (p.1 = p.2 ∧ operation g = 2) ∨ (p.1 < p.2 ∧ (operation g = 0 ∨ operation g = 1)) := by
  cases g with
  | neg a => exact .inl ⟨rfl,rfl⟩
  | meet a b | join a b =>
    have ma : a ∈ w := List.mem_toFinset.mp (args (by simp [sources]))
    have mb : b ∈ w := List.mem_toFinset.mp (args (by simp [sources]))
    have neq : a ≠ b := by
      rintro rfl
      apply fresh
      simpa [LogicalGate.out] using ma
    have unequal : w.idxOf a ≠ w.idxOf b := by
      intro eq
      have h1 := get_word_at ma
      rw [eq,get_word_at mb] at h1
      exact neq (congrArg UInt64.toBitVec h1.symm)
    simp only [operandPair,operation]
    right
    exact ⟨by omega,by decide⟩
theorem encoded_path {gs : List LogicalGate} {w : List Word} {last : Nat}
    (ord : KeyOrdered w last gs) (fresh : FreshSeries w gs) (sz : w.length+gs.length ≤ 32) :
    PrivateCertificate.Path last (w.map UInt64.ofBitVec) (encodeGates w gs)
      ((w ++ gs.map LogicalGate.out).map UInt64.ofBitVec) := by
  induction ord with
  | nil => simpa [encodeGates] using PrivateCertificate.Path.nil _ _
  | @cons w last g gs ready mn tail ih =>
    have small : w.length ≤ 32 := by simp only [List.length_cons] at sz; omega
    have ev := eval_gate_key ready small
    obtain ⟨z,o,notSeen⟩ := fresh.2 g (by simp)
    let p := operandPair w g
    have definition : PrivateCertificate.key p.1 p.2 (operation g) = gateKey w g := by
      simp [PrivateCertificate.key,gateKey,p,Nat.mul_comm]
    have step : gateKey w g ∈ PrivateCertificate.next last (w.map UInt64.ofBitVec) := by
      rw [←definition]
      apply PrivateCertificate.mem_next_of_operands
      · simpa only [List.length_map] using (key_decode ready small).2.2.2.2
      · exact (key_decode ready small).2.2.2.1
      · exact key_operands ready notSeen
      · exact definition ▸ mn
      · rw [definition,ev]
        exact fun e => z (congrArg UInt64.toBitVec e)
      · rw [definition,ev]
        exact fun e => o (congrArg UInt64.toBitVec e)
      · rw [definition,ev]
        intro hm
        obtain ⟨a,ha,e⟩ := List.mem_map.mp hm
        have ae : a = g.out := congrArg UInt64.toBitVec e
        exact notSeen (ae ▸ ha)
    have next := ih fresh.tail (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using sz)
    have eq : (w++[g.out]).map UInt64.ofBitVec =
        w.map UInt64.ofBitVec ++ [PrivateCertificate.value (w.map UInt64.ofBitVec) (gateKey w g)] := by
      simp [ev]
    rw [eq] at next
    simpa [encodeGates,List.append_assoc] using PrivateCertificate.Path.cons step next
end L652
namespace L652
theorem KeyOrdered.scheduled {w last gs} (ord : KeyOrdered w last gs) : scheduled w.toFinset gs := by
  induction ord with
  | nil => trivial
  | cons ready bound later ih => exact ⟨ready,by simpa using ih⟩
theorem history_scheduled {gs : List LogicalGate} (ok : scheduled rawWords.toFinset gs)
    (fresh : FreshSeries rawWords gs) : History gs := by
  induction gs using List.reverseRecOn with
  | nil => exact .empty
  | append_singleton gs g ih =>
    obtain ⟨p,tail⟩ := scheduled_append.mp ok
    obtain ⟨nd,clean⟩ := fresh
    simp only [List.map_append,List.map_cons,List.map_nil,List.nodup_append] at nd
    have sub : FreshSeries rawWords gs := ⟨nd.1,fun q h => clean q (List.mem_append_left _ h)⟩
    apply History.push (ih p sub)
    · intro x hx
      have h := tail.1 (mem_sources.mpr hx)
      rw [available_wires] at h
      exact List.mem_toFinset.mp h
    · obtain ⟨z,o,raw⟩ := clean g (by simp)
      refine ⟨z,o,?_⟩
      intro hm
      rcases List.mem_append.mp hm with hr | prev
      · exact raw hr
      · exact nd.2.2 _ prev _ (by simp) rfl
def DecodesThree (gs : List LogicalGate) : Prop := ∀ i : Fin 3,
  ∃ K ⊆ (wiresOf gs).toFinset, K.card ≤ 4 ∧ Determines (~~~(0 : Word)) K (matchWord i)
theorem DecodesThree.perm {gs qs : List LogicalGate} (h : DecodesThree gs) (per : qs.Perm gs) :
    DecodesThree qs := by
  intro i
  obtain ⟨k,hk,sz,det⟩ := h i
  refine ⟨k,?_,sz,det⟩
  have ws : (wiresOf qs).Perm (wiresOf gs) :=
    (List.Perm.refl rawWords).append (per.map _)
  exact fun x hx => List.mem_toFinset.mpr (ws.mem_iff.mpr (List.mem_toFinset.mp (hk hx)))
theorem DecodesThree.relabel {gs : List LogicalGate} (h : DecodesThree gs) (s : SymIndex) :
    DecodesThree (gs.map (mapGate s)) := by
  intro k
  obtain ⟨j,eq⟩ := matchings_survive s k
  obtain ⟨pool,hp,sz,det⟩ := h j
  refine ⟨pool.image (L652.relabel s),?_,Finset.card_image_le.trans sz,?_⟩
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact List.mem_toFinset.mpr ((perm_wires s gs).mem_iff.mp (List.mem_map.mpr
      ⟨w,List.mem_toFinset.mp (hp hw),rfl⟩))
  · simpa only [eq,relabel_one] using map_determines s det
theorem minimum_first_le {x : LogicalGate} {w : List Word} {qs : List LogicalGate} {last : Nat}
    (sorted : KeyOrdered w last qs) (raw : sources x ⊆ w.toFinset) (present : x ∈ qs) :
    last ≤ gateKey w x := by
  induction sorted with
  | nil => contradiction
  | @cons w last g gs ready lo tail ih =>
    rcases List.mem_cons.mp present with rfl | mem
    · exact lo
    · have same : gateKey (w++[g.out]) x = gateKey w x := by
        have stable (a : Word) (h : a ∈ sources x) : (w++[g.out]).idxOf a = w.idxOf a :=
          List.idxOf_append_of_mem (List.mem_toFinset.mp (raw h))
        cases x with
        | neg a =>
          have ma := stable a (by simp [sources])
          simp only [gateKey,operandPair,ma]
        | meet a b | join a b =>
          have ma := stable a (by simp [sources])
          have mb := stable b (by simp [sources])
          simp only [gateKey,operandPair,ma,mb]
      apply lo.trans
      rw [←same]
      apply ih _ mem
      intro v hv
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (raw hv)))
theorem first_le_ready {w : List Word} {x g : LogicalGate} {gs : List LogicalGate} {last : Nat}
    (ord : KeyOrdered w last (g::gs)) (raw : sources x ⊆ w.toFinset) (present : x ∈ g::gs) :
    gateKey w g ≤ gateKey w x := by
  cases ord with
  | cons ready lb rest =>
    exact minimum_first_le (.cons ready (Nat.le_refl _) rest) raw present
theorem raw_idx : ∀ j : Fin 6, rawWords.idxOf (rawAt j) = j.val := by decide +kernel
private def zz38n0 (a b op : Nat) := (32 * max a b + min a b)*3+op
set_option maxRecDepth 10000 in
private theorem zz38n1 : ∀ (i j : Fin 6) (op : Fin 3),
    (i = j ↔ op.val = 2) → zz38n0 i j op ∉ PrivateCertificate.firstKeys →
    ∃ s : SymIndex, zz38n0 (coordMap s i) (coordMap s j) op < zz38n0 i j op := by decide +kernel
private theorem zz38n2 : ∀ i : Fin 6, zz38n0 i i 2 ∉ PrivateCertificate.firstKeys →
    ∃ s : SymIndex, zz38n0 (coordMap s i) (coordMap s i) 2 < zz38n0 i i 2 := by decide +kernel
theorem smaller_first {g : LogicalGate} (ready : sources g ⊆ rawWords.toFinset)
    (fresh : g.out ∉ rawWords) (bad : gateKey rawWords g ∉ PrivateCertificate.firstKeys) :
    ∃ s : SymIndex, gateKey rawWords (mapGate s g) < gateKey rawWords g := by
  have locate {x : Word} (h : x ∈ sources g) : ∃ i, rawAt i = x :=
    exists_rawAt _ (List.mem_toFinset.mp (ready h))
  have rn (s : SymIndex) (i : Fin 6) : relabel s (rawAt i) = rawAt (coordMap s i) := relabel_raw s i
  cases g with
  | neg a =>
    obtain ⟨i,rfl⟩ := locate (x := a) (by simp [sources])
    simp only [gateKey,operandPair,operation,raw_idx] at bad
    obtain ⟨s,hs⟩ := zz38n2 i (by simpa [zz38n0,Nat.mul_comm] using bad)
    exact ⟨s,by simpa [zz38n0,gateKey,operandPair,operation,mapGate,rn,raw_idx,Nat.mul_comm] using hs⟩
  | meet a b =>
    obtain ⟨i,rfl⟩ := locate (x := a) (by simp [sources])
    obtain ⟨j,rfl⟩ := locate (x := b) (by simp [sources])
    have neq : i ≠ j := by
      rintro rfl
      apply fresh
      simpa [LogicalGate.out] using rawAt_mem i
    simp only [gateKey,operandPair,operation,raw_idx] at bad
    obtain ⟨s,hs⟩ := zz38n1 i j 0 (by simp [neq]) (by simpa [zz38n0,Nat.mul_comm] using bad)
    exact ⟨s,by simpa [zz38n0,gateKey,operandPair,operation,mapGate,rn,raw_idx,Nat.mul_comm] using hs⟩
  | join a b =>
    obtain ⟨i,rfl⟩ := locate (x := a) (by simp [sources])
    obtain ⟨j,rfl⟩ := locate (x := b) (by simp [sources])
    have neq : i ≠ j := by
      rintro rfl
      apply fresh
      simpa [LogicalGate.out] using rawAt_mem i
    simp only [gateKey,operandPair,operation,raw_idx] at bad
    obtain ⟨s,hs⟩ := zz38n1 i j 1 (by simp [neq]) (by simpa [zz38n0,Nat.mul_comm] using bad)
    exact ⟨s,by simpa [zz38n0,gateKey,operandPair,operation,mapGate,rn,raw_idx,Nat.mul_comm] using hs⟩
end L652
namespace L652
structure ResidualExample (f j k : Fin 3) (b : Bool) (gs : List LogicalGate) (t u : Word) : Prop where
  hist : History gs
  fresh : FiberFresh (domainWord f b) gs
  budget : gs.length ≤ 10
  mt : t ∈ wiresOf gs
  mu : u ∈ wiresOf gs
  vt : equalOn (domainWord f b) t (matchWord j)
  vu : equalOn (domainWord f b) u (matchWord k)
  overlap : shared gs t u ≠ ∅
theorem ResidualExample.swap {f j k b gs t u} (ex : ResidualExample f j k b gs t u) :
    ResidualExample f k j b gs u t := by
  refine ⟨ex.hist,ex.fresh,ex.budget,ex.mu,ex.mt,ex.vu,ex.vt,?_⟩
  simpa only [shared,Finset.inter_comm (gatesFor gs u)] using ex.overlap
theorem ResidualExample.mapped {f j k b gs t u} (ex : ResidualExample f j k b gs t u)
    (s : SymIndex) (f' j' k' : Fin 3)
    (ef : relabel s (matchWord f) = matchWord f')
    (ej : relabel s (matchWord j) = matchWord j') (ek : relabel s (matchWord k) = matchWord k') :
    ResidualExample f' j' k' b (gs.map (mapGate s)) (relabel s t) (relabel s u) := by
  have dom : relabel s (domainWord f b) = domainWord f' b := by cases b <;> simp [domainWord,relabel_neg,ef]
  have wire {v : Word} (h : v ∈ wiresOf gs) :
      relabel s v ∈ wiresOf (List.map (mapGate s) gs) :=
    (perm_wires s gs).mem_iff.mp (List.mem_map.mpr ⟨v,h,rfl⟩)
  refine ⟨relabel_history s ex.hist,dom ▸ renamed_fresh s ex.fresh,by simpa using ex.budget,
    wire ex.mt,wire ex.mu,?_,?_,?_⟩
  · rw [←dom,←ej]; exact (equalOn_relabel_iff ..).mpr ex.vt
  · rw [←dom,←ek]; exact (equalOn_relabel_iff ..).mpr ex.vu
  · simpa [renamed_shared,renamedSet] using ex.overlap
def sharedProgram (gs : List LogicalGate) (t u : Word) := kept (shared gs t u) gs
theorem sharedProgram_swap (gs : List LogicalGate) (t u : Word) :
    sharedProgram gs u t = sharedProgram gs t u := by simp only [sharedProgram,shared,Finset.inter_comm]
theorem sharedProgram_map (gs : List LogicalGate) (t u : Word) (s : SymIndex) :
    sharedProgram (gs.map (mapGate s)) (relabel s t) (relabel s u) =
      (sharedProgram gs t u).map (mapGate s) := by rw [sharedProgram,renamed_shared,renamed_kept]; rfl
theorem orient_zero (f : Fin 3) : ∃ s : SymIndex,
    relabel s (matchWord f) = matchWord 0 ∧ relabel s (matchWord (forwardShift f)) = matchWord 1 ∧
      relabel s (matchWord (backShift f)) = matchWord 2 := by
  have eq : ∀ f : Fin 3, ∃ s : SymIndex,
      matchFrom (fun i => rawAt (coordMap s i)) f = matchWord 0 ∧
      matchFrom (fun i => rawAt (coordMap s i)) (forwardShift f) = matchWord 1 ∧
      matchFrom (fun i => rawAt (coordMap s i)) (backShift f) = matchWord 2 := by decide +kernel
  simpa only [relabel_from] using eq f
def fixesZero (s : SymIndex) : Prop :=
  matchFrom (fun i => rawAt (coordMap s i)) 0 = matchWord 0 ∧
  ((matchFrom (fun i => rawAt (coordMap s i)) 1 = matchWord 1 ∧
    matchFrom (fun i => rawAt (coordMap s i)) 2 = matchWord 2) ∨
   (matchFrom (fun i => rawAt (coordMap s i)) 1 = matchWord 2 ∧
    matchFrom (fun i => rawAt (coordMap s i)) 2 = matchWord 1))
instance (s : SymIndex) : Decidable (fixesZero s) := by unfold fixesZero; infer_instance
def allowedSharedFirst (n : Nat) : Prop :=
  n ∈ ([2,96,97,288,289,291,292] : List Nat)
private def zz39n0 (a b op : Nat) := (32*max a b + min a b)*3+op
private theorem zz39n1 : ∀ (i j : Fin 6) (op : Fin 3), (i=j ↔ op.val=2) →
    ¬ allowedSharedFirst (zz39n0 i j op) → ∃ s : SymIndex, fixesZero s ∧
      zz39n0 (coordMap s i) (coordMap s j) op < zz39n0 i j op := by
  unfold allowedSharedFirst
  decide +kernel
theorem shared_first_relabel {g : LogicalGate} (ready : sources g ⊆ rawWords.toFinset)
    (fresh : g.out ∉ rawWords) (bad : ¬allowedSharedFirst (gateKey rawWords g)) :
    ∃ s, fixesZero s ∧ gateKey rawWords (mapGate s g) < gateKey rawWords g := by
  have locate {x : Word} (h : x ∈ sources g) : ∃ i, rawAt i = x :=
    exists_rawAt _ (List.mem_toFinset.mp (ready h))
  have rn (s : SymIndex) (i : Fin 6) : relabel s (rawAt i) = rawAt (coordMap s i) := relabel_raw s i
  cases g with
  | neg a =>
    obtain ⟨i,rfl⟩ := locate (x := a) (by simp [sources])
    have fix := zz39n1 i i 2 (by simp) (by
      simpa [zz39n0,gateKey,operandPair,operation,raw_idx,Nat.mul_comm] using bad)
    obtain ⟨s,good,hs⟩ := fix
    exact ⟨s,good,by simpa [zz39n0,gateKey,operandPair,operation,mapGate,rn,raw_idx,Nat.mul_comm] using hs⟩
  | meet a b =>
    obtain ⟨i,rfl⟩ := locate (x := a) (by simp [sources])
    obtain ⟨j,rfl⟩ := locate (x := b) (by simp [sources])
    have neq : i ≠ j := by
      rintro rfl
      apply fresh
      simpa [LogicalGate.out] using rawAt_mem i
    obtain ⟨s,good,hs⟩ := zz39n1 i j 0 (by simp [neq]) (by
      simpa [zz39n0,gateKey,operandPair,operation,raw_idx,Nat.mul_comm] using bad)
    exact ⟨s,good,by simpa [zz39n0,gateKey,operandPair,operation,mapGate,rn,raw_idx,Nat.mul_comm] using hs⟩
  | join a b =>
    obtain ⟨i,rfl⟩ := locate (x := a) (by simp [sources])
    obtain ⟨j,rfl⟩ := locate (x := b) (by simp [sources])
    have neq : i ≠ j := by
      rintro rfl
      apply fresh
      simpa [LogicalGate.out] using rawAt_mem i
    obtain ⟨s,good,hs⟩ := zz39n1 i j 1 (by simp [neq]) (by
      simpa [zz39n0,gateKey,operandPair,operation,raw_idx,Nat.mul_comm] using bad)
    exact ⟨s,good,by simpa [zz39n0,gateKey,operandPair,operation,mapGate,rn,raw_idx,Nat.mul_comm] using hs⟩
end L652
namespace L652
theorem DecodesThree.snoc {gs : List LogicalGate} (hd : DecodesThree gs) (g : LogicalGate) :
    DecodesThree (gs++[g]) := by
  intro i
  obtain ⟨K,hK,sz,det⟩ := hd i
  refine ⟨K,?_,sz,det⟩
  intro x hx
  have old := List.mem_toFinset.mp (hK hx)
  apply List.mem_toFinset.mpr
  simp only [wiresOf,List.map_append,List.append_assoc] at old ⊢
  simpa only [←List.append_assoc] using List.mem_append_left (List.map LogicalGate.out [g]) old
private theorem zz40n0 {gs : List LogicalGate} (hi : gs.length < 5) :
    ∃ a ∈ rawWords, (LogicalGate.neg a).out ≠ 0 ∧ (LogicalGate.neg a).out ≠ ~~~0 ∧
      (LogicalGate.neg a).out ∉ wiresOf gs := by
  let negs := (rawWords.map (fun w => (LogicalGate.neg w).out)).toFinset
  have cnt : negs.card = 6 := by decide
  have small : (produced gs).card ≤ gs.length := by
    simpa [produced] using (List.toFinset_card_le (l := gs.map LogicalGate.out))
  have notAll : ¬negs ⊆ produced gs := fun incl => by have hh := Finset.card_le_card incl; omega
  obtain ⟨v,hv,absent⟩ := Finset.not_subset.mp notAll
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
  have clean : ∀ j : Fin 6, (LogicalGate.neg (rawAt j)).out ≠ 0 ∧
      (LogicalGate.neg (rawAt j)).out ≠ ~~~0 ∧ (LogicalGate.neg (rawAt j)).out ∉ rawWords := by decide
  obtain ⟨j,rfl⟩ := exists_rawAt a ha
  obtain ⟨nz,no,nr⟩ := clean j
  refine ⟨_,ha,nz,no,?_⟩
  intro hm
  rcases List.mem_append.mp hm with hr | hp
  · exact nr hr
  · exact absent (List.mem_toFinset.mpr hp)
theorem pad_private {gs : List LogicalGate} (hist : History gs) (hc : DecodesThree gs) (n : Nat)
    (len : gs.length+n=5) : ∃ qs, History qs ∧ qs.length=5 ∧ DecodesThree qs := by
  induction n generalizing gs with
  | zero => exact ⟨gs,hist,by simpa using len,hc⟩
  | succ k ih =>
    obtain ⟨a,ha,nz,no,fresh⟩ := zz40n0 (gs := gs) (by omega)
    let g := LogicalGate.neg a
    have args : g.args ⊆ wiresOf gs := by
      intro v hv
      have eq : v=a := by simpa [g,LogicalGate.args] using hv
      exact eq ▸ List.mem_append_left _ ha
    exact ih (hist.push args ⟨nz,no,fresh⟩) (hc.snoc g) (by simp; omega)
end L652
namespace L652
theorem different_on_fiber (b : Bool) :
    ∃ i : Fin 64, (domainWord 0 b).getLsbD i.val = true ∧
      (matchWord 1).getLsbD i.val ≠ (matchWord 2).getLsbD i.val := by
  exact (by decide : ∀ b : Bool, ∃ i : Fin 64, (domainWord 0 b).getLsbD i.val = true ∧
    (matchWord 1).getLsbD i.val ≠ (matchWord 2).getLsbD i.val) b
theorem shared_program_spec {b gs t u} (ex : ResidualExample 0 1 2 b gs t u) :
    let p := sharedProgram gs t u
    scheduled rawWords.toFinset p ∧ FreshSeries rawWords p ∧ produced p = shared gs t u ∧
      p.length = (shared gs t u).card ∧ 0 < p.length ∧ p.length ≤ 9 := by
  obtain ⟨ok,nd,dis⟩ := history_schedule ex.hist
  have av {v} (h : v ∈ wiresOf gs) : v ∈ availableAfter rawWords.toFinset gs := by
    rw [available_wires]; exact List.mem_toFinset.mpr h
  obtain ⟨sched,graph⟩ := shared_history ok (av ex.mt) (av ex.mu) nd
  have source : (sharedProgram gs t u).Sublist gs := List.filter_sublist ..
  have fresh : FreshSeries rawWords (sharedProgram gs t u) :=
    ⟨nd.sublist (source.map _),fun g hg => (history_fresh ex.hist).2 g (source.subset hg)⟩
  have size : (sharedProgram gs t u).length = (shared gs t u).card := by
    rw [←graph]
    have nd' := fresh.1
    change _ = (List.map LogicalGate.out (sharedProgram gs t u)).toFinset.card
    rw [List.toFinset_card_of_nodup nd',List.length_map]
  have positive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ex.overlap)
  have nonempty : gs ≠ [] := by rintro rfl; exact ex.overlap rfl
  obtain ⟨i,hi,neq⟩ := different_on_fiber b
  have distinct : t ≠ u := by rintro rfl; exact neq ((ex.vt i hi).symm.trans (ex.vu i hi))
  have strict := shared_lt nd nonempty distinct
  have budget := ex.budget
  exact ⟨sched,fresh,graph,size,by omega,by omega⟩
structure SortedCommon (b : Bool) (first : LogicalGate) (tail : List LogicalGate) : Prop where
  example_exists : ∃ gs t u, ResidualExample 0 1 2 b gs t u ∧
    (first::tail).Perm (sharedProgram gs t u)
  ordered : KeyOrdered rawWords 0 (first::tail)
theorem sort_common {b gs t u} (ex : ResidualExample 0 1 2 b gs t u) :
    ∃ g q, (g::q).Perm (sharedProgram gs t u) ∧ SortedCommon b g q := by
  obtain ⟨ok,_,_,_,pos,cap⟩ := shared_program_spec ex
  obtain ⟨p,perm,sort⟩ := canonical_order (by change 6+(sharedProgram gs t u).length ≤ 32; omega) ok
  cases p with
  | nil => have bad := perm.length_eq; simp at bad; omega
  | cons g qs => exact ⟨g,qs,perm,⟨⟨_,_,_,ex,perm⟩,sort⟩⟩
theorem canonical_common {b gs t u} (ex : ResidualExample 0 1 2 b gs t u) :
    ∃ g qs, SortedCommon b g qs ∧ allowedSharedFirst (gateKey rawWords g) := by
  classical
  let admits := fun n => ∃ g qs, SortedCommon b g qs ∧ gateKey rawWords g=n
  obtain ⟨g₀,q₀,_,rawCase⟩ := sort_common ex
  have some_n : ∃ n, admits n := ⟨_,g₀,q₀,rawCase,rfl⟩
  obtain ⟨g,q,cert,first⟩ := Nat.find_spec some_n
  obtain ⟨source,t',u',counter,perm⟩ := cert.example_exists
  refine ⟨g,q,cert,?_⟩
  by_contra bad
  have fresh := ((shared_program_spec counter).2.1.perm perm).2 g (by simp)
  have ready := cert.ordered.scheduled.1
  obtain ⟨s,fix,smaller⟩ := shared_first_relabel ready fresh.2.2 bad
  have src : g ∈ sharedProgram source t' u' := perm.mem_iff.mp (by simp)
  have ready' : sources (mapGate s g) ⊆ rawWords.toFinset := by
    intro x h
    have hh := mem_sources.mp h
    rw [mapGate_args] at hh
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hh
    exact List.mem_toFinset.mpr ((mapped_raw s).mem_iff.mp (List.mem_map.mpr
      ⟨a,List.mem_toFinset.mp (ready (mem_sources.mpr ha)),rfl⟩))
  have contradicts {v w : Word} (cnt : ResidualExample 0 1 2 b (source.map (mapGate s)) v w)
      (contains : mapGate s g ∈ sharedProgram (source.map (mapGate s)) v w) : False := by
    obtain ⟨g',q',per,spec⟩ := sort_common cnt
    have early := first_le_ready spec.ordered ready' (per.mem_iff.mpr contains)
    have minimal := Nat.find_min' some_n (show admits (gateKey rawWords g') from ⟨g',q',spec,rfl⟩)
    omega
  rw [fixesZero,←relabel_from,←relabel_from,←relabel_from] at fix
  have stays : mapGate s g ∈ sharedProgram (source.map (mapGate s)) (relabel s t') (relabel s u') := by
    rw [sharedProgram_map]; exact List.mem_map.mpr ⟨g,src,rfl⟩
  rcases fix with ⟨fixed, ⟨a,c⟩ | ⟨a,c⟩⟩
  · exact contradicts (counter.mapped s 0 1 2 fixed a c) stays
  · exact contradicts (counter.mapped s 0 2 1 fixed a c).swap
      ((sharedProgram_swap ..).symm ▸ stays)
theorem residual_obstruction_of_no_canonical (deny : ∀ b g q, SortedCommon b g q →
    allowedSharedFirst (gateKey rawWords g) → False) : ResidualObstruction := by
  intro f b
  have n : f ≠ forwardShift f ∧ f ≠ backShift f :=
    (by decide : ∀ f : Fin 3, f ≠ forwardShift f ∧ f ≠ backShift f) f
  apply noShare_of_fresh n.1 n.2 b
  intro gs hist fresh cap t ht u hu vt vu
  by_contra overlap
  have ex : ResidualExample f (forwardShift f) (backShift f) b gs t u :=
    ⟨hist,fresh,cap,ht,hu,vt,vu,overlap⟩
  obtain ⟨s,ef,ej,ek⟩ := orient_zero f
  obtain ⟨g,q,exam,first⟩ := canonical_common (ex.mapped s 0 1 2 ef ej ek)
  exact deny b g q exam first
end L652
namespace L652
structure CommonBook where
  tips : List Word
  used : List Word
def consumes (g : LogicalGate) (w : Word) := decide (w ∈ sources g)
def CommonBook.push (book : CommonBook) (g : LogicalGate) : CommonBook :=
  ⟨g.out :: book.tips.filter (fun w => !(consumes g w)),
    book.tips.filter (consumes g) ++ book.used⟩
def bookOf (p : List LogicalGate) := p.foldl CommonBook.push ⟨[],[]⟩
theorem book_snoc (p : List LogicalGate) (g : LogicalGate) :
    bookOf (p++[g]) = (bookOf p).push g := by simp [bookOf]
theorem read_append (p q : List LogicalGate) : readBy (p++q) = readBy p ∪ readBy q := by
  induction p with
  | nil => simp [readBy]
  | cons a p ih => simp [readBy,ih,Finset.union_assoc]
theorem book_partition (p : List LogicalGate) :
    ((bookOf p).tips ++ (bookOf p).used).Perm (p.map LogicalGate.out) := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p g ih =>
    let a := (bookOf p).tips
    let b := (bookOf p).used
    have part : (a.filter (fun w => !(consumes g w)) ++ a.filter (consumes g)).Perm a := by
      simpa using List.filter_append_perm (fun w => !(consumes g w)) a
    have reorder := (((part.append_right b).trans ih).cons g.out).trans
      (List.perm_append_comm (l₁ := [g.out]) (l₂ := p.map LogicalGate.out))
    simpa [book_snoc,CommonBook.push,a,b,List.append_assoc] using reorder
theorem book_tips {p : List LogicalGate} (h : History p) :
    (bookOf p).tips.toFinset = produced p \ readBy p := by
  induction h with
  | empty => rfl
  | @push p g old args fresh ih =>
    have out : g.out ∉ readBy p := fun m => by
      have hm := read_available (history_schedule old).1 m
      rw [available_wires] at hm
      exact fresh.2.2 (List.mem_toFinset.mp hm)
    have src : g.out ∉ sources g := fun m => fresh.2.2 (args (mem_sources.mp m))
    have eq : (bookOf p).tips.toFinset = produced p \ readBy p := ih
    rw [book_snoc,read_append]
    ext x
    have ii := Finset.ext_iff.mp eq x
    simp only [CommonBook.push,produced,List.map_append,List.map_cons,List.map_nil,
      List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,List.mem_filter,consumes,Bool.not_eq_true',
      decide_eq_false_iff_not,Finset.mem_sdiff,Finset.mem_union,List.mem_append,List.mem_singleton,
      readBy,Finset.union_empty] at ii ⊢
    by_cases same : x=g.out
    · subst x; tauto
    · tauto
theorem tips_nonempty (p : List LogicalGate) (ne : p≠[]) : (bookOf p).tips ≠ [] := by
  obtain ⟨q,g,rfl⟩ : ∃ q g, p=q++[g] :=
    ⟨p.dropLast,p.getLast ne,(List.dropLast_concat_getLast ne).symm⟩
  simp [book_snoc,CommonBook.push]
theorem book_wires (p : List LogicalGate) :
    (rawWords++(bookOf p).tips++(bookOf p).used).Perm (wiresOf p) := by
  rw [List.append_assoc]
  exact (List.Perm.refl _).append (book_partition p)
theorem equalOn_determines {m t u : Word} {fs : Finset Word} (h : equalOn m t u)
    (d : Determines m fs t) : Determines m fs u := by
  intro i j hi hj eq
  exact (h i hi).symm.trans ((d i j hi hj eq).trans (h j hj))
theorem book_features {b : Bool} {g : LogicalGate} {q pre post : List LogicalGate}
    (common : SortedCommon b g q) (each : g::q=pre++post) :
    ∃ a c : Finset Word, a ⊆ (wiresOf pre).toFinset ∧ c ⊆ (wiresOf pre).toFinset ∧
      (bookOf pre).tips.toFinset ⊆ a ∧ (bookOf pre).tips.toFinset ⊆ c ∧
      Determines (domainWord 0 b) a (matchWord 1) ∧ Determines (domainWord 0 b) c (matchWord 2) ∧
      a.card+c.card+2*pre.length ≤ 12+(g::q).length := by
  obtain ⟨gs,t,u,ex,perm⟩ := common.example_exists
  obtain ⟨sched,nd,disj⟩ := history_schedule ex.hist
  have av {x} (h : x ∈ wiresOf gs) : x ∈ availableAfter rawWords.toFinset gs := by
    rw [available_wires]; exact List.mem_toFinset.mpr h
  have ordered := common.ordered.scheduled
  rw [each] at ordered
  have prefixOk := (scheduled_append.mp ordered).1
  have sub : pre ⊆ g::q := fun _ hm => each ▸ List.mem_append_left _ hm
  have valid := (shared_program_spec ex).2.1.perm perm
  have unique : (pre.map LogicalGate.out).Nodup := by
    have ht := valid.1
    rw [each,List.map_append] at ht
    exact (List.nodup_append.mp ht).1
  have clean := history_scheduled prefixOk ⟨unique,fun v hv => valid.2 v (sub hv)⟩
  have cnt : (produced pre).card=pre.length := by simp [produced,List.toFinset_card_of_nodup unique]
  obtain ⟨a,c,pa,pc,ta,tc,da,dc,bound⟩ := projections_of_prefix sched (av ex.mt) (av ex.mu) nd disj
    (p := pre) (fun _ hv => perm.mem_iff.mp (sub hv)) prefixOk (domainWord 0 b)
  have total := (shared_program_spec ex).2.2.2.1
  have same := perm.length_eq
  have lim := ex.budget
  have wires : rawWords.toFinset ∪ produced pre = (wiresOf pre).toFinset := available_wires pre
  exact ⟨a,c,wires ▸ pa,wires ▸ pc,(book_tips clean).symm ▸ ta,(book_tips clean).symm ▸ tc,
    equalOn_determines ex.vt da,equalOn_determines ex.vu dc,by omega⟩
end L652
namespace L652
def masked (m v : Word) : Nat := (v &&& m).toNat
theorem masked_eq {m x y : Word} : masked m x = masked m y ↔ equalOn m x y := by
  constructor
  · intro h i hi
    have eq : x &&& m = y &&& m := BitVec.eq_of_toNat_eq h
    simpa only [BitVec.getLsbD_and,hi,Bool.and_true] using
      congrArg (fun w : Word => w.getLsbD i.val) eq
  · exact fun h => congrArg BitVec.toNat (equalOn_and h)
theorem masked_zero (m : Word) : masked m 0 = 0 := by simp [masked]
theorem masked_one (m : Word) : masked m (~~~(0:Word)) = m.toNat := by
  change (BitVec.allOnes 64 &&& m).toNat = _
  rw [BitVec.allOnes_and]
theorem fiber_fresh_wires {b : Bool} {p : List LogicalGate} (h : FiberFresh (domainWord 0 b) p) :
    ((wiresOf p).map (masked (domainWord 0 b))).Nodup ∧ ∀ g ∈ p,
    masked (domainWord 0 b) g.out ≠ 0 ∧ masked (domainWord 0 b) g.out ≠ (domainWord 0 b).toNat := by
  let m := domainWord 0 b
  induction h with
  | empty => exact ⟨(by decide : ∀ b, ((wiresOf []).map (masked (domainWord 0 b))).Nodup) b,by simp⟩
  | @push p old g no ih =>
    have bound : ∀ v, AllowedWord (wiresOf p) v → masked m g.out ≠ masked m v :=
      fun v mem eq => no ⟨v,mem,masked_eq.mp eq⟩
    have fresh : masked m g.out ∉ (wiresOf p).map (masked m) := by
      intro hm
      obtain ⟨v,mem,eq⟩ := List.mem_map.mp hm
      exact bound v (Or.inr (Or.inr mem)) eq.symm
    have zero := bound 0 (Or.inl rfl)
    have one := bound (~~~(0:Word)) (Or.inr (Or.inl rfl))
    rw [masked_zero] at zero
    rw [masked_one] at one
    refine ⟨?_,?_⟩
    · have eq : wiresOf (p++[g])=wiresOf p++[g.out] := by simp [wiresOf,List.append_assoc]
      rw [eq,List.map_append,List.nodup_append]
      exact ⟨ih.1,by simp,by simpa [m] using fresh⟩
    · intro a ha
      rcases List.mem_append.mp ha with yes | here
      · exact ih.2 a yes
      · obtain rfl := List.mem_singleton.mp here
        exact ⟨zero,one⟩
theorem SortedCommon.clean {b g qs} (common : SortedCommon b g qs) :
    let m := domainWord 0 b
    ((wiresOf (g::qs)).map (masked m)).Nodup ∧ ∀ a ∈ g::qs,
      masked m a.out ≠ 0 ∧ masked m a.out ≠ m.toNat := by
  obtain ⟨gs,t,u,ex,perm⟩ := common.example_exists
  obtain ⟨all,strong⟩ := fiber_fresh_wires ex.fresh
  have hp : (sharedProgram gs t u).Sublist gs := List.filter_sublist ..
  have p : (wiresOf (sharedProgram gs t u)).Sublist (wiresOf gs) :=
    (hp.map _).append_left rawWords
  have ordered : (wiresOf (g::qs)).Perm (wiresOf (sharedProgram gs t u)) :=
    (List.Perm.refl rawWords).append (perm.map _)
  exact ⟨(ordered.map _).nodup_iff.mpr (all.sublist (p.map _)),
    fun a ha => strong a (hp.subset (perm.mem_iff.mp ha))⟩
theorem prefix_clean {b first q pre post} (h : SortedCommon b first q) (split : first::q=pre++post) :
    ((wiresOf pre).map (masked (domainWord 0 b))).Nodup := by
  obtain ⟨all,_⟩ := h.clean
  rw [split] at all
  have pre' : (wiresOf pre).Sublist (wiresOf (pre++post)) := by
    simp only [wiresOf,List.map_append,←List.append_assoc]
    exact List.sublist_append_left ..
  exact all.sublist (pre'.map _)
theorem next_clean {b first q pre post g} (h : SortedCommon b first q)
    (split : first::q=pre++g::post) : let m := domainWord 0 b
    masked m g.out ≠ 0 ∧ masked m g.out ≠ m.toNat ∧
    masked m g.out ∉ (wiresOf pre).map (masked m) := by
  have pr := prefix_clean h (pre := pre++[g]) (post := post) (by rw [split]; simp)
  have nz := h.clean.2 g (split ▸ List.mem_append_right _ List.mem_cons_self)
  have e : wiresOf (pre++[g])=wiresOf pre++[g.out] := by simp [wiresOf,List.append_assoc]
  rw [e,List.map_append,List.nodup_append] at pr
  exact ⟨nz.1,nz.2,fun mem => pr.2.2 _ mem _ (by simp) rfl⟩
end L652
namespace L652.GroupProjection
abbrev Word := Nat
structure Col where
  full : Word
  p1 : Word
  n1 : Word
  p2 : Word
  n2 : Word
  deriving Inhabited, BEq, Repr
structure Data where
  domain : Word
  active1 : Word
  active2 : Word
  raw : List Col
  valid : Word
  deriving Inhabited
def data0 : Data := ⟨72907581239285247,0,0,[⟨0x2000a002200aa,0x21006713c00,0x21006710007,0x33884203c00,0x33884200007⟩,
⟨0x40c000044cc,0x3389e000840,0x33880038840,0x2101e000ce2,0x21000038ce2⟩,
⟨0x103050f0,0xf0004200ce2,0x1c4200ce2,0xf0006710840,0x1c6710840⟩,
⟨0x100050011005500,0xc21d0020000,0xc21d0023ce0,0x80118438000,0x8011843bce0⟩,
⟨0x103000011330000,0x80100003087,0x8011e703087,0xc21c0002004,0xc21de702004⟩,
⟨0x103050f00000000,0x1843a004,0xf381843a004,0x10023087,0xf3810023087⟩],0xf39de73bce7⟩
def data1 : Data := ⟨18373836492470266368,0,0,[⟨0xaaa8aaa0aa88aa00,0xac0f30080,0xac0f3008f,0x7980138040,0x798013804f⟩,
⟨0xccccc8c0cccc8800,0x7980200027,0x7980278027,0x22c04001ea,0x22c04781ea⟩,
⟨0xf0f0f0f0e0c0a000,0x20004581ea,0x23c04581ea,0x1000f50087,0x13c0f50087⟩,
⟨0xfe00fa00ee00aa00,0x4bc0b20004,0x4bc0b201e4,0x5900978004,0x59009781e4⟩,
⟨0xfefc0000eecc0000,0x710004012f,0x7100f4012f,0x63c0020168,0x63c0f20168⟩,
⟨0xfefcfaf000000000,0x200c781c8,0x7a00c781c8,0x200e4018f,0x7a00e4018f⟩],0x7bc0f781ef⟩
end L652.GroupProjection
namespace L652.GroupProjection
def Col.combine (join : Bool) (x y : Col) : Col :=
  if join then ⟨x.full ||| y.full, x.p1 ||| y.p1, x.n1 ||| y.n1, x.p2 ||| y.p2, x.n2 ||| y.n2⟩
  else ⟨x.full &&& y.full, x.p1 &&& y.p1, x.n1 &&& y.n1, x.p2 &&& y.p2, x.n2 &&& y.n2⟩
def Col.neg (x : Col) (dom : Word) : Col :=
  ⟨dom ^^^ x.full, (0xffffffffffffffff ^^^ x.p1), (0xffffffffffffffff ^^^ x.n1), (0xffffffffffffffff ^^^ x.p2), (0xffffffffffffffff ^^^ x.n2)⟩
def Col.separates (second : Bool) (c : Col) : Word :=
  if second then c.p2 ^^^ c.n2 else c.p1 ^^^ c.n1
def rawCost (d : Data) (hit : Nat) : Nat :=
  let unresolved := ((d.valid &&& (18446744073709551615 ^^^ hit)) + 17024696172015) &&& 18159675916816
  let a := unresolved &&& 17180393488
  let b := (unresolved >>> 5) &&& 17180393488
  let p := (unresolved >>> 10) &&& 17180393488
  let cost := a + b + (p &&& (18446744073709551615 ^^^ (a ||| b)))
  ((cost + (cost >>> 15) + (cost >>> 30)) >>> 4) &&& 7
def extraCost (d : Data) (second : Bool) (hit : Word) (limit : Nat) : List Col → Nat
  | [] => min limit (rawCost d hit)
  | x :: xs =>
    let absent := extraCost d second hit limit xs
    if absent ≤ 1 then absent else
    min absent (1 + extraCost d second (hit ||| x.separates second) (absent - 1) xs)
def canContinue (d : Data) (sinks optional : List Col) (allowance : Nat) : Bool :=
  let base := sinks.length - 1
  if 2 * base > allowance then false else
  let budget := allowance - 2 * base
  let first := extraCost d false (sinks.foldl (fun h c => h ||| c.separates false) 0) (budget+1) optional
  if first > budget then false else
  let remaining := budget - first
  let second := extraCost d true (sinks.foldl (fun h c => h ||| c.separates true) 0) (remaining+1) optional
  second ≤ remaining
structure State where
  wires : List Col
  sunk : List Col
  internal : List Col
  last : Nat
def key (a b op : Nat) := ((b*32)+a)*3+op
def stepAll (d : Data) (s : State) (initial : Bool) (accept : State → Bool) : Bool :=
  s.wires.zipIdx.all fun (y,b) =>
    if key b b 2 < s.last then true else
    (s.wires.take (b+1)).zipIdx.all fun (x,a) =>
      if initial && !(a == 0 && b == 0 || a == 0 && b == 1 || a == 0 && b == 3 || a == 1 && b == 3) then true else
      let run := fun (op : Nat) (z : Col) =>
        let order := key a b op
        if order < s.last || z.full == 0 || z.full == d.domain || s.wires.any (fun p => z.full == p.full) then true
        else
          let consumed := fun t : Col => t.full == x.full || t.full == y.full
          let sinks := z :: s.sunk.filter fun t => !(consumed t)
          let older := s.sunk.filter consumed ++ s.internal
          accept ⟨s.wires ++ [z], sinks, older, order⟩
      if a == b then run 2 (x.neg d.domain)
      else run 0 (x.combine false y) && run 1 (x.combine true y)
def check (d : Data) (n : Nat) (s : State) : Nat → Bool
  | 0 => !canContinue d s.sunk s.internal (10-n)
  | fuel+1 =>
    if canContinue d s.sunk s.internal (10-n) then false else
    if !canContinue d s.sunk s.internal (10+fuel+1-n) then true else
    stepAll d s false fun next => check d (n+1) next fuel
def verify (d : Data) (extra : Nat) : Bool :=
  stepAll d ⟨d.raw, [], [], 0⟩ true fun next => check d 1 next extra
def advance (d : Data) (s : State) (code : Nat) : State :=
  let a := code/3 % 32
  let b := code/3/32
  let op := code % 3
  let x := s.wires.getD a default
  let y := s.wires.getD b default
  let z := if op == 2 then x.neg d.domain else x.combine (op==1) y
  let consumes := fun c : Col => c.full == x.full || c.full == y.full
  ⟨s.wires ++ [z], z :: s.sunk.filter fun t => !(consumes t), s.sunk.filter consumes ++ s.internal, code⟩
def unpackCodes : Nat → Nat → List Nat
  | 0, _ => []
  | k+1, w => w % 2048 :: unpackCodes k (w/2048)
def prefixState (d : Data) (n encoded : Nat) : State :=
  (unpackCodes n encoded).foldl (advance d) ⟨d.raw,[],[],0⟩
def branch (d : Data) (n encoded : Nat) : Bool :=
  let s := prefixState d n encoded
  check d n s (9-n)
end L652.GroupProjection
namespace L652
open GroupProjection (Col Data State)
structure GroupRules (b : Bool) (d : Data) (col : Word → Col) : Prop where
  raw : rawWords.map col = d.raw
  domain : d.domain = (domainWord 0 b).toNat
  full : ∀ w, (col w).full = masked (domainWord 0 b) w
  neg : ∀ x, (col x).neg d.domain = col (~~~x)
  meet : ∀ x y, (col x).combine false (col y) = col (x &&& y)
  join : ∀ x y, (col x).combine true (col y) = col (x ||| y)
  bound : ∀ (sinks opts : List Word) (A B : Finset Word) (budget : Nat),
    (rawWords ++ sinks ++ opts).Nodup → (opts.map col).Nodup → sinks ≠ [] →
    A ⊆ (rawWords ++ sinks ++ opts).toFinset → B ⊆ (rawWords ++ sinks ++ opts).toFinset →
    sinks.toFinset ⊆ A → sinks.toFinset ⊆ B → A.card+B.card ≤ budget+2 →
    Determines (domainWord 0 b) A (matchWord 1) → Determines (domainWord 0 b) B (matchWord 2) →
    GroupProjection.canContinue d (sinks.map col) (opts.map col) budget = true
def projectState (col : Word → Col) (p : List LogicalGate) (last : Nat) : State :=
  ⟨(wiresOf p).map col, (bookOf p).tips.map col, (bookOf p).used.map col, last⟩
theorem group_budget {b d col first q p post} (r : GroupRules b d col) (c : SortedCommon b first q)
    (split : first::q=p++post) (ne : p≠[]) (budget : Nat)
    (room : 10+(first::q).length ≤ budget+2*p.length) :
    GroupProjection.canContinue d ((bookOf p).tips.map col) ((bookOf p).used.map col) budget = true := by
  obtain ⟨A,B,sa,sb,ta,tb,da,db,cost⟩ := book_features c split
  have eq : (rawWords++(bookOf p).tips++(bookOf p).used).toFinset = (wiresOf p).toFinset :=
    List.toFinset_eq_of_perm _ _ (book_wires p)
  have uniq := prefix_clean c split
  have nodup := ((book_wires p).map (masked (domainWord 0 b))).nodup_iff.mpr uniq
  have un : (rawWords++(bookOf p).tips++(bookOf p).used).Nodup := nodup.of_map _
  have nc : ((bookOf p).used.map (masked (domainWord 0 b))).Nodup := by
    rw [List.map_append,List.nodup_append] at nodup
    exact nodup.2.1
  have opts : ((bookOf p).used.map col).Nodup := by
    apply List.Nodup.of_map Col.full
    simpa only [List.map_map,Function.comp_def,r.full] using nc
  exact r.bound _ _ A B budget un opts (tips_nonempty _ ne) (eq ▸ sa) (eq ▸ sb) ta tb
    (by omega) da db
end L652
namespace L652
structure Selection (w : List Word) (g : LogicalGate) where
  a : Nat
  b : Nat
  op : Nat
  x : Word
  y : Word
  x_at : w[a]? = some x
  y_at : w[b]? = some y
  a_le : a ≤ b
  b_lt : b < w.length
  kind : (a=b ∧ op=2) ∨ (a<b ∧ (op=0 ∨ op=1))
  index : GroupProjection.key a b op = gateKey w g
  src : sources g = {x,y}
  val : g.out = if op=2 then ~~~x else if op=1 then x ||| y else x &&& y
theorem select_gate {w : List Word} {g : LogicalGate} (r : sources g ⊆ w.toFinset)
    (new : g.out ∉ w) : Nonempty (Selection w g) := by
  have loc (v : Word) (hv : v ∈ sources g) :
      w.idxOf v < w.length ∧ w[w.idxOf v]? = some v := by
    have h := List.idxOf_lt_length_of_mem (List.mem_toFinset.mp (r hv))
    exact ⟨h,by rw [List.getElem?_eq_getElem h,List.getElem_idxOf h]⟩
  cases g with
  | neg v =>
    obtain ⟨sz,look⟩ := loc v (by simp [sources])
    exact ⟨⟨_,_,2,v,v,look,look,le_rfl,sz,Or.inl ⟨rfl,rfl⟩,rfl,by simp [sources],rfl⟩⟩
  | meet v z =>
    obtain ⟨sv,iv⟩ := loc v (by simp [sources])
    obtain ⟨sz,iz⟩ := loc z (by simp [sources])
    have ne : w.idxOf v ≠ w.idxOf z := by
      intro h
      rw [h,iz] at iv
      have eq := Option.some.inj iv
      subst z
      apply new
      simpa [LogicalGate.out] using List.mem_toFinset.mp (r (by simp [sources] : v ∈ sources (.meet v v)))
    by_cases h : w.idxOf v ≤ w.idxOf z
    · exact ⟨⟨_,_,0,v,z,iv,iz,h,sz,Or.inr ⟨by omega,by decide⟩,
        by simp [GroupProjection.key,gateKey,operandPair,operation,min_eq_left h,max_eq_right h],
        rfl,rfl⟩⟩
    · have h' : w.idxOf z ≤ w.idxOf v := by omega
      exact ⟨⟨_,_,0,z,v,iz,iv,h',sv,Or.inr ⟨by omega,by decide⟩,
        by simp [GroupProjection.key,gateKey,operandPair,operation,min_eq_right h',max_eq_left h'],
        by ext k; simp [sources,or_comm],by simpa [LogicalGate.out] using BitVec.and_comm v z⟩⟩
  | join v z =>
    obtain ⟨sv,iv⟩ := loc v (by simp [sources])
    obtain ⟨sz,iz⟩ := loc z (by simp [sources])
    have ne : w.idxOf v ≠ w.idxOf z := by
      intro h
      rw [h,iz] at iv
      have eq := Option.some.inj iv
      subst z
      apply new
      simpa [LogicalGate.out] using List.mem_toFinset.mp (r (by simp [sources] : v ∈ sources (.join v v)))
    by_cases h : w.idxOf v ≤ w.idxOf z
    · exact ⟨⟨_,_,1,v,z,iv,iz,h,sz,Or.inr ⟨by omega,by decide⟩,
        by simp [GroupProjection.key,gateKey,operandPair,operation,min_eq_left h,max_eq_right h],
        rfl,rfl⟩⟩
    · have h' : w.idxOf z ≤ w.idxOf v := by omega
      exact ⟨⟨_,_,1,z,v,iz,iv,h',sv,Or.inr ⟨by omega,by decide⟩,
        by simp [GroupProjection.key,gateKey,operandPair,operation,min_eq_right h',max_eq_left h'],
        by ext k; simp [sources,or_comm],by simpa [LogicalGate.out] using BitVec.or_comm v z⟩⟩
def firstOK (a b : Nat) : Bool :=
  (a == 0 && b == 0 || a == 0 && b == 1 || a == 0 && b == 3 || a == 1 && b == 3)
theorem first_good {w g} (s : Selection w g) (h : allowedSharedFirst (gateKey w g)) :
    firstOK s.a s.b = true := by
  rw [←s.index] at h
  unfold allowedSharedFirst GroupProjection.key at h
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at h
  have h1 := s.a_le
  rcases s.kind with ⟨he,hop⟩ | ⟨he,hop | hop⟩ <;>
    simp only [firstOK,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] <;> omega
end L652
namespace L652
open GroupProjection (Data Col State)
def nextColumn (d : Data) (x y : Col) (op : Nat) : Col :=
  if op=2 then x.neg d.domain else x.combine (op==1) y
def readsColumns (x y t : Col) : Bool := t.full==x.full || t.full==y.full
def colAfter (d : Data) (s : State) (a b op : Nat) (x y : Col) : State :=
  let z := nextColumn d x y op
  ⟨s.wires++[z],z :: s.sunk.filter (fun v => !(readsColumns x y v)),
    s.sunk.filter (readsColumns x y) ++ s.internal, GroupProjection.key a b op⟩
theorem stepAll_select {d : Data} {s : State} {start : Bool} {test : State → Bool}
    {a b op : Nat} {x y : Col}
    (ix : s.wires[a]? = some x) (iy : s.wires[b]? = some y) (hab : a ≤ b)
    (kind : (a=b ∧ op=2) ∨ (a<b ∧ (op=0 ∨ op=1)))
    (lb : s.last ≤ GroupProjection.key a b op)
    (first : start=true → firstOK a b = true)
    (nz : (nextColumn d x y op).full ≠ 0) (nd : (nextColumn d x y op).full ≠ d.domain)
    (new : ∀ v ∈ s.wires, (nextColumn d x y op).full ≠ v.full)
    (all : GroupProjection.stepAll d s start test = true) : test (colAfter d s a b op x y) = true := by
  have top := List.all_eq_true.mp all (y,b) (List.mk_mem_zipIdx_iff_getElem?.mpr iy)
  have ko : ¬GroupProjection.key b b 2 < s.last := by
    dsimp [GroupProjection.key] at *
    rcases kind with ⟨_,op2⟩ | ⟨_,op0 | op1⟩ <;> omega
  dsimp only at top
  rw [if_neg ko] at top
  have inner : (x,a) ∈ (s.wires.take (b+1)).zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa [List.getElem?_take, show a<b+1 by omega] using ix
  have branch := List.all_eq_true.mp top (x,a) inner
  dsimp only at branch
  have fv : (start && !(firstOK a b)) = false := by
    cases start with
    | false => rfl
    | true => simp [first rfl]
  unfold firstOK at fv
  simp only [fv,Bool.false_eq_true,ite_false] at branch
  have fresh : s.wires.any (fun p => (nextColumn d x y op).full==p.full) = false := by
    apply List.any_eq_false.mpr
    intro p hp ev
    exact new p hp (beq_iff_eq.mp ev)
  let run := fun (o : Nat) (z : Col) =>
    if decide (GroupProjection.key a b o < s.last) || z.full == 0 || z.full == d.domain ||
        s.wires.any (fun w => z.full == w.full) then true
    else test ⟨s.wires++[z], z :: s.sunk.filter (fun v => !(readsColumns x y v)),
      s.sunk.filter (readsColumns x y) ++ s.internal,GroupProjection.key a b o⟩
  have br : (if a == b then run 2 (x.neg d.domain) else
      run 0 (x.combine false y) && run 1 (x.combine true y)) = true := branch
  have accepted : run op (nextColumn d x y op) = true := by
    rcases kind with ⟨rfl,rfl⟩ | ⟨lt,rfl | rfl⟩
    · simpa only [beq_self_eq_true,ite_true,nextColumn] using br
    · have ne : a ≠ b := Nat.ne_of_lt lt
      simp only [beq_eq_false_iff_ne.mpr ne,Bool.false_eq_true,ite_false,Bool.and_eq_true] at br
      exact br.1
    · have ne : a ≠ b := Nat.ne_of_lt lt
      simp only [beq_eq_false_iff_ne.mpr ne,Bool.false_eq_true,ite_false,Bool.and_eq_true] at br
      exact br.2
  simp only [run,decide_eq_false (Nat.not_lt.mpr lb),beq_eq_false_iff_ne.mpr nz,
    beq_eq_false_iff_ne.mpr nd,fresh,Bool.false_or,Bool.false_eq_true,ite_false] at accepted
  exact accepted
end L652
namespace L652
open GroupProjection (Data Col State)
theorem selection_value {b d col w g} (r : GroupRules b d col) (sel : Selection w g) :
    nextColumn d (col sel.x) (col sel.y) sel.op = col g.out := by
  rw [sel.val]
  rcases sel.kind with ⟨_,h⟩ | ⟨_,h | h⟩ <;> rw [h] <;>
    simp [nextColumn,r.neg,r.meet,r.join]
theorem actual_next {b d col first q pre post g last} (rules : GroupRules b d col)
    (com : SortedCommon b first q) (split : first::q=pre++g::post)
    (sel : Selection (wiresOf pre) g) :
    colAfter d (projectState col pre last) sel.a sel.b sel.op (col sel.x) (col sel.y) =
      projectState col (pre++[g]) (gateKey (wiresOf pre) g) := by
  have unique := prefix_clean com split
  have inj := List.inj_on_of_nodup_map unique
  have members (v : Word) (hv : v ∈ (bookOf pre).tips) : v ∈ wiresOf pre :=
    (book_wires pre).mem_iff.mp (List.mem_append_left _ (List.mem_append_right _ hv))
  have eval (v : Word) (inpool : v ∈ (bookOf pre).tips) :
      readsColumns (col sel.x) (col sel.y) (col v) = consumes g v := by
    have hv := members v inpool
    have ax := List.mem_of_getElem? sel.x_at
    have ay := List.mem_of_getElem? sel.y_at
    have ext {a : Word} (mem : a ∈ wiresOf pre) :
        (masked (domainWord 0 b) v == masked (domainWord 0 b) a) = (v==a) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact ⟨inj hv mem,fun e => congrArg _ e⟩
    simp only [readsColumns,rules.full,ext ax,ext ay,consumes,sel.src,Finset.mem_insert,
      Finset.mem_singleton]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq]
  have w : wiresOf (pre++[g])=wiresOf pre++[g.out] := by simp [wiresOf,List.append_assoc]
  have one : ((bookOf pre).tips.map col).filter (readsColumns (col sel.x) (col sel.y)) =
      ((bookOf pre).tips.filter (consumes g)).map col := by
    rw [List.filter_map]
    exact congrArg _ (List.filter_congr eval)
  have two : ((bookOf pre).tips.map col).filter (fun v => !(readsColumns (col sel.x) (col sel.y) v)) =
      ((bookOf pre).tips.filter (fun v => !(consumes g v))).map col := by
    rw [List.filter_map]
    exact congrArg _ (List.filter_congr (fun v hv => congrArg not (eval v hv)))
  simp only [colAfter,projectState,selection_value rules sel,w,sel.index,List.map_append,List.map_cons,
    List.map_nil,book_snoc,CommonBook.push,one,two]
theorem follow_group {b d col first q pre post g last} (rules : GroupRules b d col)
    (com : SortedCommon b first q) (split : first::q=pre++g::post)
    (ready : sources g ⊆ (wiresOf pre).toFinset) (min : last ≤ gateKey (wiresOf pre) g)
    (start : Bool) (allowed : start=true → allowedSharedFirst (gateKey (wiresOf pre) g))
    (test : State → Bool) (acc : GroupProjection.stepAll d (projectState col pre last) start test = true) :
    test (projectState col (pre++[g]) (gateKey (wiresOf pre) g)) = true := by
  obtain ⟨zero,one,absent⟩ := next_clean com split
  have fresh : g.out ∉ wiresOf pre := fun h => absent (List.mem_map.mpr ⟨_,h,rfl⟩)
  obtain ⟨sel⟩ := select_gate ready fresh
  have hx := sel.x_at
  have hy := sel.y_at
  have row : ∀ v ∈ (wiresOf pre).map col, (col g.out).full ≠ v.full := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    rw [rules.full,rules.full]
    exact fun e => absent (List.mem_map.mpr ⟨x,hx,e.symm⟩)
  have sc := selection_value rules sel
  rw [←actual_next (last := last) rules com split sel]
  apply stepAll_select (d := d) (s := projectState col pre last) (start := start)
  · simp only [projectState,List.getElem?_map,hx,Option.map_some]
  · simp only [projectState,List.getElem?_map,hy,Option.map_some]
  · exact sel.a_le
  · exact sel.kind
  · exact sel.index ▸ min
  · exact fun h => first_good sel (allowed h)
  · rw [sc,rules.full]; exact zero
  · rw [sc,rules.domain,rules.full]; exact one
  · rw [sc]; exact row
  · exact acc
end L652
namespace L652
open GroupProjection (Data Col State)
theorem excludes_suffix {b d col first q} (rules : GroupRules b d col) (com : SortedCommon b first q)
    (pre post : List LogicalGate) (last fuel : Nat) (split : first::q=pre++post)
    (ord : KeyOrdered (wiresOf pre) last post) (used : pre≠[]) (room : post.length ≤ fuel) :
    GroupProjection.check d pre.length (projectState col pre last) fuel ≠ true := by
  obtain ⟨gs,t,u,ex,per⟩ := com.example_exists
  have limit := (shared_program_spec ex).2.2.2.2.2
  have count := per.length_eq
  have total : (first::q).length = pre.length+post.length := by rw [split,List.length_append]
  have ht : pre.length ≤ 9 := by omega
  have hnext := group_budget rules com split used (10+fuel-pre.length) (by omega)
  cases post with
  | nil =>
    have low := group_budget rules com split used (10-pre.length) (by simp only [List.length_nil,Nat.add_zero] at total; omega)
    cases fuel <;> simp [GroupProjection.check,projectState,low]
  | cons g rest =>
    cases fuel with
    | zero => simp at room
    | succ n =>
      cases ord with
      | cons ready min tail =>
        by_contra yes
        have accept : GroupProjection.stepAll d (projectState col pre last) false
            (fun s => GroupProjection.check d (pre.length+1) s n) = true := by
          change GroupProjection.check d pre.length (projectState col pre last) (n+1) = true at yes
          simp only [GroupProjection.check] at yes
          split at yes
          · contradiction
          · have succeeds : GroupProjection.canContinue d (projectState col pre last).sunk
                (projectState col pre last).internal (10+n+1-pre.length) = true := by
              simpa [Nat.add_assoc,projectState] using hnext
            simpa only [succeeds,Bool.not_true,Bool.false_eq_true,ite_false] using yes
        have next := follow_group rules com split ready min false (by simp) _ accept
        have eq : first::q=(pre++[g])++rest := by simpa [List.append_assoc] using split
        have ord' : KeyOrdered (wiresOf (pre++[g])) (gateKey (wiresOf pre) g) rest := by
          simpa [wiresOf,List.append_assoc] using tail
        have contradiction' := excludes_suffix rules com (pre++[g]) rest _ n eq ord' (by simp)
          (by simpa using room)
        exact contradiction' (by simpa using next)
termination_by post.length
end L652
namespace L652.GroupProjection
structure Trial where
  a : Nat
  b : Nat
  order : Nat
  value : Col
  consumed : Nat
  deriving Inhabited
def eatenMask (sinks : List Col) (x y : Col) : Nat :=
  sinks.foldr (fun c n => 2*n + if c.full == x.full || c.full == y.full then 1 else 0) 0
def trials (d : Data) (s : State) (initial : Bool) : List Trial :=
  s.wires.zipIdx.flatMap fun (y,b) =>
    if key b b 2 < s.last then [] else
    (s.wires.take (b+1)).zipIdx.flatMap fun (x,a) =>
      if initial && !(a == 0 && b == 0 || a == 0 && b == 1 || a == 0 && b == 3 || a == 1 && b == 3) then [] else
      let mk := fun (op : Nat) (z : Col) =>
        let k := key a b op
        if k<s.last || z.full==0 || z.full==d.domain || s.wires.any (fun t => t.full==z.full) then []
        else [Trial.mk a b k z (eatenMask s.sunk x y)]
      if a==b then mk 2 (x.neg d.domain) else mk 0 (x.combine false y) ++ mk 1 (x.combine true y)
def laneMin (rep a b : Nat) : Nat :=
  let carries := ((32*rep+a)-b) &&& (32*rep)
  let mask := carries - (carries >>> 5)
  (a &&& ((31*rep) ^^^ mask)) ||| (b &&& mask)
def allRaws (d : Data) (rep hit : Nat) : Nat :=
  let unresolved := ((d.valid*rep &&& ((0xffffffffffffffff*rep) ^^^ hit)) + (17024696172015*rep)) &&& (18159675916816*rep)
  let a := unresolved &&& (17180393488*rep)
  let b := (unresolved >>> 5) &&& (17180393488*rep)
  let p := (unresolved >>> 10) &&& (17180393488*rep)
  let cost := a+b+(p &&& ((0xffffffffffffffff*rep) ^^^ (a ||| b)))
  ((cost >>> 4) &&& (3*rep)) + ((cost >>> 19) &&& (3*rep)) + ((cost >>> 34) &&& (3*rep))
def allScores (d : Data) (rep : Nat) (second : Bool) (hit : Nat) : List Col → Nat
  | [] => allRaws d rep hit
  | x :: xs => laneMin rep (allScores d rep second hit xs)
        (rep + allScores d rep second (hit ||| (x.separates second * rep)) xs)
def allFail (rep scores : Nat) (room : Nat) : Nat :=
  (scores+(31-room)*rep) &&& (32*rep)
def coarseHit (rep : Nat) (ts : List Trial) (rest : List Col) (second : Bool) : Nat :=
  let old := rest.foldl (fun h c => h ||| c.separates second) 0
  let fresh := ts.foldr (fun t v => t.value.separates second ||| (v <<< 64)) 0
  (old*rep) ||| fresh
def coarseSide (d : Data) (rep : Nat) (ts : List Trial) (rest opts : List Col) (second : Bool) : Nat :=
  let h := coarseHit rep ts rest second
  let all := opts.foldl (fun h c => h ||| c.separates second) 0
  laneMin rep (allRaws d rep h) (rep + allRaws d rep (h ||| (all*rep)))
def coarseClose (d : Data) (rep : Nat) (ts : List Trial) (rest opts : List Col) (room : Nat) : Bool :=
  opts.length >= 2 && allFail rep (coarseSide d rep ts rest opts false + coarseSide d rep ts rest opts true) room == 32*rep
def evaluateTrials (d : Data) (n fuel : Nat) (s : State) (mask : Nat) (ts : List Trial)
    (next : State → Bool) : Bool :=
  if ts.isEmpty then true else
  let remaining := (s.sunk.zipIdx.filter fun (_,i) => !mask.testBit i).map Prod.fst
  let optional := (s.sunk.zipIdx.filter fun (_,i) => mask.testBit i).map Prod.fst ++ s.internal
  let base := 2*remaining.length
  if base>10+fuel-n then true else
  let rep := ts.foldr (fun _ v => 1+(v <<< 64)) 0
  if coarseClose d rep ts remaining optional (10+fuel-n-base) then true else
  let side := fun second =>
    let old := remaining.foldl (fun h c => h ||| c.separates second) 0
    let fresh := ts.foldr (fun t v => t.value.separates second ||| (v <<< 64)) 0
    allScores d rep second ((old * rep) ||| fresh) optional
  let scores := side false + side true
  if base≤10-n && allFail rep scores (10-n-base) != 32*rep then false else
  if fuel==0 then true else
  let exclude := allFail rep scores (10+fuel-n-base)
  if exclude == 32*rep then true else
  ts.zipIdx.all fun (t,i) => exclude.testBit (64*i+5) ||
    next ⟨s.wires++[t.value], t.value::remaining,optional,t.order⟩
def bulk (d : Data) (n : Nat) (s : State) (initial : Bool) : Nat → Bool
  | 0 => true
  | fuel+1 =>
    let ts := trials d s initial
    let groups := (ts.map Trial.consumed).eraseDups
    groups.all fun mask => evaluateTrials d (n+1) fuel s mask (ts.filter fun t => t.consumed == mask)
      (fun s' => bulk d (n+1) s' false fuel)
def bulkAt8 (d : Data) (n : Nat) (s : State) : Bool :=
  !canContinue d s.sunk s.internal (10-n) &&
  (!canContinue d s.sunk s.internal (18-2*n) || bulk d n s false (8-n))
def range8 (d : Data) (n : Nat) (s : State) (first count : Nat) : Bool :=
  !canContinue d s.sunk s.internal (10-n) &&
  (!canContinue d s.sunk s.internal (18-2*n) ||
    (((trials d s false).drop first).take count).all
      (fun t => bulkAt8 d (n+1) (advance d s t.order)))
end L652.GroupProjection
namespace L652.GroupProjection
def maskKeep (sinks : List Col) (mask : Nat) (consumed : Bool) : List Col :=
  (sinks.zipIdx.filter (fun p => mask.testBit p.2 == consumed)).map Prod.fst
def trialAfter (s : State) (t : Trial) : State :=
  ⟨s.wires++[t.value],t.value :: maskKeep s.sunk t.consumed false,
    maskKeep s.sunk t.consumed true ++ s.internal,t.order⟩
theorem eaten_bit {l : List Col} (x y : Col) {i : Nat} {c : Col} (ix : l[i]? = some c) :
    (eatenMask l x y).testBit i = (c.full==x.full || c.full==y.full) := by
  induction l generalizing i with
  | nil => simp at ix
  | cons a as ih =>
    have ed : eatenMask (a::as) x y =
        2*eatenMask as x y + (if a.full==x.full || a.full==y.full then 1 else 0) := rfl
    rw [ed]
    cases i with
    | zero =>
      obtain rfl : a=c := by simpa using ix
      rw [Nat.testBit_zero]
      split <;> rename_i h <;> simp_all [Nat.add_mod]
    | succ i =>
      rw [Nat.testBit_succ]
      have div : (2*eatenMask as x y + (if a.full==x.full || a.full==y.full then 1 else 0))/2 =
          eatenMask as x y := by split <;> omega
      rw [div]; exact ih ix
theorem mask_partition (s : List Col) (x y : Col) (b : Bool) :
    maskKeep s (eatenMask s x y) b = s.filter (fun t => (t.full==x.full || t.full==y.full) == b) := by
  unfold maskKeep
  rw [show s.filter (fun t => (t.full==x.full || t.full==y.full) == b) =
      (s.zipIdx.map Prod.fst).filter (fun t => (t.full==x.full || t.full==y.full) == b) by
        rw [List.zipIdx_map_fst]]
  rw [List.filter_map]
  apply congrArg _
  apply List.filter_congr
  rintro ⟨c,i⟩ h
  change ((eatenMask s x y).testBit i == b) = _
  rw [eaten_bit x y (List.mk_mem_zipIdx_iff_getElem?.mp h)]
  rfl
theorem trial_replay (s : State) (a b k : Nat) (x y z : Col) :
    trialAfter s ⟨a,b,k,z,eatenMask s.sunk x y⟩ =
      ⟨s.wires++[z],z::s.sunk.filter (fun t => !(t.full==x.full || t.full==y.full)),
       s.sunk.filter (fun t => t.full==x.full || t.full==y.full) ++ s.internal,k⟩ := by
  simp [trialAfter,mask_partition]
theorem stepAll_trials (d : Data) (s : State) (initial : Bool) (accept : State → Bool) :
    stepAll d s initial accept = (trials d s initial).all (fun t => accept (trialAfter s t)) := by
  unfold stepAll trials
  simp only [List.all_flatMap]
  apply congrArg (List.all s.wires.zipIdx)
  funext p
  obtain ⟨y,b⟩ := p
  dsimp only
  by_cases tooLarge : key b b 2 < s.last
  · simp [tooLarge]
  · simp only [tooLarge,ite_false,List.all_flatMap]
    apply congrArg (List.all (s.wires.take (b+1)).zipIdx)
    funext p
    obtain ⟨x,a⟩ := p
    dsimp only
    split
    · rfl
    · have law (op : Nat) (z : Col) :
          (if key a b op < s.last || z.full==0 || z.full==d.domain || s.wires.any (fun t => z.full==t.full)
            then true else accept
              ⟨s.wires++[z],z::s.sunk.filter (fun t => !(t.full==x.full || t.full==y.full)),
                s.sunk.filter (fun t => t.full==x.full || t.full==y.full) ++ s.internal,key a b op⟩) =
          ((if key a b op < s.last || z.full==0 || z.full==d.domain || s.wires.any (fun t => t.full==z.full)
            then [] else [⟨a,b,key a b op,z,eatenMask s.sunk x y⟩] : List Trial).all
               (fun t => accept (trialAfter s t))) := by
          have any_eq : s.wires.any (fun t => t.full==z.full) = s.wires.any (fun t => z.full==t.full) := by
            apply congrArg (List.any s.wires); funext t; apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; exact eq_comm
          rw [any_eq]
          split <;> simp [trial_replay]
      split
      · exact law ..
      · rw [List.all_append,←law,←law]
end L652.GroupProjection
namespace L652.GroupProjection
inductive Reach (d : Data) : Nat → State → Prop where
  | root : Reach d 0 ⟨d.raw,[],[],0⟩
  | step {n s init t} (old : Reach d n s) (ht : t ∈ trials d s init) :
      Reach d (n+1) (trialAfter s t)
def groupResult (d : Data) (n fuel : Nat) (s : State) (initial : Bool) (t : Trial)
    (next : State → Bool) : Bool :=
  evaluateTrials d (n+1) fuel s t.consumed ((trials d s initial).filter (fun z => z.consumed == t.consumed)) next
def LaneLaw (d : Data) : Prop := ∀ (n fuel : Nat) (s : State) (init : Bool) (t : Trial) (next : State → Bool),
  Reach d n s → n+fuel+1≤9 → t ∈ trials d s init → groupResult d n fuel s init t next = true →
  let dst := trialAfter s t
  canContinue d dst.sunk dst.internal (10-(n+1)) = false ∧
  (0<fuel → canContinue d dst.sunk dst.internal (10+fuel-(n+1)) = true → next dst = true)
theorem bulk_trial {d n fuel s init t} (h : bulk d n s init (fuel+1)=true)
    (mem : t ∈ trials d s init) :
    groupResult d n fuel s init t (fun dst => bulk d (n+1) dst false fuel)=true := by
  apply List.all_eq_true.mp h t.consumed
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨t,mem,rfl⟩
theorem bulk_steps {d : Data} (law : LaneLaw d) {n s init : _} (fuel : Nat) (ok : Reach d n s)
    (cap : n+fuel+1≤9) (h : bulk d n s init (fuel+1)=true) :
    stepAll d s init (fun dst => check d (n+1) dst fuel)=true := by
  rw [stepAll_trials]
  apply List.all_eq_true.mpr
  intro t ht
  let dst := trialAfter s t
  obtain ⟨closed,further⟩ := law n fuel s init t _ ok cap ht (bulk_trial h ht)
  cases fuel with
  | zero =>
    change !canContinue d (trialAfter s t).sunk (trialAfter s t).internal (10-(n+1)) = true
    rw [closed]; rfl
  | succ k =>
    simp only [check,closed,Bool.false_eq_true,ite_false]
    by_cases open_ : canContinue d (trialAfter s t).sunk (trialAfter s t).internal (10+k+1-(n+1))=true
    · simp only [open_,Bool.not_true,Bool.false_eq_true,ite_false]
      exact bulk_steps law k (.step ok ht) (by omega) (further (by omega) (by simpa [Nat.add_assoc] using open_))
    · simpa only [Bool.eq_false_iff.mpr open_,Bool.not_false,ite_true]
termination_by fuel
end L652.GroupProjection
namespace L652
private theorem zz54n0 (P ignore need : Finset Word) (gs : List LogicalGate)
    (ins : ∀ g ∈ gs, g.out ∈ P → sources g ⊆ ignore)
    (outs : ∀ g ∈ gs, g.out ∉ P → g.out ∉ ignore) :
    demand gs need ⊆ demand (exceptFor P gs) need ∪ ignore ∧
    exceptFor P (cone gs need) ⊆ cone (exceptFor P gs) need := by
  induction gs with
  | nil => simp [demand,cone,exceptFor]
  | cons g gs ih =>
    obtain ⟨lower,keep⟩ := ih (fun a ha => ins a (List.mem_cons_of_mem _ ha))
      (fun a ha => outs a (List.mem_cons_of_mem _ ha))
    let old := demand gs need
    let new := demand (exceptFor P gs) need
    have next : old ⊆ new ∪ ignore := lower
    by_cases discard : g.out ∈ P
    · have hcut : exceptFor P (g::gs) = exceptFor P gs := by simp [exceptFor,discard]
      rw [hcut]
      constructor
      · change prior g old ⊆ new ∪ ignore
        by_cases h : g.out ∈ old
        · simp only [prior,h,ite_true]
          exact Finset.union_subset ((Finset.erase_subset ..).trans next)
            ((ins g (by simp) discard).trans Finset.subset_union_right)
        · simpa [prior,h] using next
      · by_cases h : g.out ∈ demand gs need <;> simpa [cone,h,exceptFor,discard] using keep
    · have hcut : exceptFor P (g::gs) = g :: exceptFor P gs := by simp [exceptFor,discard]
      have kept : g.out ∉ ignore := outs g (by simp) discard
      have use : g.out ∈ old → g.out ∈ new := fun h => (Finset.mem_union.mp (next h)).resolve_right kept
      rw [hcut]
      constructor
      · change prior g old ⊆ prior g new ∪ ignore
        intro x hx
        by_cases h : g.out ∈ old
        · have h' := use h
          simp only [prior,h,h',ite_true,Finset.mem_union,Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne,hm⟩ | src
          · rcases Finset.mem_union.mp (next hm) with a | a <;> tauto
          · tauto
        · simp only [prior,h,ite_false] at hx
          by_cases h' : g.out ∈ new
          · simp only [prior,h',ite_true,Finset.mem_union,Finset.mem_erase]
            rcases Finset.mem_union.mp (next hx) with a | a
            · exact .inl (.inl ⟨fun e => h (e ▸ hx),a⟩)
            · exact .inr a
          · simpa [prior,h'] using next hx
      · by_cases h : g.out ∈ old
        · have h' := use h
          change g.out ∈ demand gs need at h
          change g.out ∈ demand (exceptFor P gs) need at h'
          simp only [cone,h,h',ite_true]
          rw [show exceptFor P (g::cone gs need) = g :: exceptFor P (cone gs need) by
            simp [exceptFor,discard]]
          exact List.cons_subset_cons _ keep
        · change g.out ∉ demand gs need at h
          simp only [cone,h,ite_false]
          split
          · exact fun _ ha => List.mem_cons_of_mem _ (keep ha)
          · exact keep
theorem tips_demand_except {P raw : Finset Word} {gs : List LogicalGate} {t : Word}
    (closed : prefixClosed raw P gs) (disj : Disjoint raw (produced gs))
    (inside : P ⊆ gatesFor gs t) :
    tips P gs ⊆ demand (exceptFor P gs) {t} := by
  let ignore := raw ∪ P
  have frozen := zz54n0 P ignore {t} gs closed (by
    intro g hg hn h
    exact (Finset.mem_union.mp h).elim (fun hraw =>
      Finset.disjoint_left.mp disj hraw (mem_produced.mpr ⟨g,hg,rfl⟩)) hn)
  intro v hv
  have bd := boundary_covers_tips (cone_sublist gs {t}).subset (cone_productive gs t) inside hv
  obtain ⟨src,_⟩ := Finset.mem_sdiff.mp bd
  have touch : v ∈ ({t} : Finset Word) ∪ readBy (cone (exceptFor P gs) {t}) := by
    rcases Finset.mem_insert.mp src with eq | hread
    · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr eq)
    · obtain ⟨g,hg,hs⟩ := mem_readBy.mp hread
      exact Finset.mem_union_right _ (mem_readBy.mpr ⟨g,frozen.2 hg,hs⟩)
  rw [← cone_touches] at touch
  exact (Finset.mem_union.mp touch).resolve_right (fun hp => by
    have e := produced_mono (cone_sublist (exceptFor P gs) {t}).subset hp
    rw [produced_except] at e
    exact (Finset.mem_sdiff.mp e).2 (Finset.mem_sdiff.mp hv).1)
theorem common_tips_demand {raw : Finset Word} {gs p : List LogicalGate} {t u : Word}
    (unique : (gs.map LogicalGate.out).Nodup) (disj : Disjoint raw (produced gs))
    (sub : p ⊆ kept (shared gs t u) gs) (valid : scheduled raw p) :
    produced p \ readBy p ⊆
      demand (exceptFor (produced p) gs) {t} ∩ demand (exceptFor (produced p) gs) {u} := by
  have whole : p ⊆ gs := fun _ h => (List.mem_filter.mp (sub h)).1
  have inside : produced p ⊆ shared gs t u := by
    intro x hx
    obtain ⟨g,hg,rfl⟩ := mem_produced.mp hx
    exact of_decide_eq_true (List.mem_filter.mp (sub hg)).2
  have closed := subset_prefix_closed unique whole valid
  have left := tips_demand_except closed disj (fun x hx => (Finset.mem_inter.mp (inside hx)).1)
  have right := tips_demand_except closed disj (fun x hx => (Finset.mem_inter.mp (inside hx)).2)
  intro x hx
  obtain ⟨prod,unread⟩ := Finset.mem_sdiff.mp hx
  have tip : x ∈ tips (produced p) gs := by
    apply Finset.mem_sdiff.mpr
    refine ⟨prod,?_⟩
    intro read
    obtain ⟨g,hm,hx⟩ := mem_readBy.mp read
    obtain ⟨hg,sel⟩ := List.mem_filter.mp hm
    obtain ⟨q,hq,e⟩ := mem_produced.mp (of_decide_eq_true sel)
    exact unread (mem_readBy.mpr ⟨q,hq,same_producer unique hg (whole hq) e.symm ▸ hx⟩)
  exact Finset.mem_inter.mpr ⟨left tip,right tip⟩
theorem common_book_tips_demand {gs p : List LogicalGate} {t u : Word}
    (orig : History gs) (pre : History p) (sub : p ⊆ kept (shared gs t u) gs) :
    (bookOf p).tips.toFinset ⊆
      demand (exceptFor (produced p) gs) {t} ∩ demand (exceptFor (produced p) gs) {u} := by
  obtain ⟨_,nd,disj⟩ := history_schedule orig
  rw [book_tips pre]
  exact common_tips_demand nd disj sub (history_schedule pre).1
end L652
namespace L652
private def zz55n0 (t u : Word) : Prop :=
  ∀ a b : Bool, ∃ i : Fin 64, t.getLsbD i.val = a ∧ u.getLsbD i.val = b
private theorem zz55n1 : ∀ (b a c : Bool), ∃ i : Fin 64,
    (domainWord 0 b).getLsbD i.val = true ∧ (matchWord 1).getLsbD i.val = a ∧
    (matchWord 2).getLsbD i.val = c := by decide +kernel
private theorem zz55n2 {b gs t u} (ex : ResidualExample 0 1 2 b gs t u) : zz55n0 t u := by
  intro a c
  obtain ⟨i,dom,aa,cc⟩ := zz55n1 b a c
  exact ⟨i,(ex.vt i dom).trans aa,(ex.vu i dom).trans cc⟩
private theorem zz55n3 (g : LogicalGate) (x : Word) (used : x ∈ sources g) :
    ¬zz55n0 x g.out := by
  intro all
  cases g with
  | neg v =>
    have e : x=v := by simpa [sources] using used
    subst x
    obtain ⟨i,h,k⟩ := all true true
    simp only [LogicalGate.out,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,h] at k
    exact Bool.noConfusion k
  | meet v w =>
    obtain ⟨i,h,k⟩ := all false true
    simp only [sources,Finset.mem_insert,Finset.mem_singleton] at used
    rcases used with rfl|rfl <;> simp only [LogicalGate.out,BitVec.getLsbD_and,h,Bool.false_and,Bool.and_false] at k <;> exact Bool.noConfusion k
  | join v w =>
    obtain ⟨i,h,k⟩ := all true false
    simp only [sources,Finset.mem_insert,Finset.mem_singleton] at used
    rcases used with rfl|rfl <;> simp only [LogicalGate.out,BitVec.getLsbD_or,h,Bool.true_or,Bool.or_true] at k <;> exact Bool.noConfusion k
private theorem zz55n4 (g : LogicalGate) (t : Word) :
    demand [g] {t} = if g.out=t then sources g else {t} := by
  by_cases eq : g.out=t <;> simp [demand,prior,eq]
private theorem zz55n5 {t u x : Word} (gs : List LogicalGate)
    (both : x ∈ demand gs {t} ∩ demand gs {u}) (all : zz55n0 t u) : 2 ≤ gs.length := by
  have diff : t ≠ u := by
    rintro rfl
    obtain ⟨i,h,k⟩ := all true false
    exact Bool.noConfusion (h.symm.trans k)
  cases gs with
  | nil =>
    simp only [demand,List.foldr_nil,Finset.mem_inter,Finset.mem_singleton] at both
    exact (diff (both.1.symm.trans both.2)).elim
  | cons g gs =>
    cases gs with
    | cons a rest => simp
    | nil =>
      obtain ⟨pa,pb⟩ := Finset.mem_inter.mp both
      rw [zz55n4] at pa pb
      by_cases ht : g.out=t
      · have hu : g.out ≠ u := fun h => diff (ht.symm.trans h)
        simp only [ht,ite_true] at pa
        simp only [hu,ite_false,Finset.mem_singleton] at pb
        subst u
        apply False.elim
        apply zz55n3 g x pa
        intro a b
        obtain ⟨i,h,k⟩ := all b a
        exact ⟨i,k,ht ▸ h⟩
      · simp only [ht,ite_false,Finset.mem_singleton] at pa
        by_cases hu : g.out=u
        · simp only [hu,ite_true] at pb
          subst t
          exact (zz55n3 g x pb (hu.symm ▸ all)).elim
        · simp only [hu,ite_false,Finset.mem_singleton] at pb
          exact (diff (pa.symm.trans pb)).elim
theorem sorted_shared_eight {b first q} (c : SortedCommon b first q) : (first::q).length ≤ 8 := by
  obtain ⟨gs,t,u,ex,per⟩ := c.example_exists
  let p := sharedProgram gs t u
  have h := shared_program_spec ex
  have pre : History p := history_scheduled h.1 h.2.1
  have sub : p ⊆ kept (shared gs t u) gs := fun _ hm => hm
  have common := common_book_tips_demand ex.hist pre sub
  have ne : p ≠ [] := List.length_pos_iff.mp h.2.2.2.2.1
  have sn := tips_nonempty p ne
  have last := List.getLast_mem (l := (bookOf p).tips) sn
  have witness := common (List.mem_toFinset.mpr last)
  have two := zz55n5 (exceptFor (produced p) gs) witness (zz55n2 ex)
  have graph : produced p = shared gs t u := h.2.2.1
  have count := (List.filter_append_perm (fun g : LogicalGate => decide (g.out ∈ shared gs t u)) gs).length_eq
  rw [graph] at two
  change (p ++ exceptFor (shared gs t u) gs).length = gs.length at count
  rw [List.length_append] at count
  have total := ex.budget
  have same := per.length_eq
  change (first::q).length = p.length at same
  omega
end L652
namespace L652.GroupProjection
def dataFor (b : Bool) : Data := if b then data1 else data0
def rows : Bool → Bool → Bool → List Nat
  | false, false, false => [16,20,48,0,0,4,6,20,0,0,5,7,17,49,0,32,33,40,0,0,1,5,33,0,0,3,7,34,42,0,8,10,24,0,0,2,3,10,0,0,6,7,12,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  | false, false, true => [17,21,49,0,0,12,14,28,0,0,12,14,24,56,0,34,35,42,0,0,17,21,49,0,0,17,21,48,56,0,12,14,28,0,0,34,35,42,0,0,34,35,40,56,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  | false, true, false => [32,34,48,0,0,2,6,34,0,0,3,7,33,49,0,8,12,40,0,0,4,5,12,0,0,6,7,10,42,0,16,17,24,0,0,1,3,17,0,0,5,7,20,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  | false, true, true => [33,35,49,0,0,10,14,42,0,0,10,14,40,56,0,10,14,42,0,0,20,21,28,0,0,20,21,24,56,0,20,21,28,0,0,33,35,49,0,0,33,35,48,56,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  | true, false, false => [18,22,26,52,0,22,36,37,52,0,0,0,0,0,0,36,37,41,52,0,9,11,37,41,0,0,0,0,0,0,9,11,26,41,0,11,18,22,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  | true, false, true => [19,23,27,53,0,30,44,45,60,0,0,0,0,0,0,38,39,43,54,0,25,27,53,57,0,0,0,0,0,0,13,15,30,45,0,43,50,54,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  | true, true, false => [36,38,44,50,0,18,19,38,50,0,0,0,0,0,0,9,13,25,44,0,13,36,38,44,0,0,0,0,0,0,18,19,25,50,0,9,13,19,25,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  | true, true, true => [37,39,45,51,0,26,27,46,58,0,0,0,0,0,0,11,15,27,46,0,29,52,54,60,0,0,0,0,0,0,22,23,29,54,0,41,45,51,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem rowLen : ∀ b s r, (rows b s r).length=64 := by decide +kernel
def lane (b s r : Bool) (x : L652.Word) : Nat :=
  (BitVec.ofBoolListLE ((rows b s r).map x.getLsbD)).toNat
def column (b : Bool) (x : L652.Word) : Col :=
  ⟨(x &&& domainWord 0 b).toNat,lane b false false x,lane b false true x,
    lane b true false x,lane b true true x⟩
theorem column_full (b : Bool) (x : L652.Word) :
    (column b x).full=(x &&& domainWord 0 b).toNat := rfl
theorem domainFor : ∀ b, (dataFor b).domain=(domainWord 0 b).toNat := by decide +kernel
private def zz56n0 (c : Col) := (c.full,c.p1,c.n1,c.p2,c.n2)
private theorem zz56n1 : Function.Injective zz56n0 := by
  intro x y h
  cases x
  cases y
  simpa [zz56n0] using h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem zz56n2 : ∀ b, (rawWords.map (column b)).map zz56n0 = (dataFor b).raw.map zz56n0 :=
  by decide +kernel
theorem raw_column (b : Bool) : rawWords.map (column b) = (dataFor b).raw :=
  List.map_injective_iff.mpr zz56n1 (zz56n2 b)
theorem lane_at (b s r : Bool) (x : L652.Word) (i : Fin 64) :
    (lane b s r x).testBit i.val = x.getLsbD ((rows b s r).getD i.val 0) := by
  have hi : i.val < (rows b s r).length := by rw [rowLen]; exact i.isLt
  simp only [lane,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
    List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]
private theorem zz56n3 (b s r : Bool) (x : L652.Word) (i : Nat) (hi : 64 ≤ i) :
    (lane b s r x).testBit i = false := by
  have h : (rows b s r).length ≤ i := by rwa [rowLen]
  simp [lane,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
    List.getElem?_eq_none h]
set_option maxRecDepth 10000 in
theorem row_lt : ∀ b s r (i : Fin 64), (rows b s r).getD i.val 0 < 64 := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem legal : ∀ b s (i : Fin 64), (dataFor b).valid.testBit i.val = true →
    let a := (rows b s false).getD i.val 0
    let c := (rows b s true).getD i.val 0
    let target := matchWord (if s then 2 else 1)
    (domainWord 0 b).getLsbD a = true ∧ (domainWord 0 b).getLsbD c = true ∧
    target.getLsbD a ≠ target.getLsbD c := by decide +kernel
private theorem zz56n4 (b s r join : Bool) (x y : L652.Word) :
    lane b s r (if join then x ||| y else x &&& y) =
      (if join then lane b s r x ||| lane b s r y else lane b s r x &&& lane b s r y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · cases join <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.testBit_or,Nat.testBit_and,
      lane_at _ _ _ _ ⟨i,hi⟩,BitVec.getLsbD_or,BitVec.getLsbD_and]
  · cases join <;> simp [zz56n3 _ _ _ _ i (by omega),Nat.testBit_or,Nat.testBit_and]
private theorem zz56n5 (i : Nat) : Nat.testBit 0xffffffffffffffff i = decide (i < 64) := by
  change Nat.testBit ((2:Nat)^64-1) i = _
  rw [Nat.testBit_two_pow_sub_one]
private theorem zz56n6 (b s r : Bool) (x : L652.Word) :
    lane b s r (~~~x) = (0xffffffffffffffff ^^^ lane b s r x) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor,zz56n5]
  by_cases hi : i < 64
  · simp only [hi, decide_true, Bool.true_xor, lane_at _ _ _ _ ⟨i,hi⟩, BitVec.getLsbD_not,
      row_lt b s r ⟨i,hi⟩, Bool.true_and]
  · simp [hi,zz56n3 _ _ _ _ i (by omega)]
theorem column_bop (b join : Bool) (x y : L652.Word) :
    (column b x).combine join (column b y) = column b (if join then x ||| y else x &&& y) := by
  let m := domainWord 0 b
  have orFull : (x &&& m) ||| (y &&& m) = (x ||| y) &&& m := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or,BitVec.getLsbD_and]
    cases m.getLsbD i <;> simp
  have andFull : (x &&& m) &&& (y &&& m) = (x &&& y) &&& m := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and]
    cases m.getLsbD i <;> simp
  cases join <;> simp only [Col.combine,column,Bool.false_eq_true,ite_false,ite_true,Col.mk.injEq]
  · exact ⟨(BitVec.toNat_and _ _).symm.trans (congrArg BitVec.toNat andFull),
        (zz56n4 b false false false x y).symm,(zz56n4 b false true false x y).symm,
        (zz56n4 b true false false x y).symm,(zz56n4 b true true false x y).symm⟩
  · exact ⟨(BitVec.toNat_or _ _).symm.trans (congrArg BitVec.toNat orFull),
        (zz56n4 b false false true x y).symm,(zz56n4 b false true true x y).symm,
        (zz56n4 b true false true x y).symm,(zz56n4 b true true true x y).symm⟩
theorem column_neg (b : Bool) (x : L652.Word) :
    (column b x).neg (dataFor b).domain = column b (~~~x) := by
  let m := domainWord 0 b
  have full : m ^^^ (x &&& m) = (~~~x) &&& m := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor,BitVec.getLsbD_not,BitVec.getLsbD_and,hi,decide_true,Bool.true_and]
    cases m.getLsbD i <;> cases x.getLsbD i <;> decide
  simp only [Col.neg,column,Col.mk.injEq,domainFor]
  exact ⟨(BitVec.toNat_xor _ _).symm.trans (congrArg BitVec.toNat full),
    (zz56n6 b false false x).symm,(zz56n6 b false true x).symm,
    (zz56n6 b true false x).symm,(zz56n6 b true true x).symm⟩
theorem separates_at (b second : Bool) (x : L652.Word) (i : Fin 64) :
    ((column b x).separates second).testBit i.val =
      (x.getLsbD ((rows b second false).getD i.val 0) != x.getLsbD ((rows b second true).getD i.val 0)) := by
  cases second <;> simp only [Col.separates,column,Bool.false_eq_true,ite_false,ite_true,
    Nat.testBit_xor,lane_at]
end L652.GroupProjection
namespace L652.GroupProjection
def RawBound (b : Bool) : Prop :=
  ∀ (second : Bool) (m : Fin 64) (hit : Nat),
    (∀ i : Fin 64, (dataFor b).valid.testBit i.val = true → hit.testBit i.val = false →
       ∃ j : Fin 6, m.val.testBit j.val = true ∧
         (((dataFor b).raw.getD j.val default).separates second).testBit i.val = true) →
    rawCost (dataFor b) hit ≤ ((List.finRange 6).filter (fun j => m.val.testBit j.val)).length
private def zz57n0 (j : Fin 6) : L652.Word := rawWords.getD j.val 0
private def zz57n1 (A : Finset L652.Word) : Fin 64 :=
  (BitVec.ofBoolListLE (rawWords.map fun v => decide (v ∈ A))).toFin
private theorem zz57n2 (A : Finset L652.Word) (j : Fin 6) :
    (zz57n1 A).val.testBit j.val = decide (zz57n0 j ∈ A) := by
  have h : j.val < rawWords.length := j.isLt
  simp only [zz57n1,BitVec.val_toFin,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    zz57n0,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h,
    Option.map_some, Option.getD_some]
private theorem zz57n3 : (List.finRange 6).map zz57n0 = rawWords := by decide +kernel
private theorem zz57n4 (A : Finset L652.Word) :
    ((List.finRange 6).filter (fun j => (zz57n1 A).val.testBit j.val)).length =
    (rawWords.filter (fun v => decide (v ∈ A))).length := by
  rw [← zz57n3, List.filter_map,List.length_map]
  simp [zz57n2,Function.comp_def]
private theorem zz57n5 (b : Bool) (j : Fin 6) :
    (dataFor b).raw.getD j.val default = column b (zz57n0 j) := by
  have h : j.val < rawWords.length := j.isLt
  simp only [←raw_column,zz57n0,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]
private def zz57n6 (b second : Bool) (hit : Nat) (x : L652.Word) : Nat :=
  hit ||| (column b x).separates second
private def zz57n7 (b second : Bool) (hit : Nat) (ws : List L652.Word) : Nat :=
  ws.foldl (zz57n6 b second) hit
private theorem zz57n8 (b second : Bool) (hit : Nat) (ws : List L652.Word) :
    (ws.map (column b)).foldl (fun h c => h ||| c.separates second) hit = zz57n7 b second hit ws := by
  rw [List.foldl_map]
  rfl
private theorem zz57n9 (b s : Bool) (x y : List L652.Word) (hit : Nat) :
    zz57n7 b s hit (x ++ y) = zz57n7 b s (zz57n7 b s hit x) y := List.foldl_append
private theorem zz57n10 (b s : Bool) (i : Fin 64) (ws : List L652.Word) (hit : Nat) :
    (zz57n7 b s hit ws).testBit i.val = true ↔ hit.testBit i.val = true ∨
      ∃ w ∈ ws, ((column b w).separates s).testBit i.val = true := by
  induction ws generalizing hit with
  | nil => simp [zz57n7]
  | cons x xs ih =>
    change (zz57n7 b s (zz57n6 b s hit x) xs).testBit i.val = true ↔ _
    rw [ih]
    simp [zz57n6,Nat.testBit_or]
    aesop
private theorem zz57n11 (b s : Bool) (pick : L652.Word → Bool)
    (ws : List L652.Word) (hit limit : Nat) :
    extraCost (dataFor b) s hit limit (ws.map (column b)) ≤
    (ws.filter pick).length + rawCost (dataFor b) (zz57n7 b s hit (ws.filter pick)) := by
  induction ws generalizing hit limit with
  | nil => simp [extraCost,zz57n7]
  | cons x xs ih =>
    simp only [List.map_cons,extraCost]
    let a := extraCost (dataFor b) s hit limit (xs.map (column b))
    by_cases p : pick x = true
    · simp only [List.filter_cons,p,ite_true,List.length_cons]
      change (if a ≤ 1 then a else min a _) ≤ _+1 + rawCost _ (zz57n7 b s (zz57n6 b s hit x) _)
      split
      · omega
      · refine (Nat.min_le_right ..).trans ?_
        have h := ih (zz57n6 b s hit x) (a-1)
        simpa only [zz57n6,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using Nat.add_le_add_left h 1
    · simp only [List.filter_cons,p]
      split
      · exact ih hit limit
      · exact (Nat.min_le_left ..).trans (ih hit limit)
private theorem zz57n12 (sinks opts : List L652.Word) (A : Finset L652.Word)
    (clean : (rawWords ++ sinks ++ opts).Nodup)
    (within : A ⊆ (rawWords ++ sinks ++ opts).toFinset) (required : sinks.toFinset ⊆ A) :
    (rawWords.filter (fun x => decide (x ∈ A))).length + sinks.length +
      (opts.filter (fun x => decide (x ∈ A))).length = A.card := by
  let pool := rawWords ++ sinks ++ opts
  let pick := fun (x : L652.Word) => decide (x ∈ A)
  have e : (pool.filter pick).toFinset = A := by
    ext x
    simp only [List.mem_toFinset,List.mem_filter,pick,decide_eq_true_eq]
    exact ⟨And.right,fun h => ⟨List.mem_toFinset.mp (within h),h⟩⟩
  have cnt := List.toFinset_card_of_nodup (clean.filter pick)
  change (pool.filter pick).toFinset.card = _ at cnt
  rw [e] at cnt
  have fs : sinks.filter pick = sinks := List.filter_eq_self.mpr (by
    intro x hx; exact decide_eq_true (required (List.mem_toFinset.mpr hx)))
  simpa only [pool,List.filter_append,fs,List.length_append,pick] using cnt.symm
private theorem zz57n13 (b s : Bool) (A : Finset L652.Word) (sinks opts : List L652.Word)
    (within : A ⊆ (rawWords ++ sinks ++ opts).toFinset)
    (det : Determines (domainWord 0 b) A (matchWord (if s then 2 else 1))) :
    let selected := opts.filter (fun x => decide (x ∈ A))
    let hit := zz57n7 b s 0 (sinks ++ selected)
    ∀ i : Fin 64, (dataFor b).valid.testBit i.val = true → hit.testBit i.val = false →
       ∃ j : Fin 6, (zz57n1 A).val.testBit j.val = true ∧
         (((dataFor b).raw.getD j.val default).separates s).testBit i.val = true := by
  intro selected hit i active missed
  obtain ⟨left,right,apart⟩ := legal b s i active
  let u : Fin 64 := ⟨_,row_lt b s false i⟩
  let v : Fin 64 := ⟨_,row_lt b s true i⟩
  have witness : ∃ w ∈ A, w.getLsbD u.val ≠ w.getLsbD v.val := by
    by_contra! h
    exact apart (det u v left right h)
  obtain ⟨w,mem,diff⟩ := witness
  have changed : ((column b w).separates s).testBit i.val = true := by
    rw [separates_at]
    exact bne_iff_ne.mpr diff
  have pool := List.mem_toFinset.mp (within mem)
  simp only [List.mem_append] at pool
  rcases pool with (raw | sink) | opt
  · rw [←zz57n3] at raw
    obtain ⟨j,_,eq⟩ := List.mem_map.mp raw
    refine ⟨j,?_,?_⟩
    · simpa [zz57n2,eq] using mem
    · simpa only [zz57n5,eq] using changed
  · have h := (zz57n10 b s i (sinks ++ selected) 0).mpr
        (Or.inr ⟨w,List.mem_append_left _ sink,changed⟩)
    exact Bool.noConfusion (h.symm.trans missed)
  · have inside : w ∈ selected := List.mem_filter.mpr ⟨opt,decide_eq_true mem⟩
    have h := (zz57n10 b s i (sinks ++ selected) 0).mpr
        (Or.inr ⟨w,List.mem_append_right _ inside,changed⟩)
    exact Bool.noConfusion (h.symm.trans missed)
private theorem zz57n14 (b s : Bool) (rb : RawBound b) (A : Finset L652.Word)
    (sinks opts : List L652.Word) (limit : Nat)
    (clean : (rawWords ++ sinks ++ opts).Nodup) (within : A ⊆ (rawWords ++ sinks ++ opts).toFinset)
    (required : sinks.toFinset ⊆ A) (det : Determines (domainWord 0 b) A (matchWord (if s then 2 else 1))) :
    extraCost (dataFor b) s ((sinks.map (column b)).foldl (fun h c => h ||| c.separates s) 0)
      limit (opts.map (column b)) + sinks.length ≤ A.card := by
  let selected := opts.filter (fun x => decide (x ∈ A))
  have r := rb s (zz57n1 A) (zz57n7 b s 0 (sinks ++ selected)) (zz57n13 b s A sinks opts within det)
  rw [zz57n4,zz57n9] at r
  have e := zz57n11 b s (fun x => decide (x ∈ A)) opts (zz57n7 b s 0 sinks) limit
  have c := zz57n12 sinks opts A clean within required
  rw [zz57n8]
  change rawCost _ (zz57n7 b s (zz57n7 b s 0 sinks) (opts.filter _)) ≤ _ at r
  omega
theorem rules_of_raw (b : Bool) (rb : RawBound b) : GroupRules b (dataFor b) (column b) where
  raw := raw_column b
  domain := domainFor b
  full := column_full b
  neg := column_neg b
  meet := column_bop b false
  join := column_bop b true
  bound := by
    intro sinks opts A B budget clean _ ne a bsub ta tb total dA dB
    let sl := sinks.length
    have pos : 0 < sl := List.length_pos_iff.mpr ne
    let n := budget - 2*(sl-1)
    let sndHit := (sinks.map (column b)).foldl (fun h c => h ||| c.separates true) 0
    let fstHit := (sinks.map (column b)).foldl (fun h c => h ||| c.separates false) 0
    let fst := extraCost (dataFor b) false fstHit (n+1) (opts.map (column b))
    let snd := extraCost (dataFor b) true sndHit (n-fst+1) (opts.map (column b))
    have h1 : fst+sl ≤ A.card := zz57n14 b false rb A sinks opts _ clean a ta dA
    have h2 : snd+sl ≤ B.card := zz57n14 b true rb B sinks opts _ clean bsub tb dB
    change (if 2*((sinks.map (column b)).length - 1) > budget then false else _) = true
    simp only [List.length_map]
    have hbase : ¬2*(sinks.length - 1) > budget := by change ¬2*(sl-1)>budget; omega
    rw [if_neg hbase]
    change (if fst > n then false else decide (snd ≤ n - fst)) = true
    have hf : ¬fst > n := by dsimp only [n]; omega
    rw [if_neg hf, decide_eq_true_eq]
    dsimp only [n] at *
    omega
end L652.GroupProjection
namespace L652.GroupProjection
private def zz58n0 (b : Bool) := if b then data1 else data0
private def zz58n1 : Nat := 17024696172015
private def zz58n2 : Nat := 18159675916816
private def zz58n3 : Nat := 18446744073709551615
private def zz58n4 (j : Fin 9) := 5*j.val+4
private def zz58n5 (bs : Fin 9 → Bool) : Nat :=
  (List.finRange 9).foldr (fun j v => (if bs j then 2^(zz58n4 j) else 0) ||| v) 0
private def zz58n6 (u : Nat) :=
  let a := u &&& 17180393488
  let b := (u >>> 5) &&& 17180393488
  let p := (u >>> 10) &&& 17180393488
  let c := a + b + (p &&& (18446744073709551615 ^^^ (a ||| b)))
  ((c + (c >>> 15) + (c >>> 30)) >>> 4) &&& 7
private def zz58n7 (b second : Bool) (m : Fin 64) : Nat :=
  let d := zz58n0 b
  d.valid &&& ((List.finRange 6).foldr (fun j v =>
    (if m.val.testBit j.val then ((d.raw.getD j.val default).separates second) else 0) ||| v) 0)
private def zz58n8 (m : Fin 64) (j : Fin 9) :=
  let x := j.val/3
  if j.val % 3 == 0 then m.val.testBit x else if j.val % 3 == 1 then m.val.testBit (3+x)
    else m.val.testBit x || m.val.testBit (3+x)
private def zz58n9 (m : Fin 64) := ((List.finRange 6).filter (fun j => m.val.testBit j.val)).length
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n10 : zz58n5 (fun _ => true) = zz58n2 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private def zz58n11 (a b t : Bool) := a.toNat + b.toNat + (t && !(a || b)).toNat
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n12 : ∀ a b t x y : Bool, (a = true → x = true) →
    (b = true → y = true) → (t = true → (x || y) = true) → zz58n11 a b t ≤ x.toNat + y.toNat := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n13 : ∀ z : Fin 512, let bit := z.val.testBit
    zz58n6 (zz58n5 (fun j => bit j.val)) = zz58n11 (bit 0) (bit 1) (bit 2) +
      zz58n11 (bit 3) (bit 4) (bit 5) + zz58n11 (bit 6) (bit 7) (bit 8) := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n14 : ∀ m : Fin 64, let bit := m.val.testBit
    zz58n9 m = (bit 0).toNat + (bit 1).toNat + (bit 2).toNat +
      (bit 3).toNat + (bit 4).toNat + (bit 5).toNat := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n15 (z : Fin 512) (m : Fin 64)
    (ok : ∀ j : Fin 9, z.val.testBit j.val = true → zz58n8 m j = true) :
    zz58n6 (zz58n5 (fun j => z.val.testBit j.val)) ≤ zz58n9 m := by
  rw [zz58n13,zz58n14]
  have a := zz58n12 _ _ _ _ _ (ok 0) (ok 1) (ok 2)
  have c := zz58n12 _ _ _ _ _ (ok 3) (ok 4) (ok 5)
  have d := zz58n12 _ _ _ _ _ (ok 6) (ok 7) (ok 8)
  change zz58n11 (z.val.testBit 0) (z.val.testBit 1) (z.val.testBit 2) ≤
    (m.val.testBit 0).toNat + (m.val.testBit 3).toNat at a
  change zz58n11 (z.val.testBit 3) (z.val.testBit 4) (z.val.testBit 5) ≤
    (m.val.testBit 1).toNat + (m.val.testBit 4).toNat at c
  change zz58n11 (z.val.testBit 6) (z.val.testBit 7) (z.val.testBit 8) ≤
    (m.val.testBit 2).toNat + (m.val.testBit 5).toNat at d
  omega
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private def zz58n16 (b second : Bool) := ∀ (m : Fin 64) (j : Fin 9),
    let p := zz58n4 j; let M := 2^(p+1)
    2^p ≤ (zz58n7 b second m)%M + zz58n1 % M → zz58n8 m j = true
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n17 (b second : Bool) : zz58n16 b second := by
  unfold zz58n16
  cases b <;> cases second <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n18 (u : Nat) : u &&& zz58n2 = zz58n5 (fun j => u.testBit (zz58n4 j)) := by
  rw [←zz58n10]
  unfold zz58n5
  induction List.finRange 9 with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldr_cons,ite_true,Nat.and_or_distrib_left,ih]
    congr 1
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.testBit_two_pow]
    by_cases e : zz58n4 j = i
    · subst i; by_cases h : u.testBit (zz58n4 j) = true <;> simp_all [Nat.testBit_two_pow]
    · by_cases h : u.testBit (zz58n4 j) = true <;> simp_all [Nat.testBit_two_pow]
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n19 {α : Type} (f : α → Nat) (xs : List α) {j : α} (hj : j ∈ xs) (i : Nat)
    (bit : (f j).testBit i = true) : (xs.foldr (fun x v => f x ||| v) 0).testBit i = true := by
  induction xs with
  | nil => simp at hj
  | cons x xs ih =>
    simp only [List.foldr_cons,Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp hj with rfl | mem
    · exact Or.inl bit
    · exact Or.inr (ih mem)
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n20 {b second : Bool} {m : Fin 64} {hit : Nat}
    (h : ∀ i : Fin 64, (zz58n0 b).valid.testBit i.val = true → hit.testBit i.val = false →
      ∃ j : Fin 6, m.val.testBit j.val = true ∧
        (((zz58n0 b).raw.getD j.val default).separates second).testBit i.val = true) :
    let w := (zz58n0 b).valid &&& (zz58n3 ^^^ hit)
    w &&& zz58n7 b second m = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  by_cases hi : i < 64
  · have F : zz58n3.testBit i = true := by
      change ((2^64-1 : Nat).testBit i) = true
      exact (Nat.testBit_two_pow_sub_one 64 i).trans (decide_eq_true hi)
    rw [F]
    cases vd : (zz58n0 b).valid.testBit i <;> cases hv : hit.testBit i <;> simp only [Bool.false_and,Bool.true_and,Bool.and_false,Bool.xor_false,Bool.xor_true,Bool.not_true]
    obtain ⟨j,hm,hj⟩ := h ⟨i,hi⟩ vd hv
    simp only [zz58n7,Nat.testBit_and,vd,Bool.true_and]
    apply zz58n19 _ _ (by simp : j ∈ List.finRange 6) i
    simpa [hm] using hj
  · have small : (zz58n0 b).valid < 2^64 := by cases b <;> decide
    have hv := Nat.testBit_lt_two_pow (i:=i) (Nat.lt_of_lt_of_le small
      (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hv]
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private def zz58n21 (v : Nat) : Fin 512 :=
  ⟨(BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => v.testBit (zz58n4 j)))).toNat,
    by simpa using (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => v.testBit (zz58n4 j)))).isLt⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n22 (v : Nat) (j : Fin 9) :
    (zz58n21 v).val.testBit j.val = v.testBit (zz58n4 j) := by
  change (BitVec.ofBoolListLE _).toNat.testBit j.val = _
  rw [BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos j.isLt]
  rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n23 (v : Nat) (m : Fin 64)
    (allowed : ∀ j : Fin 9, v.testBit (zz58n4 j) = true → zz58n8 m j = true) :
    zz58n6 (v &&& zz58n2) ≤ zz58n9 m := by
  rw [zz58n18]
  have e : (fun j : Fin 9 => v.testBit (zz58n4 j)) =
      (fun j : Fin 9 => (zz58n21 v).val.testBit j.val) := funext fun j => (zz58n22 v j).symm
  rw [e]
  exact zz58n15 (zz58n21 v) m fun j hj => allowed j ((zz58n22 v j).symm.trans hj)
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n24 (w u : Nat) (hu : w &&& u = w) (p : Nat)
    (hj : (w+zz58n1).testBit p = true) :
    2^p ≤ u % (2^(p+1)) + zz58n1 % (2^(p+1)) := by
  let M := 2^(p+1)
  have hv : ((w+zz58n1)%M).testBit p = true := by simp [M,Nat.testBit_mod_two_pow,hj]
  have minV : 2^p ≤ (w+zz58n1)%M := Nat.ge_two_pow_of_testBit hv
  have bound : w % M ≤ u % M := by
    calc w % M = (w &&& u)%M := congrArg (fun n => n % M) hu.symm
         _ = (w % M) &&& (u % M) := Nat.and_mod_two_pow ..
         _ ≤ u % M := Nat.and_le_right
  have sum : (w+zz58n1)%M ≤ w % M + zz58n1 % M := by
    rw [Nat.add_mod]
    exact Nat.mod_le _ _
  exact Nat.le_trans minV (Nat.le_trans sum (Nat.add_le_add_right bound _))
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem rawCost_le_of_selected (b second : Bool) (m : Fin 64) (hit : Nat)
    (h : ∀ i : Fin 64, (zz58n0 b).valid.testBit i.val = true → hit.testBit i.val = false →
      ∃ j : Fin 6, m.val.testBit j.val = true ∧
        (((zz58n0 b).raw.getD j.val default).separates second).testBit i.val = true) :
    rawCost (zz58n0 b) hit ≤ zz58n9 m := by
  let w := (zz58n0 b).valid &&& (zz58n3 ^^^ hit)
  change zz58n6 ((w+zz58n1) &&& zz58n2) ≤ zz58n9 m
  apply zz58n23
  have hu : w &&& zz58n7 b second m = w := zz58n20 h
  exact fun j hj => zz58n17 b second m j (zz58n24 w _ hu (zz58n4 j) hj)
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
def postLower (u : Nat) :=
  let a := u &&& 17180393488
  let b := (u >>> 5) &&& 17180393488
  let p := (u >>> 10) &&& 17180393488
  let c := a + b + (p &&& (18446744073709551615 ^^^ (a ||| b)))
  ((c >>> 4) &&& 3) + ((c >>> 19) &&& 3) + ((c >>> 34) &&& 3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n25 : ∀ z : Fin 512, zz58n6 (zz58n5 (fun j => z.val.testBit j.val)) =
    postLower (zz58n5 (fun j => z.val.testBit j.val)) := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem rawCost_postLower (d : Data) (hit : Nat) :
    rawCost d hit = postLower (((d.valid &&& (18446744073709551615 ^^^ hit)) + 17024696172015) &&& 18159675916816) := by
  let v := (d.valid &&& (18446744073709551615 ^^^ hit)) + 17024696172015
  change zz58n6 (v &&& zz58n2) = postLower (v &&& zz58n2)
  rw [zz58n18,show (fun j : Fin 9 => v.testBit (zz58n4 j)) =
      (fun j : Fin 9 => (zz58n21 v).val.testBit j.val) from funext fun j => (zz58n22 v j).symm]
  exact zz58n25 _
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem rawCost_le_seven (d : Data) (hit : Nat) : rawCost d hit ≤ 7 := Nat.and_le_right
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n26 : ∀ a b c x y z : Bool, (a=true → x=true) →
    (b=true → y=true) → (c=true → z=true) → zz58n11 a b c ≤ zz58n11 x y z := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n27 (v : Nat) :
    zz58n6 (v &&& zz58n2) =
      zz58n11 (v.testBit (zz58n4 0)) (v.testBit (zz58n4 1)) (v.testBit (zz58n4 2)) +
      zz58n11 (v.testBit (zz58n4 3)) (v.testBit (zz58n4 4)) (v.testBit (zz58n4 5)) +
      zz58n11 (v.testBit (zz58n4 6)) (v.testBit (zz58n4 7)) (v.testBit (zz58n4 8)) := by
  rw [zz58n18]
  have e := zz58n13 (zz58n21 v)
  simp only [zz58n22] at e
  have B (i : Nat) (k : i<9) : (zz58n21 v).val.testBit i = v.testBit (zz58n4 ⟨i,k⟩) := zz58n22 v ⟨i,k⟩
  rw [B 0 (by decide), B 1 (by decide), B 2 (by decide), B 3 (by decide), B 4 (by decide), B 5 (by decide), B 6 (by decide), B 7 (by decide), B 8 (by decide)] at e
  exact e
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n28 : ∀ (b : Bool) (j : Fin 9),
    let M := 2^(zz58n4 j+1)
    (zz58n0 b).valid % M + zz58n1 % M < M := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem zz58n29 {b : Bool} (w u : Nat) (hu : w &&& u = w)
    (valid : u &&& (zz58n0 b).valid = u) (j : Fin 9)
    (h : (w+zz58n1).testBit (zz58n4 j) = true) : (u+zz58n1).testBit (zz58n4 j) = true := by
  let p := zz58n4 j
  let M := 2^(p+1)
  have bound : u % M ≤ (zz58n0 b).valid % M := by
    calc u % M = (u &&& (zz58n0 b).valid)%M := congrArg (fun n => n % M) valid.symm
         _ = _ := Nat.and_mod_two_pow ..
         _ ≤ _ := Nat.and_le_right
  have zz58n7 : u % M+zz58n1 % M < M := Nat.lt_of_le_of_lt (Nat.add_le_add_right bound _) (zz58n28 b j)
  have lower : 2^p ≤ u % M+zz58n1 % M := zz58n24 w u hu p h
  have div : (u % M+zz58n1 % M)/2^p = 1 := Nat.div_eq_of_lt_le (by simpa using lower)
    (by simpa [M,Nat.pow_succ,Nat.mul_comm] using zz58n7)
  have hb : ((u+zz58n1)%M).testBit p = true := by
    rw [Nat.add_mod,Nat.mod_eq_of_lt zz58n7,Nat.testBit_eq_decide_div_mod_eq,div]; rfl
  simpa [M,Nat.testBit_mod_two_pow] using hb
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem rawCost_more_hits (b : Bool) (h extra : Nat) :
    rawCost (zz58n0 b) (h ||| extra) ≤ rawCost (zz58n0 b) h := by
  let u := (zz58n0 b).valid &&& (zz58n3 ^^^ h)
  let w := (zz58n0 b).valid &&& (zz58n3 ^^^ (h ||| extra))
  have valid : u &&& (zz58n0 b).valid = u := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [u,Nat.testBit_and]; cases (zz58n0 b).valid.testBit i <;> simp
  have hu : w &&& u = w := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [w,u,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_or]
    by_cases fin : i<64
    · have F : zz58n3.testBit i = true := (Nat.testBit_two_pow_sub_one 64 i).trans (decide_eq_true fin)
      rw [F]; cases (zz58n0 b).valid.testBit i <;> cases h.testBit i <;> cases extra.testBit i <;> rfl
    · have sm : (zz58n0 b).valid < 2^64 := by cases b <;> decide
      have hv : (zz58n0 b).valid.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le sm (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hv]
  change zz58n6 ((w+zz58n1) &&& zz58n2) ≤ zz58n6 ((u+zz58n1) &&& zz58n2)
  rw [zz58n27,zz58n27]
  have p := zz58n29 w u hu valid
  exact Nat.add_le_add (Nat.add_le_add (zz58n26 _ _ _ _ _ _ (p 0) (p 1) (p 2))
       (zz58n26 _ _ _ _ _ _ (p 3) (p 4) (p 5))) (zz58n26 _ _ _ _ _ _ (p 6) (p 7) (p 8))
end L652.GroupProjection
namespace L652.GroupProjection
theorem checked_rules (b : Bool) : GroupRules b (dataFor b) (column b) :=
  rules_of_raw b (rawCost_le_of_selected b)
end L652.GroupProjection
namespace L652
open GroupProjection
end L652
namespace L652
def moveIndex (s : SymIndex) (i : Nat) := if h : i<6 then (coordMap s ⟨i,h⟩).val else i
def ordKey (a b op : Nat) := (max a b*32+min a b)*3+op
def moveKey (s : SymIndex) (c : Nat) := ordKey (moveIndex s (c/3 % 32)) (moveIndex s (c/3/32)) (c % 3)
def pairRank (a b : Nat) := 2048*a+b
def orbitPair (a b : Nat) : Prop := ∀ s : SymIndex, fixesZero s →
  pairRank a b ≤ pairRank (moveKey s a) (moveKey s b) ∧
  (b/3/32<6 → pairRank a b ≤ pairRank (moveKey s b) (moveKey s a))
instance (a b : Nat) : Decidable (orbitPair a b) := by unfold orbitPair; infer_instance
theorem order_raw_image {s : SymIndex} {x : Word} : relabel s x ∈ rawWords ↔ x ∈ rawWords := by
  constructor
  · intro yes
    obtain ⟨a,ha,e⟩ := List.mem_map.mp ((mapped_raw s).mem_iff.mpr yes)
    exact (relabel_injective s e) ▸ ha
  · intro hx
    exact (mapped_raw s).mem_iff.mp (List.mem_map.mpr ⟨x,hx,rfl⟩)
private theorem zz61n0 (s : SymIndex) (xs : List Word) (v : Word) :
    (xs.map (relabel s)).idxOf (relabel s v) = xs.idxOf v := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.idxOf_cons]
    by_cases h : a=v
    · simp [h]
    · have h' : relabel s a ≠ relabel s v := fun e => h (relabel_injective s e)
      simp [h,h',ih,Ne.symm h,Ne.symm h']
theorem move_idx (s : SymIndex) (extra : List Word) (v : Word) :
    (rawWords++extra.map (relabel s)).idxOf (relabel s v) =
      moveIndex s ((rawWords++extra).idxOf v) := by
  by_cases hm : v∈rawWords
  · obtain ⟨i,rfl⟩ := exists_rawAt v hm
    have same := (@order_raw_image s _).mpr hm
    rw [List.idxOf_append_of_mem same,List.idxOf_append_of_mem hm]
    rw [show relabel s (rawAt i)=rawAt (coordMap s i) from relabel_raw s i,raw_idx,raw_idx]
    simp [moveIndex,i.isLt]
  · have no := mt (@order_raw_image s _).mp hm
    rw [List.idxOf_append_of_notMem hm,List.idxOf_append_of_notMem no,zz61n0]
    change 6+extra.idxOf v = moveIndex s (6+extra.idxOf v)
    simp [moveIndex]
theorem renamed_key (s : SymIndex) (extra : List Word) {g : LogicalGate}
    (ok : sources g ⊆ (rawWords++extra).toFinset) (sz : extra.length≤26) :
    gateKey (rawWords++extra.map (relabel s)) (mapGate s g) = moveKey s (gateKey (rawWords++extra) g) := by
  have d := key_decode ok (by rw [List.length_append]; change 6+extra.length≤32; omega)
  unfold moveKey
  rw [d.1,d.2.1,d.2.2.1]
  cases g with
  | neg a => simp [gateKey,mapGate,operandPair,operation,ordKey,move_idx]
  | meet a b | join a b =>
    by_cases h : (rawWords++extra).idxOf a ≤ (rawWords++extra).idxOf b
    · simp [gateKey,mapGate,operandPair,operation,ordKey,move_idx,min_eq_left h,max_eq_right h]
    · have h' : (rawWords++extra).idxOf b ≤ (rawWords++extra).idxOf a := by omega
      simp [gateKey,mapGate,operandPair,operation,ordKey,move_idx,min_eq_right h',max_eq_left h',min_comm,max_comm]
theorem moved_ready (s : SymIndex) (extra : List Word) {g : LogicalGate}
    (ok : sources g ⊆ (rawWords++extra).toFinset) :
    sources (mapGate s g) ⊆ (rawWords++extra.map (relabel s)).toFinset := by
  intro x hx
  have hm := mem_sources.mp hx
  rw [mapGate_args] at hm
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
  rcases List.mem_append.mp (List.mem_toFinset.mp (ok (mem_sources.mpr hv))) with hr | he
  · exact List.mem_toFinset.mpr (List.mem_append_left _ (order_raw_image.mpr hr))
  · exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨_,he,rfl⟩))
theorem key_stable {w : List Word} {g : LogicalGate} (ok : sources g ⊆ w.toFinset) (v : Word) :
    gateKey (w++[v]) g = gateKey w g := by
  have stable (x : Word) (h : x ∈ sources g) := List.idxOf_append_of_mem (l₂:=[v]) (List.mem_toFinset.mp (ok h))
  cases g with
  | neg a => simp only [gateKey,operandPair,stable a (by simp [sources])]
  | meet a b | join a b =>
    simp only [gateKey,operandPair,stable a (by simp [sources]),stable b (by simp [sources])]
theorem raw_only_of_key {g : LogicalGate} {v : Word}
    (ok : sources g ⊆ (rawWords++[v]).toFinset) (early : gateKey (rawWords++[v]) g /3/32 < 6) :
    sources g ⊆ rawWords.toFinset := by
  have dec := key_decode ok (by simp [rawWords])
  rw [dec.2.1] at early
  have yes (a : Word) (h : (rawWords++[v]).idxOf a <6) : a ∈ rawWords := by
    by_contra miss
    rw [List.idxOf_append_of_notMem miss] at h
    change 6+_ < 6 at h; omega
  cases g with
  | neg a => simpa [sources] using yes a early
  | meet a b | join a b =>
    change max _ _ < 6 at early
    simpa only [sources,Finset.insert_subset_iff,Finset.singleton_subset_iff,List.mem_toFinset] using And.intro (yes a (by omega)) (yes b (by omega))
end L652
namespace L652
theorem same_key_value {w : List Word} {g x : LogicalGate} (a : sources g ⊆ w.toFinset)
    (b : sources x ⊆ w.toFinset) (short : w.length≤32) (e : gateKey w g = gateKey w x) :
    g.out = x.out := by
  have h := (eval_gate_key a short).symm.trans ((congrArg (PrivateCertificate.value (w.map UInt64.ofBitVec)) e).trans
    (eval_gate_key b short))
  exact congrArg UInt64.toBitVec h
theorem least_two {g k : LogicalGate} {tail : List LogicalGate} (c : SortedCommon b g (k::tail))
    {a z : LogicalGate} (ha : a∈g::k::tail) (hz : z∈g::k::tail) (distinct : a.out ≠ z.out)
    (ra : sources a ⊆ rawWords.toFinset) (rz : sources z ⊆ (rawWords++[a.out]).toFinset) :
    pairRank (gateKey rawWords g) (gateKey (rawWords++[g.out]) k) ≤
      pairRank (gateKey rawWords a) (gateKey (rawWords++[a.out]) z) := by
  have lb := first_le_ready c.ordered ra ha
  cases c.ordered with
  | cons rg zero tailord =>
    have rk := tailord.scheduled.1
    by_cases tie : gateKey rawWords g = gateKey rawWords a
    · have same := same_key_value rg ra (by decide) tie
      have neq : z ≠ g := fun e => distinct (same.symm.trans (congrArg LogicalGate.out e).symm)
      rw [←same] at rz ⊢
      have l2 := first_le_ready tailord rz ((List.mem_cons.mp hz).resolve_left neq)
      unfold pairRank; omega
    · have cap := (key_ready (rawWords++[g.out]) k (by simp [rawWords])).mp rk
      change gateKey (rawWords++[g.out]) k < 96*7 at cap
      unfold pairRank
      omega
theorem relabel_common {b g q} (c : SortedCommon b g q) (s : SymIndex) (keep : fixesZero s) :
    ∃ k r, SortedCommon b k r ∧ (k::r).Perm ((g::q).map (mapGate s)) := by
  obtain ⟨gs,t,u,ex,perm⟩ := c.example_exists
  rw [fixesZero,←relabel_from,←relabel_from,←relabel_from] at keep
  rcases keep with ⟨ef,⟨ej,ek⟩ | ⟨ej,ek⟩⟩
  · obtain ⟨k,r,p,ok⟩ := sort_common (ex.mapped s 0 1 2 ef ej ek)
    rw [sharedProgram_map] at p
    exact ⟨k,r,ok,p.trans (perm.map _).symm⟩
  · obtain ⟨k,r,p,ok⟩ := sort_common (ex.mapped s 0 2 1 ef ej ek).swap
    rw [sharedProgram_swap,sharedProgram_map] at p
    exact ⟨k,r,ok,p.trans (perm.map _).symm⟩
end L652
namespace L652
def rankThree (a b c : Nat) := (2048*a+b)*2048+c
theorem least_three {g k m : LogicalGate} {tail : List LogicalGate}
    (c : SortedCommon b g (k::m::tail)) {a z h : LogicalGate}
    (ha : a∈g::k::m::tail) (hz : z∈g::k::m::tail) (hh : h∈g::k::m::tail)
    (az : a.out≠z.out) (ah : a.out≠h.out) (zh : z.out≠h.out)
    (ra : sources a ⊆ rawWords.toFinset)
    (rz : sources z ⊆ (rawWords++[a.out]).toFinset)
    (rh : sources h ⊆ (rawWords++[a.out,z.out]).toFinset) :
    rankThree (gateKey rawWords g) (gateKey (rawWords++[g.out]) k)
      (gateKey (rawWords++[g.out,k.out]) m) ≤
    rankThree (gateKey rawWords a) (gateKey (rawWords++[a.out]) z)
      (gateKey (rawWords++[a.out,z.out]) h) := by
  have low := least_two c ha hz az ra rz
  cases c.ordered with
  | cons rg _ ord =>
    cases ord with
    | cons rk _ ord' =>
      have rm : sources m ⊆ (rawWords++[g.out,k.out]).toFinset := ord'.scheduled.1
      have mk := (key_ready _ m (by simp [rawWords])).mp rm
      change gateKey (rawWords++[g.out,k.out]) m < 96*8 at mk
      have kk := (key_ready _ k (by simp [rawWords])).mp rk
      change gateKey (rawWords++[g.out]) k < 96*7 at kk
      have zk := (key_ready _ z (by simp [rawWords])).mp rz
      change gateKey (rawWords++[a.out]) z < 96*7 at zk
      unfold pairRank at low
      by_cases eqPair : 2048 * gateKey rawWords g + gateKey (rawWords++[g.out]) k =
                        2048 * gateKey rawWords a + gateKey (rawWords++[a.out]) z
      · have eqA : gateKey rawWords g = gateKey rawWords a := by omega
        have ea := same_key_value rg ra (by decide) eqA
        have eqZ : gateKey (rawWords++[g.out]) k = gateKey (rawWords++[a.out]) z := by omega
        rw [←ea] at rz eqZ
        have ez := same_key_value rk rz (by simp [rawWords]) eqZ
        rw [←ea,←ez] at rh
        have hg : h ≠ g := fun e => ah (ea.symm.trans (congrArg LogicalGate.out e).symm)
        have hk : h ≠ k := fun e => zh (ez.symm.trans (congrArg LogicalGate.out e).symm)
        have rest := first_le_ready ord' rh ((List.mem_cons.mp ((List.mem_cons.mp hh).resolve_left hg)).resolve_left hk)
        unfold rankThree
        rw [eqPair]
        simpa only [ea,ez,List.append_assoc,List.cons_append,List.nil_append] using Nat.add_le_add_left rest
          ((2048 * gateKey rawWords a + gateKey (rawWords++[a.out]) z)*2048)
      · unfold rankThree
        omega
def flipWire (i : Nat) := if i=6 then 7 else if i=7 then 6 else i
def flipKey (k : Nat) := ordKey (flipWire (k/3 % 32)) (flipWire (k/96)) (k % 3)
def orbitThird (a b c : Nat) : Prop := ∀ s : SymIndex, fixesZero s →
  rankThree a b c ≤ rankThree (moveKey s a) (moveKey s b) (moveKey s c) ∧
  (b/96<6 → rankThree a b c ≤ rankThree (moveKey s b) (moveKey s a) (flipKey (moveKey s c)))
instance (a b c : Nat) : Decidable (orbitThird a b c) := by unfold orbitThird; infer_instance
theorem flip_idx {a z x : Word} (ha : a∉rawWords) (hz : z∉rawWords) (ne : a ≠ z)
    (hx : x∈rawWords++[a,z]) :
    (rawWords++[z,a]).idxOf x = flipWire ((rawWords++[a,z]).idxOf x) := by
  by_cases hr : x∈rawWords
  · have lt := List.idxOf_lt_length_iff.mpr hr
    change rawWords.idxOf x < 6 at lt
    rw [List.idxOf_append_of_mem hr,List.idxOf_append_of_mem hr]
    simp [flipWire,show rawWords.idxOf x≠6 by omega,show rawWords.idxOf x≠7 by omega]
  · rcases List.mem_append.mp hx with bad | good
    · exact (hr bad).elim
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at good
      rw [List.idxOf_append_of_notMem hr,List.idxOf_append_of_notMem hr]
      rcases good with rfl | rfl <;>
        simp [show rawWords.length=6 by rfl,ne,Ne.symm ne,List.idxOf_cons,flipWire]
theorem flip_key {a z : Word} {g : LogicalGate} (ha : a∉rawWords) (hz : z∉rawWords) (ne : a≠z)
    (ok : sources g ⊆ (rawWords++[a,z]).toFinset) :
    gateKey (rawWords++[z,a]) g = flipKey (gateKey (rawWords++[a,z]) g) := by
  have dec := key_decode ok (by simp [rawWords])
  have ids (x : Word) (h : x∈sources g) := flip_idx ha hz ne (List.mem_toFinset.mp (ok h))
  unfold flipKey
  rw [show gateKey (rawWords ++ [a,z]) g/96 = gateKey (rawWords++[a,z]) g/3/32 by
    rw [Nat.div_div_eq_div_mul],dec.1,dec.2.1,dec.2.2.1]
  cases g with
  | neg x => simp [gateKey,operandPair,operation,ordKey,ids x (by simp [sources])]
  | meet x y | join x y =>
    by_cases h : (rawWords++[a,z]).idxOf x ≤ (rawWords++[a,z]).idxOf y
    all_goals first
      | solve | simp [gateKey,operandPair,operation,ordKey,ids x (by simp [sources]),
          ids y (by simp [sources]),min_eq_left h,max_eq_right h,min_comm,max_comm]
      | have h' : (rawWords++[a,z]).idxOf y ≤ (rawWords++[a,z]).idxOf x := by omega
        simp [gateKey,operandPair,operation,ordKey,ids x (by simp [sources]),
          ids y (by simp [sources]),min_eq_right h',max_eq_left h',min_comm,max_comm]
end L652
namespace L652
def rankGates (g k m : LogicalGate) := rankThree (gateKey rawWords g)
  (gateKey (rawWords++[g.out]) k) (gateKey (rawWords++[g.out,k.out]) m)
private def zz64n0 (b : Bool) (n : Nat) := ∃ g k m r,
  SortedCommon b g (k::m::r) ∧ rankGates g k m = n
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1800000 in
theorem third_common {b first second third q}
    (orig : SortedCommon b first (second::third::q)) :
    ∃ g k m r, SortedCommon b g (k::m::r) ∧
      allowedSharedFirst (gateKey rawWords g) ∧
      orbitPair (gateKey rawWords g) (gateKey (rawWords++[g.out]) k) ∧
      orbitThird (gateKey rawWords g) (gateKey (rawWords++[g.out]) k)
        (gateKey (rawWords++[g.out,k.out]) m) := by
  classical
  have some_n : ∃ n, zz64n0 b n := ⟨_,first,second,third,q,orig,rfl⟩
  obtain ⟨g,k,m,r,c,minimal⟩ := Nat.find_spec some_n
  obtain ⟨gs,t,u,ex,perm⟩ := c.example_exists
  have fresh := (shared_program_spec ex).2.1.perm perm
  have rawg := (fresh.2 g (by simp)).2.2
  have rawk := (fresh.2 k (by simp)).2.2
  have data (s : SymIndex) (keep : fixesZero s) := relabel_common c s keep
  have r0 := c.ordered.scheduled.1
  have r1 : sources k ⊆ (rawWords++[g.out]).toFinset := by simpa using c.ordered.scheduled.2.1
  have r2 : sources m ⊆ (rawWords++[g.out,k.out]).toFinset := by simpa [Finset.insert_comm] using c.ordered.scheduled.2.2.1
  have sep := fresh.1
  simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at sep
  have move_ne (s : SymIndex) {a z : LogicalGate} (h : a.out ≠ z.out) :
      (mapGate s a).out ≠ (mapGate s z).out :=
    fun e => h (relabel_injective s ((mapGate_out s a).trans (e.trans (mapGate_out s z).symm)))
  have lower (s : SymIndex) (keep : fixesZero s) {a z h : LogicalGate}
      (ha : a∈(g::k::m::r).map (mapGate s)) (hz : z∈(g::k::m::r).map (mapGate s))
      (hh : h∈(g::k::m::r).map (mapGate s))
      (az : a.out≠z.out) (ah : a.out≠h.out) (zh : z.out≠h.out)
      (ra : sources a ⊆ rawWords.toFinset)
      (rz : sources z ⊆ (rawWords++[a.out]).toFinset)
      (rh : sources h ⊆ (rawWords++[a.out,z.out]).toFinset) :
      rankGates g k m ≤ rankGates a z h := by
    obtain ⟨gg,tail,ok,p⟩ := data s keep
    rcases tail with _ | ⟨kk, _ | ⟨mm,tail'⟩⟩
    · have bad := p.length_eq; simp at bad
    · have bad := p.length_eq; simp at bad
    · have low := Nat.find_min' some_n (show zz64n0 b _ from ⟨gg,kk,mm,tail',ok,rfl⟩)
      have hi := least_three ok (p.mem_iff.mpr ha) (p.mem_iff.mpr hz) (p.mem_iff.mpr hh) az ah zh ra rz rh
      rw [minimal]
      exact le_trans low hi
  have both (s : SymIndex) (fix : fixesZero s) := by
    have ma : mapGate s g∈(g::k::m::r).map (mapGate s) := by simp
    have mz : mapGate s k∈(g::k::m::r).map (mapGate s) := by simp
    have mh : mapGate s m∈(g::k::m::r).map (mapGate s) := by simp
    have a0 : sources (mapGate s g) ⊆ rawWords.toFinset := by
      simpa using moved_ready s [] (g := g) (by simpa using r0)
    have a1 : sources (mapGate s k) ⊆ (rawWords++[(mapGate s g).out]).toFinset := by
      simpa [mapGate_out] using moved_ready s [g.out] r1
    have a2 : sources (mapGate s m) ⊆ (rawWords++[(mapGate s g).out,(mapGate s k).out]).toFinset := by
      simpa [mapGate_out] using moved_ready s [g.out,k.out] r2
    have e0 : gateKey rawWords (mapGate s g) = moveKey s (gateKey rawWords g) := by
      simpa using renamed_key s [] (g := g) (by simpa using r0) (by decide)
    have e1 : gateKey (rawWords++[(mapGate s g).out]) (mapGate s k) = moveKey s (gateKey (rawWords++[g.out]) k) := by
      simpa [mapGate_out] using renamed_key s [g.out] r1 (by simp)
    have e2 : gateKey (rawWords++[(mapGate s g).out,(mapGate s k).out]) (mapGate s m) =
        moveKey s (gateKey (rawWords++[g.out,k.out]) m) := by
      simpa [mapGate_out] using renamed_key s [g.out,k.out] r2 (by simp)
    have dg := move_ne s sep.1.1
    have dm := move_ne s sep.1.2.1
    have dk := move_ne s sep.2.1.1
    have regular := lower s fix ma mz mh dg dm dk a0 a1 a2
    have bound := (key_ready _ _ (by simp [rawWords])).mp a2
    change gateKey (rawWords++[(mapGate s g).out,(mapGate s k).out]) (mapGate s m) < 96*8 at bound
    rw [e2] at bound
    unfold rankGates at regular
    rw [e0,e1,e2] at regular
    have swapped (rawOnly : gateKey (rawWords++[g.out]) k/96 < 6) := by
      have ok0 : sources k ⊆ rawWords.toFinset := raw_only_of_key r1 (by simpa only [Nat.div_div_eq_div_mul] using rawOnly)
      have a1' : sources (mapGate s k) ⊆ rawWords.toFinset := by
        simpa using moved_ready s [] (g := k) (by simpa using ok0)
      have a0' : sources (mapGate s g) ⊆ (rawWords++[(mapGate s k).out]).toFinset := by
        intro v hv; exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (a0 hv)))
      have a2' : sources (mapGate s m) ⊆ (rawWords++[(mapGate s k).out,(mapGate s g).out]).toFinset := by
        simpa only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_comm] using a2
      have rs := lower s fix mz ma mh dg.symm dk dm a1' a0' a2'
      have noa : (mapGate s g).out ∉ rawWords := by rw [←mapGate_out]; exact fun h => rawg (order_raw_image.mp h)
      have noz : (mapGate s k).out ∉ rawWords := by rw [←mapGate_out]; exact fun h => rawk (order_raw_image.mp h)
      have flip := flip_key noa noz dg a2
      have cap := (key_ready _ _ (by simp [rawWords])).mp a2'
      change gateKey (rawWords++[(mapGate s k).out,(mapGate s g).out]) (mapGate s m) < 96*8 at cap
      unfold rankGates at rs
      rw [key_stable a0,flip,e2] at rs
      rw [flip,e2] at cap
      rw [key_stable a1'] at e1
      rw [e1,e0] at rs
      exact And.intro rs cap
    exact And.intro regular (And.intro bound swapped)
  refine ⟨g,k,m,r,c,?_,?_,?_⟩
  · by_contra bad
    obtain ⟨s,fix,sm⟩ := shared_first_relabel r0 rawg bad
    have tr := (both s fix).1
    have hi := (both s fix).2.1
    have a1 : sources (mapGate s k) ⊆ (rawWords++[(mapGate s g).out]).toFinset := by
      simpa [mapGate_out] using moved_ready s [g.out] r1
    have e0 : gateKey rawWords (mapGate s g) = moveKey s (gateKey rawWords g) := by
      simpa using renamed_key s [] (g := g) (by simpa using r0) (by decide)
    have base := (key_ready _ _ (by simp [rawWords])).mp a1
    change gateKey (rawWords++[(mapGate s g).out]) (mapGate s k) < 96*7 at base
    have e1 : gateKey (rawWords++[(mapGate s g).out]) (mapGate s k) = moveKey s (gateKey (rawWords++[g.out]) k) := by
      simpa [mapGate_out] using renamed_key s [g.out] r1 (by simp)
    rw [e0] at sm; rw [e1] at base
    unfold rankThree at tr
    omega
  · intro s keep
    have ⟨reg,hi,swap⟩ := both s keep
    constructor
    · unfold rankThree at reg
      unfold pairRank
      omega
    · intro hr
      obtain ⟨rs,cap⟩ := swap (by simpa only [Nat.div_div_eq_div_mul] using hr)
      unfold rankThree at rs
      unfold pairRank
      omega
  · intro s keep
    have ⟨reg,hi,swap⟩ := both s keep
    exact ⟨reg,fun hr => (swap hr).1⟩
end L652
namespace L652.GroupProjection
def inspect8 (d : Data) (n : Nat) (s : State) :=
  !canContinue d s.sunk s.internal (10-n) &&
    (!canContinue d s.sunk s.internal (18-2*n) || bulk d n s false (8-n))
theorem inspect8_checks {d : Data} (law : LaneLaw d) {n : Nat} {s : State} (reach : Reach d n s)
    (hn : n≤8) (passed : inspect8 d n s = true) : check d n s (8-n)=true := by
  simp only [inspect8,Bool.and_eq_true,Bool.not_eq_true',Bool.or_eq_true] at passed
  generalize e : 8-n = fuel
  cases fuel with
  | zero => simp [check,passed.1]
  | succ k =>
    simp only [check,passed.1,Bool.false_eq_true,ite_false]
    have same : 10+k+1-n=18-2*n := by omega
    rcases passed.2 with stop | go
    · simp [same,stop]
    · split
      · rfl
      · exact bulk_steps law k reach (by omega) (e ▸ go)
end L652.GroupProjection
namespace L652.GroupProjection
theorem reach_width {d n s} (h : Reach d n s) : s.wires.length=d.raw.length+n := by
  induction h with
  | root => simp
  | step old mem ih => simp [trialAfter,ih,Nat.add_assoc]
theorem trial_index {d : Data} {s : State} {init : Bool} {t : Trial} (mem : t ∈ trials d s init)
    (width : s.wires.length≤32) : advance d s t.order = trialAfter s t := by
  unfold trials at mem
  obtain ⟨⟨y,b⟩,hy,outer⟩ := List.mem_flatMap.mp mem
  dsimp only at outer
  split at outer
  · simp at outer
  obtain ⟨⟨x,a⟩,hx,inner⟩ := List.mem_flatMap.mp outer
  dsimp only at inner
  split at inner
  · simp at inner
  obtain ⟨hb,ey⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hy)
  have ha' := List.mk_mem_zipIdx_iff_getElem?.mp hx
  obtain ⟨ha,ex⟩ := List.getElem?_eq_some_iff.mp ha'
  have hab : a≤b := by simp only [List.length_take] at ha; omega
  have ha0 : a<s.wires.length := by omega
  have ix : s.wires.getD a default = x := by
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha0] using ex
  have iy : s.wires.getD b default = y := by
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb] using ey
  have gate (op : Nat) (small : op≤2) (z : Col)
      (eq : z = if op==2 then x.neg d.domain else x.combine (op==1) y)
      (withTrial : t ∈ (if key a b op < s.last || z.full==0 || z.full==d.domain ||
          s.wires.any (fun w => w.full==z.full) then [] else
          [Trial.mk a b (key a b op) z (eatenMask s.sunk x y)])) :
      advance d s t.order = trialAfter s t := by
    split at withTrial
    · simp at withTrial
    · obtain rfl := List.mem_singleton.mp withTrial
      rw [trial_replay]
      have ai : key a b op / 3 % 32 = a := by unfold key; omega
      have bi : key a b op / 3 /32 = b := by unfold key; omega
      have oi : key a b op % 3 = op := by unfold key; omega
      simpa only [advance,ai,bi,oi,ix,iy,eq]
  split at inner
  · exact gate 2 (by decide) _ rfl inner
  · rcases List.mem_append.mp inner with h | h
    · exact gate 0 (by decide) _ rfl h
    · exact gate 1 (by decide) _ rfl h
end L652.GroupProjection
namespace L652.GroupProjection
def ticketCode (e : Nat) := e % 4194304
def ticketStart (e : Nat) := e/4194304 % 64
def ticketCount (e : Nat) := e/268435456
def rootState (d : Data) : State := ⟨d.raw,[],[],0⟩
theorem ticket_advance (d : Data) {a b : Nat} (ha : a<2048) (hb : b<2048) :
    prefixState d 2 (a+2048*b) = advance d (advance d (rootState d) a) b := by
  have l : (a+2048*b)%2048=a := by omega
  have r : (a+2048*b)/2048 % 2048=b := by omega
  simp only [prefixState,unpackCodes,l,r,List.foldl_cons,List.foldl_nil,rootState]
end L652.GroupProjection
namespace L652.GroupProjection
def rangeTicket (d : Data) (e : Nat) : Bool :=
  range8 d 2 (prefixState d 2 (ticketCode e)) (ticketStart e) (ticketCount e)
def coversThird (tickets : List Nat) (a b : Nat) (xs : List Trial) : Bool :=
  let sel := tickets.filter (fun e => ticketCode e == a+2048*b)
  xs.zipIdx.all fun (t,i) =>
    sel.any (fun e => decide (ticketStart e ≤ i ∧ i < ticketStart e+ticketCount e)) ||
    !decide (orbitThird a b t.order)
def thirdCoverage (d : Data) (tickets : List Nat) : Bool :=
  (trials d (rootState d) true).all fun t =>
    let s := advance d (rootState d) t.order
    decide (t.order<2048) &&
    (trials d s false).all fun u =>
      if orbitPair t.order u.order then
        let dst := advance d s u.order
        decide (u.order<2048) && coversThird tickets t.order u.order (trials d dst false)
      else true
def thirdNode (d : Data) (a b : Nat) (s : State) : Bool :=
  !canContinue d s.sunk s.internal 14 || stepAll d s false (fun dst =>
    if orbitThird a b dst.last then check d 3 dst 5 else true)
def nextThree (d : Data) (s : State) : Bool :=
  stepAll d s false (fun dst => if orbitPair s.last dst.last then thirdNode d s.last dst.last dst else true)
theorem third_range_local {d : Data} {tickets : List Nat}
    (all : ∀ e∈tickets,rangeTicket d e=true) {a b : Nat} {s : State}
    (eq : prefixState d 2 (a+2048*b)=s)
    (covered : coversThird tickets a b (trials d s false)=true)
    (law : LaneLaw d) (reachable : Reach d 2 s) (width : s.wires.length≤32) :
    thirdNode d a b s=true := by
  unfold thirdNode
  by_cases live : canContinue d s.sunk s.internal 14=true
  · simp only [live,Bool.not_true,Bool.false_or,stepAll_trials]
    apply List.all_eq_true.mpr
    intro t ht
    change (if orbitThird a b t.order then check d 3 (trialAfter s t) 5 else true)=true
    split
    next accept =>
      obtain ⟨i,hi,et⟩ := List.mem_iff_getElem.mp ht
      have zip : (t,i) ∈ (trials d s false).zipIdx :=
        List.mk_mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_eq_getElem hi,et])
      have ok := List.all_eq_true.mp covered (t,i) zip
      simp only [accept,decide_true,Bool.not_true,Bool.or_false] at ok
      obtain ⟨ticket,within,ran⟩ := List.any_eq_true.mp ok
      obtain ⟨mem,code⟩ := List.mem_filter.mp within
      have value := all _ mem
      simp only [rangeTicket,beq_iff_eq.mp code,eq,range8,live,Bool.not_true,Bool.false_or,
        Bool.and_eq_true] at value
      have sub : t ∈ ((trials d s false).drop (ticketStart ticket)).take (ticketCount ticket) := by
        obtain ⟨lo,top⟩ := of_decide_eq_true ran
        apply List.mem_iff_getElem.mpr
        refine ⟨i-ticketStart ticket,?_,?_⟩
        · simp only [List.length_take,List.length_drop]; omega
        · simpa only [List.getElem_take,List.getElem_drop,Nat.add_sub_of_le lo] using et
      have hit := List.all_eq_true.mp value.2 t sub
      rw [trial_index ht width] at hit
      exact inspect8_checks law (.step reachable ht) (by decide) hit
    next => rfl
  · simp [Bool.eq_false_iff.mpr live]
theorem third_root {b : Bool} {tickets : List Nat} (law : LaneLaw (dataFor b))
    (cov : thirdCoverage (dataFor b) tickets=true)
    (all : ∀ e∈tickets,rangeTicket (dataFor b) e=true) :
    stepAll (dataFor b) (rootState (dataFor b)) true (nextThree (dataFor b))=true := by
  let d := dataFor b
  have width : d.raw.length=6 := by cases b <;> rfl
  have root : Reach d 0 (rootState d) := .root
  rw [stepAll_trials]
  apply List.all_eq_true.mpr
  intro t ht
  have h := List.all_eq_true.mp cov t ht
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  have tt := trial_index ht (show (rootState d).wires.length≤32 by change d.raw.length≤32; omega)
  have r1 : Reach d 1 (trialAfter (rootState d) t) := .step root ht
  change stepAll d (trialAfter (rootState d) t) false _=true
  rw [stepAll_trials]
  apply List.all_eq_true.mpr
  intro u hu
  change (if orbitPair t.order u.order then thirdNode d t.order u.order (trialAfter _ u) else true)=true
  split
  next lead =>
    have hu' : u ∈ trials d (advance d (rootState d) t.order) false := tt.symm ▸ hu
    have hh := List.all_eq_true.mp h.2 u hu'
    simp only [lead,ite_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    have uu : advance d (trialAfter (rootState d) t) u.order = trialAfter (trialAfter (rootState d) t) u := trial_index hu (by rw [reach_width r1,width]; decide)
    have two := ticket_advance d h.1 hh.1
    rw [tt,uu] at two
    apply third_range_local all two _ law (.step r1 hu) (by rw [reach_width (.step r1 hu),width]; decide)
    have hcov : coversThird tickets t.order u.order (trials d (advance d (advance d (rootState d) t.order) u.order) false)=true := hh.2
    rw [tt,uu] at hcov
    exact hcov
  next => rfl
end L652.GroupProjection
namespace L652.GroupProjection
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem shortCommon (b : Bool) : verify (dataFor b) 1=true := by
  cases b <;> decide +kernel
theorem exclude_short {b g q} (c : SortedCommon b g q)
    (hf : allowedSharedFirst (gateKey rawWords g)) (len : q.length≤1) : False := by
  have r := checked_rules b
  have ini : projectState (column b) [] 0 = rootState (dataFor b) := by
    simp [projectState,rootState,wiresOf,bookOf,r.raw]
  cases c.ordered with
  | cons ready lo tail =>
    have passed := follow_group (pre := []) (g := g) (post := q) (last := 0) r c rfl ready lo true
      (fun _ => hf) (fun s => check (dataFor b) 1 s 1) (ini ▸ shortCommon b)
    exact excludes_suffix r c [g] q _ 1 rfl tail (by simp) len passed
theorem third_residual (tickets : Bool → List Nat) (laws : ∀ b,LaneLaw (dataFor b))
    (coverage : ∀ b,thirdCoverage (dataFor b) (tickets b)=true)
    (verified : ∀ b,∀ e∈tickets b,rangeTicket (dataFor b) e=true) : ResidualObstruction := by
  apply residual_obstruction_of_no_canonical
  intro b old oldTail orig oldOK
  rcases oldTail with _ | ⟨old2, _ | ⟨old3,r0⟩⟩
  · exact exclude_short orig oldOK (by simp)
  · exact exclude_short orig oldOK (by simp)
  obtain ⟨g,k,m,r,c,first,second,third⟩ := third_common orig
  have model := checked_rules b
  have beginAll := third_root (laws b) (coverage b) (verified b)
  have initial : projectState (column b) [] 0 = rootState (dataFor b) := by
    simp [projectState,rootState,bookOf,wiresOf,model.raw]
  have length := sorted_shared_eight c
  cases c.ordered with
  | cons ready lo more =>
    cases more with
    | cons ready2 lo2 more2 =>
      cases more2 with
      | cons ready3 lo3 tail =>
        have pass := follow_group (pre := []) (g := g) (post := k::m::r) (last := 0) model c rfl ready lo true
          (fun _ => first) _ (initial ▸ beginAll)
        let a := gateKey rawWords g
        let bkey := gateKey (rawWords++[g.out]) k
        let ckey := gateKey (rawWords++[g.out,k.out]) m
        have pass2 := follow_group (pre := [g]) (g := k) (post := m::r) (last := a) model c rfl ready2 lo2 false
          (by simp) (fun dst => if orbitPair a dst.last then thirdNode (dataFor b) a dst.last dst else true) pass
        change (if orbitPair a bkey then thirdNode (dataFor b) a bkey (projectState (column b) [g,k] bkey) else true)=true at pass2
        rw [if_pos second] at pass2
        have cost := group_budget model c (p := [g,k]) (post := m::r) rfl (by simp) 14
          (by simp only [List.length_cons,List.length_nil] at *; omega)
        simp only [thirdNode,projectState,cost,Bool.not_true,Bool.false_or] at pass2
        have pass3 := follow_group (pre := [g,k]) (g := m) (post := r) (last := bkey) model c rfl ready3 lo3 false
          (by simp) (fun dst => if orbitThird a bkey dst.last then check (dataFor b) 3 dst 5 else true) pass2
        change (if orbitThird a bkey ckey then check (dataFor b) 3 (projectState (column b) [g,k,m] ckey) 5 else true)=true at pass3
        rw [if_pos third] at pass3
        exact excludes_suffix model c [g,k,m] r ckey 5 rfl tail (by simp)
          (by simp only [List.length_cons,List.length_nil] at length; omega) pass3
end L652.GroupProjection
namespace L652.GroupProjection
def thirdBlock0_0 : List Nat := [5368905730,5721227266,1782775810,3221424130,4345497602,3875735554,1786972162,541263968,289605728,830670944,574818400,314771552,339937376,344131680,620955744,637732960,377686112,658704480,398657632,402851936]
def thirdBlock0_1 : List Nat := [2021853280,985860192,537077762,1090725890,839067650,604186626,616769538,901982210,2533566466,725821442,9131393120,709230688,8053459040,3615885408,268830817,273025121,818284641,839256161,314968161,319162465]
def thirdBlock0_2 : List Nat := [591792225,331745377,335939681,637929569,1187383393,1204160609,415631457,721815649,268834818,814094338,2445678594,633739266,3599112194,973477890,809902082,1636179970,856039426,629547010,642129922,658907138]
def thirdBlock0_3 : List Nat := [1749426178,977674242,537462786,2164852738,319358978,621348866,633931778,650708994,667486210,684263426,432605186,6443042912,4127787104,1879640161,1103693921,852035681,1401489505,617154657,2236156001,2269710433]
def thirdBlock0_4 : List Nat := [1766393953,537466882,2424903682,1388910594,1409882114,2773030914,1741232130,4832434272,2223577184,3062437984,1879644257,2982746209,2492012641,2798196833,2953386273,2731088161,1430853921,3330873633,10738016258,9664274528]
def thirdBlock0_5 : List Nat := [2416517217,575217761,3267960929,3049857121,1753817185,5100871969,5448999201,701047073,537469219,550052131,562635043,331948323,893985059,1456021795,420028707,6174617696,3318296672,805908577,550056033,826880097]
def thirdBlock0_6 : List Nat := [302592097,306786401,579416161,1124675681,1678323809,629747809,1175007329,1460220001,1481191521,273232163,277426467,550056227,290009379,1099510051,608776483,352923939,357118243,361312547,365506851,638136611]
def thirdBlock0_7 : List Nat := [378089763,675885347,9932716128,8858974305,1749629025,9395845411,7516797220,688470308,814307330,612980738,629757954,411654146,3490447362,2739666946,2781609986,315359523,608960803,348913955,365691171,395051299]
def thirdBlock0_8 : List Nat := [9127593986,541853987,311167267,873204003,1435240739,667683107,2727086372,369887524,676071716,1879842818,1909202946,3549175810,1993089026,306979105,1137451297,365699361,671883553,806105090,1892429826,1921789954]
def thirdBlock0_9 : List Nat := [1951150082,1443639298,659304450,269234465,562835745,596390177,604778785,898380065,374092065,927740193,286011683,290205987,327954723,869019939,881602851,382480675,8590735362,558643489,1129068833,1431058721]
def thirdBlock0_10 : List Nat := [931936545,4027332899,4358682915,7798012196,6711691266,642533378,2441889888,873220192,374098016,1879855106,1103908866,3805040642,1447841794,541872224,827084896,1116491872,1405898848,1703694432,290213985,1120686177]
def thirdBlock0_11 : List Nat := [877416545,655118433,286027778,2190241794,646737922,2953773152,3268345952,634323040,269418593,273612897,1351549025,298778721,1108279393,856621153,869204065,881786977,1162805345,6443436128,7517177953,2148481120]
def thirdBlock0_12 : List Nat := [1380923488,604977248,890189920,537868385,1359951969,1389312097,613365857,898578529,1896826976,340740192,3759100000,1938772064,1624199265,844058721,621760609,269443074,2962186242,1401905154,542074882,558852098]
def thirdBlock0_13 : List Nat := [1112500226,1406101506,4027711780,538052899,278006051,550635811,1632766243,584190243,861014307,3759278372,4296153090,1880234273,1909594401,1133648161,3759284226,3759284513,538062944,1087516768,571617376,806498401]
def thirdBlock0_14 : List Nat := [1364340833,588394593,605171809,1343369507,1095905571,4296159524,269629536,1351759968,575813728,861026400,538064993,1360148577,852637793,538065187,1620195619,1913796899,3222419748,1611810913,831670369,1112688737]
def thirdBlock0_15 : List Nat := [3222425696,588402784,3222425697,3222429698,2685560834,1074952288,290617440,1074952289,831682657,315783265,806518880,1095925856,315785312,1343389793,299008097,269656160,1083351136,269656161,1083351137,571646049]
def thirdBlock0_16 : List Nat := [806527265,806527267,1343398180]
def thirdTickets0 : List Nat := thirdBlock0_0 ++ (thirdBlock0_1 ++ (thirdBlock0_2 ++ (thirdBlock0_3 ++ (thirdBlock0_4 ++ (thirdBlock0_5 ++ (thirdBlock0_6 ++ (thirdBlock0_7 ++ (thirdBlock0_8 ++ (thirdBlock0_9 ++ (thirdBlock0_10 ++ (thirdBlock0_11 ++ (thirdBlock0_12 ++ (thirdBlock0_13 ++ (thirdBlock0_14 ++ (thirdBlock0_15 ++ (thirdBlock0_16))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem third_intervals0 : thirdCoverage data0 thirdTickets0=true := by decide +kernel
def thirdBlock1_0 : List Nat := [13153533954,1547894786,9127004162,4706207746,541263968,1363347552,579012704,318965856,616761440,629344352,1182992480,1476593760,969082976,981665888,734201952,537077762,1896032258,314779650,612575234,625158146]
def thirdBlock1_1 : List Nat := [1178806274,3083020290,755181570,541458528,1090912352,2726690912,654704736,2546335840,738590816,12348426336,9932507233,449185889,268834818,1082529794,2718308354,646322178,658905090,3360036866,1002838018,1078337538]
def thirdBlock1_2 : List Nat := [2714116098,642129922,3875938306,453386242,805896194,2705915906,633929730,3330867202,705232898,722010114,12348620896,11274879073,537462786,2701723650,629737474,2252933122,684263426,701040642,717817858,11543316576]
def thirdBlock1_3 : List Nat := [11543316577,537463072,1103694112,642320672,944310560,445188384,269031426,1883838466,1913198594,2479429634,4396226562,1510545410,9127401568,2827556960,6443047009,4396226657,11811756320,11274885409,11274887170,10469580896]
def thirdBlock1_4 : List Nat := [10469580897,10469581088,11006452001,537469219,281616675,285810979,566829347,604578083,1170809123,935928099,411640099,428417315,7785230432,3611897952,7248359521,3603509345,273232163,277426467,818491683,294203683]
def thirdBlock1_5 : List Nat := [1103704355,617165091,898183459,910766371,923349283,701051171,10469587040,9664280673,9932716323,7516797220,411646244,1082742786,621369346,1175017474,705255426,9396027394,1221328898,587989283,885784867,361496867]
def thirdBlock1_6 : List Nat := [382468387,688652579,9664464898,546048291,583797027,1150028067,1183582499,944507171,2731280676,369887524,667683108,10201339906,7022057760,9932906498,9664471328,7017865505,1879846914,4593561602,3322687490,269234464]
def thirdBlock1_7 : List Nat := [562835744,1137455392,1439445280,940323104,269234465,562835745,1137455393,1439445281,940323105,554447139,1137455395,1154232611,365703459,403452195,407646499,8322299906,5658917152,659306784,5658917153,659306785]
def thirdBlock1_8 : List Nat := [6980122915,1720465699,4845222180,382482724,7516997634,1728858114,2978760800,885803104,663504992,8322306050,7789629536,3779874913,642535521,554463234,2731307010,667709442,4295950432,3826188384,6980304993,6711871584]
def thirdBlock1_9 : List Nat := [6443436129,4564398176,1959735392,6175010913,4295964768,1955543136,5906577505,5118052448,5638148192,1892634721,336547937,269443074,2156879874,1125081090,1418682370,2152687618,852453378,604989442,4027711779,4564582692]
def thirdBlock1_10 : List Nat := [3222407459,1662126371,2685536548,5101459458,4027717920,5101459745,4833026050,4296155424,3222413601,2685546592,856830048,538062945,1091711073,580005985,865218657,3222417699,319959331,4027724068,2417113184,584202336]
def thirdBlock1_11 : List Nat := [869415008,2953984291,1389508899,2148681730,580012034,328353794,3490859104,4296165473,538071042,823283714,575819778,324161538,4296167520,2417119329,3490865154,3222431746,1611823200,303200352,806516833,1095923809]
def thirdBlock1_12 : List Nat := [315783265,806518880,1095925856,315785312,269656160,1083351136,571646048,269656161,546480225,806527264,806527265,1343398179,806527268]
def thirdTickets1 : List Nat := thirdBlock1_0 ++ (thirdBlock1_1 ++ (thirdBlock1_2 ++ (thirdBlock1_3 ++ (thirdBlock1_4 ++ (thirdBlock1_5 ++ (thirdBlock1_6 ++ (thirdBlock1_7 ++ (thirdBlock1_8 ++ (thirdBlock1_9 ++ (thirdBlock1_10 ++ (thirdBlock1_11 ++ (thirdBlock1_12))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem third_intervals1 : thirdCoverage data1 thirdTickets1=true := by decide +kernel
end L652.GroupProjection
namespace L652.GroupProjection
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_0 : ∀ e∈thirdBlock0_0, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_0,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_1 : ∀ e∈thirdBlock0_1, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_1,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_2 : ∀ e∈thirdBlock0_2, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_2,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_3 : ∀ e∈thirdBlock0_3, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_3,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_4 : ∀ e∈thirdBlock0_4, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_4,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_5 : ∀ e∈thirdBlock0_5, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_5,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_6 : ∀ e∈thirdBlock0_6, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_6,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_7 : ∀ e∈thirdBlock0_7, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_7,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_8 : ∀ e∈thirdBlock0_8, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_8,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_9 : ∀ e∈thirdBlock0_9, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_9,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_10 : ∀ e∈thirdBlock0_10, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_10,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_11 : ∀ e∈thirdBlock0_11, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_11,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_12 : ∀ e∈thirdBlock0_12, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_12,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_13 : ∀ e∈thirdBlock0_13, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_13,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_14 : ∀ e∈thirdBlock0_14, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_14,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_15 : ∀ e∈thirdBlock0_15, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_15,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock0_16 : ∀ e∈thirdBlock0_16, rangeTicket data0 e=true := by
  intro e h
  simp only [thirdBlock0_16,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
theorem third_done0 : ∀ e∈thirdTickets0, rangeTicket data0 e=true := by
  simp only [thirdTickets0,List.forall_mem_append]
  exact ⟨pass_thirdBlock0_0,pass_thirdBlock0_1,pass_thirdBlock0_2,pass_thirdBlock0_3,pass_thirdBlock0_4,pass_thirdBlock0_5,pass_thirdBlock0_6,pass_thirdBlock0_7,pass_thirdBlock0_8,pass_thirdBlock0_9,pass_thirdBlock0_10,pass_thirdBlock0_11,pass_thirdBlock0_12,pass_thirdBlock0_13,pass_thirdBlock0_14,pass_thirdBlock0_15,pass_thirdBlock0_16⟩
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_0 : ∀ e∈thirdBlock1_0, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_0,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_1 : ∀ e∈thirdBlock1_1, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_1,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_2 : ∀ e∈thirdBlock1_2, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_2,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_3 : ∀ e∈thirdBlock1_3, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_3,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_4 : ∀ e∈thirdBlock1_4, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_4,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_5 : ∀ e∈thirdBlock1_5, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_5,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_6 : ∀ e∈thirdBlock1_6, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_6,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_7 : ∀ e∈thirdBlock1_7, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_7,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_8 : ∀ e∈thirdBlock1_8, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_8,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_9 : ∀ e∈thirdBlock1_9, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_9,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_10 : ∀ e∈thirdBlock1_10, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_10,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_11 : ∀ e∈thirdBlock1_11, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_11,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem pass_thirdBlock1_12 : ∀ e∈thirdBlock1_12, rangeTicket data1 e=true := by
  intro e h
  simp only [thirdBlock1_12,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold rangeTicket
  all_goals conv in prefixState _ _ _ => cbv
  all_goals decide +kernel
theorem third_done1 : ∀ e∈thirdTickets1, rangeTicket data1 e=true := by
  simp only [thirdTickets1,List.forall_mem_append]
  exact ⟨pass_thirdBlock1_0,pass_thirdBlock1_1,pass_thirdBlock1_2,pass_thirdBlock1_3,pass_thirdBlock1_4,pass_thirdBlock1_5,pass_thirdBlock1_6,pass_thirdBlock1_7,pass_thirdBlock1_8,pass_thirdBlock1_9,pass_thirdBlock1_10,pass_thirdBlock1_11,pass_thirdBlock1_12⟩
end L652.GroupProjection
namespace L652.GroupProjection
def naiveScore (d : Data) (second : Bool) (hit : Nat) : List Col → Nat
  | [] => rawCost d hit
  | x :: xs => min (naiveScore d second hit xs)
      (1 + naiveScore d second (hit ||| x.separates second) xs)
theorem extraCost_eq_min (d : Data) (second : Bool) (hit limit : Nat) (opts : List Col) :
    extraCost d second hit limit opts = min limit (naiveScore d second hit opts) := by
  induction opts generalizing hit limit with
  | nil => rfl
  | cons x xs ih =>
    simp only [extraCost,naiveScore,ih]
    split <;> omega
def sinkHit (second : Bool) (sinks : List Col) : Nat :=
  sinks.foldl (fun h c => h ||| c.separates second) 0
private theorem zz72n0 (base x y cap : Nat) :
    (if base > cap then false else
      let rest := cap-base
      let a := min (rest+1) x
      if a > rest then false else
        let room := rest-a
        decide (min (room+1) y ≤ room)) = true ↔ base+x+y ≤ cap := by
  split <;> rename_i h
  · simp only [Bool.false_eq_true,false_iff]
    omega
  · dsimp only
    split <;> rename_i h'
    · simp only [Bool.false_eq_true,false_iff]
      omega
    · simp only [decide_eq_true_eq]
      omega
theorem canContinue_iff_sum (d : Data) (sinks opts : List Col) (allowance : Nat) :
    canContinue d sinks opts allowance = true ↔
      2 * (sinks.length - 1) + naiveScore d false (sinkHit false sinks) opts +
      naiveScore d true (sinkHit true sinks) opts ≤ allowance := by
  unfold canContinue
  simp only [extraCost_eq_min]
  exact zz72n0 (2*(sinks.length-1)) _ _ _
theorem canContinue_cons_iff (d : Data) (fresh : Col) (sinks opts : List Col) (allowance : Nat) :
    canContinue d (fresh::sinks) opts allowance = true ↔
      2*sinks.length + naiveScore d false (sinkHit false (fresh::sinks)) opts +
        naiveScore d true (sinkHit true (fresh::sinks)) opts ≤ allowance := by
  simpa using canContinue_iff_sum d (fresh::sinks) opts allowance
end L652.GroupProjection
namespace L652.Lanes
abbrev base := 18446744073709551616
def pack (xs : List α) (f : α → Nat) : Nat := xs.foldr (fun x p => 2^64*p+f x) 0
abbrev ones (xs : List α) := pack xs (fun _ => 1)
abbrev Small (xs : List α) (f : α → Nat) := ∀ x ∈ xs, f x < 2^64
theorem congr {xs : List α} {f g : α → Nat} (h : ∀ x ∈ xs, f x = g x) : pack xs f = pack xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [pack,List.foldr_cons]; rw [h _ (by simp)]; congr 2; exact ih fun y hy => h y (by simp [hy])
theorem zero (xs : List α) : pack xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 2^64*pack xs (fun _ => 0)+0 = 0
    simp only [ih,Nat.mul_zero,Nat.zero_add]
theorem add (xs : List α) (f g : α → Nat) : pack xs f + pack xs g = pack xs (fun x => f x + g x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (2^64*pack xs f + f x) + (2^64*pack xs g + g x) = 2^64*pack xs _ + (f x+g x)
    rw [←ih, Nat.mul_add]; omega
theorem mul (xs : List α) (f : α → Nat) (c : Nat) : c * pack xs f = pack xs (fun x => c * f x) := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih =>
    change c*(2^64*pack xs f+f x)=2^64*pack xs _ + c*f x
    rw [Nat.mul_add,←Nat.mul_assoc,Nat.mul_comm c (2^64),Nat.mul_assoc,ih]
theorem const (xs : List α) (c : Nat) : c*ones xs = pack xs (fun _ => c) := by simpa using mul xs (fun _ => 1) c
theorem sub {xs : List α} {f g : α → Nat} (h : ∀ x∈xs,g x ≤ f x) : pack xs f - pack xs g = pack xs (fun x => f x - g x) := by
  have eq : pack xs (fun x => f x - g x) + pack xs g = pack xs f := by
    rw [add]; exact congr fun x hx => Nat.sub_add_cancel (h x hx)
  omega
theorem bit (xs : List α) (f : α → Nat) (hf : Small xs f) (i j : Nat) (hj : j<64) :
    (pack xs f).testBit (64*i+j) = if h : i<xs.length then (f xs[i]).testBit j else false := by
  induction xs generalizing i with
  | nil => simp [pack]
  | cons x xs ih =>
    change (2^64*pack xs f+f x).testBit (64*i+j) = _
    rw [Nat.testBit_two_pow_mul_add _ (hf _ (by simp))]
    cases i with
    | zero => simp [hj]
    | succ i =>
      have hh : ¬ 64*(i+1)+j < 64 := by omega
      have h' : 64*(i+1)+j-64 = 64*i+j := by omega
      have hl : Small xs f := fun y hy => hf y (by simp [hy])
      simp only [hh,decide_false,Bool.false_and,Nat.le_of_not_gt hh,decide_true,Bool.true_and,
        Bool.false_or,h',List.length_cons,Nat.add_lt_add_iff_right,List.getElem_cons_succ]
      exact ih hl i
private theorem zz73n0 (i : Nat) : 64*(i/64)+i % 64 = i := by omega
theorem and {xs : List α} {f g : α → Nat} (hf : Small xs f) (hg : Small xs g) :
    pack xs f &&& pack xs g = pack xs (fun x => f x &&& g x) := by
  apply Nat.eq_of_testBit_eq; intro t
  let i := t/64; let j := t % 64
  have e : t = 64*i+j := (zz73n0 t).symm
  rw [e,Nat.testBit_and,bit xs f hf,bit xs g hg,bit xs _ (fun x hx => Nat.lt_of_le_of_lt Nat.and_le_left (hf x hx))]
  · split <;> simp [Nat.testBit_and]
  all_goals exact Nat.mod_lt _ (by decide)
theorem or {xs : List α} {f g : α → Nat} (hf : Small xs f) (hg : Small xs g) :
    pack xs f ||| pack xs g = pack xs (fun x => f x ||| g x) := by
  apply Nat.eq_of_testBit_eq; intro t
  let i := t/64; let j := t % 64
  have e : t = 64*i+j := (zz73n0 t).symm
  rw [e,Nat.testBit_or,bit xs f hf,bit xs g hg,bit xs _ (fun x hx => Nat.or_lt_two_pow (hf x hx) (hg x hx))]
  · split <;> simp [Nat.testBit_or]
  all_goals exact Nat.mod_lt _ (by decide)
theorem xor {xs : List α} {f g : α → Nat} (hf : Small xs f) (hg : Small xs g) :
    pack xs f ^^^ pack xs g = pack xs (fun x => f x ^^^ g x) := by
  apply Nat.eq_of_testBit_eq; intro t
  let i := t/64; let j := t % 64
  have e : t = 64*i+j := (zz73n0 t).symm
  rw [e,Nat.testBit_xor,bit xs f hf,bit xs g hg,bit xs _ (fun x hx => Nat.xor_lt_two_pow (hf x hx) (hg x hx))]
  · split <;> simp [Nat.testBit_xor]
  all_goals exact Nat.mod_lt _ (by decide)
theorem shiftMask {xs : List α} {f : α → Nat} (hf : Small xs f) (k mask : Nat)
    (hk : k ≤ 64) (hm : mask < 2^(64-k)) :
    ((pack xs f >>> k) &&& (mask*ones xs)) = pack xs (fun x => (f x >>> k) &&& mask) := by
  have smallM : mask < 2^64 := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
  rw [const]
  apply Nat.eq_of_testBit_eq; intro t
  let i := t/64; let j := t % 64
  have hj : j < 64 := Nat.mod_lt _ (by decide)
  have e : t = 64*i+j := (zz73n0 t).symm
  rw [e,Nat.testBit_and,Nat.testBit_shiftRight,bit xs _ (fun _ _ => smallM) i j hj,
    bit xs _ (fun _ _ => Nat.lt_of_le_of_lt Nat.and_le_right smallM) i j hj]
  by_cases hpos : j+k < 64
  · rw [show k+(64*i+j) = 64*i+(j+k) by omega,bit xs f hf i (j+k) hpos]
    split <;> simp [Nat.testBit_and,Nat.testBit_shiftRight,Nat.add_comm]
  · have notBit : mask.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))
    split <;> simp [Nat.testBit_and,notBit]
theorem packFold {xs : List α} {f : α → Nat} (hf : Small xs f) :
    xs.foldr (fun x n => f x ||| (n <<< 64)) 0 = pack xs f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f x ||| ((_ : Nat) <<< 64) = 2^64*pack xs f+f x
    rw [ih (fun y hy => hf y (by simp [hy])),Nat.or_comm,← Nat.shiftLeft_add_eq_or_of_lt (hf x (by simp)),Nat.shiftLeft_eq,Nat.mul_comm]
end L652.Lanes
namespace L652.GroupProjection
open L652.Lanes
private theorem zz74n0 (xs : List α) (c : Nat) (h : c < 2^64) : Small xs (fun _ => c) := fun _ _ => h
private theorem zz74n1 {xs : List α} {f g : α → Nat} (hf : Small xs f) (hg : Small xs g) :
    Small xs (fun x => f x ^^^ g x) := fun x h => Nat.xor_lt_two_pow (hf x h) (hg x h)
private theorem zz74n2 {xs : List α} {f : α → Nat} (g : α → Nat) (hf : Small xs f) :
    Small xs (fun x => f x &&& g x) := fun x h => Nat.lt_of_le_of_lt Nat.and_le_left (hf x h)
theorem allRaws_packed {d : Data} (hd : d.valid < 2^48) (xs : List α) (f : α → Nat)
    (hf : Small xs f) : allRaws d (Lanes.ones xs) (Lanes.pack xs f) = Lanes.pack xs (fun x => rawCost d (f x)) := by
  let full := 18446744073709551615
  let low := 17024696172015
  let marker := 18159675916816
  let block := 17180393488
  let z := fun x => d.valid &&& (full ^^^ f x)
  let u := fun x => (z x + low) &&& marker
  let a := fun x => u x &&& block
  let b := fun x => (u x >>> 5) &&& block
  let p := fun x => (u x >>> 10) &&& block
  let c := fun x => a x + b x + (p x &&& (full ^^^ (a x ||| b x)))
  have D := zz74n0 xs d.valid (Nat.lt_trans hd (by decide))
  have F := zz74n0 xs full (by decide)
  have L := zz74n0 xs low (by decide)
  have B := zz74n0 xs block (by decide)
  have M := zz74n0 xs marker (by decide)
  have Z : (d.valid*Lanes.ones xs &&& ((full*Lanes.ones xs) ^^^ Lanes.pack xs f)) = Lanes.pack xs z := by
    rw [Lanes.const,Lanes.const,Lanes.xor F hf,Lanes.and D (zz74n1 F hf)]
  have boundZ (x : α) : z x ≤ d.valid := Nat.and_le_left
  have SL : Small xs (fun x => z x + low) := fun x _ =>
    Nat.lt_trans (Nat.add_lt_add_right (Nat.lt_of_le_of_lt (boundZ x) hd) low) (by decide)
  have U : (Lanes.pack xs z + low*Lanes.ones xs) &&& (marker*Lanes.ones xs) = Lanes.pack xs u := by
    rw [Lanes.const,Lanes.const,Lanes.add,Lanes.and SL M]
  have SU : Small xs u := fun _ _ => Nat.lt_of_le_of_lt Nat.and_le_right (by decide : marker < 2^64)
  have A : Lanes.pack xs u &&& (block*Lanes.ones xs) = Lanes.pack xs a := by rw [Lanes.const,Lanes.and SU B]
  have B' : (Lanes.pack xs u >>> 5) &&& (block*Lanes.ones xs) = Lanes.pack xs b := shiftMask SU 5 block (by decide) (by decide)
  have P : (Lanes.pack xs u >>> 10) &&& (block*Lanes.ones xs) = Lanes.pack xs p := shiftMask SU 10 block (by decide) (by decide)
  have ba (x : α) : a x ≤ block := Nat.and_le_right
  have bb (x : α) : b x ≤ block := Nat.and_le_right
  have bp (x : α) : p x ≤ block := Nat.and_le_right
  have SA : Small xs a := fun x _ => Nat.lt_of_le_of_lt (ba x) (by decide)
  have SB : Small xs b := fun x _ => Nat.lt_of_le_of_lt (bb x) (by decide)
  have SP : Small xs p := fun x _ => Nat.lt_of_le_of_lt (bp x) (by decide)
  have SAB : Small xs (fun x => a x ||| b x) := fun x h => Nat.or_lt_two_pow (SA x h) (SB x h)
  have C : Lanes.pack xs a + Lanes.pack xs b + (Lanes.pack xs p &&& ((full*Lanes.ones xs) ^^^ (Lanes.pack xs a ||| Lanes.pack xs b))) =
      Lanes.pack xs c := by rw [Lanes.const,Lanes.or SA SB,Lanes.xor F SAB,Lanes.and SP (zz74n1 F SAB),Lanes.add,Lanes.add]
  have SC : Small xs c := fun x _ => by
    have h : p x &&& (full ^^^ (a x ||| b x)) ≤ p x := Nat.and_le_left
    exact Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add (ba x) (bb x)) (Nat.le_trans h (bp x))) (by decide)
  simp only [allRaws]
  change _ = Lanes.pack xs (fun x => rawCost d (f x))
  rw [Z,U,A,B',P,C,shiftMask SC 4 3 (by decide) (by decide),
    shiftMask SC 19 3 (by decide) (by decide),shiftMask SC 34 3 (by decide) (by decide),Lanes.add,Lanes.add]
  exact Lanes.congr fun x _ => (rawCost_postLower d (f x)).symm
private theorem zz74n3 : ∀ a b : Fin 32, let c := ((32+a.val)-b.val) &&& 32
    c = 32*(decide (b.val ≤ a.val)).toNat ∧
    let mask := c - (decide (b.val ≤ a.val)).toNat
    (a.val &&& (31 ^^^ mask)) ||| (b.val &&& mask) = min a.val b.val := by decide +kernel
theorem laneMin_packed (xs : List α) (f g : α → Nat) (hf : ∀ x∈xs, f x < 32) (hg : ∀ x∈xs, g x < 32) :
    laneMin (Lanes.ones xs) (Lanes.pack xs f) (Lanes.pack xs g) = Lanes.pack xs (fun x => min (f x) (g x)) := by
  let c := fun x => ((32+f x)-g x) &&& 32
  let u := fun x => (decide (g x ≤ f x)).toNat
  let m := fun x => c x - u x
  have facts (x : α) (hx : x∈xs) := zz74n3 ⟨f x,hf x hx⟩ ⟨g x,hg x hx⟩
  have F : Small xs f := fun x hx => by have := hf x hx; omega
  have G : Small xs g := fun x hx => by have := hg x hx; omega
  have Q : Small xs (fun x => 32+f x-g x) := fun x hx => by change 32+f x-g x < 18446744073709551616; have := hf x hx; omega
  have C : ((32*Lanes.ones xs + Lanes.pack xs f)-Lanes.pack xs g) &&& (32*Lanes.ones xs) = Lanes.pack xs c := by
    rw [Lanes.const,Lanes.add,Lanes.sub (fun x hx => by have := hg x hx; omega),Lanes.and Q (zz74n0 xs 32 (by decide))]
  have S : Lanes.pack xs c >>> 5 = Lanes.pack xs u := by
    have e : Lanes.pack xs c = 32*Lanes.pack xs u := by
      rw [mul]; exact Lanes.congr fun x hx => (facts x hx).1
    rw [e,Nat.shiftRight_eq_div_pow]; omega
  have M : Lanes.pack xs c - Lanes.pack xs u = Lanes.pack xs m := by
    apply Lanes.sub; intro x hx; have h : c x = 32*u x := (facts x hx).1; omega
  have SM : Small xs m := fun x _ => by
    have h : c x ≤ 32 := Nat.and_le_right; dsimp only [m]; omega
  simp only [laneMin]
  rw [C,S,M,Lanes.const,Lanes.xor (zz74n0 xs 31 (by decide)) SM,Lanes.and F (zz74n1 (zz74n0 xs 31 (by decide)) SM),
    Lanes.and G SM,Lanes.or (zz74n2 _ F) (zz74n2 _ G)]
  exact Lanes.congr fun x hx => (facts x hx).2
end L652.GroupProjection
namespace L652.GroupProjection
open L652.Lanes
theorem naive_small (d : Data) (second : Bool) (hit : Nat) (opts : List Col) :
    naiveScore d second hit opts ≤ 7 := by
  induction opts generalizing hit with
  | nil => exact rawCost_le_seven _ _
  | cons c cs ih => exact Nat.le_trans (Nat.min_le_left ..) (ih hit)
theorem scores_packed {d : Data} (hd : d.valid < 2^48) (xs : List α) (f : α → Nat)
    (hf : Small xs f) (second : Bool) (opts : List Col)
    (hopt : ∀ c∈opts, c.separates second < 2^64) :
    allScores d (Lanes.ones xs) second (Lanes.pack xs f) opts =
      Lanes.pack xs (fun x => naiveScore d second (f x) opts) := by
  induction opts generalizing f with
  | nil => exact allRaws_packed hd xs f hf
  | cons c cs ih =>
    have csmall := hopt c (by simp)
    have rest : ∀ u∈cs, u.separates second < 2^64 := fun u hu => hopt u (by simp [hu])
    have ext : Small xs (fun x => f x ||| c.separates second) :=
      fun x hx => Nat.or_lt_two_pow (hf x hx) csmall
    simp only [allScores,naiveScore]
    rw [Lanes.const,Lanes.or hf (fun _ _ => csmall),ih _ hf rest,ih _ ext rest]
    change laneMin (Lanes.ones xs) (Lanes.pack xs _) (Lanes.pack xs (fun _ => 1) + Lanes.pack xs _) = _
    rw [Lanes.add]
    apply laneMin_packed
    · exact fun x _ => Nat.lt_of_le_of_lt (naive_small ..) (by decide)
    · intro x _; exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (naive_small ..) 1) (by decide)
private theorem zz75n0 : ∀ x : Fin 16, ∀ r : Fin 32,
    (x.val+(31-r.val)) &&& 32 = if r.val < x.val then 32 else 0 := by decide +kernel
theorem fail_packed {xs : List α} (f : α → Nat) (hf : ∀ x∈xs,f x < 16) (r : Nat) (hr : r < 32) :
    allFail (Lanes.ones xs) (Lanes.pack xs f) r = Lanes.pack xs (fun x => if r < f x then 32 else 0) := by
  have small : Small xs (fun x => f x + (31-r)) := fun x hx => by
    change f x+(31-r) < 18446744073709551616; have H := hf x hx; omega
  simp only [allFail]
  rw [Lanes.const,Lanes.add,Lanes.const,Lanes.and small (fun _ _ => by decide)]
  exact Lanes.congr fun x hx => zz75n0 ⟨f x,hf x hx⟩ ⟨r,hr⟩
theorem fail_bit {xs : List α} (f : α → Nat) (i : Nat) (hi : i<xs.length) (r : Nat) :
    (Lanes.pack xs (fun x => if r < f x then 32 else 0)).testBit (64*i+5) = decide (r < f xs[i]) := by
  rw [bit]; simp only [hi,dif_pos]
  · split <;> simp_all <;> decide
  · intro x _; change (if r < f x then 32 else 0) < 2^64; split <;> decide
  · decide
theorem ones_bit {xs : List α} (i : Nat) (hi : i<xs.length) :
    (32*Lanes.ones xs).testBit (64*i+5) = true := by
  rw [Lanes.const,bit xs _ (fun _ _ => by decide) i 5 (by decide)]
  simp [hi] <;> decide
private theorem zz75n1 (second : Bool) (xs : List Col) (w : Nat) :
    xs.foldl (fun h c => h ||| c.separates second) w = w ||| sinkHit second xs := by
  unfold sinkHit
  induction xs generalizing w with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons,Nat.zero_or]; rw [ih,ih (c.separates second),Nat.or_assoc]
theorem hit_cons (second : Bool) (c : Col) (xs : List Col) :
    sinkHit second (c::xs) = sinkHit second xs ||| c.separates second := by
  simp only [sinkHit,List.foldl_cons,Nat.zero_or]
  rw [zz75n1,Nat.or_comm]; rfl
theorem hit_small (second : Bool) (xs : List Col) (h : ∀ c∈xs,c.separates second < 2^64) :
    sinkHit second xs < 2^64 := by
  induction xs with
  | nil => change 0 < 2^64; decide
  | cons c cs ih =>
    rw [hit_cons]
    exact Nat.or_lt_two_pow (ih fun u hu => h u (by simp [hu])) (h c (by simp))
end L652.GroupProjection
namespace L652.GroupProjection
def Col.Bounded (c : Col) : Prop :=
  c.full < 2^64 ∧ c.p1 < 2^64 ∧ c.n1 < 2^64 ∧ c.p2 < 2^64 ∧ c.n2 < 2^64
theorem Col.Bounded.separation {c : Col} (ok : c.Bounded) (second : Bool) :
    c.separates second < 2^64 := by
  cases second
  · exact Nat.xor_lt_two_pow ok.2.1 ok.2.2.1
  · exact Nat.xor_lt_two_pow ok.2.2.2.1 ok.2.2.2.2
private theorem zz76n0 {c : Col} {dom : Nat} (ok : c.Bounded) (small : dom < 2^64) :
    (c.neg dom).Bounded := by
  have m : (0xffffffffffffffff : Nat) < 2^64 := by decide
  exact ⟨Nat.xor_lt_two_pow small ok.1,Nat.xor_lt_two_pow m ok.2.1,
    Nat.xor_lt_two_pow m ok.2.2.1,Nat.xor_lt_two_pow m ok.2.2.2.1,
    Nat.xor_lt_two_pow m ok.2.2.2.2⟩
private theorem zz76n1 {x y : Col} (a : x.Bounded) (h : y.Bounded) (join : Bool) :
    (x.combine join y).Bounded := by
  cases join
  · exact ⟨Nat.and_lt_two_pow _ h.1,Nat.and_lt_two_pow _ h.2.1,Nat.and_lt_two_pow _ h.2.2.1,
      Nat.and_lt_two_pow _ h.2.2.2.1,Nat.and_lt_two_pow _ h.2.2.2.2⟩
  · exact ⟨Nat.or_lt_two_pow a.1 h.1,Nat.or_lt_two_pow a.2.1 h.2.1,
      Nat.or_lt_two_pow a.2.2.1 h.2.2.1,Nat.or_lt_two_pow a.2.2.2.1 h.2.2.2.1,
      Nat.or_lt_two_pow a.2.2.2.2 h.2.2.2.2⟩
private theorem zz76n2 {l : List Col} {c : Col} {i : Nat} (h : (c,i) ∈ l.zipIdx) : c ∈ l := by
  have k : c ∈ l.zipIdx.map Prod.fst := List.mem_map.mpr ⟨(c,i),h,rfl⟩
  simpa only [List.zipIdx_map_fst] using k
theorem trial_bounded_of_wires {d : Data} {s : State} {init : Bool} {t : Trial}
    (dom : d.domain < 2^64) (wires : ∀ c ∈ s.wires, c.Bounded) (mem : t ∈ trials d s init) :
    t.value.Bounded := by
  unfold trials at mem
  obtain ⟨⟨y,b⟩,hy,lower⟩ := List.mem_flatMap.mp mem
  dsimp only at lower
  split at lower
  · simp at lower
  obtain ⟨⟨x,a⟩,hx,inner⟩ := List.mem_flatMap.mp lower
  dsimp only at inner
  split at inner
  · simp at inner
  have bx := wires x (List.mem_of_mem_take (zz76n2 hx))
  have by' := wires y (zz76n2 hy)
  have law (op : Nat) (z : Col) (hz : z.Bounded)
      (hm : t ∈ (if key a b op < s.last || z.full==0 || z.full==d.domain ||
          s.wires.any (fun c => c.full==z.full) then [] else
          [⟨a,b,key a b op,z,eatenMask s.sunk x y⟩] : List Trial)) : t.value.Bounded := by
    split at hm
    · simp at hm
    · obtain rfl := List.mem_singleton.mp hm
      exact hz
  split at inner
  · exact law _ _ (zz76n0 bx dom) inner
  · rcases List.mem_append.mp inner with one | two
    · exact law _ _ (zz76n1 bx by' false) one
    · exact law _ _ (zz76n1 bx by' true) two
private theorem zz76n3 (s : List Col) (mask : Nat) (x : Bool) :
    maskKeep s mask x ⊆ s := by
  intro c hc
  obtain ⟨⟨y,i⟩,h,rfl⟩ := List.mem_map.mp hc
  exact zz76n2 (List.mem_filter.mp h).1
theorem reach_bounds {b n s} (ok : Reach (dataFor b) n s) :
    (∀ c ∈ s.wires,c.Bounded) ∧ (∀ c ∈ s.sunk,c.Bounded) ∧ (∀ c ∈ s.internal,c.Bounded) := by
  induction ok with
  | root =>
    refine ⟨?_,by simp,by simp⟩
    have finite : ∀ d : Bool, (dataFor d).raw.all (fun c =>
        c.full<2^64 && c.p1<2^64 && c.n1<2^64 && c.p2<2^64 && c.n2<2^64) = true := by decide +kernel
    intro c hc
    have h := List.all_eq_true.mp (finite b) c hc
    simpa [Col.Bounded,and_assoc] using h
  | @step n s init t old mem ih =>
    obtain ⟨ws,sk,inter⟩ := ih
    have z := trial_bounded_of_wires (by rw [domainFor]; exact BitVec.isLt _) ws mem
    simp only [trialAfter,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    refine ⟨?_,?_,?_⟩
    · rintro c (h|rfl)
      · exact ws c h
      · exact z
    · rintro c (rfl|h)
      · exact z
      · exact sk c (zz76n3 _ _ _ h)
    · rintro c (h|h)
      · exact sk c (zz76n3 _ _ _ h)
      · exact inter c h
theorem reach_trial_bounded {b n s init t} (ok : Reach (dataFor b) n s)
    (mem : t ∈ trials (dataFor b) s init) : t.value.Bounded :=
  trial_bounded_of_wires (by rw [domainFor]; exact BitVec.isLt _) (reach_bounds ok).1 mem
end L652.GroupProjection
namespace L652.GroupProjection
open L652.Lanes
private def zz77n0 (d : Data) (ts : List Trial) (rest opts : List Col) (second : Bool) :=
  let rep := ts.foldr (fun _ v => 1+(v <<< 64)) 0
  let old := rest.foldl (fun h c => h ||| c.separates second) 0
  let fresh := ts.foldr (fun t v => t.value.separates second ||| (v <<< 64)) 0
  allScores d rep second ((old*rep) ||| fresh) opts
private def zz77n1 (d : Data) (rest opts : List Col) (second : Bool) (t : Trial) :=
  naiveScore d second (sinkHit second (t.value::rest)) opts
private def zz77n2 (d : Data) (rest opts : List Col) (t : Trial) :=
  zz77n1 d rest opts false t + zz77n1 d rest opts true t
private theorem zz77n3 (ts : List Trial) : ts.foldr (fun _ v => 1+(v <<< 64)) 0 = Lanes.ones ts := by
  induction ts with
  | nil => simp only [Lanes.ones,Lanes.pack,List.foldr_nil]
  | cons t ts ih =>
    simp only [List.foldr_cons]
    rw [ih,Nat.shiftLeft_eq]
    change 1+Lanes.ones ts * 2^64 = 2^64*Lanes.ones ts+1
    rw [Nat.mul_comm,Nat.add_comm]
private theorem zz77n4 {d : Data} (hd : d.valid < 2^48) {ts : List Trial} (rest opts : List Col)
    (bd : ∀ t∈ts, t.value.Bounded) (br : ∀ x∈rest,x.Bounded) (bo : ∀ x∈opts,x.Bounded)
    (sec : Bool) : zz77n0 d ts rest opts sec = Lanes.pack ts (zz77n1 d rest opts sec) := by
  let f := fun t : Trial => t.value.separates sec
  have F : Small ts f := fun t ht => (bd t ht).separation _
  have R := hit_small sec rest fun x hx => (br x hx).separation _
  have OR : Small ts (fun t => sinkHit sec rest ||| f t) :=
    fun t ht => Nat.or_lt_two_pow R (F t ht)
  unfold zz77n0
  rw [zz77n3,packFold F]
  change allScores d (Lanes.ones ts) sec ((sinkHit sec rest * Lanes.ones ts) ||| Lanes.pack ts f) opts = _
  rw [Lanes.const,Lanes.or (fun _ _ => R) F,scores_packed hd _ _ OR sec opts (fun x h => (bo x h).separation _)]
  apply Lanes.congr; intro t ht; unfold zz77n1; rw [hit_cons]
private theorem zz77n5 {ts : List Trial} (f : Trial → Nat) (small : ∀ t∈ts,f t<16)
    (r : Nat) (hr : r<32) (i : Nat) (hi : i<ts.length) :
    (allFail (Lanes.ones ts) (Lanes.pack ts f) r).testBit (64*i+5) = decide (r<f ts[i]) := by
  rw [fail_packed f small r hr,fail_bit f i hi]
private theorem zz77n6 {ts : List Trial} {f : Trial → Nat} (small : ∀ t∈ts,f t<16)
    {base n fuel : Nat} (cap : n+fuel≤9) {next : Trial → Bool} {t : Trial} (ht : t∈ts)
    (ok :
      (if base>10+fuel-n then true else
        if base≤10-n && allFail (Lanes.ones ts) (Lanes.pack ts f) (10-n-base) != 32*Lanes.ones ts then false else
        if fuel==0 then true else
        let exclude := allFail (Lanes.ones ts) (Lanes.pack ts f) (10+fuel-n-base)
        if exclude == 32*Lanes.ones ts then true else
        ts.zipIdx.all fun (t,i) => exclude.testBit (64*i+5) || next t) = true) :
    10-n < base+f t ∧ (0<fuel → base+f t ≤ 10+fuel-n → next t = true) := by
  obtain ⟨i,hi,ei⟩ := List.getElem_of_mem ht
  have bad (r : Nat) (hr : r<32) (eq : allFail (Lanes.ones ts) (Lanes.pack ts f) r = 32*Lanes.ones ts) : r < f t := by
    have a := zz77n5 f small r hr i hi
    rw [eq,ones_bit i hi,ei] at a
    exact of_decide_eq_true a.symm
  by_cases too : base > 10+fuel-n
  · exact ⟨by omega,by omega⟩
  simp only [too,ite_false] at ok
  have closed : 10-n < base+f t := by
    by_cases lo : base ≤ 10-n
    · have ex : allFail (Lanes.ones ts) (Lanes.pack ts f) (10-n-base) = 32*Lanes.ones ts := by
        by_contra he
        simp [lo,he] at ok
      have := bad _ (by omega) ex; omega
    · omega
  refine ⟨closed, ?_⟩
  intro positive fits
  have pre : (decide (base ≤ 10-n) && (allFail (Lanes.ones ts) (Lanes.pack ts f) (10-n-base) != 32*Lanes.ones ts)) = false := by
    split at ok <;> simp_all
  simp only [pre,Bool.false_eq_true,ite_false,beq_iff_eq] at ok
  rw [if_neg (by omega : ¬fuel = 0)] at ok
  try dsimp only at ok
  split at ok
  · rename_i ex; have := bad (10+fuel-n-base) (by omega) (by simpa using ex); omega
  · have bit := zz77n5 f small (10+fuel-n-base) (by omega) i hi
    have ix : (t,i) ∈ ts.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hi,ei])
    have accept := List.all_eq_true.mp ok (t,i) ix
    rw [ei] at bit
    have no : ¬(10+fuel-n-base < f t) := by omega
    simpa [bit,no] using accept
private theorem zz77n7 (b sec : Bool) (h : Nat) (opts : List Col) :
    rawCost (dataFor b) (h ||| sinkHit sec opts) ≤ naiveScore (dataFor b) sec h opts := by
  induction opts generalizing h with
  | nil => simp [sinkHit,naiveScore]
  | cons c cs ih =>
    simp only [hit_cons,naiveScore]
    have movable : h ||| (sinkHit sec cs ||| c.separates sec) =
        (h ||| c.separates sec) ||| sinkHit sec cs := by ac_rfl
    have lo : rawCost (dataFor b) (h ||| (sinkHit sec cs ||| c.separates sec)) ≤
        rawCost (dataFor b) (h ||| sinkHit sec cs) := by
      rw [←Nat.or_assoc]; exact rawCost_more_hits b _ _
    have a := Nat.le_trans lo (ih h)
    rw [movable] at a ⊢
    have c' := ih (h ||| c.separates sec)
    omega
private def zz77n8 (d : Data) (h : Nat) (sec : Bool) (opts : List Col) : Nat :=
  min (rawCost d h) (1+rawCost d (h ||| sinkHit sec opts))
private theorem zz77n9 (b sec : Bool) (h : Nat) (opts : List Col) :
    zz77n8 (dataFor b) h sec opts ≤ naiveScore (dataFor b) sec h opts := by
  induction opts generalizing h with
  | nil => exact Nat.min_le_left ..
  | cons c cs ih =>
    simp only [zz77n8,hit_cons,naiveScore]
    have movable : h ||| (sinkHit sec cs ||| c.separates sec) =
        (h ||| c.separates sec) ||| sinkHit sec cs := by ac_rfl
    have lo : rawCost (dataFor b) (h ||| (sinkHit sec cs ||| c.separates sec)) ≤
        rawCost (dataFor b) (h ||| sinkHit sec cs) := by
      rw [←Nat.or_assoc]; exact rawCost_more_hits b _ _
    rw [movable] at lo ⊢
    have a := ih h
    change min _ (1+rawCost (dataFor b) (h ||| sinkHit sec cs)) ≤ _ at a
    have c' := zz77n7 b sec (h ||| c.separates sec) cs
    omega
private theorem zz77n10 (d : Data) (h : Nat) (sec : Bool) (opts : List Col) :
    zz77n8 d h sec opts ≤ 7 := Nat.le_trans (Nat.min_le_left ..) (rawCost_le_seven ..)
private theorem zz77n11 {d : Data} (hd : d.valid < 2^48) {ts : List Trial} (rest opts : List Col)
    (bd : ∀ t∈ts,t.value.Bounded) (br : ∀ x∈rest,x.Bounded) (bo : ∀ x∈opts,x.Bounded)
    (sec : Bool) :
    coarseSide d (Lanes.ones ts) ts rest opts sec =
    Lanes.pack ts (fun t => zz77n8 d (sinkHit sec (t.value::rest)) sec opts) := by
  let f := fun t : Trial => t.value.separates sec
  let hit := fun t : Trial => sinkHit sec rest ||| f t
  have F : Small ts f := fun t ht => (bd t ht).separation _
  have R := hit_small sec rest fun x hx => (br x hx).separation _
  have H : Small ts hit := fun t ht => Nat.or_lt_two_pow R (F t ht)
  have O := hit_small sec opts fun x hx => (bo x hx).separation _
  have J : Small ts (fun t => hit t ||| sinkHit sec opts) := fun t ht => Nat.or_lt_two_pow (H t ht) O
  have packed : coarseHit (Lanes.ones ts) ts rest sec = Lanes.pack ts hit := by
    unfold coarseHit; rw [packFold F]
    change (sinkHit sec rest * Lanes.ones ts) ||| _ = _
    rw [Lanes.const,Lanes.or (fun _ _ => R) F]
  unfold coarseSide
  rw [packed]
  change laneMin (Lanes.ones ts) (allRaws d (Lanes.ones ts) (Lanes.pack ts hit))
    (Lanes.pack ts (fun _ => 1) + allRaws d (Lanes.ones ts)
      (Lanes.pack ts hit ||| (sinkHit sec opts * Lanes.ones ts))) = _
  rw [Lanes.const,Lanes.or H (fun _ _ => O),allRaws_packed hd _ _ H,allRaws_packed hd _ _ J,Lanes.add,
    laneMin_packed _ _ _ (fun _ _ => Nat.lt_of_le_of_lt (rawCost_le_seven ..) (by decide))
      (fun _ _ => Nat.lt_of_le_of_lt (Nat.add_le_add_left (rawCost_le_seven ..) 1) (by decide))]
  apply Lanes.congr; intro t _
  simp only [zz77n8,hit_cons,hit,f]
private theorem zz77n12 {b : Bool} {ts : List Trial} (rest opts : List Col)
    (bd : ∀ t∈ts,t.value.Bounded) (br : ∀ x∈rest,x.Bounded) (bo : ∀ x∈opts,x.Bounded)
    {r : Nat} (hr : r<32) (t : Trial) (ht : t∈ts)
    (stop : coarseClose (dataFor b) (Lanes.ones ts) ts rest opts r = true) :
    r < zz77n2 (dataFor b) rest opts t := by
  let d := dataFor b
  have hd : d.valid < 2^48 := by cases b <;> decide
  let v := fun t : Trial => zz77n8 d (sinkHit false (t.value::rest)) false opts +
      zz77n8 d (sinkHit true (t.value::rest)) true opts
  have V : ∀ t∈ts, v t<16 := fun t _ => Nat.lt_of_le_of_lt
    (Nat.add_le_add (zz77n10 ..) (zz77n10 ..)) (by decide)
  have eq : allFail (Lanes.ones ts) (Lanes.pack ts v) r = 32*Lanes.ones ts := by
    simp only [coarseClose,Bool.and_eq_true,beq_iff_eq] at stop
    have E := stop.2
    change allFail _ (coarseSide d _ ts rest opts false + coarseSide d _ ts rest opts true) r = _ at E
    rw [zz77n11 hd rest opts bd br bo,zz77n11 hd rest opts bd br bo,Lanes.add] at E
    exact E
  obtain ⟨i,hi,et⟩ := List.getElem_of_mem ht
  have W := zz77n5 v V r hr i hi
  rw [eq,ones_bit i hi,et] at W
  have small := of_decide_eq_true W.symm
  exact Nat.lt_of_lt_of_le small (Nat.add_le_add (zz77n9 b false _ _) (zz77n9 b true _ _))
theorem laneLaw_for (b : Bool) : LaneLaw (dataFor b) := by
  intro n fuel s init t next reach cap mem ok
  let d := dataFor b
  let ts := (trials d s init).filter (fun z => z.consumed == t.consumed)
  let rest := maskKeep s.sunk t.consumed false
  let opts := maskKeep s.sunk t.consumed true ++ s.internal
  let step := fun (z : Trial) => next ⟨s.wires++[z.value],z.value::rest,opts,z.order⟩
  let cost := zz77n2 d rest opts
  let base := 2*rest.length
  have mt : t∈ts := List.mem_filter.mpr ⟨mem,by simp⟩
  have hbd : ∀ z∈ts,z.value.Bounded := fun z hz => reach_trial_bounded reach (List.mem_filter.mp hz).1
  have sub (v : Bool) (x : Col) (hx : x∈maskKeep s.sunk t.consumed v) : x∈s.sunk := by
    obtain ⟨⟨c,i⟩,hc,rfl⟩ := List.mem_map.mp hx
    exact List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hc).1)
  have br : ∀ c∈rest,c.Bounded := fun c hc => (reach_bounds reach).2.1 c (sub _ _ hc)
  have bo : ∀ c∈opts,c.Bounded := by
    intro c hc
    rcases List.mem_append.mp hc with h|h
    · exact (reach_bounds reach).2.1 c (sub _ _ h)
    · exact (reach_bounds reach).2.2 c h
  have hd : d.valid < 2^48 := by cases b <;> decide
  have score : zz77n0 d ts rest opts false + zz77n0 d ts rest opts true = Lanes.pack ts cost := by
    rw [zz77n4 hd rest opts hbd br bo,zz77n4 hd rest opts hbd br bo,Lanes.add]; rfl
  have small : ∀ z∈ts,cost z < 16 := fun z _ =>
    Nat.lt_of_le_of_lt (Nat.add_le_add (naive_small ..) (naive_small ..)) (by decide)
  have R : ((s.sunk.zipIdx.filter fun (_,i) => !t.consumed.testBit i).map Prod.fst) = rest := by
    unfold rest maskKeep; simp
  have O : ((s.sunk.zipIdx.filter fun (_,i) => t.consumed.testBit i).map Prod.fst ++ s.internal) = opts := by
    unfold opts maskKeep; simp
  have nonempty : ts.isEmpty = false := List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem mt)
  change evaluateTrials d (n+1) fuel s t.consumed ts next = true at ok
  simp only [evaluateTrials,nonempty,Bool.false_eq_true,ite_false,R,O] at ok
  have noCheaper (stop : coarseClose d (Lanes.ones ts) ts rest opts (10+fuel-(n+1)-base) = true) :
      canContinue d (t.value::rest) opts (10+fuel-(n+1)) = false := by
    apply Bool.eq_false_iff.mpr
    intro fit
    have fit' := (canContinue_cons_iff d t.value rest opts _).mp fit
    have fail := zz77n12 rest opts hbd br bo (by omega) t mt stop
    change 10+fuel-(n+1)-base < zz77n1 d rest opts false t + zz77n1 d rest opts true t at fail
    change base+zz77n1 d rest opts false t+zz77n1 d rest opts true t ≤ _ at fit'
    omega
  by_cases cheap : coarseClose d (Lanes.ones ts) ts rest opts (10+fuel-(n+1)-base) = true
  · have failed := noCheaper cheap
    constructor
    · apply Bool.eq_false_iff.mpr
      intro fit
      have f := (canContinue_cons_iff d t.value rest opts _).mp fit
      have h : canContinue d (t.value::rest) opts (10+fuel-(n+1)) = true :=
        (canContinue_cons_iff d t.value rest opts _).mpr (Nat.le_trans f (by omega))
      exact Bool.noConfusion (failed.symm.trans h)
    · intro _ fit; exact Bool.noConfusion (failed.symm.trans fit)
  have skipped : ¬coarseClose d (ts.foldr (fun _ v => 1+(v <<< 64)) 0) ts rest opts
      (10+fuel-(n+1)-2*rest.length) = true := by simpa only [zz77n3] using cheap
  simp only [skipped,ite_false] at ok
  change (if base>10+fuel-(n+1) then true else
       if base≤10-(n+1) && allFail _ (zz77n0 d ts rest opts false + zz77n0 d ts rest opts true) _ != 32*_ then false else
       if fuel==0 then true else
       let exclude := allFail _ (zz77n0 d ts rest opts false + zz77n0 d ts rest opts true) _
       if exclude == 32*_ then true else
       ts.zipIdx.all fun (z,i) => exclude.testBit (64*i+5) || step z) = true at ok
  rw [score,zz77n3] at ok
  obtain ⟨closed,more⟩ := zz77n6 small (by omega : (n+1)+fuel≤9) mt ok
  have dstS : (trialAfter s t).sunk = t.value::rest := rfl
  have dstI : (trialAfter s t).internal = opts := rfl
  dsimp only
  rw [dstS,dstI]
  constructor
  · apply Bool.eq_false_iff.mpr; intro pos
    have h := (canContinue_cons_iff d t.value rest opts _).mp pos
    change 10-(n+1)<base+cost t at closed
    change base+zz77n1 d rest opts false t+zz77n1 d rest opts true t ≤ _ at h
    unfold cost zz77n2 at closed; omega
  · intro pos fit
    apply more pos
    have h := (canContinue_cons_iff d t.value rest opts _).mp fit
    change base+(zz77n1 d rest opts false t+zz77n1 d rest opts true t)≤_
    simpa only [Nat.add_assoc,base,zz77n1] using h
end L652.GroupProjection
namespace L652
def movedIndex (s : SymIndex) (i : Nat) : Nat :=
  if h : i<6 then (coordMap s ⟨i,h⟩).val else i
def movedKey (s : SymIndex) (c : Nat) : Nat :=
  let a := movedIndex s (c/3 % 32)
  let b := movedIndex s (c/3/32)
  (32*max a b+min a b)*3+c % 3
private theorem zz78n0 (s : SymIndex) (e : List Word) (x : Word) :
    (e.map (relabel s)).idxOf (relabel s x) = e.idxOf x := by
  induction e with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y=x
    · subst y; simp
    · have hh := (relabel_injective s).ne h
      simp [h,hh,ih]
private theorem zz78n1 (s : SymIndex) (e : List Word) (x : Word) :
    (rawWords ++ e.map (relabel s)).idxOf (relabel s x) = movedIndex s ((rawWords++e).idxOf x) := by
  by_cases mem : x∈rawWords
  · obtain ⟨i,rfl⟩ := exists_rawAt _ mem
    rw [show relabel s (rawAt i)=rawAt (coordMap s i) from relabel_raw s i,List.idxOf_append_of_mem (rawAt_mem _),List.idxOf_append_of_mem (rawAt_mem _),raw_idx,raw_idx]
    simp [movedIndex,i.isLt]
  · have nmem : relabel s x ∉ rawWords := by
      intro m
      obtain ⟨y,hy,eq⟩ := List.mem_map.mp ((mapped_raw s).mem_iff.mpr m)
      exact mem ((relabel_injective s eq) ▸ hy)
    rw [List.idxOf_append_of_notMem nmem,List.idxOf_append_of_notMem mem,zz78n0]
    have len : rawWords.length=6 := rfl
    simp [movedIndex,len]
theorem moved_key (s : SymIndex) (e : List Word) (g : LogicalGate)
    (ready : sources g ⊆ (rawWords++e).toFinset) (small : (rawWords++e).length≤32) :
    gateKey (rawWords++e.map (relabel s)) (mapGate s g) =
      movedKey s (gateKey (rawWords++e) g) := by
  obtain ⟨a,b,op,_,_⟩ := key_decode ready small
  simp only [movedKey,a,b,op]
  cases g with
  | neg x => simp [gateKey,mapGate,operandPair,operation,zz78n1,Nat.mul_comm]
  | meet x y | join x y =>
    simp only [gateKey,mapGate,operandPair,operation,zz78n1]
    cases Nat.le_total ((rawWords++e).idxOf x) ((rawWords++e).idxOf y) with
    | inl h => simp [min_eq_left h,max_eq_right h,Nat.mul_comm]
    | inr h => simp [min_eq_right h,max_eq_left h,Nat.max_comm,Nat.min_comm,Nat.mul_comm]
end L652
namespace L652
private def zz79n0 (g h : LogicalGate) :=
  1024*gateKey rawWords g + gateKey (rawWords++[g.out]) h
private def zz79n1 (k : Nat) := ∃ (g h : LogicalGate) (q : List LogicalGate),
  History (g::h::q) ∧ (g::h::q).length=5 ∧ DecodesThree (g::h::q) ∧
  KeyOrdered rawWords 0 (g::h::q) ∧ zz79n0 g h=k
private theorem zz79n2 {p} (hist : History p) (len : p.length=5) (sup : DecodesThree p) :
    ∃ g h q, (g::h::q).Perm p ∧ zz79n1 (zz79n0 g h) ∧ KeyOrdered rawWords 0 (g::h::q) := by
  obtain ⟨qs,perm,ord⟩ := canonical_order (by change 6+p.length≤32; omega) (history_schedule hist).1
  have size := perm.length_eq.trans len
  cases qs with
  | nil => simp at size
  | cons g q =>
    cases q with
    | nil => simp at size
    | cons h q =>
      exact ⟨g,h,q,perm,⟨g,h,q,history_scheduled ord.scheduled ((history_fresh hist).perm perm),
        size,sup.perm perm,ord,rfl⟩,ord⟩
private theorem zz79n3 (s : SymIndex) (e : List Word) (g : LogicalGate)
    (ready : sources g ⊆ (rawWords++e).toFinset) :
    sources (mapGate s g) ⊆ (rawWords++e.map (relabel s)).toFinset := by
  intro x hx
  have m := mem_sources.mp hx
  rw [mapGate_args] at m
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp m
  rcases List.mem_append.mp (List.mem_toFinset.mp (ready (mem_sources.mpr hv))) with hr | he
  · exact List.mem_toFinset.mpr (List.mem_append_left _ ((mapped_raw s).mem_iff.mp (List.mem_map.mpr ⟨v,hr,rfl⟩)))
  · exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨v,he,rfl⟩))
theorem normalize_private_two {gs} (hist₀ : History gs) (sz : gs.length≤5) (dec : DecodesThree gs) :
    ∃ g h q, History (g::h::q) ∧ (g::h::q).length=5 ∧ DecodesThree (g::h::q) ∧
      KeyOrdered rawWords 0 (g::h::q) ∧ gateKey rawWords g∈PrivateCertificate.firstKeys ∧
      ∀ s : SymIndex, movedKey s (gateKey rawWords g)=gateKey rawWords g →
        gateKey (rawWords++[g.out]) h ≤ movedKey s (gateKey (rawWords++[g.out]) h) := by
  classical
  obtain ⟨p,hp,lenp,dp⟩ := pad_private hist₀ dec (5-gs.length) (by omega)
  obtain ⟨g₀,h₀,_,_,b₀,_⟩ := zz79n2 hp lenp dp
  have someBad : ∃ k, zz79n1 k := ⟨_,b₀⟩
  obtain ⟨g,h,q,hist,len,hd,ord,eq⟩ := Nat.find_spec someBad
  have minrank {u v} (b : zz79n1 (zz79n0 u v)) : zz79n0 g h ≤ zz79n0 u v :=
    eq ▸ Nat.find_min' someBad b
  have gr := ord.scheduled.1
  have hrest : KeyOrdered (rawWords++[g.out]) (gateKey rawWords g) (h::q) := by cases ord; assumption
  have hr := hrest.scheduled.1
  have moved (s : SymIndex) : ∃ u v t, (u::v::t).Perm ((g::h::q).map (mapGate s)) ∧
      zz79n0 g h ≤ zz79n0 u v ∧ KeyOrdered rawWords 0 (u::v::t) ∧
      gateKey rawWords u ≤ gateKey rawWords (mapGate s g) ∧ gateKey (rawWords++[u.out]) v < 1024 := by
    obtain ⟨u,v,t,perm,bad,ord'⟩ := zz79n2 (relabel_history s hist) (by simpa using len) (hd.relabel s)
    refine ⟨u,v,t,perm,minrank bad,ord',?_,?_⟩
    · apply first_le_ready ord' (by simpa using zz79n3 s [] g (by simpa using gr))
      exact perm.mem_iff.mpr (by simp)
    · have rd : sources v ⊆ (rawWords++[u.out]).toFinset := by cases ord'; rename_i tail; exact tail.scheduled.1
      have bound := (key_ready (rawWords++[u.out]) v (by decide : 7≤32)).mp rd
      change gateKey (rawWords++[u.out]) v < 96*7 at bound
      omega
  refine ⟨g,h,q,hist,len,hd,ord,?_,?_⟩
  · by_contra fail
    have new := (history_fresh hist).2 g (by simp)
    obtain ⟨s,lt⟩ := smaller_first gr new.2.2 fail
    obtain ⟨u,v,t,_,low,_,first,bound⟩ := moved s
    unfold zz79n0 at low
    omega
  · intro s stay
    obtain ⟨u,v,t,perm,low,ord',first,bound⟩ := moved s
    have mg : gateKey rawWords (mapGate s g) = gateKey rawWords g := by
      simpa using (moved_key s [] g (by simpa using gr) (by decide)).trans stay
    have same : gateKey rawWords u = gateKey rawWords (mapGate s g) := by
      unfold zz79n0 at low
      omega
    have ug := ord'.scheduled.1
    have mappedReady : sources (mapGate s g) ⊆ rawWords.toFinset := by
      simpa using zz79n3 s [] g (by simpa using gr)
    have eu := eval_gate_key ug (by decide : rawWords.length≤32)
    rw [same,eval_gate_key mappedReady (by decide)] at eu
    have out : (mapGate s g).out=u.out := congrArg UInt64.toBitVec eu
    have tail : KeyOrdered (rawWords++[u.out]) (gateKey rawWords u) (v::t) := by cases ord'; assumption
    have hs : sources (mapGate s h) ⊆ (rawWords++[u.out]).toFinset := by
      simpa [mapGate_out,out] using zz79n3 s [g.out] h hr
    have member : mapGate s h ∈ v::t := by
      have inFull := perm.mem_iff.mpr (show mapGate s h ∈ (g::h::q).map (mapGate s) by simp)
      apply (List.mem_cons.mp inFull).resolve_left
      intro hu
      have distinct : g.out≠h.out := by
        have clean := (history_fresh hist).1
        simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at clean
        exact clean.1.1
      apply distinct
      apply relabel_injective s
      rw [mapGate_out,mapGate_out,out,hu]
    have smaller := first_le_ready tail hs member
    have mh := moved_key s [g.out] h hr (by decide : 7≤32)
    have transformed : gateKey (rawWords++[u.out]) (mapGate s h)=movedKey s (gateKey (rawWords++[g.out]) h) := by
      simpa [mapGate_out,out] using mh
    rw [transformed] at smaller
    unfold zz79n0 at low
    omega
end L652
namespace L652.PrivateCertificate
def seconds : Nat → List Nat
  | 2 => [96,97,101,195,196,288,289,291,292,299,393,394,579,580,585,586]
  | 96 => [97,192,193,200,288,289,294,295,299,393,394,582,583,585,586,596]
  | 97 => [192,193,200,288,289,294,295,299,393,394,582,583,585,586,596]
  | 288 => [289,291,292,387,388,390,391,579,580,596]
  | 289 => [291,292,387,388,390,391,579,580,596]
  | _ => []
end L652.PrivateCertificate
namespace L652
open PrivateCertificate
set_option maxRecDepth 10000 in
private theorem zz81n0 :
    (firstKeys.all fun a => (next a (raw++[value raw a])).all fun b =>
      (seconds a).contains b || (List.finRange 36).any (fun s =>
        movedKey s a == a && decide (movedKey s b < b))) = true := by decide +kernel
private theorem zz81n1 {a b : Nat} (first : a∈firstKeys)
    (step : b∈next a (raw++[value raw a]))
    (minimal : ∀ s : SymIndex, movedKey s a=a → b≤movedKey s b) : b∈seconds a := by
  have test := List.all_eq_true.mp (List.all_eq_true.mp zz81n0 a first) b step
  simp only [Bool.or_eq_true,List.contains_iff_mem,List.any_eq_true,Bool.and_eq_true,beq_iff_eq,
    decide_eq_true_eq] at test
  rcases test with h|⟨s,_,same,improve⟩
  · exact h
  · exact False.elim ((Nat.not_lt.mpr (minimal s same)) improve)
private theorem zz81n2 {a b cs dst} (p : Path 0 raw (a::b::cs) dst) :
    b ∈ next a (raw++[value raw a]) := by
  cases p with
  | cons _ tail => cases tail with | cons h _ => exact h
theorem canonical_private_two_path {gs} (hist : History gs) (size : gs.length≤5) (dec : DecodesThree gs) :
    ∃ g h q cs, DecodesThree (g::h::q) ∧
      let a := gateKey rawWords g
      let b := gateKey (rawWords++[g.out]) h
      (a::b::cs).length=5 ∧ a∈firstKeys ∧ b∈seconds a ∧
      Path 0 raw (a::b::cs) ((wiresOf (g::h::q)).map UInt64.ofBitVec) := by
  obtain ⟨g,h,q,history,len,hd,order,first,stable⟩ := normalize_private_two hist size dec
  have enc := encoded_path order (history_fresh history) (by change 6+(g::h::q).length≤32; omega)
  have el (ws : List Word) (xs : List LogicalGate) : (encodeGates ws xs).length=xs.length := by
    induction xs generalizing ws with
    | nil => rfl
    | cons g xs ih => simp [encodeGates,ih]
  refine ⟨g,h,q,_,hd,(el _ _).trans len,first,?_,enc⟩
  exact zz81n1 first (zz81n2 enc) stable
end L652
namespace L652.PrivateCertificate
def goalWord (k : Nat) : W :=
  if k=0 then 0xfefcfaf0eeccaa00 else if k=1 then 0xfeeefcccfaaaf000 else 0xfefaeeaafcf0cc00
def skip (p : Nat) : Nat := p / 4 % 8
def coordinate (p j : Nat) : Nat := if j < skip p then j else j+1
def low (p j : Nat) : Nat := (p >>> (5+6*coordinate p j)) % 64
def high (p j : Nat) : Nat := low p j ^^^ (1 <<< coordinate p j)
def bit (w : W) (r : Nat) : Bool := w.toBitVec.getLsbD r
def changed (p j : Nat) (w : W) : Bool := bit w (low p j) != bit w (high p j)
def packOK (n : Nat) (ws : List W) (p : Nat) : Bool :=
  decide (p % 4 < 3) && (if n=6 then skip p == 6 else decide (skip p < 6)) &&
  (List.range n).all (fun j => changed p j (goalWord (p % 4))) &&
  (ws.drop 6).all (fun w => decide ((List.range n).countP (fun j => changed p j w) ≤ 1))
end L652.PrivateCertificate
namespace L652.PrivatePacking
variable {Signal Row : Type} [DecidableEq Signal]
def Determines (ev : Signal → Row → Bool) (features : Finset Signal) (goal : Row → Bool) : Prop :=
  ∀ x y, (∀ s ∈ features, ev s x = ev s y) → goal x = goal y
theorem lower {n : Nat} (ev : Signal → Row → Bool) (pool read : Finset Signal)
    (goal : Row → Bool) (lo hi : Fin n → Row)
    (subset : read ⊆ pool) (det : Determines ev read goal)
    (different : ∀ i, goal (lo i) ≠ goal (hi i))
    (oneChange : ∀ s ∈ pool, ∀ i j,
      ev s (lo i) ≠ ev s (hi i) → ev s (lo j) ≠ ev s (hi j) → i=j) :
    n ≤ read.card := by
  classical
  have finds (i : Fin n) : ∃ s : read, ev s.val (lo i) ≠ ev s.val (hi i) := by
    by_contra! denied
    exact different i (det _ _ (fun s hs => denied ⟨s,hs⟩))
  choose chooseSignal changes using finds
  have injective : Function.Injective chooseSignal := by
    intro i j eq
    apply oneChange (chooseSignal i).val (subset (chooseSignal i).property) i j (changes i)
    rw [eq]
    exact changes j
  simpa using Fintype.card_le_of_injective chooseSignal injective
theorem expandGate (ev : Signal → Row → Bool) (pool read : Finset Signal)
    (a b new : Signal) (goal : Row → Bool) (op : Bool → Bool → Bool)
    (ha : a ∈ pool) (hb : b ∈ pool)
    (value : ∀ r, ev new r = op (ev a r) (ev b r))
    (hr : read ⊆ insert new pool) (hd : Determines ev read goal) :
    ∃ prior ⊆ pool, Determines ev prior goal ∧ prior.card ≤ read.card+1 := by
  classical
  by_cases use : new ∈ read
  · let prior := insert a (insert b (read.erase new))
    refine ⟨prior,?_,?_,?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | rest
      · exact ha
      rcases Finset.mem_insert.mp rest with rfl | rem
      · exact hb
      exact (Finset.mem_insert.mp (hr (Finset.mem_erase.mp rem).2)).resolve_left
        (Finset.mem_erase.mp rem).1
    · intro x y same
      apply hd
      intro s hs
      by_cases h : s=new
      · subst s
        simp only [value, same a (by simp [prior]), same b (by simp [prior])]
      · exact same s (by simp [prior,h,hs])
    · have p := Finset.card_insert_le a (insert b (read.erase new))
      have q := Finset.card_insert_le b (read.erase new)
      have z := Finset.card_erase_add_one use
      dsimp [prior]
      omega
  · exact ⟨read, fun x hx => (Finset.mem_insert.mp (hr hx)).resolve_left
      (fun eq => use (eq ▸ hx)), hd, Nat.le_succ _⟩
end L652.PrivatePacking
namespace L652.PrivateCertificate
def rowBit (w : W) (r : Fin 64) : Bool := bit w r.val
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem zz84n0 : ∀ (i j : Fin 6) (r : Fin 64),
    bit (raw.getD i.val 0) r.val ≠ bit (raw.getD i.val 0) (r.val ^^^ (1 <<< j.val)) →
    i=j := by decide +kernel
private theorem zz84n1 (p : Nat) : Function.Injective (coordinate p) := by
  intro i j h
  simp only [coordinate] at h
  split at h <;> split at h <;> omega
private theorem zz84n2 {n p : Nat} {v : W}
    (count : (List.range n).countP (fun j => changed p j v) ≤ 1)
    {i j : Fin n} (hi : changed p i v=true) (hj : changed p j v=true) : i=j := by
  let xs := (List.range n).filter (fun t => changed p t v)
  have sz : xs.toFinset.card ≤ 1 := le_trans (List.toFinset_card_le _) (by
    simpa only [xs, ← List.countP_eq_length_filter] using count)
  apply Fin.ext
  apply Finset.card_le_one.mp sz
  · exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr i.isLt,hi⟩)
  · exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr j.isLt,hj⟩)
theorem packOK_lower {n p : Nat} (small : n=5 ∨ n=6) (extra : List W)
    (ok : packOK n (raw++extra) p = true) (O : Finset W)
    (subset : O ⊆ (raw++extra).toFinset)
    (det : PrivatePacking.Determines rowBit O (rowBit (goalWord (p % 4)))) :
    n ≤ O.card := by
  simp only [packOK,Bool.and_eq_true] at ok
  have inds : ∀ j : Fin n, coordinate p j.val < 6 := by
    intro j
    rcases small with h | h
    · subst n; dsimp [coordinate]; split <;> omega
    · subst n
      have sk : skip p=6 := by simpa using ok.1.1.2
      simp [coordinate,sk,j.isLt]
  have lowBound j : low p j < 64 := Nat.mod_lt _ (by decide)
  have allhigh : ∀ (r : Fin 64) (c : Fin 6), r.val ^^^ (1 <<< c.val) < 64 := by decide +kernel
  let lo : Fin n → Fin 64 := fun i => ⟨low p i.val,lowBound i.val⟩
  let hi : Fin n → Fin 64 := fun i => ⟨high p i.val,allhigh (lo i) ⟨_,inds i⟩⟩
  have goalChange (i : Fin n) : changed p i.val (goalWord (p % 4)) = true :=
    List.all_eq_true.mp ok.1.2 _ (List.mem_range.mpr i.isLt)
  apply PrivatePacking.lower rowBit (raw++extra).toFinset O _ lo hi subset det
  · intro i; exact bne_iff_ne.mp (goalChange i)
  · intro s mem i j ci cj
    have ci' : changed p i s=true := bne_iff_ne.mpr ci
    have cj' : changed p j s=true := bne_iff_ne.mpr cj
    rcases List.mem_append.mp (List.mem_toFinset.mp mem) with rawMember | more
    · obtain ⟨k,hk,ek⟩ := List.mem_iff_getElem.mp rawMember
      have ks : k<6 := hk
      have asRaw : raw.getD k 0=s := by simp [List.getD_eq_getElem?_getD,hk,ek]
      have only (t : Fin n) (c : changed p t s=true) : k=coordinate p t := by
        apply congrArg Fin.val (zz84n0 ⟨k,ks⟩ ⟨coordinate p t,inds t⟩ (lo t) ?_)
        change bit (raw.getD k 0) (low p t) ≠ bit (raw.getD k 0) (high p t)
        rw [asRaw]; exact bne_iff_ne.mp c
      exact Fin.ext (zz84n1 p ((only i ci').symm.trans (only j cj')))
    · have drop : (raw++extra).drop 6 = extra := by
        rw [show 6=raw.length by decide]; simp
      obtain cnt := List.all_eq_true.mp ok.2 s (drop ▸ more)
      exact zz84n2 (of_decide_eq_true cnt) ci' cj'
end L652.PrivateCertificate
namespace L652.PrivateCertificate
def sequenceChecks {α : Type} (f : α → List Nat → Option (List Nat)) :
    List α → List Nat → Option (List Nat)
  | [], data => some data
  | x::xs, data => do sequenceChecks f xs (←f x data)
theorem sequenceChecks_mem {α : Type} {f : α → List Nat → Option (List Nat)}
    {xs : List α} {input output : List Nat} {x : α}
    (ok : sequenceChecks f xs input = some output) (hx : x ∈ xs) :
    ∃ a b, f x a = some b := by
  induction xs generalizing input with
  | nil => simp at hx
  | cons a as ih =>
    cases step : f a input with
    | none => simp [sequenceChecks,step] at ok
    | some after =>
      rcases List.mem_cons.mp hx with rfl | old
      · exact ⟨_,_,step⟩
      · exact ih (by simpa [sequenceChecks,step] using ok) old
def checkStream : Nat → Nat → List W → List Nat → Option (List Nat)
  | 0, _, ws, p::tail => if packOK 5 ws p then some tail else none
  | 0, _, _, [] => none
  | 1, minimum, ws, p::tail =>
      if p=0 then sequenceChecks (fun c => checkStream 0 c (ws++[value ws c])) (next minimum ws) tail
      else if packOK 6 ws p then some tail else none
  | 1, _, _, [] => none
  | n+2, minimum, ws, data =>
      sequenceChecks (fun c => checkStream (n+1) c (ws++[value ws c])) (next minimum ws) data
theorem checked_path {n min ws cs dst input output}
    (ok : checkStream n min ws input = some output) (path : Path min ws cs dst) (len : cs.length=n) :
    (∃ witness, packOK 5 dst witness = true) ∨
    (∃ prior c witness, dst=prior++[value prior c] ∧ c ∈ next 0 prior ∧ packOK 6 prior witness = true) := by
  induction n generalizing min ws cs dst input output with
  | zero =>
    have : cs=[] := List.length_eq_zero_iff.mp len
    subst cs; cases path
    cases input with
    | nil => simp [checkStream] at ok
    | cons p tail =>
      cases h : packOK 5 ws p
      · simp [checkStream,h] at ok
      · exact Or.inl ⟨_,h⟩
  | succ n ih =>
    cases path with
    | nil => simp at len
    | @cons _ _ c rest final step tail =>
      cases n with
      | zero =>
        cases input with
        | nil => simp [checkStream] at ok
        | cons p data =>
          by_cases e : p=0
          · have ch := sequenceChecks_mem (by simpa [checkStream,e] using ok) step
            obtain ⟨a,b,success⟩ := ch
            exact ih success tail (by simpa using len)
          · cases valid : packOK 6 ws p
            · simp [checkStream,e,valid] at ok
            · have emp : rest=[] := List.length_eq_zero_iff.mp (by simpa using len)
              subst rest; cases tail
              refine Or.inr ⟨_,c,p,rfl,?_,valid⟩
              obtain ⟨mem,passed⟩ := List.mem_filter.mp step
              refine List.mem_filter.mpr ⟨mem,?_⟩
              simp only [Bool.and_eq_true] at passed ⊢
              exact ⟨⟨⟨by simp,passed.1.1.2⟩,passed.1.2⟩,passed.2⟩
      | succ m =>
        obtain ⟨a,b,success⟩ := sequenceChecks_mem ok step
        exact ih success tail (by simpa using len)
end L652.PrivateCertificate
namespace L652
open PrivateCertificate
private theorem zz86n0 {gs : List LogicalGate} (all : DecodesThree gs) (p : Nat) :
    ∃ O ⊆ ((wiresOf gs).map UInt64.ofBitVec).toFinset, O.card ≤ 4 ∧
      PrivatePacking.Determines rowBit O (rowBit (goalWord (p % 4))) := by
  let i : Fin 3 := if p % 4=0 then 0 else if p % 4=1 then 1 else 2
  have target : (goalWord (p % 4)).toBitVec = matchWord i := by
    dsimp [goalWord,i]
    split
    · rfl
    · split <;> rfl
  obtain ⟨K,ks,sz,det⟩ := all i
  refine ⟨K.image UInt64.ofBitVec,?_,Finset.card_image_le.trans sz,?_⟩
  · intro x hx
    obtain ⟨v,mem,rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,List.mem_toFinset.mp (ks mem),rfl⟩)
  · intro x y agree
    change (goalWord (p % 4)).toBitVec.getLsbD x.val = (goalWord (p % 4)).toBitVec.getLsbD y.val
    rw [target]
    have inside : ∀ t : Fin 64, (~~~(0 : Word)).getLsbD t.val = true := by decide +kernel
    apply det x y (inside x) (inside y)
    exact fun w hw => agree _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
private theorem zz86n1 {min ws cs dst} (h : Path min ws cs dst) :
    dst.length=ws.length+cs.length := by
  induction h with
  | nil => simp
  | cons step tail ih => simp only [List.length_append,List.length_cons,List.length_nil] at ih ⊢; omega
private theorem zz86n2 {ws : List W} {c : Nat} (small : ws.length≤32) (step : c ∈ next 0 ws) :
    c/3 % 32<ws.length ∧ c/3/32<ws.length := by
  obtain ⟨mem,_⟩ := List.mem_filter.mp step
  obtain ⟨b,hb,mem⟩ := List.mem_flatMap.mp mem
  obtain ⟨a,ha,ops⟩ := List.mem_flatMap.mp mem
  have bl := List.mem_range.mp hb
  have al := List.mem_range.mp ha
  by_cases h : a=b
  · subst a
    simp at ops
    subst c
    unfold key
    omega
  · simp [h] at ops
    rcases ops with rfl|rfl <;> unfold key <;> omega
private theorem zz86n3 {ws : List W} {c : Nat} (small : ws.length≤32)
    (step : c ∈ next 0 ws) {O : Finset W} {goal : Fin 64 → Bool}
    (sub : O ⊆ (ws++[value ws c]).toFinset) (det : PrivatePacking.Determines rowBit O goal) :
    ∃ K ⊆ ws.toFinset, PrivatePacking.Determines rowBit K goal ∧ K.card ≤ O.card+1 := by
  let a := ws.getD (c/3 % 32) 0
  let b := ws.getD (c/3/32) 0
  let op (x y : Bool) := if c % 3=0 then x&&y else if c % 3=1 then x||y else !x
  have mem (i : Nat) (h : i<ws.length) : ws.getD i 0 ∈ ws.toFinset := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  obtain ⟨ha,hb⟩ := zz86n2 small step
  apply PrivatePacking.expandGate rowBit ws.toFinset O a b (value ws c) goal op (mem _ ha) (mem _ hb)
  · intro r
    simp only [value,op,a,b,rowBit,bit]
    split
    · simp
    · split <;> simp [r.isLt]
  · simpa using sub
  · exact det
theorem private_of_two_pack
    (pack : ∀ {a b cs dst}, Path 0 raw (a::b::cs) dst → (a::b::cs).length=5 →
      a ∈ firstKeys → b ∈ seconds a →
      (∃ w, packOK 5 dst w=true) ∨
      (∃ prior c w, dst=prior++[value prior c] ∧ c∈next 0 prior ∧ packOK 6 prior w=true)) :
    PrefixObstruction := by
  intro gs hist size dec
  obtain ⟨g,h,q,cs,three,len,first,second,path⟩ := canonical_private_two_path hist size dec
  let dst := (wiresOf (g::h::q)).map UInt64.ofBitVec
  let extra := ((g::h::q).map LogicalGate.out).map UInt64.ofBitVec
  have form : dst=raw++extra := by simp [dst,extra,wiresOf]; rfl
  have sizeDst : dst.length=11 := by
    have cnt := zz86n1 path
    rw [len] at cnt
    exact cnt
  rcases pack path len first second with ⟨w,ok⟩ | ⟨prior,c,w,eq,step,ok⟩
  · obtain ⟨O,sub,sz,det⟩ := zz86n0 three w
    change packOK 5 dst w=true at ok
    change O ⊆ dst.toFinset at sub
    rw [form] at ok sub
    have h := packOK_lower (Or.inl rfl) extra ok O sub det
    omega
  · obtain ⟨O,sub,sz,det⟩ := zz86n0 three w
    change dst=prior++[value prior c] at eq
    change O ⊆ dst.toFinset at sub
    have priorSize : prior.length=10 := by rw [eq,List.length_append,List.length_singleton] at sizeDst; omega
    rw [eq] at sub
    obtain ⟨K,ks,decoder,bound⟩ := zz86n3 (by omega) step sub det
    have sizeRaw : raw.length≤prior.length := by rw [priorSize]; decide
    have front := congrArg (List.take raw.length) (form.symm.trans eq)
    simp only [List.take_append_of_le_length (Nat.le_refl _),List.take_length,
      List.take_append_of_le_length sizeRaw] at front
    have peq : prior=raw++prior.drop raw.length := by
      exact (List.take_append_drop raw.length prior).symm.trans
        (congrArg (fun z => z++prior.drop raw.length) front.symm)
    have h := packOK_lower (Or.inr rfl) (prior.drop raw.length) (peq ▸ ok) K (peq ▸ ks) decoder
    omega
end L652
namespace L652.PrivateCertificate
private def zz87n0 : Nat := 0xa060c081180a5148918c8418a448c642045260d323022950319181149838cad28a440c6460452246323022910b195a1148818c8e08a441c647081830a303850c18518102060438c0a14302046062452206323548c1811838ac60c08c0a5630214607291830a302948c0811814a060428c183038204614181c30230a8c0e08518146870428c0e3038614605391c10a302060e08118506060408c0c30306046020e5230632106291a3190831c8c18c8418a560c6430c5230632106291c319483148c18c941ca460c6460c5230632186291871908b148c18c8438ac60c6420456a463230a2d10319181168838cac08b440c6460456a06323022d103591c1168818c8c08b442c656845a206323032d103191c1168838c8c48b440c646145e20632106295231908715a818c8418a440d6430c52206325072910319183168818c8618a441c6421c5620632a460c08318143860438c291a3020c60c0f18106302868c08718147070438c083a3820c614085a102306042d0851810a568408c2952b420460c295a10230294ad08518506178408c0a30bc2146040858d02302842c085185020e0608c181470304606047228632ac41c0c5181428e0628c1852303046062838382302941c0c5185060f0608c183478304606183c3823021c1e0c1180831c8e18c8c08f450c6450c3818e302141c0c3181070f0618c0a10f4314604187e182302141c081184a1129814c970884c0865684426043294221322194a1109a50ca44a8440865a864620432d4321106196a9908810cb50c84c0865a864229432d5221102192c9128810cac4894408646244a29432b42a5102195a1128814cad4894408656844a60432b422514a19289928810c8c2c94408646064a205323132510219181929810c8c0c94528656864a204325022510219066090220d022059110681102c8c834188124641a4e6090220d0e20591106831024088b419a120441a0c4099220d272048110687102c088345c321106191e1128830c960c84408643844220432382251021908950ad10c844a84c0a652a54620432952a114219289d08810c944e8450865aa74220432352a510219189528814c8c4a94508646054a20432312a530219189528a50cad4a94408646274a20432198920441a0e9508830c8e4a94418646244a20432d4b23102195a5138810c8c2c9c40864314462043294aa310219285d18810c8c2a9c408656044220432102211a2191a1118810c84288548864a16422043230a251021908510801028c3030200003144220c3210aa1102192c3109c10c8c1884e086520c62304329062158219483109c10ca4188452864a0e4230c32507a11821928390ac10c941c84e0864a0e4229432d072118219283108c10c8c38946086460c4a305323063518219183138c10c8c58946086460c4a70432b062518219183928c10ca4188461864b0e4230c3238625186190c3108c10c945a846086422d42b0432517a11821918b528c10c865a8461864a1e463043230e2718219087518c10c843884608643142408c34088120cc1a186060c000022048118681312408c3408e120cc1a245890220d0a285811068314242883408e120c41a0c4198220d0228cc11868310662883408a330441a344090220d022048190681102408b3418a121461a144898220d0220c8110681106448934689320441a044190320d2320c8110689126408834288360441a0c4190a20d0260c811068118641883408a320461a6a1188a10cad08d450864a046a2843218231142194a9588a10c944ac4508646256a2843210a33142190c1188a30c8428c45086520c6238432506311c2191831a8e10c845ac4708643144620c3220c2f08000083100810484088452965284622043250231102191811a8810c8608c441864214662043218221103190c1d08818c960ca440a6432642206323022930219081149810c8408a4c886420442606321023934a192c11c8a50ca508ac40865a86422063294229102992e1948810ca508a4c086528472294329022910219281948814c940ca4c0864a047229432d432910219185168810c8e0c9440c646045a604323023d14a195a1168810c8c08a440864310340883410221107190c1148834c8708a4418647045a20c3218229102190c9d08818c8428ac40a64b16562043210a29302194a5158810c942cac408646145e2043210a291021908314ac10c861c8460c6420c5230532106291c2592c3948c10c8418a4e086520c52304325072918219183168c10c8618a46186421c5630432106291021904c490228d02286811068b04722843294239142192811c8a10c8c08f45086420c7238432a148c0895832286044ac39143023561c8a18312b07450c0895872286144ac1810706256040b18112b03022150a595a5108852c8c08844a96460452214b2b422110a593a2860c4ac0d103022560c2a1811ab02850c0855814286146ac2b143023560c081811ab03c40c18d581c206046ac0a1430225615291811ab02148e289d852a46844ac3956302256062542214b23548c1895838ac60c4ac0c5230225605a91811ab02948c08d5814a46042ac2b52302356052b1811ab03948c18d5814a06046ac283838235614185c112b0a0c0e089d854607044ac18343862560c1b1c112b060d0e089d838687044ac38343822560c181c112b0a0c0e18958386870c4ac0c3038225615181c11ab028d0e08d581c6070c6ac187238225604391c113b061d8e0895818e470c4ac0a72382356041818513b0a0c0c0895830686044ac0c3030625605181811ab03062110a59081108c12c8418844096422d62214b210e2350a5972386044ac1818302256060c18112b0ac60c08d5852346044ac181e302256050d1811ab0a0e0e0895830787044ac0a38382356041d1c112b02060c0815872216844ac0c10b4225605085a11ab0ac42d08d5830216846ac2952b422560c295a112b0294ad08d5850617844ac1830bc225605185e11ab021caf08958182168c4ac0a10300051040858952b0a442c0895830216044ac0c10b0625605085811ab02062c089585220e046ac3910703056158838112b0a441c289585020e044ac18147022561c8a38112b03023114a591a20e0c4ac1c14706256060838112b0ac41c08d581428e046ac0e1070635614a838112b02941c08d585060f044ac183478225606183c312b021c1e089581060e044ac29187022560c0e38112b02861c08d581070f044ac2910f422560c087a112b02843d08d581061f844ac0810303056020462214b23022910b5918116885ac860c8442d6420442216b21822910a59085158852c8418a44296548918952b0a440c4ad5852206054ac2810312a560c2a18952b06050c0a95872286254ac1810312a56068818952b02840c4ad5814206252ac2b10312b56050a1895ab03840c4ad5830a46254ac0852352a56042958952b02948c4a95810a46054ac2952312a560c2b18952b03148c4a95814a46256ac0850312a56051818952b0a0c0c4a95830686254ac0c30312a5605181895ab021c8c4a95852306254ac181c312a56040d18952b020e0c4a95852216a54ac1810b52a5605085a95ab0214ad4a95810206a44ac0c107138560408381c2b03041c4a9581420e256ac0850712a56040c38952b02043d4a95808114a952ca91031225605081891ab02148c4895810606244ac0810712256148818513b0a440c281d850206144ec181430a0761c8a18513b06040c289d81a2061c4ec1c1430e276060818513b0ac40c289d814286144ec0e1030e276042918513b02148c281d852a46144ec185630a276062918713b02948c289d810a06144ec283038a2760c1a1c513b030c0e389d814607144ec087238a27604081c512b02860c289d810346144ec083838a276148858513b06042c289d814216144ec0852b0a27604185c513b0a441c289d83028e144ec0a1070a276042838513b020c1e289d852206354ec181431aa76060818d53b02148c6a9d810216354ec081031a276040818d52b03840c08518142062508c083038a066070838312302040c6a918103063548c0a1031e076070818d5230ac40c1815852206150ac0f10306246148818d5230a040c08918382860c0ac181430a856070a18312306050c6a918722860448c1810302246060442214323040c6a9181a2060c48c1c14306246040818312302840c2a558142063568c2b10302346050a1811a303840c18d1810a46150ac085231aa4614a918112306158c0891814a460468c083038a856011024088b420c0c6a918506070448c183438224606181c3123021c8e08918106060448c081831aac6148c18116306070c08b18143060478c08383822c6040858d5230a442d08918302168448c0a10b4234604185e112302042c089185220e0448c1814702246020452214322840c4a1581c2062548c0c10312a4605081895a302060c4ab1810216a548c0810712a4604081815230a440c2899830286144cc0a1030a2660429185133020c0e2899810206354cc291830204605081850a303032910319522070408c0c28ac40c652045220632d4329103190c40d0228d0708a441c64b065220e32512a1103194a9148818c944ca440c643245220e3294a2b10319285958818c8448ac40c6421452206321022918319483148818c8458a440c6441c1c10630a0e0e083180450d0228d0220e811468429181823094239143192811c8a18c8418e450c644287a1823014221102192e1908810cb40c84408642064220432d422110219581128810c960c94408641102428834189120441a1c1928830c944c84408656254a2043291621182192c3908c10c8c1894528643182418834916a118219487118c10c8810b820000419581000020d0c080001060e04000222848110691906608834489330441a1441b8220d0260cc1106811866188349c8121441a0c4890a20d0e20585106833124288342043c0e0000c6090e20d060880408251142408c3448b120461a1450b0230d023848318682046228002102301420910a0e06000083070300003044200c0a10a230020518607040000c3038600002046220432102311000118286060000c107060000b044220e3258329302192c1148810c9408a4408646044a206323032d102190c1149830c84488440c652a452204323122d102190c9148830c8448ac4086420c72304321063914a1908b148c10c8222681106811076488340883b0441a045490228d026a6811068310342883408a1a0461a0441d0220d28103022561c0a18112b06040c0895872206044ac0408944296460442614b23032110a5938206044ac0c1030225614881811ab0a840c089581c1108852c8e14306356040918112b0a0c0e2895830e87044ac183438a256061446214b2a1c8e0895810207044ac0a1c302356040818116302062d08958183060c4ac081034225604185c112b0a451c0895814206002a20830380051128452216b25032910b590c114885ac8448a442d6421456216b21062910b590811c8a5acad0894429646064a214b23822510a59189528852c8c289c4296460c4a214b23023514a5908110881ac960ca44296528452214b25032910a59181168852cab10312a560e0a18952b02860c4ad5810616a54ac0810713856041838952b01022952b5910206244ac18143122560c0a18513b03022130ad910e46144ec0830382276148c18513b06070c289d8181129856c8a1031aa76041818d53b02060c6a9d81020e354ec0a1030a25606081831230a440c0815830286040ac0818302246040838d52303022510a19522062548c1814312a460429189523020c0c4a91810206144cc0c1030204614081894230e450c4a118302062508c0d103128460e0a1894230ac40c4a518142862528c0e1031294614a918942306158c4a11818a462508c0a5231294604281894230a0c0c4a118306862508c0a3031294604391894230a460c4a318303862518c0a183129c6040d1894630a442d4a11830216a508c0a10b5294604295a942302040d481185220e2708c18147138460608389c2302841c4e51810a0e2708c0830713846040c389c6302043d4e11808114a910c8810312046148818902306050c48118142062428c085231204614081850330e450c281981a2061c0cc0c1030a06615881850330a548c2819830ac6140cc0a5230a06614181c5033060d0e2819810e47140cc041884c0a6548c1850730a442c281985220e160cc181470b066042838583302040c6819852206350cc181431a866050818d43302148c6a198106063408c0408b440c6470452206321062910b1910a460418c0a2068114681183418a342881e0451a0460d0228d0408a400c14204502061250325102190c4090260d25088460864a2e423043220c2d08000664890220d0b205811068d122c088348d8920441a24cc90220d0a625811069418181000060d0c08000466090620d123448310685182c1883408c920c41a102060c4000d103020000225420040a3148c080001811280102aa10302000040858940003022110001083108c0008c089440004214462000210620182094a1948810ca5088440c646045a205321123914a19083108c18c8220481146811034489348c81a0441a1440f0220d026268110681183418834112391421908114801028a20481316811824098b46151c0895850204044a4181020225206081011290284080894812206000a2350c8442964a0442214b21c22110a592c1908852ca54a8442964a2742214b2192a110a594a5118852c942c8c4296421546214b210a2110a59283908852c8618844296422d42214b210e2310a59044190262d2508c452964a0462294b21023914a595220e254ac2508854a964a0642a54b23022152a590c110a952c844a854a96421446a54b21023152a5914206146ac250884c2b64a0642615b21822130ad9089509856c842884c2b6420c42615b21022930ad908110b956c840885ca86528442214325032110a1908110a950ca85230204606044260432b4a2110219181908810c9d1430604606881810230ac50c085181c1108830c8f1030614614a91810230e558c08118189508810c8c5230204615a91810a30e0d0e08118386870c08c0c3038204605181c1023061d8e0811818e470c08c183430204605181810a30306211821908711a810ca4188440864a0e422043230625102190c3108830c84388c40865c8e1810630ac60c08718307870418c081a3020461c885a102303042d08118562168428c1830bc204604395e102302840c00104522160408c1810b02046060858302302062c083187228e0608c0c08c45086468838382307051c1c11852a0e0608c185470304604183818230a461c0c3183038e0618c2910f430460c087a18230a441c081181060f0408c081070b0660c0a18502306070c08318081948818c8220ec114683103428a3408a1a0471a0891c8a18c88187030460419181000020c2c080001021e060000c107070000215462043220d0e080000c110083048810f02000020652204325932910219289948810ca910382256148838182b01062118259483108852c8228481316822452214b26051c4a9581020e0448c2d0884408642044220c32a1c8e081181030e0618c083038004104081818230106215a219102060508c081830a066050818503302050c08118302860428c0e103060460409181023020e0e081184a9508810c845a84608641102408004088100440a4a1188a10c9408c4508646046a284321c221106191c1128830c942c8c4086430c4230c3210e23182190895088000844a80408244083894000583291061930286046ac185230225604391c112b06051c0c15810606000a20d10306256062918312b030c0e1895814607044ac2910b42256060838312b020c1e089581030e044ac0830382a56020442254b23040c389581c3060408c0c10b4604605181c10a30106215221908114a918c881070b046020c42705328c81a0451a2440d0228d0262681146940810102103040808108142040408409103000410110660883408a120461a5220e0600024088400814a04420040a9422100205281908010285088440004224422000294221100012819088000a910b420000c085a100003440c1800018a460c00028303820000c1a1c1000010320102090815008104a5088040824a064020412088120040610206a4000081230300004183c1000050321103192440d0220d060c8440c643045220c32a448c0895830386044ac081a3022560c085a112b02841c089581021e044ac2408844296411066098b42881604c5a046090662d0228481396860818952b02060c4a95808310a952c8810b0a276060818302b02042d08918122060408c0408944086440818302302860c08318102c60408c0810382046020442304322840c005044a110a910c8c08854886430442a4c32112a15221908118a910c881031a8460e0a1830230ac40c0851810e470408c0810f430460304420040a2040e2800008310880008428ac408644081811ab0204ac0895810616844ac0408804292440818113b0102a110219102560408c08307830460a0642a4432a440c281984a1109814c8408a4c0a64408181073020c8e080001061704000042884400042046020412112a11031938286044ac091830225605085a112b02042d48958106070448c0408a442c6440c5a102303060c18118102068408c2220481106840838982302148c281981811080102a8103020001c8a181000021c0c08000102060700029102022520c0a10112902060c0010452206000a2181430005107081831ab020e0c08958464090262d1224481316831024098b40989204c5a0440d0262d0220491b16811024499b42040c28000522060418c0a204811068118240883420c2e081181820e0608c0408a04082440c18513b02840c0800012a060408c083030004104085a142302040e28118182061c08c0810302066040818900002141c0800014306046ac0c288c40864e081810000a442c080005220e040000810312a4604081810a302040c08318182062508c0810b0a066021456206322141c08958081129810c842884c086440838512b018229103193021604000040884c2b64c2a18102302060c2831810206042ac0528844086420562204322060c68118089109810c881070300004085a10000a450c0800010306040000812b0200007083810230088124641a2c1109810c8c10302000020462294b2e450c08118302860608c04088441a6420442204b22140c001041028e040000830312846148918100002058c0800010206000a2081070305614881010210a440c00104302860008204188452864b0652204325032910219244890220d1810202042060452206329422910219083148c10c88183022c6020c52206323022d1021910a46040000c0c944086420442e043210239102190c4090220d24188460864a0e42304323022110a59181168818c8c189460864224522043210629183196a1908810c8c4a944086450a1811ab06050c080005a1128810ca830382256148838112b020c0c4a95812206044ac3914302256040a18112b060d0e089581028e044ac1814302246040818942b02140c0895830286254ac0852312a5614881811230a440c4a95810206040ec0830302256040858112b02840c289d810206354ec0852302246050a1810a302948c0895810e06044ac0810302a56021442204322040c1895812a06044ac291030a2560c0a18512b02148c2895808b108810c840884c0a6558818112b06150c0895814206254ac0a10302346068818302302068c083181020e2508c1810b4204604181c512b0a0c0e081181820e0c08c24088440864e08181023030c0e181180a9108810c8c523060460c1a1c102302842d085185220e0608c181030204605291810a30a442d0811810a468408c0818702046040878102302140c08118303860408c0830b42046041c18102302040c08800089108a50c8a18302146011024098342460c08118081109a50c964884408644081851230102211031908111a810c8a1030a04604181c10330112291031910a461408c081071a046148818502302041c4a958281948818c8a10312946042918942309422910319181128852c8830302000148818942306050c4a11830286140cc08103020560310242883410621102191020e0408c0c08844086422442204322042c08118502060408c0830302046150818102302051c0811810a0e0608c38103020460508181023021c0c08118083108852ca912302046030442214b22840c08d5810206144ec18523020460134240883410a2310a59081148852c88183020c6011026488342040c68118182060c4ac0810b42256070818102300881a0441a081109852c881830225605102c0883408c120c41a08110a952c844a8442964a0642214b220c0e080004a1108852c881030a0660b0442204323040c18000244090220d08102022520131240883418221106190811088000a320481106820462284321022010209522060400004288c408640000000000102215221908110801028408a4408641103408a341022130219081108a50c8810702000040858100002040c0891810246040000810702256040a18100000881204c5a14206044ac0418846086440818512b0302251021910206254ac181430225604181c112b0a440c0895810204040840852302256060818302302840c085181020e0608c140c84408644181c10230112a110219102168408c2508844086440818002082060c08118081148818c881030a04604081894230a440c0811810a460408c1814302046020442214b2088120441a10206040000810302256020442204322040c08118
private def zz87n1 (v : Nat) : Nat :=
  match v % 4 with
  | 0 => v / 4 % 2
  | 1 => 2 + v / 4 % 8
  | 2 => 10 + v / 4 % 64
  | _ => 74 + v / 4 % 4096
private def zz87n2 (v : Nat) : Nat :=
  match v % 4 with
  | 0 => v >>> 3
  | 1 => v >>> 5
  | 2 => v >>> 8
  | _ => v >>> 14
def unpackRuns : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n+1, table, data =>
    let i := (table >>> (11 * zz87n1 data)) % 2048
    let p := (zz87n0 >>> (41 * i)) % 2199023255552
    let d := zz87n2 data
    List.replicate (zz87n1 d + 1) p ++ unpackRuns n table (zz87n2 d)
end L652.PrivateCertificate
namespace L652.PrivateCertificate
def laneWord : List W → Nat
  | [] => 0
  | w::tail => w.toNat ||| (laneWord tail <<< 64)
def laneMask : Nat := 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001
def rowDiff (p columns j : Nat) : Nat :=
  ((columns >>> low p j) ^^^ (columns >>> high p j)) &&& laneMask
def checkRows (p columns : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | j::js, seen =>
    let d := rowDiff p columns j
    decide (high p j < 64) && (d &&& seen == 1) && checkRows p columns js (seen ||| d)
def simdOK (n : Nat) (ws : List W) (p : Nat) :=
  decide (p % 4 < 3) && (if n=6 then skip p == 6 else decide (skip p < 6)) &&
    checkRows p (laneWord (goalWord (p % 4)::ws.drop 6)) (List.range n) 1
def simdStream : Nat → Nat → List W → List Nat → Option (List Nat)
  | 0, _, ws, p::tail => if simdOK 5 ws p then some tail else none
  | 0, _, _, [] => none
  | 1, minimum, ws, p::tail =>
      if p=0 then sequenceChecks (fun c => simdStream 0 c (ws++[value ws c])) (next minimum ws) tail
      else if simdOK 6 ws p then some tail else none
  | 1, _, _, [] => none
  | n+2, minimum, ws, data =>
      sequenceChecks (fun c => simdStream (n+1) c (ws++[value ws c])) (next minimum ws) data
abbrev RunsPacked (b : Nat) (x y : W) (n tab runs : Nat) :=
  simdStream 3 b (raw ++ [x,y]) (unpackRuns n tab runs) = some []
end L652.PrivateCertificate
namespace L652.PrivateCertificate
private theorem zz89n0 (ws : List W) (i r : Nat) (hi : i<ws.length) (hr : r<64) :
    (laneWord ws).testBit (64*i+r) = bit ws[i] r := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    change (x.toNat ||| (laneWord xs <<< 64)).testBit (64*i+r) = _
    rw [Nat.testBit_or,Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [Nat.not_le.mpr hr]; rfl
    | succ i =>
      have large : 64≤64*(i+1)+r := by omega
      have top : x.toNat < 2^(64*(i+1)+r) :=
        Nat.lt_of_lt_of_le x.toNat_lt_size (Nat.pow_le_pow_right (by decide : 0<2) large)
      simp [large,Nat.testBit_lt_two_pow top,show 64*(i+1)+r-64=64*i+r by omega,
        ih i (by simpa using hi)]
private theorem zz89n1 {ws : List W} {i j p : Nat} (hi : i<ws.length) (cap : i<6)
    (good : high p j<64) :
    (rowDiff p (laneWord ws) j).testBit (64*i) = changed p j ws[i] := by
  have mask : ∀ t : Fin 6, laneMask.testBit (64*t.val)=true := by decide +kernel
  have lowOK : low p j < 64 := Nat.mod_lt _ (by decide)
  simp only [rowDiff,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_shiftRight,mask ⟨i,cap⟩,Bool.and_true]
  rw [Nat.add_comm (low p j),Nat.add_comm (high p j),zz89n0 ws _ _ hi lowOK,zz89n0 ws _ _ hi good]
  rfl
private theorem zz89n2 {p columns js seen}
    (h : checkRows p columns js seen=true) :
    ∀ j∈js, high p j<64 ∧ (rowDiff p columns j).testBit 0=true := by
  induction js generalizing seen with
  | nil => simp
  | cons j js ih =>
    simp only [checkRows,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
    have bit0 := congrArg (fun z : Nat => z.testBit 0) h.1.2
    simp only [Nat.testBit_and,Nat.testBit_one_zero,Bool.and_eq_true] at bit0
    exact List.forall_mem_cons.mpr ⟨⟨h.1.1,bit0.1⟩,ih h.2⟩
private theorem zz89n3 {p columns js seen}
    (h : checkRows p columns js seen=true) (t : Nat) (nz : t≠0) :
    js.countP (fun j => (rowDiff p columns j).testBit t) + (if seen.testBit t then 1 else 0) ≤ 1 := by
  induction js generalizing seen with
  | nil => simp; split <;> decide
  | cons j js ih =>
    simp only [checkRows,Bool.and_eq_true,beq_iff_eq] at h
    have overlap := congrArg (fun z : Nat => z.testBit t) h.1.2
    have zero : (1 : Nat).testBit t=false := by
      cases h : (1 : Nat).testBit t
      · rfl
      · exact False.elim (nz (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h))
    simp only [Nat.testBit_and,zero] at overlap
    have bounds := ih h.2
    simp only [Nat.testBit_or] at bounds
    rw [List.countP_cons]
    cases a : seen.testBit t <;> cases b : (rowDiff p columns j).testBit t <;> simp_all <;> omega
theorem simd_sound {n ws p} (width : ws.length≤11) (h : simdOK n ws p=true) :
    packOK n ws p=true := by
  simp only [simdOK,Bool.and_eq_true] at h
  simp only [packOK,Bool.and_eq_true]
  refine ⟨⟨h.1,?_⟩,?_⟩
  · apply List.all_eq_true.mpr
    intro j hj
    obtain ⟨bound,lowbit⟩ := zz89n2 h.2 j hj
    exact (zz89n1 (i:=0) (ws:=goalWord (p % 4)::ws.drop 6) (by simp) (by decide) bound) ▸ lowbit
  · apply List.all_eq_true.mpr
    intro w hw
    obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hw
    let cols := goalWord (p % 4)::ws.drop 6
    have cap : k+1<6 := by simp only [List.length_drop] at hk; omega
    have ind : k+1<cols.length := by simpa [cols] using hk
    have equiv : (List.range n).countP (fun j => changed p j (ws.drop 6)[k]) =
        (List.range n).countP (fun j => (rowDiff p (laneWord cols) j).testBit (64*(k+1))) := by
      apply List.countP_congr
      intro j hj
      rw [zz89n1 ind cap (zz89n2 h.2 j hj).1]
      rfl
    have cnt := zz89n3 h.2 (64*(k+1)) (by omega)
    rw [equiv]
    dsimp only [cols]
    exact decide_eq_true (by omega)
private theorem zz89n4 {α} {f g : α → List Nat → Option (List Nat)}
    (imp : ∀ c d o, f c d=some o → g c d=some o) {xs input output}
    (h : sequenceChecks f xs input=some output) : sequenceChecks g xs input=some output := by
  induction xs generalizing input with
  | nil => exact h
  | cons c cs ih =>
    cases step : f c input with
    | none => simp [sequenceChecks,step] at h
    | some o =>
      simp only [sequenceChecks,imp _ _ _ step]
      apply ih
      simpa [sequenceChecks,step] using h
theorem simdStream_sound {n min ws d o} (cap : n+ws.length≤11)
    (h : simdStream n min ws d=some o) : checkStream n min ws d=some o := by
  induction n generalizing min ws d o with
  | zero =>
    cases d with
    | nil => simp [simdStream] at h
    | cons p d =>
      cases ok : simdOK 5 ws p
      · simp [simdStream,ok] at h
      · simpa [checkStream,simd_sound (by omega) ok] using
          (show some d=some o by simpa [simdStream,ok] using h)
  | succ n ih =>
    cases n with
    | zero =>
      cases d with
      | nil => simp [simdStream] at h
      | cons p d =>
        by_cases e : p=0
        · subst p
          simp only [simdStream,ite_true] at h
          simp only [checkStream,ite_true]
          exact zz89n4 (fun c _ _ hc => ih (by simp only [List.length_append,List.length_singleton]; omega) hc) h
        · cases ok : simdOK 6 ws p
          · simp [simdStream,e,ok] at h
          · simpa [checkStream,e,simd_sound (by omega) ok] using
              (show some d=some o by simpa [simdStream,e,ok] using h)
    | succ m =>
      apply zz89n4 (fun c _ _ hc => ih (by simp only [List.length_append,List.length_singleton]; omega) hc) h
end L652.PrivateCertificate
namespace L652.PrivateCertificate
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream000 : RunsPacked 96 0x5555555555555555 0x8888888888888888 564 0x16c2b05e0b21542904e06a1741b8540b41802e0580ae17c150650c81a8348731261b4318720de1c4370ab15a2c84b0a60f22c41c8450680c80581c03c1203a82e0620e80982c0501880a81402203c0800e02409c0600900e0200500604801000800 0xc80e80130480008d01d00740018242a01200e8020003008740401004006400d9e022004c120002d407401d0006090d8082c0240150040006580802008006801b0c048040100140052e0029c17a2bc0792f247704af011002f2f011002405e8028400c20ea568028400c201e117808801300085a5208e6010bc02068042d00ad011002609001c4102290110026090001017aa378546d4ac0e151ad2abc044009824000601a4bc10a402338040b0083a8102c023280578088013048001a8054018cac044009802301e000d402a0016017a00a10030812a4819007080220c2528028400c20ec83a15a401c203a107445a022004c002078001805400180047601158088013048000c02a000c1200bd00508018402520120ad200e101d0804a402422f011002600103c000c02a000c0023b00be56085201174020b8041b4082e0116d030b8041b40836015e022004c120006a015000b412402002c948088013004e03c001a8054002d004e1d8009000b805a8028400c204a9206401c2008811a4019204415c101aa40440098240006015000609201000180456c8aa1914d330a864514c89e19135330aa64150c8969905432bc04400982400060150006092010001804002115a0ca36190d341915a248344746c260d1151a218344146c268d04c1a1fa3413068420d5a022004c12000300a8003049008000c020032006c00aa404400982400060150006092010001804006400d02140114a0881f4282200412822050f592822850ec0a1ca16010286e850d40a19a160142802050050a00814310283e85 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream001 : RunsPacked 97 0x5555555555555555 0xeeeeeeeeeeeeeeee 534 0x310b716c2d4620a01322f44f8981482c05d0b41462a8548b91661ec560af12e2b85c06c1442784e8a81382443b8a70ce144260530960901f84f0861402384607c0ec1e82708406c100190340880c01603a07c02802 0x1011201904089022d00d0024019824320200200200240254028025f001000609000126020b000c004800182042a020020d00440048024f010140100050014a848103388808900c8b800a705e6af0194bd518c2abc0340184bc034015017a0121007082f97a01210070807845601a00ac03a2e8a10450208821045d0822e845b008b2811d08402a403401582400042045201a00ac12000202f2457048aa8982c1229a257806802b048000c02897b2278644d4c8e83e191d9912c32bc034015824000600900492f00d005600740780018024019015a01210070811a49d900b083a203a5a8048401c20069003042900b080f8400c22900d005601d03c000c01200cc03a01a0115806802b048000c01200cc1200bd009080384035201a0852016101f0806a403422f00d005601d03c000c01200cc03a01a011c9880a9181522028aa2228444348c0a111d91104223b2302a440508ab00d0056090001802401982480400456806802b003603c000c01200cc00d80340068011014a01210070811a49d900b083a203a907641d014203608055201a00ac1200030048033049008008c022f0107e0041ea0142e0041da010720041ba0142e8040b80106a8040b8012b00d00560900018024019824804004601000ccd282a850540a0a858a0a8a50c40a17a16130285a850ac0a14a1613428260509d0a098142502a900d0056090001802401982480400460100004002800c95806802b048000c01200cc124020023008000200140 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream002 : RunsPacked 101 0x5555555555555555 0x3333333333333333 640 0x602d81a0ac1780f8590aa0582904e06a1740c8370a81683005c0441602b85f05406c328640d41a43986c03a1b4318720de1c4370240721141a0320160700f04805c0c41d0130580a00a81402203c0800501c0480600900e0200300a00401000800 0x801142d400bd00a1022006c1200c00a100ad020402a408802a000c00b002a402f402c406802a008000800a002c402f402f4080200800c84c00b500bd00bd002002c00a12002800a04017a0142808801b048000800a14017a014480e803a000c00a2000a24016a0400146806802a00800284028d005e8052602008020012004800a3c017a01498090428016800500149808000810052601d11e45510e00a5407707347515347306870052a02200560e00a5404400d003a00a2a8018400420e20a8028aa00610010807840a00a5404400d80042905046f15046d00856010340214804280295011003609001ac2402010052a022006c12000200754691554670a8ca9581c2a31a543802950110036090001806107045f150425008ba0102c020da040b008b6010e00a5404400d824000d402a00b20a00a5404400d801f01e000d402a0016002a00a2a8018400420429206401c200882b82a00a2a8018400420ec83a13a401c2036107440a00a5404400d80040f000300a80030008e80022030052a022006c12000300a8003048007401455003080084025201209d200e101b0804a40242070052a022006c0020780018054001800476015414114c54109402288041500832810540227a061500832810640214014a808801b048001a8054002d049008009a0a00a5404400d802301e000d402a001680230ec00480054005401455003080084085240c8038401101f48032408825801900240802950110036090001805400182480400060102b2248ab223864454cc261910d32208643f4cc269904c321ea64130c850052a022006c12000300a8003049008000c02000e9a905d130ba243b0b24171521c8243744c22090d512198243144c22890441217a24110483a090a00a5404400d824000601500060920100018040064009 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream005 : RunsPacked 195 0x5555555555555555 0xc0c0c0c0c0c0c0c0 436 0x4816c2b05e0b21542904e06a1741b8540b41802e0580ae17c150a253aa714da9a0e64b41c8450680c80581c03c70d4f02e06204c0500202a0500781001c048648110180200384800c01000800 0x1b80c800b0480009301900340018243600a00680200030087c0040120100f0006ab808800b048000bb0150054001800d0874041e00a0068020006a680802008001e000f4f012083400b6000d19001520c516202c988a2b8158808801396808800a031400c200210552d400c2002100b08c40440058004252f04530084e0102402128057808800b04800a208115808800b04800080c4d13c1a26a3605068968d62022002c12000300925a08420111c0232020aa0464044500b101100160900025006802196808800b003602c00128034019018a0061001080ea4819005080220825e8018400420ac82a11a4014202a105445e022002c00205800180340018004560116808800b048000c01a000c1200b500308008401d200e08d200a10150803a401c231011001600102c000c01a000c0022b007e5a0842010f402088041340822010ed030880413408260162022002c120004a00d006609201000e4bc044005801f0160009401a00cc00f856001c0022017a0061001080ea48190050802203690064811037400795808800b048000c01a000c124020003008d48321d090d5120b829064123b9482e2a43304862899d090bd12168242b44cec48e84852891d09 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream006 : RunsPacked 196 0x5555555555555555 0xfcfcfcfcfcfcfcfc 406 0x160ac057eaf95eabc576ae84bab9570add5b2b5568acd592b1330ac157aae55aab155aaa552aa049aa754ca95522a3544a855029f32e71096957282558aa9542a64342401b1fe3c0740de0d21b03286a0c81cc16009 0x4f00d00160900092e02002002412090118800aba01a002c003840025d800200010000a001421d0107802802a008000a9a1038001d000a01d3c04820541028c804a90626b1019cc451940ac4034018cc4034005016a02a1013080898a0c2105f0801845a01a002c03a0197922e8245b4481e16412bc03400582400570408ac0340058240024062a8aa1514d2a068510a89e956201a002c120013009a01190846421198119286642119060896011240233023223a044500ad00d001609000980540016201a002c00c803001300a803202d405420261011483a07a4034200882197a082103f0800a40041ea40ec2008800845e01a002c03a01800980540198074014022d00d00160900098054001824018a07210370804a40241aa40cc2008804a402422d00d001601d00c004c02a00cc03a00a00c49882e9105c220b8442f17442d088569102c14844274884a1108d22058214883e115a01a002c12001300a8003049008008af00d0016006c0180098054019801b0028009002202f405420261011483a07a4034200880ca41d90740b080ea001cac03400582400260150006092010011804 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream008 : RunsPacked 288 0x5555555555555555 0xaa00aa00aa00aa00 539 0x8e17e2ec6505e18e22c3b0be0ba284630c518426c30066096354680d41983046786107809c1c84d0920ac028330e80dc1a8400620d0170300641041c0440500981782d04a0781181c0240400702105401001801 0x64034015000b4102340340110004011800498016000600102c00163e0022200080058009d3c03401500660812e0021c0340110004009cdc05401182040058a005800180040b0005a780084e000400c4004e2e0029c179abc0652b54630aaf00d002f2f64610c8be195e01a00a802e97806802a00c80bc104c021080411008b6520826010bc02088041900ad00d0054019812a04883a2006100903401c204c91480505e80055806802a00cc10202b4459088ae11155230fa457806802a00cc10300a65e0826010840208804174082e0107c02bc034015006604e81220e8801840240d007081324520140ca01100512f0109e004268010968050ea010920040e8012f00d005401982060110004011ca4034015006600b40ca01100170000805a08260108402088043540a34091074400c2012068038409902501e90050083e814a81220e8801840240d0070813204a03c583a208a0140e8042d400aa40340150066081804400100014002ac034015006600ac0ca01100170000a00ac02f04130084201044021aa052a04883a2006100903401c204c80a80f48028041f40a74091074400c2012068038409901501e2c1d101500a0740216a042b2b04130084201044020da041b0083e8106c0e8041b40836015e01a00a80330274091074400c2012068038409922900a065008800b800050254091074400c2012068038409902501e2c1d10334812840150274091074400c2012068038409901501e2c1d1033480a8300300a0c50a06a1423428868508c208142304a0692508cd287e050f40a1da160d42872050340a1ba140d42c1a05 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream009 : RunsPacked 289 0x5555555555555555 0xffaaffaaffaaffaa 343 0x3a05b0ac2186889511a164528550a4138450851002404488c0a8168600c319a1e03f87a1281f4150841242204187e0b821c2c08f0ae2084085f014090228680d61c0250020260440a8070520200781400c02c06000 0x1005006400d000504028900280a26120024021900d003440005230815040ab2022002c0123a004b50100100120014217019c24014019003400151c02401001a002600134d0045040a001100028b804a705e8af0194bc518c0aac0440184bc04400501782068040b008be5ee8ba1d16d3a02bc04400580540f2d2459048ae891503c12a404400580047401541022901100160011d002405ec8a619145320484f0c89a9956022002c0023a004c025978084900211d008544500215804218012f01100160011d002601900412f011001600fc3a004c032000201782068040b0087a819581024022a021d8b007490384a00eac0e4206e920440d5206610314802a40440058054740098064000500a88005e56022002c0023a004c0320002800440179a168342b46c0868528d09c1a12a3606355808800b00a8e801300c8000a01512008cbc0c1080303e80c2a0e8030ac0606c01856030a83280c0b8032b01100160011d0026019000140022401a002a := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream010 : RunsPacked 291 0x5555555555555555 0xcc00cc00cc00cc00 425 0x48240b61582f0590aa148270850ba240449990a81680f01c0c0718ac05c38a204f40581d23c4f380a072114700221b23486c0d70680401700f02a0380902d04e03015833060008088080280182f80702e03400800 0x37009004609000044c0240090026010011d01024010019c00024200080005040200015701900460900157600480024001280010864041e0220048020000a88083a008005a002d4f012080400ca000119015520c596203196a230845880c80159880c80220314044201e105f2d4044201e101308c4064011822501c0a03814070280e662846050850a068292f545d0a8569506c14855780c802304800b60811580c802304800a80b49164122ba2619048aa8962032008c12002b00a662e8a21d13d3b0b8744d4e8961d62032008c12002b00480249680c8023008e04c00ac01200e80c501108078411521304070080e0101c02038c820f8041d4080e010340da4064202e10432f4044201e1009480481b480c8405c201211780c8023044a02814050280a05014c4508c0a10a140d026005600900760884050080a01014020298820f8041d4080a810150213804414081a024008b40640118240056009007609005a8088403c202a90150369019080b84055202a11880c8023044a0181403028060500ccc508c0a10a140d02600560090076088403008060100c020199820f8041d40806810fd0213804034081a025007a8d09405a360b15a128340b068760d0e41cd0dc1a1aa360b068668d0c41a17a360b468160d := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream011 : RunsPacked 292 0x5555555555555555 0xffccffccffccffcc 312 0x1c70d81b81382225c7ccf91f13e044cf79ee0c27b4208d63d87acf51e90525082004d0923c44388f1c60dc408e91040d4190570b00c409804 0x1b808009008640482446024122b09001208081c064004c008000bf01500560900017e009800f4000c124b0120100400ec00729e0020090081b800d45c04560c4d620198140342c068580c92c068500c00838a188156806800ac5007080a23100d000100179882168042b0080a015a01a00280200149780680008019006405e8038405920441908015601a002802000300894888488c48884889724270484a8911024122312b403400500400060100096201a000200110011a004400880c5007080b2408833204881098a00e1016403c0284199024403c22d00d0001000f8001800401180041d2f041b008320115811503502048040d008a80af00d00140100015008004c12002b008ac03400500400060100098240004062082e01054023b023a05a040900816011d811d015a01a0028020002a010009824005601d := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream014 : RunsPacked 299 0x5555555555555555 0xff00ff00ff00ff 353 0x540902d8560bc1642a85209c0d42e83206e1502d0600680240780a0721140f00b0380b80a011020054070120180080380800c01000800 0x140201d8013a04280900140900010040813a046809003406090011204e81320401004064002e0048811e813a048040106400880207010a04e81004012005c00880201013a040e012002c120002205013a041602a00a8003008c86c24160202801a008008c020d013a042a0200802000a80054211011e810b809048801c801110a8028003d021500a48e972428085c037031464b8a1a81418085c024004c1400b17009001400e8068aa0e883220660e8008aa0e8832200210280097009001600104414101c5410c40209804070082201060217009001609000bc00680274085c024005824000400668062e685a0d0ad1b01834294683010b804800b048000c0138382028a8212804230080a010250202804210085010b804800b048000e8034007c1400f170090016003c008001d0068002800e8068aa0e883220169206400c200880e82a0a9541d106441590541b48018402420a880c004b804800b000802000600d000600115 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream021 : RunsPacked 393 0x5555555555555555 0xff000000ff000000 168 0x240b61582f0150b20502a95b2881483b013018028070120721147a84a004200040060ba01000800 0x6e01a004c120002540401004000d00326c0480401000d002a8400401201064015ae01a004c120002dc00b000580018054432020f0090064010015a202008020004800254c048254009400a99001520b4d6201196921082588068001988068012031401c200a101f31401c200a101d08c40340098004012f041b0080601064020080578068013048002e8045601a004c120002042888ec2c894a220a0a814130288871411028e8288c28881e85 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream022 : RunsPacked 394 0x5555555555555555 0xffffff00ffffff00 152 0xa642a8510988a424844428800a81bc458f521e1d80b05206a13808007 0x170014812a004010f80800924048240040035180280240202801ad402400182400147800a220121001a00d109800a281058008408006d1010030020000800054c04823400540069900552024915091504d122a1495a02ad08cc08cc08c97041100ad00900058804800203141d1044403cc5074411100d08c402400180140b2f140902888280e0511055e012000c120023008ac02400182400140 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream035 : RunsPacked 579 0x5555555555555555 0x4444444444444444 169 0x1001c060060140140480404800401000 0x9901c1c8110e022008022008802200880298121812204c812202866400c1214a1b0a1a0a1a0a1b52e400c12000bd822980a2010018240014010001000300330408012000c12000a0080c00609000500428107401d002601004001824001401018008003048002802240800c80008001004080182400140105800c12000a009100b00084800200a802a000c12000a0083c00609000d004a8 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream036 : RunsPacked 580 0x5555555555555555 0xdddddddddddddddd 81 0x38050100300300a00800800800 0x140018004240010602a006c12000a340640190016090180950020008002000a3010140100090026780a801b048002b301100440058004436020900d007401000192020280200120048d0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream039 : RunsPacked 585 0x5555555555555555 0x5500550055005500 130 0x500d1170940a82801609e0200900b01e0300200700201801000 0x900a50108ec08228103c50e40085206a240b0cb520482720040090e28e828c82e400801200a8606c91a206c81a200e1005080184c8010024005004e801002401500406002004800a008100200020006085003400100240050040e002004800a00890220088022006c02028002004800a0081c014001002400500468 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream040 : RunsPacked 586 0x5555555555555555 0xff55ff55ff55ff55 78 0x781400c0280400c00800800800 0x202802403a000d408501a00cc12000bd00ad012004800b000880c04c8101401001100443809d0030408002000e40f42a02001a00ac12000b90217010202400900160011320408 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream045 : RunsPacked 97 0x8888888888888888 0xeeeeeeeeeeeeeeee 984 0x4408c3bd778eeddd3b9770edddb3b5768ecdd93b1760ebdd73ad758eadd53a9750e9dd33a5748e8dd13a1740e7dcf39d738e6dcd399730e5dcb395728e4dc92ca722e41c7b8e71ae31c5b8a712e21c3ac758ce19c2ac5588e11c1b82702e01bfb7e6fadf1bd80d05ab35662cb5924c9642c34448851021f396358019612c04cc671020f6368798771c2298588ad164258558790ea18813824 0x24b83524b83340029002049018400d2070100018206010a0240090026080d0006e811080844011004401120440112040300b4a128140514a3a1c0428010505c009385c1aa170023c25c19820052004010a0041400c06420022c401d240e4c0c403840152540850020b00810078003c001e820340018a00302c018a001000400180428010580480210240204804401120440112041b408ec088020d806a0428010580408010d0351a00870041868560d03456801fe340d4681a8d003d8681a0b6a0428010580408010034480850020b0081002006801d9003b97217800e732006f0e42f0c801ae64380850020b0081002006c000670ea8018cb50b4005f95002d86a1685400af2a0053150e02140082c020400801b00c80004f0e02250020b000e08010036019005401a801824401458018302348108407c20012c4a006054200a2c00c1800479000862000fc405420301128010580070400801b00c802b004800ec2a20383101c00379101c1880e110019c8800bc44005722120027110602140082c020400801b00c802b048000e0204180850020b0081002006c03200ac120022007010162810160011c0202c10202c008003f0080036008002f00a0b0020009c020e02140082c020400801b00c802b048008c0058493088290007c48002c24110520007890001848fe09044123ea2411048f6090e02140082c020400801b00c802b048008c000801e40c044a00416001c1002006c03200ac00c81500230002001100250030488028b003060469021080f8409d244c8058409101909400c0784014580183077483a841cc201e900f0e2900b08378403c20301128010580070400801b00c802b00482a00460004004c012368480850020b0081002006c03200ac1200230002002609001a80181308028b003060d6906908338404d2026195201610630809a404c20701128010580070400801b00c802b00482a00460004004c01207a018420120c02524124c06c0484014580d8302b482f841742012900904c805840910094804a40240c0428010580408010036019005609001180010008a0920100101808940082c0038200400d8064015802902a004600040022802901e801300048012801824401458018302348108407c204e9226402c204880ca4099026416c2404280105804080100360190056090011800100130490080090080dd1653a0683d0343a2b8740d07a06a74550e8a69d074288744f4e89a1d12d3a0e8494e88e1d1153a0e874180850020b0081002006c03200ac12002300020026092010012010010c9284a850d0940514a1a1280a09434143614410287e858140a1ea143b02872858150a02814054280a050dc0a0c042801058040801003601900560900118001001304900800900800e800a03d00200850020b0081002006c03200ac1200230002002609201001201001d00140 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream047 : RunsPacked 192 0x8888888888888888 0xa0a0a0a0a0a0a0a0 462 0x902d8560bc1642a85209c0d42e8370a81683005c0b015c2f82a0ca190350690e624c3a93d0da7943906f0e21b81c8450680c80581c03c4281703109004c160150280440802801c0480780c01201c0400601401000800 0x17806803b0480009300d00740018243603a00e8020003008740480401005401a54c0640098240005b80c8032000c123f0090064010001804860200802002a0028016179abc0672f246504af00d00272b00d002405e8018400420c65680184004201a117806801300084a4e08c20109c02058042500af00d0026090017cc4034009824000405e88ba1116d23038445948af00d002609000180572b0421008aa01024020ba0409008a6015e01a004c120005a01100512b00d0026006c068002d0088004805e80184004203a9206401c200882793a0061001083320c8469007080b8419117806801300081a00060110006001196201a004c120003008800304802b400c2002107641d08d200e1017083b20e88bc03400980040d000300880030008cc0269582108044b008220105502088044940c2201055020a80578068013048001680440025049008008e4e01a004c00f80d0005a0110009400f86601d001100bd003080084075240c8038401101b48032408822978068013048000c022000c1240200030089d510c2a20a560f0a87e950f42a1da560f4a81e150e52a0785578068013048000c022000c124020003008002609405428320dcd286a050640a09808a198143142c0a050bd0a168142b42c0a850140a14a14050282605 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream048 : RunsPacked 193 0x8888888888888888 0xfafafafafafafafa 622 0x532a614ba96382a554a293524ef948a9051ea394693d51879945a8a512a1d43285508a0ca012c32c1dcca90c27e3ec9f1522163e87f0ef19239c7a0e20de18c3886d134124370720900e81400a 0x290025003040a40800904800810d088108b001e801002100402220220088c089d08ae42140060810e0030409400e0036090009280182041800c1025002000e0007000b0485003040870018206200434001c002801b00810030408b00182072214005001520060811e003040f400890018207a05b213a662701645800c1020405b2b010b20042c00608102032001216003040810190001000d05641590540a0361009080c81a0ac82b20a81415c20121013082c00608102032000280445505202a24054480a2a40544ca60248a20902513028243800c1020406400050480048d0018204080c8000a09000900581825406894040c2780309a80d0680309680c2c0060810203200028240026003425d0743a0ea74490174470e88a9d8443a233a218743800c102040640005048004c001800741c006081020320002801f0260026000c00e801d05641590540a0361009080ca411015201a1011082081a0ac82b20a8140fc201210074803805480684044200e103800c1020406400050088260026000c00ec0221e86800c102040640005048004c001801d824003a0ac82b20a8140ec2012100f4807805480684044201e900f081c00608102032000280441300130006007601101d001e0b423468468b4463444390134370686a8d110841a231a19834463444214688868b0018204080c8000a0900098003003b049008006870018204080c8000a005c0980098003003b002e01d001e003400682b20ac82a0501b08048406520880a900d08088407d208c922202e0102002100304081019000141200130006007609201000d8040505452c1605054528168502c0a808a188142f42c16050b50a158142942c168502c0a1b0a058143800c102040640005048004c001801d8248040036010005 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream051 : RunsPacked 200 0x8888888888888888 0xf0f0f0f0f0f0f0f 379 0x1d00a0b61582f0590aa148270350ba0dc2a05a0c01702c0570be0a8120090721141a0320160700f02e06204c0a8140200380901101e0300400700c01000800 0x4602640c802b0080009901900240010244202a00480200c02230120100400740f9680080240208e07ce40440058240005d8088022000c12430050044010001804920200802000e801152c045e0c4d62021988a208158806800d97806800a02f400420e881f96a0021074401c23100d0016001064b410f4020d8040500832016201a002c12001d80015e01a002c12000203124390486e8980c121aa258806800b048000c01997820a80431008c8081a8119010bc02bc03400582400054012005a5a01a002c0078070002a0090064062800841d101149032006100440acb5001083a208c8220ba400c201a104446201a002c00203800180240018004440117806800b048000c012000c1200bd001083a20ac82a0ba400c201a1056415117806800b00080e000600900060011180292d04150084e010240205a04090084a818240205a040b00b100d00160900015004803304900800465a01a002c0098070002a0090066004c2300a80048062800841d1011490320061004403d200c9022042 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream052 : RunsPacked 288 0x8888888888888888 0xaa00aa00aa00aa00 521 0x582385f8bb1941786388b0ec2f82e8a118c3146109b0c01986a8d01a8330608cf0c20f0138740721342482b0660dc1a8400620b8180280641041c0340880981782d04a078118120380400702a04201001801 0xbc034019001541024c03401100040118004c802a0006001054002a4200222000800a800bd4c034003400ac102dc03401100040005000b90034008c102004bf015000600118c002a006c2f35780c256c8be195e01a00565ea8ba1516c2abc03401900592b00d0064015017820980421008220115c9c104c0215804110081a015e01a00c802b0294051074400c2012028038405922500a0acc40340190056081015a22a84453088a29187d22bc0340190056081804f2f04130084201044020ca04190083e015e01a00c802b0294051074400c2012028038405922500a0350088026958084b00212400847402875008450020740097806803200ac103008800200864e01a00c802b0052035008800c8000402f041300842010440219a054a02883a2006100901401c202c81180f48028041f40a94051074400c2012028038405902301e2c1d104100a074021497806803200ac1030088002000280055806803200ac01380d4022003200014013805e08260108402088043340a94051074400c2012028038405901701e90050083e815280a20e88018402405007080b202e03c583a202e0140e804294084e4e08260108402088041b408360107d020d81d008368106c02bc034019005605280a20e88018402405007080b244a01406a01100190000a05280a20e88018402405007080b204603c583a206290230802a05280a20e88018402405007080b202e03c583a2062901706006014178240b4485a8902c5487e090b41481602487a090ec121ca260b4486e0902c121aa240b44c1609 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream053 : RunsPacked 289 0x8888888888888888 0xffaaffaaffaaffaa 315 0x120282d85610c3444a88d0b22942a85209c22842880120224460540b4300618cd0f01fc3d0940fa210490881061f82e0870b023c2b88210217c228680d61c02502402601c0880f0100540a02900c02c06000 0xc048014050f010012010b80c88000a3e002a0815340400160011100355808008009048bc014010019000300019d8008800c803180185f415aaac05f2b145d02a7015005b2b0150014056081a0102c022c93a22b844554880ab015001600903c9cd14c1a28a34240f06a7015001600111004f2d0150016001110034056021340084b4020242480108e8049c05400580044400d80452b74430e8829d090fc3a133a1e875580a800b00088801b0002003b27015001600e422006c000801d01582068040b0086e8189810240212021a8300749038ba06610314902205e902d0815a4014e02a002c01222006c000801d802445602a002c00222006c000801d80044015b214864274cc08c84a9908c3210a660665380a800b00488801b0002007600912007c9c0c0e80303680c120c80304c0605c01826030482a80c09803270150016001110036000400ec002240320022 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream056 : RunsPacked 294 0x8888888888888888 0xf000f000f000f000 352 0x2d85610c4584a88d0b21542904e114200460540b4100209f82b03808a8780fe4c03d0940fa50c409f73ec7d4419f404804c0480a08a364690611b035c2504d25e4500a0110640d41b82d09201c040150b805c068060180c002000 0x66012004c02048021300900010024020297009824002700158f808002c0204a002b59005002601064011b802800a0090080aec02400500290024024309000a4004e0025003617babc06f2b246d04af01d006b2b01d002405e8058401c20d256c8ce19195320e9780e80130081195a0c6100708078408c22f01d002608c4044404440444058a2108441f4880a1900613101d0026010640100560217c0085d4020242d801012804bc0740098041900480592b402c200e100d082ba403420aa11780e8013046202220222022202c51084220fa44050c8007a000400a65603a004c028864003d0002000d00bd00b08038413c203a9099a021a021a021a025cd06c1a0ca3406344d00a1009484cd010d010d010d012e68360d0651a031a25a3449068080a11c1282e8585c6c51140a21a1415082050fd0a1e8143b4282a5e03a004c020c8024000801201015780e80130083200900020048040500b504c088540336a09854390a86e0aa86a150cd2a018310a806950bc2a08a540305a95 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream057 : RunsPacked 295 0x8888888888888888 0xfff0fff0fff0fff0 241 0x1882c050238fe85e3f87ec4585d1e47e8fc8603341703b01e2620e40e0841242204187e0920480802e01c0d007801 0x66024121b010012010f8480089c04824c200a00080240200b700500340090048047a002006c00882f00243010009801105a002b0026178abc0292f442708ab00500092f401420061158028022004a5600a0088003805e8028400d20a846560842010240200a04012f0050044012010093100500440120100405e683e0d03c1a3b1a3a07a355802802200900803003a5e483609064123312322b120b82558028022009008030068032ad0050801a4834200290744191178028022000e80540600d00240054ac0140110007400580600d0024003402f401420069054130800a41d106641502cbc014011004804018034009004804 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream058 : RunsPacked 299 0x8888888888888888 0xff00ff00ff00ff 246 0xa0b61582f0590aa148270350ba0c81b8540b40780e06006803c1203908a0b8048140220400a80e0240300380800c01000800 0xdc0240050240004c804801a030488c040100401c00224a024020080e000f09010680080240088003ce40440058240005d8088022000c124100500440100018049202008020003800d53c015683125880665e2862055e012001a6201200280c5064415102f2d419105441d118804800b0008165a085a0103402028040b00b1009001609000ac006af00900160900010179a148342746c020d0951abc0240058240006008cc41084020f80403008128100c020e8058804800b048000a8034006cb402400580190e8002a00d000300c506441510174903200210044054b5064415104641104d20021009082223100900160011d000600d000600111 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream065 : RunsPacked 393 0x8888888888888888 0xff000000ff000000 152 0x901416c2b05e02a1640a0552b6510290760261281200e0240e4228f5018200040060ba01000800 0x1980680130480009501004010002c00122e024020080058001c7c004012010090003ac80a8013048000b301500540018247601200a80200030091c040100400250011801b0acd5e01095920f8257806800097806801202f40142006101d2b40142006101b08bc0340098004755820c804010082e011d015e01a004c12000a97806801304800080128cc2c8b4a0981411028885140f028c8288c28881a85 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream066 : RunsPacked 394 0x8888888888888888 0xffffff00ffffff00 127 0x530570d21bd0aa144262290921110a1742a08b21e3d43b05206a13808007 0x1a8088c048a02412002002230050048040500173500900060900056e01300021d8247600300021000550090c041d00400130008801b03491503d122a0c95602ad088c088c08895040d00ab00900057804800202f4191034402cad06440d100908bc0240018014072b1405028682806050d055e012000c12001abc02400182400140 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream079 : RunsPacked 582 0x8888888888888888 0x8080808080808080 62 0x90140200380601801000800 0x28088013048000830110034001824160120068020003008c401400982400051802800a000c122b0090014010001804660200802003200a890 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream080 : RunsPacked 583 0x8888888888888888 0xf8f8f8f8f8f8f8f8 145 0x1e0b80983a00c0302400901401000800 0x5c03a06f422202240411ec00c2002104840803a0498d090d09020200802001a128cc2cc84b1a0a1a0a1a0a04040100400240050a0200802001200284082200ac12000210200802001200281010040100090014a00401100440018240810040100090014280802008004800ad02002a008802000300900802008004800a240401004002400588 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream081 : RunsPacked 585 0x8888888888888888 0x8800880088008800 52 0x70120280400601801000800 0x500d00260900010601a00c800304834040100400540116600a004c1200028c01400500060915804800a008000c02030 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream082 : RunsPacked 586 0x8888888888888888 0xff88ff88ff88ff88 131 0x1e01c0300402603000800 0x1875a1c01404440444a1110105010e01a000f602880a20700d0004005ea4142414241427a0340010040017a034001005400503b01440592244050601a00080200130080068002006c1200130068002008004c0264068002008004c020400800200080130490068002008004c020100d000401000980428 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream087 : RunsPacked 596 0x8888888888888888 0x7777777777777777 54 0x20038090c40300302401401000800 0xc001001b0480008b01100440018242601a00e80200030086c04010040064005c812010040090027200401201014015c8 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream089 : RunsPacked 192 0xeeeeeeeeeeeeeeee 0xa0a0a0a0a0a0a0a0 459 0x2416e2d85a8c41402645e89f130290580ba16828c550a91722cc3d8ac15e25c570b80d82884f09d59c2703bbc10ce2442805109814c2583f28a11c2303e0861081d83d04e06c1001a0320600b02203a07c02802 0x380080030480008700100340158241e002006802001300844048040900010032a58096c04400d0056091b8080080080090083404004c2b45580c656c8c2195602200be4e02200c80ad007080284174ad007080284044227011006601d16c1083e8107c1083e2208b20115d023a0e80538088033048000ad01100660900010159a2a8345346c1a0d1451aac0440198240006013c9d51342a25a54741b0a8eca892155602200cc12000300680239580880330032044000c01a00a809d00708028408d24ec806841d101927401c200a1009480481d48068406c2012113808803300e822000600d005601d024b4044019824000600d005609004e80384014201e900f03a900d080d8403d201e115808803300e822000600d005601d025008a4a40344c068900c44910c1220a2603048ec487e091d8980d120182538088033048000c01a00ac1240200129c0440198017022000600d0056005c04a003c004809d00708028408d24ec806841d1019483b20e80610172b01100660900018034015824804002601138083d0020ed00a150020e5008370020d500a154020540083340205400938088033048000c01a00ac12402001300800624940b428260504c128420504c0a09808a178142d42c16050ad0a148142142c168502c0a13a140b0284a05 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream090 : RunsPacked 193 0xeeeeeeeeeeeeeeee 0xfafafafafafafafa 694 0xeafb5f63eb7d4fa5f42d87cef99f2ace7c8f8df13e17c0f7def3dd7b8f6ded3d97b0f5deb3d57a8f4de93d17a0f3de73cd798f2de53c9790f1de33c5788b45e1bc25b2b5d6b2d55a8b4d692d059e2aca2a2b4548a51422744c89512223338588889191f229c7b0911382744f0a80ee10c2781d 0x40224080c040048040044812010011a004001820400148ac014c1e020701000c0cc206210044059006b0080904810830210810a40013f60d012010012011200520480400422024020020b012010010a0400340150066081681201001078090080091020080020008003000a4090080083404824e807c003e001f54090080099020d0120100132079a16a3400461a001feb47809008009d0001b1e8856910cc220017ec40026223c04804004e80d00001e3c04804004e80d004400e08ec08e8423bd08360106402000b1608ec08e8423bd08001c04000602058045809008009d01a008c00287f2520ea241d048fa090745491ec123ca24170ee090e024020027406802304080124404804004e80d0046081002401ea862951d42a39bb51c42a37a54150da151ad2a3c04804004e80d0046081002601a45590bc3217bb919c3232a64130c619185322f8645809008009d01a008c102004c02a00ba1e0240200274068023002202c004c02a00c801c11d811d08477a106c020c804294080a05d020a804130082216080e8101c1080ee842d008560101d020385b408b20115c02038043809008009d01a008c00280b001300a8033000a01c4404804004e80d004608100260150066081005823b023a108ef422a80453008128102428a044f0089a0102502048045809008009d01a008c00280b001300a8033000a01d00120940304a01a160314a01a140354b018a512c0a24814034280611d0a2281443028068500d0a0185809008009d01a008c102004c02a00cc103000800a3c04804004e80d0046003c0580098054019800f00e80090001800608ec08e8423bd0836010640214a040502e810540209804114080a810140a02078402022409008009d01a008c102004c02a00cc103000800b000e408235408253408275408410020fd0080d07a00413a010760041ca0101a0950083700208d0080d0020e0240200274068023040801300a8033040c002002c002006a := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream093 : RunsPacked 200 0xeeeeeeeeeeeeeeee 0xf0f0f0f0f0f0f0f 379 0x1d0362dc5b0b51882804c8bd13e260520b01742d0518aa1522e45987b09e0903385109814c2585008e0f82103b07a1181381a0300581102003207c02802 0x2301320140005008008a3200a008800a0488400100220081b0088c048040d0043000c95803600480406c003282027101500440058248e0200200200240215012c808bc18aac404131643f0cb1015003d2f015006405e8028400c2076628028400c201611680a8033004872810350206a040d042068b821b80435408482a015a02a00cc120002002af0150066090001018a2198443148c12110bd22c4054019824000600b4bc50ac0a14a1424130284c284e055e02a00cc12000300880129880a8033002202c000c02200280b500508018405d244c8048409101131401420061007480381548048404c200e11680a80330048160006011001600901c008bc0540198240006011001609005e8028400c2002900102a9009080984005200211780a80330048160006011001600901d00464b47636763474b9a108341f46ce8684c683a0d098d9d8d1d0d5a02a00cc120003008800b049008006b10150066003c0580018044005800f00e8001001a02d4014200610174913201210244045204c8123a201e := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream094 : RunsPacked 288 0xeeeeeeeeeeeeeeee 0xaa00aa00aa00aa00 580 0x2d491922aee5da311222435d890920aeb4808fd1f2ea47a8f0b19cf476ba51d2394707391ba3646aba2134255ceb9972ae45c709211c223a05a4331660f63581e1cd46810c8f91e2d04748e16705646c199460981441c02605e0b41283e04619c1e85307612c108270f808002803 0x7415107440a52408741510050802204c8023502908032008488148aa44881220488139d05441d10014902bd004401100440190048a00c5401003e2b555a0005d3ba00131d5682a20003d58080016008000e0095a0a883a20000d5a0a883a200211382138042500846010849c11fc023e8047b00822014e82a20e8800a43a01a000600070006a0058016005800b001b04360240896a0a883a2002920444e0a1e40287700a1d50281f0e6814ad05441d1001490320665608e2011bc02368041340826011ac02ad05441d10014884034000c000e000d400b002c00b00160036086c048114802841a4dc8760c43233a643b1164650c8c619185320e85f4c8ba1916c329d05441d10014903200a10044194e82a20e8800a40d408a40142026106444e084e01094021180421409d00d0003000380035002c00b002c005800d801701e80090083e814201a000600070006a0058016005800b001b002e03c5001800dc0481d008b25682a20e8800a4819005080220cc8029d05441d1001481c81148028404c20cc81c8456084e0109402118042140a100d0003000380035002c00b002c005800d801501e80090083e814a01a000600070006a0058016005800b001b002a03c5001800dc0481d0086a8115c12021480c4c087260424062455048a609145130312198240424314480c480a74151074400521d00d0003000380035002c00b002c005800d821b012045200a1013083321d00d0003000380035002c00b002c005800d801701e2800c005e80170004a44201a000600070006a0058016005800b001b002a03c5001800bd002a0801c048243113d222683112c22248442d0621580a22384445088869106420a442d0887e110f5220ca441905611 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream095 : RunsPacked 289 0xeeeeeeeeeeeeeeee 0xffaaffaaffaaffaa 329 0x905b8b616b0a0d31371402645e92113e260d28a41602e85a1a434628c5542726c5bc8396e240688b693529051c548b9166684b60fc34067cb5af55e8bcd792f15e0bbc3101d0a03386d132236118238190300680b02208407c25802 0x17800c002740040035006a308352400f0401e000f40389e800eb0150034019804056e022006800080098042a00680370bd55e03797a236845580a80359780a802200b4015200a0c015d80e8406c20d25ee8ce1d1953a22b0150046000c3192102d020582102c541184022fa04190ba014e02a008c020e8002c40540118041d000405e68b60d1651a0b857068aa8d5602a008c020e800300a65ec8a21913d320a84d0c8969912432bc0540118041d000600d00472f0150046004c3a000c01a00c801d0054802830057603a101b0822a400c0ca405c202a101324a04a1609428122a2886051050b20287e850f40a1da1444e02a008c0018740018034019800302af015004601074001803401980405017808390020dd00a40041aa0106600418a0149009580a802300061d000600d0066000c0b005e4a40744c0e8901c5490b41215a24110520909d12128242344822085120f825380a80230083a000c01a00cc0202c0008009 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream098 : RunsPacked 294 0xeeeeeeeeeeeeeeee 0xf000f000f000f000 354 0x1b09e2dc5b0b549c6989b8a01322f49089f130694520b01742d0d20a315459cb444e5ee9349b16f5f641cb712089a5ae2644b8951262402404407525a4a4929209312523e4788e91c48e4909192228c5997d1485f28dc280e034e3386d82d0320602381606c2a42101a03e03410002 0x3300900260091d00149804803200068040d3603b0081d80000dc01e8e802801b00005c39401eae802eb000400c8001a01035f8048032008801da0108807200dc2f012f00009ab24001e12bc00100000b560008009017a05610290800075ee8000c747f4e84e5600080098041f49281e8503c1281e2a28f6051e50a20ee0556000800982350dc2a1a854330a8625aa85e150b52a028740056200080098041d0014056c8ea191cd32128710c8de995e00080098041d001601b4ac0c358030d280c20ce00c240619401978002002608d4370a86a150cc2a1898aa178542d4a80a1d001601900632f0004004c0308740058064000c02b40ac2052105f0813a41608460103402058042105040714303a041f0083a8106d022e8050812a41e08460103402058042105040714303a041f0083a8106d022da040d008160142c92d0251b04a3409153457068aa8d06429834514689e0d1351a0c9580020026010740058064000d0081abc00100130083a002c03200068040d00b105c098444b3620b84415088920a888e11115220884308882910542209a441107e91 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream099 : RunsPacked 295 0xeeeeeeeeeeeeeeee 0xfff0fff0fff0fff0 234 0x138a92d516c6245a8b31622bc568ab1503dc538a51462844f5f819c299a22905a4b694726a0f82603d07614423005 0x33012090d8080090088c24802f2501201001000b020020024123b005004400d00480432025300b400f85e2af00acbc90a412ac01401d5e802841d1158028012004e5e00a00480048056802841d900104a68654045604231504210083e011581155600a00480240200b100500240120100405e883a1106c2201a4403032915600a00480240200c00b979a0a83413068cc68c8228d03c1aac0140090048040180440195e802841d9207082b2006106445600a0048004a000403008801a000e5e00a0048004a002c03008801a000e015a00a1076400406841590030833200202cbc01400900480401804400d004804 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream100 : RunsPacked 299 0xeeeeeeeeeeeeeeee 0xff00ff00ff00ff 245 0x4e2dc5b0b51882804c8bd13e260520b01742d0518aa0ce06c0e8530a21302803e08e0ec1e8420400580c81a03007c02802 0x64085021900500240900013200a00886c1223010340101100078880990240206604444040810080080240079d80890271005004400d824860200200200240213010012e804ad0622b100c4bc90bc12bc01400b4c4014009018a002107440acc5001083a2006116802801300a852484074080e084071704270084a811502c02b401400982400040115e00a004c12000202f44230884291814220fa4578028013048000c00e989a0d83419468a8120d158d05c1ac4014009824000601100153100500260034018001804400d016a0021074404d24ac8028415100d31400420e883320c816900508048419116802801300a8060006011003601519 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream107 : RunsPacked 393 0xeeeeeeeeeeeeeeee 0xff000000ff000000 145 0x110b716c2d4620471402645e85114721c0d81d0480641d83d60a27c4c07b0a00800d01803e2c002802 0x3300900360900052a02012004000f00068d809008138003d00163a00a00900806a002d7404ce0120088004a091f808008008009008540400dc2b257804a5668460d5e01200425e01200680bd00708028407cbd00708028407422b009003601106c928ac28a84a2a5450640a0ba14441502ab00900360900055e012006c12000a00423a023250806084010082608403010401008ec0cc8082281 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream108 : RunsPacked 394 0xeeeeeeeeeeeeeeee 0xffffff00ffffff00 126 0x49592828e49c9248490648c9091e6948e48e91b23245c8a912902440a61606a8b809814827c1f016 0x6a0223012280904800900ca1009400900811a0197a02670018054214123f01201510012010a80801b8010d0843604360434a10d0107c5086f42ac004693225488f520e82558008022bc004009017a0361019080b97a02a101308088456002004c00780d24a05a140904a038a8a0281403428021d0556002004c12000abc00400982400140 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream121 : RunsPacked 582 0xeeeeeeeeeeeeeeee 0xe0e0e0e0e0e0e0e0 65 0xd81d0300881201902c07c02802 0x12002000c1200022c00400500260909800800a008008c02150120104401d0d3a002009008321b6c04ce02a0028013048fc040040040048042202170 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream122 : RunsPacked 583 0xeeeeeeeeeeeeeeee 0xfefefefefefefefe 84 0x3b07a2a80d0a90440641001802c07402802 0x4008024102d018028400c200c8021a190085020404800a000282408102042811207400500640158036001160234089024020f01068095012002802304810211013a04004004004804804e8 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream123 : RunsPacked 585 0xeeeeeeeeeeeeeeee 0xee00ee00ee00ee00 139 0x7610c548180321181101a04e05801005 0x340800c0048013044c1d850020008002000c00211d80085022000280741401168ec004004088d00341400588ec00400400403b00100100100108803400400400402401b00100100100100900128008008008048076002002002012005800832200882b2412002002002012000d001001001009004c := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream124 : RunsPacked 586 0xeeeeeeeeeeeeeeee 0xffeeffeeffeeffee 23 0xf81802c06402802 0x700d420120028003049102530125804800a000c12030 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream129 : RunsPacked 596 0xeeeeeeeeeeeeeeee 0x1111111111111111 34 0x6204807402802 0x1c040048031204289098081024023b010040100810212040481012012005c8 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream130 : RunsPacked 289 0xaa00aa00aa00aa00 0xffaaffaaffaaffaa 966 0x2744e70f9399734e59c938e7113e9c33811a4df9bd3766e2e59b736a6ccd89aeb926b4d59a934e692e39a334267cce99b33265cca99332263cc698b31261cc29833025fcbe97b2f25dcba9732e25bcb696b2d259b1a9652c6584af95d2b594b284b6c9d93325648c8d911cd642c818fb1e63ac718db19630c5d8b3150ccc518983c4b4964ea9384b095d2b2554a894d292514a093c731d43a60cc891ac2e85ccb91712940e01302f04a0b41182119033c6a04b1a03306a8c10e800c2202a 0x82048a214a2b038003fea001f6004a202880a202890a202890a002c10b002e801420400482400480480402b912644990e02400b0080202804074081601007bc081268058014012005806400d0741a1282d1d41683a0d1dc0e83f068ee007986803be36a048016019807104a12814241424143b428ce05007594a1232a142502d409002c033006800a1000e70026000718037c0006dc034a0006bc03300ea0026005001400580480160198034005803003082ca400c00d310019e19018400c5800cb103b080184a812005806600d00142041202400b00cc01a002840804a8861cc2a39854018e9a8860061ca886005f8a802ee54016e2a3185401662a00af950e02400b00cc01a00284090002ac741b0e8464f41b0ec360fc3a0d8014e3a00a39d0d1bc11874013e3a009b9d004b8e83012005806601c4002840900a80378444106200934c441088da0047c88da10422008b911ac2230844010e22008391003f888d6110e02400b00cc01a002840900a803a0001ec3802e801601980340050800d00a803a00880250370a2103516032104f082a8b033080c840c42001dc2a001cc1508006f2c07420be106916001ac407420019c4054203006d002c033007e00142003402a00e802303304050080e0102c0207a040d0080a810a4138090018c4809002c033006800a102402a00e802304804487a08d121e82b4487a09002fc48ce8919512129290ed123182423048c2890bc2fa241809002c033006800a102402a00e802304900489484c20016cb000ae20ba1000a658004f10009620011c404d2026105d081c017400b00cc01a00284006805401d004606e080a0101c02058040f4081a0101502148270120550048000438041c85b04085b002001f840839000ee01072001b8020019c02001780215c00800560085940200138020011802000fc020b4001b8042b8010005c0107012005806600d0014204805401d00460920090040000260c017400b00cc01a00284006805401d004601240aa00900130000800a81b8001e206a2c06420002c41545819840642062104d48bc101402038040b0081e810340202a042102281024205e919820280407008160103d020680405408420445080e0112c0482d08000705e8050048016019803400508120150074011824802401000050080c017400b00cc01a00284006805401d0046014c0aa00900130000a014c00540dc28840d4580c8413c208e2c0cc203210310826a45e080a0101c02058040f4081a01015020f81140812102f48cc101402038040b0081e810340202a041f02228407008960241684125208e0a9018400c580003102b08018b07f083e841ec200690030815a400c3c8400d2006101802e801601980340050800d00a803a008c0cc101402038040b0081e810340202a042904e0240aa00900130000a05e080a0101c02058040f4081a0101502108111420380445408420102502f04050080e0102c0207a040d0080a8107c088a101c0222a041f04205809006 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream131 : RunsPacked 291 0xaa00aa00aa00aa00 0xcc00cc00cc00cc00 2009 0x2c5ce0a8470bf1763282f2674cc6d0d9b311162f932a640ba3c8d9106660cbe789d9142318628c23626c1318604c453130a6065c1992fa5e9e097277cee9db3b275cea9d20143b09b314624a698830e760c3185274610c19af4ba608c09802fe5f0bd9122f45e4eb9ae2eecb4788d6658cacbb32a25652c951292205f8be92835a0e49e13b1da424829042ea4e4eb0f72103b0730eb2f040c140ea24e3746e0bc1be0783e01c0680b80901004e038658380780cc1583005e0041282604208c16803 0xbd10242207844154881e04c4d10242206844110883291001d994415088229180858884e3e88269100838040c4427088010e9a2048440f0884e91124099ba2048440d088221103522069ea2138441148c4e1109d15102c068440b0884e110021801715e125e8803fd387801f60797a204844492f15003dc15003cc152f44090881e110077ab44090881e11054221c040602010102014001080d0025a04c8102004015000401580562041a02000a000801a004f4082c04080d80410a801a0082060215010d8086404420204028002006801224043602000a00a800b04e91010d808100200a8002000e8007130113808101b00e80e003401d32022b0118808a4046e0204a188a59d46288cc01444842104223a04750823a02233005000446b4744505a3a8cd1d0d1d0d119802800200688123b123b123a4491d091d091d2a474247424742445600a000801a00488ec01400100340090046ea862150842a1e854294a88ec01400100340098057080a0ea161d27141f0286a0506d0a2a81447600a000801a004c02a00288dc0140010034009805400500426e800dc7400663a2d874005e5dd00158e8009c745b082dd00758e87e1d0bc3a178bba00e71d0fc3a1787445626007182612409801bf098580a940a605c14014001003400980540058001b617845e88121103c220aa45d8028002006801300a800b04e882498a2048440f0882a917a00a000801a004c02a002c13a2026114e1a006b81a001f81a0069c1a16080e0101d020383820f8210940219a04210083e8100678032c4001fc1a5e88121103c220aa45d8028002006801300a800b04e8809a44018ebc4400c304400bf04400bb844ec0c002300c2380308a00c1da030a200c27a03002dc01662002be11002ac112f44090881e1105522ec014001003400980540058274404d2206844014eac6400a3064009f064009b864cc0140010034009805400582744004bc32001d83200498325e88121103c220aa463d001b8e800cc745b0e800bd8ba002b1d00138e8023e74404d220684411088022d5a2048440f0882a911e02a1016a00b40c014001003400980540058274404d22068441108832110e020b012204080100040010017140814040801005400180010e0baa041a0200020008002002ee8105808100300020c030002002e060215010005c002e8217000b8380864044202040280020068012240436020402802a002c000805110111808000802a0008003a001c4c044e020406c000807001a008232022b0116808a4046e0224a188a58048c511980288108420844740802420802011158028002235a0084505a007f4668020d0041a233005000400d10290051200a244b11240104802090045480209004120082445600a000801a00488f401400100340090046ea862150842a1e854294a88ec01400100340098057081283a858749c507c0a1a8141b428aa0511d8028002006801300a800a23b005000400d002601500140109808003e0080036008002e0085917010004c010003c01001ec46e0a0040280100a0040280140a1f40283f40a00423b005000400d0026015001600ac178408152814c0b8f8028002006801300a800b0002014008ec01400100340098054005800100a8047600a000801a004c02a002c00080504080203804074080e42083e084250086681084020fa0400163d8a111d8028002006801300a800b00020145002237030008c0308e00c2280307680c2880309e80c0007003b94184d00611d8028002006801300a800b000201450020001cc46600a000801a004c02a002c0006f014500200060042602000f802000d802000b8021645c040013004000f004006b804158204000b00400070042c840815080b5005a3a00a000801a004c02a002c00080514008001a000422d44090881e1105522e4014001003400980540058274404d22068441108832917200a000801a004c02a002c00080514008001a00040089d1024220784415488d3643068861268e868e85a3b1a00030d1fd1b3a202691034220884419488d3643068861268020d004168028d0001868fe8d8045684a0d0033c68020d104438080c0402020402800200684a40814040805001d000b043aa81068081002003a0004000d009ac8108808004800ea008c12008206020f010d8084c044202040280020068012240436020402802a002c03202888088c040801005400100074003898089c04003601901c006803264044602310114808dc044943114b328c511980288908420846604650823202233005000442b6642d19ab4350684a0d0dc24d190d190d115802800200688148cc48cc48c91246424642464a91909190919091158028002006801223d005000400d0024011daa18854210a87a150a52a23b005000400d0026015c20283a858749c507c0a1a8141b428aa0511d8028002006801300a800a237005000400d002601500140109b23c864770c872191d45d91cc3238a6446e0a190143202864050cc0a1f40283f40a1911d8028002006801300a800b00560bc2240a940a605c7c01400100340098054005806f00a0047600a000801a004c02a002c03202a011e8028002006801300a800b00c80a081004070080e8101c84107c1084a010cd02108041f408da1ec5088ec01400100340098054005806405140088dc0c3201864030c8061980c2880309e80d3250613401847600a000801a004c02a002c032028a00401911b8028002006801300a800b00018c051400800180109b23c864770c872191d45d91cc32388b90ac37a646d072005f112054202d40168e8028002006801300a800b00c80a28010003403223b005000400d0026015001600ac028a004000d00560046e00a000801a004c02a002c032028a004000d00cc0246cc868cd5a3583425068d61268c868c85a331a1e8343546cc95a128346634642d1022c32a0b0d2002db458670161a4142c005702c005302c004f82c1c91d899d6a47424742474a91d091d091d2a42904836899d10009705867016002381619505859230a24230966a41b048460908c548360917c121b8a90a4120da24630ba2a433048768918c1224160e48c28908c259a906c1211824231520d8245f0486e2a42904836890e42e8a90cc121da24390521b84 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream132 : RunsPacked 292 0xaa00aa00aa00aa00 0xffccffccffccffcc 398 0x4ba7fcfe9fa7c863cfc9f73ea7ccf89ef3da7acf49e73c99ab34666cc8698612ec76ced04d04e6dcdb1b50923c46b18b05a0ac6f8400820d47703206e09818804 0x180800900834048242e02412210900126804800a0028024022900900460101300233005824001300059b808002602130009be82b25580920941f0283e8507c54511c0a9c02400556a88a1510c2aac02400500412b4044201e100d089c024005005400fc9c0240050054007402b4044201e100d488410d818d2840100802010045080a011d818040183d2d00900140150048044e8876110e4221b8440948812114e012002802a009008001256012002802a003a8035002202b4044201e100d488410d818d2840100802010045080a011d81804018334804840c4ad90bc32168642b0c80e9901c3214a6407270090014015004804004601007274044201e100d490aa4024202a100708ac0240050054007502504360634a11d0106c020c8a1014023b021381740806004604a086c0c69423a020d804191420280476042702e284230084200c32002a52012002802a009008008c020c802009d0110807840352416900908058401d2016113804800a00a800ea042086c0c69423a020d804191420280476042502e8100c008c08410d818d28474041b0083228405008ec084a05c50846010840186400550016 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream138 : RunsPacked 387 0xaa00aa00aa00aa00 0xcccc0000cccc0000 234 0x582385f8bb1941786388b0ec2f82e8a11ac66103a0640a8108aa034040dc170353146249594d31061d3182d0685644d839064104140050380480806001c0ac02001 0xcc01400500160907802801b04800c9b00500480412c00c9f012010640190066c802802200ec1233005003401000d8047a03a0090083a00ec50103401001d006401b0ac55e02495a2238457802800297aa22854430aaf00500440104ac014011005405e801840842002103f2b400c200a10010805845e00a008802b04420d804190082e01054c4104c02088040f4081a014bc014011005609004e687a0d0ec1a1ca361d46af005004401582480372b400c20421001080fa407c203a117802802200ac11083601064020b80415310413008220103d020680b401a006a2a409066090c4d48120901c12178292168242b048528909c12a24070484609 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream139 : RunsPacked 388 0xaa00aa00aa00aa00 0xffffccccffffcccc 255 0xa7f4f8ca853a7b4f29dd3aa734e29bd36a6b4d299d32a634c297d2ea5ad3a9652b4109ad3526969b4aa94d28a4f49a92d24a469a291521a4147e8f0601acd41a7a75698d2cd802304a0981782b05a6c53b1ba04200c6109b18a3182001e 0x12c04004004824c811580934048240040046a012002e00734123700900240120074008e4071002402036006f4901000742000d801b400981d81064020980411408e808ea4235804693420c80467008ca81560021282a4946334a308145f14a0b81415028ba0516d0a2c8157800802b92d154968a66b4510689e6b44d068960d1251a238344506af0010014010cbc0040050034056820840fc207a103b2b40e4206e10350800845e002002801b0374454440d088161102522038445646050060ccbc004005003609000919090c5133314cc8485e0a4826090b41215a242904e8956002002801b049004af4044204a10230807a403c2042115800800a006c0cd115110342205844094880e111591814018014012003e := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream140 : RunsPacked 390 0xaa00aa00aa00aa00 0xf0f00000f0f00000 564 0x1526a401e0582681383111c2fc5d8ca0bc4108192a1ee37c9498a312534c41874ce998da1b32201f19888b17c3a8842654c8176a3d46a8b511a52746924a1a43474da9b2a1d42a83500848ec1784ac828761e4530ee9dc00a32c6e8dc0e63981c8280240701a00e1421980802f04a0981182b0420b400803 0xcd005083a20129000660387a0e883b24e883a750005e002b107440013880d8fa00e9000463a201a101b5940142016100d480780733401420e8806841d9075ca01a100d490684035250003e3a20006c40342036006e2b052f4000bab0b0004c0b2f4014201e5612000781200058125e8028402c20001d7a00a100b0804840e0022c0072004201400d08150045a0040800801a00c801a00cc033100234004201400d0054011e8012200200ac017864015002f030012a0026c004c800a10010805003420540111a0025c004005006400582648800a3001080500340150044a800a7001004401980244400932002ac0058800af0016e0021285a2962518a02cc014042d05c1683e8d09426848680b3005003404b5090741a84a35424542454059802801a00a8086213221322128d1091109110911016600a006802a00880bb0050034015004400166c85a1905c320003191fd3202ec01400d0054011807d0084a15a162b271415028f6051e50a3b81405d802801a00a802300c800a02cc01400d0054011806400500049923a8247304852091c45c91bc123682429008f246b0484e0904412088b923482427048220901560e19c0380f00e195038580c940c61841401400d00540118064005805f022015e8028402c201291d802801a00a802300c800b0448081e5e8028402c201291d802801a00a802300c800b0448080e113ba2e874250e8b69d1668320d0651a0c839a0a82d1641a2ba34170682a8d15429804254eaf40142016100948ec01400d00540118064005822404074828820c27a03026134d0608c0181300604c140c1180309600c24a030b0108e804108453408430020840084134083f00207c0081d0020f50083b0020e50083706a010cd01831006 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream141 : RunsPacked 391 0xaa00aa00aa00aa00 0xfffff0f0fffff0f0 164 0x7d550a9f538638613b04f09d9752fc5f59832f05b536a654ba94134509b23b234c791060400f01a8410640dc17004 0x19808009008540482446024122909001308028002000802402350050036001c2a008ec006001c2002a005e8602002b0082a00a8036178aac074210040200a040119042d00af0050005792158242904ab00500040195e83a200a106445e00a0008012004e5600a0008012004a017a0e8802841991da211844210883e11075220d844194882e054098112f005000400900480456681e0d0341a0583403468060d5600a00080120090080012 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream156 : RunsPacked 579 0xaa00aa00aa00aa00 0x8800880088008800 64 0xf02c00a0700900e0200a002001 0x2804801a008c1203009001401001d8041202200900832000b3009003400182446012002802000b008a4004012010040016a0202802000200a890 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream157 : RunsPacked 580 0xaa00aa00aa00aa00 0xeecceecceecceecc 151 0xc40901e040038028270200a002001 0xb807409851985194942448080bd800840910080482801302122a108a84312021202240405004000409b121a121a121a04040500400040090a0202802000200684082200e800304810202802000200681010140100010034a014011001401000580480405004000400d0a02028020002006b40080020090080200084080a008000801a240405004000400d88 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream164 : RunsPacked 596 0xaa00aa00aa00aa00 0x55ff55ff55ff55ff 53 0x1c05407813874134038090050200a002001 0xc04400d00054120b0110014010005804280d0016090000c540040120100400142020020040074009e8120106454009e8 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream165 : RunsPacked 291 0xffaaffaaffaaffaa 0xcc00cc00cc00cc00 402 0x1216c2b0861a22544685914a1542904e11421440090112230cc8540b430061a7a19a1e03f87a1281f44209211020c3f2792b0170361e81d3640f388208a1a0358f80e03f42519132063cc710e248718e285811e320408d91b035c700d205a0cc078110040500401500c17c0380c02e02c06800 0x1c034015800464000c1c03400d003600d00c4400434001c00009c000c4c00300018080c00068601300a80666012004c012ec007048001a180068203000e15baac000469d5000f8aa701d000036ac074015015821c80437008005d3b20013190007cc80ab01d005608942d0281a050ac0a14968a0a8140d428160ecac04000b00400078041a83b0024e03a00ac0023200000d680e802b0008c8000804e68fe0d1f51a1987b068f28d4e03a00ac00232000280772b050ea01439a050621c40286f40a1b4029580e802b0008c8000a00d006b2701d005601a43200028034001402b04390086e0119d024d0270807840942046268098404520ca100b06a810cc02188046325217a262f172461048be898109175122d824594480a701d005608940902812050240a04948a0a8140d42816190001401a000a82300908048402420125280984045201290094807840852016095203a00ac0023200028034001500084809c1c2b8070aa81d020385340e1440384f40e8181c9c07401582250b40a068142b0285252282a050350a0586400050068002a08c09c201e1025081194a02610114826a412d201e102148058260124188369107c238b1074220f844170544450883a910640d8444348882110fd220c83d4882e11 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream166 : RunsPacked 292 0xffaaffaaffaaffaa 0xffccffccffccffcc 301 0x110370dab47688f9da13e27c2d059fb3c7bcf759db3966ecd599b307b6cbd966bc7b0f5d95b2964cf51e9b25645b0b606be77ce3b5d0be44ca11de1c63a4a70c810e23c4085710416014813 0xd4047202002002412010125808002c02c857002a9a80900904040048048e127d002c51058002d5c17aabc053008060840340c06684034080614414113c029c0540015e02a00080bd015080984134351024230482a22584449488cab0150006010092f411c208a10010800845602a000c0322200026202a000c0208802009488609035120b824171524410487e890441e8243b44a70150006010440120095e81c840dc200e10354803840cc22f0150006019110001401200625e02a000c01784400050048003805680a8404c205a10664191011483215a14054281e8583cd280a858141450a40a13a1664142542846050850a32ac05400180411004802401201015680a80030082200900480240202801a3a56ce868eb5a3b1b3a14d07c1a0ea3664341b4681a0d0651b331a9c0540018041100480240120101600d := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream172 : RunsPacked 387 0xffaaffaaffaaffaa 0xcccc0000cccc0000 252 0xb92dd5ba1e3b9171ee35c5b8970ee15c1b80344ca1934f8dcdb9371b7edc0efb6f6dd6f8c936d6d8daedeb6a6d2d7ade5bbb756e6dc5b74f76dada82a2703f4c70e021c4906c0d74f40b5b43676cc12c7c2800d61a0380c301a3341480b 0xcc0440150046090980a801b049003a2a02200900839800048c04804001d00200015f013380800800800900904040048240042602006e15a2bc0712f546f0aab011006d252359291a4548ce0a465048c689184948be89174122d8257808802a00b25602200a801202f415c20aa1053082897a09e104d0825841d115808802a004c094505c0a0a814130282202281e050350a05814090eaf0110054009824002d1251a0d847468362a688a0d10c1a20a343f07a8d5602200a8013049006ab40ec20721037080ca4064206a117808802a004c0a4505c0a0a814130282202281e050350a05814090ec01a006601c3302038310085e01192840500806010b40215a0429242330202804270084a8108c10a04030083e01 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream173 : RunsPacked 388 0xffaaffaaffaaffaa 0xffffccccffffcccc 160 0xb6158435d5ba974ee95d1ba173ee75cd12a2353e85914b7302a85209d72c4508510024044dca1186642a05a08a03c0601102a0500100800c01c60000 0x66003004869b001000140027c06401001aac03608dba03b00286bf01d007601d8600087400d9e01b04680461792ac0432f144102ab009003f2f009001408c0f42076ac0e4206e2c0d49819a40c4205e102d2f542b0a85295115804800b004e00cbd10942211a44210061156012002c020a800f97804800b0082a00880bc1074020da041902e01055029c024005804150046004cbd90443207a640d0161902532038655804800b0082a008c002000a := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream174 : RunsPacked 390 0xffaaffaaffaaffaa 0xf0f00000f0f00000 175 0x240505b0ac2183406b1a22544699132063c6c82d0b22947c0550a41383808a10a2003f5d80fb75d05369bac8240982a01e3482295a0a80300100702a0500b80b00c16804000 0x330100058240042600a00c80058003d001a2a024012078014400ea30100005001a13c00ed500050028ebb00040002800143002c00801d9e03b04e805615a2f0134bc512c0aac0400492b010005017922382445048865ea882150fd2a12bc04001608b43d068120d0ec1a1c989a1b834094686a01cbd10cc2218a442f00e115602000b0048a801697808002c0122a00880ad90ac3214a642704a1908d32ac04001600915004600845080a07c1083a28405008060841b0104190082e8105409804114080601 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream175 : RunsPacked 391 0xffaaffaaffaaffaa 0xfffff0f0fffff0f0 143 0xfc1c5b2210bbcdb1b5b76bba83d075dcbb6666ed20d418da905dd90b4ddc7e9c803253c4608912015014811 0x258080090480081402b3d01209001001512014af8090082afc04800300243010000c2b2c05609500ac24a330a008140104e2e2ab0055e484a095600a00465e00a00480ad021080f84074bcd06c1a0ca3475780280130080b97a02a101308088403c22b005002601d0d000d2f00500260103401000111084440444a1112864421110208c8081681024038040540a7005002601034012001 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream190 : RunsPacked 579 0xffaaffaaffaaffaa 0xcc88cc88cc88cc88 64 0x540a0130120280580601e00806000 0x2404002600d00400e8b010010012010047804802000a04c9b00d1000500540113e0020008102000d1012009017602002402430051000196003040910 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream191 : RunsPacked 580 0xffaaffaaffaaffaa 0xffeeffeeffeeffee 76 0x1802c0640580601e03000002 0x4c0031202400e8036002040c802a008c11b100b101d0092006804904800803204812012401d009204c000440190044024805a01240d80480a022012012403d009208c := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stream198 : RunsPacked 596 0xffaaffaaffaaffaa 0x55005500550055 33 0x1d01500c00c03c01000 0x1c0140050004140051a012044c020483011361020408002840480300102806850 := by decide +kernel
end L652.PrivateCertificate
namespace L652.PrivateCertificate
private def zz91n0 (a b : Nat) : Prop := ∃ input, simdStream 3 b (raw ++ [value raw a, value (raw++[value raw a]) b]) input = some []
private theorem zz91n1 (b : Nat) (h : b ∈ seconds 2) : zz91n0 2 b := by
  simp only [seconds,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_,stream000⟩
  · exact ⟨_,stream001⟩
  · exact ⟨_,stream002⟩
  · exact ⟨_,stream005⟩
  · exact ⟨_,stream006⟩
  · exact ⟨_,stream008⟩
  · exact ⟨_,stream009⟩
  · exact ⟨_,stream010⟩
  · exact ⟨_,stream011⟩
  · exact ⟨_,stream014⟩
  · exact ⟨_,stream021⟩
  · exact ⟨_,stream022⟩
  · exact ⟨_,stream035⟩
  · exact ⟨_,stream036⟩
  · exact ⟨_,stream039⟩
  · exact ⟨_,stream040⟩
private theorem zz91n2 (b : Nat) (h : b ∈ seconds 96) : zz91n0 96 b := by
  simp only [seconds,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_,stream045⟩
  · exact ⟨_,stream047⟩
  · exact ⟨_,stream048⟩
  · exact ⟨_,stream051⟩
  · exact ⟨_,stream052⟩
  · exact ⟨_,stream053⟩
  · exact ⟨_,stream056⟩
  · exact ⟨_,stream057⟩
  · exact ⟨_,stream058⟩
  · exact ⟨_,stream065⟩
  · exact ⟨_,stream066⟩
  · exact ⟨_,stream079⟩
  · exact ⟨_,stream080⟩
  · exact ⟨_,stream081⟩
  · exact ⟨_,stream082⟩
  · exact ⟨_,stream087⟩
private theorem zz91n3 (b : Nat) (h : b ∈ seconds 97) : zz91n0 97 b := by
  simp only [seconds,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_,stream089⟩
  · exact ⟨_,stream090⟩
  · exact ⟨_,stream093⟩
  · exact ⟨_,stream094⟩
  · exact ⟨_,stream095⟩
  · exact ⟨_,stream098⟩
  · exact ⟨_,stream099⟩
  · exact ⟨_,stream100⟩
  · exact ⟨_,stream107⟩
  · exact ⟨_,stream108⟩
  · exact ⟨_,stream121⟩
  · exact ⟨_,stream122⟩
  · exact ⟨_,stream123⟩
  · exact ⟨_,stream124⟩
  · exact ⟨_,stream129⟩
private theorem zz91n4 (b : Nat) (h : b ∈ seconds 288) : zz91n0 288 b := by
  simp only [seconds,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_,stream130⟩
  · exact ⟨_,stream131⟩
  · exact ⟨_,stream132⟩
  · exact ⟨_,stream138⟩
  · exact ⟨_,stream139⟩
  · exact ⟨_,stream140⟩
  · exact ⟨_,stream141⟩
  · exact ⟨_,stream156⟩
  · exact ⟨_,stream157⟩
  · exact ⟨_,stream164⟩
private theorem zz91n5 (b : Nat) (h : b ∈ seconds 289) : zz91n0 289 b := by
  simp only [seconds,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_,stream165⟩
  · exact ⟨_,stream166⟩
  · exact ⟨_,stream172⟩
  · exact ⟨_,stream173⟩
  · exact ⟨_,stream174⟩
  · exact ⟨_,stream175⟩
  · exact ⟨_,stream190⟩
  · exact ⟨_,stream191⟩
  · exact ⟨_,stream198⟩
theorem canonical_pack_two {a b cs dst} (path : Path 0 raw (a::b::cs) dst) (len : (a::b::cs).length=5)
    (first : a ∈ firstKeys) (second : b ∈ seconds a) :
    (∃ w, packOK 5 dst w = true) ∨
    (∃ prior c w, dst=prior++[value prior c] ∧ c ∈ next 0 prior ∧ packOK 6 prior w=true) := by
  have done : zz91n0 a b := by
    simp only [firstKeys,List.mem_cons,List.not_mem_nil,or_false] at first
    rcases first with rfl|rfl|rfl|rfl|rfl
    · exact zz91n1 b second
    · exact zz91n2 b second
    · exact zz91n3 b second
    · exact zz91n4 b second
    · exact zz91n5 b second
  obtain ⟨input,verified⟩ := done
  cases path with
  | cons _ tail =>
    cases tail with
    | cons _ rest =>
      apply checked_path (simdStream_sound (by simp [raw]) verified) _ (by simpa using len)
      simpa [List.append_assoc] using rest
end L652.PrivateCertificate
namespace L652
theorem private_obstruction : PrefixObstruction :=
  private_of_two_pack PrivateCertificate.canonical_pack_two
end L652
namespace L652
theorem triple_matching_exact : Realizable 15 ∧ ¬Realizable 14 := by
  apply exact_from_two_obstructions _ private_obstruction
  apply GroupProjection.third_residual (fun b =>
    if b then GroupProjection.thirdTickets1 else GroupProjection.thirdTickets0) GroupProjection.laneLaw_for
  · intro b
    cases b
    · exact GroupProjection.third_intervals0
    · exact GroupProjection.third_intervals1
  · intro b
    cases b
    · exact GroupProjection.third_done0
    · exact GroupProjection.third_done1
end L652
end PEqualNP.Outside.L_meta_652_aux

theorem PEqualNP.Outside.L_meta_652 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∃ o0 o1 o2 : ℕ, ∀ x : Fin 6 → Bool, (C.wires (List.ofFn x)).getD o0 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧ (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧ (C.wires (List.ofFn x)).getD o2 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4))) ∧ ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o0 o1 o2 : ℕ, ∀ x : Fin 6 → Bool, (C.wires (List.ofFn x)).getD o0 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧ (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧ (C.wires (List.ofFn x)).getD o2 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4))) := by
  exact PEqualNP.Outside.L_meta_652_aux.L652.triple_matching_exact
