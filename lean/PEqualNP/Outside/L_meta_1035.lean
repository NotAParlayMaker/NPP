import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Ref1035
open CircuitLowerBounds

def base : List ℕ := [0,4294967295,2863311530,3435973836,4042322160,4278255360,4294901760]
def validOp (B : List ℕ) (v : ℕ) : Prop := v ∈ B ∨ (∃ a ∈ B, v = 4294967295 ^^^ a) ∨ ∃ a ∈ B, ∃ b ∈ B, v = a &&& b ∨ v = a ||| b

def maskInputs : List ℕ := [2863311530,3435973836,4042322160,4278255360,4294901760]

def row (x : Fin 5 → Bool) : ℕ :=
  (x 0).toNat + 2*(x 1).toNat + 4*(x 2).toNat + 8*(x 3).toNat + 16*(x 4).toNat

def readMask (x : Fin 5 → Bool) (m : ℕ) : Bool := m.testBit (row x)

private theorem maskInputs_eval : ∀ x : Fin 5 → Bool,
    maskInputs.map (readMask x) = List.ofFn x := by decide

private theorem ones_eval : ∀ x : Fin 5 → Bool, readMask x 4294967295 = true := by decide

private theorem zero_eval (x : Fin 5 → Bool) : readMask x 0 = false := by simp [readMask]

def gateMask (w : List ℕ) (g : Gate) : ℕ :=
  let ins := g.inputs.map fun i => w.getD i 0
  match g.op with
  | .and => match ins with | [] => 4294967295 | [a] => a | a::b::_ => a &&& b
  | .or => match ins with | [] => 0 | [a] => a | a::b::_ => a ||| b
  | .not => 4294967295 ^^^ ins.headD 0
  | _ => 0

def wireMasks (gs : List Gate) : List ℕ := gs.foldl (fun w g => w ++ [gateMask w g]) maskInputs

def admissible (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem mask_admissible {C : Circuit} (hc : MetaComplexity.FanInTwo C) :
    ∀ g ∈ C.gates, admissible g := fun g hg => hc g hg

theorem lookup_map (x : Fin 5 → Bool) (w : List ℕ) (i : ℕ) :
    (w.map (readMask x)).getD i false = readMask x (w.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [zero_eval]

private theorem gateMask_eval (x : Fin 5 → Bool) (w : List ℕ) (g : Gate) (hg : admissible g) :
    readMask x (gateMask w g) = g.op.eval (g.inputs.map fun i => (w.map (readMask x)).getD i false) := by
  obtain ⟨op,arity⟩ := hg
  obtain ⟨op', ins⟩ := g
  simp only at op arity
  simp_rw [lookup_map]
  have htop : (4294967295 : ℕ).testBit (row x) = true := ones_eval x
  rcases op with rfl | rfl | rfl <;> cases ins with
  | nil => simp [gateMask, GateOp.eval, readMask, htop]
  | cons a tail =>
    cases tail with
    | nil => simp [gateMask, GateOp.eval, readMask, Nat.testBit_and, Nat.testBit_or,
          Nat.testBit_xor, show (4294967295 : ℕ).testBit (row x) = true from ones_eval x]
    | cons b tail =>
      have ht : tail = [] := by simpa using arity
      subst tail
      simp [gateMask, GateOp.eval, readMask, Nat.testBit_and, Nat.testBit_or,
          Nat.testBit_xor, show (4294967295 : ℕ).testBit (row x) = true from ones_eval x]


theorem simulate (C : Circuit) (hf : MetaComplexity.FanInTwo C) (x : Fin 5 → Bool) :
    (wireMasks C.gates).map (readMask x) = C.wires (List.ofFn x) := by
  let step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  suffices H : ∀ (gs : List Gate) (w : List ℕ), (∀ g ∈ gs, admissible g) →
      (gs.foldl (fun ws g => ws ++ [gateMask ws g]) w).map (readMask x) =
      gs.foldl step (w.map (readMask x)) by
    simpa only [wireMasks, Circuit.wires, step, maskInputs_eval] using H C.gates maskInputs (mask_admissible hf)
  intro gs
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w h
    simp only [List.foldl_cons]
    rw [ih _ (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    simp [step, gateMask_eval x w g (h _ (by simp))]

theorem gateMask_valid (w B : List ℕ) (g : Gate) (hg : admissible g)
    (hsub : ∀ v ∈ w, v ∈ B) (hz : 0 ∈ B) (ho : 4294967295 ∈ B) :
    validOp B (gateMask w g) := by
  have input (i : ℕ) : w.getD i 0 ∈ B := by
    by_cases hi : i < w.length
    · simpa [List.getD_eq_getElem?_getD, hi] using hsub w[i] (List.getElem_mem hi)
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)] using hz
  obtain ⟨hop,arity⟩ := hg
  obtain ⟨op, ins⟩ := g
  simp only at hop arity
  rcases hop with rfl | rfl | rfl <;> cases ins with
  | nil => simp [gateMask, validOp, hz, ho]
  | cons a tail =>
    cases tail with
    | nil =>
      first | exact Or.inl (input a) | exact Or.inr (Or.inl ⟨_,input a,rfl⟩)
    | cons b tail =>
      first
      | exact Or.inr (Or.inr ⟨_,input a,_,input b,Or.inl rfl⟩)
      | exact Or.inr (Or.inr ⟨_,input a,_,input b,Or.inr rfl⟩)
      | exact Or.inr (Or.inl ⟨_,input a,rfl⟩)


theorem valid_bound {B : List ℕ} {v : ℕ} (hB : ∀ t ∈ B, t < 2^32) (h : validOp B v) :
    v < 2^32 := by
  rcases h with hv | ⟨a,ha,rfl⟩ | ⟨a,ha,b,hb,h|h⟩
  · exact hB _ hv
  · exact Nat.xor_lt_two_pow (by decide) (hB _ ha)
  · subst v
    exact Nat.and_lt_two_pow _ (hB _ hb)
  · subst v
    exact Nat.or_lt_two_pow (hB _ ha) (hB _ hb)

theorem wireMasks_bound (C : Circuit) (hf : MetaComplexity.FanInTwo C) :
    ∀ t ∈ wireMasks C.gates, t < 2^32 := by
  suffices aux : ∀ (gs : List Gate) (w : List ℕ), (∀ g ∈ gs, admissible g) →
      (∀ t ∈ w, t < 2^32) → ∀ t ∈ gs.foldl (fun ws g => ws ++ [gateMask ws g]) w, t < 2^32 by
    exact aux C.gates maskInputs (mask_admissible hf) (by decide)
  intro gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro w hg hw
    apply ih _ (fun t ht => hg t (by simp [ht]))
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hw t ht
    · obtain rfl : t = gateMask w g := by simpa using ht
      apply valid_bound (B := 0::4294967295::w)
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | rfl | ht
        · decide
        · decide
        · exact hw _ ht
      · exact gateMask_valid _ _ _ (hg _ (by simp)) (by simp_all) (by simp) (by simp)

theorem mask_inj {a b : ℕ} (ha : a < 2^32) (hb : b < 2^32)
    (h : ∀ x, readMask x a = readMask x b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 32
  · have hr : ∀ i : Fin 32, row (fun t => i.val.testBit t.val) = i.val := by decide
    have e := h (fun t : Fin 5 => j.testBit t.val)
    change a.testBit _ = b.testBit _ at e
    rwa [hr ⟨j,hj⟩] at e
  · have hp : 2^32 ≤ (2:ℕ)^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

theorem wire_read (C : Circuit) (hf : MetaComplexity.FanInTwo C) (j : ℕ) (x : Fin 5 → Bool) :
    readMask x ((wireMasks C.gates).getD j 0) = (C.wires (List.ofFn x)).getD j false := by
  rw [← simulate C hf x, lookup_map]

def generated : List Gate → List Nat → List Nat
  | [], _ => []
  | g::gs,w => let v := gateMask w g; v :: generated gs (w++[v])

theorem fold_generated (gs : List Gate) (w : List Nat) :
    gs.foldl (fun ws g => ws++[gateMask ws g]) w = w ++ generated gs w := by
  induction gs generalizing w with
  | nil => simp [generated]
  | cons g gs ih => simp [generated,ih,List.append_assoc]
@[simp] theorem generated_length (gs : List Gate) (w : List Nat) :
    (generated gs w).length = gs.length := by
  induction gs generalizing w with | nil => rfl | cons g gs ih => simp [generated,ih]
def free : Finset Nat := {0,2863311530,3435973836,4042322160,4278255360,4294901760}
def bank (gs : List Gate) : Finset Nat := insert 0 (wireMasks gs).toFinset
def paid (gs : List Gate) : Finset Nat := bank gs \ free

theorem budget (gs : List Gate) : (paid gs).card ≤ gs.length := by
  have incl : paid gs ⊆ (generated gs maskInputs).toFinset := by
    intro v hv
    obtain ⟨hm,hfree⟩ := Finset.mem_sdiff.mp hv
    simp only [bank, Finset.mem_insert,List.mem_toFinset,wireMasks,fold_generated,List.mem_append] at hm
    rcases hm with hz | hin | gen
    · subst v; exact (hfree (by decide)).elim
    · have sub : ∀ x ∈ maskInputs, x∈free := by simp [maskInputs,free]
      exact (hfree (sub _ hin)).elim
    · exact List.mem_toFinset.mpr gen
  exact (Finset.card_le_card incl).trans ((List.toFinset_card_le _).trans (by simp))
theorem out_mem (gs : List Gate) (o : Nat) : (wireMasks gs).getD o 0 ∈ bank gs := by
  by_cases h : o < (wireMasks gs).length
  · rw [List.getD_eq_getElem _ _ h]
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Finset.mem_insert_self ..
theorem out_eval (gs : List Gate) (o : Nat) (hf : ∀ g∈gs,admissible g) (x : Fin 5 → Bool) :
    readMask x ((wireMasks gs).getD o 0) = Circuit.eval ⟨gs,o⟩ (List.ofFn x) :=
  wire_read ⟨gs,o⟩ hf o x

end PEqualNP.Outside.Ref1035
namespace PEqualNP.Outside.Ref1035
open CircuitLowerBounds
def stepN (bank : List Nat) (v : Nat) := ∃ a∈bank,∃ b∈bank,v=a&&&b ∨ v=a|||b
inductive Trace (B : List Nat) : List Nat → Prop where
  | nil : Trace B []
  | cons {s} (h : Trace B s) (v : Nat) (hv : stepN (s++B) v) : Trace B (v::s)
theorem gateN (g : Gate) (w B : List Nat) (hg : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (hw : ∀ v∈w,v∈B) (hz : 0∈B) (ht : 4294967295∈B) :
    gateMask w g∈B ∨ stepN B (gateMask w g) := by
  have input (i : Nat) : w.getD i 0∈B := by
    by_cases hi : i<w.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hw _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
      exact hz
  obtain ⟨hop,arity⟩ := hg
  obtain ⟨op, ins⟩ := g
  simp only at hop arity
  rcases hop with rfl|rfl <;> cases ins with
  | nil => simp [gateMask,hz,ht]
  | cons i rest =>
    cases rest with
    | nil => exact Or.inl (input i)
    | cons j tail =>
      first
      | exact Or.inr ⟨_,input i,_,input j,Or.inl rfl⟩
      | exact Or.inr ⟨_,input i,_,input j,Or.inr rfl⟩
theorem trace_all (gs : List Gate) (B : List Nat)
    (hg : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (base : ∀ v∈maskInputs,v∈B) (hz : 0∈B) (ht : 4294967295∈B) :
    ∃ l, Trace B l ∧ l.Nodup ∧ (∀v∈l,v∈bank gs ∧ v∉B) ∧
      ∀v∈bank gs,v∈l++B := by
  let final := bank gs
  have go (ts : List Gate) (w l : List Nat) (tr : Trace B l) (nd : l.Nodup)
      (inside : ∀v∈l,v∈final ∧ v∉B) (seen : ∀v∈w,v∈l++B)
      (gen : ∀v∈generated ts w,v∈final)
      (mono : ∀g∈ts,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
      ∃ L, Trace B L ∧ L.Nodup ∧ (∀v∈L,v∈final ∧ v∉B) ∧
        ∀v∈w++generated ts w,v∈L++B := by
    induction ts generalizing w l with
    | nil => exact ⟨l,tr,nd,inside,by simpa [generated] using seen⟩
    | cons g ts ih =>
      let v := gateMask w g
      have next : ∀z∈generated ts (w++[v]),z∈final := fun z hz => gen z (List.mem_cons_of_mem _ hz)
      have mo := fun q (hq : q∈ts) => mono q (List.mem_cons_of_mem _ hq)
      by_cases old : v∈l++B
      · have se : ∀ z∈w++[v], z∈l++B := by
          intro z he
          rcases List.mem_append.mp he with h|h
          · exact seen z h
          · have eq : z=v := by simpa using h
            exact eq ▸ old
        obtain ⟨L,t,d,i,c⟩ := ih (w++[v]) l tr nd inside se next mo
        exact ⟨L,t,d,i,by simpa [generated,v,List.append_assoc] using c⟩
      · have hv := (gateN g w _ (mono g (by simp)) seen (List.mem_append_right _ hz)
            (List.mem_append_right _ ht)).resolve_left old
        have hn : v∉l ∧ v∉B := by simpa using old
        have se : ∀ z∈w++[v], z∈(v::l)++B := by
          intro z he
          rcases List.mem_append.mp he with he|he
          · exact List.mem_cons_of_mem _ (seen z he)
          · have eq : z=v := by simpa using he
            simp [eq]
        have ins : ∀z∈v::l,z∈final ∧ z∉B := by
          intro z he
          rcases List.mem_cons.mp he with rfl|he
          · exact ⟨gen _ (by simp [generated,v]),hn.2⟩
          · exact inside _ he
        obtain ⟨L,t,d,i,c⟩ := ih (w++[v]) (v::l) (.cons tr _ hv) (List.nodup_cons.mpr ⟨hn.1,nd⟩)
          ins se next mo
        exact ⟨L,t,d,i,by simpa [generated,v,List.append_assoc] using c⟩
  have inc : ∀ v∈generated gs maskInputs,v∈final := by
    intro z hz
    apply Finset.mem_insert_of_mem
    apply List.mem_toFinset.mpr
    rw [wireMasks,fold_generated]
    exact List.mem_append_right _ hz
  obtain ⟨L,t,d,i,c⟩ := go gs maskInputs [] .nil (by simp) (by simp) (by simpa using base) inc hg
  refine ⟨L,t,d,i,?_⟩
  intro z hz'
  rcases Finset.mem_insert.mp hz' with rfl|h
  · exact List.mem_append_right _ hz
  · apply c
    simpa [wireMasks,fold_generated] using List.mem_toFinset.mp h
end PEqualNP.Outside.Ref1035
namespace PEqualNP.Outside.Ref1035
open CircuitLowerBounds
theorem paid_len {B L : List Nat} (gs : List Gate) (P : Finset Nat)
    (nd : L.Nodup) (saved : ∀v∈L,v∈bank gs ∧ v∉B) (inc : P⊆paid gs)
    (pb : ∀v∈P,v∈B) (fr : ∀v∈free,v∈B) :
    L.length+P.card ≤ gs.length := by
  have dis : Disjoint L.toFinset P := Finset.disjoint_left.mpr (by
    intro v hv hp; exact (saved v (List.mem_toFinset.mp hv)).2 (pb v hp))
  have sub : L.toFinset∪P ⊆ paid gs := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · obtain ⟨hbank,hn⟩ := saved v (List.mem_toFinset.mp hv)
      exact Finset.mem_sdiff.mpr ⟨hbank,fun h => hn (fr _ h)⟩
    · exact inc hv
  have h := (Finset.card_le_card sub).trans (budget gs)
  simpa only [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup nd] using h

theorem copyN {B : List Nat} {x : Nat} (h : x∈B) : stepN B x :=
  ⟨x,h,x,h,Or.inl (Nat.and_self x).symm⟩
theorem trace_three {B L : List Nat} {target : Nat} (hz : 0∈B) (tr : Trace B L)
    (sz : L.length≤3) (member : target∈L) :
    ∃u v,stepN B u ∧ stepN (u::B) v ∧ stepN (v::u::B) target := by
  cases tr with
  | nil => simp at member
  | @cons s tx c hc =>
    cases tx with
    | nil =>
      have eq : target=c := by simpa using member
      subst target
      exact ⟨c,c,hc,copyN (by simp),copyN (by simp)⟩
    | @cons ss ty b hb =>
      cases ty with
      | nil =>
        refine ⟨b,c,hb,hc,copyN ?_⟩
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl <;> simp
      | @cons sss tz a ha =>
        have emp : sss=[] := by
          simp at sz; exact List.length_eq_zero_iff.mp (by omega)
        subst sss
        refine ⟨a,b,ha,hb,?_⟩
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl
        · exact hc
        · exact copyN (by simp)
        · exact copyN (by simp)
end PEqualNP.Outside.Ref1035
namespace PEqualNP.Outside.Ref1035.Example
abbrev T := BitVec 32
def target : T := 4244425728
def preTables : List T := [4210752250, 4210688000, 4289396650, 3431517320, 4008636142, 4008574976, 4278059008, 4278111368, 2694881440, 2694840320, 2290649224, 2281736192, 2863267840, 2290614272, 2829582336, 2829617152]
def free : List T := [0, 4294967295, 2863311530, 3435973836, 4042322160, 4278255360, 4294901760, 4210752250, 4210688000, 4289396650, 3431517320, 4008636142, 4008574976, 4278059008, 4278111368, 2694881440, 2694840320, 2290649224, 2281736192, 2863267840, 2290614272, 2829582336, 2829617152]
private def pairPool : List T := [0, 2147483648, 2147516416, 2155872256, 2155905152, 2281701376, 2281736192, 2290614272, 2290649088, 2290649224, 2684354560, 2684395520, 2694840320, 2694873088, 2694873216, 2694881440, 2818572288, 2818607104, 2829092864, 2829101216, 2829582336, 2829617152, 2829617288, 2829623456, 2829625504, 2829625512, 2852126720, 2852170240, 2863267840, 2863302656, 2863302792, 2863308960, 2863311530, 3229663360, 3233857728, 3364356096, 3364407432, 3368550400, 3368601800, 3422604288, 3431464960, 3431517320, 3435921408, 3435973768, 3435973836, 3772776448, 3772834016, 3941203968, 3941264106, 3970485384, 3970493608, 3974941900, 3974950124, 3992977408, 3993038336, 4004118528, 4004170888, 4004179626, 4008574976, 4008609792, 4008609928, 4008616096, 4008618666, 4008627336, 4008627404, 4008636142, 4026593280, 4037079200, 4042260480, 4042309760, 4042322160, 4176541936, 4177064176, 4177066224, 4177066232, 4194304000, 4194368000, 4205445120, 4205509290, 4210688000, 4210722816, 4210722952, 4210729120, 4210731690, 4210739336, 4210749680, 4210752250, 4244176120, 4244438268, 4261412864, 4261465088, 4272553984, 4272606344, 4277849224, 4277862138, 4278059008, 4278093824, 4278093960, 4278100128, 4278102698, 4278111368, 4278111436, 4278119592, 4278120106, 4278120174, 4278120688, 4278123258, 4278123768, 4278124282, 4278124286, 4278190080, 4278255360, 4287168256, 4287168392, 4288741120, 4288741280, 4289265408, 4289331200, 4289396480, 4289396650, 4291624908, 4293852928, 4293853098, 4293853166, 4293984240, 4294639360, 4294639530, 4294639610, 4294901504, 4294901640, 4294901674, 4294901760, 4294936576, 4294936712, 4294942880, 4294945450, 4294954120, 4294954188, 4294962926, 4294963440, 4294966010, 4294967040, 4294967210, 4294967295]
def step (xs : List T) (v : T) : Prop :=
  ∃ a ∈ xs, ∃ b ∈ xs, v = a &&& b ∨ v = a ||| b
private def freeCheck : Bool := free.all fun a => free.all fun b =>
  pairPool.contains (a &&& b) && pairPool.contains (a ||| b)
private theorem freeChecked : freeCheck = true := by decide +kernel
private theorem poolStep {v : T} (h : step free v) : v ∈ pairPool := by
  obtain ⟨a,ha,b,hb,h|h⟩ := h <;> subst v
  all_goals
    have ok := List.all_eq_true.mp (List.all_eq_true.mp freeChecked a ha) b hb
    simp only [Bool.and_eq_true, List.contains_iff_mem] at ok
  · exact ok.1
  · exact ok.2
private theorem poolRaw {a : T} (ha : a ∈ free) : a ∈ pairPool :=
  poolStep ⟨a,ha,a,ha,Or.inl (by simp)⟩
private def misses (a b : T) : Bool := (a &&& b != target) && (a ||| b != target)
private def poolCheck : Bool := pairPool.all fun a => pairPool.all (misses a)
private theorem poolChecked : poolCheck = true := by decide +kernel
private theorem poolMiss {a b : T} (ha : a ∈ pairPool) (hb : b ∈ pairPool) :
    misses a b = true := List.all_eq_true.mp (List.all_eq_true.mp poolChecked a ha) b hb
private def missesAll (z : T) (xs : List T) : Bool :=
  ((z &&& target != target) || xs.all (fun w => z &&& w != target)) &&
  ((z ||| target != target) || xs.all (fun w => z ||| w != target))
private theorem missesAll_spec {z w : T} {xs : List T}
    (h : missesAll z xs = true) (hw : w ∈ xs) : misses z w = true := by
  simp only [missesAll, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at h
  simp only [misses, Bool.and_eq_true, bne_iff_ne]
  constructor
  · rcases h.1 with h | h
    · intro he
      apply h
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · simpa using List.all_eq_true.mp h w hw
  · rcases h.2 with h | h
    · intro he
      apply h
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
    · simpa using List.all_eq_true.mp h w hw
private def chainCheck : Bool := pairPool.all fun u => free.all fun p =>
  missesAll (u &&& p) (u :: free) && missesAll (u ||| p) (u :: free)
private theorem chainChecked : chainCheck = true := by decide +kernel
private theorem chainMiss {u p w : T} (hu : u ∈ pairPool) (hp : p ∈ free)
    (hw : w ∈ u :: free) : misses (u &&& p) w = true ∧ misses (u ||| p) w = true := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp chainChecked u hu) p hp
  simp only [Bool.and_eq_true] at h
  exact ⟨missesAll_spec h.1 hw, missesAll_spec h.2 hw⟩
private theorem miss_ne {a b : T} (h : misses a b = true) :
    target ≠ a &&& b ∧ target ≠ a ||| b := by
  simp only [misses, Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨Ne.symm h.1,Ne.symm h.2⟩
theorem noThree (u v : T) (hu : step free u) (hv : step (u::free) v) :
    ¬ step (v::u::free) target := by
  have hU := poolStep hu
  have old {w : T} (hw : w ∈ u :: free) : w ∈ pairPool := by
    rcases List.mem_cons.mp hw with rfl | h
    · exact hU
    · exact poolRaw h
  have mix {w : T} (hw : w ∈ u :: free) : misses v w = true := by
    obtain ⟨a,ha,b,hb,H⟩ := hv
    rcases List.mem_cons.mp ha with eqA | hA <;> rcases List.mem_cons.mp hb with eqB | hB <;> try rw [eqA] at H <;> try rw [eqB] at H
    · rcases H with rfl | rfl <;> simpa using poolMiss hU (old hw)
    · rcases H with rfl | rfl
      · exact (chainMiss hU hB hw).1
      · exact (chainMiss hU hB hw).2
    · rcases H with rfl | rfl
      
      · simpa only [eqB, BitVec.and_comm a u] using (chainMiss hU hA hw).1
      · simpa only [eqB, BitVec.or_comm a u] using (chainMiss hU hA hw).2
    · exact poolMiss (poolStep ⟨a,hA,b,hB,H⟩) (old hw)
  have vt : v ≠ target := by
    obtain ⟨a,ha,b,hb,h|h⟩ := hv
    · exact h ▸ Ne.symm (miss_ne (poolMiss (old ha) (old hb))).1
    · exact h ▸ Ne.symm (miss_ne (poolMiss (old ha) (old hb))).2
  rintro ⟨a,ha,b,hb,H⟩
  rcases List.mem_cons.mp ha with eqA | hA <;> rcases List.mem_cons.mp hb with eqB | hB <;> try rw [eqA] at H <;> try rw [eqB] at H
  · simp_all
  · exact H.elim (miss_ne (mix hB)).1 (miss_ne (mix hB)).2
  · simp only [eqB, BitVec.and_comm a v, BitVec.or_comm a v] at H
    exact H.elim (miss_ne (mix hA)).1 (miss_ne (mix hA)).2
  · exact H.elim (miss_ne (poolMiss (old hA) (old hB))).1 (miss_ne (poolMiss (old hA) (old hB))).2
end PEqualNP.Outside.Ref1035.Example
namespace PEqualNP.Outside.Ref1035.Example
open PEqualNP.CircuitLowerBounds
def gates : List Gate := [⟨.or, [0, 2]⟩,
  ⟨.and, [4, 5]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.and, [1, 7]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.and, [4, 9]⟩,
  ⟨.or, [6, 10]⟩,
  ⟨.or, [8, 11]⟩,
  ⟨.and, [0, 2]⟩,
  ⟨.and, [4, 13]⟩,
  ⟨.and, [0, 1]⟩,
  ⟨.and, [3, 15]⟩,
  ⟨.and, [0, 4]⟩,
  ⟨.and, [1, 17]⟩,
  ⟨.or, [14, 18]⟩,
  ⟨.or, [16, 19]⟩,
  ⟨.not, [0]⟩,
  ⟨.and, [21, 12]⟩,
  ⟨.or, [22, 20]⟩]
def out (j : Fin 17) : ℕ := if j.val < 16 then 5+j.val else 23
def outTable (j : Fin 17) : T := (preTables ++ [target]).getD j.val 0
def fn (j : Fin 17) (x : Fin 5 → Bool) : Bool := readMask x (outTable j).toNat
theorem gates_length : gates.length = 19 := rfl
theorem gates_valid : ∀ g ∈ gates, admissible g := by
  simp [gates,admissible]
private instance decNot (x : GateOp) : Decidable (x = .not) := by
  cases x <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
theorem gates_not : ∀ i j : Fin gates.length, (gates.get i).op = .not →
    (gates.get j).op = .not → i = j := by decide
theorem tables_computed : ∀ j : Fin 17, (wireMasks gates).getD (out j) 0 = (outTable j).toNat := by decide
theorem computes (j : Fin 17) (x : Fin 5 → Bool) : Circuit.eval ⟨gates,out j⟩ (List.ofFn x) = fn j x := by
  rw [← out_eval gates (out j) gates_valid, tables_computed]
  rfl
theorem family_mono : ∀ (j : Fin 17) (x y : Fin 5 → Bool), (∀ i, x i ≤ y i) →
    fn j x ≤ fn j y := by decide +kernel
end PEqualNP.Outside.Ref1035.Example
namespace PEqualNP.Outside.Ref1035.Example
open PEqualNP.CircuitLowerBounds
private theorem reduce_step {l : List Nat} {v : Nat} (h : stepN l v) :
    step (l.map (BitVec.ofNat 32)) (BitVec.ofNat 32 v) := by
  obtain ⟨a,ha,b,hb,eq⟩ := h
  refine ⟨_,List.mem_map_of_mem ha,_,List.mem_map_of_mem hb,?_⟩
  rcases eq with rfl|rfl <;> simp
private def poolN := free.map BitVec.toNat
private def must := (preTables.map BitVec.toNat).toFinset
theorem impossible (ts : List Gate) (o : Fin 17→Nat)
    (hg : ∀g∈ts,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (eval : ∀ j x, Circuit.eval ⟨ts,o j⟩ (List.ofFn x)=fn j x)
    (sz : ts.length≤19) : False := by
  have admit (g) (h : g∈ts) : admissible g :=
    ⟨(hg g h).1.imp_right Or.inl,(hg g h).2⟩
  have output (j : Fin 17) : (outTable j).toNat∈bank ts := by
    let z := (wireMasks ts).getD (o j) 0
    have zm : z∈bank ts := out_mem ts _
    have zh : z<2^32 := by
      rcases Finset.mem_insert.mp zm with h|h
      · rw [h]; decide
      · exact wireMasks_bound ⟨ts,o j⟩ admit _ (List.mem_toFinset.mp h)
    have eq : z=(outTable j).toNat := mask_inj zh (outTable j).isLt (fun x =>
      (out_eval ts (o j) admit x).trans (eval j x))
    exact eq ▸ zm
  have inc : must ⊆ paid ts := by
    intro v hv
    have each : ∀ w∈must,∃j : Fin 17,(outTable j).toNat=w := by decide +kernel
    obtain ⟨j,rfl⟩ := each v hv
    have nonfree : Disjoint must Ref1035.free := by decide
    exact Finset.mem_sdiff.mpr ⟨output j,fun h => Finset.disjoint_left.mp nonfree hv h⟩
  have tg : target.toNat∈bank ts := output 16
  obtain ⟨l,tr,nd,saved,all⟩ := trace_all ts poolN hg (by decide) (by decide) (by decide)
  have hlen := paid_len ts must nd saved inc (by decide) (by decide)
  have hcard : must.card=16 := by decide
  have hmem : target.toNat∈l := (List.mem_append.mp (all _ tg)).resolve_right (by decide)
  obtain ⟨u,v,hu,hv,ht⟩ := trace_three (by decide : 0∈poolN) tr (by omega) hmem
  have mp : poolN.map (BitVec.ofNat 32)=free := by decide
  apply noThree (BitVec.ofNat 32 u) (BitVec.ofNat 32 v)
  · simpa [mp] using reduce_step hu
  · simpa [mp] using reduce_step hv
  · simpa [mp] using reduce_step ht
end PEqualNP.Outside.Ref1035.Example
theorem PEqualNP.Outside.L_meta_1035 : ¬ (∀ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 7 → (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) ∧ gates'.length ≤ gates.length) := by
  intro universal
  obtain ⟨ts,o,hg,he,sz⟩ := universal 5 17 PEqualNP.Outside.Ref1035.Example.fn (by decide)
    PEqualNP.Outside.Ref1035.Example.family_mono
    PEqualNP.Outside.Ref1035.Example.gates PEqualNP.Outside.Ref1035.Example.out
    ⟨PEqualNP.Outside.Ref1035.Example.gates_valid,PEqualNP.Outside.Ref1035.Example.gates_not,
      PEqualNP.Outside.Ref1035.Example.computes⟩
  exact PEqualNP.Outside.Ref1035.Example.impossible ts o hg he sz
