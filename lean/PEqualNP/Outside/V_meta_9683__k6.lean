import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.V_meta_9683__k6

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and,[4,5]⟩, ⟨.or,[6,7]⟩, ⟨.and,[8,9]⟩,
    ⟨.and,[0,1]⟩, ⟨.and,[11,7]⟩, ⟨.or,[10,12]⟩], 13⟩

theorem upper : PEqualNP.Represents.HasLitSize 4
    (fun x : Fin 4 → Bool => (409 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 6 :=
  ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2],
    by decide, by decide +kernel⟩

def gateVal (op : Bool) (a b : Nat) : Nat := if op then a &&& b else a ||| b

inductive Form (S : Nat → Prop) : Nat → Nat → Prop where
  | leaf {k w} (h : S w) : Form S k w
  | node {i j k a b} (op : Bool) (ha : Form S i a) (hb : Form S j b)
      (h : i+j+1 ≤ k) : Form S k (gateVal op a b)

theorem formWiden {S : Nat → Prop} {m n w : Nat} (hw : Form S m w) (h : m ≤ n) :
    Form S n w := by
  cases hw with
  | leaf ha => exact .leaf ha
  | node op ha hb hab => exact .node op ha hb (Nat.le_trans hab h)

theorem gateValSelf (op : Bool) (x : Nat) : gateVal op x x = x := by
  cases op <;> simp [gateVal]

theorem gateValComm (op : Bool) (a b : Nat) : gateVal op a b = gateVal op b a := by
  cases op
  · exact Nat.or_comm _ _
  · exact Nat.and_comm _ _

theorem gateValRepeat (p q : Bool) (a b : Nat) :
    gateVal p a (gateVal q a b) = if p=q then gateVal q a b else a := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases p <;> cases q <;> simp only [gateVal, ite_true, ite_false, Bool.false_eq_true,
    Bool.true_eq_false, Nat.testBit_and, Nat.testBit_or] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

theorem oneGateForm {S : Nat → Prop} {a b : Nat} (p : Bool) (ha : S a) (hb : S b) :
    Form S 1 (gateVal p a b) :=
  .node (i:=0) (j:=0) p (.leaf ha) (.leaf hb) (by decide)

theorem threeSuffix {S : Nat → Prop} (w1 w2 a3 b3 : Nat) (op3 : Bool)
    (h1 : Form S 1 w1)
    (h2 : ∃ p a b, (S a ∨ a=w1) ∧ (S b ∨ b=w1) ∧ w2=gateVal p a b)
    (ha : S a3 ∨ a3=w1 ∨ a3=w2) (hb : S b3 ∨ b3=w1 ∨ b3=w2) :
    Form S 3 (gateVal op3 a3 b3) := by
  obtain ⟨p,a,b,hA,hB,rfl⟩ := h2
  have pair : Form S 2 (gateVal p a b) ∧ Form S 3 (gateVal op3 w1 (gateVal p a b)) := by
    rcases hA with aOld | hA <;> rcases hB with bOld | hB
    · have h := oneGateForm p aOld bOld
      exact ⟨formWiden h (by decide), .node op3 h1 h (by decide)⟩
    · subst b
      rw [gateValComm p a w1, gateValRepeat]
      have h : Form S 2 (gateVal p w1 a) :=
        .node (i:=1) (j:=0) p h1 (.leaf aOld) (by decide)
      refine ⟨h,?_⟩
      split
      · exact formWiden h (by decide)
      · exact formWiden h1 (by decide)
    · subst a
      rw [gateValRepeat]
      have h : Form S 2 (gateVal p w1 b) :=
        .node (i:=1) (j:=0) p h1 (.leaf bOld) (by decide)
      refine ⟨h,?_⟩
      split
      · exact formWiden h (by decide)
      · exact formWiden h1 (by decide)
    · subst a
      subst b
      rw [gateValSelf, gateValSelf]
      exact ⟨formWiden h1 (by decide), formWiden h1 (by decide)⟩
  rcases ha with aOld | rfl | rfl <;> rcases hb with bOld | rfl | rfl
  · exact formWiden (oneGateForm op3 aOld bOld) (by decide)
  · exact .node (i:=0) (j:=1) op3 (.leaf aOld) h1 (by decide)
  · exact .node (i:=0) (j:=2) op3 (.leaf aOld) pair.1 (by decide)
  · exact .node (i:=1) (j:=0) op3 h1 (.leaf bOld) (by decide)
  · rw [gateValSelf]; exact formWiden h1 (by decide)
  · exact pair.2
  · exact .node (i:=2) (j:=0) op3 pair.1 (.leaf bOld) (by decide)
  · rw [gateValComm]; exact pair.2
  · rw [gateValSelf]; exact formWiden pair.1 (by decide)

open PEqualNP.CircuitLowerBounds

def bridgeInputs : List Nat := [42,44,79,112,85,83,48,15]
def bridgePool : List Nat := [42,44,79,112,85,83,48,15,0,127]
def bridgeRow (i : Fin 7) (j : Fin 4) : Bool :=
  ([4,5,6,7,8,11,12] : List Nat).getD i 0 |>.testBit j

def bridgeChoice (S : List Nat) (v : Nat) : Prop :=
  v ∈ S ∨ ∃ a ∈ S, ∃ b ∈ S, v = a &&& b ∨ v = a ||| b

inductive BridgeRun : Nat → List Nat → Nat → Prop where
  | done {S z} : z ∈ S → BridgeRun 0 S z
  | next {k S z v} : bridgeChoice S v → BridgeRun k (v :: S) z → BridgeRun (k+1) S z

theorem bridgePad {S z} (hz : z ∈ S) : ∀ k, BridgeRun k S z
  | 0 => .done hz
  | k+1 => .next (Or.inl hz) (bridgePad (List.mem_cons_self ..) k)

theorem bridgeRead {W S : List Nat} (hw : ∀ a ∈ W, a ∈ S) (zero : 0 ∈ S) (i : Nat) :
    W.getD i 0 ∈ S := by
  by_cases hi : i < W.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hw _ (List.getElem_mem ..)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact zero

def bridgeAnd : GateOp → Bool
  | .and => true
  | _ => false

def bridgeGate (W : List Nat) (g : Gate) : Nat :=
  match g.inputs with
  | [] => if bridgeAnd g.op then 127 else 0
  | [i] => W.getD i 0
  | i::j::_ => if bridgeAnd g.op then W.getD i 0 &&& W.getD j 0 else W.getD i 0 ||| W.getD j 0

theorem bridgeSelect {S W : List Nat} (hw : ∀ a ∈ W, a ∈ S) (z : 0 ∈ S) (o : 127 ∈ S)
    (g : Gate) : bridgeChoice S (bridgeGate W g) := by
  cases g with
  | mk op ins =>
    cases ins with
    | nil => cases h : bridgeAnd op <;> simp [bridgeGate,h,bridgeChoice,z,o]
    | cons i is =>
      cases is with
      | nil => exact Or.inl (bridgeRead hw z i)
      | cons j js =>
        right
        refine ⟨_, bridgeRead hw z i, _, bridgeRead hw z j, ?_⟩
        cases h : bridgeAnd op <;> simp [bridgeGate,h]

def bridgeEval (W : List Nat) (gs : List Gate) : List Nat :=
  gs.foldl (fun w g => w ++ [bridgeGate w g]) W

theorem bridgeRunOfGates (gs : List Gate) (out : Nat) (k : Nat) (hk : gs.length ≤ k)
    (W S : List Nat) (hw : ∀ a ∈ W, a ∈ S) (hz : 0 ∈ S) (ho : 127 ∈ S) :
    BridgeRun k S ((bridgeEval W gs).getD out 0) := by
  induction gs generalizing k W S with
  | nil => exact bridgePad (bridgeRead hw hz out) k
  | cons g gs ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      apply BridgeRun.next (bridgeSelect hw hz ho g)
      apply ih k (by simpa using hk) (W ++ [bridgeGate W g]) (bridgeGate W g :: S)
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_cons_of_mem _ (hw _ ha)
        · exact List.mem_cons.mpr (Or.inl (by simpa using ha))
      · exact List.mem_cons_of_mem _ hz
      · exact List.mem_cons_of_mem _ ho

theorem bridgeBound {k S z} (h : BridgeRun k S z) (hs : ∀ a ∈ S, a < 2^7) : z < 2^7 := by
  induction h with
  | done hz => exact hs _ hz
  | @next k S z v hv _ ih =>
    apply ih
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · rcases hv with h | ⟨x,hx,y,hy,h|h⟩
      · exact hs _ h
      · rw [h]; exact Nat.and_lt_two_pow _ (hs _ hy)
      · rw [h]; exact Nat.or_lt_two_pow (hs _ hx) (hs _ hy)
    · exact hs _ ha

theorem bridgeBitRead (w : List Nat) (i p : Nat) :
    (w.map (fun a => a.testBit p)).getD i false = (w.getD i 0).testBit p := by
  simpa using (List.getD_map (l:=w) (n:=i) (d:=0) (fun a : Nat => a.testBit p))

theorem bridgeOpt (m : Option Nat) (p : Nat) :
    (m.getD 0).testBit p = (m.map (fun a => a.testBit p)).getD false := by
  cases m <;> simp

theorem bridgeGateBit (W : List Nat) (g : Gate) (p : Fin 7)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    (bridgeGate W g).testBit p =
      g.op.eval (g.inputs.map fun i => (W.map (fun a => a.testBit p)).getD i false) := by
  have hall : ∀ j : Fin 7, (127 : Nat).testBit j = true := by decide +kernel
  obtain ⟨op,ins⟩ := g
  change op = .and ∨ op = .or at hop
  change ins.length ≤ 2 at hlen
  obtain rfl|rfl := hop <;> cases ins with
  | nil => simp [bridgeGate,bridgeAnd,GateOp.eval,hall]
  | cons i is =>
    cases is with
    | nil => simp [bridgeGate,GateOp.eval,bridgeOpt]
    | cons j js =>
      have : js = [] := by simpa using hlen
      subst js
      simp [bridgeGate,bridgeAnd,GateOp.eval,bridgeOpt]

theorem bridgeFoldBit (gs : List Gate) (W : List Nat) (p : Fin 7)
    (hok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    (bridgeEval W gs).map (fun a => a.testBit p) =
      gs.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map fun a => a.testBit p) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    have h := hok g (by simp)
    have htail := ih (W ++ [bridgeGate W g]) (fun q hq => hok q (by simp [hq]))
    simpa [bridgeEval,List.map_append,bridgeGateBit W g p h.1 h.2] using htail

theorem bridgeHolds {t : Nat} (ht : t ≤ 5)
    (hc : PEqualNP.Represents.HasLitSize 4 (fun x => (409 : Nat).testBit (PEqualNP.MetaComplexity.tableIndex x)) t) :
    BridgeRun 5 bridgePool 25 := by
  obtain ⟨C,hm,hs,he⟩ := hc
  let out := (bridgeEval bridgeInputs C.gates).getD C.output 0
  have hr : BridgeRun 5 bridgePool out := bridgeRunOfGates C.gates C.output 5
    (by change C.gates.length ≤ t at hs; omega) bridgeInputs bridgePool
    (by intro a ha; simpa [bridgeInputs,bridgePool] using (show a ∈ bridgeInputs ++ [0,127] from List.mem_append_left _ ha))
    (by decide) (by decide)
  have hb := bridgeBound hr (by decide +kernel : ∀ a ∈ bridgePool, a < 2^7)
  have hinputs : ∀ p : Fin 7, bridgeInputs.map (fun a => a.testBit p) =
      List.ofFn (bridgeRow p) ++ List.ofFn (fun i => !(bridgeRow p i)) := by decide +kernel
  have htgt : ∀ p : Fin 7, (409 : Nat).testBit (PEqualNP.MetaComplexity.tableIndex (bridgeRow p)) =
      (25 : Nat).testBit p := by decide +kernel
  have hbits (p : Fin 7) : out.testBit p = (25 : Nat).testBit p := by
    have hb' := bridgeFoldBit C.gates bridgeInputs p (fun g hg => by
      obtain ⟨a,b⟩ := hm g hg
      exact ⟨by simpa using a,b⟩)
    rw [hinputs p] at hb'
    change ((bridgeEval bridgeInputs C.gates).getD C.output 0).testBit p = _
    rw [← bridgeBitRead, hb']
    exact (he (bridgeRow p)).trans (htgt p)
  have huniq : ∀ v : Fin 128, (∀ p : Fin 7, v.val.testBit p = (25 : Nat).testBit p) → v.val=25 := by decide +kernel
  have eq : out = 25 := huniq ⟨out,hb⟩ hbits
  exact eq ▸ hr

theorem suffixChoice {S : List Nat} {v : Nat} (h : bridgeChoice S v) :
    ∃ p a b, a ∈ S ∧ b ∈ S ∧ v=gateVal p a b := by
  rcases h with hv | ⟨a,ha,b,hb,h | h⟩
  · exact ⟨true,v,v,hv,hv,(gateValSelf _ _).symm⟩
  · exact ⟨true,a,b,ha,hb,h⟩
  · exact ⟨false,a,b,ha,hb,h⟩

theorem suffixNext {k : Nat} {S : List Nat} {z : Nat} (h : BridgeRun (k+1) S z) :
    ∃ v, bridgeChoice S v ∧ BridgeRun k (v :: S) z := by
  cases h with
  | next hv hr => exact ⟨_,hv,hr⟩

theorem suffixTwoReads {a v w : Nat} {S : List Nat} (h : a ∈ w :: v :: S) :
    a ∈ S ∨ a=v ∨ a=w := by
  rcases List.mem_cons.mp h with rfl | hr
  · exact Or.inr (Or.inr rfl)
  · rcases List.mem_cons.mp hr with rfl | ha
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl ha

theorem bridgeSuffixForm {S : List Nat} {z : Nat} (h : BridgeRun 3 S z) :
    Form (· ∈ S) 3 z := by
  obtain ⟨v,hv,hr⟩ := suffixNext h
  obtain ⟨w,hw,hr⟩ := suffixNext hr
  obtain ⟨u,hu,hr⟩ := suffixNext hr
  have hz : z ∈ u :: w :: v :: S := by cases hr with | done h => exact h
  have hzChoice : bridgeChoice (w :: v :: S) z := by
    rcases List.mem_cons.mp hz with he | hz
    · exact he ▸ hu
    · exact Or.inl hz
  obtain ⟨p,a,b,ha,hb,rfl⟩ := suffixChoice hzChoice
  have hvForm : Form (· ∈ S) 1 v := by
    obtain ⟨q,x,y,hx,hy,he⟩ := suffixChoice hv
    rw [he]
    exact oneGateForm q hx hy
  apply threeSuffix v w a b p hvForm _ (suffixTwoReads ha) (suffixTwoReads hb)
  obtain ⟨q,x,y,hx,hy,he⟩ := suffixChoice hw
  exact ⟨q,x,y,(List.mem_cons.mp hx).symm,(List.mem_cons.mp hy).symm,he⟩

def miniBase : List Nat := [42,44,79,112,85,83,48,15,0,127]
def miniTarget : Nat := 25
def miniMix (xs ys : List Nat) := xs.flatMap fun a => ys.flatMap fun b => [a &&& b, a ||| b]
def miniStep (xs : List Nat) := (xs ++ miniMix xs xs).eraseDups

def tab0 (x : Nat) := (if x < 64 then (if x < 32 then (if x < 16 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x800000000000000000000000000000000000000000000000000000000000000000000040000000000000400000000000000) else (if x < 3 then 0x3ffffffe0000002 else 0x7ffffffc00000020000004)) else (if x < 6 then (if x < 5 then 0x3ffffff8000000800000040000008 else 0x1ffffffc0000008000001000000080000010) else (if x < 7 then 0x0 else 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if x < 12 then (if x < 10 then (if x < 9 then 0x10000000000000000400000200000000000000000000000000000000000 else 0x0) else (if x < 11 then 0x3fffffe00000080000010000002000000100000020 else 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if x < 14 then (if x < 13 then 0x3fffffc00000400000100000020000004000000200000040 else 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if x < 15 then 0x4000000000000000000000000000000000000000000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 24 then (if x < 20 then (if x < 18 then (if x < 17 then 0xfffffc00000800000800000200000040000008000000400000080 else 0x0) else (if x < 19 then 0x10000000000000000000000000000000000000000000000000000000000000000000000000 else 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if x < 22 then (if x < 21 then 0x400000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if x < 23 then 0x0 else 0x0))) else (if x < 28 then (if x < 26 then (if x < 25 then 0x0 else 0x0) else (if x < 27 then 0x0 else 0x0)) else (if x < 30 then (if x < 29 then 0x0 else 0x0) else (if x < 31 then 0x0 else 0x400000000000000000000000000000000000000000000000))))) else (if x < 48 then (if x < 40 then (if x < 36 then (if x < 34 then (if x < 33 then 0xfffff00000800001000001000000400000080000010000000800000100 else 0x0) else (if x < 35 then 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x0)) else (if x < 38 then (if x < 37 then 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x0) else (if x < 39 then 0x0 else 0x0))) else (if x < 44 then (if x < 42 then (if x < 41 then 0x3fffff0000100001000002000002000000800000100000020000001000000200 else 0x0) else (if x < 43 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x40000000000000000)) else (if x < 46 then (if x < 45 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1000000000000000000000000000000) else (if x < 47 then 0x7ffffc000020000200002000004000004000002000000200000080000002000000400 else 0xffff800008000040000400004000008000008000004000000400000100000004000000800)))) else (if x < 56 then (if x < 52 then (if x < 50 then (if x < 49 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x0) else (if x < 51 then 0x8000000000 else 0x200000000000000000)) else (if x < 54 then (if x < 53 then 0x800000000000000000000000 else 0x8000000000000000000000000000000) else (if x < 55 then 0x0 else 0x0))) else (if x < 60 then (if x < 58 then (if x < 57 then 0x80000000000000000000000000000000000000000000000000000000000 else 0x0) else (if x < 59 then 0x3ffff0000800010000100000800008000010000010000010000001000000400000010000001000 else 0x0)) else (if x < 62 then (if x < 61 then 0x7fffc00020001000020000200001000010000020000020000020000002000000800000020000002000 else 0x0) else (if x < 63 then 0x800040000000040000000000000000000000000000000000000000000000000000000000000000 else 0x7fff8001000080002000080000400002000020000040000040000040000004000001000000040000004000)))))) else (if x < 96 then (if x < 80 then (if x < 72 then (if x < 68 then (if x < 66 then (if x < 65 then 0x3fff80020002000100004000100000800004000040000080000080000080000008000002000000080000008000 else 0x1000001000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if x < 67 then 0x0 else 0xfffc00080040004000200008000200001000008000080000100000100000100000010000004000000100000010000)) else (if x < 70 then (if x < 69 then 0x0 else 0x1fff000800100080008000400010000400002000010000100000200000200000200000020000008000000200000020000) else (if x < 71 then 0x0 else 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if x < 76 then (if x < 74 then (if x < 73 then 0x0 else 0x0) else (if x < 75 then 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if x < 78 then (if x < 77 then 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if x < 79 then 0x0 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 88 then (if x < 84 then (if x < 82 then (if x < 81 then 0x7fe002001000200100010000800020000800004000020000200000400000400000400000040000010000000400000040000 else 0x7ff802004002000400200020001000040001000008000040000400000800000800000800000080000020000000800000080000) else (if x < 83 then 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 86 then (if x < 85 then 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 87 then 0x0 else 0x3ff802004008004000800400040002000080002000010000080000800001000001000001000000100000040000001000000100000))) else (if x < 92 then (if x < 90 then (if x < 89 then 0x0 else 0x0) else (if x < 91 then 0x0 else 0x2000000000000000000000000000000000000000)) else (if x < 94 then (if x < 93 then 0x0 else 0x2000000000000000000000000000000000000000000000) else (if x < 95 then 0x0 else 0x1fc02004008010008001000800080004000100004000020000100001000004000004000002000000200000080000002000000200000))))) else (if x < 112 then (if x < 104 then (if x < 100 then (if x < 98 then (if x < 97 then 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x0) else (if x < 99 then 0x0 else 0x0)) else (if x < 102 then (if x < 101 then 0x0 else 0x0) else (if x < 103 then 0x0 else 0x0))) else (if x < 108 then (if x < 106 then (if x < 105 then 0x0 else 0x0) else (if x < 107 then 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if x < 110 then (if x < 109 then 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if x < 111 then 0x0 else 0xfe0404008010040020008001000100008000200008000040000200002000008000008000004000000400000100000004000000400000)))) else (if x < 120 then (if x < 116 then (if x < 114 then (if x < 113 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if x < 115 then 0x8000000000000 else 0x7f040808020020080040010002000200010000400010000080000400004000010000010000008000000800000200000010000000800000)) else (if x < 118 then (if x < 117 then 0x1000000000000000000000000000 else 0x1f82081010040040100080020004000400020000800020000100000800008000020000020000010000002000000400000020000001000000) else (if x < 119 then 0x0 else 0x104000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if x < 124 then (if x < 122 then (if x < 121 then 0x200000000000000000000000000000000000000000000000000000000000000 else 0x0) else (if x < 123 then 0x7e208102040080080200100040008000800040001000040000400001000010000040000040000020000004000000800000040000002000000 else 0x788410204080100100400200080010001000080002000080000800002000020000080000080000040000008000001000000080000004000000)) else (if x < 126 then (if x < 125 then 0x7a10820408100200200800400100020002000100004000100001000004000040000100000100000080000010000002000000100000008000000 else 0x1a421040810200400401000800200040004000200008000200002000008000080000200000200000100000020000004000000200000010000000) else (if x < 127 then 0x4040000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))))))
def tab1 (x : Nat) := (if x < 64 then (if x < 32 then (if x < 16 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x80800000000007ff8020050024004002000200010000400010000080000400004000008000008001ffffffc008000fffffffc008000a0080014) else (if x < 3 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 6 then (if x < 5 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 7 then 0x2000000000000000000000000000000000000000000000000000000000040000000 else 0x1040003ff802004008004000800400040002000080002000010000080000800001000001000001000000100000040001801000080100000))) else (if x < 12 then (if x < 10 then (if x < 9 then 0x18982000000000000000000000000000000000000000000000003fffff00001000013fffffffffffe00000980000130000026000001300000260 else 0x0) else (if x < 11 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x788410204080100100400210080010001000080002000080000800002000020000080000082000040000008000001000042080000004000000)) else (if x < 14 then (if x < 13 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1a421040810200400401020800200040004000200008000200002000008000080000202000200000100001120000004000000200000010000000) else (if x < 15 then 0x40400000000000000000000000000000000008000400007ffffc000020000200002000004000004400002000000210000080000002200000400 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 24 then (if x < 20 then (if x < 18 then (if x < 17 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x218000000000000000000000000000000000000000000000000008000000000000200000000000000000) else (if x < 19 then 0xbffff0000800050000100000800008000010000010000010000001000000400000018400001000 else 0x7fff8001000080002000080000400002000020400040000040000040000004000001208000040000004000)) else (if x < 22 then (if x < 21 then 0x7fffc00060001000060000200001000010000020000020000020000002840000800000020000002000 else 0x7fff8001000080002000080000400002000020400040000040000048200004000001000000040000004000) else (if x < 23 then 0x0 else 0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if x < 28 then (if x < 26 then (if x < 25 then 0x0 else 0x0) else (if x < 27 then 0x4000000000000000000000000000000000000000800000000000000000000000000000000000 else 0x0)) else (if x < 30 then (if x < 29 then 0x80000000000000000000000000000000000000800000000000000000000000000000000000000000 else 0x0) else (if x < 31 then 0x0 else 0x8180004000100000000000000000000fffffc00000800000800000200000040000008000000400000080))))) else (if x < 48 then (if x < 40 then (if x < 36 then (if x < 34 then (if x < 33 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x0) else (if x < 35 then 0x17f040828020020080040010002000200010000400010000080000400004000010000010000008000000800000200200018008800800000 else 0x400000000000000000000000000000000000000000000000000000010000000000000000)) else (if x < 38 then (if x < 37 then 0x1f86081030040040100080020004000400020000800020000100000800008000020000020000010008003000880400000020000001000000 else 0x800000000000000000000000000000000000000000400000000000000000000000000000) else (if x < 39 then 0x0 else 0x0))) else (if x < 44 then (if x < 42 then (if x < 41 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x0) else (if x < 43 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x80000000000000800000000000000000000000002000000000000000000000000000000000000000000040000007ffffffc00000020000004)) else (if x < 46 then (if x < 45 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x80000000000000008000000000000000000000000080000000000000000000000000000000000001ffffffc0000008000001400000080000010) else (if x < 47 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 56 then (if x < 52 then (if x < 50 then (if x < 49 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x800000000000000000000000000000000000000000000000000000000000000000000040000000000000400000000000000) else (if x < 51 then 0x10000000000000000000000000000000100100000000000000000000000000000000000000000000000000000000003ffffffe0000002 else 0x2008000000000000000000000000000000000000000000000000000000000007ffffffc00000020000004)) else (if x < 54 then (if x < 53 then 0x8000000000000000000000000000040040000000000000000000000000000000000000000000000003ffffff8000000800000040000008 else 0x40100000000000000000000000000000000000000000000001ffffffc0000008000001000000080000010) else (if x < 55 then 0x0 else 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if x < 60 then (if x < 58 then (if x < 57 then 0x1800300020000000003fffff0000100001000002400002200000800000100000020000001000000200 else 0x0) else (if x < 59 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x80000000000000000000000000010008000000000000000000000000000000000000000000000000000000000000000640000000000000000)) else (if x < 62 then (if x < 61 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x8000000000000000000000000000040010000000000000000000000000000000000000000000000000029000000000000000000000000000000) else (if x < 63 then 0x7ffffffff0001fffffc000320001a0001a000034000034000032000003a00000c8000003a000003400 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))))) else (if x < 96 then (if x < 80 then (if x < 72 then (if x < 68 then (if x < 66 then (if x < 65 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x101000000000007ff803ffffffc005802c002c00160005800160000b000058000580000b00000b00000b000000b000002c000000b000000b0000) else (if x < 67 then 0x6000000000000000000100002000000000000000000000000000000000000000000000000000000000000000000000000008080000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 70 then (if x < 69 then 0x1800000000000000000800000004000000000000000000000000000000000000000000000000000000000001008000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 71 then 0x0 else 0x1040003ff802004008004800800400040002000080002000010000080000800001000001000001100000110000048000001200000100000))) else (if x < 76 then (if x < 74 then (if x < 73 then 0x200000000000000000000000000000000000000000000000000000000000000 else 0x0) else (if x < 75 then 0x7e208102040080080200100042008000800040001000040000400001000010000040000040080020000004000000800000040000002000000 else 0x788410204080100100400210080010001000080002000080000800002000020000080000082100040000008000001000000080000004000000)) else (if x < 78 then (if x < 77 then 0x7a10820408100200200800400104020002000100004000100001000004000040000100080100000080000010000002000000100000008000000 else 0x1a421040810200400401020800200040004000200008000200002000008000080000202200200000100000020000004000000200000010000000) else (if x < 79 then 0x4040000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 88 then (if x < 84 then (if x < 82 then (if x < 81 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 83 then 0x407e208102040080080200100040008000800040001000440000400001000010000040000040000020000004000000800000048400002000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 86 then (if x < 85 then 0x7a50820408100200200800400100020002000100004000500001000004000040000100000100000080000011040002000000100000008000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 87 then 0x0 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) else (if x < 92 then (if x < 90 then (if x < 89 then 0x0 else 0x0) else (if x < 91 then 0x2000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000 else 0x1820000040000000000000000000000000000000000000000000000100000000000000007fffffe00000080000010000002000000100000020)) else (if x < 94 then (if x < 93 then 0x8000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000 else 0x188000000100000000000000000000000000000000000000000000000100000000003fffffc00000600000100000020000004000000200000040) else (if x < 95 then 0x0 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))))) else (if x < 112 then (if x < 104 then (if x < 100 then (if x < 98 then (if x < 97 then 0xfe040400801006003000e001000100008000200008000040000204002000008000008000004000000400000100000004000000400000 else 0x0) else (if x < 99 then 0x0 else 0x40000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000)) else (if x < 102 then (if x < 101 then 0x0 else 0x80000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000) else (if x < 103 then 0x0 else 0x0))) else (if x < 108 then (if x < 106 then (if x < 105 then 0x800000000000000000000000000000000000000000000000000000000000 else 0x0) else (if x < 107 then 0x20001200000000000000003fff80020002000100004000100000800004000040000080000080000080000008000002000000080000008000 else 0x100000200000001000001fffc00080040004000200008000200001000008000080000100000100000100000010000004000000100000010000)) else (if x < 110 then (if x < 109 then 0x8000004200000000000000003fff80020002000100004000100000800004000040000080000080000080000008000002000000080000008000 else 0x10000000800000001001fff000c00100080008000400010000400002000010000100000200000200000200000020000008000000200000020000) else (if x < 111 then 0x802000000000000000000000006000000000000000000000100000000000000000000000000000000000000000000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 120 then (if x < 116 then (if x < 114 then (if x < 113 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x4420000007ff802005002400400200020001000040001000008000040000400000800000800000800040080000020000400800000080000) else (if x < 115 then 0x40090000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000003ffffffe0000002 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 118 then (if x < 117 then 0x100088000000000000000000000000000000040000000000000000000000000000000000000000000000003ffffff8000000800000040000008 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 119 then 0x0 else 0x1fff0c1bff8620641880c4030806400640032000c80032000190000c8000c800031000031000019008003900800640200039008001900000))) else (if x < 124 then (if x < 122 then (if x < 121 then 0x230000000000000000000000000000000000000000000000003fffff0000100001000002400002200000800000100000020000001000000200 else 0x400000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000) else (if x < 123 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 126 then (if x < 125 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 127 then 0x7a7ea2850a140280280a005001400280028009400450007ffffd4000250002500021400041400040a000201500020280008014800200a000400 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))))))
def tab2 (x : Nat) := (if x < 64 then (if x < 32 then (if x < 16 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 3 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 6 then (if x < 5 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 7 then 0x3ff8020040080040008004000400020000807ffffc01002008020080200100400100400100203ffffff8040080bffffffe010040a else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) else (if x < 12 then (if x < 10 then (if x < 9 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x8480000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000) else (if x < 11 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 14 then (if x < 13 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 15 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 24 then (if x < 20 then (if x < 18 then (if x < 17 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x80800000000007ff80200400200047fff80210010800420010800084000420004204008400008401ffffffc008400fffffffc008400a0084014) else (if x < 19 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 22 then (if x < 21 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 23 then 0x40c02050000002040000000000000000000000000000000000000001000000000000020000000000 else 0x3ff80200400800400087fff8041402090082002080010400082000820401040001040001050000104000041800001040000104000))) else (if x < 28 then (if x < 26 then (if x < 25 then 0x20090000000001002010c02020a00000000000000000000000000000000000 else 0x0) else (if x < 27 then 0x1fc020040080100080010008000803ffff01008040100201001008fffffc04010bfffffe0201028020105008040a0020105002010a0 else 0x80000000000000000000000000000008000000000000000000000000000020000400000002040000000000000000000000000000000000000)) else (if x < 30 then (if x < 29 then 0x1fc02004008010008001000807fffc040201010040200202001010fffffffffffc04020c0202030020206008080c0020206002020c0 else 0x8000000000000000000000000000000010000000000000000000000000000080000402040000000000000000000000000000000000000000000) else (if x < 31 then 0x80c04050000004044000000000000002000010000020000000000000000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))))) else (if x < 48 then (if x < 40 then (if x < 36 then (if x < 34 then (if x < 33 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x10800000000000000000000000000040000000000000040000000000000000000008001440000000400050400000000000000) else (if x < 35 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x7f04080802002008004001000200020001000ffff81000808004fffff04004810009010009008004400800487ffffffc10004820800904)) else (if x < 38 then (if x < 37 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1f8208101004004010008002000400040002000ffff82000810004fffff080048200090200091ffffffc2000488400111020004881000910) else (if x < 39 then 0x185000020000000000000000000000000000000000032000000000000000000000000000000000000000800000000000020000000000000 else 0x185000020800000000000000000000000000000c80000000000000080000000000000000000008000000000000400000000000000000000))) else (if x < 44 then (if x < 42 then (if x < 41 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x800000000000000000000000000000000000008000000000000000000000000040001840000004000060400000000000000) else (if x < 43 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 46 then (if x < 45 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 47 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 56 then (if x < 52 then (if x < 50 then (if x < 49 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x80800000000007ff8020050024004002180200010000400010000080000400004000008000008001ffffffc008000fffffffc008000a0080014) else (if x < 51 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 54 then (if x < 53 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 55 then 0x2000000000000000000000000000000000000000000800000000000008040000000 else 0x1040003ff802004008004000806400040002000080002000010000080000800001000001000001008000100800040201801008080100000))) else (if x < 60 then (if x < 58 then (if x < 57 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x0) else (if x < 59 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x78841020408010090040021008007fff90013ffff2002880090800582002820028480050082050040058048005007ffffffc80050024005004)) else (if x < 62 then (if x < 61 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1a421040810200400c0102080020007fffffffe000a80032000a20006880030800306020602000601ffffffe000600c001a01600060090006010) else (if x < 63 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))))) else (if x < 96 then (if x < 80 then (if x < 72 then (if x < 68 then (if x < 66 then (if x < 65 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 67 then 0x487e209122041080080200fffffff8806080604031100c44030040180100c0100c00401800401800201800040180008060003ffffffe2018002 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 70 then (if x < 69 then 0x7a528a0428101200201fff400bfffa00a200a50050401450050100280401404014010028010028008028003ffffffa00a000900280048028008 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 71 then 0x0 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) else (if x < 76 then (if x < 74 then (if x < 73 then 0x10b32000000000000000000000000000000000000000000000003fffff0000100001000082400082200000800000100000020000001000000200 else 0x10500000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000) else (if x < 75 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 78 then (if x < 77 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 79 then 0x7a7ea2850a140280280a005001460280028009400450007ffffd4000250002500021400041400040a000201500020280008014800200a000400 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 88 then (if x < 84 then (if x < 82 then (if x < 81 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 83 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 86 then (if x < 85 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 87 then 0x5044000000140000000000000000000000000000000000402000000000000000000000000000000000000004000000000000100000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) else (if x < 92 then (if x < 90 then (if x < 89 then 0x224010000000000042400502400200000000000000000000000000000000000 else 0x8010000000000082800602800200000000000000000000000000000000000) else (if x < 91 then 0x7e20811fc420847fe2121090412089008900448011200448004240011200112000444003fffffe22400084240010890002042400102240020 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 94 then (if x < 93 then 0x7a1082041fd022047fe8124091012209020901048041201048010240041200412003fffffd04400482400110240022090004102400208240040 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 95 then 0x504400000a000000000000000000000000000000000000404804000000000000000040000100000000000000000000000000000000000000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))))) else (if x < 112 then (if x < 104 then (if x < 100 then (if x < 98 then (if x < 97 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x190000a1090400000000000000000000000000000000058000000000000000000000000000000000000000000000000000000) else (if x < 99 then 0x102000000000000000001200000000000000000000000000000000000000000000000000000000000000000000000000c000000000000 else 0x7ffe0c0c0280300c0fffc180830403040182006080182000c100fffff0608081810101810100c100400c10080304010014100800c10100)) else (if x < 102 then (if x < 101 then 0x80020000000000000000024000000000000000000000000000000000000000000000000000000000001400000000000000000000000000 else 0x1f82fe1414048051fff0a0828105080508028400a1002840014200fffff0a100828201028201014200402420080508010024200801420100) else (if x < 103 then 0x0 else 0x1850c0025000000080080000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000))) else (if x < 108 then (if x < 106 then (if x < 105 then 0x200000000002204103fff80020002000100004000103fffff0004100041000082000082000080800008100002020000081000008200 else 0x100042181040000000000000000000000000000b000000000000000000000000000000000000000000000000000000000000) else (if x < 107 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 110 then (if x < 109 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 111 then 0x7a7ea2852a140280280a005003fffa80228021401050047ffffd4008250042500421400841400840a008201500820280208014808200a008400 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) else (if x < 120 then (if x < 116 then (if x < 114 then (if x < 113 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 115 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 118 then (if x < 117 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 119 then 0x2000000000000000000000000000000000000001000000000000008000040000000 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) else (if x < 124 then (if x < 122 then (if x < 121 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1a7a9450a142807ffd03404a0228045020502028100a040281003fffffa0401a0401280802280802140800828080105020020280801014080200) else (if x < 123 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if x < 126 then (if x < 125 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if x < 127 then 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))))))
def tab3 (x : Nat) := if x = 25 then 0 else 0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def miniCase (u v : Nat) := ((fun (x : Nat) => (if x < 64 then (if x < 32 then (if x < 16 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000 else 0x0) else (if x < 3 then 0x80072381b8d80000000006a001a0cc0001190000000000000000000000000000000000188000000000000000180000200008005e2e008000000000000000000005a0016000002b150000029000a000000000000000009c0001130940001000040024000000000000000023000000000000000000000000000000000022008000021000800000000003e1e0e8040001 else 0x1000ac552a14c000000000a400288000002280000000000000000000000000000000000278000000000000000270000400010009a4c0100000000000000000000096002500000492400000470011800000000000002280000022210c000221008004100000000000000004000000000000000000000000000000000003f01000003e000f4000000000783b010747402)) else (if x < 6 then (if x < 5 then 0x1800e270379b8000000000da6c35800000335000000000000000000000000000000000034800000000000000034000060001800ce6601800000000000000000000ca0032000006331000006100180000000000005f0000000032f17400030000c005c00000000000000005b00000000000000000000000000000000005a01800005900160000000000ae031d8780003 else 0x2001188b45224000000001100043800000443000000000000000000000000000000000042800000000000000042000080002001068202000000000000000000001020040000007f3f000007d001f0000000000f6000000000043d1e4f004000100077000000000000000076000000000000000000000000000000000075020000074001cc00000000008571e07ce404) else (if x < 7 then 0x0 else 0x0))) else (if x < 12 then (if x < 10 then (if x < 9 then 0x0 else 0x0) else (if x < 11 then 0x28014aa451a8800000000142005000000054f80000000000000000000000000000000004f00000004e80000004e0000a0002801369a0280000000000000000000132004c00000974b000009500250000000000000000000000549a48000500014009100000000000000009000000000000000000000000000000000008f02800008e00014008d00000e6581e8800005 else 0x0)) else (if x < 14 then (if x < 13 then 0x30017abc5dae800000000172005c00000065b80000000000000000000000000000000005b0016a000000000005a0000c000300166b20300000000000000000000162005800000af5700000ad002b0000000000000000000000655aa800060001800a90000000000000000a80000000000000000000000000000000000a70300000060023800a600000e8591f0840006 else 0x0) else (if x < 15 then 0x0 else 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000)))) else (if x < 24 then (if x < 20 then (if x < 18 then (if x < 17 then 0x3801a6d268b400000000019e00670000007668000000000000000000000000000000000660000000000000000658000e000380194c90380000000000000000000190006380000c66280000c40030c00000000000000000000076130400070001c00c00000000000000000bf5f00000000000000000000000000000000070380000a70023c000000000ea5a1f8880007 else 0x0) else (if x < 19 then 0x0 else 0x0)) else (if x < 22 then (if x < 21 then 0x0 else 0x0) else (if x < 23 then 0x0 else 0x0))) else (if x < 28 then (if x < 26 then (if x < 25 then 0x0 else 0x0) else (if x < 27 then 0x0 else 0x0)) else (if x < 30 then (if x < 29 then 0x0 else 0x0) else (if x < 31 then 0x0 else 0x0))))) else (if x < 48 then (if x < 40 then (if x < 36 then (if x < 34 then (if x < 33 then 0x4001cee672b90000000001c6007100000087080000000000000000000000000000000007000000000000000006f800100004001bcdd04000000000000000000001b8006d80000da6c80000d80035c00000000000000000000086b35400080002000d40000000000000000080000000000000000000000000000000000bf0400000a800240000000000ec5b2008c0008 else 0x0) else (if x < 35 then 0x0 else 0x0)) else (if x < 38 then (if x < 37 then 0x0 else 0x0) else (if x < 39 then 0x0 else 0x0))) else (if x < 44 then (if x < 42 then (if x < 41 then 0x4801fafc7dbe800f900001f0007b80000097b00000000000000000000000000000000007a80000000000000007a000120004801e6f204800000000000000000001e2007800000ef7700000ed003b000eb000000000000000009753a400090002400090000000000000000d40000000000000000000000000000000000c00480000a90024400e800000ee5c208900009 else 0x0) else (if x < 43 then 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000 else 0x0)) else (if x < 46 then (if x < 45 then 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000 else 0x0) else (if x < 47 then 0x544a231087c380000000021a0086000000a858000000000000000000000000000000000850000000000000000848001400050021107050000000000000000000020c0082800010481c08010100400000000000000000000000a7f828000a0002800e90000000000000000d50000000000000000000000000000000000c1053f800aa00248000000000f25d21894000a else 0x5802472290c800000000023e008f000000b8e80000000000000000000000000000000008e00000000000000008d80016000580235190580000000000000000000230008b80001168a80001140044c000000000000000000000b05bfc000b0002c00ea0000000000000000d60000000000000000000000000000000000c20580000ab0024c000000000f45e22098000b)))) else (if x < 56 then (if x < 52 then (if x < 50 then (if x < 49 then 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000 else 0x0) else (if x < 51 then 0x0 else 0x0)) else (if x < 54 then (if x < 53 then 0x0 else 0x0) else (if x < 55 then 0x0 else 0x0))) else (if x < 60 then (if x < 58 then (if x < 57 then 0x0 else 0x0) else (if x < 59 then 0x60026b3499cc8000000002620098000000c97800000000000000000000000000000000097000000000000000096800180006002592b06000000000000000000002540094800012893c98012500030000000000000000000000c89c00000c0003000ec0000000000000000d70000000000000000000000000000049000c30600000ac00250000000000f860230a0000c else 0x0)) else (if x < 62 then (if x < 61 then 0x68028d45a250c0000000028400a0800000da000000000000000000000000000000000009f80000000000000009f0001a00068027b3c0680000000000000000000276009d00001399c4dc000d00494000000000000000000000d8a404000d0003400ed0000000000000000d80000000000000000000000001360000000c40680000ad00254000000000fa61238a4000d else 0x0) else (if x < 63 then 0x0 else 0x7002ad55aa54c000000002a400a8800000ea80000000000000000000000000000000000a78000000000000000a70001c00070029b4c070000000000000000000029600a500001490700001380049c000000000000000000000e8ac0c000e0003800ee0000000000000000d9000000000000000000000029000a380000c50700000ae00258000000000fc62240a8000e)))))) else (if x < 96 then (if x < 80 then (if x < 72 then (if x < 68 then (if x < 66 then (if x < 65 then 0x7802cb64b1d88000000002c200b0000000faf800015e005740000000000000000000000ae0000000000000000ad8001e0007802b55907800000000000000000002b000ab800000fa48000139004a0000000000000000000000f8b410000f0003c00ef0000000000000000da0000000000000000000000000000000000c60780000af0025c000000000fe63248ac000f else 0x0) else (if x < 67 then 0x0 else 0x8002e772b8dc0000000002de00b70000010b68000000b60000000000000000000000000b58000000000000000b5000200008002d36808000000000000000000002ce0008002cd57a5000013a004a400000000000000000000108bc1400100004000f00000000000000000db0000000000000000000000000000000000c70800000b0002600000000010064250b00010)) else (if x < 70 then (if x < 69 then 0x0 else 0x8803017fbf5f4000000002f800bd8000011bd002f200000000000000000000000000000bc0000000000000000bb800220008802ed75088000000000000000000002200b3802e958a5800013b004a800000000000000000000118c41800110004400f10000000000000000dc0000000000000000000000000000000000c80880000b1002640000000010265258b40011) else (if x < 71 then 0x0 else 0x0))) else (if x < 76 then (if x < 74 then (if x < 73 then 0x0 else 0x0) else (if x < 75 then 0x0 else 0x0)) else (if x < 78 then (if x < 77 then 0x0 else 0x0) else (if x < 79 then 0x0 else 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000)))) else (if x < 88 then (if x < 84 then (if x < 82 then (if x < 81 then 0x90031589c461c0000000030c00c28000012c20000000000000000000000000000000000c18000000000000000c1000240009003021209000000000000000000002ea00b40000159a6000013c004ac00000000000000000000128cc1c00120004800f20000000000000000dd0000000000000000000000000000000000c90900000b2002680000000010466260b80012 else 0x98032d95ca64c0000000032400c88032013c78000000000000000000000000000000000c70000000000000000c6800260009800278109800000000000000000002ec00b4803195aa6800013d004b000000000000000000000138d42000130004c00f30000000000000000de0000000000000000000000000000000000ca0980000b30026c0000000010667268bf1613) else (if x < 83 then 0x0 else 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000)) else (if x < 86 then (if x < 85 then 0x0 else 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000) else (if x < 87 then 0x0 else 0xa00343a0cfe780000ce8033800cd8000014cd0000000000000000000000000000000000cc80000000000000000a00028000a0031b820a0000000000000000cc002ee00b5000015ba7000013e004b400000000000000000000148dc2400140005000f40000000000000000df0000000000000000000000000000000000cb0a00000b4002700000cb8010868270c00014))) else (if x < 92 then (if x < 90 then (if x < 89 then 0x0 else 0x0) else (if x < 91 then 0x0 else 0x0)) else (if x < 94 then (if x < 93 then 0x0 else 0x0) else (if x < 95 then 0x0 else 0xa80351a7d36940000000034800d18000015d100000000000000000000000000000000000a8000000000000000cc8002a000a8031d830a800000000000000000002f000b5800015ca7800013f004b800000000000000000000158e42800150005400f50000000000000000e00000000000000000000000000000000000cc0a80000b6002780000000010a69278c40015))))) else (if x < 112 then (if x < 104 then (if x < 100 then (if x < 98 then (if x < 97 then 0x0 else 0x0) else (if x < 99 then 0x0 else 0x0)) else (if x < 102 then (if x < 101 then 0x0 else 0x0) else (if x < 103 then 0x0 else 0x0))) else (if x < 108 then (if x < 106 then (if x < 105 then 0x0 else 0x0) else (if x < 107 then 0x0 else 0x0)) else (if x < 110 then (if x < 109 then 0x0 else 0x0) else (if x < 111 then 0x0 else 0xb0035faed6eb00000000035600d500000160b00000000000000000000000000000001a9d10000000000000000cd0002c000b0031f840b000000000000000000002f400b6800015fa80000140004bc00000000000000000000168ec2c00160005800f60000000000000000e10000000000000000000000000000000000cd0b00000b70027c0000000010c6a280c80016)))) else (if x < 120 then (if x < 116 then (if x < 114 then (if x < 113 then 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000 else 0x0) else (if x < 115 then 0x0 else 0xb8036db5da6cc0000d900362000b8000017d50000000000000000000000000000000000d18000000000000000cd8002e000b80323850b800000000000000000002f600b70000160a88000141004c000000000000000000000178f43000170005c00f7000000000006c000e20000000000000000000000000000000000ce0b80000b8002800000000010e6b288d00017)) else (if x < 118 then (if x < 117 then 0x0 else 0xc00379bbdd6e40000dc0003000d88000018d58000000000000000000000000000000000d20000000000000000ce00030000c00325860c000000000000000000002f800b78000161a90000142004c400000000000000000000188fc3400180006000f80000001b70000000e30000000000000000000000000000000000cf0c00000b900284000000001106d290d40018) else (if x < 119 then 0x0 else 0x0))) else (if x < 124 then (if x < 122 then (if x < 121 then 0x0 else 0x0) else (if x < 123 then 0xcf0b83c0df8640000000037200d98000019d60000000000000000000000000000000000d28000000000000000cf00032000cefb27870c8000000006f4000000002fa00b80000162a98000143004c800000000000000000000199043800190006400fa0000000000000000e40000000000000000000000000000000000d00c80000ba00288000000001126e298d80019 else 0xd0038dc50d6fc0000000037400da000001ad68000000000000000000000000000000000d30000000000000000cf80034000d00329880d0000000e2000000000002fc00b88000163aa0000144004cc000000000000000000001a90c3c001a0006800fb0000000000000000e50000000000000000000000000000000000d10d00000bbe1a8c000000001146f2a0dc001a)) else (if x < 126 then (if x < 125 then 0xdf2b921be2f000000000037600da800001bd70000000000000000000000000000000000d38000000000000000d000037c80d8032b890d80001c700000000000002fe00b90000164aa8000145004d0000000000000000000001b91440001b0006c00fc0000000000000000e60000000000000000000000000000000000d20d80000bc0029000000000116702a8e0001b else 0xe00039c9e37040000000037800db000001cd78000000000000000000000000000000000d40000000000000000d080038000e0032d8a0e0039800000000000000030000b98000165ab0000146004d4000000000000000000001c91c44001c0007000fd0000000000000000e70000000000000000000000000000000000d30e00396bd0029400000000118712b0e4001c) else (if x < 127 then 0x0 else 0x381b0d06400000000030000b80000000b00000000000000000000000000000000000a80000000000000000a000000000000261200000000000000000000000220008000000f07000000d000300000000000000000000000058280000000000009000000000000000008000000000000000000000000000000000007000000006000140000000000803010040000)))))))) u >>> (9*v)) &&& 511
def miniMaskSub (a b : Nat) : Bool := (a &&& b) == a
def miniCell (l r d : Nat → Nat) (a b : Nat) : Bool :=
  let v := l a &&& r b
  miniMaskSub v (d (a &&& b)) && miniMaskSub v (d (a ||| b))
def miniBand (l r d : Nat → Nat) (start count : Nat) : Bool :=
  (List.range count).all fun n => (List.range 128).all fun b => miniCell l r d (start+n) b
theorem miniBandD (l r d : Nat → Nat) (start count : Nat)
    (h : miniBand l r d start count=true) (a b : Nat) (h₁ : start ≤ a)
    (h₂ : a < start+count) (hb : b < 128) : miniCell l r d a b=true := by
  have hh := List.all_eq_true.mp h (a-start) (List.mem_range.mpr (by omega))
  have w := List.all_eq_true.mp hh b (List.mem_range.mpr hb)
  have eqn : start+(a-start)=a := by omega
  simpa only [eqn] using w
theorem miniTransfer {l r d : Nat → Nat} {a b q : Nat} (op : Bool)
    (c : miniCell l r d a b=true) (ha : (l a).testBit q=true) (hb : (r b).testBit q=true) :
    (d (gateVal op a b)).testBit q=true := by
  have hc := Bool.and_eq_true_iff.mp c
  cases op with
  | true =>
    have eqn : (l a &&& r b) &&& d (a &&& b) = l a &&& r b := eq_of_beq hc.1
    have e := congrArg (fun x : Nat => x.testBit q) eqn
    simpa [gateVal,Nat.testBit_and,ha,hb] using e
  | false =>
    have eqn : (l a &&& r b) &&& d (a ||| b) = l a &&& r b := eq_of_beq hc.2
    have e := congrArg (fun x : Nat => x.testBit q) eqn
    simpa [gateVal,Nat.testBit_and,ha,hb] using e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa0 : miniBand tab0 tab0 tab1 0 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa8 : miniBand tab0 tab0 tab1 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa16 : miniBand tab0 tab0 tab1 16 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa24 : miniBand tab0 tab0 tab1 24 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa32 : miniBand tab0 tab0 tab1 32 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa40 : miniBand tab0 tab0 tab1 40 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa48 : miniBand tab0 tab0 tab1 48 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa56 : miniBand tab0 tab0 tab1 56 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa64 : miniBand tab0 tab0 tab1 64 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa72 : miniBand tab0 tab0 tab1 72 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa80 : miniBand tab0 tab0 tab1 80 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa88 : miniBand tab0 tab0 tab1 88 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa96 : miniBand tab0 tab0 tab1 96 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa104 : miniBand tab0 tab0 tab1 104 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa112 : miniBand tab0 tab0 tab1 112 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem aa120 : miniBand tab0 tab0 tab1 120 8 = true := by decide +kernel
theorem aaall (a b : Nat) (ha : a < 128) (hb : b < 128) : miniCell tab0 tab0 tab1 a b = true := by
  by_cases h64 : a < 64
  ·
    by_cases h32 : a < 32
    ·
      by_cases h16 : a < 16
      ·
        by_cases h8 : a < 8
        ·
          exact miniBandD _ _ _ 0 8 aa0 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 8 8 aa8 a b (by omega) (by omega) hb
      ·
        by_cases h24 : a < 24
        ·
          exact miniBandD _ _ _ 16 8 aa16 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 24 8 aa24 a b (by omega) (by omega) hb
    ·
      by_cases h48 : a < 48
      ·
        by_cases h40 : a < 40
        ·
          exact miniBandD _ _ _ 32 8 aa32 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 40 8 aa40 a b (by omega) (by omega) hb
      ·
        by_cases h56 : a < 56
        ·
          exact miniBandD _ _ _ 48 8 aa48 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 56 8 aa56 a b (by omega) (by omega) hb
  ·
    by_cases h96 : a < 96
    ·
      by_cases h80 : a < 80
      ·
        by_cases h72 : a < 72
        ·
          exact miniBandD _ _ _ 64 8 aa64 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 72 8 aa72 a b (by omega) (by omega) hb
      ·
        by_cases h88 : a < 88
        ·
          exact miniBandD _ _ _ 80 8 aa80 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 88 8 aa88 a b (by omega) (by omega) hb
    ·
      by_cases h112 : a < 112
      ·
        by_cases h104 : a < 104
        ·
          exact miniBandD _ _ _ 96 8 aa96 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 104 8 aa104 a b (by omega) (by omega) hb
      ·
        by_cases h120 : a < 120
        ·
          exact miniBandD _ _ _ 112 8 aa112 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 120 8 aa120 a b (by omega) (by omega) hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab0 : miniBand tab0 tab1 tab2 0 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab8 : miniBand tab0 tab1 tab2 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab16 : miniBand tab0 tab1 tab2 16 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab24 : miniBand tab0 tab1 tab2 24 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab32 : miniBand tab0 tab1 tab2 32 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab40 : miniBand tab0 tab1 tab2 40 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab48 : miniBand tab0 tab1 tab2 48 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab56 : miniBand tab0 tab1 tab2 56 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab64 : miniBand tab0 tab1 tab2 64 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab72 : miniBand tab0 tab1 tab2 72 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab80 : miniBand tab0 tab1 tab2 80 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab88 : miniBand tab0 tab1 tab2 88 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab96 : miniBand tab0 tab1 tab2 96 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab104 : miniBand tab0 tab1 tab2 104 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab112 : miniBand tab0 tab1 tab2 112 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ab120 : miniBand tab0 tab1 tab2 120 8 = true := by decide +kernel
theorem aball (a b : Nat) (ha : a < 128) (hb : b < 128) : miniCell tab0 tab1 tab2 a b = true := by
  by_cases h64 : a < 64
  ·
    by_cases h32 : a < 32
    ·
      by_cases h16 : a < 16
      ·
        by_cases h8 : a < 8
        ·
          exact miniBandD _ _ _ 0 8 ab0 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 8 8 ab8 a b (by omega) (by omega) hb
      ·
        by_cases h24 : a < 24
        ·
          exact miniBandD _ _ _ 16 8 ab16 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 24 8 ab24 a b (by omega) (by omega) hb
    ·
      by_cases h48 : a < 48
      ·
        by_cases h40 : a < 40
        ·
          exact miniBandD _ _ _ 32 8 ab32 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 40 8 ab40 a b (by omega) (by omega) hb
      ·
        by_cases h56 : a < 56
        ·
          exact miniBandD _ _ _ 48 8 ab48 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 56 8 ab56 a b (by omega) (by omega) hb
  ·
    by_cases h96 : a < 96
    ·
      by_cases h80 : a < 80
      ·
        by_cases h72 : a < 72
        ·
          exact miniBandD _ _ _ 64 8 ab64 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 72 8 ab72 a b (by omega) (by omega) hb
      ·
        by_cases h88 : a < 88
        ·
          exact miniBandD _ _ _ 80 8 ab80 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 88 8 ab88 a b (by omega) (by omega) hb
    ·
      by_cases h112 : a < 112
      ·
        by_cases h104 : a < 104
        ·
          exact miniBandD _ _ _ 96 8 ab96 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 104 8 ab104 a b (by omega) (by omega) hb
      ·
        by_cases h120 : a < 120
        ·
          exact miniBandD _ _ _ 112 8 ab112 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 120 8 ab120 a b (by omega) (by omega) hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac0 : miniBand tab0 tab2 tab3 0 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac8 : miniBand tab0 tab2 tab3 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac16 : miniBand tab0 tab2 tab3 16 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac24 : miniBand tab0 tab2 tab3 24 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac32 : miniBand tab0 tab2 tab3 32 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac40 : miniBand tab0 tab2 tab3 40 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac48 : miniBand tab0 tab2 tab3 48 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac56 : miniBand tab0 tab2 tab3 56 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac64 : miniBand tab0 tab2 tab3 64 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac72 : miniBand tab0 tab2 tab3 72 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac80 : miniBand tab0 tab2 tab3 80 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac88 : miniBand tab0 tab2 tab3 88 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac96 : miniBand tab0 tab2 tab3 96 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac104 : miniBand tab0 tab2 tab3 104 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac112 : miniBand tab0 tab2 tab3 112 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ac120 : miniBand tab0 tab2 tab3 120 8 = true := by decide +kernel
theorem acall (a b : Nat) (ha : a < 128) (hb : b < 128) : miniCell tab0 tab2 tab3 a b = true := by
  by_cases h64 : a < 64
  ·
    by_cases h32 : a < 32
    ·
      by_cases h16 : a < 16
      ·
        by_cases h8 : a < 8
        ·
          exact miniBandD _ _ _ 0 8 ac0 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 8 8 ac8 a b (by omega) (by omega) hb
      ·
        by_cases h24 : a < 24
        ·
          exact miniBandD _ _ _ 16 8 ac16 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 24 8 ac24 a b (by omega) (by omega) hb
    ·
      by_cases h48 : a < 48
      ·
        by_cases h40 : a < 40
        ·
          exact miniBandD _ _ _ 32 8 ac32 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 40 8 ac40 a b (by omega) (by omega) hb
      ·
        by_cases h56 : a < 56
        ·
          exact miniBandD _ _ _ 48 8 ac48 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 56 8 ac56 a b (by omega) (by omega) hb
  ·
    by_cases h96 : a < 96
    ·
      by_cases h80 : a < 80
      ·
        by_cases h72 : a < 72
        ·
          exact miniBandD _ _ _ 64 8 ac64 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 72 8 ac72 a b (by omega) (by omega) hb
      ·
        by_cases h88 : a < 88
        ·
          exact miniBandD _ _ _ 80 8 ac80 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 88 8 ac88 a b (by omega) (by omega) hb
    ·
      by_cases h112 : a < 112
      ·
        by_cases h104 : a < 104
        ·
          exact miniBandD _ _ _ 96 8 ac96 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 104 8 ac104 a b (by omega) (by omega) hb
      ·
        by_cases h120 : a < 120
        ·
          exact miniBandD _ _ _ 112 8 ac112 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 120 8 ac120 a b (by omega) (by omega) hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb0 : miniBand tab1 tab1 tab3 0 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb8 : miniBand tab1 tab1 tab3 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb16 : miniBand tab1 tab1 tab3 16 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb24 : miniBand tab1 tab1 tab3 24 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb32 : miniBand tab1 tab1 tab3 32 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb40 : miniBand tab1 tab1 tab3 40 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb48 : miniBand tab1 tab1 tab3 48 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb56 : miniBand tab1 tab1 tab3 56 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb64 : miniBand tab1 tab1 tab3 64 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb72 : miniBand tab1 tab1 tab3 72 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb80 : miniBand tab1 tab1 tab3 80 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb88 : miniBand tab1 tab1 tab3 88 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb96 : miniBand tab1 tab1 tab3 96 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb104 : miniBand tab1 tab1 tab3 104 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb112 : miniBand tab1 tab1 tab3 112 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bb120 : miniBand tab1 tab1 tab3 120 8 = true := by decide +kernel
theorem bball (a b : Nat) (ha : a < 128) (hb : b < 128) : miniCell tab1 tab1 tab3 a b = true := by
  by_cases h64 : a < 64
  ·
    by_cases h32 : a < 32
    ·
      by_cases h16 : a < 16
      ·
        by_cases h8 : a < 8
        ·
          exact miniBandD _ _ _ 0 8 bb0 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 8 8 bb8 a b (by omega) (by omega) hb
      ·
        by_cases h24 : a < 24
        ·
          exact miniBandD _ _ _ 16 8 bb16 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 24 8 bb24 a b (by omega) (by omega) hb
    ·
      by_cases h48 : a < 48
      ·
        by_cases h40 : a < 40
        ·
          exact miniBandD _ _ _ 32 8 bb32 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 40 8 bb40 a b (by omega) (by omega) hb
      ·
        by_cases h56 : a < 56
        ·
          exact miniBandD _ _ _ 48 8 bb48 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 56 8 bb56 a b (by omega) (by omega) hb
  ·
    by_cases h96 : a < 96
    ·
      by_cases h80 : a < 80
      ·
        by_cases h72 : a < 72
        ·
          exact miniBandD _ _ _ 64 8 bb64 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 72 8 bb72 a b (by omega) (by omega) hb
      ·
        by_cases h88 : a < 88
        ·
          exact miniBandD _ _ _ 80 8 bb80 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 88 8 bb88 a b (by omega) (by omega) hb
    ·
      by_cases h112 : a < 112
      ·
        by_cases h104 : a < 104
        ·
          exact miniBandD _ _ _ 96 8 bb96 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 104 8 bb104 a b (by omega) (by omega) hb
      ·
        by_cases h120 : a < 120
        ·
          exact miniBandD _ _ _ 112 8 bb112 a b (by omega) (by omega) hb
        ·
          exact miniBandD _ _ _ 120 8 bb120 a b (by omega) (by omega) hb
def miniTab : Nat → Nat → Nat
  | 0 => tab0
  | 1 => tab1
  | 2 => tab2
  | _ => tab3

def miniInitial (u v : Nat) : Bool :=
  (v :: u :: miniBase).all fun w => decide (w < 128) && (tab0 w).testBit (miniCase u v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem miniStarts : (miniStep miniBase).all (fun u =>
    (miniStep (u::miniBase)).all (miniInitial u)) = true := by decide +kernel

private theorem miniLiftAll : (List.range 3).all (fun j =>
    (List.range 128).all (fun w => miniMaskSub (miniTab j w) (miniTab (j+1) w))) = true := by decide +kernel

theorem miniUp {i k w q : Nat} (hw : w < 128) (le : i ≤ k) (hk : k ≤ 3)
    (h : (miniTab i w).testBit q = true) : (miniTab k w).testBit q = true := by
  induction k with
  | zero =>
    have e : i=0 := by omega
    simpa [e] using h
  | succ k ih =>
    by_cases e : i=k+1
    · simpa [e] using h
    · have prev := ih (by omega) (by omega)
      have row := List.all_eq_true.mp miniLiftAll k (List.mem_range.mpr (by omega))
      have eqn : miniTab k w &&& miniTab (k+1) w = miniTab k w :=
        eq_of_beq (List.all_eq_true.mp row w (List.mem_range.mpr hw))
      have ex := congrArg (fun x : Nat => x.testBit q) eqn
      simpa [Nat.testBit_and,prev] using ex

theorem miniFits {S : Nat → Prop} {k w q : Nat} (h : Form S k w)
    (hs : ∀ a, S a → a < 128 ∧ (tab0 a).testBit q=true) (hk : k ≤ 3) :
    w < 128 ∧ (miniTab k w).testBit q=true := by
  induction h with
  | leaf h =>
    obtain ⟨hw,hm⟩ := hs _ h
    exact ⟨hw,miniUp hw (Nat.zero_le _) hk hm⟩
  | @node i j k a b op _ _ bound ia ib =>
    obtain ⟨ha,ma⟩ := ia (by omega)
    obtain ⟨hb,mb⟩ := ib (by omega)
    have hw : gateVal op a b < 128 := by
      cases op with
      | false => exact Nat.or_lt_two_pow (n:=7) ha hb
      | true => exact Nat.lt_of_le_of_lt Nat.and_le_left ha
    refine ⟨hw, miniUp hw bound hk ?_⟩
    have flip : gateVal op b a = gateVal op a b := by
      cases op <;> simp [gateVal,Nat.and_comm,Nat.or_comm]
    have cases : (i=0 ∧ j=0) ∨ (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) ∨
        (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) ∨ (i=1 ∧ j=1) := by omega
    rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact miniTransfer op (aaall _ _ ha hb) ma mb
    · exact miniTransfer op (aball _ _ ha hb) ma mb
    · rw [← flip]; exact miniTransfer op (aball _ _ hb ha) mb ma
    · exact miniTransfer op (acall _ _ ha hb) ma mb
    · rw [← flip]; exact miniTransfer op (acall _ _ hb ha) mb ma
    · exact miniTransfer op (bball _ _ ha hb) ma mb

theorem miniExcluded (u : Nat) (hu : u ∈ miniStep miniBase) (v : Nat)
    (hv : v ∈ miniStep (u :: miniBase)) : ¬ Form (fun w => w ∈ v::u::miniBase) 3 25 := by
  intro hf
  have r := List.all_eq_true.mp miniStarts u hu
  have s := List.all_eq_true.mp r v hv
  have bounds (w : Nat) (hw : w ∈ v::u::miniBase) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp s w hw)
  have err := (miniFits (q:=miniCase u v) hf (fun w hw =>
    ⟨of_decide_eq_true (bounds w hw).1,(bounds w hw).2⟩) (by decide)).2
  change (0 : Nat).testBit _ = true at err
  simp at err

theorem miniStepOfBridge {xs : List Nat} {v : Nat} (h : bridgeChoice xs v) :
    v ∈ miniStep xs := by
  simp only [miniStep, List.mem_eraseDups, List.mem_append]
  rcases h with hv | ⟨a,ha,b,hb,h|h⟩
  · exact Or.inl hv
  · exact Or.inr (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,by simp [h]⟩⟩)
  · exact Or.inr (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,by simp [h]⟩⟩)

theorem lower (t : Nat) (hc : PEqualNP.Represents.HasLitSize 4
    (fun x => (409 : Nat).testBit (PEqualNP.MetaComplexity.tableIndex x)) t) : 6 ≤ t := by
  by_contra h
  have hr := bridgeHolds (by omega : t ≤ 5) hc
  change BridgeRun 5 miniBase 25 at hr
  cases hr with
  | next first tail =>
    cases tail with
    | next second suffix =>
      exact miniExcluded _ (miniStepOfBridge first) _ (miniStepOfBridge second) (bridgeSuffixForm suffix)


end PEqualNP.Outside.V_meta_9683__k6

theorem PEqualNP.Outside.V_meta_9683__k6 : PEqualNP.Represents.HasLitSize 4 (fun x : Fin 4 → Bool => (409 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 6 ∧
  ∀ t : ℕ, PEqualNP.Represents.HasLitSize 4 (fun x : Fin 4 → Bool => (409 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 6 ≤ t :=
  ⟨PEqualNP.Outside.V_meta_9683__k6.upper, PEqualNP.Outside.V_meta_9683__k6.lower⟩
