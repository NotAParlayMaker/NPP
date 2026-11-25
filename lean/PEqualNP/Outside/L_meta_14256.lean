import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14256

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_snoc {α : Type} (l : List α) (x d : α) (k : ℕ) (hk : l.length = k) :
    (l ++ [x]).getD k d = x := by
  subst hk; simp

lemma wiresFrom_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ),
    i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [wiresFrom_cons, ih _ i (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

def IsGoodGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
  g.inputs.length ≤ 2 ∧
  (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_eval (g : Gate) (w : List Bool) :
    (normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  cases hop : g.op with
  | not =>
    cases hins : g.inputs with
    | nil => simp [normGate, hop, hins, GateOp.eval]
    | cons a l => simp [normGate, hop, hins, GateOp.eval]
  | _ => simp [normGate, hop]

lemma normGate_good (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    IsGoodGate (normGate g) := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · refine ⟨Or.inl (by simp [normGate, h]), by simp [normGate, h, hlen], by simp [normGate, h]⟩
  · refine ⟨Or.inr (Or.inl (by simp [normGate, h])), by simp [normGate, h, hlen], by simp [normGate, h]⟩
  · refine ⟨Or.inr (Or.inr (by simp [normGate, h])), by simp [normGate, h], fun _ => by simp [normGate, h]⟩

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    simp only [List.map_cons, wiresFrom_cons, normGate_eval]
    exact ih _

lemma good_of_fanInTwo {C : Circuit} (hC : FanInTwo C) :
    ∃ D : Circuit, (∀ g ∈ D.gates, IsGoodGate g) ∧ D.size = C.size ∧
      ∀ w : List Bool, D.eval w = C.eval w := by
  refine ⟨⟨C.gates.map normGate, C.output⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_good g0 (hC g0 hg0)
  · intro w
    change (wiresFrom (C.gates.map normGate) w).getD C.output false =
      (wiresFrom C.gates w).getD C.output false
    rw [wiresFrom_norm]

inductive Val where
  | const (b : Bool)
  | wire (w : ℕ)
deriving DecidableEq

def valEval (w : List Bool) : Val → Bool
  | Val.const b => b
  | Val.wire i => w.getD i false

def valBound (m : ℕ) : Val → Prop
  | Val.const _ => True
  | Val.wire i => i < m

lemma valBound_mono {m m' : ℕ} (h : m ≤ m') : ∀ v : Val, valBound m v → valBound m' v
  | Val.const _, _ => trivial
  | Val.wire _, hi => Nat.lt_of_lt_of_le hi h

def simpAnd (m : ℕ) : List Val → Option Gate × Val
  | [] => (none, Val.const true)
  | [v] => (none, v)
  | [Val.const false, _] => (none, Val.const false)
  | [Val.const true, v] => (none, v)
  | [Val.wire _, Val.const false] => (none, Val.const false)
  | [Val.wire a, Val.const true] => (none, Val.wire a)
  | [Val.wire a, Val.wire b] => (some ⟨GateOp.and, [a, b]⟩, Val.wire m)
  | _ => (none, Val.const false)

def simpOr (m : ℕ) : List Val → Option Gate × Val
  | [] => (none, Val.const false)
  | [v] => (none, v)
  | [Val.const true, _] => (none, Val.const true)
  | [Val.const false, v] => (none, v)
  | [Val.wire _, Val.const true] => (none, Val.const true)
  | [Val.wire a, Val.const false] => (none, Val.wire a)
  | [Val.wire a, Val.wire b] => (some ⟨GateOp.or, [a, b]⟩, Val.wire m)
  | _ => (none, Val.const false)

def simpNot (m : ℕ) : List Val → Option Gate × Val
  | [] => (none, Val.const true)
  | [Val.const b] => (none, Val.const (!b))
  | [Val.wire a] => (some ⟨GateOp.not, [a]⟩, Val.wire m)
  | _ => (none, Val.const false)

def simpGate (op : GateOp) (m : ℕ) (ins : List Val) : Option Gate × Val :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Val.const false)

lemma simpGate_fanInTwo (op : GateOp) (m : ℕ) (ins : List Val) (g : Gate)
    (h : (simpGate op m ins).1 = some g) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  cases op with
  | and =>
    match ins with
    | [] | [_] | [Val.const false, _] | [Val.const true, _]
    | [Val.wire _, Val.const false] | [Val.wire _, Val.const true]
    | _ :: _ :: _ :: _ => simp [simpGate, simpAnd] at h
    | [Val.wire a, Val.wire b] => simp [simpGate, simpAnd] at h; subst h; simp
  | or =>
    match ins with
    | [] | [_] | [Val.const true, _] | [Val.const false, _]
    | [Val.wire _, Val.const true] | [Val.wire _, Val.const false]
    | _ :: _ :: _ :: _ => simp [simpGate, simpOr] at h
    | [Val.wire a, Val.wire b] => simp [simpGate, simpOr] at h; subst h; simp
  | not =>
    match ins with
    | [] | [Val.const _] | _ :: _ :: _ => simp [simpGate, simpNot] at h
    | [Val.wire a] => simp [simpGate, simpNot] at h; subst h; simp
  | mod _ => simp [simpGate] at h
  | maj => simp [simpGate] at h

lemma simpGate_bound (op : GateOp) (m : ℕ) (ins : List Val)
    (hb : ∀ v ∈ ins, valBound m v) :
    valBound (m + (simpGate op m ins).1.toList.length) (simpGate op m ins).2 := by
  cases op with
  | and =>
    match ins with
    | [] => trivial
    | [v] => exact hb v (by simp)
    | [Val.const false, _] => trivial
    | [Val.const true, v] => exact hb v (by simp)
    | [Val.wire _, Val.const false] => trivial
    | [Val.wire a, Val.const true] => exact hb (Val.wire a) (by simp)
    | [Val.wire a, Val.wire b] => simp [simpGate, simpAnd, valBound]
    | _ :: _ :: _ :: _ => trivial
  | or =>
    match ins with
    | [] => trivial
    | [v] => exact hb v (by simp)
    | [Val.const true, _] => trivial
    | [Val.const false, v] => exact hb v (by simp)
    | [Val.wire _, Val.const true] => trivial
    | [Val.wire a, Val.const false] => exact hb (Val.wire a) (by simp)
    | [Val.wire a, Val.wire b] => simp [simpGate, simpOr, valBound]
    | _ :: _ :: _ :: _ => trivial
  | not =>
    match ins with
    | [] => trivial
    | [Val.const _] => trivial
    | [Val.wire a] => simp [simpGate, simpNot, valBound]
    | _ :: _ :: _ => simp [simpGate, simpNot, valBound]
  | mod _ => trivial
  | maj => trivial

lemma simpGate_eval (op : GateOp) (ins : List Val) (w : List Bool)
    (hop : (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) ∧ ins.length ≤ 2 ∧
      (op = GateOp.not → ins.length ≤ 1)) :
    valEval (wiresFrom (simpGate op w.length ins).1.toList w) (simpGate op w.length ins).2 =
      op.eval (ins.map (valEval w)) := by
  rcases hop with ⟨ho, hlen, hnot⟩
  rcases ho with rfl | rfl | rfl
  · match ins with
    | [] => simp [simpGate, simpAnd, valEval, GateOp.eval]
    | [v] => simp [simpGate, simpAnd, wiresFrom, valEval, GateOp.eval]
    | [Val.const false, _] => simp [simpGate, simpAnd, valEval, GateOp.eval]
    | [Val.const true, v] => simp [simpGate, simpAnd, wiresFrom, valEval, GateOp.eval]
    | [Val.wire _, Val.const false] => simp [simpGate, simpAnd, valEval, GateOp.eval]
    | [Val.wire a, Val.const true] => simp [simpGate, simpAnd, wiresFrom, valEval, GateOp.eval]
    | [Val.wire a, Val.wire b] => simp [simpGate, simpAnd, wiresFrom, valEval, GateOp.eval]
    | _ :: _ :: _ :: _ => simp at hlen
  · match ins with
    | [] => simp [simpGate, simpOr, valEval, GateOp.eval]
    | [v] => simp [simpGate, simpOr, wiresFrom, valEval, GateOp.eval]
    | [Val.const true, _] => simp [simpGate, simpOr, valEval, GateOp.eval]
    | [Val.const false, v] => simp [simpGate, simpOr, wiresFrom, valEval, GateOp.eval]
    | [Val.wire _, Val.const true] => simp [simpGate, simpOr, valEval, GateOp.eval]
    | [Val.wire a, Val.const false] => simp [simpGate, simpOr, wiresFrom, valEval, GateOp.eval]
    | [Val.wire a, Val.wire b] => simp [simpGate, simpOr, wiresFrom, valEval, GateOp.eval]
    | _ :: _ :: _ :: _ => simp at hlen
  · have h1 := hnot rfl
    match ins with
    | [] => simp [simpGate, simpNot, valEval, GateOp.eval]
    | [Val.const b] => simp [simpGate, simpNot, valEval, GateOp.eval]
    | [Val.wire a] => simp [simpGate, simpNot, wiresFrom, valEval, GateOp.eval]
    | _ :: _ :: _ => simp at h1

lemma simpGate_none_of_const (op : GateOp) (m : ℕ) (ins : List Val) (c : Bool)
    (hc : Val.const c ∈ ins) :
    (simpGate op m ins).1 = none := by
  cases op with
  | and =>
    match ins with
    | [] => simp at hc
    | [_] | [Val.const false, _] | [Val.const true, _]
    | [Val.wire _, Val.const false] | [Val.wire _, Val.const true]
    | _ :: _ :: _ :: _ => rfl
    | [Val.wire _, Val.wire _] => simp at hc
  | or =>
    match ins with
    | [] => simp at hc
    | [_] | [Val.const true, _] | [Val.const false, _]
    | [Val.wire _, Val.const true] | [Val.wire _, Val.const false]
    | _ :: _ :: _ :: _ => rfl
    | [Val.wire _, Val.wire _] => simp at hc
  | not =>
    match ins with
    | [] => simp at hc
    | [Val.const _] => rfl
    | [Val.wire _] => simp at hc
    | _ :: _ :: _ => simp [simpGate, simpNot]
  | mod _ => rfl
  | maj => rfl

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

lemma simpGate_const_of_fixBit (g : Gate) (hg : IsGoodGate g) (m : ℕ) (ins : List Val)
    (hins : ins.length = g.inputs.length) (hc : Val.const (fixBit g) ∈ ins) :
    ∃ d : Bool, simpGate g.op m ins = (none, Val.const d) := by
  rcases hg with ⟨ho, hlen, hnot⟩
  rcases ho with h | h | h
  · have hfb : fixBit g = false := by simp [fixBit, h]
    rw [hfb] at hc
    rw [h]
    match ins with
    | [] => simp at hc
    | [v] => simp at hc; subst hc; exact ⟨false, rfl⟩
    | [Val.const false, _] => exact ⟨false, rfl⟩
    | [Val.const true, v] => simp at hc; subst hc; exact ⟨false, rfl⟩
    | [Val.wire _, Val.const false] => exact ⟨false, rfl⟩
    | [Val.wire _, Val.const true] => simp at hc
    | [Val.wire _, Val.wire _] => simp at hc
    | _ :: _ :: _ :: _ => simp only [List.length_cons] at hins; omega
  · have hfb : fixBit g = true := by simp [fixBit, h]
    rw [hfb] at hc
    rw [h]
    match ins with
    | [] => simp at hc
    | [v] => simp at hc; subst hc; exact ⟨true, rfl⟩
    | [Val.const true, _] => exact ⟨true, rfl⟩
    | [Val.const false, v] => simp at hc; subst hc; exact ⟨true, rfl⟩
    | [Val.wire _, Val.const true] => exact ⟨true, rfl⟩
    | [Val.wire _, Val.const false] => simp at hc
    | [Val.wire _, Val.wire _] => simp at hc
    | _ :: _ :: _ :: _ => simp only [List.length_cons] at hins; omega
  · have hfb : fixBit g = false := by simp [fixBit, h]
    rw [hfb] at hc
    have h1 := hnot h
    rw [h]
    match ins with
    | [] => simp at hc
    | [v] => simp at hc; subst hc; exact ⟨true, rfl⟩
    | _ :: _ :: _ => simp only [List.length_cons] at hins; omega

def elimStep (n : ℕ) (acc : List Val × List Gate) (g : Gate) : List Val × List Gate :=
  let ins := g.inputs.map fun i => acc.1.getD i (Val.const false)
  let res := simpGate g.op (n + acc.2.length) ins
  (acc.1 ++ [res.2], acc.2 ++ res.1.toList)

def elimGates (n : ℕ) (gs : List Gate) (acc : List Val × List Gate) : List Val × List Gate :=
  gs.foldl (elimStep n) acc

lemma elimGates_nil (n : ℕ) (acc : List Val × List Gate) :
    elimGates n [] acc = acc := rfl

lemma elimGates_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Val × List Gate) :
    elimGates n (g :: gs) acc = elimGates n gs (elimStep n acc g) := rfl

lemma elimGates_append (n : ℕ) (gs₁ gs₂ : List Gate) (acc : List Val × List Gate) :
    elimGates n (gs₁ ++ gs₂) acc = elimGates n gs₂ (elimGates n gs₁ acc) := by
  simp [elimGates, List.foldl_append]

lemma elimGates_fst_length (n : ℕ) (gs : List Gate) :
    ∀ acc : List Val × List Gate,
      (elimGates n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elimGates]
  | cons g gs ih =>
    intro acc
    rw [elimGates_cons, ih]
    simp [elimStep]; omega

lemma elimGates_good (n : ℕ) (gs : List Gate) :
    ∀ acc : List Val × List Gate,
      (∀ g ∈ acc.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ g ∈ (elimGates n gs acc).2,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih
    intro g' hg'
    simp only [elimStep, List.mem_append] at hg'
    rcases hg' with h1 | h2
    · exact h g' h1
    · rw [Option.mem_toList] at h2
      exact simpGate_fanInTwo g.op (n + acc.2.length) _ g' h2

lemma option_toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimGates_len_le (n : ℕ) (gs : List Gate) :
    ∀ acc : List Val × List Gate,
      (elimGates n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elimGates]
  | cons g gs ih =>
    intro acc
    rw [elimGates_cons]
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := option_toList_length_le (simpGate g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Val.const false))).1
      omega
    simp only [List.length_cons]
    omega

lemma elimGates_val_prefix (n : ℕ) (gs : List Gate) :
    ∀ (acc : List Val × List Gate) (i : ℕ), i < acc.1.length →
      (elimGates n gs acc).1.getD i (Val.const false) = acc.1.getD i (Val.const false) := by
  induction gs with
  | nil => intro acc i _; rfl
  | cons g gs ih =>
    intro acc i hi
    rw [elimGates_cons, ih _ i (by simp [elimStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma elimGates_len_drop (n : ℕ) (p : ℕ) (c : Bool) (gs : List Gate) :
    ∀ acc : List Val × List Gate,
      p < acc.1.length →
      acc.1.getD p (Val.const false) = Val.const c →
      (∃ g ∈ gs, p ∈ g.inputs) →
      (elimGates n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ ⟨g, hg, _⟩; simp at hg
  | cons g gs ih =>
    intro acc hp hpc hex
    rw [elimGates_cons]
    rcases hex with ⟨g', hg', hpg'⟩
    simp only [List.mem_cons] at hg'
    rcases hg' with rfl | hmem
    · have hcin : Val.const c ∈ List.map (fun i => acc.1.getD i (Val.const false)) g'.inputs := by
        rw [List.mem_map]
        exact ⟨p, hpg', hpc⟩
      have hnone : (simpGate g'.op (n + acc.2.length)
          (List.map (fun i => acc.1.getD i (Val.const false)) g'.inputs)).1 = none :=
        simpGate_none_of_const _ _ _ c hcin
      have hstep : (elimStep n acc g').2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have h1 := elimGates_len_le n gs (elimStep n acc g')
      simp only [List.length_cons]
      omega
    · have hp' : p < (elimStep n acc g).1.length := by simp [elimStep]; omega
      have hpc' : (elimStep n acc g).1.getD p (Val.const false) = Val.const c := by
        simp only [elimStep]
        rw [List.getD_append _ _ _ _ hp]
        exact hpc
      have h1 := ih (elimStep n acc g) hp' hpc' ⟨g', hmem, hpg'⟩
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := option_toList_length_le (simpGate g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Val.const false))).1
        omega
      simp only [List.length_cons]
      omega

def ElimInv (n : ℕ) (x : List Bool) (wOrig : List Bool) (acc : List Val × List Gate) : Prop :=
  wOrig.length = acc.1.length ∧
  (∀ v ∈ acc.1, valBound (n + acc.2.length) v) ∧
  (∀ i : ℕ, valEval (wiresFrom acc.2 x) (acc.1.getD i (Val.const false)) = wOrig.getD i false)

lemma elimGates_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (wOrig : List Bool) (acc : List Val × List Gate),
      (∀ g ∈ gs, IsGoodGate g) →
      ElimInv n x wOrig acc →
      ElimInv n x (wiresFrom gs wOrig) (elimGates n gs acc) := by
  induction gs with
  | nil => intro wOrig acc _ hinv; exact hinv
  | cons g gs ih =>
    intro wOrig acc hgs hinv
    rw [wiresFrom_cons, elimGates_cons]
    apply ih _ _ (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    rcases hinv with ⟨hlen, hbd, hev⟩
    have hg : IsGoodGate g := hgs g (List.mem_cons_self ..)
    let wNew := wiresFrom acc.2 x
    have hwNewLen : wNew.length = n + acc.2.length := by
      rw [wiresFrom_length, hx]
    let ins := g.inputs.map fun i => acc.1.getD i (Val.const false)
    let res := simpGate g.op (n + acc.2.length) ins
    have hinsBd : ∀ v ∈ ins, valBound (n + acc.2.length) v := by
      intro v hv
      rw [List.mem_map] at hv
      obtain ⟨i, _, rfl⟩ := hv
      by_cases hi : i < acc.1.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hbd _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        trivial
    have hresBd : valBound (n + acc.2.length + res.1.toList.length) res.2 :=
      simpGate_bound g.op (n + acc.2.length) ins hinsBd
    have hresEval : valEval (wiresFrom (acc.2 ++ res.1.toList) x) res.2 =
        g.op.eval (g.inputs.map fun i => wOrig.getD i false) := by
      have hwf : wiresFrom (acc.2 ++ res.1.toList) x = wiresFrom res.1.toList wNew := by
        simp [wiresFrom, wNew, List.foldl_append]
      rw [hwf]
      have hse := simpGate_eval g.op ins wNew
        ⟨hg.1, by simp [ins, hg.2.1], fun hn => by simp [ins, hg.2.2 hn]⟩
      rw [hwNewLen] at hse
      rw [hse]
      congr 1
      simp only [ins, List.map_map]
      apply List.map_congr_left
      intro i _
      exact hev i
    refine ⟨?_, ?_, ?_⟩
    · simp [elimStep, hlen]
    · intro v hv
      simp only [elimStep, List.mem_append, List.mem_singleton] at hv ⊢
      rw [List.length_append, ← Nat.add_assoc]
      rcases hv with h1 | rfl
      · exact valBound_mono (by omega) v (hbd v h1)
      · exact hresBd
    · intro i
      simp only [elimStep]
      have hwf : wiresFrom (acc.2 ++ res.1.toList) x = wiresFrom res.1.toList wNew := by
        simp [wiresFrom, wNew, List.foldl_append]
      by_cases hi : i < acc.1.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
        have hvbd : valBound wNew.length (acc.1.getD i (Val.const false)) := by
          rw [hwNewLen, List.getD_eq_getElem _ _ hi]
          exact hbd _ (List.getElem_mem hi)
        cases hv : acc.1.getD i (Val.const false) with
        | const c =>
          have := hev i; rw [hv] at this; exact this
        | wire k =>
          rw [hv] at hvbd
          have hev_i := hev i; rw [hv] at hev_i
          rw [hwf]
          change (wiresFrom res.1.toList wNew).getD k false = wOrig.getD i false
          rw [wiresFrom_prefix res.1.toList wNew k hvbd]
          exact hev_i
      · by_cases heq : i = acc.1.length
        · subst heq
          have h1 : (acc.1 ++ [res.2]).getD acc.1.length (Val.const false) = res.2 := by simp
          have h2 : (wOrig ++ [g.op.eval (g.inputs.map fun j => wOrig.getD j false)]).getD
              acc.1.length false = g.op.eval (g.inputs.map fun j => wOrig.getD j false) := by
            rw [← hlen]; simp
          rw [h1, h2]
          exact hresEval
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
          rfl

lemma wiresFrom_no_read_set (S : ℕ → Prop) (gs : List Gate)
    (hno : ∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ S a) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i : ℕ, ¬ S i → w1.getD i false = w2.getD i false) →
      ∀ i : ℕ, ¬ S i → (wiresFrom gs w1).getD i false = (wiresFrom gs w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ h i hi; exact h i hi
  | cons g gs ih =>
    intro w1 w2 hlen h i hi
    rw [wiresFrom_cons, wiresFrom_cons]
    have hg := hno g (List.mem_cons_self ..)
    have hmap : (g.inputs.map fun j => w1.getD j false) =
        (g.inputs.map fun j => w2.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact h j (hg j hj)
    rw [hmap]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w1.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
      exact h j hj
    · by_cases heq : j = w1.length
      · subst heq; simp [hlen]
      · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]

lemma wiresFrom_no_read_p (p : ℕ) (gs : List Gate) (hno : ∀ g ∈ gs, p ∉ g.inputs) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i : ℕ, i ≠ p → w1.getD i false = w2.getD i false) →
      ∀ i : ℕ, i ≠ p → (wiresFrom gs w1).getD i false = (wiresFrom gs w2).getD i false :=
  wiresFrom_no_read_set (fun a => a = p) gs (fun g hg a ha heq => hno g hg (heq ▸ ha))

lemma first_read_split (p : ℕ) (gs : List Gate) (hex : ∃ g ∈ gs, p ∈ g.inputs) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate),
      gs = pre ++ g :: post ∧ p ∈ g.inputs ∧ ∀ g' ∈ pre, p ∉ g'.inputs := by
  induction gs with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons a gs ih =>
    by_cases ha : p ∈ a.inputs
    · exact ⟨[], a, gs, rfl, ha, fun _ h => by simp at h⟩
    · have hex' : ∃ g ∈ gs, p ∈ g.inputs := by
        obtain ⟨g, hg, hp⟩ := hex
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact absurd hp ha
        · exact ⟨g, hg, hp⟩
      obtain ⟨pre, g, post, rfl, hp, hpre⟩ := ih hex'
      refine ⟨a :: pre, g, post, rfl, hp, ?_⟩
      intro g' hg'
      simp only [List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · exact ha
      · exact hpre g' hg'

theorem elim_var {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin n → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize n f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x p b)) s' := by
  obtain ⟨C0, hC0, hsz0, hev0⟩ := h
  obtain ⟨C, hCgood, hCsz, hCev⟩ := good_of_fanInTwo hC0
  have hevC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := fun x => (hCev _).trans (hev0 x)
  have hread : ∃ g ∈ C.gates, p.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    by_cases hout : C.output = p.val
    · obtain ⟨x, y, hxy⟩ := hnc
      have hx : f (Function.update x p b) = b := by
        rw [← hevC]
        change (wiresFrom C.gates (List.ofFn (Function.update x p b))).getD C.output false = b
        rw [wiresFrom_prefix _ _ _ (by simp [hout]), hout]
        simp
      have hy : f (Function.update y p b) = b := by
        rw [← hevC]
        change (wiresFrom C.gates (List.ofFn (Function.update y p b))).getD C.output false = b
        rw [wiresFrom_prefix _ _ _ (by simp [hout]), hout]
        simp
      exact hxy (hx.trans hy.symm)
    · obtain ⟨x, hx⟩ := hdep
      have heq := wiresFrom_no_read_p p.val C.gates hno
        (List.ofFn (Function.update x p (!x p))) (List.ofFn x) (by simp)
        (fun i hi => by
          by_cases hlt : i < n
          · rw [List.getD_eq_getElem _ _ (by simp [hlt]),
                List.getD_eq_getElem _ _ (by simp [hlt])]
            simp only [List.getElem_ofFn]
            have hne : (⟨i, hlt⟩ : Fin n) ≠ p := fun he => hi (congrArg Fin.val he)
            exact Function.update_of_ne hne (!x p) x
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        C.output hout
      exact hx ((hevC _).symm.trans (heq.trans (hevC _)))
  let initVals : List Val := List.ofFn fun i : Fin n => if i = p then Val.const b else Val.wire i.val
  let res := elimGates n C.gates (initVals, [])
  have hlen : res.2.length + 1 ≤ C.gates.length := by
    have hp : p.val < initVals.length := by simp [initVals]
    have hpc : initVals.getD p.val (Val.const false) = Val.const b := by
      rw [List.getD_eq_getElem _ _ hp]
      simp [initVals]
    have := elimGates_len_drop n p.val b C.gates (initVals, []) hp hpc hread
    simpa using this
  have hinv_all : ∀ x : Fin n → Bool,
      ElimInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn (Function.update x p b))) res := by
    intro x
    apply elimGates_inv n (List.ofFn x) (by simp) C.gates _ (initVals, []) hCgood
    refine ⟨by simp [initVals], ?_, ?_⟩
    · intro v hv
      simp only [initVals, List.mem_ofFn] at hv
      obtain ⟨i, rfl⟩ := hv
      split_ifs <;> simp [valBound]
    · intro i
      by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simp [initVals, hi]),
            List.getD_eq_getElem _ _ (by simp [hi])]
        simp only [initVals, List.getElem_ofFn, wiresFrom_nil]
        split_ifs with hpi
        · rw [hpi]; simp [valEval]
        · change (List.ofFn x).getD i false = Function.update x p b ⟨i, hi⟩
          rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
          exact (Function.update_of_ne hpi b x).symm
      · rw [List.getD_eq_default _ _ (by simp [initVals]; omega),
            List.getD_eq_default _ _ (by simp; omega)]
        rfl
  cases hout : res.1.getD C.output (Val.const false) with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := (hinv_all x).2.2 C.output
    have hy := (hinv_all y).2.2 C.output
    rw [hout] at hx hy
    have hfx : f (Function.update x p b) = c := (hevC _).symm.trans hx.symm
    have hfy : f (Function.update y p b) = c := (hevC _).symm.trans hy.symm
    exact hxy (hfx.trans hfy.symm)
  | wire wout =>
    refine ⟨res.2.length, by change C.gates.length = C0.gates.length at hCsz; change C0.gates.length ≤ s at hsz0; omega, ?_⟩
    refine ⟨⟨res.2, wout⟩, ?_, le_rfl, ?_⟩
    · exact elimGates_good n C.gates (initVals, []) (fun _ hg => by simp at hg)
    · intro x
      have hx := (hinv_all x).2.2 C.output
      rw [hout] at hx
      exact hx.trans (hevC _)

theorem gate_elim_two {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) (s : ℕ)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin n → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize n f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x p b)) s' := by
  obtain ⟨C0, hC0, hsz0, hev0⟩ := h
  obtain ⟨C, hCgood, hCsz, hCev⟩ := good_of_fanInTwo hC0
  have hevC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := fun x => (hCev _).trans (hev0 x)
  have hread : ∃ g ∈ C.gates, p.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    by_cases hout : C.output = p.val
    · obtain ⟨x, y, hxy⟩ := hnc false
      have hx : f (Function.update x p false) = false := by
        rw [← hevC]
        change (wiresFrom C.gates (List.ofFn (Function.update x p false))).getD C.output false = false
        rw [wiresFrom_prefix _ _ _ (by simp [hout]), hout]; simp
      have hy : f (Function.update y p false) = false := by
        rw [← hevC]
        change (wiresFrom C.gates (List.ofFn (Function.update y p false))).getD C.output false = false
        rw [wiresFrom_prefix _ _ _ (by simp [hout]), hout]; simp
      exact hxy (hx.trans hy.symm)
    · obtain ⟨x, hx⟩ := hdep
      have heq := wiresFrom_no_read_p p.val C.gates hno
        (List.ofFn (Function.update x p (!x p))) (List.ofFn x) (by simp)
        (fun i hi => by
          by_cases hlt : i < n
          · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt])]
            simp only [List.getElem_ofFn]
            have hne : (⟨i, hlt⟩ : Fin n) ≠ p := fun he => hi (congrArg Fin.val he)
            exact Function.update_of_ne hne (!x p) x
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
        C.output hout
      exact hx ((hevC _).symm.trans (heq.trans (hevC _)))
  obtain ⟨pre, g, post, hgs_eq, hpg, hpre_no⟩ := first_read_split p.val C.gates hread
  let b := fixBit g
  let initVals : List Val := List.ofFn fun i : Fin n => if i = p then Val.const b else Val.wire i.val
  let accPre := elimGates n pre (initVals, [])
  let accG := elimStep n accPre g
  let res := elimGates n post accG
  have haccPre_len : accPre.1.length = n + pre.length := by
    simp only [accPre, elimGates_fst_length, initVals, List.length_ofFn]
  have haccG_len : accG.1.length = n + pre.length + 1 := by
    simp [accG, elimStep, haccPre_len]
  have hp_accPre : accPre.1.getD p.val (Val.const false) = Val.const b := by
    rw [elimGates_val_prefix n pre (initVals, []) p.val (by simp [initVals])]
    rw [List.getD_eq_getElem _ _ (by simp [initVals])]
    simp [initVals]
  have hg_good : IsGoodGate g := hCgood g (by rw [hgs_eq]; simp)
  have hcin : Val.const (fixBit g) ∈ List.map (fun i => accPre.1.getD i (Val.const false)) g.inputs := by
    rw [List.mem_map]
    exact ⟨p.val, hpg, hp_accPre⟩
  obtain ⟨c, hsimp_g⟩ := simpGate_const_of_fixBit g hg_good (n + accPre.2.length)
    (g.inputs.map fun i => accPre.1.getD i (Val.const false)) (by simp) hcin
  have haccG_len_eq : accG.2.length = accPre.2.length := by
    simp only [accG, elimStep, hsimp_g, Option.toList_none, List.append_nil]
  have haccPre_le : accPre.2.length ≤ pre.length := by
    have := elimGates_len_le n pre (initVals, [])
    simpa [accPre] using this
  have haccG_p : accG.1.getD p.val (Val.const false) = Val.const b := by
    simp only [accG, elimStep]
    rw [List.getD_append _ _ _ _ (by rw [haccPre_len]; omega)]
    exact hp_accPre
  have haccG_new : accG.1.getD (n + pre.length) (Val.const false) = Val.const c := by
    simp only [accG, elimStep, hsimp_g]
    exact getD_snoc accPre.1 (Val.const c) (Val.const false) (n + pre.length) haccPre_len
  have hinv_all : ∀ x : Fin n → Bool,
      ElimInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn (Function.update x p b))) res := by
    intro x
    have hinv0 : ElimInv n (List.ofFn x) (List.ofFn (Function.update x p b)) (initVals, []) := by
      refine ⟨by simp [initVals], ?_, ?_⟩
      · intro v hv
        simp only [initVals, List.mem_ofFn] at hv
        obtain ⟨i, rfl⟩ := hv
        split_ifs <;> simp [valBound]
      · intro i
        by_cases hi : i < n
        · rw [List.getD_eq_getElem _ _ (by simp [initVals, hi]),
              List.getD_eq_getElem _ _ (by simp [hi])]
          simp only [initVals, List.getElem_ofFn]
          split_ifs with hpi
          · rw [hpi]; simp [valEval]
          · change (List.ofFn x).getD i false = Function.update x p b ⟨i, hi⟩
            rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
            exact (Function.update_of_ne hpi b x).symm
        · rw [List.getD_eq_default _ _ (by simp [initVals]; omega),
              List.getD_eq_default _ _ (by simp; omega)]
          rfl
    have heq_res : res = elimGates n C.gates (initVals, []) := by
      rw [hgs_eq, elimGates_append, elimGates_cons]
    rw [heq_res]
    exact elimGates_inv n (List.ofFn x) (by simp) C.gates _ (initVals, []) hCgood hinv0
  have hlen2 : res.2.length + 2 ≤ C.gates.length := by
    have hgs_len : C.gates.length = pre.length + 1 + post.length := by
      rw [hgs_eq, List.length_append, List.length_cons]; omega
    by_cases hp_post : ∃ g' ∈ post, p.val ∈ g'.inputs
    · have hd := elimGates_len_drop n p.val b post accG (by rw [haccG_len]; omega) haccG_p hp_post
      change res.2.length + 1 ≤ accG.2.length + post.length at hd
      omega
    · by_cases hnew_post : ∃ g' ∈ post, (n + pre.length) ∈ g'.inputs
      · have hd := elimGates_len_drop n (n + pre.length) c post accG
          (by rw [haccG_len]; omega) haccG_new hnew_post
        change res.2.length + 1 ≤ accG.2.length + post.length at hd
        omega
      · exfalso
        push Not at hp_post hnew_post
        by_cases hout_p : C.output = p.val
        · obtain ⟨x, y, hxy⟩ := hnc b
          have hp_res : res.1.getD p.val (Val.const false) = Val.const b := by
            rw [elimGates_val_prefix n post accG p.val (by rw [haccG_len]; omega)]
            exact haccG_p
          have hx : f (Function.update x p b) = b := by
            have h1 := (hinv_all x).2.2 C.output
            have h2 : (wiresFrom C.gates (List.ofFn (Function.update x p b))).getD C.output false = f (Function.update x p b) :=
              hevC (Function.update x p b)
            rw [h2, hout_p, hp_res] at h1
            exact h1.symm
          have hy : f (Function.update y p b) = b := by
            have h1 := (hinv_all y).2.2 C.output
            have h2 : (wiresFrom C.gates (List.ofFn (Function.update y p b))).getD C.output false = f (Function.update y p b) :=
              hevC (Function.update y p b)
            rw [h2, hout_p, hp_res] at h1
            exact h1.symm
          exact hxy (hx.trans hy.symm)
        · by_cases hout_new : C.output = n + pre.length
          · obtain ⟨x, y, hxy⟩ := hnc b
            have hnew_res : res.1.getD (n + pre.length) (Val.const false) = Val.const c := by
              rw [elimGates_val_prefix n post accG (n + pre.length) (by rw [haccG_len]; omega)]
              exact haccG_new
            have hx : f (Function.update x p b) = c := by
              have h1 := (hinv_all x).2.2 C.output
              have h2 : (wiresFrom C.gates (List.ofFn (Function.update x p b))).getD C.output false = f (Function.update x p b) :=
                hevC (Function.update x p b)
              rw [h2, hout_new, hnew_res] at h1
              exact h1.symm
            have hy : f (Function.update y p b) = c := by
              have h1 := (hinv_all y).2.2 C.output
              have h2 : (wiresFrom C.gates (List.ofFn (Function.update y p b))).getD C.output false = f (Function.update y p b) :=
                hevC (Function.update y p b)
              rw [h2, hout_new, hnew_res] at h1
              exact h1.symm
            exact hxy (hx.trans hy.symm)
          · obtain ⟨x, hx⟩ := hdep
            let x' := Function.update x p (!x p)
            have hpre_eq := wiresFrom_no_read_p p.val pre hpre_no (List.ofFn x') (List.ofFn x) (by simp)
              (fun i hi => by
                by_cases hlt : i < n
                · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt])]
                  simp only [List.getElem_ofFn]
                  have hne : (⟨i, hlt⟩ : Fin n) ≠ p := fun he => hi (congrArg Fin.val he)
                  exact Function.update_of_ne hne (!x p) x
                · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
            let w1 := wiresFrom (pre ++ [g]) (List.ofFn x')
            let w2 := wiresFrom (pre ++ [g]) (List.ofFn x)
            have hlen1 : w1.length = n + pre.length + 1 := by simp [w1, wiresFrom_length]; omega
            have hlen2 : w2.length = n + pre.length + 1 := by simp [w2, wiresFrom_length]; omega
            have hpost_eq := wiresFrom_no_read_set (fun a => a = p.val ∨ a = n + pre.length) post
              (fun g' hg' a ha hor => by
                rcases hor with rfl | rfl
                · exact hp_post g' hg' ha
                · exact hnew_post g' hg' ha)
              w1 w2 (by omega)
              (fun i hi => by
                have hip : i ≠ p.val := fun h => hi (Or.inl h)
                have hinew : i ≠ n + pre.length := fun h => hi (Or.inr h)
                have hpl1 : (wiresFrom pre (List.ofFn x')).length = n + pre.length := by
                  rw [wiresFrom_length]; simp
                have hpl2 : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
                  rw [wiresFrom_length]; simp
                by_cases hlt : i < n + pre.length
                · simp only [w1, w2, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
                  rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
                  exact hpre_eq i hip
                · simp only [w1, w2, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
                  rw [List.getD_eq_default _ _ (by simp [hpl1]; omega),
                      List.getD_eq_default _ _ (by simp [hpl2]; omega)])
              C.output (by rintro (h | h) <;> contradiction)
            have hev_eq : C.eval (List.ofFn x') = C.eval (List.ofFn x) := by
              have hsp : C.gates = (pre ++ [g]) ++ post := by rw [hgs_eq]; simp
              have hL : wiresFrom C.gates (List.ofFn x') = wiresFrom post w1 := by
                rw [hsp, wiresFrom_append]
              have hR : wiresFrom C.gates (List.ofFn x) = wiresFrom post w2 := by
                rw [hsp, wiresFrom_append]
              change (wiresFrom C.gates (List.ofFn x')).getD C.output false =
                (wiresFrom C.gates (List.ofFn x)).getD C.output false
              rw [hL, hR]
              exact hpost_eq
            exact hx ((hevC x').symm.trans (hev_eq.trans (hevC x)))
  cases hout : res.1.getD C.output (Val.const false) with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc b
    have hx := (hinv_all x).2.2 C.output
    have hy := (hinv_all y).2.2 C.output
    rw [hout] at hx hy
    have hfx : f (Function.update x p b) = c := (hevC _).symm.trans hx.symm
    have hfy : f (Function.update y p b) = c := (hevC _).symm.trans hy.symm
    exact hxy (hfx.trans hfy.symm)
  | wire wout =>
    refine ⟨b, res.2.length, by change C.gates.length = C0.gates.length at hCsz; change C0.gates.length ≤ s at hsz0; omega, ?_⟩
    refine ⟨⟨res.2, wout⟩, ?_, le_rfl, ?_⟩
    · have heq_res : res = elimGates n C.gates (initVals, []) := by
        rw [hgs_eq, elimGates_append, elimGates_cons]
      rw [heq_res]
      exact elimGates_good n C.gates (initVals, []) (fun _ hg => by simp at hg)
    · intro x
      have hx := (hinv_all x).2.2 C.output
      rw [hout] at hx
      exact hx.trans (hevC _)

def relabelGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if h : i < n then (π ⟨i, h⟩).val else m + (i - n)⟩

lemma wiresFrom_relabel (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) (y : Fin m → Bool) :
    ∀ k : ℕ,
      (wiresFrom (gs.map (relabelGate n m π)) (List.ofFn y)).getD (m + k) false =
        (wiresFrom gs (List.ofFn (y ∘ π))).getD (n + k) false := by
  suffices h : ∀ (w1 w2 : List Bool), w1.length = m → w2.length = n →
      (∀ i : Fin n, w1.getD (π i).val false = w2.getD i.val false) →
      ∀ (k : ℕ),
        (wiresFrom (gs.map (relabelGate n m π)) w1).getD (m + k) false =
          (wiresFrom gs w2).getD (n + k) false ∧
        ∀ i : Fin n,
          (wiresFrom (gs.map (relabelGate n m π)) w1).getD (π i).val false =
            (wiresFrom gs w2).getD i.val false by
    intro k
    exact (h (List.ofFn y) (List.ofFn (y ∘ π)) (by simp) (by simp) (fun i => by
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp) k).1
  suffices h2 : ∀ (gs : List Gate) (w1 w2 : List Bool) (d : ℕ),
      w1.length = m + d → w2.length = n + d →
      (∀ i : Fin n, w1.getD (π i).val false = w2.getD i.val false) →
      (∀ k : ℕ, w1.getD (m + k) false = w2.getD (n + k) false) →
      ∀ k : ℕ,
        (wiresFrom (gs.map (relabelGate n m π)) w1).getD (m + k) false =
          (wiresFrom gs w2).getD (n + k) false by
    intro w1 w2 hm hn hi k
    refine ⟨h2 gs w1 w2 0 hm hn hi (fun k => by
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]) k, ?_⟩
    intro i
    rw [wiresFrom_prefix _ _ _ (by omega), wiresFrom_prefix _ _ _ (by omega)]
    exact hi i
  intro gs
  induction gs with
  | nil => intro w1 w2 d _ _ _ hk k; exact hk k
  | cons g gs ih =>
    intro w1 w2 d hm hn hi hk k
    simp only [List.map_cons, wiresFrom_cons]
    have hmap : ((relabelGate n m π g).inputs.map fun i => w1.getD i false) =
        (g.inputs.map fun i => w2.getD i false) := by
      simp only [relabelGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      split_ifs with hlt
      · exact hi ⟨i, hlt⟩
      · have he : n + (i - n) = i := by omega
        rw [hk (i - n), he]
    rw [hmap]
    apply ih _ _ (d + 1) (by simp [hm]; omega) (by simp [hn]; omega)
    · intro i
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact hi i
    · intro j
      by_cases hlt : j < d
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hk j
      · by_cases heq : j = d
        · subst heq
          have hop : (relabelGate n m π g).op = g.op := rfl
          rw [hop, getD_snoc w1 _ false (m + j) hm, getD_snoc w2 _ false (n + j) hn]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize n f s) : HasCircuitSize m (fun y => f (y ∘ π)) s := by
  obtain ⟨C, hC, hsz, hev⟩ := h
  let out' := if ho : C.output < n then (π ⟨C.output, ho⟩).val else m + (C.output - n)
  refine ⟨⟨C.gates.map (relabelGate n m π), out'⟩, ?_, by simpa [Circuit.size] using hsz, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hC g0 hg0).1, by simpa [relabelGate] using (hC g0 hg0).2⟩
  · intro y
    dsimp only
    rw [← hev (y ∘ π)]
    change (wiresFrom (C.gates.map (relabelGate n m π)) (List.ofFn y)).getD out' false =
      (wiresFrom C.gates (List.ofFn (y ∘ π))).getD C.output false
    by_cases ho : C.output < n
    · simp only [out', ho, ↓reduceDIte]
      rw [wiresFrom_prefix _ _ _ (by simp), wiresFrom_prefix _ _ _ (by simp [ho])]
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp [ho])]
      simp
    · simp only [out', ho, ↓reduceDIte]
      have he : n + (C.output - n) = C.output := by omega
      have := wiresFrom_relabel n m π C.gates y (C.output - n)
      rwa [he] at this

def maj3 (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

def suppStep3 (s : List (Finset (Fin 3))) (g : Gate) : List (Finset (Fin 3)) :=
  s ++ [g.inputs.foldl (fun acc i => acc ∪ s.getD i ∅) ∅]

def initSupps3 : List (Finset (Fin 3)) :=
  List.ofFn fun i : Fin 3 => ({i} : Finset (Fin 3))

def supps3 (gs : List Gate) : List (Finset (Fin 3)) :=
  gs.foldl suppStep3 initSupps3

lemma initSupps3_length : initSupps3.length = 3 := by simp [initSupps3]

lemma initSupps3_getD_lt (k : ℕ) (hk : k < 3) :
    initSupps3.getD k ∅ = ({⟨k, hk⟩} : Finset (Fin 3)) := by
  rw [List.getD_eq_getElem _ _ (by rw [initSupps3_length]; exact hk)]
  simp only [initSupps3, List.getElem_ofFn]

lemma supp3_foldl_sub (s : List (Finset (Fin 3))) (l : List ℕ) :
    ∀ acc : Finset (Fin 3),
      acc ⊆ l.foldl (fun a i => a ∪ s.getD i ∅) acc ∧
      ∀ i ∈ l, s.getD i ∅ ⊆ l.foldl (fun a j => a ∪ s.getD j ∅) acc := by
  induction l with
  | nil => intro acc; exact ⟨Finset.Subset.rfl, fun _ h => by simp at h⟩
  | cons a l ih =>
    intro acc
    obtain ⟨h1, h2⟩ := ih (acc ∪ s.getD a ∅)
    refine ⟨Finset.subset_union_left.trans h1, ?_⟩
    intro i hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hm
    · exact Finset.subset_union_right.trans h1
    · exact h2 i hm

lemma supp3_eval_eq (gs : List Gate) :
    ∀ (x y : Fin 3 → Bool) (w : ℕ),
      (∀ i ∈ (supps3 gs).getD w ∅, x i = y i) →
      (wiresFrom gs (List.ofFn x)).getD w false = (wiresFrom gs (List.ofFn y)).getD w false := by
  suffices h : ∀ (gs : List Gate) (s : List (Finset (Fin 3))) (wx wy : List Bool) (x y : Fin 3 → Bool),
      s.length = wx.length → s.length = wy.length →
      (∀ w : ℕ, (∀ i ∈ s.getD w ∅, x i = y i) → wx.getD w false = wy.getD w false) →
      ∀ w : ℕ, (∀ i ∈ (gs.foldl suppStep3 s).getD w ∅, x i = y i) →
        (wiresFrom gs wx).getD w false = (wiresFrom gs wy).getD w false by
    intro x y w hw
    apply h gs initSupps3 (List.ofFn x) (List.ofFn y) x y
      (by simp [initSupps3_length]) (by simp [initSupps3_length])
    · intro k hk
      by_cases hlt : k < 3
      · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt])]
        simp only [List.getElem_ofFn]
        apply hk
        rw [initSupps3_getD_lt k hlt]
        exact Finset.mem_singleton_self _
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact hw
  intro gs
  induction gs with
  | nil => intro s wx wy x y _ _ h w hw; exact h w hw
  | cons g gs ih =>
    intro s wx wy x y hx hy h w hw
    rw [List.foldl_cons] at hw
    rw [wiresFrom_cons, wiresFrom_cons]
    apply ih (suppStep3 s g) _ _ x y (by simp [suppStep3, hx]) (by simp [suppStep3, hy]) _ w hw
    intro k hk
    by_cases hlt : k < s.length
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply h k
      intro i hi
      apply hk
      simp only [suppStep3]
      rw [List.getD_append _ _ _ _ hlt]
      exact hi
    · by_cases heq : k = s.length
      · subst heq
        rw [getD_snoc wx _ false s.length hx.symm, getD_snoc wy _ false s.length hy.symm]
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hk
        simp only [suppStep3]
        have hs : (s ++ [g.inputs.foldl (fun acc t => acc ∪ s.getD t ∅) ∅]).getD s.length ∅ =
            g.inputs.foldl (fun acc t => acc ∪ s.getD t ∅) ∅ := by simp
        rw [hs]
        exact (supp3_foldl_sub s g.inputs ∅).2 j hj hi
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma maj3_dep : ∀ i : Fin 3, ∃ x : Fin 3 → Bool, maj3 (Function.update x i (!x i)) ≠ maj3 x := by
  decide

lemma maj3_no_pair_factor :
    ∀ u v : Fin 3, u ≠ v →
      ∀ h : Bool → Bool → Bool,
        ∃ (a1 b1 a2 b2 : Bool) (y : Fin 3 → Bool),
          h a1 b1 = h a2 b2 ∧
          maj3 (Function.update (Function.update y u a1) v b1) ≠
            maj3 (Function.update (Function.update y u a2) v b2) := by
  decide

lemma eval_step_eq (g : Gate) (w1 w2 : List Bool)
    (h : ∀ i ∈ g.inputs, w1.getD i false = w2.getD i false) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  congr 1
  exact List.map_congr_left h

lemma suppStep3_getD_lt (s : List (Finset (Fin 3))) (g : Gate) (w : ℕ) (hw : w < s.length) :
    (suppStep3 s g).getD w ∅ = s.getD w ∅ :=
  List.getD_append _ _ _ _ hw

lemma suppStep3_getD_eq (s : List (Finset (Fin 3))) (g : Gate) (k : ℕ) (hk : s.length = k) :
    (suppStep3 s g).getD k ∅ = g.inputs.foldl (fun a i => a ∪ s.getD i ∅) ∅ :=
  getD_snoc s _ ∅ k hk

lemma not_factor_pair (f : (Fin 3 → Bool) → Bool) (hfl : f = maj3 ∨ f = fun x => !maj3 x)
    (u v : Fin 3) (huv : u ≠ v) (w : (Fin 3 → Bool) → Bool)
    (hw : ∀ x y : Fin 3 → Bool, x u = y u → x v = y v → w x = w y)
    (hfac : ∀ x y : Fin 3 → Bool, (∀ i : Fin 3, i ≠ u → i ≠ v → x i = y i) → w x = w y → f x = f y) :
    False := by
  let h0 (a b : Bool) : Bool := w (Function.update (Function.update (fun _ => false) u a) v b)
  obtain ⟨a1, b1, a2, b2, y, hh, hfne⟩ := maj3_no_pair_factor u v huv h0
  let x1 := Function.update (Function.update y u a1) v b1
  let x2 := Function.update (Function.update y u a2) v b2
  have hw1 : w x1 = h0 a1 b1 := hw x1 _ (by simp [x1, Function.update_of_ne huv]) (by simp [x1])
  have hw2 : w x2 = h0 a2 b2 := hw x2 _ (by simp [x2, Function.update_of_ne huv]) (by simp [x2])
  have hfeq : f x1 = f x2 := hfac x1 x2 (fun i hiu hiv => by
    simp [x1, x2, Function.update_of_ne hiu, Function.update_of_ne hiv]) (hw1.trans (hh.trans hw2.symm))
  rcases hfl with rfl | rfl
  · exact hfne hfeq
  · exact hfne (Bool.not_inj hfeq)

lemma not_dep_le2 (f : (Fin 3 → Bool) → Bool) (hfl : f = maj3 ∨ f = fun x => !maj3 x)
    (S : Finset (Fin 3)) (hScard : S.card ≤ 2)
    (hdep : ∀ x y : Fin 3 → Bool, (∀ i ∈ S, x i = y i) → f x = f y) : False := by
  have hne : S ≠ Finset.univ := by
    intro hu; rw [hu] at hScard; simp at hScard
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ∉ S := by
    by_contra hall
    push Not at hall
    apply hne; ext k; simp [hall k]
  obtain ⟨x, hx⟩ := maj3_dep i
  have heq : f (Function.update x i (!x i)) = f x :=
    hdep _ _ (fun j hj => Function.update_of_ne (fun h : j = i => hi (h ▸ hj)) _ _)
  rcases hfl with rfl | rfl
  · exact hx heq
  · exact hx (Bool.not_inj heq)

lemma supp3_card_init (w : ℕ) : (initSupps3.getD w ∅).card ≤ 1 := by
  by_cases h : w < 3
  · rw [initSupps3_getD_lt w h]; simp
  · rw [List.getD_eq_default _ _ (by rw [initSupps3_length]; omega)]; simp

lemma card3_foldl_le (s : List (Finset (Fin 3))) (l : List ℕ) (B : ℕ)
    (hB : ∀ w : ℕ, (s.getD w ∅).card ≤ B) :
    (l.foldl (fun a i => a ∪ s.getD i ∅) ∅).card ≤ l.length * B := by
  suffices h : ∀ (l : List ℕ) (acc : Finset (Fin 3)),
      (l.foldl (fun a i => a ∪ s.getD i ∅) acc).card ≤ acc.card + l.length * B by
    simpa using h l ∅
  intro l
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons]
    have h1 := ih (acc ∪ s.getD a ∅)
    have h2 := Finset.card_union_le acc (s.getD a ∅)
    have h3 := hB a
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

lemma no_size_2_maj3_or_not (f : (Fin 3 → Bool) → Bool) (hfl : f = maj3 ∨ f = fun x => !maj3 x)
    (gs : List Gate) (hglen : gs.length ≤ 2) (hgood : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (out : ℕ) (hev : ∀ x : Fin 3 → Bool, (wiresFrom gs (List.ofFn x)).getD out false = f x) :
    False := by
  cases gs with
  | nil =>
    exact not_dep_le2 f hfl (initSupps3.getD out ∅) (by have := supp3_card_init out; omega)
      (fun x y hxy => (hev x).symm.trans ((supp3_eval_eq [] x y out hxy).trans (hev y)))
  | cons g0 gs1 =>
    have hg0 : g0.inputs.length ≤ 2 := hgood g0 (by simp)
    have hcard_s0 (w : ℕ) : ((supps3 [g0]).getD w ∅).card ≤ if w = 3 then 2 else 1 := by
      by_cases hw : w < 3
      · have hne : w ≠ 3 := by omega
        simp only [hne, ↓reduceIte]
        change ((suppStep3 initSupps3 g0).getD w ∅).card ≤ 1
        rw [suppStep3_getD_lt initSupps3 g0 w (by rw [initSupps3_length]; exact hw)]
        exact supp3_card_init w
      · by_cases heq : w = 3
        · subst heq; simp only [↓reduceIte]
          change ((suppStep3 initSupps3 g0).getD 3 ∅).card ≤ 2
          rw [suppStep3_getD_eq initSupps3 g0 3 initSupps3_length]
          have := card3_foldl_le initSupps3 g0.inputs 1 supp3_card_init; omega
        · simp only [heq, ↓reduceIte]
          have hlen : (supps3 [g0]).length = 4 := by simp [supps3, suppStep3, initSupps3_length]
          rw [List.getD_eq_default _ _ (by omega)]; simp
    cases gs1 with
    | nil =>
      have hc := hcard_s0 out
      exact not_dep_le2 f hfl ((supps3 [g0]).getD out ∅) (by split_ifs at hc <;> omega)
        (fun x y hxy => (hev x).symm.trans ((supp3_eval_eq [g0] x y out hxy).trans (hev y)))
    | cons g1 gs2 =>
      cases gs2 with
      | cons _ _ => simp at hglen
      | nil =>
        have hg1 : g1.inputs.length ≤ 2 := hgood g1 (by simp)
        have hlen1 : (supps3 [g0]).length = 4 := by simp [supps3, suppStep3, initSupps3_length]
        have hout4 : out = 4 := by
          by_contra hne
          have hle2 : ((supps3 [g0, g1]).getD out ∅).card ≤ 2 := by
            by_cases hlt : out < 4
            · change ((suppStep3 (supps3 [g0]) g1).getD out ∅).card ≤ 2
              rw [suppStep3_getD_lt (supps3 [g0]) g1 out (by omega)]
              have := hcard_s0 out; split_ifs at this <;> omega
            · have hlen2 : (supps3 [g0, g1]).length = 5 := by simp [supps3, suppStep3, initSupps3_length]
              rw [List.getD_eq_default _ _ (by omega)]; simp
          exact not_dep_le2 f hfl ((supps3 [g0, g1]).getD out ∅) hle2
            (fun x y hxy => (hev x).symm.trans ((supp3_eval_eq [g0, g1] x y out hxy).trans (hev y)))
        subst hout4
        have hS4_3 : ((supps3 [g0, g1]).getD 4 ∅).card = 3 := by
          have hle3 : ((supps3 [g0, g1]).getD 4 ∅).card ≤ 3 := Finset.card_le_univ _
          by_contra hne3
          exact not_dep_le2 f hfl ((supps3 [g0, g1]).getD 4 ∅) (by omega)
            (fun x y hxy => (hev x).symm.trans ((supp3_eval_eq [g0, g1] x y 4 hxy).trans (hev y)))
        have hs4_def : (supps3 [g0, g1]).getD 4 ∅ =
            g1.inputs.foldl (fun a i => a ∪ (supps3 [g0]).getD i ∅) ∅ :=
          suppStep3_getD_eq (supps3 [g0]) g1 4 hlen1
        rw [hs4_def] at hS4_3
        match hg1i : g1.inputs with
        | [] => simp [hg1i] at hS4_3
        | [a] =>
          simp only [hg1i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS4_3
          have := hcard_s0 a; split_ifs at this <;> omega
        | [a, b] =>
          simp only [hg1i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS4_3
          have hu := Finset.card_union_le ((supps3 [g0]).getD a ∅) ((supps3 [g0]).getD b ∅)
          have ha := hcard_s0 a; have hb := hcard_s0 b
          have hab3 : (a = 3 ∧ b ≠ 3) ∨ (a ≠ 3 ∧ b = 3) := by
            by_cases ha3 : a = 3 <;> by_cases hb3 : b = 3
            · subst ha3; subst hb3; rw [Finset.union_idempotent] at hS4_3
              simp only [↓reduceIte] at ha; omega
            · exact Or.inl ⟨ha3, hb3⟩
            · exact Or.inr ⟨ha3, hb3⟩
            · split_ifs at ha hb <;> omega
          have hcard3_2 : ((supps3 [g0]).getD 3 ∅).card = 2 := by
            have h3le := hcard_s0 3; simp only [↓reduceIte] at h3le
            rcases hab3 with ⟨rfl, hb3⟩ | ⟨ha3, rfl⟩ <;> split_ifs at ha hb <;> omega
          obtain ⟨u, v, huv, h3uv⟩ := Finset.card_eq_two.mp hcard3_2
          have hdisj : ∀ i ∈ [a, b], ∀ hi3 : i < 3, (⟨i, hi3⟩ : Fin 3) ∉ (supps3 [g0]).getD 3 ∅ := by
            intro i hi hi3 hmem
            have hin : (⟨i, hi3⟩ : Fin 3) ∈ (supps3 [g0]).getD i ∅ := by
              change (⟨i, hi3⟩ : Fin 3) ∈ (suppStep3 initSupps3 g0).getD i ∅
              rw [suppStep3_getD_lt initSupps3 g0 i (by rw [initSupps3_length]; exact hi3),
                  initSupps3_getD_lt i hi3]
              exact Finset.mem_singleton_self _
            rcases hab3 with ⟨rfl, hb3⟩ | ⟨ha3, rfl⟩
            · simp at hi
              rcases hi with rfl | rfl
              · omega
              · have hdi := Finset.card_union_add_card_inter ((supps3 [g0]).getD 3 ∅) ((supps3 [g0]).getD i ∅)
                have hi1 := hcard_s0 i; split_ifs at hi1; · omega
                have h0i : (supps3 [g0]).getD 3 ∅ ∩ (supps3 [g0]).getD i ∅ = ∅ :=
                  Finset.card_eq_zero.mp (by omega)
                have := Finset.mem_inter.mpr ⟨hmem, hin⟩
                rw [h0i] at this; exact Finset.notMem_empty _ this
            · simp at hi
              rcases hi with rfl | rfl
              · have hdi := Finset.card_union_add_card_inter ((supps3 [g0]).getD i ∅) ((supps3 [g0]).getD 3 ∅)
                have hi1 := hcard_s0 i; split_ifs at hi1; · omega
                have h0i : (supps3 [g0]).getD i ∅ ∩ (supps3 [g0]).getD 3 ∅ = ∅ :=
                  Finset.card_eq_zero.mp (by omega)
                have := Finset.mem_inter.mpr ⟨hin, hmem⟩
                rw [h0i] at this; exact Finset.notMem_empty _ this
              · omega
          refine not_factor_pair f hfl u v huv (fun x => (wiresFrom [g0] (List.ofFn x)).getD 3 false)
            (fun x y hxu hxv => supp3_eval_eq [g0] x y 3 (fun i hi => by
              rw [h3uv, Finset.mem_insert, Finset.mem_singleton] at hi
              rcases hi with rfl | rfl <;> assumption)) ?_
          intro x y hout_ag hw3
          have hlen_x : (wiresFrom [g0] (List.ofFn x)).length = 4 := by rw [wiresFrom_length]; simp
          have hlen_y : (wiresFrom [g0] (List.ofFn y)).length = 4 := by rw [wiresFrom_length]; simp
          rw [← hev x, ← hev y]
          change (wiresFrom [g0] (List.ofFn x) ++ _).getD 4 false =
            (wiresFrom [g0] (List.ofFn y) ++ _).getD 4 false
          rw [getD_snoc _ _ false 4 hlen_x, getD_snoc _ _ false 4 hlen_y]
          apply eval_step_eq
          intro i hi
          rw [hg1i] at hi
          by_cases hlt : i < 3
          · change (wiresFrom [g0] (List.ofFn x)).getD i false = (wiresFrom [g0] (List.ofFn y)).getD i false
            rw [wiresFrom_prefix [g0] _ i (by simp [hlt]), wiresFrom_prefix [g0] _ i (by simp [hlt])]
            rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt])]
            simp only [List.getElem_ofFn]
            have hni := hdisj i hi hlt
            rw [h3uv, Finset.mem_insert, Finset.mem_singleton, not_or] at hni
            exact hout_ag ⟨i, hlt⟩ hni.1 hni.2
          · by_cases he3 : i = 3
            · subst he3; exact hw3
            · change (wiresFrom [g0] (List.ofFn x)).getD i false = (wiresFrom [g0] (List.ofFn y)).getD i false
              rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        | _ :: _ :: _ :: _ => simp [hg1i] at hg1

lemma no_unary_in_3_maj3 (g0 g1 g2 : Gate)
    (h0 : IsGoodGate g0) (h1 : IsGoodGate g1) (h2 : IsGoodGate g2)
    (hun : g0.inputs.length ≤ 1 ∨ g1.inputs.length ≤ 1 ∨ g2.inputs.length ≤ 1)
    (out : ℕ)
    (hev : ∀ x : Fin 3 → Bool, (wiresFrom [g0, g1, g2] (List.ofFn x)).getD out false = maj3 x) :
    False := by
  have hwf_split (x : Fin 3 → Bool) :
      wiresFrom [g0, g1, g2] (List.ofFn x) =
        wiresFrom [g0, g1] (List.ofFn x) ++
          [g2.op.eval (g2.inputs.map fun i => (wiresFrom [g0, g1] (List.ofFn x)).getD i false)] := by
    simp [wiresFrom]
  by_cases hout5 : out = 5
  · subst hout5
    have hstep2 (x : Fin 3 → Bool) :
        g2.op.eval (g2.inputs.map fun i => (wiresFrom [g0, g1] (List.ofFn x)).getD i false) = maj3 x := by
      have := hev x
      rw [hwf_split x, getD_snoc _ _ false 5 (by rw [wiresFrom_length]; simp)] at this
      exact this
    rcases hun with hu0 | hu1 | hu2
    · have hcard_s0 (w : ℕ) : ((supps3 [g0]).getD w ∅).card ≤ 1 := by
        by_cases hw : w < 3
        · change ((suppStep3 initSupps3 g0).getD w ∅).card ≤ 1
          rw [suppStep3_getD_lt initSupps3 g0 w (by rw [initSupps3_length]; exact hw)]
          exact supp3_card_init w
        · by_cases heq : w = 3
          · subst heq
            change ((suppStep3 initSupps3 g0).getD 3 ∅).card ≤ 1
            rw [suppStep3_getD_eq initSupps3 g0 3 initSupps3_length]
            have := card3_foldl_le initSupps3 g0.inputs 1 supp3_card_init; omega
          · have hlen : (supps3 [g0]).length = 4 := by simp [supps3, suppStep3, initSupps3_length]
            rw [List.getD_eq_default _ _ (by omega)]; simp
      have hcard_s1 (w : ℕ) : ((supps3 [g0, g1]).getD w ∅).card ≤ if w = 4 then 2 else 1 := by
        have hlen1 : (supps3 [g0]).length = 4 := by simp [supps3, suppStep3, initSupps3_length]
        by_cases hw : w < 4
        · have hne : w ≠ 4 := by omega
          simp only [hne, ↓reduceIte]
          change ((suppStep3 (supps3 [g0]) g1).getD w ∅).card ≤ 1
          rw [suppStep3_getD_lt (supps3 [g0]) g1 w (by omega)]
          exact hcard_s0 w
        · by_cases heq : w = 4
          · subst heq; simp only [↓reduceIte]
            change ((suppStep3 (supps3 [g0]) g1).getD 4 ∅).card ≤ 2
            rw [suppStep3_getD_eq (supps3 [g0]) g1 4 hlen1]
            have := card3_foldl_le (supps3 [g0]) g1.inputs 1 hcard_s0
            have := h1.2.1; omega
          · simp only [heq, ↓reduceIte]
            have hlen2 : (supps3 [g0, g1]).length = 5 := by simp [supps3, suppStep3, initSupps3_length]
            rw [List.getD_eq_default _ _ (by omega)]; simp
      have hS5_3 : ((supps3 [g0, g1, g2]).getD 5 ∅).card = 3 := by
        have hle3 : ((supps3 [g0, g1, g2]).getD 5 ∅).card ≤ 3 := Finset.card_le_univ _
        by_contra hne3
        exact not_dep_le2 maj3 (Or.inl rfl) ((supps3 [g0, g1, g2]).getD 5 ∅) (by omega)
          (fun x y hxy => (hev x).symm.trans ((supp3_eval_eq [g0, g1, g2] x y 5 hxy).trans (hev y)))
      have hlen2 : (supps3 [g0, g1]).length = 5 := by simp [supps3, suppStep3, initSupps3_length]
      have hs5_def : (supps3 [g0, g1, g2]).getD 5 ∅ =
          g2.inputs.foldl (fun a i => a ∪ (supps3 [g0, g1]).getD i ∅) ∅ :=
        suppStep3_getD_eq (supps3 [g0, g1]) g2 5 hlen2
      rw [hs5_def] at hS5_3
      match hg2i : g2.inputs with
      | [] => simp [hg2i] at hS5_3
      | [a] =>
        simp only [hg2i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS5_3
        have := hcard_s1 a; split_ifs at this <;> omega
      | [a, b] =>
        simp only [hg2i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS5_3
        have hu := Finset.card_union_le ((supps3 [g0, g1]).getD a ∅) ((supps3 [g0, g1]).getD b ∅)
        have ha := hcard_s1 a; have hb := hcard_s1 b
        have hab4 : (a = 4 ∧ b ≠ 4) ∨ (a ≠ 4 ∧ b = 4) := by
          by_cases ha4 : a = 4 <;> by_cases hb4 : b = 4
          · subst ha4; subst hb4; rw [Finset.union_idempotent] at hS5_3
            simp only [↓reduceIte] at ha; omega
          · exact Or.inl ⟨ha4, hb4⟩
          · exact Or.inr ⟨ha4, hb4⟩
          · split_ifs at ha hb <;> omega
        have hcard4_2 : ((supps3 [g0, g1]).getD 4 ∅).card = 2 := by
          have h4le := hcard_s1 4; simp only [↓reduceIte] at h4le
          rcases hab4 with ⟨rfl, hb4⟩ | ⟨ha4, rfl⟩ <;> split_ifs at ha hb <;> omega
        obtain ⟨u, v, huv, h4uv⟩ := Finset.card_eq_two.mp hcard4_2
        have hdisj : ∀ i ∈ [a, b], i ≠ 4 → (supps3 [g0, g1]).getD i ∅ ∩ (supps3 [g0, g1]).getD 4 ∅ = ∅ := by
          intro i hi hi4
          rcases hab4 with ⟨rfl, hb4⟩ | ⟨ha4, rfl⟩
          · simp at hi; rcases hi with rfl | rfl
            · exact absurd rfl hi4
            · have hdi := Finset.card_union_add_card_inter ((supps3 [g0, g1]).getD 4 ∅) ((supps3 [g0, g1]).getD i ∅)
              have hi1 := hcard_s1 i; split_ifs at hi1; · omega
              rw [Finset.inter_comm]; exact Finset.card_eq_zero.mp (by omega)
          · simp at hi; rcases hi with rfl | rfl
            · have hdi := Finset.card_union_add_card_inter ((supps3 [g0, g1]).getD i ∅) ((supps3 [g0, g1]).getD 4 ∅)
              have hi1 := hcard_s1 i; split_ifs at hi1; · omega
              exact Finset.card_eq_zero.mp (by omega)
            · exact absurd rfl hi4
        refine not_factor_pair maj3 (Or.inl rfl) u v huv
          (fun x => (wiresFrom [g0, g1] (List.ofFn x)).getD 4 false)
          (fun x y hxu hxv => supp3_eval_eq [g0, g1] x y 4 (fun i hi => by
            rw [h4uv, Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl <;> assumption)) ?_
        intro x y hout_ag hw4
        rw [← hstep2 x, ← hstep2 y]
        apply eval_step_eq
        intro i hi
        rw [hg2i] at hi
        by_cases hi4 : i = 4
        · subst hi4; exact hw4
        · apply supp3_eval_eq [g0, g1]
          intro j hj
          have hdj := hdisj i hi hi4
          have hnj : j ∉ (supps3 [g0, g1]).getD 4 ∅ := fun hmem => by
            have := Finset.mem_inter.mpr ⟨hj, hmem⟩
            rw [hdj] at this; exact Finset.notMem_empty _ this
          rw [h4uv, Finset.mem_insert, Finset.mem_singleton, not_or] at hnj
          exact hout_ag j hnj.1 hnj.2
      | _ :: _ :: _ :: _ => have := h2.2.1; simp [hg2i] at this
    · have hcard_s0 (w : ℕ) : ((supps3 [g0]).getD w ∅).card ≤ if w = 3 then 2 else 1 := by
        by_cases hw : w < 3
        · have hne : w ≠ 3 := by omega
          simp only [hne, ↓reduceIte]
          change ((suppStep3 initSupps3 g0).getD w ∅).card ≤ 1
          rw [suppStep3_getD_lt initSupps3 g0 w (by rw [initSupps3_length]; exact hw)]
          exact supp3_card_init w
        · by_cases heq : w = 3
          · subst heq; simp only [↓reduceIte]
            change ((suppStep3 initSupps3 g0).getD 3 ∅).card ≤ 2
            rw [suppStep3_getD_eq initSupps3 g0 3 initSupps3_length]
            have := card3_foldl_le initSupps3 g0.inputs 1 supp3_card_init
            have := h0.2.1; omega
          · simp only [heq, ↓reduceIte]
            have hlen : (supps3 [g0]).length = 4 := by simp [supps3, suppStep3, initSupps3_length]
            rw [List.getD_eq_default _ _ (by omega)]; simp
      have hlen1 : (supps3 [g0]).length = 4 := by simp [supps3, suppStep3, initSupps3_length]
      have hlen2 : (supps3 [g0, g1]).length = 5 := by simp [supps3, suppStep3, initSupps3_length]
      have hS4_sub : (supps3 [g0, g1]).getD 4 ∅ ⊆ (supps3 [g0]).getD 3 ∅ ∨
          ((supps3 [g0, g1]).getD 4 ∅).card ≤ 1 := by
        have h4def : (supps3 [g0, g1]).getD 4 ∅ =
            g1.inputs.foldl (fun a i => a ∪ (supps3 [g0]).getD i ∅) ∅ :=
          suppStep3_getD_eq (supps3 [g0]) g1 4 hlen1
        rw [h4def]
        match hg1i : g1.inputs with
        | [] => right; simp
        | [a1] =>
          simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
          by_cases ha3 : a1 = 3
          · left; subst ha3; exact Finset.Subset.rfl
          · right; have := hcard_s0 a1; simp only [ha3, ↓reduceIte] at this; exact this
        | _ :: _ :: _ => simp [hg1i] at hu1
      have hS5_3 : ((supps3 [g0, g1, g2]).getD 5 ∅).card = 3 := by
        have hle3 : ((supps3 [g0, g1, g2]).getD 5 ∅).card ≤ 3 := Finset.card_le_univ _
        by_contra hne3
        exact not_dep_le2 maj3 (Or.inl rfl) ((supps3 [g0, g1, g2]).getD 5 ∅) (by omega)
          (fun x y hxy => (hev x).symm.trans ((supp3_eval_eq [g0, g1, g2] x y 5 hxy).trans (hev y)))
      have hs5_def : (supps3 [g0, g1, g2]).getD 5 ∅ =
          g2.inputs.foldl (fun a i => a ∪ (supps3 [g0, g1]).getD i ∅) ∅ :=
        suppStep3_getD_eq (supps3 [g0, g1]) g2 5 hlen2
      rw [hs5_def] at hS5_3
      have h3eq : (supps3 [g0, g1]).getD 3 ∅ = (supps3 [g0]).getD 3 ∅ :=
        suppStep3_getD_lt (supps3 [g0]) g1 3 (by omega)
      have h3le : ((supps3 [g0]).getD 3 ∅).card ≤ 2 := by
        have := hcard_s0 3; simp only [↓reduceIte] at this; exact this
      have hcard_s1 (w : ℕ) : ((supps3 [g0, g1]).getD w ∅).card ≤ if w = 3 ∨ w = 4 then 2 else 1 := by
        by_cases hw : w < 4
        · have heq : (supps3 [g0, g1]).getD w ∅ = (supps3 [g0]).getD w ∅ :=
            suppStep3_getD_lt (supps3 [g0]) g1 w (by omega)
          rw [heq]
          have := hcard_s0 w; split_ifs at this ⊢ <;> omega
        · by_cases hw4 : w = 4
          · subst hw4; simp only [or_true, ↓reduceIte]
            rcases hS4_sub with hsub | hle1
            · have := Finset.card_le_card hsub; omega
            · omega
          · have hnot : ¬ (w = 3 ∨ w = 4) := by omega
            simp only [hnot, ↓reduceIte]
            rw [List.getD_eq_default _ _ (by omega)]; simp
      have hsub_or_1 (w : ℕ) : (supps3 [g0, g1]).getD w ∅ ⊆ (supps3 [g0]).getD 3 ∅ ∨
          ((supps3 [g0, g1]).getD w ∅).card ≤ 1 := by
        by_cases hw3 : w = 3
        · left; subst hw3; rw [h3eq]
        · by_cases hw4 : w = 4
          · subst hw4; exact hS4_sub
          · right
            have hnot : ¬ (w = 3 ∨ w = 4) := by omega
            have := hcard_s1 w; simp only [hnot, ↓reduceIte] at this; exact this
      have h3_card2 : ((supps3 [g0]).getD 3 ∅).card = 2 ∧
          (∀ i ∈ g2.inputs, (supps3 [g0, g1]).getD i ∅ ⊆ (supps3 [g0]).getD 3 ∅ ∨
            (supps3 [g0, g1]).getD i ∅ ∩ (supps3 [g0]).getD 3 ∅ = ∅) := by
        match hg2i : g2.inputs with
        | [] => simp [hg2i] at hS5_3
        | [a] =>
          simp only [hg2i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS5_3
          have := hcard_s1 a; split_ifs at this <;> omega
        | [a, b] =>
          simp only [hg2i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS5_3
          rcases hsub_or_1 a with hasub | ha1 <;> rcases hsub_or_1 b with hbsub | hb1
          · have := Finset.card_le_card (Finset.union_subset hasub hbsub); omega
          · have hale := Finset.card_le_card hasub
            have hu := Finset.card_union_le ((supps3 [g0, g1]).getD a ∅) ((supps3 [g0, g1]).getD b ∅)
            have h32 : ((supps3 [g0]).getD 3 ∅).card = 2 := by omega
            have haeq : (supps3 [g0, g1]).getD a ∅ = (supps3 [g0]).getD 3 ∅ :=
              Finset.eq_of_subset_of_card_le hasub (by omega)
            rw [haeq] at hS5_3
            have hdi := Finset.card_union_add_card_inter ((supps3 [g0]).getD 3 ∅) ((supps3 [g0, g1]).getD b ∅)
            have hbi0 : (supps3 [g0, g1]).getD b ∅ ∩ (supps3 [g0]).getD 3 ∅ = ∅ := by
              rw [Finset.inter_comm]; exact Finset.card_eq_zero.mp (by omega)
            refine ⟨h32, fun i hi => ?_⟩
            simp at hi; rcases hi with rfl | rfl
            · exact Or.inl hasub
            · exact Or.inr hbi0
          · have hble := Finset.card_le_card hbsub
            have hu := Finset.card_union_le ((supps3 [g0, g1]).getD a ∅) ((supps3 [g0, g1]).getD b ∅)
            have h32 : ((supps3 [g0]).getD 3 ∅).card = 2 := by omega
            have hbeq : (supps3 [g0, g1]).getD b ∅ = (supps3 [g0]).getD 3 ∅ :=
              Finset.eq_of_subset_of_card_le hbsub (by omega)
            rw [hbeq] at hS5_3
            have hdi := Finset.card_union_add_card_inter ((supps3 [g0, g1]).getD a ∅) ((supps3 [g0]).getD 3 ∅)
            have hai0 : (supps3 [g0, g1]).getD a ∅ ∩ (supps3 [g0]).getD 3 ∅ = ∅ :=
              Finset.card_eq_zero.mp (by omega)
            refine ⟨h32, fun i hi => ?_⟩
            simp at hi; rcases hi with rfl | rfl
            · exact Or.inr hai0
            · exact Or.inl hbsub
          · have hu := Finset.card_union_le ((supps3 [g0, g1]).getD a ∅) ((supps3 [g0, g1]).getD b ∅)
            omega
        | _ :: _ :: _ :: _ => have := h2.2.1; simp [hg2i] at this
      obtain ⟨h3card, hdisj_or_sub⟩ := h3_card2
      obtain ⟨u, v, huv, h3uv⟩ := Finset.card_eq_two.mp h3card
      have hg2_wire (i : ℕ) (hi : i ∈ g2.inputs) (hsub : (supps3 [g0, g1]).getD i ∅ ⊆ (supps3 [g0]).getD 3 ∅) :
          (supps3 [g0, g1]).getD i ∅ = ∅ ∨ i = 3 ∨ (i = 4 ∧ g1.inputs = [3]) := by
        by_cases hemp : (supps3 [g0, g1]).getD i ∅ = ∅
        · exact Or.inl hemp
        · right
          by_cases hi3 : i = 3
          · exact Or.inl hi3
          · by_cases hi4 : i = 4
            · right; refine ⟨hi4, ?_⟩
              have h4def : (supps3 [g0, g1]).getD 4 ∅ =
                  g1.inputs.foldl (fun a j => a ∪ (supps3 [g0]).getD j ∅) ∅ :=
                suppStep3_getD_eq (supps3 [g0]) g1 4 hlen1
              match hg1i : g1.inputs with
              | [] => subst hi4; simp [hg1i] at h4def; exact absurd h4def hemp
              | [a1] =>
                by_cases ha3 : a1 = 3
                · subst ha3; rfl
                · exfalso
                  have h4le1 : ((supps3 [g0, g1]).getD 4 ∅).card ≤ 1 := by
                    rw [h4def, hg1i]; simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
                    have := hcard_s0 a1; simp only [ha3, ↓reduceIte] at this; exact this
                  match hg2i : g2.inputs with
                  | [] => simp [hg2i] at hS5_3
                  | [a] =>
                    simp only [hg2i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS5_3
                    simp [hg2i] at hi; subst hi; subst hi4; omega
                  | [a, b] =>
                    simp only [hg2i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS5_3
                    simp [hg2i] at hi; subst hi4
                    rcases hi with rfl | rfl
                    · rcases hsub_or_1 b with hbs | hb1
                      · have := Finset.card_le_card (Finset.union_subset hsub hbs); omega
                      · have := Finset.card_union_le ((supps3 [g0, g1]).getD 4 ∅) ((supps3 [g0, g1]).getD b ∅); omega
                    · rcases hsub_or_1 a with has | ha1
                      · have := Finset.card_le_card (Finset.union_subset has hsub); omega
                      · have := Finset.card_union_le ((supps3 [g0, g1]).getD a ∅) ((supps3 [g0, g1]).getD 4 ∅); omega
                  | _ :: _ :: _ :: _ => have := h2.2.1; simp [hg2i] at this
              | _ :: _ :: _ => simp [hg1i] at hu1
            · exfalso
              have hnot : ¬ (i = 3 ∨ i = 4) := by omega
              have hile1 : ((supps3 [g0, g1]).getD i ∅).card ≤ 1 := by
                have := hcard_s1 i; simp only [hnot, ↓reduceIte] at this; exact this
              match hg2i : g2.inputs with
              | [] => simp [hg2i] at hS5_3
              | [a] =>
                simp only [hg2i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS5_3
                simp [hg2i] at hi; subst hi; omega
              | [a, b] =>
                simp only [hg2i, List.foldl_cons, List.foldl_nil, Finset.empty_union] at hS5_3
                simp [hg2i] at hi
                rcases hi with rfl | rfl
                · rcases hsub_or_1 b with hbs | hb1
                  · have := Finset.card_le_card (Finset.union_subset hsub hbs); omega
                  · have := Finset.card_union_le ((supps3 [g0, g1]).getD i ∅) ((supps3 [g0, g1]).getD b ∅); omega
                · rcases hsub_or_1 a with has | ha1
                  · have := Finset.card_le_card (Finset.union_subset has hsub); omega
                  · have := Finset.card_union_le ((supps3 [g0, g1]).getD a ∅) ((supps3 [g0, g1]).getD i ∅); omega
              | _ :: _ :: _ :: _ => have := h2.2.1; simp [hg2i] at this
      refine not_factor_pair maj3 (Or.inl rfl) u v huv
        (fun x => (wiresFrom [g0] (List.ofFn x)).getD 3 false)
        (fun x y hxu hxv => supp3_eval_eq [g0] x y 3 (fun i hi => by
          rw [h3uv, Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl <;> assumption)) ?_
      intro x y hout_ag hw3
      rw [← hstep2 x, ← hstep2 y]
      apply eval_step_eq
      intro i hi
      rcases hdisj_or_sub i hi with hsub | hdisj
      · rcases hg2_wire i hi hsub with hemp | rfl | ⟨rfl, hg1_3⟩
        · apply supp3_eval_eq [g0, g1]; intro j hj; rw [hemp] at hj; exact absurd hj (Finset.notMem_empty _)
        · have hlen_x : (wiresFrom [g0] (List.ofFn x)).length = 4 := by rw [wiresFrom_length]; simp
          have hlen_y : (wiresFrom [g0] (List.ofFn y)).length = 4 := by rw [wiresFrom_length]; simp
          change (wiresFrom [g0] (List.ofFn x) ++ _).getD 3 false =
            (wiresFrom [g0] (List.ofFn y) ++ _).getD 3 false
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact hw3
        · have hlen_x : (wiresFrom [g0] (List.ofFn x)).length = 4 := by rw [wiresFrom_length]; simp
          have hlen_y : (wiresFrom [g0] (List.ofFn y)).length = 4 := by rw [wiresFrom_length]; simp
          change (wiresFrom [g0] (List.ofFn x) ++ _).getD 4 false =
            (wiresFrom [g0] (List.ofFn y) ++ _).getD 4 false
          rw [getD_snoc _ _ false 4 hlen_x, getD_snoc _ _ false 4 hlen_y]
          simp only [hg1_3, List.map_cons, List.map_nil]
          change g1.op.eval [(wiresFrom [g0] (List.ofFn x)).getD 3 false] =
            g1.op.eval [(wiresFrom [g0] (List.ofFn y)).getD 3 false]
          rw [hw3]
      · apply supp3_eval_eq [g0, g1]
        intro j hj
        have hnj : j ∉ (supps3 [g0]).getD 3 ∅ := fun hmem => by
          have := Finset.mem_inter.mpr ⟨hj, hmem⟩
          rw [hdisj] at this; exact Finset.notMem_empty _ this
        rw [h3uv, Finset.mem_insert, Finset.mem_singleton, not_or] at hnj
        exact hout_ag j hnj.1 hnj.2
    · match hg2i : g2.inputs with
      | [] =>
        have hconst : ∀ x y : Fin 3 → Bool, maj3 x = maj3 y := by
          intro x y; rw [← hstep2 x, ← hstep2 y, hg2i]; rfl
        have : maj3 (fun _ => false) ≠ maj3 (fun _ => true) := by decide
        exact this (hconst _ _)
      | [a] =>
        rcases h2.1 with hg2a | hg2o | hg2n
        · refine no_size_2_maj3_or_not maj3 (Or.inl rfl) [g0, g1] (by simp)
            (fun g hg => by simp at hg; rcases hg with rfl | rfl; exact h0.2.1; exact h1.2.1) a ?_
          intro x; have := hstep2 x; rw [hg2a, hg2i] at this; simpa [GateOp.eval] using this
        · refine no_size_2_maj3_or_not maj3 (Or.inl rfl) [g0, g1] (by simp)
            (fun g hg => by simp at hg; rcases hg with rfl | rfl; exact h0.2.1; exact h1.2.1) a ?_
          intro x; have := hstep2 x; rw [hg2o, hg2i] at this; simpa [GateOp.eval] using this
        · refine no_size_2_maj3_or_not (fun x => !maj3 x) (Or.inr rfl) [g0, g1] (by simp)
            (fun g hg => by simp at hg; rcases hg with rfl | rfl; exact h0.2.1; exact h1.2.1) a ?_
          intro x; have := hstep2 x; rw [hg2n, hg2i] at this
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at this
          rw [← this, Bool.not_not]
      | _ :: _ :: _ => simp [hg2i] at hu2
  · by_cases hout_lt5 : out < 5
    · refine no_size_2_maj3_or_not maj3 (Or.inl rfl) [g0, g1] (by simp)
        (fun g hg => by simp at hg; rcases hg with rfl | rfl; exact h0.2.1; exact h1.2.1) out ?_
      intro x
      have := hev x
      rw [hwf_split x, List.getD_append _ _ _ _ (by rw [wiresFrom_length]; simp; omega)] at this
      exact this
    · have := hev (fun _ => true)
      rw [List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)] at this
      have hm : maj3 (fun _ => true) = true := by decide
      rw [hm] at this
      exact Bool.noConfusion this

lemma no_mono_3_maj3 (g0 g1 g2 : Gate)
    (h0 : (g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs.length = 2)
    (h1 : (g1.op = GateOp.and ∨ g1.op = GateOp.or) ∧ g1.inputs.length = 2)
    (h2 : (g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length = 2)
    (out : ℕ)
    (hev : ∀ x : Fin 3 → Bool, (wiresFrom [g0, g1, g2] (List.ofFn x)).getD out false = maj3 x) :
    False := by
  have hwf_split (x : Fin 3 → Bool) :
      wiresFrom [g0, g1, g2] (List.ofFn x) =
        wiresFrom [g0, g1] (List.ofFn x) ++
          [g2.op.eval (g2.inputs.map fun i => (wiresFrom [g0, g1] (List.ofFn x)).getD i false)] := by
    simp [wiresFrom]
  have hout5 : out = 5 := by
    by_contra hne
    by_cases hlt : out < 5
    · refine no_size_2_maj3_or_not maj3 (Or.inl rfl) [g0, g1] (by simp)
        (fun g hg => by simp at hg; rcases hg with rfl | rfl <;> omega) out ?_
      intro x; have := hev x
      rw [hwf_split x, List.getD_append _ _ _ _ (by rw [wiresFrom_length]; simp; omega)] at this
      exact this
    · have := hev (fun _ => true)
      rw [List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)] at this
      have hm : maj3 (fun _ => true) = true := by decide
      rw [hm] at this; exact Bool.noConfusion this
  subst hout5
  let f (k : ℕ) (x : Fin 3 → Bool) : Bool := (wiresFrom [g0, g1] (List.ofFn x)).getD k false
  have hf_in (i : Fin 3) (x : Fin 3 → Bool) : f i.val x = x i := by
    change (wiresFrom [g0, g1] (List.ofFn x)).getD i.val false = x i
    rw [wiresFrom_prefix [g0, g1] _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hf_ge5 (k : ℕ) (hk : 5 ≤ k) (x : Fin 3 → Bool) : f k x = false :=
    List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
  have hf3 (x : Fin 3 → Bool) :
      f 3 x = g0.op.eval (g0.inputs.map fun i => if i < 3 then f i x else false) := by
    have hl0 : (List.ofFn x).length = 3 := by simp
    change (wiresFrom [g0] (List.ofFn x) ++ _).getD 3 false = _
    rw [List.getD_append _ _ _ _ (by rw [wiresFrom_length]; simp)]
    change (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).getD 3 false = _
    rw [getD_snoc _ _ false 3 hl0]
    congr 1; apply List.map_congr_left; intro i _
    split_ifs with hi
    · rw [hf_in ⟨i, hi⟩ x, List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
    · exact List.getD_eq_default _ _ (by simp; omega)
  have hf4 (x : Fin 3 → Bool) :
      f 4 x = g1.op.eval (g1.inputs.map fun i => if i < 4 then f i x else false) := by
    have hl1 : (wiresFrom [g0] (List.ofFn x)).length = 4 := by rw [wiresFrom_length]; simp
    change (wiresFrom [g0] (List.ofFn x) ++ _).getD 4 false = _
    rw [getD_snoc _ _ false 4 hl1]
    congr 1; apply List.map_congr_left; intro i _
    split_ifs with hi
    · change (wiresFrom [g0] (List.ofFn x)).getD i false = (wiresFrom [g0] (List.ofFn x) ++ _).getD i false
      rw [List.getD_append _ _ _ _ (by rw [hl1]; exact hi)]
    · change (wiresFrom [g0] (List.ofFn x)).getD i false = false
      exact List.getD_eq_default _ _ (by rw [hl1]; omega)
  have hf5 (x : Fin 3 → Bool) :
      g2.op.eval (g2.inputs.map fun i => f i x) = maj3 x := by
    have := hev x
    rw [hwf_split x, getD_snoc _ _ false 5 (by rw [wiresFrom_length]; simp)] at this
    exact this
  have hno2 (k : ℕ) (hk : ∀ x, f k x = maj3 x) : False :=
    no_size_2_maj3_or_not maj3 (Or.inl rfl) [g0, g1] (by simp)
      (fun g hg => by simp at hg; rcases hg with rfl | rfl <;> omega) k hk
  let e1 (i : Fin 3) : Fin 3 → Bool := fun j => decide (j = i)
  let e2 (i : Fin 3) : Fin 3 → Bool := fun j => decide (j ≠ i)
  have hm1 (i : Fin 3) : maj3 (e1 i) = false := by revert i; decide
  have hm2 (i : Fin 3) : maj3 (e2 i) = true := by revert i; decide
  match hg2i : g2.inputs with
  | [a, b] =>
    rcases h2.1 with hg2a | hg2o
    · have hab (x : Fin 3 → Bool) : (f a x && f b x) = maj3 x := by
        have := hf5 x; rw [hg2a, hg2i] at this; simpa [GateOp.eval] using this
      have ha_t (i : Fin 3) : f a (e2 i) = true := by
        have := hab (e2 i); rw [hm2 i, Bool.and_eq_true] at this; exact this.1
      have hb_t (i : Fin 3) : f b (e2 i) = true := by
        have := hab (e2 i); rw [hm2 i, Bool.and_eq_true] at this; exact this.2
      have h34 (k : ℕ) (ht : ∀ i : Fin 3, f k (e2 i) = true) : k = 3 ∨ k = 4 := by
        by_cases hlt3 : k < 3
        · have := ht ⟨k, hlt3⟩; rw [hf_in ⟨k, hlt3⟩] at this; simp [e2] at this
        · by_cases hge5 : 5 ≤ k
          · have := ht 0; rw [hf_ge5 k hge5] at this; exact Bool.noConfusion this
          · omega
      have ha34 := h34 a ha_t
      have hb34 := h34 b hb_t
      have hpair : ∀ x, (f 3 x && f 4 x) = maj3 x := by
        rcases ha34 with rfl | rfl <;> rcases hb34 with rfl | rfl
        · exfalso; exact hno2 3 (fun x => by have := hab x; simpa using this)
        · exact hab
        · intro x; rw [Bool.and_comm]; exact hab x
        · exfalso; exact hno2 4 (fun x => by have := hab x; simpa using this)
      have hf3_t (i : Fin 3) : f 3 (e2 i) = true := by
        have := hpair (e2 i); rw [hm2 i, Bool.and_eq_true] at this; exact this.1
      have hf4_t (i : Fin 3) : f 4 (e2 i) = true := by
        have := hpair (e2 i); rw [hm2 i, Bool.and_eq_true] at this; exact this.2
      match hg0i : g0.inputs with
      | [p, q] =>
        have hfg0_or : g0.op = GateOp.or ∧ p < 3 ∧ q < 3 ∧ p ≠ q := by
          rcases h0.1 with hg0a | hg0o
          · exfalso
            have hp_t (i : Fin 3) : ∃ hp : p < 3, e2 i ⟨p, hp⟩ = true := by
              have := hf3 (e2 i); rw [hg0a, hg0i, hf3_t i] at this
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true] at this
              symm at this
              rw [Bool.and_eq_true] at this
              have h1 := this.1
              by_cases hp : p < 3
              · rw [ite_eq_left_iff.mpr (fun hn => absurd hp hn)] at h1
                exact ⟨hp, (hf_in ⟨p, hp⟩ (e2 i)).symm.trans h1⟩
              · rw [ite_eq_right_iff.mpr (fun h => absurd h hp)] at h1
                exact Bool.noConfusion h1
            obtain ⟨hp3, _⟩ := hp_t 0
            obtain ⟨_, hpv⟩ := hp_t ⟨p, hp3⟩
            simp [e2] at hpv
          · refine ⟨hg0o, ?_⟩
            have hor (x : Fin 3 → Bool) :
                f 3 x = ((if p < 3 then f p x else false) || (if q < 3 then f q x else false)) := by
              have := hf3 x; rw [hg0o, hg0i] at this; simpa [GateOp.eval] using this
            by_cases hp3 : p < 3
            · by_cases hq3 : q < 3
              · by_cases hpq : p = q
                · exfalso; subst hpq
                  have := hf3_t ⟨p, hp3⟩; rw [hor, ite_eq_left_iff.mpr (fun h => absurd hp3 h), hf_in ⟨p, hp3⟩] at this; simp [e2] at this
                · exact ⟨hp3, hq3, hpq⟩
              · exfalso
                have := hf3_t ⟨p, hp3⟩; rw [hor, ite_eq_left_iff.mpr (fun h => absurd hp3 h), ite_eq_right_iff.mpr (fun h => absurd h hq3), hf_in ⟨p, hp3⟩] at this; simp [e2] at this
            · exfalso
              by_cases hq3 : q < 3
              · have := hf3_t ⟨q, hq3⟩; rw [hor, ite_eq_right_iff.mpr (fun h => absurd h hp3), ite_eq_left_iff.mpr (fun h => absurd hq3 h), hf_in ⟨q, hq3⟩] at this; simp [e2] at this
              · have := hf3_t 0; rw [hor, ite_eq_right_iff.mpr (fun h => absurd h hp3), ite_eq_right_iff.mpr (fun h => absurd h hq3)] at this; simp at this
        rcases hfg0_or with ⟨hg0o, hp3, hq3, hpq⟩
        let u : Fin 3 := ⟨p, hp3⟩
        let v : Fin 3 := ⟨q, hq3⟩
        have huv : u ≠ v := fun h => hpq (congrArg Fin.val h)
        let w : Fin 3 := ⟨3 - p - q, by omega⟩
        have hwu : w ≠ u := by intro h; have := congrArg Fin.val h; dsimp [w, u] at this; omega
        have hwv : w ≠ v := by intro h; have := congrArg Fin.val h; dsimp [w, v] at this; omega
        have hf3_val (x : Fin 3 → Bool) : f 3 x = (x u || x v) := by
          have := hf3 x; rw [hg0o, hg0i] at this
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, hp3, hq3, ↓reduceIte] at this
          rw [this, hf_in u x, hf_in v x]
        have hf4_fu : f 4 (e1 u) = false := by
          have := hpair (e1 u); rw [hm1 u, hf3_val (e1 u)] at this
          simp [e1] at this; exact this
        have hf4_fv : f 4 (e1 v) = false := by
          have := hpair (e1 v); rw [hm1 v, hf3_val (e1 v)] at this
          simp [e1] at this; exact this
        match hg1i : g1.inputs with
        | [r, t] =>
          rcases h1.1 with hg1a | hg1o
          · have hrt (x : Fin 3 → Bool) :
                f 4 x = ((if r < 4 then f r x else false) && (if t < 4 then f t x else false)) := by
              have := hf4 x; rw [hg1a, hg1i] at this; simpa [GateOp.eval] using this
            have hmust3 (k : ℕ) (hk : ∀ i : Fin 3, (if k < 4 then f k (e2 i) else false) = true) : k = 3 := by
              by_cases hlt3 : k < 3
              · have := hk ⟨k, hlt3⟩; rw [ite_eq_left_iff.mpr (by omega), hf_in ⟨k, hlt3⟩] at this; simp [e2] at this
              · by_cases hlt4 : k < 4
                · omega
                · have := hk 0; rw [ite_eq_right_iff.mpr (fun h => absurd h hlt4)] at this; exact Bool.noConfusion this
            have hr3 : r = 3 := hmust3 r (fun i => by
              have := hf4_t i; rw [hrt, Bool.and_eq_true] at this; exact this.1)
            have ht3 : t = 3 := hmust3 t (fun i => by
              have := hf4_t i; rw [hrt, Bool.and_eq_true] at this; exact this.2)
            have := hf4_fu; rw [hrt, hr3, ht3] at this; simp [hf3_val, e1] at this
          · have hrt (x : Fin 3 → Bool) :
                f 4 x = ((if r < 4 then f r x else false) || (if t < 4 then f t x else false)) := by
              have := hf4 x; rw [hg1o, hg1i] at this; simpa [GateOp.eval] using this
            have hfalse_e2w (k : ℕ)
                (hku : (if k < 4 then f k (e1 u) else false) = false)
                (hkv : (if k < 4 then f k (e1 v) else false) = false) :
                (if k < 4 then f k (e2 w) else false) = false := by
              by_cases hk4 : k < 4
              · simp only [hk4, ↓reduceIte] at hku hkv ⊢
                by_cases hk3 : k = 3
                · subst hk3; rw [hf3_val] at hku; simp [e1] at hku
                · have hlt3 : k < 3 := by omega
                  rw [hf_in ⟨k, hlt3⟩] at hku hkv ⊢
                  have hne_u : (⟨k, hlt3⟩ : Fin 3) ≠ u := fun h => by rw [h] at hku; simp [e1] at hku
                  have hne_v : (⟨k, hlt3⟩ : Fin 3) ≠ v := fun h => by rw [h] at hkv; simp [e1] at hkv
                  have hkw : (⟨k, hlt3⟩ : Fin 3) = w := by
                    ext; have := Fin.val_ne_of_ne hne_u; have := Fin.val_ne_of_ne hne_v
                    dsimp [w, u, v] at *; omega
                  rw [hkw]; simp [e2]
              · simp [hk4]
            have hru : (if r < 4 then f r (e1 u) else false) = false := by
              have := hf4_fu; rw [hrt, Bool.or_eq_false_iff] at this; exact this.1
            have hrv : (if r < 4 then f r (e1 v) else false) = false := by
              have := hf4_fv; rw [hrt, Bool.or_eq_false_iff] at this; exact this.1
            have htu : (if t < 4 then f t (e1 u) else false) = false := by
              have := hf4_fu; rw [hrt, Bool.or_eq_false_iff] at this; exact this.2
            have htv : (if t < 4 then f t (e1 v) else false) = false := by
              have := hf4_fv; rw [hrt, Bool.or_eq_false_iff] at this; exact this.2
            have := hf4_t w
            rw [hrt, hfalse_e2w r hru hrv, hfalse_e2w t htu htv] at this
            simp at this
        | [] | [_] | _ :: _ :: _ :: _ => simp [hg1i] at h1
      | [] | [_] | _ :: _ :: _ :: _ => simp [hg0i] at h0
    · have hab (x : Fin 3 → Bool) : (f a x || f b x) = maj3 x := by
        have := hf5 x; rw [hg2o, hg2i] at this; simpa [GateOp.eval] using this
      have ha_f (i : Fin 3) : f a (e1 i) = false := by
        have := hab (e1 i); rw [hm1 i, Bool.or_eq_false_iff] at this; exact this.1
      have hb_f (i : Fin 3) : f b (e1 i) = false := by
        have := hab (e1 i); rw [hm1 i, Bool.or_eq_false_iff] at this; exact this.2
      have hnot_lt3 (k : ℕ) (hf_k : ∀ i : Fin 3, f k (e1 i) = false) : ¬ k < 3 := by
        intro hlt3; have := hf_k ⟨k, hlt3⟩; rw [hf_in ⟨k, hlt3⟩] at this; simp [e1] at this
      have ha_ge3 : 3 ≤ a := by have := hnot_lt3 a ha_f; omega
      have hb_ge3 : 3 ≤ b := by have := hnot_lt3 b hb_f; omega
      have ha_lt5 : a < 5 := by
        by_contra hge
        have : ∀ x, f b x = maj3 x := fun x => by have := hab x; rw [hf_ge5 a (by omega)] at this; simpa using this
        exact hno2 b this
      have hb_lt5 : b < 5 := by
        by_contra hge
        have : ∀ x, f a x = maj3 x := fun x => by have := hab x; rw [hf_ge5 b (by omega)] at this; simpa using this
        exact hno2 a this
      have hpair : ∀ x, (f 3 x || f 4 x) = maj3 x := by
        have ha34 : a = 3 ∨ a = 4 := by omega
        have hb34 : b = 3 ∨ b = 4 := by omega
        rcases ha34 with rfl | rfl <;> rcases hb34 with rfl | rfl
        · exfalso; exact hno2 3 (fun x => by have := hab x; simpa using this)
        · exact hab
        · intro x; rw [Bool.or_comm]; exact hab x
        · exfalso; exact hno2 4 (fun x => by have := hab x; simpa using this)
      have hf3_f (i : Fin 3) : f 3 (e1 i) = false := by
        have := hpair (e1 i); rw [hm1 i, Bool.or_eq_false_iff] at this; exact this.1
      have hf4_f (i : Fin 3) : f 4 (e1 i) = false := by
        have := hpair (e1 i); rw [hm1 i, Bool.or_eq_false_iff] at this; exact this.2
      match hg0i : g0.inputs with
      | [p, q] =>
        have hfg0_and : g0.op = GateOp.and ∧ p < 3 ∧ q < 3 ∧ p ≠ q := by
          rcases h0.1 with hg0a | hg0o
          · refine ⟨hg0a, ?_⟩
            have hand (x : Fin 3 → Bool) :
                f 3 x = ((if p < 3 then f p x else false) && (if q < 3 then f q x else false)) := by
              have := hf3 x; rw [hg0a, hg0i] at this; simpa [GateOp.eval] using this
            by_cases hp3 : p < 3
            · by_cases hq3 : q < 3
              · by_cases hpq : p = q
                · exfalso; subst hpq
                  have := hf3_f ⟨p, hp3⟩; rw [hand, ite_eq_left_iff.mpr (fun h => absurd hp3 h), hf_in ⟨p, hp3⟩] at this; simp [e1] at this
                · exact ⟨hp3, hq3, hpq⟩
              · exfalso
                exact hno2 4 (fun x => by
                  have h3z : f 3 x = false := by rw [hand, ite_eq_right_iff.mpr (fun h => absurd h hq3)]; simp
                  have := hpair x; rwa [h3z, Bool.false_or] at this)
            · exfalso
              exact hno2 4 (fun x => by
                have h3z : f 3 x = false := by rw [hand, ite_eq_right_iff.mpr (fun h => absurd h hp3)]; simp
                have := hpair x; rwa [h3z, Bool.false_or] at this)
          · exfalso
            have hor (x : Fin 3 → Bool) :
                f 3 x = ((if p < 3 then f p x else false) || (if q < 3 then f q x else false)) := by
              have := hf3 x; rw [hg0o, hg0i] at this; simpa [GateOp.eval] using this
            by_cases hp3 : p < 3
            · have := hf3_f ⟨p, hp3⟩; rw [hor, ite_eq_left_iff.mpr (fun h => absurd hp3 h), hf_in ⟨p, hp3⟩] at this; simp [e1] at this
            · by_cases hq3 : q < 3
              · have := hf3_f ⟨q, hq3⟩; rw [hor, ite_eq_left_iff.mpr (fun h => absurd hq3 h), hf_in ⟨q, hq3⟩] at this; simp [e1] at this
              · exact hno2 4 (fun x => by
                  have h3z : f 3 x = false := by rw [hor, ite_eq_right_iff.mpr (fun h => absurd h hp3), ite_eq_right_iff.mpr (fun h => absurd h hq3)]; rfl
                  have := hpair x; rwa [h3z, Bool.false_or] at this)
        rcases hfg0_and with ⟨hg0a, hp3, hq3, hpq⟩
        let u : Fin 3 := ⟨p, hp3⟩
        let v : Fin 3 := ⟨q, hq3⟩
        have huv : u ≠ v := fun h => hpq (congrArg Fin.val h)
        let w : Fin 3 := ⟨3 - p - q, by omega⟩
        have hwu : w ≠ u := by intro h; have := congrArg Fin.val h; dsimp [w, u] at this; omega
        have hwv : w ≠ v := by intro h; have := congrArg Fin.val h; dsimp [w, v] at this; omega
        have hf3_val (x : Fin 3 → Bool) : f 3 x = (x u && x v) := by
          have := hf3 x; rw [hg0a, hg0i] at this
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, hp3, hq3, ↓reduceIte] at this
          rw [this, hf_in u x, hf_in v x]
        have hf4_tu : f 4 (e2 u) = true := by
          have := hpair (e2 u); rw [hm2 u, hf3_val (e2 u)] at this
          simp [e2] at this; exact this
        have hf4_tv : f 4 (e2 v) = true := by
          have := hpair (e2 v); rw [hm2 v, hf3_val (e2 v)] at this
          simp [e2] at this; exact this
        match hg1i : g1.inputs with
        | [r, t] =>
          rcases h1.1 with hg1a | hg1o
          · have hrt (x : Fin 3 → Bool) :
                f 4 x = ((if r < 4 then f r x else false) && (if t < 4 then f t x else false)) := by
              have := hf4 x; rw [hg1a, hg1i] at this; simpa [GateOp.eval] using this
            have htrue_e1w (k : ℕ)
                (hku : (if k < 4 then f k (e2 u) else false) = true)
                (hkv : (if k < 4 then f k (e2 v) else false) = true) :
                (if k < 4 then f k (e1 w) else false) = true := by
              by_cases hk4 : k < 4
              · simp only [hk4, ↓reduceIte] at hku hkv ⊢
                by_cases hk3 : k = 3
                · subst hk3; rw [hf3_val] at hku; simp [e2] at hku
                · have hlt3 : k < 3 := by omega
                  rw [hf_in ⟨k, hlt3⟩] at hku hkv ⊢
                  have hne_u : (⟨k, hlt3⟩ : Fin 3) ≠ u := fun h => by rw [h] at hku; simp [e2] at hku
                  have hne_v : (⟨k, hlt3⟩ : Fin 3) ≠ v := fun h => by rw [h] at hkv; simp [e2] at hkv
                  have hkw : (⟨k, hlt3⟩ : Fin 3) = w := by
                    ext; have := Fin.val_ne_of_ne hne_u; have := Fin.val_ne_of_ne hne_v
                    dsimp [w, u, v] at *; omega
                  rw [hkw]; simp [e1]
              · simp only [hk4, ↓reduceIte] at hku; exact Bool.noConfusion hku
            have hru : (if r < 4 then f r (e2 u) else false) = true := by
              have := hf4_tu; rw [hrt, Bool.and_eq_true] at this; exact this.1
            have hrv : (if r < 4 then f r (e2 v) else false) = true := by
              have := hf4_tv; rw [hrt, Bool.and_eq_true] at this; exact this.1
            have htu : (if t < 4 then f t (e2 u) else false) = true := by
              have := hf4_tu; rw [hrt, Bool.and_eq_true] at this; exact this.2
            have htv : (if t < 4 then f t (e2 v) else false) = true := by
              have := hf4_tv; rw [hrt, Bool.and_eq_true] at this; exact this.2
            have := hf4_f w
            rw [hrt, htrue_e1w r hru hrv, htrue_e1w t htu htv] at this
            simp at this
          · have hrt (x : Fin 3 → Bool) :
                f 4 x = ((if r < 4 then f r x else false) || (if t < 4 then f t x else false)) := by
              have := hf4 x; rw [hg1o, hg1i] at this; simpa [GateOp.eval] using this
            have hfalse_e2u (k : ℕ)
                (hk : ∀ i : Fin 3, (if k < 4 then f k (e1 i) else false) = false) :
                (if k < 4 then f k (e2 u) else false) = false := by
              by_cases hk4 : k < 4
              · simp only [hk4, ↓reduceIte]
                by_cases hk3 : k = 3
                · subst hk3; rw [hf3_val]; simp [e2]
                · have hlt3 : k < 3 := by omega
                  have := hk ⟨k, hlt3⟩; rw [ite_eq_left_iff.mpr (fun h => absurd hk4 h), hf_in ⟨k, hlt3⟩] at this; simp [e1] at this
              · simp [hk4]
            have hrf : ∀ i, (if r < 4 then f r (e1 i) else false) = false := fun i => by
              have := hf4_f i; rw [hrt, Bool.or_eq_false_iff] at this; exact this.1
            have htf : ∀ i, (if t < 4 then f t (e1 i) else false) = false := fun i => by
              have := hf4_f i; rw [hrt, Bool.or_eq_false_iff] at this; exact this.2
            have := hf4_tu
            rw [hrt, hfalse_e2u r hrf, hfalse_e2u t htf] at this
            simp at this
        | [] | [_] | _ :: _ :: _ :: _ => simp [hg1i] at h1
      | [] | [_] | _ :: _ :: _ :: _ => simp [hg0i] at h0
  | [] | [_] | _ :: _ :: _ :: _ => simp [hg2i] at h2

theorem no_size_3_maj3 : ¬ HasCircuitSize 3 maj3 3 := by
  rintro ⟨C0, hC0, hsz0, hev0⟩
  obtain ⟨C, hCgood, hCsz, hCev⟩ := good_of_fanInTwo hC0
  have hev : ∀ x : Fin 3 → Bool, (wiresFrom C.gates (List.ofFn x)).getD C.output false = maj3 x :=
    fun x => (hCev _).trans (hev0 x)
  have hlen : C.gates.length ≤ 3 := by
    change C.gates.length = C0.gates.length at hCsz
    change C0.gates.length ≤ 3 at hsz0
    omega
  by_cases hle2 : C.gates.length ≤ 2
  · exact no_size_2_maj3_or_not maj3 (Or.inl rfl) C.gates hle2
      (fun g hg => (hCgood g hg).2.1) C.output hev
  · match hgs : C.gates with
    | [g0, g1, g2] =>
      have h0 := hCgood g0 (by simp [hgs])
      have h1 := hCgood g1 (by simp [hgs])
      have h2 := hCgood g2 (by simp [hgs])
      rw [hgs] at hev
      by_cases hun : g0.inputs.length ≤ 1 ∨ g1.inputs.length ≤ 1 ∨ g2.inputs.length ≤ 1
      · exact no_unary_in_3_maj3 g0 g1 g2 h0 h1 h2 hun C.output hev
      · push Not at hun
        have hlen0 : g0.inputs.length = 2 := by have := h0.2.1; omega
        have hlen1 : g1.inputs.length = 2 := by have := h1.2.1; omega
        have hlen2 : g2.inputs.length = 2 := by have := h2.2.1; omega
        have hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or :=
          h0.1.elim Or.inl (fun h => h.elim Or.inr (fun hn => by have := h0.2.2 hn; omega))
        have hop1 : g1.op = GateOp.and ∨ g1.op = GateOp.or :=
          h1.1.elim Or.inl (fun h => h.elim Or.inr (fun hn => by have := h1.2.2 hn; omega))
        have hop2 : g2.op = GateOp.and ∨ g2.op = GateOp.or :=
          h2.1.elim Or.inl (fun h => h.elim Or.inr (fun hn => by have := h2.2.2 hn; omega))
        exact no_mono_3_maj3 g0 g1 g2 ⟨hop0, hlen0⟩ ⟨hop1, hlen1⟩ ⟨hop2, hlen2⟩ C.output hev
    | [] | [_] | [_, _] => simp [hgs] at hle2
    | _ :: _ :: _ :: _ :: _ => simp only [hgs, List.length_cons] at hlen; omega

def targetEdges : List ℕ :=
  [0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 3, 7, 6, 7]

def targetFn (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < targetEdges.length / 2,
    (List.ofFn x).getD (targetEdges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (targetEdges.getD (2 * i + 1) 0) false = true)

def witnessGates : List Gate :=
  [⟨GateOp.or, [0, 1]⟩,
   ⟨GateOp.and, [4, 8]⟩,
   ⟨GateOp.or, [0, 2]⟩,
   ⟨GateOp.and, [5, 10]⟩,
   ⟨GateOp.or, [3, 8]⟩,
   ⟨GateOp.or, [6, 7]⟩,
   ⟨GateOp.and, [12, 13]⟩,
   ⟨GateOp.and, [6, 7]⟩,
   ⟨GateOp.or, [9, 11]⟩,
   ⟨GateOp.or, [14, 15]⟩,
   ⟨GateOp.or, [16, 17]⟩]

lemma witness_mono : ∀ g ∈ witnessGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [witnessGates]

lemma witness_len : witnessGates.length = 11 := rfl

lemma witness_eval : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witnessGates, 18⟩ (List.ofFn x) = targetFn x := by
  decide +kernel

def proj3 : Fin 8 → Fin 3 := ![0, 0, 0, 0, 0, 0, 1, 2]

lemma branch_false (b5 b4 : Bool) (s : ℕ)
    (hs : HasCircuitSize 8 (fun x =>
      targetFn (Function.update (Function.update (Function.update x 2 false) 5 b5) 4 b4)) s) :
    6 ≤ s := by
  let g := fun x : Fin 8 → Bool =>
    targetFn (Function.update (Function.update (Function.update x 2 false) 5 b5) 4 b4)
  have hd0 : ∃ x : Fin 8 → Bool, g (Function.update x 0 (!x 0)) ≠ g x := by
    cases b5 <;> cases b4 <;> decide +kernel
  have hnc0 : ∃ x y : Fin 8 → Bool,
      g (Function.update x 0 false) ≠ g (Function.update y 0 false) := by
    cases b5 <;> cases b4 <;> decide +kernel
  obtain ⟨s0, hs0, h0⟩ := elim_var g 0 false s hd0 hnc0 hs
  let g1 := fun z : Fin 8 → Bool => g (Function.update z 0 false)
  have hd1 : ∃ x : Fin 8 → Bool, g1 (Function.update x 1 (!x 1)) ≠ g1 x := by
    cases b5 <;> cases b4 <;> decide +kernel
  have hnc1 : ∃ x y : Fin 8 → Bool,
      g1 (Function.update x 1 false) ≠ g1 (Function.update y 1 false) := by
    cases b5 <;> cases b4 <;> decide +kernel
  obtain ⟨s1, hs1, h1⟩ := elim_var g1 1 false s0 hd1 hnc1 h0
  have h3 := relabel_size proj3 _ s1 h1
  have heq : (fun y : Fin 3 → Bool => g1 (Function.update (y ∘ proj3) 1 false)) = maj3 := by
    funext y
    cases b5 <;> cases b4
    · exact (by decide +kernel : ∀ z : Fin 3 → Bool,
        targetFn (Function.update (Function.update (Function.update (Function.update (Function.update (z ∘ proj3) 1 false) 0 false) 2 false) 5 false) 4 false) = maj3 z) y
    · exact (by decide +kernel : ∀ z : Fin 3 → Bool,
        targetFn (Function.update (Function.update (Function.update (Function.update (Function.update (z ∘ proj3) 1 false) 0 false) 2 false) 5 false) 4 true) = maj3 z) y
    · exact (by decide +kernel : ∀ z : Fin 3 → Bool,
        targetFn (Function.update (Function.update (Function.update (Function.update (Function.update (z ∘ proj3) 1 false) 0 false) 2 false) 5 true) 4 false) = maj3 z) y
    · exact (by decide +kernel : ∀ z : Fin 3 → Bool,
        targetFn (Function.update (Function.update (Function.update (Function.update (Function.update (z ∘ proj3) 1 false) 0 false) 2 false) 5 true) 4 true) = maj3 z) y
  rw [heq] at h3
  have hs1ge : 4 ≤ s1 := by
    by_contra hlt
    have hs1le : s1 ≤ 3 := by omega
    obtain ⟨C, hC, hCsz, hCev⟩ := h3
    exact no_size_3_maj3 ⟨C, hC, hCsz.trans hs1le, hCev⟩
  omega

lemma branch_true (b4 : Bool) (s : ℕ)
    (hs : HasCircuitSize 8 (fun x =>
      targetFn (Function.update (Function.update x 2 true) 4 b4)) s) :
    7 ≤ s := by
  let g := fun x : Fin 8 → Bool => targetFn (Function.update (Function.update x 2 true) 4 b4)
  have hd0 : ∃ x : Fin 8 → Bool, g (Function.update x 0 (!x 0)) ≠ g x := by
    cases b4 <;> decide +kernel
  have hnc0 : ∃ x y : Fin 8 → Bool,
      g (Function.update x 0 false) ≠ g (Function.update y 0 false) := by
    cases b4 <;> decide +kernel
  obtain ⟨s0, hs0, h0⟩ := elim_var g 0 false s hd0 hnc0 hs
  let g1 := fun z : Fin 8 → Bool => g (Function.update z 0 false)
  have hd1 : ∃ x : Fin 8 → Bool, g1 (Function.update x 1 (!x 1)) ≠ g1 x := by
    cases b4 <;> decide +kernel
  have hnc1 : ∃ x y : Fin 8 → Bool,
      g1 (Function.update x 1 false) ≠ g1 (Function.update y 1 false) := by
    cases b4 <;> decide +kernel
  obtain ⟨s1, hs1, h1⟩ := elim_var g1 1 false s0 hd1 hnc1 h0
  let g2 := fun z : Fin 8 → Bool => g1 (Function.update z 1 false)
  have hd5 : ∃ x : Fin 8 → Bool, g2 (Function.update x 5 (!x 5)) ≠ g2 x := by
    cases b4 <;> decide +kernel
  have hnc5 : ∃ x y : Fin 8 → Bool,
      g2 (Function.update x 5 false) ≠ g2 (Function.update y 5 false) := by
    cases b4 <;> decide +kernel
  obtain ⟨s5, hs5, h5⟩ := elim_var g2 5 false s1 hd5 hnc5 h1
  have h3 := relabel_size proj3 _ s5 h5
  have heq : (fun y : Fin 3 → Bool => g2 (Function.update (y ∘ proj3) 5 false)) = maj3 := by
    funext y
    cases b4
    · exact (by decide +kernel : ∀ z : Fin 3 → Bool,
        targetFn (Function.update (Function.update (Function.update (Function.update (Function.update (z ∘ proj3) 5 false) 1 false) 0 false) 2 true) 4 false) = maj3 z) y
    · exact (by decide +kernel : ∀ z : Fin 3 → Bool,
        targetFn (Function.update (Function.update (Function.update (Function.update (Function.update (z ∘ proj3) 5 false) 1 false) 0 false) 2 true) 4 true) = maj3 z) y
  rw [heq] at h3
  have hs5ge : 4 ≤ s5 := by
    by_contra hlt
    have hs5le : s5 ≤ 3 := by omega
    obtain ⟨C, hC, hCsz, hCev⟩ := h3
    exact no_size_3_maj3 ⟨C, hC, hCsz.trans hs5le, hCev⟩
  omega

lemma target_lower (s : ℕ) (hs : HasCircuitSize 8 targetFn s) : 11 ≤ s := by
  have hd2 : ∃ x : Fin 8 → Bool, targetFn (Function.update x 2 (!x 2)) ≠ targetFn x := by
    decide +kernel
  have hnc2 : ∀ b : Bool, ∃ x y : Fin 8 → Bool,
      targetFn (Function.update x 2 b) ≠ targetFn (Function.update y 2 b) := by
    intro b; cases b <;> decide +kernel
  obtain ⟨b2, s2, hs2, h2⟩ := gate_elim_two targetFn 2 s hd2 hnc2 hs
  cases b2
  · let f2 := fun x : Fin 8 → Bool => targetFn (Function.update x 2 false)
    have hd5 : ∃ x : Fin 8 → Bool, f2 (Function.update x 5 (!x 5)) ≠ f2 x := by decide +kernel
    have hnc5 : ∀ b : Bool, ∃ x y : Fin 8 → Bool,
        f2 (Function.update x 5 b) ≠ f2 (Function.update y 5 b) := by
      intro b; cases b <;> decide +kernel
    obtain ⟨b5, s5, hs5, h5⟩ := gate_elim_two f2 5 s2 hd5 hnc5 h2
    let f25 := fun x : Fin 8 → Bool => f2 (Function.update x 5 b5)
    have hd4 : ∃ x : Fin 8 → Bool, f25 (Function.update x 4 (!x 4)) ≠ f25 x := by
      cases b5 <;> decide +kernel
    have hnc4 : ∀ b : Bool, ∃ x y : Fin 8 → Bool,
        f25 (Function.update x 4 b) ≠ f25 (Function.update y 4 b) := by
      intro b; cases b5 <;> cases b <;> decide +kernel
    obtain ⟨b4, s4, hs4, h4⟩ := gate_elim_two f25 4 s5 hd4 hnc4 h5
    have h4le := branch_false b5 b4 s4 h4
    omega
  · let f2 := fun x : Fin 8 → Bool => targetFn (Function.update x 2 true)
    have hd4 : ∃ x : Fin 8 → Bool, f2 (Function.update x 4 (!x 4)) ≠ f2 x := by decide +kernel
    have hnc4 : ∀ b : Bool, ∃ x y : Fin 8 → Bool,
        f2 (Function.update x 4 b) ≠ f2 (Function.update y 4 b) := by
      intro b; cases b <;> decide +kernel
    obtain ⟨b4, s4, hs4, h4⟩ := gate_elim_two f2 4 s2 hd4 hnc4 h2
    have h4le := branch_true b4 s4 h4
    omega

end PEqualNP.Outside.L_meta_14256

open PEqualNP.Outside.L_meta_14256 in
theorem PEqualNP.Outside.L_meta_14256 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hbasis _ hev
  have hfan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩ := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hbasis g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h <;> simp [h]
  have hhas : PEqualNP.MetaComplexity.HasCircuitSize 8 targetFn gates.length :=
    ⟨⟨gates, o⟩, hfan, le_rfl, hev⟩
  have hge := target_lower gates.length hhas
  exact ⟨witnessGates, 18, witness_mono, by rw [witness_len]; exact hge, witness_eval⟩
