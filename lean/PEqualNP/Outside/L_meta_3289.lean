import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3289_aux

namespace WireMap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def idx {m n} (σ : Fin m → Option (Fin n)) (size i : ℕ) : ℕ :=
  if h : i < m then (σ ⟨i,h⟩).elim (n+size) Fin.val else n+(i-m)
def mapG {m n} (σ : Fin m → Option (Fin n)) (size : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (idx σ size)⟩
def mapped {m n} (σ : Fin m → Option (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mapG σ C.size),idx σ C.size C.output⟩
def pull {m n} (σ : Fin m → Option (Fin n)) (x : Fin n → Bool) : Fin m → Bool :=
  fun k => (σ k).elim false x
def tr (gs : List Gate) (w : List Bool) := gs.foldl (fun z g => z++[g.op.eval (g.inputs.map fun i => z.getD i false)]) w

theorem getraw {n} (x : Fin n → Bool) (k : Fin n) : (List.ofFn x).getD k.val false=x k := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,k.isLt,dif_pos,Option.getD_some]

theorem getMapped {m n} (σ : Fin m → Option (Fin n)) (x : Fin n → Bool) (size : ℕ)
    (extra : List Bool) (cap : extra.length ≤ size) (i : ℕ) :
    (List.ofFn x++extra).getD (idx σ size i) false = (List.ofFn (pull σ x)++extra).getD i false := by
  by_cases h : i < m
  · rw [List.getD_append (List.ofFn (pull σ x)) _ _ _ (by simpa using h)]
    have r := getraw (pull σ x) ⟨i,h⟩
    rw [r];simp only [idx,dif_pos h,pull]
    cases q : σ ⟨i,h⟩ with
    | none => exact List.getD_eq_default _ _ (by simp;omega)
    | some k =>
      change (List.ofFn x++extra).getD k.val false=x k
      rw [List.getD_append _ _ _ _ (by simpa using k.isLt),getraw]
  · rw [show idx σ size i=n+(i-m) by simp [idx,h],List.getD_append_right _ _ _ _ (by simp),
        List.getD_append_right _ _ _ _ (by simp;omega)]
    simp

theorem traceMapped {m n} (σ : Fin m → Option (Fin n)) (x : Fin n → Bool) (size : ℕ)
    (gs : List Gate) (extra : List Bool) (cap : extra.length+gs.length ≤ size) :
    ∃ out, out.length=extra.length+gs.length ∧
      tr (gs.map (mapG σ size)) (List.ofFn x++extra) = List.ofFn x++out ∧
      tr gs (List.ofFn (pull σ x)++extra) = List.ofFn (pull σ x)++out := by
  induction gs generalizing extra with
  | nil => exact ⟨extra,by simp,rfl,rfl⟩
  | cons g gs ih =>
    let a := g.op.eval (g.inputs.map fun i => (List.ofFn (pull σ x)++extra).getD i false)
    have f : (mapG σ size g).op.eval ((mapG σ size g).inputs.map fun i => (List.ofFn x++extra).getD i false)=a := by
      simp only [a,mapG,List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => getMapped σ x size extra (by omega) i)
    obtain ⟨o,l,left,right⟩ := ih (extra++[a]) (by simp at cap ⊢;omega)
    refine ⟨o,by simp at l ⊢;omega,?_,?_⟩
    · change tr _ ((List.ofFn x++extra)++[_])=_
      rw [f,List.append_assoc];exact left
    · change tr _ ((List.ofFn (pull σ x)++extra)++[a])=_
      rw [List.append_assoc];exact right

theorem mapped_eval {m n} (σ : Fin m → Option (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    (mapped σ C).eval (List.ofFn x) = C.eval (List.ofFn (pull σ x)) := by
  obtain ⟨o,len,l,r⟩ := traceMapped σ x C.size C.gates [] (by simp [Circuit.size])
  simp only [List.append_nil,List.length_nil,Nat.zero_add] at len l r
  change (tr (C.gates.map (mapG σ C.size)) (List.ofFn x)).getD _ false = (tr C.gates _).getD _ false
  rw [l,r];exact getMapped σ x C.size o (by change o.length ≤ C.gates.length;omega) C.output
theorem mapped_size {m n} (σ : Fin m → Option (Fin n)) (C : Circuit) : (mapped σ C).size=C.size := by simp [mapped,Circuit.size]
theorem mapped_fan {m n} (σ : Fin m → Option (Fin n)) (C : Circuit) (h : FanInTwo C) : FanInTwo (mapped σ C) := by
  intro g hg
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (show g∈C.gates.map (mapG σ C.size) from hg)
  simpa [mapG] using h t ht

end WireMap

namespace PaidPin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The constant-propagation pass adapts the proof of L-meta-468 by k-sandhu in pull request 355.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := elimPass_len_lt m k gs (elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


end PaidPin

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def paid (g : Gate) : Bool := GateOp.rec true true false (fun _ => true) true g.op

theorem paid_norm (gs : List Gate) : (gs.map normGate).countP paid = gs.countP paid := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,l⟩ := g
    cases op <;> simp [List.countP_cons,paid,normGate,ih]

theorem paid_emit (m : ℕ) (g : Gate) (ins : List (Bool ⊕ ℕ)) :
    (simplifyGate g.op m ins).1.toList.countP paid ≤ (paid g).toNat := by
  obtain ⟨op,l⟩ := g
  cases op <;> simp only [paid,GateOp.rec] <;>
    rcases ins with _|⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp [simplifyGate,simpNot,simpOr,simpAnd,paid]

theorem paid_step (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (elimStep m acc g).2.countP paid ≤ acc.2.countP paid + (paid g).toNat := by
  simp only [elimStep,List.countP_append]
  exact Nat.add_le_add_left (paid_emit _ _ _) _

theorem paid_pass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.countP paid ≤ acc.2.countP paid + gs.countP paid := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons]
    have s := paid_step m acc g
    have h := ih (elimStep m acc g)
    cases b : paid g <;> simp [List.countP_cons,b] at s ⊢ <;> omega

def Compatible (a b : List Bool) (v : List (Bool ⊕ ℕ)) : Prop :=
  ∀ i, a.getD i false ≠ b.getD i false → ∃ c, v.getD i (.inl false)=.inl c

theorem step_compat (m : ℕ) (g : Gate) (a b : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (ok : NOkGate g)
    (la : a.length=acc.1.length) (lb : b.length=acc.1.length)
    (h : Compatible a b acc.1)
    (full : (elimStep m acc g).2.countP paid = acc.2.countP paid + (paid g).toNat) :
    Compatible (a++[g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b++[g.op.eval (g.inputs.map fun i => b.getD i false)]) (elimStep m acc g).1 := by
  intro i ne
  simp only [elimStep]
  by_cases e : i=acc.1.length
  · rw [getD_snoc_eq _ _ _ _ e]
    rw [getD_snoc_eq _ _ _ _ (e.trans la.symm),getD_snoc_eq _ _ _ _ (e.trans lb.symm)] at ne
    have why : ∃ k∈g.inputs, a.getD k false ≠ b.getD k false := by
      by_contra! no
      exact ne (congrArg _ (List.map_congr_left no))
    obtain ⟨k,hk,diff⟩ := why
    obtain ⟨c,eq⟩ := h k diff
    have hc : ∃ c, Sum.inl c ∈ (g.inputs.map fun i => acc.1.getD i (.inl false)) :=
      ⟨c,List.mem_map.mpr ⟨k,hk,eq⟩⟩
    by_cases n : g.op=.not
    · obtain ⟨op,l⟩ := g
      change op=.not at n
      subst op
      have len := ok.2 rfl
      change l.length≤1 at len
      rcases l with _|⟨u,_|⟨t,more⟩⟩
      · simp at hk
      · have ku : k=u := List.mem_singleton.mp hk
        subst u
        exact ⟨!c,by change (simpNot _ [acc.1.getD k (.inl false)]).2=_;rw [eq];rfl⟩
      · simp at len
    · have kill := simplifyGate_none_of_const g.op (m+acc.2.length) _ ok.1.1
          (by simpa using ok.1.2) (fun n => by simpa using ok.2 n) hc
      have pg : paid g = true := by
        obtain ⟨op,l⟩ := g;cases op <;> simp_all [paid]
      simp only [elimStep,kill,Option.toList_none,List.append_nil,pg,Bool.toNat_true] at full
      omega
  · rw [getD_snoc_ne _ _ _ _ e]
    rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)] at ne
    exact h _ ne

theorem pass_compat (m : ℕ) (gs : List Gate) (a b : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (ok : ∀ g∈gs, NOkGate g)
    (la : a.length=acc.1.length) (lb : b.length=acc.1.length) (h : Compatible a b acc.1)
    (full : (elimPass m gs acc).2.countP paid = acc.2.countP paid + gs.countP paid) :
    Compatible (wiresFrom gs a) (wiresFrom gs b) (elimPass m gs acc).1 := by
  induction gs generalizing a b acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons] at full ⊢
    rw [wiresFrom_cons,wiresFrom_cons]
    have hs := paid_step m acc g
    have hp := paid_pass m gs (elimStep m acc g)
    have cnt : (g::gs).countP paid=(paid g).toNat+gs.countP paid := by
      cases b : paid g <;> simp [List.countP_cons,b,Nat.add_comm]
    rw [cnt] at full
    apply ih _ _ _ (fun g hg => ok _ (List.mem_cons_of_mem _ hg))
        (by simp [elimStep,la]) (by simp [elimStep,lb])
        (step_compat _ _ _ _ _ (ok _ List.mem_cons_self) la lb h (by omega)) (by omega)

theorem raw_compat {m} (x : Fin m → Bool) (v : Fin m) (pin : Bool) :
    Compatible (List.ofFn (Function.update x v false)) (List.ofFn (Function.update x v true))
      (initVar m v pin) := by
  intro i ne
  by_cases hi : i < m
  · rw [ofFn_getD_lt _ _ _ hi,ofFn_getD_lt _ _ _ hi] at ne
    by_cases eq : (⟨i,hi⟩ : Fin m)=v
    · exact ⟨pin,by rw [initVar,ofFn_getD_lt _ _ _ hi];simp [eq]⟩
    · simp [Function.update_of_ne eq] at ne
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)] at ne
    exact (ne rfl).elim

theorem pinPaid {m : ℕ} (C : Circuit) (ok : FanInTwo C) (v : Fin m) (pin : Bool)
    (dep : ∃ x : Fin m → Bool, circuitFun m C (Function.update x v false) ≠
      circuitFun m C (Function.update x v true))
    (varies : ∃ x y : Fin m → Bool, circuitFun m C (Function.update x v pin) ≠
      circuitFun m C (Function.update y v pin)) :
    ∃ D : Circuit, FanInTwo D ∧ D.gates.countP paid < C.gates.countP paid ∧
      ∀ x : Fin m → Bool, circuitFun m D x = circuitFun m C (Function.update x v pin) := by
  let gs := C.gates.map normGate
  let ini : List (Bool ⊕ ℕ) × List Gate := (initVar m v pin,[])
  let fin := elimPass m gs ini
  have hnok : ∀ g∈gs, NOkGate g := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok a (ok a ha)
  have val (x : Fin m → Bool) :
      statVal (wiresFrom fin.2 (List.ofFn x)) (fin.1.getD C.output (.inl false)) =
        circuitFun m C (Function.update x v pin) := by
    have h := elimInv_pass m (List.ofFn x) gs _ ini (fun g hg => (hnok g hg).1) (elimInv_initVar m v pin x)
    exact ((h.2.2 C.output).2).trans (by rw [show gs=C.gates.map normGate from rfl,wiresFrom_norm];rfl)
  cases out : fin.1.getD C.output (.inl false) with
  | inl c =>
    obtain ⟨x,y,ne⟩ := varies
    have hx := val x
    have hy := val y
    rw [out] at hx hy
    exact (ne (hx.symm.trans hy)).elim
  | inr i =>
    refine ⟨⟨fin.2,i⟩,elimPass_ok m gs ini (by simp [ini]),?_,?_⟩
    · change fin.2.countP paid < C.gates.countP paid
      have ct : gs.countP paid=C.gates.countP paid := paid_norm C.gates
      have ub : fin.2.countP paid≤C.gates.countP paid := by simpa only [fin,ini,List.countP_nil,Nat.zero_add,ct] using paid_pass m gs ini
      by_contra! le
      have exactCount : fin.2.countP paid=ini.2.countP paid+gs.countP paid := by
        simp only [ini,List.countP_nil,Nat.zero_add,ct];omega
      obtain ⟨x,ne⟩ := dep
      have stable := pass_compat m gs _ _ ini hnok (by simp [ini,initVar])
        (by simp [ini,initVar]) (raw_compat x v pin) exactCount
      obtain ⟨c,h⟩ := stable C.output (by simp only [gs,wiresFrom_norm];exact ne)
      change fin.1.getD C.output (.inl false)=.inl c at h
      rw [out] at h
      contradiction
    · intro x
      have h := val x
      rw [out] at h
      exact h
end PaidPin

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Acc := List (Bool ⊕ ℕ) × List Gate
def IsConst (s : Bool ⊕ ℕ) := ∃ c, s=.inl c
def Twin (A B : Acc) (x y : List Bool) := ∀ i, x.getD i false ≠ y.getD i false →
  IsConst (A.1.getD i (.inl false)) ∨ IsConst (B.1.getD i (.inl false))

theorem constantImage (m : ℕ) (g : Gate) (A : Acc) (ok : NOkGate g)
    (full : (elimStep m A g).2.countP paid=A.2.countP paid+(paid g).toNat)
    (k : ℕ) (hk : k∈g.inputs) (hc : IsConst (A.1.getD k (.inl false))) :
    IsConst ((simplifyGate g.op (m+A.2.length) (g.inputs.map fun i => A.1.getD i (.inl false))).2) := by
  obtain ⟨c,eq⟩ := hc
  by_cases n : g.op=.not
  · obtain ⟨op,l⟩ := g
    change op=.not at n
    subst op
    have len := ok.2 rfl
    change l.length≤1 at len
    rcases l with _|⟨u,_|⟨v,more⟩⟩
    · simp at hk
    · have h : k=u := List.mem_singleton.mp hk
      subst u
      exact ⟨!c,by change (simpNot _ [A.1.getD k (.inl false)]).2=_;rw [eq];rfl⟩
    · simp at len
  · have kill := simplifyGate_none_of_const g.op (m+A.2.length) (g.inputs.map fun k => A.1.getD k (.inl false)) ok.1.1
        (by simpa using ok.1.2) (fun h => by simpa using ok.2 h)
        ⟨c,List.mem_map.mpr ⟨k,hk,eq⟩⟩
    have pg : paid g = true := by
      obtain ⟨op,l⟩ := g;cases op <;> simp_all [paid]
    simp only [elimStep,kill,Option.toList_none,List.append_nil,pg,Bool.toNat_true] at full
    omega

theorem twin_step (m : ℕ) (g : Gate) (A B : Acc) (x y : List Bool)
    (ok : NOkGate g) (lx : x.length=A.1.length) (ly : y.length=A.1.length) (lb : B.1.length=A.1.length)
    (fullA : (elimStep m A g).2.countP paid=A.2.countP paid+(paid g).toNat)
    (fullB : (elimStep m B g).2.countP paid=B.2.countP paid+(paid g).toNat)
    (init : Twin A B x y) :
    Twin (elimStep m A g) (elimStep m B g)
      (x++[g.op.eval (g.inputs.map fun i => x.getD i false)])
      (y++[g.op.eval (g.inputs.map fun i => y.getD i false)]) := by
  intro i ne
  simp only [elimStep]
  by_cases h : i=A.1.length
  · rw [getD_snoc_eq _ _ _ _ h,getD_snoc_eq _ _ _ _ (by omega)]
    rw [getD_snoc_eq _ _ _ _ (by omega),getD_snoc_eq _ _ _ _ (by omega)] at ne
    have why : ∃ k∈g.inputs, x.getD k false ≠ y.getD k false := by
      by_contra! same
      exact ne (congrArg _ (List.map_congr_left same))
    obtain ⟨k,uses,dif⟩ := why
    rcases init k dif with p|p
    · exact Or.inl (constantImage _ _ _ ok fullA k uses p)
    · exact Or.inr (constantImage _ _ _ ok fullB k uses p)
  · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)]
    rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)] at ne
    exact init i ne

theorem twin_pass (m : ℕ) (gs : List Gate) (A B : Acc) (x y : List Bool)
    (ok : ∀ g∈gs, NOkGate g) (lx : x.length=A.1.length) (ly : y.length=A.1.length) (lb : B.1.length=A.1.length)
    (fullA : (elimPass m gs A).2.countP paid=A.2.countP paid+gs.countP paid)
    (fullB : (elimPass m gs B).2.countP paid=B.2.countP paid+gs.countP paid)
    (init : Twin A B x y) :
    Twin (elimPass m gs A) (elimPass m gs B) (wiresFrom gs x) (wiresFrom gs y) := by
  induction gs generalizing A B x y with
  | nil => exact init
  | cons g gs ih =>
    rw [elimPass_cons] at fullA fullB
    rw [elimPass_cons,elimPass_cons,wiresFrom_cons,wiresFrom_cons]
    have ha := paid_step m A g
    have hb := paid_step m B g
    have hr := paid_pass m gs (elimStep m A g)
    have hs := paid_pass m gs (elimStep m B g)
    have cnt : (g::gs).countP paid=(paid g).toNat+gs.countP paid := by
      cases h : paid g <;> simp [List.countP_cons,h,Nat.add_comm]
    rw [cnt] at fullA fullB
    apply ih _ _ _ _ (fun g hg => ok _ (List.mem_cons_of_mem _ hg))
      (by simp [elimStep,lx]) (by simp [elimStep,ly]) (by simp [elimStep,lb])
      (by omega) (by omega) (twin_step m g A B x y (ok _ List.mem_cons_self) lx ly lb (by omega) (by omega) init)
end PaidPin

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Lit (n : ℕ) := Option (Fin n) × Bool
def lc {n : ℕ} : Lit n := (none,false)
def lv {n : ℕ} (L : Lit n) (x : Fin n → Bool) : Bool := (L.1.elim false x).xor L.2
def flip {n : ℕ} (L : Lit n) : Lit n := (L.1,!L.2)
def cond {n : ℕ} (L : Lit n) (i : Fin n) := L.1 = none ∨ L.1 = some i
theorem lv_flip {n} (L : Lit n) (x : Fin n → Bool) : lv (flip L) x = !lv L x := by
  simp [lv,flip]

def CR {n} (R : List (Lit n)) (W : (Fin n → Bool) → List Bool) (A : Fin n → Acc) : Prop :=
  (∀ x, (W x).length=R.length) ∧ (∀ i, (A i).1.length=R.length) ∧
  (∀ k x, (W x).getD k false=lv (R.getD k lc) x) ∧
  ∀ i k, cond (R.getD k lc) i → IsConst ((A i).1.getD k (.inl false))

theorem CR_init (n : ℕ) : CR (List.ofFn fun i : Fin n => (some i,false))
    (fun x => List.ofFn x) (fun i => (initVar n i false,[])) := by
  refine ⟨by simp,by simp [initVar],?_,?_⟩
  · intro k x
    by_cases h : k < n
    · rw [ofFn_getD_lt _ _ _ h,ofFn_getD_lt _ _ _ h];simp [lv]
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)];rfl
  · intro i k hy
    by_cases h : k < n
    · rw [ofFn_getD_lt _ _ _ h] at hy
      simp [cond] at hy
      refine ⟨false,?_⟩
      change (initVar n i false).getD k _=_
      rw [initVar,ofFn_getD_lt _ _ _ h]
      simp [hy]
    · refine ⟨false,?_⟩
      exact List.getD_eq_default _ _ (by simp [initVar];omega)

def per {n} (R : List (Lit n)) : List ℕ → Lit n
  | [] => (none,true)
  | k::_ => flip (R.getD k lc)

theorem CR_not {n} (R : List (Lit n)) (W : (Fin n → Bool) → List Bool) (A : Fin n → Acc)
    (h : CR R W A) (l : List ℕ) :
    CR (R++[per R l]) (fun x => W x++[GateOp.not.eval (l.map fun k => (W x).getD k false)])
      (fun i => elimStep n (A i) ⟨.not,l⟩) := by
  obtain ⟨wl,al,we,ac⟩ := h
  refine ⟨by simp [wl],by simp [elimStep,al],?_,?_⟩
  · intro k x
    by_cases e : k=R.length
    · rw [getD_snoc_eq _ _ _ _ (e.trans (wl x).symm),getD_snoc_eq _ _ _ _ e]
      cases l with
      | nil => rfl
      | cons a l => simp only [List.map_cons,GateOp.eval,List.headD_cons,per,lv_flip,we]
    · rw [getD_snoc_ne _ _ _ _ (by rw [wl];exact e),getD_snoc_ne _ _ _ _ e]
      exact we _ _
  · intro i k hc
    simp only [elimStep]
    by_cases e : k=R.length
    · rw [getD_snoc_eq _ _ _ _ e] at hc
      rw [getD_snoc_eq _ _ _ _ (e.trans (al i).symm)]
      cases l with
      | nil => exact ⟨true,rfl⟩
      | cons a l =>
        obtain ⟨v,hv⟩ := ac i a hc
        refine ⟨!v,?_⟩
        change (simpNot _ ((A i).1.getD a (.inl false)::_)).2=_
        rw [hv];rfl
    · rw [getD_snoc_ne _ _ _ _ e] at hc
      rw [getD_snoc_ne _ _ _ _ (by rw [al];exact e)]
      exact ac _ _ hc

theorem CR_prefix {n} (gs : List Gate) (R : List (Lit n)) (W : (Fin n → Bool) → List Bool)
    (A : Fin n → Acc) (h : CR R W A) (ns : ∀ g∈gs,g.op=.not) :
    ∃ R', CR R' (fun x => wiresFrom gs (W x)) (fun i => elimPass n gs (A i)) := by
  induction gs generalizing R W A with
  | nil => exact ⟨R,h⟩
  | cons g gs ih =>
    obtain ⟨op,l⟩ := g
    have e := ns ⟨op,l⟩ List.mem_cons_self
    change op=.not at e
    subst op
    exact ih _ _ _ (CR_not R W A h l) (fun k hk => ns _ (List.mem_cons_of_mem _ hk))

theorem dif_const {n} (L : Lit n) (x y : Fin n → Bool) (i j : Fin n)
    (rest : ∀ k, k≠i → k≠j → x k=y k) (h : lv L x ≠ lv L y) : cond L i ∨ cond L j := by
  obtain ⟨idx,s⟩ := L
  cases idx with
  | none => exact Or.inl (Or.inl rfl)
  | some k =>
    by_cases hi : k=i
    · exact Or.inl (Or.inr (congrArg some hi))
    by_cases hj : k=j
    · exact Or.inr (Or.inr (congrArg some hj))
    exact (h (congrArg (fun z => Bool.xor z s) (rest k hi hj))).elim

theorem twin_prefix {n} (R : List (Lit n)) (W : (Fin n → Bool) → List Bool) (A : Fin n → Acc)
    (h : CR R W A) (x y : Fin n → Bool) (i j : Fin n) (rest : ∀ k, k≠i → k≠j → x k=y k) :
    Twin (A i) (A j) (W x) (W y) := by
  intro k ne
  rw [h.2.2.1,h.2.2.1] at ne
  exact (dif_const _ x y i j rest ne).imp (h.2.2.2 i k) (h.2.2.2 j k)
end PaidPin

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem all_fold (m : ℕ) (op : GateOp) (allow : op=.and ∨ op=.or)
    (ins : List (Bool ⊕ ℕ)) (ln : ins.length≤2) (h : ∀ k∈ins,IsConst k) :
    (simplifyGate op m ins).1=none ∧ IsConst (simplifyGate op m ins).2 := by
  rcases ins with _|⟨a,_|⟨b,_|⟨c,more⟩⟩⟩
  · rcases allow with rfl|rfl <;> exact ⟨rfl,_,rfl⟩
  · obtain ⟨a,rfl⟩ := h a List.mem_cons_self
    rcases allow with rfl|rfl <;> exact ⟨rfl,_,rfl⟩
  · obtain ⟨v,rfl⟩ := h a List.mem_cons_self
    obtain ⟨w,rfl⟩ := h b (by simp)
    rcases allow with rfl|rfl <;> exact ⟨rfl,_,rfl⟩
  · simp at ln

abbrev nextW (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun k => w.getD k false)]
abbrev simpResult (m : ℕ) (A : Acc) (g : Gate) :=
  simplifyGate g.op (m+A.2.length) (g.inputs.map fun k => A.1.getD k (.inl false))

theorem appendTwin {m} (g : Gate) (A B : Acc) (x y : List Bool)
    (lx : x.length=A.1.length) (ly : y.length=A.1.length) (lb : B.1.length=A.1.length)
    (h : Twin A B x y)
    (new : g.op.eval (g.inputs.map fun k => x.getD k false)=g.op.eval (g.inputs.map fun k => y.getD k false) ∨
      IsConst (simpResult m A g).2 ∨ IsConst (simpResult m B g).2) :
    Twin (elimStep m A g) (elimStep m B g) (nextW x g) (nextW y g) := by
  intro k ne
  simp only [elimStep]
  change (x++[_]).getD k false≠(y++[_]).getD k false at ne
  by_cases eq : k=A.1.length
  · rw [getD_snoc_eq _ _ _ _ eq,getD_snoc_eq _ _ _ _ (by omega)]
    rw [getD_snoc_eq _ _ _ _ (by omega),getD_snoc_eq _ _ _ _ (by omega)] at ne
    exact new.resolve_left ne
  · rw [getD_snoc_ne _ _ _ _ eq,getD_snoc_ne _ _ _ _ (by omega)]
    rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)] at ne
    exact h k ne

end PaidPin

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem firstPaid (gs : List Gate) (ok : ∀ g∈gs,NOkGate g) (pos : 0<gs.countP paid) :
    ∃ pre g post, gs=pre++g::post ∧ (∀ h∈pre,h.op=.not) ∧ paid g=true := by
  induction gs with
  | nil => simp at pos
  | cons g gs ih =>
    cases e : paid g with
    | true => exact ⟨[],g,gs,rfl,by simp,e⟩
    | false =>
      have z : g.op=.not := by
        obtain ⟨op,ins⟩ := g
        cases op <;> simp_all [paid]
      obtain ⟨pre,h,post,rfl,alln,hp⟩ := ih (fun _ hg => ok _ (List.mem_cons_of_mem _ hg)) (by simpa [e] using pos)
      exact ⟨g::pre,h,post,rfl,fun k hk => (List.mem_cons.mp hk).elim (fun k => k ▸ z) (alln k),hp⟩

end PaidPin

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem classAt {n : ℕ} (anchor : Fin n) (R : List (Lit n)) (l : List ℕ) (ln : l.length≤2) :
    (∃ i : Fin n, ∀ a∈l,cond (R.getD a lc) i) ∨
    ∃ a b : ℕ, l=[a,b] ∧ ∃ i j : Fin n, i≠j ∧ (R.getD a lc).1=some i ∧ (R.getD b lc).1=some j := by
  rcases l with _|⟨a,_|⟨b,_|⟨c,more⟩⟩⟩
  · exact Or.inl ⟨anchor,by simp⟩
  · left
    cases e : (R.getD a lc).1 with
    | none => exact ⟨anchor,by intro k h;rw [List.mem_singleton.mp h];exact Or.inl e⟩
    | some i => exact ⟨i,by intro k h;rw [List.mem_singleton.mp h];exact Or.inr e⟩
  · cases ea : (R.getD a lc).1 with
    | none =>
      cases eb : (R.getD b lc).1 with
      | none => exact Or.inl ⟨anchor,by intro k h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl;exact Or.inl ea;exact Or.inl eb⟩
      | some j => exact Or.inl ⟨j,by intro k h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl;exact Or.inl ea;exact Or.inr eb⟩
    | some i =>
      cases eb : (R.getD b lc).1 with
      | none => exact Or.inl ⟨i,by intro k h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl;exact Or.inr ea;exact Or.inl eb⟩
      | some j =>
        by_cases e : i=j
        · subst j
          exact Or.inl ⟨i,by intro k h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl;exact Or.inr ea;exact Or.inr eb⟩
        · exact Or.inr ⟨a,b,rfl,i,j,e,ea,eb⟩
  · simp at ln

theorem mixAt {n : ℕ} (anchor : Fin n) (f : (Fin n→Bool)→Bool)
    (essential : ∀ i : Fin n, ∃ x y : Fin n→Bool, (∀ k, k≠i → x k=y k) ∧ f x≠f y)
    (collisionAt : ∀ i j : Fin n, i≠j → ∀ c : Bool→Bool→Bool, ∃ x y : Fin n→Bool,
      (∀ k, k≠i → k≠j → x k=y k) ∧ c (x i) (x j)=c (y i) (y j) ∧ f x≠f y) (g : Gate) (ok : NOkGate g) (pg : paid g=true)
    (R : List (Lit n)) (W : (Fin n → Bool) → List Bool) (A : Fin n → Acc) (h : CR R W A) :
    ∃ i j : Fin n, (simpResult n (A i) g).1=none ∧
      (simpResult n (A j) g).1=none ∧ ∃ x y, f x≠f y ∧
        Twin (elimStep n (A i) g) (elimStep n (A j) g) (nextW (W x) g) (nextW (W y) g) := by
  have allow : g.op=.and ∨ g.op=.or := by
    have ho : g.op=.and ∨ g.op=.or ∨ g.op=.not := ok.1.1
    rcases ho with hoa|hor|hon
    · exact Or.inl hoa
    · exact Or.inr hor
    · simp [paid,hon] at pg
  rcases classAt anchor R g.inputs ok.1.2 with ⟨i,hi⟩|⟨a,b,hab,i,j,ne,ea,eb⟩
  · have folded := all_fold (n+(A i).2.length) g.op allow (g.inputs.map fun k => (A i).1.getD k (.inl false))
        (by simpa using ok.1.2) (by intro u hu;obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hu;exact h.2.2.2 _ _ (hi _ hk))
    obtain ⟨x,y,other,hk⟩ := essential i
    refine ⟨i,i,folded.1,folded.1,x,y,hk,?_⟩
    apply appendTwin _ _ _ _ _ ((h.1 _).trans (h.2.1 _).symm) ((h.1 _).trans (h.2.1 _).symm) rfl
        (twin_prefix _ _ _ h _ _ i i (fun k hk _ => other k hk)) (Or.inr (Or.inl folded.2))
  · let s := (R.getD a lc).2
    let t := (R.getD b lc).2
    obtain ⟨x,y,rest,eq,neq⟩ := collisionAt i j ne (fun u v => g.op.eval [u.xor s,v.xor t])
    have killed (k : Fin n) (v : ℕ) (em : v∈g.inputs) (e : (R.getD v lc).1=some k) :
        (simpResult n (A k) g).1=none := by
      obtain ⟨d,ed⟩ := h.2.2.2 k v (Or.inr e)
      apply simplifyGate_none_of_const _ _ _ ok.1.1 (by simpa using ok.1.2) (fun h => by simpa using ok.2 h)
      exact ⟨d,List.mem_map.mpr ⟨v,em,ed⟩⟩
    refine ⟨i,j,killed i a (by simp [hab]) ea,killed j b (by simp [hab]) eb,x,y,neq,?_⟩
    apply appendTwin _ _ _ _ _ ((h.1 _).trans (h.2.1 _).symm) ((h.1 _).trans (h.2.1 _).symm)
        ((h.2.1 _).trans (h.2.1 _).symm) (twin_prefix _ _ _ h x y i j rest) (Or.inl ?_)
    simp only [hab,List.map_cons,List.map_nil,h.2.2.1,lv,ea,eb]
    exact eq
theorem twoDropBound {n b : ℕ} (anchor : Fin n) (f : (Fin n→Bool)→Bool)
    (essential : ∀ i : Fin n, ∃ x y : Fin n→Bool, (∀ k, k≠i → x k=y k) ∧ f x≠f y)
    (collisionAt : ∀ i j : Fin n, i≠j → ∀ c : Bool→Bool→Bool, ∃ x y : Fin n→Bool,
      (∀ k, k≠i → k≠j → x k=y k) ∧ c (x i) (x j)=c (y i) (y j) ∧ f x≠f y)
    (pinnedVar : ∀ i : Fin n, ∃ x y : Fin n→Bool, f (Function.update x i false) ≠ f (Function.update y i false))
    (floor : ∀ (i : Fin n) (D : Circuit), FanInTwo D → (∀ x, circuitFun n D x=f (Function.update x i false)) → b≤D.gates.countP paid)
    (C : Circuit) (ok : FanInTwo C) (cv : circuitFun n C=f) : b+2≤C.gates.countP paid := by
  by_contra! below
  let gs := C.gates.map normGate
  have nok : ∀ g∈gs,NOkGate g := by
    intro g hg;obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hg;exact normGate_nok _ (ok _ ha)
  have ct : gs.countP paid=C.gates.countP paid := paid_norm _
  obtain ⟨x,y,neq⟩ := pinnedVar anchor
  obtain ⟨u,v,same,ne⟩ := essential anchor
  have dep : ∃ z : Fin n→Bool, circuitFun n C (Function.update z anchor false) ≠ circuitFun n C (Function.update z anchor true) := by
    use u
    have equal : Function.update u anchor (v anchor) = v := by
      funext k
      by_cases e : k=anchor
      · subst k; simp
      · simpa [Function.update_of_ne e] using same k e
    intro spare
    rw [cv] at spare
    have values (a d : Bool) : f (Function.update u anchor a) = f (Function.update u anchor d) := by
      cases a <;> cases d <;> first | rfl | exact spare | exact spare.symm
    have values' := values (u anchor) (v anchor)
    rw [Function.update_eq_self,equal] at values'
    exact ne values'
  obtain ⟨D,hd,short,ev⟩ := pinPaid C ok anchor false dep (by rw [cv];exact ⟨x,y,neq⟩)
  have sub := floor anchor D hd (fun z => by rw [ev,cv])
  have th : b+1≤C.gates.countP paid := by omega
  obtain ⟨pre,g,post,split,nots,pp⟩ := firstPaid gs nok (by omega)
  let I (i : Fin n) : Acc := (initVar n i false,[])
  let F (i : Fin n) := elimPass n gs (I i)
  have values (i : Fin n) (x : Fin n → Bool) :
      statVal (wiresFrom (F i).2 (List.ofFn x)) ((F i).1.getD C.output (.inl false)) =
        f (Function.update x i false) := by
    have h := elimInv_pass n (List.ofFn x) gs _ (I i) (fun g hg => (nok g hg).1) (elimInv_initVar n i false x)
    rw [(h.2.2 C.output).2]
    change (wiresFrom (C.gates.map normGate) _).getD C.output false=_
    rw [wiresFrom_norm]
    exact congrFun cv _
  have out (i : Fin n) : ∃ k, (F i).1.getD C.output (.inl false)=.inr k := by
    cases e : (F i).1.getD C.output (.inl false) with
    | inr k => exact ⟨k,rfl⟩
    | inl d =>
      obtain ⟨a,b,ne⟩ := pinnedVar i
      have h := values i a
      have h' := values i b
      rw [e] at h h'
      exact (ne (h.symm.trans h')).elim
  have minCost (i : Fin n) : b≤(F i).2.countP paid := by
    obtain ⟨k,hk⟩ := out i
    apply floor i ⟨(F i).2,k⟩ (elimPass_ok n gs (I i) (by simp [I]))
    intro x
    have v:=values i x;rw [hk] at v;exact v
  let A (i : Fin n) := elimPass n pre (I i)
  let W (x : Fin n → Bool) := wiresFrom pre (List.ofFn x)
  have gOk : NOkGate g := nok _ (by simp [split])
  have tailOk : ∀ v∈post,NOkGate v := by intro v hv;exact nok _ (by simp [split,hv])
  obtain ⟨R,cr⟩ := CR_prefix pre _ _ _ (CR_init n) nots
  obtain ⟨i,j,ei,ej,x,y,diff,hin⟩ := mixAt anchor f essential collisionAt g gOk pp R W A cr
  have pc : pre.countP paid=0 := by
    apply List.countP_eq_zero.mpr
    intro h mem
    simp [paid,nots h mem]
  have spent (i : Fin n) : (A i).2.countP paid=0 := by
    have h:=paid_pass n pre (I i)
    simp only [I,List.countP_nil,Nat.zero_add,pc] at h
    exact Nat.eq_zero_of_le_zero h
  have len : post.countP paid=b := by
    rw [split,List.countP_append,List.countP_cons,pp] at ct
    simp [pc] at ct
    omega
  have residue (i : Fin n) (drop : (simpResult n (A i) g).1=none) :
      (elimPass n post (elimStep n (A i) g)).2.countP paid =
        (elimStep n (A i) g).2.countP paid+post.countP paid := by
    have e : (elimStep n (A i) g).2.countP paid=0 := by
      change (((A i).2++(simpResult n (A i) g).1.toList).countP paid)=0
      rw [drop];simpa using spent i
    have lo:=minCost i
    have hi:=paid_pass n post (elimStep n (A i) g)
    change b≤(elimPass n gs (I i)).2.countP paid at lo
    rw [split,elimPass_append,elimPass_cons] at lo
    change b≤(elimPass n post (elimStep n (A i) g)).2.countP paid at lo
    omega
  have stable := twin_pass n post (elimStep n (A i) g) (elimStep n (A j) g) _ _ tailOk
    (show (nextW (W x) g).length=(elimStep n (A i) g).1.length by simp [nextW,elimStep];exact (cr.1 x).trans (cr.2.1 i).symm)
    (show (nextW (W y) g).length=(elimStep n (A i) g).1.length by simp [nextW,elimStep];exact (cr.1 y).trans (cr.2.1 i).symm)
    (by simp [elimStep];exact (cr.2.1 j).trans (cr.2.1 i).symm) (residue i ei) (residue j ej) hin
  have ev (z : Fin n → Bool) : (wiresFrom post (nextW (W z) g)).getD C.output false=f z := by
    have ev0 : (wiresFrom gs (List.ofFn z)).getD C.output false=f z := by
      rw [show gs=C.gates.map normGate from rfl,wiresFrom_norm]
      exact congrFun cv z
    rw [split,wiresFrom_append,wiresFrom_cons] at ev0
    exact ev0
  have impossible (i : Fin n) : ¬IsConst ((elimPass n post (elimStep n (A i) g)).1.getD C.output (.inl false)) := by
    obtain ⟨k,h⟩:=out i
    change (elimPass n gs (I i)).1.getD C.output (.inl false)=.inr k at h
    rw [split,elimPass_append,elimPass_cons] at h
    intro ⟨c,hc⟩
    have e : (Sum.inr k : Bool ⊕ ℕ)=.inl c := h.symm.trans hc
    cases e
  exact (stable C.output (by rw [ev,ev];exact diff)).elim (impossible _) (impossible _)

end PaidPin

namespace Plane2475
theorem exclusive {V : Type} (e : V→V→Prop)
    (symm : ∀ {a b}, e a b → e b a) (loop : ∀ a, ¬ e a a)
    (triangle : ∀ {a b c}, e a b → e a c → ¬e b c)
    (squares : ∀ {a b p q}, a≠b → e a p → e b p → e a q → e b q → p=q)
    (degree : ∀ a, ∃ r s, r≠s ∧ e a r ∧ e a s)
    {a b} (ne : a ≠ b) : ∃ p, p≠a ∧ p≠b ∧ e a p ∧ ¬e b p := by
  classical
  obtain ⟨r,s,rs,ar,as'⟩ := degree a
  have non {v} (av : e a v) : v ≠ a := by intro h; exact loop a (by simpa only [h] using av)
  by_cases ab : e a b
  · by_cases rb : r=b
    · subst r; exact ⟨s,non as',rs.symm,as',triangle ab as'⟩
    · exact ⟨r,non ar,rb,ar,triangle ab ar⟩
  have rb : r≠b := by rintro rfl; exact ab ar
  have sb : s≠b := by rintro rfl; exact ab as'
  by_cases br : e b r
  · have bs : ¬ e b s := fun bs => rs (squares ne ar br as' bs)
    exact ⟨s,non as',sb,as',bs⟩
  · exact ⟨r,non ar,rb,ar,br⟩

theorem no_single_reader_pair {V : Type} [DecidableEq V] (e : V→V→Prop) (F : (V→Bool)→Bool)
    (sing : ∀ p, F (fun v => decide (v=p)) = false)
    (pair : ∀ p i, p≠i → (F (fun v => decide (v=p ∨ v=i)) = true ↔ e i p))
    (dist : ∀ a b, a≠b → ∃ p, p≠a ∧ p≠b ∧ e a p ∧ ¬e b p)
    (i j : V) (ne : i≠j) (c : Bool→Bool→Bool) :
    ∃ x y : V→Bool, (∀ k, k≠i → k≠j → x k=y k) ∧
      c (x i) (x j)=c (y i) (y j) ∧ F x≠F y := by
  obtain ⟨p,pi,pj,piE,pjE⟩ := dist i j ne
  obtain ⟨q,qj,qi,qjE,qiE⟩ := dist j i ne.symm
  let s (p : V) := fun v => decide (v=p)
  let d (p a : V) := fun v => decide (v=p ∨ v=a)
  have ip : F (d p i)=true := (pair p i pi).2 piE
  have jq : F (d q j)=true := (pair q j qj).2 qjE
  have jp : F (d p j)=false := Bool.eq_false_iff.mpr (fun e => pjE ((pair p j pj).mp e))
  by_cases a : c false false = c true false
  · refine ⟨s p,d p i,?_,?_,?_⟩
    · intro k hi hj; simp [s,d,hi]
    · simpa [s,d,pi.symm,pj.symm,ne,ne.symm] using a
    · have h : F (s p)=false := sing p
      rw [h,ip];decide
  by_cases b : c false false = c false true
  · refine ⟨s q,d q j,?_,?_,?_⟩
    · intro k hi hj; simp [s,d,hj]
    · simpa [s,d,qi.symm,qj.symm,ne,ne.symm] using b
    · have h : F (s q)=false := sing q
      rw [h,jq];decide
  have eq : c true false = c false true := by
    cases ha : c false false <;> cases hb : c true false <;> cases hc : c false true <;> simp_all
  refine ⟨d p i,d p j,?_,?_,?_⟩
  · intro k hi hj; simp [d,hi,hj]
  · simpa [d,pi.symm,pj.symm,ne,ne.symm] using eq
  · rw [ip,jp];decide
end Plane2475

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem twoDropGraph {n : ℕ} (anchor : Fin n) (f : (Fin n→Bool)→Bool)
    (E : Fin n→Fin n→Prop) (symm : ∀ {i j}, E i j → E j i) (loop : ∀ i, ¬E i i)
    (triangle : ∀ {i j k}, E i j → E i k → ¬E j k)
    (squares : ∀ {i j u v}, i≠j → E i u → E j u → E i v → E j v → u=v)
    (degree : ∀ i, ∃ j k, j≠k ∧ E i j ∧ E i k)
    (sing : ∀ i, f (fun z => decide (z=i))=false)
    (pair : ∀ i j, i≠j → (f (fun z => decide (z=i ∨ z=j))=true ↔ E j i))
    (C : Circuit) (ok : FanInTwo C) (cv : circuitFun n C=f) :
    ∃ (i : Fin n) (D : Circuit), FanInTwo D ∧ D.gates.countP paid+2≤C.gates.countP paid ∧
      ∀ x, circuitFun n D x=f (Function.update x i false) := by
  classical
  have nearNe {i j : Fin n} (h : E i j) : i≠j := by rintro rfl;exact loop _ h
  have essential (i : Fin n) : ∃ x y : Fin n→Bool, (∀ k, k≠i → x k=y k) ∧ f x≠f y := by
    obtain ⟨j,k,_,hij,_⟩:=degree i
    refine ⟨fun z => decide (z=j),fun z => decide (z=j ∨ z=i),fun z ne => by simp [ne],?_⟩
    rw [sing,(pair j i (nearNe hij).symm).mpr hij]
    decide
  have varies (i : Fin n) : ∃ x y : Fin n→Bool, f (Function.update x i false)≠f (Function.update y i false) := by
    obtain ⟨a,b,ab,ia,ib⟩:=degree i
    have ai : a≠i := (nearNe ia).symm
    obtain ⟨u,v,uv,au,av⟩:=degree a
    obtain ⟨k,ki,ak⟩ : ∃ k, k≠i ∧ E a k := by
      by_cases ui : u=i
      · exact ⟨v,by simpa [ui] using uv.symm,av⟩
      · exact ⟨u,ui,au⟩
    let s : Fin n→Bool := fun z => decide (z=a)
    let d : Fin n→Bool := fun z => decide (z=a ∨ z=k)
    have su : Function.update s i false=s := by
      have h : s i=false := by simp [s,ai.symm]
      rw [←h,Function.update_eq_self]
    have du : Function.update d i false=d := by
      have h : d i=false := by simp [d,ai.symm,ki.symm]
      rw [←h,Function.update_eq_self]
    refine ⟨s,d,?_⟩
    rw [su,du,show f s=false from sing _,show f d=true from (pair a k (nearNe ak)).mpr (symm ak)]
    decide
  have distinct := fun i j (ij : i≠j) => Plane2475.exclusive E symm loop triangle squares degree ij
  have coll := Plane2475.no_single_reader_pair E f sing pair distinct
  have base := twoDropBound (b:=0) anchor f essential coll varies (by intros;omega) C ok cv
  by_contra no
  have floor (i : Fin n) (D : Circuit) (hd : FanInTwo D) (ev : ∀ x, circuitFun n D x=f (Function.update x i false)) :
      C.gates.countP paid-1≤D.gates.countP paid := by
    by_contra! lt
    exact no ⟨i,D,hd,by omega,ev⟩
  have limit := twoDropBound anchor f essential coll varies floor C ok cv
  omega
end PaidPin

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def atBit {n : ℕ} (f : (Fin n→Bool)→Bool) (i : Fin n) (a : Bool) : (Fin n→Bool)→Bool :=
  fun x => f (Function.update x i a)
def differs {n : ℕ} (f : (Fin n→Bool)→Bool) := ∃ x y, f x≠f y
def readsBit {n : ℕ} (f : (Fin n→Bool)→Bool) (i : Fin n) := ∃ x, atBit f i false x≠atBit f i true x
theorem bitsComm {n : ℕ} (f : (Fin n→Bool)→Bool) (i j : Fin n) (ij : i≠j) (a b : Bool) :
    atBit (atBit f i a) j b=atBit (atBit f j b) i a := by
  funext x
  exact congrArg f (Function.update_comm ij.symm _ _ _)
theorem diffFromPin {n : ℕ} {f : (Fin n→Bool)→Bool} {i : Fin n} {a : Bool}
    (h : differs (atBit f i a)) : differs f := by
  obtain ⟨x,y,ne⟩:=h
  exact ⟨Function.update x i a,Function.update y i a,ne⟩
theorem diffFromRead {n : ℕ} {f : (Fin n→Bool)→Bool} {i : Fin n} (h : readsBit f i) : differs f := by
  obtain ⟨x,ne⟩:=h
  exact ⟨Function.update x i false,Function.update x i true,ne⟩
theorem readFromPin {n : ℕ} {f : (Fin n→Bool)→Bool} {i j : Fin n} (ij : i≠j) {a : Bool}
    (h : readsBit (atBit f i a) j) : readsBit f j := by
  obtain ⟨x,ne⟩:=h
  refine ⟨Function.update x i a,?_⟩
  change atBit (atBit f j false) i a x ≠ atBit (atBit f j true) i a x
  rwa [bitsComm _ j i ij.symm,bitsComm _ j i ij.symm]
theorem pairPinBase {n : ℕ} {C : Circuit} {f : (Fin n→Bool)→Bool} (ok : FanInTwo C)
    (cv : circuitFun n C=f) {i j : Fin n} {a b : Bool} (ri : readsBit f i)
    (rj : readsBit (atBit f i a) j) (varies : differs (atBit (atBit f i a) j b)) :
    ∃ D : Circuit, FanInTwo D ∧ D.gates.countP paid+2≤C.gates.countP paid ∧
      circuitFun n D=atBit (atBit f i a) j b := by
  obtain ⟨D,okD,cost,vD⟩:=pinPaid C ok i a (by rw [cv];exact ri) (by rw [cv];exact diffFromPin varies)
  have fD : circuitFun n D=atBit f i a := funext fun z => (vD z).trans (congrFun cv _)
  obtain ⟨E,okE,cost',vE⟩:=pinPaid D okD j b (by rw [fD];exact rj) (by rw [fD];exact varies)
  exact ⟨E,okE,by omega,funext fun z => (vE z).trans (congrFun fD _)⟩
theorem pairZeroDrop {n : ℕ} {C : Circuit} {f : (Fin n→Bool)→Bool} (ok : FanInTwo C)
    (cv : circuitFun n C=f) {i j : Fin n} (ij : i≠j)
    (left : readsBit (atBit f j true) i) (right : readsBit (atBit f i true) j)
    (varies : differs (atBit (atBit f i false) j false)) :
    ∃ D : Circuit, FanInTwo D ∧ D.gates.countP paid+2≤C.gates.countP paid ∧
      circuitFun n D=atBit (atBit f i false) j false := by
  by_cases r : readsBit (atBit f j false) i
  · rw [bitsComm f i j ij] at varies ⊢
    exact pairPinBase ok cv (readFromPin ij right) r varies
  · have switch : atBit (atBit f j false) i false=atBit (atBit f j false) i true := by
      funext x
      by_contra ne
      exact r ⟨x,ne⟩
    have eq : atBit (atBit f i false) j false=atBit (atBit f i true) j false := by
      rw [bitsComm f i j ij,bitsComm f i j ij]
      exact switch
    rw [eq] at varies ⊢
    exact pairPinBase ok cv (readFromPin ij.symm left) right varies
end PaidPin

namespace PaidPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def singleRow {n : ℕ} (i : Fin n) : Fin n→Bool := fun k => decide (k=i)
def pairRow {n : ℕ} (i j : Fin n) : Fin n→Bool := fun k => decide (k=i ∨ k=j)
theorem switchOn {n : ℕ} {f : (Fin n→Bool)→Bool} {i j : Fin n} (ij : i≠j)
    (sing : f (singleRow i)=false) (pair : f (pairRow i j)=true) : readsBit (atBit f i true) j := by
  refine ⟨fun _ => false,?_⟩
  have s : Function.update (Function.update (fun _ : Fin n => false) j false) i true=singleRow i := by
    funext k; by_cases a : k=i <;> by_cases b : k=j <;> simp_all [singleRow,Function.update]
  have p : Function.update (Function.update (fun _ : Fin n => false) j true) i true=pairRow i j := by
    funext k; by_cases a : k=i <;> by_cases b : k=j <;> simp_all [pairRow,Function.update]
  change f _≠f _
  rw [s,p,sing,pair];decide
theorem switchBoth {n : ℕ} {f : (Fin n→Bool)→Bool} {i j : Fin n} (ij : i≠j)
    (s : ∀ v, f (singleRow v)=false) (p : f (pairRow i j)=true) :
    readsBit (atBit f i true) j ∧ readsBit (atBit f j true) i := by
  refine ⟨switchOn ij (s _) p,switchOn ij.symm (s _) ?_⟩
  have same : pairRow j i=pairRow i j := by
    funext k
    simp only [pairRow,or_comm]
  rwa [same]
theorem costPositive {n : ℕ} {f : (Fin n→Bool)→Bool} {C : Circuit} (ok : FanInTwo C)
    (cv : circuitFun n C=f) {i j : Fin n} (ij : i≠j)
    (s : ∀ v, f (singleRow v)=false) (p : f (pairRow i j)=true) : 1≤C.gates.countP paid := by
  obtain ⟨right,left⟩:=switchBoth ij s p
  obtain ⟨D,_,h,_⟩:=pinPaid C ok i true (by rw [cv];exact readFromPin ij.symm left) (by rw [cv];exact diffFromRead right)
  omega
theorem oneDrop {n : ℕ} {f : (Fin n→Bool)→Bool} {C : Circuit} (ok : FanInTwo C)
    (cv : circuitFun n C=f) {i j : Fin n} (ij : i≠j)
    (s : ∀ v, f (singleRow v)=false) (p : f (pairRow i j)=true) (varies : differs (atBit f i false)) :
    ∃ D : Circuit, FanInTwo D ∧ D.gates.countP paid+1≤C.gates.countP paid ∧ circuitFun n D=atBit f i false := by
  obtain ⟨_,left⟩:=switchBoth ij s p
  obtain ⟨D,okD,h,vD⟩:=pinPaid C ok i false (by rw [cv];exact readFromPin ij.symm left) (by rw [cv];exact varies)
  exact ⟨D,okD,by omega,funext fun z => (vD z).trans (congrFun cv _)⟩
end PaidPin

namespace Plane3289.Support
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open WireMap
open PaidPin
variable {n : ℕ}

def enum (S : Finset (Fin n)) : Fin S.card ≃ ↥S := (S.orderIsoOfFin rfl).toEquiv

def position (S : Finset (Fin n)) (i : Fin n) : Option (Fin S.card) :=
  if h : i∈S then some ((enum S).symm ⟨i,h⟩) else none

def circuit (S : Finset (Fin n)) (D : Circuit) := mapped (position S) D
def lift (S : Finset (Fin n)) (x : Fin S.card → Bool) : Fin n → Bool := pull (position S) x

theorem lift_inside (S : Finset (Fin n)) (x : Fin S.card → Bool) (i : Fin S.card) :
    lift S x (enum S i).val=x i := by
  simp [lift,pull,position,(enum S i).property]

theorem lift_outside (S : Finset (Fin n)) (x : Fin S.card → Bool) {k : Fin n} (h : k∉S) :
    lift S x k=false := by simp [lift,pull,position,h]

theorem eval (S : Finset (Fin n)) (D : Circuit) (x : Fin S.card → Bool) :
    circuitFun S.card (circuit S D) x = circuitFun n D (lift S x) := mapped_eval _ _ _

theorem fan (S : Finset (Fin n)) (D : Circuit) (ok : FanInTwo D) :
    FanInTwo (circuit S D) := mapped_fan _ _ ok

theorem paidCount (S : Finset (Fin n)) (D : Circuit) :
    (circuit S D).gates.countP paid=D.gates.countP paid := by
  unfold circuit mapped
  simp only [List.countP_map]
  rfl

theorem size (S : Finset (Fin n)) (D : Circuit) : (circuit S D).size=D.size := mapped_size _ _

theorem image_ne (S : Finset (Fin n)) {i j : Fin S.card} (h : i≠j) :
    (enum S i).val ≠ (enum S j).val := fun e => h ((enum S).injective (Subtype.ext e))

theorem liftPair (S : Finset (Fin n)) (i j : Fin S.card) :
    lift S (fun z=>decide (z=i ∨ z=j)) = fun z=>decide (z=(enum S i).val ∨ z=(enum S j).val) := by
  funext z
  by_cases h : z∈S
  · let k := (enum S).symm ⟨z,h⟩
    have zk : (enum S k).val=z := congrArg Subtype.val ((enum S).apply_symm_apply ⟨z,h⟩)
    rw [←zk,lift_inside]
    have same (a b : Fin S.card) : (enum S a).val=(enum S b).val ↔ a=b :=
      ⟨fun e => (enum S).injective (Subtype.ext e),fun e=>e ▸ rfl⟩
    simp only [same]
  · have outside (a : Fin S.card) : z≠(enum S a).val := fun e => h (e ▸ (enum S a).property)
    simp [lift_outside S _ h,outside]

theorem liftSingle (S : Finset (Fin n)) (i : Fin S.card) :
    lift S (fun z=>decide (z=i)) = fun z=>decide (z=(enum S i).val) := by
  simpa using liftPair S i i

theorem evalSingle (S : Finset (Fin n)) (D : Circuit) (i : Fin S.card) :
    circuitFun S.card (circuit S D) (fun z=>decide (z=i)) =
      circuitFun n D (fun z=>decide (z=(enum S i).val)) := by rw [eval,liftSingle]

theorem evalPair (S : Finset (Fin n)) (D : Circuit) (i j : Fin S.card) :
    circuitFun S.card (circuit S D) (fun z=>decide (z=i ∨ z=j)) =
      circuitFun n D (fun z=>decide (z=(enum S i).val ∨ z=(enum S j).val)) := by rw [eval,liftPair]


def expand (S : Finset (Fin n)) (D : Circuit) := mapped (fun i => some (enum S i).val) D

theorem expandEval (S : Finset (Fin n)) (D : Circuit) (x : Fin n → Bool) :
    circuitFun n (expand S D) x = circuitFun S.card D (fun i=>x (enum S i).val) :=
  mapped_eval _ _ _

theorem expandFan (S : Finset (Fin n)) (D : Circuit) (ok : FanInTwo D) :
    FanInTwo (expand S D) := mapped_fan _ _ ok

theorem expandPaid (S : Finset (Fin n)) (D : Circuit) :
    (expand S D).gates.countP paid=D.gates.countP paid := by
  unfold expand mapped
  simp only [List.countP_map]
  rfl

theorem restrict_lift (S : Finset (Fin n)) (x : Fin n → Bool) :
    lift S (fun i=>x (enum S i).val) = fun j=>if j∈S then x j else false := by
  funext j
  by_cases h : j∈S
  · simp [lift,pull,position,h]
  · simp [lift_outside S _ h,h]


theorem lift_update (S : Finset (Fin n)) (x : Fin S.card → Bool) (k : Fin S.card) (b : Bool) :
    lift S (Function.update x k b) = Function.update (lift S x) (enum S k).val b := by
  funext z
  by_cases h : z∈S
  · let j := (enum S).symm ⟨z,h⟩
    have zj : (enum S j).val=z := congrArg Subtype.val ((enum S).apply_symm_apply ⟨z,h⟩)
    rw [←zj,lift_inside]
    by_cases eq : j=k
    · simp [eq]
    · simp [Function.update,eq,image_ne S eq,lift_inside]
  · have ne : z≠(enum S k).val := fun e=>h (e ▸ (enum S k).property)
    simp [Function.update,ne,lift_outside S _ h]

end Plane3289.Support

namespace Plane3289
variable {V : Type} [DecidableEq V]

def adjacent (E : Finset (V×V)) (i j : V) : Prop := (i,j)∈E ∨ (j,i)∈E
def endpoints (E : Finset (V×V)) : Finset V := E.image Prod.fst ∪ E.image Prod.snd
def removeVertex (E : Finset (V×V)) (i : V) : Finset (V×V) := E.filter fun e => e.1≠i ∧ e.2≠i
def touching (E : Finset (V×V)) (i : V) : Finset (V×V) := E.filter fun e => e.1=i ∨ e.2=i
def other (i : V) (e : V×V) : V := if e.1=i then e.2 else e.1
def neighbors (E : Finset (V×V)) (i : V) : Finset V := (touching E i).image (other i)

theorem touching_injective (E : Finset (V×V)) (oriented : ∀ a b, (a,b)∈E → (b,a)∉E) (i : V) :
    Set.InjOn (other i) (↑(touching E i)) := by
  rintro ⟨a,b⟩ h ⟨c,d⟩ h' eq
  obtain ⟨ab,h⟩ := Finset.mem_filter.mp h
  obtain ⟨cd,h'⟩ := Finset.mem_filter.mp h'
  change a=i ∨ b=i at h
  change c=i ∨ d=i at h'
  change (if a=i then b else a)=(if c=i then d else c) at eq
  have reverse (u v : V) : (if u=v then v else u)=u := by by_cases eq : u=v <;> simp [eq]
  rcases h with ha|hb <;> rcases h' with hc|hd
  · subst a;subst c;simp at eq;subst d;rfl
  · subst a;subst d;simp [reverse] at eq;subst c;exact (oriented _ _ ab cd).elim
  · subst b;subst c;simp [reverse] at eq;subst d;exact (oriented _ _ ab cd).elim
  · subst b;subst d;rw [reverse,reverse] at eq;subst c;rfl

theorem edgeSplit (E : Finset (V×V)) (oriented : ∀ a b, (a,b)∈E → (b,a)∉E) (i : V) :
    (removeVertex E i).card+(neighbors E i).card=E.card := by
  rw [neighbors,Finset.card_image_of_injOn (touching_injective E oriented i)]
  have all : removeVertex E i ∪ touching E i = E := by
    ext e
    simp only [removeVertex,touching,Finset.mem_union,Finset.mem_filter]
    tauto
  have disj : Disjoint (removeVertex E i) (touching E i) := by
    apply Finset.disjoint_left.mpr
    intro e a b
    obtain ⟨_,a,b'⟩ := Finset.mem_filter.mp a
    have := (Finset.mem_filter.mp b).2
    tauto
  rw [←Finset.card_union_of_disjoint disj,all]

theorem memNeighbors (E : Finset (V×V)) (i j : V) :
    j∈neighbors E i ↔ adjacent E i j := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,mem,eq⟩:=Finset.mem_image.mp h
    obtain ⟨ab,cond⟩:=Finset.mem_filter.mp mem
    change a=i ∨ b=i at cond
    rcases cond with rfl|rfl
    · simp [other] at eq;subst j;exact Or.inl ab
    · by_cases e : a=b
      · subst a;simp [other] at eq;subst j;exact Or.inl ab
      · simp [other,e] at eq;subst j;exact Or.inr ab
  · rintro (h|h)
    · exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨h,Or.inl rfl⟩,by simp [other]⟩
    · exact Finset.mem_image.mpr ⟨(j,i),Finset.mem_filter.mpr ⟨h,Or.inr rfl⟩,by by_cases e : j=i <;> simp_all [other]⟩

theorem memEndpoints (E : Finset (V×V)) (i : V) : i∈endpoints E ↔ ∃ j, adjacent E i j := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨⟨a,b⟩,mem,rfl⟩:=Finset.mem_image.mp h
      exact ⟨b,Or.inl mem⟩
    · obtain ⟨⟨a,b⟩,mem,rfl⟩:=Finset.mem_image.mp h
      exact ⟨a,Or.inr mem⟩
  · rintro ⟨j,h|h⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),h,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(j,i),h,rfl⟩)

end Plane3289

namespace Plane3289
variable {V : Type} [DecidableEq V]
theorem adjacent_remove (E : Finset (V×V)) (i j k : V) :
    adjacent (removeVertex E i) j k ↔ j≠i ∧ k≠i ∧ adjacent E j k := by
  simp only [adjacent,removeVertex,Finset.mem_filter]
  tauto
theorem endpoints_remove (E : Finset (V×V)) (i : V)
    (survive : ∀ j∈endpoints E, j≠i → ∃ k, k≠i ∧ adjacent E j k) :
    endpoints (removeVertex E i)=(endpoints E).erase i := by
  ext j
  rw [memEndpoints,Finset.mem_erase]
  constructor
  · rintro ⟨k,h⟩
    obtain ⟨ji,_,edge⟩ := (adjacent_remove _ _ _ _).mp h
    exact ⟨ji,(memEndpoints _ _).mpr ⟨k,edge⟩⟩
  · rintro ⟨ji,inS⟩
    obtain ⟨k,ki,edge⟩:=survive j inS ji
    exact ⟨k,(adjacent_remove _ _ _ _).mpr ⟨ji,ki,edge⟩⟩
theorem endpoints_isolated (E : Finset (V×V)) (i j : V) (ij : i≠j)
    (left : ∀ k, adjacent E i k → k=j) (right : ∀ k, adjacent E j k → k=i) :
    endpoints (removeVertex E i)=((endpoints E).erase i).erase j := by
  have symm {a b : V} : adjacent E a b → adjacent E b a := Or.symm
  ext a
  rw [memEndpoints,Finset.mem_erase,Finset.mem_erase]
  constructor
  · rintro ⟨k,h⟩
    obtain ⟨ai,ki,edge⟩:=(adjacent_remove _ _ _ _).mp h
    exact ⟨by rintro rfl;exact ki (right _ edge),ai,(memEndpoints _ _).mpr ⟨k,edge⟩⟩
  · rintro ⟨aj,ai,m⟩
    obtain ⟨k,h⟩:=(memEndpoints E a).mp m
    have ki : k≠i := by rintro rfl;exact aj (left _ (symm h))
    exact ⟨k,(adjacent_remove _ _ _ _).mpr ⟨ai,ki,h⟩⟩
end Plane3289

namespace Plane3289
variable {V : Type} [DecidableEq V]
def supported (E : Finset (V×V)) (budget : ℕ) : Prop := ∃ d : ℕ,
  (endpoints E).card+d≤budget+1 ∧ E.card≤(endpoints E).card+130*d

theorem peeling (P : Finset (V×V)→ℕ→Prop)
    (move : ∀ E b, P E b → supported E b ∨
      ∃ F c, P F c ∧ (endpoints F).card<(endpoints E).card ∧
        (((endpoints E).card=(endpoints F).card+1 ∧ E.card≤F.card+1 ∧ c+1≤b) ∨
         ((endpoints E).card=(endpoints F).card+2 ∧ E.card≤F.card+1 ∧ c+2≤b) ∨
         ((endpoints E).card=(endpoints F).card+1 ∧ E.card≤F.card+131 ∧ c+2≤b))) :
    ∀ E b, P E b → supported E b := by
  intro E b h
  generalize eq : (endpoints E).card=n
  revert E b
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro E b h eq
    rcases move E b h with done|⟨F,c,p,lt,cases⟩
    · exact done
    obtain ⟨d,lower,edges⟩:=ih _ (lt.trans_eq eq) F c p rfl
    rcases cases with ⟨size,delta,cost⟩|⟨size,delta,cost⟩|⟨size,delta,cost⟩
    · exact ⟨d,by omega,by omega⟩
    · exact ⟨d,by omega,by omega⟩
    · exact ⟨d+1,by omega,by omega⟩

theorem baseEmpty {E : Finset (V×V)} (empty : E=∅) (b : ℕ) : supported E b := by
  subst E
  exact ⟨0,by simp [endpoints],by simp [endpoints]⟩

theorem baseOne {E : Finset (V×V)} (edgeCount : E.card=1) (b : ℕ) (pos : 0<b) : supported E b := by
  obtain ⟨⟨i,j⟩,rfl⟩:=Finset.card_eq_one.mp edgeCount
  by_cases e : i=j
  · subst j; exact ⟨0,by simp [endpoints],by simp [endpoints]⟩
  · exact ⟨0,by simp [endpoints,e];omega,by simp [endpoints,e]⟩
end Plane3289

namespace Plane3289
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PaidPin
variable {n : ℕ}
def Witness (E : Finset (Fin n × Fin n)) (C : Circuit) : Prop :=
  FanInTwo C ∧ (∀ i∈endpoints E, circuitFun n C (singleRow i)=false) ∧
    ∀ i∈endpoints E, ∀ j∈endpoints E, i≠j →
      (circuitFun n C (pairRow i j)=true ↔ adjacent E i j)

namespace Witness
variable {E : Finset (Fin n × Fin n)} {C : Circuit}

theorem edgeEnds {a b : Fin n} (h : adjacent E a b) : a∈endpoints E ∧ b∈endpoints E :=
  ⟨(memEndpoints E a).mpr ⟨b,h⟩,(memEndpoints E b).mpr ⟨a,Or.symm h⟩⟩

theorem remain {i a : Fin n} (h : a∈endpoints (removeVertex E i)) :
    a≠i ∧ a∈endpoints E := by
  obtain ⟨b,ab⟩ := (memEndpoints _ _).mp h
  obtain ⟨ai,_,edge⟩ := (adjacent_remove _ _ _ _).mp ab
  exact ⟨ai,(edgeEnds edge).1⟩

theorem absent (E : Finset (Fin n × Fin n)) (i : Fin n) : i∉endpoints (removeVertex E i) :=
  fun h => (remain h).1 rfl

theorem restore (w : Witness E C) (i : Fin n) (D : Circuit) (ok : FanInTwo D)
    (same : ∀ x : Fin n → Bool, (∀ k, k∉endpoints (removeVertex E i) → x k=false) →
      circuitFun n D x=circuitFun n C x) : Witness (removeVertex E i) D := by
  refine ⟨ok,?_,?_⟩
  · intro a ha
    rw [same (singleRow a) (fun k hk => by
      have ne : k≠a := fun e => hk (e ▸ ha)
      simp [singleRow,ne])]
    exact w.2.1 a (remain ha).2
  · intro a ha b hb ab
    rw [same (pairRow a b) (fun k hk => by
      have na : k≠a := fun e => hk (e ▸ ha)
      have nb : k≠b := fun e => hk (e ▸ hb)
      simp [pairRow,na,nb]),adjacent_remove]
    have test := w.2.2 a (remain ha).2 b (remain hb).2 ab
    exact ⟨fun h => ⟨(remain ha).1,(remain hb).1,test.mp h⟩,fun h=>test.mpr h.2.2⟩

theorem edge_true (w : Witness E C) {i j : Fin n} (ne : i≠j) (ij : adjacent E i j) :
    circuitFun n C (pairRow i j)=true :=
  (w.2.2 _ (edgeEnds ij).1 _ (edgeEnds ij).2 ne).mpr ij

theorem switches (w : Witness E C) {i j : Fin n} (ne : i≠j) (ij : adjacent E i j) :
    readsBit (atBit (circuitFun n C) i true) j ∧ readsBit (atBit (circuitFun n C) j true) i :=
  ⟨switchOn ne (w.2.1 _ (edgeEnds ij).1) (edge_true w ne ij),
   switchOn ne.symm (w.2.1 _ (edgeEnds ij).2) (edge_true w ne.symm (Or.symm ij))⟩

theorem positive (w : Witness E C) {i j : Fin n} (ne : i≠j) (ij : adjacent E i j) :
    1≤C.gates.countP paid := by
  obtain ⟨right,left⟩:=switches w ne ij
  obtain ⟨_,_,lt,_⟩ := pinPaid C w.1 i true (readFromPin ne.symm left) (diffFromRead right)
  omega

theorem surviveRows (w : Witness E C) (i : Fin n) (loop : ∀ a, ¬adjacent E a a)
    (nonempty : (removeVertex E i).Nonempty) :
    ∃ (x y : Fin n → Bool), circuitFun n C x≠circuitFun n C y ∧
      ∀ k, k∉endpoints (removeVertex E i) → x k=false ∧ y k=false := by
  obtain ⟨⟨a,b⟩,mem⟩:=nonempty
  have inF : adjacent (removeVertex E i) a b := Or.inl mem
  obtain ⟨_,_,edge⟩ := (adjacent_remove _ _ _ _).mp inF
  have ne : a≠b := by rintro rfl;exact loop _ edge
  refine ⟨singleRow a,pairRow a b,?_,?_⟩
  · rw [w.2.1 _ (edgeEnds edge).1,edge_true w ne edge]
    decide
  · intro k hk
    have na : k≠a := fun e=>hk (e ▸ (edgeEnds inF).1)
    have nb : k≠b := fun e=>hk (e ▸ (edgeEnds inF).2)
    simp [singleRow,pairRow,na,nb]

theorem pin_eq {m : ℕ} {x : Fin m→Bool} {k : Fin m} (h : x k=false) :
    Function.update x k false=x := by rw [←h,Function.update_eq_self]

theorem low (w : Witness E C) (loop : ∀ a, ¬adjacent E a a) {i j : Fin n}
    (ij : adjacent E i j) (other : (removeVertex E i).Nonempty) :
    ∃ D, Witness (removeVertex E i) D ∧ D.gates.countP paid+1≤C.gates.countP paid := by
  have ne : i≠j := by rintro rfl;exact loop _ ij
  obtain ⟨x,y,xy,off⟩:=surviveRows w i loop other
  obtain ⟨a,b⟩:=off i (absent _ _)
  have varying : differs (atBit (circuitFun n C) i false) := by
    exact ⟨x,y,by simpa only [atBit,pin_eq a,pin_eq b] using xy⟩
  obtain ⟨D,ok,lt,evalD⟩ := pinPaid C w.1 i false
    (readFromPin ne.symm (switches w ne ij).2) varying
  refine ⟨D,restore w i D ok ?_,by omega⟩
  intro z hz
  simpa only [pin_eq (hz _ (absent _ _))] using evalD z

theorem lowPair (w : Witness E C) (loop : ∀ a, ¬adjacent E a a) {i j : Fin n}
    (ij : adjacent E i j) (gone : j∉endpoints (removeVertex E i)) (other : (removeVertex E i).Nonempty) :
    ∃ D, Witness (removeVertex E i) D ∧ D.gates.countP paid+2≤C.gates.countP paid := by
  have ne : i≠j := by rintro rfl;exact loop _ ij
  obtain ⟨x,y,xy,off⟩:=surviveRows w i loop other
  obtain ⟨xi,yi⟩:=off i (absent _ _)
  obtain ⟨xj,yj⟩:=off j gone
  have varying : differs (atBit (atBit (circuitFun n C) i false) j false) := by
    exact ⟨x,y,by simpa only [atBit,pin_eq xi,pin_eq yi,pin_eq xj,pin_eq yj] using xy⟩
  obtain ⟨r,l⟩:=switches w ne ij
  obtain ⟨D,ok,lt,evalD⟩:=pairZeroDrop w.1 rfl ne l r varying
  refine ⟨D,restore w i D ok ?_,lt⟩
  intro z hz
  simpa only [atBit,pin_eq (hz _ (absent _ _)),pin_eq (hz _ gone)] using congrFun evalD z

theorem high (w : Witness E C) (active : (endpoints E).Nonempty)
    (loop : ∀ i, ¬adjacent E i i)
    (triangle : ∀ {i j k}, adjacent E i j → adjacent E i k → ¬adjacent E j k)
    (squares : ∀ {i j u v}, i≠j → adjacent E i u → adjacent E j u →
      adjacent E i v → adjacent E j v → u=v)
    (degree : ∀ i∈endpoints E, ∃ j k, j≠k ∧ adjacent E i j ∧ adjacent E i k) :
    ∃ i∈endpoints E, ∃ D, Witness (removeVertex E i) D ∧ D.gates.countP paid+2≤C.gates.countP paid := by
  let S:=endpoints E
  let v (k : Fin S.card) := (Support.enum S k).val
  let idx (a : Fin n) (h : a∈S) := (Support.enum S).symm ⟨a,h⟩
  have vi (a : Fin n) (h : a∈S) : v (idx a h)=a := congrArg Subtype.val ((Support.enum S).apply_symm_apply ⟨a,h⟩)
  have inj : Function.Injective v := fun _ _ e => (Support.enum S).injective (Subtype.ext e)
  let rel (a b : Fin S.card) := adjacent E (v a) (v b)
  let D := Support.circuit S C
  let f := circuitFun S.card D
  obtain ⟨a,ha⟩:=active
  have deg (k : Fin S.card) : ∃ j l, j≠l ∧ rel k j ∧ rel k l := by
    obtain ⟨b,c,bc,kb,kc⟩:=degree (v k) (Support.enum S k).property
    let hb := (edgeEnds kb).2
    let hc := (edgeEnds kc).2
    refine ⟨idx b hb,idx c hc,?_,?_,?_⟩
    · intro e;exact bc ((vi b hb).symm.trans ((congrArg v e).trans (vi c hc)))
    · simpa only [rel,vi] using kb
    · simpa only [rel,vi] using kc
  have sing (k : Fin S.card) : f (singleRow k)=false := by
    change circuitFun S.card (Support.circuit S C) (fun z=>decide (z=k))=false
    rw [Support.evalSingle]
    exact w.2.1 _ (Support.enum S k).property
  have pair (i j : Fin S.card) (ne : i≠j) : f (pairRow i j)=true ↔ rel j i := by
    change circuitFun S.card (Support.circuit S C) (fun z=>decide (z=i ∨ z=j))=true ↔ _
    rw [Support.evalPair]
    exact (w.2.2 _ (Support.enum S i).property _ (Support.enum S j).property (inj.ne ne)).trans ⟨Or.symm,Or.symm⟩
  obtain ⟨k,D',ok,lt,ev⟩:=twoDropGraph (idx a ha) f rel (fun e => Or.symm e)
    (fun b=>loop (v b)) (fun e g=>triangle e g)
    (fun ne e1 e2 e3 e4 => inj (squares (inj.ne ne) e1 e2 e3 e4))
    deg sing pair D (Support.fan S C w.1) rfl
  refine ⟨v k,(Support.enum S k).property,Support.expand S D',restore w (v k) _ (Support.expandFan S D' ok) ?_,?_⟩
  · intro z hz
    let z' : Fin S.card→Bool := fun t => z (v t)
    have off : z' k=false := hz _ (absent _ _)
    rw [Support.expandEval]
    change circuitFun S.card D' z'=_
    rw [ev,pin_eq off]
    change circuitFun S.card (Support.circuit S C) z'=_
    rw [Support.eval]
    apply congrArg (circuitFun n C)
    change Support.lift S (fun t=>z (Support.enum S t).val)=z
    rw [Support.restrict_lift]
    funext u
    by_cases h : u∈S
    · simp [h]
    · simp only [h,↓reduceIte]
      exact (hz _ fun eh=>h (remain eh).2).symm
  · simpa only [Support.expandPaid,D,Support.paidCount] using lt

end Witness
end Plane3289

namespace Plane3289
open PEqualNP.CircuitLowerBounds
open PaidPin
theorem witnessCount {n : ℕ} (G : Finset (Fin n×Fin n))
    (oriented : ∀ a b, (a,b)∈G → (b,a)∉G)
    (noTriangle : ∀ {i j k}, adjacent G i j → adjacent G i k → ¬adjacent G j k)
    (noSquare : ∀ {i j u v}, i≠j → adjacent G i u → adjacent G j u → adjacent G i v → adjacent G j v → u=v)
    (cap : ∀ i, (neighbors G i).card≤131)
    (C : Circuit) (w : Witness G C) : supported G (C.gates.countP paid) := by
  classical
  let P : Finset (Fin n×Fin n)→ℕ→Prop := fun E b => E⊆G ∧ ∃ D : Circuit, Witness E D ∧ D.gates.countP paid ≤ b
  apply peeling P ?_ G _ ⟨Finset.Subset.rfl,C,w,le_rfl⟩
  rintro E b ⟨sub,D,wd,budget⟩
  have ori : ∀ a b,(a,b)∈E → (b,a)∉E := fun a b hab hba => oriented a b (sub hab) (sub hba)
  have loop : ∀ i, ¬adjacent E i i := by intro i h;rcases h with h|h <;> exact ori i i h h
  have rel {i j} : adjacent E i j → adjacent G i j := by rintro (h|h);exact Or.inl (sub h);exact Or.inr (sub h)
  have symm {i j} : adjacent E i j → adjacent E j i := Or.symm
  have newP (i : Fin n) {D' : Circuit} (ww : Witness (removeVertex E i) D') :
      P (removeVertex E i) (D'.gates.countP paid) :=
    ⟨fun _ h => sub (Finset.mem_filter.mp h).1, D',ww,le_rfl⟩
  by_cases zero : E=∅
  · exact Or.inl (baseEmpty zero _)
  obtain ⟨⟨a,z⟩,edge⟩:=Finset.nonempty_iff_ne_empty.mpr zero
  have az : adjacent E a z := Or.inl edge
  have pos := wd.positive (show a≠z by rintro rfl;exact loop a az) az
  by_cases one : E.card=1
  · exact Or.inl (baseOne one b (by omega))
  have above : 1<E.card := by have := Finset.card_pos.mpr ⟨_,edge⟩;omega
  right
  by_cases deg : ∀ i∈endpoints E, ∃ j k, j≠k ∧ adjacent E i j ∧ adjacent E i k
  · have ta {i j k} (a : adjacent E i j) (b : adjacent E i k) (c : adjacent E j k) :=
      noTriangle (rel a) (rel b) (rel c)
    have sq {i j u v} (ij : i≠j) (a : adjacent E i u) (b : adjacent E j u) (c : adjacent E i v) (d : adjacent E j v) :=
      noSquare ij (rel a) (rel b) (rel c) (rel d)
    obtain ⟨i,hi,K,wk,saves⟩:=wd.high ⟨a,(memEndpoints E a).mpr ⟨z,az⟩⟩ loop ta sq deg
    have remain (j) (hj : j∈endpoints E) (ji : j≠i) : ∃ k, k≠i ∧ adjacent E j k := by
      obtain ⟨u,v,uv,ju,jv⟩:=deg j hj
      by_cases ui : u=i
      · exact ⟨v,by simpa [ui] using uv.symm,jv⟩
      · exact ⟨u,ui,ju⟩
    have cnt := congrArg Finset.card (endpoints_remove E i remain)
    rw [Finset.card_erase_of_mem hi] at cnt
    have posS := Finset.card_pos.mpr ⟨i,hi⟩
    have del := edgeSplit E ori i
    have lim : (neighbors E i).card ≤ 131 := (Finset.card_le_card (show neighbors E i ⊆ neighbors G i from
      fun j hj => (memNeighbors G i j).mpr (rel ((memNeighbors E i j).mp hj)))).trans (cap i)
    exact ⟨_,_,newP i wk,by omega,Or.inr (Or.inr ⟨by omega,by omega,by omega⟩)⟩
  · push Not at deg
    obtain ⟨i,hi,few⟩:=deg
    obtain ⟨j,ij⟩ := (memEndpoints E i).mp hi
    have neq : i≠j := by rintro rfl;exact loop i ij
    have only (k) (h : adjacent E i k) : k=j := by
      by_contra ne
      exact few k j ne h ij
    have n1 : neighbors E i={j} := by
      ext k;rw [memNeighbors,Finset.mem_singleton];exact ⟨only k,fun h => h.symm ▸ ij⟩
    have diff:=edgeSplit E ori i
    rw [n1,Finset.card_singleton] at diff
    have alive : (removeVertex E i).Nonempty := Finset.card_pos.mp (by omega)
    have posS := Finset.card_pos.mpr ⟨i,hi⟩
    by_cases survivor : ∃ k, k≠i ∧ adjacent E j k
    · have remain (u) (hu : u∈endpoints E) (ui : u≠i) : ∃ k, k≠i ∧ adjacent E u k := by
        by_cases uj : u=j
        · simpa [uj] using survivor
        obtain ⟨k,uk⟩ := (memEndpoints E u).mp hu
        exact ⟨k,by rintro rfl;exact uj (only _ (symm uk)),uk⟩
      obtain ⟨K,wk,saves⟩:=wd.low loop ij alive
      have cnt := congrArg Finset.card (endpoints_remove E i remain)
      rw [Finset.card_erase_of_mem hi] at cnt
      exact ⟨_,_,newP i wk,by omega,Or.inl ⟨by omega,by omega,by omega⟩⟩
    · have onlyJ (k) (jk : adjacent E j k) : k=i := by
        by_contra ki;exact survivor ⟨k,ki,jk⟩
      have desc:=endpoints_isolated E i j neq only onlyJ
      have hj : j∈(endpoints E).erase i := Finset.mem_erase.mpr ⟨neq.symm,(memEndpoints E j).mpr ⟨i,symm ij⟩⟩
      have p2 := Finset.card_pos.mpr ⟨j,hj⟩
      rw [Finset.card_erase_of_mem hi] at p2
      have cnt := congrArg Finset.card desc
      rw [Finset.card_erase_of_mem hj,Finset.card_erase_of_mem hi] at cnt
      have gone : j∉endpoints (removeVertex E i) := by rw [desc];exact Finset.notMem_erase _ _
      obtain ⟨K,wk,saves⟩:=wd.lowPair loop ij gone alive
      exact ⟨_,_,newP i wk,by omega,Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)⟩
end Plane3289

namespace Plane3289
variable {A B : Type} [DecidableEq A] [DecidableEq B]
theorem fiberBound {X Y : Type} [DecidableEq X] [DecidableEq Y] (E : Finset X) (v : X→Y)
    (bound : ℕ) (degree : ∀ i∈E.image v,(E.filter (fun e => v e=i)).card≤bound) :
    E.card ≤ bound*(E.image v).card := by
  classical
  let S := E.image v
  let F := fun i => E.filter (fun e => v e=i)
  have cover : S.biUnion F=E := by
    ext e
    constructor
    · intro h
      obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hi).1
    · intro he
      exact Finset.mem_biUnion.mpr ⟨v e,Finset.mem_image_of_mem v he,Finset.mem_filter.mpr ⟨he,rfl⟩⟩
  have disj : (↑S : Set Y).PairwiseDisjoint F := by
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro e a b
    exact ne ((Finset.mem_filter.mp a).2.symm.trans (Finset.mem_filter.mp b).2)
  calc
    E.card = (S.biUnion F).card := congrArg Finset.card cover.symm
    _ = ∑ i∈S, (F i).card := Finset.card_biUnion disj
    _ ≤ ∑ _i∈S, bound := Finset.sum_le_sum degree
    _ = bound*(E.image v).card := by simp [S,Nat.mul_comm]
theorem doubleCount (E : Finset (A×B)) (bound : ℕ)
    (left : ∀ i∈E.image Prod.fst,(E.filter (fun e => e.1=i)).card≤bound)
    (right : ∀ i∈E.image Prod.snd,(E.filter (fun e => e.2=i)).card≤bound) :
    let n := (E.image Prod.fst).card+(E.image Prod.snd).card
    2*E.card≤bound*n ∧ 4*E.card≤n*n := by
  let l := (E.image Prod.fst).card
  let r := (E.image Prod.snd).card
  change 2*E.card≤bound*(l+r) ∧ 4*E.card≤(l+r)*(l+r)
  have a : E.card≤bound*l := fiberBound E Prod.fst bound left
  have b : E.card≤bound*r := fiberBound E Prod.snd bound right
  have rect : E ⊆ (E.image Prod.fst) ×ˢ (E.image Prod.snd) := by
    intro e he
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he,Finset.mem_image_of_mem _ he⟩
  have prod : E.card≤l*r := by simpa [l,r] using Finset.card_le_card rect
  constructor
  · rw [Nat.mul_add];omega
  · have h : (4:ℤ)*(E.card:ℤ) ≤ ((l:ℤ)+(r:ℤ))*((l:ℤ)+(r:ℤ)) := by
      have p : (E.card:ℤ)≤(l:ℤ)*(r:ℤ) := by exact_mod_cast prod
      nlinarith [sq_nonneg ((l:ℤ)-(r:ℤ))]
    exact_mod_cast h
end Plane3289

namespace Plane3289.Plane
open Plane3289
variable {N : ℕ}
def L (p : Fin N) := Fin.castAdd N p
def R (l : Fin N) := Fin.natAdd N l
theorem lInj : Function.Injective (L (N:=N)) := by intro p q h;exact Fin.ext (congrArg (fun z : Fin (N+N) => z.val) h)
theorem rInj : Function.Injective (R (N:=N)) := by
  intro p q h
  apply Fin.ext
  have e := congrArg Fin.val h
  change N+p.val=N+q.val at e
  omega
theorem sep (p l : Fin N) : L p ≠ R l := by
  intro h
  have eq:=congrArg Fin.val h
  change p.val=N+l.val at eq
  omega
def encode (T : Finset (Fin N × Fin N)) : Finset (Fin (N+N) × Fin (N+N)) :=
  T.image fun e => (L e.1,R e.2)
theorem encodedCard (T : Finset (Fin N×Fin N)) : (encode T).card=T.card := by
  apply Finset.card_image_of_injective
  intro a b eq
  exact Prod.ext (lInj (congrArg Prod.fst eq)) (rInj (congrArg Prod.snd eq))
theorem inEnc {T : Finset (Fin N×Fin N)} {x y : Fin (N+N)} :
    (x,y)∈encode T ↔ ∃ p l, (p,l)∈T ∧ L p=x ∧ R l=y := by
  constructor
  · intro h
    obtain ⟨⟨p,l⟩,pl,eq⟩:=Finset.mem_image.mp h
    exact ⟨p,l,pl,congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  · rintro ⟨p,l,pl,rfl,rfl⟩
    exact Finset.mem_image.mpr ⟨(p,l),pl,rfl⟩
theorem oriented (T : Finset (Fin N×Fin N)) : ∀ a b, (a,b)∈encode T → (b,a)∉encode T := by
  intro a b h g
  obtain ⟨p,l,_,rfl,rfl⟩:=inEnc.mp h
  obtain ⟨u,v,_,eq,_⟩:=inEnc.mp g
  exact sep u l eq
theorem lr (T : Finset (Fin N×Fin N)) (p l : Fin N) : adjacent (encode T) (L p) (R l) ↔ (p,l)∈T := by
  constructor
  · rintro (h|h)
    · obtain ⟨u,v,uv,eu,ev⟩:=inEnc.mp h
      simpa [lInj eu,rInj ev] using uv
    · obtain ⟨u,v,_,bad,_⟩:=inEnc.mp h
      exact (sep u l bad).elim
  · intro h;exact Or.inl (inEnc.mpr ⟨p,l,h,rfl,rfl⟩)
theorem rl (T : Finset (Fin N×Fin N)) (p l : Fin N) : adjacent (encode T) (R l) (L p) ↔ (p,l)∈T :=
  ⟨fun h => (lr T p l).mp (Or.symm h),fun h => Or.symm ((lr T p l).mpr h)⟩
theorem ll (T : Finset (Fin N×Fin N)) (a b : Fin N) : ¬adjacent (encode T) (L a) (L b) := by
  rintro (h|h) <;> obtain ⟨p,l,_,_,bad⟩:=inEnc.mp h
  · exact sep b l bad.symm
  · exact sep a l bad.symm
theorem rr (T : Finset (Fin N×Fin N)) (a b : Fin N) : ¬adjacent (encode T) (R a) (R b) := by
  rintro (h|h) <;> obtain ⟨p,l,_,bad,_⟩:=inEnc.mp h
  · exact sep p a bad
  · exact sep p b bad
theorem side (i : Fin (N+N)) : (∃ p : Fin N, i=L p) ∨ ∃ l : Fin N, i=R l :=
  Fin.addCases (fun p => Or.inl ⟨p,rfl⟩) (fun l => Or.inr ⟨l,rfl⟩) i
theorem trFree (T : Finset (Fin N×Fin N)) {i j k} :
    adjacent (encode T) i j → adjacent (encode T) i k → ¬adjacent (encode T) j k := by
  rcases side i with ⟨a,rfl⟩|⟨a,rfl⟩ <;> rcases side j with ⟨b,rfl⟩|⟨b,rfl⟩ <;>
    rcases side k with ⟨c,rfl⟩|⟨c,rfl⟩ <;> simp only [ll,rr,false_implies,not_false_eq_true,implies_true]
theorem sqFree (T : Finset (Fin N×Fin N))
    (rect : ∀ {p q l m : Fin N}, p≠q → (p,l)∈T → (q,l)∈T → (p,m)∈T → (q,m)∈T → l=m)
    {i j u v} : i≠j → adjacent (encode T) i u → adjacent (encode T) j u →
      adjacent (encode T) i v → adjacent (encode T) j v → u=v := by
  have flip {p q l m : Fin N} (ne : l≠m) (pl : (p,l)∈T) (pm : (p,m)∈T) (ql : (q,l)∈T) (qm : (q,m)∈T) :
      p=q := by by_contra pq;exact ne (rect pq pl ql pm qm)
  rcases side i with ⟨a,rfl⟩|⟨a,rfl⟩ <;> rcases side j with ⟨b,rfl⟩|⟨b,rfl⟩ <;>
    rcases side u with ⟨c,rfl⟩|⟨c,rfl⟩ <;> rcases side v with ⟨d,rfl⟩|⟨d,rfl⟩ <;>
    simp only [ll,rr,lr,rl,false_implies,implies_true]
  · intro ne ac bc ad bd
    exact congrArg R (rect (fun e => ne (congrArg L e)) ac bc ad bd)
  · intro ne ca cb da db
    exact congrArg L (flip (fun e => ne (congrArg R e)) ca cb da db)
end Plane3289.Plane

namespace Plane3289

theorem pencilSize {N q : ℕ} (hq : 0 < q) (hs : N = q^2+q+1)
    (S : Fin N → Finset (Fin N)) (line : ∀ l, (S l).card=q+1)
    (unique : ∀ a b : Fin N, a≠b → ∃! l, a∈S l ∧ b∈S l) :
    ∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => p∈S l)).card=q+1 := by
  classical
  intro p
  let L := Finset.univ.filter (fun l : Fin N => p ∈ S l)
  let t := fun l => (S l).erase p
  have punctured (D : Finset (Fin N)) (sub : D ⊆ L) : (D.biUnion t).card=D.card*q := by
    have disj : (↑D : Set (Fin N)).PairwiseDisjoint t := by
      intro a ha b hb ne
      apply Finset.disjoint_left.mpr
      intro x hxa hxb
      obtain ⟨nx,xa⟩ := Finset.mem_erase.mp hxa
      obtain ⟨_,xb⟩ := Finset.mem_erase.mp hxb
      exact ne ((unique p x nx.symm).unique ⟨(Finset.mem_filter.mp (sub ha)).2,xa⟩ ⟨(Finset.mem_filter.mp (sub hb)).2,xb⟩)
    rw [Finset.card_biUnion disj]
    have cells (l) (hl : l ∈ D) : (t l).card=q := by
      rw [show t l=(S l).erase p from rfl,Finset.card_erase_of_mem (Finset.mem_filter.mp (sub hl)).2,line]
      omega
    rw [Finset.sum_congr rfl cells]
    simp
  have entire : L.biUnion t = Finset.univ.erase p := by
    ext x
    constructor
    · intro hx
      obtain ⟨l,_,hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,Finset.mem_univ _⟩
    · intro hx
      obtain ⟨nx,_⟩ := Finset.mem_erase.mp hx
      obtain ⟨l,⟨hp,h⟩,_⟩ := unique p x nx.symm
      exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,Finset.mem_erase.mpr ⟨nx,h⟩⟩
  have cnt := punctured L (fun _ h => h)
  rw [entire,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin] at cnt
  have count : L.card=q+1 := by
    have e : L.card*q=(q+1)*q := by nlinarith [show N-1=q^2+q from by omega]
    exact Nat.eq_of_mul_eq_mul_right hq e
  exact count
end Plane3289

namespace Plane3289.Plane
open Plane3289
variable {N q : ℕ}
theorem capOfIncidence (T : Finset (Fin N × Fin N)) (lines : Fin N→Finset (Fin N))
    (inside : ∀ p l,(p,l)∈T → p∈lines l)
    (lineCard : ∀ l, (lines l).card=q+1)
    (pencilCard : ∀ p, (Finset.univ.filter (fun l => p∈lines l)).card=q+1)
    (qSmall : q≤130) (i : Fin (N+N)) : (neighbors (encode T) i).card≤131 := by
  classical
  rcases side i with ⟨p,rfl⟩|⟨l,rfl⟩
  · let A := Finset.univ.filter (fun l => p∈lines l)
    have sub : neighbors (encode T) (L p) ⊆ A.image R := by
      intro k h
      have e := (memNeighbors _ _ _).mp h
      rcases side k with ⟨a,rfl⟩|⟨l,rfl⟩
      · exact (ll T p a e).elim
      · exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,inside _ _ ((lr _ _ _).mp e)⟩,rfl⟩
    have b := (Finset.card_le_card sub).trans (Finset.card_image_le)
    change (neighbors (encode T) (L p)).card ≤ (Finset.univ.filter (fun l => p∈lines l)).card at b
    rw [pencilCard p] at b
    omega
  · have sub : neighbors (encode T) (R l) ⊆ (lines l).image L := by
      intro k h
      have e := (memNeighbors _ _ _).mp h
      rcases side k with ⟨p,rfl⟩|⟨a,rfl⟩
      · exact Finset.mem_image.mpr ⟨p,inside _ _ ((rl _ _ _).mp e),rfl⟩
      · exact (rr T l a e).elim
    have b := (Finset.card_le_card sub).trans (Finset.card_image_le)
    rw [lineCard l] at b
    omega
theorem encodedCounts (T : Finset (Fin N×Fin N)) (cap : ∀ i,(neighbors (encode T) i).card≤131) :
    2*(encode T).card ≤ 131*(endpoints (encode T)).card ∧
    4*(encode T).card ≤ (endpoints (encode T)).card*(endpoints (encode T)).card := by
  classical
  let E := encode T
  have disj : Disjoint (E.image Prod.fst) (E.image Prod.snd) := by
    apply Finset.disjoint_left.mpr
    intro i a b
    obtain ⟨⟨p,l⟩,pl,rfl⟩:=Finset.mem_image.mp a
    obtain ⟨⟨u,v⟩,uv,ev⟩:=Finset.mem_image.mp b
    obtain ⟨x,y,_,hx,_⟩:=inEnc.mp pl
    obtain ⟨x',y',_,_,hy⟩:=inEnc.mp uv
    exact sep x y' ((hx.trans ev.symm).trans hy.symm)
  have count : (endpoints E).card=(E.image Prod.fst).card+(E.image Prod.snd).card :=
    Finset.card_union_of_disjoint disj
  have left (i) (_ : i∈E.image Prod.fst) : (E.filter (fun e => e.1=i)).card≤131 := by
    have sub : E.filter (fun e => e.1=i) ⊆ touching E i :=
      fun e h => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,Or.inl (Finset.mem_filter.mp h).2⟩
    have same : (touching E i).card=(neighbors E i).card := (Finset.card_image_of_injOn (touching_injective E (oriented T) i)).symm
    exact (Finset.card_le_card sub).trans (same.le.trans (cap i))
  have right (i) (_ : i∈E.image Prod.snd) : (E.filter (fun e => e.2=i)).card≤131 := by
    have sub : E.filter (fun e => e.2=i) ⊆ touching E i :=
      fun e h => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,Or.inr (Finset.mem_filter.mp h).2⟩
    have same : (touching E i).card=(neighbors E i).card := (Finset.card_image_of_injOn (touching_injective E (oriented T) i)).symm
    exact (Finset.card_le_card sub).trans (same.le.trans (cap i))
  change 2*E.card≤131*(endpoints E).card ∧ 4*E.card≤(endpoints E).card*(endpoints E).card
  rw [count];exact doubleCount E 131 left right
end Plane3289.Plane

namespace Plane3289.Plane
open Plane3289
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PaidPin
variable {N q : ℕ}
def tests (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) : Finset (Fin N×Fin N) :=
  Finset.univ.filter fun e => I e.1 e.2 ∧ circuitFun (N+N) C (pairRow (L e.1) (R e.2))=true
def SoundOn (I : Fin N → Fin N → Prop) (C : Circuit) (q : ℕ) : Prop :=
  ∀ x : Fin (N+N)→Bool, Fintype.card { l : Fin N // x (R l)=true }≤q →
    (¬∃ p l,I p l ∧ x (L p)=true ∧ x (R l)=true) → circuitFun (N+N) C x=false
theorem fewLines (a b : Fin (N+N)) : Fintype.card { l : Fin N // pairRow a b (R l)=true }≤2 := by
  let S : Finset (Fin (N+N)) := {a,b}
  let g : { l : Fin N // pairRow a b (R l)=true } → ↥S := fun l =>
    ⟨R l.val,by simpa [S,pairRow] using l.property⟩
  have inj : Function.Injective g := by
    intro x y eq
    exact Subtype.ext (rInj (congrArg Subtype.val eq))
  have c := Fintype.card_le_of_injective g inj
  have d : S.card≤2 := by simpa [S] using (Finset.card_insert_le a ({b} : Finset (Fin (N+N))))
  exact c.trans (by simpa using d)
theorem testsWitness (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (q2 : 2≤q) (mono : Monotone2 C) (sound : SoundOn I C q) : Witness (encode (tests I C)) C := by
  classical
  let E := encode (tests I C)
  let f := circuitFun (N+N) C
  have off (a b : Fin (N+N)) (h : ¬∃ p l, I p l ∧ pairRow a b (L p)=true ∧ pairRow a b (R l)=true) :
      f (pairRow a b)=false := sound _ ((fewLines a b).trans q2) h
  have pointOff (p p' : Fin N) : f (pairRow (L p) (L p'))=false := by
    apply off
    rintro ⟨_,l,_,_,h⟩
    simp [pairRow,(sep p l).symm,(sep p' l).symm] at h
  have lineOff (l l' : Fin N) : f (pairRow (R l) (R l'))=false := by
    apply off
    rintro ⟨p,_,_,h,_⟩
    simp [pairRow,sep p l,sep p l'] at h
  have single (i : Fin (N+N)) : f (singleRow i)=false := by
    have eq : singleRow i=pairRow i i := by funext z;simp [singleRow,pairRow]
    rw [eq]
    rcases side i with ⟨p,rfl⟩|⟨l,rfl⟩
    · exact pointOff p p
    · exact lineOff l l
  have cross (p l : Fin N) : f (pairRow (L p) (R l))=true ↔ (p,l)∈tests I C := by
    simp only [tests,Finset.mem_filter,Finset.mem_univ,true_and]
    change f _=true ↔ I p l ∧ f _=true
    refine ⟨fun yes => ⟨?_,yes⟩,And.right⟩
    by_contra bad
    have ff := off (L p) (R l) (by
      rintro ⟨a,b,inside,ha,hb⟩
      have aa : L a=L p := by simpa [pairRow,sep a l] using ha
      have bb : R b=R l := by simpa [pairRow,(sep p b).symm] using hb
      exact bad (by simpa [lInj aa,rInj bb] using inside))
    rw [ff] at yes
    contradiction
  refine ⟨?_,fun i _ => single i,?_⟩
  · intro g hg
    obtain ⟨ops,sz⟩:=mono g hg
    exact ⟨ops.imp_right Or.inl,sz⟩
  · intro a _ b _ ne
    change f (pairRow a b)=true ↔ adjacent E a b
    rcases side a with ⟨p,rfl⟩|⟨l,rfl⟩ <;> rcases side b with ⟨p',rfl⟩|⟨l',rfl⟩
    · simp only [pointOff,Bool.false_eq_true,ll,E]
    · exact (cross p l').trans (lr _ _ _).symm
    · have rev : pairRow (R l) (L p')=pairRow (L p') (R l) := by funext x;simp [pairRow,or_comm]
      rw [rev];exact (cross p' l).trans (rl _ _ _).symm
    · simp only [lineOff,Bool.false_eq_true,rr,E]
end Plane3289.Plane

namespace Plane3289
theorem countBipartite (n m d s : ℕ) (support : n+d ≤ s+1)
    (deleted : m ≤ n+130*d) (degree : 2*m ≤ 131*n)
    (bip : 4*m ≤ n*n) (nontrivial : 0 < m → 0 < s) : m ≤ 44*s := by
  by_cases large : 199 ≤ s
  · have h : 389*m ≤ 17030*(s+1) := by linarith only [support,deleted,degree]
    linarith only [h,large]
  · by_contra! big
    have nsmall : n ≤ 134 := by omega
    have bound := Nat.mul_le_mul_right n nsmall
    have sp : 0 < s := nontrivial (by omega)
    by_cases s1 : s ≤ 3
    · have a : n ≤ 4 := by omega
      have z := Nat.mul_le_mul a a
      omega
    · omega
end Plane3289

namespace Plane3289.Plane
open Plane3289
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PaidPin
theorem filterCard {A : Type} [Fintype A] [DecidableEq A] (p : A→Prop) [DecidablePred p] :
    Fintype.card {a // p a}=(Finset.univ.filter p).card := by
  let e : {a // p a} ≃ ↥(Finset.univ.filter p) :=
    ⟨fun a => ⟨a.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.property⟩⟩,
     fun a => ⟨a.val,(Finset.mem_filter.mp a.property).2⟩,fun _ => rfl,fun _ => rfl⟩
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)
theorem planeResult (q N : ℕ) (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (q2 : 2≤q) (qMax : q≤130) (nEq : N=q^2+q+1)
    (lineCard : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ a b : Fin N,a≠b → ∃! l, I a l ∧ I b l)
    (mono : Monotone2 C) (sound : SoundOn I C q) : (tests I C).card≤44*C.size := by
  classical
  let T := tests I C
  let E := encode T
  let lines (l : Fin N) := Finset.univ.filter (fun p => I p l)
  have lc (l : Fin N) : (lines l).card=q+1 := (filterCard (fun p => I p l)).symm.trans (lineCard l)
  have u (a b : Fin N) (h : a≠b) : ∃! l, a∈lines l ∧ b∈lines l := by simpa [lines] using unique a b h
  have pencil := pencilSize (by omega : 0<q) nEq lines lc u
  have onT {p l : Fin N} (h : (p,l)∈T) : I p l := (Finset.mem_filter.mp h).2.1
  have cap := capOfIncidence T lines (fun _ _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,onT h⟩) lc pencil qMax
  have rect {p p' l m : Fin N} (ne : p≠p') (pa : (p,l)∈T) (pb : (p',l)∈T)
      (pc : (p,m)∈T) (pd : (p',m)∈T) : l=m :=
    (unique p p' ne).unique ⟨onT pa,onT pb⟩ ⟨onT pc,onT pd⟩
  have w : Witness E C := testsWitness I C q2 mono sound
  obtain ⟨d,support,deleted⟩ := witnessCount E (oriented T) (trFree T) (sqFree T rect) cap C w
  obtain ⟨degree,bip⟩ := encodedCounts T cap
  have pos (m : 0<E.card) : 0<C.gates.countP paid := by
    obtain ⟨⟨a,b⟩,h⟩:=Finset.card_pos.mp m
    have ne : a≠b := by rintro rfl;exact oriented T _ _ h h
    exact w.positive ne (Or.inl h)
  have bounds := countBipartite (endpoints E).card E.card d (C.gates.countP paid) support deleted degree bip pos
  have pay : C.gates.countP paid ≤ C.size := List.countP_le_length
  change T.card≤44*C.size
  rw [←encodedCard T]
  exact bounds.trans (Nat.mul_le_mul_left _ pay)
end Plane3289.Plane

end PEqualNP.Outside.L_meta_3289_aux

open PEqualNP.Outside.L_meta_3289_aux

theorem PEqualNP.Outside.L_meta_3289 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x13.1 ∨ x14 = Fin.natAdd x2 x13.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  intro q N I dec C q2 qMax nEq lc u mono sound
  rw [Plane3289.Plane.filterCard]
  exact Plane3289.Plane.planeResult q N I C q2 qMax nEq lc u mono sound
