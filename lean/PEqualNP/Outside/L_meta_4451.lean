import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4451.Mono
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def Rel (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

theorem rel_append (a b : List Bool) (ha : Rel a b) (u v : Bool)
    (huv : u = true → v = true) : Rel (a ++ [u]) (b ++ [v]) := by
  have hlength := ha.1
  constructor
  · simp [ha.1]
  · intro i hi
    by_cases h : i < a.length
    · rw [List.getD_append a [u] false i h] at hi
      rw [List.getD_append b [v] false i (by omega)]
      exact ha.2 i hi
    · have hle : a.length ≤ i := by omega
      have hle' : b.length ≤ i := by omega
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_append_right hle] at hi
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_append_right hle', ← ha.1]
      cases hsub : i - a.length with
      | zero => simpa [hsub] using huv (by simpa [hsub] using hi)
      | succ k => simp [hsub] at hi

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_rel (g : Gate) (a b : List Bool) (hab : Rel a b)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2) :
    Rel (step a g) (step b g) := by
  apply rel_append a b hab
  intro h
  obtain ⟨i,j,hij⟩ := List.length_eq_two.mp hlen
  rcases hop with hop | hop
  · simp [hop, hij, GateOp.eval] at h ⊢
    exact ⟨hab.2 i h.1, hab.2 j h.2⟩
  · simp [hop, hij, GateOp.eval] at h ⊢
    exact h.elim (fun hi => Or.inl (hab.2 i hi)) (fun hj => Or.inr (hab.2 j hj))

theorem fold_rel (gs : List Gate) (a b : List Bool) (hab : Rel a b)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hlen : ∀ g ∈ gs, g.inputs.length = 2) :
    Rel (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (step_rel g a b hab (hop g (by simp)) (hlen g (by simp)))
      (fun q hq => hop q (by simp [hq])) (fun q hq => hlen q (by simp [hq]))

theorem ofFn_rel {n : Nat} (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : Rel (List.ofFn x) (List.ofFn y) := by
  constructor
  · simp
  · intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    by_cases h : i < n
    · simp only [dite_eq_left h, Option.getD_some] at hi ⊢
      exact hxy ⟨i,h⟩ hi
    · simp [h] at hi

theorem wires_mono {n : Nat} : ∀ (C : Circuit), IsAO2 n C →
    ∀ (x y : Fin n → Bool), (∀ i, x i = true → y i = true) →
    ∀ (w : Nat), (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  intro C hC x y hxy w hw
  exact (fold_rel C.gates _ _ (ofFn_rel x y hxy) hC.1 hC.2.2).2 w hw

end PEqualNP.Outside.L_meta_4451.Mono


namespace PEqualNP.Outside.L_meta_4451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


abbrev Stat := Option Nat

def sval (w : List Bool) : Stat → Bool
  | none => false
  | some i => w.getD i false

def valid (m : Nat) : Stat → Prop
  | none => True
  | some i => i < m

def Ok (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

def simplify (op : GateOp) (m : Nat) (ins : List Stat) : Option Gate × Stat :=
  match op, ins with
  | .and, [some i, some j] => (some ⟨.and, [i,j]⟩, some m)
  | .and, _ => (none, none)
  | .or, [none, s] => (none, s)
  | .or, [s, none] => (none, s)
  | .or, [some i, some j] => (some ⟨.or, [i,j]⟩, some m)
  | _, _ => (none, none)

theorem simplify_ok (op : GateOp) (m : Nat) (ins : List Stat)
    (hop : op = .and ∨ op = .or) (hlen : ins.length = 2)
    (hv : ∀ s ∈ ins, valid m s) :
    ∀ g ∈ (simplify op m ins).1.toList, Ok g ∧ ∀ i ∈ g.inputs, i < m := by
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [simplify, valid, Ok]

theorem simplify_count (op : GateOp) (m : Nat) (ins : List Stat)
    (hop : op = .and ∨ op = .or) (hlen : ins.length = 2) (hc : none ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> simp_all [simplify]

theorem simplify_sound (op : GateOp) (hop : op = .and ∨ op = .or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length = 2)
    (hv : ∀ s ∈ ins, valid w.length s) :
    valid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (sval w)) := by
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [simplify, valid, sval, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i none)).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i none)).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i none)).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : Nat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length → acc.1.getD k none = none →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g,hg,_⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · have hgok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i none)).1 = none := by
        apply simplify_count
        · exact hgok.1
        · simpa using hgok.2
        · exact List.mem_map.2 ⟨k,hkg,hc⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g',hg',hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g',h,hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc) hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i none)).1
        omega
      omega

theorem valid_mono {m m' : Nat} (h : m ≤ m') : ∀ s : Stat, valid m s → valid m' s
  | none, _ => trivial
  | some _, hj => lt_of_lt_of_le hj h

theorem sval_append (w t : List Bool) : ∀ s : Stat, valid w.length s →
    sval (w ++ t) s = sval w s
  | none, _ => rfl
  | some _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    valid (n + acc.2.length) (acc.1.getD i none) ∧
    sval (wiresFrom acc.2 y) (acc.1.getD i none) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i none with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (sval w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show valid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i none) ∧
      sval (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i none) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, sval_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


theorem model_append_option (n : Nat) (gs : List Gate) (o : Option Gate)
    (hmodel : IsAO2 n ⟨gs,0⟩)
    (hnew : ∀ g ∈ o.toList, Ok g ∧ ∀ i ∈ g.inputs, i < n + gs.length) :
    IsAO2 n ⟨gs ++ o.toList,0⟩ := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hmodel.1 g hg
    · exact (hnew g hg).1.1
  · intro j hj i hi
    change i ∈ ((gs ++ o.toList).getD j ⟨.or,[]⟩).inputs at hi
    by_cases h : j < gs.length
    · rw [List.getD_append gs o.toList ⟨.or,[]⟩ j h] at hi
      exact hmodel.2.1 j h i hi
    · cases o with
      | none => simp only [Option.toList_none, List.append_nil] at hj; omega
      | some g =>
        have heq : j = gs.length := by
          simp only [Option.toList_some, List.length_append, List.length_singleton] at hj
          omega
        subst j
        simp only [Option.toList_some, getD_snoc_eq] at hi
        exact (hnew g (by simp)).2 i hi
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hmodel.2.2 g hg
    · exact (hnew g hg).1.2

theorem model_elim (n : Nat) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, Ok g) → Inv n y w acc → IsAO2 n ⟨acc.2,0⟩ →
      IsAO2 n ⟨(elim n gs acc).2,0⟩ := by
  induction gs with
  | nil => intro w acc _ _ hm; exact hm
  | cons g gs ih =>
    intro w acc hok hinv hm
    have hg : Ok g := hok g (by simp)
    have hnext := inv_elim n y hy [g] w acc (by simpa using hg) hinv
    apply ih (wiresFrom [g] w) (elimStep n acc g)
      (fun q hq => hok q (by simp [hq])) hnext
    apply model_append_option n acc.2 _ hm
    apply simplify_ok
    · exact hg.1
    · simpa using hg.2
    · intro s hs
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
      exact (hinv.2 i).1

def initStats (n : Nat) (a : Fin n) : List Stat :=
  List.ofFn fun i : Fin n => if i = a then none else some i.val

theorem inv_init (n : Nat) (a : Fin n) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn fun i => if i = a then false else x i)
      (initStats n a, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  by_cases h : i < n
  · simp only [initStats, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_left h, Option.getD_some, List.length_nil, Nat.add_zero]
    split_ifs with ha
    · simp [valid, sval]
    · simp [valid, sval, wiresFrom, h]
  · simp [initStats, List.getD_eq_getElem?_getD, h, valid, sval]

theorem initStats_at (n : Nat) (a : Fin n) : (initStats n a).getD a.val none = none := by
  simp [initStats, List.getD_eq_getElem?_getD, a.isLt]

theorem restrict_circuit (n : Nat) (C : Circuit) (a : Fin n)
    (hC : IsAO2 n C) (hread : ∃ g ∈ C.gates, a.val ∈ g.inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x, circuitFun n D x = circuitFun n C (fun i => if i = a then false else x i) := by
  let acc := elim n C.gates (initStats n a, [])
  let o := acc.1.getD C.output none
  let D : Circuit := ⟨acc.2, o.getD (n + acc.2.length)⟩
  have hok : ∀ g ∈ C.gates, Ok g := fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩
  have hm : IsAO2 n ⟨acc.2,0⟩ := model_elim n (List.ofFn fun _ : Fin n => false)
    (by simp) C.gates _ _ hok (inv_init n a (fun _ => false)) (by
      simp [IsAO2, AndOrOnly, ReadsBack, gateAt])
  refine ⟨D,hm,?_,?_⟩
  · have hs := elim_len_lt n a.val C.gates (initStats n a, []) hok
      (by simp [initStats]) (initStats_at n a) hread
    change acc.2.length < C.gates.length
    change acc.2.length + 1 ≤ 0 + C.gates.length at hs
    omega
  · intro x
    have hinv := inv_elim n (List.ofFn x) (by simp) C.gates _ _ hok (inv_init n a x)
    have hout := (hinv.2 C.output).2
    change sval (wiresFrom acc.2 (List.ofFn x)) o =
      circuitFun n C (fun i => if i = a then false else x i) at hout
    change (wiresFrom acc.2 (List.ofFn x)).getD (o.getD (n + acc.2.length)) false = _
    rw [← hout]
    cases ho : o with
    | none =>
      simp only [Option.getD_none, sval]
      apply List.getD_eq_default
      rw [length_wiresFrom, List.length_ofFn]
    | some j => rfl

end PEqualNP.Outside.L_meta_4451


namespace PEqualNP.Outside.L_meta_4451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

theorem foldl_stepW_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem input_val (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (C.gates.foldl stepW (List.ofFn x)).getD i.val false = x i
  rw [foldl_stepW_getD _ _ _ (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem append_agree_except (a : Nat) (w v : List Bool) (b : Bool)
    (hlen : w.length = v.length)
    (hag : ∀ i, i ≠ a → w.getD i false = v.getD i false) :
    ∀ i, i ≠ a → (w ++ [b]).getD i false = (v ++ [b]).getD i false := by
  intro i hi
  by_cases h : i < w.length
  · rw [List.getD_append w [b] false i h,
        List.getD_append v [b] false i (by omega)]
    exact hag i hi
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : w.length ≤ i),
      List.getElem?_append_right (by omega : v.length ≤ i), hlen]

theorem fold_agree_except (a : Nat) (gs : List Gate) (w v : List Bool)
    (hlen : w.length = v.length)
    (hag : ∀ i, i ≠ a → w.getD i false = v.getD i false)
    (hread : ∀ g ∈ gs, a ∉ g.inputs) :
    ∀ i, i ≠ a → (gs.foldl stepW w).getD i false =
      (gs.foldl stepW v).getD i false := by
  induction gs generalizing w v with
  | nil => exact hag
  | cons g gs ih =>
    have hvals : (g.inputs.map fun i => w.getD i false) =
        (g.inputs.map fun i => v.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hag i (by intro h; subst i; exact hread g (by simp) hi)
    apply ih
    · simp [stepW, hlen]
    · unfold stepW
      rw [hvals]
      exact append_agree_except a w v _ hlen hag
    · intro q hq
      exact hread q (by simp [hq])

theorem ofFn_agree_except {n : Nat} (a : Fin n) (x y : Fin n → Bool)
    (hag : ∀ i, i ≠ a → x i = y i) :
    ∀ i, i ≠ a.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < n
  · simp only [dite_eq_left h, Option.getD_some]
    exact hag ⟨i,h⟩ (by intro ha; exact hi (congrArg Fin.val ha))
  · simp [h]

theorem reads_input {n : Nat} (C : Circuit) (a b : Fin n)
    (ha : circuitFun n C (fun i => decide (i = a)) = false)
    (hb : circuitFun n C (fun i => decide (i = b)) = false)
    (hab : circuitFun n C (fun i => decide (i = a ∨ i = b)) = true) :
    ∃ g ∈ C.gates, a.val ∈ g.inputs := by
  have hout : C.output ≠ a.val := by
    intro h
    change (C.wires (List.ofFn fun i : Fin n => decide (i = a))).getD C.output false = false at ha
    rw [h, input_val] at ha
    simp at ha
  by_contra hnone
  have hread : ∀ g ∈ C.gates, a.val ∉ g.inputs := by
    intro g hg hi
    exact hnone ⟨g,hg,hi⟩
  have hag : ∀ i : Fin n, i ≠ a → decide (i = a ∨ i = b) = decide (i = b) := by
    intro i hi
    simp [hi]
  have heq := fold_agree_except a.val C.gates
    (List.ofFn fun i : Fin n => decide (i = a ∨ i = b))
    (List.ofFn fun i : Fin n => decide (i = b))
    (by simp) (ofFn_agree_except a _ _ hag) hread C.output hout
  change circuitFun n C (fun i => decide (i = a ∨ i = b)) =
    circuitFun n C (fun i => decide (i = b)) at heq
  rw [hab,hb] at heq
  contradiction

end PEqualNP.Outside.L_meta_4451

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4451

theorem PEqualNP.Outside.L_meta_4451 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x3)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x8 : Fin x1) => Decidable.decide (x8 = x4)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x9 : Fin x1) => Decidable.decide (x9 = x3 ∨ x9 = x4)) = Bool.true → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x10 ∧ x10.size < x2.size ∧ (∀ (x11 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.true) ∧ ∀ (x11 : Fin x1 → Bool), x11 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x2 x11 := by
  intro n C a b hC hne ha hb hab
  obtain ⟨D,hD,hs,hfun⟩ := restrict_circuit n C a hC (reads_input C a b ha hb hab)
  refine ⟨D,hD,hs,?_,?_⟩
  · intro x hon
    rw [hfun] at hon
    exact Mono.wires_mono C hC _ x (by
      intro i hi
      by_cases h : i = a
      · simp [h] at hi
      · simpa [h] using hi) C.output hon
  · intro x hx
    rw [hfun]
    congr 1
    funext i
    by_cases h : i = a
    · subst i
      simp [hx]
    · simp [h]
