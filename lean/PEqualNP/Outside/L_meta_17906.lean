import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17906

open PEqualNP.CircuitLowerBounds

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

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

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Represents

private def good (m : ℕ) (g : Gate) : Prop :=
    (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) ∧
    g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m

private def packed (n : ℕ) (gs : List Gate) : Prop :=
    ∀ j < gs.length, good (n+j) (gs.getD j ⟨.or, []⟩)

private theorem emitted_good (op : GateOp) (hop : op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (m : ℕ) (ins : List Stat) (valid : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, good m g := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd, good, Stat.Valid]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr, good, Stat.Valid]

private theorem packed_extend (n : ℕ) (gs : List Gate) (step : Option Gate)
    (h : packed n gs) (hstep : ∀ g ∈ step, good (n+gs.length) g) :
    packed n (gs ++ step.toList) := by
  cases step with
  | none => simpa using h
  | some g =>
    intro j hj
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj']
      exact h j hj'
    · have he : j = gs.length := by simp at hj; omega
      subst j
      simpa using hstep g (by simp)

private theorem elim_packed (n : ℕ) (gs : List Gate) (y : List Bool) (hy : y.length = n)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) (acc : List Stat × List Gate)
    (hs : Inv n y w acc) (hp : packed n acc.2) :
    packed n (elim n gs acc).2 := by
  induction gs generalizing acc w with
  | nil => exact hp
  | cons g gs ih =>
    have hOk (g' : Gate) (mem : g' ∈ g :: gs) : Ok g' := by
      obtain ⟨op,len⟩ := hmono g' mem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
      exact ⟨op.elim Or.inl (Or.inr ∘ Or.inl), len⟩
    apply ih (fun g' hg => hmono g' (List.mem_cons_of_mem _ hg))
      (wiresFrom [g] w) (elimStep n acc g)
    · exact inv_elim n y hy [g] w acc
        (fun g' hg => hOk g' (List.mem_cons.mpr (Or.inl (by simpa using hg)))) hs
    · unfold elimStep
      refine packed_extend _ _ _ hp (emitted_good g.op (hmono g (by simp)).1 _ _ ?_)
      intro s h
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
      exact (hs.2 a).1

private def startStats (n : ℕ) : List Stat :=
    List.ofFn (fun i : Fin n => Stat.wire i)

private theorem inv_start (n : ℕ) (y : List Bool) (hy : y.length = n) :
    Inv n y y (startStats n, []) := by
  refine ⟨by simp [startStats, hy], ?_⟩
  intro i
  change ((startStats n).getD i (.const false)).Valid (n+0) ∧
    ((startStats n).getD i (.const false)).val y = y.getD i false
  by_cases hi : i < n
  · simp [startStats, List.getD_eq_getElem?_getD, hi, Stat.Valid, Stat.val]
  · simp [startStats, List.getD_eq_getElem?_getD, hi, hy, Stat.Valid, Stat.val]

private theorem packed_isAO2 {n : ℕ} {gs : List Gate} (h : packed n gs) (o : ℕ) :
    IsAO2 n (⟨gs,o⟩ : Circuit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g mem
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
    have hh := h j hj
    rw [List.getD_eq_getElem?_getD] at hh
    exact (by simpa [hj] using hh.1)
  · intro j hj i hi
    exact (h j hj).2.2 i hi
  · intro g mem
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
    have hh := h j hj
    rw [List.getD_eq_getElem?_getD] at hh
    exact (by simpa [hj] using hh.2.1)

theorem normalize_nonconstant {n : ℕ} {C : Circuit} (mono : Monotone2 C)
    {x y : List Bool} (hx : x.length = n) (hy : y.length = n) (hne : C.eval x ≠ C.eval y) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ D.output < n+D.gates.length ∧
      ∀ z : List Bool, z.length = n → D.eval z = C.eval z := by
  let a := elim n C.gates (startStats n, [])
  have hOk (g : Gate) (mem : g ∈ C.gates) : Ok g := by
    obtain ⟨op,len⟩ := mono g mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    exact ⟨op.elim Or.inl (Or.inr ∘ Or.inl), len⟩
  have hInv (z : List Bool) (hz : z.length = n) :
      Inv n z (wiresFrom C.gates z) a :=
    inv_elim n z hz C.gates z _ hOk (inv_start n z hz)
  have hp : packed n a.2 := elim_packed n C.gates x hx mono x _
    (inv_start n x hx) (by simp [packed])
  have hl : a.2.length ≤ C.gates.length := by
    simpa [a] using elim_len n C.gates (startStats n, [])
  cases hs : a.1.getD C.output (.const false) with
  | const b =>
    apply False.elim
    apply hne
    have ex := ((hInv x hx).2 C.output).2
    have ey := ((hInv y hy).2 C.output).2
    rw [hs] at ex ey
    exact ex.symm.trans ey
  | wire o =>
    have hh := ((hInv x hx).2 C.output).1
    rw [hs] at hh
    refine ⟨⟨a.2,o⟩, packed_isAO2 hp o, hl, hh, ?_⟩
    intro z hz
    have e := ((hInv z hz).2 C.output).2
    rw [hs] at e
    exact e

open PEqualNP.GenericRejection PEqualNP.HeptadCover

private theorem main (C : Circuit) (hm : Monotone2 C)
    (hc : ComputesIncidence singerLines3 C) :
    ∃ D : Circuit, IsAO2 26 D ∧ ComputesIncidence singerLines3 D ∧ D.size ≤ C.size := by
  have htrue : C.eval (incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13))) = true := by
    rw [hc]
    decide
  have hfalse : C.eval (incidenceInput (∅ : Finset (Fin 13)) (∅ : Finset (Fin 13))) = false := by
    rw [hc]
    decide
  have hne : C.eval (incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13))) ≠
      C.eval (incidenceInput (∅ : Finset (Fin 13)) (∅ : Finset (Fin 13))) := by
    simp [htrue, hfalse]
  obtain ⟨D, hd, hsize, _, heq⟩ := normalize_nonconstant (n := 26) hm
    (by simp [incidenceInput]) (by simp [incidenceInput]) hne
  refine ⟨D, hd, ?_, hsize⟩
  intro X Y
  rw [heq _ (by simp [incidenceInput]), hc]

end PEqualNP.Outside.L_meta_17906

theorem PEqualNP.Outside.L_meta_17906 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧ PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x4 ∧ x4.size ≤ x1.size) := by
  exact PEqualNP.Outside.L_meta_17906.main
