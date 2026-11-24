import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3497_aux

open PEqualNP.CircuitLowerBounds

-- A clause family is satisfied by the input string x when every clause has a true variable.
def sem {n : ℕ} (x : List Bool) (S : Finset (Finset (Fin n))) : Prop :=
  ∀ c ∈ S, ∃ i ∈ c, x.getD (↑i) false = true

-- The clause family of a gate from the families of its two inputs.
def comb {n : ℕ} (op : GateOp) (S T : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  if op.eval [false, true] = true then S.biUnion (fun c => T.image (fun d => c ∪ d)) else S ∪ T

def stepR {n : ℕ} (R : List (Finset (Finset (Fin n)))) (g : Gate) :
    List (Finset (Finset (Fin n))) :=
  R ++ [match g.inputs with
        | [a, b] => comb g.op (R.getD a {∅}) (R.getD b {∅})
        | _ => {∅}]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def initR (n : ℕ) : List (Finset (Finset (Fin n))) :=
  (List.finRange n).map fun i => {{i}}

def Good (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b]

theorem length_stepR {n : ℕ} (R : List (Finset (Finset (Fin n)))) (g : Gate) :
    (stepR R g).length = R.length + 1 := by
  simp [stepR]

theorem length_foldl_stepR {n : ℕ} (gs : List Gate) (R : List (Finset (Finset (Fin n)))) :
    (gs.foldl stepR R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, length_stepR]
    simp
    omega

theorem getD_append_left' {α : Type} (l : List α) (y : α) (j : ℕ) (d : α) (h : j < l.length) :
    (l ++ [y]).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_last {α : Type} (l : List α) (y : α) (d : α) :
    (l ++ [y]).getD l.length d = y := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_right {α : Type} (l : List α) (y : α) (j : ℕ) (d : α)
    (h : l.length < j) : (l ++ [y]).getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  simp

theorem getD_foldl_stepR {n : ℕ} (gs : List Gate) (R : List (Finset (Finset (Fin n)))) (j : ℕ)
    (d : Finset (Finset (Fin n))) (h : j < R.length) :
    (gs.foldl stepR R).getD j d = R.getD j d := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepR R g) (by rw [length_stepR]; omega)]
    exact getD_append_left' R _ j d h

theorem sem_union {n : ℕ} (x : List Bool) (S T : Finset (Finset (Fin n))) :
    sem x (S ∪ T) ↔ sem x S ∧ sem x T := by
  unfold sem
  constructor
  · intro h
    exact ⟨fun c hc => h c (Finset.mem_union_left _ hc),
      fun c hc => h c (Finset.mem_union_right _ hc)⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem sem_prod {n : ℕ} (x : List Bool) (S T : Finset (Finset (Fin n))) :
    sem x (S.biUnion (fun c => T.image (fun d => c ∪ d))) ↔ sem x S ∨ sem x T := by
  unfold sem
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    obtain ⟨⟨c, hc, hc'⟩, ⟨d, hd, hd'⟩⟩ := hn
    obtain ⟨i, hi, hix⟩ := h (c ∪ d) (Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩)
    rcases Finset.mem_union.mp hi with hi | hi
    · exact absurd hix (by simpa using hc' i hi)
    · exact absurd hix (by simpa using hd' i hi)
  · intro h e he
    obtain ⟨c, hc, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    rcases h with h | h
    · obtain ⟨i, hi, hix⟩ := h c hc
      exact ⟨i, Finset.mem_union_left _ hi, hix⟩
    · obtain ⟨i, hi, hix⟩ := h d hd
      exact ⟨i, Finset.mem_union_right _ hi, hix⟩

theorem not_sem_empty {n : ℕ} (x : List Bool) : ¬ sem x ({∅} : Finset (Finset (Fin n))) := by
  intro h
  obtain ⟨i, hi, _⟩ := h ∅ (Finset.mem_singleton_self _)
  simp at hi

theorem sem_single {n : ℕ} (x : List Bool) (i : Fin n) :
    sem x ({{i}} : Finset (Finset (Fin n))) ↔ x.getD (↑i) false = true := by
  unfold sem
  simp

theorem sem_comb {n : ℕ} (x : List Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (S T : Finset (Finset (Fin n))) (u v : Bool) (hu : u = true ↔ sem x S)
    (hv : v = true ↔ sem x T) :
    op.eval [u, v] = true ↔ sem x (comb op S T) := by
  rcases hop with rfl | rfl
  · simp only [comb, GateOp.eval]
    simp [sem_union, hu, hv]
  · simp only [comb, GateOp.eval]
    simp [sem_prod, hu, hv]

def Inv {n : ℕ} (x : List Bool) (W : List Bool) (R : List (Finset (Finset (Fin n)))) : Prop :=
  W.length = R.length ∧ ∀ w : ℕ, W.getD w false = true ↔ sem x (R.getD w {∅})

theorem inv_step {n : ℕ} (x : List Bool) (W : List Bool) (R : List (Finset (Finset (Fin n))))
    (g : Gate) (hg : Good g) (h : Inv x W R) : Inv x (stepW W g) (stepR R g) := by
  obtain ⟨hl, hw⟩ := h
  obtain ⟨hop, a, b, hab⟩ := hg
  refine ⟨by simp [stepW, stepR, hl], fun w => ?_⟩
  rcases lt_trichotomy w W.length with hlt | heq | hgt
  · rw [stepW, stepR, getD_append_left' W _ w _ hlt, getD_append_left' R _ w _ (hl ▸ hlt)]
    exact hw w
  · subst heq
    rw [stepW, stepR, getD_append_last, hl, getD_append_last, hab]
    simp only [List.map_cons, List.map_nil]
    exact sem_comb x g.op hop _ _ _ _ (hw a) (hw b)
  · rw [stepW, stepR, getD_append_right W _ w _ hgt, getD_append_right R _ w _ (hl ▸ hgt)]
    simp only [Bool.false_eq_true, false_iff]
    exact not_sem_empty x

theorem inv_foldl {n : ℕ} (x : List Bool) (gs : List Gate) (hgs : ∀ g ∈ gs, Good g)
    (W : List Bool) (R : List (Finset (Finset (Fin n)))) (h : Inv x W R) :
    Inv x (gs.foldl stepW W) (gs.foldl stepR R) := by
  induction gs generalizing W R with
  | nil => simpa using h
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (inv_step x W R g (hgs g (List.mem_cons_self ..)) h)

theorem length_initR (n : ℕ) : (initR n).length = n := by
  simp [initR]

theorem getD_initR (n : ℕ) (i : Fin n) : (initR n).getD (↑i) {∅} = {{i}} := by
  simp [initR, List.getD_eq_getElem?_getD]

theorem inv_init (n : ℕ) (x : List Bool) (hx : x.length = n) : Inv x x (initR n) := by
  refine ⟨by rw [hx, length_initR], fun w => ?_⟩
  by_cases hw : w < n
  · have := getD_initR n ⟨w, hw⟩
    simp only at this
    rw [this, sem_single]
  · have h1 : x.getD w false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp
    have h2 : (initR n).getD w {∅} = {∅} := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_initR]; omega)]
      simp
    rw [h1, h2]
    simp only [Bool.false_eq_true, false_iff]
    exact not_sem_empty x

end PEqualNP.Outside.L_meta_3497_aux

open PEqualNP.Outside.L_meta_3497_aux

theorem PEqualNP.Outside.L_meta_3497 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9) else x5 x8 ∪ x5 x9) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∀ x9 ∈ x5 x8, ∃ x11 ∈ x9, x6.getD (↑x11) Bool.false = Bool.true := by
  intro n C hmono hin
  have hgood : ∀ g ∈ C.gates, Good g := by
    intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨a, b, hab, -, -⟩ := hin k g hk
    have hop := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, a, b, hab⟩
  refine ⟨fun w => (C.gates.foldl stepR (initR n)).getD w {∅}, ?_, ?_, ?_⟩
  · intro i
    simp only
    rw [getD_foldl_stepR _ _ _ _ (by rw [length_initR]; exact i.isLt), getD_initR]
  · intro k hk
    have hk' : k < C.gates.length := hk
    obtain ⟨a, b, hab, hlt, hb⟩ := hin k C.gates[k] (List.getElem?_eq_getElem hk')
    refine ⟨a, b, hab, hlt, hb, ?_⟩
    have hsplit : C.gates = C.gates.take k ++ (C.gates[k] :: C.gates.drop (k + 1)) := by
      rw [← List.drop_eq_getElem_cons hk', List.take_append_drop]
    set Ri := (C.gates.take k).foldl stepR (initR n) with hRi
    have hlen : Ri.length = n + k := by
      rw [hRi, length_foldl_stepR, length_initR, List.length_take]
      omega
    have hfin : C.gates.foldl stepR (initR n)
        = (C.gates.drop (k + 1)).foldl stepR (stepR Ri C.gates[k]) := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hstab : ∀ j, j < n + k →
        (C.gates.foldl stepR (initR n)).getD j {∅} = Ri.getD j {∅} := by
      intro j hj
      rw [hfin, getD_foldl_stepR _ _ _ _ (by rw [length_stepR]; omega), stepR,
        getD_append_left' _ _ _ _ (by omega)]
    simp only
    rw [hstab a (by omega), hstab b hb, hfin,
      getD_foldl_stepR _ _ _ _ (by rw [length_stepR]; omega), stepR, ← hlen, getD_append_last,
      hab]
    rfl
  · intro x hx w
    have h := (inv_foldl x C.gates hgood x (initR n) (inv_init n x hx)).2 w
    exact h
