import PEqualNP.Defs

-- Inlined below (the checker allows only Mathlib and PEqualNP.Defs as imports): the helpers
-- Shannon, RepReads and RepInduced from PEqualNP.MetaComplexity.Helpers, and the proof of L-meta-7626.
-- The double crown on 2k + 2k vertices: keep the even rows and columns (RepInduced.induced saves
-- 2k gates), relabel them onto the crown on k + k vertices (same size), and use L-meta-7626.

/-!
# Shannon expansion as a straight-line program

Helper for `L-meta-001`. The construction is made at an arbitrary wire offset: the function
reads the first `k` wires of a wire list of length `m`, and the new gates are appended after
wire `m - 1`. So two subcircuits are put one after the other without renumbering any gate.
-/

namespace PEqualNP.Outside.L_meta_17365

namespace Helpers

open PEqualNP.CircuitLowerBounds

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
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

/-- The four gates that close one Shannon expansion step, appended to the wires `v`: with
`a = v[k]`, `p = v[o0]`, `q = v[o1]` they produce `(¬a ∧ p) ∨ (a ∧ q)` on the last wire. -/
theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end Helpers


/-!
# A circuit representing a bipartite graph must read its vertices

A circuit of `k` gates of fan-in at most two depends on at most `k + 1` inputs (`needed`), and a
circuit of AND and OR gates is monotone (`mono`). In a representing circuit, a left vertex with an
edge into a column that is not full, and a right vertex with an edge from a row that is not full,
must be read. So their number is at most the size plus one (`reads_le`).
-/

namespace RepReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17365.Helpers
open PEqualNP.Represents

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- The wires that decide a set `N` of wires: at most one more per gate. -/
theorem needed (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ N : Finset ℕ, ∃ N' : Finset ℕ, N'.card ≤ N.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ N', x.getD i false = y.getD i false) →
        ∀ i ∈ N, (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => intro N; exact ⟨N, by simp, fun x y _ _ h => h⟩
  | append_singleton gs g ih =>
    intro N
    have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (List.mem_append_left _ h)
    have hg2 : g.inputs.length ≤ 2 := hg g (by simp)
    by_cases hm : n + gs.length ∈ N
    · obtain ⟨N', hc, hN⟩ := ih hgs (N.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · have h1 := Finset.card_union_le (N.erase (n + gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem hm
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, hm⟩
        rw [List.length_append, List.length_singleton]
        omega
      · have H := hN x y hx hy h
        rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        split_ifs with hk
        · congr 1
          apply List.map_congr_left
          intro a ha
          exact H a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · exact H i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hk, hi⟩))
    · obtain ⟨N', hc, hN⟩ := ih hgs N
      refine ⟨N', ?_, fun x y hx hy h i hi => ?_⟩
      · rw [List.length_append, List.length_singleton]; omega
      · rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom,
          length_wiresFrom, hx, hy]
        have hk : i ≠ n + gs.length := fun h => hm (h ▸ hi)
        rw [if_neg hk, if_neg hk]
        exact hN x y hx hy h i hi

/-- AND and OR gates are monotone. -/
theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom, length_wiresFrom,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

/-- The input with the vertices of `P` on (wires). -/
def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

/-- The left vertices that must be read. -/
def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v, A u v = true ∧ ∃ u', A u' v = false

/-- The right vertices that must be read. -/
def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u, A u v = true ∧ ∃ w, A u w = false

/-- The vertices that must be read number at most the size plus one. -/
theorem reads_le {n m s : ℕ} (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    (forcedL A).card + (forcedR A).card ≤ s + 1 := by
  obtain ⟨C, hC, hs, hR⟩ := h
  obtain ⟨S, hcard, hS⟩ := needed (n + m) C.gates (fun g hg => (hC g hg).2) {C.output}
  have hop : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
    fun g hg => (hC g hg).1
  have hev : ∀ P, C.eval (inp (n + m) P) =
      (wiresFrom C.gates (inp (n + m) P)).getD C.output false := fun P => rfl
  -- turning off an unread wire changes nothing
  have hoff : ∀ P w, w ∉ S → C.eval (inp (n + m) P) = C.eval (inp (n + m) (P.erase w)) := by
    intro P w hw
    rw [hev, hev]
    refine hS _ _ (by simp [inp]) (by simp [inp]) (fun i hi => ?_) _ (Finset.mem_singleton_self _)
    rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
    have : i ≠ w := fun e => hw (e ▸ hi)
    tauto
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → C.eval (inp (n + m) P) = true →
      C.eval (inp (n + m) Q) = true := by
    intro P Q hPQ
    rw [hev, hev]
    refine mono C.gates hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m), C.eval (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v
    rw [← oneEach_eq]; exact hR u v
  have hL : ∀ u ∈ forcedL A, (u : ℕ) ∈ S := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, n + (v : ℕ) ∈ S := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hsub : (forcedL A).image (fun u : Fin n => (u : ℕ)) ∪
      (forcedR A).image (fun v : Fin m => n + (v : ℕ)) ⊆ S := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi; exact hL u hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi; exact hRr v hv
  have hdis : Disjoint ((forcedL A).image (fun u : Fin n => (u : ℕ)))
      ((forcedR A).image (fun v : Fin m => n + (v : ℕ))) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
    have := u.2
    omega
  have hcc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at hcc
  rw [Finset.card_singleton] at hcard
  have : C.gates.length ≤ s := hs
  omega

end RepReads


/-!
# Switching lines off: the excess of an induced subgraph is at most that of the graph

Switch a set `Z` of inputs off. A gate reading a wire that is off disappears (an AND is off, an OR
is its other wire). Every live wire that is off is read by a live gate that disappears, so at least
as many gates disappear as there are live inputs in `Z`, unless the output is off (`kill`).
-/

namespace RepInduced

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17365.Helpers
open PEqualNP.Represents RepReads

open scoped Classical

section kill
variable (N : ℕ) (Z : Finset ℕ) (gs : List Gate)

def gat (j : ℕ) : Gate := gs.getD j ⟨.and, []⟩

/-- The new gates and the new names of the old wires (`none`: the wire is off). -/
noncomputable def st : ℕ → List Gate × (ℕ → Option ℕ)
  | 0 => ([], fun w => if w < N ∧ w ∉ Z then some w else none)
  | j + 1 =>
    let p := st j
    let g := gat gs j
    if ∃ i ∈ g.inputs, p.2 i = none then
      (p.1, Function.update p.2 (N + j)
        (if g.op = GateOp.and then none else (g.inputs.filterMap p.2).head?))
    else (p.1 ++ [⟨g.op, g.inputs.map fun i => (p.2 i).getD 0⟩],
      Function.update p.2 (N + j) (some (N + p.1.length)))

/-- Gate `j` reads an off wire. -/
def Dead (j : ℕ) : Prop := ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i = none

theorem st_dead {j : ℕ} (h : Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1, Function.update (st N Z gs j).2 (N + j)
      (if (gat gs j).op = GateOp.and then none
        else ((gat gs j).inputs.filterMap (st N Z gs j).2).head?)) := by
  rw [st]; exact if_pos h

theorem st_keep {j : ℕ} (h : ¬ Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1 ++ [⟨(gat gs j).op, (gat gs j).inputs.map fun i =>
      ((st N Z gs j).2 i).getD 0⟩],
      Function.update (st N Z gs j).2 (N + j) (some (N + (st N Z gs j).1.length))) := by
  rw [st]; exact if_neg h

theorem st_ne {j w : ℕ} (h : w ≠ N + j) : (st N Z gs (j + 1)).2 w = (st N Z gs j).2 w := by
  by_cases hd : Dead N Z gs j
  · rw [st_dead N Z gs hd]; exact Function.update_of_ne h _ _
  · rw [st_keep N Z gs hd]; exact Function.update_of_ne h _ _

theorem st_late (j : ℕ) : ∀ w, N + j ≤ w → (st N Z gs j).2 w = none := by
  induction j with
  | zero => intro w h; simp [st, show ¬ w < N by omega]
  | succ j ih => intro w h; rw [st_ne N Z gs (by omega)]; exact ih w (by omega)

theorem st_final {j k w : ℕ} (hjk : j ≤ k) (h : w < N + j) :
    (st N Z gs k).2 w = (st N Z gs j).2 w := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [st_ne N Z gs (by omega)]; exact ih

/-- An operand off at the end is off when read. -/
theorem st_off {j k w : ℕ} (hjk : j ≤ k) (h : (st N Z gs k).2 w = none) :
    (st N Z gs j).2 w = none := by
  by_cases hw : w < N + j
  · rw [← st_final N Z gs hjk hw]; exact h
  · exact st_late N Z gs j w (by omega)

theorem st_len (j : ℕ) : (st N Z gs j).1.length +
    ((Finset.range j).filter fun i => Dead N Z gs i).card = j := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hd : Dead N Z gs j
    · rw [if_pos hd, Finset.card_insert_of_notMem (by simp), st_dead N Z gs hd]
      show (st N Z gs j).1.length + _ = _
      omega
    · rw [if_neg hd, st_keep N Z gs hd]
      simp only [List.length_append, List.length_singleton]
      omega

theorem st_lt (j : ℕ) : ∀ w a, (st N Z gs j).2 w = some a → a < N + (st N Z gs j).1.length := by
  induction j with
  | zero =>
    intro w a h
    simp only [st] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq] at h
      simp [st]; omega
  | succ j ih =>
    intro w a h
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd] at h ⊢
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self] at h
        split_ifs at h
        have hm := List.mem_of_mem_head? (Option.mem_def.2 h)
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 hm
        exact ih i a hi
      · simp only [Function.update_of_ne hw] at h
        exact ih w a h
    · rw [st_keep N Z gs hd] at h ⊢
      simp only [List.length_append, List.length_singleton]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, Option.some.injEq] at h
        omega
      · simp only [Function.update_of_ne hw] at h
        have := ih w a h
        omega

variable (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)

include hgs in
theorem gat_ok (j : ℕ) : ((gat gs j).op = GateOp.and ∨ (gat gs j).op = GateOp.or) ∧
    (gat gs j).inputs.length ≤ 2 := by
  by_cases h : j < gs.length
  · have := hgs (gat gs j) (by rw [gat, List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    simpa using this
  · rw [gat, List.getD_eq_default _ _ (by omega)]; simp

include hgs in
theorem st_ok (j : ℕ) : ∀ g ∈ (st N Z gs j).1,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]; exact ih
    · rw [st_keep N Z gs hd]
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ih g hg
      · rw [List.mem_singleton.1 hg]
        have := gat_ok gs hgs j
        simpa using this

theorem take_succ (j : ℕ) (hj : j < gs.length) : gs.take (j + 1) = gs.take j ++ [gat gs j] := by
  rw [List.take_succ_eq_append_getElem hj, gat, List.getD_eq_getElem _ _ hj]

include hgs in
/-- The new wires carry the old values with `Z` off. -/
theorem st_val (P : Finset ℕ) (j : ℕ) (hj : j ≤ gs.length) : ∀ w,
    ((st N Z gs j).2 w = none → (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false = false) ∧
    ∀ a, (st N Z gs j).2 w = some a → (wiresFrom (st N Z gs j).1 (inp N P)).getD a false =
      (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false := by
  induction j with
  | zero =>
    intro w
    simp only [st, List.take_zero, wiresFrom, List.foldl_nil, inp_getD, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hw
      simp only [decide_eq_false_iff_not]; tauto
    · intro a h
      split_ifs at h with hw
      simp only [Option.some.injEq] at h
      subst h
      rw [decide_eq_decide]; tauto
  | succ j ih =>
    have H := ih (by omega)
    have hl1 : (wiresFrom (gs.take j) (inp N (P \ Z))).length = N + j := by
      rw [length_wiresFrom, List.length_take]; simp [inp]; omega
    have hl2 : (wiresFrom (st N Z gs j).1 (inp N P)).length = N + (st N Z gs j).1.length := by
      rw [length_wiresFrom]; simp [inp]
    have hok := gat_ok gs hgs j
    rw [take_succ gs j (by omega), wiresFrom_snoc]
    set V := wiresFrom (gs.take j) (inp N (P \ Z)) with hV
    intro w
    rw [getD_snoc, hl1]
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        obtain ⟨i, hi, hoff⟩ := hd
        have hi0 := (H i).1 hoff
        rcases hok.1 with hop | hop
        · simp only [hop, if_true]
          refine ⟨fun _ => ?_, fun a h => by simp at h⟩
          rw [← Bool.not_eq_true, GateOp.eval, List.all_eq_true]
          intro h
          have := h _ (List.mem_map.2 ⟨i, hi, rfl⟩)
          rw [hi0] at this; simp at this
        · simp only [hop, reduceCtorEq, if_false]
          -- the OR of its wires that are not off
          have hlen := hok.2
          constructor
          · intro h
            rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
            rw [← Bool.not_eq_true, GateOp.eval, List.any_eq_true]
            rintro ⟨b, hb, hb1⟩
            obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hb
            have := (H i').1 (h i' hi')
            rw [this] at hb1; simp at hb1
          · intro a h
            obtain ⟨i', hi', hia⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? (Option.mem_def.2 h))
            rw [(H i').2 a hia, GateOp.eval]
            have hne : i ≠ i' := by rintro rfl; rw [hoff] at hia; simp at hia
            -- the gate reads exactly `i` and `i'`
            have hall : ∀ b ∈ (gat gs j).inputs, b = i ∨ b = i' := by
              intro b hb
              by_contra hn
              push Not at hn
              have h3 : ({i, i', b} : Finset ℕ) ⊆ (gat gs j).inputs.toFinset := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                rcases hc with rfl | rfl | rfl <;> simpa
              have := Finset.card_le_card h3
              rw [Finset.card_eq_three.2 ⟨i, i', b, hne, fun e => hn.1 e.symm, fun e => hn.2 e.symm,
                rfl⟩] at this
              have := List.toFinset_card_le (gat gs j).inputs
              omega
            apply Bool.eq_iff_iff.2
            rw [List.any_eq_true]
            constructor
            · intro hv; exact ⟨_, List.mem_map.2 ⟨i', hi', rfl⟩, hv⟩
            · rintro ⟨b, hb, hb1⟩
              obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
              rcases hall c hc with rfl | rfl
              · rw [hi0] at hb1; simp at hb1
              · exact hb1
      · simp only [Function.update_of_ne hw, if_neg hw]
        exact H w
    · rw [st_keep N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        simp only [Option.some.injEq] at h
        subst h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_pos rfl]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        obtain ⟨b, hb⟩ : ∃ b, (st N Z gs j).2 i = some b := by
          cases h : (st N Z gs j).2 i with
          | none => exact absurd ⟨i, hi, h⟩ hd
          | some b => exact ⟨b, rfl⟩
        simp only [Function.comp_apply, hb, Option.getD_some]
        exact (H i).2 b hb
      · simp only [Function.update_of_ne hw, if_neg hw]
        refine ⟨(H w).1, fun a h => ?_⟩
        have hlt := st_lt N Z gs j w a h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_neg (by omega)]
        exact (H w).2 a h

/-- Wires the output `o` depends on by reading. -/
def Live (o : ℕ) : ℕ → Prop :=
  Relation.ReflTransGen (fun g w => ∃ j < gs.length, g = N + j ∧ w ∈ (gat gs j).inputs) o

theorem live_dep (o : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (h : ∀ i, Live N gs o i → x.getD i false = y.getD i false) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ w, Live N gs o w →
      (wiresFrom (gs.take j) x).getD w false = (wiresFrom (gs.take j) y).getD w false := by
  induction j with
  | zero => intro w hw; simpa [wiresFrom] using h w hw
  | succ j ih =>
    intro w hw
    have H := ih (by omega)
    rw [take_succ gs j (by omega), wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc,
      length_wiresFrom, length_wiresFrom, hx, hy, List.length_take, Nat.min_eq_left (by omega)]
    split_ifs with hwj
    · congr 1
      apply List.map_congr_left
      intro a ha
      exact H a (hw.tail ⟨j, by omega, hwj, ha⟩)
    · exact H w hw

include hgs in
/-- At least as many gates disappear as there are live inputs off. -/
theorem kill_count (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (ho : (st N Z gs gs.length).2 o ≠ none) :
    Z0.card ≤ ((Finset.range gs.length).filter fun i => Dead N Z gs i).card := by
  set k := gs.length with hk
  let K := (Finset.range k).filter fun j => Dead N Z gs j ∧ Live N gs o (N + j)
  let Y := (Finset.range k).filter fun j => (st N Z gs k).2 (N + j) = none ∧ Live N gs o (N + j)
  let Q : Finset (Σ _ : ℕ, ℕ) := K.sigma fun j =>
    (gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none
  let W := Z0 ∪ Y.image fun j => N + j
  have hYK : Y ⊆ K := by
    intro j hj
    obtain ⟨hjk, hz, hl⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨hjk, ?_, hl⟩
    by_contra hd
    have hjk' := Finset.mem_range.1 hjk
    rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_keep N Z gs hd] at hz
    simp at hz
  have hW : W ⊆ Q.image fun q => q.2 := by
    intro w hw
    have hw2 : (st N Z gs k).2 w = none ∧ Live N gs o w := by
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨h1, h2, h3⟩ := hZ0 w h
        refine ⟨?_, h3⟩
        rw [st_final N Z gs (Nat.zero_le k) (by omega)]
        simp [st, h2]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hj).2
    have hne : w ≠ o := fun e => ho (e ▸ hw2.1)
    rcases Relation.ReflTransGen.cases_tail hw2.2 with e | ⟨g, hg, j, hj, rfl, hi⟩
    · exact absurd e hne
    · have hoff := st_off N Z gs (show j ≤ k by omega) hw2.1
      refine Finset.mem_image.2 ⟨⟨j, w⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ⟨w, hi, hoff⟩, hg⟩
      · exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hi, hoff⟩
  have hWc : W.card = Z0.card + Y.card := by
    have : Disjoint Z0 (Y.image fun j => N + j) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 h2
      have := (hZ0 _ h1).1
      omega
    show (Z0 ∪ Y.image fun j => N + j).card = _
    rw [Finset.card_union_of_disjoint this,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hQ : Q.card ≤ K.card + Y.card := by
    show (K.sigma _).card ≤ _
    rw [Finset.card_sigma]
    calc ∑ j ∈ K, ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card
        ≤ ∑ j ∈ K, (1 + if j ∈ Y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hjk, hd, hl⟩ := Finset.mem_filter.1 hj
          have hjk' := Finset.mem_range.1 hjk
          have hok := gat_ok gs hgs j
          have hc := List.toFinset_card_le (gat gs j).inputs
          have hf := Finset.card_filter_le (gat gs j).inputs.toFinset
            fun i => (st N Z gs j).2 i = none
          split_ifs with hY
          · omega
          · -- the gate is not off, so one of its wires is not off
            have hsome : (st N Z gs k).2 (N + j) ≠ none := fun e =>
              hY (Finset.mem_filter.2 ⟨hjk, e, hl⟩)
            rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_dead N Z gs hd] at hsome
            simp only [Function.update_self] at hsome
            obtain ⟨i, hi, hia⟩ : ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i ≠ none := by
              by_contra hn
              push Not at hn
              apply hsome
              split_ifs
              · rfl
              · rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]; exact hn
            have hlt : ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card <
                (gat gs j).inputs.toFinset.card :=
              Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, List.mem_toFinset.2 hi, hia⟩)
            omega
      _ = K.card + Y.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_ite_mem,
            Finset.inter_eq_right.2 hYK, Finset.sum_const, smul_eq_mul, mul_one]
  have h1 := Finset.card_le_card hW
  have h2 := Finset.card_image_le (s := Q) (f := fun q => q.2)
  have h3 : K.card ≤ ((Finset.range k).filter fun i => Dead N Z gs i).card :=
    Finset.card_le_card fun j hj => by
      obtain ⟨a, b, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨a, b⟩
  omega

include hgs in
/-- Switching off inputs: the circuit that is left. -/
theorem kill (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (P0 : Finset ℕ) (hP0 : Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + Z0.card ≤ gs.length ∧
      ∀ P, D.eval (inp N P) = Circuit.eval ⟨gs, o⟩ (inp N (P \ Z)) := by
  have hv : ∀ P, _ := fun P => st_val N Z gs hgs P gs.length le_rfl o
  simp only [List.take_length] at hv
  have ho : (st N Z gs gs.length).2 o ≠ none := by
    intro e
    have := (hv P0).1 e
    rw [show Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) =
      (wiresFrom gs (inp N (P0 \ Z))).getD o false from rfl, this] at hP0
    exact Bool.noConfusion hP0
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 ho
  refine ⟨⟨(st N Z gs gs.length).1, a⟩, st_ok N Z gs hgs _, ?_, fun P => (hv P).2 a ha⟩
  have h1 := kill_count N Z gs hgs o Z0 hZ0 ho
  have h2 := st_len N Z gs gs.length
  show (st N Z gs gs.length).1.length + Z0.card ≤ gs.length
  omega

end kill

/-- The excess of an induced subgraph without full lines is at most that of the graph. -/
theorem induced : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) := by
  intro n m s A R K hR hK ⟨u0, hu0, v0, hv0, h0⟩ ⟨⟨gs, o⟩, hC, hs, hrep⟩
  let BL := R.filter fun a => ∃ b ∈ K, A a b = true
  let BR := K.filter fun b => ∃ a ∈ R, A a b = true
  let Z : Finset ℕ := (Finset.univ.filter fun a : Fin n => a ∉ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (Finset.univ.filter fun b : Fin m => b ∉ BR).image (fun b : Fin m => n + (b : ℕ))
  have hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hC
  have hop : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC g hg).1
  have hZl : ∀ a : Fin n, (a : ℕ) ∈ Z ↔ a ∉ BL := by
    intro a
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, hx, e⟩ | ⟨x, _, e⟩)
      · rwa [← Fin.ext e]
      · have := a.2; omega
    · exact fun h => Or.inl ⟨a, h, rfl⟩
  have hZr : ∀ b : Fin m, n + (b : ℕ) ∈ Z ↔ b ∉ BR := by
    intro b
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, _, e⟩ | ⟨x, hx, e⟩)
      · have := x.2; omega
      · rwa [← Fin.ext (show (x : ℕ) = b by omega)]
    · exact fun h => Or.inr ⟨b, h, rfl⟩
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = true →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) Q) = true := by
    intro P Q hPQ
    refine mono gs hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq]; exact hrep u v
  have hoff : ∀ P w, ¬ Live (n + m) gs o w →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = Circuit.eval ⟨gs, o⟩ (inp (n + m) (P.erase w)) := by
    intro P w hw
    have := live_dep (n + m) gs o (inp (n + m) P) (inp (n + m) (P.erase w)) (by simp [inp])
      (by simp [inp]) (fun i hi => by
        rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
        have : i ≠ w := fun e => hw (e ▸ hi)
        tauto) gs.length le_rfl o Relation.ReflTransGen.refl
    rw [List.take_length] at this
    exact this
  have hL : ∀ u ∈ forcedL A, Live (n + m) gs o (u : ℕ) := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, Live (n + m) gs o (n + (v : ℕ)) := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hBL : BL ⊆ forcedL A := by
    intro a ha
    obtain ⟨_, b, hb, hab⟩ := Finset.mem_filter.1 ha
    obtain ⟨a', _, ha'⟩ := hK b hb
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab, a', ha'⟩
  have hBR : BR ⊆ forcedR A := by
    intro b hb
    obtain ⟨_, a, ha, hab⟩ := Finset.mem_filter.1 hb
    obtain ⟨b', _, hb'⟩ := hR a ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, a, hab, b', hb'⟩
  let Z0 : Finset ℕ := (forcedL A \ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))
  have hZ0 : ∀ i ∈ Z0, i < n + m ∧ i ∈ Z ∧ Live (n + m) gs o i := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ha
      exact ⟨by have := a.2; omega, (hZl a).2 h2, hL a h1⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hb
      exact ⟨by have := b.2; omega, (hZr b).2 h2, hRr b h1⟩
  have hZ0c : Z0.card = (forcedL A \ BL).card + (forcedR A \ BR).card := by
    have hdis : Disjoint ((forcedL A \ BL).image (fun a : Fin n => (a : ℕ)))
        ((forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
      have := u.2
      omega
    show (_ ∪ _ : Finset ℕ).card = _
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]
  -- the value with `Z` off
  have hval : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) (({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z)) =
        (A u v && decide (u ∈ R) && decide (v ∈ K)) := by
    intro u v
    by_cases hu : u ∈ BL
    · by_cases hv : v ∈ BR
      · have hu' := (Finset.mem_filter.1 hu).1
        have hv' := (Finset.mem_filter.1 hv).1
        rw [show ({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z = {(u : ℕ), n + (v : ℕ)} from by
          rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
          intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi
          · rw [hZl]; exact fun h => h hu
          · rw [Finset.mem_singleton.1 hi, hZr]; exact fun h => h hv, hA]
        simp [hu', hv']
      · -- column off: the row alone
        have hu' := (Finset.mem_filter.1 hu).1
        obtain ⟨b, hb, hab⟩ := hR u hu'
        have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
          by_contra hne
          simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
          exact hv (Finset.mem_filter.2 ⟨hne.2, u, hne.1.2, hne.1.1⟩)
        rw [e1]
        by_contra hne
        rw [Bool.not_eq_false] at hne
        have := hmono _ {(u : ℕ), n + (b : ℕ)} (fun i hi => by
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
          rcases Finset.mem_insert.1 h1 with rfl | h1
          · simp
          · rw [Finset.mem_singleton.1 h1] at h2; exact absurd ((hZr v).2 hv) h2) hne
        rw [hA, hab] at this
        exact Bool.noConfusion this
    · -- row off: at most the column alone
      have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
        by_contra hne
        simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
        exact hu (Finset.mem_filter.2 ⟨hne.1.2, v, hne.2, hne.1.1⟩)
      rw [e1]
      by_contra hne
      rw [Bool.not_eq_false] at hne
      obtain ⟨b, hb, a, hab⟩ : ∃ b : Fin m, (n + (v : ℕ) ∉ Z → b = v) ∧ ∃ a : Fin n, A a b = false := by
        by_cases hv : v ∈ BR
        · obtain ⟨a, _, ha⟩ := hK v (Finset.mem_filter.1 hv).1
          exact ⟨v, fun _ => rfl, a, ha⟩
        · obtain ⟨a, _, ha⟩ := hK v0 hv0
          exact ⟨v0, fun h => absurd ((hZr v).2 hv) h, a, ha⟩
      have := hmono _ {(a : ℕ), n + (b : ℕ)} (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
        rcases Finset.mem_insert.1 h1 with rfl | h1
        · exact absurd ((hZl u).2 hu) h2
        · rw [Finset.mem_singleton.1 h1] at h2 ⊢
          rw [hb h2]; simp) hne
      rw [hA, hab] at this
      exact Bool.noConfusion this
  obtain ⟨D, hD1, hD2, hD3⟩ := kill (n + m) Z gs hgs o Z0 hZ0 {(u0 : ℕ), n + (v0 : ℕ)}
    (by rw [hval]; simp [h0, hu0, hv0])
  refine ⟨D.size, ⟨D, hD1, le_rfl, fun u v => ?_⟩, ?_⟩
  · rw [oneEach_eq, hD3, hval]
  · have c1 := Finset.card_sdiff_add_card_eq_card hBL
    have c2 := Finset.card_sdiff_add_card_eq_card hBR
    have hs' : gs.length ≤ s := hs
    have e1 : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
      ∃ a' : Fin n, A a' b = false)).card = (forcedL A).card := by unfold forcedL; congr
    have e2 : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
      ∃ b' : Fin m, A a b' = false)).card = (forcedR A).card := by unfold forcedR; congr
    have e3 : (R.filter (fun a => ∃ b ∈ K, A a b = true)).card = BL.card := by congr
    have e4 : (K.filter (fun b => ∃ a ∈ R, A a b = true)).card = BR.card := by congr
    rw [e1, e2]
    try rw [e3, e4]
    omega

end RepInduced


namespace C7626

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi

theorem det : ∀ (gs : List Gate) (N : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ S : Finset ℕ, ∃ S' : Finset ℕ, S'.card ≤ S.card + gs.length ∧
    ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ S', x.getD w false = y.getD w false) → ∀ w ∈ S, (run gs x).getD w false = (run gs y).getD w false := by
  intro gs
  induction gs with
  | nil => intro N _ S; exact ⟨S, by simp, fun x y _ _ h => h⟩
  | cons g gs ih =>
    intro N hg S
    obtain ⟨T, hT, hd⟩ := ih (N + 1) (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) S
    have step : ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ T, w ≠ N → x.getD w false = y.getD w false) →
        (N ∈ T → ∀ w ∈ g.inputs, x.getD w false = y.getD w false) → ∀ w ∈ S, (run (g :: gs) x).getD w false = (run (g :: gs) y).getD w false := by
      intro x y hx hy h1 h2
      refine hd (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [hx]) (by simp [hy]) ?_
      intro w hw
      rcases Nat.lt_trichotomy w N with h | h | h
      · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
        exact h1 w hw (by omega)
      · subst h
        have e1 : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
          rw [← hx]; exact getD_at _ _
        have e2 : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => y.getD i false) := by
          rw [← hy]; exact getD_at _ _
        rw [e1, e2, List.map_congr_left fun i hi => h2 hw i hi]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    by_cases hN : N ∈ T
    · refine ⟨T.erase N ∪ g.inputs.toFinset, ?_, fun x y hx hy h => step x y hx hy (fun w hw hne => h w ?_) (fun _ w hw => h w ?_)⟩
      · have e1 := Finset.card_union_le (T.erase N) g.inputs.toFinset
        have e2 := Finset.card_erase_add_one hN
        have e3 := List.toFinset_card_le g.inputs
        have e4 := hg g List.mem_cons_self
        simp only [List.length_cons]
        omega
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 hw)
    · refine ⟨T, by simp only [List.length_cons]; omega, fun x y hx hy h => step x y hx hy (fun w hw _ => h w hw) (fun h' => absurd h' hN)⟩




def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl


theorem engine3 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      -- extend with a value for wire `n + k`
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm


def rd (A B : ℕ → ℕ) (k w : ℕ) : Prop := A k = w ∨ B k = w

def pt (n u v : ℕ) : ℕ → Bool := fun k => decide (k = u ∨ k = n + v)

def Tg (n m : ℕ) (A B : ℕ → ℕ) (An : ℕ → Bool) (i j : ℕ) : Prop :=
  i < n ∧ j < m ∧ An j = false ∧ ((A j = i ∧ B j = n + i) ∨ (A j = n + i ∧ B j = i)) ∧
    ∀ k < m, (rd A B k i ∨ rd A B k (n + i)) → k = j

def Kill (n : ℕ) (V : (ℕ → Bool) → ℕ → Bool) (i j : ℕ) : Prop :=
  (∃ b, ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) (n + n + j) = b) ∨
    ∃ w < n + n + j, ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) (n + n + j) = V (pt n u v) w

theorem core (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (A B : ℕ → ℕ) (An : ℕ → Bool) (V : (ℕ → Bool) → ℕ → Bool) (o : ℕ)
    (hA : ∀ j < m, A j < n + n + j) (hB : ∀ j < m, B j < n + n + j) (hAB : ∀ j < m, A j ≠ B j)
    (v0 : ∀ P k, k < n + n → V P k = P k)
    (v1 : ∀ P j, j < m → V P (n + n + j) = if An j = true then V P (A j) && V P (B j) else V P (A j) || V P (B j))
    (ho : o < n + n + m)
    (hf : ∀ u v, u < n → v < n → V (pt n u v) o = decide (u ≠ v))
    (irr : ∀ j < m, ∀ w < n + n + j, ¬∀ u v, u < n → v < n → V (pt n u v) (n + n + j) = V (pt n u v) w) :
    ∃ i < n, ∃ a b c, a < m ∧ b < m ∧ c < m ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Kill n V i a ∧ Kill n V i b ∧ Kill n V i c := by
  classical
  -- monotonicity
  have mono : ∀ (P Q : ℕ → Bool), (∀ k, P k = true → Q k = true) → ∀ w < n + n + m, V P w = true → V Q w = true := by
    intro P Q hPQ w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw h
      by_cases hwn : w < n + n
      · rw [v0 _ _ hwn] at h ⊢; exact hPQ _ h
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
        have hj : j < m := by omega
        have a1 := hA j hj
        have b1 := hB j hj
        rw [v1 _ _ hj] at h ⊢
        split_ifs at h ⊢ with hAn
        · rw [Bool.and_eq_true] at h ⊢
          exact ⟨ih _ a1 (by omega) h.1, ih _ b1 (by omega) h.2⟩
        · rw [Bool.or_eq_true] at h ⊢
          exact h.imp (ih _ a1 (by omega)) (ih _ b1 (by omega))
  -- replacement
  have rep : ∀ (Hd : ℕ → Prop) (P Q : ℕ → Bool), (∀ k < n + n, ¬Hd k → P k = Q k) →
      (∀ j < m, ¬Hd (n + n + j) → (Hd (A j) ∨ Hd (B j)) → V P (n + n + j) = V Q (n + n + j)) →
      ∀ w < n + n + m, ¬Hd w → V P w = V Q w := by
    intro Hd P Q h1 h2 w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hH
      by_cases hwn : w < n + n
      · rw [v0 _ _ hwn, v0 _ _ hwn]; exact h1 _ hwn hH
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
        have hj : j < m := by omega
        have a1 := hA j hj
        have b1 := hB j hj
        by_cases hr : Hd (A j) ∨ Hd (B j)
        · exact h2 j hj hH hr
        · rw [not_or] at hr
          rw [v1 _ _ hj, v1 _ _ hj, ih _ a1 (by omega) hr.1, ih _ b1 (by omega) hr.2]
  -- single inputs give false
  have row1 : ∀ u < n, V (fun k => decide (k = u)) o = false := by
    intro u hu
    by_contra h
    have h1 := mono (fun k => decide (k = u)) (pt n u u) (by
      intro k hk
      have : k = u := by simpa using hk
      simp [pt, this]) o ho (by simpa using h)
    rw [hf u u hu hu] at h1
    simp at h1
  have col1 : ∀ v < n, V (fun k => decide (k = n + v)) o = false := by
    intro v hv
    by_contra h
    have h1 := mono (fun k => decide (k = n + v)) (pt n v v) (by
      intro k hk
      have : k = n + v := by simpa using hk
      simp [pt, this]) o ho (by simpa using h)
    rw [hf v v hv hv] at h1
    simp at h1
  -- the output is a gate, and it is false at equal points
  obtain ⟨jo, hjo, rfl⟩ : ∃ jo, jo < m ∧ o = n + n + jo := by
    by_cases h : o < n + n
    · exfalso
      by_cases h2 : o < n
      · have := hf o o h2 h2
        rw [v0 _ _ h] at this
        simp [pt] at this
      · have := hf (o - n) (o - n) (by omega) (by omega)
        rw [v0 _ _ h] at this
        have e : o = n + (o - n) := by omega
        simp only [pt, ← e] at this
        simp at this
    · exact ⟨o - (n + n), by omega, by omega⟩
  -- zero wires on the smaller domain
  let Z : ℕ → ℕ → Prop := fun i w => ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) w = false
  have zr : ∀ i < n, Z i i := by
    intro i hi u v hu hv hui hvi
    rw [v0 _ _ (by omega)]
    simp only [pt, decide_eq_false_iff_not, not_or]
    omega
  have zc : ∀ i < n, Z i (n + i) := by
    intro i hi u v hu hv hui hvi
    rw [v0 _ _ (by omega)]
    simp only [pt, decide_eq_false_iff_not, not_or]
    omega
  have kr : ∀ i j w, j < m → rd A B j w → Z i w → Kill n V i j := by
    intro i j w hj hr hz
    have a1 := hA j hj
    have b1 := hB j hj
    by_cases hAn : An j = true
    · left
      refine ⟨false, fun u v hu hv hui hvi => ?_⟩
      rw [v1 _ _ hj, if_pos hAn]
      rcases hr with rfl | rfl
      · rw [hz u v hu hv hui hvi]; rfl
      · rw [hz u v hu hv hui hvi, Bool.and_false]
    · right
      rcases hr with rfl | rfl
      · refine ⟨B j, b1, fun u v hu hv hui hvi => ?_⟩
        rw [v1 _ _ hj, if_neg hAn, hz u v hu hv hui hvi, Bool.false_or]
      · refine ⟨A j, a1, fun u v hu hv hui hvi => ?_⟩
        rw [v1 _ _ hj, if_neg hAn, hz u v hu hv hui hvi, Bool.or_false]
  have zor : ∀ i j, j < m → An j = false → Z i (A j) → Z i (B j) → Z i (n + n + j) := by
    intro i j hj hAn h1 h2 u v hu hv hui hvi
    rw [v1 _ _ hj, if_neg (by simp [hAn]), h1 u v hu hv hui hvi, h2 u v hu hv hui hvi]; rfl
  -- a pair gate OR(r_i, c_i) is true at (i, i), so it is not the output
  have orii : ∀ i j, i < n → j < m → An j = false → (rd A B j i ∨ rd A B j (n + i)) → V (pt n i i) (n + n + j) = true := by
    intro i j hi hj hAn hr
    have p1 : V (pt n i i) i = true := by rw [v0 _ _ (by omega)]; simp [pt]
    have p2 : V (pt n i i) (n + i) = true := by rw [v0 _ _ (by omega)]; simp [pt]
    rw [v1 _ _ hj, if_neg (by simp [hAn]), Bool.or_eq_true]
    rcases hr with (h | h) | (h | h)
    · exact Or.inl (by rw [h]; exact p1)
    · exact Or.inr (by rw [h]; exact p1)
    · exact Or.inl (by rw [h]; exact p2)
    · exact Or.inr (by rw [h]; exact p2)
  have notout : ∀ i j, i < n → j < m → An j = false → (rd A B j i ∨ rd A B j (n + i)) → j ≠ jo := by
    rintro i j hi hj hAn hr rfl
    have h1 := orii i j hi hj hAn hr
    rw [hf i i hi hi] at h1
    simp at h1
  -- each input is seen with its partner off
  have seesC : ∀ i < n, ∃ P Q : ℕ → Bool, (∀ k, k ≠ n + i → P k = Q k) ∧ P i = false ∧ Q i = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo) := by
    intro i hi
    obtain ⟨u, hu, hui⟩ : ∃ u < n, u ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨pt n u i, fun k => decide (k = u), ?_, ?_, ?_, ?_⟩
    · intro k hk; simp [pt, hk]
    · simp only [pt, decide_eq_false_iff_not, not_or]; omega
    · simp only [decide_eq_false_iff_not]; omega
    · rw [hf u i hu hi, row1 u hu]; simp [hui]
  have seesR : ∀ i < n, ∃ P Q : ℕ → Bool, (∀ k, k ≠ i → P k = Q k) ∧ P (n + i) = false ∧ Q (n + i) = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo) := by
    intro i hi
    obtain ⟨v, hv, hvi⟩ : ∃ v < n, v ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨pt n i v, fun k => decide (k = n + v), ?_, ?_, ?_, ?_⟩
    · intro k hk; simp [pt, hk]
    · simp only [pt, decide_eq_false_iff_not, not_or]; omega
    · simp only [decide_eq_false_iff_not]; omega
    · rw [hf i v hi hv, col1 v hv]; simp [Ne.symm hvi]
  -- two readers of a raw input of the first gate outside the pair gates
  have raw : ∀ (i x y h g : ℕ), i < n → ((x = i ∧ y = n + i) ∨ (x = n + i ∧ y = i)) → h < m → g < m → h ≠ g → rd A B h x → rd A B g x →
      (∀ a, rd A B h a → a < n + n ∨ ∃ i' j, a = n + n + j ∧ Tg n m A B An i' j) →
      (∃ P Q : ℕ → Bool, (∀ k, k ≠ y → P k = Q k) ∧ P x = false ∧ Q x = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo)) →
      ∃ i < n, ∃ a b c, a < m ∧ b < m ∧ c < m ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Kill n V i a ∧ Kill n V i b ∧ Kill n V i c := by
    intro i x y h g hi hxy hh hg hhg rhx rgx hat hsee
    have zx : Z i x := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact zr _ hi; exact zc _ hi]
    have zy : Z i y := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> [exact zc _ hi; exact zr _ hi]
    have hxN : x < n + n := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hyN : y < n + n := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hne : x ≠ y := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    by_cases h3 : ∃ k < m, (rd A B k x ∨ rd A B k y) ∧ k ≠ h ∧ k ≠ g
    · obtain ⟨k, hk, hr, k1, k2⟩ := h3
      refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, Ne.symm k1, Ne.symm k2, kr i h x hh rhx zx, kr i g x hg rgx zx, ?_⟩
      exact hr.elim (fun r => kr i k x hk r zx) (fun r => kr i k y hk r zy)
    push Not at h3
    have only : ∀ k < m, (rd A B k x ∨ rd A B k y) → k = h ∨ k = g := by
      intro k hk hr
      by_contra hc
      rw [not_or] at hc
      exact hc.2 (h3 k hk hr hc.1)
    obtain ⟨P, Q, pq, px, qx, hdiff⟩ := hsee
    -- operands of a gate reading both
    have both : ∀ k < m, rd A B k x → rd A B k y → (A k = x ∧ B k = y) ∨ (A k = y ∧ B k = x) := by
      intro k _ h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.symm.trans h2) hne
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact absurd (h1.symm.trans h2) hne
    have andv : ∀ k < m, An k = true → rd A B k x → ∀ W : ℕ → Bool, W x = false → V W (n + n + k) = false := by
      intro k hk hAn hr W hW
      rw [v1 _ _ hk, if_pos hAn]
      rcases hr with hr | hr
      · rw [hr, v0 _ _ hxN, hW]; rfl
      · rw [hr, v0 _ _ hxN, hW, Bool.and_false]
    have orxy : ∀ k < m, An k = false → (rd A B k x ∧ rd A B k y) → k ≠ jo := by
      intro k hk hAn hr
      refine notout i k hi hk hAn ?_
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hr.1
      · exact Or.inl hr.2
    have zgate : ∀ k < m, An k = false → rd A B k x → rd A B k y → Z i (n + n + k) := by
      intro k hk hAn r1 r2
      rcases both k hk r1 r2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact zor i k hk hAn (by rw [e1]; exact zx) (by rw [e2]; exact zy)
      · exact zor i k hk hAn (by rw [e1]; exact zy) (by rw [e2]; exact zx)
    by_cases rhy : rd A B h y
    · by_cases rgy : rd A B g y
      · -- both read both
        have hops : An h ≠ An g := by
          intro e
          have same : ∀ W, V W (n + n + h) = V W (n + n + g) := by
            intro W
            rw [v1 _ _ hh, v1 _ _ hg, e]
            rcases both h hh rhx rhy with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases both g hg rgx rgy with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> rw [e1, e2, e3, e4] <;>
              cases V W x <;> cases V W y <;> cases An g <;> rfl
          rcases Nat.lt_or_gt_of_ne hhg with hlt | hlt
          · exact irr g hg (n + n + h) (by omega) fun u v _ _ => (same _).symm
          · exact irr h hh (n + n + g) (by omega) fun u v _ _ => same _
        obtain ⟨p, q, hp, hq, hpq, pAn, qAn, rpx, rpy, rqx, rqy, hset⟩ : ∃ p q, p < m ∧ q < m ∧ p ≠ q ∧ An p = false ∧ An q = true ∧ rd A B p x ∧ rd A B p y ∧ rd A B q x ∧ rd A B q y ∧ (∀ k, k = h ∨ k = g → k = p ∨ k = q) := by
          cases e1 : An h with
          | false =>
            have e2 : An g = true := by
              cases e2 : An g with
              | true => rfl
              | false => exact absurd (e1.trans e2.symm) hops
            exact ⟨h, g, hh, hg, hhg, e1, e2, rhx, rhy, rgx, rgy, fun k hk => hk⟩
          | true =>
            have e2 : An g = false := by
              cases e2 : An g with
              | false => rfl
              | true => exact absurd (e1.trans e2.symm) hops
            exact ⟨g, h, hg, hh, Ne.symm hhg, e2, e1, rgx, rgy, rhx, rhy, fun k hk => hk.symm⟩
        have hrd : ∃ k < m, rd A B k (n + n + p) := by
          by_contra hno
          push Not at hno
          refine hdiff (rep (fun w => w = y ∨ w = n + n + p) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
          · intro j hj hjH hr
            have hjp : j ≠ p := fun e => hjH (Or.inr (by rw [e]))
            have : rd A B j y := by
              rcases hr with (e | e) | (e | e)
              · exact Or.inl e
              · exact absurd (Or.inl e) (hno j hj)
              · exact Or.inr e
              · exact absurd (Or.inr e) (hno j hj)
            have hjq : j = q := by
              rcases hset j (only j hj (Or.inr this)) with e | e
              · exact absurd e hjp
              · exact e
            subst hjq
            rw [andv j hj qAn rqx P px, andv j hj qAn rqx Q qx]
          · rintro (e | e)
            · omega
            · exact orxy p hp pAn ⟨rpx, rpy⟩ (by omega)
        obtain ⟨k, hk, hr⟩ := hrd
        have ar : ∀ c < m, rd A B c x → rd A B c y → ¬rd A B c (n + n + p) := by
          intro c hc c1 c2 c3
          rcases both c hc c1 c2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases c3 with e3 | e3 <;> omega
        refine ⟨i, hi, p, q, k, hp, hq, hk, hpq, ?_, ?_, kr i p x hp rpx zx, kr i q x hq rqx zx, kr i k _ hk hr (zgate p hp pAn rpx rpy)⟩
        · rintro rfl; exact ar _ hp rpx rpy hr
        · rintro rfl; exact ar _ hq rqx rqy hr
      · -- y is read only by h
        have oy : ∀ k < m, rd A B k y → k = h := by
          intro k hk r
          rcases only k hk (Or.inr r) with e | e
          · exact e
          · subst e; exact absurd r rgy
        cases hAn : An h with
        | true =>
          exfalso
          refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
          intro j hj _ hr
          have : j = h := oy j hj hr
          subst this
          rw [andv j hj hAn rhx P px, andv j hj hAn rhx Q qx]
        | false =>
          have hrd : ∃ k < m, rd A B k (n + n + h) := by
            by_contra hno
            push Not at hno
            refine hdiff (rep (fun w => w = y ∨ w = n + n + h) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
            · intro j hj hjH hr
              exfalso
              have : rd A B j y := by
                rcases hr with (e | e) | (e | e)
                · exact Or.inl e
                · exact absurd (Or.inl e) (hno j hj)
                · exact Or.inr e
                · exact absurd (Or.inr e) (hno j hj)
              exact hjH (Or.inr (by rw [oy j hj this]))
            · rintro (e | e)
              · omega
              · exact orxy h hh hAn ⟨rhx, rhy⟩ (by omega)
          by_cases hother : ∃ k < m, rd A B k (n + n + h) ∧ k ≠ g
          · obtain ⟨k, hk, hr, hkg⟩ := hother
            refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, ?_, Ne.symm hkg, kr i h x hh rhx zx, kr i g x hg rgx zx, kr i k _ hk hr (zgate h hh hAn rhx rhy)⟩
            rintro rfl
            have a1 := hA h hh
            have b1 := hB h hh
            rcases hr with e | e <;> omega
          · exfalso
            push Not at hother
            obtain ⟨k, hk, hr⟩ := hrd
            have hkg := hother k hk hr
            subst hkg
            have hhk : h < k := by
              have a1 := hA k hk
              have b1 := hB k hk
              rcases hr with e | e <;> omega
            have ops : (A k = x ∧ B k = n + n + h) ∨ (A k = n + n + h ∧ B k = x) := by
              rcases rgx with e1 | e1 <;> rcases hr with e2 | e2
              · omega
              · exact Or.inl ⟨e1, e2⟩
              · exact Or.inr ⟨e2, e1⟩
              · omega
            have hhv : ∀ W, V W (n + n + h) = (V W x || V W y) := by
              intro W
              rw [v1 _ _ hh, if_neg (by simp [hAn])]
              rcases both h hh rhx rhy with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · rw [e1, e2]
              · rw [e1, e2, Bool.or_comm]
            cases hAk : An k with
            | true =>
              refine irr k hk x (by omega) fun u v _ _ => ?_
              rw [v1 _ _ hk, if_pos hAk]
              rcases ops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hhv] <;> cases V (pt n u v) x <;> cases V (pt n u v) y <;> rfl
            | false =>
              refine irr k hk (n + n + h) (by omega) fun u v _ _ => ?_
              rw [v1 _ _ hk, if_neg (by simp [hAk])]
              rcases ops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hhv] <;> cases V (pt n u v) x <;> cases V (pt n u v) y <;> rfl
    · -- y is not read by h
      have oy : ∀ k < m, rd A B k y → k = g := by
        intro k hk r
        rcases only k hk (Or.inr r) with e | e
        · subst e; exact absurd r rhy
        · exact e
      have rgy : rd A B g y := by
        by_contra hno
        refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
        intro j hj _ hr
        exfalso
        have := oy j hj hr
        subst this
        exact hno hr
      cases hAn : An g with
      | true =>
        exfalso
        refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
        intro j hj _ hr
        have : j = g := oy j hj hr
        subst this
        rw [andv j hj hAn rgx P px, andv j hj hAn rgx Q qx]
      | false =>
        have hrd : ∃ k < m, rd A B k (n + n + g) := by
          by_contra hno
          push Not at hno
          refine hdiff (rep (fun w => w = y ∨ w = n + n + g) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
          · intro j hj hjH hr
            exfalso
            have : rd A B j y := by
              rcases hr with (e | e) | (e | e)
              · exact Or.inl e
              · exact absurd (Or.inl e) (hno j hj)
              · exact Or.inr e
              · exact absurd (Or.inr e) (hno j hj)
            exact hjH (Or.inr (by rw [oy j hj this]))
          · rintro (e | e)
            · omega
            · exact orxy g hg hAn ⟨rgx, rgy⟩ (by omega)
        obtain ⟨k, hk, hr⟩ := hrd
        refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, ?_, ?_, kr i h x hh rhx zx, kr i g x hg rgx zx, kr i k _ hk hr (zgate g hg hAn rgx rgy)⟩
        · rintro rfl
          rcases hat _ hr with e | ⟨i', j, e, hT⟩
          · omega
          · have hjg : j = g := by omega
            subst hjg
            obtain ⟨_, _, _, hops, hex⟩ := hT
            have hx' : x = i' ∨ x = n + i' := by
              rcases hops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases rgx with e3 | e3 <;> omega
            have : h = j := by
              refine hex h hh ?_
              rcases hx' with rfl | rfl
              · exact Or.inl rhx
              · exact Or.inr rhx
            exact hhg this
        · rintro rfl
          have a1 := hA g hg
          have b1 := hB g hg
          rcases hr with e | e <;> omega
  by_contra hG
  have hexT : ∃ j, j < m ∧ ¬∃ i, Tg n m A B An i j := by
    refine ⟨jo, hjo, ?_⟩
    rintro ⟨i, hi, hj, hAn, hops, _⟩
    refine notout i jo hi hj hAn ?_ rfl
    rcases hops with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
  obtain ⟨hh, hhT⟩ := Nat.find_spec hexT
  have hmin : ∀ j, j < Nat.find hexT → ∃ i, Tg n m A B An i j := by
    intro j hj
    by_contra hc
    exact Nat.find_min hexT hj ⟨by omega, hc⟩
  generalize Nat.find hexT = h at hh hhT hmin
  clear hexT
  have hAh := hA h hh
  have hBh := hB h hh
  have hat : ∀ a, rd A B h a → a < n + n ∨ ∃ i' j, a = n + n + j ∧ Tg n m A B An i' j := by
    intro a ha
    by_cases h1 : a < n + n
    · exact Or.inl h1
    · right
      have : a < n + n + h := by rcases ha with e | e <;> omega
      obtain ⟨i, hi⟩ := hmin (a - (n + n)) (by omega)
      exact ⟨i, a - (n + n), by omega, hi⟩
  have Tne : ∀ i j, Tg n m A B An i j → j ≠ h := by
    rintro i j hT rfl
    exact hhT ⟨i, hT⟩
  have Tno : ∀ i j, Tg n m A B An i j → j ≠ jo := by
    rintro i j ⟨hi, hj, hAn, hops, _⟩
    refine notout i j hi hj hAn ?_
    rcases hops with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
  have VT : ∀ i j, Tg n m A B An i j → ∀ W : ℕ → Bool, V W (n + n + j) = (W i || W (n + i)) := by
    rintro i j ⟨hi, hj, hAn, hops, _⟩ W
    rw [v1 _ _ hj, if_neg (by simp [hAn])]
    rcases hops with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2, v0 _ _ (by omega), v0 _ _ (by omega)]
    · rw [e1, e2, v0 _ _ (by omega), v0 _ _ (by omega), Bool.or_comm]
  have sole : ∀ a, rd A B h a → ∀ k < m, rd A B k a → k = h := by
    intro a ha k hk hr
    by_contra hkh
    apply hG
    rcases hat a ha with h1 | ⟨i, j, rfl, hT⟩
    · by_cases h2 : a < n
      · exact raw a a (n + a) h k h2 (Or.inl ⟨rfl, rfl⟩) hh hk (Ne.symm hkh) ha hr hat (seesC a h2)
      · have e : a = n + (a - n) := by omega
        exact raw (a - n) a (a - n) h k (by omega) (Or.inr ⟨e, rfl⟩) hh hk (Ne.symm hkh) ha hr hat (by
          have := seesR (a - n) (by omega)
          rwa [← e] at this)
    · obtain ⟨hi, hj, hAn, hops, hex⟩ := hT
      have zA : Z i (A j) := by rcases hops with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> [exact zr i hi; exact zc i hi]
      have zB : Z i (B j) := by rcases hops with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> [exact zc i hi; exact zr i hi]
      have zj := zor i j hj hAn zA zB
      refine ⟨i, hi, j, h, k, hj, hh, hk, Tne i j ⟨hi, hj, hAn, hops, hex⟩, ?_, Ne.symm hkh, kr i j _ hj (Or.inl rfl) zA, kr i h _ hh ha zj, kr i k _ hk hr zj⟩
      rintro rfl
      have a1 := hA j hj
      have b1 := hB j hj
      rcases hr with e | e <;> omega
  have fin : ∀ (Hd : ℕ → Prop) (P Q : ℕ → Bool), (∀ k < n + n, ¬Hd k → P k = Q k) →
      (∀ j < m, ¬Hd (n + n + j) → (Hd (A j) ∨ Hd (B j)) → j = h) → V P (n + n + h) = V Q (n + n + h) → ¬Hd (n + n + jo) →
      V P (n + n + jo) = V Q (n + n + jo) := by
    intro Hd P Q h1 h2 h3 h4
    refine rep Hd P Q h1 (fun j hj hjH hr => ?_) _ (by omega) h4
    rw [h2 j hj hjH hr]; exact h3
  have hVh : ∀ W, V W (n + n + h) = if An h = true then V W (A h) && V W (B h) else V W (A h) || V W (B h) := fun W => v1 W h hh
  have ra : rd A B h (A h) := Or.inl rfl
  have rb : rd A B h (B h) := Or.inr rfl
  have sa := sole _ ra
  have sb := sole _ rb
  have hab := hAB h hh
  have atom : ∀ a, rd A B h a → (∃ i < n, a = i) ∨ (∃ i < n, a = n + i) ∨ ∃ i j, a = n + n + j ∧ Tg n m A B An i j := by
    intro a ha
    rcases hat a ha with h1 | h1
    · by_cases h2 : a < n
      · exact Or.inl ⟨a, h2, rfl⟩
      · exact Or.inr (Or.inl ⟨a - n, by omega, by omega⟩)
    · exact Or.inr (Or.inr h1)
  have third : ∀ i j, i < n → j < n → ∃ v < n, v ≠ i ∧ v ≠ j := by
    intro i j _ _
    by_cases h0 : 0 ≠ i ∧ 0 ≠ j
    · exact ⟨0, by omega, h0.1, h0.2⟩
    · by_cases h1 : 1 ≠ i ∧ 1 ≠ j
      · exact ⟨1, by omega, h1.1, h1.2⟩
      · refine ⟨2, by omega, ?_, ?_⟩ <;> omega
  rcases atom _ ra with ⟨i, hi, ea⟩ | ⟨i, hi, ea⟩ | ⟨i, ja, ea, hTa⟩
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · by_cases hij : i = j
      · subst hij
        exact hab (ea.trans eb.symm)
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = j ∨ (i) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = i ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = false := (hf i i hi hi).trans (by simp)
            have f2 : V Q (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + i) = decide (k = j ∨ k = n + i)
            have hH2 : ¬(k = i ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ n + n + jo = j := hH
            omega
    · by_cases hij : i = j
      · subst hij
        cases hAn : An h with
        | false =>
          refine hhT ⟨i, hi, hh, hAn, Or.inl ⟨ea, eb⟩, fun k hk hr => ?_⟩
          rcases hr with hr | hr
          · exact sa k hk (by rw [ea]; exact hr)
          · exact sb k hk (by rw [eb]; exact hr)
        | true =>
          obtain ⟨P, Q, pq, px, qx, hdiff⟩ := seesC i hi
          refine hdiff (fin (fun w => w = n + i) P Q (fun k _ hk => pq k hk) ?_ ?_ (by omega))
          · intro k hk _ hr
            exact sb k hk (by rw [eb]; exact hr)
          · rw [hVh, hVh, if_pos hAn, if_pos hAn, ea, eb, v0 _ i (by omega), v0 _ i (by omega), px, qx]
            simp
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬(k = i ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ n + n + jo = n + j := hH
            omega
    · have hj := hTb.1
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i jb hTb (xb h hh (Or.inl (by rw [← ea]; exact ra))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have ua : V Q (i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬(k = i ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | (rfl | rfl | rfl)
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno j jb hTb
            omega
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · by_cases hij : i = j
      · subst hij
        cases hAn : An h with
        | false =>
          refine hhT ⟨i, hi, hh, hAn, Or.inr ⟨ea, eb⟩, fun k hk hr => ?_⟩
          rcases hr with hr | hr
          · exact sb k hk (by rw [eb]; exact hr)
          · exact sa k hk (by rw [ea]; exact hr)
        | true =>
          obtain ⟨P, Q, pq, px, qx, hdiff⟩ := seesC i hi
          refine hdiff (fin (fun w => w = n + i) P Q (fun k _ hk => pq k hk) ?_ ?_ (by omega))
          · intro k hk _ hr
            exact sa k hk (by rw [ea]; exact hr)
          · rw [hVh, hVh, if_pos hAn, if_pos hAn, ea, eb, v0 _ i (by omega), v0 _ i (by omega), px, qx]
            simp
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = v ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = true := by rw [v0 _ _ (by omega)]; exact (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = j) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = n + i ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = j)
            have hH2 : ¬(k = n + i ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ n + n + jo = j := hH
            omega
    · by_cases hij : i = j
      · subst hij
        exact hab (ea.trans eb.symm)
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = v ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = i ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = n + i ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = false := (hf i i hi hi).trans (by simp)
            have f2 : V Q (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + i) = decide (k = i ∨ k = n + j)
            have hH2 : ¬(k = n + i ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ n + n + jo = n + j := hH
            omega
    · have hj := hTb.1
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i jb hTb (xb h hh (Or.inr (by rw [← ea]; exact ra))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = v ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = v ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = n + i)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + j) = false from by show decide ((n + j) = j ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = true from by show decide ((n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = n + i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = n + i)
            have hH2 : ¬(k = n + i ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | (rfl | rfl | rfl)
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno j jb hTb
            omega
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · have hi := hTa.1
      have xa := hTa.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i ja hTa (xa h hh (Or.inl (by rw [← eb]; exact rb))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = false from by show decide ((i) = j ∨ (i) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have vb : V P (j) = true := by rw [v0 _ _ (by omega)]; exact (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = j) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = j)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | rfl
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ n + n + jo = j := hH
            have := Tno i ja hTa
            omega
    · have hi := hTa.1
      have xa := hTa.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i ja hTa (xa h hh (Or.inr (by rw [← eb]; exact rb))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = n + j)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = true from by show decide ((n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = n + j)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | rfl
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ n + n + jo = n + j := hH
            have := Tno i ja hTa
            omega
    · have hi := hTa.1
      have hj := hTb.1
      have xa := hTa.2.2.2.2
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exfalso
        have e1 : ja = jb := by
          refine xb ja hTa.2.1 ?_
          rcases hTa.2.2.2.1 with ⟨e, _⟩ | ⟨_, e⟩
          · exact Or.inl (Or.inl e)
          · exact Or.inl (Or.inr e)
        exact hab (by rw [ea, eb, e1])
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have ua : V Q (n + n + ja) = true := by rw [VT i ja hTa Q, (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno i ja hTa
            have := Tno j jb hTb
            omega

def onl (n : ℕ) (Q : ℕ → Bool) : List Bool := (List.range (n + n)).map Q

theorem onl_len (n : ℕ) (Q : ℕ → Bool) : (onl n Q).length = n + n := by simp [onl]

theorem onl_get (n : ℕ) (Q : ℕ → Bool) (k : ℕ) (hk : k < n + n) : (onl n Q).getD k false = Q k := by
  simp [onl, List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem one_onl (n : ℕ) (u v : Fin n) : PEqualNP.Represents.oneEach u v = onl n (pt n u v) := by
  refine List.ext_getElem (by simp [PEqualNP.Represents.oneEach, onl]) fun k h1 h2 => ?_
  have hk : k < n + n := by simpa [onl] using h2
  simp only [PEqualNP.Represents.oneEach, onl, List.getElem_map, List.getElem_range, pt]
  by_cases h : k < n
  · rw [List.getElem_append_left (by simpa using h)]
    simp only [List.getElem_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := v.isLt
    omega
  · rw [List.getElem_append_right (by simpa using h)]
    simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := u.isLt
    omega

theorem vmono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (Q R : ℕ → Bool) (h : ∀ k, Q k = true → R k = true) (w : ℕ)
    (hw : (run C.gates (onl n Q)).getD w false = true) : (run C.gates (onl n R)).getD w false = true := by
  refine mono C.gates (onl n Q) (onl n R) (by simp [onl]) ?_ (fun g hg => by simpa using (hC g hg).1) w hw
  intro i hi
  by_cases hin : i < n + n
  · rw [onl_get n _ i hin] at hi ⊢; exact h i hi
  · rw [List.getD_eq_default _ _ (by rw [onl_len]; omega)] at hi; cases hi

/-- two indices: every input is seen, so at least three gates -/
theorem two (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hf : ∀ u v : Fin 2, C.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) : 3 ≤ C.size := by
  classical
  obtain ⟨S, hS, hdet⟩ := det C.gates 4 (fun g hg => (hC g hg).2) {C.output}
  have hv : ∀ u v : Fin 2, (run C.gates (onl 2 (pt 2 u v))).getD C.output false = decide (u ≠ v) := by
    intro u v
    rw [← one_onl]; exact hf u v
  have row : ∀ u : Fin 2, (run C.gates (onl 2 fun k => decide (k = (u : ℕ)))).getD C.output false = false := by
    intro u
    by_contra h
    have h1 := vmono 2 C hC (fun k => decide (k = (u : ℕ))) (pt 2 u u) (by
      intro k hk
      have : k = (u : ℕ) := by simpa using hk
      simp [pt, this]) C.output (by simpa using h)
    rw [hv u u] at h1
    simp at h1
  have col : ∀ u : Fin 2, (run C.gates (onl 2 fun k => decide (k = 2 + (u : ℕ)))).getD C.output false = false := by
    intro u
    by_contra h
    have h1 := vmono 2 C hC (fun k => decide (k = 2 + (u : ℕ))) (pt 2 u u) (by
      intro k hk
      have : k = 2 + (u : ℕ) := by simpa using hk
      simp [pt, this]) C.output (by simpa using h)
    rw [hv u u] at h1
    simp at h1
  have see : ∀ (w : ℕ) (Q R : ℕ → Bool), (∀ k, k ≠ w → Q k = R k) → (run C.gates (onl 2 Q)).getD C.output false ≠ (run C.gates (onl 2 R)).getD C.output false → w ∈ S := by
    intro w Q R hQR hne
    by_contra hw
    refine hne (hdet (onl 2 Q) (onl 2 R) (by simp [onl]) (by simp [onl]) (fun i hi => ?_) C.output (by simp))
    by_cases hin : i < 2 + 2
    · rw [onl_get 2 _ i hin, onl_get 2 _ i hin]
      exact hQR i fun e => hw (e ▸ hi)
    · rw [List.getD_eq_default _ _ (by rw [onl_len]; omega), List.getD_eq_default _ _ (by rw [onl_len]; omega)]
  have h0 : 0 ∈ S := see 0 (pt 2 (0 : Fin 2) (1 : Fin 2)) (fun k => decide (k = 2 + ((1 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, col]; decide)
  have h1 : 1 ∈ S := see 1 (pt 2 (1 : Fin 2) (0 : Fin 2)) (fun k => decide (k = 2 + ((0 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, col]; decide)
  have h2 : 2 ∈ S := see 2 (pt 2 (1 : Fin 2) (0 : Fin 2)) (fun k => decide (k = ((1 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, row]; decide)
  have h3 : 3 ∈ S := see 3 (pt 2 (0 : Fin 2) (1 : Fin 2)) (fun k => decide (k = ((0 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, row]; decide)
  have hsub : ({0, 1, 2, 3} : Finset ℕ) ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  have e : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide
  rw [e] at hc
  rw [Finset.card_singleton] at hS
  have : C.size = C.gates.length := rfl
  omega

theorem main : ∀ (n : ℕ) (C : Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∀ u v : Fin n, C.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) → 3 * n ≤ C.size + 3 := by
  intro n
  induction n with
  | zero => intro C _ _; omega
  | succ k ih =>
    intro C0 hC0 hf0
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · omega
      · have := two C0 hC0 hf0
        omega
    classical
    -- a least circuit
    have hex : ∃ s, ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = s ∧ ∀ u v : Fin (k + 1), C.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v) := ⟨_, C0, hC0, rfl, hf0⟩
    obtain ⟨C, hC, hCs, hf⟩ := Nat.find_spec hex
    have hmin : ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D → (∀ u v : Fin (k + 1), D.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) → C.size ≤ D.size := by
      intro D h1 h2
      rw [hCs]
      exact Nat.find_min' hex ⟨D, h1, rfl, h2⟩
    have hle : C.size ≤ C0.size := hmin C0 hC0 hf0
    suffices hs : 3 * (k + 1) ≤ C.size + 3 by omega
    set n := k + 1 with hn
    have hn3 : 3 ≤ n := by omega
    let V : (ℕ → Bool) → ℕ → Bool := fun Q w => (run C.gates (onl n Q)).getD w false
    have hm : C.size = C.gates.length := rfl
    have hV : ∀ u v : Fin n, ∀ w, V (pt n u v) w = (run C.gates (PEqualNP.Represents.oneEach u v)).getD w false := by
      intro u v w
      rw [one_onl]
    have hlen1 : ∀ u v : Fin n, (PEqualNP.Represents.oneEach u v).length = n + n := fun u v => by
      simp only [PEqualNP.Represents.oneEach, List.length_append, List.length_ofFn]
    have nonc : ¬∃ b, ∀ p : Fin n × Fin n, C.eval (PEqualNP.Represents.oneEach p.1 p.2) = b := by
      rintro ⟨b, hb⟩
      have h1 := hb (⟨0, by omega⟩, ⟨0, by omega⟩)
      have h2 := hb (⟨0, by omega⟩, ⟨1, by omega⟩)
      rw [hf] at h1 h2
      rw [← h1] at h2
      simp at h2
    -- no gate is constant or a copy on the points
    have irr0 : ∀ j < C.gates.length, ¬((∃ b, ∀ p : Fin n × Fin n, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + n + j) false = b) ∨
        ∃ w < n + n + j, ∀ p : Fin n × Fin n, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + n + j) false = (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD w false) := by
      intro j hj hbad
      obtain ⟨D, d1, d2, d3⟩ := engine3 (n + n) (n + n) C (fun p : Fin n × Fin n => PEqualNP.Represents.oneEach p.1 p.2) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
        (fun p => hlen1 _ _) (fun p => hlen1 _ _) {j} hC (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩) nonc (by
          intro i hi
          have : i = j := by simpa using hi
          subst this
          exact ⟨hj, hbad⟩)
      have := hmin D d1 fun u v => (d3 (u, v)).trans (hf u v)
      rw [Finset.card_singleton] at d2
      omega
    have shape : ∀ j, j < C.gates.length → ∃ a b : ℕ, ∃ c : Bool, a < n + n + j ∧ b < n + n + j ∧ a ≠ b ∧
        ∀ Q, V Q (n + n + j) = if c = true then V Q a && V Q b else V Q a || V Q b := by
      intro j hj
      obtain ⟨hop, hl⟩ := hC _ (List.getElem_mem hj)
      have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hop
      have rg0 : ∀ l : List Bool, l.length = n + n → (run C.gates l).getD (n + n + j) false = C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < n + n + j then (run C.gates l).getD i false else false) := by
        intro l hll
        have := run_gate C.gates l j hj
        rw [hll] at this
        exact this
      have bad := irr0 j hj
      generalize hin : C.gates[j].inputs = l at hl rg0
      rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact absurd (Or.inl ⟨C.gates[j].op.eval [], fun p => by rw [rg0 _ (hlen1 _ _)]; rfl⟩) bad
      · by_cases ha : a < n + n + j
        · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
          rw [rg0 _ (hlen1 _ _)]
          rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
        · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
          rw [rg0 _ (hlen1 _ _)]
          rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
      · by_cases ha : a < n + n + j
        · by_cases hb : b < n + n + j
          · by_cases hab : a = b
            · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
              rw [rg0 _ (hlen1 _ _), ← hab]
              rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
            · rcases hop' with e | e
              · refine ⟨a, b, true, ha, hb, hab, fun Q => ?_⟩
                have := rg0 (onl n Q) (onl_len n Q)
                rw [e] at this
                simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] at this
                simpa [V] using this
              · refine ⟨a, b, false, ha, hb, hab, fun Q => ?_⟩
                have := rg0 (onl n Q) (onl_len n Q)
                rw [e] at this
                simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] at this
                simpa [V] using this
          · rcases hop' with e | e
            · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
              rw [rg0 _ (hlen1 _ _)]
              simp [e, GateOp.eval, hb]
            · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
              rw [rg0 _ (hlen1 _ _)]
              simp [e, GateOp.eval, ha, hb]
        · rcases hop' with e | e
          · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha]
          · by_cases hb : b < n + n + j
            · refine absurd (Or.inr ⟨b, hb, fun p => ?_⟩) bad
              rw [rg0 _ (hlen1 _ _)]
              simp [e, GateOp.eval, ha, hb]
            · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
              rw [rg0 _ (hlen1 _ _)]
              simp [e, GateOp.eval, ha, hb]
      · simp at hl
    choose! A B An hA hB hAB hv1 using shape
    have hout : C.output < n + n + C.gates.length := by
      by_contra h
      refine nonc ⟨false, fun p => ?_⟩
      change (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD C.output false = false
      exact List.getD_eq_default _ _ (by rw [run_length, hlen1]; omega)
    obtain ⟨i, hi, a, b, c, ha, hb, hc, hab, hac, hbc, ka, kb, kc⟩ := core n hn3 C.gates.length A B An V C.output hA hB hAB
      (fun Q w hw => by
        simp only [V]
        rw [run_input _ _ _ (by rw [onl_len]; exact hw), onl_get n Q w hw])
      (fun Q j hj => hv1 j hj Q) hout
      (fun u v hu hv => by
        have := hf ⟨u, hu⟩ ⟨v, hv⟩
        rw [one_onl] at this
        change (run C.gates (onl n (pt n u v))).getD C.output false = _ at this
        simp only [V]
        rw [this]
        simp [Fin.ext_iff])
      (fun j hj w hw hall => irr0 j hj (Or.inr ⟨w, hw, fun p => by rw [← hV, ← hV]; exact hall _ _ p.1.isLt p.2.isLt⟩))
    -- remove index `i`
    let ii : Fin (k + 1) := ⟨i, hi⟩
    have hsa : ∀ u : Fin k, ((ii.succAbove u : Fin (k + 1)) : ℕ) ≠ i := fun u h => Fin.succAbove_ne ii u (Fin.ext h)
    have hlen2 : ∀ u v : Fin k, (PEqualNP.Represents.oneEach u v).length = k + k := by intro u v; simp [PEqualNP.Represents.oneEach]
    have kf : ∀ j, Kill n V i j → (∃ b, ∀ p : Fin k × Fin k, (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD (n + n + j) false = b) ∨
        ∃ w < n + n + j, ∀ p : Fin k × Fin k, (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD (n + n + j) false = (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD w false := by
      rintro j (⟨b, h⟩ | ⟨w, hw, h⟩)
      · exact Or.inl ⟨b, fun p => by rw [← hV]; exact h _ _ (Fin.isLt _) (Fin.isLt _) (hsa _) (hsa _)⟩
      · exact Or.inr ⟨w, hw, fun p => by rw [← hV, ← hV]; exact h _ _ (Fin.isLt _) (Fin.isLt _) (hsa _) (hsa _)⟩
    obtain ⟨D, d1, d2, d3⟩ := engine3 (n + n) (k + k) C (fun p : Fin k × Fin k => PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2)) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
      (fun p => hlen1 _ _) (fun p => hlen2 _ _) {a, b, c} hC (by
        intro w hw
        by_cases h : w < n
        · by_cases hwi : w = i
          · left
            refine ⟨false, fun p => ?_⟩
            rw [one_onl, onl_get n _ w hw, pt, decide_eq_false_iff_not]
            have := hsa p.1
            omega
          · right
            obtain ⟨u', hu'⟩ := Fin.exists_succAbove_eq (x := (⟨w, h⟩ : Fin (k + 1))) (y := ii) (fun e => hwi (congrArg Fin.val e))
            refine ⟨u', by have := u'.isLt; omega, fun p => ?_⟩
            rw [one_onl, one_onl, onl_get n _ w hw, onl_get k _ _ (by have := u'.isLt; omega)]
            simp only [pt]
            rw [decide_eq_decide]
            have e1 : w = ((ii.succAbove p.1 : Fin (k + 1)) : ℕ) ↔ (u' : ℕ) = p.1 := by
              rw [← show ((ii.succAbove u' : Fin (k + 1)) : ℕ) = w from congrArg Fin.val hu', ← Fin.ext_iff, ← Fin.ext_iff, (Fin.succAbove_right_injective).eq_iff]
            have := u'.isLt
            constructor
            · rintro (e | e)
              · exact Or.inl (e1.1 e)
              · omega
            · rintro (e | e)
              · exact Or.inl (e1.2 e)
              · omega
        · by_cases hwi : w = n + i
          · left
            refine ⟨false, fun p => ?_⟩
            rw [one_onl, onl_get n _ w hw, pt, decide_eq_false_iff_not]
            have := hsa p.2
            have := (ii.succAbove p.1).isLt
            omega
          · right
            obtain ⟨u', hu'⟩ := Fin.exists_succAbove_eq (x := (⟨w - n, by omega⟩ : Fin (k + 1))) (y := ii) (fun e => hwi (by have := congrArg Fin.val e; simp only [ii] at this; omega))
            refine ⟨k + u', by have := u'.isLt; omega, fun p => ?_⟩
            rw [one_onl, one_onl, onl_get n _ w hw, onl_get k _ _ (by have := u'.isLt; omega)]
            simp only [pt]
            rw [decide_eq_decide]
            have e0 : ((ii.succAbove u' : Fin (k + 1)) : ℕ) = w - n := congrArg Fin.val hu'
            have e1 : w - n = ((ii.succAbove p.2 : Fin (k + 1)) : ℕ) ↔ (u' : ℕ) = p.2 := by
              rw [← e0, ← Fin.ext_iff, ← Fin.ext_iff, (Fin.succAbove_right_injective).eq_iff]
            have h1 := u'.isLt
            have h2 := p.1.isLt
            have h3 := (ii.succAbove p.1).isLt
            constructor
            · rintro (e | e)
              · omega
              · have := e1.1 (by omega); omega
            · rintro (e | e)
              · omega
              · have := e1.2 (by omega); omega)
      (by
        rintro ⟨b, hb⟩
        have h1 := hb (⟨0, by omega⟩, ⟨0, by omega⟩)
        have h2 := hb (⟨0, by omega⟩, ⟨1, by omega⟩)
        simp only [hf] at h1 h2
        rw [← h1] at h2
        simp [(Fin.succAbove_right_injective).eq_iff] at h2)
      (by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl
        · exact ⟨ha, kf _ ka⟩
        · exact ⟨hb, kf _ kb⟩
        · exact ⟨hc, kf _ kc⟩)
    have hD := ih D d1 fun u v => by
      rw [d3 (u, v), hf]
      simp only [ne_eq, (Fin.succAbove_right_injective).eq_iff]
    have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    rw [hcard] at d2
    omega

theorem aux : True := trivial

end C7626

theorem C7626.crown : ∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → 3 * n ≤ s + 3 := by
  rintro n s ⟨C, hC, hs, hf⟩
  have := PEqualNP.Outside.L_meta_17365.C7626.main n C hC hf
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- One gate step, as in `Circuit.wires`. -/
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- Rename the wires a gate reads. -/
def rn (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

theorem getD_app (W : List Bool) (b : Bool) (i : ℕ) :
    (W ++ [b]).getD i false = if i < W.length then W.getD i false
      else if i = W.length then b else false := by
  by_cases h1 : i < W.length
  · rw [if_pos h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : i = W.length
    · subst h2; simp
    · rw [if_neg h2, List.getD_eq_default _ _ (by simp; omega)]

theorem relabel (n1 n2 : ℕ) (φ : ℕ → ℕ) (hφ : ∀ i, n1 ≤ i → φ i + n1 = i + n2) :
    ∀ (gs : List Gate) (W W' : List Bool), n1 ≤ W.length →
      W.length + n2 = W'.length + n1 →
      (∀ i, i < n1 → φ i < n2 ∨ W'.length + gs.length ≤ φ i) →
      (∀ i, W.getD i false = W'.getD (φ i) false) →
      ∀ i, (gs.foldl stp W).getD i false = ((gs.map (rn φ)).foldl stp W').getD (φ i) false := by
  intro gs
  induction gs with
  | nil => intro W W' _ _ _ h i; simpa using h i
  | cons g rest ih =>
    intro W W' h1 h2 h3 h4
    have hl : (g :: rest).length = rest.length + 1 := rfl
    simp only [List.foldl_cons, List.map_cons]
    have hb : (rn φ g).op.eval ((rn φ g).inputs.map fun i => W'.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [rn, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (h4 i).symm
    apply ih
    · simp [stp]; omega
    · simp [stp]; omega
    · intro i hi
      rcases h3 i hi with h | h
      · exact Or.inl h
      · right; simp only [stp, List.length_append, List.length_singleton]; omega
    · intro i
      simp only [stp]
      rw [getD_app, getD_app, hb]
      by_cases hi : i < W.length
      · rw [if_pos hi]
        by_cases hn : i < n1
        · rcases h3 i hn with h | h
          · rw [if_pos (by omega)]; exact h4 i
          · rw [if_neg (show ¬ φ i < W'.length by omega),
              if_neg (show ¬ φ i = W'.length by omega), h4 i, List.getD_eq_default]; omega
        · have := hφ i (by omega)
          rw [if_pos (by omega)]; exact h4 i
      · have := hφ i (by omega)
        rw [if_neg hi, if_neg (show ¬ φ i < W'.length by omega)]
        by_cases he : i = W.length
        · rw [if_pos he, if_pos (show φ i = W'.length by omega)]
        · rw [if_neg he, if_neg (show ¬ φ i = W'.length by omega)]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ (n ≤ i ∧ i = n + v.val)) := by
  unfold oneEach
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_ofFn]
    by_cases hu : i = u.val
    · simp [hu, Fin.ext_iff]
    · have : ¬ (⟨i, h⟩ : Fin n) = u := fun e => hu (by rw [← e])
      simp [this, hu]; omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h2 : i - n < m
    · rw [List.getD_eq_getElem _ _ (by simpa using h2)]
      simp only [List.getElem_ofFn]
      by_cases hv : i - n = v.val
      · have : (⟨i - n, h2⟩ : Fin m) = v := Fin.ext hv
        simp [this]; omega
      · have : ¬ (⟨i - n, h2⟩ : Fin m) = v := fun e => hv (by rw [← e])
        simp [this]; omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp; omega

/-- The renaming from the double crown inputs (4k wires) onto the crown inputs (2k wires). -/
def phi (k B : ℕ) (i : ℕ) : ℕ :=
  if i < 2 * k then (if i % 2 = 0 then i / 2 else B)
  else if i < 4 * k then (if (i - 2 * k) % 2 = 0 then k + (i - 2 * k) / 2 else B)
  else i - 2 * k

/-- The kept part of the double crown relabels onto the crown on `k + k` vertices. -/
theorem shrink (k s : ℕ)
    (h : RepSizeAtMost (fun u v : Fin (2 * k) =>
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k)) && decide (u.val % 2 = 0) &&
        decide (v.val % 2 = 0)) s) :
    RepSizeAtMost (fun u v : Fin k => decide (u ≠ v)) s := by
  obtain ⟨C, hC, hs, hr⟩ := h
  set B := 2 * k + C.gates.length with hBdef
  have hB : 2 * k ≤ B := by omega
  refine ⟨⟨C.gates.map (rn (phi k B)), phi k B C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hC g0 hg0
    simpa [rn] using this
  · simpa [Circuit.size] using hs
  · intro t t'
    have ht : 2 * t.val < 2 * k := by omega
    have ht' : 2 * t'.val < 2 * k := by omega
    have key := hr ⟨2 * t.val, ht⟩ ⟨2 * t'.val, ht'⟩
    have hx : (oneEach (⟨2 * t.val, ht⟩ : Fin (2 * k)) (⟨2 * t'.val, ht'⟩ : Fin (2 * k))).length
        = 2 * k + 2 * k := by simp [oneEach]
    have hy : (oneEach t t').length = k + k := by simp [oneEach]
    have R := relabel (2 * k + 2 * k) (k + k) (phi k B)
      (by intro i hi; unfold phi; rw [if_neg (by omega), if_neg (by omega)]; omega)
      C.gates (oneEach (⟨2 * t.val, ht⟩ : Fin (2 * k)) (⟨2 * t'.val, ht'⟩ : Fin (2 * k)))
      (oneEach t t') (by omega) (by omega)
      (by
        intro i hi
        unfold phi
        rw [hy]
        by_cases a : i < 2 * k
        · rw [if_pos a]; split_ifs <;> omega
        · rw [if_neg a, if_pos (by omega)]; split_ifs <;> omega)
      (by
        intro i
        rw [oneEach_getD, oneEach_getD]
        simp only [Fin.val_mk, decide_eq_decide]
        unfold phi
        by_cases a : i < 2 * k
        · rw [if_pos a]
          split_ifs with e <;> omega
        · rw [if_neg a]
          by_cases b : i < 4 * k
          · rw [if_pos b]
            split_ifs with e <;> omega
          · rw [if_neg b]
            omega)
      C.output
    have e1 : C.eval (oneEach (⟨2 * t.val, ht⟩ : Fin (2 * k)) (⟨2 * t'.val, ht'⟩ : Fin (2 * k))) =
        (C.gates.foldl stp
          (oneEach (⟨2 * t.val, ht⟩ : Fin (2 * k)) (⟨2 * t'.val, ht'⟩ : Fin (2 * k)))).getD
          C.output false := rfl
    show ((C.gates.map (rn (phi k B))).foldl stp (oneEach t t')).getD (phi k B C.output) false = _
    rw [← R, ← e1, key]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have hm : (2 * t.val + 1) % (2 * k) % 2 = 1 := by
      rcases Nat.lt_or_ge (2 * t.val + 1) (2 * k) with c | c
      · rw [Nat.mod_eq_of_lt c]; omega
      · have : 2 * t.val + 1 = 2 * k := by omega
        omega
    have hne : 2 * t'.val ≠ (2 * t.val + 1) % (2 * k) := by
      intro e
      have : 2 * t'.val % 2 = (2 * t.val + 1) % (2 * k) % 2 := by rw [e]
      omega
    by_cases q : t = t'
    · subst q; simp
    · have : t.val ≠ t'.val := fun e => q (Fin.ext e)
      simp [q, hne]; omega

theorem count_rows (k : ℕ) (hk : 2 ≤ k) :
    (Finset.univ.filter (fun a : Fin (2 * k) => ∃ b : Fin (2 * k),
      decide (b.val ≠ a.val ∧ b.val ≠ (a.val + 1) % (2 * k)) = true ∧
      ∃ a' : Fin (2 * k), decide (b.val ≠ a'.val ∧ b.val ≠ (a'.val + 1) % (2 * k)) = false)).card
      = 2 * k := by
  rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
  intro a _
  have h2 : (a.val + 2) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
  refine ⟨⟨(a.val + 2) % (2 * k), h2⟩, ?_, ⟨(a.val + 2) % (2 * k), h2⟩, by simp⟩
  have ha := a.isLt
  simp only [decide_eq_true_eq]
  rcases Nat.lt_or_ge (a.val + 2) (2 * k) with c | c
  · rw [Nat.mod_eq_of_lt c]
    rcases Nat.lt_or_ge (a.val + 1) (2 * k) with d | d
    · rw [Nat.mod_eq_of_lt d]; omega
    · omega
  · have e : (a.val + 2) % (2 * k) = a.val + 2 - 2 * k := by
      rw [Nat.mod_eq_sub_mod c, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    rcases Nat.lt_or_ge (a.val + 1) (2 * k) with d | d
    · rw [Nat.mod_eq_of_lt d]; omega
    · have e2 : (a.val + 1) % (2 * k) = a.val + 1 - 2 * k := by
        rw [Nat.mod_eq_sub_mod d, Nat.mod_eq_of_lt (by omega)]
      rw [e2]; omega

theorem count_cols (k : ℕ) (hk : 2 ≤ k) :
    (Finset.univ.filter (fun b : Fin (2 * k) => ∃ a : Fin (2 * k),
      decide (b.val ≠ a.val ∧ b.val ≠ (a.val + 1) % (2 * k)) = true ∧
      ∃ b' : Fin (2 * k), decide (b'.val ≠ a.val ∧ b'.val ≠ (a.val + 1) % (2 * k)) = false)).card
      = 2 * k := by
  rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
  intro b _
  have h2 : (b.val + 2) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
  refine ⟨⟨(b.val + 2) % (2 * k), h2⟩, ?_, ⟨(b.val + 2) % (2 * k), h2⟩, by simp⟩
  have hb := b.isLt
  simp only [decide_eq_true_eq]
  rcases Nat.lt_or_ge (b.val + 3) (2 * k) with c | c
  · rw [Nat.mod_eq_of_lt (by omega : b.val + 2 < 2 * k)]
    rw [Nat.mod_eq_of_lt (by omega : b.val + 2 + 1 < 2 * k)]; omega
  · rcases Nat.lt_or_ge (b.val + 2) (2 * k) with d | d
    · rw [Nat.mod_eq_of_lt d]
      have e2 : (b.val + 2 + 1) % (2 * k) = b.val + 3 - 2 * k := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e2]; omega
    · have e : (b.val + 2) % (2 * k) = b.val + 2 - 2 * k := by
        rw [Nat.mod_eq_sub_mod d, Nat.mod_eq_of_lt (by omega)]
      rw [e]
      rw [Nat.mod_eq_of_lt (by omega : b.val + 2 - 2 * k + 1 < 2 * k)]; omega

theorem evens_card (k : ℕ) :
    (Finset.univ.filter (fun u : Fin (2 * k) => u.val % 2 = 0)).card ≤ k := by
  have : Finset.univ.filter (fun u : Fin (2 * k) => u.val % 2 = 0) ⊆
      (Finset.univ : Finset (Fin k)).image (fun t => (⟨2 * t.val, by omega⟩ : Fin (2 * k))) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨u.val / 2, by omega⟩, Fin.ext (by simp; omega)⟩
  calc _ ≤ _ := Finset.card_le_card this
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

theorem main (k s : ℕ) (hk : 2 ≤ k)
    (h : RepSizeAtMost (fun u v : Fin (2 * k) =>
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k))) s) : 5 * k - 3 ≤ s := by
  set R := Finset.univ.filter (fun u : Fin (2 * k) => u.val % 2 = 0)
  have hev : ∀ u : Fin (2 * k), u.val % 2 = 0 → u ∈ R := by
    intro u hu; simp [R, hu]
  obtain ⟨s', hs', hle⟩ := PEqualNP.Outside.L_meta_17365.RepInduced.induced (2 * k) (2 * k) s
    (fun u v : Fin (2 * k) => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k))) R R
    (by
      intro u hu
      exact ⟨u, hu, by simp⟩)
    (by
      intro v hv
      exact ⟨v, hv, by simp⟩)
    (by
      refine ⟨⟨0, by omega⟩, hev _ (by simp), ⟨2, by omega⟩, hev _ (by simp), ?_⟩
      simp only [decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt (by omega)]; omega)
    h
  rw [count_rows k hk, count_cols k hk] at hle
  have c1 := (Finset.card_filter_le R (fun a => ∃ b ∈ R, decide (b.val ≠ a.val ∧
    b.val ≠ (a.val + 1) % (2 * k)) = true)).trans (evens_card k)
  have c2 := (Finset.card_filter_le R (fun b => ∃ a ∈ R, decide (b.val ≠ a.val ∧
    b.val ≠ (a.val + 1) % (2 * k)) = true)).trans (evens_card k)
  have hs2 : RepSizeAtMost (fun u v : Fin (2 * k) =>
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k)) && decide (u.val % 2 = 0) &&
        decide (v.val % 2 = 0)) s' := by
    have e : (fun u v : Fin (2 * k) =>
        decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k)) && decide (u ∈ R) &&
          decide (v ∈ R)) = (fun u v : Fin (2 * k) =>
        decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k)) && decide (u.val % 2 = 0) &&
          decide (v.val % 2 = 0)) := by
      funext u v; simp [R]
    rw [← e]; exact hs'
  have hc := PEqualNP.Outside.L_meta_17365.C7626.crown k s' (shrink k s' hs2)
  omega

end PEqualNP.Outside.L_meta_17365

theorem PEqualNP.Outside.L_meta_17365 : ∀ k s : ℕ, 2 ≤ k → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (2 * k) => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k))) s → 5 * k - 3 ≤ s :=
  fun k s hk h => PEqualNP.Outside.L_meta_17365.main k s hk h
