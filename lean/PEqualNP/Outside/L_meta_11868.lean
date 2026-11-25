import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11868_aux

-- From .pnp-tools/BoolMat11868Count.lean
section

open scoped BigOperators

namespace BoolMat11868Count

theorem lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (active gates outputs branches : Finset V)
    (hActive : active.card = 8 + gates.card) (hOutputs : outputs.card = 4)
    (hBranches : branches.card = 8) (hSubset : branches ⊆ active)
    (hSuccessor : ∀ a ∈ active, ∃ b, E a b)
    (hTwo : ∀ a ∈ branches, ∃ b c, b ≠ c ∧ E a b ∧ E a c)
    (hIn : ∀ b, (Finset.univ.filter (fun a => E a b)).card ≤
      2 * (if b ∈ gates then 1 else 0) + (if b ∈ outputs then 1 else 0)) :
    12 ≤ gates.card := by
  let outDegree (a : V) := (Finset.univ.filter (E a)).card
  let inDegree (b : V) := (Finset.univ.filter (fun a => E a b)).card
  have demand (a : V) : (if a ∈ active then 1 else 0) +
      (if a ∈ branches then 1 else 0) ≤ outDegree a := by
    by_cases hb : a ∈ branches
    · have ha := hSubset hb
      obtain ⟨b, c, hbc, hab, hac⟩ := hTwo a hb
      have h : 1 < outDegree a :=
        Finset.one_lt_card_iff.mpr ⟨b, c, by simp [hab], by simp [hac], hbc⟩
      simpa [ha, hb] using (Nat.succ_le_of_lt h)
    · by_cases ha : a ∈ active
      · obtain ⟨b, hab⟩ := hSuccessor a ha
        have h : 1 ≤ outDegree a := Finset.one_le_card.mpr ⟨b, by simp [hab]⟩
        simpa [ha, hb] using h
      · simp [ha, hb]
  have card_sum (s : Finset V) : (∑ a : V, if a ∈ s then (1 : ℕ) else 0) = s.card :=
    (Finset.card_eq_sum_ite (Finset.subset_univ s)).symm
  have count : active.card + branches.card ≤ 2 * gates.card + outputs.card := calc
    active.card + branches.card =
        ∑ a : V, ((if a ∈ active then 1 else 0) + (if a ∈ branches then 1 else 0)) := by
      rw [Finset.sum_add_distrib, card_sum, card_sum]
    _ ≤ ∑ a : V, outDegree a := Finset.sum_le_sum (fun a _ => demand a)
    _ = ∑ b : V, inDegree b := by
      simp only [outDegree, inDegree, Finset.card_filter]
      exact Finset.sum_comm
    _ ≤ ∑ b : V, (2 * (if b ∈ gates then 1 else 0) + (if b ∈ outputs then 1 else 0)) :=
      Finset.sum_le_sum (fun b _ => hIn b)
    _ = 2 * gates.card + outputs.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, card_sum, card_sum]
  omega

end BoolMat11868Count

end

-- From pequalnp-proofs/lean/PEqualNP/Outside/L_meta_2752.lean
section

namespace BranchProof2752

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b∧a≠cut∧b≠cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b,edge a b → rank a < rank b)
    (localStep : ∀ b,¬ input b → x b≠y b → ∃ a,edge a b∧x a≠y a)
    (sameCut : x cut = y cut) {out : W} (different : x out≠y out) :
    ∃ a,input a∧x a≠y a∧Relation.ReflTransGen (avoid edge cut) a out:=by
  classical
  have track : ∀ k b,rank b = k → x b≠y b →
      ∃ a,input a∧x a≠y a∧Relation.ReflTransGen (avoid edge cut) a b:=by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b,hInput,diff,Relation.ReflTransGen.refl⟩
      · obtain ⟨p,hp,dp⟩:=localStep b hInput diff
        have earlier : rank p < k:=(order p b hp).trans_eq hb
        obtain ⟨a,ha,da,path⟩:=ih (rank p) earlier p rfl dp
        have pOff : p≠cut:=by rintro rfl; exact dp sameCut
        have bOff : b≠cut:=by rintro rfl; exact diff sameCut
        exact ⟨a,ha,da,path.tail ⟨hp,pOff,bOff⟩⟩
  exact track (rank out) out rfl different

end PetersenCutTrace

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop:=∃ a b,reads v a∧reads v b∧a≠b

def Terminal (v : Fin m) : Prop:=v = output∨Branches reads v

def Follow (v w : Fin m) : Prop:=reads v w∧¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b:=by
  by_contra separate
  exact first.2 (Or.inr ⟨a,b,first.1,next.1,separate⟩)

variable (forward : ∀ {v w : Fin m},reads v w → v < w)

variable (live : ∀ v : Fin m,v≠output → ∃ w,reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m,Terminal reads output root∧ReflTransGen (Follow reads output) v root:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v,terminal,ReflTransGen.refl⟩
    obtain ⟨next,edge⟩:=live v (fun e => terminal (Or.inl e))
    have increase:=forward edge
    have closer : distance next < distance v:=by
      dsimp [distance]
      have bounds:=next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root,stopped,route⟩:=ih next closer
    exact ⟨root,stopped,route.head ⟨edge,terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next,edge,tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_,edgeB,_⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB,edgeB,tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal:=follow_unique reads output edge edgeB
      subst nextB
      have increase:=forward edge.1
      have closer : distance next < distance v:=by
        dsimp [distance]
        have bounds:=next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w:=by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w∧first reads output forward live w = first reads output forward live v:=by
  induction route with
  | refl => exact ⟨ReflTransGen.refl,rfl⟩
  | tail _ edge ih =>
    have predecessorBefore:=lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked,label⟩:=ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _:=⟨edge,fun stopped => by
      have self:=first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step,(first_of_follows reads output forward live step).symm.trans label⟩

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b:=by
  have earlier:=lt_of_lt_of_le (forward edge) bound
  have same:=(read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge,fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop:=reads v w∧v≠cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v:=by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label:=(read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier:=lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _:=⟨edge.1,fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same:=(first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b:=by
  let distance (w : Fin m):=m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA,stepA,laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next,stepB,later⟩
      · exact bHere
      have equal : next = goal:=follow_unique reads output stepB edgeA
      subst next
      have increasing:=path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB,stepB,laterB⟩
      · subst b
        have equal : nextA = goal:=follow_unique reads output stepA edgeB
        subst nextA
        have increasing:=path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal:=follow_unique reads output stepA stepB
      subst nextB
      have increase:=forward stepA.1
      have closer : distance nextA < distance source:=by
        dsimp [distance]
        have bounds:=nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b:=by
  have aBound:=le_trans (le_of_lt (forward edgeA)) bound
  have bBound:=le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

end FirstBranchRoute

end BranchProof2752

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Shannon.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers

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

end CircuitHelpers

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Support.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

end CircuitHelpers

end

-- From .pnp-tools/BoolMat11868Facts.lean
section

namespace BoolMat11868Facts

def target (x : Fin 8 → Bool) : Fin 4 → Bool :=
  ![x 0 && x 4 || x 1 && x 6, x 0 && x 5 || x 1 && x 7,
    x 2 && x 4 || x 3 && x 6, x 2 && x 5 || x 3 && x 7]

def DependsOn (o : Fin 4) (i : Fin 8) : Prop :=
  ∃ x y : Fin 8 → Bool, (∀ k, k ≠ i → x k = y k) ∧ target x o ≠ target y o

private def row (ones : List (Fin 8)) (k : Fin 8) : Bool := decide (k ∈ ones)

private theorem row_cons (ones : List (Fin 8)) {i k : Fin 8} (h : k ≠ i) :
    row (i :: ones) k = row ones k := by
  simp [row, h]

private def firstProduct : Fin 8 → Fin 4 × Fin 8 :=
  ![(0, 4), (0, 6), (2, 4), (2, 6), (0, 0), (1, 0), (0, 1), (1, 1)]

private def secondProduct : Fin 8 → Fin 4 × Fin 8 :=
  ![(1, 5), (1, 7), (3, 5), (3, 7), (2, 2), (3, 2), (2, 3), (3, 3)]

private theorem sensitivity_table : ∀ i : Fin 8,
    let a := firstProduct i
    let b := secondProduct i
    a.1 ≠ b.1 ∧
      target (row [a.2]) a.1 ≠ target (row [i, a.2]) a.1 ∧
      target (row [b.2]) b.1 ≠ target (row [i, b.2]) b.1 := by
  decide +kernel

theorem each_raw_affects_two (i : Fin 8) : ∃ a b, a ≠ b ∧ DependsOn a i ∧ DependsOn b i := by
  have h := sensitivity_table i
  exact ⟨_, _, h.1,
    ⟨_, _, fun _ hk => (row_cons _ hk).symm, h.2.1⟩,
    ⟨_, _, fun _ hk => (row_cons _ hk).symm, h.2.2⟩⟩

private def mixedFixed (a b : Fin 8) : List (Fin 8) :=
  [2 * (1 - a / 2) + (b - 4) / 2, 4 + 2 * (a % 2) + (1 - b % 2)]

private def fixedBits (i j : Fin 8) : List (Fin 8) :=
  if i < 4 then
    if j < 4 then [4, 7] else mixedFixed i j
  else
    if j < 4 then mixedFixed j i else [0, 3]

set_option maxRecDepth 5000 in
private theorem pair_table : ∀ i j : Fin 8, i ≠ j →
    let bits := fixedBits i j
    let x := row bits
    let y := row (i :: bits)
    let z := row (j :: bits)
    target x ≠ target y ∧ target x ≠ target z ∧ target y ≠ target z := by
  decide +kernel

theorem pair_has_three_vectors (i j : Fin 8) (h : i ≠ j) :
    ∃ x y z : Fin 8 → Bool,
      (∀ k, k ≠ i → k ≠ j → x k = y k ∧ x k = z k) ∧
      target x ≠ target y ∧ target x ≠ target z ∧ target y ≠ target z := by
  refine ⟨_, _, _, ?_, pair_table i j h⟩
  intro k ki kj
  exact ⟨(row_cons _ ki).symm, (row_cons _ kj).symm⟩

open PEqualNP.CircuitLowerBounds

end BoolMat11868Facts

end

-- From .pnp-tools/BoolMat11868Graph.lean
section

namespace BoolMat11868Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers Relation

open BranchProof2752

abbrev Vertex (C : Circuit) := Fin (8 + C.gates.length + 5)

def raw (C : Circuit) (i : Fin 8) : Vertex C := ⟨i.val, by have := i.isLt; omega⟩

def obs (C : Circuit) (q : Fin 4) : Vertex C :=
  ⟨8 + C.gates.length + q.val, by have := q.isLt; omega⟩

def sink (C : Circuit) : Vertex C := ⟨8 + C.gates.length + 4, by omega⟩

theorem obsInjective (C : Circuit) : Function.Injective (obs C) := by
  intro i j h
  apply Fin.ext
  have eq := congrArg Fin.val h
  simp only [obs] at eq
  omega

def Edge (C : Circuit) (out : Fin 4 → ℕ) (a b : Vertex C) : Prop :=
  (∃ (p : ℕ) (g : Gate), C.gates[p]? = some g ∧ b.val = 8 + p ∧
    a.val < 8 + p ∧ a.val ∈ g.inputs) ∨
  (∃ q : Fin 4, b = obs C q ∧ a.val = out q ∧ a.val < 8 + C.gates.length)

theorem edgeOrder {C : Circuit} {out : Fin 4 → ℕ} {a b : Vertex C}
    (e : Edge C out a b) : a < b := by
  rcases e with ⟨p, g, hg, hb, ha, hi⟩ | ⟨q, rfl, he, ha⟩
  · change a.val < b.val
    rwa [hb]
  · change a.val < 8 + C.gates.length + q.val
    omega

theorem edgeSourceEarly {C : Circuit} {out : Fin 4 → ℕ} {a b : Vertex C}
    (e : Edge C out a b) : a.val < 8 + C.gates.length := by
  rcases e with ⟨p, g, hg, hb, ha, hi⟩ | ⟨q, hb, he, ha⟩
  · have hp := (List.getElem?_eq_some_iff.1 hg).1
    omega
  · exact ha

theorem obsTerminal (C : Circuit) (out : Fin 4 → ℕ) (q : Fin 4) (b : Vertex C) :
    ¬ Edge C out (obs C q) b := by
  intro e
  have h := edgeSourceEarly e
  change 8 + C.gates.length + q.val < 8 + C.gates.length at h
  omega

def value (C : Circuit) (out : Fin 4 → ℕ) (x : Fin 8 → Bool) (v : Vertex C) : Bool :=
  if v.val < 8 + C.gates.length then
    (C.wires (List.ofFn x)).getD v.val false
  else if h : v.val < 8 + C.gates.length + 4 then
    (C.wires (List.ofFn x)).getD (out ⟨v.val - (8 + C.gates.length), by omega⟩) false
  else false

theorem wireLength (C : Circuit) (x : Fin 8 → Bool) :
    (C.wires (List.ofFn x)).length = 8 + C.gates.length := by
  rw [wires_eq, length_wiresFrom, List.length_ofFn]

theorem valueReal (C : Circuit) (out : Fin 4 → ℕ) (x : Fin 8 → Bool) {v : Vertex C}
    (h : v.val < 8 + C.gates.length) :
    value C out x v = (C.wires (List.ofFn x)).getD v.val false := by simp [value, h]

theorem valueObs (C : Circuit) (out : Fin 4 → ℕ) (x : Fin 8 → Bool) (q : Fin 4) :
    value C out x (obs C q) = (C.wires (List.ofFn x)).getD (out q) false := by
  have bound := q.isLt
  have hn : ¬ (obs C q).val < 8 + C.gates.length := by dsimp [obs]; omega
  have ht : (obs C q).val < 8 + C.gates.length + 4 := by dsimp [obs]; omega
  simp only [value, if_neg hn, dif_pos ht]
  congr 2
  exact Fin.ext (by dsimp [obs]; omega)

theorem valueRaw (C : Circuit) (out : Fin 4 → ℕ) (x : Fin 8 → Bool) (i : Fin 8) :
    value C out x (raw C i) = x i := by
  have hb : (raw C i).val < 8 + C.gates.length := by
    change i.val < 8 + C.gates.length
    exact lt_of_lt_of_le i.isLt (by omega)
  rw [valueReal C out x hb, wires_eq, getD_wiresFrom _ _ _ (by simpa [raw] using i.isLt)]
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]

private theorem gateEval (C : Circuit) (x : Fin 8 → Bool) (p : ℕ) (hp : p < C.gates.length) :
    (C.wires (List.ofFn x)).getD (8 + p) false =
      C.gates[p].op.eval (C.gates[p].inputs.map fun w =>
        if w < 8 + p then (C.wires (List.ofFn x)).getD w false else false) := by
  let before := wiresFrom (C.gates.take p) (List.ofFn x)
  let after := C.gates.drop (p + 1)
  let bit := C.gates[p].op.eval (C.gates[p].inputs.map fun w => before.getD w false)
  have hlen : before.length = 8 + p := by
    simp [before, length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hp)]
  have whole : C.wires (List.ofFn x) = wiresFrom after (before ++ [bit]) := by
    rw [wires_eq]
    conv_lhs => rw [← List.take_append_drop p C.gates, List.drop_eq_getElem_cons hp, wiresFrom_append]
    rfl
  have hb : 8 + p < (before ++ [bit]).length := by simp [hlen]
  calc
    (C.wires (List.ofFn x)).getD (8 + p) false = bit := by
      rw [whole, getD_wiresFrom _ _ _ hb]
      simpa only [hlen] using getD_snoc_eq before bit false
    _ = _ := by
      dsimp [bit]
      congr 1
      apply List.map_congr_left
      intro w _
      by_cases hw : w < 8 + p
      · have hw' : w < before.length := by rwa [hlen]
        have hw'' : w < (before ++ [bit]).length := by simp [List.length_append]; omega
        rw [if_pos hw, whole, getD_wiresFrom _ _ _ hw'', List.getD_append _ _ _ _ hw']
      · have outOfRange : before.length ≤ w := by omega
        rw [if_neg hw, List.getD_eq_default _ _ outOfRange]

theorem valueStep {C : Circuit} {out : Fin 4 → ℕ} {x y : Fin 8 → Bool} {b : Vertex C}
    (notRaw : ¬ b.val < 8) (different : value C out x b ≠ value C out y b) :
    ∃ a, Edge C out a b ∧ value C out x a ≠ value C out y a := by
  by_cases real : b.val < 8 + C.gates.length
  · let p := b.val - 8
    have hp : p < C.gates.length := by dsimp [p]; omega
    have location : b.val = 8 + p := by dsimp [p]; omega
    by_contra! same
    apply different
    rw [valueReal C out x real, valueReal C out y real, location,
      gateEval C x p hp, gateEval C y p hp]
    congr 1
    apply List.map_congr_left
    intro w read
    by_cases earlier : w < 8 + p
    · have realW : w < 8 + C.gates.length := by omega
      let a : Vertex C := ⟨w, by omega⟩
      have e : Edge C out a b := Or.inl ⟨p, C.gates[p],
        List.getElem?_eq_getElem hp, location, earlier, read⟩
      have bits := same a e
      rw [valueReal C out x (v := a) realW, valueReal C out y (v := a) realW] at bits
      simpa [a, earlier] using bits
    · rw [if_neg earlier, if_neg earlier]
  · by_cases observed : b.val < 8 + C.gates.length + 4
    · let q : Fin 4 := ⟨b.val - (8 + C.gates.length), by omega⟩
      have location : b = obs C q := Fin.ext (by dsimp [obs, q]; omega)
      rw [location, valueObs, valueObs] at different
      by_cases valid : out q < 8 + C.gates.length
      · let a : Vertex C := ⟨out q, by omega⟩
        refine ⟨a, Or.inr ⟨q, location, rfl, valid⟩, ?_⟩
        rw [valueReal C out x (v := a) valid, valueReal C out y (v := a) valid]
        exact different
      · exfalso
        have xb : (C.wires (List.ofFn x)).length ≤ out q := by rw [wireLength]; omega
        have yb : (C.wires (List.ofFn y)).length ≤ out q := by rw [wireLength]; omega
        exact different ((List.getD_eq_default _ _ xb).trans (List.getD_eq_default _ _ yb).symm)
    · exact (different (by simp [value, real, observed])).elim

end BoolMat11868Graph

end

-- From .pnp-tools/BoolMat11868Routes.lean
section

namespace BoolMat11868Routes

open Relation BranchProof2752

open FirstBranchRoute

theorem eightBranches {N : Nat}
    (edge : Fin N → Fin N → Prop) (sink : Fin N) (top : ∀ v, v ≤ sink)
    (raw : Fin 8 → Fin N) (obs : Fin 4 → Fin N)
    (obsInjective : Function.Injective obs) (obsBefore : ∀ j, obs j < sink)
    (obsTerminal : ∀ j b, ¬ edge (obs j) b)
    (order : ∀ {a b}, edge a b → a < b)
    (beforeObs : ∀ {a b}, edge a b → ∀ j, a < obs j)
    (two : ∀ i, ∃ j k, j ≠ k ∧ ReflTransGen edge (raw i) (obs j) ∧
      ReflTransGen edge (raw i) (obs k))
    (separates : ∀ i j, i ≠ j → ∀ cut, ∃ q,
      ReflTransGen (PetersenCutTrace.avoid edge cut) (raw i) (obs q) ∨
      ReflTransGen (PetersenCutTrace.avoid edge cut) (raw j) (obs q)) :
    ∃ f : Fin 8 → Fin N, Function.Injective f ∧ ∀ i, Branches edge (f i) := by
  classical
  let reads (a b : Fin N) := edge a b ∨ a ≠ sink ∧ b = sink ∧ ¬ ∃ c, edge a c
  have forward {a b : Fin N} (step : reads a b) : a < b := by
    rcases step with step | ⟨notSink, rfl, _⟩
    · exact order step
    · exact lt_of_le_of_ne (top a) notSink
  have live (v : Fin N) (notSink : v ≠ sink) : ∃ w, reads v w := by
    by_cases next : ∃ w, edge v w
    · obtain ⟨w, hw⟩ := next
      exact ⟨w, Or.inl hw⟩
    · exact ⟨sink, Or.inr ⟨notSink, rfl, next⟩⟩
  let f (i : Fin 8) := first reads sink forward live (raw i)
  have obsToSink (j : Fin 4) : reads (obs j) sink :=
    Or.inr ⟨ne_of_lt (obsBefore j), rfl, fun ⟨w, hw⟩ => obsTerminal j w hw⟩
  have realPath {a b : Fin N} (route : ReflTransGen edge a b) : ReflTransGen reads a b :=
    ReflTransGen.mono (fun _ _ step => Or.inl step) _ _ route
  have firstNotSink (i : Fin 8) : f i ≠ sink := by
    intro atSink
    obtain ⟨j, k, distinct, routeJ, routeK⟩ := two i
    have bound : sink ≤ f i := atSink.ge
    have same := unique_predecessor_before reads sink forward live bound
      (realPath routeJ) (obsToSink j) (realPath routeK) (obsToSink k)
    exact distinct (obsInjective same)
  have branches (i : Fin 8) : Branches edge (f i) := by
    rcases first_stops reads sink forward live (raw i) with atSink | ⟨a, b, ha, hb, distinct⟩
    · exact (firstNotSink i atSink).elim
    have next : ∃ w, edge (f i) w := by
      rcases ha with ha | ⟨_, aSink, _⟩
      · exact ⟨a, ha⟩
      rcases hb with hb | ⟨_, bSink, _⟩
      · exact ⟨b, hb⟩
      exact (distinct (aSink.trans bSink.symm)).elim
    have real (w : Fin N) : reads (f i) w → edge (f i) w :=
      fun step => step.elim id (fun extra => (extra.2.2 next).elim)
    exact ⟨a, b, real a ha, real b hb, distinct⟩
  have noRoute (i : Fin 8) (q : Fin 4) :
      ¬ ReflTransGen (PetersenCutTrace.avoid edge (f i)) (raw i) (obs q) := by
    obtain ⟨a, _, ha, _, _⟩ := branches i
    intro route
    exact no_avoiding_after reads sink forward live (beforeObs ha q)
      (ReflTransGen.mono (fun _ _ step => ⟨Or.inl step.1, step.2.1⟩) _ _ route)
  refine ⟨f, ?_, branches⟩
  intro i j same
  by_contra distinct
  obtain ⟨q, route | route⟩ := separates i j distinct (f i)
  · exact noRoute i q route
  · exact noRoute j q (same ▸ route)

end BoolMat11868Routes

end

-- From .pnp-tools/BoolMat11868Live.lean
section

namespace BoolMat11868Live

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open BranchProof2752 Relation

open BoolMat11868Graph BoolMat11868Facts

def Live (C : Circuit) (out : Fin 4 → ℕ) (v : Vertex C) : Prop :=
  ∃ q : Fin 4, ReflTransGen (Edge C out) v (obs C q)

def LiveEdge (C : Circuit) (out : Fin 4 → ℕ) (a b : Vertex C) : Prop :=
  Edge C out a b ∧ Live C out b

theorem liveSource {C : Circuit} {out : Fin 4 → ℕ} {a b : Vertex C}
    (edge : LiveEdge C out a b) : Live C out a := by
  obtain ⟨q, reach⟩ := edge.2
  exact ⟨q, reach.head edge.1⟩

private theorem sinkNotLive (C : Circuit) (out : Fin 4 → ℕ) : ¬ Live C out (sink C) := by
  rintro ⟨q, route⟩
  have bound : sink C ≤ obs C q :=
    FirstBranchRoute.path_forward (Edge C out) (fun h => edgeOrder h) route
  change 8 + C.gates.length + 4 ≤ 8 + C.gates.length + q.val at bound
  have := q.isLt
  omega

noncomputable def liveValue (C : Circuit) (out : Fin 4 → ℕ) (x : Fin 8 → Bool) (v : Vertex C) : Bool := by
  classical
  exact if v.val < 8 ∨ Live C out v then value C out x v else false

private theorem liveValueLive {C : Circuit} {out : Fin 4 → ℕ} (x : Fin 8 → Bool) {v : Vertex C}
    (h : Live C out v) : liveValue C out x v = value C out x v := by
  classical
  unfold liveValue
  exact if_pos (Or.inr h)

private theorem liveValueRaw (C : Circuit) (out : Fin 4 → ℕ) (x : Fin 8 → Bool) (i : Fin 8) :
    liveValue C out x (raw C i) = x i := by
  classical
  unfold liveValue
  have here : (raw C i).val < 8 ∨ Live C out (raw C i) := Or.inl i.isLt
  rw [ite_eq_left here, valueRaw]

private theorem liveValueSink (C : Circuit) (out : Fin 4 → ℕ) (x : Fin 8 → Bool) :
    liveValue C out x (sink C) = false := by
  classical
  unfold liveValue
  refine if_neg (fun h => ?_)
  rcases h with h | h
  · change 8 + C.gates.length + 4 < 8 at h
    omega
  · exact sinkNotLive C out h

private theorem liveValueStep {C : Circuit} {out : Fin 4 → ℕ} {x y : Fin 8 → Bool} {b : Vertex C}
    (notRaw : ¬ b.val < 8) (different : liveValue C out x b ≠ liveValue C out y b) :
    ∃ a, LiveEdge C out a b ∧ liveValue C out x a ≠ liveValue C out y a := by
  classical
  by_cases live : Live C out b
  · rw [liveValueLive x live, liveValueLive y live] at different
    obtain ⟨a, h, ab⟩ := valueStep notRaw different
    have step : LiveEdge C out a b := ⟨h, live⟩
    exact ⟨a, step, by rw [liveValueLive x (liveSource step), liveValueLive y (liveSource step)]; exact ab⟩
  · simp [liveValue, notRaw, live] at different

abbrev Computes (C : Circuit) (out : Fin 4 → ℕ) : Prop :=
  ∀ x q, (C.wires (List.ofFn x)).getD (out q) false = target x q

private theorem liveValueObs {C : Circuit} {out : Fin 4 → ℕ} (fit : Computes C out)
    (x : Fin 8 → Bool) (q : Fin 4) : liveValue C out x (obs C q) = target x q := by
  rw [liveValueLive x ⟨q, .refl⟩, valueObs, fit]

private theorem trace {C : Circuit} {out : Fin 4 → ℕ} (fit : Computes C out)
    (x y : Fin 8 → Bool) (q : Fin 4) (cut : Vertex C)
    (same : liveValue C out x cut = liveValue C out y cut) (different : target x q ≠ target y q) :
    ∃ i : Fin 8, x i ≠ y i ∧
      ReflTransGen (PetersenCutTrace.avoid (LiveEdge C out) cut) (raw C i) (obs C q) := by
  have changed : liveValue C out x (obs C q) ≠ liveValue C out y (obs C q) := by
    simpa only [liveValueObs fit] using different
  obtain ⟨v, isRaw, bits, route⟩ := PetersenCutTrace.difference_traces
    (fun v : Vertex C => v.val) (fun v => v.val < 8) (LiveEdge C out) cut
    (liveValue C out x) (liveValue C out y) (fun a b step => edgeOrder step.1)
    (fun _ rawOff diff => liveValueStep rawOff diff) same changed
  let i : Fin 8 := ⟨v.val, isRaw⟩
  have eq : v = raw C i := Fin.ext rfl
  rw [eq, liveValueRaw, liveValueRaw] at bits
  exact ⟨i, bits, eq ▸ route⟩

private theorem dependencyPath {C : Circuit} {out : Fin 4 → ℕ} (fit : Computes C out)
    (i : Fin 8) (q : Fin 4) (dep : DependsOn q i) :
    ReflTransGen (LiveEdge C out) (raw C i) (obs C q) := by
  obtain ⟨x, y, agree, changed⟩ := dep
  have same : liveValue C out x (sink C) = liveValue C out y (sink C) := by
    rw [liveValueSink, liveValueSink]
  obtain ⟨j, diff, route⟩ := trace fit x y q (sink C) same changed
  have eq : j = i := by
    by_contra different
    exact diff (agree j different)
  subst j
  exact ReflTransGen.mono (fun _ _ e => e.1) _ _ route

theorem allRawLive {C : Circuit} {out : Fin 4 → ℕ} (fit : Computes C out) :
    ∀ i, Live C out (raw C i) := by
  intro i
  obtain ⟨q, q', distinct, dep, dep'⟩ := each_raw_affects_two i
  refine ⟨q, ?_⟩
  have route := dependencyPath fit i q dep
  exact ReflTransGen.mono (fun _ _ e => e.1) _ _ route

private theorem separatingPath {C : Circuit} {out : Fin 4 → ℕ} (fit : Computes C out)
    (i j : Fin 8) (distinct : i ≠ j) (cut : Vertex C) :
    ∃ q : Fin 4,
      ReflTransGen (PetersenCutTrace.avoid (LiveEdge C out) cut) (raw C i) (obs C q) ∨
      ReflTransGen (PetersenCutTrace.avoid (LiveEdge C out) cut) (raw C j) (obs C q) := by
  have witness (x y : Fin 8 → Bool) (outside : ∀ k, k ≠ i → k ≠ j → x k = y k)
      (different : target x ≠ target y)
      (same : liveValue C out x cut = liveValue C out y cut) :
      ∃ q : Fin 4,
        ReflTransGen (PetersenCutTrace.avoid (LiveEdge C out) cut) (raw C i) (obs C q) ∨
        ReflTransGen (PetersenCutTrace.avoid (LiveEdge C out) cut) (raw C j) (obs C q) := by
    have someDiff : ∃ q, target x q ≠ target y q := by
      by_contra! all
      exact different (funext all)
    obtain ⟨q, differs⟩ := someDiff
    obtain ⟨k, changed, path⟩ := trace fit x y q cut same differs
    by_cases e : k = i
    · exact ⟨q, Or.inl (e ▸ path)⟩
    · have eq : k = j := by
        by_contra e'
        exact changed (outside k e e')
      exact ⟨q, Or.inr (eq ▸ path)⟩
  obtain ⟨x, y, z, same, xy, xz, yz⟩ := pair_has_three_vectors i j distinct
  have collision : liveValue C out x cut = liveValue C out y cut ∨
      liveValue C out x cut = liveValue C out z cut ∨
      liveValue C out y cut = liveValue C out z cut := by
    cases liveValue C out x cut <;> cases liveValue C out y cut <;> cases liveValue C out z cut <;> decide
  rcases collision with h | h | h
  · exact witness x y (fun k ki kj => (same k ki kj).1) xy h
  · exact witness x z (fun k ki kj => (same k ki kj).2) xz h
  · exact witness y z (fun k ki kj => (same k ki kj).1.symm.trans (same k ki kj).2) yz h

theorem branches {C : Circuit} {out : Fin 4 → ℕ} (fit : Computes C out) :
    ∃ f : Fin 8 → Vertex C, Function.Injective f ∧
      ∀ i, FirstBranchRoute.Branches (LiveEdge C out) (f i) := by
  refine BoolMat11868Routes.eightBranches (LiveEdge C out) (sink C) ?_
    (raw C) (obs C) (obsInjective C) ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    change v.val ≤ 8 + C.gates.length + 4
    have := v.isLt
    omega
  · intro q
    change 8 + C.gates.length + q.val < 8 + C.gates.length + 4
    have := q.isLt
    omega
  · intro q b e
    exact obsTerminal C out q b e.1
  · intro a b e
    exact edgeOrder e.1
  · intro a b e q
    change a.val < 8 + C.gates.length + q.val
    have := edgeSourceEarly e.1
    omega
  · intro i
    obtain ⟨q, r, separate, hq, hr⟩ := each_raw_affects_two i
    exact ⟨q, r, separate, dependencyPath fit i q hq, dependencyPath fit i r hr⟩
  · exact separatingPath fit

end BoolMat11868Live

end

-- From .pnp-tools/BoolMat11868Degree.lean
section

namespace BoolMat11868Degree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open BranchProof2752

open BoolMat11868Graph BoolMat11868Live

theorem lower_bound (C : Circuit) (out : Fin 4 → ℕ) (hFan : FanInTwo C)
    (allRaw : ∀ i, Live C out (raw C i))
    (hBranches : ∃ f : Fin 8 → Vertex C, Function.Injective f ∧
      ∀ i, FirstBranchRoute.Branches (LiveEdge C out) (f i)) :
    12 ≤ C.gates.length := by
  classical
  obtain ⟨f, fInjective, fBranches⟩ := hBranches
  let raws := Finset.univ.image (raw C)
  let gates : Finset (Vertex C) := Finset.univ.filter fun v =>
    8 ≤ v.val ∧ v.val < 8 + C.gates.length ∧ Live C out v
  let active : Finset (Vertex C) := Finset.univ.filter fun v =>
    v.val < 8 + C.gates.length ∧ Live C out v
  let outputs := Finset.univ.image (obs C)
  let branches := Finset.univ.image f
  have memActive (v : Vertex C) : v ∈ active ↔ v.val < 8 + C.gates.length ∧ Live C out v := by
    simp [active]
  have memGates (v : Vertex C) : v ∈ gates ↔
      8 ≤ v.val ∧ v.val < 8 + C.gates.length ∧ Live C out v := by
    simp [gates]
  have memRaws (v : Vertex C) : v ∈ raws ↔ v.val < 8 := by
    change v ∈ Finset.univ.image (raw C) ↔ _
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact i.isLt
    · intro h
      exact ⟨⟨v.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have activeUnion : active = raws ∪ gates := by
    ext v
    rw [memActive, Finset.mem_union, memGates]
    constructor
    · rintro ⟨within, alive⟩
      by_cases isRaw : v.val < 8
      · exact Or.inl ((memRaws v).2 isRaw)
      · exact Or.inr ⟨Nat.le_of_not_gt isRaw, within, alive⟩
    · rintro (isRaw | ⟨_, within, alive⟩)
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 isRaw
        have hi := i.isLt
        exact ⟨by change i.val < 8 + C.gates.length; omega, allRaw i⟩
      · exact ⟨within, alive⟩
  have disjointRaws : Disjoint raws gates := by
    rw [Finset.disjoint_left]
    intro v hr hg
    exact (not_lt_of_ge ((memGates v).1 hg).1) ((memRaws v).1 hr)
  have rawInjective : Function.Injective (raw C) := by
    intro i j h
    exact Fin.ext (congrArg (fun v : Vertex C => v.val) h)
  have activeCount : active.card = 8 + gates.card := by
    rw [activeUnion, Finset.card_union_of_disjoint disjointRaws]
    simp [raws, Finset.card_image_of_injective _ rawInjective]
  have gateCount : gates.card ≤ C.gates.length := by
    rw [← Finset.card_range C.gates.length]
    refine Finset.card_le_card_of_injOn (fun v : Vertex C => v.val - 8) ?_ ?_
    · intro v hv
      obtain ⟨lower, upper, _⟩ := (memGates v).1 hv
      change v.val - 8 ∈ Finset.range C.gates.length
      exact Finset.mem_range.2 (by omega)
    · intro a ha b hb equal
      have aLower := ((memGates a).1 ha).1
      have bLower := ((memGates b).1 hb).1
      apply Fin.ext
      change a.val - 8 = b.val - 8 at equal
      omega
  have outputCount : outputs.card = 4 := by
    simp [outputs, Finset.card_image_of_injective _ (obsInjective C)]
  have branchCount : branches.card = 8 := by
    simp [branches, Finset.card_image_of_injective _ fInjective]
  have memberBranches (v : Vertex C) (hv : v ∈ branches) :
      FirstBranchRoute.Branches (LiveEdge C out) v := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
    exact fBranches i
  have branchActive : branches ⊆ active := by
    intro v hv
    obtain ⟨a, _, edge, _, _⟩ := memberBranches v hv
    exact (memActive v).2 ⟨edgeSourceEarly edge.1, liveSource edge⟩
  have successor : ∀ a ∈ active, ∃ b, LiveEdge C out a b := by
    intro a ha
    obtain ⟨within, q, path⟩ := (memActive a).1 ha
    rcases path.cases_head with atOutput | ⟨b, step, rest⟩
    · subst a
      change 8 + C.gates.length + q.val < 8 + C.gates.length at within
      omega
    · exact ⟨b, step, q, rest⟩
  have twoSuccessors : ∀ a ∈ branches, ∃ b c, b ≠ c ∧
      LiveEdge C out a b ∧ LiveEdge C out a c := by
    intro a ha
    obtain ⟨b, c, ab, ac, distinct⟩ := memberBranches a ha
    exact ⟨b, c, distinct, ab, ac⟩
  have incoming (b : Vertex C) : (Finset.univ.filter (fun a => LiveEdge C out a b)).card ≤
      2 * (if b ∈ gates then 1 else 0) + (if b ∈ outputs then 1 else 0) := by
    let preds := Finset.univ.filter (fun a => LiveEdge C out a b)
    change preds.card ≤ _
    have predEdge (a : Vertex C) (ha : a ∈ preds) : LiveEdge C out a b :=
      (Finset.mem_filter.1 ha).2
    by_cases nonempty : preds.Nonempty
    · obtain ⟨a, ha⟩ := nonempty
      have oneStep := predEdge a ha
      rcases oneStep.1 with ⟨p, g, hg, hb, _, _⟩ | ⟨q, hq, _, _⟩
      · have hp := (List.getElem?_eq_some_iff.1 hg).1
        have gate : b ∈ gates := (memGates b).2 ⟨by omega, by omega, oneStep.2⟩
        have inputCount : preds.card ≤ g.inputs.toFinset.card := by
          refine Finset.card_le_card_of_injOn (fun u : Vertex C => u.val) ?_ Fin.val_injective.injOn
          intro u hu
          change u.val ∈ g.inputs.toFinset
          rw [List.mem_toFinset]
          rcases (predEdge u hu).1 with ⟨r, g', hg', hb', _, wire⟩ | ⟨j, hj, _, _⟩
          · have hr : r = p := by omega
            subst r
            have hgEq : g' = g := Option.some.inj (hg'.symm.trans hg)
            simpa only [hgEq] using wire
          · have obsVal : b.val = 8 + C.gates.length + j.val := congrArg Fin.val hj
            omega
        have bound := inputCount.trans (g.inputs.toFinset_card_le.trans
          (hFan g (List.mem_of_getElem? hg)).2)
        rw [ite_eq_left gate]
        omega
      · have output : b ∈ outputs := Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq.symm⟩
        have source (u : Vertex C) (hu : u ∈ preds) : u.val = out q := by
          rcases (predEdge u hu).1 with ⟨p, g, hg, hb, _, _⟩ | ⟨j, hj, fromOut, _⟩
          · have hp := (List.getElem?_eq_some_iff.1 hg).1
            have obsVal : b.val = 8 + C.gates.length + q.val := congrArg Fin.val hq
            omega
          · exact fromOut.trans (congrArg out (obsInjective C (hj.symm.trans hq)))
        have bound : preds.card ≤ 1 := Finset.card_le_one.2 fun u hu v hv =>
          Fin.ext ((source u hu).trans (source v hv).symm)
        rw [ite_eq_left output]
        omega
    · simp [Finset.not_nonempty_iff_eq_empty.1 nonempty]
  exact (BoolMat11868Count.lower_bound (LiveEdge C out) active gates outputs branches
    activeCount outputCount branchCount branchActive successor twoSuccessors incoming).trans gateCount

end BoolMat11868Degree

end

end PEqualNP.Outside.L_meta_11868_aux

open PEqualNP.Outside.L_meta_11868_aux

theorem PEqualNP.Outside.L_meta_11868 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 4 → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ x : Fin 8 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 && x 4 || x 1 && x 6) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 && x 5 || x 1 && x 7) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 2 && x 4 || x 3 && x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 2 && x 5 || x 3 && x 7)) := by
  rintro ⟨C, out, fan, cap, computes⟩
  have fit : BoolMat11868Live.Computes C out := by
    intro x q
    have outputs := computes x
    fin_cases q
    · exact outputs.1
    · exact outputs.2.1
    · exact outputs.2.2.1
    · exact outputs.2.2.2
  have lower := BoolMat11868Degree.lower_bound C out fan
    (BoolMat11868Live.allRawLive fit) (BoolMat11868Live.branches fit)
  change C.gates.length ≤ 11 at cap
  omega
