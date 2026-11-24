import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_2519

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The normalization, fork bound, and pair invariant below are adapted from
-- L-meta-2165 by copsrlpond and its predecessor L-meta-1549.


-- The branch-group argument and circuit simplifier are adapted from L_meta_1549.
-- The simplifier tracks the number of non-NOT gates independently of length.

namespace BranchGraph

variable {V : Type*} [DecidableEq V]

def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I, ∃ b ∈ I, G.Adj a b

omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w} := by
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab

lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w} ↔ G.Adj u w := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u, by simp, w, by simp, h⟩

def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

section FiniteGraph

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v ∧ v ∉ removed)

lemma neighborsAfter_subset {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u := by
  intro v membership
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at membership ⊢
  exact ⟨membership.1, fun vIn => membership.2 (h vIn)⟩

lemma neighbor_equality_survives {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w := by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B) := by
    ext z
    simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => ⟨⟨hz.1, fun zIn => hz.2 (h zIn)⟩, hz.2⟩, fun hz => ⟨hz.1.1, hz.2⟩⟩
  rw [e u, e w, same]

def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group, ∀ w ∈ group, (neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty → neighborsAfter G removed u = neighborsAfter G removed w

def isolates (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v = ∅)

def maximalClass (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed ∧ (neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed ∧ neighborsAfter G removed v = neighborsAfter G removed root)
  else ∅

def closeIsolates (removed : Finset V) : Finset V := removed ∪ isolates G removed

def removeClass (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ maximalClass G removed root)

lemma subset_removeClass (removed : Finset V) (root : V) : removed ⊆ removeClass G removed root := by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)

lemma isolate_mem_removeClass {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ removeClass G removed root := by
  have hn : ¬ (neighborsAfter G (removed ∪ maximalClass G removed root) u).Nonempty := by
    intro existsNeighbor
    exact h (existsNeighbor.mono (neighborsAfter_subset G Finset.subset_union_left u))
  have hu : u ∈ isolates G (removed ∪ maximalClass G removed root) := by
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu

theorem dominates_step [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V, A ∪ Q ⊆ removeClass G B root := by
  classical
  by_cases someActive : ∃ root ∈ Q, root ∉ B ∧ (neighborsAfter G B root).Nonempty
  · obtain ⟨root, rootQ, rootOut, rootLive⟩ := someActive
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU := live.mono (neighborsAfter_subset G smaller u)
      have oldRoot := rootLive.mono (neighborsAfter_subset G smaller root)
      have same := neighbor_equality_survives G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ maximalClass G B root := by simp [maximalClass, rootOut, rootLive, uIn, same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact isolate_mem_removeClass G root u live
  · let root : V := Classical.choice inferInstance
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    exact isolate_mem_removeClass G root u (fun live => someActive ⟨u, hu, uIn, live⟩)

lemma retained_after_close {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty := by
  have uOut : u ∉ removed := fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty := by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp empty]
  obtain ⟨v, hv⟩ := old
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  refine ⟨v, ?_⟩
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hv.1, fun dropped => ?_⟩
  rcases Finset.mem_union.mp dropped with h | h
  · exact hv.2 h
  · have witness : u ∈ neighborsAfter G removed v := by
      simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv.1.symm, uOut⟩
    have none : neighborsAfter G removed v = ∅ := by simpa [isolates] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness

lemma closeIsolates_idempotent (removed : Finset V) :
    closeIsolates G (closeIsolates G removed) = closeIsolates G removed := by
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp hu with already | isolated
    · exact already
    by_contra out
    have live := retained_after_close G out
    have noNeighbors : neighborsAfter G (closeIsolates G removed) u = ∅ := by
      simpa [isolates] using isolated
    simpa [noNeighbors] using live
  · exact Finset.subset_union_left

def TwinSteps : Finset V → List (Finset V) → Prop
  | _, [] => True
  | removed, group :: rest => TwinGroup G removed group ∧ TwinSteps (removed ∪ group) rest

def removedThrough : Finset V → List (Finset V) → Finset V
  | removed, [] => removed
  | removed, group :: rest => removedThrough (removed ∪ group) rest

def ClassSteps : ℕ → Finset V → Finset V → Prop
  | 0, start, finish => finish = start
  | k + 1, start, finish => ∃ root : V, ClassSteps k (removeClass G start root) finish

theorem dominates_steps [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : TwinSteps G A groups) :
    ∃ finish : Finset V, ClassSteps G groups.length B finish ∧ removedThrough A groups ⊆ finish := by
  induction groups generalizing A B with
  | nil => exact ⟨B, rfl, smaller⟩
  | cons group rest ih =>
    obtain ⟨twins, next⟩ := steps
    obtain ⟨root, subset⟩ := dominates_step G smaller twins
    obtain ⟨finish, walk, covered⟩ := ih subset next
    exact ⟨finish, ⟨root, walk⟩, covered⟩

def EdgelessAfter (removed : Finset V) : Prop :=
  ∀ u v, u ∉ removed → v ∉ removed → ¬ G.Adj u v

omit [Fintype V] [DecidableRel G.Adj] in
lemma edgeless_mono {A B : Finset V} (subset : A ⊆ B) (noEdges : EdgelessAfter G A) :
    EdgelessAfter G B := by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))

lemma closed_edgeless_all {D : Finset V} (noEdges : EdgelessAfter G (closeIsolates G D)) :
    closeIsolates G D = Finset.univ := by
  ext u
  simp only [Finset.mem_univ, iff_true]
  by_contra out
  obtain ⟨v, hv⟩ := retained_after_close G out
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact noEdges u v out hv.2 hv.1

lemma classSteps_finish_closed {k : ℕ} {start finish : Finset V} (walk : ClassSteps G k start finish)
    (closed : ∃ D : Finset V, start = closeIsolates G D) : ∃ D : Finset V, finish = closeIsolates G D := by
  induction k generalizing start with
  | zero =>
    change finish = start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root, after⟩ := walk
    exact ih after ⟨_, rfl⟩

theorem covering_sequence_reaches_univ [Nonempty V] (groups : List (Finset V))
    (twins : TwinSteps G ∅ groups) (finished : EdgelessAfter G (removedThrough ∅ groups)) :
    ClassSteps G groups.length (closeIsolates G ∅) Finset.univ := by
  obtain ⟨D, steps, subset⟩ := dominates_steps G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges := edgeless_mono G subset finished
  obtain ⟨A, hD⟩ := classSteps_finish_closed G steps ⟨∅, rfl⟩
  rw [hD] at noEdges
  rwa [hD, closed_edgeless_all G noEdges] at steps

end FiniteGraph

end BranchGraph

namespace BranchGroupsLean

open BranchGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}

def bucket (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v = r)

def below (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v < r)

def coveredBy (label : V → Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)

omit [DecidableEq V] in
@[simp] lemma coveredBy_nil (label : V → Fin m) : coveredBy label [] = ∅ := by
  ext v
  simp [coveredBy]

lemma coveredBy_append_singleton (label : V → Fin m) (done : List (Fin m)) (r : Fin m) :
    coveredBy label (done ++ [r]) = coveredBy label done ∪ bucket label r := by
  ext v
  simp [coveredBy, bucket, List.mem_append]

omit [DecidableEq V] in
lemma covered_before_of_sorted (label : V → Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V, label v = out ∨ label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : coveredBy label done = below label r := by
  have facts := List.pairwise_append.mp sorted
  ext v
  simp only [coveredBy, below, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro member
    exact facts.2.2 _ member r (by simp)
  · intro earlier
    rcases roots v with isOut | member
    · rw [isOut] at earlier
      exact (lt_asymm earlier beforeOut).elim
    rcases List.mem_append.mp member with doneMember | coming
    · exact doneMember
    rcases List.mem_cons.mp coming with atRoot | later
    · exact (ne_of_lt earlier atRoot).elim
    have after := (List.pairwise_cons.mp facts.2.1).1 _ later
    exact (lt_asymm earlier after).elim

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sorted_tail_twin_steps (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (beforeOut : ∀ r ∈ roots, r < out)
    (twinAt : ∀ r ∈ roots, TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending = roots) :
    TwinSteps G (coveredBy label done) (pending.map (bucket label)) := by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots := complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev := covered_before_of_sorted label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next := ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_, ?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [coveredBy_append_singleton] at next

lemma removedThrough_coveredBy (label : V → Fin m) (done pending : List (Fin m)) :
    removedThrough (coveredBy label done) (pending.map (bucket label)) = coveredBy label (done ++ pending) := by
  induction pending generalizing done with
  | nil => simp [removedThrough]
  | cons r tail ih =>
    change removedThrough (coveredBy label done ∪ bucket label r) (tail.map (bucket label)) = _
    rw [← coveredBy_append_singleton, ih]
    simp [List.append_assoc]

omit [DecidableRel G.Adj] in
lemma no_edges_after_branches (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    EdgelessAfter G (removedThrough ∅ (roots.map (bucket label))) := by
  rw [← coveredBy_nil label, removedThrough_coveredBy, List.nil_append]
  intro u v uNot vNot
  have hu : label u = out := (allRoots u).resolve_right (by simpa [coveredBy] using uNot)
  have hv : label v = out := (allRoots v).resolve_right (by simpa [coveredBy] using vNot)
  exact outputIndependent u (by simp [bucket, hu]) v (by simp [bucket, hv])

theorem roots_required (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ branches)
    (beforeOut : ∀ r ∈ branches, r < out)
    (twinAt : ∀ r ∈ branches, TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V), TwinSteps G ∅ groups →
      EdgelessAfter G (removedThrough ∅ groups) → k ≤ groups.length) : k ≤ branches.card := by
  let roots := branches.sort
  have sorted : roots.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out ∨ label v ∈ roots := by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out := beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : TwinSteps G ∅ (roots.map (bucket label)) := by
    simpa using sorted_tail_twin_steps G label out roots sorted covers early twins [] roots rfl
  have last := no_edges_after_branches G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last

end Graph

end BranchGroupsLean

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

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


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Stat.const false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem


def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp


theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩


theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_, ?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k, [])) _)
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]


end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

end PetersenCutTrace

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x


structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)


theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ ∀ x, vl gs x o = f x := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, he⟩ := clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb⟩
  intro testGates testOut testClean testEval testCost
  have lower := Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates, testOut, testClean, testCost.trans hb, testEval, rfl⟩)
  exact hl.trans_le lower


theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount gs ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', hcost, he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs := by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'', o'', hc'', by omega, hcost.trans hkeep, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩


theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end LocalSection1

end CircuitProof.Readers

namespace CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

open CircuitProof.Readers

theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b]) : a ≠ b := by
  rintro rfl
  have hcl := L.hcl p g hg
  have hlt : a < m + p := by
    rcases hcl with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, hj, hk, h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg, hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]


end CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm

theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w ≠ out) :
    ∃ p, Reads gs p w := by
  by_cases isInput : w < n
  · let v : Fin n := ⟨w, isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p := w - n
    have wire : w = n + p := by dsimp [p]; omega
    have pLt : p < gs.length := by omega
    have notOut : out ≠ n + p := by omega
    obtain ⟨q, _, read⟩ := least.live nonconstant p pLt notOut
    exact ⟨q, wire.symm ▸ read⟩

theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup := by
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [args]
  · have distinct := pq2f_nodup least nonconstant atSlot ops args
    simp [args, distinct]

theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val ≠ out) :
    ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ w.val ∈ g.inputs ∧ n + p < n + gs.length := by
  obtain ⟨p, g, hit, reads⟩ := least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound := (List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p, g, hit, reads, by omega⟩

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega

theorem predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup := by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact PEqualNP.Outside.L_meta_2519.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have := b.isLt; omega))
  · simp [predecessors, internal]

end PetersenCutTrace

namespace PetersenScratch

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool := by
  classical
  exact decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

private theorem edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true := by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u, v, h, hu, hv⟩

private theorem edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w, x w = true → w = u ∨ w = v) :
    edgeValue G x = false := by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s, t, es, hs, ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es

private theorem edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (pairInput i j (fun _ => false) a b) = (a && b) := by
  cases a <;> cases b
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    simp [pairInput] at hk
  · apply edgeValue_false_pair (u := j) (v := j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
    assumption
  · exact edgeValue_true h (by simp [pairInput]) (by simp [pairInput, h.ne.symm])

private theorem edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i ≠ j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (pairInput i j (fun k => decide (k = u ∨ k = v)) a b) = (a || b) := by
  have hu : pairInput i j (fun k => decide (k = u ∨ k = v)) a b u = true := by
    simp [pairInput, hiu.ne.symm, huj]
  have hv : pairInput i j (fun k => decide (k = u ∨ k = v)) a b v = true := by
    simp [pairInput, hvi, hjv.ne.symm]
  cases a <;> cases b
  · apply edgeValue_false_pair huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk
    exact hk
  · exact edgeValue_true hjv (by simp [pairInput, hij.symm]) hv
  · exact edgeValue_true hiu (by simp [pairInput]) hu
  · exact edgeValue_true hiu (by simp [pairInput]) hu

theorem adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (factors : ∀ base : Fin n → Bool, ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue i j base p a b) = edgeValue G (pairInput i j base a b)) : False := by
  obtain ⟨outerA, ha⟩ := factors (fun _ => false)
  obtain ⟨outerO, ho⟩ := factors (fun k => decide (k = u ∨ k = v))
  exact fixed_pair_invariant i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (edge_pair_and hij a b))
    (fun a b => (ho a b).trans (edge_pair_or hij.ne hiu hjv huj hvi huv a b))

end PetersenScratch

namespace PetersenCutFormula

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl

end PetersenCutFormula

namespace PetersenCutIndependent

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

theorem adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (hi : occurrences i (wireFormula i gs cut.val) ≤ 1)
    (hj : occurrences j (wireFormula i gs cut.val) ≤ 1)
    (controlled : cut = out ∨ ∀ k : Fin n, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out) : False := by
  refine adjacent_cut_invariant G i j u v hij hiu hjv huj hvi huv
    (wireFormula i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f, hf⟩ := cut_factors hcl cut out (fun k => k = i ∨ k = j) base controlled
  refine ⟨f, fun a b => ?_⟩
  have agree : ∀ k, ¬ (k = i ∨ k = j) → pairInput i j base a b k = base k := by
    intro k hk
    simp [pairInput, show k ≠ i from fun e => hk (Or.inl e),
      show k ≠ j from fun e => hk (Or.inr e)]
  unfold pairValue
  rw [wireFormula_eval i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)

end PetersenCutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v

def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)

variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
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
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace PetersenFirstGroup

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path

theorem firstInputGroup_independent {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j, G.Adj i j → ∃ u v,
      G.Adj i u ∧ G.Adj j v ∧ u ≠ j ∧ v ≠ i ∧ ¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut) := by
  intro i iIn j jIn adjacent
  obtain ⟨u, v, hiu, hjv, huj, hvi, huv⟩ := witnesses i j adjacent
  have iFirst := (mem_firstInputGroup clean out live cut i).mp iIn
  have jFirst := (mem_firstInputGroup clean out live cut j).mp jIn
  have iCount := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine adjacent_cut_excluded clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases firstInputGroup_controlled clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))

end PetersenFirstGroup

namespace PetersenNine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Vertex := Fin 9
abbrev Edges := List (Vertex × Vertex)


def edges : Edges := [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)]

def edgeFun (es : Edges) (x : Vertex → Bool) : Bool :=
  es.any (fun edge => x edge.1 && x edge.2)


lemma noLoops : ∀ e ∈ edges, e.1 ≠ e.2 := by decide

lemma edgeFun_true (es : Edges) (x : Vertex → Bool) :
    edgeFun es x = true ↔ ∃ a b, (a, b) ∈ es ∧ x a = true ∧ x b = true := by
  simp only [edgeFun, List.any_eq_true, Bool.and_eq_true, Prod.exists]


def graph (es : Edges) (noSelf : ∀ e ∈ es, e.1 ≠ e.2) : SimpleGraph Vertex where
  Adj a b := (a, b) ∈ es ∨ (b, a) ∈ es
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => noSelf (v, v) he rfl) (fun he => noSelf (v, v) he rfl)⟩

end PetersenNine

namespace PetersenGroupBFS

structure MaskGraph where
  width : Nat
  adjacency : Nat → Nat

def bit (vertex : Nat) : Nat :=
  Nat.shiftLeft 1 vertex

def fullMask (g : MaskGraph) : Nat :=
  bit g.width - 1

def residualNeighbors (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  Nat.land (g.adjacency vertex) (Nat.xor (fullMask g) deleted)

def closeIsolates (g : MaskGraph) (deleted : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if residualNeighbors g deleted v = 0 then Nat.lor mask (bit v) else mask)
    deleted

def twinClass (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if !(Nat.testBit deleted v) &&
        (residualNeighbors g deleted v == residualNeighbors g deleted vertex)
      then Nat.lor mask (bit v) else mask)
    0

theorem bit_at (v w : Nat) : (bit v).testBit w = decide (v = w) := by
  simp [bit, Nat.shiftLeft_eq, Nat.testBit_two_pow]

theorem full_at (g : MaskGraph) (w : Nat) :
    (fullMask g).testBit w = decide (w < g.width) := by
  simp [fullMask, bit, Nat.shiftLeft_eq]

theorem neighbor_at (g : MaskGraph) (deleted v w : Nat) (hw : w < g.width) :
    (residualNeighbors g deleted v).testBit w =
      ((g.adjacency v).testBit w && !(deleted.testBit w)) := by
  simp [residualNeighbors, Nat.testBit_xor, full_at, hw]

private theorem fold_mask_at (vertices : List Nat) (p : Nat → Prop) [DecidablePred p]
    (initial w : Nat) :
    (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
      (initial.testBit w || (vertices.any fun v => decide (p v) && (v == w))) := by
  induction vertices generalizing initial with
  | nil => simp
  | cons v vertices ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    by_cases h : p v <;> simp [h, bit_at, Bool.or_assoc, Bool.beq_eq_decide_eq]

private theorem any_mask_at (p : Nat → Prop) [DecidablePred p] (n w : Nat) :
    ((List.range n).any fun v => decide (p v) && (v == w)) =
      (decide (w < n) && decide (p w)) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.and_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨v, hv, hp, rfl⟩
    exact ⟨hv, hp⟩
  · rintro ⟨hw, hp⟩
    exact ⟨w, hw, hp, rfl⟩

theorem close_at (g : MaskGraph) (deleted w : Nat) :
    (closeIsolates g deleted).testBit w =
      (deleted.testBit w || (decide (w < g.width) && decide (residualNeighbors g deleted w = 0))) := by
  unfold closeIsolates
  rw [fold_mask_at, any_mask_at]

theorem class_at (g : MaskGraph) (deleted v w : Nat) :
    (twinClass g deleted v).testBit w =
      (decide (w < g.width) &&
        (!(deleted.testBit w) && (residualNeighbors g deleted w == residualNeighbors g deleted v))) := by
  unfold twinClass
  rw [fold_mask_at, any_mask_at]
  simp [Bool.beq_eq_decide_eq]

theorem bit_eq_power (width : Nat) : bit width = 2 ^ width := by
  simp [bit, Nat.shiftLeft_eq]

theorem lor_bounded {width a b : Nat} (ha : a < bit width) (hb : b < bit width) :
    Nat.lor a b < bit width := by
  rw [bit_eq_power] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb

theorem high_false {width m w : Nat} (hm : m < bit width) (hw : width ≤ w) :
    m.testBit w = false := by
  rw [bit_eq_power] at hm
  exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))

theorem mask_ext {width a b : Nat} (ha : a < bit width) (hb : b < bit width)
    (same : ∀ w < width, a.testBit w = b.testBit w) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro w
  by_cases hw : w < width
  · exact same w hw
  · rw [high_false ha (Nat.le_of_not_gt hw), high_false hb (Nat.le_of_not_gt hw)]

theorem neighbor_bounded (g : MaskGraph) (deleted v : Nat) (hd : deleted < bit g.width) :
    residualNeighbors g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [residualNeighbors, full_at, Nat.not_lt_of_ge hw, high_false hd hw]

theorem close_bounded (g : MaskGraph) (deleted : Nat) (hd : deleted < bit g.width) :
    closeIsolates g deleted < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [close_at, Nat.not_lt_of_ge hw, high_false hd hw]

theorem class_bounded (g : MaskGraph) (deleted v : Nat) :
    twinClass g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [class_at, Nat.not_lt_of_ge hw]

def step (g : MaskGraph) (deleted : Nat) : List Nat :=
  deleted :: (List.range g.width).filterMap fun v =>
    if !(Nat.testBit deleted v) && (residualNeighbors g deleted v != 0)
    then some (closeIsolates g (Nat.lor deleted (twinClass g deleted v)))
    else none

def frontier (g : MaskGraph) : Nat → List Nat
  | 0 => [closeIsolates g 0]
  | depth + 1 => ((frontier g depth).flatMap (step g)).eraseDups

theorem advance {g : MaskGraph} {depth deleted next : Nat}
    (hd : deleted ∈ frontier g depth) (hs : next ∈ step g deleted) :
    next ∈ frontier g (depth + 1) := by
  rw [frontier, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨deleted, hd, hs⟩

theorem stay {g : MaskGraph} {depth deleted : Nat} (hd : deleted ∈ frontier g depth) :
    deleted ∈ frontier g (depth + 1) :=
  advance hd (by simp [step])

theorem advance_class {g : MaskGraph} {depth deleted vertex : Nat}
    (hd : deleted ∈ frontier g depth) (hv : vertex < g.width)
    (hlive : Nat.testBit deleted vertex = false)
    (hne : residualNeighbors g deleted vertex ≠ 0) :
    closeIsolates g (Nat.lor deleted (twinClass g deleted vertex)) ∈ frontier g (depth + 1) := by
  apply advance hd
  apply List.mem_cons_of_mem
  rw [List.mem_filterMap]
  refine ⟨vertex, List.mem_range.mpr hv, ?_⟩
  simp [hlive, hne]

def petersenNine : MaskGraph :=
  ⟨9, fun v => (#[50, 69, 138, 276, 9, 385, 258, 36, 104] : Array Nat)[v]?.getD 0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem petersen_nine_no_four : fullMask petersenNine ∉ frontier petersenNine 4 := by
  decide +kernel

end PetersenGroupBFS

namespace PetersenMaskBridge

open PetersenGroupBFS
open BranchGraph

def decode (g : MaskGraph) (mask : Nat) : Finset (Fin g.width) :=
  Finset.univ.filter (fun v => mask.testBit v.val)

@[simp] lemma mem_decode (g : MaskGraph) (mask : Nat) (v : Fin g.width) :
    v ∈ decode g mask ↔ mask.testBit v.val = true := by
  simp [decode]

@[simp] lemma decode_zero (g : MaskGraph) : decode g 0 = ∅ := by
  ext v
  simp

@[simp] lemma decode_full (g : MaskGraph) : decode g (fullMask g) = Finset.univ := by
  ext v
  simp [full_at, v.isLt]

lemma decode_or (g : MaskGraph) (a b : Nat) :
    decode g (Nat.lor a b) = decode g a ∪ decode g b := by
  ext v
  simp [Bool.or_eq_true]

lemma decode_inj (g : MaskGraph) {a b : Nat} (ha : a < bit g.width) (hb : b < bit g.width)
    (same : decode g a = decode g b) : a = b := by
  apply mask_ext ha hb
  intro w hw
  have hm : (⟨w, hw⟩ : Fin g.width) ∈ decode g a ↔ (⟨w, hw⟩ : Fin g.width) ∈ decode g b := by
    rw [same]
  simp only [mem_decode] at hm
  exact Bool.eq_iff_iff.mpr hm

lemma bit_pos (n : Nat) : 0 < bit n := by
  rw [bit_eq_power]
  exact Nat.two_pow_pos n

lemma full_bounded (g : MaskGraph) : fullMask g < bit g.width := by
  unfold fullMask
  have := bit_pos g.width
  omega

section Graph

variable (g : MaskGraph) (G : SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj : ∀ u v : Fin g.width, G.Adj u v ↔ (g.adjacency u.val).testBit v.val = true)

include adj in
lemma decode_neighbors (deleted : Nat) (u : Fin g.width) :
    decode g (residualNeighbors g deleted u.val) = neighborsAfter G (decode g deleted) u := by
  ext v
  cases h : deleted.testBit v.val <;>
    simp [mem_decode, neighborsAfter, neighbor_at g deleted u.val v.val v.isLt, adj, h]

include adj in
lemma residual_zero_iff (deleted : Nat) (bound : deleted < bit g.width) (u : Fin g.width) :
    residualNeighbors g deleted u.val = 0 ↔ neighborsAfter G (decode g deleted) u = ∅ := by
  constructor
  · intro h
    rw [← decode_neighbors g G adj, h, decode_zero]
  · intro h
    apply decode_inj g (neighbor_bounded g deleted u.val bound) (bit_pos g.width)
    rw [decode_neighbors g G adj, h, decode_zero]

include adj in
lemma decode_close (deleted : Nat) (bound : deleted < bit g.width) :
    decode g (PetersenGroupBFS.closeIsolates g deleted) = BranchGraph.closeIsolates G (decode g deleted) := by
  ext v
  simp [close_at, v.isLt, BranchGraph.closeIsolates, isolates, Bool.or_eq_true,
    residual_zero_iff g G adj deleted bound]

include adj in
lemma decode_class (deleted : Nat) (bound : deleted < bit g.width) (root : Fin g.width)
    (outside : root ∉ decode g deleted) (live : (neighborsAfter G (decode g deleted) root).Nonempty) :
    decode g (twinClass g deleted root.val) = maximalClass G (decode g deleted) root := by
  have same (u : Fin g.width) : residualNeighbors g deleted u.val = residualNeighbors g deleted root.val ↔
      neighborsAfter G (decode g deleted) u = neighborsAfter G (decode g deleted) root := by
    rw [← decode_neighbors g G adj deleted u, ← decode_neighbors g G adj deleted root]
    exact ⟨congrArg (decode g), decode_inj g (neighbor_bounded g deleted u.val bound)
      (neighbor_bounded g deleted root.val bound)⟩
  ext v
  cases h : deleted.testBit v.val <;>
    simp [class_at, v.isLt, maximalClass, outside, live, h, same, Bool.beq_eq_decide_eq]

def Represented (depth : Nat) (removed : Finset (Fin g.width)) : Prop :=
  ∃ m, m ∈ frontier g depth ∧ m < bit g.width ∧ decode g m = removed

include adj in
lemma initial_rep : Represented g 0 (BranchGraph.closeIsolates G ∅) := by
  refine ⟨PetersenGroupBFS.closeIsolates g 0, ?_,
    close_bounded g 0 (bit_pos g.width), ?_⟩
  · change PetersenGroupBFS.closeIsolates g 0 ∈ [PetersenGroupBFS.closeIsolates g 0]
    exact List.mem_cons_self
  · rw [decode_close g G adj _ (bit_pos g.width), decode_zero]

include adj in
lemma advance_rep {depth : Nat} {removed : Finset (Fin g.width)} (root : Fin g.width)
    (rep : Represented g depth removed) (closed : BranchGraph.closeIsolates G removed = removed) :
    Represented g (depth + 1) (removeClass G removed root) := by
  obtain ⟨m, hm, bounded, same⟩ := rep
  subst removed
  by_cases active : root ∉ decode g m ∧ (neighborsAfter G (decode g m) root).Nonempty
  · have live : m.testBit root.val = false := by
      cases h : m.testBit root.val
      · rfl
      · exact (active.1 ((mem_decode g m root).mpr h)).elim
    have someNeighbor : residualNeighbors g m root.val ≠ 0 := by
      intro h
      have none := (residual_zero_iff g G adj m bounded root).mp h
      simpa [none] using active.2
    have united := lor_bounded bounded (class_bounded g m root.val)
    refine ⟨PetersenGroupBFS.closeIsolates g (Nat.lor m (twinClass g m root.val)),
      advance_class hm root.isLt live someNeighbor, close_bounded g _ united, ?_⟩
    rw [decode_close g G adj _ united, decode_or, decode_class g G adj m bounded root active.1 active.2,
      removeClass]
  · have sameRemoval : removeClass G (decode g m) root = decode g m := by
      have emptyClass : maximalClass G (decode g m) root = ∅ := ite_eq_right active
      simp only [removeClass, emptyClass, Finset.union_empty, closed]
    exact ⟨m, stay hm, bounded, sameRemoval.symm⟩

include adj in
lemma simulate {count depth : Nat} {start finish : Finset (Fin g.width)}
    (walk : ClassSteps G count start finish) (initial : Represented g depth start)
    (closed : BranchGraph.closeIsolates G start = start) : Represented g (depth + count) finish := by
  induction count generalizing depth start with
  | zero =>
    change finish = start at walk
    simpa only [walk, Nat.add_zero] using initial
  | succ count ih =>
    obtain ⟨root, next⟩ := walk
    have nextClosed : BranchGraph.closeIsolates G (removeClass G start root) = removeClass G start root :=
      closeIsolates_idempotent G _
    have rest := ih next (advance_rep g G adj root initial closed) nextClosed
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using rest

lemma frontier_up {m k r : Nat} (reached : m ∈ frontier g k) (budget : k ≤ r) : m ∈ frontier g r := by
  induction r with
  | zero =>
    have : k = 0 := by omega
    simpa only [this] using reached
  | succ r ih =>
    by_cases eq : k = r + 1
    · simpa [eq] using reached
    · exact stay (ih (by omega))

include adj in
theorem groups_exceed_budget [Nonempty (Fin g.width)] (k : Nat) (noFinish : fullMask g ∉ frontier g k)
    (groups : List (Finset (Fin g.width))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : k < groups.length := by
  by_contra! budget
  have walk := covering_sequence_reaches_univ G groups twins finished
  obtain ⟨m, reached, bound, allGone⟩ :=
    simulate g G adj walk (initial_rep g G adj) (closeIsolates_idempotent G ∅)
  have equal : m = fullMask g := decode_inj g bound (full_bounded g) (by simpa using allGone)
  rw [equal, Nat.zero_add] at reached
  exact noFinish (frontier_up g reached budget)

end Graph

theorem petersen_nine_groups_need_five (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (adj : ∀ u v : Fin 9, G.Adj u v ↔ (petersenNine.adjacency u.val).testBit v.val = true)
    (groups : List (Finset (Fin 9))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : 5 ≤ groups.length :=
  @groups_exceed_budget petersenNine G (inferInstance : DecidableRel G.Adj) adj
    (inferInstance : Nonempty (Fin 9)) 4 petersen_nine_no_four groups twins finished

end PetersenMaskBridge

open PetersenNine

def petersenGraph : SimpleGraph Vertex := graph edges noLoops

def petersenAdjDecidable : DecidableRel petersenGraph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))

theorem petersen_graph_marked_edges (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S)) = true ↔
      BranchGraph.containsEdge petersenGraph S := by
  constructor
  · intro h
    obtain ⟨a, b, edge, ha, hb⟩ := (edgeFun_true edges _).mp h
    exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, Or.inl edge⟩
  · rintro ⟨a, ha, b, hb, adjacent⟩
    change (a, b) ∈ edges ∨ (b, a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, decide_eq_true ha, decide_eq_true hb⟩
    · exact ⟨b, a, edge, decide_eq_true hb, decide_eq_true ha⟩

theorem petersen_graph_matches_mask :
    ∀ a b : Vertex, petersenGraph.Adj a b ↔
      (PetersenGroupBFS.petersenNine.adjacency a.val).testBit b.val = true := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide

theorem petersen_graph_alternate_neighbors :
    ∀ i j : Vertex, petersenGraph.Adj i j →
      ∃ u v, petersenGraph.Adj i u ∧ petersenGraph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ petersenGraph.Adj u v := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs


def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace

theorem least_read_edge_live {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length), w ≠ (⟨out, outValid⟩ : Fin (n + gs.length)) → ∃ v, readEdge gs w v := by
  intro w notOutput
  have notSame : w.val ≠ out := fun eq => notOutput (Fin.ext eq)
  obtain ⟨p, g, atSlot, reads, bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p, bound⟩, p, g, atSlot, rfl, reads⟩

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]


def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut

def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut

theorem class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut ↔ label v = cut := by
  simp [classAt]

theorem classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut ↔ label v < cut := by
  simp [classesBefore]

theorem class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V, (∀ i ∈ I, label i = cut) →
      (∀ i ∈ O, cut < label i) → (BranchGraph.containsEdge G (I ∪ O) ↔ decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y := by
    have ne : label y ≠ cut := fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut := fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y ↔ decode (code {x}) {y}) := by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut := by
      have eq : i = x := Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i := by
      have eq : i = y := Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x} ≠ code ∅ := by
    obtain ⟨y, neighbor⟩ := active
    simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at neighbor
    have yLater := later xGroup neighbor.1 neighbor.2
    have yes := (single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one := (factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a := cannot u uGroup uActive
  have b := cannot v vGroup vActive
  have sameCode : code {u} = code {v} := by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, remains⟩
    have pos := later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_, remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge, remains⟩
    have pos := later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_, remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds CircuitProof
open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation

def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

theorem finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool, ∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) → (∀ i ∈ O, cut < label i) →
        (vl gs (setInput (I ∪ O)) out.val = true ↔ decode (code I) O) := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n), (∀ j ∈ J, label j = cut) ∧ code J = b ∧
      vl gs (setInput (J ∪ O)) out.val = true
  refine ⟨code, decode, ?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I, label i = cut) at groupI
  change (∀ i ∈ O, cut < label i) at afterO
  change (_ ↔ decode (code I) O)
  constructor
  · exact fun yes => ⟨I, groupI, rfl, yes⟩
  · rintro ⟨J, groupJ, sameCode, yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (K ∪ O)) cut.val = code K := by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput, absent]
    have sameCut : vl gs (setInput (I ∪ O)) cut.val = vl gs (setInput (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out := lt_of_le_of_ne prior atOutput
    have eq := circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut := by
        by_contra offGroup
        have notI : i ∉ I := fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J := fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput, notI, notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut := isGroup
      have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v := inputWire gs i) (w := out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b, avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1, h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]

open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace

theorem circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n), vl gs (setInput S) out.val = true ↔ BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (independent : BranchGraph.Independent G
      (classAt (fun i => FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)) cut)) :
    let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  obtain ⟨code, decode, factors⟩ := finite_branch_bit_factor clean out live cut prior terminal
  change BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut)
  exact class_twins_of_later_factor G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

abbrev petersenF := edgeFun edges

private theorem petersen_dependency_samples : ∀ v : Vertex, ∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i = w)) v
      (!(decide (v = w)))) ≠ petersenF (fun i => decide (i = w)) := by
  decide +kernel

theorem petersen_depends (v : Vertex) : Dep petersenF v := by
  obtain ⟨w, hw⟩ := petersen_dependency_samples v
  exact ⟨fun i => decide (i = w), hw⟩

theorem petersen_nonconstant : ∃ x y : Vertex → Bool, petersenF x ≠ petersenF y :=
  dep_nc (petersen_depends 0)

private theorem petersen_cofactor_samples : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b) = false ∧
    petersenF (Function.update (fun _ => true) v b) = true := by
  decide +kernel

theorem petersen_restrict_nonconstant (v : Vertex) (b : Bool) :
    ∃ x y, petersenF (Function.update x v b) ≠ petersenF (Function.update y v b) := by
  obtain ⟨no, yes⟩ := petersen_cofactor_samples v b
  exact ⟨fun _ => false, fun _ => true, by rw [no, yes]; decide⟩


lemma petersenF_graph_edges (x : Fin 9 → Bool) : petersenF x = true ↔
    ∃ u v : Fin 9, petersenGraph.Adj u v ∧ x u = true ∧ x v = true := by
  change PetersenNine.edgeFun PetersenNine.edges x = true ↔ _
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a, b, edge, ha, hb⟩
    exact ⟨a, b, Or.inl edge, ha, hb⟩
  · rintro ⟨a, b, adjacent, ha, hb⟩
    change (a, b) ∈ PetersenNine.edges ∨ (b, a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, ha, hb⟩
    · exact ⟨b, a, edge, hb, ha⟩

lemma least_petersen_output_valid {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv petersen_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

theorem least_petersen_five_branches (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    : 5 ≤ (circuitBranchWires (n := 9) gs).card := by
  classical
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  have outValid := least_petersen_output_valid least
  let outWire : Fin (9 + gs.length) := ⟨out, outValid⟩
  have live := least_read_edge_live least petersen_nonconstant petersen_depends petersen_restrict_nonconstant outValid
  let label : Fin 9 → Fin (9 + gs.length) := firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)) := circuitBranchWires gs
  have computes (x : Fin 9 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue petersenGraph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 9)) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge petersenGraph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact petersen_graph_marked_edges S
  have independent (r) : BranchGraph.Independent petersenGraph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least petersen_nonconstant)
      petersenGraph computes petersen_graph_alternate_neighbors r
  have labels (v : Fin 9) : label v = outWire ∨ label v ∈ branches := by
    have stopped := FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (in_circuit_branches.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup petersenGraph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live petersenGraph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member)) (independent r)
  exact BranchGroupsLean.roots_required petersenGraph label outWire branches 5 labels before twins
    (independent outWire) (PetersenMaskBridge.petersen_nine_groups_need_five petersenGraph petersen_graph_matches_mask)

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega

lemma nonNotCount_replace_not (gs : List Gate) (p : ℕ) (hp : p < gs.length)
    (hn : gs[p].op = .not) :
    nonNotCount (gs.set p ⟨.and, []⟩) = nonNotCount gs + 1 := by
  simp [nonNotCount, List.countP_set hp, hn, isNotGate]

lemma nonNotCount_three_not (gs : List Gate) (i j k : Fin gs.length)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (gs.get i).op = .not) (hj : (gs.get j).op = .not)
    (hk : (gs.get k).op = .not) : nonNotCount gs + 3 ≤ gs.length := by
  let g : Gate := ⟨.and, []⟩
  let gs' := gs.set i.val g
  let gs'' := gs'.set j.val g
  let gs''' := gs''.set k.val g
  have hj' : j.val < gs'.length := by simpa [gs'] using j.isLt
  have hk' : k.val < gs'.length := by simpa [gs'] using k.isLt
  have hk'' : k.val < gs''.length := by simpa [gs''] using hk'
  have cmp_i := nonNotCount_replace_not gs i.val i.isLt hi
  have cmp_j := nonNotCount_replace_not gs' j.val hj' (by
    rw [show gs'[j.val] = gs[j.val] from List.getElem_set_ne (fun h => hij (Fin.ext h)) hj']
    exact hj)
  have cmp_k := nonNotCount_replace_not gs'' k.val hk'' (by
    rw [show gs''[k.val] = gs'[k.val] from List.getElem_set_ne (fun h => hjk (Fin.ext h)) hk'',
        show gs'[k.val] = gs[k.val] from List.getElem_set_ne (fun h => hik (Fin.ext h)) hk']
    exact hk)
  change nonNotCount gs' = nonNotCount gs + 1 at cmp_i
  change nonNotCount gs'' = nonNotCount gs' + 1 at cmp_j
  change nonNotCount gs''' = nonNotCount gs'' + 1 at cmp_k
  have hbound : nonNotCount gs''' ≤ gs.length := by
    simpa [nonNotCount, gs''', gs'', gs', g] using
      (List.countP_le_length (p := fun q : Gate => !(isNotGate q.op)) (l := gs'''))
  omega

theorem petersen_binary_lower (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x : Vertex → Bool, C.eval (List.ofFn x) = petersenF x) :
    13 ≤ nonNotCount C.gates := by
  obtain ⟨gs, o, least, budget⟩ := least_with_budget C hfan he petersen_nonconstant
  have valid := least_petersen_output_valid least
  have live := least_read_edge_live least petersen_nonconstant petersen_depends
    petersen_restrict_nonconstant valid
  let branches := circuitBranchWires (n := 9) gs
  have branchLower : 5 ≤ branches.card := least_petersen_five_branches gs o least
  have branchBudget := branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at countTotal
  omega




open PEqualNP.CircuitLowerBounds CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

theorem threeForksOfBudget {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (budget : nonNotCount gs ≤ 12) : (circuitBranchWires (n := 10) gs).card ≤ 3 := by
  classical
  let branches := circuitBranchWires (n := 10) gs
  have h := branching_budget clean out.isLt (fun w hw hne => by
      let wire : Fin (10 + gs.length) := ⟨w, hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩ := live wire (fun e => hne (congrArg Fin.val e))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  have count := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at count
  change branches.card ≤ 3
  omega

namespace Suffix2770

def F (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def plug (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := Fin.lastCases b x

lemma plug_list (x : Fin 9 → Bool) (b : Bool) :
    List.ofFn (plug x b) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ_last]
  simp [plug]
  rfl

def nonNot : GateOp → Bool
  | .not => false
  | _ => true

def binary (gs : List Gate) := gs.countP (fun g => nonNot g.op)


open PetersenNine

lemma binary_eq (gs : List Gate) : binary gs = nonNotCount gs := by
  change List.countP (fun g : Gate => nonNot g.op) gs = List.countP (fun g : Gate => !(isNotGate g.op)) gs
  congr 1
  funext g
  cases g.op <;> rfl

lemma lower (B : Circuit) (fan : FanInTwo B) (hfun : circuitFun 9 B = F) : 13 ≤ binary B.gates := by
  rw [binary_eq]
  apply petersen_binary_lower B fan
  intro x
  have hx := congrFun hfun x
  simpa only [circuitFun,F,petersenF,edgeFun,edges,List.any_cons,List.any_nil,
    Bool.or_false,Bool.or_assoc] using hx

lemma dep_of_pair {n : ℕ} {H : (Fin n → Bool) → Bool} {i : Fin n}
    (hd : ∃ p q : Fin n → Bool, (∀ j, j ≠ i → p j = q j) ∧ H p ≠ H q) : Dep H i := by
  obtain ⟨p,q,ha,hf⟩ := hd
  have ne : p i ≠ q i := by
    intro hp
    have eq : p = q := funext (fun j => by
      by_cases h : j = i
      · simpa only [h] using hp
      · exact ha j h)
    exact hf (congrArg H eq)
  have hi : (!p i) = q i := by cases hp : p i <;> cases hq : q i <;> simp_all
  have up : Function.update p i (!p i) = q := by
    funext j
    by_cases h : j = i
    · simpa only [h, Function.update_self] using hi
    · simpa only [Function.update_of_ne h] using ha j h
  exact ⟨p, by simpa only [up] using hf.symm⟩


end Suffix2770

namespace Or02Rank

def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def valid (x : Fin 10 → Bool) : Prop := x 9 = (x 0 || x 2)

def conflicts : List (Fin 10 × Fin 10) := [(3,4), (0,5), (1,6), (5,7), (3,8), (5,8), (6,8)]

def row (m : ℕ) (i : Fin 10) : Bool := m.testBit i.val

def cube (i j k : Fin 10) (a b c : ℕ) : Prop :=
  let hi m := Function.update (row m) k true
  (∀ v, v ≠ i → v ≠ j → row a v = row b v ∧ row b v = row c v) ∧
  valid (row a) ∧ valid (row b) ∧ valid (hi a) ∧ valid (hi b) ∧ valid (hi c) ∧
  target (row a) ≠ target (row b) ∧ target (hi a) ≠ target (hi c) ∧ target (hi b) ≠ target (hi c)

def Cut (label : Fin 10 → Fin 4) (t : Fin 4) : Prop :=
  ∃ code : (Fin 10 → Bool) → Bool,
    (∀ x y, (∀ i, label i ≤ t → x i = y i) → code x = code y) ∧
    (∀ x y, valid x → valid y → (∀ i, label i ≠ t → x i = y i) →
      code x = code y → target x = target y)

lemma cubeBound (label : Fin 10 → Fin 4) (cut : ∀ t, t < 3 → Cut label t)
    (i j k : Fin 10) (a b c : ℕ) (hw : cube i j k a b c) :
    label i = label j → label k ≤ label i := by
  intro hh
  by_contra hle
  have hlt : label i < label k := lt_of_not_ge hle
  have h3 : label i < 3 := by omega
  obtain ⟨code, low, high⟩ := cut (label i) h3
  obtain ⟨same, va, vb, vha, vhb, vhc, nab, nac, nbc⟩ := hw
  let hi (m : ℕ) := Function.update (row m) k true
  have aux (m : ℕ) : code (hi m) = code (row m) := by
    apply low
    intro u hu
    have hne : u ≠ k := by
      rintro rfl
      exact (not_le_of_gt hlt) hu
    exact Function.update_of_ne hne _ _
  have off {u} (h : label u ≠ label i) : u ≠ i ∧ u ≠ j := by
    constructor
    · exact fun he => h (he ▸ rfl)
    · exact fun he => h (he ▸ hh.symm)
  have hab : code (row a) ≠ code (row b) := fun e =>
    nab (high _ _ va vb (fun u hu => (same u (off hu).1 (off hu).2).1) e)
  have lift {m n : ℕ} (h : ∀ u, label u ≠ label i → row m u = row n u) :
      ∀ u, label u ≠ label i → hi m u = hi n u := by
    intro u hu
    by_cases eq : u = k
    · subst u; simp [hi]
    · simpa [hi, Function.update_of_ne eq] using h u hu
  have hac : code (row a) ≠ code (row c) := fun e =>
    nac (high _ _ vha vhc (lift (fun u hu => ((same u (off hu).1 (off hu).2).1).trans
      (same u (off hu).1 (off hu).2).2)) ((aux a).trans (e.trans (aux c).symm)))
  have hbc : code (row b) ≠ code (row c) := fun e =>
    nbc (high _ _ vhb vhc (lift (fun u hu => (same u (off hu).1 (off hu).2).2))
      ((aux b).trans (e.trans (aux c).symm)))
  cases ha : code (row a) <;> cases hb : code (row b) <;> cases hc : code (row c) <;> simp_all

set_option maxHeartbeats 0 in
lemma shape_fin (v0 v1 v2 v3 v4 v5 v6 v7 v8 : Fin 4)
    (p34 : v3 ≠ v4)
    (p05 : v0 ≠ v5)
    (p16 : v1 ≠ v6)
    (p57 : v5 ≠ v7)
    (p38 : v3 ≠ v8)
    (p58 : v5 ≠ v8)
    (p68 : v6 ≠ v8)
    (q034 : v0 = v3 → v4 ≤ v0)
    (q068 : v0 = v6 → v8 ≤ v0)
    (q132 : v1 = v3 → v2 ≤ v1)
    (q136 : v1 = v3 → v6 ≤ v1)
    (q146 : v1 = v4 → v6 ≤ v1)
    (q157 : v1 = v5 → v7 ≤ v1)
    (q176 : v1 = v7 → v6 ≤ v1)
    (q186 : v1 = v8 → v6 ≤ v1)
    (q238 : v2 = v3 → v8 ≤ v2)
    (q257 : v2 = v5 → v7 ≤ v2)
    (q268 : v2 = v6 → v8 ≤ v2)
    (q354 : v3 = v5 → v4 ≤ v3)
    (q357 : v3 = v5 → v7 ≤ v3)
    (q361 : v3 = v6 → v1 ≤ v3)
    (q368 : v3 = v6 → v8 ≤ v3)
    (q374 : v3 = v7 → v4 ≤ v3)
    (q457 : v4 = v5 → v7 ≤ v4)
    (q460 : v4 = v6 → v0 ≤ v4)
    (q463 : v4 = v6 → v3 ≤ v4)
    (q473 : v4 = v7 → v3 ≤ v4)
    (q483 : v4 = v8 → v3 ≤ v4)
    (q567 : v5 = v6 → v7 ≤ v5)
    (q568 : v5 = v6 → v8 ≤ v5)
    (q671 : v6 = v7 → v1 ≤ v6)
    (q785 : v7 = v8 → v5 ≤ v7)
    : v0 = 3 ∧ v1 = 3 ∧ v2 = 3 ∧ v4 = 3 ∧ v7 = 3 ∧ v8 = 3 ∧ v3 < 3 ∧ v5 < 3 ∧ v6 < 3 ∧ v3 ≠ v5 ∧ v3 ≠ v6 ∧ v5 ≠ v6 := by
  fin_cases v6
  · fin_cases v7
    · fin_cases v1
      · exact (False.elim (p16 rfl))
      · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q671 rfl)))
      · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q671 rfl)))
      · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q671 rfl)))
    · fin_cases v3
      · fin_cases v8
        · exact (False.elim (p38 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q368 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q368 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q368 rfl)))
      · fin_cases v4
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q463 rfl)))
        · exact (False.elim (p34 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q374 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q374 rfl)))
      · fin_cases v5
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q567 rfl)))
        · exact (False.elim (p57 rfl))
        · fin_cases v4
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q463 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q473 rfl)))
          · exact (False.elim (p34 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q354 rfl)))
        · fin_cases v8
          · exact (False.elim (p68 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q785 rfl)))
          · exact (False.elim (p38 rfl))
          · exact (False.elim (p58 rfl))
      · fin_cases v8
        · exact (False.elim (p68 rfl))
        · fin_cases v5
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q567 rfl)))
          · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q785 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q785 rfl)))
        · fin_cases v4
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q463 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q473 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q483 rfl)))
          · exact (False.elim (p34 rfl))
        · exact (False.elim (p38 rfl))
    · fin_cases v5
      · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q567 rfl)))
      · fin_cases v3
        · fin_cases v8
          · exact (False.elim (p38 rfl))
          · exact (False.elim (p58 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q368 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q368 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q357 rfl)))
        · fin_cases v4
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q463 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q457 rfl)))
          · exact (False.elim (p34 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q374 rfl)))
        · fin_cases v4
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q463 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q457 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q473 rfl)))
          · exact (False.elim (p34 rfl))
      · exact (False.elim (p57 rfl))
      · fin_cases v8
        · exact (False.elim (p68 rfl))
        · fin_cases v3
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q368 rfl)))
          · exact (False.elim (p38 rfl))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q463 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q483 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q463 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q473 rfl)))
            · exact (False.elim (p34 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q785 rfl)))
        · exact (False.elim (p58 rfl))
    · fin_cases v5
      · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q567 rfl)))
      · fin_cases v8
        · exact (False.elim (p68 rfl))
        · exact (False.elim (p58 rfl))
        · fin_cases v3
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q368 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q357 rfl)))
          · exact (False.elim (p38 rfl))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q463 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q457 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q483 rfl)))
            · exact (False.elim (p34 rfl))
        · fin_cases v3
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q368 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q357 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q463 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q457 rfl)))
            · exact (False.elim (p34 rfl))
            · fin_cases v0
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q068 rfl)))
              · exact (False.elim (p05 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q034 rfl)))
              · fin_cases v2
                · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q268 rfl)))
                · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q257 rfl)))
                · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q238 rfl)))
                · fin_cases v1
                  · exact (False.elim (p16 rfl))
                  · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q157 rfl)))
                  · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q132 rfl)))
                  · exact (by decide)
          · exact (False.elim (p38 rfl))
      · fin_cases v8
        · exact (False.elim (p68 rfl))
        · fin_cases v3
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q368 rfl)))
          · exact (False.elim (p38 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q357 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q463 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q457 rfl)))
            · exact (False.elim (p34 rfl))
        · exact (False.elim (p58 rfl))
        · fin_cases v3
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q368 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q463 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q457 rfl)))
            · fin_cases v0
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q068 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q034 rfl)))
              · exact (False.elim (p05 rfl))
              · fin_cases v2
                · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q268 rfl)))
                · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q238 rfl)))
                · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q257 rfl)))
                · fin_cases v1
                  · exact (False.elim (p16 rfl))
                  · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q132 rfl)))
                  · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q157 rfl)))
                  · exact (by decide)
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q357 rfl)))
          · exact (False.elim (p38 rfl))
      · exact (False.elim (p57 rfl))
  · fin_cases v3
    · fin_cases v7
      · fin_cases v4
        · exact (False.elim (p34 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q374 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q374 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q374 rfl)))
      · fin_cases v1
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q136 rfl)))
        · exact (False.elim (p16 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q671 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q671 rfl)))
      · fin_cases v5
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q357 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q567 rfl)))
        · exact (False.elim (p57 rfl))
        · fin_cases v8
          · exact (False.elim (p38 rfl))
          · exact (False.elim (p68 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q785 rfl)))
          · exact (False.elim (p58 rfl))
      · fin_cases v5
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q357 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q567 rfl)))
        · fin_cases v8
          · exact (False.elim (p38 rfl))
          · exact (False.elim (p68 rfl))
          · exact (False.elim (p58 rfl))
          · fin_cases v4
            · exact (False.elim (p34 rfl))
            · fin_cases v0
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q034 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q068 rfl)))
              · exact (False.elim (p05 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q460 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q457 rfl)))
            · fin_cases v1
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q136 rfl)))
              · exact (False.elim (p16 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q157 rfl)))
              · fin_cases v0
                · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q034 rfl)))
                · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q068 rfl)))
                · exact (False.elim (p05 rfl))
                · fin_cases v2
                  · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q238 rfl)))
                  · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q268 rfl)))
                  · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q257 rfl)))
                  · exact (by decide)
        · exact (False.elim (p57 rfl))
    · fin_cases v8
      · fin_cases v1
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q186 rfl)))
        · exact (False.elim (p16 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q361 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q361 rfl)))
      · exact (False.elim (p38 rfl))
      · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q368 rfl)))
      · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q368 rfl)))
    · fin_cases v8
      · fin_cases v7
        · fin_cases v5
          · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q785 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q785 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q785 rfl)))
        · fin_cases v1
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q186 rfl)))
          · exact (False.elim (p16 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q671 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q671 rfl)))
        · fin_cases v4
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q483 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q463 rfl)))
          · exact (False.elim (p34 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q374 rfl)))
        · fin_cases v5
          · exact (False.elim (p58 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q567 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q357 rfl)))
          · exact (False.elim (p57 rfl))
      · exact (False.elim (p68 rfl))
      · exact (False.elim (p38 rfl))
      · fin_cases v5
        · fin_cases v7
          · exact (False.elim (p57 rfl))
          · fin_cases v1
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q157 rfl)))
            · exact (False.elim (p16 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q671 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q671 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q457 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q463 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q457 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q463 rfl)))
            · exact (False.elim (p34 rfl))
            · fin_cases v0
              · exact (False.elim (p05 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q068 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q034 rfl)))
              · fin_cases v2
                · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q257 rfl)))
                · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q268 rfl)))
                · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q238 rfl)))
                · fin_cases v1
                  · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q157 rfl)))
                  · exact (False.elim (p16 rfl))
                  · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q132 rfl)))
                  · exact (by decide)
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q568 rfl)))
        · fin_cases v4
          · fin_cases v7
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q473 rfl)))
            · fin_cases v1
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q146 rfl)))
              · exact (False.elim (p16 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q671 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q671 rfl)))
            · exact (False.elim (p57 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q357 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q463 rfl)))
          · exact (False.elim (p34 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q354 rfl)))
        · exact (False.elim (p58 rfl))
    · fin_cases v8
      · fin_cases v4
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q483 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q463 rfl)))
        · fin_cases v7
          · fin_cases v5
            · exact (False.elim (p57 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q785 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q785 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q785 rfl)))
          · fin_cases v1
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q186 rfl)))
            · exact (False.elim (p16 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q671 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q671 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q473 rfl)))
          · fin_cases v5
            · exact (False.elim (p58 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q567 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q457 rfl)))
            · exact (False.elim (p57 rfl))
        · exact (False.elim (p34 rfl))
      · exact (False.elim (p68 rfl))
      · fin_cases v4
        · fin_cases v5
          · fin_cases v7
            · exact (False.elim (p57 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q457 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q457 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q457 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q568 rfl)))
          · exact (False.elim (p58 rfl))
          · fin_cases v7
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q473 rfl)))
            · fin_cases v1
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q146 rfl)))
              · exact (False.elim (p16 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q671 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q671 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q785 rfl)))
            · exact (False.elim (p57 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q463 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q483 rfl)))
        · exact (False.elim (p34 rfl))
      · exact (False.elim (p38 rfl))
  · fin_cases v8
    · fin_cases v7
      · fin_cases v5
        · exact (False.elim (p57 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q785 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q785 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q785 rfl)))
      · fin_cases v3
        · exact (False.elim (p38 rfl))
        · fin_cases v4
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q483 rfl)))
          · exact (False.elim (p34 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q374 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q374 rfl)))
        · fin_cases v1
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q186 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q176 rfl)))
          · exact (False.elim (p16 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q361 rfl)))
        · fin_cases v4
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q483 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q473 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q463 rfl)))
          · exact (False.elim (p34 rfl))
      · fin_cases v1
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q186 rfl)))
        · fin_cases v3
          · exact (False.elim (p38 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q136 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q146 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q463 rfl)))
            · exact (False.elim (p34 rfl))
        · exact (False.elim (p16 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q671 rfl)))
      · fin_cases v5
        · exact (False.elim (p58 rfl))
        · fin_cases v3
          · exact (False.elim (p38 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q357 rfl)))
          · fin_cases v1
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q186 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q157 rfl)))
            · exact (False.elim (p16 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q361 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q457 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q463 rfl)))
            · exact (False.elim (p34 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q567 rfl)))
        · exact (False.elim (p57 rfl))
    · fin_cases v3
      · fin_cases v7
        · fin_cases v4
          · exact (False.elim (p34 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q374 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q374 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q374 rfl)))
        · fin_cases v5
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q357 rfl)))
          · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q785 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q785 rfl)))
        · fin_cases v1
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q136 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q186 rfl)))
          · exact (False.elim (p16 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q671 rfl)))
        · fin_cases v5
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q357 rfl)))
          · exact (False.elim (p58 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q567 rfl)))
          · exact (False.elim (p57 rfl))
      · exact (False.elim (p38 rfl))
      · fin_cases v1
        · fin_cases v7
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q176 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q157 rfl)))
            · exact (False.elim (p57 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q785 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q785 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q483 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q157 rfl)))
            · exact (False.elim (p58 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q357 rfl)))
            · exact (False.elim (p57 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q186 rfl)))
        · exact (False.elim (p16 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q361 rfl)))
      · fin_cases v4
        · fin_cases v7
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q473 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q457 rfl)))
            · exact (False.elim (p57 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q785 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q785 rfl)))
          · fin_cases v1
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q186 rfl)))
            · exact (False.elim (p16 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q671 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q457 rfl)))
            · exact (False.elim (p58 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q567 rfl)))
            · exact (False.elim (p57 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q483 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q463 rfl)))
        · exact (False.elim (p34 rfl))
    · exact (False.elim (p68 rfl))
    · fin_cases v3
      · fin_cases v5
        · fin_cases v7
          · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q357 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q357 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q357 rfl)))
        · fin_cases v7
          · fin_cases v4
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q374 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q374 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q374 rfl)))
          · exact (False.elim (p57 rfl))
          · fin_cases v1
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q136 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q157 rfl)))
            · exact (False.elim (p16 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q671 rfl)))
          · fin_cases v4
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q457 rfl)))
            · fin_cases v0
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q034 rfl)))
              · exact (False.elim (p05 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q068 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q460 rfl)))
            · fin_cases v1
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q136 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q157 rfl)))
              · exact (False.elim (p16 rfl))
              · fin_cases v0
                · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q034 rfl)))
                · exact (False.elim (p05 rfl))
                · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q068 rfl)))
                · fin_cases v2
                  · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q238 rfl)))
                  · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q257 rfl)))
                  · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q268 rfl)))
                  · exact (by decide)
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q568 rfl)))
        · exact (False.elim (p58 rfl))
      · fin_cases v5
        · fin_cases v7
          · exact (False.elim (p57 rfl))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q457 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q374 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v1
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q157 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q136 rfl)))
            · exact (False.elim (p16 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q671 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q457 rfl)))
            · exact (False.elim (p34 rfl))
            · fin_cases v0
              · exact (False.elim (p05 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q034 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q068 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q460 rfl)))
            · fin_cases v1
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q157 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q136 rfl)))
              · exact (False.elim (p16 rfl))
              · fin_cases v0
                · exact (False.elim (p05 rfl))
                · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q034 rfl)))
                · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q068 rfl)))
                · fin_cases v2
                  · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q257 rfl)))
                  · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q238 rfl)))
                  · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q268 rfl)))
                  · exact (by decide)
        · fin_cases v7
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q473 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q354 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q354 rfl)))
          · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q357 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q357 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q568 rfl)))
        · exact (False.elim (p58 rfl))
      · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q368 rfl)))
      · exact (False.elim (p38 rfl))
  · fin_cases v8
    · fin_cases v7
      · fin_cases v5
        · exact (False.elim (p57 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q785 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q785 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q785 rfl)))
      · fin_cases v1
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q186 rfl)))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q176 rfl)))
        · fin_cases v3
          · exact (False.elim (p38 rfl))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q483 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q374 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q136 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q473 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim (p34 rfl))
        · exact (False.elim (p16 rfl))
      · fin_cases v1
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q186 rfl)))
        · fin_cases v3
          · exact (False.elim (p38 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q136 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q473 rfl)))
            · exact (False.elim (p34 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q176 rfl)))
        · exact (False.elim (p16 rfl))
      · fin_cases v5
        · exact (False.elim (p58 rfl))
        · fin_cases v1
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q186 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q157 rfl)))
          · fin_cases v3
            · exact (False.elim (p38 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q357 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q136 rfl)))
            · fin_cases v4
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q483 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q457 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q146 rfl)))
              · exact (False.elim (p34 rfl))
          · exact (False.elim (p16 rfl))
        · fin_cases v1
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q186 rfl)))
          · fin_cases v3
            · exact (False.elim (p38 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q136 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q357 rfl)))
            · fin_cases v4
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q483 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q146 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q457 rfl)))
              · exact (False.elim (p34 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q157 rfl)))
          · exact (False.elim (p16 rfl))
        · exact (False.elim (p57 rfl))
    · fin_cases v1
      · fin_cases v7
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q176 rfl)))
        · fin_cases v5
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q157 rfl)))
          · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q785 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q785 rfl)))
        · fin_cases v3
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q136 rfl)))
          · exact (False.elim (p38 rfl))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q483 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q483 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q473 rfl)))
            · exact (False.elim (p34 rfl))
        · fin_cases v5
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q157 rfl)))
          · exact (False.elim (p58 rfl))
          · fin_cases v3
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q136 rfl)))
            · exact (False.elim (p38 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q357 rfl)))
            · fin_cases v4
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q146 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q483 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q457 rfl)))
              · exact (False.elim (p34 rfl))
          · exact (False.elim (p57 rfl))
      · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q186 rfl)))
      · fin_cases v3
        · fin_cases v7
          · fin_cases v4
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q374 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q357 rfl)))
            · exact (False.elim (p57 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q785 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q785 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q176 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q357 rfl)))
            · exact (False.elim (p58 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q157 rfl)))
            · exact (False.elim (p57 rfl))
        · exact (False.elim (p38 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q136 rfl)))
        · fin_cases v4
          · fin_cases v7
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q473 rfl)))
            · fin_cases v5
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 1)) (q457 rfl)))
              · exact (False.elim (p57 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q785 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q785 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q176 rfl)))
            · fin_cases v5
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q457 rfl)))
              · exact (False.elim (p58 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q157 rfl)))
              · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q483 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q146 rfl)))
          · exact (False.elim (p34 rfl))
      · exact (False.elim (p16 rfl))
    · fin_cases v1
      · fin_cases v3
        · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q136 rfl)))
        · fin_cases v7
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q176 rfl)))
          · fin_cases v4
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q374 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q374 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q157 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q357 rfl)))
            · exact (False.elim (p57 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q785 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q157 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q357 rfl)))
            · exact (False.elim (p58 rfl))
            · exact (False.elim (p57 rfl))
        · exact (False.elim (p38 rfl))
        · fin_cases v4
          · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q146 rfl)))
          · fin_cases v7
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q176 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q473 rfl)))
            · fin_cases v5
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q157 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q457 rfl)))
              · exact (False.elim (p57 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q785 rfl)))
            · fin_cases v5
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q157 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q457 rfl)))
              · exact (False.elim (p58 rfl))
              · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q483 rfl)))
          · exact (False.elim (p34 rfl))
      · fin_cases v3
        · fin_cases v7
          · fin_cases v4
            · exact (False.elim (p34 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q146 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q374 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q374 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q176 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q357 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q157 rfl)))
            · exact (False.elim (p57 rfl))
            · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q785 rfl)))
          · fin_cases v5
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q357 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q157 rfl)))
            · exact (False.elim (p58 rfl))
            · exact (False.elim (p57 rfl))
        · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q136 rfl)))
        · exact (False.elim (p38 rfl))
        · fin_cases v4
          · fin_cases v7
            · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q473 rfl)))
            · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q176 rfl)))
            · fin_cases v5
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 2)) (q457 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 2)) (q157 rfl)))
              · exact (False.elim (p57 rfl))
              · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q785 rfl)))
            · fin_cases v5
              · exact (False.elim ((not_le_of_gt (by decide : (0 : Fin 4) < 3)) (q457 rfl)))
              · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q157 rfl)))
              · exact (False.elim (p58 rfl))
              · exact (False.elim (p57 rfl))
          · exact (False.elim ((not_le_of_gt (by decide : (1 : Fin 4) < 3)) (q146 rfl)))
          · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q483 rfl)))
          · exact (False.elim (p34 rfl))
      · exact (False.elim ((not_le_of_gt (by decide : (2 : Fin 4) < 3)) (q186 rfl)))
      · exact (False.elim (p16 rfl))
    · exact (False.elim (p68 rfl))

def Shape (r : Fin 10 → Fin 4) : Prop :=
    r 0 = 3 ∧ r 1 = 3 ∧ r 2 = 3 ∧ r 4 = 3 ∧ r 7 = 3 ∧ r 8 = 3 ∧
      r 3 < 3 ∧ r 5 < 3 ∧ r 6 < 3 ∧ r 3 ≠ r 5 ∧ r 3 ≠ r 6 ∧ r 5 ≠ r 6

theorem shapes (label : Fin 10 → Fin 4)
    (conf : ∀ e ∈ conflicts, label e.1 ≠ label e.2)
    (cut : ∀ t, t < 3 → Cut label t) : Shape label := by
  have hcf (i j : Fin 10) (hm : (i,j) ∈ conflicts) : label i ≠ label j := conf (i,j) hm
  have hbound (i j k : Fin 10) (a b c : ℕ) (hw : cube i j k a b c) :
      label i = label j → label k ≤ label i := fun h => cubeBound label cut i j k a b c hw h
  exact shape_fin (label 0) (label 1) (label 2) (label 3) (label 4) (label 5) (label 6) (label 7) (label 8)
    (hcf 3 4 (by decide))
    (hcf 0 5 (by decide))
    (hcf 1 6 (by decide))
    (hcf 5 7 (by decide))
    (hcf 3 8 (by decide))
    (hcf 5 8 (by decide))
    (hcf 6 8 (by decide))
    (hbound 0 3 4 517 525 516 (by unfold cube valid row target; decide))
    (hbound 0 6 8 533 596 532 (by unfold cube valid row target; decide))
    (hbound 1 3 2 515 521 513 (by unfold cube valid row target; decide))
    (hbound 1 3 6 18 26 16 (by unfold cube valid row target; decide))
    (hbound 1 4 6 10 26 8 (by unfold cube valid row target; decide))
    (hbound 1 5 7 66 96 64 (by unfold cube valid row target; decide))
    (hbound 1 7 6 34 162 32 (by unfold cube valid row target; decide))
    (hbound 1 8 6 515 769 513 (by unfold cube valid row target; decide))
    (hbound 2 3 8 521 525 513 (by unfold cube valid row target; decide))
    (hbound 2 5 7 517 549 513 (by unfold cube valid row target; decide))
    (hbound 2 6 8 645 705 641 (by unfold cube valid row target; decide))
    (hbound 3 5 4 136 168 128 (by unfold cube valid row target; decide))
    (hbound 3 5 7 24 48 16 (by unfold cube valid row target; decide))
    (hbound 3 6 1 24 80 16 (by unfold cube valid row target; decide))
    (hbound 3 6 8 10 74 2 (by unfold cube valid row target; decide))
    (hbound 3 7 4 40 168 32 (by unfold cube valid row target; decide))
    (hbound 4 5 7 24 40 8 (by unfold cube valid row target; decide))
    (hbound 4 6 0 788 852 772 (by unfold cube valid row target; decide))
    (hbound 4 6 3 18 82 2 (by unfold cube valid row target; decide))
    (hbound 4 7 3 48 176 32 (by unfold cube valid row target; decide))
    (hbound 4 8 3 529 769 513 (by unfold cube valid row target; decide))
    (hbound 5 6 7 34 98 2 (by unfold cube valid row target; decide))
    (hbound 5 6 8 545 577 513 (by unfold cube valid row target; decide))
    (hbound 6 7 1 96 224 32 (by unfold cube valid row target; decide))
    (hbound 7 8 5 644 772 516 (by unfold cube valid row target; decide))

end Or02Rank

namespace Or02Attempt
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2519
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
open Or02Rank

theorem preciseCuts {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (hcard : (circuitBranchWires (n := n) gs).card ≤ 3) :
    ∃ label : Fin n → Fin 4,
      (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
      (∀ i, label i = 3 → firstInputBoundary clean out live i = out) ∧
      (∀ i j, label i ≤ label j ↔ firstInputBoundary clean out live i ≤ firstInputBoundary clean out live j) ∧
      (∀ k : Fin 4, ∃ code : (Fin n → Bool) → Bool,
        (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
        (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → vl gs x out.val = vl gs y out.val)) := by
  classical
  let branches := circuitBranchWires (n := n) gs
  change branches.card ≤ 3 at hcard
  let cuts := insert out branches
  have small : cuts.card ≤ 4 := (Finset.card_insert_le ..).trans (by omega)
  let boundary := firstInputBoundary clean out live
  have mem (i : Fin n) : boundary i ∈ cuts := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i)
      with ho | hb
    · exact Finset.mem_insert.mpr (Or.inl ho)
    · exact Finset.mem_insert.mpr (Or.inr (in_circuit_branches.mpr hb))
  let embed := (cuts.orderIsoOfFin rfl).symm
  let rank (c : cuts) : Fin 4 :=
    ⟨4 - cuts.card + (embed c).val, by have := (embed c).isLt; omega⟩
  have strict : StrictMono rank := by
    intro c d hcd
    have he := embed.strictMono hcd
    change (embed c).val < (embed d).val at he
    change 4 - cuts.card + (embed c).val < 4 - cuts.card + (embed d).val
    omega
  let loc (i : Fin n) : cuts := ⟨boundary i, mem i⟩
  let label (i : Fin n) := rank (loc i)
  have eqv (i j : Fin n) : label i = label j ↔ boundary i = boundary j := by
    change rank (loc i) = rank (loc j) ↔ (loc i).val = (loc j).val
    rw [strict.injective.eq_iff, Subtype.ext_iff]
  have leq (i j : Fin n) : label i ≤ label j ↔ boundary i ≤ boundary j := by
    change rank (loc i) ≤ rank (loc j) ↔ loc i ≤ loc j
    exact strict.le_iff_le
  have last (i : Fin n) (hr : label i = 3) : boundary i = out := by
    let j : cuts := ⟨out,Finset.mem_insert_self _ _⟩
    have hj : rank (loc i) ≤ rank j := strict.monotone (wire_le_output clean out live (boundary i))
    have hh : (3 : Fin 4) ≤ rank j := by
      change label i ≤ rank j at hj
      rwa [hr] at hj
    have hx : 3 ≤ (rank j).val := hh
    have eq : rank (loc i) = rank j := by
      apply Fin.ext
      change (label i).val = (rank j).val
      rw [hr]
      have bounded := (rank j).isLt
      omega
    exact congrArg Subtype.val (strict.injective eq)
  refine ⟨label, eqv, last, leq, ?_⟩
  intro k
  by_cases used : ∃ z, label z = k
  · obtain ⟨z, rfl⟩ := used
    let c := boundary z
    have term : FirstBranchRoute.Terminal (readEdge gs) out c :=
      FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs z)
    refine ⟨fun x => vl gs x c.val, ?_, ?_⟩
    · intro x y hxy
      apply agree_on_input_ancestors clean
      intro i path
      apply hxy i
      exact strict.monotone (show loc i ≤ loc z from
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live path term)
    · intro x y hxy heq
      have blocked := firstInputGroup_controlled clean out live c
      rcases blocked with atOut | apart
      · simpa only [atOut] using heq
      · apply circuit_cut_agreement clean c out x y heq
        intro i hi
        apply apart i
        apply (mem_firstInputGroup clean out live c i).mpr
        exact (eqv i z).mp (by_contra fun ne => hi (hxy i ne))
  · refine ⟨fun _ => false, fun _ _ _ => rfl, ?_⟩
    intro x y hxy _
    have : x = y := funext (fun i => hxy i (fun h => used ⟨i,h⟩))
    rw [this]

open CircuitProof PetersenCutFormula PetersenCutIndependent PetersenFirstGroup PetersenCutTrace PetersenScratch

def value (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def contexts (e : Fin 10 × Fin 10) : Nat × Nat :=
  match e.1.val, e.2.val with
  | 3, 4 => (0, 517)
  | 0, 5 => (516, 788)
  | 1, 6 => (0, 769)
  | 5, 7 => (0, 517)
  | 3, 8 => (0, 548)
  | 5, 8 => (0, 521)
  | 6, 8 => (0, 10)
  | _, _ => (0,0)

def bits (v : Nat) (i : Fin 10) := v.testBit i.val

theorem checkedContexts : ∀ e ∈ conflicts, ∀ (a b : Bool),
    let xa := pairInput e.1 e.2 (bits (contexts e).1) a b
    let xo := pairInput e.1 e.2 (bits (contexts e).2) a b
    xa 9 = (xa 0 || xa 2) ∧ value xa = (a && b) ∧
      xo 9 = (xo 0 || xo 2) ∧ value xo = (a || b) := by
  decide +kernel

theorem boundaryConflict {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool, x 9 = (x 0 || x 2) → vl gs x out.val = value x)
    (e : Fin 10 × Fin 10) (he : e ∈ conflicts) :
    firstInputBoundary clean out live e.1 ≠ firstInputBoundary clean out live e.2 := by
  intro same
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin 10, (k = e.1 ∨ k = e.2) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]
        exact same.symm
  have factor (base : Fin 10 → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor (bits (contexts e).1)
  obtain ⟨fo, ho⟩ := factor (bits (contexts e).2)
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b
    have h := checkedContexts e he a b
    exact (ha a b).trans ((computes _ h.1).trans h.2.1)
  · intro a b
    have h := checkedContexts e he a b
    exact (ho a b).trans ((computes _ h.2.2.1).trans h.2.2.2)



open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup


def before : Fin 9 → ℕ := ![532,513,521,516,513,513,2,516,8]
def after : Fin 9 → ℕ := ![533,515,525,524,529,545,66,644,264]
def cofactorNo (i : Fin 10) (b : Bool) : ℕ := if b then ![513,2,516,8,16,32,64,128,256,513] i else ![0,0,0,0,0,0,0,0,0,0] i
def cofactorYes (i : Fin 10) (b : Bool) : ℕ := if b then ![515,515,518,523,529,545,66,643,771,515] i else ![518,524,515,515,515,515,515,515,515,24] i
lemma rawPairs : ∀ i : Fin 9, let a := row (before i); let b := row (after i)
    valid a ∧ valid b ∧ (∀ j : Fin 10, j ≠ i.castSucc → a j = b j) ∧ target a ≠ target b := by
  unfold valid
  decide +kernel

lemma cofactorPairs : ∀ i b,
    let p := row (cofactorNo i b)
    let q := row (cofactorYes i b)
    valid p ∧ valid q ∧ p i = b ∧ q i = b ∧ target p ≠ target q := by
  unfold valid
  decide +kernel

theorem obtainRank (D : Circuit) (fan : FanInTwo D) (budget : nonNotCount D.gates ≤ 12)
    (necessary : ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) ≠ D.eval (List.ofFn x ++ [true]))
    (runs : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = Suffix2770.F x) :
    ∃ (gs : List Gate) (out : Fin (10 + gs.length)) (clean : CleanL 10 gs)
      (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v),
      (∀ w, (predecessors clean w).Nodup) ∧
      (∀ x, valid x → vl gs x out.val = target x) ∧
      ∃ label : Fin 10 → Fin 4, Shape label ∧
        (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
        (∀ i, label i = 3 → firstInputBoundary clean out live i = out) ∧
        (∀ i j, label i ≤ label j ↔ firstInputBoundary clean out live i ≤ firstInputBoundary clean out live j) := by
  have agree (x : Fin 10 → Bool) (hx : valid x) : circuitFun 10 D x = target x := by
    change x 9 = (x 0 || x 2) at hx
    have e : Suffix2770.plug (fun i : Fin 9 => x i.castSucc) (x 0 || x 2) = x := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change Fin.lastCases (motive := fun _ => Bool) (x 0 || x 2)
          (fun i : Fin 9 => x i.castSucc) (Fin.last 9) = x 9
        rw [Fin.lastCases_last]; exact hx.symm
      · simp [Suffix2770.plug]
    have h := runs (fun i : Fin 9 => x i.castSucc)
    change D.eval (List.ofFn (fun i : Fin 9 => x i.castSucc) ++ [x 0 || x 2]) = _ at h
    rw [← Suffix2770.plug_list, e] at h
    exact h
  have dep (i : Fin 10) : Dep (circuitFun 10 D) i := by
    apply Suffix2770.dep_of_pair
    refine Fin.lastCases ?_ (fun j => ?_) i
    · obtain ⟨x, h⟩ := necessary
      refine ⟨Suffix2770.plug x false, Suffix2770.plug x true, ?_, ?_⟩
      · intro j
        exact Fin.lastCases (fun hn => (hn rfl).elim) (fun k _ => by simp [Suffix2770.plug]) j
      · simpa only [circuitFun, Suffix2770.plug_list] using h
    · obtain ⟨ha,hb,off,ne⟩ := rawPairs j
      exact ⟨_,_,off,fun he => ne ((agree _ ha).symm.trans (he.trans (agree _ hb)))⟩
  have still (i : Fin 10) (b : Bool) : ∃ p q : Fin 10 → Bool,
      circuitFun 10 D (Function.update p i b) ≠ circuitFun 10 D (Function.update q i b) := by
    obtain ⟨hp,hq,ep,eq,ne⟩ := cofactorPairs i b
    refine ⟨row (cofactorNo i b),row (cofactorYes i b),?_⟩
    have pupdate (p : Fin 10 → Bool) (e : p i = b) : Function.update p i b = p :=
      (congrArg (fun c : Bool => Function.update p i c) e.symm).trans (Function.update_eq_self _ _)
    have ep' := pupdate _ ep
    have eq' := pupdate _ eq
    rw [ep', eq']
    exact fun e => ne ((agree _ hp).symm.trans (e.trans (agree _ hq)))
  have nc := dep_nc (dep 0)
  obtain ⟨gs, o, least, bound⟩ := least_with_budget D fan (fun _ => rfl) nc
  have validOut : o < 10 + gs.length := by
    by_contra! h
    obtain ⟨x,y,ne⟩ := least.ncv nc
    exact ne ((vl_beyond gs x o h).trans (vl_beyond gs y o h).symm)
  let out : Fin (10+gs.length) := ⟨o,validOut⟩
  have live := least_read_edge_live least nc dep still validOut
  have distinct := predecessors_nodup least nc
  have correct (x : Fin 10 → Bool) (hx : valid x) : vl gs x out.val = target x :=
    (least.hev x).trans (agree x hx)
  have forks := threeForksOfBudget least.hcl out live (bound.trans budget)
  obtain ⟨label, loc, last, leq, codes⟩ := preciseCuts least.hcl out live forks
  have shape : Shape label := by
    apply shapes label
    · intro p hp same
      exact boundaryConflict least.hcl out live distinct correct p hp ((loc _ _).mp same)
    · intro j _
      obtain ⟨c,lo,hi⟩ := codes j
      refine ⟨c,lo,fun x y hx hy opp e => ?_⟩
      exact (correct x hx).symm.trans ((hi x y opp e).trans (correct y hy))
  exact ⟨gs,out,least.hcl,live,distinct,correct,label,shape,loc,last,leq⟩

end Or02Attempt

namespace ReadOnceCatalog

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2519.PetersenScratch (occurrences)

abbrev Word := BitVec 16
abbrev Slots := Finset (Fin 4)
abbrev Family := List Word

def top : Word := BitVec.allOnes 16
def constants : Family := [0, top]
def raw (i : Fin 4) : Word := ![0xaaaa,0xcccc,0xf0f0,0xff00] i
def leaf (i : Fin 4) (positive : Bool) : Family :=
  0 :: top :: [if positive then raw i else ~~~raw i]
def mix (isAnd : Bool) (a b : Word) : Word := if isAnd then a &&& b else a ||| b
def product (isAnd : Bool) (a b : Family) : Family := a.flatMap fun x => b.map (mix isAnd x)

def all : List Slots := [∅,{0},{1},{2},{3},{0,1},{0,2},{0,3},{1,2},{1,3},{2,3},{0,1,2},{0,1,3},{0,2,3},{1,2,3},{0,1,2,3}]
def indices : List (Fin 4) := [0,1,2,3]
lemma all_mem : ∀ s : Slots, s ∈ all := by decide +kernel
lemma indices_mem : ∀ i : Fin 4, i ∈ indices := by decide +kernel
def anchor (s : Slots) : Fin 4 :=
  if 0 ∈ s then 0 else if 1 ∈ s then 1 else if 2 ∈ s then 2 else 3
lemma anchor_mem : ∀ s : Slots, s ≠ ∅ → anchor s ∈ s := by decide +kernel

def families : Nat → Slots → List Family
  | 0, _ => [constants]
  | fuel + 1, s =>
    if s = ∅ then [constants]
    else if s.card = 1 then (indices.filter fun i => i ∈ s).flatMap fun i => [leaf i true, leaf i false]
    else (all.filter fun l => l ⊆ s ∧ anchor s ∈ l).flatMap fun l =>
      let r := s \ l
      if l = ∅ ∨ r = ∅ then []
      else (families fuel l).flatMap fun a => (families fuel r).flatMap fun b =>
        [product true a b, product false a b]

def put {n : Nat} (ports : Fin 4 → Fin n) (base : Fin n → Bool) (k : Nat) (i : Fin n) : Bool :=
  if i = ports 0 then k.testBit 0 else
  if i = ports 1 then k.testBit 1 else
  if i = ports 2 then k.testBit 2 else
  if i = ports 3 then k.testBit 3 else base i

lemma put_at {n : Nat} {ports : Fin 4 → Fin n} (inj : Function.Injective ports)
    (base : Fin n → Bool) (k : Nat) (i : Fin 4) : put ports base k (ports i) = k.testBit i.val := by
  fin_cases i <;> simp [put, inj.eq_iff]

lemma put_other {n : Nat} {ports : Fin 4 → Fin n} (base : Fin n → Bool)
    (k : Nat) (i : Fin n) (h : ∀ j, i ≠ ports j) : put ports base k i = base i := by
  simp [put, h]

def support {n : Nat} (ports : Fin 4 → Fin n) (p : DMFormula n) : Slots :=
  Finset.univ.filter fun i => 0 < occurrences (ports i) p

lemma mem_support {n : Nat} {ports : Fin 4 → Fin n} {p : DMFormula n} {i : Fin 4} :
    i ∈ support ports p ↔ 0 < occurrences (ports i) p := by simp [support]

def Represents {n : Nat} (ports : Fin 4 → Fin n) (p : DMFormula n) (F : Family) : Prop :=
  0 ∈ F ∧ top ∈ F ∧ ∀ base, ∃ w ∈ F, ∀ k < 16, w.getLsbD k = p.eval (put ports base k)

lemma eval_agreement {n : Nat} {p : DMFormula n} {x y : Fin n → Bool}
    (eq : ∀ i, 0 < occurrences i p → x i = y i) : p.eval x = p.eval y := by
  induction p with
  | lit i s => have e := eq i (by simp [occurrences]); simp [DMFormula.eval, e]
  | and a b ha hb =>
    simp only [DMFormula.eval]
    exact congrArg₂ (· && ·) (ha (fun i h => eq i (by simp only [occurrences]; omega)))
      (hb (fun i h => eq i (by simp only [occurrences]; omega)))
  | or a b ha hb =>
    simp only [DMFormula.eval]
    exact congrArg₂ (· || ·) (ha (fun i h => eq i (by simp only [occurrences]; omega)))
      (hb (fun i h => eq i (by simp only [occurrences]; omega)))

lemma empty_repr {n : Nat} {ports : Fin 4 → Fin n} {p : DMFormula n}
    (empty : support ports p = ∅) : Represents ports p constants := by
  refine ⟨by simp [constants],by simp [constants],?_⟩
  intro base
  have eq (k : Nat) : p.eval (put ports base k) = p.eval base := by
    apply eval_agreement
    intro i used
    apply put_other
    intro j h
    have mem : j ∈ support ports p := mem_support.2 (h ▸ used)
    simp [empty] at mem
  cases hb : p.eval base with
  | false => exact ⟨0, by simp [constants], fun k hk => by simp [eq, hb]⟩
  | true =>
    refine ⟨top, by simp [constants], fun k hk => ?_⟩
    rw [eq, hb]
    change (BitVec.allOnes 16).getLsbD k = true
    rw [BitVec.getLsbD_allOnes]
    simp [hk]

lemma raw_bit (i : Fin 4) (k : Nat) (hk : k < 16) : (raw i).getLsbD k = k.testBit i.val := by
  let j : Fin 16 := ⟨k,hk⟩
  exact (by decide +kernel : ∀ (i : Fin 4) (j : Fin 16), (raw i).getLsbD j.val = j.val.testBit i.val) i j

lemma leaf_repr {n : Nat} {ports : Fin 4 → Fin n} (inj : Function.Injective ports)
    (i : Fin 4) (s : Bool) : Represents ports (.lit (ports i) s) (leaf i s) := by
  refine ⟨by simp [leaf], by simp [leaf], fun base => ⟨if s then raw i else ~~~raw i, by simp [leaf], ?_⟩⟩
  intro k hk
  have e := put_at inj base k i
  cases s <;> simp only [Bool.false_eq_true, ite_true, ite_false, DMFormula.eval, e,
    BitVec.getLsbD_not, hk, decide_true, Bool.true_and, raw_bit i k hk]

def node {n} (isAnd : Bool) (p q : DMFormula n) : DMFormula n := if isAnd then .and p q else .or p q
def branch (isAnd : Bool) (v w : Bool) := if isAnd then v && w else v || w

lemma node_eval {n} (isAnd : Bool) (p q : DMFormula n) (x : Fin n → Bool) :
    (node isAnd p q).eval x = branch isAnd (p.eval x) (q.eval x) := by cases isAnd <;> rfl

lemma mix_bit (isAnd : Bool) (a b : Word) (k : Nat) :
    (mix isAnd a b).getLsbD k = branch isAnd (a.getLsbD k) (b.getLsbD k) := by
  cases isAnd <;> simp [mix, branch, BitVec.getLsbD_and, BitVec.getLsbD_or]

lemma mem_product (b : Bool) {p q : Family} {a c : Word} (ha : a ∈ p) (hc : c ∈ q) :
    mix b a c ∈ product b p q := List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨c,hc,rfl⟩⟩

lemma product_repr {n} {ports : Fin 4 → Fin n} {p q : DMFormula n} {a b : Family}
    (isAnd : Bool) (ha : Represents ports p a) (hb : Represents ports q b) :
    Represents ports (node isAnd p q) (product isAnd a b) := by
  refine ⟨?_,?_,?_⟩
  · have h := mem_product isAnd ha.1 hb.1
    cases isAnd <;> exact h
  · have h := mem_product isAnd ha.2.1 hb.2.1
    cases isAnd <;> exact h
  · intro x
    obtain ⟨u,hu,eu⟩ := ha.2.2 x
    obtain ⟨v,hv,ev⟩ := hb.2.2 x
    refine ⟨mix isAnd u v, mem_product isAnd hu hv, fun k hk => ?_⟩
    rw [mix_bit, eu k hk, ev k hk, node_eval]

lemma constants_eliminate (d : Bool) (w z : Word) (hz : z ∈ constants) :
    mix d w z = 0 ∨ mix d w z = top ∨ mix d w z = w := by
  simp only [constants, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · cases d
    · exact Or.inr (Or.inr (show w ||| 0#16 = w from BitVec.or_zero))
    · exact Or.inl (show w &&& 0#16 = 0#16 from BitVec.and_zero)
  · cases d
    · exact Or.inr (Or.inl (show w ||| BitVec.allOnes 16 = BitVec.allOnes 16 from BitVec.or_allOnes))
    · exact Or.inr (Or.inr (show w &&& BitVec.allOnes 16 = w from BitVec.and_allOnes))

lemma mix_comm (d : Bool) (x y : Word) : mix d x y = mix d y x := by
  cases d <;> simp [mix, BitVec.and_comm, BitVec.or_comm]

lemma product_repr_swap {n} {ports : Fin 4 → Fin n} {p q : DMFormula n} {a b : Family}
    (d : Bool) (ha : Represents ports p a) (hb : Represents ports q b) :
    Represents ports (node d p q) (product d b a) := by
  have swapped := product_repr d hb ha
  refine ⟨swapped.1,swapped.2.1,?_⟩
  intro x
  obtain ⟨w,mem,eq⟩ := swapped.2.2 x
  refine ⟨w,mem,fun k hk => ?_⟩
  rw [eq k hk, node_eval, node_eval]
  cases d <;> simp [branch, Bool.and_comm, Bool.or_comm]

lemma product_skip_right {n} {ports : Fin 4 → Fin n} {p q : DMFormula n} {a : Family}
    (d : Bool) (ha : Represents ports p a) (hb : Represents ports q constants) :
    Represents ports (node d p q) a := by
  refine ⟨ha.1, ha.2.1, ?_⟩
  intro x
  obtain ⟨u,hu,eu⟩ := ha.2.2 x
  obtain ⟨v,hv,ev⟩ := hb.2.2 x
  refine ⟨mix d u v, ?_, fun k hk => ?_⟩
  · rcases constants_eliminate d u v hv with h|h|h <;> rw [h]
    · exact ha.1
    · exact ha.2.1
    · exact hu
  · rw [mix_bit, eu k hk, ev k hk, node_eval]

lemma product_skip_left {n} {ports : Fin 4 → Fin n} {p q : DMFormula n} {b : Family}
    (d : Bool) (ha : Represents ports p constants) (hb : Represents ports q b) :
    Represents ports (node d p q) b := by
  refine ⟨hb.1, hb.2.1, ?_⟩
  intro x
  obtain ⟨u,hu,eu⟩ := ha.2.2 x
  obtain ⟨v,hv,ev⟩ := hb.2.2 x
  refine ⟨mix d u v, ?_, fun k hk => ?_⟩
  · rw [mix_comm]
    rcases constants_eliminate d v u hu with h|h|h <;> rw [h]
    · exact hb.1
    · exact hb.2.1
    · exact hv
  · rw [mix_bit, eu k hk, ev k hk, node_eval]

lemma support_node {n} (ports : Fin 4 → Fin n) (d : Bool) (p q : DMFormula n) :
    support ports (node d p q) = support ports p ∪ support ports q := by
  ext i
  simp only [mem_support, Finset.mem_union]
  cases d <;> simp only [node, Bool.false_eq_true, ↓reduceIte, occurrences] <;> omega

lemma families_empty (fuel : Nat) : families fuel ∅ = [constants] := by cases fuel <;> rfl

lemma families_leaf {fuel : Nat} (pos : 0 < fuel) (i : Fin 4) (d : Bool) :
    leaf i d ∈ families fuel {i} := by
  cases fuel with
  | zero => omega
  | succ m =>
    simp only [families, Finset.singleton_ne_empty, Finset.card_singleton, ↓reduceIte]
    exact List.mem_flatMap.mpr ⟨i,List.mem_filter.mpr ⟨indices_mem _, by simp⟩,by cases d <;> simp⟩

lemma package {n} {ports : Fin 4 → Fin n} (inj : Function.Injective ports)
    (p : DMFormula n) (once : ∀ i, occurrences (ports i) p ≤ 1) (fuel : Nat)
    (capacity : (support ports p).card ≤ fuel) :
    ∃ F ∈ families fuel (support ports p), Represents ports p F := by
  have combine_proofs (d : Bool) (p q : DMFormula n) (m : Nat)
      (h : ∀ i, occurrences (ports i) p + occurrences (ports i) q ≤ 1)
      (cap : (support ports (node d p q)).card ≤ m)
      (ip : ∀ fuel, (support ports p).card ≤ fuel → ∃ A ∈ families fuel (support ports p), Represents ports p A)
      (iq : ∀ fuel, (support ports q).card ≤ fuel → ∃ B ∈ families fuel (support ports q), Represents ports q B) :
      ∃ F ∈ families m (support ports (node d p q)), Represents ports (node d p q) F := by
    let L := support ports p
    let R := support ports q
    have eq : support ports (node d p q) = L ∪ R := support_node ..
    rw [eq] at cap ⊢
    by_cases hl : L = ∅
    · rw [hl, Finset.empty_union] at cap ⊢
      obtain ⟨B,hB,b⟩ := iq m cap
      exact ⟨B,hB,product_skip_left d (empty_repr hl) b⟩
    by_cases hr : R = ∅
    · rw [hr, Finset.union_empty] at cap ⊢
      obtain ⟨A,hA,a⟩ := ip m cap
      exact ⟨A,hA,product_skip_right d a (empty_repr hr)⟩
    have disj : Disjoint L R := by
      apply Finset.disjoint_left.mpr
      intro i h1 h2
      have h1 := mem_support.mp h1
      have h2 := mem_support.mp h2
      have hh := h i
      omega
    have cnt := Finset.card_union_of_disjoint disj
    have lp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hl)
    have rp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hr)
    obtain ⟨k,rfl⟩ : ∃ k, m = k+1 := ⟨m-1,by omega⟩
    obtain ⟨A,hA,a⟩ := ip k (show L.card ≤ k by omega)
    obtain ⟨B,hB,b⟩ := iq k (show R.card ≤ k by omega)
    have hne : L ∪ R ≠ ∅ := fun e => hl (Finset.union_eq_empty.mp e).1
    have two : (L ∪ R).card ≠ 1 := by omega
    have add {U V : Slots} {X Y : Family} (order : U ∪ V = L ∪ R) (apart : Disjoint U V)
        (hu : U ≠ ∅) (hv : V ≠ ∅) (pivot : anchor (L ∪ R) ∈ U)
        (hx : X ∈ families k U) (hy : Y ∈ families k V) : product d X Y ∈ families (k+1) (L ∪ R) := by
      have diff : (L ∪ R) \ U = V := by
        rw [← order]
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_union]
        have hd (hl : i ∈ U) (hr : i ∈ V) : False := Finset.disjoint_left.mp apart hl hr
        tauto
      simp only [families, ite_eq_right hne, ite_eq_right two]
      apply List.mem_flatMap.mpr
      have sub : U ⊆ L ∪ R := order ▸ Finset.subset_union_left
      refine ⟨U, List.mem_filter.mpr ⟨all_mem _, by simpa using And.intro sub pivot⟩, ?_⟩
      simp only [diff, hu, hv, or_self, ↓reduceIte]
      refine List.mem_flatMap.mpr ⟨X,hx,List.mem_flatMap.mpr ⟨Y,hy,?_⟩⟩
      cases d <;> simp
    rcases Finset.mem_union.mp (anchor_mem _ hne) with pivot | pivot
    · exact ⟨product d A B, add rfl disj hl hr pivot hA hB, product_repr d a b⟩
    · exact ⟨product d B A, add (Finset.union_comm _ _) disj.symm hr hl pivot hB hA, product_repr_swap d a b⟩
  induction p generalizing fuel with
  | lit j s =>
    by_cases hit : ∃ i, ports i = j
    · obtain ⟨i,rfl⟩ := hit
      have eq : support ports (.lit (ports i) s) = {i} := by
        ext k
        rw [mem_support, Finset.mem_singleton]
        change (0 < if ports i = ports k then 1 else 0) ↔ k = i
        by_cases h : i = k
        · subst k
          simp
        · have hh : ports i ≠ ports k := fun e => h (inj e)
          simp [hh, Ne.symm h]
      rw [eq] at capacity ⊢
      refine ⟨leaf i s, families_leaf (by simp at capacity; omega) i s, leaf_repr inj i s⟩
    · have eq : support ports (.lit j s) = ∅ := by
        ext i
        have no : ports i ≠ j := fun h => hit ⟨i,h⟩
        simp [mem_support, occurrences, Ne.symm no]
      refine ⟨constants, ?_, empty_repr eq⟩
      rw [eq, families_empty]
      simp
  | and p q a b =>
    exact combine_proofs true p q fuel once capacity (fun k c => a (fun i => by have := once i; simp only [occurrences] at this; omega) k c)
      (fun k c => b (fun i => by have := once i; simp only [occurrences] at this; omega) k c)
  | or p q a b =>
    exact combine_proofs false p q fuel once capacity (fun k c => a (fun i => by have := once i; simp only [occurrences] at this; omega) k c)
      (fun k c => b (fun i => by have := once i; simp only [occurrences] at this; omega) k c)

def fits (mask want : Word) (F : Family) : Bool := F.any fun w => (w &&& mask) == want

def possible (S : Slots) : Bool := (families 4 S).any fun F =>
  fits 0xaa55 0xa800 F && fits 0xff00 0xec00 F && fits 0xaa55 0xaa54 F

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem noPossible : ∀ S : Slots, possible S = false := by decide +kernel

def pathPossible (S : Slots) : Bool := (families 4 S).any (fits 0xffff 0xeca8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem noPath : ∀ S : Slots, pathPossible S = false := by decide +kernel

lemma fits_samples {n} {ports : Fin 4 → Fin n} {p : DMFormula n} {F : Family}
    (h : Represents ports p F) (base : Fin n → Bool) (mask want : Word)
    (sample : ∀ k < 16, (p.eval (put ports base k) && mask.getLsbD k) = want.getLsbD k) :
      fits mask want F = true := by
  obtain ⟨w, hw, hwk⟩ := h.2.2 base
  apply List.any_eq_true.mpr
  refine ⟨w,hw,beq_iff_eq.mpr ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, hwk k hk]
  exact sample k hk

lemma noSamples {n} {ports : Fin 4 → Fin n} {p : DMFormula n}
    (inj : Function.Injective ports) (once : ∀ i, occurrences (ports i) p ≤ 1)
    (base0 base4 base104 : Fin n → Bool)
    (s0 : ∀ k < 16, (p.eval (put ports base0 k) && (0xaa55 : Word).getLsbD k) = (0xa800 : Word).getLsbD k)
    (s4 : ∀ k < 16, (p.eval (put ports base4 k) && (0xff00 : Word).getLsbD k) = (0xec00 : Word).getLsbD k)
    (s104 : ∀ k < 16, (p.eval (put ports base104 k) && (0xaa55 : Word).getLsbD k) = (0xaa54 : Word).getLsbD k) : False := by
  have cap : (support ports p).card ≤ 4 := (Finset.card_le_univ _).trans (by decide)
  obtain ⟨F,mem,repr⟩ := package inj p once 4 cap
  have e0 := fits_samples repr base0 0xaa55 0xa800 s0
  have e4 := fits_samples repr base4 0xff00 0xec00 s4
  have e104 := fits_samples repr base104 0xaa55 0xaa54 s104
  have e : possible (support ports p) = true := List.any_eq_true.mpr ⟨F, mem, by rw [e0,e4,e104]; rfl⟩
  exact Bool.noConfusion (e.symm.trans (noPossible _))

lemma noPathSamples {n} {ports : Fin 4 → Fin n} {p : DMFormula n}
    (inj : Function.Injective ports) (once : ∀ i, occurrences (ports i) p ≤ 1)
    (base : Fin n → Bool)
    (sample : ∀ k < 16, (p.eval (put ports base k) && (0xffff : Word).getLsbD k) = (0xeca8 : Word).getLsbD k) : False := by
  have cap : (support ports p).card ≤ 4 := (Finset.card_le_univ _).trans (by decide)
  obtain ⟨F,mem,repr⟩ := package inj p once 4 cap
  have e : pathPossible (support ports p) = true := List.any_eq_true.mpr ⟨F,mem,fits_samples repr base 0xffff 0xeca8 sample⟩
  exact Bool.noConfusion (e.symm.trans (noPath _))

end ReadOnceCatalog

namespace UnateOwner
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2519.PetersenScratch (occurrences)

lemma ignores {n} (p : DMFormula n) (v : Fin n) (visit : occurrences v p = 0)
    (x : Fin n → Bool) (a b : Bool) :
    p.eval (Function.update x v a) = p.eval (Function.update x v b) := by
  induction p with
  | lit i s =>
    have h : i ≠ v := by intro e; subst i; simp [occurrences] at visit
    simp [DMFormula.eval, Function.update_of_ne h]
  | and p q hp hq =>
    simp only [occurrences] at visit
    simp only [DMFormula.eval, hp (by omega), hq (by omega)]
  | or p q hp hq =>
    simp only [occurrences] at visit
    simp only [DMFormula.eval, hp (by omega), hq (by omega)]

def branch (d : Bool) (a b : Bool) : Bool := if d then a && b else a || b

lemma neutral (d a b c : Bool) (h : branch d a c ≠ branch d b c) :
    a ≠ b ∧ ∀ x, branch d x c = x := by
  cases d <;> cases c <;> simp_all [branch]

lemma branch_comm (d a b : Bool) : branch d a b = branch d b a := by
  cases d <;> simp [branch, Bool.or_comm, Bool.and_comm]

def node {n} (d : Bool) (a b : DMFormula n) : DMFormula n := if d then .and a b else .or a b

lemma node_run {n} (d : Bool) (a b : DMFormula n) (x : Fin n → Bool) :
    (node d a b).eval x = branch d (a.eval x) (b.eval x) := by cases d <;> rfl

def Sensitive {n} (p : DMFormula n) (v : Fin n) (x : Fin n → Bool) : Prop :=
  p.eval (Function.update x v false) ≠ p.eval (Function.update x v true)

lemma pair {n} (p : DMFormula n) (v : Fin n) (once : occurrences v p ≤ 1)
    (x y : Fin n → Bool) (hx : Sensitive p v x) (hy : Sensitive p v y) (s : Bool) :
    p.eval (Function.update x v s) = p.eval (Function.update y v s) := by
  have pull {a b : DMFormula n} (d : Bool) (z : Fin n → Bool)
      (hb : occurrences v b = 0) (hz : Sensitive (node d a b) v z) :
      Sensitive a v z ∧ ∀ c, (node d a b).eval (Function.update z v c) = a.eval (Function.update z v c) := by
    unfold Sensitive at hz ⊢
    simp only [node_run] at hz
    rw [ignores b v hb z true false] at hz
    obtain ⟨sep, idle⟩ := neutral _ _ _ _ hz
    refine ⟨sep, fun c => ?_⟩
    rw [node_run, ignores b v hb z c false, idle]
  have flip {a b : DMFormula n} (d : Bool) (z : Fin n → Bool) (c : Bool) :
      (node d a b).eval (Function.update z v c) = (node d b a).eval (Function.update z v c) := by
    simp only [node_run]
    exact branch_comm _ _ _
  have solve {a b : DMFormula n} (d : Bool) (h : occurrences v a + occurrences v b ≤ 1)
      (hx : Sensitive (node d a b) v x) (hy : Sensitive (node d a b) v y)
      (ihA : occurrences v a ≤ 1 → Sensitive a v x → Sensitive a v y →
        a.eval (Function.update x v s) = a.eval (Function.update y v s))
      (ihB : occurrences v b ≤ 1 → Sensitive b v x → Sensitive b v y →
        b.eval (Function.update x v s) = b.eval (Function.update y v s)) :
      (node d a b).eval (Function.update x v s) = (node d a b).eval (Function.update y v s) := by
    by_cases no : occurrences v b = 0
    · obtain ⟨ha,xsimp⟩ := pull d x no hx
      obtain ⟨hb,ysimp⟩ := pull d y no hy
      rw [xsimp,ysimp]
      exact ihA (by omega) ha hb
    · have noA : occurrences v a = 0 := by omega
      have sx : Sensitive (node d b a) v x := by
        unfold Sensitive at hx ⊢
        rwa [← flip d x false, ← flip d x true]
      have sy : Sensitive (node d b a) v y := by
        unfold Sensitive at hy ⊢
        rwa [← flip d y false, ← flip d y true]
      obtain ⟨ha,xsimp⟩ := pull d x noA sx
      obtain ⟨hb,ysimp⟩ := pull d y noA sy
      rw [flip d x s, flip d y s, xsimp,ysimp]
      exact ihB (by omega) ha hb
  induction p with
  | lit i b =>
    by_cases e : i = v
    · subst i
      simp [DMFormula.eval]
    · exfalso
      exact hx (ignores (.lit i b) v (by simp [occurrences,e]) x false true)
  | and a b ha hb => exact solve true once hx hy ha hb
  | or a b ha hb => exact solve false once hx hy ha hb

end UnateOwner

namespace Or02Attempt

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2519
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup PetersenCutFormula PetersenScratch
open Or02Rank

def withAux : Fin 4 → Fin 10 := ![0,1,4,9]
def withoutAux : Fin 4 → Fin 10 := ![0,1,4,2]
def baseCodes : Fin 3 → Nat := ![0,4,104]
def masks : Fin 3 → ReadOnceCatalog.Word := ![0xaa55,0xff00,0xaa55]
def wants : Fin 3 → ReadOnceCatalog.Word := ![0xa800,0xec00,0xaa54]

lemma auxData : ∀ t : Fin 3, ∀ k : Fin 16,
    let x := ReadOnceCatalog.put withAux (row (baseCodes t)) k.val
    ((masks t).getLsbD k.val = true → valid x) ∧
    (target x && (masks t).getLsbD k.val) = (wants t).getLsbD k.val := by
  unfold valid
  decide +kernel

lemma pathData : ∀ k : Fin 16,
    let x := ReadOnceCatalog.put withoutAux (fun _ => false) k.val
    let y := Function.update x 9 (x 0 || x 2)
    (x 3 = false ∧ x 5 = false ∧ x 6 = false ∧ x 9 = false) ∧
    valid y ∧ (target y && (0xffff : ReadOnceCatalog.Word).getLsbD k.val) =
      (0xeca8 : ReadOnceCatalog.Word).getLsbD k.val := by
  unfold valid
  decide +kernel

def ownerRow (i : Fin 10) (aux : Bool) : Fin 10 → Bool :=
  row (if i = 3 then if aux then 516 else 16
    else if i = 5 then if aux then 513 else 128
    else if aux then 769 else 2)

lemma ownerData : ∀ (i : Fin 10), i ∈ ([3,5,6] : List (Fin 10)) → ∀ aux : Bool,
    let x := ownerRow i aux
    let y := Function.update x i true
    valid x ∧ valid y ∧ x i = false ∧ x 9 = aux ∧
      (∀ j ∈ ([3,5,6] : List (Fin 10)), x j = false) ∧ target x ≠ target y := by
  unfold valid
  decide +kernel

lemma labelOwner : ∀ (a b c k : Fin 4),
    a < 3 → b < 3 → c < 3 → a ≠ b → a ≠ c → b ≠ c → k < 3 →
    k = a ∨ k = b ∨ k = c := by decide +kernel

theorem excludeRank {gs : List Gate} (out : Fin (10+gs.length)) (clean : CleanL 10 gs)
    (live : ∀ w : Fin (10+gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (correct : ∀ x, valid x → vl gs x out.val = target x)
    (label : Fin 10 → Fin 4) (shape : Shape label)
    (loc : ∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j)
    (last : ∀ i, label i = 3 → firstInputBoundary clean out live i = out)
    (leq : ∀ i j, label i ≤ label j ↔ firstInputBoundary clean out live i ≤ firstInputBoundary clean out live j) : False := by
  rcases shape with ⟨l0,l1,l2,l4,l7,l8,l3,l5,l6,d35,d36,d56⟩
  let p := wireFormula (0 : Fin 10) gs out.val
  have pv (x : Fin 10 → Bool) : p.eval x = vl gs x out.val := wireFormula_eval 0 clean x _ out.isLt
  have count (i : Fin 10) (h : label i = 3) : occurrences i p ≤ 1 := by
    dsimp only [p]
    rw [← last i h]
    exact firstInputBoundary_occurrences_le_one clean out live distinct 0 i
  by_cases top : label 9 = 3
  · have occ : ∀ i, occurrences (withAux i) p ≤ 1 := by
      intro i
      apply count
      fin_cases i <;> simp [withAux, l0,l1,l4,top]
    have sample (t : Fin 3) (k : Nat) (hk : k < 16) :
        (p.eval (ReadOnceCatalog.put withAux (row (baseCodes t)) k) && (masks t).getLsbD k) =
          (wants t).getLsbD k := by
      obtain ⟨val, want⟩ := auxData t ⟨k,hk⟩
      change ((masks t).getLsbD k = true → valid _) at val
      change (target _ && (masks t).getLsbD k) = _ at want
      by_cases h : (masks t).getLsbD k = true
      · rw [pv, correct _ (val h)]
        exact want
      · have en : (masks t).getLsbD k = false := Bool.eq_false_iff.mpr h
        simpa only [en, Bool.and_false] using want
    exact ReadOnceCatalog.noSamples (by decide +kernel) occ
      (row (baseCodes 0)) (row (baseCodes 1)) (row (baseCodes 2)) (sample 0) (sample 1) (sample 2)
  · have early : label 9 < 3 := by
      have bound := (label 9).isLt
      have ne : (label 9).val ≠ 3 := fun h => top (Fin.ext h)
      change (label 9).val < 3
      omega
    have owner : ∃ i ∈ ([3,5,6] : List (Fin 10)), label 9 = label i := by
      rcases labelOwner (label 3) (label 5) (label 6) (label 9) l3 l5 l6 d35 d36 d56 early with e|e|e
      · exact ⟨3,by simp,e⟩
      · exact ⟨5,by simp,e⟩
      · exact ⟨6,by simp,e⟩
    obtain ⟨i,hi,li⟩ := owner
    have ni : i ≠ 9 := by intro h; subst i; simp at hi
    let cut := firstInputBoundary clean out live 9
    have cuti : cut = firstInputBoundary clean out live i := (loc 9 i).mp li
    have away : cut ≠ out := by
      intro h
      have h' : firstInputBoundary clean out live 9 = firstInputBoundary clean out live 0 := h.trans (last 0 l0).symm
      exact top (((loc 9 0).mpr h').trans l0)
    have terminal : FirstBranchRoute.Terminal (readEdge gs) out cut :=
      FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs 9)
    let q := wireFormula (0 : Fin 10) gs cut.val
    have qv (x : Fin 10 → Bool) : q.eval x = vl gs x cut.val := wireFormula_eval 0 clean x _ cut.isLt
    have qonce : occurrences i q ≤ 1 := by
      dsimp only [q]
      rw [cuti]
      exact firstInputBoundary_occurrences_le_one clean out live distinct 0 i
    have beforeOnly (j : Fin 10) (hj : label j ≤ label 9) :
        j = 9 ∨ j ∈ ([3,5,6] : List (Fin 10)) := by
      by_contra missed
      have complement : ∀ v : Fin 10, ¬(v = 9 ∨ v ∈ ([3,5,6] : List (Fin 10))) →
          v ∈ ([0,1,2,4,7,8] : List (Fin 10)) := by decide +kernel
      have member := complement j missed
      have atTop : label j = 3 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
      exact (not_le_of_gt early) (atTop ▸ hj)
    have qAgree (x y : Fin 10 → Bool)
        (agree : ∀ j, j = 9 ∨ j ∈ ([3,5,6] : List (Fin 10)) → x j = y j) : q.eval x = q.eval y := by
      rw [qv, qv]
      apply agree_on_input_ancestors clean
      intro j path
      apply agree
      apply beforeOnly
      apply (leq j 9).2
      exact FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live path terminal
    have block (v : Fin 10) (bound : firstInputBoundary clean out live v = cut) :
        ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs v) out := by
      rcases firstInputGroup_controlled clean out live cut with stop|apart
      · exact (away stop).elim
      · exact apart v ((mem_firstInputGroup clean out live cut v).2 bound)
    have swapAt (v : Fin 10) (h : firstInputBoundary clean out live v = cut)
        (x : Fin 10 → Bool) (z : Bool) (eq : q.eval x = q.eval (Function.update x v z)) :
        vl gs x out.val = vl gs (Function.update x v z) out.val := by
      apply circuit_cut_agreement clean cut out x _
      · exact (qv x).symm.trans (eq.trans (qv _))
      · intro j ne
        by_cases hj : j = v
        · subst j; exact block v h
        · exact (ne (Function.update_of_ne hj _ _).symm).elim
    let b0 (b : Bool) : Fin 10 → Bool := Function.update (fun _ => false) 9 b
    have sens (b : Bool) : UnateOwner.Sensitive q i (b0 b) := by
      let x := ownerRow i b
      obtain ⟨hvalid,hvalid',hi0,h9,hothers,ne⟩ := ownerData i hi b
      have sep : q.eval x ≠ q.eval (Function.update x i true) := by
        intro e
        have e' := swapAt i cuti.symm x true e
        exact ne ((correct x hvalid).symm.trans (e'.trans (correct _ hvalid')))
      have bridge (s : Bool) : q.eval (Function.update x i s) = q.eval (Function.update (b0 b) i s) := by
        apply qAgree
        intro j hj
        by_cases ji : j = i
        · simp [ji]
        · simp only [Function.update_of_ne ji]
          rcases hj with rfl|he
          · simpa [b0] using h9
          · have j9 : j ≠ 9 := by intro h; subst j; simp at he
            simpa [b0, Function.update_of_ne j9] using hothers j he
      have passthru : Function.update x i false = x := by
        rw [← hi0]; exact Function.update_eq_self _ _
      unfold UnateOwner.Sensitive
      rw [← bridge false, ← bridge true, passthru]
      exact sep
    have noAuxDiff : q.eval (b0 false) = q.eval (b0 true) := by
      have e := UnateOwner.pair q i qonce (b0 false) (b0 true) (sens false) (sens true) false
      have hfalse (b : Bool) : b0 b i = false := by simp [b0, Function.update_of_ne ni]
      have identity (b : Bool) : Function.update (b0 b) i false = b0 b := by
        rw [← hfalse b]; exact Function.update_eq_self _ _
      simpa only [identity] using e
    have cleanAux (x : Fin 10 → Bool) (h3 : x 3 = false) (h5 : x 5 = false) (h6 : x 6 = false) :
        p.eval x = p.eval (Function.update x 9 false) := by
      have rawZero : ∀ j ∈ ([3,5,6] : List (Fin 10)), x j = false := by
        intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl|rfl|rfl <;> assumption
      have eqv (y : Fin 10 → Bool) (zero : ∀ j ∈ ([3,5,6] : List (Fin 10)), y j = false) :
          q.eval y = q.eval (b0 (y 9)) := by
        apply qAgree
        intro j hj
        rcases hj with rfl|hm
        · simp [b0]
        · have j9 : j ≠ 9 := by intro h; subst j; simp at hm
          simpa [b0, Function.update_of_ne j9] using zero j hm
      have diff : q.eval x = q.eval (Function.update x 9 false) := by
        rw [eqv x rawZero, eqv (Function.update x 9 false)]
        · rw [Function.update_self]
          cases x 9 <;> simp_all
        · intro j hj
          have j9 : j ≠ 9 := by intro h; subst j; simp at hj
          simpa only [Function.update_of_ne j9] using rawZero j hj
      rw [pv, pv]
      exact swapAt 9 rfl x false diff
    have occ : ∀ i, occurrences (withoutAux i) p ≤ 1 := by
      intro j; apply count
      fin_cases j <;> simp [withoutAux, l0,l1,l4,l2]
    apply ReadOnceCatalog.noPathSamples (by decide +kernel) occ (fun _ => false)
    intro k hk
    let x := ReadOnceCatalog.put withoutAux (fun _ => false) k
    let y := Function.update x 9 (x 0 || x 2)
    obtain ⟨⟨z3,z5,z6,z9⟩,isValid,table⟩ := pathData ⟨k,hk⟩
    change x 3 = false at z3
    change x 5 = false at z5
    change x 6 = false at z6
    change x 9 = false at z9
    change valid y at isValid
    have eqUpdate : Function.update y 9 false = x := by
      change Function.update (Function.update x 9 (x 0 || x 2)) 9 false = x
      rw [Function.update_idem, ← z9, Function.update_eq_self]
    have equal : p.eval y = p.eval x := by
      have same (j : Fin 10) (h : j ≠ 9) : y j = x j := Function.update_of_ne h _ _
      rw [cleanAux y (same 3 (by decide) |>.trans z3) (same 5 (by decide) |>.trans z5)
        (same 6 (by decide) |>.trans z6), eqUpdate]
    change (p.eval x && _) = _
    rw [← equal, pv, correct y isValid]
    exact table

end Or02Attempt

end PEqualNP.Outside.L_meta_2519

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2519
open CircuitProof

theorem PEqualNP.Outside.L_meta_2519 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ (8 : ℕ) ≤ ↑x3 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan nots first correct
  by_contra! short
  obtain ⟨i,j,order,late,ni,nj,_⟩ := nots
  obtain ⟨gates,out⟩ := C
  cases gates with
  | nil => exact Fin.elim0 i
  | cons g gs =>
    let D : Circuit := ⟨gs,out⟩
    let p := fun z : Gate => isNotGate z.op
    have hshort : gs.length < 15 := by
      change (g :: gs).length < 16 at short
      simp only [List.length_cons] at short
      omega
    have fd : FanInTwo D := fun z hz => fan z (List.mem_cons_of_mem _ hz)
    have ilt : i.val < gs.length + 1 := i.isLt
    have jlt : j.val < gs.length + 1 := j.isLt
    have lt : i.val < j.val := order
    let u : Fin gs.length := ⟨i.val-1, by omega⟩
    let v : Fin gs.length := ⟨j.val-1, by omega⟩
    have shift (a : Fin (g :: gs).length) (z : Fin gs.length) (hz : a.val = z.val + 1) :
        (g :: gs).get a = gs.get z := by simp [List.get_eq_getElem, hz]
    have hu : gs[u.val].op = .not := by
      change (gs.get u).op = .not
      rwa [← shift i u (by dsimp [u]; omega)]
    have hv : gs[v.val].op = .not := by
      change (gs.get v).op = .not
      rwa [← shift j v (by dsimp [v]; omega)]
    have neq : u.val ≠ v.val := by dsimp [u,v]; omega
    let gate : Gate := ⟨.and, []⟩
    let updated := gs.set u.val gate
    have index : v.val < updated.length := by simp [updated]
    have preserve : updated[v.val].op = .not := by
      rw [show updated[v.val] = gs[v.val] from List.getElem_set_ne neq index]
      exact hv
    have afterSet (L : List Gate) (k : ℕ) (hk : k < L.length) (yes : p L[k] = true) :
        (L.set k gate).countP p + 1 = L.countP p := by
      have pos : 0 < L.countP p := List.countP_pos_iff.mpr ⟨L[k],List.getElem_mem hk,yes⟩
      have zero : p gate = false := rfl
      simp only [List.countP_set hk, yes, zero, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega
    have count1 : updated.countP p + 1 = gs.countP p :=
      afterSet gs _ u.isLt (by simp [p,hu,isNotGate])
    have count2 : (updated.set v.val gate).countP p + 1 = updated.countP p :=
      afterSet updated _ index (by simp [p,preserve,isNotGate])
    have two : 2 ≤ notGateCount gs := by
      change 2 ≤ (gs.filter p).length
      rw [← List.countP_eq_length_filter]
      omega
    have total := nonNotCount_add_notCount gs
    change nonNotCount gs + notGateCount gs = gs.length at total
    have budget : nonNotCount gs ≤ 12 := by omega
    let step := fun (w : List Bool) (a : Gate) => w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
    have keep (ts : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
        (ts.foldl step w).getD k false = w.getD k false := by
      induction ts generalizing w with
      | nil => rfl
      | cons a ts ih =>
        rw [List.foldl_cons, ih (step w a) (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hk
    have runs (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 2]) = Suffix2770.F x := by
      let f := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
      have value := first x
      change (gs.foldl step (List.ofFn x ++ [f])).getD 9 false = _ at value
      rw [keep _ _ _ (by simp)] at value
      have eq : f = (x 0 || x 2) := by
        simpa [List.getD_eq_getElem?_getD,List.getElem?_append] using value
      have hv := congrFun correct x
      change D.eval (List.ofFn x ++ [f]) = Suffix2770.F x at hv
      simpa only [eq] using hv
    have relevance : ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) ≠ D.eval (List.ofFn x ++ [true]) := by
      by_contra! irrelevant
      let a : Gate := ⟨.not,[0]⟩
      let E : Circuit := ⟨a :: gs,out⟩
      have fanE : FanInTwo E := by
        intro z hz
        change z ∈ a::gs at hz
        rcases List.mem_cons.mp hz with rfl|mem
        · simp [a]
        · exact fd z mem
      have start (x : Fin 9 → Bool) : step (List.ofFn x) a = List.ofFn x ++ [!x 0] := by
        simp [a,step,GateOp.eval,List.getD_eq_getElem?_getD]
      have Ecorrect (x : Fin 9 → Bool) : circuitFun 9 E x = Suffix2770.F x := by
        change (gs.foldl step (step (List.ofFn x) a)).getD out false = _
        rw [start]
        change D.eval (List.ofFn x ++ [!x 0]) = _
        have any (q : Bool) : D.eval (List.ofFn x ++ [q]) = D.eval (List.ofFn x ++ [false]) := by
          cases q
          · rfl
          · exact (irrelevant x).symm
        exact (any _).trans ((any _).symm.trans (runs x))
      have pb := Suffix2770.lower E fanE (funext Ecorrect)
      rw [Suffix2770.binary_eq] at pb
      change 13 ≤ nonNotCount (a::gs) at pb
      change 13 ≤ (a::gs).countP (fun z => !(isNotGate z.op)) at pb
      rw [List.countP_cons] at pb
      change 13 ≤ nonNotCount gs at pb
      omega
    obtain ⟨ts,t,clean,live,dist,ok,lab,shape,loc,last,leq⟩ :=
      Or02Attempt.obtainRank D fd budget relevance runs
    exact Or02Attempt.excludeRank t clean live dist ok lab shape loc last leq
