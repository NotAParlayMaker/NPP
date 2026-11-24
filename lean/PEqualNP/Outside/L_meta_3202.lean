import Mathlib
import PEqualNP.Defs

-- The circuit normalization and binary lower bound reuse L-meta-2770 by GGGWANNN.
-- That proof credits the L-meta-2165 lower bound by copsrlpond.

namespace PEqualNP.Outside.L_meta_3202

namespace Previous

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity








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
    exact PEqualNP.Outside.L_meta_3202.Previous.least_gate_inputs_nodup least nonnull _
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

theorem normalizedCuts {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (hcard : (circuitBranchWires (n := n) gs).card ≤ 3) :
    ∃ label : Fin n → Fin 4,
      (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
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
  refine ⟨label, eqv, ?_⟩
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


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def runStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def before : Fin 9 → ℕ := ![10,1,2,5,1,1,2,4,8]
def after : Fin 9 → ℕ := ![11,3,6,13,17,33,66,132,264]
def maskBits (m : Nat) (j : Fin 9) := m.testBit j.val
def embed (x : Fin 9 → Bool) := plug x (x 0 || x 3)

lemma rawPairs : ∀ i : Fin 9, let a := maskBits (before i); let b := maskBits (after i)
    (∀ j : Fin 10, j ≠ i.castSucc → embed a j = embed b j) ∧ F a ≠ F b := by decide +kernel

def nonNot : GateOp → Bool
  | .not => false
  | _ => true

def binary (gs : List Gate) := gs.countP (fun g => nonNot g.op)

lemma budget (gs : List Gate)
    (fan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    binary gs + gs.countP (fun g => g.op.eval [false]) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ih' := ih (fun q hq => fan q (List.mem_cons_of_mem _ hq))
    have hg := fan g List.mem_cons_self
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    unfold binary at ih' ⊢
    have one : (if nonNot g.op then 1 else 0) + (if g.op.eval [false] then 1 else 0) = 1 := by
      rcases hg with ho | ho | ho <;> rw [ho] <;> rfl
    simp only [List.countP_cons, List.length_cons]
    split_ifs at one ⊢ <;> omega

lemma suffix_shape
    (hBound : ∀ B : Circuit, FanInTwo B → circuitFun 9 B = F → 13 ≤ binary B.gates)
    (C : Circuit) (hfan : FanInTwo C) (hlen : C.gates.length = 15)
    (first : C.gates[0]? = some ⟨.or, [0,3]⟩)
    (nots : 2 ≤ C.gates.countP (fun g => g.op.eval [false])) (hfun : circuitFun 9 C = F) :
    ∃ D : Circuit, FanInTwo D ∧ binary D.gates ≤ 12 ∧ D.gates.length = 14 ∧
      (∀ x : Fin 9 → Bool, circuitFun 10 D (embed x) = F x) ∧
      ∀ i : Fin 10, ∃ p q : Fin 10 → Bool, (∀ j, j ≠ i → p j = q j) ∧
          circuitFun 10 D p ≠ circuitFun 10 D q := by
  rcases C with ⟨gs,out⟩
  cases gs with
  | nil => contradiction
  | cons g gs =>
    change (g :: gs)[0]? = _ at first
    simp only [List.getElem?_cons_zero,Option.some.injEq] at first
    subst g
    let D : Circuit := ⟨gs,out⟩
    have hfd : FanInTwo D := fun a ha => hfan a (List.mem_cons_of_mem _ ha)
    have hs : gs.length = 14 := by change (Gate.mk .or [0,3] :: gs).length = 15 at hlen; simpa using hlen
    have hn : 2 ≤ gs.countP (fun g => g.op.eval [false]) := by
      change 2 ≤ (Gate.mk .or [0,3] :: gs).countP _ at nots
      simpa [List.countP_cons,GateOp.eval] using nots
    have hb : binary gs ≤ 12 := by
      have := budget gs (fun a ha => (hfd a ha).1)
      omega
    have seed (x : Fin 9 → Bool) : runStep (List.ofFn x) ⟨.or,[0,3]⟩ = List.ofFn (embed x) := by
      rw [embed,plug_list]; simp [runStep,GateOp.eval,List.getD]
    have valid (x : Fin 9 → Bool) : circuitFun 10 D (embed x) = F x := by
      have hx := congrFun hfun x
      change (gs.foldl runStep (runStep (List.ofFn x) ⟨.or,[0,3]⟩)).getD out false = F x at hx
      rw [seed] at hx
      exact hx
    refine ⟨D, hfd, hb, hs, valid, ?_⟩
    intro i
    by_cases hlt : i.val < 9
    · let v : Fin 9 := ⟨i.val,hlt⟩
      have hi : i = v.castSucc := Fin.ext rfl
      obtain ⟨hp,hd⟩ := rawPairs v
      exact ⟨embed (maskBits (before v)), embed (maskBits (after v)), by simpa only [hi] using hp,
        by simpa only [valid] using hd⟩
    · have last : i = Fin.last 9 := Fin.ext (by have := i.isLt; change i.val = 9; omega)
      subst i
      by_contra! hind
      let a : Gate := ⟨.not,[0]⟩
      let E : Circuit := ⟨a :: gs,out⟩
      have fan : FanInTwo E := by
        intro q hq
        change q ∈ a :: gs at hq
        rcases List.mem_cons.mp hq with rfl | hmem
        · simp [a]
        · exact hfd q hmem
      have start (x : Fin 9 → Bool) : runStep (List.ofFn x) a = List.ofFn (plug x (!x 0)) := by
        rw [plug_list]
        simp [runStep, a, GateOp.eval, List.getD]
      have he (x : Fin 9 → Bool) : circuitFun 9 E x = F x := by
        have hx := hind (plug x (!x 0)) (embed x) (by
          intro j hj
          refine Fin.lastCases ?_ (fun j => ?_) j hj
          · exact fun h => (h rfl).elim
          · simp [embed,plug])
        change (gs.foldl runStep (runStep (List.ofFn x) a)).getD out false = F x
        rw [start]
        exact hx.trans (valid x)
      have bad := hBound E fan (funext he)
      change 13 ≤ binary (a :: gs) at bad
      have same : binary (a :: gs) = binary gs := by unfold binary; rw [List.countP_cons]; rfl
      rw [same] at bad
      omega

def cofactorNo (i : Fin 10) (b : Bool) : Nat :=
  if b then ![1,2,4,8,16,32,64,128,256,1] i else 0

def cofactorYes (i : Fin 10) (b : Bool) : Nat :=
  if b then ![3,3,6,11,17,33,66,131,259,3] i else ![6,12,3,3,3,3,3,3,3,6] i

lemma cofactorPairs : ∀ (i : Fin 10) (b : Bool),
    let p := maskBits (cofactorNo i b)
    let q := maskBits (cofactorYes i b)
    embed p i = b ∧ embed q i = b ∧ F p ≠ F q := by decide +kernel

lemma suffix_data
    (hBound : ∀ B : Circuit, FanInTwo B → circuitFun 9 B = F → 13 ≤ binary B.gates)
    (C : Circuit) (hfan : FanInTwo C) (hlen : C.gates.length = 15)
    (first : C.gates[0]? = some ⟨.or, [0,3]⟩)
    (nots : 2 ≤ C.gates.countP (fun g => g.op.eval [false])) (hfun : circuitFun 9 C = F) :
    ∃ D : Circuit, FanInTwo D ∧ binary D.gates ≤ 12 ∧ D.gates.length = 14 ∧
      (∀ x : Fin 10 → Bool, x 9 = (x 0 || x 3) →
        circuitFun 10 D x = F (fun i : Fin 9 => x i.castSucc)) ∧
      (∀ i : Fin 10, ∃ p q : Fin 10 → Bool, (∀ j, j ≠ i → p j = q j) ∧
          circuitFun 10 D p ≠ circuitFun 10 D q) ∧
      (∀ (i : Fin 10) (b : Bool), ∃ p q : Fin 10 → Bool,
          circuitFun 10 D (Function.update p i b) ≠ circuitFun 10 D (Function.update q i b)) := by
  obtain ⟨D, fan, hb, len, agree, dep⟩ := suffix_shape hBound C hfan hlen first nots hfun
  refine ⟨D, fan, hb, len, ?_, dep, ?_⟩
  · intro x hx
    have heq : embed (fun i : Fin 9 => x i.castSucc) = x := by
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · change Fin.lastCases (motive := fun _ => Bool) (x 0 || x 3) (fun i : Fin 9 => x i.castSucc) (Fin.last 9) = x 9
        rw [Fin.lastCases_last]; exact hx.symm
      · simp [embed, plug]
    exact heq ▸ agree (fun i : Fin 9 => x i.castSucc)
  · intro i b
    let p := maskBits (cofactorNo i b)
    let q := maskBits (cofactorYes i b)
    obtain ⟨hp, hq, hf⟩ := cofactorPairs i b
    refine ⟨embed p, embed q, ?_⟩
    have ep : Function.update (embed p) i b = embed p := hp ▸ Function.update_eq_self _ _
    have eq : Function.update (embed q) i b = embed q := hq ▸ Function.update_eq_self _ _
    simpa only [ep, eq, agree] using hf

end Suffix2770

namespace Finite2770

def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def valid (x : Fin 10 → Bool) : Prop := x 9 = (x 0 || x 3)

def conflicts : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8)]

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

def flag (v0 v1 v2 v5 v6 v7 v8 : BitVec 2) : Bool :=
  decide (v0 ≠ v1) &&
  decide (v1 ≠ v2) &&
  decide (v0 ≠ v5) &&
  decide (v1 ≠ v6) &&
  decide (v2 ≠ v7) &&
  decide (v5 ≠ v7) &&
  decide (v5 ≠ v8) &&
  decide (v6 ≠ v8) &&
  decide (v0 = v2 → v1 ≤ v0) &&
  decide (v0 = v2 → v5 ≤ v0) &&
  decide (v0 = v6 → v1 ≤ v0) &&
  decide (v0 = v7 → v5 ≤ v0) &&
  decide (v0 = v8 → v5 ≤ v0) &&
  decide (v1 = v5 → v0 ≤ v1) &&
  decide (v1 = v7 → v2 ≤ v1) &&
  decide (v1 = v8 → v6 ≤ v1) &&
  decide (v2 = v5 → v7 ≤ v2) &&
  decide (v2 = v6 → v1 ≤ v2) &&
  decide (v2 = v6 → v7 ≤ v2) &&
  decide (v2 = v8 → v6 ≤ v2) &&
  decide (v5 = v6 → v8 ≤ v5) &&
  decide (v6 = v7 → v8 ≤ v6) &&
  decide (v7 = v8 → v2 ≤ v7)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 10000000 in
lemma badFlags : ∀ (v0 v1 v2 v5 v6 v7 v8 : BitVec 2), flag v0 v1 v2 v5 v6 v7 v8 = false := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 10000000 in
lemma noRanks (v0 v1 v2 v5 v6 v7 v8 : BitVec 2)
    (c0 : v0 ≠ v1)
    (c1 : v1 ≠ v2)
    (c2 : v0 ≠ v5)
    (c3 : v1 ≠ v6)
    (c4 : v2 ≠ v7)
    (c5 : v5 ≠ v7)
    (c6 : v5 ≠ v8)
    (c7 : v6 ≠ v8)
    (h0 : v0 = v2 → v1 ≤ v0)
    (h1 : v0 = v2 → v5 ≤ v0)
    (h2 : v0 = v6 → v1 ≤ v0)
    (h3 : v0 = v7 → v5 ≤ v0)
    (h4 : v0 = v8 → v5 ≤ v0)
    (h5 : v1 = v5 → v0 ≤ v1)
    (h6 : v1 = v7 → v2 ≤ v1)
    (h7 : v1 = v8 → v6 ≤ v1)
    (h8 : v2 = v5 → v7 ≤ v2)
    (h9 : v2 = v6 → v1 ≤ v2)
    (h10 : v2 = v6 → v7 ≤ v2)
    (h11 : v2 = v8 → v6 ≤ v2)
    (h12 : v5 = v6 → v8 ≤ v5)
    (h13 : v6 = v7 → v8 ≤ v6)
    (h14 : v7 = v8 → v2 ≤ v7)
    : False := by
  have h := badFlags v0 v1 v2 v5 v6 v7 v8
  simp_all [flag]

theorem impossible (label : Fin 10 → Fin 4)
    (conf : ∀ e ∈ conflicts, label e.1 ≠ label e.2)
    (cut : ∀ t, t < 3 → Cut label t) : False := by
  let f (i : Fin 10) : BitVec 2 := BitVec.ofFin (label i)
  have inj {i j : Fin 10} (h : f i = f j) : label i = label j := congrArg BitVec.toFin h
  have hcf (i j : Fin 10) (hm : (i,j) ∈ conflicts) : f i ≠ f j := fun h => conf (i,j) hm (inj h)
  have hbound (i j k : Fin 10) (a b c : ℕ) (hw : cube i j k a b c) :
      f i = f j → f k ≤ f i := fun h => cubeBound label cut i j k a b c hw (inj h)
  exact noRanks (f 0) (f 1) (f 2) (f 5) (f 6) (f 7) (f 8)
    (hcf 0 1 (by decide))
    (hcf 1 2 (by decide))
    (hcf 0 5 (by decide))
    (hcf 1 6 (by decide))
    (hcf 2 7 (by decide))
    (hcf 5 7 (by decide))
    (hcf 5 8 (by decide))
    (hcf 6 8 (by decide))
    (hbound 0 2 1 525 521 520 (by unfold cube valid; decide))
    (hbound 0 2 5 525 521 520 (by unfold cube valid; decide))
    (hbound 0 6 1 617 616 552 (by unfold cube valid; decide))
    (hbound 0 7 5 651 650 522 (by unfold cube valid; decide))
    (hbound 0 8 5 777 521 520 (by unfold cube valid; decide))
    (hbound 1 5 0 618 616 584 (by unfold cube valid; decide))
    (hbound 1 7 2 162 34 32 (by unfold cube valid; decide))
    (hbound 1 8 6 262 260 4 (by unfold cube valid; decide))
    (hbound 2 5 7 38 34 2 (by unfold cube valid; decide))
    (hbound 2 6 1 196 192 128 (by unfold cube valid; decide))
    (hbound 2 6 7 324 260 256 (by unfold cube valid; decide))
    (hbound 2 8 6 388 384 128 (by unfold cube valid; decide))
    (hbound 5 6 8 98 34 2 (by unfold cube valid; decide))
    (hbound 6 7 8 196 68 4 (by unfold cube valid; decide))
    (hbound 7 8 2 448 192 64 (by unfold cube valid; decide))

end Finite2770

namespace Conflict2770

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof PetersenCutFormula PetersenCutIndependent PetersenFirstGroup PetersenCutTrace PetersenScratch

def pairs : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8)]

def value (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def contexts (e : Fin 10 × Fin 10) : Nat × Nat :=
  match e.1.val, e.2.val with
  | 0, 1 => (520, 616)
  | 1, 2 => (0, 192)
  | 2, 3 => (513, 897)
  | 0, 5 => (520, 650)
  | 1, 6 => (0, 260)
  | 2, 7 => (0, 34)
  | 5, 7 => (0, 260)
  | 3, 8 => (513, 581)
  | 5, 8 => (0, 192)
  | _, _ => (0, 34)

def bits (v : Nat) (i : Fin 10) := v.testBit i.val

theorem checkedContexts : ∀ e ∈ pairs, ∀ (a b : Bool),
    let xa := pairInput e.1 e.2 (bits (contexts e).1) a b
    let xo := pairInput e.1 e.2 (bits (contexts e).2) a b
    xa 9 = (xa 0 || xa 3) ∧ value xa = (a && b) ∧
      xo 9 = (xo 0 || xo 3) ∧ value xo = (a || b) := by
  decide +kernel

theorem boundaryConflict {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool, x 9 = (x 0 || x 3) → vl gs x out.val = value x)
    (e : Fin 10 × Fin 10) (he : e ∈ pairs) :
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

end Conflict2770

open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup

lemma noSuffix (D : Circuit) (fan : FanInTwo D) (budget : nonNotCount D.gates ≤ 12)
    (agree : ∀ x : Fin 10 → Bool, x 9 = (x 0 || x 3) →
      circuitFun 10 D x = Suffix2770.F (fun i : Fin 9 => x i.castSucc))
    (dep : ∀ i, Dep (circuitFun 10 D) i)
    (still : ∀ (i : Fin 10) (b : Bool), ∃ x y : Fin 10 → Bool,
      circuitFun 10 D (Function.update x i b) ≠ circuitFun 10 D (Function.update y i b)) : False := by
  classical
  have nc := dep_nc (dep 0)
  obtain ⟨gs, o, least, bound⟩ := least_with_budget D fan (fun _ => rfl) nc
  have valid : o < 10 + gs.length := by
    by_contra! h
    obtain ⟨x, y, different⟩ := least.ncv nc
    exact different ((vl_beyond gs x o h).trans (vl_beyond gs y o h).symm)
  let out : Fin (10 + gs.length) := ⟨o, valid⟩
  have live := least_read_edge_live least nc dep still valid
  have branches := threeForksOfBudget least.hcl out live (bound.trans budget)
  obtain ⟨label, locations, codes⟩ := normalizedCuts least.hcl out live branches
  have computes (x : Fin 10 → Bool) (hx : Finite2770.valid x) :
      vl gs x out.val = Finite2770.target x := (least.hev x).trans (agree x hx)
  apply Finite2770.impossible label
  · intro e he same
    exact Conflict2770.boundaryConflict least.hcl out live (predecessors_nodup least nc)
      computes e he ((locations _ _).mp same)
  · intro t _
    obtain ⟨c, low, high⟩ := codes t
    refine ⟨c, low, ?_⟩
    intro x y vx vy rest same
    exact (computes x vx).symm.trans ((high x y rest same).trans (computes y vy))


namespace Suffix2770

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous
open PEqualNP.Outside.L_meta_3202.Previous.CircuitProof
open PEqualNP.Outside.L_meta_3202.Previous.CircuitProof.Readers
open PEqualNP.Outside.L_meta_3202.Previous.PetersenNine

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

def Posted (C : Circuit) : Prop :=
  C.gates.length = 15 ∧ C.output = 23 ∧ C.gates[0]? = some ⟨.or,[0,3]⟩ ∧
    ∀ (s : ℕ) (h : s < C.gates.length),
      let g := C.gates[s]
      let ok (a : ℕ) := a < 9+s ∨ a = 24
      let rank (a : ℕ) := if a < 9 then a else if a = 24 then 9 else a+1
      g = ⟨.and,[]⟩ ∨ (∃ a, ok a ∧ g = ⟨.not,[a]⟩) ∨
        ∃ a b, ok a ∧ ok b ∧ rank a ≤ rank b ∧ (g = ⟨.and,[a,b]⟩ ∨ g = ⟨.or,[a,b]⟩)

theorem fromPosted (C : Circuit) (shape : Posted C)
    (nots : 2 ≤ C.gates.countP (fun g => g.op.eval [false])) (hfun : circuitFun 9 C = F) :
    ∃ D : Circuit, FanInTwo D ∧ nonNotCount D.gates ≤ 12 ∧
      (∀ x : Fin 10 → Bool, x 9 = (x 0 || x 3) →
        circuitFun 10 D x = F (fun i : Fin 9 => x i.castSucc)) ∧
      (∀ i : Fin 10, Dep (circuitFun 10 D) i) ∧
      (∀ (i : Fin 10) (b : Bool), ∃ p q : Fin 10 → Bool,
          circuitFun 10 D (Function.update p i b) ≠ circuitFun 10 D (Function.update q i b)) := by
  obtain ⟨len,_,first,slots⟩ := shape
  have fan : FanInTwo C := by
    intro g hg
    obtain ⟨s, hs, hsg⟩ := List.mem_iff_getElem.mp hg
    have form := slots s hs
    dsimp only at form
    rw [hsg] at form
    rcases form with e | ⟨_,_,e⟩ | ⟨_,_,_,_,_,e | e⟩ <;> rw [e] <;> simp
  obtain ⟨D,hD,hb,_,slice,dep,cofactor⟩ := suffix_data lower C fan len first nots hfun
  exact ⟨D,hD,by simpa only [binary_eq] using hb,slice,fun i => dep_of_pair (dep i),cofactor⟩

end Suffix2770

end Previous

namespace FiniteRanks





def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def valid (x : Fin 10 → Bool) : Prop := x 9 = (x 0 || x 2)

def conflicts : List (Fin 10 × Fin 10) :=
  [(0,5), (1,6), (2,3), (3,4), (3,8), (5,7), (5,8), (6,8)]

def contexts (e : Fin 10 × Fin 10) : ℕ × ℕ :=
  match e.1.val, e.2.val with
  | 0, 5 => (580,788)
  | 1, 6 => (144,897)
  | 2, 3 => (577,897)
  | 3, 4 => (192,897)
  | 3, 8 => (641,628)
  | 5, 7 => (80,788)
  | 5, 8 => (532,713)
  | 6, 8 => (641,138)
  | _, _ => (0,0)

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

private theorem cubeBound (label : Fin 10 → Fin 4) (cut : ∀ t, t < 3 → Cut label t)
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

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

 
theorem checkedContexts : ∀ e ∈ conflicts, ∀ (a b : Bool),
    let xa := pairInput e.1 e.2 (row (contexts e).1) a b
    let xo := pairInput e.1 e.2 (row (contexts e).2) a b
    valid xa ∧ target xa = (a && b) ∧ valid xo ∧ target xo = (a || b) := by
  unfold valid
  decide +kernel

private def constraints (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 2) : Bool :=
  decide (v0 ≠ v5) &&
  decide (v1 ≠ v6) &&
  decide (v2 ≠ v3) &&
  decide (v3 ≠ v4) &&
  decide (v3 ≠ v8) &&
  decide (v5 ≠ v7) &&
  decide (v5 ≠ v8) &&
  decide (v6 ≠ v8) &&
  decide (v0 = v3 → v4 ≤ v0) &&
  decide (v0 = v6 → v8 ≤ v0) &&
  decide (v1 = v3 → v4 ≤ v1) &&
  decide (v1 = v4 → v6 ≤ v1) &&
  decide (v1 = v5 → v7 ≤ v1) &&
  decide (v1 = v7 → v6 ≤ v1) &&
  decide (v1 = v8 → v6 ≤ v1) &&
  decide (v2 = v5 → v7 ≤ v2) &&
  decide (v2 = v6 → v8 ≤ v2) &&
  decide (v3 = v5 → v7 ≤ v3) &&
  decide (v3 = v5 → v8 ≤ v3) &&
  decide (v3 = v6 → v4 ≤ v3) &&
  decide (v3 = v6 → v8 ≤ v3) &&
  decide (v3 = v7 → v4 ≤ v3) &&
  decide (v4 = v5 → v7 ≤ v4) &&
  decide (v4 = v6 → v1 ≤ v4) &&
  decide (v4 = v7 → v5 ≤ v4) &&
  decide (v4 = v8 → v3 ≤ v4) &&
  decide (v5 = v6 → v7 ≤ v5) &&
  decide (v5 = v6 → v8 ≤ v5) &&
  decide (v6 = v7 → v1 ≤ v6) &&
  decide (v7 = v8 → v5 ≤ v7)

private def shape (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 2) : Bool :=
  decide (v0 = 3) &&
  decide (v1 = 3) &&
  decide (v2 = 3) &&
  decide (v4 = 3) &&
  decide (v7 = 3) &&
  decide (v8 = 3) &&
  decide (v3 ≠ 3) &&
  decide (v5 ≠ 3) &&
  decide (v6 ≠ 3) &&
  decide (v3 ≠ v5) &&
  decide (v3 ≠ v6) &&
  decide (v5 ≠ v6)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 50000000 in
private theorem finite_rank_bound :
    ∀ (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 2), constraints v0 v1 v2 v3 v4 v5 v6 v7 v8 = true → shape v0 v1 v2 v3 v4 v5 v6 v7 v8 = true := by
  decide +kernel

theorem rank_pattern (label : Fin 10 → Fin 4)
    (conf : ∀ e ∈ conflicts, label e.1 ≠ label e.2)
    (cut : ∀ t, t < 3 → Cut label t) :
    label 0 = 3 ∧ label 1 = 3 ∧ label 2 = 3 ∧ label 4 = 3 ∧ label 7 = 3 ∧ label 8 = 3 ∧
    label 3 ≠ 3 ∧ label 5 ≠ 3 ∧ label 6 ≠ 3 ∧
    label 3 ≠ label 5 ∧ label 3 ≠ label 6 ∧ label 5 ≠ label 6 := by
  let f (i : Fin 10) : BitVec 2 := BitVec.ofFin (label i)
  have hinj {i j : Fin 10} (h : f i = f j) : label i = label j := congrArg BitVec.toFin h
  have hconf (i j : Fin 10) (hm : (i,j) ∈ conflicts) : f i ≠ f j := fun h => conf (i,j) hm (hinj h)
  have hbound (i j k : Fin 10) (a b c : ℕ) (hw : cube i j k a b c) :
      f i = f j → f k ≤ f i := fun h => cubeBound label cut i j k a b c hw (hinj h)
  have h0 := hconf 0 5 (by decide)
  have h1 := hconf 1 6 (by decide)
  have h2 := hconf 2 3 (by decide)
  have h3 := hconf 3 4 (by decide)
  have h4 := hconf 3 8 (by decide)
  have h5 := hconf 5 7 (by decide)
  have h6 := hconf 5 8 (by decide)
  have h7 := hconf 6 8 (by decide)
  have h8 := hbound 0 3 4 517 524 516 (by unfold cube valid; decide)
  have h9 := hbound 0 6 8 533 596 532 (by unfold cube valid; decide)
  have h10 := hbound 1 3 4 66 72 64 (by unfold cube valid; decide)
  have h11 := hbound 1 4 6 10 24 8 (by unfold cube valid; decide)
  have h12 := hbound 1 5 7 66 96 64 (by unfold cube valid; decide)
  have h13 := hbound 1 7 6 34 160 32 (by unfold cube valid; decide)
  have h14 := hbound 1 8 6 10 264 8 (by unfold cube valid; decide)
  have h15 := hbound 2 5 7 517 545 513 (by unfold cube valid; decide)
  have h16 := hbound 2 6 8 645 705 641 (by unfold cube valid; decide)
  have h17 := hbound 3 5 7 24 48 16 (by unfold cube valid; decide)
  have h18 := hbound 3 5 8 24 48 16 (by unfold cube valid; decide)
  have h19 := hbound 3 6 4 10 66 2 (by unfold cube valid; decide)
  have h20 := hbound 3 6 8 10 66 2 (by unfold cube valid; decide)
  have h21 := hbound 3 7 4 40 160 32 (by unfold cube valid; decide)
  have h22 := hbound 4 5 7 24 40 8 (by unfold cube valid; decide)
  have h23 := hbound 4 6 1 24 72 8 (by unfold cube valid; decide)
  have h24 := hbound 4 7 5 24 136 8 (by unfold cube valid; decide)
  have h25 := hbound 4 8 3 48 288 32 (by unfold cube valid; decide)
  have h26 := hbound 5 6 7 34 66 2 (by unfold cube valid; decide)
  have h27 := hbound 5 6 8 34 66 2 (by unfold cube valid; decide)
  have h28 := hbound 6 7 1 96 160 32 (by unfold cube valid; decide)
  have h29 := hbound 7 8 5 136 264 8 (by unfold cube valid; decide)
  have h : constraints (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) = true := by
    simp only [constraints, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩, h28⟩, h29⟩
  have hs := finite_rank_bound (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) h
  have finEq (u v : Fin 4) : (BitVec.ofFin u = BitVec.ofFin v) ↔ u = v :=
    ⟨fun h => congrArg BitVec.toFin h, fun h => congrArg (BitVec.ofFin (w := 2)) h⟩
  have hthree (z : Fin 4) : (BitVec.ofFin z = (3 : BitVec 2)) ↔ z = 3 := finEq z 3
  simpa only [shape, Bool.and_eq_true, decide_eq_true_eq, and_assoc, f, ne_eq, hthree,
    finEq] using hs

end FiniteRanks

namespace TopRows

def row (m : ℕ) (i : Fin 10) : Bool := m.testBit i.val

def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def valid (x : Fin 10 → Bool) : Prop := x 9 = (x 0 || x 2)

def two (i j : Fin 10) (m : ℕ) (a b : Bool) (k : Fin 10) : Bool :=
  if k = i then a else if k = j then b else row m k

 

def lcaRows : List (Fin 10 × Fin 10 × Bool × ℕ) :=
  [(0,1,false,788),(0,4,true,772),(0,7,false,788),(0,8,false,628),
   (1,2,false,897),(1,4,false,897),(1,7,false,788),(1,8,false,713),
   (2,4,false,897),(2,7,true,769),(2,8,false,713),
   (4,7,false,773),(4,8,false,713),(7,8,false,628)]

theorem checked_lca_rows : ∀ e ∈ lcaRows, ∀ a b : Bool,
    let x := two e.1 e.2.1 e.2.2.2 a b
    valid x ∧ target x = (if e.2.2.1 then a && b else a || b) := by
  unfold valid
  decide +kernel

 
def andLeafRows : List (Fin 10 × Fin 10 × ℕ) :=
  [(4,0,548),(0,4,8),(7,2,521),(2,7,32)]

theorem checked_and_leaf_rows : ∀ e ∈ andLeafRows, ∀ b : Bool,
    let x := two e.1 e.2.1 e.2.2 false b
    valid x ∧ target x = b := by
  unfold valid
  decide +kernel

 

theorem checked_or_leaf_rows : ∀ a b : Bool,
    valid (two 1 8 8 a b) ∧ target (two 1 8 8 a b) = b ∧
    valid (two 1 8 513 a b) ∧ target (two 1 8 513 a b) = a := by
  unfold valid
  decide +kernel

def early (e : Fin 3 → Bool) (bit : Bool) (i : Fin 10) : Bool :=
  if i = 3 then e 0 else if i = 5 then e 1 else if i = 6 then e 2
  else if i = 8 then bit else false

 

theorem checked_early : ∀ (e : Fin 3 → Bool) (bit : Bool),
    valid (early e bit) ∧ target (early e bit) = (bit && (e 0 || e 1 || e 2)) := by
  unfold valid
  decide +kernel

end TopRows

namespace LastAbsorber

 
structure Step (E : Type*) where
  conj : Bool
  other : E → Bool

 
def run {E : Type*} : List (Step E) → E → Bool → Bool
  | [], _, b => b
  | step :: rest, e, b =>
      if step.conj then run rest e b && step.other e
      else run rest e b || step.other e

private theorem tail_pivotal {E : Type*} (step : Step E) (rest : List (Step E)) (e : E)
    (h : run (step :: rest) e false = false ∧ run (step :: rest) e true = true) :
    step.other e = step.conj ∧
      run rest e false = false ∧ run rest e true = true := by
  cases hop : step.conj <;> cases hv : step.other e <;> simp_all [run]

 
theorem neutral_of_pivotal {E : Type*} (path : List (Step E)) (e : E)
    (h : run path e false = false ∧ run path e true = true) :
    ∀ s ∈ path, s.other e = s.conj := by
  induction path with
  | nil => simp
  | cons head rest ih =>
      obtain ⟨hh, ht⟩ := tail_pivotal head rest e h
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hh
      · exact ih ht s hs

 
theorem has_false_and {E : Type*} (path : List (Step E)) (e : E)
    (hoff : run path e true = false) :
    ∃ s ∈ path, s.conj = true ∧ s.other e = false := by
  induction path with
  | nil => simp [run] at hoff
  | cons head tail ih =>
    cases hop : head.conj <;> cases hv : head.other e
    · have hd : run tail e true = false := by simpa [run, hop, hv] using hoff
      obtain ⟨s, hs, hc, hz⟩ := ih hd
      exact ⟨s, List.mem_cons_of_mem _ hs, hc, hz⟩
    · simp [run, hop, hv] at hoff
    · exact ⟨head, List.mem_cons_self, hop, hv⟩
    · have hd : run tail e true = false := by simpa [run, hop, hv] using hoff
      obtain ⟨s, hs, hc, hz⟩ := ih hd
      exact ⟨s, List.mem_cons_of_mem _ hs, hc, hz⟩

 


theorem exists_and_guard {E : Type*} (path : List (Step E)) (zero : E)
    (hoff : run path zero true = false)
    (hrest : ∀ e ≠ zero, run path e false = false ∧ run path e true = true) :
    ∃ s ∈ path, s.conj = true ∧ s.other zero = false ∧
      ∀ e ≠ zero, s.other e = true := by
  obtain ⟨s, hs, hc, hzero⟩ := has_false_and path zero hoff
  exact ⟨s, hs, hc, hzero, fun e he => (neutral_of_pivotal path e (hrest e he) s hs).trans hc⟩

end LastAbsorber

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup

abbrev F := Suffix2770.F

def embed (x : Fin 9 → Bool) : Fin 10 → Bool :=
  Suffix2770.plug x (x 0 || x 2)

def before : Fin 9 → ℕ := ![20, 1, 9, 4, 1, 1, 2, 4, 8]
def after : Fin 9 → ℕ := ![21, 3, 13, 12, 17, 33, 66, 132, 264]

lemma rawPairs : ∀ i : Fin 9, let a := Suffix2770.maskBits (before i)
    let b := Suffix2770.maskBits (after i)
    (∀ j : Fin 10, j ≠ i.castSucc → embed a j = embed b j) ∧ F a ≠ F b := by
  decide +kernel

def cofactorNo (i : Fin 10) (b : Bool) : ℕ :=
  if b then ![1, 2, 4, 8, 16, 32, 64, 128, 256, 1] i else 0

def cofactorYes (i : Fin 10) (b : Bool) : ℕ :=
  if b then ![3, 3, 6, 11, 17, 33, 66, 131, 259, 3] i
  else ![6, 12, 3, 3, 3, 3, 3, 3, 3, 24] i

lemma cofactorPairs : ∀ (i : Fin 10) (b : Bool),
    let a := Suffix2770.maskBits (cofactorNo i b)
    let c := Suffix2770.maskBits (cofactorYes i b)
    embed a i = b ∧ embed c i = b ∧ F a ≠ F c := by
  decide +kernel

private theorem suffix_two_not (g : Gate) (gs : List Gate)
    (i j : Fin (g :: gs).length) (hij : i < j) (hi : i.val = 7)
    (hni : ((g :: gs).get i).op = .not)
    (hnj : ((g :: gs).get j).op = .not) : nonNotCount gs + 2 ≤ gs.length := by
  have hpos : 0 < i.val := by omega
  have hjpos : 0 < j.val := by
    have := show i.val < j.val from hij
    omega
  obtain ⟨iv, ivl⟩ := i
  obtain ⟨jv, jvl⟩ := j
  cases iv with
  | zero => simp at hpos
  | succ a =>
    cases jv with
    | zero => simp at hjpos
    | succ b =>
      let ia : Fin gs.length := ⟨a, by simpa using ivl⟩
      let ib : Fin gs.length := ⟨b, by simpa using jvl⟩
      have ha : (gs.get ia).op = .not := hni
      have hb : (gs.get ib).op = .not := hnj
      have hab : ia.val ≠ ib.val := by
        intro he
        have hh : a + 1 < b + 1 := hij
        change a = b at he
        omega
      let pad : Gate := ⟨.and, []⟩
      let G := gs.set ia.val pad
      have hbl : ib.val < G.length := by simpa [G] using ib.isLt
      have hgb : G[ib.val].op = .not := by
        rw [show G[ib.val] = gs[ib.val] from List.getElem_set_ne hab hbl]
        exact hb
      have first := nonNotCount_replace_not gs ia.val ia.isLt ha
      have second := nonNotCount_replace_not G ib.val hbl hgb
      change nonNotCount G = nonNotCount gs + 1 at first
      change nonNotCount (G.set ib.val pad) = nonNotCount G + 1 at second
      have total : nonNotCount (G.set ib.val pad) ≤ gs.length := by
        simpa [nonNotCount, G] using
          (List.countP_le_length (p := fun q : Gate => !(isNotGate q.op))
            (l := G.set ib.val pad))
      omega

def NotSlots (C : Circuit) : Prop :=
  ∃ i j : Fin C.gates.length, i < j ∧ i.val = 7 ∧
    (C.gates.get i).op = .not ∧ (C.gates.get j).op = .not ∧
    ∀ k : Fin C.gates.length, (C.gates.get k).op = .not → k = i ∨ k = j

def FirstWire (C : Circuit) : Prop :=
  ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)

def Slice (x : Fin 10 → Bool) : Prop := x 9 = (x 0 || x 2)

theorem suffix_data (C : Circuit) (fan : FanInTwo C) (size : C.gates.length ≤ 15)
    (nots : NotSlots C) (first : FirstWire C) (computes : circuitFun 9 C = F) :
    ∃ D : Circuit, FanInTwo D ∧ nonNotCount D.gates ≤ 12 ∧
      (∀ x : Fin 10 → Bool, Slice x →
        circuitFun 10 D x = F (fun i : Fin 9 => x i.castSucc)) ∧
      (∀ i : Fin 10, Dep (circuitFun 10 D) i) ∧
      (∀ (i : Fin 10) (b : Bool), ∃ p q : Fin 10 → Bool,
        circuitFun 10 D (Function.update p i b) ≠ circuitFun 10 D (Function.update q i b)) := by
  rcases C with ⟨gs, out⟩
  obtain ⟨i, j, hij, hival, hni, hnj, _⟩ := nots
  cases gs with
  | nil => exact Fin.elim0 i
  | cons g gs =>
    let D : Circuit := ⟨gs, out⟩
    have hfan : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem _ ha)
    have count := suffix_two_not g gs i j hij hival hni hnj
    have length : gs.length ≤ 14 := by
      change (g :: gs).length ≤ 15 at size
      simp only [List.length_cons] at size
      omega
    have hb : nonNotCount D.gates ≤ 12 := by
      change nonNotCount gs ≤ 12
      omega
    have seed (x : Fin 9 → Bool) :
        Suffix2770.runStep (List.ofFn x) g = List.ofFn (embed x) := by
      have hfirst := first x
      change ((g :: gs).foldl Suffix2770.runStep (List.ofFn x)).getD 9 false = _ at hfirst
      rw [List.foldl_cons] at hfirst
      have hkeep := getD_wiresFrom gs (Suffix2770.runStep (List.ofFn x) g) 9 (by
        simp [Suffix2770.runStep])
      change (gs.foldl Suffix2770.runStep (Suffix2770.runStep (List.ofFn x) g)).getD 9 false =
        (Suffix2770.runStep (List.ofFn x) g).getD 9 false at hkeep
      rw [hkeep] at hfirst
      unfold Suffix2770.runStep at hfirst ⊢
      rw [getD_snoc_len _ _ _ 9 (by simp)] at hfirst
      rw [embed, Suffix2770.plug_list, hfirst]
    have agree (x : Fin 9 → Bool) : circuitFun 10 D (embed x) = F x := by
      have hx := congrFun computes x
      change (gs.foldl Suffix2770.runStep
        (Suffix2770.runStep (List.ofFn x) g)).getD out false = F x at hx
      rw [seed] at hx
      exact hx
    refine ⟨D, hfan, hb, ?_, ?_, ?_⟩
    · intro x hx
      have heq : embed (fun i : Fin 9 => x i.castSucc) = x := by
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · change Fin.lastCases (motive := fun _ => Bool) (x 0 || x 2)
            (fun i : Fin 9 => x i.castSucc) (Fin.last 9) = x 9
          rw [Fin.lastCases_last]
          exact hx.symm
        · simp [embed, Suffix2770.plug]
      exact heq ▸ agree (fun i : Fin 9 => x i.castSucc)
    · intro i
      apply Suffix2770.dep_of_pair
      by_cases hlt : i.val < 9
      · let v : Fin 9 := ⟨i.val, hlt⟩
        have hi : i = v.castSucc := Fin.ext rfl
        obtain ⟨hp, hd⟩ := rawPairs v
        exact ⟨embed (Suffix2770.maskBits (before v)), embed (Suffix2770.maskBits (after v)),
          by simpa only [hi] using hp, by simpa only [agree] using hd⟩
      · have last : i = Fin.last 9 := Fin.ext (by
          have := i.isLt
          change i.val = 9
          omega)
        subst i
        by_contra! hind
        let a : Gate := ⟨.not, [0]⟩
        let E : Circuit := ⟨a :: gs, out⟩
        have fanE : FanInTwo E := by
          intro q hq
          change q ∈ a :: gs at hq
          rcases List.mem_cons.mp hq with rfl | hmem
          · simp [a]
          · exact hfan q hmem
        have start (x : Fin 9 → Bool) :
            Suffix2770.runStep (List.ofFn x) a = List.ofFn (Suffix2770.plug x (!x 0)) := by
          rw [Suffix2770.plug_list]
          simp [Suffix2770.runStep, a, GateOp.eval, List.getD]
        have he (x : Fin 9 → Bool) : circuitFun 9 E x = F x := by
          have hx := hind (Suffix2770.plug x (!x 0)) (embed x) (by
            intro j hj
            refine Fin.lastCases ?_ (fun j => ?_) j hj
            · exact fun h => (h rfl).elim
            · simp [embed, Suffix2770.plug])
          change (gs.foldl Suffix2770.runStep
            (Suffix2770.runStep (List.ofFn x) a)).getD out false = F x
          rw [start]
          exact hx.trans (agree x)
        have bad := Suffix2770.lower E fanE (funext he)
        rw [Suffix2770.binary_eq] at bad
        change 13 ≤ nonNotCount (a :: gs) at bad
        have same : nonNotCount (a :: gs) = nonNotCount gs := rfl
        rw [same] at bad
        omega
    · intro i b
      let p := Suffix2770.maskBits (cofactorNo i b)
      let q := Suffix2770.maskBits (cofactorYes i b)
      obtain ⟨hp, hq, hf⟩ := cofactorPairs i b
      refine ⟨embed p, embed q, ?_⟩
      have ep : Function.update (embed p) i b = embed p := hp ▸ Function.update_eq_self _ _
      have eq : Function.update (embed q) i b = embed q := hq ▸ Function.update_eq_self _ _
      simpa only [ep, eq, agree] using hf

theorem normalizedCutsTop {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (hcard : (circuitBranchWires (n := n) gs).card ≤ 3) :
    ∃ label : Fin n → Fin 4,
      (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
      (∀ i, label i = 3 ↔ firstInputBoundary clean out live i = out) ∧
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
  let top : cuts := ⟨out, Finset.mem_insert_self _ _⟩
  have index_le (j : Fin cuts.card) : j ≤ embed top := by
    have below : embed.symm j ≤ top := wire_le_output clean out live ((embed.symm j).val)
    simpa using embed.monotone below
  have index_end : (embed top).val + 1 = cuts.card := by
    let last : Fin cuts.card := ⟨cuts.card - 1, by
      have := (embed top).isLt
      omega⟩
    have hl : last.val ≤ (embed top).val := index_le last
    have := (embed top).isLt
    change cuts.card - 1 ≤ (embed top).val at hl
    omega
  have rank_top : rank top = 3 := by
    apply Fin.ext
    change 4 - cuts.card + (embed top).val = 3
    omega
  have atTop (i : Fin n) : label i = 3 ↔ boundary i = out := by
    change rank (loc i) = 3 ↔ (loc i).val = top.val
    rw [← rank_top, strict.injective.eq_iff, Subtype.ext_iff]
  refine ⟨label, eqv, atTop, ?_⟩
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

open PetersenCutFormula PetersenCutIndependent PetersenScratch

def target10 (x : Fin 10 → Bool) : Bool := F (fun i : Fin 9 => x i.castSucc)

theorem boundaryConflict {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool, Slice x → vl gs x out.val = target10 x)
    (e : Fin 10 × Fin 10) (andContext orContext : Fin 10 → Bool)
    (witness : ∀ (a b : Bool),
      let xa := pairInput e.1 e.2 andContext a b
      let xo := pairInput e.1 e.2 orContext a b
      Slice xa ∧ target10 xa = (a && b) ∧
        Slice xo ∧ target10 xo = (a || b)) :
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
  obtain ⟨fa, ha⟩ := factor andContext
  obtain ⟨fo, ho⟩ := factor orContext
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b
    have h := witness a b
    exact (ha a b).trans ((computes _ h.1).trans h.2.1)
  · intro a b
    have h := witness a b
    exact (ho a b).trans ((computes _ h.2.2.1).trans h.2.2.2)

end Bridge

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
open PetersenScratch PetersenCutFormula

def topLabels : Finset (Fin 10) := {0, 1, 2, 4, 7, 8}

structure RankedSuffix where
  gates : List Gate
  output : Fin (10 + gates.length)
  clean : CleanL 10 gates
  binary_bound : nonNotCount gates ≤ 12
  live : ∀ w : Fin (10 + gates.length), w ≠ output → ∃ v, readEdge gates w v
  distinct : ∀ w, (predecessors clean w).Nodup
  computes : ∀ x : Fin 10 → Bool, Slice x → vl gates x output.val = target10 x
  top_at_output : ∀ i ∈ topLabels, firstInputBoundary clean output live i = output
  top_once : ∀ i ∈ topLabels, occurrences i (wireFormula 0 gates output.val) ≤ 1
  cut3_live : firstInputBoundary clean output live 3 ≠ output
  cut5_live : firstInputBoundary clean output live 5 ≠ output
  cut6_live : firstInputBoundary clean output live 6 ≠ output
  cut35 : firstInputBoundary clean output live 3 ≠ firstInputBoundary clean output live 5
  cut36 : firstInputBoundary clean output live 3 ≠ firstInputBoundary clean output live 6
  cut56 : firstInputBoundary clean output live 5 ≠ firstInputBoundary clean output live 6

theorem ranked_suffix (D : Circuit) (fan : FanInTwo D) (budget : nonNotCount D.gates ≤ 12)
    (agree : ∀ x : Fin 10 → Bool, Slice x → circuitFun 10 D x = target10 x)
    (dep : ∀ i, Dep (circuitFun 10 D) i)
    (still : ∀ (i : Fin 10) (b : Bool), ∃ x y : Fin 10 → Bool,
      circuitFun 10 D (Function.update x i b) ≠ circuitFun 10 D (Function.update y i b)) :
    Nonempty RankedSuffix := by
  classical
  have nc := dep_nc (dep 0)
  obtain ⟨gs, o, least, bound⟩ := least_with_budget D fan (fun _ => rfl) nc
  have valid : o < 10 + gs.length := by
    by_contra! h
    obtain ⟨x, y, different⟩ := least.ncv nc
    exact different ((vl_beyond gs x o h).trans (vl_beyond gs y o h).symm)
  let out : Fin (10 + gs.length) := ⟨o, valid⟩
  have live := least_read_edge_live least nc dep still valid
  have branchBound := threeForksOfBudget least.hcl out live (bound.trans budget)
  obtain ⟨label, locations, atTop, codes⟩ := normalizedCutsTop least.hcl out live branchBound
  have computes (x : Fin 10 → Bool) (hx : Slice x) : vl gs x out.val = target10 x :=
    (least.hev x).trans (agree x hx)
  have distinct := predecessors_nodup least nc
  have conflicts : ∀ e ∈ FiniteRanks.conflicts, label e.1 ≠ label e.2 := by
    intro e he eq
    have h := boundaryConflict least.hcl out live distinct computes e
      (FiniteRanks.row (FiniteRanks.contexts e).1)
      (FiniteRanks.row (FiniteRanks.contexts e).2)
      (fun a b => FiniteRanks.checkedContexts e he a b)
    exact h ((locations _ _).mp eq)
  have cuts : ∀ t, t < 3 → FiniteRanks.Cut label t := by
    intro t _
    obtain ⟨c, low, high⟩ := codes t
    refine ⟨c, low, ?_⟩
    intro x y vx vy rest eq
    exact (computes x vx).symm.trans ((high x y rest eq).trans (computes y vy))
  obtain ⟨l0,l1,l2,l4,l7,l8,e3,e5,e6,e35,e36,e56⟩ :=
    FiniteRanks.rank_pattern label conflicts cuts
  have top_ranks : ∀ i ∈ topLabels, label i = 3 := by
    intro i hi
    simp [topLabels] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  refine ⟨{
    gates := gs
    output := out
    clean := least.hcl
    binary_bound := bound.trans budget
    live := live
    distinct := distinct
    computes := computes
    top_at_output := fun i hi => (atTop i).mp (top_ranks i hi)
    top_once := ?_
    cut3_live := fun h => e3 ((atTop 3).mpr h)
    cut5_live := fun h => e5 ((atTop 5).mpr h)
    cut6_live := fun h => e6 ((atTop 6).mpr h)
    cut35 := fun h => e35 ((locations 3 5).mpr h)
    cut36 := fun h => e36 ((locations 3 6).mpr h)
    cut56 := fun h => e56 ((locations 5 6).mpr h)
  }⟩
  intro i hi
  have once := firstInputBoundary_occurrences_le_one least.hcl out live distinct 0 i
  rw [(atTop i).mp (top_ranks i hi)] at once
  exact once

theorem ranked_of_small (C : Circuit) (fan : FanInTwo C) (small : C.size < 16)
    (nots : NotSlots C) (first : FirstWire C) (computes : circuitFun 9 C = F) :
    Nonempty RankedSuffix := by
  have size : C.gates.length ≤ 15 := by
    change C.gates.length < 16 at small
    omega
  obtain ⟨D, fanD, budget, agree, dep, still⟩ := suffix_data C fan size nots first computes
  exact ranked_suffix D fanD budget agree dep still

theorem no_fork_of_top_path (B : RankedSuffix) (i : Fin 10) (hi : i ∈ topLabels)
    (w : Fin (10 + B.gates.length))
    (path : Relation.ReflTransGen (readEdge B.gates) (inputWire B.gates i) w) :
    ¬ FirstBranchRoute.Branches (readEdge B.gates) w := by
  intro fork
  have bound := FirstBranchRoute.ancestor_first_le (readEdge B.gates) B.output
    (read_order B.clean) B.live path (Or.inr fork)
  change firstInputBoundary B.clean B.output B.live i ≤ w at bound
  rw [B.top_at_output i hi] at bound
  have equal : w = B.output := le_antisymm (wire_le_output B.clean B.output B.live w) bound
  obtain ⟨v, _, edge, _, _⟩ := fork
  have increase := read_order B.clean edge
  rw [equal] at increase
  exact (not_lt_of_ge (wire_le_output B.clean B.output B.live v)) increase

end Bridge

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
open Relation
open scoped BigOperators

theorem leaves_le_one_add_forks {α : Type*} [DecidableEq α]
    (R : Finset α) (root : α) (kids : α → Finset α)
    (hroot : root ∈ R)
    (hparent : ∀ v ∈ R.erase root, ∃ w ∈ R, v ∈ kids w)
    (hdegree : ∀ w ∈ R, (kids w).card ≤ 2) :
    (R.filter (fun w => (kids w).card = 0)).card ≤
      1 + (R.filter (fun w => (kids w).card = 2)).card := by
  classical
  have hcovered : (R.erase root).card ≤ ∑ w ∈ R, (kids w).card := by
    refine Finset.card_le_card (t := R.biUnion kids) ?_ |>.trans Finset.card_biUnion_le
    intro v hv
    obtain ⟨w, hw, hchild⟩ := hparent v hv
    exact Finset.mem_biUnion.mpr ⟨w, hw, hchild⟩
  have hroot' := Finset.card_erase_add_one hroot
  have hsum :
      ∑ w ∈ R, ((kids w).card + (if (kids w).card = 0 then 1 else 0)) ≤
        ∑ w ∈ R, (1 + (if (kids w).card = 2 then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro w hw
    have hmax := hdegree w hw
    by_cases hz : (kids w).card = 0
    · simp [hz]
    by_cases ht : (kids w).card = 2
    · simp [ht]
    simp [hz, ht]
    omega
  have hleaf_count :
      (∑ w ∈ R, (if (kids w).card = 0 then (1 : ℕ) else 0)) =
        (R.filter (fun w => (kids w).card = 0)).card := by simp
  have hfork_count :
      (∑ w ∈ R, (if (kids w).card = 2 then (1 : ℕ) else 0)) =
        (R.filter (fun w => (kids w).card = 2)).card := by simp
  have hones : (∑ _w ∈ R, (1 : ℕ)) = R.card := by simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleaf_count, hfork_count, hones] at hsum
  omega


def BinaryWire {n : ℕ} {gs : List Gate} (w : Fin (n + gs.length)) : Prop :=
  ∃ (p : ℕ) (g : Gate), gs[p]? = some g ∧ w.val = n + p ∧
    (g.op = .and ∨ g.op = .or)

noncomputable def ancestorWires {n : ℕ} (gs : List Gate) (w : Fin (n + gs.length)) :
    Finset (Fin (n + gs.length)) := by
  classical
  exact Finset.univ.filter (fun v => ReflTransGen (readEdge gs) v w)

lemma mem_ancestorWires {n : ℕ} {gs : List Gate} {u w : Fin (n + gs.length)} :
    u ∈ ancestorWires gs w ↔ ReflTransGen (readEdge gs) u w := by
  classical
  simp [ancestorWires]

noncomputable def binaryAncestors {n : ℕ} (gs : List Gate) (w : Fin (n + gs.length)) :
    Finset (Fin (n + gs.length)) := by
  classical
  exact (ancestorWires gs w).filter (fun u => BinaryWire u)

lemma mem_binaryAncestors {n : ℕ} {gs : List Gate} {u w : Fin (n + gs.length)} :
    u ∈ binaryAncestors gs w ↔ ReflTransGen (readEdge gs) u w ∧ BinaryWire u := by
  classical
  simp [binaryAncestors, mem_ancestorWires]

private lemma predecessors_bound {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (w : Fin (n + gs.length)) :
    (predecessors clean w).length ≤ 2 ∧
      ((predecessors clean w).length = 2 → BinaryWire w) := by
  by_cases isInput : w.val < n
  · rw [predecessors_nil_input clean w isInput]
    simp
  · let p : ℕ := w.val - n
    have hp : p < gs.length := by
      have := w.isLt
      dsimp [p]
      omega
    have position : w.val = n + p := by
      dsimp [p]
      omega
    let g := gs[p]
    have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
    have len := congrArg List.length (predecessors_val_gate clean w atSlot position)
    change ((predecessors clean w).map Fin.val).length = g.inputs.length at len
    rw [List.length_map] at len
    rcases clean p g atSlot with ⟨op, a, ha, inputs⟩ | ⟨op, a, b, ha, hb, inputs⟩
    · simp [len, inputs]
    · exact ⟨by simp [len, inputs], fun _ => ⟨p, g, atSlot, position, op⟩⟩

theorem ancestor_of_pivot {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (w : Fin (n + gs.length)) (i : Fin n) {x y : Fin n → Bool}
    (agree : ∀ j, j ≠ i → x j = y j)
    (different : vl gs x w.val ≠ vl gs y w.val) :
    ReflTransGen (readEdge gs) (inputWire gs i) w := by
  by_contra noPath
  apply different
  apply agree_on_input_ancestors clean x y w
  intro j route
  apply agree j
  intro equal
  subst j
  exact noPath route

theorem binary_ancestors_card {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (w : Fin (n + gs.length)) (A : Finset (Fin n))
    (reachable : ∀ i ∈ A, ReflTransGen (readEdge gs) (inputWire gs i) w) :
    A.card ≤ 1 + (binaryAncestors gs w).card := by
  classical
  let R := ancestorWires gs w
  let kids (v : Fin (n + gs.length)) := (predecessors clean v).toFinset
  have root : w ∈ R := mem_ancestorWires.mpr ReflTransGen.refl
  have parent : ∀ v ∈ R.erase w, ∃ u ∈ R, v ∈ kids u := by
    intro v hv
    obtain ⟨different, ancestor⟩ := Finset.mem_erase.mp hv
    rcases ReflTransGen.cases_head (mem_ancestorWires.mp ancestor) with h | ⟨u, edge, rest⟩
    · exact (different h).elim
    · exact ⟨u, mem_ancestorWires.mpr rest,
        List.mem_toFinset.mpr ((predecessors_mem clean v u).mpr edge)⟩
  have card_kids (v : Fin (n + gs.length)) :
      (kids v).card ≤ (predecessors clean v).length :=
    List.toFinset_card_le (predecessors clean v)
  have maximum : ∀ v ∈ R, (kids v).card ≤ 2 := by
    intro v _
    exact (card_kids v).trans (predecessors_bound clean v).1
  have leafSubset : A.image (inputWire gs) ⊆ R.filter (fun v => (kids v).card = 0) := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have pri : (inputWire gs i).val < n := i.isLt
    exact Finset.mem_filter.mpr ⟨mem_ancestorWires.mpr (reachable i hi), by
      simp [kids, predecessors_nil_input clean _ pri]⟩
  have forkSubset : R.filter (fun v => (kids v).card = 2) ⊆ binaryAncestors gs w := by
    intro v hv
    obtain ⟨ancestor, two⟩ := Finset.mem_filter.mp hv
    obtain ⟨maxlen, isbinary⟩ := predecessors_bound clean v
    have lower := card_kids v
    exact mem_binaryAncestors.mpr ⟨mem_ancestorWires.mp ancestor, isbinary (by omega)⟩
  have inputInjective : Function.Injective (inputWire (n := n) gs) := by
    intro p q eq
    exact Fin.ext (congrArg (fun a : Fin (n + gs.length) => a.val) eq)
  rw [← Finset.card_image_of_injective A inputInjective]
  exact (Finset.card_le_card leafSubset).trans
    ((leaves_le_one_add_forks R w kids root parent maximum).trans
      (Nat.add_le_add_left (Finset.card_le_card forkSubset) 1))

theorem at_least_two_binary_ancestors {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (w : Fin (n + gs.length)) (A : Finset (Fin n)) (many : 3 ≤ A.card)
    (reachable : ∀ i ∈ A, ReflTransGen (readEdge gs) (inputWire gs i) w) :
    ∃ a b : Fin (n + gs.length), a ≠ b ∧
      a ∈ binaryAncestors gs w ∧ b ∈ binaryAncestors gs w := by
  have cardinality := binary_ancestors_card clean w A reachable
  have more : 1 < (binaryAncestors gs w).card := by omega
  obtain ⟨a, ha, b, hb, different⟩ := Finset.one_lt_card.mp more
  exact ⟨a, b, different, ha, hb⟩

theorem ancestor_wfree {n : ℕ} {gs : List Gate} {a w : Fin (n + gs.length)}
    {W : Finset (Fin n)} (path : ReflTransGen (readEdge gs) a w)
    (wfree : ∀ i ∈ W, ¬ ReflTransGen (readEdge gs) (inputWire gs i) w) :
    ∀ i ∈ W, ¬ ReflTransGen (readEdge gs) (inputWire gs i) a := by
  intro i hi p
  exact wfree i hi (p.trans path)

end Bridge

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
open PetersenScratch PetersenCutFormula PetersenCutIndependent
open Relation

theorem occurrence_iff_path {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (fallback i : Fin n) (w : Fin (n + gs.length)) :
    0 < occurrences i (wireFormula fallback gs w.val) ↔
      ReflTransGen (readEdge gs) (inputWire gs i) w := by
  classical
  let weight (a : Fin (n + gs.length)) := occurrences i (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs i).val < n := i.isLt
  have source : weight (inputWire gs i) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback i _ sourcePrimary, ite_eq_left rfl]
  have other : ∀ v : Fin (n + gs.length), v ≠ inputWire gs i →
      weight v = ((predecessors clean v).map weight).sum := by
    intro v different
    by_cases primary : v.val < n
    · simp [weight, wireFormula_count_input_fin fallback i v primary, different,
        predecessors_nil_input clean v primary]
    · let p := v.val - n
      have hp : p < gs.length := by have := v.isLt; dsimp [p]; omega
      have hv : v.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback i clean atSlot hv _
        (predecessors_val_gate clean v atSlot hv)
  change 0 < weight w ↔ _
  constructor
  · exact FirstBranchRoute.weight_positive_path (readEdge gs) (read_order clean)
      (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
      (inputWire gs i) other
  · intro path
    induction path with
    | refl => simp [source]
    | @tail a b previous edge ih =>
      have different : b ≠ inputWire gs i := by
        intro h
        have src_le := FirstBranchRoute.path_forward (readEdge gs) (read_order clean) previous
        have after := read_order clean edge
        rw [h] at after
        exact (not_lt_of_ge src_le) after
      rw [other b different]
      have membr : weight a ∈ (predecessors clean b).map weight :=
        List.mem_map.mpr ⟨a, (predecessors_mem clean a b).mpr edge, rfl⟩
      have le : weight a ≤ ((predecessors clean b).map weight).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ membr
      omega

def earlyIndex : Fin 3 → Fin 10 := ![3, 5, 6]

def earlySingleton (i : Fin 3) : Fin 3 → Bool := fun k => decide (k = i)

private theorem early_agrees (i : Fin 3) (bit : Bool) :
    ∀ j : Fin 10, j ≠ earlyIndex i →
      TopRows.early (fun _ => false) bit j = TopRows.early (earlySingleton i) bit j := by
  fin_cases i <;> cases bit <;> decide +kernel

private theorem early_rhs (i : Fin 3) :
    earlySingleton i 0 || earlySingleton i 1 || earlySingleton i 2 := by
  fin_cases i <;> decide +kernel

theorem early_two_binary (B : RankedSuffix) (w : Fin (10 + B.gates.length))
    (phase bit : Bool)
    (coeff : ∀ e : Fin 3 → Bool,
      (vl B.gates (TopRows.early e bit) w.val ^^ phase) = (e 0 || e 1 || e 2)) :
    ∃ a b : Fin (10 + B.gates.length),
      a ≠ b ∧ a ∈ binaryAncestors B.gates w ∧ b ∈ binaryAncestors B.gates w := by
  have path (i : Fin 3) : ReflTransGen (readEdge B.gates) (inputWire B.gates (earlyIndex i)) w := by
    apply ancestor_of_pivot B.clean w (earlyIndex i) (early_agrees i bit)
    intro same
    have start := coeff (fun _ => false)
    have finish := coeff (earlySingleton i)
    rw [same] at start
    have yes : (earlySingleton i 0 || earlySingleton i 1 || earlySingleton i 2) = true :=
      early_rhs i
    rw [yes] at finish
    exact Bool.false_ne_true (start.symm.trans finish)
  apply at_least_two_binary_ancestors B.clean w ({3,5,6} : Finset (Fin 10)) (by decide)
  intro i member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact path 0
  · exact path 1
  · exact path 2

theorem early_two_binary_wfree (B : RankedSuffix) (w : Fin (10 + B.gates.length))
    (phase bit : Bool)
    (coeff : ∀ e : Fin 3 → Bool,
      (vl B.gates (TopRows.early e bit) w.val ^^ phase) = (e 0 || e 1 || e 2))
    (noTop : ∀ i ∈ topLabels, occurrences i (wireFormula 0 B.gates w.val) = 0) :
    ∃ a b : Fin (10 + B.gates.length),
      a ≠ b ∧ BinaryWire a ∧ BinaryWire b ∧
      (∀ i ∈ topLabels, occurrences i (wireFormula 0 B.gates a.val) = 0) ∧
      (∀ i ∈ topLabels, occurrences i (wireFormula 0 B.gates b.val) = 0) := by
  obtain ⟨a,b,ne,ha,hb⟩ := early_two_binary B w phase bit coeff
  obtain ⟨pa, ba⟩ := mem_binaryAncestors.mp ha
  obtain ⟨pb, bb⟩ := mem_binaryAncestors.mp hb
  have free (i : Fin 10) (hi : i ∈ topLabels) :
      ¬ ReflTransGen (readEdge B.gates) (inputWire B.gates i) w := by
    intro path
    have occ := (occurrence_iff_path B.clean 0 i w).mpr path
    rw [noTop i hi] at occ
    exact (Nat.lt_irrefl _) occ
  have allFree {v : Fin (10 + B.gates.length)}
      (path : ReflTransGen (readEdge B.gates) v w) :
      ∀ i ∈ topLabels, occurrences i (wireFormula 0 B.gates v.val) = 0 := by
    intro i hi
    by_contra h
    have p := (occurrence_iff_path B.clean 0 i v).mp (Nat.pos_of_ne_zero h)
    exact free i hi (p.trans path)
  exact ⟨a,b,ne,ba,bb,allFree pa,allFree pb⟩

end Bridge

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous
open CircuitProof

theorem binary_wires_card_le {n : ℕ} {gs : List Gate}
    (wires : Finset (Fin (n + gs.length))) (hbin : ∀ w ∈ wires, BinaryWire w) :
    wires.card ≤ nonNotCount gs := by
  classical
  let indexWire : Fin gs.length ↪ Fin (n + gs.length) :=
    ⟨fun p => ⟨n + p.val, Nat.add_lt_add_left p.isLt n⟩, fun a b eq =>
      Fin.ext (Nat.add_left_cancel (congrArg Fin.val eq))⟩
  let good : Finset (Fin gs.length) := Finset.univ.filter (fun p => !(isNotGate gs[p].op))
  have goodCard : nonNotCount gs = good.card := by
    unfold nonNotCount
    conv_lhs => rw [← List.ofFn_getElem (xs := gs)]
    rw [List.countP_ofFn]
    rfl
  have inc : wires ⊆ good.map indexWire := by
    intro w member
    obtain ⟨p, g, atSlot, eq, op⟩ := hbin w member
    have pLt : p < gs.length := by
      have hw := w.isLt
      omega
    let i : Fin gs.length := ⟨p, pLt⟩
    have isG : gs[i] = g := by
      rw [List.getElem?_eq_getElem pLt] at atSlot
      exact Option.some.inj atSlot
    have inGood : i ∈ good := by
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [isG]
      rcases op with and | or <;> simp [and, or, isNotGate]
    exact Finset.mem_map.mpr ⟨i, inGood, Fin.ext eq.symm⟩
  calc
    wires.card ≤ (good.map indexWire).card := Finset.card_le_card inc
    _ = nonNotCount gs := by rw [Finset.card_map, goodCard]

end Bridge

namespace TaggedUnroll

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous
open PEqualNP.Outside.L_meta_3202.Previous.CircuitProof
open PEqualNP.Outside.L_meta_3202.Previous.PetersenScratch
open PEqualNP.Outside.L_meta_3202.Previous.PetersenCutFormula

 
inductive Tree (n : ℕ)
  | lit : Fin n → Bool → Tree n
  | and : ℕ → Tree n → Tree n → Tree n
  | or : ℕ → Tree n → Tree n → Tree n

def erase {n : ℕ} : Tree n → DMFormula n
  | .lit i phase => .lit i phase
  | .and _ a b => .and (erase a) (erase b)
  | .or _ a b => .or (erase a) (erase b)

def negate {n : ℕ} : Tree n → Tree n
  | .lit i phase => .lit i (!phase)
  | .and p a b => .or p (negate a) (negate b)
  | .or p a b => .and p (negate a) (negate b)

@[simp] theorem erase_negate {n : ℕ} (t : Tree n) : erase (negate t) = negFormula (erase t) := by
  induction t with
  | lit => rfl
  | and _ _ _ ha hb => simp [negate, erase, negFormula, ha, hb]
  | or _ _ _ ha hb => simp [negate, erase, negFormula, ha, hb]

def binaryTags {n : ℕ} : Tree n → Finset ℕ
  | .lit _ _ => ∅
  | .and p a b | .or p a b => insert p (binaryTags a ∪ binaryTags b)

def tagsBearing {n : ℕ} (i : Fin n) : Tree n → List ℕ
  | .lit _ _ => []
  | .and p a b | .or p a b =>
      if occurrences i (erase a) + occurrences i (erase b) = 0 then []
      else p :: (tagsBearing i a ++ tagsBearing i b)

@[simp] theorem binaryTags_negate {n : ℕ} (t : Tree n) :
    binaryTags (negate t) = binaryTags t := by
  induction t with
  | lit => rfl
  | and _ _ _ ha hb => simp [negate, binaryTags, ha, hb]
  | or _ _ _ ha hb => simp [negate, binaryTags, ha, hb]

@[simp] theorem tagsBearing_negate {n : ℕ} (i : Fin n) (t : Tree n) :
    tagsBearing i (negate t) = tagsBearing i t := by
  induction t with
  | lit => rfl
  | and _ _ _ ha hb =>
    simp [negate, tagsBearing, ha, hb, negFormula_occurrences]
  | or _ _ _ ha hb =>
    simp [negate, tagsBearing, ha, hb, negFormula_occurrences]

def unroll {n : ℕ} (fallback : Fin n) (gs : List Gate) (w : Nat) : Tree n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negate (unroll fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and w (unroll fallback gs a) (unroll fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or w (unroll fallback gs a) (unroll fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem erase_unroll {n : ℕ} (fallback : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) (w : ℕ) (hw : w < n + gs.length) :
    erase (unroll fallback gs w) = wireFormula fallback gs w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [unroll, wireFormula]
      simp [hi, erase]
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      have hn : ¬ n + p < n := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [unroll, wireFormula]
        simp [hn, hg, op, inputs, ha, ih a ha (by omega)]
      · rw [unroll, wireFormula]
        simp [hn, hg, op, inputs, ha, hb, erase, ih a ha (by omega), ih b hb (by omega)]
      · rw [unroll, wireFormula]
        simp [hn, hg, op, inputs, ha, hb, erase, ih a ha (by omega), ih b hb (by omega)]

theorem unroll_eval {n : ℕ} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + gs.length) :
    (erase (unroll fallback gs w)).eval x = vl gs x w := by
  rw [erase_unroll fallback hcl w hw, wireFormula_eval fallback hcl x w hw]

def footprint {n : ℕ} (W : Finset (Fin n)) (t : Tree n) : Finset (Fin n) :=
  W.filter fun i => 0 < occurrences i (erase t)

@[simp] theorem footprint_negate {n : ℕ} (W : Finset (Fin n)) (t : Tree n) :
    footprint W (negate t) = footprint W t := by
  simp [footprint, negFormula_occurrences]

private def rootProfile {n : ℕ} (q : ℕ) (U : Finset (Fin n)) : List (ℕ × Finset (Fin n)) :=
  if U.Nonempty then [(q, U)] else []

 
def profile {n : ℕ} (W : Finset (Fin n)) : Tree n → List (ℕ × Finset (Fin n))
  | .lit _ _ => []
  | .and q a b | .or q a b =>
    rootProfile q (footprint W a ∪ footprint W b) ++ profile W a ++ profile W b

@[simp] theorem profile_negate {n : ℕ} (W : Finset (Fin n)) (t : Tree n) :
    profile W (negate t) = profile W t := by
  induction t with
  | lit => rfl
  | and _ _ _ ha hb => simp [negate, profile, ha, hb]
  | or _ _ _ ha hb => simp [negate, profile, ha, hb]

@[simp] theorem footprint_and {n : ℕ} (W : Finset (Fin n)) (q : ℕ) (a b : Tree n) :
    footprint W (.and q a b) = footprint W a ∪ footprint W b := by
  ext i
  simp only [footprint, erase, occurrences, Finset.mem_filter, Finset.mem_union]
  by_cases hi : i ∈ W <;> simp [hi]

@[simp] theorem footprint_or {n : ℕ} (W : Finset (Fin n)) (q : ℕ) (a b : Tree n) :
    footprint W (.or q a b) = footprint W a ∪ footprint W b := by
  ext i
  simp only [footprint, erase, occurrences, Finset.mem_filter, Finset.mem_union]
  by_cases hi : i ∈ W <;> simp [hi]

private theorem root_profile_mem {n : ℕ} {q p : ℕ} {U X : Finset (Fin n)}
    (h : (p, X) ∈ rootProfile q U) : p = q ∧ X = U ∧ U.Nonempty := by
  unfold rootProfile at h
  split_ifs at h with he
  · have hpair : (p, X) = (q, U) := List.mem_singleton.mp h
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair, he⟩
  · simp at h

theorem profile_scope {n : ℕ} (W : Finset (Fin n)) (t : Tree n)
    {p : ℕ} {U : Finset (Fin n)} (h : (p, U) ∈ profile W t) :
    U.Nonempty ∧ U ⊆ footprint W t := by
  induction t with
  | lit => simp [profile] at h
  | and q a b ha hb =>
      simp only [profile, List.mem_append, footprint_and] at h ⊢
      rcases h with (hr | hl) | hr
      · obtain ⟨_, rfl, hs⟩ := root_profile_mem hr
        exact ⟨hs, le_rfl⟩
      · exact ⟨(ha hl).1, (ha hl).2.trans Finset.subset_union_left⟩
      · exact ⟨(hb hr).1, (hb hr).2.trans Finset.subset_union_right⟩
  | or q a b ha hb =>
      simp only [profile, List.mem_append, footprint_or] at h ⊢
      rcases h with (hr | hl) | hr
      · obtain ⟨_, rfl, hs⟩ := root_profile_mem hr
        exact ⟨hs, le_rfl⟩
      · exact ⟨(ha hl).1, (ha hl).2.trans Finset.subset_union_left⟩
      · exact ⟨(hb hr).1, (hb hr).2.trans Finset.subset_union_right⟩

def BinaryAt {n : ℕ} (gs : List Gate) (q : ℕ) : Prop :=
  ∃ j : Fin gs.length, q = n + j.val ∧ ((gs.get j).op = .and ∨ (gs.get j).op = .or)

theorem profile_sound {n : ℕ} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (W : Finset (Fin n)) (w : ℕ) (hw : w < n + gs.length) :
    ∀ q U, (q, U) ∈ profile W (unroll fallback gs w) →
      q ≤ w ∧ BinaryAt (n := n) gs q ∧ U = footprint W (unroll fallback gs q) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro q U ht
    by_cases hi : w < n
    · rw [unroll] at ht
      simp [hi, profile] at ht
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      have hn : ¬ n + p < n := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      have earlier (t : ℕ) (hT : t < n + p)
          (hm : (q, U) ∈ profile W (unroll fallback gs t)) :
          q ≤ n + p ∧ BinaryAt (n := n) gs q ∧ U = footprint W (unroll fallback gs q) := by
        obtain ⟨hq, hbin, hu⟩ := ih t hT (by omega) q U hm
        exact ⟨hq.trans hT.le, hbin, hu⟩
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [unroll] at ht
        simp [hn, hg, op, inputs, ha] at ht
        exact earlier a ha ht
      · have hU : unroll fallback gs (n + p) =
            .and (n+p) (unroll fallback gs a) (unroll fallback gs b) := by
          conv_lhs => rw [unroll]
          simp [hn, hg, op, inputs, ha, hb]
        rw [hU] at ht
        simp only [profile, List.mem_append] at ht
        rcases ht with (hr | hl) | hr
        · obtain ⟨rfl, rfl, _⟩ := root_profile_mem hr
          exact ⟨le_rfl, ⟨⟨p, hp⟩, rfl, Or.inl op⟩, by simp [hU]⟩
        · exact earlier a ha hl
        · exact earlier b hb hr
      · have hU : unroll fallback gs (n + p) =
            .or (n+p) (unroll fallback gs a) (unroll fallback gs b) := by
          conv_lhs => rw [unroll]
          simp [hn, hg, op, inputs, ha, hb]
        rw [hU] at ht
        simp only [profile, List.mem_append] at ht
        rcases ht with (hr | hl) | hr
        · obtain ⟨rfl, rfl, _⟩ := root_profile_mem hr
          exact ⟨le_rfl, ⟨⟨p, hp⟩, rfl, Or.inr op⟩, by simp [hU]⟩
        · exact earlier a ha hl
        · exact earlier b hb hr

def bearingTags {n : ℕ} (W : Finset (Fin n)) (t : Tree n) : List ℕ :=
  (profile W t).map Prod.fst

private theorem bearing_one_step {n : ℕ} (fallback : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) (W : Finset (Fin n)) {w a b : ℕ}
    (hw : w < n + gs.length) (ha : a < w) (hb : b < w)
    (hA : (bearingTags W (unroll fallback gs a)).Nodup)
    (hB : (bearingTags W (unroll fallback gs b)).Nodup)
    (honce : ∀ i ∈ W, occurrences i (erase (unroll fallback gs a)) +
        occurrences i (erase (unroll fallback gs b)) ≤ 1) :
    (((rootProfile w (footprint W (unroll fallback gs a) ∪ footprint W (unroll fallback gs b))).map
        Prod.fst) ++ bearingTags W (unroll fallback gs a) ++
      bearingTags W (unroll fallback gs b)).Nodup := by
  let A := unroll fallback gs a
  let B := unroll fallback gs b
  have separate : ∀ q ∈ bearingTags W A, ∀ r ∈ bearingTags W B, q ≠ r := by
    intro q hq r hr he
    subst r
    unfold bearingTags at hq hr
    obtain ⟨⟨qA, UA⟩, hA', rfl⟩ := List.mem_map.mp hq
    obtain ⟨⟨qB, UB⟩, hB', hq⟩ := List.mem_map.mp hr
    change qB = qA at hq
    subst qB
    have hUA := (profile_sound fallback hcl W a (ha.trans hw) _ _ hA').2.2
    have hUB := (profile_sound fallback hcl W b (hb.trans hw) _ _ hB').2.2
    have hpA := profile_scope W A hA'
    have hpB := profile_scope W B hB'
    obtain ⟨i, hi⟩ := hpA.1
    have h_iA := Finset.mem_filter.mp (hpA.2 hi)
    have h_iB := Finset.mem_filter.mp (hpB.2 ((hUA.trans hUB.symm) ▸ hi))
    have hlim := honce i h_iA.1
    have hposA := h_iA.2
    have hposB := h_iB.2
    dsimp [A] at hposA
    dsimp [B] at hposB
    omega
  have hconcat : (bearingTags W A ++ bearingTags W B).Nodup :=
    List.nodup_append.mpr ⟨hA, hB, separate⟩
  have notA : w ∉ bearingTags W A := by
    intro h
    unfold bearingTags at h
    obtain ⟨⟨q, U⟩, hm, rfl⟩ := List.mem_map.mp h
    have hq := (profile_sound fallback hcl W a (ha.trans hw) _ _ hm).1
    omega
  have notB : w ∉ bearingTags W B := by
    intro h
    unfold bearingTags at h
    obtain ⟨⟨q, U⟩, hm, rfl⟩ := List.mem_map.mp h
    have hq := (profile_sound fallback hcl W b (hb.trans hw) _ _ hm).1
    omega
  rw [List.append_assoc]
  unfold rootProfile
  split_ifs
  · simp [hconcat, notA, notB, A, B]
  · exact hconcat

 

theorem bearingTags_nodup {n : ℕ} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (W : Finset (Fin n)) (w : ℕ) (hw : w < n + gs.length)
    (honce : ∀ i ∈ W, occurrences i (erase (unroll fallback gs w)) ≤ 1) :
    (bearingTags W (unroll fallback gs w)).Nodup := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [unroll]
      simp [hi, bearingTags, profile]
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      have hn : ¬ n + p < n := by omega
      let g := gs[p]
      have hget : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hget with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · have hu : unroll fallback gs (n+p) = negate (unroll fallback gs a) := by
          conv_lhs => rw [unroll]
          simp [hn, hget, op, inputs, ha]
        rw [hu] at honce ⊢
        simp only [bearingTags, profile_negate]
        exact ih a ha (by omega) (by simpa only [erase_negate, negFormula_occurrences] using honce)
      · have hu : unroll fallback gs (n+p) =
            .and (n+p) (unroll fallback gs a) (unroll fallback gs b) := by
          conv_lhs => rw [unroll]
          simp [hn, hget, op, inputs, ha, hb]
        rw [hu] at honce ⊢
        simp only [erase, occurrences] at honce
        simp only [bearingTags, profile, List.map_append]
        exact bearing_one_step fallback hcl W hw ha hb
          (ih a ha (by omega) (fun i hi => by have := honce i hi; omega))
          (ih b hb (by omega) (fun i hi => by have := honce i hi; omega)) honce
      · have hu : unroll fallback gs (n+p) =
            .or (n+p) (unroll fallback gs a) (unroll fallback gs b) := by
          conv_lhs => rw [unroll]
          simp [hn, hget, op, inputs, ha, hb]
        rw [hu] at honce ⊢
        simp only [erase, occurrences] at honce
        simp only [bearingTags, profile, List.map_append]
        exact bearing_one_step fallback hcl W hw ha hb
          (ih a ha (by omega) (fun i hi => by have := honce i hi; omega))
          (ih b hb (by omega) (fun i hi => by have := honce i hi; omega)) honce

 
def forks {n : ℕ} (W : Finset (Fin n)) : Tree n → ℕ
  | .lit _ _ => 0
  | .and _ a b | .or _ a b => forks W a + forks W b +
      (if (footprint W a).Nonempty ∧ (footprint W b).Nonempty then 1 else 0)

 
def attachments {n : ℕ} (W : Finset (Fin n)) : Tree n → ℕ
  | .lit _ _ => 0
  | .and _ a b | .or _ a b => attachments W a + attachments W b +
      (if ((footprint W a).Nonempty ↔ ¬ (footprint W b).Nonempty) then 1 else 0)

theorem bearing_length {n : ℕ} (W : Finset (Fin n)) (t : Tree n) :
    (bearingTags W t).length = forks W t + attachments W t := by
  induction t with
  | lit => rfl
  | and q a b ha hb =>
    simp only [bearingTags, List.length_map] at ha hb
    by_cases hA : (footprint W a).Nonempty <;> by_cases hB : (footprint W b).Nonempty <;>
      simp [bearingTags, profile, rootProfile, forks, attachments, hA, hB] <;> omega
  | or q a b ha hb =>
    simp only [bearingTags, List.length_map] at ha hb
    by_cases hA : (footprint W a).Nonempty <;> by_cases hB : (footprint W b).Nonempty <;>
      simp [bearingTags, profile, rootProfile, forks, attachments, hA, hB] <;> omega

private theorem fork_ledger_step {n : ℕ} (W : Finset (Fin n)) (a b : Tree n)
    (hA : (footprint W a).card = forks W a + if (footprint W a).Nonempty then 1 else 0)
    (hB : (footprint W b).card = forks W b + if (footprint W b).Nonempty then 1 else 0)
    (honce : ∀ i ∈ W, occurrences i (erase a) + occurrences i (erase b) ≤ 1) :
    (footprint W a ∪ footprint W b).card = forks W a + forks W b +
      (if (footprint W a).Nonempty ∧ (footprint W b).Nonempty then 1 else 0) +
      (if (footprint W a ∪ footprint W b).Nonempty then 1 else 0) := by
  have hd : Disjoint (footprint W a) (footprint W b) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨hiW, hiA⟩ := Finset.mem_filter.mp hi
    have hjB := (Finset.mem_filter.mp hj).2
    have hh := honce i hiW
    omega
  rw [Finset.card_union_of_disjoint hd, hA, hB]
  by_cases ha : (footprint W a).Nonempty <;> by_cases hb : (footprint W b).Nonempty <;>
    simp [ha, hb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

 

theorem fork_ledger {n : ℕ} (W : Finset (Fin n)) (t : Tree n)
    (honce : ∀ i ∈ W, occurrences i (erase t) ≤ 1) :
    (footprint W t).card = forks W t + if (footprint W t).Nonempty then 1 else 0 := by
  induction t with
  | lit i phase =>
    by_cases hi : i ∈ W
    · have he : footprint W (.lit i phase) = {i} := by
        ext j
        by_cases hj : i = j
        · subst j; simp [footprint, erase, occurrences, hi]
        · simp [footprint, erase, occurrences, hj, Ne.symm]
      simp [he, forks]
    · have he : footprint W (.lit i phase) = ∅ := by
        ext j
        by_cases hj : i = j
        · subst j; simp [footprint, erase, occurrences, hi]
        · simp [footprint, erase, occurrences, hj]
      simp [he, forks]
  | and q a b ha hb =>
    simp only [erase, occurrences] at honce
    simp only [footprint_and, forks]
    exact fork_ledger_step W a b
      (ha fun i hi => by have := honce i hi; omega)
      (hb fun i hi => by have := honce i hi; omega) honce
  | or q a b ha hb =>
    simp only [erase, occurrences] at honce
    simp only [footprint_or, forks]
    exact fork_ledger_step W a b
      (ha fun i hi => by have := honce i hi; omega)
      (hb fun i hi => by have := honce i hi; omega) honce

end TaggedUnroll

namespace TaggedPaths

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.PetersenScratch
open PEqualNP.Outside.L_meta_3202.Previous.PetersenCutFormula
open PEqualNP.Outside.L_meta_3202.TaggedUnroll

abbrev occurs {n : ℕ} (i : Fin n) (t : Tree n) : ℕ := occurrences i (erase t)

structure Place (n : ℕ) where
  tag : ℕ
  conj : Bool
  sibling : Tree n

def leftHas {n : ℕ} (i : Fin n) (a : Tree n) : Bool :=
  decide (0 < occurs i a)

 
def path {n : ℕ} (i : Fin n) : Tree n → List (Place n)
  | .lit _ _ => []
  | .and q a b =>
    if leftHas i a then ⟨q, true, b⟩ :: path i a else ⟨q, true, a⟩ :: path i b
  | .or q a b =>
    if leftHas i a then ⟨q, false, b⟩ :: path i a else ⟨q, false, a⟩ :: path i b

def phase {n : ℕ} (i : Fin n) : Tree n → Bool
  | .lit _ s => s
  | .and _ a b | .or _ a b => if leftHas i a then phase i a else phase i b

def interpret {n : ℕ} {E : Type*} (x : E → Fin n → Bool) (s : Place n) :
    LastAbsorber.Step E :=
  ⟨s.conj, (erase s.sibling).eval ∘ x⟩

theorem eval_update_absent {n : ℕ} (t : Tree n) {i : Fin n} (h : occurs i t = 0)
    (x : Fin n → Bool) (b : Bool) :
    (erase t).eval (Function.update x i b) = (erase t).eval x := by
  induction t with
  | lit j phase =>
    have hne : j ≠ i := by
      intro he
      subst j
      change (if i = i then 1 else 0) = 0 at h
      simp at h
    simp [erase, DMFormula.eval, Function.update_of_ne hne]
  | and q a c ihA ihC =>
    change occurs i a + occurs i c = 0 at h
    simp only [erase, DMFormula.eval]
    rw [ihA (by omega), ihC (by omega)]
  | or q a c ihA ihC =>
    change occurs i a + occurs i c = 0 at h
    simp only [erase, DMFormula.eval]
    rw [ihA (by omega), ihC (by omega)]

 

theorem eval_update_path {n : ℕ} {E : Type*} (t : Tree n) (i : Fin n)
    (h : occurs i t = 1) (x : E → Fin n → Bool) (e : E) (b : Bool) :
    (erase t).eval (Function.update (x e) i b) =
      LastAbsorber.run ((path i t).map (interpret x)) e (if phase i t then b else !b) := by
  induction t with
  | lit j s =>
    have hi : j = i := by
      by_contra hn
      change (if j = i then 1 else 0) = 1 at h
      simp [hn] at h
    subst j
    simp [path, phase, LastAbsorber.run, erase, DMFormula.eval]
    rfl
  | and q a c ha hc =>
    change occurs i a + occurs i c = 1 at h
    by_cases hl : 0 < occurs i a
    · have hA : occurs i a = 1 := by omega
      have hC : occurs i c = 0 := by omega
      simp [path, phase, leftHas, hl, LastAbsorber.run, interpret, erase, DMFormula.eval,
        eval_update_absent c hC, ha hA]
    · have hA : occurs i a = 0 := by omega
      have hC : occurs i c = 1 := by omega
      simp [path, phase, leftHas, hl, LastAbsorber.run, interpret, erase, DMFormula.eval,
        eval_update_absent a hA, hc hC, Bool.and_comm]
  | or q a c ha hc =>
    change occurs i a + occurs i c = 1 at h
    by_cases hl : 0 < occurs i a
    · have hA : occurs i a = 1 := by omega
      have hC : occurs i c = 0 := by omega
      simp [path, phase, leftHas, hl, LastAbsorber.run, interpret, erase, DMFormula.eval,
        eval_update_absent c hC, ha hA]
    · have hA : occurs i a = 0 := by omega
      have hC : occurs i c = 1 := by omega
      simp [path, phase, leftHas, hl, LastAbsorber.run, interpret, erase, DMFormula.eval,
        eval_update_absent a hA, hc hC, Bool.or_comm]

private theorem run_order {E : Type*} (p : List (LastAbsorber.Step E)) (e : E) :
    LastAbsorber.run p e false = true → LastAbsorber.run p e true = true := by
  induction p with
  | nil => simp [LastAbsorber.run]
  | cons s tail ih =>
    cases h : s.conj <;> cases h' : s.other e <;> simp [LastAbsorber.run, h, h'] <;> exact ih

 
theorem phase_of_rise {n : ℕ} {E : Type*} (t : Tree n) (i : Fin n)
    (h : occurs i t = 1) (x : E → Fin n → Bool) (e : E)
    (h₀ : (erase t).eval (Function.update (x e) i false) = false)
    (h₁ : (erase t).eval (Function.update (x e) i true) = true) :
    phase i t = true := by
  rw [eval_update_path t i h x e false] at h₀
  rw [eval_update_path t i h x e true] at h₁
  cases hp : phase i t
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at h₀ h₁
    exact (Bool.false_ne_true (h₀.symm.trans (run_order _ e h₁))).elim
  · rfl

 


theorem guarded_path_sibling {n : ℕ} {E : Type*} (t : Tree n) (i : Fin n)
    (h : occurs i t = 1) (hphase : phase i t = true)
    (x : E → Fin n → Bool) (zero : E)
    (hoff : (erase t).eval (Function.update (x zero) i true) = false)
    (hon : ∀ e ≠ zero,
      (erase t).eval (Function.update (x e) i false) = false ∧
      (erase t).eval (Function.update (x e) i true) = true) :
    ∃ s ∈ path i t, s.conj = true ∧ (erase s.sibling).eval (x zero) = false ∧
      ∀ e ≠ zero, (erase s.sibling).eval (x e) = true := by
  let p := (path i t).map (interpret x)
  have hoff' : LastAbsorber.run p zero true = false := by
    simpa [p, eval_update_path t i h x zero, hphase] using hoff
  have hon' (e : E) (he : e ≠ zero) :
      LastAbsorber.run p e false = false ∧ LastAbsorber.run p e true = true := by
    simpa [p, eval_update_path t i h x e, hphase] using hon e he
  obtain ⟨s, hs, hkind, hz, ht⟩ := LastAbsorber.exists_and_guard p zero hoff' hon'
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hs
  exact ⟨source, hsource, hkind, hz, ht⟩

private def flipPlace {n : ℕ} (s : Place n) : Place n :=
  ⟨s.tag, !s.conj, negate s.sibling⟩

@[simp] private theorem occurs_negate {n : ℕ} (i : Fin n) (t : Tree n) :
    occurs i (negate t) = occurs i t := by
  unfold occurs
  rw [erase_negate, negFormula_occurrences]

private theorem path_negate {n : ℕ} (i : Fin n) (t : Tree n) :
    path i (negate t) = (path i t).map flipPlace := by
  induction t with
  | lit => rfl
  | and q a b ha hb =>
    by_cases h : 0 < occurs i a <;>
      simp [path, negate, leftHas, occurs_negate, h, ha, hb, flipPlace]
  | or q a b ha hb =>
    by_cases h : 0 < occurs i a <;>
      simp [path, negate, leftHas, occurs_negate, h, ha, hb, flipPlace]

private theorem negate_negate {n : ℕ} (t : Tree n) : negate (negate t) = t := by
  induction t with
  | lit i s => simp [negate]
  | and q a b ha hb => simp [negate, ha, hb]
  | or q a b ha hb => simp [negate, ha, hb]

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_3202.Previous.CircuitProof

 

theorem sibling_wire {n : ℕ} (fallback i : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (w : ℕ) (hw : w < n + gs.length) {s : Place n}
    (hs : s ∈ path i (unroll fallback gs w)) :
    ∃ a < w, ∃ flip : Bool, s.sibling =
      (if flip then negate (unroll fallback gs a) else unroll fallback gs a) := by
  induction w using Nat.strong_induction_on generalizing s with
  | ind w ih =>
    by_cases hinput : w < n
    · rw [unroll] at hs
      simp [hinput, path] at hs
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      have hn : ¬ n + p < n := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      have step (a b : ℕ) (ha : a < n+p) (hb : b < n+p) (op : Bool)
          (ht : s ∈ (if leftHas i (unroll fallback gs a) then
              ⟨n+p, op, unroll fallback gs b⟩ :: path i (unroll fallback gs a)
            else ⟨n+p, op, unroll fallback gs a⟩ :: path i (unroll fallback gs b))) :
          ∃ c < n+p, ∃ flip : Bool, s.sibling =
            (if flip then negate (unroll fallback gs c) else unroll fallback gs c) := by
        split_ifs at ht
        · rcases List.mem_cons.mp ht with rfl | hl
          · exact ⟨b, hb, false, rfl⟩
          · obtain ⟨c, hc, flip, h⟩ := ih a ha (ha.trans hw) hl
            exact ⟨c, hc.trans ha, flip, h⟩
        · rcases List.mem_cons.mp ht with rfl | hr
          · exact ⟨a, ha, false, rfl⟩
          · obtain ⟨c, hc, flip, h⟩ := ih b hb (hb.trans hw) hr
            exact ⟨c, hc.trans hb, flip, h⟩
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [unroll] at hs
        simp [hn, hg, op, inputs, ha, path_negate] at hs
        obtain ⟨s', hs', rfl⟩ := hs
        obtain ⟨c, hc, flip, h⟩ := ih a ha (ha.trans hw) hs'
        refine ⟨c, hc.trans ha, !flip, ?_⟩
        change negate s'.sibling = _
        cases flip
        · simp at h
          simp [h]
        · simp at h
          simp [h, negate_negate]
      · rw [unroll] at hs
        exact step a b ha hb true (by simpa [hn, hg, op, inputs, ha, hb, path] using hs)
      · rw [unroll] at hs
        exact step a b ha hb false (by simpa [hn, hg, op, inputs, ha, hb, path] using hs)

end TaggedPaths

namespace LcaPairs

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.PetersenScratch

def node {n : ℕ} (kind : Bool) (p q : DMFormula n) : DMFormula n :=
  if kind then .and p q else .or p q

def Split {n : ℕ} (i j : Fin n) (p q : DMFormula n) : Prop :=
  (0 < occurrences i p ∧ 0 < occurrences j q) ∨
  (0 < occurrences j p ∧ 0 < occurrences i q)

inductive LCA {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Prop
  | here (kind : Bool) (p q : DMFormula n) :
      Split i j p q → LCA i j (node kind p q) kind
  | left (kind op : Bool) (p q : DMFormula n) :
      LCA i j p kind → LCA i j (node op p q) kind
  | right (kind op : Bool) (p q : DMFormula n) :
      LCA i j q kind → LCA i j (node op p q) kind

def Fits {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (kind : Bool) : Prop :=
  ∀ a b, pairValue i j base p a b = binOp kind a b

@[simp] private theorem cnt_node {n : ℕ} (i : Fin n) (op : Bool) (p q : DMFormula n) :
    occurrences i (node op p q) = occurrences i p + occurrences i q := by
  cases op <;> rfl

@[simp] private theorem value_node {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (op : Bool) (p q : DMFormula n) (a b : Bool) :
    pairValue i j base (node op p q) a b =
      binOp op (pairValue i j base p a b) (pairValue i j base q a b) := by
  cases op <;> rfl

private theorem agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have E := h k (by simp [occurrences])
    simp [DMFormula.eval, E]
  | and p q hp hq =>
    simp only [DMFormula.eval]
    rw [hp (fun k hk => h k (by simp only [occurrences]; omega)),
        hq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q hp hq =>
    simp only [DMFormula.eval]
    rw [hp (fun k hk => h k (by simp only [occurrences]; omega)),
        hq (fun k hk => h k (by simp only [occurrences]; omega))]

theorem first_absent {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (hz : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply agree
  intro k hk
  have hne : k ≠ i := by rintro rfl; omega
  simp [pairInput, hne]

theorem second_absent {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (hz : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply agree
  intro k hk
  have hne : k ≠ j := by rintro rfl; omega
  simp [pairInput, hne]

private theorem both_absent {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (hi : occurrences i p = 0) (hj : occurrences j p = 0) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false :=
  (first_absent hi a false b).trans (second_absent hj false b false)

private theorem commute (op a b : Bool) : binOp op a b = binOp op b a := by
  cases op <;> cases a <;> cases b <;> rfl

private theorem neutral (op k c : Bool) (p : Bool → Bool → Bool)
    (h : ∀ a b, binOp op (p a b) c = binOp k a b) :
    ∀ a b, p a b = binOp k a b := by
  have hf := h false false
  have ht := h true true
  cases op <;> cases c <;> cases k <;> simp_all [binOp]

private theorem split_truth_preserves_kind :
    ∀ op k p0 p1 q0 q1 : Bool,
      (∀ a b : Bool, binOp op (if a then p1 else p0) (if b then q1 else q0) =
        binOp k a b) → op = k := by
  decide +kernel

private theorem from_independent_sides (op k : Bool) (P Q : Bool → Bool)
    (h : ∀ a b, binOp op (P a) (Q b) = binOp k a b) : op = k := by
  apply split_truth_preserves_kind op k (P false) (P true) (Q false) (Q true)
  intro a b
  cases a <;> cases b <;> apply h

private theorem per_node {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (kind op : Bool)
    (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q = 1)
    (hj : occurrences j p + occurrences j q = 1)
    (hfit : Fits i j base (node op p q) kind)
    (ip : occurrences i p = 1 → occurrences j p = 1 → Fits i j base p kind → LCA i j p kind)
    (iq : occurrences i q = 1 → occurrences j q = 1 → Fits i j base q kind → LCA i j q kind) :
    LCA i j (node op p q) kind := by
  by_cases hp : 0 < occurrences i p <;> by_cases hq : 0 < occurrences j p
  · have H : Fits i j base p kind := by
      unfold Fits
      apply neutral op kind (pairValue i j base q false false)
      intro a b
      have hv := hfit a b
      rw [value_node, both_absent (p := q) (by omega) (by omega) a b] at hv
      exact hv
    exact .left kind op p q (ip (by omega) (by omega) H)
  · have hs : op = kind := by
      apply from_independent_sides op kind
        (fun a => pairValue i j base p a false) (fun b => pairValue i j base q false b)
      intro a b
      have hv := hfit a b
      rw [value_node] at hv
      rw [second_absent (by omega) a b false,
          first_absent (by omega : occurrences i q = 0) a false b] at hv
      exact hv
    exact hs ▸ LCA.here op p q (Or.inl ⟨hp, by omega⟩)
  · have hs : op = kind := by
      apply from_independent_sides op kind
        (fun a => pairValue i j base q a false) (fun b => pairValue i j base p false b)
      intro a b
      have hv := hfit a b
      rw [value_node] at hv
      rw [first_absent (by omega : occurrences i p = 0) a false b,
          second_absent (by omega : occurrences j q = 0) a b false, commute] at hv
      exact hv
    exact hs ▸ LCA.here op p q (Or.inr ⟨hq, by omega⟩)
  · have H : Fits i j base q kind := by
      unfold Fits
      apply neutral op kind (pairValue i j base p false false)
      intro a b
      have hv := hfit a b
      rw [value_node] at hv
      rw [both_absent (p := p) (by omega) (by omega) a b, commute] at hv
      exact hv
    exact .right kind op p q (iq (by omega) (by omega) H)

theorem forced_lca {n : ℕ} (i j : Fin n) (hne : i ≠ j) (base : Fin n → Bool)
    (kind : Bool) (p : DMFormula n) (hi : occurrences i p = 1)
    (hj : occurrences j p = 1) (hfit : Fits i j base p kind) : LCA i j p kind := by
  induction p with
  | lit k s =>
    by_cases H : k = i
    · subst k
      simp [occurrences, hne] at hj
    · simp [occurrences, H] at hi
  | and p q ip iq =>
    exact per_node i j base kind true p q hi hj hfit ip iq
  | or p q ip iq =>
    exact per_node i j base kind false p q hi hj hfit ip iq

def Both {n : ℕ} (i j : Fin n) (t : DMFormula n) : Prop :=
  0 < occurrences i t ∧ 0 < occurrences j t

instance {n : ℕ} (i j : Fin n) (p q : DMFormula n) : Decidable (Split i j p q) := by
  unfold Split
  infer_instance

instance {n : ℕ} (i j : Fin n) (p : DMFormula n) : Decidable (Both i j p) := by
  unfold Both
  infer_instance

def kindAt {n : ℕ} (i j : Fin n) : DMFormula n → Option Bool
  | .lit _ _ => none
  | .and a b =>
    if Split i j a b then some true else if Both i j a then kindAt i j a else kindAt i j b
  | .or a b =>
    if Split i j a b then some false else if Both i j a then kindAt i j a else kindAt i j b

theorem kindAt_node {n : ℕ} (i j : Fin n) (op : Bool) (p q : DMFormula n) :
    kindAt i j (node op p q) =
      if Split i j p q then some op else if Both i j p then kindAt i j p else kindAt i j q := by
  cases op <;> rfl

theorem LCA.occurs {n : ℕ} {i j : Fin n} {p : DMFormula n} {k : Bool}
    (h : LCA i j p k) : Both i j p := by
  induction h with
  | here op a b hs =>
    unfold Split at hs
    simp only [Both, cnt_node]
    omega
  | left kind op a b h ih =>
    unfold Both at ih
    simp only [Both, cnt_node]
    omega
  | right kind op a b h ih =>
    unfold Both at ih
    simp only [Both, cnt_node]
    omega

theorem LCA.kind {n : ℕ} {i j : Fin n} {p : DMFormula n} {k : Bool}
    (h : LCA i j p k) (hi : occurrences i p ≤ 1)
    (hj : occurrences j p ≤ 1) : kindAt i j p = some k := by
  induction h with
  | here op a b hs =>
    rw [kindAt_node, ite_eq_left hs]
  | left kind op a b h ih =>
    simp only [cnt_node] at hi hj
    have hb := h.occurs
    have hn : ¬ Split i j a b := by
      unfold Both at hb
      unfold Split
      omega
    rw [kindAt_node, ite_eq_right hn, ite_eq_left hb]
    exact ih (by omega) (by omega)
  | right kind op a b h ih =>
    simp only [cnt_node] at hi hj
    have hb := h.occurs
    unfold Both at hb
    have hn : ¬ Split i j a b := by
      unfold Split
      omega
    have ha : ¬ Both i j a := by
      unfold Both
      omega
    rw [kindAt_node, ite_eq_right hn, ite_eq_right ha]
    exact ih (by omega) (by omega)

inductive Context (n : ℕ)
  | hole
  | left : Bool → Context n → DMFormula n → Context n
  | right : Bool → DMFormula n → Context n → Context n

def Context.fill {n : ℕ} : Context n → DMFormula n → DMFormula n
  | .hole, t => t
  | .left op p r, t => node op (p.fill t) r
  | .right op l p, t => node op l (p.fill t)

theorem Context.occ_le {n : ℕ} (ctx : Context n) (t : DMFormula n) (i : Fin n) :
    occurrences i t ≤ occurrences i (ctx.fill t) := by
  induction ctx with
  | hole => rfl
  | left op c r hc =>
    simp only [Context.fill, cnt_node]
    omega
  | right op l c hc =>
    simp only [Context.fill, cnt_node]
    omega

theorem Context.lift {n : ℕ} (ctx : Context n) {t : DMFormula n} {i j : Fin n}
    {k : Bool} (h : LCA i j t k) : LCA i j (ctx.fill t) k := by
  induction ctx with
  | hole => exact h
  | left op c r hc => exact .left k op (c.fill t) r hc
  | right op l c hc => exact .right k op l (c.fill t) hc

theorem LCA.locate {n : ℕ} {i j : Fin n} {p : DMFormula n} {k : Bool}
    (h : LCA i j p k) :
    ∃ (ctx : Context n) (a b : DMFormula n),
      p = ctx.fill (node k a b) ∧ Split i j a b := by
  induction h with
  | here op a b hs =>
    exact ⟨.hole, a, b, rfl, hs⟩
  | left kind op a b _ ih =>
    obtain ⟨ctx, l, r, e, hs⟩ := ih
    exact ⟨.left op ctx b, l, r, by rw [e]; rfl, hs⟩
  | right kind op a b _ ih =>
    obtain ⟨ctx, l, r, e, hs⟩ := ih
    exact ⟨.right op a ctx, l, r, by rw [e]; rfl, hs⟩

theorem and_excludes_third {n : ℕ} (ctx : Context n) (p q : DMFormula n)
    (i j v : Fin n)
    (hi : occurrences i (ctx.fill (node true p q)) ≤ 1)
    (hj : occurrences j (ctx.fill (node true p q)) ≤ 1)
    (hv : occurrences v (ctx.fill (node true p q)) ≤ 1)
    (hs : Split i j p q)
    (vi : kindAt i v (ctx.fill (node true p q)) = some false)
    (vj : kindAt j v (ctx.fill (node true p q)) = some false) :
    occurrences v (node true p q) = 0 := by
  by_contra hn
  have hvp : 0 < occurrences v p ∨ 0 < occurrences v q := by
    simp only [cnt_node] at hn
    omega
  unfold Split at hs
  rcases hs with (⟨ip, jq⟩ | ⟨jp, iq⟩) <;> rcases hvp with vp | vq
  · have hk := (ctx.lift (LCA.here true p q (i := j) (j := v)
      (Or.inr ⟨vp, jq⟩))).kind hj hv
    rw [vj] at hk
    contradiction
  · have hk := (ctx.lift (LCA.here true p q (i := i) (j := v)
      (Or.inl ⟨ip, vq⟩))).kind hi hv
    rw [vi] at hk
    contradiction
  · have hk := (ctx.lift (LCA.here true p q (i := i) (j := v)
      (Or.inr ⟨vp, iq⟩))).kind hi hv
    rw [vi] at hk
    contradiction
  · have hk := (ctx.lift (LCA.here true p q (i := j) (j := v)
      (Or.inl ⟨jp, vq⟩))).kind hj hv
    rw [vj] at hk
    contradiction

private theorem kind_swap_node {n : ℕ} (i j : Fin n) (op : Bool) (p q : DMFormula n)
    (ip : kindAt i j p = kindAt j i p) (iq : kindAt i j q = kindAt j i q) :
    kindAt i j (node op p q) = kindAt j i (node op p q) := by
  have hs : Split i j p q ↔ Split j i p q := or_comm
  have hb : Both i j p ↔ Both j i p := and_comm
  rw [kindAt_node, kindAt_node, ip, iq]
  by_cases a : Split i j p q
  · simp [a, hs.mp a]
  · have a' : ¬ Split j i p q := fun h => a (hs.mpr h)
    by_cases b : Both i j p
    · simp [a, a', b, hb.mp b]
    · have b' : ¬ Both j i p := fun h => b (hb.mpr h)
      simp [a, a', b, b']

theorem kindAt_swap {n : ℕ} (i j : Fin n) (t : DMFormula n) :
    kindAt i j t = kindAt j i t := by
  induction t with
  | lit => rfl
  | and p q ip iq => exact kind_swap_node i j true p q ip iq
  | or p q ip iq => exact kind_swap_node i j false p q ip iq

private theorem in_left_kind {n : ℕ} (a b : Fin n) (op : Bool) (p q : DMFormula n)
    (hpa : 0 < occurrences a p) (hpb : 0 < occurrences b p)
    (hqa : occurrences a q = 0) (hqb : occurrences b q = 0) :
    kindAt a b (node op p q) = kindAt a b p := by
  have hn : ¬ Split a b p q := by
    unfold Split
    omega
  rw [kindAt_node, ite_eq_right hn, ite_eq_left ⟨hpa, hpb⟩]

private theorem in_right_kind {n : ℕ} (a b : Fin n) (op : Bool) (p q : DMFormula n)
    (hpa : occurrences a p = 0) (hpb : occurrences b p = 0) :
    kindAt a b (node op p q) = kindAt a b q := by
  have hn : ¬ Split a b p q := by
    unfold Split
    omega
  have ha : ¬ Both a b p := by
    unfold Both
    omega
  rw [kindAt_node, ite_eq_right hn, ite_eq_right ha]

theorem Context.outside_kind {n : ℕ} (ctx : Context n) (t : DMFormula n)
    (a c d : Fin n) (pa : 0 < occurrences a t) (pc : 0 < occurrences c t)
    (zd : occurrences d t = 0)
    (oa : occurrences a (ctx.fill t) ≤ 1)
    (oc : occurrences c (ctx.fill t) ≤ 1)
    (od : occurrences d (ctx.fill t) = 1) :
    kindAt a d (ctx.fill t) = kindAt c d (ctx.fill t) := by
  induction ctx with
  | hole =>
    simp only [Context.fill] at od
    omega
  | left op inner r ih =>
    simp only [Context.fill, cnt_node] at oa oc od
    simp only [Context.fill]
    have ma : 0 < occurrences a (inner.fill t) := pa.trans_le (inner.occ_le t a)
    have mc : 0 < occurrences c (inner.fill t) := pc.trans_le (inner.occ_le t c)
    by_cases dh : 0 < occurrences d (inner.fill t)
    · rw [in_left_kind a d op (inner.fill t) r ma dh (by omega) (by omega),
          in_left_kind c d op (inner.fill t) r mc dh (by omega) (by omega)]
      exact ih (by omega) (by omega) (by omega)
    · have ds : 0 < occurrences d r := by omega
      rw [kindAt_node, kindAt_node,
          ite_eq_left (show Split a d (inner.fill t) r from Or.inl ⟨ma, ds⟩),
          ite_eq_left (show Split c d (inner.fill t) r from Or.inl ⟨mc, ds⟩)]
  | right op l inner ih =>
    simp only [Context.fill, cnt_node] at oa oc od
    simp only [Context.fill]
    have ma : 0 < occurrences a (inner.fill t) := pa.trans_le (inner.occ_le t a)
    have mc : 0 < occurrences c (inner.fill t) := pc.trans_le (inner.occ_le t c)
    by_cases dh : 0 < occurrences d (inner.fill t)
    · rw [in_right_kind a d op l (inner.fill t) (by omega) (by omega),
          in_right_kind c d op l (inner.fill t) (by omega) (by omega)]
      exact ih (by omega) (by omega) (by omega)
    · have ds : 0 < occurrences d l := by omega
      rw [kindAt_node, kindAt_node,
          ite_eq_left (show Split a d l (inner.fill t) from Or.inr ⟨ds, ma⟩),
          ite_eq_left (show Split c d l (inner.fill t) from Or.inr ⟨ds, mc⟩)]

theorem and_excludes_via_partner {n : ℕ} (ctx : Context n) (p q : DMFormula n)
    (i j v d : Fin n)
    (hi : occurrences i (ctx.fill (node true p q)) ≤ 1)
    (hj : occurrences j (ctx.fill (node true p q)) ≤ 1)
    (hv : occurrences v (ctx.fill (node true p q)) ≤ 1)
    (hd : occurrences d (ctx.fill (node true p q)) = 1)
    (hs : Split i j p q)
    (id : kindAt i d (ctx.fill (node true p q)) = some false)
    (jd : kindAt j d (ctx.fill (node true p q)) = some false)
    (vd : kindAt v d (ctx.fill (node true p q)) = some true) :
    occurrences v (node true p q) = 0 := by
  have zd := and_excludes_third ctx p q i j d hi hj (by omega) hs id jd
  by_contra nv
  have ip : 0 < occurrences i (node true p q) := (LCA.here true p q hs).occurs.1
  have H := ctx.outside_kind (node true p q) i v d ip (by omega) zd hi hv hd
  rw [id, vd] at H
  contradiction

private theorem eval_node' {n : ℕ} (op : Bool) (p q : DMFormula n) (x : Fin n → Bool) :
    (node op p q).eval x = binOp op (p.eval x) (q.eval x) := by
  cases op <;> rfl

private theorem bin_mono_left :
    ∀ op a b c : Bool, a ≤ b → binOp op a c ≤ binOp op b c := by decide +kernel

private theorem bin_mono_right :
    ∀ op a b c : Bool, a ≤ b → binOp op c a ≤ binOp op c b := by decide +kernel

theorem Context.eval_mono_at {n : ℕ} (ctx : Context n) (t : DMFormula n)
    (i : Fin n) (x y : Fin n → Bool)
    (ha : ∀ k, k ≠ i → x k = y k)
    (hc : occurrences i (ctx.fill t) = occurrences i t)
    (ht : t.eval x ≤ t.eval y) :
    (ctx.fill t).eval x ≤ (ctx.fill t).eval y := by
  induction ctx with
  | hole => exact ht
  | left op c r ih =>
    simp only [Context.fill, cnt_node] at hc
    have hc' := c.occ_le t i
    have hr : r.eval x = r.eval y := by
      apply agree
      intro k hk
      apply ha
      rintro rfl
      omega
    simp only [Context.fill, eval_node', hr]
    exact bin_mono_left op _ _ _ (ih (by omega))
  | right op l c ih =>
    simp only [Context.fill, cnt_node] at hc
    have hc' := c.occ_le t i
    have hl : l.eval x = l.eval y := by
      apply agree
      intro k hk
      apply ha
      rintro rfl
      omega
    simp only [Context.fill, eval_node', hl]
    exact bin_mono_right op _ _ _ (ih (by omega))

theorem Context.eval_eq_at {n : ℕ} (ctx : Context n) (t : DMFormula n)
    (i : Fin n) (x y : Fin n → Bool)
    (ha : ∀ k, k ≠ i → x k = y k)
    (hc : occurrences i (ctx.fill t) = occurrences i t)
    (ht : t.eval x = t.eval y) :
    (ctx.fill t).eval x = (ctx.fill t).eval y := by
  apply le_antisymm
  · exact ctx.eval_mono_at t i x y ha hc ht.le
  · exact ctx.eval_mono_at t i y x (fun k hk => (ha k hk).symm) hc ht.symm.le

theorem and_left_nonliteral {n : ℕ} (ctx : Context n) (p q : DMFormula n)
    (i j : Fin n) (_ne : i ≠ j) (base pivot : Fin n → Bool)
    (ip : occurrences i p = 1) (jq : occurrences j q = 1)
    (ot : occurrences i (ctx.fill (node true p q)) ≤ 1)
    (oj : occurrences j (ctx.fill (node true p q)) ≤ 1)
    (fit : Fits i j base (ctx.fill (node true p q)) true)
    (test : ∀ b, pairValue i j pivot (ctx.fill (node true p q)) false b = b) :
    ∀ k s, p ≠ .lit k s := by
  intro k s eq
  subst p
  have ki : k = i := by
    by_contra h
    simp [occurrences, h] at ip
  subst k
  let a : DMFormula n := .lit i s
  change occurrences i a = 1 at ip
  change occurrences i (ctx.fill (node true a q)) ≤ 1 at ot
  change occurrences j (ctx.fill (node true a q)) ≤ 1 at oj
  change Fits i j base (ctx.fill (node true a q)) true at fit
  change (∀ b, pairValue i j pivot (ctx.fill (node true a q)) false b = b) at test
  have ia := ctx.occ_le (node true a q) i
  have ja := ctx.occ_le (node true a q) j
  simp only [cnt_node] at ia ja
  have iEq : occurrences i (ctx.fill (node true a q)) =
      occurrences i (node true a q) := by simp only [cnt_node]; omega
  have jEq : occurrences j (ctx.fill (node true a q)) =
      occurrences j (node true a q) := by simp only [cnt_node]; omega
  cases s
  · let x := pairInput i j base true true
    let y := pairInput i j base false true
    have ha : ∀ k, k ≠ i → x k = y k := by
      intro k hk
      simp [x, y, pairInput, hk]
    have hlocal : (node true a q).eval x ≤ (node true a q).eval y := by
      simp [eval_node', binOp, a, DMFormula.eval, x, pairInput]
    have h := ctx.eval_mono_at (node true a q) i x y ha iEq hlocal
    change pairValue i j base (ctx.fill (node true a q)) true true ≤
        pairValue i j base (ctx.fill (node true a q)) false true at h
    rw [fit true true, fit false true] at h
    exact (by decide : ¬ (true ≤ false)) (by simpa [binOp] using h)
  · let x := pairInput i j pivot false false
    let y := pairInput i j pivot false true
    have ha : ∀ k, k ≠ j → x k = y k := by
      intro k hk
      simp [x, y, pairInput, hk]
    have hlocal : (node true a q).eval x = (node true a q).eval y := by
      simp [eval_node', binOp, a, DMFormula.eval, x, y, pairInput]
    have h := ctx.eval_eq_at (node true a q) j x y ha jEq hlocal
    change pairValue i j pivot (ctx.fill (node true a q)) false false =
        pairValue i j pivot (ctx.fill (node true a q)) false true at h
    rw [test false, test true] at h
    contradiction

theorem Context.eval_eq_focus {n : ℕ} (ctx : Context n) (p q : DMFormula n)
    (x : Fin n → Bool) (h : p.eval x = q.eval x) :
    (ctx.fill p).eval x = (ctx.fill q).eval x := by
  induction ctx with
  | hole => exact h
  | left op c r ih => simp only [Context.fill, eval_node', ih]
  | right op l c ih => simp only [Context.fill, eval_node', ih]

theorem Context.occ_eq_focus {n : ℕ} (ctx : Context n) (p q : DMFormula n)
    (i : Fin n) (h : occurrences i p = occurrences i q) :
    occurrences i (ctx.fill p) = occurrences i (ctx.fill q) := by
  induction ctx with
  | hole => exact h
  | left op c r ih => simp only [Context.fill, cnt_node, ih]
  | right op l c ih => simp only [Context.fill, cnt_node, ih]

private theorem swap_input {n : ℕ} (i j : Fin n) (ne : i ≠ j)
    (base : Fin n → Bool) (a b : Bool) :
    pairInput i j base a b = pairInput j i base b a := by
  funext k
  by_cases ki : k = i
  · subst k
    simp [pairInput, ne]
  · by_cases kj : k = j
    · subst k
      simp [pairInput, ki]
    · simp [pairInput, ki, kj]

theorem pair_value_swap {n : ℕ} (i j : Fin n) (ne : i ≠ j)
    (base : Fin n → Bool) (t : DMFormula n) (a b : Bool) :
    pairValue i j base t a b = pairValue j i base t b a := by
  unfold pairValue
  rw [swap_input i j ne base a b]

private theorem swap_and_value {n : ℕ} (ctx : Context n) (p q : DMFormula n)
    (i j : Fin n) (ne : i ≠ j) (base : Fin n → Bool) (a b : Bool) :
    pairValue j i base (ctx.fill (node true q p)) b a =
      pairValue i j base (ctx.fill (node true p q)) a b := by
  unfold pairValue
  rw [← swap_input i j ne base a b]
  apply Context.eval_eq_focus
  simp [eval_node', commute]

theorem and_right_nonliteral {n : ℕ} (ctx : Context n) (p q : DMFormula n)
    (i j : Fin n) (ne : i ≠ j) (base pivot : Fin n → Bool)
    (ip : occurrences i p = 1) (jq : occurrences j q = 1)
    (ot : occurrences i (ctx.fill (node true p q)) ≤ 1)
    (oj : occurrences j (ctx.fill (node true p q)) ≤ 1)
    (fit : Fits i j base (ctx.fill (node true p q)) true)
    (test : ∀ a, pairValue i j pivot (ctx.fill (node true p q)) a false = a) :
    ∀ k s, q ≠ .lit k s := by
  apply and_left_nonliteral ctx q p j i ne.symm base pivot jq ip
  · rw [ctx.occ_eq_focus _ (node true p q) _ (by simp [Nat.add_comm])]
    exact oj
  · rw [ctx.occ_eq_focus _ (node true p q) _ (by simp [Nat.add_comm])]
    exact ot
  · intro b a
    rw [swap_and_value ctx p q i j ne, fit a b, commute]
  · intro a
    rw [swap_and_value ctx p q i j ne, test a]

def positiveCount {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k sign => if k = i then (if sign then 1 else 0) else 0
  | .and a b | .or a b => positiveCount i a + positiveCount i b

theorem positive_le_occurrences {n : ℕ} (i : Fin n) (p : DMFormula n) :
    positiveCount i p ≤ occurrences i p := by
  induction p with
  | lit k s => cases s <;> simp [positiveCount, occurrences]
  | and p q ip iq => simp only [positiveCount, occurrences]; omega
  | or p q ip iq => simp only [positiveCount, occurrences]; omega

private theorem not_antitone : ∀ a b : Bool, a ≤ b → (!b) ≤ (!a) := by
  decide +kernel

theorem no_positive_decreases {n : ℕ} (i : Fin n) (t : DMFormula n)
    (x y : Fin n → Bool) (ha : ∀ k, k ≠ i → x k = y k) (hi : x i ≤ y i)
    (zero : positiveCount i t = 0) : t.eval y ≤ t.eval x := by
  induction t with
  | lit k s =>
    by_cases hki : k=i
    · subst k
      cases s
      · exact not_antitone _ _ hi
      · simp [positiveCount] at zero
    · simp [DMFormula.eval, ha k hki]
  | and p q ip iq =>
    simp only [positiveCount] at zero
    change binOp true (p.eval y) (q.eval y) ≤ binOp true (p.eval x) (q.eval x)
    exact (bin_mono_left true _ _ _ (ip (by omega))).trans
      (bin_mono_right true _ _ _ (iq (by omega)))
  | or p q ip iq =>
    simp only [positiveCount] at zero
    change binOp false (p.eval y) (q.eval y) ≤ binOp false (p.eval x) (q.eval x)
    exact (bin_mono_left false _ _ _ (ip (by omega))).trans
      (bin_mono_right false _ _ _ (iq (by omega)))

theorem positive_of_pivot {n : ℕ} (i : Fin n) (t : DMFormula n)
    (x y : Fin n → Bool) (ha : ∀ k, k ≠ i → x k = y k) (hi : x i ≤ y i)
    (hx : t.eval x = false) (hy : t.eval y = true) :
    0 < positiveCount i t := by
  by_contra hz
  have h := no_positive_decreases i t x y ha hi (by omega)
  rw [hx, hy] at h
  exact (by decide : ¬(true ≤ false)) h

theorem pair_positive_left {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (kind : Bool) (t : DMFormula n) (h : Fits i j base t kind) :
    0 < positiveCount i t := by
  apply positive_of_pivot i t (pairInput i j base false kind) (pairInput i j base true kind)
  · intro k hk
    simp [pairInput, hk]
  · simp [pairInput]
  · change pairValue i j base t false kind = false
    rw [h]
    cases kind <;> rfl
  · change pairValue i j base t true kind = true
    rw [h]
    cases kind <;> rfl

theorem pair_positive_right {n : ℕ} (i j : Fin n) (ne : i ≠ j)
    (base : Fin n → Bool) (kind : Bool) (t : DMFormula n)
    (h : Fits i j base t kind) : 0 < positiveCount j t := by
  apply pair_positive_left j i base kind t
  intro b a
  unfold pairValue
  rw [← swap_input i j ne base a b]
  change pairValue i j base t a b = binOp kind b a
  rw [h, commute]

end LcaPairs

namespace AttachmentMarks

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.PetersenScratch
open PEqualNP.Outside.L_meta_3202.TaggedUnroll

 
def support {n : ℕ} (W : Finset (Fin n)) (t : DMFormula n) : Finset (Fin n) :=
  W.filter fun i => 0 < occurrences i t

private def mark {n : ℕ} (A B : Finset (Fin n)) : List (Finset (Fin n)) :=
  if A.Nonempty ↔ ¬ B.Nonempty then [A ∪ B] else []

 

def marks {n : ℕ} (W : Finset (Fin n)) : DMFormula n → List (Finset (Fin n))
  | .lit _ _ => []
  | .and l r | .or l r => mark (support W l) (support W r) ++ marks W l ++ marks W r

def node {n : ℕ} (conj : Bool) (l r : DMFormula n) : DMFormula n :=
  if conj then .and l r else .or l r

theorem marks_node {n : ℕ} (W : Finset (Fin n)) (conj : Bool) (l r : DMFormula n) :
    marks W (node conj l r) =
      mark (support W l) (support W r) ++ marks W l ++ marks W r := by
  cases conj <;> rfl

theorem mark_left {n : ℕ} (W : Finset (Fin n)) (op : Bool) (l r : DMFormula n)
    (hL : (support W l).Nonempty) (hR : support W r = ∅) :
    support W l ∈ marks W (node op l r) := by
  simp [marks_node, mark, hL, hR]

theorem mark_right {n : ℕ} (W : Finset (Fin n)) (op : Bool) (l r : DMFormula n)
    (hL : support W l = ∅) (hR : (support W r).Nonempty) :
    support W r ∈ marks W (node op l r) := by
  simp [marks_node, mark, hL, hR]

theorem mem_marks_left {n : ℕ} (W : Finset (Fin n)) (op : Bool) (l r : DMFormula n)
    {A : Finset (Fin n)} (h : A ∈ marks W l) :
    A ∈ marks W (node op l r) := by
  simp [marks_node, h]

theorem mem_marks_right {n : ℕ} (W : Finset (Fin n)) (op : Bool) (l r : DMFormula n)
    {A : Finset (Fin n)} (h : A ∈ marks W r) :
    A ∈ marks W (node op l r) := by
  simp [marks_node, h]

theorem count_marks {n : ℕ} (W : Finset (Fin n)) (t : Tree n) :
    (marks W (erase t)).length = attachments W t := by
  have hsupport (a : Tree n) : support W (erase a) = footprint W a := rfl
  induction t with
  | lit => rfl
  | and q a b ha hb =>
    simp only [erase, marks, hsupport, mark, attachments, List.length_append, ha, hb]
    split_ifs <;> simp <;> omega
  | or q a b ha hb =>
    simp only [erase, marks, hsupport, mark, attachments, List.length_append, ha, hb]
    split_ifs <;> simp <;> omega

 

theorem six_of_marks (W : Finset (Fin 10)) (t : DMFormula 10)
    (h0 : {0} ∈ marks W t) (h2 : {2} ∈ marks W t)
    (h4 : {4} ∈ marks W t) (h7 : {7} ∈ marks W t)
    (h1 : ∃ U ∈ marks W t, 1 ∈ U ∧ 8 ∉ U)
    (h8 : ∃ U ∈ marks W t, 8 ∈ U ∧ 1 ∉ U) :
    6 ≤ (marks W t).length := by
  obtain ⟨A, ha, ha1, ha8⟩ := h1
  obtain ⟨B, hb, hb8, hb1⟩ := h8
  have ha0 : A ≠ {0} := fun h => by simp [h] at ha1
  have ha2 : A ≠ {2} := fun h => by simp [h] at ha1
  have ha4 : A ≠ {4} := fun h => by simp [h] at ha1
  have ha7 : A ≠ {7} := fun h => by simp [h] at ha1
  have hb0 : B ≠ {0} := fun h => by simp [h] at hb8
  have hb2 : B ≠ {2} := fun h => by simp [h] at hb8
  have hb4 : B ≠ {4} := fun h => by simp [h] at hb8
  have hb7 : B ≠ {7} := fun h => by simp [h] at hb8
  have hab : A ≠ B := fun h => hb1 (h ▸ ha1)
  let L : List (Finset (Fin 10)) := [A, B, {0}, {2}, {4}, {7}]
  have hd : L.Nodup := by
    simp [L, ha0, ha2, ha4, ha7, hb0, hb2, hb4, hb7, hab]
  have hsub : L.toFinset ⊆ (marks W t).toFinset := by
    intro X hx
    simp only [L, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [ha, hb, h0, h2, h4, h7]
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hd] at hc
  exact hc.trans (List.toFinset_card_le (marks W t))

end AttachmentMarks

namespace X8Guard

open PEqualNP.Outside.L_meta_3202.TaggedUnroll
open PEqualNP.Outside.L_meta_3202.TaggedPaths

def anyEarly (e : Fin 3 → Bool) : Bool := e 0 || e 1 || e 2
private def zero : Fin 3 → Bool := fun _ => false

private theorem nonempty_true (e : Fin 3 → Bool) (he : e ≠ zero) : anyEarly e = true := by
  by_contra hn
  apply he
  funext i
  have hf : anyEarly e = false := by cases h : anyEarly e <;> simp_all
  have heq : e 0 = false ∧ e 1 = false ∧ e 2 = false := by
    simpa [anyEarly, Bool.or_assoc, Bool.or_eq_false_iff] using hf
  fin_cases i
  · exact heq.1
  · exact heq.2.1
  · exact heq.2.2

private theorem update_early (e : Fin 3 → Bool) (b : Bool) :
    Function.update (TopRows.early e false) 8 b = TopRows.early e b := by
  funext i
  by_cases h : i = 8
  · subst i; simp [TopRows.early]
  · simp [TopRows.early, h]

 

theorem find_sibling (t : Tree 10) (honce : occurs 8 t = 1)
    (computes : ∀ x, TopRows.valid x → (erase t).eval x = TopRows.target x) :
    ∃ s ∈ path 8 t, s.conj = true ∧ ∀ e,
      (erase s.sibling).eval (TopRows.early e false) = anyEarly e := by
  have heval (e : Fin 3 → Bool) (b : Bool) :
      (erase t).eval (Function.update (TopRows.early e false) 8 b) = (b && anyEarly e) := by
    rw [update_early]
    exact (computes _ (TopRows.checked_early e b).1).trans (TopRows.checked_early e b).2
  have hp := phase_of_rise t 8 honce (fun e => TopRows.early e false) (fun _ => true)
    (by simpa using heval (fun _ => true) false)
    (by simpa [anyEarly] using heval (fun _ => true) true)
  have hoff : (erase t).eval (Function.update (TopRows.early zero false) 8 true) = false := by
    simpa [anyEarly, zero] using heval zero true
  have hon (e : Fin 3 → Bool) (he : e ≠ zero) :
      (erase t).eval (Function.update (TopRows.early e false) 8 false) = false ∧
      (erase t).eval (Function.update (TopRows.early e false) 8 true) = true :=
    ⟨by simpa using heval e false, by simpa [nonempty_true e he] using heval e true⟩
  obtain ⟨s, hs, hc, hz, ht⟩ := guarded_path_sibling t 8 honce hp
    (fun e => TopRows.early e false) zero hoff hon
  refine ⟨s, hs, hc, ?_⟩
  intro e
  by_cases he : e = zero
  · subst e; simpa [anyEarly, zero] using hz
  · exact (ht e he).trans (nonempty_true e he).symm

end X8Guard

namespace LcaPairs

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.PetersenScratch
open PEqualNP.Outside.L_meta_3202.AttachmentMarks

private theorem support_bin {n : ℕ} (W : Finset (Fin n)) (op : Bool)
    (p q : DMFormula n) : support W (node op p q) = support W p ∪ support W q := by
  cases op <;>
    ext v <;>
    simp [node, support, occurrences, and_or_left]

private theorem singleton_bin_mark {n : ℕ} (W : Finset (Fin n)) (i : Fin n)
    (op : Bool) (p q : DMFormula n)
    (hs : support W (node op p q) = {i})
    (hc : occurrences i (node op p q) = 1) :
    {i} ∈ marks W (node op p q) := by
  have hS : support W p ∪ support W q = {i} := (support_bin W op p q).symm.trans hs
  have hp : support W p ⊆ ({i} : Finset (Fin n)) := by
    rw [←hS]
    exact Finset.subset_union_left
  have hq : support W q ⊆ ({i} : Finset (Fin n)) := by
    rw [←hS]
    exact Finset.subset_union_right
  have hc' : occurrences i p + occurrences i q = 1 := by
    cases op <;> exact hc
  have one : i ∈ support W p ∨ i ∈ support W q := by
    apply Finset.mem_union.mp
    rw [hS]
    simp
  rcases one with h | h
  · have pe : support W p = {i} := Finset.Subset.antisymm hp (Finset.singleton_subset_iff.mpr h)
    have qe : support W q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hji := Finset.mem_singleton.mp (hq hj)
      subst j
      have il := (Finset.mem_filter.mp h).2
      have ir := (Finset.mem_filter.mp hj).2
      omega
    have hm := mark_left W op p q ⟨i,h⟩ qe
    rw [pe] at hm
    exact hm
  · have qe : support W q = {i} := Finset.Subset.antisymm hq (Finset.singleton_subset_iff.mpr h)
    have pe : support W p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hji := Finset.mem_singleton.mp (hp hj)
      subst j
      have il := (Finset.mem_filter.mp h).2
      have ir := (Finset.mem_filter.mp hj).2
      omega
    have hm := mark_right W op p q pe ⟨i,h⟩
    rw [qe] at hm
    exact hm

theorem singleton_mark_of_nonliteral {n : ℕ} (W : Finset (Fin n)) (i : Fin n)
    (t : DMFormula n) (hs : support W t = {i}) (hc : occurrences i t = 1)
    (hn : ∀ k s, t ≠ .lit k s) : {i} ∈ marks W t := by
  cases t with
  | lit k s => exact False.elim (hn k s rfl)
  | and p q => exact singleton_bin_mark W i true p q hs hc
  | or p q => exact singleton_bin_mark W i false p q hs hc

theorem Context.lift_mark {n : ℕ} (ctx : Context n) (W : Finset (Fin n))
    {U : Finset (Fin n)} {t : DMFormula n} (h : U ∈ marks W t) :
    U ∈ marks W (ctx.fill t) := by
  induction ctx with
  | hole => exact h
  | left op sub other ih => exact mem_marks_left W op (sub.fill t) other ih
  | right op other sub ih => exact mem_marks_right W op other (sub.fill t) ih

theorem and_left_singleton_mark {n : ℕ} (ctx : Context n) (W : Finset (Fin n))
    (p q : DMFormula n) (i j : Fin n) (ne : i ≠ j) (base pivot : Fin n → Bool)
    (hs : support W p = {i})
    (ip : occurrences i p = 1) (jq : occurrences j q = 1)
    (ot : occurrences i (ctx.fill (node true p q)) ≤ 1)
    (oj : occurrences j (ctx.fill (node true p q)) ≤ 1)
    (fit : Fits i j base (ctx.fill (node true p q)) true)
    (test : ∀ b, pairValue i j pivot (ctx.fill (node true p q)) false b = b) :
    {i} ∈ marks W (ctx.fill (node true p q)) := by
  apply ctx.lift_mark
  apply mem_marks_left W true p q
  exact singleton_mark_of_nonliteral W i p hs ip
    (and_left_nonliteral ctx p q i j ne base pivot ip jq ot oj fit test)

theorem and_right_singleton_mark {n : ℕ} (ctx : Context n) (W : Finset (Fin n))
    (p q : DMFormula n) (i j : Fin n) (ne : i ≠ j) (base pivot : Fin n → Bool)
    (hs : support W q = {j})
    (ip : occurrences i p = 1) (jq : occurrences j q = 1)
    (ot : occurrences i (ctx.fill (node true p q)) ≤ 1)
    (oj : occurrences j (ctx.fill (node true p q)) ≤ 1)
    (fit : Fits i j base (ctx.fill (node true p q)) true)
    (test : ∀ a, pairValue i j pivot (ctx.fill (node true p q)) a false = a) :
    {j} ∈ marks W (ctx.fill (node true p q)) := by
  apply ctx.lift_mark
  apply mem_marks_right W true p q
  exact singleton_mark_of_nonliteral W j q hs jq
    (and_right_nonliteral ctx p q i j ne base pivot ip jq ot oj fit test)

theorem split_singleton_supports {n : ℕ} (W : Finset (Fin n)) (op : Bool)
    (p q : DMFormula n) (i j : Fin n)
    (outer : support W (node op p q) = {i, j})
    (ip : 0 < occurrences i p) (jq : 0 < occurrences j q)
    (iN : occurrences i (node op p q) ≤ 1)
    (jN : occurrences j (node op p q) ≤ 1) :
    support W p = {i} ∧ support W q = {j} := by
  have uni : support W p ∪ support W q = {i, j} :=
    (support_bin W op p q).symm.trans outer
  have il : i ∈ W := by
    have h : i ∈ support W (node op p q) := by rw [outer]; simp
    exact (Finset.mem_filter.mp h).1
  have jl : j ∈ W := by
    have h : j ∈ support W (node op p q) := by rw [outer]; simp
    exact (Finset.mem_filter.mp h).1
  have qi : occurrences i q = 0 := by
    cases op <;> change occurrences i p + occurrences i q ≤ 1 at iN <;> omega
  have pj : occurrences j p = 0 := by
    cases op <;> change occurrences j p + occurrences j q ≤ 1 at jN <;> omega
  constructor
  · apply Finset.Subset.antisymm
    · intro v hv
      have hu : v ∈ support W p ∪ support W q := Finset.mem_union_left _ hv
      rw [uni] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with (rfl | rfl)
      · rfl
      · exact False.elim ((Finset.mem_filter.mp hv).2.ne' pj)
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨il, ip⟩)
  · apply Finset.Subset.antisymm
    · intro v hv
      have hu : v ∈ support W p ∪ support W q := Finset.mem_union_right _ hv
      rw [uni] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with (rfl | rfl)
      · exact False.elim ((Finset.mem_filter.mp hv).2.ne' qi)
      · rfl
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨jl, jq⟩)

theorem both_and_cluster_marks {n : ℕ} (ctx : Context n) (W : Finset (Fin n))
    (p q : DMFormula n) (i j : Fin n) (ne : i ≠ j) (base leftPivot rightPivot : Fin n → Bool)
    (hs : support W (node true p q) = {i,j})
    (sp : Split i j p q)
    (ot : occurrences i (ctx.fill (node true p q)) ≤ 1)
    (oj : occurrences j (ctx.fill (node true p q)) ≤ 1)
    (fit : Fits i j base (ctx.fill (node true p q)) true)
    (leftTest : ∀ b, pairValue i j leftPivot (ctx.fill (node true p q)) false b = b)
    (rightTest : ∀ a, pairValue i j rightPivot (ctx.fill (node true p q)) a false = a) :
    {i} ∈ marks W (ctx.fill (node true p q)) ∧
    {j} ∈ marks W (ctx.fill (node true p q)) := by
  have iN := (ctx.occ_le (node true p q) i).trans ot
  have jN := (ctx.occ_le (node true p q) j).trans oj
  rcases sp with (⟨ip,jq⟩ | ⟨jp,iq⟩)
  · obtain ⟨hl,hr⟩ := split_singleton_supports W true p q i j hs ip jq iN jN
    change occurrences i p + occurrences i q ≤ 1 at iN
    change occurrences j p + occurrences j q ≤ 1 at jN
    exact ⟨and_left_singleton_mark ctx W p q i j ne base leftPivot hl
              (by omega) (by omega) ot oj fit leftTest,
           and_right_singleton_mark ctx W p q i j ne base rightPivot hr
              (by omega) (by omega) ot oj fit rightTest⟩
  · have hs' : support W (node true p q) = {j,i} := by
      rw [hs]
      ext v
      simp [or_comm]
    obtain ⟨hl,hr⟩ := split_singleton_supports W true p q j i hs' jp iq jN iN
    change occurrences i p + occurrences i q ≤ 1 at iN
    change occurrences j p + occurrences j q ≤ 1 at jN
    have f' : Fits j i base (ctx.fill (node true p q)) true := by
      intro b a
      rw [pair_value_swap j i ne.symm, fit a b]
      simpa [binOp] using Bool.and_comm a b
    have lp : ∀ a, pairValue j i rightPivot (ctx.fill (node true p q)) false a = a := by
      intro a
      rw [pair_value_swap j i ne.symm, rightTest a]
    have rp : ∀ b, pairValue j i leftPivot (ctx.fill (node true p q)) b false = b := by
      intro b
      rw [pair_value_swap j i ne.symm, leftTest b]
    exact ⟨and_right_singleton_mark ctx W p q j i ne.symm base leftPivot hr
              (by omega) (by omega) oj ot f' rp,
           and_left_singleton_mark ctx W p q j i ne.symm base rightPivot hl
              (by omega) (by omega) oj ot f' lp⟩

end LcaPairs

namespace OrAttachments

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.PetersenScratch
open PEqualNP.Outside.L_meta_3202.TaggedUnroll
open PEqualNP.Outside.L_meta_3202.TaggedPaths
open PEqualNP.Outside.L_meta_3202.AttachmentMarks

private def candidate {n : ℕ} (W : Finset (Fin n)) (i j : Fin n) (s : Place n)
    (t : Tree n) : Prop :=
  (0 < occurs j t ∧ s ∈ path j t) ∨
    ∃ U ∈ marks W (erase t), i ∈ U ∧ j ∉ U

private theorem occurs_free {n : ℕ} {W : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ W) {t : Tree n} (h : footprint W t = ∅) : occurs i t = 0 := by
  by_contra hn
  have hm : i ∈ footprint W t := Finset.mem_filter.mpr ⟨hi, Nat.pos_of_ne_zero hn⟩
  simp [h] at hm

private def taggedNode {n : ℕ} (op : Bool) (q : ℕ) (a b : Tree n) : Tree n :=
  if op then .and q a b else .or q a b

private theorem path_node {n : ℕ} (op : Bool) (q : ℕ) (a b : Tree n) (i : Fin n) :
    path i (taggedNode op q a b) =
      (if leftHas i a then ⟨q, op, b⟩ :: path i a else ⟨q, op, a⟩ :: path i b) := by
  cases op <;> rfl

private theorem erase_node {n : ℕ} (op : Bool) (q : ℕ) (a b : Tree n) :
    erase (taggedNode op q a b) = node op (erase a) (erase b) := by
  cases op <;> rfl

private theorem occurs_node {n : ℕ} (op : Bool) (q : ℕ) (a b : Tree n) (i : Fin n) :
    occurs i (taggedNode op q a b) = occurs i a + occurs i b := by
  cases op <;> rfl

private theorem path_step {n : ℕ} (W : Finset (Fin n)) (i j : Fin n) (s : Place n)
    (hi : i ∈ W) (hj : j ∈ W) (hfree : footprint W s.sibling = ∅)
    (op : Bool) (q : ℕ) (a b : Tree n)
    (ha : occurs i a = 1 → occurs j a ≤ 1 → s ∈ path i a → candidate W i j s a)
    (hb : occurs i b = 1 → occurs j b ≤ 1 → s ∈ path i b → candidate W i j s b)
    (hi₁ : occurs i (taggedNode op q a b) = 1)
    (hj₁ : occurs j (taggedNode op q a b) ≤ 1)
    (hs : s ∈ path i (taggedNode op q a b)) :
    candidate W i j s (taggedNode op q a b) := by
  rw [occurs_node] at hi₁ hj₁
  rw [path_node] at hs
  unfold candidate
  rw [occurs_node, path_node, erase_node]
  by_cases hiA : 0 < occurs i a
  · have haI : occurs i a = 1 := by omega
    rw [ite_eq_left (by simp [leftHas, hiA])] at hs
    rcases List.mem_cons.mp hs with hroot | htail
    · subst s
      have hjB : occurs j b = 0 := occurs_free hj hfree
      by_cases hjA : 0 < occurs j a
      · left
        constructor
        · omega
        · simp [leftHas, hjA]
      · right
        have hm : i ∈ support W (erase a) := Finset.mem_filter.mpr ⟨hi, hiA⟩
        refine ⟨support W (erase a), mark_left W op (erase a) (erase b) ⟨i, hm⟩ hfree, hm, ?_⟩
        exact fun h => hjA (Finset.mem_filter.mp h).2
    · rcases ha haI (by omega) htail with ⟨hjA, hp⟩ | ⟨U, hU, hUi, hUj⟩
      · left
        exact ⟨by omega, by simp [leftHas, hjA, hp]⟩
      · exact Or.inr ⟨U, mem_marks_left W op _ _ hU, hUi, hUj⟩
  · have hbI : occurs i b = 1 := by omega
    rw [ite_eq_right (by simp [leftHas, hiA])] at hs
    rcases List.mem_cons.mp hs with hroot | htail
    · subst s
      have hjA : occurs j a = 0 := occurs_free hj hfree
      by_cases hjB : 0 < occurs j b
      · left
        exact ⟨by omega, by simp [leftHas, hjA]⟩
      · right
        have hm : i ∈ support W (erase b) := Finset.mem_filter.mpr ⟨hi, Nat.lt_of_succ_le (Nat.le_of_eq hbI.symm)⟩
        refine ⟨support W (erase b), mark_right W op (erase a) (erase b) hfree ⟨i, hm⟩, hm, ?_⟩
        exact fun h => hjB (Finset.mem_filter.mp h).2
    · rcases hb hbI (by omega) htail with ⟨hjB, hp⟩ | ⟨U, hU, hUi, hUj⟩
      · left
        have hjA : occurs j a = 0 := by omega
        exact ⟨by omega, by simp [leftHas, hjA, hp]⟩
      · exact Or.inr ⟨U, mem_marks_right W op _ _ hU, hUi, hUj⟩

private theorem mark_or_same_path {n : ℕ} (W : Finset (Fin n)) (i j : Fin n) (s : Place n)
    (hi : i ∈ W) (hj : j ∈ W) (hfree : footprint W s.sibling = ∅)
    (t : Tree n) (hi₁ : occurs i t = 1) (hj₁ : occurs j t ≤ 1)
    (hs : s ∈ path i t) : candidate W i j s t := by
  induction t with
  | lit => simp [path] at hs
  | and q a b ha hb => exact path_step W i j s hi hj hfree true q a b ha hb hi₁ hj₁ hs
  | or q a b ha hb => exact path_step W i j s hi hj hfree false q a b ha hb hi₁ hj₁ hs

 

theorem mark_of_other_pivotal {n : ℕ} (W : Finset (Fin n)) (i j : Fin n)
    (hi : i ∈ W) (hj : j ∈ W) (t : Tree n)
    (hi₁ : occurs i t = 1) (hj₁ : occurs j t = 1) (hiPhase : phase i t = true)
    (hfree : ∀ s ∈ path i t, s.conj = true → footprint W s.sibling = ∅)
    (x : Fin n → Bool) (hxi : x i = true) (hxj : x j = false)
    (hlo : (erase t).eval x = false)
    (hhi : (erase t).eval (Function.update x j true) = true) :
    ∃ U ∈ marks W (erase t), i ∈ U ∧ j ∉ U := by
  let X : Unit → Fin n → Bool := fun _ => x
  let e : Unit := ()
  have eqI : Function.update x i true = x := hxi ▸ Function.update_eq_self i x
  have eqJ : Function.update x j false = x := hxj ▸ Function.update_eq_self j x
  let p := (path i t).map (interpret X)
  let q := (path j t).map (interpret X)
  have hiOff : LastAbsorber.run p e true = false := by
    have le := eval_update_path t i hi₁ X e true
    simpa [p, e, X, eqI, hiPhase, hlo] using le.symm
  have hJPhase := phase_of_rise t j hj₁ X e (by simpa [X, eqJ] using hlo) hhi
  have hjPiv : LastAbsorber.run q e false = false ∧ LastAbsorber.run q e true = true := by
    have lo := eval_update_path t j hj₁ X e false
    have hh := eval_update_path t j hj₁ X e true
    exact ⟨by simpa [q, X, e, eqJ, hlo, hJPhase] using lo.symm,
      by simpa [q, X, e, hhi, hJPhase] using hh.symm⟩
  obtain ⟨s', hmem, hc, hsFalse⟩ := LastAbsorber.has_false_and p e hiOff
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
  rcases mark_or_same_path W i j s hi hj (hfree s hs hc) t hi₁ hj₁.le hs with hboth | hw
  · have he := LastAbsorber.neutral_of_pivotal q e hjPiv (interpret X s)
      (List.mem_map.mpr ⟨s, hboth.2, rfl⟩)
    exact (Bool.false_ne_true (hsFalse.symm.trans (he.trans hc))).elim
  · exact hw

end OrAttachments

namespace LcaFreePaths

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.PetersenScratch
open PEqualNP.Outside.L_meta_3202.TaggedUnroll
open PEqualNP.Outside.L_meta_3202.TaggedPaths
open PEqualNP.Outside.L_meta_3202.LcaPairs

private theorem and_sibling_lca {n : ℕ} (i j : Fin n) (t : Tree n)
    (hi : 0 < occurs i t) (s : Place n) (hs : s ∈ path i t) (hAND : s.conj = true)
    (hj : 0 < occurs j s.sibling) :
    LCA i j (erase t) true := by
  induction t with
  | lit => simp [path] at hs
  | and tag a b ha hb =>
    change 0 < occurs i a + occurs i b at hi
    by_cases hl : 0 < occurs i a
    · simp [path, leftHas, hl] at hs
      rcases hs with hr | ht
      · subst s
        exact .here true _ _ (Or.inl ⟨hl, hj⟩)
      · exact .left true true _ _ (ha hl ht)
    · have hr : 0 < occurs i b := by omega
      simp [path, leftHas, hl] at hs
      rcases hs with hr' | ht
      · subst s
        exact .here true _ _ (Or.inr ⟨hj, hr⟩)
      · exact .right true true _ _ (hb hr ht)
  | or tag a b ha hb =>
    change 0 < occurs i a + occurs i b at hi
    by_cases hl : 0 < occurs i a
    · simp [path, leftHas, hl] at hs
      rcases hs with hr | ht
      · subst s; contradiction
      · exact .left true false _ _ (ha hl ht)
    · have hr : 0 < occurs i b := by omega
      simp [path, leftHas, hl] at hs
      rcases hs with hr' | ht
      · subst s; contradiction
      · exact .right true false _ _ (hb hr ht)

private theorem twice_of_self_lca {n : ℕ} {i : Fin n} {t : DMFormula n} {b : Bool}
    (h : LCA i i t b) : 2 ≤ occurrences i t := by
  induction h with
  | here op a b hs =>
    unfold Split at hs
    cases op <;> change 2 ≤ occurrences i a + occurrences i b <;> omega
  | left kind op a b _ ih =>
    cases op <;> change 2 ≤ occurrences i a + occurrences i b <;> omega
  | right kind op a b _ ih =>
    cases op <;> change 2 ≤ occurrences i a + occurrences i b <;> omega

 

theorem and_steps_wfree {n : ℕ} (W : Finset (Fin n)) (t : Tree n) (i : Fin n)
    (hi : occurs i t = 1) (honce : ∀ j ∈ W, occurs j t ≤ 1)
    (hkind : ∀ j ∈ W, j ≠ i → kindAt i j (erase t) = some false) :
    ∀ s ∈ path i t, s.conj = true → footprint W s.sibling = ∅ := by
  intro s hs hAND
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hjW, hj⟩ := Finset.mem_filter.mp hj
  have hpath := and_sibling_lca i j t (by omega) s hs hAND hj
  by_cases he : j = i
  · subst j
    have ht := twice_of_self_lca hpath
    change 2 ≤ occurs i t at ht
    rw [hi] at ht
    omega
  · have ha := hpath.kind hi.le (honce j hjW)
    rw [hkind j hjW he] at ha
    contradiction

 
theorem table_lca (t : Tree 10)
    (honce : ∀ i, i ∈ ({0,1,2,4,7,8} : Finset (Fin 10)) → occurs i t = 1)
    (computes : ∀ x, TopRows.valid x → (erase t).eval x = TopRows.target x) :
    ∀ e ∈ TopRows.lcaRows, kindAt e.1 e.2.1 (erase t) = some e.2.2.1 := by
  intro e he
  have aux : ∀ e ∈ TopRows.lcaRows, e.1 ≠ e.2.1 ∧
      e.1 ∈ ({0,1,2,4,7,8} : Finset (Fin 10)) ∧
      e.2.1 ∈ ({0,1,2,4,7,8} : Finset (Fin 10)) := by decide +kernel
  obtain ⟨hne, hiW, hjW⟩ := aux e he
  let base := TopRows.row e.2.2.2
  have hfit : Fits e.1 e.2.1 base (erase t) e.2.2.1 := by
    intro a b
    have h := TopRows.checked_lca_rows e he a b
    exact (computes _ h.1).trans h.2
  exact (forced_lca _ _ hne base _ _ (honce _ hiW) (honce _ hjW) hfit).kind
    (honce _ hiW).le (honce _ hjW).le

 
theorem two_paths_wfree (t : Tree 10)
    (honce : ∀ i ∈ ({0,1,2,4,7,8} : Finset (Fin 10)), occurs i t = 1)
    (computes : ∀ x, TopRows.valid x → (erase t).eval x = TopRows.target x) :
    ∀ i ∈ ({1,8} : Finset (Fin 10)), ∀ s ∈ path i t, s.conj = true →
      footprint ({0,1,2,4,7,8} : Finset (Fin 10)) s.sibling = ∅ := by
  let W : Finset (Fin 10) := {0,1,2,4,7,8}
  intro i hi
  have hiW : i ∈ W := by
    have hh : ({1,8} : Finset (Fin 10)) ⊆ W := by decide +kernel
    exact hh hi
  apply and_steps_wfree W t i (honce i hiW) (fun j hj => (honce j hj).le)
  intro j hj hne
  have htable := table_lca t honce computes
  let test (i j : Fin 10) : Bool := TopRows.lcaRows.any fun e =>
    decide (e.2.2.1 = false ∧ ((e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i)))
  have data : ∀ i ∈ ({1,8} : Finset (Fin 10)), ∀ j ∈ W, j ≠ i → test i j = true := by
    decide +kernel
  obtain ⟨e, he, hh⟩ := List.any_eq_true.mp (data i hi j hj hne)
  have hm : e.2.2.1 = false ∧ ((e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i)) :=
    of_decide_eq_true hh
  have hv := htable e he
  rw [hm.1] at hv
  rcases hm.2 with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simpa [hl, hr] using hv
  · rw [kindAt_swap]
    simpa [hl, hr] using hv

end LcaFreePaths

namespace OrMarks3202

open PEqualNP.Outside.L_meta_3202.TaggedUnroll
open PEqualNP.Outside.L_meta_3202.TaggedPaths
open PEqualNP.Outside.L_meta_3202.AttachmentMarks
open PEqualNP.Outside.L_meta_3202.OrAttachments
open PEqualNP.Outside.L_meta_3202.LcaFreePaths

private def W : Finset (Fin 10) := {0,1,2,4,7,8}

private def phaseRows : List (Fin 10 × ℕ) := [(1,513),(8,8)]

private theorem phase_data : ∀ e ∈ phaseRows, ∀ b : Bool,
    let x := Function.update (TopRows.row e.2) e.1 b
    TopRows.valid x ∧ TopRows.target x = b := by
  unfold TopRows.valid
  decide +kernel

private def markRows : List (Fin 10 × Fin 10 × ℕ) := [(1,8,10),(8,1,769)]

private theorem mark_data : ∀ e ∈ markRows,
    let x := TopRows.row e.2.2
    let y := Function.update x e.2.1 true
    x e.1 = true ∧ x e.2.1 = false ∧
      TopRows.valid x ∧ TopRows.target x = false ∧
      TopRows.valid y ∧ TopRows.target y = true := by
  unfold TopRows.valid
  decide +kernel

theorem exact_or_marks (t : Tree 10)
    (honce : ∀ i ∈ ({0,1,2,4,7,8} : Finset (Fin 10)), occurs i t = 1)
    (computes : ∀ x, TopRows.valid x → (erase t).eval x = TopRows.target x) :
    (∃ U ∈ marks ({0,1,2,4,7,8} : Finset (Fin 10)) (erase t), 1 ∈ U ∧ 8 ∉ U) ∧
      (∃ U ∈ marks ({0,1,2,4,7,8} : Finset (Fin 10)) (erase t), 8 ∈ U ∧ 1 ∉ U) := by
  have phaseAt (i : Fin 10) (hi : i ∈ W) (m : ℕ) (hm : (i,m) ∈ phaseRows) :
      phase i t = true := by
    have lo := phase_data (i,m) hm false
    have hi' := phase_data (i,m) hm true
    exact phase_of_rise t i (honce i hi) (fun _ : Unit => TopRows.row m) ()
      ((computes _ lo.1).trans lo.2) ((computes _ hi'.1).trans hi'.2)
  have markAt (i j : Fin 10) (hi : i ∈ ({1,8} : Finset (Fin 10))) (hiW : i ∈ W)
      (hjW : j ∈ W) (hphase : phase i t = true) (m : ℕ) (hm : (i,j,m) ∈ markRows) :
      ∃ U ∈ marks W (erase t), i ∈ U ∧ j ∉ U := by
    obtain ⟨hxi, hxj, hv, ht, hv', ht'⟩ := mark_data (i,j,m) hm
    exact mark_of_other_pivotal W i j hiW hjW t (honce i hiW) (honce j hjW) hphase
      (two_paths_wfree t honce computes i hi) (TopRows.row m) hxi hxj
      ((computes _ hv).trans ht) ((computes _ hv').trans ht')
  exact ⟨markAt 1 8 (by decide) (by decide) (by decide)
      (phaseAt 1 (by decide) 513 (by decide)) 10 (by decide),
    markAt 8 1 (by decide) (by decide) (by decide)
      (phaseAt 8 (by decide) 8 (by decide)) 769 (by decide)⟩

end OrMarks3202

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous
open CircuitProof CircuitProof.Readers PetersenCutTrace
open PetersenScratch PetersenCutFormula
open TaggedUnroll TaggedPaths

abbrev rankedTree (B : RankedSuffix) : Tree 10 := unroll 0 B.gates B.output.val

theorem rankedTree_computes (B : RankedSuffix) :
    ∀ x, TopRows.valid x → (erase (rankedTree B)).eval x = TopRows.target x := by
  intro x valid
  rw [unroll_eval 0 B.clean x _ B.output.isLt]
  exact B.computes x valid

theorem rankedTree_atMostOnce (B : RankedSuffix) :
    ∀ i ∈ topLabels, occurrences i (erase (rankedTree B)) ≤ 1 := by
  intro i hi
  rw [erase_unroll 0 B.clean _ B.output.isLt]
  exact B.top_once i hi

private def pivotalMask (i : Fin 10) : ℕ :=
  if i = 0 then 532 else if i = 1 then 64 else if i = 2 then 521 else
  if i = 4 then 8 else if i = 7 then 32 else 8

private theorem pivotalRows : ∀ i : Fin 10, i ∈ topLabels →
    let x := TopRows.row (pivotalMask i)
    let y := Function.update x i true
    Slice x ∧ Slice y ∧ target10 x = false ∧ target10 y = true := by
  intro i hi
  simp only [topLabels, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Slice] <;> decide +kernel

theorem rankedTree_footprint (B : RankedSuffix) :
    footprint topLabels (rankedTree B) = topLabels := by
  ext i
  constructor
  · exact fun h => (Finset.mem_filter.mp h).1
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    rw [erase_unroll 0 B.clean _ B.output.isLt]
    apply (occurrence_iff_path B.clean 0 i B.output).mpr
    obtain ⟨hx, hy, xf, yt⟩ := pivotalRows i hi
    apply ancestor_of_pivot B.clean B.output i
      (x := TopRows.row (pivotalMask i))
      (y := Function.update (TopRows.row (pivotalMask i)) i true)
    · exact fun j hj => (Function.update_of_ne hj _ _).symm
    · rw [B.computes _ hx, B.computes _ hy, xf, yt]
      decide

theorem rankedTree_once (B : RankedSuffix) :
    ∀ i ∈ topLabels, occurs i (rankedTree B) = 1 := by
  intro i hi
  have member : i ∈ footprint topLabels (rankedTree B) := by rwa [rankedTree_footprint]
  have pos : 0 < occurrences i (erase (rankedTree B)) := (Finset.mem_filter.mp member).2
  exact Nat.le_antisymm (rankedTree_atMostOnce B i hi) pos

theorem rankedTree_forks (B : RankedSuffix) : forks topLabels (rankedTree B) = 5 := by
  have h := fork_ledger topLabels (rankedTree B) (rankedTree_atMostOnce B)
  rw [rankedTree_footprint] at h
  have hn : topLabels.Nonempty := by decide
  have hs : topLabels.card = 6 := by decide
  rw [ite_eq_left hn, hs] at h
  omega

private theorem binary_val_mem_ledger {n : ℕ} {gs : List Gate}
    (L : List ℕ) (nodup : L.Nodup)
    (valid : ∀ v ∈ L, ∃ a : Fin (n + gs.length), a.val = v ∧ BinaryWire a) :
    L.length ≤ nonNotCount gs := by
  classical
  let V : Finset ℕ := L.toFinset
  let wire : {v // v ∈ V} ↪ Fin (n + gs.length) :=
    ⟨fun v => ⟨v.val, by
       obtain ⟨a, eq, _⟩ := valid v.val (List.mem_toFinset.mp v.property)
       rw [← eq]; exact a.isLt⟩, fun a b eq => Subtype.ext (congrArg Fin.val eq)⟩
  let tally := V.attach.map wire
  have eligible : ∀ v ∈ tally, BinaryWire v := by
    intro v h
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp h
    obtain ⟨b, eq, hb⟩ := valid a.val (List.mem_toFinset.mp a.property)
    have same : b = wire a := Fin.ext eq
    exact same ▸ hb
  have h := binary_wires_card_le tally eligible
  simpa [tally, V, List.toFinset_card_of_nodup nodup] using h

private theorem two_wfree (B : RankedSuffix)
    (h8 : ∀ s ∈ path 8 (rankedTree B), s.conj = true →
      footprint topLabels s.sibling = ∅) :
    ∃ a b : Fin (10 + B.gates.length),
      a ≠ b ∧ BinaryWire a ∧ BinaryWire b ∧
      (∀ i ∈ topLabels, occurrences i (wireFormula 0 B.gates a.val) = 0) ∧
      (∀ i ∈ topLabels, occurrences i (wireFormula 0 B.gates b.val) = 0) := by
  obtain ⟨s, hs, conj, coeff⟩ := X8Guard.find_sibling (rankedTree B)
    (rankedTree_once B 8 (by decide)) (rankedTree_computes B)
  have free := h8 s hs conj
  obtain ⟨k, hk, phase, he⟩ := sibling_wire 0 8 B.clean B.output.val B.output.isLt hs
  have hkAll : k < 10 + B.gates.length := hk.trans B.output.isLt
  let w : Fin (10 + B.gates.length) := ⟨k, hkAll⟩
  apply early_two_binary_wfree B w phase false
  · intro e
    have h := coeff e
    rw [he] at h
    cases phase <;>
      simpa [w, erase_negate, negFormula_eval, unroll_eval 0 B.clean _ k hkAll,
        X8Guard.anyEarly] using h
  · intro i hi
    have f : footprint topLabels (unroll 0 B.gates k) = ∅ := by
      rw [he] at free
      cases phase <;> simpa using free
    by_contra hn
    have hm : i ∈ footprint topLabels (unroll 0 B.gates k) := by
      apply Finset.mem_filter.mpr
      refine ⟨hi, ?_⟩
      rw [erase_unroll 0 B.clean _ hkAll]
      exact Nat.pos_of_ne_zero hn
    rw [f] at hm
    exact Finset.notMem_empty i hm

 
theorem attachment_contradiction (B : RankedSuffix)
    (six : 6 ≤ attachments topLabels (rankedTree B))
    (h8 : ∀ s ∈ path 8 (rankedTree B), s.conj = true →
      footprint topLabels s.sibling = ∅) : False := by
  classical
  let tags := bearingTags topLabels (rankedTree B)
  have tagNodup : tags.Nodup := bearingTags_nodup 0 B.clean topLabels B.output.val
    B.output.isLt (rankedTree_atMostOnce B)
  have tagCount : 11 ≤ tags.length := by
    dsimp [tags]
    rw [bearing_length, rankedTree_forks]
    omega
  have tagData {q : ℕ} (h : q ∈ tags) :
      ∃ v : Fin (10 + B.gates.length), v.val = q ∧ BinaryWire v ∧
        ∃ i ∈ topLabels, 0 < occurrences i (wireFormula 0 B.gates v.val) := by
    obtain ⟨⟨k, U⟩, hprof, rfl⟩ := List.mem_map.mp h
    obtain ⟨hk, ⟨p, eq, kind⟩, hU⟩ :=
      profile_sound 0 B.clean topLabels B.output.val B.output.isLt k U hprof
    obtain ⟨i, hi⟩ := (profile_scope topLabels _ hprof).1
    rw [hU, footprint, Finset.mem_filter, erase_unroll 0 B.clean _ (hk.trans_lt B.output.isLt)] at hi
    refine ⟨⟨k, hk.trans_lt B.output.isLt⟩, rfl, ?_, i, hi⟩
    exact ⟨p.val, B.gates.get p, List.getElem?_eq_getElem p.isLt, eq, kind⟩
  obtain ⟨a,b,ne,ab,bb,freeA,freeB⟩ := two_wfree B h8
  have absent {v : Fin (10 + B.gates.length)}
      (free : ∀ i ∈ topLabels, occurrences i (wireFormula 0 B.gates v.val) = 0) :
      v.val ∉ tags := by
    intro h
    obtain ⟨w, eq, _, i, hi, pos⟩ := tagData h
    rw [eq, free i hi] at pos
    exact (Nat.lt_irrefl _) pos
  have distinct : a.val ≠ b.val := fun e => ne (Fin.ext e)
  have nodup : (a.val :: b.val :: tags).Nodup := by
    simp [List.nodup_cons, distinct, absent freeA, absent freeB, tagNodup]
  have hbound := binary_val_mem_ledger (n := 10) (gs := B.gates)
    (a.val :: b.val :: tags) nodup (fun v hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨a, rfl, ab⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨b, rfl, bb⟩
      · obtain ⟨w, eq, bin, _⟩ := tagData hv
        exact ⟨w, eq, bin⟩)
  have cap := B.binary_bound
  simp only [List.length_cons] at hbound
  omega

end Bridge

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.Suffix2770 (F)
open TaggedUnroll TaggedPaths

theorem proof_of_topology
    (six : ∀ B : RankedSuffix, 6 ≤ attachments topLabels (rankedTree B))
    (free : ∀ (B : RankedSuffix) (s : Place 10), s ∈ path 8 (rankedTree B) →
      s.conj = true → footprint topLabels s.sibling = ∅)
    (C : Circuit) (fan : FanInTwo C) (nots : NotSlots C)
    (first : FirstWire C) (computes : circuitFun 9 C = F) : 16 ≤ C.size := by
  by_contra! small
  obtain ⟨B⟩ := ranked_of_small C fan small nots first computes
  exact attachment_contradiction B (six B) (free B)

end Bridge

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.Suffix2770 (F)
open TaggedUnroll TaggedPaths AttachmentMarks

theorem no_and_skeleton_on_x8 (B : RankedSuffix) :
    ∀ s ∈ path 8 (rankedTree B), s.conj = true → footprint topLabels s.sibling = ∅ :=
  LcaFreePaths.two_paths_wfree (rankedTree B) (rankedTree_once B) (rankedTree_computes B)
    8 (by decide)

theorem rankedTree_six_of_marks (B : RankedSuffix)
    (h0 : {0} ∈ marks topLabels (erase (rankedTree B)))
    (h2 : {2} ∈ marks topLabels (erase (rankedTree B)))
    (h4 : {4} ∈ marks topLabels (erase (rankedTree B)))
    (h7 : {7} ∈ marks topLabels (erase (rankedTree B)))
    (h1 : ∃ U ∈ marks topLabels (erase (rankedTree B)), 1 ∈ U ∧ 8 ∉ U)
    (h8 : ∃ U ∈ marks topLabels (erase (rankedTree B)), 8 ∈ U ∧ 1 ∉ U) :
    6 ≤ attachments topLabels (rankedTree B) :=
  (count_marks topLabels (rankedTree B)) ▸
    (six_of_marks topLabels (erase (rankedTree B)) h0 h2 h4 h7 h1 h8)

theorem proof_of_marks
    (andMarks : ∀ B : RankedSuffix,
      ({0} : Finset (Fin 10)) ∈ marks topLabels (erase (rankedTree B)) ∧
      ({2} : Finset (Fin 10)) ∈ marks topLabels (erase (rankedTree B)) ∧
      ({4} : Finset (Fin 10)) ∈ marks topLabels (erase (rankedTree B)) ∧
      ({7} : Finset (Fin 10)) ∈ marks topLabels (erase (rankedTree B)))
    (orMarks : ∀ B : RankedSuffix,
      (∃ U ∈ marks topLabels (erase (rankedTree B)), 1 ∈ U ∧ 8 ∉ U) ∧
      (∃ U ∈ marks topLabels (erase (rankedTree B)), 8 ∈ U ∧ 1 ∉ U))
    (C : Circuit) (fan : FanInTwo C) (nots : NotSlots C)
    (first : FirstWire C) (computes : circuitFun 9 C = F) : 16 ≤ C.size := by
  apply proof_of_topology _ no_and_skeleton_on_x8 C fan nots first computes
  intro B
  obtain ⟨h0, h2, h4, h7⟩ := andMarks B
  obtain ⟨h1, h8⟩ := orMarks B
  exact rankedTree_six_of_marks B h0 h2 h4 h7 h1 h8

end Bridge

namespace Bridge

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3202.Previous.PetersenScratch
open TaggedUnroll AttachmentMarks LcaPairs

abbrev rankedFormula (B : RankedSuffix) : DMFormula 10 := erase (rankedTree B)

private theorem rankedTable (B : RankedSuffix) (i j : Fin 10) (op : Bool) (m : ℕ)
    (hm : (i,j,op,m) ∈ TopRows.lcaRows) :
    kindAt i j (rankedFormula B) = some op :=
  LcaFreePaths.table_lca (rankedTree B) (rankedTree_once B) (rankedTree_computes B)
    (i,j,op,m) hm

private theorem rankedTableSwap (B : RankedSuffix) (i j : Fin 10) (op : Bool) (m : ℕ)
    (hm : (j,i,op,m) ∈ TopRows.lcaRows) :
    kindAt i j (rankedFormula B) = some op := by
  rw [kindAt_swap i j]
  exact rankedTable B j i op m hm

private theorem fittedAnd (B : RankedSuffix) (i j : Fin 10) (m : ℕ)
    (hm : (i,j,true,m) ∈ TopRows.lcaRows) :
    Fits i j (TopRows.row m) (rankedFormula B) true := by
  intro a b
  have h := TopRows.checked_lca_rows (i,j,true,m) hm a b
  exact (rankedTree_computes B _ h.1).trans h.2

private theorem find_pair_cluster (B : RankedSuffix) (i j u d : Fin 10)
    (ne : i ≠ j) (hi : i ∈ topLabels) (hj : j ∈ topLabels)
    (hu : u ∈ topLabels) (hd : d ∈ topLabels) (seed : Fin 10 → Bool)
    (fit : Fits i j seed (rankedFormula B) true)
    (id : kindAt i d (rankedFormula B) = some false)
    (jd : kindAt j d (rankedFormula B) = some false)
    (ud : kindAt u d (rankedFormula B) = some true)
    (rest : ∀ k ∈ topLabels, k ≠ i → k ≠ j → k ≠ u →
      kindAt i k (rankedFormula B) = some false ∧
      kindAt j k (rankedFormula B) = some false) :
    ∃ (ctx : Context 10) (p q : DMFormula 10),
      rankedFormula B = ctx.fill (LcaPairs.node true p q) ∧
      Split i j p q ∧ support topLabels (LcaPairs.node true p q) = {i,j} := by
  have cnt : ∀ k ∈ topLabels, occurrences k (rankedFormula B) = 1 := rankedTree_once B
  have lca := forced_lca i j ne seed true (rankedFormula B) (cnt i hi) (cnt j hj) fit
  obtain ⟨ctx,p,q,eq,split⟩ := lca.locate
  refine ⟨ctx,p,q,eq,split,?_⟩
  have cntAt : ∀ k ∈ topLabels, occurrences k (ctx.fill (LcaPairs.node true p q)) = 1 := by
    rw [← eq]
    exact cnt
  have xhi := (cntAt i hi).le
  have xhj := (cntAt j hj).le
  have except : occurrences u (LcaPairs.node true p q) = 0 := by
    rw [eq] at id jd ud
    exact and_excludes_via_partner ctx p q i j u d xhi xhj (cntAt u hu).le
      (cntAt d hd) split id jd ud
  apply Finset.Subset.antisymm
  · intro k hk
    obtain ⟨hw, pos⟩ := Finset.mem_filter.mp hk
    by_cases ei : k = i
    · simp [ei]
    by_cases ej : k = j
    · simp [ej]
    by_cases eu : k = u
    · subst k
      exact False.elim (pos.ne' except)
    have ⟨ki,kj⟩ := rest k hw ei ej eu
    rw [eq] at ki kj
    have ex := and_excludes_third ctx p q i j k xhi xhj (cntAt k hw).le split ki kj
    exact False.elim (pos.ne' ex)
  · intro k hk
    have ks := (LCA.here true p q split).occurs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hi, ks.1⟩
    · exact Finset.mem_filter.mpr ⟨hj, ks.2⟩

private theorem found04 (B : RankedSuffix) :
    ∃ (ctx : Context 10) (p q : DMFormula 10),
      rankedFormula B = ctx.fill (LcaPairs.node true p q) ∧
      Split 0 4 p q ∧ support topLabels (LcaPairs.node true p q) = {0,4} := by
  apply find_pair_cluster B 0 4 2 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    (TopRows.row 772) (fittedAnd B 0 4 772 (by decide))
    (rankedTable B 0 7 false 788 (by decide)) (rankedTable B 4 7 false 773 (by decide))
    (rankedTable B 2 7 true 769 (by decide))
  intro k hk ne0 ne4 ne2
  simp only [topLabels, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (ne0 rfl)
  · exact ⟨rankedTable B 0 1 false 788 (by decide),
      rankedTableSwap B 4 1 false 897 (by decide)⟩
  · exact False.elim (ne2 rfl)
  · exact False.elim (ne4 rfl)
  · exact ⟨rankedTable B 0 7 false 788 (by decide), rankedTable B 4 7 false 773 (by decide)⟩
  · exact ⟨rankedTable B 0 8 false 628 (by decide), rankedTable B 4 8 false 713 (by decide)⟩

private theorem found27 (B : RankedSuffix) :
    ∃ (ctx : Context 10) (p q : DMFormula 10),
      rankedFormula B = ctx.fill (LcaPairs.node true p q) ∧
      Split 2 7 p q ∧ support topLabels (LcaPairs.node true p q) = {2,7} := by
  apply find_pair_cluster B 2 7 0 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (TopRows.row 769) (fittedAnd B 2 7 769 (by decide))
    (rankedTable B 2 4 false 897 (by decide)) (rankedTableSwap B 7 4 false 773 (by decide))
    (rankedTable B 0 4 true 772 (by decide))
  intro k hk ne2 ne7 ne0
  simp only [topLabels, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (ne0 rfl)
  · exact ⟨rankedTableSwap B 2 1 false 897 (by decide),
      rankedTableSwap B 7 1 false 788 (by decide)⟩
  · exact False.elim (ne2 rfl)
  · exact ⟨rankedTable B 2 4 false 897 (by decide), rankedTableSwap B 7 4 false 773 (by decide)⟩
  · exact False.elim (ne7 rfl)
  · exact ⟨rankedTable B 2 8 false 713 (by decide), rankedTable B 7 8 false 628 (by decide)⟩

private theorem concrete_left_pivot (B : RankedSuffix) (i j : Fin 10) (m : ℕ)
    (rows : ∀ b, TopRows.valid (TopRows.two i j m false b) ∧
      TopRows.target (TopRows.two i j m false b) = b) :
    ∀ b, pairValue i j (TopRows.row m) (rankedFormula B) false b = b := by
  intro b
  exact (rankedTree_computes B _ (rows b).1).trans (rows b).2

private theorem concrete_right_pivot (B : RankedSuffix) (i j : Fin 10) (m : ℕ)
    (rows : ∀ a, TopRows.valid (TopRows.two i j m a false) ∧
      TopRows.target (TopRows.two i j m a false) = a) :
    ∀ a, pairValue i j (TopRows.row m) (rankedFormula B) a false = a := by
  intro a
  exact (rankedTree_computes B _ (rows a).1).trans (rows a).2

private theorem pair_marks (B : RankedSuffix) (i j : Fin 10) (ne : i ≠ j)
    (hi : i ∈ topLabels) (hj : j ∈ topLabels) (base l r : ℕ)
    (hbase : (i,j,true,base) ∈ TopRows.lcaRows)
    (hleft : ∀ b, TopRows.valid (TopRows.two i j l false b) ∧
      TopRows.target (TopRows.two i j l false b) = b)
    (hright : ∀ a, TopRows.valid (TopRows.two i j r a false) ∧
      TopRows.target (TopRows.two i j r a false) = a)
    (found : ∃ (ctx : Context 10) (p q : DMFormula 10),
      rankedFormula B = ctx.fill (LcaPairs.node true p q) ∧
      Split i j p q ∧ support topLabels (LcaPairs.node true p q) = {i,j}) :
    {i} ∈ marks topLabels (rankedFormula B) ∧ {j} ∈ marks topLabels (rankedFormula B) := by
  obtain ⟨ctx,p,q,eq,hs,hW⟩ := found
  have onceI := rankedTree_atMostOnce B i hi
  have onceJ := rankedTree_atMostOnce B j hj
  change occurrences i (rankedFormula B) ≤ 1 at onceI
  change occurrences j (rankedFormula B) ≤ 1 at onceJ
  have ff := fittedAnd B i j base hbase
  have ll := concrete_left_pivot B i j l hleft
  have rr := concrete_right_pivot B i j r hright
  rw [eq] at onceI onceJ ff ll rr ⊢
  exact both_and_cluster_marks ctx topLabels p q i j ne (TopRows.row base)
    (TopRows.row l) (TopRows.row r) hW hs onceI onceJ ff ll rr

theorem exact_and_marks (B : RankedSuffix) :
    ({0} : Finset (Fin 10)) ∈ marks topLabels (rankedFormula B) ∧
    ({2} : Finset (Fin 10)) ∈ marks topLabels (rankedFormula B) ∧
    ({4} : Finset (Fin 10)) ∈ marks topLabels (rankedFormula B) ∧
    ({7} : Finset (Fin 10)) ∈ marks topLabels (rankedFormula B) := by
  obtain ⟨h0,h4⟩ := pair_marks B 0 4 (by decide) (by decide) (by decide)
    772 8 548 (by decide) (by unfold TopRows.valid; decide +kernel)
    (by unfold TopRows.valid; decide +kernel) (found04 B)
  obtain ⟨h2,h7⟩ := pair_marks B 2 7 (by decide) (by decide) (by decide)
    769 32 521 (by decide) (by unfold TopRows.valid; decide +kernel)
    (by unfold TopRows.valid; decide +kernel) (found27 B)
  exact ⟨h0,h2,h4,h7⟩

end Bridge

end PEqualNP.Outside.L_meta_3202

theorem PEqualNP.Outside.L_meta_3202 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (7 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  exact PEqualNP.Outside.L_meta_3202.Bridge.proof_of_marks
    PEqualNP.Outside.L_meta_3202.Bridge.exact_and_marks
    (fun B =>
      PEqualNP.Outside.L_meta_3202.OrMarks3202.exact_or_marks
        (PEqualNP.Outside.L_meta_3202.Bridge.rankedTree B)
        (PEqualNP.Outside.L_meta_3202.Bridge.rankedTree_once B)
        (PEqualNP.Outside.L_meta_3202.Bridge.rankedTree_computes B))
