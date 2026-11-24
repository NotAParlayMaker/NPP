import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3174
namespace Binary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace y6
variable {V: Type*} [DecidableEq V]
def containsEdge (G: SimpleGraph V) (I: Finset V): Prop :=
 ∃ a ∈ I,∃ b ∈ I,G.Adj a b
omit [DecidableEq V] in
lemma singleton_no_edge (G: SimpleGraph V) (w: V): ¬ containsEdge G {w}:=by
 rintro ⟨a,ha,b,hb,hab⟩
 rw [Finset.mem_singleton] at ha hb
 subst a
 subst b
 exact G.loopless.irrefl w hab
lemma pair_contains_edge (G: SimpleGraph V) (u w: V): containsEdge G {u,w}↔G.Adj u w:=by
 constructor
 · rintro ⟨a,ha,b,hb,hab⟩
   simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
   rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
   · exact (G.loopless.irrefl _ hab).elim
   · exact hab
   · exact hab.symm
   · exact (G.loopless.irrefl _ hab).elim
 · intro h
   exact ⟨u,by simp,w,by simp,h⟩
def Independent (G: SimpleGraph V) (S: Finset V): Prop :=
 ∀ a ∈ S,∀ b ∈ S,¬ G.Adj a b
section FiniteGraph
variable [Fintype V] (G: SimpleGraph V) [DecidableRel G.Adj]
def z0 (removed: Finset V) (u: V): Finset V :=
 Finset.univ.filter (fun v => G.Adj u v /\ v ∉ removed)
lemma b31 {A B: Finset V} (h: A ⊆ B) (u: V) :
   z0 G B u ⊆ z0 G A u:=by
 intro v membership
 simp only [z0,Finset.mem_filter,Finset.mem_univ,true_and] at membership ⊢
 exact ⟨membership.1,fun vIn => membership.2 (h vIn)⟩
lemma b85 {A B: Finset V} (h: A ⊆ B) {u w: V}
   (same: z0 G A u=z0 G A w) :
   z0 G B u=z0 G B w:=by
 have e (v: V): z0 G B v=(z0 G A v).filter (· ∉ B):=by
   ext z
   simp only [z0,Finset.mem_filter,Finset.mem_univ,true_and]
   exact ⟨fun hz => ⟨⟨hz.1,fun zIn => hz.2 (h zIn)⟩,hz.2⟩,fun hz => ⟨hz.1.1,hz.2⟩⟩
 rw [e u,e w,same]
def TwinGroup (removed group: Finset V): Prop :=
 ∀ u ∈ group,∀ w ∈ group,(z0 G removed u).Nonempty ->
   (z0 G removed w).Nonempty->z0 G removed u=z0 G removed w
def w39 (removed: Finset V): Finset V :=
 Finset.univ.filter (fun v => z0 G removed v=∅)
def b24 (removed: Finset V) (root: V): Finset V :=
 if root ∉ removed /\ (z0 G removed root).Nonempty then
   Finset.univ.filter (fun v => v ∉ removed /\ z0 G removed v=z0 G removed root)
 else ∅
def z5 (removed: Finset V): Finset V:=removed ∪ w39 G removed
def b20 (removed: Finset V) (root: V): Finset V :=
 z5 G (removed ∪ b24 G removed root)
lemma b29 (removed: Finset V) (root: V): removed ⊆ b20 G removed root:=by
 intro u hu
 exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)
lemma b56 {removed: Finset V} (root u: V)
   (h: ¬ (z0 G removed u).Nonempty): u ∈ b20 G removed root:=by
 have hn: ¬ (z0 G (removed ∪ b24 G removed root) u).Nonempty:=by
   intro existsNeighbor
   exact h (existsNeighbor.mono (b31 G Finset.subset_union_left u))
 have hu: u ∈ w39 G (removed ∪ b24 G removed root):=by
   simp [w39,Finset.not_nonempty_iff_eq_empty.mp hn]
 exact Finset.mem_union_right _ hu
lemma b175 [Nonempty V] {A B Q: Finset V} (smaller: A ⊆ B)
   (twins: TwinGroup G A Q): ∃ root: V,A ∪ Q ⊆ b20 G B root:=by
 classical
 by_cases someActive: ∃ root ∈ Q,root ∉ B /\ (z0 G B root).Nonempty
 · obtain ⟨root,rootQ,rootOut,rootLive⟩:=someActive
   refine ⟨root,?_⟩
   intro u hu
   rcases Finset.mem_union.mp hu with hu | hu
   · exact b29 G B root (smaller hu)
   by_cases uIn: u ∈ B
   · exact b29 G B root uIn
   by_cases live: (z0 G B u).Nonempty
   · have oldU:=live.mono (b31 G smaller u)
     have oldRoot:=rootLive.mono (b31 G smaller root)
     have same:=b85 G smaller (twins u hu root rootQ oldU oldRoot)
     have j0: u ∈ b24 G B root:=by simp [b24,rootOut,rootLive,uIn,same]
     exact Finset.mem_union_left _ (Finset.mem_union_right _ j0)
   · exact b56 G root u live
 · let root: V:=Classical.choice inferInstance
   refine ⟨root,?_⟩
   intro u hu
   rcases Finset.mem_union.mp hu with hu | hu
   · exact b29 G B root (smaller hu)
   by_cases uIn: u ∈ B
   · exact b29 G B root uIn
   exact b56 G root u (fun live => someActive ⟨u,hu,uIn,live⟩)
lemma b67 {removed: Finset V} {u: V} (out: u ∉ z5 G removed) :
   (z0 G (z5 G removed) u).Nonempty:=by
 have uOut: u ∉ removed:=fun h => out (Finset.mem_union_left _ h)
 have old: (z0 G removed u).Nonempty:=by
   by_contra empty
   apply out
   apply Finset.mem_union_right
   simp [w39,Finset.not_nonempty_iff_eq_empty.mp empty]
 obtain ⟨v,hv⟩:=old
 simp only [z0,Finset.mem_filter,Finset.mem_univ,true_and] at hv
 refine ⟨v,?_⟩
 simp only [z0,Finset.mem_filter,Finset.mem_univ,true_and]
 refine ⟨hv.1,fun dropped => ?_⟩
 rcases Finset.mem_union.mp dropped with h | h
 · exact hv.2 h
 · have xz: u ∈ z0 G removed v:=by
     simp only [z0,Finset.mem_filter,Finset.mem_univ,true_and]
     exact ⟨hv.1.symm,uOut⟩
   have none: z0 G removed v=∅:=by simpa [w39] using h
   rw [none] at xz
   exact Finset.notMem_empty _ xz
lemma b51 (removed: Finset V) :
   z5 G (z5 G removed)=z5 G removed:=by
 apply Finset.Subset.antisymm
 · intro u hu
   rcases Finset.mem_union.mp hu with already | isolated
   · exact already
   by_contra out
   have live:=b67 G out
   have noNeighbors: z0 G (z5 G removed) u=∅:=by
     simpa [w39] using isolated
   simpa [noNeighbors] using live
 · exact Finset.subset_union_left
def b60: Finset V->List (Finset V)->Prop
 | _,[] => True
 | removed,group :: rest => TwinGroup G removed group /\ b60 (removed ∪ group) rest
def b13: Finset V->List (Finset V)->Finset V
 | removed,[] => removed
 | removed,group :: rest => b13 (removed ∪ group) rest
def v17: ℕ->Finset V->Finset V->Prop
 | 0,start,finish => finish=start
 | k+1,start,finish => ∃ root: V,v17 k (b20 G start root) finish
lemma b169 [Nonempty V] {A B: Finset V} (groups: List (Finset V))
   (smaller: A ⊆ B) (steps: b60 G A groups) :
   ∃ finish: Finset V,v17 G groups.length B finish /\ b13 A groups ⊆ finish:=by
 induction groups generalizing A B with
 | nil => exact ⟨B,rfl,smaller⟩
 | cons group rest ih =>
   obtain ⟨twins,next⟩:=steps
   obtain ⟨root,subset⟩:=b175 G smaller twins
   obtain ⟨finish,walk,j0⟩:=ih subset next
   exact ⟨finish,⟨root,walk⟩,j0⟩
def b19 (removed: Finset V): Prop :=
 ∀ u v,u ∉ removed->v ∉ removed->¬ G.Adj u v
omit [Fintype V] [DecidableRel G.Adj] in
lemma b178 {A B: Finset V} (subset: A ⊆ B) (noEdges: b19 G A) :
   b19 G B:=by
 intro u v uOut vOut
 exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))
lemma b134 {D: Finset V} (noEdges: b19 G (z5 G D)) :
   z5 G D=Finset.univ:=by
 ext u
 simp only [Finset.mem_univ,iff_true]
 by_contra out
 obtain ⟨v,hv⟩:=b67 G out
 simp only [z0,Finset.mem_filter,Finset.mem_univ,true_and] at hv
 exact noEdges u v out hv.2 hv.1
lemma b99 {k: ℕ} {start finish: Finset V} (walk: v17 G k start finish)
   (closed: ∃ D: Finset V,start=z5 G D): ∃ D: Finset V,finish=z5 G D:=by
 induction k generalizing start with
 | zero =>
   change finish=start at walk
   rw [walk]
   exact closed
 | succ k ih =>
   obtain ⟨root,after⟩:=walk
   exact ih after ⟨_,rfl⟩
lemma b58 [Nonempty V] (groups: List (Finset V))
   (twins: b60 G ∅ groups) (finished: b19 G (b13 ∅ groups)) :
   v17 G groups.length (z5 G ∅) Finset.univ:=by
 obtain ⟨D,steps,subset⟩:=b169 G groups (Finset.empty_subset (z5 G ∅)) twins
 have noEdges:=b178 G subset finished
 obtain ⟨A,hD⟩:=b99 G steps ⟨∅,rfl⟩
 rw [hD] at noEdges
 rwa [hD,b134 G noEdges] at steps
end FiniteGraph
end y6
namespace j7
open y6
variable {V: Type*} [Fintype V] [DecidableEq V] {m: Nat}
def bucket (label: V->Fin m) (r: Fin m): Finset V:=Finset.univ.filter (fun v => label v=r)
def below (label: V->Fin m) (r: Fin m): Finset V:=Finset.univ.filter (fun v => label v < r)
def b23 (label: V->Fin m) (done: List (Fin m)): Finset V :=
 Finset.univ.filter (fun v => label v ∈ done)
omit [DecidableEq V] in
@[simp] lemma coveredBy_nil (label: V->Fin m): b23 label []=∅:=by
 ext v
 simp [b23]
lemma b36 (label: V->Fin m) (done: List (Fin m)) (r: Fin m) :
   b23 label (done ++ [r])=b23 label done ∪ bucket label r:=by
 ext v
 simp [b23,bucket,List.mem_append]
omit [DecidableEq V] in
lemma b98 (label: V->Fin m) (out: Fin m) (done rest: List (Fin m)) (r: Fin m)
   (sorted: (done ++ r :: rest).Pairwise (· < ·))
   (roots: ∀ v: V,label v=out \/ label v ∈ done ++ r :: rest)
   (beforeOut: r < out): b23 label done=below label r:=by
 have facts:=List.pairwise_append.mp sorted
 ext v
 simp only [b23,below,Finset.mem_filter,Finset.mem_univ,true_and]
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
   have after:=(List.pairwise_cons.mp facts.2.1).1 _ later
   exact (lt_asymm earlier after).elim
section Graph
variable (G: SimpleGraph V) [DecidableRel G.Adj]
lemma b110 (label: V->Fin m) (out: Fin m) (roots: List (Fin m))
   (sorted: roots.Pairwise (· < ·)) (allRoots: ∀ v: V,label v=out \/ label v ∈ roots)
   (beforeOut: ∀ r ∈ roots,r < out)
   (twinAt: ∀ r ∈ roots,TwinGroup G (below label r) (bucket label r))
   (done pending: List (Fin m)) (complete: done ++ pending=roots) :
   b60 G (b23 label done) (pending.map (bucket label)):=by
 induction pending generalizing done with
 | nil => exact True.intro
 | cons r tail ih =>
   have rMember: r ∈ roots:=complete ▸ List.mem_append_right done (by simp: r ∈ r :: tail)
   have prev:=b98 label out done tail r (by simpa only [complete] using sorted)
     (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
   have next:=ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
   refine ⟨?_,?_⟩
   · rw [prev]
     exact twinAt r rMember
   · rwa [b36] at next
lemma b96 (label: V->Fin m) (done pending: List (Fin m)) :
   b13 (b23 label done) (pending.map (bucket label))=b23 label (done ++ pending):=by
 induction pending generalizing done with
 | nil => simp [b13]
 | cons r tail ih =>
   change b13 (b23 label done ∪ bucket label r) (tail.map (bucket label))=_
   rw [← b36,ih]
   simp [List.append_assoc]
omit [DecidableRel G.Adj] in
lemma b105 (label: V->Fin m) (out: Fin m) (roots: List (Fin m))
   (allRoots: ∀ v: V,label v=out \/ label v ∈ roots)
   (outputIndependent: Independent G (bucket label out)) :
   b19 G (b13 ∅ (roots.map (bucket label))):=by
 rw [← coveredBy_nil label,b96,List.nil_append]
 intro u v uNot vNot
 have hu: label u=out:=(allRoots u).resolve_right (by simpa [b23] using uNot)
 have hv: label v=out:=(allRoots v).resolve_right (by simpa [b23] using vNot)
 exact outputIndependent u (by simp [bucket,hu]) v (by simp [bucket,hv])
lemma roots_required (label: V->Fin m) (out: Fin m) (branches: Finset (Fin m)) (k: Nat)
   (allRoots: ∀ v: V,label v=out \/ label v ∈ branches)
   (beforeOut: ∀ r ∈ branches,r < out)
   (twinAt: ∀ r ∈ branches,TwinGroup G (below label r) (bucket label r))
   (outputIndependent: Independent G (bucket label out))
   (required: ∀ groups: List (Finset V),b60 G ∅ groups ->
     b19 G (b13 ∅ groups)->k ≤ groups.length): k ≤ branches.card:=by
 let roots:=branches.sort
 have sorted: roots.Pairwise (· < ·):=List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
 have covers (v: V): label v=out \/ label v ∈ roots:=by simpa [roots] using allRoots v
 have early (r) (member: r ∈ roots): r < out:=beforeOut r (by simpa [roots] using member)
 have twins (r) (member: r ∈ roots): TwinGroup G (below label r) (bucket label r) :=
   twinAt r (by simpa [roots] using member)
 have valid: b60 G ∅ (roots.map (bucket label)):=by
   simpa using b110 G label out roots sorted covers early twins [] roots rfl
 have last:=b105 G label out roots covers outputIndependent
 simpa [roots] using required (roots.map (bucket label)) valid last
end Graph
end j7
namespace z2
open PEqualNP.CircuitLowerBounds
def b1 (gs: List Gate) (w: List Bool): List Bool :=
 gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma b42 (gs gs': List Gate) (w: List Bool) :
   b1 (gs ++ gs') w=b1 gs' (b1 gs w):=by
 simp [b1,List.foldl_append]
lemma b61 (gs: List Gate): ∀ w: List Bool,
   ∃ t: List Bool,b1 gs w=w ++ t /\ t.length=gs.length:=by
 induction gs with
 | nil => intro w; exact ⟨[],by simp [b1],rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩:=ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,?_,by simp [hl]⟩
   have: b1 (g :: gs) w
      =b1 gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [this,ht]; simp
lemma b28 (gs: List Gate) (w: List Bool) :
   (b1 gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=b61 gs w
 rw [ht]; simp [hl]
lemma b41 (gs: List Gate) (w: List Bool) (i: ℕ) (h: i < w.length) :
   (b1 gs w).getD i false=w.getD i false:=by
 obtain ⟨t,ht,_⟩:=b61 gs w
 rw [ht,List.getD_append _ _ _ _ h]
def Ok (g: Gate): Prop :=
 g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) /\ g.inputs.length ≤ 2
end z2
namespace z2
open PEqualNP.CircuitLowerBounds
variable {n: ℕ}
lemma b33 {α: Type} (L: List α) (S d: α) (j: ℕ) (h: j≠L.length) :
   (L ++ [S]).getD j d=L.getD j d:=by
 by_cases hj: j < L.length
 · exact List.getD_append _ _ _ _ hj
 · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
lemma b50 {α: Type} (L: List α) (S d: α): (L ++ [S]).getD L.length d=S:=by
 simp
end z2
namespace z2
open PEqualNP.CircuitLowerBounds
def NOk (g: Gate): Prop:=Ok g /\ (g.op=GateOp.not->g.inputs.length ≤ 1)
abbrev f9:=Sum Bool ℕ
def f9.val (w: List Bool): f9->Bool
 | Sum.inl c => c
 | Sum.inr j => w.getD j false
def f9.Valid (m: ℕ): f9->Prop
 | Sum.inl _ => True
 | Sum.inr j => j < m
def v15 (m: ℕ): List f9->Option Gate × f9
 | [] => (none,Sum.inl true)
 | Sum.inl c :: _ => (none,Sum.inl (!c))
 | Sum.inr j :: _ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def w42 (m: ℕ): List f9->Option Gate × f9
 | [] => (none,Sum.inl true)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def qv (m: ℕ): List f9->Option Gate × f9
 | [] => (none,Sum.inl false)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def b12 (op: GateOp) (m: ℕ) (ins: List f9): Option Gate × f9 :=
 match op with
 | GateOp.and => w42 m ins
 | GateOp.or => qv m ins
 | GateOp.not => v15 m ins
 | _ => (none,Sum.inl false)
lemma b172 (op: GateOp) (hop: op=GateOp.and \/ op=GateOp.or \/ op=GateOp.not)
   (w: List Bool) (ins: List f9) (hlen: ins.length ≤ 2)
   (hv: ∀ s ∈ ins,s.Valid w.length) :
   ((b12 op w.length ins).2).Valid (w.length+(b12 op w.length ins).1.toList.length) ∧
   ((b12 op w.length ins).2).val (b1 (b12 op w.length ins).1.toList w)
    =op.eval (ins.map (f9.val w)):=by
 rcases hop with rfl | rfl | rfl
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   · simp [b12,w42,f9.Valid,f9.val,GateOp.eval]
   · cases a <;> simp_all [b12,w42,f9.Valid,f9.val,GateOp.eval,b1]
   · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
       simp_all [b12,w42,f9.Valid,f9.val,GateOp.eval,b1]
   · simp at hlen
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   · simp [b12,qv,f9.Valid,f9.val,GateOp.eval]
   · cases a <;> simp_all [b12,qv,f9.Valid,f9.val,GateOp.eval,b1]
   · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
       simp_all [b12,qv,f9.Valid,f9.val,GateOp.eval,b1]
   · simp at hlen
 · rcases ins with _ | ⟨a,l⟩
   · simp [b12,v15,f9.Valid,f9.val,GateOp.eval]
   · cases a <;> simp_all [b12,v15,f9.Valid,f9.val,GateOp.eval,b1]
def b43 (n: ℕ) (acc: List f9 × List Gate) (g: Gate): List f9 × List Gate :=
 (acc.1 ++ [(b12 g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
   acc.2 ++ (b12 g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n: ℕ) (gs: List Gate) (acc: List f9 × List Gate): List f9 × List Gate :=
 gs.foldl (b43 n) acc
lemma b140 {α: Type} (L: List α) (S d: α) (k: ℕ) (h: L.length=k) :
   (L ++ [S]).getD k d=S:=by
 subst h; simp
lemma b156 {α: Type} (o: Option α): o.toList.length ≤ 1:=by
 cases o <;> simp
lemma z55 (n: ℕ) (gs: List Gate): ∀ acc: List f9 × List Gate,
   (elim n gs acc).2.length ≤ acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc; simp [elim]
 | cons g gs ih =>
   intro acc
   have h1:=ih (b43 n acc g)
   have h2: (b43 n acc g).2.length ≤ acc.2.length+1:=by
     simp only [b43,List.length_append]
     have:=b156 (b12 g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
     omega
   have h3: elim n (g :: gs) acc=elim n gs (b43 n acc g):=rfl
   rw [h3,List.length_cons]; omega
lemma f9.valid_mono {m m': ℕ} (h: m ≤ m'): ∀ s: f9,s.Valid m->s.Valid m'
 | Sum.inl _,_ => trivial
 | Sum.inr _,hj => lt_of_lt_of_le hj h
lemma f9.val_append (w t: List Bool): ∀ s: f9,s.Valid w.length ->
   s.val (w ++ t)=s.val w
 | Sum.inl _,_ => rfl
 | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n: ℕ) (y: List Bool) (w: List Bool) (acc: List f9 × List Gate): Prop :=
 acc.1.length=w.length /\ ∀ i: ℕ,
   (acc.1.getD i (Sum.inl false)).Valid (n+acc.2.length) ∧
   (acc.1.getD i (Sum.inl false)).val (b1 acc.2 y)=w.getD i false
lemma v16 (n: ℕ) (y: List Bool) (hy: y.length=n) (gs: List Gate) :
   ∀ (w: List Bool) (acc: List f9 × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
     Inv n y (b1 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ h; exact h
 | cons g gs ih =>
   intro w acc hok h
   apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (b43 n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   obtain ⟨hl,hi⟩:=h
   set w':=b1 acc.2 y with hw'
   have lw': w'.length=n+acc.2.length:=by rw [hw',b28,hy]
   set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
   have hgok:=hok g List.mem_cons_self
   have hs:=b172 g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
     (by
       intro s hs
       obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
       rw [lw']; exact (hi a).1)
   rw [lw'] at hs
   set r:=b12 g.op (n+acc.2.length) ins with hr
   have hvals: ins.map (f9.val w')=g.inputs.map fun i => w.getD i false:=by
     rw [hins,List.map_map]
     apply List.map_congr_left
     intro a _
     exact (hi a).2
   have hnew: b1 (acc.2 ++ r.1.toList) y=b1 r.1.toList w':=by
     rw [b42]
   obtain ⟨t,ht,htl⟩:=b61 r.1.toList w'
   refine ⟨by simp [b43,hl],?_⟩
   intro i
   show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n+(acc.2 ++ r.1.toList).length) ∧
     ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (b1 (acc.2 ++ r.1.toList) y)=_
   rw [hnew,List.length_append,← Nat.add_assoc]
   by_cases hil: i=acc.1.length
   · subst hil
     rw [b50,hl,b50]
     exact ⟨hs.1,by rw [hs.2,hvals]⟩
   · rw [b33 _ _ _ _ hil,b33 _ _ _ _ (by omega)]
     refine ⟨f9.valid_mono (by omega) _ (hi i).1,?_⟩
     rw [ht,f9.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
     exact (hi i).2
def q6 (op: GateOp): Bool :=
 match op with
 | .not => true
 | _ => false
def b47 (test: GateOp->Bool) (gs: List Gate): ℕ :=
 gs.countP (fun g => test g.op)
lemma b157 (op: GateOp) (m: ℕ) (ins: List f9) :
   ∀ g ∈ (b12 op m ins).1,g.op=op:=by
 intro g hg
 cases op <;> simp only [b12] at hg
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [w42] at hg <;> (subst hg; rfl)
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [qv] at hg <;> (subst hg; rfl)
 · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp [v15] at hg <;> (subst hg; rfl)
 · simp at hg
 · simp at hg
lemma b174 (test: GateOp->Bool) (gs hs: List Gate) :
   b47 test (gs ++ hs)=b47 test gs+b47 test hs:=by
 simp [b47]
lemma b151 (test: GateOp->Bool) (g: Gate) (gs: List Gate) :
   b47 test (g :: gs)=b47 test gs+(if test g.op then 1 else 0):=by
 by_cases h: test g.op <;> simp [b47,h]
lemma b133 (test: GateOp->Bool) (op: GateOp) (m: ℕ) (ins: List f9) :
   b47 test (b12 op m ins).1.toList ≤ (if test op then 1 else 0):=by
 cases h: (b12 op m ins).1 with
 | none => simp [b47]
 | some g =>
   have hg: g ∈ (b12 op m ins).1:=by simp [h]
   have he:=b157 op m ins g hg
   simp [h,b151,b47,he]
lemma b167 (test: GateOp->Bool) (n: ℕ) (gs: List Gate) :
   ∀ acc: List f9 × List Gate,
     b47 test (elim n gs acc).2 ≤ b47 test acc.2+b47 test gs:=by
 induction gs with
 | nil => intro acc; simp [elim,b47]
 | cons g gs ih =>
   intro acc
   change b47 test (elim n gs (b43 n acc g)).2 ≤ _
   apply (ih (b43 n acc g)).trans
   simp only [b43,b174,b151]
   have hb:=b133 test g.op (n+acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
   omega
def z6 (gs: List Gate): ℕ :=
 gs.countP (fun g => !(q6 g.op))
lemma b65 (n: ℕ) (gs: List Gate) (acc: List f9 × List Gate) :
   z6 (elim n gs acc).2 ≤ z6 acc.2+z6 gs :=
 b167 (fun op => !(q6 op)) n gs acc
end z2
namespace z2
open PEqualNP.CircuitLowerBounds
def w43 (m: ℕ) (g: Gate): Prop :=
 (g.op=GateOp.not /\ ∃ j,j < m /\ g.inputs=[j]) ∨
 ((g.op=GateOp.and \/ g.op=GateOp.or) /\ ∃ j k,j < m /\ k < m /\ g.inputs=[j,k])
def v0 (m: ℕ) (gs: List Gate): Prop :=
 ∀ (p: ℕ) (g: Gate),gs[p]?=some g->w43 (m+p) g
lemma w43.nok {m: ℕ} {g: Gate} (h: w43 m g): NOk g:=by
 rcases h with ⟨h1,j,_,h2⟩ | ⟨h1 | h1,j,k,_,_,h2⟩
 · refine ⟨⟨?_,?_⟩,?_⟩
   · rw [h1]; exact Or.inr (Or.inr rfl)
   · rw [h2]; simp
   · intro _; rw [h2]; simp
 · refine ⟨⟨?_,?_⟩,?_⟩
   · rw [h1]; exact Or.inl rfl
   · rw [h2]; simp
   · intro h; rw [h1] at h; cases h
 · refine ⟨⟨?_,?_⟩,?_⟩
   · rw [h1]; exact Or.inr (Or.inl rfl)
   · rw [h2]; simp
   · intro h; rw [h1] at h; cases h
lemma w43.lt {m: ℕ} {g: Gate} (h: w43 m g): ∀ a ∈ g.inputs,a < m:=by
 intro a ha
 rcases h with ⟨_,j,hj,h2⟩ | ⟨_,j,k,hj,hk,h2⟩
 · rw [h2] at ha
   simp at ha
   subst ha; exact hj
 · rw [h2] at ha
   simp at ha
   rcases ha with rfl | rfl
   · exact hj
   · exact hk
lemma b188 (m: ℕ) (gs: List Gate) (h: v0 m gs): ∀ g ∈ gs,NOk g:=by
 intro g hg
 obtain ⟨p,hp⟩:=List.mem_iff_getElem?.1 hg
 exact (h p g hp).nok
lemma b173 (op: GateOp) (m: ℕ) (ins: List f9) (hv: ∀ s ∈ ins,s.Valid m) :
   ∀ g ∈ (b12 op m ins).1,w43 m g:=by
 intro g hg
 cases op <;> simp only [b12] at hg
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [w42] at hg
   subst hg
   refine Or.inr ⟨Or.inl rfl,_,_,?_,?_,rfl⟩
   · exact hv _ List.mem_cons_self
   · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [qv] at hg
   subst hg
   refine Or.inr ⟨Or.inr rfl,_,_,?_,?_,rfl⟩
   · exact hv _ List.mem_cons_self
   · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
 · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [v15] at hg
   subst hg
   refine Or.inl ⟨rfl,_,?_,rfl⟩
   exact hv _ List.mem_cons_self
 · simp at hg
 · simp at hg
lemma b171? {α: Type} (o: Option α) (k: ℕ) (a: α)
   (h: o.toList[k]?=some a): k=0 /\ a ∈ o:=by
 cases o with
 | none => simp at h
 | some b =>
   cases k with
   | zero => simp at h; simp [h]
   | succ k => simp at h
lemma v81 (n: ℕ) (y: List Bool) (hy: y.length=n) (gs: List Gate) :
   ∀ (w: List Bool) (acc: List f9 × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
     v0 n acc.2->v0 n (elim n gs acc).2:=by
 induction gs with
 | nil => intro w acc _ _ h; exact h
 | cons g gs ih =>
   intro w acc hok hinv hcl
   have hinv': Inv n y (b1 [g] w) (b43 n acc g) :=
     v16 n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
   refine ih _ (b43 n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
   intro p g' hp
   have hp': (acc.2 ++ (b12 g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]?=some g':=hp
   by_cases hlt: p < acc.2.length
   · rw [List.getElem?_append_left hlt] at hp'
     exact hcl p g' hp'
   · rw [List.getElem?_append_right (by omega)] at hp'
     obtain ⟨h0,hmem⟩:=b171? _ _ _ hp'
     have hpl: p=acc.2.length:=by omega
     rw [hpl]
     exact b173 _ _ _ (fun s hs => by
       obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
       exact (hinv.2 a).1) g' hmem
def b9 (n: ℕ): List f9:=List.ofFn (fun i: Fin n => Sum.inr i)
lemma jv (n: ℕ) (y: Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y) (b9 n,[]):=by
 refine ⟨by simp [b9],?_⟩
 intro i
 by_cases hlt: i < n
 · simp [b9,hlt,f9.Valid,f9.val,b1]
 · rw [List.getD_eq_default _ _ (by simp [b9]; omega),
     List.getD_eq_default _ _ (by simp; omega)]
   exact ⟨trivial,rfl⟩
lemma v80 {α: Type} (m: ℕ) (F: Fin m->α) (d: α) (j: Fin m) :
   (List.ofFn F).getD j d=F j:=by
 simp
lemma z48 {α: Type}: ∀ (l: List α) (p: ℕ) (g: α),l[p]?=some g ->
   ∃ pre post,l=pre ++ g :: post /\ pre.length=p:=by
 intro l
 induction l with
 | nil => intro p g h; simp at h
 | cons x l ih =>
   intro p g h
   cases p with
   | zero =>
     simp at h
     subst h
     exact ⟨[],l,rfl,rfl⟩
   | succ p =>
     simp at h
     obtain ⟨pre,post,rfl,rfl⟩:=ih p g h
     exact ⟨x :: pre,post,rfl,rfl⟩
lemma b190 (k: ℕ) (gs: List Gate): ∀ w w': List Bool,
   (∀ g ∈ gs,k ∉ g.inputs)->w.length=w'.length ->
   (∀ j,j≠k->w.getD j false=w'.getD j false) ->
   ∀ j,j≠k->(b1 gs w).getD j false=(b1 gs w').getD j false:=by
 induction gs with
 | nil => intro w w' _ _ h; exact h
 | cons g gs ih =>
   intro w w' hno hl h
   have hno':=hno g List.mem_cons_self
   have e: (g.inputs.map fun i => w.getD i false)=g.inputs.map fun i => w'.getD i false :=
     List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
   apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
     (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
     (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
   intro j hj
   by_cases hjl: j=w.length
   · rw [hjl,b50,hl,b50,e]
   · rw [b33 _ _ _ _ hjl,b33 _ _ _ _ (by omega)]
     exact h j hj
end z2
namespace z2
open PEqualNP.CircuitLowerBounds
def vl {k: ℕ} (gs: List Gate) (u: Fin k->Bool) (j: ℕ): Bool :=
 (b1 gs (List.ofFn u)).getD j false
lemma b69 {k: ℕ} (gs: List Gate) (u: Fin k->Bool) (j: ℕ) (h: j < k) :
   vl gs u j=u ⟨j,h⟩:=by
 unfold vl
 rw [b41 gs _ j (by simpa using h)]
 exact v80 k u false ⟨j,h⟩
lemma x52 {k: ℕ} (gs: List Gate) (hcl: v0 k gs) (u: Fin k->Bool) (p: ℕ)
   (g: Gate) (hp: gs[p]?=some g) :
   vl gs u (k+p)=g.op.eval (g.inputs.map (vl gs u)):=by
 have hlt:=(hcl p g hp).lt
 obtain ⟨pre,post,rfl,rfl⟩:=z48 gs p g hp
 have hwl: (b1 pre (List.ofFn u)).length=k+pre.length:=by
   rw [b28]; simp
 have e: b1 (pre ++ g :: post) (List.ofFn u)
    =b1 post (b1 pre (List.ofFn u) ++
       [g.op.eval (g.inputs.map fun i => (b1 pre (List.ofFn u)).getD i false)]):=by
   rw [b42]; rfl
 have full: ∀ j,j < k+pre.length ->
     (b1 (pre ++ g :: post) (List.ofFn u)).getD j false
      =(b1 pre (List.ofFn u)).getD j false:=by
   intro j hj
   rw [e,b41 _ _ j (by simp [hwl]; omega),b33 _ _ _ _ (by omega)]
 have top: (b1 (pre ++ g :: post) (List.ofFn u)).getD (k+pre.length) false
    =g.op.eval (g.inputs.map fun i => (b1 pre (List.ofFn u)).getD i false):=by
   rw [e,b41 _ _ _ (by simp [hwl]),b140 _ _ _ _ hwl]
 show (b1 (pre ++ g :: post) (List.ofFn u)).getD (k+pre.length) false
  =g.op.eval (g.inputs.map fun j => (b1 (pre ++ g :: post) (List.ofFn u)).getD j false)
 rw [top]
 congr 1
 apply List.map_congr_left
 intro a ha
 exact (full a (hlt a ha)).symm
lemma z39 {k: ℕ} (gs: List Gate) (hcl: v0 k gs) (u u': Fin k->Bool) (p: ℕ)
   (g: Gate) (hp: gs[p]?=some g) (h: ∀ a ∈ g.inputs,vl gs u a=vl gs u' a) :
   vl gs u (k+p)=vl gs u' (k+p):=by
 rw [x52 gs hcl u p g hp,x52 gs hcl u' p g hp]
 congr 1
 exact List.map_congr_left h
lemma y78 (k: ℕ) (pre: List Gate) (g: Gate) (post: List Gate)
   (hcl: v0 k (pre ++ g :: post)) (o: ℕ) (S: f9)
   (hS: ∀ y: Fin k->Bool,S.Valid (k+(elim k pre (b9 k,[])).2.length) ∧
     S.val (b1 (elim k pre (b9 k,[])).2 (List.ofFn y))
      =vl (pre ++ g :: post) y (k+pre.length))
   (hnc: ∃ y y': Fin k->Bool,vl (pre ++ g :: post) y o≠vl (pre ++ g :: post) y' o) :
   ∃ gs' o',v0 k gs' /\ gs'.length+1 ≤ (pre ++ g :: post).length ∧
     z6 gs' ≤ z6 pre+z6 post ∧
     ∀ y: Fin k->Bool,vl gs' y o'=vl (pre ++ g :: post) y o:=by
 have hok: ∀ g' ∈ pre ++ g :: post,Ok g':=fun g' hg' => (b188 _ _ hcl g' hg').1
 have hokpre: ∀ g' ∈ pre,Ok g':=fun g' h => hok g' (List.mem_append_left _ h)
 have hokpost: ∀ g' ∈ post,Ok g' :=
   fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have inv1: ∀ y: Fin k->Bool,Inv k (List.ofFn y) (b1 pre (List.ofFn y))
     (elim k pre (b9 k,[])) :=
   fun y => v16 k _ (by simp) pre _ _ hokpre (jv k y)
 have hwl: ∀ y: Fin k->Bool,(b1 pre (List.ofFn y)).length=k+pre.length:=by
   intro y; rw [b28]; simp
 have hfull: ∀ y: Fin k->Bool,b1 (pre ++ g :: post) (List.ofFn y)
    =b1 post (b1 pre (List.ofFn y) ++
       [g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false)]):=by
   intro y; rw [b42]; rfl
 have hgv: ∀ y: Fin k->Bool,vl (pre ++ g :: post) y (k+pre.length)
    =g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false):=by
   intro y
   show (b1 (pre ++ g :: post) (List.ofFn y)).getD (k+pre.length) false=_
   rw [hfull,b41 _ _ _ (by simp [hwl y]),b140 _ _ _ _ (hwl y)]
 have inv2: ∀ y: Fin k->Bool,Inv k (List.ofFn y)
     (b1 pre (List.ofFn y) ++
       [g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false)])
     ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2):=by
   intro y
   obtain ⟨hl,hi⟩:=inv1 y
   refine ⟨by simp [hl],?_⟩
   intro a
   show (((elim k pre (b9 k,[])).1 ++ [S]).getD a (Sum.inl false)).Valid
       (k+(elim k pre (b9 k,[])).2.length) ∧
     (((elim k pre (b9 k,[])).1 ++ [S]).getD a (Sum.inl false)).val
       (b1 (elim k pre (b9 k,[])).2 (List.ofFn y))=_
   by_cases hal: a=(elim k pre (b9 k,[])).1.length
   · rw [hal,b50,hl,b50]
     exact ⟨(hS y).1,by rw [(hS y).2,hgv]⟩
   · rw [b33 _ _ _ _ hal,b33 _ _ _ _ (by omega)]
     exact hi a
 have inv3: ∀ y: Fin k->Bool,Inv k (List.ofFn y)
     (b1 (pre ++ g :: post) (List.ofFn y))
     (elim k post ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2)):=by
   intro y
   rw [hfull]
   exact v16 k _ (by simp) post _ _ hokpost (inv2 y)
 have hc1: v0 k (elim k pre (b9 k,[])).2 :=
   v81 k (List.ofFn fun _: Fin k => false) (by simp) pre _ _ hokpre (jv k _)
     (by intro p g' hp; simp at hp)
 have hc3: v0 k
     (elim k post ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2)).2 :=
   v81 k (List.ofFn fun _: Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
 have hlen: (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
     (elim k pre (b9 k,[])).2)).2.length+1 ≤ (pre ++ g :: post).length:=by
   have h1: (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
       (elim k pre (b9 k,[])).2)).2.length
       ≤ (elim k pre (b9 k,[])).2.length+post.length:=z55 k post _
   have h2: (elim k pre (b9 k,[])).2.length ≤ 0+pre.length :=
     z55 k pre (b9 k,[])
   simp only [List.length_append,List.length_cons]
   omega
 have hval: ∀ y: Fin k->Bool,
     ((elim k post ((elim k pre (b9 k,[])).1 ++ [S],
       (elim k pre (b9 k,[])).2)).1.getD o (Sum.inl false)).val
       (b1 (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
         (elim k pre (b9 k,[])).2)).2 (List.ofFn y))
    =vl (pre ++ g :: post) y o:=fun y => ((inv3 y).2 o).2
 cases hst: (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
     (elim k pre (b9 k,[])).2)).1.getD o (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   rw [← hval y,← hval y',hst]
   rfl
 | inr j =>
   refine ⟨_,j,hc3,hlen,?_,?_⟩
   · exact (b65 k post _).trans (Nat.add_le_add_right
       (by simpa [z6] using b65 k pre (b9 k,[])) _)
   · intro y
     have h:=hval y
     rw [hst] at h
     exact h
lemma b177 (k: ℕ) (gs: List Gate) (hcl: v0 k gs) (o p j: ℕ) (hp: p < gs.length)
   (hj: j < k+p) (heq: ∀ y: Fin k->Bool,vl gs y (k+p)=vl gs y j)
   (hnc: ∃ y y': Fin k->Bool,vl gs y o≠vl gs y' o) :
   ∃ gs' o',v0 k gs' /\ gs'.length+1 ≤ gs.length /\ z6 gs' ≤ z6 (gs.eraseIdx p) ∧
     ∀ y: Fin k->Bool,vl gs' y o'=vl gs y o:=by
 obtain ⟨g,hg⟩: ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
 obtain ⟨pre,post,rfl,rfl⟩:=z48 gs p g hg
 rw [List.eraseIdx_append_of_length_le le_rfl,Nat.sub_self,List.eraseIdx_cons_zero]
 have hcount: z6 (pre ++ post)=z6 pre+z6 post:=by
   simp [z6]
 rw [hcount]
 apply y78 k pre g post hcl o ((elim k pre (b9 k,[])).1.getD j (Sum.inl false))
   ?_ hnc
 intro y
 have hokpre: ∀ g' ∈ pre,Ok g' :=
   fun g' h => (b188 _ _ hcl g' (List.mem_append_left _ h)).1
 have inv1:=v16 k (List.ofFn y) (by simp) pre _ _ hokpre (jv k y)
 refine ⟨(inv1.2 j).1,?_⟩
 rw [(inv1.2 j).2,heq y]
 show (b1 pre (List.ofFn y)).getD j false
  =(b1 (pre ++ g :: post) (List.ofFn y)).getD j false
 rw [b42,b41 (g :: post) (b1 pre (List.ofFn y)) j
   (by rw [b28]; simp; omega)]
end z2
namespace w4
open PEqualNP.CircuitLowerBounds
open z2
def kc {W: Type} (g5: W->W->Prop) (cut: W) (a b: W): Prop :=
 g5 a b /\ a≠cut /\ b≠cut
lemma b147 {W: Type} (rank: W->Nat) (input: W->Prop)
   (g5: W->W->Prop) (cut: W) (x y: W->Bool)
   (order: ∀ a b,g5 a b->rank a < rank b)
   (localStep: ∀ b,¬ input b->x b≠y b->∃ a,g5 a b /\ x a≠y a)
   (sameCut: x cut=y cut) {out: W} (different: x out≠y out) :
   ∃ a,input a /\ x a≠y a /\ Relation.ReflTransGen (kc g5 cut) a out:=by
 classical
 have track: ∀ k b,rank b=k->x b≠y b ->
     ∃ a,input a /\ x a≠y a /\ Relation.ReflTransGen (kc g5 cut) a b:=by
   intro k
   induction k using Nat.strong_induction_on with
   | ind k ih =>
     intro b hb diff
     by_cases hInput: input b
     · exact ⟨b,hInput,diff,Relation.ReflTransGen.refl⟩
     · obtain ⟨p,hp,dp⟩:=localStep b hInput diff
       have earlier: rank p < k:=(order p b hp).trans_eq hb
       obtain ⟨a,ha,da,path⟩:=ih (rank p) earlier p rfl dp
       have pOff: p≠cut:=by rintro rfl; exact dp sameCut
       have bOff: b≠cut:=by rintro rfl; exact diff sameCut
       exact ⟨a,ha,da,path.tail ⟨hp,pOff,bOff⟩⟩
 exact track (rank out) out rfl different
lemma b180 {W: Type} (rank: W->Nat) (input: W->Prop)
   (g5: W->W->Prop) (cut out: W) (x y: W->Bool)
   (order: ∀ a b,g5 a b->rank a < rank b)
   (localStep: ∀ b,¬ input b->x b≠y b->∃ a,g5 a b /\ x a≠y a)
   (sameCut: x cut=y cut)
   (blocked: ∀ a,input a->x a≠y a ->
     ¬ Relation.ReflTransGen (kc g5 cut) a out): x out=y out:=by
 by_contra different
 obtain ⟨a,ha,da,reaches⟩:=b147 rank input g5 cut x y
   order localStep sameCut different
 exact blocked a ha da reaches
lemma b184 {A: Type} (w f: A->Bool)
   (h: ∀ x y,w x=w y->f x=f y) :
   ∃ outer: Bool->Bool,∀ x,outer (w x)=f x:=by
 classical
 let outer (b: Bool):=if hb: ∃ a,w a=b then f (Classical.choose hb) else false
 refine ⟨outer,fun x => ?_⟩
 have hx: ∃ a,w a=w x:=⟨x,rfl⟩
 unfold outer
 rw [dite_eq_left hx]
 exact h _ _ (Classical.choose_spec hx)
def b8 {n: Nat} (gs: List Gate) (v: Fin n): Fin (n+gs.length) :=
 v.castLE (Nat.le_add_right n gs.length)
def b5 {n: Nat} (gs: List Gate) (a b: Fin (n+gs.length)): Prop :=
 ∃ (p: Nat) (g: Gate),gs[p]?=some g /\ b.val=n+p /\ a.val ∈ g.inputs
lemma b15 {n: Nat} {gs: List Gate} (hcl: v0 n gs)
   {a b: Fin (n+gs.length)} (g5: b5 gs a b): a.val < b.val:=by
 obtain ⟨p,g,hpg,hb,ha⟩:=g5
 rw [hb]
 exact (hcl p g hpg).lt _ ha
private lemma b166 {n: Nat} {gs: List Gate} (hcl: v0 n gs)
   (x y: Fin n->Bool) (b: Fin (n+gs.length)) (notInput: ¬ b.val < n)
   (diff: vl gs x b.val≠vl gs y b.val) :
   ∃ a: Fin (n+gs.length),b5 gs a b /\ vl gs x a.val≠vl gs y a.val:=by
 let p:=b.val - n
 have hb: b.val=n+p:=by dsimp [p]; omega
 have hp: p < gs.length:=by have:=b.isLt; omega
 let g:=gs[p]
 have hpg: gs[p]?=some g:=List.getElem?_eq_getElem hp
 have differingRead: ∃ a ∈ g.inputs,vl gs x a≠vl gs y a:=by
   classical
   by_contra none
   apply diff
   rw [hb]
   exact z39 gs hcl x y p g hpg (fun a ha => by
     by_contra da
     exact none ⟨a,ha,da⟩)
 obtain ⟨a,ha,da⟩:=differingRead
 have ha':=(hcl p g hpg).lt a ha
 refine ⟨⟨a,by have:=b.isLt; omega⟩,⟨p,g,hpg,hb,ha⟩,da⟩
lemma b59 {n: Nat} {gs: List Gate} (hcl: v0 n gs)
   (cut out: Fin (n+gs.length)) (x y: Fin n->Bool)
   (sameCut: vl gs x cut.val=vl gs y cut.val)
   (blocked: ∀ i: Fin n,x i≠y i ->
     ¬ Relation.ReflTransGen (kc (b5 gs) cut) (b8 gs i) out) :
   vl gs x out.val=vl gs y out.val:=by
 apply b180 Fin.val (fun v => v.val < n) (b5 gs) cut out
   (fun v => vl gs x v.val) (fun v => vl gs y v.val)
 · exact fun _ _ e => b15 hcl e
 · exact b166 hcl x y
 · exact sameCut
 · intro a ha diff
   let i: Fin n:=⟨a.val,ha⟩
   have sameWire: b8 gs i=a:=Fin.ext rfl
   have di: x i≠y i:=by
     rw [b69 gs x a.val ha,b69 gs y a.val ha] at diff
     exact diff
   rw [← sameWire]
   exact blocked i di
lemma b135 {n: Nat} {gs: List Gate} (hcl: v0 n gs)
   (cut out: Fin (n+gs.length)) (group: Fin n->Prop) (base: Fin n->Bool)
   (blocked: ∀ i: Fin n,group i ->
     ¬ Relation.ReflTransGen (kc (b5 gs) cut) (b8 gs i) out) :
   ∃ outer: Bool->Bool,∀ x: Fin n->Bool,(∀ i,¬ group i->x i=base i) ->
     outer (vl gs x cut.val)=vl gs x out.val:=by
 let Fiber:={x: Fin n->Bool // ∀ i,¬ group i->x i=base i}
 obtain ⟨outer,ho⟩:=b184
   (fun x: Fiber => vl gs x.val cut.val) (fun x: Fiber => vl gs x.val out.val) (by
     intro x y sameCut
     apply b59 hcl cut out x.val y.val sameCut
     intro i diff
     apply blocked i
     by_contra notGroup
     exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
 exact ⟨outer,fun x agrees => ho ⟨x,agrees⟩⟩
end w4
namespace z2.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity z2
def Dep {m: ℕ} (f: (Fin m->Bool)->Bool) (p: Fin m): Prop :=
 ∃ x: Fin m->Bool,f (Function.update x p (!x p))≠f x
def p1 (m: ℕ) (f: (Fin m->Bool)->Bool) (gs: List Gate) (o: ℕ): Prop :=
 v0 m gs /\ (∀ x: Fin m->Bool,vl gs x o=f x) ∧
   ∀ (gs': List Gate) (o': ℕ),v0 m gs'->(∀ x: Fin m->Bool,vl gs' x o'=f x) ->
   z6 gs' ≤ z6 gs->gs.length ≤ gs'.length
def p1.hcl {m f gs o} (h: p1 m f gs o):=h.1
def p1.hev {m f gs o} (h: p1 m f gs o):=h.2.1
def p1.hmin {m f gs o} (h: p1 m f gs o):=h.2.2
def c3 (gs: List Gate) (p w: ℕ): Prop:=∃ g,gs[p]?=some g /\ w ∈ g.inputs
lemma w97 {m: ℕ} {f: (Fin m->Bool)->Bool} {p: Fin m} (h: Dep f p) :
   ∃ x y: Fin m->Bool,f x≠f y:=by
 obtain ⟨x,hx⟩:=h
 exact ⟨_,_,hx⟩
lemma x23 {k: ℕ} {gs: List Gate} (hcl: v0 k gs) {q w: ℕ} (h: c3 gs q w) :
   w < k+q:=by
 obtain ⟨g,hg,hw⟩:=h
 exact (hcl q g hg).lt w hw
lemma v23 {k: ℕ} (gs: List Gate) (u: Fin k->Bool) (w: ℕ) (h: k+gs.length ≤ w) :
   vl gs u w=false:=by
 unfold vl
 exact List.getD_eq_default _ _ (by rw [b28]; simp; omega)
lemma b149 {n: ℕ} {f: (Fin n->Bool)->Bool} (C: Circuit)
   (hfan: FanInTwo C) (hev: ∀ x: Fin n->Bool,C.eval (List.ofFn x)=f x)
   (hnc: ∃ x y,f x≠f y) :
   ∃ gs o,v0 n gs /\ z6 gs ≤ z6 C.gates /\ ∀ x,vl gs x o=f x:=by
 have hok: ∀ g ∈ C.gates,Ok g:=hfan
 set acc:=elim n C.gates (b9 n,[]) with hacc
 have hinv: ∀ y: Fin n->Bool,
     Inv n (List.ofFn y) (b1 C.gates (List.ofFn y)) acc :=
   fun y => v16 n _ (by simp) C.gates _ _ hok (jv n y)
 have hval: ∀ y: Fin n->Bool,
     (acc.1.getD C.output (Sum.inl false)).val (b1 acc.2 (List.ofFn y))=f y:=by
   intro y
   rw [((hinv y).2 C.output).2,← hev y]
   rfl
 cases hst: acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   rw [← hval y,← hval y',hst]
   rfl
 | inr j =>
   refine ⟨acc.2,j,?_,?_,?_⟩
   · exact v81 n (List.ofFn fun _: Fin n => false) (by simp) C.gates _ _ hok
       (jv n _) (by intro p g hp; simp at hp)
   · simpa [z6,hacc] using b65 n C.gates (b9 n,[])
   · intro y
     simpa only [hst,f9.val,vl] using hval y
lemma b146 {n: ℕ} {f: (Fin n->Bool)->Bool} (C: Circuit)
   (hfan: FanInTwo C) (hev: ∀ x: Fin n->Bool,C.eval (List.ofFn x)=f x)
   (hnc: ∃ x y,f x≠f y) :
   ∃ gs o,p1 n f gs o /\ z6 gs ≤ z6 C.gates:=by
 classical
 let admissible (t: ℕ):=∃ gs o,v0 n gs /\ z6 gs ≤ z6 C.gates ∧
   (∀ x,vl gs x o=f x) /\ gs.length=t
 obtain ⟨gs,o,clean,count,he⟩:=b149 C hfan hev hnc
 have existsAdmissible: ∃ t,admissible t:=⟨gs.length,gs,o,clean,count,he,rfl⟩
 obtain ⟨gs',o',hc,hb,he',hl⟩:=Nat.find_spec existsAdmissible
 refine ⟨gs',o',⟨hc,he',?_⟩,hb⟩
 intro testGates testOut testClean testEval testCost
 have lower:=Nat.find_min' existsAdmissible
   (show admissible testGates.length from
     ⟨testGates,testOut,testClean,testCost.trans hb,testEval,rfl⟩)
 exact hl.trans_le lower
lemma y77 (k: ℕ) (gs: List Gate) (hcl: v0 k gs) (o p: ℕ) (hp: p < gs.length)
   (ho: o≠k+p) (hno: ∀ q,¬ c3 gs q (k+p))
   (hnc: ∃ y y': Fin k->Bool,vl gs y o≠vl gs y' o) :
   ∃ gs' o',v0 k gs' /\ gs'.length+1 ≤ gs.length /\ z6 gs' ≤ z6 gs ∧
     ∀ y: Fin k->Bool,vl gs' y o'=vl gs y o:=by
 obtain ⟨g,hg⟩: ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
 have hpos: 0 < k+p:=by
   rcases hcl p g hg with ⟨_,j,hj,_⟩ | ⟨_,j,_,hj,_,_⟩ <;> omega
 let g0: Gate:=⟨GateOp.and,[0,0]⟩
 let gs':=gs.set p g0
 have hlen: gs'.length=gs.length:=by simp [gs']
 have hget_p: gs'[p]?=some g0:=by simp [gs',hp]
 have hget_ne: ∀ r,r≠p->gs'[r]?=gs[r]?:=by
   intro r hr
   simp [gs',Ne.symm hr]
 have hcl': v0 k gs':=by
   intro r g' hr'
   by_cases hrp: r=p
   · subst hrp
     rw [hget_p] at hr'
     cases hr'
     exact Or.inr ⟨Or.inl rfl,0,0,hpos,hpos,rfl⟩
   · rw [hget_ne r hrp] at hr'
     exact hcl r g' hr'
 have hagree: ∀ y: Fin k->Bool,∀ w,w≠k+p->vl gs' y w=vl gs y w:=by
   intro y w
   induction w using Nat.strong_induction_on with
   | _ w ih =>
     intro hw
     by_cases hwk: w < k
     · rw [b69 gs' y w hwk,b69 gs y w hwk]
     · obtain ⟨r,rfl⟩: ∃ r,w=k+r:=⟨w - k,by omega⟩
       have hrp: r≠p:=fun e => hw (by rw [e])
       cases hr: gs[r]? with
       | none =>
         have hl: gs.length ≤ r:=List.getElem?_eq_none_iff.1 hr
         rw [v23 gs' y _ (by omega),v23 gs y _ (by omega)]
       | some g' =>
         have hr': gs'[r]?=some g':=by rw [hget_ne r hrp]; exact hr
         rw [x52 gs' hcl' y r g' hr',x52 gs hcl y r g' hr]
         congr 1
         apply List.map_congr_left
         intro a ha
         have hlt:=(hcl r g' hr).lt a ha
         exact ih a hlt (fun e => hno r ⟨g',hr,e ▸ ha⟩)
 have halias: ∀ y: Fin k->Bool,vl gs' y (k+p)=vl gs' y 0:=by
   intro y
   rw [x52 gs' hcl' y p g0 hget_p]
   simp [g0,GateOp.eval]
 have hnc': ∃ y y': Fin k->Bool,vl gs' y o≠vl gs' y' o:=by
   obtain ⟨y,y',h⟩:=hnc
   exact ⟨y,y',by rw [hagree y o ho,hagree y' o ho]; exact h⟩
 obtain ⟨gs'',o'',hc'',hl'',hcost,he''⟩ :=
   b177 k gs' hcl' o p 0 (by omega) hpos halias hnc'
 have hkeep: z6 (gs'.eraseIdx p) ≤ z6 gs:=by
   rw [show gs'.eraseIdx p=gs.eraseIdx p from List.eraseIdx_set_eq]
   exact (List.eraseIdx_sublist gs p).countP_le
 exact ⟨gs'',o'',hc'',by omega,hcost.trans hkeep,fun y => by rw [he'' y,hagree y o ho]⟩
section LocalSection1
variable {m: ℕ} {f: (Fin m->Bool)->Bool} {gs: List Gate} {o: ℕ}
lemma p1.ncv (L: p1 m f gs o) (hnc: ∃ x y: Fin m->Bool,f x≠f y) :
   ∃ y y': Fin m->Bool,vl gs y o≠vl gs y' o:=by
 obtain ⟨x,y,h⟩:=hnc
 exact ⟨x,y,by rw [L.hev,L.hev]; exact h⟩
lemma p1.no_alias (L: p1 m f gs o) (hnc: ∃ x y: Fin m->Bool,f x≠f y) (p: ℕ)
   (hp: p < gs.length) (j: ℕ) (hj: j < m+p) :
   ¬ ∀ u: Fin m->Bool,vl gs u (m+p)=vl gs u j:=by
 intro hall
 obtain ⟨gs',o',hc',hl',hcost,he'⟩:=b177 m gs L.hcl o p j hp hj hall (L.ncv hnc)
 have hcost': z6 gs' ≤ z6 gs :=
   hcost.trans (List.eraseIdx_sublist gs p).countP_le
 have:=L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
 omega
lemma p1.live (L: p1 m f gs o) (hnc: ∃ x y: Fin m->Bool,f x≠f y) (p: ℕ)
   (hp: p < gs.length) (ho: o≠m+p): ∃ q,p < q /\ c3 gs q (m+p):=by
 by_contra hno
 have hno': ∀ q,¬ c3 gs q (m+p):=by
   intro q hq
   by_cases hpq: p < q
   · exact hno ⟨q,hpq,hq⟩
   · have:=x23 L.hcl hq
     omega
 obtain ⟨gs',o',hc',hl',hcost,he'⟩:=y77 m gs L.hcl o p hp ho hno' (L.ncv hnc)
 have:=L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
 omega
lemma p1.dep_read (L: p1 m f gs o) (i: Fin m) (hd: Dep f i)
   (hnc: ∀ b: Bool,∃ x y: Fin m->Bool,
     f (Function.update x i b)≠f (Function.update y i b)): ∃ q,c3 gs q i:=by
 by_contra hno
 have hno': ∀ g ∈ gs,(i: ℕ) ∉ g.inputs:=by
   intro g hg hi
   obtain ⟨q,hq⟩:=List.mem_iff_getElem?.1 hg
   exact hno ⟨q,g,hq,hi⟩
 have hoi: o≠i:=by
   intro e
   obtain ⟨x,y,hxy⟩:=hnc false
   apply hxy
   rw [← L.hev,← L.hev,e,b69 gs _ i i.isLt,b69 gs _ i i.isLt]
   simp
 obtain ⟨x,hx⟩:=hd
 apply hx
 rw [← L.hev,← L.hev]
 refine b190 i gs _ _ hno' (by simp) ?_ o hoi
 intro j hj
 by_cases hjm: j < m
 · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
      =Function.update x i (!x i) ⟨j,hjm⟩ from v80 m _ false ⟨j,hjm⟩,
     show (List.ofFn x).getD j false=x ⟨j,hjm⟩ from v80 m x false ⟨j,hjm⟩]
   exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
 · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
end LocalSection1
end z2.Readers
namespace z2.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity z2
open z2.Readers
lemma z69 {m: ℕ} {f: (Fin m->Bool)->Bool} {gs: List Gate} {o: ℕ}
   (L: p1 m f gs o) (hnc: ∃ x y: Fin m->Bool,f x≠f y) {p: ℕ} {g: Gate}
   (hg: gs[p]?=some g) (hop: g.op=GateOp.and \/ g.op=GateOp.or) {a b: ℕ}
   (hin: g.inputs=[a,b]): a≠b:=by
 rintro rfl
 have hcl:=L.hcl p g hg
 have hlt: a < m+p:=by
   rcases hcl with ⟨h1,j,_,h2⟩ | ⟨h1,j,k,hj,hk,h2⟩
   · rw [hin] at h2; simp at h2
   · rw [hin] at h2; simp at h2; omega
 have hp: p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 refine L.no_alias hnc p hp a hlt (fun u => ?_)
 rw [x52 gs L.hcl u p g hg,hin]
 rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
end z2.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open z2 z2.Readers
open z2.RunAsm
lemma b164 {n out: Nat} {f: (Fin n->Bool)->Bool} {gs: List Gate}
   (least: p1 n f gs out) (nonconstant: ∃ x y,f x≠f y)
   (dependent: ∀ v: Fin n,Dep f v)
   (stillNonconstant: ∀ (v: Fin n) (b: Bool),∃ x y,
     f (Function.update x v b)≠f (Function.update y v b))
   (w: Nat) (amongWires: w < n+gs.length) (notOutput: w≠out) :
   ∃ p,c3 gs p w:=by
 by_cases isInput: w < n
 · let v: Fin n:=⟨w,isInput⟩
   exact least.dep_read v (dependent v) (stillNonconstant v)
 · let p:=w - n
   have wire: w=n+p:=by dsimp [p]; omega
   have pLt: p < gs.length:=by omega
   have notOut: out≠n+p:=by omega
   obtain ⟨q,_,read⟩:=least.live nonconstant p pLt notOut
   exact ⟨q,wire.symm ▸ read⟩
lemma least_gate_inputs_nodup {n out: Nat} {f: (Fin n->Bool)->Bool} {gs: List Gate}
   (least: p1 n f gs out) (nonconstant: ∃ x y,f x≠f y) (g: Gate) (present: g ∈ gs) :
   g.inputs.Nodup:=by
 obtain ⟨slot,atSlot⟩:=List.mem_iff_getElem?.mp present
 rcases least.hcl slot g atSlot with ⟨_,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
 · simp [args]
 · have distinct:=z69 least nonconstant atSlot ops args
   simp [args,distinct]
lemma b79 {n out: Nat} {gs: List Gate}
   {f: (Fin n->Bool)->Bool} (least: p1 n f gs out) (nonnull: ∃ x y,f x≠f y)
   (dependent: ∀ v: Fin n,Dep f v)
   (stillNonconstant: ∀ (v: Fin n) (b: Bool),∃ x y,
     f (Function.update x v b)≠f (Function.update y v b))
   (w: Fin (n+gs.length)) (notOutput: w.val≠out) :
   ∃ (p: Nat) (g: Gate),gs[p]?=some g /\ w.val ∈ g.inputs /\ n+p < n+gs.length:=by
 obtain ⟨p,g,hit,reads⟩:=b164 least nonnull dependent stillNonconstant w.val w.isLt notOutput
 have bound:=(List.getElem?_eq_some_iff.mp hit).1
 exact ⟨p,g,hit,reads,by omega⟩
namespace w4
open PEqualNP.CircuitLowerBounds
open z2 z2.Readers
def b10 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (b: Fin (n+gs.length)): List (Fin (n+gs.length)) :=
 if gate: n ≤ b.val then
   let slot:=b.val - n
   have hs: slot < gs.length:=by have:=b.isLt; omega
   let g:=gs[slot]'hs
   g.inputs.attach.map fun a => ⟨a.val,by
     have atSlot: gs[slot]?=some g:=List.getElem?_eq_getElem hs
     have before:=(clean slot g atSlot).lt a.val a.property
     omega⟩
 else []
lemma b45 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (b: Fin (n+gs.length)) (internal: n ≤ b.val) :
   (b10 clean b).map Fin.val =
     (gs[b.val - n]'(by have:=b.isLt; omega)).inputs:=by
 simp [b10,internal,List.map_map,Function.comp_def]
lemma b111 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (b: Fin (n+gs.length)) (primary: b.val < n): b10 clean b=[]:=by
 simp [b10,show ¬ n ≤ b.val by omega]
lemma b116 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (b: Fin (n+gs.length)) {p: Nat} {g: Gate} (atSlot: gs[p]?=some g) (bWire: b.val=n+p) :
   (b10 clean b).map Fin.val=g.inputs:=by
 have isGate: n ≤ b.val:=by omega
 have which: b.val - n=p:=by omega
 have located:=(List.getElem?_eq_some_iff.mp atSlot).2
 simpa [which,located] using b45 clean b isGate
lemma b158 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (a b: Fin (n+gs.length)): a ∈ b10 clean b↔b5 gs a b:=by
 by_cases internal: n ≤ b.val
 · let slot:=b.val - n
   have hs: slot < gs.length:=by have:=b.isLt; dsimp [slot]; omega
   let g:=gs[slot]'hs
   have wire: b.val=n+slot:=by dsimp [slot]; omega
   have atSlot: gs[slot]?=some g:=List.getElem?_eq_getElem hs
   have valList: (b10 clean b).map Fin.val=g.inputs :=
     b45 clean b internal
   constructor
   · intro mem
     refine ⟨slot,g,atSlot,wire,?_⟩
     rw [← valList]
     exact List.mem_map.mpr ⟨a,mem,rfl⟩
   · rintro ⟨q,h,atQ,wireQ,inside⟩
     have same: q=slot:=by omega
     subst q
     have gateSame: h=g:=Option.some.inj (atQ.symm.trans atSlot)
     subst h
     rw [← valList] at inside
     obtain ⟨a',mem,equal⟩:=List.mem_map.mp inside
     exact (Fin.ext equal: a'=a) ▸ mem
 · have empty: b10 clean b=[]:=by simp [b10,internal]
   rw [empty]
   constructor
   · simp
   · rintro ⟨slot,g,_,wire,_⟩
     omega
lemma b137 {n out: Nat} {gs: List Gate} {f: (Fin n->Bool)->Bool}
   (least: p1 n f gs out) (nonnull: ∃ x y,f x≠f y) (b: Fin (n+gs.length)) :
   (b10 least.hcl b).Nodup:=by
 by_cases internal: n ≤ b.val
 · apply List.Nodup.of_map Fin.val
   rw [b45 least.hcl b internal]
   exact PEqualNP.Outside.L_meta_3174.Binary.least_gate_inputs_nodup least nonnull _
     (List.getElem_mem (by have:=b.isLt; omega))
 · simp [b10,internal]
end w4
namespace j1
open PEqualNP.MetaComplexity
def b0 {n: ℕ} (i: Fin n): DMFormula n->ℕ
 | .lit k _ => if k=i then 1 else 0
 | .and p q => b0 i p+b0 i q
 | .or p q => b0 i p+b0 i q
def b21 {n: ℕ} (i j: Fin n) (p: DMFormula n): Prop :=
 0 < b0 i p \/ 0 < b0 j p
def b11 {n: ℕ} (i j: Fin n) (base: Fin n->Bool) (a b: Bool) (k: Fin n): Bool :=
 if k=i then a else if k=j then b else base k
def b4 {n: ℕ} (i j: Fin n) (base: Fin n->Bool) (p: DMFormula n) :
   Bool->Bool->Bool :=
 fun a b => p.eval (b11 i j base a b)
def wc (conj: Bool) (a b: Bool): Bool :=
 if conj then a&&b else a||b
noncomputable def w9 {n: ℕ} (conj: Bool) (i j: Fin n) (p q: DMFormula n)
   (P Q: Bool->Bool->Bool): Bool->Bool->Bool:=by
 classical
 exact if b21 i j p then
   if b21 i j q then fun a b => wc conj (P a b) (Q a b) else P
   else Q
noncomputable def v3 {n: ℕ} (i j: Fin n): DMFormula n->Bool->Bool->Bool
 | .lit k sign => fun a b =>
   let bit:=if k=i then a else if k=j then b else false
   if sign then bit else !bit
 | .and p q => w9 true i j p q (v3 i j p) (v3 i j q)
 | .or p q => w9 false i j p q (v3 i j p) (v3 i j q)
private lemma b176 {n: ℕ} (p: DMFormula n) {x y: Fin n->Bool}
   (h: ∀ k,0 < b0 k p->x k=y k): p.eval x=p.eval y:=by
 induction p with
 | lit k s =>
   have e:=h k (by simp [b0])
   simp [DMFormula.eval,e]
 | and p q ihp ihq =>
   simp only [DMFormula.eval]
   rw [ihp (fun k hk => h k (by simp only [b0]; omega)),
     ihq (fun k hk => h k (by simp only [b0]; omega))]
 | or p q ihp ihq =>
   simp only [DMFormula.eval]
   rw [ihp (fun k hk => h k (by simp only [b0]; omega)),
     ihq (fun k hk => h k (by simp only [b0]; omega))]
private lemma v26 {n: ℕ} {i j: Fin n} {base: Fin n->Bool} {p: DMFormula n}
   (h: b0 i p=0) (a a' b: Bool) :
   b4 i j base p a b=b4 i j base p a' b:=by
 apply b176
 intro k hk
 have ne: k≠i:=by rintro rfl; omega
 simp [b11,ne]
private lemma v83 {n: ℕ} {i j: Fin n} {base: Fin n->Bool} {p: DMFormula n}
   (h: b0 j p=0) (a b b': Bool) :
   b4 i j base p a b=b4 i j base p a b':=by
 apply b176
 intro k hk
 have ne: k≠j:=by rintro rfl; omega
 simp [b11,ne]
def b39 (f: Bool->Bool->Bool): Prop :=
 ∃ b,f false b≠f true b
private lemma b154 {op: Bool->Bool->Bool} {P Q: Bool->Bool->Bool}
   (h: b39 fun a b => op (P a b) (Q a b))
   (hQ: ∀ b,Q false b=Q true b): b39 P:=by
 obtain ⟨b,hb⟩:=h
 exact ⟨b,fun hp => hb (by
   change op (P false b) (Q false b)=op (P true b) (Q true b)
   rw [hp,hQ])⟩
private lemma b144 {op: Bool->Bool->Bool} {P Q: Bool->Bool->Bool}
   (h: b39 fun a b => op (P a b) (Q a b))
   (hP: ∀ b,P false b=P true b): b39 Q:=by
 obtain ⟨b,hb⟩:=h
 exact ⟨b,fun hq => hb (by
   change op (P false b) (Q false b)=op (P true b) (Q true b)
   rw [hq,hP])⟩
private lemma b73 {n: ℕ} {i j: Fin n} {base: Fin n->Bool} {p: DMFormula n}
   (h: ¬ b21 i j p) (a b: Bool) :
   b4 i j base p a b=b4 i j base p false false:=by
 have hi: b0 i p=0:=by
   by_contra e
   exact h (Or.inl (by omega))
 have hj: b0 j p=0:=by
   by_contra e
   exact h (Or.inr (by omega))
 exact (v26 hi a false b).trans (v83 hj false b false)
private lemma b138 (conj c: Bool) (P: Bool->Bool->Bool)
   (h: ∃ a b a' b',wc conj (P a b) c≠wc conj (P a' b') c) :
   ∀ a b,wc conj (P a b) c=P a b:=by
 cases conj <;> cases c <;> simp [wc] at h ⊢
private lemma z61 (conj a b: Bool): wc conj a b=wc conj b a:=by
 cases conj <;> cases a <;> cases b <;> rfl
private lemma b132 {n: ℕ} (i j: Fin n) (base: Fin n->Bool)
   (conj: Bool) (p q: DMFormula n)
   (hi: b0 i p+b0 i q ≤ 1)
   (hj: b0 j p+b0 j q ≤ 1)
   (present: b21 i j p \/ b21 i j q)
   (dep_i: 0 < b0 i p+b0 i q ->
     b39 fun a b => wc conj (b4 i j base p a b) (b4 i j base q a b))
   (dep_j: 0 < b0 j p+b0 j q ->
     b39 fun b a => wc conj (b4 i j base p a b) (b4 i j base q a b))
   (ihp: b0 i p ≤ 1->b0 j p ≤ 1->b21 i j p ->
     (0 < b0 i p->b39 (b4 i j base p)) ->
     (0 < b0 j p->b39 fun b a => b4 i j base p a b) ->
     ∀ a b,b4 i j base p a b=v3 i j p a b)
   (ihq: b0 i q ≤ 1->b0 j q ≤ 1->b21 i j q ->
     (0 < b0 i q->b39 (b4 i j base q)) ->
     (0 < b0 j q->b39 fun b a => b4 i j base q a b) ->
     ∀ a b,b4 i j base q a b=v3 i j q a b)
   (a b: Bool) :
   wc conj (b4 i j base p a b) (b4 i j base q a b) =
     w9 conj i j p q (v3 i j p) (v3 i j q) a b:=by
 classical
 have pl: b21 i j p->∀ a b,b4 i j base p a b=v3 i j p a b:=by
   intro hp
   apply ihp (by omega) (by omega) hp
   · intro h
     exact b154 (dep_i (by omega)) (fun b => v26 (by omega) false true b)
   · intro h
     exact b154 (dep_j (by omega)) (fun a => v83 (by omega) a false true)
 have ql: b21 i j q->∀ a b,b4 i j base q a b=v3 i j q a b:=by
   intro hq
   apply ihq (by omega) (by omega) hq
   · intro h
     exact b144 (dep_i (by omega)) (fun b => v26 (by omega) false true b)
   · intro h
     exact b144 (dep_j (by omega)) (fun a => v83 (by omega) a false true)
 have nonconst: ∃ a b a' b',
     wc conj (b4 i j base p a b) (b4 i j base q a b) ≠
       wc conj (b4 i j base p a' b') (b4 i j base q a' b'):=by
   unfold b21 at present
   rcases present with (h | h) | (h | h)
   · obtain ⟨b,h⟩:=dep_i (by omega)
     exact ⟨false,b,true,b,h⟩
   · obtain ⟨a,h⟩:=dep_j (by omega)
     exact ⟨a,false,a,true,h⟩
   · obtain ⟨b,h⟩:=dep_i (by omega)
     exact ⟨false,b,true,b,h⟩
   · obtain ⟨a,h⟩:=dep_j (by omega)
     exact ⟨a,false,a,true,h⟩
 by_cases hp: b21 i j p
 · by_cases hq: b21 i j q
   · simp [w9,hp,hq,pl hp,ql hq]
   · rw [b73 hq a b]
     have hn:=nonconst
     simp_rw [b73 hq] at hn
     rw [b138 conj _ _ hn a b,pl hp]
     simp [w9,hp,hq]
 · have hq:=present.resolve_left hp
   rw [b73 hp a b,z61]
   have hn:=nonconst
   simp_rw [b73 hp,z61 conj (b4 i j base p false false)] at hn
   rw [b138 conj _ _ hn a b,ql hq]
   simp [w9,hp]
private lemma b161 {n: ℕ} (i j: Fin n) (base: Fin n->Bool) (p: DMFormula n)
   (hi: b0 i p ≤ 1) (hj: b0 j p ≤ 1) (present: b21 i j p)
   (dep_i: 0 < b0 i p->b39 (b4 i j base p))
   (dep_j: 0 < b0 j p->b39 fun b a => b4 i j base p a b) :
   ∀ a b,b4 i j base p a b=v3 i j p a b:=by
 induction p with
 | lit k s =>
   intro a b
   by_cases hki: k=i
   · simp [b4,v3,DMFormula.eval,b11,hki]
   · have hkj: k=j:=by
       by_contra h
       simp [b21,b0,hki,h] at present
     simp [b4,v3,DMFormula.eval,b11,hkj]
 | and p q ihp ihq =>
   have present': b21 i j p \/ b21 i j q:=by
     unfold b21 at *
     simp only [b0] at present
     omega
   exact b132 i j base true p q hi hj present' dep_i dep_j ihp ihq
 | or p q ihp ihq =>
   have present': b21 i j p \/ b21 i j q:=by
     unfold b21 at *
     simp only [b0] at present
     omega
   exact b132 i j base false p q hi hj present' dep_i dep_j ihp ihq
lemma b129 {n: ℕ} (i j: Fin n) (p: DMFormula n)
   (hi: b0 i p ≤ 1) (hj: b0 j p ≤ 1)
   (baseA baseO: Fin n->Bool) (outerA outerO: Bool->Bool)
   (hA: ∀ a b,outerA (b4 i j baseA p a b)=(a&&b))
   (hO: ∀ a b,outerO (b4 i j baseO p a b)=(a||b)): False:=by
 have depAi: b39 (b4 i j baseA p):=by
   refine ⟨true,fun h => ?_⟩
   have e:=congrArg outerA h
   rw [hA,hA] at e
   cases e
 have depAj: b39 fun b a => b4 i j baseA p a b:=by
   refine ⟨true,fun h => ?_⟩
   have e:=congrArg outerA h
   rw [hA,hA] at e
   cases e
 have depOi: b39 (b4 i j baseO p):=by
   refine ⟨false,fun h => ?_⟩
   have e:=congrArg outerO h
   rw [hO,hO] at e
   cases e
 have depOj: b39 fun b a => b4 i j baseO p a b:=by
   refine ⟨false,fun h => ?_⟩
   have e:=congrArg outerO h
   rw [hO,hO] at e
   cases e
 have present: b21 i j p:=by
   left
   by_contra! h
   obtain ⟨b,hb⟩:=depAi
   exact hb (v26 (by omega) false true b)
 have stableA:=b161 i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
 have stableO:=b161 i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
 simp_rw [stableA] at hA
 simp_rw [stableO] at hO
 have ne: v3 i j p false false≠v3 i j p false true:=by
   intro e
   have f:=congrArg outerO e
   rw [hO,hO] at f
   cases f
 have zeros:=hA false false
 have other:=hA false true
 have one:=hA true true
 cases hk: v3 i j p false false <;>
   cases hl: v3 i j p false true <;>
   cases hm: v3 i j p true true <;>
   simp_all
noncomputable def edgeValue {n: ℕ} (G: SimpleGraph (Fin n)) (x: Fin n->Bool): Bool:=by
 classical
 exact decide (∃ u v,G.Adj u v /\ x u=true /\ x v=true)
private lemma b57 {n: ℕ} {G: SimpleGraph (Fin n)} {x: Fin n->Bool}
   {u v: Fin n} (h: G.Adj u v) (hu: x u=true) (hv: x v=true) :
   edgeValue G x=true:=by
 classical
 unfold edgeValue
 exact decide_eq_true ⟨u,v,h,hu,hv⟩
private lemma b22 {n: ℕ} {G: SimpleGraph (Fin n)} {x: Fin n->Bool}
   {u v: Fin n} (h: ¬ G.Adj u v) (active: ∀ w,x w=true->w=u \/ w=v) :
   edgeValue G x=false:=by
 classical
 unfold edgeValue
 apply decide_eq_false
 rintro ⟨s,t,es,hs,ht⟩
 rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
 · exact G.irrefl es
 · exact h es
 · exact h es.symm
 · exact G.irrefl es
private lemma b179 {n: ℕ} {G: SimpleGraph (Fin n)} {i j: Fin n}
   (h: G.Adj i j) (a b: Bool) :
   edgeValue G (b11 i j (fun _ => false) a b)=(a&&b):=by
 cases a <;> cases b
 · apply b22 (u:=i) (v:=i) G.irrefl
   intro k hk
   simp [b11] at hk
 · apply b22 (u:=j) (v:=j) G.irrefl
   intro k hk
   by_cases hki: k=i <;> by_cases hkj: k=j <;>
     simp [b11,hki,hkj] at hk ⊢
 · apply b22 (u:=i) (v:=i) G.irrefl
   intro k hk
   by_cases hki: k=i <;> by_cases hkj: k=j <;>
     simp [b11,hki,hkj] at hk ⊢
   assumption
 · exact b57 h (by simp [b11]) (by simp [b11,h.ne.symm])
private lemma b186 {n: ℕ} {G: SimpleGraph (Fin n)} {i j u v: Fin n}
   (hij: i≠j) (hiu: G.Adj i u) (hjv: G.Adj j v)
   (huj: u≠j) (hvi: v≠i) (huv: ¬ G.Adj u v) (a b: Bool) :
   edgeValue G (b11 i j (fun k => decide (k=u \/ k=v)) a b)=(a||b):=by
 have hu: b11 i j (fun k => decide (k=u \/ k=v)) a b u=true:=by
   simp [b11,hiu.ne.symm,huj]
 have hv: b11 i j (fun k => decide (k=u \/ k=v)) a b v=true:=by
   simp [b11,hvi,hjv.ne.symm]
 cases a <;> cases b
 · apply b22 huv
   intro k hk
   by_cases hki: k=i <;> by_cases hkj: k=j <;>
     simp [b11,hki,hkj] at hk
   exact hk
 · exact b57 hjv (by simp [b11,hij.symm]) hv
 · exact b57 hiu (by simp [b11]) hu
 · exact b57 hiu (by simp [b11]) hu
lemma b113 {n: ℕ} (G: SimpleGraph (Fin n)) (i j u v: Fin n)
   (hij: G.Adj i j) (hiu: G.Adj i u) (hjv: G.Adj j v)
   (huj: u≠j) (hvi: v≠i) (huv: ¬ G.Adj u v)
   (p: DMFormula n) (hi: b0 i p ≤ 1) (hj: b0 j p ≤ 1)
   (factors: ∀ base: Fin n->Bool,∃ outer: Bool->Bool,∀ a b,
     outer (b4 i j base p a b)=edgeValue G (b11 i j base a b)): False:=by
 obtain ⟨outerA,ha⟩:=factors (fun _ => false)
 obtain ⟨outerO,ho⟩:=factors (fun k => decide (k=u \/ k=v))
 exact b129 i j p hi hj _ _ outerA outerO
   (fun a b => (ha a b).trans (b179 hij a b))
   (fun a b => (ho a b).trans (b186 hij.ne hiu hjv huj hvi huv a b))
end j1
namespace f6
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open z2
open j1
def b18 {n: Nat}: DMFormula n->DMFormula n
 | .lit i sign => .lit i (!sign)
 | .and a b => .or (b18 a) (b18 b)
 | .or a b => .and (b18 a) (b18 b)
lemma b163 {n: Nat} (p: DMFormula n) (x: Fin n->Bool) :
   (b18 p).eval x=!(p.eval x):=by
 induction p with
 | lit i s =>
   cases s <;> cases e: x i <;> simp [b18,DMFormula.eval,e]
 | and a b iha ihb =>
   simp only [b18,DMFormula.eval,iha,ihb]
   cases a.eval x <;> cases b.eval x <;> rfl
 | or a b iha ihb =>
   simp only [b18,DMFormula.eval,iha,ihb]
   cases a.eval x <;> cases b.eval x <;> rfl
lemma b112 {n: Nat} (i: Fin n) (p: DMFormula n) :
   b0 i (b18 p)=b0 i p:=by
 induction p with
 | lit i s => rfl
 | and a b iha ihb => simp [b18,b0,iha,ihb]
 | or a b iha ihb => simp [b18,b0,iha,ihb]
def b2 {n: Nat} (fallback: Fin n) (gs: List Gate) (w: Nat): DMFormula n :=
 if hw: w < n then
   .lit ⟨w,hw⟩ true
 else
   match gs[w - n]? with
   | none => .lit fallback true
   | some g =>
     match g.op,g.inputs with
     | .not,[a] =>
       if _ha: a < w then b18 (b2 fallback gs a) else .lit fallback true
     | .and,[a,b] =>
       if _ha: a < w then
         if _hb: b < w then .and (b2 fallback gs a) (b2 fallback gs b)
         else .lit fallback true
       else .lit fallback true
     | .or,[a,b] =>
       if _ha: a < w then
         if _hb: b < w then .or (b2 fallback gs a) (b2 fallback gs b)
         else .lit fallback true
       else .lit fallback true
     | _,_ => .lit fallback true
termination_by w
decreasing_by all_goals assumption
lemma b94 {n: Nat} (fallback: Fin n) (gs: List Gate) (i: Fin n) :
   b2 fallback gs i.val=.lit i true:=by
 rw [b2]
 simp [i.isLt]
private lemma b114 {n: Nat} (fallback: Fin n) {gs: List Gate}
   {p a: Nat} {g: Gate} (hg: gs[p]?=some g) (op: g.op=.not)
   (inputs: g.inputs=[a]) (ha: a < n+p) :
   b2 fallback gs (n+p)=b18 (b2 fallback gs a):=by
 have hn: ¬ n+p < n:=by omega
 have hp: n+p - n=p:=by omega
 conv_lhs => rw [b2]
 simp [hn,hp,hg,op,inputs,ha]
private lemma b115 {n: Nat} (fallback: Fin n) {gs: List Gate}
   {p a b: Nat} {g: Gate} (hg: gs[p]?=some g) (op: g.op=.and)
   (inputs: g.inputs=[a,b]) (ha: a < n+p) (hb: b < n+p) :
   b2 fallback gs (n+p)=.and (b2 fallback gs a) (b2 fallback gs b):=by
 have hn: ¬ n+p < n:=by omega
 have hp: n+p - n=p:=by omega
 conv_lhs => rw [b2]
 simp [hn,hp,hg,op,inputs,ha,hb]
private lemma b131 {n: Nat} (fallback: Fin n) {gs: List Gate}
   {p a b: Nat} {g: Gate} (hg: gs[p]?=some g) (op: g.op=.or)
   (inputs: g.inputs=[a,b]) (ha: a < n+p) (hb: b < n+p) :
   b2 fallback gs (n+p)=.or (b2 fallback gs a) (b2 fallback gs b):=by
 have hn: ¬ n+p < n:=by omega
 have hp: n+p - n=p:=by omega
 conv_lhs => rw [b2]
 simp [hn,hp,hg,op,inputs,ha,hb]
lemma b155 {n: Nat} (fallback: Fin n) {gs: List Gate} (hcl: v0 n gs)
   (x: Fin n->Bool) (w: Nat) (hw: w < n+gs.length) :
   (b2 fallback gs w).eval x=vl gs x w:=by
 induction w using Nat.strong_induction_on with
 | ind w ih =>
   by_cases hi: w < n
   · rw [b94 fallback gs ⟨w,hi⟩,b69 gs x w hi]
     rfl
   · obtain ⟨p,rfl⟩: ∃ p,w=n+p:=⟨w - n,by omega⟩
     have hp: p < gs.length:=by omega
     let g:=gs[p]
     have hg: gs[p]?=some g:=List.getElem?_eq_getElem hp
     rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
     · rw [b114 fallback hg op inputs ha,b163,ih a ha (by omega),
         x52 gs hcl x p g hg]
       simp [op,inputs,GateOp.eval]
     · rw [b115 fallback hg op inputs ha hb]
       simp only [DMFormula.eval]
       rw [ih a ha (by omega),ih b hb (by omega),x52 gs hcl x p g hg]
       simp [op,inputs,GateOp.eval]
     · rw [b131 fallback hg op inputs ha hb]
       simp only [DMFormula.eval]
       rw [ih a ha (by omega),ih b hb (by omega),x52 gs hcl x p g hg]
       simp [op,inputs,GateOp.eval]
lemma b103 {n: Nat} (fallback: Fin n) (gs: List Gate) (chosen i: Fin n) :
   b0 chosen (b2 fallback gs i.val)=if i=chosen then 1 else 0:=by
 rw [b94]
 rfl
lemma b109 {n: Nat} (fallback: Fin n) {gs: List Gate} (hcl: v0 n gs)
   (chosen: Fin n) {p: Nat} {g: Gate} (hg: gs[p]?=some g) :
   b0 chosen (b2 fallback gs (n+p)) =
     (g.inputs.map fun a => b0 chosen (b2 fallback gs a)).sum:=by
 rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
 · simp [b114 fallback hg op inputs ha,inputs,b112]
 · simp [b115 fallback hg op inputs ha hb,inputs,b0]
 · simp [b131 fallback hg op inputs ha hb,inputs,b0]
lemma b84 {n: Nat} (fallback chosen: Fin n) {gs: List Gate}
   (hcl: v0 n gs) {p: Nat} {g: Gate} (hg: gs[p]?=some g)
   {b: Fin (n+gs.length)} (hb: b.val=n+p)
   (parents: List (Fin (n+gs.length))) (parentsVal: parents.map Fin.val=g.inputs) :
   b0 chosen (b2 fallback gs b.val) =
     (parents.map fun a => b0 chosen (b2 fallback gs a.val)).sum:=by
 rw [hb,b109 fallback hcl chosen hg,← parentsVal,List.map_map]
 rfl
end f6
namespace f7
open PEqualNP.CircuitLowerBounds
open z2
open f6 w4 j1
lemma b30 {n: Nat} {gs: List Gate} (fallback chosen: Fin n)
   (a: Fin (n+gs.length)) (ha: a.val < n) :
   b0 chosen (b2 fallback gs a.val) =
     if a=b8 gs chosen then 1 else 0:=by
 let i: Fin n:=⟨a.val,ha⟩
 have e: i=chosen↔a=b8 gs chosen:=by
   constructor
   · intro h
     exact Fin.ext (congrArg (fun k: Fin n => k.val) h)
   · intro h
     exact Fin.ext (congrArg (fun k: Fin (n+gs.length) => k.val) h)
 change b0 chosen (b2 fallback gs i.val)=_
 simp only [b103,e]
lemma b196 {n: Nat} {gs: List Gate} (hcl: v0 n gs)
   (cut out: Fin (n+gs.length)) (group: Fin n->Prop) (base: Fin n->Bool)
   (controlled: cut=out \/ ∀ i: Fin n,group i ->
     ¬ Relation.ReflTransGen (kc (b5 gs) cut) (b8 gs i) out) :
   ∃ outer: Bool->Bool,∀ x: Fin n->Bool,(∀ i,¬ group i->x i=base i) ->
     outer (vl gs x cut.val)=vl gs x out.val:=by
 rcases controlled with rfl | blocked
 · exact ⟨id,fun _ _ => rfl⟩
 · exact b135 hcl cut out group base blocked
lemma b124 {n: Nat} {gs: List Gate} (hcl: v0 n gs)
   (G: SimpleGraph (Fin n)) (cut out: Fin (n+gs.length))
   (computes: ∀ x,vl gs x out.val=edgeValue G x)
   (i j u v: Fin n) (hij: G.Adj i j) (hiu: G.Adj i u) (hjv: G.Adj j v)
   (huj: u≠j) (hvi: v≠i) (huv: ¬ G.Adj u v)
   (hi: b0 i (b2 i gs cut.val) ≤ 1)
   (hj: b0 j (b2 i gs cut.val) ≤ 1)
   (controlled: cut=out \/ ∀ k: Fin n,(k=i \/ k=j) ->
     ¬ Relation.ReflTransGen (kc (b5 gs) cut) (b8 gs k) out): False:=by
 refine b113 G i j u v hij hiu hjv huj hvi huv
   (b2 i gs cut.val) hi hj (fun base => ?_)
 obtain ⟨f,hf⟩:=b196 hcl cut out (fun k => k=i \/ k=j) base controlled
 refine ⟨f,fun a b => ?_⟩
 have agree: ∀ k,¬ (k=i \/ k=j)->b11 i j base a b k=base k:=by
   intro k hk
   simp [b11,show k≠i from fun e => hk (Or.inl e),
     show k≠j from fun e => hk (Or.inr e)]
 unfold b4
 rw [b155 i hcl _ cut.val cut.isLt]
 exact (hf _ agree).trans (computes _)
end f7
namespace z8
open Relation
variable {m: Nat} (reads: Fin m->Fin m->Prop) (output: Fin m)
def Branches (v: Fin m): Prop:=∃ a b,reads v a /\ reads v b /\ a≠b
def Terminal (v: Fin m): Prop:=v=output \/ Branches reads v
def d6 (v w: Fin m): Prop:=reads v w /\ ¬ Terminal reads output v
lemma b72 {v a b: Fin m} (first: d6 reads output v a) (next: d6 reads output v b) :
   a=b:=by
 by_contra separate
 exact first.2 (Or.inr ⟨a,b,first.1,next.1,separate⟩)
variable (forward: ∀ {v w: Fin m},reads v w->v < w)
variable (live: ∀ v: Fin m,v≠output->∃ w,reads v w)
include forward live in
lemma b81 (v: Fin m) :
   ∃ root: Fin m,Terminal reads output root /\ ReflTransGen (d6 reads output) v root:=by
 let distance (w: Fin m):=m - w.val
 induction v using (measure distance).wf.induction with
 | h v ih =>
   by_cases terminal: Terminal reads output v
   · exact ⟨v,terminal,ReflTransGen.refl⟩
   obtain ⟨next,g5⟩:=live v (fun e => terminal (Or.inl e))
   have increase:=forward g5
   have closer: distance next < distance v:=by
     dsimp [distance]
     have bounds:=next.isLt
     change v.val < next.val at increase
     omega
   obtain ⟨root,stopped,route⟩:=ih next closer
   exact ⟨root,stopped,route.head ⟨g5,terminal⟩⟩
include forward in
lemma b121 {v a b: Fin m} (terminalA: Terminal reads output a)
   (terminalB: Terminal reads output b) (routeA: ReflTransGen (d6 reads output) v a)
   (routeB: ReflTransGen (d6 reads output) v b): a=b:=by
 let distance (w: Fin m):=m - w.val
 induction v using (measure distance).wf.induction generalizing a b with
 | h v ih =>
   rcases routeA.cases_head with h | ⟨next,g5,tailA⟩
   · subst a
     rcases routeB.cases_head with h | ⟨_,edgeB,_⟩
     · exact h
     · exact (edgeB.2 terminalA).elim
   · rcases routeB.cases_head with h | ⟨nextB,edgeB,tailB⟩
     · subst b
       exact (g5.2 terminalB).elim
     have equal:=b72 reads output g5 edgeB
     subst nextB
     have increase:=forward g5.1
     have closer: distance next < distance v:=by
       dsimp [distance]
       have bounds:=next.isLt
       change v.val < next.val at increase
       omega
     exact ih next closer terminalA terminalB tailA tailB
noncomputable def first (v: Fin m): Fin m :=
 Classical.choose (b81 reads output forward live v)
lemma first_stops (v: Fin m): Terminal reads output (first reads output forward live v) :=
 (Classical.choose_spec (b81 reads output forward live v)).1
lemma v24 (v: Fin m): ReflTransGen (d6 reads output) v (first reads output forward live v) :=
 (Classical.choose_spec (b81 reads output forward live v)).2
lemma b35 {v: Fin m} (stopped: Terminal reads output v) :
   first reads output forward live v=v :=
 b121 reads output forward (first_stops reads output forward live v) stopped
   (v24 reads output forward live v) ReflTransGen.refl
lemma b108 {v w: Fin m} (y28: d6 reads output v w) :
   first reads output forward live v=first reads output forward live w :=
 b121 reads output forward (first_stops reads output forward live v)
   (first_stops reads output forward live w) (v24 reads output forward live v)
   ((v24 reads output forward live w).head y28)
include forward in
lemma v84 {v w: Fin m} (route: ReflTransGen reads v w): v ≤ w:=by
 induction route with
 | refl => exact le_rfl
 | tail _ g5 ih => exact le_trans ih (le_of_lt (forward g5))
lemma b38 {v w: Fin m} (route: ReflTransGen (d6 reads output) v w) :
   ReflTransGen reads v w:=by
 induction route with
 | refl => exact ReflTransGen.refl
 | tail _ g5 ih => exact ih.tail g5.1
lemma b141 (v: Fin m): v ≤ first reads output forward live v :=
 v84 reads forward (b38 reads output (v24 reads output forward live v))
lemma b75 {v w: Fin m} (route: ReflTransGen reads v w)
   (before: w ≤ first reads output forward live v) :
   ReflTransGen (d6 reads output) v w /\ first reads output forward live w=first reads output forward live v:=by
 induction route with
 | refl => exact ⟨ReflTransGen.refl,rfl⟩
 | tail _ g5 ih =>
   have predecessorBefore:=lt_of_lt_of_le (forward g5) before
   obtain ⟨tracked,label⟩:=ih (le_of_lt predecessorBefore)
   have y28: d6 reads output _ _:=⟨g5,fun stopped => by
     have self:=b35 reads output forward live stopped
     rw [self] at label
     exact (ne_of_lt predecessorBefore) label⟩
   exact ⟨tracked.tail y28,(b108 reads output forward live y28).symm.trans label⟩
lemma ancestor_first_le {v w: Fin m} (route: ReflTransGen reads v w)
   (stopped: Terminal reads output w): first reads output forward live v ≤ w:=by
 by_contra tooLate
 have earlier:=lt_of_not_ge tooLate
 have same:=(b75 reads output forward live route (le_of_lt earlier)).2
 rw [b35 reads output forward live stopped] at same
 exact (ne_of_lt earlier) same
lemma b168 {v a b: Fin m} (route: ReflTransGen reads v a) (g5: reads a b)
   (bound: b ≤ first reads output forward live v): d6 reads output a b:=by
 have earlier:=lt_of_lt_of_le (forward g5) bound
 have same:=(b75 reads output forward live route (le_of_lt earlier)).2
 refine ⟨g5,fun stopped => ?_⟩
 rw [b35 reads output forward live stopped] at same
 exact (ne_of_lt earlier) same
def Avoid (cut v w: Fin m): Prop:=reads v w /\ v≠cut
lemma b123 (cut: Fin m) {v w: Fin m} (route: ReflTransGen (Avoid reads cut) v w) :
   ReflTransGen reads v w:=by
 induction route with
 | refl => exact ReflTransGen.refl
 | tail _ g5 ih => exact ih.tail g5.1
lemma b122 {v w: Fin m}
   (route: ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
   w ≤ first reads output forward live v:=by
 induction route with
 | refl => exact b141 reads output forward live v
 | tail prior g5 ih =>
   have label:=(b75 reads output forward live (b123 reads _ prior) ih).2
   have earlier:=lt_of_le_of_ne ih g5.2
   have following: d6 reads output _ _:=⟨g5.1,fun terminal => by
     rw [b35 reads output forward live terminal] at label
     exact (ne_of_lt earlier) label⟩
   have same:=(b108 reads output forward live following).symm.trans label
   rw [← same]
   exact b141 reads output forward live _
lemma no_avoiding_after {v w: Fin m} (after: first reads output forward live v < w) :
   ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
 fun route => (not_lt_of_ge (b122 reads output forward live route)) after
include forward in
lemma b90 {source a b goal: Fin m}
   (routeA: ReflTransGen (d6 reads output) source a) (edgeA: d6 reads output a goal)
   (routeB: ReflTransGen (d6 reads output) source b) (edgeB: d6 reads output b goal): a=b:=by
 let distance (w: Fin m):=m - w.val
 induction source using (measure distance).wf.induction generalizing a b with
 | h source ih =>
   rcases routeA.cases_head with aHere | ⟨nextA,stepA,laterA⟩
   · subst a
     rcases routeB.cases_head with bHere | ⟨next,stepB,later⟩
     · exact bHere
     have equal: next=goal:=b72 reads output stepB edgeA
     subst next
     have increasing:=v84 reads forward (b38 reads output later)
     exact (not_lt_of_ge increasing (forward edgeB.1)).elim
   · rcases routeB.cases_head with bHere | ⟨nextB,stepB,laterB⟩
     · subst b
       have equal: nextA=goal:=b72 reads output stepA edgeB
       subst nextA
       have increasing:=v84 reads forward (b38 reads output laterA)
       exact (not_lt_of_ge increasing (forward edgeA.1)).elim
     have equal:=b72 reads output stepA stepB
     subst nextB
     have increase:=forward stepA.1
     have closer: distance nextA < distance source:=by
       dsimp [distance]
       have bounds:=nextA.isLt
       change source.val < nextA.val at increase
       omega
     exact ih nextA closer laterA edgeA laterB edgeB
lemma b89 {source a b goal: Fin m}
   (bound: goal ≤ first reads output forward live source)
   (routeA: ReflTransGen reads source a) (edgeA: reads a goal)
   (routeB: ReflTransGen reads source b) (edgeB: reads b goal): a=b:=by
 have aBound:=le_trans (le_of_lt (forward edgeA)) bound
 have bBound:=le_trans (le_of_lt (forward edgeB)) bound
 exact b90 reads output forward
   (b75 reads output forward live routeA aBound).1
   (b168 reads output forward live routeA edgeA bound)
   (b75 reads output forward live routeB bBound).1
   (b168 reads output forward live routeB edgeB bound)
lemma b54 {α: Type*} (weight: α->Nat) (xs: List α)
   (positive: 0 < (xs.map weight).sum): ∃ a ∈ xs,0 < weight a:=by
 induction xs with
 | nil => simp at positive
 | cons a rest ih =>
   by_cases h: 0 < weight a
   · exact ⟨a,by simp,h⟩
   have hr: 0 < (rest.map weight).sum:=by
     simp only [List.map_cons,List.sum_cons] at positive
     omega
   obtain ⟨b,hb,hbPos⟩:=ih hr
   exact ⟨b,by simp [hb],hbPos⟩
lemma b62 {α: Type*} (weight: α->Nat) (xs: List α)
   (distinct: xs.Nodup) (small: ∀ a ∈ xs,weight a ≤ 1)
   (unique: ∀ a ∈ xs,∀ b ∈ xs,0 < weight a->0 < weight b->a=b) :
   (xs.map weight).sum ≤ 1:=by
 induction xs with
 | nil => simp
 | cons a rest ih =>
   simp only [List.nodup_cons] at distinct
   simp only [List.map_cons,List.sum_cons]
   by_cases h: weight a=0
   · rw [h,Nat.zero_add]
     exact ih distinct.2 (fun b hb => small b (by simp [hb]))
       (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
   have restZero: (rest.map weight).sum=0:=by
     by_contra some
     obtain ⟨b,hb,hbPos⟩:=b54 weight rest (by omega)
     have equal:=unique a (by simp) b (by simp [hb]) (by omega) hbPos
     exact distinct.1 (by simpa [equal] using hb)
   rw [restZero,Nat.add_zero]
   exact small a (by simp)
section Count
variable (parents: Fin m->List (Fin m))
variable (reads_parent: ∀ a b: Fin m,reads a b↔a ∈ parents b)
variable (weight: Fin m->Nat) (source: Fin m)
variable (other_weight: ∀ v: Fin m,v≠source->weight v=((parents v).map weight).sum)
include forward reads_parent other_weight in
lemma b66 {v: Fin m} (positive: 0 < weight v): ReflTransGen reads source v:=by
 revert positive
 induction v using (measure (fun w: Fin m => w.val)).wf.induction with
 | h v ih =>
   intro positive
   by_cases isSource: v=source
   · subst v
     exact ReflTransGen.refl
   rw [other_weight v isSource] at positive
   obtain ⟨a,member,hp⟩:=b54 weight (parents v) positive
   have g5:=(reads_parent a v).mpr member
   have earlier:=forward g5
   exact (ih a earlier hp).tail g5
include reads_parent other_weight in
lemma weight_before_le_one (rootWeight: weight source=1) (distinct: ∀ v,(parents v).Nodup)
   {v: Fin m} (bound: v ≤ first reads output forward live source): weight v ≤ 1:=by
 revert bound
 induction v using (measure (fun w: Fin m => w.val)).wf.induction with
 | h v ih =>
   intro bound
   by_cases isSource: v=source
   · subst v
     exact le_of_eq rootWeight
   rw [other_weight v isSource]
   apply b62 weight (parents v) (distinct v)
   · intro a member
     have earlier:=forward ((reads_parent a v).mpr member)
     exact ih a earlier (le_trans (le_of_lt earlier) bound)
   · intro a ma b mb ha hb
     exact b89 reads output forward live bound
       (b66 reads forward parents reads_parent weight source other_weight ha)
       ((reads_parent a v).mpr ma)
       (b66 reads forward parents reads_parent weight source other_weight hb)
       ((reads_parent b v).mpr mb)
end Count
end z8
namespace p6
open PEqualNP.CircuitLowerBounds
open z2
open f6 f7 w4 j1
noncomputable def firstInputBoundary {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (out: Fin (n+gs.length))
   (live: ∀ w: Fin (n+gs.length),w≠out->∃ v,b5 gs w v)
   (i: Fin n): Fin (n+gs.length) :=
 z8.first (b5 gs) out (b15 clean) live (b8 gs i)
noncomputable def firstInputGroup {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (out: Fin (n+gs.length))
   (live: ∀ w: Fin (n+gs.length),w≠out->∃ v,b5 gs w v)
   (cut: Fin (n+gs.length)): Finset (Fin n) :=
 Finset.univ.filter fun i => firstInputBoundary clean out live i=cut
lemma b48 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (out: Fin (n+gs.length))
   (live: ∀ w: Fin (n+gs.length),w≠out->∃ v,b5 gs w v)
   (cut: Fin (n+gs.length)) (i: Fin n) :
   i ∈ firstInputGroup clean out live cut↔firstInputBoundary clean out live i=cut:=by
 simp [firstInputGroup]
lemma b130 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (out: Fin (n+gs.length))
   (live: ∀ w: Fin (n+gs.length),w≠out->∃ v,b5 gs w v)
   (w: Fin (n+gs.length)): w ≤ out:=by
 let last: Fin (n+gs.length):=⟨n+gs.length - 1,by have:=out.isLt; omega⟩
 have top (v: Fin (n+gs.length)): v ≤ last:=by
   change v.val ≤ n+gs.length - 1
   have:=v.isLt
   omega
 have lastOut: last=out:=by
   by_contra notOutput
   obtain ⟨v,e⟩:=live last notOutput
   exact (not_lt_of_ge (top v)) (b15 clean e)
 exact lastOut ▸ top w
lemma b17 {n: Nat} {gs: List Gate}
   (clean: v0 n gs) (out: Fin (n+gs.length))
   (live: ∀ w: Fin (n+gs.length),w≠out->∃ v,b5 gs w v)
   (distinct: ∀ w,(b10 clean w).Nodup)
   (fallback chosen: Fin n) :
   b0 chosen (b2 fallback gs (firstInputBoundary clean out live chosen).val)
     ≤ 1:=by
 let weight (a: Fin (n+gs.length)):=b0 chosen (b2 fallback gs a.val)
 have sourcePrimary: (b8 gs chosen).val < n:=chosen.isLt
 have atSource: weight (b8 gs chosen)=1:=by
   dsimp [weight]
   rw [b30 fallback chosen _ sourcePrimary,ite_eq_left rfl]
 have otherWeight: ∀ w: Fin (n+gs.length),w≠b8 gs chosen ->
     weight w=((b10 clean w).map weight).sum:=by
   intro w other
   by_cases primary: w.val < n
   · simp [weight,b30 fallback chosen w primary,other,
       b111 clean w primary]
   · let p:=w.val - n
     have hp: p < gs.length:=by have:=w.isLt; dsimp [p]; omega
     have hw: w.val=n+p:=by dsimp [p]; omega
     let g:=gs[p]
     have atSlot: gs[p]?=some g:=List.getElem?_eq_getElem hp
     exact b84 fallback chosen clean atSlot hw _
       (b116 clean w atSlot hw)
 exact z8.weight_before_le_one (b5 gs) out (b15 clean) live
   (b10 clean) (fun a b => (b158 clean a b).symm) weight
   (b8 gs chosen) otherWeight atSource distinct le_rfl
lemma b86 {n: Nat} {gs: List Gate}
   (clean: v0 n gs) (out: Fin (n+gs.length))
   (live: ∀ w: Fin (n+gs.length),w≠out->∃ v,b5 gs w v)
   (cut: Fin (n+gs.length)) :
   cut=out \/ ∀ k: Fin n,k ∈ firstInputGroup clean out live cut ->
     ¬ Relation.ReflTransGen (kc (b5 gs) cut) (b8 gs k) out:=by
 by_cases terminal: cut=out
 · exact Or.inl terminal
 right
 intro k member path
 have before: cut < out:=lt_of_le_of_ne (b130 clean out live cut) terminal
 have firstHere:=(b48 clean out live cut k).mp member
 have after: firstInputBoundary clean out live k < out:=by rwa [firstHere]
 have blocked:=z8.no_avoiding_after (b5 gs) out
   (b15 clean) live after
 apply blocked
 change Relation.ReflTransGen (z8.Avoid (b5 gs)
   (firstInputBoundary clean out live k)) (b8 gs k) out
 rw [firstHere]
 exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1,e.2.1⟩) _ _ path
lemma b80 {n: Nat} {gs: List Gate}
   (clean: v0 n gs) (out: Fin (n+gs.length))
   (live: ∀ w: Fin (n+gs.length),w≠out->∃ v,b5 gs w v)
   (distinct: ∀ w,(b10 clean w).Nodup)
   (G: SimpleGraph (Fin n)) (computes: ∀ x,vl gs x out.val=edgeValue G x)
   (witnesses: ∀ i j,G.Adj i j->∃ u v,
     G.Adj i u /\ G.Adj j v /\ u≠j /\ v≠i /\ ¬ G.Adj u v)
   (cut: Fin (n+gs.length)): y6.Independent G (firstInputGroup clean out live cut):=by
 intro i iIn j jIn adjacent
 obtain ⟨u,v,hiu,hjv,huj,hvi,huv⟩:=witnesses i j adjacent
 have iFirst:=(b48 clean out live cut i).mp iIn
 have jFirst:=(b48 clean out live cut j).mp jIn
 have iCount:=b17 clean out live distinct i i
 have jCount:=b17 clean out live distinct i j
 rw [iFirst] at iCount
 rw [jFirst] at jCount
 refine b124 clean G cut out computes i j u v adjacent hiu hjv huj hvi
   huv iCount jCount ?_
 rcases b86 clean out live cut with stopped | blocked
 · exact Or.inl stopped
 · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))
end p6
namespace v7
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev d5:=Fin 9
abbrev x54:=List (d5 × d5)
def edges: x54:=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def yk (es: x54) (x: d5->Bool): Bool :=
 es.any (fun g5 => x g5.1&&x g5.2)
lemma x87: ∀ e ∈ edges,e.1≠e.2:=by decide
lemma edgeFun_true (es: x54) (x: d5->Bool) :
   yk es x=true↔∃ a b,(a,b) ∈ es /\ x a=true /\ x b=true:=by
 simp only [yk,List.any_eq_true,Bool.and_eq_true,Prod.exists]
def d4 (es: x54) (noSelf: ∀ e ∈ es,e.1≠e.2): SimpleGraph d5 where
 Adj a b:=(a,b) ∈ es \/ (b,a) ∈ es
 symm:=⟨fun _ _ => Or.symm⟩
 loopless:=⟨fun v h => h.elim (fun he => noSelf (v,v) he rfl) (fun he => noSelf (v,v) he rfl)⟩
end v7
namespace q0
def b7:=Nat × (Nat->Nat)
def b7.width (g: b7):=g.1
def b7.adjacency (g: b7):=g.2
def bit (d1: Nat): Nat :=
 Nat.shiftLeft 1 d1
def b71 (g: b7): Nat :=
 bit g.width - 1
def b3 (g: b7) (deleted d1: Nat): Nat :=
 Nat.land (g.adjacency d1) (Nat.xor (b71 g) deleted)
def z5 (g: b7) (deleted: Nat): Nat :=
 (List.range g.width).foldl
   (fun mask v => if b3 g deleted v=0 then Nat.lor mask (bit v) else mask)
   deleted
def b74 (g: b7) (deleted d1: Nat): Nat :=
 (List.range g.width).foldl
   (fun mask v => if !(Nat.testBit deleted v) &&
       (b3 g deleted v==b3 g deleted d1)
     then Nat.lor mask (bit v) else mask)
   0
lemma v14 (v w: Nat): (bit v).testBit w=decide (v=w):=by
 simp [bit,Nat.shiftLeft_eq,Nat.testBit_two_pow]
lemma v79 (g: b7) (w: Nat) :
   (b71 g).testBit w=decide (w < g.width):=by
 simp [b71,bit,Nat.shiftLeft_eq]
lemma b191 (g: b7) (deleted v w: Nat) (hw: w < g.width) :
   (b3 g deleted v).testBit w =
     ((g.adjacency v).testBit w&&!(deleted.testBit w)):=by
 simp [b3,Nat.testBit_xor,v79,hw]
private lemma b152 (vertices: List Nat) (p: Nat->Prop) [DecidablePred p]
   (initial w: Nat) :
   (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
     (initial.testBit w||(vertices.any fun v => decide (p v)&&(v==w))):=by
 induction vertices generalizing initial with
 | nil => simp
 | cons v vertices ih =>
   simp only [List.foldl_cons,List.any_cons]
   rw [ih]
   by_cases h: p v <;> simp [h,v14,Bool.or_assoc,Bool.beq_eq_decide_eq]
private lemma b170 (p: Nat->Prop) [DecidablePred p] (n w: Nat) :
   ((List.range n).any fun v => decide (p v)&&(v==w)) =
     (decide (w < n)&&decide (p w)):=by
 rw [Bool.eq_iff_iff,List.any_eq_true,Bool.and_eq_true]
 simp only [List.mem_range,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
 constructor
 · rintro ⟨v,hv,hp,rfl⟩
   exact ⟨hv,hp⟩
 · rintro ⟨hw,hp⟩
   exact ⟨w,hw,hp,rfl⟩
lemma z58 (g: b7) (deleted w: Nat) :
   (z5 g deleted).testBit w =
     (deleted.testBit w||(decide (w < g.width)&&decide (b3 g deleted w=0))):=by
 unfold z5
 rw [b152,b170]
lemma z59 (g: b7) (deleted v w: Nat) :
   (b74 g deleted v).testBit w =
     (decide (w < g.width) &&
       (!(deleted.testBit w)&&(b3 g deleted w==b3 g deleted v))):=by
 unfold b74
 rw [b152,b170]
 simp [Bool.beq_eq_decide_eq]
lemma b52 (width: Nat): bit width=2 ^ width:=by
 simp [bit,Nat.shiftLeft_eq]
lemma b192 {width a b: Nat} (ha: a < bit width) (hb: b < bit width) :
   Nat.lor a b < bit width:=by
 rw [b52] at ha hb ⊢
 exact Nat.or_lt_two_pow ha hb
lemma v25 {width m w: Nat} (hm: m < bit width) (hw: width ≤ w) :
   m.testBit w=false:=by
 rw [b52] at hm
 exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))
lemma x25 {width a b: Nat} (ha: a < bit width) (hb: b < bit width)
   (same: ∀ w < width,a.testBit w=b.testBit w): a=b:=by
 apply Nat.eq_of_testBit_eq
 intro w
 by_cases hw: w < width
 · exact same w hw
 · rw [v25 ha (Nat.le_of_not_gt hw),v25 hb (Nat.le_of_not_gt hw)]
lemma b64 (g: b7) (deleted v: Nat) (hd: deleted < bit g.width) :
   b3 g deleted v < bit g.width:=by
 rw [b52]
 apply Nat.lt_pow_two_of_testBit
 intro w hw
 simp [b3,v79,Nat.not_lt_of_ge hw,v25 hd hw]
lemma b142 (g: b7) (deleted: Nat) (hd: deleted < bit g.width) :
   z5 g deleted < bit g.width:=by
 rw [b52]
 apply Nat.lt_pow_two_of_testBit
 intro w hw
 simp [z58,Nat.not_lt_of_ge hw,v25 hd hw]
lemma b181 (g: b7) (deleted v: Nat) :
   b74 g deleted v < bit g.width:=by
 rw [b52]
 apply Nat.lt_pow_two_of_testBit
 intro w hw
 simp [z59,Nat.not_lt_of_ge hw]
def y28 (g: b7) (deleted: Nat): List Nat :=
 deleted :: (List.range g.width).filterMap fun v =>
   if !(Nat.testBit deleted v)&&(b3 g deleted v != 0)
   then some (z5 g (Nat.lor deleted (b74 g deleted v)))
   else none
def b34 (g: b7): Nat->List Nat
 | 0 => [z5 g 0]
 | depth+1 => ((b34 g depth).flatMap (y28 g)).eraseDups
lemma y87 {g: b7} {depth deleted next: Nat}
   (hd: deleted ∈ b34 g depth) (hs: next ∈ y28 g deleted) :
   next ∈ b34 g (depth+1):=by
 rw [b34,List.mem_eraseDups,List.mem_flatMap]
 exact ⟨deleted,hd,hs⟩
lemma stay {g: b7} {depth deleted: Nat} (hd: deleted ∈ b34 g depth) :
   deleted ∈ b34 g (depth+1) :=
 y87 hd (by simp [y28])
lemma b183 {g: b7} {depth deleted d1: Nat}
   (hd: deleted ∈ b34 g depth) (hv: d1 < g.width)
   (hlive: Nat.testBit deleted d1=false)
   (hne: b3 g deleted d1≠0) :
   z5 g (Nat.lor deleted (b74 g deleted d1)) ∈ b34 g (depth+1):=by
 apply y87 hd
 apply List.mem_cons_of_mem
 rw [List.mem_filterMap]
 refine ⟨d1,List.mem_range.mpr hv,?_⟩
 simp [hlive,hne]
def petersenNine: b7 :=
 ⟨9,fun v => (#[50,69,138,276,9,385,258,36,104]: Array Nat)[v]?.getD 0⟩
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in
lemma b117: b71 petersenNine ∉ b34 petersenNine 4:=by decide +kernel
end q0
namespace p5
open q0
open y6
def v9 (g: b7) (mask: Nat): Finset (Fin g.width) :=
 Finset.univ.filter (fun v => mask.testBit v.val)
@[simp] lemma mem_decode (g: b7) (mask: Nat) (v: Fin g.width) :
   v ∈ v9 g mask↔mask.testBit v.val=true:=by
 simp [v9]
@[simp] lemma decode_zero (g: b7): v9 g 0=∅:=by
 ext v
 simp
@[simp] lemma decode_full (g: b7): v9 g (b71 g)=Finset.univ:=by
 ext v
 simp [v79,v.isLt]
lemma y79 (g: b7) (a b: Nat) :
   v9 g (Nat.lor a b)=v9 g a ∪ v9 g b:=by
 ext v
 simp [Bool.or_eq_true]
lemma v82 (g: b7) {a b: Nat} (ha: a < bit g.width) (hb: b < bit g.width)
   (same: v9 g a=v9 g b): a=b:=by
 apply x25 ha hb
 intro w hw
 have hm: (⟨w,hw⟩: Fin g.width) ∈ v9 g a↔(⟨w,hw⟩: Fin g.width) ∈ v9 g b:=by
   rw [same]
 simp only [mem_decode] at hm
 exact Bool.eq_iff_iff.mpr hm
lemma v22 (n: Nat): 0 < bit n:=by
 rw [b52]
 exact Nat.two_pow_pos n
lemma b185 (g: b7): b71 g < bit g.width:=by
 unfold b71
 have:=v22 g.width
 omega
section Graph
variable (g: b7) (G: SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj: ∀ u v: Fin g.width,G.Adj u v↔(g.adjacency u.val).testBit v.val=true)
include adj in
lemma b44 (deleted: Nat) (u: Fin g.width) :
   v9 g (b3 g deleted u.val)=z0 G (v9 g deleted) u:=by
 ext v
 cases h: deleted.testBit v.val <;>
   simp [mem_decode,z0,b191 g deleted u.val v.val v.isLt,adj,h]
include adj in
lemma b95 (deleted: Nat) (bound: deleted < bit g.width) (u: Fin g.width) :
   b3 g deleted u.val=0↔z0 G (v9 g deleted) u=∅:=by
 constructor
 · intro h
   rw [← b44 g G adj,h,decode_zero]
 · intro h
   apply v82 g (b64 g deleted u.val bound) (v22 g.width)
   rw [b44 g G adj,h,decode_zero]
include adj in
lemma b153 (deleted: Nat) (bound: deleted < bit g.width) :
   v9 g (q0.z5 g deleted)=y6.z5 G (v9 g deleted):=by
 ext v
 simp [z58,v.isLt,y6.z5,w39,Bool.or_eq_true,
   b95 g G adj deleted bound]
include adj in
lemma b187 (deleted: Nat) (bound: deleted < bit g.width) (root: Fin g.width)
   (outside: root ∉ v9 g deleted) (live: (z0 G (v9 g deleted) root).Nonempty) :
   v9 g (b74 g deleted root.val)=b24 G (v9 g deleted) root:=by
 have same (u: Fin g.width): b3 g deleted u.val=b3 g deleted root.val ↔
     z0 G (v9 g deleted) u=z0 G (v9 g deleted) root:=by
   rw [← b44 g G adj deleted u,← b44 g G adj deleted root]
   exact ⟨congrArg (v9 g),v82 g (b64 g deleted u.val bound)
     (b64 g deleted root.val bound)⟩
 ext v
 cases h: deleted.testBit v.val <;>
   simp [z59,v.isLt,b24,outside,live,h,same,Bool.beq_eq_decide_eq]
def b83 (depth: Nat) (removed: Finset (Fin g.width)): Prop :=
 ∃ m,m ∈ b34 g depth /\ m < bit g.width /\ v9 g m=removed
include adj in
lemma b193: b83 g 0 (y6.z5 G ∅):=by
 refine ⟨q0.z5 g 0,?_,
   b142 g 0 (v22 g.width),?_⟩
 · change q0.z5 g 0 ∈ [q0.z5 g 0]
   exact List.mem_cons_self
 · rw [b153 g G adj _ (v22 g.width),decode_zero]
include adj in
lemma b197 {depth: Nat} {removed: Finset (Fin g.width)} (root: Fin g.width)
   (rep: b83 g depth removed) (closed: y6.z5 G removed=removed) :
   b83 g (depth+1) (b20 G removed root):=by
 obtain ⟨m,hm,bounded,same⟩:=rep
 subst removed
 by_cases active: root ∉ v9 g m /\ (z0 G (v9 g m) root).Nonempty
 · have live: m.testBit root.val=false:=by
     cases h: m.testBit root.val
     · rfl
     · exact (active.1 ((mem_decode g m root).mpr h)).elim
   have someNeighbor: b3 g m root.val≠0:=by
     intro h
     have none:=(b95 g G adj m bounded root).mp h
     simpa [none] using active.2
   have united:=b192 bounded (b181 g m root.val)
   refine ⟨q0.z5 g (Nat.lor m (b74 g m root.val)),
     b183 hm root.isLt live someNeighbor,b142 g _ united,?_⟩
   rw [b153 g G adj _ united,y79,b187 g G adj m bounded root active.1 active.2,
     b20]
 · have sameRemoval: b20 G (v9 g m) root=v9 g m:=by
     have emptyClass: b24 G (v9 g m) root=∅:=ite_eq_right active
     simp only [b20,emptyClass,Finset.union_empty,closed]
   exact ⟨m,stay hm,bounded,sameRemoval.symm⟩
include adj in
lemma y92 {count depth: Nat} {start finish: Finset (Fin g.width)}
   (walk: v17 G count start finish) (initial: b83 g depth start)
   (closed: y6.z5 G start=start): b83 g (depth+count) finish:=by
 induction count generalizing depth start with
 | zero =>
   change finish=start at walk
   simpa only [walk,Nat.add_zero] using initial
 | succ count ih =>
   obtain ⟨root,next⟩:=walk
   have nextClosed: y6.z5 G (b20 G start root)=b20 G start root :=
     b51 G _
   have rest:=ih next (b197 g G adj root initial closed) nextClosed
   simpa only [Nat.add_assoc,Nat.add_comm 1 count] using rest
lemma b195 {m k r: Nat} (reached: m ∈ b34 g k) (budget: k ≤ r): m ∈ b34 g r:=by
 induction r with
 | zero =>
   have: k=0:=by omega
   simpa only [this] using reached
 | succ r ih =>
   by_cases eq: k=r+1
   · simpa [eq] using reached
   · exact stay (ih (by omega))
include adj in
lemma b128 [Nonempty (Fin g.width)] (k: Nat) (noFinish: b71 g ∉ b34 g k)
   (groups: List (Finset (Fin g.width))) (twins: b60 G ∅ groups)
   (finished: b19 G (b13 ∅ groups)): k < groups.length:=by
 by_contra! budget
 have walk:=b58 G groups twins finished
 obtain ⟨m,reached,bound,allGone⟩ :=
   y92 g G adj walk (b193 g G adj) (b51 G ∅)
 have equal: m=b71 g:=v82 g bound (b185 g) (by simpa using allGone)
 rw [equal,Nat.zero_add] at reached
 exact noFinish (b195 g reached budget)
end Graph
lemma petersen_nine_groups_need_five (G: SimpleGraph (Fin 9)) [DecidableRel G.Adj]
   (adj: ∀ u v: Fin 9,G.Adj u v↔(petersenNine.adjacency u.val).testBit v.val=true)
   (groups: List (Finset (Fin 9))) (twins: b60 G ∅ groups)
   (finished: b19 G (b13 ∅ groups)): 5 ≤ groups.length :=
 @b128 petersenNine G (inferInstance: DecidableRel G.Adj) adj
   (inferInstance: Nonempty (Fin 9)) 4 b117 groups twins finished
end p5
open v7
def b6: SimpleGraph d5:=d4 edges x87
def b37: DecidableRel b6.Adj:=fun a b =>
 inferInstanceAs (Decidable ((a,b) ∈ edges \/ (b,a) ∈ edges))
lemma b77 (S: Finset d5) :
   yk edges (fun i => decide (i ∈ S))=true ↔
     y6.containsEdge b6 S:=by
 constructor
 · intro h
   obtain ⟨a,b,g5,ha,hb⟩:=(edgeFun_true edges _).mp h
   exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,Or.inl g5⟩
 · rintro ⟨a,ha,b,hb,adjacent⟩
   change (a,b) ∈ edges \/ (b,a) ∈ edges at adjacent
   apply (edgeFun_true edges _).mpr
   rcases adjacent with g5 | g5
   · exact ⟨a,b,g5,decide_eq_true ha,decide_eq_true hb⟩
   · exact ⟨b,a,g5,decide_eq_true hb,decide_eq_true ha⟩
lemma b76 :
   ∀ a b: d5,b6.Adj a b ↔
     (q0.petersenNine.adjacency a.val).testBit b.val=true:=by
 letI: DecidableRel b6.Adj:=b37
 decide
lemma b53 :
   ∀ i j: d5,b6.Adj i j ->
     ∃ u v,b6.Adj i u /\ b6.Adj j v ∧
       u≠j /\ v≠i /\ ¬ b6.Adj u v:=by
 letI: DecidableRel b6.Adj:=b37
 decide
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open z2 z2.Readers
open scoped BigOperators
def b14 (gs: List Gate): List Nat:=gs.flatMap Gate.inputs
def b49 (gs: List Gate): Nat:=(gs.filter fun g => q6 g.op).length
lemma b46 {gs: List Gate} {slot wire: Nat} (read: c3 gs slot wire) :
   wire ∈ b14 gs:=by
 obtain ⟨g,gAt,before⟩:=read
 exact List.mem_flatMap.mpr ⟨g,List.mem_iff_getElem?.mpr ⟨slot,gAt⟩,before⟩
lemma b91 {gs: List Gate} {wire p q: Nat}
   (neq: p≠q) (first: c3 gs p wire) (second: c3 gs q wire) :
   2 ≤ (b14 gs).count wire:=by
 induction gs generalizing p q with
 | nil =>
   rcases first with ⟨g,atGate,_⟩
   simp at atGate
 | cons a rest ih =>
   simp only [b14,List.flatMap_cons,List.count_append]
   cases p with
   | zero =>
     cases q with
     | zero => exact (neq rfl).elim
     | succ q =>
       have atA: wire ∈ a.inputs:=by simpa [c3] using first
       have later: c3 rest q wire:=by simpa [c3] using second
       have aPos: 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
       have restPos: 0 < (b14 rest).count wire:=List.count_pos_iff.mpr (b46 later)
       simp only [b14] at restPos
       omega
   | succ p =>
     cases q with
     | zero =>
       have atA: wire ∈ a.inputs:=by simpa [c3] using second
       have later: c3 rest p wire:=by simpa [c3] using first
       have aPos: 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
       have restPos: 0 < (b14 rest).count wire:=List.count_pos_iff.mpr (b46 later)
       simp only [b14] at restPos
       omega
     | succ q =>
       have early: c3 rest p wire:=by simpa [c3] using first
       have late: c3 rest q wire:=by simpa [c3] using second
       have different: p≠q:=fun eq => neq (congrArg Nat.succ eq)
       have count:=ih different early late
       simp only [b14] at count
       omega
lemma b120 (gs: List Gate)
   (arity: ∀ g ∈ gs,g.inputs.length+(if q6 g.op then 1 else 0)=2) :
   (b14 gs).length+b49 gs=2*gs.length:=by
 induction gs with
 | nil => simp [b14,b49]
 | cons g gs ih =>
   have gArity:=arity g (by simp)
   have rest:=ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
   cases h: q6 g.op
   · simp [h] at gArity
     simp [b14,b49,h] at rest ⊢
     omega
   · simp [h] at gArity
     simp [b14,b49,h] at rest ⊢
     omega
lemma b159 {n: Nat} {gs: List Gate} (h: v0 n gs) :
   ∀ g ∈ gs,g.inputs.length+(if q6 g.op then 1 else 0)=2:=by
 intro g gMem
 obtain ⟨p,atGate⟩:=List.mem_iff_getElem?.mp gMem
 rcases h p g atGate with ⟨op,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
 · simp [op,args,q6]
 · rcases ops with op | op <;> simp [op,args,q6]
lemma b40 (gs: List Gate) (branches: Finset Nat)
   (twice: ∀ w ∈ branches,2 ≤ (b14 gs).count w) :
   branches.card+(b14 gs).toFinset.card ≤ (b14 gs).length:=by
 classical
 let W:=(b14 gs).toFinset
 have subset: branches ⊆ W:=by
   intro w wm
   have t:=twice w wm
   exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
 have aux: (∑ w ∈ W,if w ∈ branches then (1: Nat) else 0)=branches.card:=by
   have same: (∑ w ∈ W,if w ∈ branches then (1: Nat) else 0) =
       ∑ w ∈ branches,if w ∈ branches then (1: Nat) else 0:=by
     symm
     apply Finset.sum_subset subset
     intro w _ notBranch
     simp [notBranch]
   rw [same]
   simp
 have total: (∑ w ∈ W,(b14 gs).count w)=(b14 gs).length :=
   List.sum_toFinset_count_eq_length _
 have bound: (∑ w ∈ W,((if w ∈ branches then (1: Nat) else 0)+1)) ≤
     ∑ w ∈ W,(b14 gs).count w:=by
   apply Finset.sum_le_sum
   intro w wIn
   by_cases b: w ∈ branches
   · simpa [b] using twice w b
   · have pos: 0 < (b14 gs).count w:=List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
     simpa [b] using pos
 rw [Finset.sum_add_distrib,aux,total] at bound
 simpa [W] using bound
lemma b160 {n out: Nat} {gs: List Gate} (clean: v0 n gs)
   (outValid: out < n+gs.length)
   (everyNonoutputUsed: ∀ w < n+gs.length,w≠out->∃ p,c3 gs p w)
   (branches: Finset Nat)
   (twoReaders: ∀ w ∈ branches,∃ p q,p≠q /\ c3 gs p w /\ c3 gs q w) :
   branches.card+(n+gs.length - 1)+b49 gs ≤ 2*gs.length:=by
 let W:=(b14 gs).toFinset
 let required:=(Finset.range (n+gs.length)).erase out
 have requiredUsed: required ⊆ W:=by
   intro w inSet
   have spec:=Finset.mem_erase.mp inSet
   obtain ⟨p,read⟩:=everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
   exact List.mem_toFinset.mpr (b46 read)
 have numRequired: required.card=n+gs.length - 1:=by
   change ((Finset.range (n+gs.length)).erase out).card=_
   rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid),Finset.card_range]
 have twice: ∀ w ∈ branches,2 ≤ (b14 gs).count w:=by
   intro w mem
   obtain ⟨p,q,different,pReads,qReads⟩:=twoReaders w mem
   exact b91 different pReads qReads
 have up:=b40 gs branches twice
 have used:=Finset.card_le_card requiredUsed
 rw [numRequired] at used
 have total:=b120 gs (b159 clean)
 change n+gs.length - 1 ≤ (b14 gs).toFinset.card at used
 omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open z2 z2.Readers
open w4
lemma b68 {n out: Nat} {gs: List Gate}
   {f: (Fin n->Bool)->Bool} (least: p1 n f gs out) (nonnull: ∃ x y,f x≠f y)
   (dependent: ∀ v: Fin n,Dep f v)
   (stillNonconstant: ∀ (v: Fin n) (b: Bool),∃ x y,
     f (Function.update x v b)≠f (Function.update y v b))
   (outValid: out < n+gs.length) :
   ∀ w: Fin (n+gs.length),w≠(⟨out,outValid⟩: Fin (n+gs.length))->∃ v,b5 gs w v:=by
 intro w notOutput
 have notSame: w.val≠out:=fun eq => notOutput (Fin.ext eq)
 obtain ⟨p,g,atSlot,reads,bound⟩ :=
   b79 least nonnull dependent stillNonconstant w notSame
 exact ⟨⟨n+p,bound⟩,p,g,atSlot,rfl,reads⟩
lemma b88 {n: Nat} {gs: List Gate} {w: Fin (n+gs.length)}
   (fork: z8.Branches (b5 gs) w) :
   ∃ p q,p≠q /\ c3 gs p w.val /\ c3 gs q w.val:=by
 obtain ⟨first,next,pRead,qRead,separate⟩:=fork
 obtain ⟨p,g,atP,src,ap⟩:=pRead
 obtain ⟨q,h,atQ,dst,aq⟩:=qRead
 refine ⟨p,q,?_,⟨g,atP,ap⟩,⟨h,atQ,aq⟩⟩
 intro same
 subst q
 exact separate (Fin.ext (src.trans dst.symm))
noncomputable def circuitBranchWires {n: Nat} (gs: List Gate): Finset (Fin (n+gs.length)):=by
 classical
 exact (Finset.univ).filter fun w => z8.Branches (b5 gs) w
lemma b25 {n: Nat} {gs: List Gate} {w: Fin (n+gs.length)} :
   w ∈ circuitBranchWires gs↔z8.Branches (b5 gs) w:=by
 classical
 simp [circuitBranchWires]
def b93 {V W: Type} [Fintype V] (label: V->W) [DecidableEq W] (cut: W): Finset V :=
 Finset.univ.filter fun v => label v=cut
def b26 {V W: Type} [Fintype V] (label: V->W) [LinearOrder W] (cut: W): Finset V :=
 Finset.univ.filter fun v => label v < cut
lemma b189 {V W: Type} [Fintype V] (label: V->W) [DecidableEq W] (cut: W) (v: V) :
   v ∈ b93 label cut↔label v=cut:=by
 simp [b93]
lemma b143 {V W: Type} [Fintype V] (label: V->W) [LinearOrder W] (cut: W) (v: V) :
   v ∈ b26 label cut↔label v < cut:=by
 simp [b26]
lemma b82 {V W: Type} [Fintype V] [DecidableEq V] [LinearOrder W]
   (G: SimpleGraph V) [DecidableRel G.Adj] (label: V->W) (cut: W)
   (independent: y6.Independent G (b93 label cut))
   (code: Finset V->Bool) (v9: Bool->Finset V->Prop)
   (factors: ∀ I O: Finset V,(∀ i ∈ I,label i=cut) ->
     (∀ i ∈ O,cut < label i)->(y6.containsEdge G (I ∪ O)↔v9 (code I) O)) :
   y6.TwinGroup G (b26 label cut) (b93 label cut):=by
 intro u uGroup v vGroup uActive vActive
 have later {x y: V} (xGroup: x ∈ b93 label cut) (g5: G.Adj x y)
     (notEarlier: y ∉ b26 label cut): cut < label y:=by
   have ne: label y≠cut:=fun equal =>
     independent x xGroup y ((b189 label cut y).mpr equal) g5
   have notBefore: ¬ label y < cut:=fun h => notEarlier ((b143 label cut y).mpr h)
   exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
 have single (x y: V) (xGroup: x ∈ b93 label cut) (yLater: cut < label y) :
     (G.Adj x y↔v9 (code {x}) {y}):=by
   have g (i: V) (mem: i ∈ ({x}: Finset V)): label i=cut:=by
     have eq: i=x:=Finset.mem_singleton.mp mem
     subst i
     exact (b189 label cut x).mp xGroup
   have h (i: V) (mem: i ∈ ({y}: Finset V)): cut < label i:=by
     have eq: i=y:=Finset.mem_singleton.mp mem
     rwa [eq]
   simpa [y6.pair_contains_edge] using factors {x} {y} g h
 have cannot (x: V) (xGroup: x ∈ b93 label cut)
     (active: (y6.z0 G (b26 label cut) x).Nonempty) :
     code {x}≠code ∅:=by
   obtain ⟨y,xd⟩:=active
   simp only [y6.z0,Finset.mem_filter,Finset.mem_univ,true_and] at xd
   have yLater:=later xGroup xd.1 xd.2
   have yes:=(single x y xGroup yLater).mp xd.1
   intro collapse
   rw [collapse] at yes
   have one:=(factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
   exact y6.singleton_no_edge G y (by simpa using one)
 have a:=cannot u uGroup uActive
 have b:=cannot v vGroup vActive
 have sameCode: code {u}=code {v}:=by
   cases hc: code ∅ <;> cases ha: code {u} <;> cases hb: code {v} <;> simp_all
 ext z
 simp only [y6.z0,Finset.mem_filter,Finset.mem_univ,true_and]
 constructor
 · rintro ⟨g5,remains⟩
   have pos:=later uGroup g5 remains
   refine ⟨(single v z vGroup pos).mpr ?_,remains⟩
   rw [← sameCode]
   exact (single u z uGroup pos).mp g5
 · rintro ⟨g5,remains⟩
   have pos:=later vGroup g5 remains
   refine ⟨(single u z uGroup pos).mpr ?_,remains⟩
   rw [sameCode]
   exact (single v z vGroup pos).mp g5
namespace w4
open PEqualNP.CircuitLowerBounds z2
open Relation
lemma b100 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (x y: Fin n->Bool) (w: Fin (n+gs.length))
   (agrees: ∀ i,ReflTransGen (b5 gs) (b8 gs i) w->x i=y i) :
   vl gs x w.val=vl gs y w.val:=by
 revert agrees
 induction w using (measure (fun a: Fin (n+gs.length) => a.val)).wf.induction with
 | h w earlier =>
   intro agree
   by_cases input: w.val < n
   · let i: Fin n:=⟨w.val,input⟩
     have name: b8 gs i=w:=Fin.ext rfl
     have atInput: ReflTransGen (b5 gs) (b8 gs i) w:=by
       simpa only [name] using (ReflTransGen.refl: ReflTransGen (b5 gs) w w)
     have a:=agree i atInput
     simpa only [b69 gs x w.val input,b69 gs y w.val input] using a
   · let p:=w.val - n
     have pLt: p < gs.length:=by have:=w.isLt; dsimp [p]; omega
     have gateWire: w.val=n+p:=by dsimp [p]; omega
     let g:=gs[p]'pLt
     have atGate: gs[p]?=some g:=List.getElem?_eq_getElem pLt
     rw [gateWire]
     apply z39 gs clean x y p g atGate
     intro a inGate
     have readBefore:=(clean p g atGate).lt a inGate
     let wire: Fin (n+gs.length):=⟨a,by have:=w.isLt; omega⟩
     have read: b5 gs wire w:=⟨p,g,atGate,gateWire,inGate⟩
     apply earlier wire (show wire.val < w.val by change a < w.val; omega)
     intro i path
     exact agree i (path.tail read)
end w4
open PEqualNP.CircuitLowerBounds
open z2
open w4 Relation
def b55 {n: Nat} (S: Finset (Fin n)) (i: Fin n): Bool:=decide (i ∈ S)
lemma b97 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (out: Fin (n+gs.length))
   (live: ∀ v: Fin (n+gs.length),v≠out->∃ w,b5 gs v w)
   (cut: Fin (n+gs.length)) (prior: cut ≤ out)
   (terminal: z8.Terminal (b5 gs) out cut) :
   let label (i: Fin n) :=
     z8.first (b5 gs) out (b15 clean) live (b8 gs i)
   ∃ code: Finset (Fin n)->Bool,∃ v9: Bool->Finset (Fin n)->Prop,
     ∀ I O: Finset (Fin n),
       (∀ i ∈ I,label i=cut)->(∀ i ∈ O,cut < label i) ->
       (vl gs (b55 (I ∪ O)) out.val=true↔v9 (code I) O):=by
 classical
 let label (i: Fin n) :=
   z8.first (b5 gs) out (b15 clean) live (b8 gs i)
 let code (I: Finset (Fin n)):=vl gs (b55 I) cut.val
 let v9 (b: Bool) (O: Finset (Fin n)) :=
   ∃ J: Finset (Fin n),(∀ j ∈ J,label j=cut) /\ code J=b ∧
     vl gs (b55 (J ∪ O)) out.val=true
 refine ⟨code,v9,?_⟩
 intro I O groupI afterO
 change (∀ i ∈ I,label i=cut) at groupI
 change (∀ i ∈ O,cut < label i) at afterO
 change (_↔v9 (code I) O)
 constructor
 · exact fun yes => ⟨I,groupI,rfl,yes⟩
 · rintro ⟨J,groupJ,sameCode,yes⟩
   have stable (K: Finset (Fin n)): vl gs (b55 (K ∪ O)) cut.val=code K:=by
     apply b100 clean
     intro i ancestral
     have limit: label i ≤ cut :=
       z8.ancestor_first_le (b5 gs) out (b15 clean) live ancestral terminal
     have absent: i ∉ O:=fun mem => (not_lt_of_ge limit) (afterO i mem)
     simp [b55,absent]
   have sameCut: vl gs (b55 (I ∪ O)) cut.val=vl gs (b55 (J ∪ O)) cut.val :=
     (stable I).trans (sameCode.symm.trans (stable J).symm)
   by_cases atOutput: cut=out
   · rw [atOutput] at sameCut
     exact sameCut.trans yes
   have before: cut < out:=lt_of_le_of_ne prior atOutput
   have eq:=b59 clean cut out _ _ sameCut (by
     intro i diff
     have isGroup: label i=cut:=by
       by_contra offGroup
       have notI: i ∉ I:=fun mem => offGroup (groupI i mem)
       have notJ: i ∉ J:=fun mem => offGroup (groupJ i mem)
       exact diff (by simp [b55,notI,notJ])
     intro bypass
     have groupLabel: z8.first (b5 gs) out (b15 clean) live
         (b8 gs i)=cut:=isGroup
     have forbid:=z8.no_avoiding_after (b5 gs) out (b15 clean) live
       (v:=b8 gs i) (w:=out) (by simpa [groupLabel] using before)
     apply forbid
     have weaker: ∀ a b,kc (b5 gs) cut a b->z8.Avoid (b5 gs) cut a b :=
       fun _ _ h => ⟨h.1,h.2.1⟩
     have convert: ReflTransGen (z8.Avoid (b5 gs) cut) (b8 gs i) out :=
       ReflTransGen.mono weaker _ _ bypass
     simpa only [groupLabel] using convert)
   rwa [eq]
open PEqualNP.CircuitLowerBounds z2
open w4
lemma b87 {n: Nat} {gs: List Gate} (clean: v0 n gs)
   (out: Fin (n+gs.length))
   (live: ∀ v: Fin (n+gs.length),v≠out->∃ w,b5 gs v w)
   (G: SimpleGraph (Fin n)) [DecidableRel G.Adj]
   (computes: ∀ S: Finset (Fin n),vl gs (b55 S) out.val=true↔y6.containsEdge G S)
   (cut: Fin (n+gs.length)) (prior: cut ≤ out)
   (terminal: z8.Terminal (b5 gs) out cut)
   (independent: y6.Independent G
     (b93 (fun i => z8.first (b5 gs) out (b15 clean) live (b8 gs i)) cut)) :
   let label (i: Fin n):=z8.first (b5 gs) out (b15 clean) live (b8 gs i)
   y6.TwinGroup G (b26 label cut) (b93 label cut):=by
 let label (i: Fin n):=z8.first (b5 gs) out (b15 clean) live (b8 gs i)
 obtain ⟨code,v9,factors⟩:=b97 clean out live cut prior terminal
 change y6.TwinGroup G (b26 label cut) (b93 label cut)
 exact b82 G label cut independent code v9 (by
   intro I O group after
   rw [← computes (I ∪ O)]
   exact factors I O group after)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open z2 z2.Readers
open w4 p6
abbrev k8:=yk edges
private lemma b78: ∀ v: d5,∃ w: d5,
   k8 (Function.update (fun i => decide (i=w)) v
     (!(decide (v=w))))≠k8 (fun i => decide (i=w)):=by decide +kernel
lemma b63 (v: d5): Dep k8 v:=by
 obtain ⟨w,hw⟩:=b78 v
 exact ⟨fun i => decide (i=w),hw⟩
lemma b16: ∃ x y: d5->Bool,k8 x≠k8 y :=
 w97 (b63 0)
private lemma b92: ∀ (v: d5) (b: Bool),
   k8 (Function.update (fun _ => false) v b)=false ∧
   k8 (Function.update (fun _ => true) v b)=true:=by decide +kernel
lemma b27 (v: d5) (b: Bool) :
   ∃ x y,k8 (Function.update x v b)≠k8 (Function.update y v b):=by
 obtain ⟨no,yes⟩:=b92 v b
 exact ⟨fun _ => false,fun _ => true,by rw [no,yes]; decide⟩
lemma b118 (x: Fin 9->Bool): k8 x=true ↔
   ∃ u v: Fin 9,b6.Adj u v /\ x u=true /\ x v=true:=by
 change v7.yk v7.edges x=true↔_
 rw [v7.edgeFun_true]
 constructor
 · rintro ⟨a,b,g5,ha,hb⟩
   exact ⟨a,b,Or.inl g5,ha,hb⟩
 · rintro ⟨a,b,adjacent,ha,hb⟩
   change (a,b) ∈ v7.edges \/ (b,a) ∈ v7.edges at adjacent
   rcases adjacent with g5 | g5
   · exact ⟨a,b,g5,ha,hb⟩
   · exact ⟨b,a,g5,hb,ha⟩
lemma b32 {gs: List Gate} {out: Nat} (least: p1 9 k8 gs out) :
   out < 9+gs.length:=by
 by_contra! after
 obtain ⟨x,y,different⟩:=least.ncv b16
 exact different ((v23 gs x out after).trans (v23 gs y out after).symm)
lemma b70 (gs: List Gate) (out: Nat) (least: p1 9 k8 gs out)
   : 5 ≤ (circuitBranchWires (n:=9) gs).card:=by
 classical
 letI: DecidableRel b6.Adj:=b37
 have outValid:=b32 least
 let outWire: Fin (9+gs.length):=⟨out,outValid⟩
 have live:=b68 least b16 b63 b27 outValid
 let label: Fin 9->Fin (9+gs.length):=firstInputBoundary least.hcl outWire live
 let branches: Finset (Fin (9+gs.length)):=circuitBranchWires gs
 have computes (x: Fin 9->Bool): vl gs x outWire.val=j1.edgeValue b6 x:=by
   change vl gs x out=_
   rw [least.hev,Bool.eq_iff_iff,b118]
   simp only [j1.edgeValue,decide_eq_true_eq]
 have marked (S: Finset (Fin 9)): vl gs (b55 S) outWire.val=true ↔
     y6.containsEdge b6 S:=by
   change vl gs (b55 S) out=true↔_
   rw [least.hev]
   exact b77 S
 have independent (r): y6.Independent b6 (j7.bucket label r) :=
   b80 least.hcl outWire live (b137 least b16)
     b6 computes b53 r
 have labels (v: Fin 9): label v=outWire \/ label v ∈ branches:=by
   have stopped:=z8.first_stops (b5 gs) outWire (b15 least.hcl) live (b8 gs v)
   rcases stopped with outLabel | fork
   · exact Or.inl outLabel
   · exact Or.inr (b25.mpr fork)
 have before (r) (member: r ∈ branches): r < outWire:=by
   obtain ⟨a,_,path,_,_⟩:=b25.mp member
   exact lt_of_lt_of_le (b15 least.hcl path) (b130 least.hcl outWire live a)
 have twins (r) (member: r ∈ branches): y6.TwinGroup b6
     (j7.below label r) (j7.bucket label r) :=
   b87 least.hcl outWire live b6 marked r
     (le_of_lt (before r member)) (Or.inr (b25.mp member)) (independent r)
 exact j7.roots_required b6 label outWire branches 5 labels before twins
   (independent outWire) (p5.petersen_nine_groups_need_five b6 b76)
lemma nonNotCount_add_notCount (gs: List Gate) :
   z6 gs+(gs.filter (fun g => q6 g.op)).length=gs.length:=by
 rw [← List.countP_eq_length_filter]
 induction gs with
 | nil => simp [z6]
 | cons g gs ih =>
   simp only [z6,List.countP_cons,List.length_cons] at ih ⊢
   cases h: q6 g.op <;> simp [h] <;> omega
lemma petersen_binary_lower (C: Circuit) (hfan: FanInTwo C)
   (he: ∀ x: d5->Bool,C.eval (List.ofFn x)=k8 x) :
   13 ≤ z6 C.gates:=by
 obtain ⟨gs,o,least,budget⟩:=b146 C hfan he b16
 have valid:=b32 least
 have live:=b68 least b16 b63
   b27 valid
 let branches:=circuitBranchWires (n:=9) gs
 have branchLower: 5 ≤ branches.card:=b70 gs o least
 have branchBudget:=b160 least.hcl valid (fun w hw hne => by
     let wire: Fin (9+gs.length):=⟨w,hw⟩
     obtain ⟨v,p,g,hg,_,hw'⟩:=live wire (fun h => hne (congrArg Fin.val h))
     exact ⟨p,g,hg,hw'⟩)
   (branches.image Fin.val) (fun w hw => by
     obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
     exact b88 (b25.mp hv))
 rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
 have countTotal:=nonNotCount_add_notCount gs
 change z6 gs+b49 gs=gs.length at countTotal
 omega
end Binary
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero: Sig:=0
def one: Sig:=BitVec.allOnes 512
def neg (a: Sig): Sig:= ~~~a
def bin (d: Bool) (a b: Sig): Sig:=if d then a ||| b else a &&& b
def x7 (a: Sig): Prop:=a≠zero /\ a≠one
private lemma m24 (d: Bool) (a b: Sig): bin d a b=bin d b a:=by
 cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def j6 (target: Sig): Nat->Nat->Finset Sig->Prop:=fun k t S =>
 ∀ (M: (Nat->Nat->Finset Sig->Prop)),(x7 target->M 0 0 {target}) ->
 (∀ {k t: Nat} {U: Finset Sig} {a: Sig},x7 a->neg a ∉ insert a U->M k t (insert (neg a) U)->M (k+1) (t+1) (insert a U)) ->
 (∀ {k t: Nat} {U: Finset Sig} {a b: Sig} {d: Bool},x7 a->x7 b->a≠b->bin d a b ∉ insert a (insert b U)->M k t (insert (bin d a b) U)->M (k+1) t (insert a (insert b U))) ->
 M k t S
lemma j6.stop {target: Sig}  (h0: x7 target): j6 target 0 0 {target}:=fun M stop unary binary => @stop  h0
lemma j6.unary {target: Sig} {k t: Nat} {U: Finset Sig} {a: Sig} (h0: x7 a) (h1: neg a ∉ insert a U) (h2: j6 target k t (insert (neg a) U)): j6 target (k+1) (t+1) (insert a U):=fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
lemma j6.binary {target: Sig} {k t: Nat} {U: Finset Sig} {a b: Sig} {d: Bool} (h0: x7 a) (h1: x7 b) (h2: a≠b) (h3: bin d a b ∉ insert a (insert b U)) (h4: j6 target k t (insert (bin d a b) U)): j6 target (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
lemma j6.induct {target: Sig} {M: (Nat->Nat->Finset Sig->Prop)} {k t S} (h: j6 target k t S)
 (stop: x7 target->M 0 0 {target})
 (unary: ∀ {k t: Nat} {U: Finset Sig} {a: Sig},x7 a->neg a ∉ insert a U->j6 target k t (insert (neg a) U)->M k t (insert (neg a) U)->M (k+1) (t+1) (insert a U))
 (binary: ∀ {k t: Nat} {U: Finset Sig} {a b: Sig} {d: Bool},x7 a->x7 b->a≠b->bin d a b ∉ insert a (insert b U)->j6 target k t (insert (bin d a b) U)->M k t (insert (bin d a b) U)->M (k+1) t (insert a (insert b U))): M k t S :=
 (h (fun k t S => j6 target k t S /\ M k t S)
 (fun h0 => ⟨@j6.stop target  h0,@stop  h0⟩)
 (@fun k t U a h0 h1 h2 => ⟨@j6.unary target k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
 (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@j6.binary target k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
lemma j6.recurse {target: Sig} {M: ∀ (k t: Nat) (S: Finset Sig) (proof: j6 target k t S),Prop}
 (stop: ∀ (h0: x7 target),M 0 0 {target} (@j6.stop target  h0))
 (unary: ∀ {k t: Nat} {U: Finset Sig} {a: Sig} (h0: x7 a) (h1: neg a ∉ insert a U) (h2: j6 target k t (insert (neg a) U)) (ih: M k t (insert (neg a) U) h2),M (k+1) (t+1) (insert a U) (@j6.unary target k t U a h0 h1 h2))
 (binary: ∀ {k t: Nat} {U: Finset Sig} {a b: Sig} {d: Bool} (h0: x7 a) (h1: x7 b) (h2: a≠b) (h3: bin d a b ∉ insert a (insert b U)) (h4: j6 target k t (insert (bin d a b) U)) (ih: M k t (insert (bin d a b) U) h4),M (k+1) t (insert a (insert b U)) (@j6.binary target k t U a b d h0 h1 h2 h3 h4))
 {k t S} (h: j6 target k t S): M k t S h:=by
 have r:=j6.induct (M:=fun k t S => ∀ hh: j6 target k t S,M k t S hh) h
   (fun h0 _ => @stop  h0)
   (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
   (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
 exact r h
lemma j6.zeroSet {T t S} (h: j6 T 0 t S): S={T}:=by
 have hh:=h (fun k _ W => k=0->W={T}) (fun _ _ => rfl)
   (@fun _ _ _ _ _ _ _ e => by omega)
   (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
 exact hh rfl
private lemma m22 {k t S} (h: j6 target k t S): ∀ a ∈ S,x7 a:=by
 induction h using j6.recurse with
 | stop hp => simpa using hp
 | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
 | binary ha hb hab hf _ ih =>
   simp only [Finset.forall_mem_insert]
   exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma m26 {k t S} (h: j6 target k t S): t ≤ k /\ S.card+t ≤ k+1:=by
 induction h using j6.recurse with
 | stop hp => simp
 | @unary k t U a ha hf _ ih =>
   have hu: neg a ∉ U:=fun hm => hf (Finset.mem_insert_of_mem hm)
   rw [Finset.card_insert_of_notMem hu] at ih
   have hc:=Finset.card_insert_le a U
   exact ⟨by omega,by omega⟩
 | @binary k t U a b d ha hb hab hf _ ih =>
   have hu: bin d a b ∉ U:=fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
   rw [Finset.card_insert_of_notMem hu] at ih
   have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
   have h2:=Finset.card_insert_le (a:=b) (s:=U)
   exact ⟨by omega,by omega⟩
def gv (w: List Sig) (g: Gate): Sig :=
 let xs:=g.inputs.map (fun i => w.getD i zero)
 match g.op with
 | .and => xs.foldr (bin false) one
 | .or => xs.foldr (bin true) zero
 | .not => neg (xs.headD zero)
 | _ => zero
def xq (gs: List Gate) (w: List Sig): List Sig :=
 gs.foldl (fun l g => l ++ [gv l g]) w
def w1 (w: List Sig) (v: Sig): Prop:=v ∈ w \/ ¬x7 v
private lemma yv (w: List Sig) (i: Nat): w1 w (w.getD i zero):=by
 simp only [List.getD_eq_getElem?_getD]
 cases h: w[i]? with
 | none => exact Or.inr (fun h => h.1 rfl)
 | some a => exact Or.inl (List.mem_of_getElem? h)
private lemma m16 (a: Sig) :
   bin false a one=a /\ bin true a zero=a ∧
   bin false a zero=zero /\ bin true a one=one ∧
   bin false a a=a /\ bin true a a=a:=by
 simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
private lemma m70: neg zero=one /\ neg one=zero:=by simp [neg,zero,one]
private lemma m13 {w: List Sig} {a: Sig} (h: w1 w a) :
   a=zero \/ a=one \/ a ∈ w /\ x7 a:=by
 by_cases hz: a=zero
 · exact Or.inl hz
 by_cases ho: a=one
 · exact Or.inr (Or.inl ho)
 exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def xz (w: List Sig) (z: Sig): Prop :=
 (∃ a ∈ w,x7 a /\ z=neg a) ∨
 (∃ d a b,a ∈ w /\ b ∈ w /\ x7 a /\ x7 b /\ a≠b /\ z=bin d a b)
private lemma w38 {w a b} (d: Bool) (ha: w1 w a) (hb: w1 w b) :
   w1 w (bin d a b) \/ xz w (bin d a b):=by
 have rz: w1 w zero:=Or.inr (fun h => h.1 rfl)
 have ro: w1 w one:=Or.inr (fun h => h.2 rfl)
 obtain ⟨a1,a0,az,ao,aa,aa'⟩:=m16 a
 obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=m16 b
 rcases m13 ha with rfl | rfl | ⟨ham,hap⟩
 · rw [m24]; cases d <;> simp_all
 · rw [m24]; cases d <;> simp_all
 rcases m13 hb with rfl | rfl | ⟨hbm,hbp⟩
 · cases d <;> simp_all
 · cases d <;> simp_all
 by_cases he: a=b
 · subst b; cases d <;> simp_all
 exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
private lemma y37 {w: List Sig} {z: Sig} {k t S} (h: j6 target k t S)
   (hz: w1 w z \/ xz w z) (sub: ∀ a ∈ S,a ∈ w++[z]) :
   ∃ k' t' S',k' ≤ k+1 /\ j6 target k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
 by_cases hm: z ∈ S
 · by_cases hw: z ∈ w
   · refine ⟨k,t,S,by omega,h,?_⟩
     intro a ha
     have hu: a ∈ w \/ a=z:=by simpa using sub a ha
     rcases hu with hu | rfl
     · exact hu
     · exact hw
   · have hp:=m22 h z hm
     rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
     · exact False.elim ((hr.resolve_left hw) hp)
     · subst z
       let U:=S.erase (neg a)
       have ht: j6 target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
       have hu: ∀ v ∈ U,v ∈ w:=by
         intro v hv
         obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
         simpa [hne] using sub v hm
       have hf: neg a ∉ insert a U:=by
         intro hh
         rcases Finset.mem_insert.mp hh with eq | u
         · exact hw (eq.symm ▸ ha)
         · exact hw (hu _ u)
       exact ⟨_,_,_,Nat.le_refl _,j6.unary hp' hf ht,by simpa using And.intro ha hu⟩
     · subst z
       let U:=S.erase (bin d a b)
       have ht: j6 target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
       have hu: ∀ v ∈ U,v ∈ w:=by
         intro v hv
         obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
         simpa [hne] using sub v hm
       have hf: bin d a b ∉ insert a (insert b U):=by
         intro hh
         rcases Finset.mem_insert.mp hh with eq | u
         · exact hw (eq.symm ▸ ha)
         rcases Finset.mem_insert.mp u with eq | u
         · exact hw (eq.symm ▸ hb)
         · exact hw (hu _ u)
       exact ⟨_,_,_,Nat.le_refl _,j6.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
 · refine ⟨k,t,S,by omega,h,?_⟩
   intro a ha
   have hn: a≠z:=fun hh => hm (hh ▸ ha)
   simpa [hn] using sub a ha
def bit (i: Fin 512) (a: Sig): Bool:=a.getLsbD i.val
private lemma m15 (i): bit i zero=false:=by simp [bit,zero]
private lemma xj (i): bit i one=true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma zz (i) (a: Sig): bit i (neg a)=!(bit i a):=by simp [bit,neg,i.isLt]
private lemma p0 (i d) (a b: Sig): bit i (bin d a b) =
   (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
private lemma x64 (i) (w: List Sig) (j: Nat) :
   (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
 cases w[j]? with
 | none => exact (m15 _).symm
 | some a => rfl
private lemma x74 (i) (g: Gate) (w: List Sig)
   (hg: g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}: Set GateOp)) :
   bit i (gv w g)=g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false):=by
 obtain ⟨o,l⟩:=g
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
 simp only [x64]
 rcases hg with rfl | rfl | rfl
 · induction l with
   | nil => exact xj _
   | cons a l ih =>
     change bit i (bin false _ _)=(_&&_)
     rw [p0]; exact congrArg (fun x => bit i (w.getD a zero)&&x) ih
 · induction l with
   | nil => exact m15 _
   | cons a l ih =>
     change bit i (bin true _ _)=(_||_)
     rw [p0]; exact congrArg (fun x => bit i (w.getD a zero)||x) ih
 · cases l with
   | nil =>
     change bit i (neg zero)=!false
     rw [zz,m15]
   | cons a l => exact zz _ _
private lemma m47 (gs: List Gate) (i) (w: List Sig)
   (hg: ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}: Set GateOp)) :
   (xq gs w).map (bit i) =
   gs.foldl (fun (l: List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
   change (xq gs (w++[gv w g])).map _=_
   rw [ih _ (fun a ha => hg a (by simp [ha]))]
   simp only [List.foldl_cons,List.map_append,List.map_singleton,x74 i g w (hg g (by simp))]
abbrev k2 (R: Type):=R->Bool
def inv {R} (a: k2 R): k2 R:=fun r => !(a r)
def w9 {R} (isOr: Bool) (a b: k2 R): k2 R :=
 if isOr then fun r => a r||b r else fun r => a r&&b r
def v6 {R} (a: k2 R): Prop:=∃ b: Bool,a=fun _ => b
noncomputable def cost {R} (a: k2 R): Nat:=by
 classical exact if v6 a then 1 else 0
noncomputable def mass {R} (xs: List (k2 R)): Nat:=(xs.map cost).sum
def y1 {R} (pool: List (k2 R)) (v: k2 R): Prop:=v ∈ pool \/ v6 v
def wd {R} (pool xs: List (k2 R)):=∀ a ∈ xs,y1 pool a
def q4 {R} (roots: List (k2 R)): Nat->List (k2 R)->Prop:=fun p bank =>
 ∀ (M: (Nat->List (k2 R)->Prop)),(M 0 roots) ->
 (∀ {p: Nat} {bank: List (k2 R)} {a: k2 R},M p bank->y1 bank a->M (p+1) (inv a :: bank)) ->
 (∀ {p: Nat} {bank: List (k2 R)} {a b: k2 R} (op: Bool),M p bank->y1 bank a->y1 bank b->M (p+1) (w9 op a b :: bank)) ->
 M p bank
lemma q4.start {R} {roots: List (k2 R)}  : q4 roots 0 roots:=fun M start one two => @start
lemma q4.one {R} {roots: List (k2 R)} {p: Nat} {bank: List (k2 R)} {a: k2 R} (h0: q4 roots p bank) (h1: y1 bank a): q4 roots (p+1) (inv a :: bank):=fun M start one two => @one p bank a (h0 M start one two) h1
lemma q4.two {R} {roots: List (k2 R)} {p: Nat} {bank: List (k2 R)} {a b: k2 R} (op: Bool) (h0: q4 roots p bank) (h1: y1 bank a) (h2: y1 bank b): q4 roots (p+1) (w9 op a b :: bank):=fun M start one two => @two p bank a b op (h0 M start one two) h1 h2
lemma q4.induct {R} {roots: List (k2 R)} {M: (Nat->List (k2 R)->Prop)} {p bank} (h: q4 roots p bank)
 (start: M 0 roots)
 (one: ∀ {p: Nat} {bank: List (k2 R)} {a: k2 R},q4 roots p bank->M p bank->y1 bank a->M (p+1) (inv a :: bank))
 (two: ∀ {p: Nat} {bank: List (k2 R)} {a b: k2 R} (op: Bool),q4 roots p bank->M p bank->y1 bank a->y1 bank b->M (p+1) (w9 op a b :: bank)): M p bank :=
 (h (fun p bank => q4 roots p bank /\ M p bank)
 (⟨@q4.start R roots  ,@start  ⟩)
 (@fun p bank a h0 h1 => ⟨@q4.one R roots p bank a h0.1 h1,@one p bank a h0.1 h0.2 h1⟩)
 (@fun p bank a b op h0 h1 h2 => ⟨@q4.two R roots p bank a b op h0.1 h1 h2,@two p bank a b op h0.1 h0.2 h1 h2⟩)).2
lemma q4.recurse {R} {roots: List (k2 R)} {M: ∀ (p: Nat) (bank: List (k2 R)) (proof: q4 roots p bank),Prop}
 (start: M 0 roots (@q4.start R roots  ))
 (one: ∀ {p: Nat} {bank: List (k2 R)} {a: k2 R} (h0: q4 roots p bank) (ih: M p bank h0) (h2: y1 bank a),M (p+1) (inv a :: bank) (@q4.one R roots p bank a h0 h2))
 (two: ∀ {p: Nat} {bank: List (k2 R)} {a b: k2 R} (op: Bool) (h0: q4 roots p bank) (ih: M p bank h0) (h2: y1 bank a) (h3: y1 bank b),M (p+1) (w9 op a b :: bank) (@q4.two R roots p bank a b op h0 h2 h3))
 {p bank} (h: q4 roots p bank): M p bank h:=by
 have r:=q4.induct (M:=fun p bank => ∀ hh: q4 roots p bank,M p bank hh) h
   (fun  _ => @start  )
   (@fun p bank a h0 h1 h2 _ => @one p bank a h0 (h1 h0) h2)
   (@fun p bank a b op h0 h1 h2 h3 _ => @two p bank a b op h0 (h1 h0) h2 h3)
 exact r h
def g6 {α: Type} (save: Bool) (x: α) (xs: List α):=if save then x::xs else xs
def Run {R} (goal: k2 R): Nat->List (k2 R)->Prop:=fun s ws =>
 ∀ (M: (Nat->List (k2 R)->Prop)),(M 0 [goal]) ->
 (∀ {s: Nat} {xs zs: List (k2 R)},xs.Perm zs->M s xs->M s zs) ->
 (∀ {s: Nat} {a: k2 R} {rest: List (k2 R)} (save: Bool),M s (inv a :: g6 save a rest)->M (s+1) (a::rest)) ->
 (∀ {s: Nat} {a b: k2 R} {rest: List (k2 R)} (op ka kb: Bool),M s (w9 op a b :: g6 ka a (g6 kb b rest))->M (s+1) (a::b::rest)) ->
 M s ws
lemma Run.stop {R} {goal: k2 R}  : Run goal 0 [goal]:=fun M stop perm one two => @stop
lemma Run.perm {R} {goal: k2 R} {s: Nat} {xs zs: List (k2 R)} (h0: xs.Perm zs) (h1: Run goal s xs): Run goal s zs:=fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
lemma Run.one {R} {goal: k2 R} {s: Nat} {a: k2 R} {rest: List (k2 R)} (save: Bool) (h0: Run goal s (inv a :: g6 save a rest)): Run goal (s+1) (a::rest):=fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
lemma Run.two {R} {goal: k2 R} {s: Nat} {a b: k2 R} {rest: List (k2 R)} (op ka kb: Bool) (h0: Run goal s (w9 op a b :: g6 ka a (g6 kb b rest))): Run goal (s+1) (a::b::rest):=fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
lemma Run.induct {R} {goal: k2 R} {M: (Nat->List (k2 R)->Prop)} {s ws} (h: Run goal s ws)
 (stop: M 0 [goal])
 (perm: ∀ {s: Nat} {xs zs: List (k2 R)},xs.Perm zs->Run goal s xs->M s xs->M s zs)
 (one: ∀ {s: Nat} {a: k2 R} {rest: List (k2 R)} (save: Bool),Run goal s (inv a :: g6 save a rest)->M s (inv a :: g6 save a rest)->M (s+1) (a::rest))
 (two: ∀ {s: Nat} {a b: k2 R} {rest: List (k2 R)} (op ka kb: Bool),Run goal s (w9 op a b :: g6 ka a (g6 kb b rest))->M s (w9 op a b :: g6 ka a (g6 kb b rest))->M (s+1) (a::b::rest)): M s ws :=
 (h (fun s ws => Run goal s ws /\ M s ws)
 (⟨@Run.stop R goal  ,@stop  ⟩)
 (@fun s xs zs h0 h1 => ⟨@Run.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
 (@fun s a rest save h0 => ⟨@Run.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
 (@fun s a b rest op ka kb h0 => ⟨@Run.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
lemma Run.recurse {R} {goal: k2 R} {M: ∀ (s: Nat) (ws: List (k2 R)) (proof: Run goal s ws),Prop}
 (stop: M 0 [goal] (@Run.stop R goal  ))
 (perm: ∀ {s: Nat} {xs zs: List (k2 R)} (h0: xs.Perm zs) (h1: Run goal s xs) (ih: M s xs h1),M s zs (@Run.perm R goal s xs zs h0 h1))
 (one: ∀ {s: Nat} {a: k2 R} {rest: List (k2 R)} (save: Bool) (h0: Run goal s (inv a :: g6 save a rest)) (ih: M s (inv a :: g6 save a rest) h0),M (s+1) (a::rest) (@Run.one R goal s a rest save h0))
 (two: ∀ {s: Nat} {a b: k2 R} {rest: List (k2 R)} (op ka kb: Bool) (h0: Run goal s (w9 op a b :: g6 ka a (g6 kb b rest))) (ih: M s (w9 op a b :: g6 ka a (g6 kb b rest)) h0),M (s+1) (a::b::rest) (@Run.two R goal s a b rest op ka kb h0))
 {s ws} (h: Run goal s ws): M s ws h:=by
 have r:=Run.induct (M:=fun s ws => ∀ hh: Run goal s ws,M s ws hh) h
   (fun  _ => @stop  )
   (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
   (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
   (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
 exact r h
lemma m30 {R} (a: k2 R) (xs): mass (a::xs)=cost a+mass xs:=by
 simp [mass]
lemma m86 {R} (a: k2 R) (xs) (k: Bool): mass xs ≤ mass (g6 k a xs):=by
 cases k <;> simp [g6,m30]
lemma m75 {R} {a: k2 R} (h: v6 a): v6 (inv a):=by
 obtain ⟨v,rfl⟩:=h
 exact ⟨!v,rfl⟩
lemma m117 {R} {a b: k2 R} (op) (h: v6 a) (g: v6 b) :
   v6 (w9 op a b):=by
 obtain ⟨v,rfl⟩:=h
 obtain ⟨w,rfl⟩:=g
 cases op <;> exact ⟨_,rfl⟩
lemma m115 {R} (op) {a b: k2 R} {bank}
   (h: v6 a \/ v6 b) (ha: y1 bank a) (hb: y1 bank b) :
   y1 bank (w9 op a b):=by
 rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
 · cases op <;> cases v
   · exact Or.inr ⟨false,by funext x; simp [w9]⟩
   · simpa [w9] using hb
   · simpa [w9] using hb
   · exact Or.inr ⟨true,by funext x; simp [w9]⟩
 · cases op <;> cases v
   · exact Or.inr ⟨false,by funext x; simp [w9]⟩
   · simpa [w9] using ha
   · simpa [w9] using ha
   · exact Or.inr ⟨true,by funext x; simp [w9]⟩
lemma m36 {R} {bank v} (w: k2 R) (h: y1 bank v) :
   y1 (w::bank) v:=by
 exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
lemma z94 {R} (roots: List (k2 R)) {p bank a} (hp: q4 roots p bank)
   (ha: y1 bank a) :
   ∃ q next,q4 roots q next /\ y1 next (inv a) ∧
       (∀ v,y1 bank v->y1 next v) /\ q+cost a ≤ p+1+cost (inv a):=by
 classical
 by_cases c: v6 a
 · exact ⟨p,bank,hp,Or.inr (m75 c),fun _ h => h,by simp [cost,c,m75 c]⟩
 · exact ⟨p+1,_,q4.one hp ha,Or.inl (by simp),fun _ h => m36 _ h,by simp [cost,c]⟩
lemma z93 {R} (roots: List (k2 R)) {p bank a b} (op) (hp: q4 roots p bank)
   (ha: y1 bank a) (hb: y1 bank b) :
   ∃ q next,q4 roots q next /\ y1 next (w9 op a b) ∧
       (∀ v,y1 bank v->y1 next v) ∧
       q+cost a+cost b ≤ p+1+cost (w9 op a b):=by
 classical
 by_cases c: v6 a \/ v6 b
 · refine ⟨p,bank,hp,m115 op c ha hb,fun _ h => h,?_⟩
   by_cases ca: v6 a <;> by_cases cb: v6 b
   · simp [cost,ca,cb,m117 op ca cb]
   · simp [cost,ca,cb]
   · simp [cost,ca,cb]
   · exact False.elim (c.elim ca cb)
 · have ca: ¬v6 a:=fun h => c (Or.inl h)
   have cb: ¬v6 b:=fun h => c (Or.inr h)
   exact ⟨p+1,_,q4.two op hp ha hb,Or.inl (by simp),fun _ h => m36 _ h,
     by simp [cost,ca,cb]⟩
lemma v60 {α: Type} {k: Bool} {x a: α} {xs} (h: x ∈ g6 k a xs) :
   x=a \/ x∈xs:=by cases k <;> simp_all [g6]
lemma m150 {R} {goal: k2 R} (nc: ¬v6 goal) {s ws}
   (h: Run goal s ws) (roots: List (k2 R)) {p bank}
   (hp: q4 roots p bank) (hs: wd bank ws) :
   ∃ q next,q4 roots q next /\ y1 next goal /\ q+mass ws ≤ p+s:=by
 classical
 induction h using Run.recurse generalizing p bank with
 | stop =>
   exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
 | perm eq _ ih =>
   have hsub: wd bank _:=fun v hv => hs v (eq.mem_iff.mp hv)
   obtain ⟨q,W,hW,hv,hl⟩:=ih hp hsub
   exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
 | @one s a rest save _ ih =>
   obtain ⟨r,T,hT,hz,inc,le⟩:=z94 roots hp (hs a (by simp))
   have ht: wd T (inv a :: g6 save a rest):=by
     intro v h
     rcases List.mem_cons.mp h with rfl | hh
     · exact hz
     · exact inc v (hs v (List.mem_cons.mpr (v60 hh)))
   obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
   have hlen:=m86 a rest save
   rw [m30] at hl ⊢
   exact ⟨q,W,hW,hv,by omega⟩
 | @two s a b rest op ka kb _ ih =>
   obtain ⟨r,T,hT,hz,inc,le⟩:=z93 roots op hp (hs a (by simp)) (hs b (by simp))
   have ht: wd T (w9 op a b :: g6 ka a (g6 kb b rest)):=by
     intro v h
     rcases List.mem_cons.mp h with rfl | hh
     · exact hz
     · apply inc v
       apply hs
       rcases v60 hh with rfl | hh
       · simp
       · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (v60 hh))
   obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
   have hlen:=m86 a (g6 kb b rest) ka
   have hlen':=m86 b rest kb
   rw [m30] at hl
   refine ⟨q,W,hW,hv,?_⟩
   rw [m30,m30]
   omega
def z3 {R S: Type} (rows: S->R) (a: k2 R): k2 S :=
 fun r => a (rows r)
lemma m68 {R S: Type} (rows: S->R) (k: Bool) (a: k2 R) (ws) :
   (g6 k a ws).map (z3 rows) =
   g6 k (z3 rows a) (ws.map (z3 rows)):=by
 cases k <;> simp [g6]
lemma m121 {R S: Type} (rows: S->R) {goal s ws} (h: Run goal s ws) :
   Run (z3 rows goal) s (ws.map (z3 rows)):=by
 induction h using Run.recurse with
 | stop => exact Run.stop
 | perm p _ ih => exact Run.perm (p.map _) ih
 | one save _ ih =>
   simp only [List.map_cons,m68] at ih ⊢
   exact Run.one save ih
 | two op ka kb _ ih =>
   simp only [List.map_cons,m68] at ih ⊢
   cases op
   · exact Run.two false ka kb ih
   · exact Run.two true ka kb ih
lemma m29 {R S: Type} (rows: S->R) {goal s ws} (h: Run goal s ws)
   (nc: ¬v6 (z3 rows goal)) {roots: List (k2 S)} {p bank L}
   (hp: q4 roots p bank) (hs: wd bank (ws.map (z3 rows)))
   (hl: ∀ q bs,q4 roots q bs->y1 bs (z3 rows goal)->L ≤ q) :
   L+mass (ws.map (z3 rows)) ≤ p+s:=by
 obtain ⟨q,bs,hq,ht,hle⟩:=m150 nc (m121 rows h) roots hp hs
 have hqle:=hl q bs hq ht
 omega
abbrev Row:=Fin 512
def y2 (a: Sig): k2 Row:=fun r => bit r a
def zg (f: k2 Row): Sig :=
 (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
lemma m52 (f: k2 Row) (r: Row): bit r (zg f)=f r:=by
 simp only [bit,zg,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
lemma m18 (v: Sig): zg (y2 v)=v:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 exact m52 (y2 v) ⟨j,hj⟩
lemma m41 (f: k2 Row): y2 (zg f)=f:=by
 funext r
 exact m52 f r
lemma z10 (a: Sig): y2 (neg a)=inv (y2 a):=by
 funext r
 exact zz _ _
lemma z11 (d: Bool) (a b: Sig) :
   y2 (bin d a b)=w9 d (y2 a) (y2 b):=by
 funext r
 cases d <;> exact p0 _ _ _ _
lemma v59 {α β: Type} (f: α->β) (d: Bool) (a: α) (l: List α) :
   (g6 d a l).map f=g6 d (f a) (l.map f):=by cases d <;> rfl
lemma g8 {α: Type} (k: Bool) (a: α) (l: List α)
   (hn: l.Nodup) (ha: a ∉ l): (g6 k a l).Nodup:=by cases k <;> simp [g6,hn,ha]
lemma m28 (k: Bool) (a: Sig) (l: List Sig) :
   (g6 k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
 cases k <;> simp [g6]
lemma v58 {T: Sig} {k u S} (h: j6 T k u S) (v: List Sig)
   (hv: v.Nodup) (eqv: v.toFinset=S): Run (y2 T) k (v.map y2):=by
 classical
 induction h using j6.recurse generalizing v with
 | stop hp =>
   have eq: [T].Perm v:=by
     apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
     simpa [eqv]
   exact Run.perm (eq.map _) Run.stop
 | @unary k u U a ha fresh _ ih =>
   let rest:=(U.erase a).toList
   let save:=decide (a ∈ U)
   let tail:=g6 save a rest
   have er: rest.toFinset=U.erase a:=by simp [rest]
   have hm: a ∉ rest:=by simp [rest]
   have hr: rest.Nodup:=Finset.nodup_toList _
   have ht: tail.toFinset=U:=by
     rw [show tail=g6 save a rest by rfl,m28,er]
     by_cases hh: a ∈ U <;> simp [save,hh]
   have nd:=g8 save a rest hr hm
   have hf: neg a ∉ tail:=by
     intro hz
     exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
   have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
   rw [List.map_cons,v59,z10] at progress
   have perm: (a::rest).Perm v:=by
     apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
     simp [er,eqv]
   exact Run.perm (perm.map _) (Run.one save progress)
 | @binary k u U a b d ha hb hab fresh _ ih =>
   let rest:=((U.erase a).erase b).toList
   let ka:=decide (a ∈ U)
   let kb:=decide (b ∈ U)
   let mid:=g6 kb b rest
   let tail:=g6 ka a mid
   have er: rest.toFinset=(U.erase a).erase b:=by simp [rest]
   have ar: a ∉ rest:=by simp [rest]
   have br: b ∉ rest:=by simp [rest]
   have hr: rest.Nodup:=Finset.nodup_toList _
   have bm:=g8 kb b rest hr br
   have am: a ∉ mid:=by cases h: kb <;> simp [mid,g6,h,hab,ar]
   have nd:=g8 ka a mid bm am
   have ht: tail.toFinset=U:=by
     change (g6 ka a (g6 kb b rest)).toFinset=U
     rw [m28,m28,er]
     ext j
     by_cases aa: a ∈ U <;> by_cases bb: b ∈ U <;> by_cases aj: j=a <;>
       by_cases bj: j=b <;> simp_all [ka,kb]
   have hf: bin d a b ∉ tail:=by
     intro hz
     exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
   have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
   change Run _ _ ((bin d a b::g6 ka a (g6 kb b rest)).map y2) at progress
   rw [List.map_cons,v59,v59,z11] at progress
   have perm: (a::b::rest).Perm v:=by
     apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
     ext j
     by_cases ja: j=a <;> by_cases jb: j=b <;> simp_all [er]
   exact Run.perm (perm.map _) (Run.two d ka kb progress)
lemma y26 (f: k2 Row): zg (inv f)=neg (zg f):=by
 rw [←m18 (neg (zg f)),z10,m41]
lemma y27 (d: Bool) (f g: k2 Row) :
   zg (w9 d f g)=bin d (zg f) (zg g):=by
 rw [←m18 (bin d (zg f) (zg g)),z11,m41,m41]
lemma m21 {bank: List (k2 Row)} {a} (h: y1 bank a) :
   w1 (bank.map zg) (zg a):=by
 rcases h with hm | ⟨b,rfl⟩
 · exact Or.inl (List.mem_map_of_mem hm)
 · apply Or.inr
   cases b
   · have z: zg (fun _ => false)=zero:=by
       apply BitVec.eq_of_getLsbD_eq
       intro j hj
       exact (m52 _ ⟨j,hj⟩).trans (m15 ⟨j,hj⟩).symm
     exact fun hp => hp.1 z
   · have z: zg (fun _ => true)=one:=by
       apply BitVec.eq_of_getLsbD_eq
       intro j hj
       exact (m52 _ ⟨j,hj⟩).trans (xj ⟨j,hj⟩).symm
     exact fun hp => hp.2 z
lemma w10 {w a} (ha: w1 w a) :
   w1 w (neg a) \/ xz w (neg a):=by
 rcases m13 ha with rfl | rfl | ⟨hm,hp⟩
 · exact Or.inl (Or.inr fun h => h.2 m70.1)
 · exact Or.inl (Or.inr fun h => h.1 m70.2)
 · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
lemma m124 {w: List Sig} {z: Sig} {T k t S} (h: j6 T k t S)
   (hz: w1 w z \/ xz w z) (hs: ∀ a ∈ S,a ∈ z::w) :
   ∃ k' t' S',k' ≤ k+1 /\ j6 T k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
 apply y37 h hz
 intro a hm
 simpa [or_comm] using hs a hm
lemma m100 {roots: List (k2 Row)} {p bank}
   (h: q4 roots p bank) {T k t S} (run: j6 T k t S)
   (sub: ∀ a ∈ S,a ∈ bank.map zg) :
   ∃ l v U,l ≤ p+k /\ j6 T l v U /\ ∀ a ∈ U,a ∈ roots.map zg:=by
 induction h using q4.recurse generalizing k t S with
 | start => exact ⟨k,t,S,by omega,run,sub⟩
 | @one p bank a h ih ha =>
   rw [List.map_cons,y26] at sub
   obtain ⟨k',t',S',hk,run',sub'⟩:=m124 run (w10 (m21 ha)) sub
   obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
   exact ⟨l,v,U,by omega,hr,hs⟩
 | @two p bank a b d h ih ha hb =>
   rw [List.map_cons,y27] at sub
   obtain ⟨k',t',S',hk,run',sub'⟩:=m124 run (w38 d (m21 ha) (m21 hb)) sub
   obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
   exact ⟨l,v,U,by omega,hr,hs⟩
lemma m74 {roots: List Sig} {p bank T} (hp: x7 T)
   (h: q4 (roots.map y2) p bank) (hit: y1 bank (y2 T)) :
   ∃ k t S,k ≤ p /\ j6 T k t S /\ ∀ a ∈ S,a ∈ roots:=by
 have hm:=m21 hit
 rw [m18] at hm
 have mem:=hm.resolve_right (fun hn => hn hp)
 obtain ⟨l,v,U,hl,hr,hs⟩:=m100 h (j6.stop hp) (by simpa using mem)
 refine ⟨l,v,U,by omega,hr,?_⟩
 simpa [List.map_map,Function.comp_def,m18] using hs
lemma m31 {T k t S} (h: j6 T k t S) {r s: Row}
   (diff: bit r T≠bit s T): ∃ a ∈ S,bit r a≠bit s a:=by
 induction h using j6.recurse with
 | stop hp => exact ⟨_,by simp,diff⟩
 | @unary k t U a hp hf _ ih =>
   obtain ⟨v,hv,hd⟩:=ih
   rcases Finset.mem_insert.mp hv with rfl | hu
   · refine ⟨a,by simp,?_⟩
     exact fun he => hd (by rw [zz,zz,he])
   · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
 | @binary k t U a b d ha hb hab hf _ ih =>
   obtain ⟨v,hv,hd⟩:=ih
   rcases Finset.mem_insert.mp hv with rfl | hu
   · by_cases aeq: bit r a=bit s a
     · refine ⟨b,by simp,?_⟩
       intro beq
       exact hd (by rw [p0,p0,aeq,beq])
     · exact ⟨a,by simp,aeq⟩
   · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
lemma m32 {T k t S} (h: j6 T k t S) (roots: List Sig) (a: Sig)
   (sub: ∀ v ∈ S,v ∈ roots) (r s: Row) (diff: bit r T≠bit s T)
   (isolated: ∀ v ∈ roots,v≠a->bit r v=bit s v): a ∈ S:=by
 obtain ⟨v,hv,hd⟩:=m31 h diff
 by_cases veq: v=a
 · simpa [veq] using hv
 · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs: List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def d4: Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def y40: Sig:=0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def seed: Sig:=inputs.getD 0 zero ||| inputs.getD 4 zero
def p3 (r: Row) (j: Fin 9):=bit r (inputs.getD j.val zero)
def g5 (x: Fin 9->Bool): Bool :=
 (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
 (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
 (x 6&&x 8)||(x 8&&x 5)
lemma z95: ∀ r: Row,bit r d4=g5 (p3 r):=by decide +kernel
lemma m76: x7 d4:=by unfold x7; decide +kernel
lemma m38: List.ofFn (fun j: Fin 9 => inputs.getD j.val zero)=inputs:=rfl
lemma x69 (r: Row): List.ofFn (p3 r)=inputs.map (bit r):=by
 rw [←m38]
 rw [List.map_ofFn]
 rfl
def xd (i: Fin 9): Nat:=[4,2,1,2,0,0,1,2,3].getD i.val 0
def q8 (f: Row->Row) (a: Sig):=zg fun r => bit (f r) a
lemma m7 (f: Row->Row) (a: Sig) (r: Row) :
   bit r (q8 f a)=bit (f r) a:=m52 _ _
lemma m14 (f: Row->Row) (a: Sig) :
   y2 (q8 f a)=z3 f (y2 a):=by funext r; exact m7 f a r
lemma qq (f: Row->Row) (a: Sig): q8 f (neg a)=neg (q8 f a):=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 change bit ⟨j,hj⟩ (q8 f (neg a))=bit ⟨j,hj⟩ (neg (q8 f a))
 rw [m7,zz,zz,m7]
lemma qk (f: Row->Row) (d: Bool) (a b: Sig) :
   q8 f (bin d a b)=bin d (q8 f a) (q8 f b):=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 change bit ⟨j,hj⟩ (q8 f (bin d a b))=bit ⟨j,hj⟩ (bin d (q8 f a) (q8 f b))
 rw [m7,p0,p0,m7,m7]
lemma z66 (f: Row->Row) (onto: Function.Surjective f) :
   Function.Injective (q8 f):=by
 intro a b h
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 obtain ⟨r,hr⟩:=onto ⟨j,hj⟩
 have he:=congrArg (bit r) h
 change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
 rw [m7,m7,hr] at he
 exact he
lemma m79 (f: Row->Row): q8 f zero=zero /\ q8 f one=one:=by
 constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
 · exact (m7 f zero ⟨j,hj⟩).trans ((m15 _).trans (m15 ⟨j,hj⟩).symm)
 · exact (m7 f one ⟨j,hj⟩).trans ((xj _).trans (xj ⟨j,hj⟩).symm)
lemma m90 {T k t S} (h: j6 T k t S) (f: Row->Row) (onto: Function.Surjective f) :
   j6 (q8 f T) k t (S.image (q8 f)):=by
 have inj:=z66 f onto
 obtain ⟨fz,fo⟩:=m79 f
 have pp (v) (p: x7 v): x7 (q8 f v) :=
   ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
 induction h using j6.recurse with
 | stop hp => simpa using j6.stop (pp _ hp)
 | @unary k t U a hp hf _ ih =>
   have fresh: q8 f (neg a) ∉ (insert a U).image (q8 f):=by
     intro hm
     obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
     exact hf (inj eq ▸ hv)
   simp only [Finset.image_insert,qq] at fresh ih ⊢
   exact j6.unary (pp _ hp) fresh ih
 | @binary k t U a b d ha hb hab hf _ ih =>
   have fresh: q8 f (bin d a b) ∉ (insert a (insert b U)).image (q8 f):=by
     intro hm
     obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
     exact hf (inj eq ▸ hv)
   simp only [Finset.image_insert,qk] at fresh ih ⊢
   exact j6.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
lemma m63 {T k t S} (h: j6 T k t S) (none: t=0) {r s: Row}
   (pos: bit r T=true) (negRow: bit s T=false) :
   ∃ a ∈ S,bit r a=true /\ bit s a=false:=by
 induction h using j6.recurse with
 | stop hp => exact ⟨_,by simp,pos,negRow⟩
 | unary _ _ _ _ => omega
 | @binary k t U a b d ha hb hab hf _ ih =>
   obtain ⟨v,hv,hp,hn⟩:=ih none
   rcases Finset.mem_insert.mp hv with rfl | hu
   · rw [p0] at hp hn
     cases d <;> cases p: bit r a <;> cases q: bit s a <;>
       cases u: bit r b <;> cases z: bit s b <;> simp_all
   · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def k5 (roots: List Sig) (T: Sig) (L: Nat): Prop :=
 ∀ p bank,q4 (roots.map y2) p bank->y1 bank (y2 T)->L ≤ p
def x2 (T: Sig) (cap: Nat) (S: Finset Sig): Prop :=
 ∀ k t,k ≤ cap->¬j6 T k t S
def wy (T: Sig) (roots: List Sig) (a: Sig): Prop :=
 ∃ r s: Row,bit r T≠bit s T /\ ∀ v ∈ roots,v≠a->bit r v=bit s v
lemma m43 {roots T L} (hp: x7 T)
   (essential: ∀ a ∈ roots,wy T roots a)
   (noRun: x2 T L roots.toFinset): k5 roots T (L+1):=by
 intro p bank h ha
 obtain ⟨k,t,S,hk,run,hs⟩:=m74 hp h ha
 have he: roots.toFinset=S:=by
   ext a
   rw [List.mem_toFinset]
   refine ⟨fun hm => ?_,hs a⟩
   obtain ⟨r,s,hd,iso⟩:=essential _ hm
   exact m32 run roots a hs r s hd iso
 by_contra! small
 exact noRun k t (by omega) (he.symm ▸ run)
lemma m59 {v: Sig} (hv: x7 v): ¬v6 (y2 v):=by
 rintro ⟨b,h⟩
 have hr: w1 ([]: List Sig) v:=by
   have avail: y1 ([]: List (k2 Row)) (y2 v):=Or.inr ⟨b,h⟩
   simpa only [List.map_nil,m18] using m21 avail
 exact (hr.resolve_left (by simp)) hv
lemma m137 {R} (a b: List (k2 R)): mass (a++b)=mass a+mass b:=by
 simp [mass]
lemma m101 {R} (xs: List (k2 R)) (hc: ∀ x ∈ xs,v6 x) :
   mass xs=xs.length:=by
 induction xs with
 | nil => simp [mass]
 | cons a xs ih =>
   have ha:=hc a (by simp)
   simp only [m30,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
   omega
lemma m88 {roots other: List Sig} {T G: Sig} (pT: x7 T) (pG: x7 G)
   (r: Row->Row) (eq: q8 r T=G)
   (j0: ∀ a ∈ roots,y1 (other.map y2) (y2 (q8 r a)))
   (singles: Finset Sig) (necessary: ∀ a ∈ singles,wy T roots a)
   (constant: ∀ a ∈ singles,v6 (y2 (q8 r a)))
   (L: Nat) (prior: k5 other G L): k5 roots T (L+singles.card):=by
 classical
 intro p bank hh ha
 obtain ⟨k,t,S,hk,run,sub⟩:=m74 pT hh ha
 have subS: singles ⊆ S:=by
   intro a hs
   obtain ⟨i,j,hd,hiso⟩:=necessary a hs
   exact m32 run roots a sub i j hd hiso
 let front:=singles.toList ++ (S \ singles).toList
 have nd: front.Nodup:=by
   simp only [front,List.nodup_append]
   refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
   intro a ha b hb he
   subst b
   exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
 have fe: front.toFinset=S:=by ext a; simp [front,Finset.union_sdiff_of_subset subS]
 have run':=v58 run front nd fe
 have gc: z3 r (y2 T)=y2 G:=(m14 _ _).symm.trans (congrArg y2 eq)
 have supp: wd (other.map y2) ((front.map y2).map (z3 r)):=by
   intro v hv
   obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
   obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
   rw [←m14]
   exact j0 a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
 have bound:=m29 r run' (gc ▸ m59 pG) q4.start supp
   (L:=L) (gc ▸ prior)
 have massLo: singles.card ≤ mass ((front.map y2).map (z3 r)):=by
   simp only [front,List.map_append,m137]
   let xs:=(singles.toList.map y2).map (z3 r)
   have only: ∀ v ∈ xs,v6 v:=by
     intro v hv
     obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
     obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
     rw [←m14]
     exact constant _ (Finset.mem_toList.mp hmem)
   have sz:=m101 xs only
   simp only [xs,List.length_map,Finset.length_toList] at sz
   change singles.card ≤ mass xs+_
   rw [sz]
   omega
 omega
def k0 (ws: List Sig) (a: Sig) (keep: Bool): List Sig :=
 neg a :: g6 keep a (ws.erase a)
def w0 (ws: List Sig) (a b: Sig) (d ka kb: Bool): List Sig :=
 bin d a b :: g6 ka a (g6 kb b ((ws.erase a).erase b))
lemma m39 {l: List Sig} (h: l.Nodup) (a: Sig): (l.erase a).toFinset=l.toFinset.erase a:=by
 ext x
 simp [h.mem_erase_iff]
lemma y76 {T: Sig} {cap: Nat} {ws: List Sig} (hn: ws.Nodup) (out: T ∉ ws)
   (oneStep: ∀ a ∈ ws,∀ keep,neg a ∉ ws->x7 (neg a) ->
     (k0 ws a keep).length ≤ cap ->
     x2 T (cap-1) (k0 ws a keep).toFinset)
   (twoStep: ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b->bin d a b ∉ ws ->
     x7 (bin d a b)->(w0 ws a b d ka kb).length ≤ cap ->
     x2 T (cap-1) (w0 ws a b d ka kb).toFinset) :
   x2 T cap ws.toFinset:=by
 classical
 intro k t hk h
 generalize he: ws.toFinset=S at h
 induction h using j6.recurse with
 | stop hp =>
   have mem: T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _
   exact out (List.mem_toFinset.mp mem)
 | @unary k t U a ha hf tail _ =>
   have am: a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
   have fresh: neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
   have hz:=m22 tail _ (Finset.mem_insert_self _ _)
   let keep:=decide (a ∈ U)
   have er:=m39 hn a
   have rest: (g6 keep a (ws.erase a)).toFinset=U:=by
     rw [m28,er,he]
     by_cases hm: a ∈ U <;> simp [keep,hm]
   have nd: (k0 ws a keep).Nodup:=by
     have na: a ∉ ws.erase a:=hn.not_mem_erase
     have nk:=g8 keep a (ws.erase a) (hn.erase _) na
     refine List.nodup_cons.mpr ⟨?_,nk⟩
     intro h
     exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
   have eq: (k0 ws a keep).toFinset=insert (neg a) U:=by simp [k0,rest]
   have sc:=(m26 tail).2
   have len: (k0 ws a keep).length ≤ cap:=by
     rw [←List.toFinset_card_of_nodup nd,eq]
     omega
   exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
 | @binary k t U a b d ha hb hab hf tail _ =>
   have am: a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
   have bm: b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
   have fresh: bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
   have hz:=m22 tail _ (Finset.mem_insert_self _ _)
   let ka:=decide (a ∈ U)
   let kb:=decide (b ∈ U)
   let rest:=(ws.erase a).erase b
   have er: rest.toFinset=(ws.toFinset.erase a).erase b:=by
     rw [show rest=(ws.erase a).erase b by rfl,m39 (hn.erase _) b,
       m39 hn a]
   have ke: (g6 ka a (g6 kb b rest)).toFinset=U:=by
     rw [m28,m28,er,he]
     ext j
     by_cases aa: a ∈ U <;> by_cases bb: b ∈ U <;> by_cases ja: j=a <;>
       by_cases jb: j=b <;> simp_all [ka,kb]
   have rn: rest.Nodup:=(hn.erase _).erase _
   have ar: a ∉ rest:=fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
   have br: b ∉ rest:=(hn.erase a).not_mem_erase
   have nk:=g8 kb b rest rn br
   have ax: a ∉ g6 kb b rest:=by cases kb <;> simp [g6,ar,hab]
   have nd: (w0 ws a b d ka kb).Nodup:=by
     refine List.nodup_cons.mpr ⟨?_,g8 ka a _ nk ax⟩
     intro h
     exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
   have eq: (w0 ws a b d ka kb).toFinset=insert (bin d a b) U:=by
     change (bin d a b::g6 ka a (g6 kb b rest)).toFinset=_
     simp [ke]
   have sc:=(m26 tail).2
   have len: (w0 ws a b d ka kb).length ≤ cap:=by
     rw [←List.toFinset_card_of_nodup nd,eq]
     omega
   exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
def Sep (T: Sig) (width: Nat) (pos negRow: Fin width->Row)
   (asig: Sig->BitVec width × BitVec width): Prop :=
 (∀ i,bit (pos i) T=true /\ bit (negRow i) T=false) ∧
 ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
   (asig w).2.getLsbD i.val=bit (negRow i) w
def v8 {n} (oriented: Bool) (s: BitVec n × BitVec n): BitVec n :=
 if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def j0 {n} (oriented: Bool) (sig: Sig->BitVec n × BitVec n): List Sig->BitVec n
 | [] => 0
 | a::ws => v8 oriented (sig a) ||| j0 oriented sig ws
lemma m140 {n: Nat} {oriented: Bool} {sig: Sig->BitVec n × BitVec n} {ws: List Sig} {i: Fin n} :
   (j0 oriented sig ws).getLsbD i.val=true ↔
   ∃ a ∈ ws,(v8 oriented (sig a)).getLsbD i.val=true:=by
 induction ws with
 | nil => simp [j0]
 | cons a ws ih =>
   simp only [j0,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
lemma m96 {T k t S} (h: j6 T k t S) {ws: List Sig} (he: ws.toFinset=S)
   {width: Nat} {r s: Fin width->Row} {sig} (correct: Sep T width r s sig)
   (oriented: Bool) (zeroNot: oriented=true->t=0) :
   j0 oriented sig ws=BitVec.allOnes width:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 let i: Fin width:=⟨j,hj⟩
 have yes:=(correct.1 i).1
 have no:=(correct.1 i).2
 rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
 apply (m140 (i:=i)).mpr
 cases oriented with
 | false =>
   obtain ⟨a,ha,hd⟩:=m31 h (show bit (r i) T≠bit (s i) T by simp [yes,no])
   refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
   simp only [v8,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
   cases hx: bit (r i) a <;> cases hy: bit (s i) a <;> simp_all
 | true =>
   obtain ⟨a,ha,hp,hn⟩:=m63 h (zeroNot rfl) yes no
   refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
   simp only [v8,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
     Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
lemma m103 {T cap ws k t} (h: j6 T k t (List.toFinset ws))
   (hk: k ≤ cap) (hn: ws.Nodup) {n: Nat} {r s: Fin n->Row} {sig}
   (correct: Sep T n r s sig) :
   j0 (decide (ws.length=cap+1)) sig ws=BitVec.allOnes n:=by
 apply m96 h rfl correct
 intro hh
 have eq:=of_decide_eq_true hh
 have bound:=(m26 h).2
 rw [List.toFinset_card_of_nodup hn] at bound
 omega
def kp (raw: List Sig) (T d: Sig) (L: Nat): Prop :=
 ∃ (f: Row->Row) (roots: List Sig),(∀ r,bit (f r) d=true) ∧
   (∀ a ∈ raw,y1 (roots.map y2) (z3 f (y2 a))) ∧
   ¬v6 (z3 f (y2 T)) ∧
   ∀ p bank,q4 (roots.map y2) p bank->y1 bank (z3 f (y2 T))->L ≤ p
def j2 (d a: Sig):=a &&& d
def y8 (d: Sig) (pool: List Sig) (a: Sig) :=
 let m:=j2 d a
 m==zero||m==d||(pool.map (j2 d)).any (fun v => v==m)
lemma y41 {f: Row->Row} {d a b: Sig} (dom: ∀ r,bit (f r) d=true)
   (eq: j2 d a=j2 d b) :
   z3 f (y2 a)=z3 f (y2 b):=by
 funext r
 have h:=congrArg (bit (f r)) eq
 change bit (f r) a=bit (f r) b
 simpa only [bit,j2,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
   Bool.and_true] using h
lemma m87 {f: Row->Row} {d a: Sig} (dom: ∀ r,bit (f r) d=true)
   (eq: j2 d a=zero): z3 f (y2 a)=fun _ => false:=by
 funext r
 have he:=congrArg (bit (f r)) eq
 change bit (f r) a=false
 rw [m15] at he
 simpa only [bit,j2,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
   Bool.and_true] using he
lemma m106 {f: Row->Row} {d a: Sig} (dom: ∀ r,bit (f r) d=true)
   (eq: j2 d a=d): z3 f (y2 a)=fun _ => true:=by
 funext r
 have he:=congrArg (bit (f r)) eq
 change bit (f r) a=true
 rw [dom r] at he
 simpa only [bit,j2,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
   Bool.and_true] using he
def f8 (f: Row->Row) (bank: List (k2 Row)) (pool: List Sig) :=
 ∀ a ∈ pool,y1 bank (z3 f (y2 a))
lemma m6 {f: Row->Row} {d a: Sig} {bank pool}
   (dom: ∀ r,bit (f r) d=true) (supplyB: f8 f bank pool)
   (check: y8 d pool a=true): y1 bank (z3 f (y2 a)):=by
 simp only [y8,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
 rcases check with (hz | ho) | ⟨v,hv,he⟩
 · exact Or.inr ⟨false,m87 dom hz⟩
 · exact Or.inr ⟨true,m106 dom ho⟩
 · exact y41 dom he ▸ supplyB v hv
abbrev p7:=Nat × Sig × Sig
def y4 (c: p7) :=
 if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def c2 (d: Sig) (pool: List Sig) (c: p7) :=
 y8 d pool c.2.1&&(c.1==2||y8 d pool c.2.2)
lemma m104 {f: Row->Row} {d: Sig} {roots bank pool q}
   (dom: ∀ r,bit (f r) d=true) (hp: q4 roots q bank) (hs: f8 f bank pool)
   (c: p7) (valid: c2 d pool c=true) :
   ∃ next,q4 roots (q+1) next /\ f8 f next (y4 c :: pool):=by
 have ok: y8 d pool c.2.1=true /\ (c.1==2||y8 d pool c.2.2)=true:=by simpa only [c2,Bool.and_eq_true] using valid
 have ha:=m6 dom hs ok.1
 let z:=z3 f (y2 (y4 c))
 have hz: q4 roots (q+1) (z::bank):=by
   by_cases unary: c.1=2
   · change q4 _ _ (z3 f (y2 (y4 c)) :: _)
     rw [y4,if_pos unary,z10]
     exact q4.one hp ha
   · have hb: y8 d pool c.2.2=true:=by simpa [unary] using ok.2
     have hz':=q4.two (c.1==1) hp ha (m6 dom hs hb)
     change q4 _ _ (z3 f (y2 (y4 c)) :: _)
     rw [y4,if_neg unary,z11]
     have comm (b: Bool) (v w: k2 Row): z3 f (w9 b v w)=w9 b (z3 f v) (z3 f w):=by cases b <;> rfl
     rw [comm]
     exact hz'
 refine ⟨_,hz,?_⟩
 intro a hm
 rcases List.mem_cons.mp hm with rfl | hm
 · exact Or.inl (by simp [z])
 · exact m36 _ (hs _ hm)
def zp (d: Sig) (pool: List Sig): List p7->Option (List Sig)
 | [] => some pool
 | c::cs => if c2 d pool c then zp d (y4 c::pool) cs else none
lemma m61 {d: Sig} {f: Row->Row} (dom: ∀ r,bit (f r) d=true)
   {roots bank q pool} (hp: q4 roots q bank) (hs: f8 f bank pool)
   (cs: List p7) {result} (ok: zp d pool cs=some result) :
   ∃ next,q4 roots (q+cs.length) next /\ f8 f next result:=by
 induction cs generalizing bank q pool with
 | nil => cases ok; exact ⟨_,hp,hs⟩
 | cons c cs ih =>
   simp only [zp] at ok
   split at ok
   next h =>
     obtain ⟨next,hr,sh⟩:=m104 dom hp hs c h
     obtain ⟨out,hr',sh'⟩:=ih hr sh ok
     exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
   next => contradiction
def z4 (d a: Sig):=j2 d a==zero||j2 d a==d
lemma m49 {d: Sig} {f: Row->Row} (dom: ∀ r,bit (f r) d=true)
   (ws: List Sig): ws.countP (z4 d) ≤ mass ((ws.map y2).map (z3 f)):=by
 classical
 induction ws with
 | nil => simp [mass]
 | cons a ws ih =>
   simp only [List.countP_cons,List.map_cons,m30]
   cases h: z4 d a
   · simpa using (Nat.le_add_left _ _ |> ih.trans)
   · have hc: v6 (z3 f (y2 a)):=by
       have hh: j2 d a=zero \/ j2 d a=d:=by simpa only [z4,Bool.or_eq_true,beq_iff_eq] using h
       rcases hh with hz | ho
       · exact ⟨false,m87 dom hz⟩
       · exact ⟨true,m106 dom ho⟩
     simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def jp (d: Sig) (L k p: Nat) (pool ws: List Sig) :=
 decide (k+p < L+ws.countP (z4 d))&&ws.all (y8 d pool)
lemma m111 {raw T d L} (slice: kp raw T d L) (cs: List p7)
   {pool ws cap} (built: zp d raw cs=some pool)
   (nd: ws.Nodup) (cut: jp d L cap cs.length pool ws=true) :
   x2 T cap ws.toFinset:=by
 intro k t hk h
 obtain ⟨f,roots,dom,base,nc,lo⟩:=slice
 obtain ⟨bank,hr,hs⟩:=m61 dom (q4.start (roots:=roots.map y2)) base cs built
 simp only [jp,Bool.and_eq_true,decide_eq_true_eq] at cut
 obtain ⟨ineq,all⟩:=cut
 have coveredS: wd bank ((ws.map y2).map (z3 f)):=by
   intro v hv
   obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
   exact m6 dom hs (List.all_eq_true.mp all a ha)
 have b:=m29 f (v58 h ws nd rfl) nc hr coveredS lo
 have massLo:=m49 dom ws
 have hu:=ineq
 simp only [Nat.zero_add] at b
 omega
abbrev jg:=Sig × Sig × Row
def kz (d r: Row): Row :=
 if h: r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def jj (d: Row): Row:=Fin.ofNat 512 (512-d.val)
def jc (m: jg) (r: Row): Row :=
 if bit r m.1 then kz m.2.2 r else if bit r m.2.1 then kz (jj m.2.2) r else r
def mux (m a b: Sig):=(m &&& a) ||| (~~~m &&& b)
def qg (m: jg) (a: Sig) :=
 mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (jj m.2.2).val) a)
lemma y84 (d r: Row) (a: Sig): bit r (a.rotateRight d.val)=bit (kz d r) a:=by
 unfold bit
 rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
 by_cases h: r.val < 512-d.val <;> simp [kz,h,r.isLt]
lemma x46 (p x y: Bool): (p&&x||!p&&y)=(if p then x else y):=by cases p <;> simp
lemma w37 (r: Row) (m a b: Sig) :
   bit r (mux m a b)=if bit r m then bit r a else bit r b:=by
 simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
   decide_true,Bool.true_and]
 exact x46 _ _ _
lemma x51 (r: Row) (m: jg) (a: Sig): bit r (qg m a)=bit (jc m r) a:=by
 simp only [qg,w37,y84,jc]
 cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def q1 (ms: List jg) (r: Row):=ms.foldl (fun j m => jc m j) r
def y7 (ms: List jg) (a: Sig):=ms.foldr qg a
lemma m40 (ms: List jg) (a: Sig) (r: Row) :
   bit r (y7 ms a)=bit (q1 ms r) a:=by
 induction ms generalizing r with
 | nil => rfl
 | cons m ms ih => exact (x51 r m _).trans (ih _)
lemma m20 (ms: List jg) (a: Sig): y7 ms a=q8 (q1 ms) a:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 exact (m40 ms a ⟨j,hj⟩).trans (m7 _ _ ⟨j,hj⟩).symm
def kf (roots: List Sig) (w: Sig):=w==zero||w==one||roots.contains w
lemma m138 {roots w} (ok: kf roots w=true) :
   y1 (roots.map y2) (y2 w):=by
 simp only [kf,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
 rcases ok with (rfl | rfl) | hm
 · exact Or.inr ⟨false,funext m15⟩
 · exact Or.inr ⟨true,funext xj⟩
 · exact Or.inl (List.mem_map_of_mem hm)
def p4 (ms: List jg) (raw: List Sig) (T: Sig) (base: List Sig) (G: Sig) :=
 y7 ms T==G&&raw.all (fun a => kf base (y7 ms a))
lemma m64 {ms raw T base G} (ok: p4 ms raw T base G=true) :
   q8 (q1 ms) T=G ∧
   ∀ a ∈ raw,y1 (base.map y2) (y2 (q8 (q1 ms) a)):=by
 simp only [p4,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,m20] at ok
 exact ⟨ok.1,fun a ha => m138 (ok.2 a ha)⟩
lemma y44 {ms raw T base G L} (ok: p4 ms raw T base G=true)
   (pT: x7 T) (pG: x7 G) (hL: k5 base G L): k5 raw T L:=by
 obtain ⟨eq,supp⟩:=m64 ok
 simpa using m88 pT pG (q1 ms) eq supp ∅ (by simp) (by simp) L hL
lemma m110 {ms raw T base G L d} (ok: p4 ms raw T base G=true)
   (all: y7 ms d=one) (properG: x7 G) (hL: k5 base G L) :
   kp raw T d L:=by
 obtain ⟨eq,supp⟩:=m64 ok
 have obs: z3 (q1 ms) (y2 T)=y2 G :=
   (m14 _ _).symm.trans (congrArg y2 eq)
 refine ⟨q1 ms,base,?_,?_,?_,?_⟩
 · intro r
   rw [←m40,all,xj]
 · intro a ha
   rw [←m14]
   exact supp a ha
 · rw [obs]
   exact m59 properG
 · rw [obs]
   exact hL
def qf (T: Sig) (roots: List Sig) (a: Sig) (rs: Row × Row) :=
 (bit rs.1 T != bit rs.2 T) &&
 roots.all (fun w => w==a||bit rs.1 w==bit rs.2 w)
lemma m98 {T roots a rs} (ok: qf T roots a rs=true): wy T roots a:=by
 simp only [qf,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
 exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def k4 (T: Sig) (raw: List Sig) (xs: List (Sig × Row × Row)) :=
 xs.all (fun a => qf T raw a.1 a.2)
lemma m35 {T raw xs} (ok: k4 T raw xs=true) :
   ∀ a ∈ (xs.map Prod.fst).toFinset,wy T raw a:=by
 intro a ha
 obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
 exact m98 (List.all_eq_true.mp ok _ hm)
lemma m89 {raw T} (properT: x7 T) (xs: List (Sig × Row × Row))
   (ok: k4 T raw xs=true) :
   k5 raw T ((xs.map Prod.fst).toFinset.card-1):=by
 intro p bank hr hit
 obtain ⟨k,t,S,hk,run,sub⟩:=m74 properT hr hit
 have le: (xs.map Prod.fst).toFinset.card ≤ S.card:=by
   apply Finset.card_le_card
   intro a ha
   obtain ⟨r,s,hd,iso⟩:=m35 ok a ha
   exact m32 run raw a sub r s hd iso
 have bound:=(m26 run).2
 omega
def vp (ms: List jg) (T: Sig) (raw: List Sig) (base: List Sig) (G: Sig)
   (xs: List (Sig × Row × Row)) :=
 p4 ms raw T base G&&k4 T raw xs &&
   xs.all (fun a => y7 ms a.1==zero||y7 ms a.1==one)
lemma x97 {ms T raw base G xs L} (ok: vp ms T raw base G xs=true)
   (properT: x7 T) (properG: x7 G) (low: k5 base G L) :
   k5 raw T (L+(xs.map Prod.fst).toFinset.card):=by
 simp only [vp,Bool.and_eq_true] at ok
 obtain ⟨eq,supp⟩:=m64 ok.1.1
 apply m88 properT properG _ eq supp _ (m35 ok.1.2) _ L low
 intro a ha
 obtain ⟨⟨v,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
 have hh:=List.all_eq_true.mp ok.2 _ hm
 simp only [Bool.or_eq_true,beq_iff_eq,m20] at hh
 rcases hh with h | h
 · rw [h]
   exact ⟨false,funext m15⟩
 · rw [h]
   exact ⟨true,funext xj⟩
def xg (m: Nat): List (Nat × Sig) :=
 (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def f3 (m: Nat):=(xg m).map Prod.snd
def d1 (m j: Nat):=if m.testBit j then inputs.getD j zero else zero
def y0 (m: Nat): Sig :=
 let x:=d1 m
 (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
   (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
   (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def v76: Nat->Nat
 | 0 => 0xff
 | 1 => 0x55
 | 2 => 0x33
 | 3 => 0x11
 | 4 => 0xf
 | 5 => 0x5
 | 6 => 0x3
 | _ => 0x1
def v75: Nat->Nat
 | 0 => 0x101010101010101
 | 1 => 0x1000100010001
 | 2 => 0x10100000101
 | 3 => 0x100000001
 | 4 => 0x1010101
 | 5 => 0x10001
 | 6 => 0x101
 | _ => 0x1
def v74: Nat->Nat
 | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
 | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
 | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
 | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
 | 4 => 0x1000000000000000100000000000000010000000000000001
 | 5 => 0x100000000000000000000000000000001
 | 6 => 0x10000000000000001
 | _ => 0x1
def c7 (z o: Nat): Sig :=
 let fixed:=z ||| o
 if z &&& o != 0 then zero else
   BitVec.ofNat 512 ((v76 (fixed &&& 7)*v75 ((fixed >>> 3) &&& 7)*v74 ((fixed >>> 6) &&& 7)) <<< o)
def z33 (z o: Nat): List jg :=
 (List.range 9).filterMap fun j =>
   let x:=inputs.getD j zero
   let y28:=Fin.ofNat 512 (1 <<< j)
   if z.testBit j then some (zero,x,y28)
   else if o.testBit j then some (~~~x,zero,y28) else none
def f1 (v: Nat): jg :=
 let i:=v &&& 15
 let j:=v >>> 4
 let a:=inputs.getD i zero
 let b:=inputs.getD j zero
 let d:=(1 <<< j)-(1 <<< i)
 (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def wg (mask: Nat): List (Sig × Row × Row) :=
 (xg mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def zx (m hints: Nat): List (Sig × Row × Row) :=
 (xg m).map fun (i,a) =>
   let r:=1 <<< ((hints >>> (4*i)) &&& 15)
   (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def k7 (T: Sig):=T != zero&&T != one
lemma m19 (T: Sig) (h: k7 T=true): x7 T:=by
 simpa only [k7,x7,Bool.and_eq_true,bne_iff_ne] using h
def qh (m hints L: Nat) :=
 let xs:=zx m hints
 k7 (y0 m)&&k4 (y0 m) (f3 m) xs &&
   decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
lemma vj {m hints L} (h: qh m hints L=true) :
   k5 (f3 m) (y0 m) L:=by
 simp only [qh,Bool.and_eq_true,decide_eq_true_eq] at h
 intro p bank hr ha
 exact h.2.trans (m89 (m19 _ h.1.1) _ h.1.2 p bank hr ha)
abbrev w8:=Nat × Nat × Nat × Nat × Nat
def z37 (m z o: Nat):=m ^^^ (m &&& (z ||| o))
def g4 (m: Nat): Sig :=
 if m=1023 then y0 m &&& ~~~y40 else y0 m
def xb (m: Nat) (c: w8) (prior: Nat->Nat): Bool :=
 let (z,o,q,s,L):=c
 let ms:=z33 z o
 let free:=z37 m z o
 let G:=y7 ms (g4 m)
 let xs:=wg s
 let count:=(xs.map Prod.fst).toFinset.card
 k7 G&&p4 ms (f3 m) (g4 m) (f3 free) G &&
   (y7 ms (c7 z o)==one) &&
   (if q=0 then k4 G (f3 free) xs&&decide (L ≤ count-1)
    else k7 (y0 q) &&
      vp (z33 (z37 free q 0) 0) G (f3 free) (f3 q) (y0 q) xs &&
      decide (L ≤ prior q+count))
lemma m50 {m: Nat} (c: w8) (prior: Nat->Nat)
   (valid: ∀ q,k5 (f3 q) (y0 q) (prior q))
   (ok: xb m c prior=true): kp (f3 m) (g4 m) (c7 c.1 c.2.1) c.2.2.2.2:=by
 obtain ⟨z,o,q,s,L⟩:=c
 let ms:=z33 z o
 let free:=z37 m z o
 let G:=y7 ms (g4 m)
 let xs:=wg s
 change (((k7 G&&p4 ms (f3 m) (g4 m) (f3 free) G) &&
   (y7 ms (c7 z o)==one))&&_)=true at ok
 simp only [Bool.and_eq_true,beq_iff_eq] at ok
 apply m110 ok.1.1.2 ok.1.2 (m19 _ ok.1.1.1)
 intro p bank hr ha
 have hh:=ok.2
 by_cases hq: q=0
 · simp only [xb,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
   exact hh.2.trans (m89 (m19 _ ok.1.1.1) xs hh.1 p bank hr ha)
 · simp only [xb,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
   exact hh.2.trans (x97 hh.1.2 (m19 _ ok.1.1.1) (m19 _ hh.1.1) (valid q) p bank hr ha)
def vh (old rep: Nat) (swaps: List Nat) :=
 k7 (y0 old)&&k7 (y0 rep) &&
   p4 (swaps.map f1) (f3 old) (y0 old) (f3 rep) (y0 rep)
lemma z67 {old rep L swaps} (ok: vh old rep swaps=true)
   (h: k5 (f3 rep) (y0 rep) L): k5 (f3 old) (y0 old) L:=by
 simp only [vh,Bool.and_eq_true] at ok
 exact y44 ok.2 (m19 _ ok.1.1) (m19 _ ok.1.2) h
def q7 (entries: List (Nat × Nat)) (q: Nat) :=
 ((entries.find? (fun a => a.1==q)).map Prod.snd).getD 0
lemma m4 (entries: List (Nat × Nat))
   (sound: ∀ e ∈ entries,k5 (f3 e.1) (y0 e.1) e.2) (q: Nat) :
   k5 (f3 q) (y0 q) (q7 entries q):=by
 unfold q7
 cases h: entries.find? (fun a => a.1==q) with
 | none => exact fun _ _ _ _ => Nat.zero_le _
 | some e =>
   have he:=List.mem_of_find?_eq_some h
   have hit: (fun a: Nat × Nat => a.1==q) e=true:=List.find?_some (p:=fun a: Nat × Nat => a.1==q) (a:=e) h
   have eq: e.1=q:=beq_iff_eq.mp hit
   simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev w7:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev w7.domain (c: w7): Sig:=c.1
abbrev w7.bound (c: w7): Nat:=c.2.1
abbrev w7.paid (c: w7): Nat:=c.2.2.1
abbrev w7.wires (c: w7): List Sig:=c.2.2.2
def j5 (raw: List Sig) (T: Sig) (c: w7) :=
 ∃ (f: Row->Row) (roots: List Sig) (bank: List (k2 Row)),
   (∀ r,bit (f r) c.domain=true) /\ ¬v6 (z3 f (y2 T)) ∧
   (∀ q ws,q4 (roots.map y2) q ws->y1 ws (z3 f (y2 T))->c.bound ≤ q) ∧
   q4 (roots.map y2) c.paid bank /\ f8 f bank c.wires /\ True
lemma m152 {raw T d lb} (h: kp raw T d lb) (cs: List p7) {ws}
   (build: zp d raw cs=some ws): j5 raw T ⟨d,lb,cs.length,ws⟩:=by
 obtain ⟨f,roots,dom,sup,nc,prior⟩:=h
 obtain ⟨bank,hr,hs⟩:=m61 dom (q4.start (roots:=roots.map y2)) sup cs build
 exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩
lemma m109 {raw T c} (valid: j5 raw T c) (k: Nat) (rest: List Sig)
   (choice: p7) (paid: Bool)
   (known: ∀ a ∈ rest,y8 c.domain c.wires a=true)
   (buy: if paid then c2 c.domain c.wires choice=true
      else y8 c.domain c.wires (y4 choice)=true)
   (bound: k+c.paid+paid.toNat <
     c.bound+(y4 choice :: rest).countP (z4 c.domain))
   (nd: (y4 choice :: rest).Nodup) :
   x2 T k (y4 choice :: rest).toFinset:=by
 intro t num ht run
 obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:=valid
 let ws:=y4 choice::rest
 have done (n: Nat) (out: List (k2 Row)) (reach: q4 (roots.map y2) n out)
     (zs: f8 f out (y4 choice::rest)) (le: n=c.paid+paid.toNat): False:=by
   have j0: wd out ((ws.map y2).map (z3 f)):=by
     intro v hv
     obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
     obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
     exact zs _ ha
   have b:=m29 f (v58 run ws nd rfl) nc reach j0 lo
   have cm:=m49 dom ws
   change k+c.paid+paid.toNat < c.bound+ws.countP (z4 c.domain) at bound
   omega
 cases paid with
 | false =>
   apply done _ _ hp _ rfl
   intro a h
   rcases List.mem_cons.mp h with rfl | hm
   · exact m6 dom hs buy
   · exact m6 dom hs (known _ hm)
 | true =>
   obtain ⟨out,hr,hc⟩:=m104 dom hp hs choice buy
   apply done _ _ hr _ rfl
   intro a h
   rcases List.mem_cons.mp h with rfl | hm
   · exact hc _ (by simp)
   · have avail:=m6 dom hs (known _ hm)
     rcases avail with mem | con
     · have ha: y8 c.domain c.wires a=true:=known _ hm
       have point: ∀ u ∈ c.wires,y1 out (z3 f (y2 u)) :=
         fun u hu => hc u (List.mem_cons_of_mem _ hu)
       exact m6 dom point ha
     · exact Or.inr con
def v5 (c: w7) (k: Nat) (rest: List Sig) (op: p7) :=
 let z:=y4 op
 let extra:=!(y8 c.domain c.wires z)
 ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (z4 c.domain)) &&
   rest.all (y8 c.domain c.wires))&&(!extra||c2 c.domain c.wires op)
lemma m9 {raw T c} (valid: j5 raw T c) {k rest op}
   (nd: (y4 op::rest).Nodup) (cut: v5 c k rest op=true) :
   x2 T k (y4 op::rest).toFinset:=by
 let extra:=!(y8 c.domain c.wires (y4 op))
 apply m109 valid k rest op extra _ _ _ nd
 · simp only [v5,Bool.and_eq_true,List.all_eq_true] at cut
   exact cut.1.2
 · simp only [v5,Bool.and_eq_true,Bool.or_eq_true] at cut
   cases he: y8 c.domain c.wires (y4 op) <;> simp_all [extra]
 · simp only [v5,Bool.and_eq_true,decide_eq_true_eq] at cut
   exact cut.1.1
def xw (raw: List Sig) (cs: List p7) (d: Sig) (lb: Nat): Option w7 :=
 (zp d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
lemma m37 {raw T d L cs c} (slice: kp raw T d L)
   (h: xw raw cs d L=some c): j5 raw T c:=by
 unfold xw at h
 cases he: zp d raw cs with
 | none => simp [he,Option.map] at h
 | some pool =>
   rw [he] at h
   change some _=some c at h
   injection h with h
   subst c
   exact m152 slice cs he
abbrev h6:=BitVec 768
abbrev jz:=h6 × h6
abbrev y9:=Sig × jz
def c9 {n: Nat} (r: Fin n->Row) (v: Sig): BitVec n :=
 (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
lemma m8 {n: Nat} (r: Fin n->Row) (v: Sig) (i: Fin n) :
   (c9 r v).getLsbD i.val=bit (r i) v:=by
 simp only [c9,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
 simp [i.isLt]
def g7 (r s: Fin 768->Row) (a: Sig): jz:=(c9 r a,c9 s a)
def h7 (T: Sig) (r s: Fin 768->Row) :=
 ∀ i,bit (r i) T=true /\ bit (s i) T=false
lemma z50 {T r s} (h: h7 T r s): Sep T 768 r s (g7 r s):=by
 exact ⟨h,fun a i => ⟨m8 _ _ _,m8 _ _ _⟩⟩
def q2 (r s: Fin 768->Row) (x: y9):=x.2=g7 r s x.1
def x61 (x: y9): y9:=(neg x.1,~~~x.2.1,~~~x.2.2)
def x44 (d: Bool) (x y: y9): y9 :=
 if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
 else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
lemma z70 (r: Fin 768->Row) (a: Sig): c9 r (neg a)= ~~~c9 r a:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 have h:=m8 r (neg a) ⟨j,hj⟩
 rw [zz,←m8 r a ⟨j,hj⟩] at h
 simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
lemma z71 (r: Fin 768->Row) (d: Bool) (a b: Sig) :
   c9 r (bin d a b)=if d then c9 r a ||| c9 r b else c9 r a &&& c9 r b:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 have h:=m8 r (bin d a b) ⟨j,hj⟩
 rw [p0,←m8 r a ⟨j,hj⟩,←m8 r b ⟨j,hj⟩] at h
 cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
lemma m46 {r s x} (h: q2 r s x): q2 r s (x61 x):=by
 change x.2=_ at h
 simp only [q2,x61,g7,z70,h]
lemma m34 {r s x y} (d) (hx: q2 r s x) (hy: q2 r s y) :
   q2 r s (x44 d x y):=by
 change x.2=_ at hx
 change y.2=_ at hy
 cases d <;> simp only [q2,x44,Bool.false_eq_true,ite_false,ite_true,g7,z71,hx,hy]
def j4 (op: Nat) (x y: y9):=if op=2 then x61 x else x44 (op==1) x y
def y3: y9:=(zero,0,0)
lemma m80 (r s): q2 r s y3:=by
 apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
 · change (0: h6).getLsbD j=(c9 r zero).getLsbD j
   rw [show (c9 r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from m8 _ _ ⟨j,hj⟩,m15]
   simp
 · change (0: h6).getLsbD j=(c9 s zero).getLsbD j
   rw [show (c9 s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from m8 _ _ ⟨j,hj⟩,m15]
   simp
lemma m27 {r s ws} (all: ∀ v ∈ ws,q2 r s v) (i: Nat) :
   q2 r s (List.getD ws i y3):=by
 simp only [List.getD_eq_getElem?_getD]
 cases e: ws[i]? with
 | none => exact m80 _ _
 | some v => exact all _ (List.mem_of_getElem? e)
def c5 (n: Nat) (bits: Nat) (ws: List y9): List y9 :=
 match n with
 | 0 => ws
 | k+1 =>
   let a:=ws.getD (bits &&& 15) y3
   let b:=ws.getD ((bits >>> 4) &&& 15) y3
   c5 k (bits >>> 10) (ws++[j4 ((bits >>> 8) &&& 3) a b])
lemma m48 (n bits) (ws) (r s) (base: ∀ v ∈ ws,q2 r s v) :
   ∀ v ∈ c5 n bits ws,q2 r s v:=by
 induction n generalizing ws bits with
 | zero => exact base
 | succ n ih =>
   apply ih
   intro v hv
   rcases List.mem_append.mp hv with hw | hz
   · exact base _ hw
   · obtain rfl:=List.mem_singleton.mp hz
     unfold j4
     split
     · exact m46 (m27 base _)
     · exact m34 _ (m27 base _) (m27 base _)
def yx (cols: Nat->h6) (i: Fin 768): Row :=
 (BitVec.ofBoolListLE (List.ofFn (fun j: Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
   (by simp [List.length_ofFn])
lemma m149: ∀ r: Row,bit r (inputs.getD 0 zero)=r.val.testBit 0:=by decide +kernel
lemma m148: ∀ r: Row,bit r (inputs.getD 1 zero)=r.val.testBit 1:=by decide +kernel
lemma m147: ∀ r: Row,bit r (inputs.getD 2 zero)=r.val.testBit 2:=by decide +kernel
lemma m146: ∀ r: Row,bit r (inputs.getD 3 zero)=r.val.testBit 3:=by decide +kernel
lemma m145: ∀ r: Row,bit r (inputs.getD 4 zero)=r.val.testBit 4:=by decide +kernel
lemma m144: ∀ r: Row,bit r (inputs.getD 5 zero)=r.val.testBit 5:=by decide +kernel
lemma m143: ∀ r: Row,bit r (inputs.getD 6 zero)=r.val.testBit 6:=by decide +kernel
lemma m142: ∀ r: Row,bit r (inputs.getD 7 zero)=r.val.testBit 7:=by decide +kernel
lemma m141: ∀ r: Row,bit r (inputs.getD 8 zero)=r.val.testBit 8:=by decide +kernel
lemma m45: ∀ (j: Fin 9) (r: Row),
   bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by
 intro j r
 fin_cases j
 · exact m149 r
 · exact m148 r
 · exact m147 r
 · exact m146 r
 · exact m145 r
 · exact m144 r
 · exact m143 r
 · exact m142 r
 · exact m141 r
lemma m53 (cols: Nat->h6) (i: Fin 768) (j: Fin 9) :
   bit (yx cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
 rw [m45]
 change (BitVec.ofBoolListLE (List.ofFn (fun h: Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_
 simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
 simp [j.isLt]
def z49 (m: Nat) (p q: Nat->h6): List y9 :=
 (xg m).map (fun (j,a) => (a,p j,q j))
lemma m99 {m j a} (h: (j,a) ∈ xg m) :
   j<9 /\ a=inputs.getD j zero:=by
 obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h
 simp only [List.mem_range] at hv
 split at hh
 next =>
   cases hh
   exact ⟨hv,rfl⟩
 next => contradiction
lemma m122 (m) (p q: Nat->h6) :
   ∀ a ∈ z49 m p q,q2 (yx p) (yx q) a:=by
 intro a ha
 obtain ⟨⟨j,v⟩,hv,rfl⟩:=List.mem_map.mp ha
 obtain ⟨hj,rfl⟩:=m99 hv
 apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
 · exact (m53 p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (m8 _ _ ⟨i,hi⟩).symm
 · exact (m53 q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (m8 _ _ ⟨i,hi⟩).symm
def wp (m: Nat) (v: Nat->h6): h6 :=
 let x:=fun j => if m.testBit j then v j else 0
 (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
   (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
   (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
lemma z96 (m: Nat) (v: Nat->h6) (i: Fin 768) (j: Fin 9) :
   bit (yx v i) (d1 m j.val) =
   ((if m.testBit j.val then v j.val else 0): h6).getLsbD i.val:=by
 by_cases hh: m.testBit j.val=true
 · simpa [d1,hh] using m53 v i j
 · simp [d1,hh,m15]
lemma m77 (m: Nat) (v: Nat->h6) (i: Fin 768) :
   bit (yx v i) (y0 m)=(wp m v).getLsbD i.val:=by
 have pos (j: Nat) (hj: j<9): (d1 m j).getLsbD (yx v i).val=((if m.testBit j then v j else 0): h6).getLsbD i.val:=z96 m v i ⟨j,hj⟩
 simp only [bit,y0,wp,BitVec.getLsbD_and,BitVec.getLsbD_or]
 simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:=h6 × h6 × h6
def zh (z: h6) (c: Cov): Cov :=
 (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
  (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def q3 (d: Bool) (v: List y9): Cov :=
 v.foldr (fun a c => zh (v8 d a.2) c) (0,0,0)
def p8 (c: Cov) (a: h6): h6:=c.1 &&& ~~~(c.2.1 &&& a)
def wv (c: Cov) (a b: h6): h6 :=
 c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private lemma w26 (c: Cov) (a: h6): p8 (zh a c) a=c.1:=by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [p8,zh,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private lemma w25 (c: Cov) (a b: h6): wv (zh a (zh b c)) a b=c.1:=by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [wv,zh,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
   cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private lemma x53 (c: Cov) (a b: h6): zh a (zh b c)=zh b (zh a c):=by
 apply Prod.ext
 · apply BitVec.eq_of_getLsbD_eq
   intro i hi
   simp only [zh,BitVec.getLsbD_or]
   cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
 · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
     simp only [zh,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
     cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
     cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private lemma z57 (d: Bool) {l r: List y9} (h: l.Perm r): q3 d l=q3 d r:=by
 induction h with
 | nil => rfl
 | cons a _ ih => exact congrArg (zh (v8 d a.2)) ih
 | swap a b t => exact x53 _ _ _
 | trans _ _ h1 h2 => exact h1.trans h2
lemma z56 (d: Bool) (v: List y9) {r s} (good: ∀ a ∈ v,q2 r s a) :
   (q3 d v).1=j0 d (g7 r s) (v.map Prod.fst):=by
 induction v with
 | nil => rfl
 | cons a v ih =>
   change (v8 d a.2 ||| (q3 d v).1)=v8 d (g7 r s a.1) ||| _
   rw [show a.2=g7 r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def zv (ws: List y9) (a: y9) (keep: Bool) :=
 if keep then ws else ws.erase a
def jk (ws: List y9) (a b: y9) (ka kb: Bool) :=
 zv (zv ws a ka) b kb
lemma m65 {ws: List y9} (a: y9) (ha: a ∈ ws) :
   ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
lemma m97 {ws: List y9} (d: Bool) (a: y9) (ha: a ∈ ws) (keep: Bool) :
   (q3 d (zv ws a keep)).1 =
     (if keep then (q3 d ws).1 else p8 (q3 d ws) (v8 d a.2)):=by
 cases keep
 · change (q3 d (ws.erase a)).1=p8 (q3 d ws) _
   rw [z57 d (m65 a ha)]
   exact (w26 _ _).symm
 · rfl
lemma m139 {ws: List y9} (a b: y9) (ha: a ∈ ws) (hb: b ∈ ws) (hne: a≠b) :
   ws.Perm (a::b::(ws.erase a).erase b):=by
 have hm: b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
 exact (m65 a ha).trans (List.Perm.cons _ (m65 b hm))
lemma y81 {ws: List y9} (d: Bool) (a b: y9) (ha: a ∈ ws) (hb: b ∈ ws)
   (ne: a≠b) (ka kb: Bool) :
   (q3 d (jk ws a b ka kb)).1 =
     (if ka then (if kb then (q3 d ws).1 else p8 (q3 d ws) (v8 d b.2))
      else if kb then p8 (q3 d ws) (v8 d a.2)
      else wv (q3 d ws) (v8 d a.2) (v8 d b.2)):=by
 cases ka <;> cases kb
 · change (q3 d ((ws.erase a).erase b)).1=wv (q3 d ws) _ _
   rw [z57 d (m139 a b ha hb ne)]
   exact (w25 _ _ _).symm
 · exact m97 d a ha false
 · exact m97 d b hb false
 · rfl
def c8 (a b: List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
lemma m11 {xs ys} (h: c8 xs ys=true): xs.toFinset=ys.toFinset:=by
 simp only [c8,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
 ext a
 simp only [List.mem_toFinset]
 exact ⟨h.1 a,h.2 a⟩
def x98 (v: Sig) :=
 let n:=v.toNat % 2305843009213693951
 (n*(n+971)) % 2305843009213693951
def x59 (xs: List Sig):=xs.foldl (fun v x => v+x98 x) 0
def zk (pools: List w7) (links: Nat->List (List Sig)) (k: Nat)
   (rest: List Sig) (op: p7) :=
 let ws:=y4 op::rest
 (links (x59 ws)).any (c8 ws)||pools.any (fun p => v5 p k rest op)
lemma m81 {raw T pools links k rest op}
   (pValid: ∀ p ∈ pools,j5 raw T p)
   (lValid: ∀ tag xs,xs ∈ links tag->x2 T k (List.toFinset xs))
   (nd: (y4 op :: rest).Nodup)
   (h: zk pools links k rest op=true) :
   x2 T k (y4 op :: rest).toFinset:=by
 simp only [zk,Bool.or_eq_true,List.any_eq_true] at h
 rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
 · rw [m11 ok]
   exact lValid _ _ hx
 · exact m9 (pValid _ hp) nd ok
abbrev jy:=Cov × Cov
def zy (ws: List y9): jy:=(q3 false ws,q3 true ws)
def yq (c: jy) (d: Bool):=if d then c.2 else c.1
lemma z73 (ws) (d: Bool): yq (zy ws) d=q3 d ws:=by cases d <;> rfl
def p9 (v: Cov) (a b: h6) (un ka kb: Bool) :=
 if un then (if ka then v.1 else p8 v a) else
   if ka then (if kb then v.1 else p8 v b)
   else if kb then p8 v a else wv v a b
def g9 (un ka kb: Bool) (a b: y9) (ws: List y9) :=
 if un then zv ws a ka else jk ws a b ka kb
lemma m69 {ws: List y9} {a b: y9} (ha: a ∈ ws) (hb: b ∈ ws)
   (un ka kb d: Bool) (ne: un=false->a≠b) :
   (q3 d (g9 un ka kb a b ws)).1 =
     p9 (yq (zy ws) d) (v8 d a.2) (v8 d b.2) un ka kb:=by
 rw [z73]
 cases un
 · exact y81 d a b ha hb (ne rfl) ka kb
 · exact m97 d a ha ka
lemma m55 (ws: List y9) (a: y9) (k: Bool): (zv ws a k).Sublist ws:=by
 cases k
 · exact List.erase_sublist
 · exact List.Sublist.refl _
lemma m71 (ws: List y9) (a b: y9) (un ka kb: Bool) :
   (g9 un ka kb a b ws).Sublist ws:=by
 cases un
 · exact (m55 _ _ _).trans (m55 _ _ _)
 · exact m55 _ _ _
lemma z51 (ws: List y9) (a b: y9) (un ka kb: Bool) (ha: a ∈ ws) (hb: b ∈ ws)
   (ne: un=false->a≠b) :
   (g9 un ka kb a b ws).length =
     ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1):=by
 cases un
 · have hm: b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
   cases ka <;> cases kb <;> simp [g9,jk,zv,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
 · cases ka <;> cases kb <;> simp [g9,zv,List.length_erase_of_mem ha]
def z7 (op: Nat) (a b: y9):=j4 op a b
def x1 (op: Nat) (a b: y9): p7:=(op,a.1,b.1)
lemma m54 (op) (a b: y9) :
   (z7 op a b).1=y4 (x1 op a b):=by
 by_cases h: op=2
 · simp [z7,j4,h,x61,y4,x1]
 · cases hh: op==1 <;> simp [z7,j4,h,hh,x44,y4,x1]
lemma m60 {r s a b} (ha: q2 r s a) (hb: q2 r s b) (op: Nat) :
   q2 r s (z7 op a b):=by
 unfold z7 j4
 split
 · exact m46 ha
 · exact m34 _ ha hb
abbrev x6:=Nat × Nat × List y9 × jy × List w7 × (Nat->List (List Sig))
def d0 (c: x6) (op: Nat) (a b z: y9) (ka kb: Bool) :=
 let (cap,n,ws,cov,pools,links):=c
 let un:=op==2
 let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
 if len>cap then true else
   let d:=len==cap
   let rs:=p9 (yq cov d) (v8 d a.2) (v8 d b.2) un ka kb
   if (rs ||| v8 d z.2) != BitVec.allOnes 768 then true else
   if !k7 z.1||ws.any (fun v => v.1==z.1) then true else
     let rest:=(g9 un ka kb a b ws).map Prod.fst
     zk pools links (cap-1) rest (x1 op a b)
def k9 (ws: List y9) (op: Nat) (a b: y9) (ka kb: Bool) :=
 (z7 op a b).1 :: (g9 (op==2) ka kb a b ws).map Prod.fst
lemma m62 {raw T r s ws pools links cap a b op ka kb}
   (pairs: h7 T r s) (faith: ∀ w ∈ ws,q2 r s w)
   (nd: (ws.map Prod.fst).Nodup) (ha: a ∈ ws) (hb: b ∈ ws)
   (ne: (op==2)=false->a≠b) (hcap: 0<cap)
   (pv: ∀ p ∈ pools,j5 raw T p)
   (lv: ∀ tag xs,xs ∈ links tag->x2 T (cap-1) (List.toFinset xs))
   (pro: x7 (z7 op a b).1) (fresh: (z7 op a b).1 ∉ ws.map Prod.fst)
   (test: d0 (cap,ws.length,ws,zy ws,pools,links) op a b (z7 op a b) ka kb=true) :
   x2 T (cap-1) (k9 ws op a b ka kb).toFinset:=by
 let z:=z7 op a b
 let rest:=g9 (op==2) ka kb a b ws
 let child:=z.1 :: rest.map Prod.fst
 have sub: rest.Sublist ws:=m71 _ _ _ _ _ _
 have ndc: child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
   nd.sublist (sub.map _)⟩
 have fr: ws.any (fun v => v.1==z.1)=false:=by
   apply Bool.eq_false_iff.mpr
   intro hh
   obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
   exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
 have pp: k7 z.1=true:=by simpa [k7,x7] using pro
 have leq: 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
   change _=(z.1::rest.map Prod.fst).length
   rw [List.length_cons,List.length_map,z51 _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
 intro k t hk h
 have hsz:=(m26 h).2
 change child.toFinset.card+t ≤ k+1 at hsz
 rw [List.toFinset_card_of_nodup ndc] at hsz
 have len: child.length ≤ cap:=by omega
 unfold d0 at test
 change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
 rw [leq,if_neg (by omega)] at test
 have sep:=m103 h hk ndc (z50 pairs)
 have ce: cap-1+1=cap:=by omega
 rw [ce] at sep
 let d:=child.length==cap
 have g: (q3 d rest).1=j0 d (g7 r s) (rest.map Prod.fst) :=
   z56 _ _ (fun v hv => faith _ (sub.subset hv))
 have rz:=m69 ha hb (op==2) ka kb d ne
 have hf:=m60 (faith _ ha) (faith _ hb) op
 have deq: decide (child.length=cap)=(child.length==cap):=by by_cases he: child.length=cap <;> simp [he]
 change j0 (decide (child.length=cap)) (g7 r s) child=BitVec.allOnes 768 at sep
 rw [deq] at sep
 change v8 d (g7 r s z.1) ||| j0 d (g7 r s) (rest.map Prod.fst)=_ at sep
 change z.2=g7 r s z.1 at hf
 rw [←hf,←g,rz,BitVec.or_comm] at sep
 have be: ((p9 (yq (zy ws) d) (v8 d a.2) (v8 d b.2) (op==2) ka kb ||| v8 d z.2) != BitVec.allOnes 768)=false:=by simp [sep]
 change (if (_ != _) then true else if !k7 z.1||ws.any (fun v => v.1==z.1) then true else _)=true at test
 rw [be,pp,fr] at test
 have val:=m54 op a b
 change z.1=_ at val
 change j6 T k t child.toFinset at h
 have nd':=ndc
 change (z.1::rest.map Prod.fst).Nodup at nd'
 change j6 T k t (z.1::rest.map Prod.fst).toFinset at h
 rw [val] at nd' h
 exact m81 pv lv nd' test k t hk h
def d7 (ctx: x6) (a b: y9) (d: Bool) :=
 let op:=if d then 1 else 0
 let z:=z7 op a b
 let attempt:=d0 ctx op a b z
 attempt false false&&attempt true false&&attempt false true&&attempt true true
def qb (ctx: x6) (a: y9) (bs: List y9) :=
 let z:=z7 2 a a
 d0 ctx 2 a a z false false&&d0 ctx 2 a a z true true &&
   bs.all (fun b => d7 ctx a b false&&d7 ctx a b true)
def c6 (ctx: x6): List y9->Bool
 | [] => true
 | a::bs => qb ctx a bs&&c6 ctx bs
lemma y86 {ctx ws} (h: c6 ctx ws=true) {a: y9} (ha: a∈ws) (keep: Bool) :
   d0 ctx 2 a a (z7 2 a a) keep keep=true:=by
 induction ws with
 | nil => simp at ha
 | cons w ws ih =>
   simp only [c6,Bool.and_eq_true,qb] at h
   rcases List.mem_cons.mp ha with rfl | hm
   · cases keep
     · exact h.1.1.1
     · exact h.1.1.2
   · exact ih h.2 hm
lemma z97 {ctx ws} (h: c6 ctx ws=true) {a b: y9} (ha: a∈ws) (hb: b∈ws)
   (ne: a≠b) (d: Bool): d7 ctx a b d=true \/ d7 ctx b a d=true:=by
 induction ws with
 | nil => simp at ha
 | cons w ws ih =>
   simp only [c6,Bool.and_eq_true,qb,List.all_eq_true] at h
   rcases List.mem_cons.mp ha with rfl | haTail
   · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
     left
     cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
   · rcases List.mem_cons.mp hb with rfl | hbTail
     · right
       cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
     · exact ih h.2 haTail hbTail
lemma m135 {ctx a b d} (h: d7 ctx a b d=true) (ka kb: Bool) :
   d0 ctx (if d then 1 else 0) a b (z7 (if d then 1 else 0) a b) ka kb=true:=by
 simp only [d7,Bool.and_eq_true] at h
 cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
lemma m23 {v: List Sig} {w: Sig} (a: Sig) (k: Bool) :
   w ∈ g6 k a v↔(w=a /\ k=true) \/ w∈v:=by cases k <;> simp [g6]
lemma m105 {v: List y9} (nd: v.Nodup) (a w: y9) (k: Bool) :
   w ∈ zv v a k↔w∈v /\ (w≠a \/ k=true):=by
 cases k <;> simp [zv,nd.mem_erase_iff,and_comm]
lemma m44 {ws: List y9} (nd: (ws.map Prod.fst).Nodup) {a b: y9}
   (ha: a∈ws) (hb: b∈ws) (eq: a.1=b.1): a=b:=by
 induction ws with
 | nil => simp at ha
 | cons w ws ih =>
   obtain ⟨hn,ht⟩:=List.nodup_cons.mp nd
   rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
   · rfl
   · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
   · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
   · exact ih ht haTail hbTail
lemma m107 {ws: List y9} (nd: (ws.map Prod.fst).Nodup) {a b: y9}
   (ha: a ∈ ws) (hb: b ∈ ws) (un ka kb: Bool) (v: Sig) :
   v ∈ (g9 un ka kb a b ws).map Prod.fst ↔
   v ∈ ws.map Prod.fst /\ (v≠a.1 \/ ka=true) /\ (un=true \/ v≠b.1 \/ kb=true):=by
 have wn:=nd.of_map
 have dn:=wn.sublist (m55 ws a ka)
 cases un <;> simp only [g9,Bool.false_eq_true,ite_false,ite_true,jk,List.mem_map,
   m105 wn,m105 dn,or_false,false_or,true_or,and_true] <;> constructor
 all_goals
   first
   | rintro ⟨w,hw,rfl⟩
     first
     | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (m44 nd hw.1.1 ha eq)) id,
         hw.2.imp (fun ne eq => ne (m44 nd hw.1.1 hb eq)) id⟩
     | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (m44 nd hw.1 ha eq)) id⟩
   | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
     exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
       h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
   | rintro ⟨⟨w,hm,rfl⟩,h1⟩
     exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
lemma m83 {ws: List y9} (nd: (ws.map Prod.fst).Nodup) {a: y9} (ha: a∈ws)
   (keep: Bool) :
   (k9 ws 2 a a keep keep).toFinset=(k0 (ws.map Prod.fst) a.1 keep).toFinset:=by
 ext v
 simp only [k9,k0,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
   m107 nd ha ha,m23,nd.mem_erase_iff,z7,j4,x61,ite_true,
   Nat.reduceBEq,true_or,and_true]
 have av:=List.mem_map_of_mem (f:=Prod.fst) ha
 by_cases e: v=a.1 <;> cases keep <;> simp_all
lemma m78 {ws: List y9} (nd: (ws.map Prod.fst).Nodup) {a b: y9}
   (ha: a∈ws) (hb: b∈ws) (ne: a.1≠b.1) (d ka kb: Bool) :
   (k9 ws (if d then 1 else 0) a b ka kb).toFinset =
     (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
 ext v
 have av:=List.mem_map_of_mem (f:=Prod.fst) ha
 have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
 cases d <;> simp only [k9,w0,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
   m107 nd ha hb,m23,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,z7,j4,x44,
   Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
 all_goals by_cases va: v=a.1 <;> by_cases vb: v=b.1 <;> cases ka <;> cases kb <;> simp_all
lemma m73 (v: List Sig) (nd: v.Nodup) (a b: Sig) (d ka kb: Bool) :
   (w0 v a b d ka kb).toFinset=(w0 v b a d kb ka).toFinset:=by
 ext x
 simp only [w0,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
   m23,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,m24 d b a]
 tauto
lemma z72 {raw T r s ws pools links cap}
   (pairs: h7 T r s) (faith: ∀ w ∈ ws,q2 r s w)
   (nd: (ws.map Prod.fst).Nodup) (out: T ∉ ws.map Prod.fst)
   (pv: ∀ p ∈ pools,j5 raw T p)
   (lv: ∀ tag xs,xs ∈ links tag->x2 T (cap-1) (List.toFinset xs))
   (checks: c6 (cap,ws.length,ws,zy ws,pools,links) ws=true) :
   x2 T cap (ws.map Prod.fst).toFinset:=by
 by_cases hc: cap=0
 · intro k t hk h
   have ke: k=0:=by omega
   subst k
   generalize he: (ws.map Prod.fst).toFinset=S at h
   rw [h.zeroSet] at he
   exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
 have hc': 0<cap:=by omega
 apply y76 nd out
 · intro v hv keep fresh pro len
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
   have hf:=m83 nd ha keep
   rw [←hf]
   exact m62 pairs faith nd ha ha (by simp) hc' pv lv pro fresh (y86 checks ha keep)
 · intro a ha b hb d ka kb ne fresh pro len
   obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
   obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
   have ab: a≠b:=fun e => ne (congrArg Prod.fst e)
   have one (a b: y9) (aa: a∈ws) (bb: b∈ws) (ne': a.1≠b.1) (ka kb: Bool)
       (pr: x7 (bin d a.1 b.1)) (fr: bin d a.1 b.1 ∉ ws.map Prod.fst)
       (test: d7 (cap,ws.length,ws,zy ws,pools,links) a b d=true) :
       x2 T (cap-1) (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
     rw [←m78 nd aa bb ne']
     have eq: (z7 (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
     exact m62 pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
       (eq ▸ pr) (eq ▸ fr) (m135 test ka kb)
   rcases z97 checks haW hbW ab d with hh | hh
   · exact one a b haW hbW ne ka kb pro fresh hh
   · rw [m73 _ nd]
     exact one b a hbW haW (Ne.symm ne) kb ka (m24 d a.1 b.1 ▸ pro)
       (m24 d a.1 b.1 ▸ fresh) hh
lemma m134 (r s: Row) (h: ∀ a ∈ inputs,bit r a=bit s a): r=s:=by
 apply Fin.ext
 apply Nat.eq_of_testBit_eq
 intro j
 by_cases hj: j<9
 · let i: Fin 9:=⟨j,hj⟩
   have hm: inputs.getD i.val zero ∈ inputs:=by
     rw [← m38]
     exact List.mem_ofFn.mpr ⟨i,rfl⟩
   exact (m45 i r).symm.trans ((h _ hm).trans (m45 i s))
 · have le: 512 ≤ 2^j:=by
     change 2^9 ≤ 2^j
     exact Nat.pow_le_pow_right (by decide) (by omega)
   exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
     (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def wh (p q: List jg):=inputs.all (fun a => y7 p (y7 q a)==a)
lemma m42 {p q} (h: wh p q=true) (r: Row) :
   q1 q (q1 p r)=r:=by
 apply m134
 intro a ha
 rw [←m40,←m40]
 have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
 rw [eq]
def yp (T: Sig) (p: List jg) :=
 (y7 p T==T)&&wh p p.reverse&&wh p.reverse p
lemma m85 {T n} {ws: List Sig} (hi: x2 T n ws.toFinset)
   (p: List jg) (ok: yp T p=true): x2 T n (ws.map (y7 p.reverse)).toFinset:=by
 simp only [yp,Bool.and_eq_true,beq_iff_eq] at ok
 have onto: Function.Surjective (q1 p):=fun r => ⟨q1 p.reverse r,m42 ok.2 r⟩
 intro k t hk h
 have run:=m90 h (q1 p) onto
 have goal: q8 (q1 p) T=T:=(m20 p T).symm.trans ok.1.1
 have inv (x: Sig): q8 (q1 p) (y7 p.reverse x)=x:=by
   apply BitVec.eq_of_getLsbD_eq
   intro j hj
   change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
   rw [m7,m40,m42 ok.1.2]
 have back: (ws.map (y7 p.reverse)).toFinset.image (q8 (q1 p))=ws.toFinset:=by
   ext a
   simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
   constructor
   · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
     simpa only [inv] using hw
   · intro ha
     exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
 rw [goal,back] at run
 exact hi k t hk run
abbrev v4:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat->Nat)
def v2: v4:=(0,0,0,0,0,0,0,fun _ => 0)
def k3 (word: Nat->Nat) (pos len: Nat) :=
 let i:=pos/8192
 let shift:=pos % 8192
 let lo:=word i >>> shift
 if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
 else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def j8 (nb slots sw vw iw pw: Nat) (data: Nat->Nat) (h: Nat): Option (Nat × Nat) :=
 let a:=h % nb
 let sh:=k3 data (a*sw) sw
 let row:=(h/nb+sh)%slots
 let word:=k3 data (nb*sw+row*vw) vw
 if (word >>> (iw+pw))==h/(nb*slots)%16 then
   some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
 else none
def m2 (α: Type):=List α
def m2.leaf {α} (xs: List α): m2 α:=xs
def m2.fork {α} (_: Nat) (a b: m2 α): m2 α:=List.append a b
def m2.read {α} (tree: m2 α) (i: Nat):=(show List α from tree)[i]?
def m2.values {α} (tree: m2 α): List α:=tree
lemma m2.read_mem {α} (tree: m2 α) {i x} (e: tree.read i=some x) :
   x ∈ tree.values:=List.mem_of_getElem? e
def w3:=(Nat) × (Nat) × (Nat->h6 × h6) × (m2 w8) × (Array (List Nat)) × (Nat->v4) × (Nat->Nat->Option (Nat × Nat))
def w3.mask (c: w3): Nat:=c.1
def w3.cap (c: w3): Nat:=c.2.1
def w3.samples (c: w3): Nat->h6 × h6:=c.2.2.1
def w3.cols (c: w3): m2 w8:=c.2.2.2.1
def w3.autos (c: w3): Array (List Nat):=c.2.2.2.2.1
def w3.levels (c: w3): Nat->v4:=c.2.2.2.2.2.1
def w3.index (c: w3): Nat->Nat->Option (Nat × Nat):=c.2.2.2.2.2.2
def wx (g: w3) :=
 let ws:=z49 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
 let nonedge:=x61 (x44 false (ws.getD 0 y3) (ws.getD 1 y3))
 if g.mask=1023 then ws.map (fun w => x44 false w nonedge) else ws
lemma m57 (g: w3): ∀ a ∈ wx g,
   q2 (yx fun j => (g.samples j).1) (yx fun j => (g.samples j).2) a:=by
 have base:=m122 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
 intro a ha
 unfold wx at ha
 split at ha
 · obtain ⟨w,hw,rfl⟩:=List.mem_map.mp ha
   exact m34 false (base w hw) (m46 (m34 false
     (m27 base 0) (m27 base 1)))
 · exact base _ ha
def x0 (g: w3):=g4 g.mask
def g3 (m: Nat) (v: Nat->h6) :=
 if m=1023 then wp m v &&& ~~~(v 0 &&& v 1) else wp m v
lemma y82 (m: Nat) (v: Nat->h6) (i: Fin 768) :
   bit (yx v i) (g4 m)=(g3 m v).getLsbD i.val:=by
 by_cases e: m=1023
 · have u:=m53 v i (0: Fin 9)
   have w:=m53 v i (1: Fin 9)
   have h:=m77 m v i
   change (inputs.getD 0 zero).getLsbD (yx v i).val=(v 0).getLsbD i.val at u
   change (inputs.getD 1 zero).getLsbD (yx v i).val=(v 1).getLsbD i.val at w
   have seedEq: y40=inputs.getD 0 zero &&& inputs.getD 1 zero:=by decide +kernel
   simp only [g4,g3,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
     BitVec.getLsbD_not,(yx v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
   rw [h]
 · simpa only [g4,g3,e,ite_false] using m77 m v i
lemma m66 {m: Nat} {p q: Nat->h6}
   (hp: g3 m p=BitVec.allOnes 768) (hq: g3 m q=0) :
   h7 (g4 m) (yx p) (yx q):=by
 intro i
 simp only [y82,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
 simp
def k6 {α: Type} (bits: Nat): List α->List α
 | [] => []
 | w::ws => if bits &&& 1==1 then w::k6 (bits >>> 1) ws else k6 (bits >>> 1) ws
lemma m58 {α: Type} (bits: Nat) (ws: List α): (k6 bits ws).Sublist ws:=by
 induction ws generalizing bits with
 | nil => exact List.Sublist.slnil
 | cons a ws ih =>
   unfold k6
   split
   · exact List.Sublist.cons₂ _ (ih _)
   · exact List.Sublist.cons _ (ih _)
def xy (_g: w3) (depth: Nat):=depth
def kw (g: w3) (k i: Nat): Nat × List y9 × List y9 :=
 let raw:=wx g
 let (_,depth,_,_,_,_,_,data):=g.levels k
 let len:=10*xy g depth
 let width:=len+raw.length+depth
 let recp:=k3 data (i*width) width
 let stored:=recp &&& ((1 <<< len)-1)
 let ops:=stored
 let bank:=c5 depth ops raw
 (ops,bank,k6 (recp >>> len) bank)
def jq (x pos width: Nat):=(x >>> pos) &&& ((1 <<< width)-1)
def vc (bank: List y9) (ops paid: Nat): Nat->List p7
 | 0 => []
 | n+1 =>
   let more:=vc bank (ops >>> 10) (paid >>> 1) n
   if paid &&& 1==0 then more else
     (jq ops 8 2,(bank.getD (ops &&& 15) y3).1,
       (bank.getD (jq ops 4 4) y3).1) :: more
def yh (g: w3) (ops d: Nat) (bank: List y9) (idx paid: Nat): Option w7 :=
 (g.cols.read idx).bind fun ci =>
   xw (f3 g.mask) (vc bank ops paid d) (c7 ci.1 ci.2.1) ci.2.2.2.2
lemma m51 (g: w3)
   (cols: ∀ ci ∈ g.cols.values,kp (f3 g.mask) (x0 g) (c7 ci.1 ci.2.1) ci.2.2.2.2)
   {i ops depth bank paid c} (h: yh g ops depth bank i paid=some c) :
   j5 (f3 g.mask) (x0 g) c:=by
 unfold yh at h
 cases e: g.cols.read i with
 | none => simp [e] at h
 | some ci =>
   simp only [e,Option.bind_some] at h
   apply m37 _ h
   exact cols ci (g.cols.read_mem e)
def vv (data: Nat->Nat) (w v: Nat): Nat->Nat->List (Nat × Nat)
 | 0,_ => []
 | n+1,pos =>
   let x:=k3 data pos (w+v)
   (x &&& ((1 <<< w)-1),x >>> w) :: vv data w v n (pos+w+v)
def d9 (g: w3) (k i: Nat):=(kw g k i).2.2.map Prod.fst
def yw (g: w3) (k: Nat) (pair: Nat × Nat): Option (List Sig) :=
 if pair.1 ≥ (g.levels k).1 then none else
   (g.autos[pair.2]?).map fun perm => (d9 g k pair.1).map (y7 (perm.map f1).reverse)
lemma m91 (g: w3) (k: Nat)
   (names: ∀ x ∈ g.autos.toList,yp (x0 g) (x.map f1)=true)
   (earlier: ∀ i < (g.levels k).1,x2 (x0 g) k (d9 g k i).toFinset)
   {pair out} (h: yw g k pair=some out) :
   x2 (x0 g) k out.toFinset:=by
 unfold yw at h
 split at h
 · contradiction
 next valid =>
   cases e: g.autos[pair.2]? with
   | none => simp [e] at h
   | some perm =>
     simp only [e,Option.map_some,Option.some.injEq] at h
     subst out
     exact m85 (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def f5 (g: w3) (k i: Nat) :=
 let raw:=wx g
 let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
 let (ops,bank,ws):=kw g k i
 let values:=ws.map Prod.fst
 let start:=num*(10*xy g depth+raw.length+depth)
 let pos:=start+num*offw+k3 data (start+i*offw) offw
 let nr:=k3 data pos 5
 let nl:=k3 data (pos+5) lw
 let st:=pos+5+lw
 let rules:=(vv data cw depth nr st).filterMap (fun (a,b) => yh g ops depth bank a b)
 let ls:=fun tag => ((g.index k tag).bind (yw g (k-1))).toList
 decide values.Nodup&&!(values.contains (x0 g)) &&
   (if k=0 then true else c6 (k,ws.length,ws,zy ws,rules,ls) ws)
lemma m33 (g: w3) (k i: Nat)
   (samples: h7 (x0 g) (yx fun j => (g.samples j).1) (yx fun j => (g.samples j).2))
   (cols: ∀ ci ∈ g.cols.values,kp (f3 g.mask) (x0 g) (c7 ci.1 ci.2.1) ci.2.2.2.2)
   (names: ∀ x ∈ g.autos.toList,yp (x0 g) (x.map f1)=true)
   (prior: k>0->∀ j < (g.levels (k-1)).1,x2 (x0 g) (k-1) (d9 g (k-1) j).toFinset)
   (checked: f5 g k i=true): x2 (x0 g) k (d9 g k i).toFinset:=by
 simp only [f5,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
 have hN:=checked.1.1
 have hT: x0 g ∉ d9 g k i:=by simpa [d9] using checked.1.2
 by_cases h0: k=0
 · subst k
   intro t u lo h
   have ht: t=0:=by omega
   subst t
   generalize he: (d9 g 0 i).toFinset=S at h
   rw [h.zeroSet] at he
   exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
 apply z72 (raw:=f3 g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
 · intro v hv
   apply m48 _ _ _ _ _ (m57 g) v
   exact (m58 _ _).subset hv
 · intro p hp
   obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
   exact m51 g cols h
 · intro tag xs hx
   have e: ((g.index k tag).bind (yw g (k-1)))=some xs:=by simpa using hx
   obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
   exact m91 g _ names (prior (by omega)) h
def x5 (g: w3) (k start: Nat): Nat->Bool
 | 0 => true
 | n+1 => f5 g k (start+n)&&x5 g k start n
lemma z60 {g k start n} (h: x5 g k start n=true) (j: Nat) (lo: start≤j) (hi: j<start+n) :
   f5 g k j=true:=by
 induction n with
 | zero => omega
 | succ n ih =>
   simp only [x5,Bool.and_eq_true] at h
   by_cases eq: j=start+n
   · simpa [eq] using h.1
   · exact ih h.2 (by omega)
lemma m5 {g k start a b} (h: x5 g k start a=true)
   (h': x5 g k (start+a) b=true): x5 g k start (a+b)=true:=by
 induction b with
 | zero => simpa using h
 | succ b ih =>
   simp only [x5,Bool.and_eq_true] at h'
   simp only [Nat.add_succ,x5,Bool.and_eq_true]
   exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def k1 (g: w3) (top: Nat) :=
 ∀ k ≤ top,x5 g k 0 (g.levels k).1=true
def w5 (g: w3) (prior: Nat->Nat) :=
 (g3 g.mask (fun j => (g.samples j).1)==BitVec.allOnes 768) &&
 (g3 g.mask (fun j => (g.samples j).2)==0) &&
 g.cols.values.all (fun c => xb g.mask c prior) &&
 g.autos.toList.all (fun p => yp (x0 g) (p.map f1))
lemma z92 (g: w3) (top: Nat) (prior: Nat->Nat)
   (lower: ∀ q,k5 (f3 q) (y0 q) (prior q))
   (geometry: w5 g prior=true) (rows: k1 g top) :
   ∀ k ≤ top,∀ i < (g.levels k).1,x2 (x0 g) k (d9 g k i).toFinset:=by
 simp only [w5,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
 intro k
 induction k with
 | zero =>
   intro hk i hi
   apply m33 g 0 i (m66 geometry.1.1.1 geometry.1.1.2)
     (fun x hx => m50 _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
   exact z60 (rows 0 hk) i (by omega) (by omega)
 | succ k ih =>
   intro hk i hi
   apply m33 g _ i (m66 geometry.1.1.1 geometry.1.1.2)
     (fun x hx => m50 _ prior lower (geometry.1.2 x hx)) geometry.2
     (fun _ => by simpa using ih (by omega))
   exact z60 (rows _ hk) i (by omega) (by omega)
def xv (g: w3) (k i: Nat) (ws: List Sig) :=
 decide (i < (g.levels k).1)&&c8 (d9 g k i) ws
lemma z65 {g top prior k i ws} (low: ∀ q,k5 (f3 q) (y0 q) (prior q))
   (geom: w5 g prior=true) (blocks: k1 g top) (le: k ≤ top)
   (idx: xv g k i ws=true): x2 (x0 g) k ws.toFinset:=by
 simp only [xv,Bool.and_eq_true,decide_eq_true_eq] at idx
 rw [←m11 idx.2]
 exact z92 g top prior low geom blocks _ le i idx.1
lemma m17 {g prior i hints} (low: ∀ q,k5 (f3 q) (y0 q) (prior q))
   (geom: w5 g prior=true) (blocks: k1 g g.cap)
   (idx: xv g g.cap i (f3 g.mask)=true) (hp: k7 (x0 g)=true)
   (ess: k4 (x0 g) (f3 g.mask) (zx g.mask hints)=true)
   (all: (zx g.mask hints).map Prod.fst=f3 g.mask) :
   k5 (f3 g.mask) (x0 g) (g.cap+1):=by
 apply m43 (m19 _ hp) _ (z65 low geom blocks (Nat.le_refl _) idx)
 intro a ha
 apply m35 ess a
 rw [all]
 exact List.mem_toFinset.mpr ha
lemma m10 {g prior ci hints} (low: ∀ q,k5 (f3 q) (y0 q) (prior q))
   (ok: xb g.mask ci prior=true)
   (hp: k7 (x0 g)=true)
   (ess: k4 (x0 g) (f3 g.mask) (zx g.mask hints)=true)
   (all: (zx g.mask hints).map Prod.fst=f3 g.mask)
   (nd: (f3 g.mask).Nodup)
   (cut: jp (c7 ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (f3 g.mask) (f3 g.mask)=true) :
   k5 (f3 g.mask) (x0 g) (g.cap+1):=by
 apply m43 (m19 _ hp) _ (m111 (m50 ci prior low ok) [] rfl nd cut)
 intro a ha
 apply m35 ess a
 rw [all]
 exact List.mem_toFinset.mpr ha
def p2 (entries: List (Nat × Nat)):=∀ e ∈ entries,k5 (f3 e.1) (y0 e.1) e.2
def w2 (old: List (Nat × Nat)) (L: Nat) (relabels: List (Nat × List Nat)) :=
 relabels.map (fun v => (v.1,L)) ++ old
lemma m0 {old L m relabels} (previous: p2 old)
   (main: k5 (f3 m) (y0 m) L)
   (ok: relabels.all (fun v => vh v.1 m v.2)=true) :
   p2 (w2 old L relabels):=by
 intro e he
 rcases List.mem_append.mp he with hx | h
 · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
   exact z67 (List.all_eq_true.mp ok _ hv) main
 · exact previous e h
lemma y85: p2 []:=by simp [p2]
def q5 (v: Nat) (upper: Nat):=2^769*upper+v
def z9 {α: Type} (f: α->h6): List α->Nat
 | [] => 0
 | x::xs => q5 (f x).toNat (z9 f xs)
def ww: Nat->Nat
 | 0 => 0
 | n+1 => q5 1 (ww n)
lemma m95 (x: h6): x.toNat < 2^769 :=
 lt_trans x.isLt (by decide +kernel)
lemma y39 (a b: h6) (u v: Nat) :
   q5 a.toNat u &&& q5 b.toNat v=q5 (a &&& b).toNat (u &&& v):=by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [q5,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (m95 _)]
 by_cases h: i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
lemma x24 (a b: h6) (u v: Nat) :
   q5 a.toNat u ||| q5 b.toNat v=q5 (a ||| b).toNat (u ||| v):=by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [q5,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (m95 _)]
 by_cases h: i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
lemma y38 (a b: h6) (u v: Nat) :
   q5 a.toNat u ^^^ q5 b.toNat v=q5 (a ^^^ b).toNat (u ^^^ v):=by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [q5,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (m95 _)]
 by_cases h: i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
lemma m93 {α} (f g: α->h6) (xs) :
   z9 f xs &&& z9 g xs=z9 (fun x => f x &&& g x) xs:=by
 induction xs with
 | nil => simp [z9]
 | cons a xs ih => simp only [z9,y39,ih]
lemma m82 {α} (f g: α->h6) (xs) :
   z9 f xs ||| z9 g xs=z9 (fun x => f x ||| g x) xs:=by
 induction xs with
 | nil => simp [z9]
 | cons a xs ih => simp only [z9,x24,ih]
lemma m92 {α} (f g: α->h6) (xs) :
   z9 f xs ^^^ z9 g xs=z9 (fun x => f x ^^^ g x) xs:=by
 induction xs with
 | nil => simp [z9]
 | cons a xs ih => simp only [z9,y38,ih]
lemma y83 {α} (a: h6) (xs: List α) :
   ww xs.length*a.toNat=z9 (fun _ => a) xs:=by
 induction xs with
 | nil => simp [ww,z9]
 | cons v xs ih => simp only [List.length_cons,ww,z9,q5,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def zw (r packed: Nat):=((packed+r) >>> 768) &&& r
lemma y89 (n i: Nat) (hi: i<n): (ww n).testBit (769*i)=true:=by
 induction n generalizing i with
 | zero => omega
 | succ n ih =>
   rw [ww,q5,Nat.testBit_two_pow_mul_add _ (by decide +kernel: 1 < 2^769)]
   cases i with
   | zero => simp
   | succ i =>
     have di: 769*(i+1)-769=769*i:=by omega
     have ge: ¬769*(i+1)<769:=by omega
     simp only [ge,ite_false,di]
     exact ih _ (by omega)
set_option maxRecDepth 8192 in
lemma x32 (a: h6): (a.toNat+1).testBit 768=(a==BitVec.allOnes 768):=by
 by_cases h: a=BitVec.allOnes 768
 · subst a
   decide +kernel
 · have lim:=a.isLt
   have ne: a.toNat≠2^768-1:=by
     intro eq
     apply h
     apply BitVec.eq_of_toNat_eq
     simpa only [BitVec.toNat_allOnes] using eq
   have lt: a.toNat+1<2^768:=by omega
   rw [Nat.testBit_eq_false_of_lt lt]
   exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
lemma y42 {α} (f: α->h6) (xs: List α) (i: Nat) (hi: i<xs.length) :
   (zw (ww xs.length) (z9 f xs)).testBit (769*i) =
     (f xs[i]==BitVec.allOnes 768):=by
 simp only [zw,Nat.testBit_and,Nat.testBit_shiftRight,y89 _ _ hi,Bool.and_true]
 induction xs generalizing i with
 | nil => simp at hi
 | cons a xs ih =>
   simp only [z9,List.length_cons,ww,q5]
   have sum (u v x: Nat): 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
   rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt; omega)]
   have hi': i < xs.length+1:=hi
   cases i with
   | zero => simpa using x32 (f a)
   | succ i =>
     have ge: ¬769*(i+1)+768<769:=by omega
     have di: 769*(i+1)+768-769=769*i+768:=by omega
     simp only [ge,ite_false,di,List.getElem_cons_succ]
     apply ih i (by omega)
abbrev yg:=Nat × Nat
abbrev wz:=Nat × Nat × Nat
def h8 {α} (s: α->jz) (xs: List α): yg :=
 (z9 (fun x => (s x).1) xs,z9 (fun x => (s x).2) xs)
def j3 {α} (c: α->Cov) (xs: List α): wz :=
 (z9 (fun x => (c x).1) xs,z9 (fun x => (c x).2.1) xs,
  z9 (fun x => (c x).2.2) xs)
def v1 (d: Bool) (a: yg) :=
 if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
lemma z38 (a b: h6): a ^^^ (a &&& b)=a &&& ~~~b:=by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
lemma m12 {α} (s: α->jz) (xs: List α) (d: Bool) :
   v1 d (h8 s xs)=z9 (fun x => v8 d (s x)) xs:=by
 cases d <;> simp only [v1,h8,v8,Bool.false_eq_true,ite_false,ite_true,m93,m92,z38]
def zd (full: Nat) (op: Nat) (a b: yg): yg :=
 if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
 else (a.1 &&& b.1,a.2 &&& b.2)
lemma x68 (a: h6): BitVec.allOnes 768 ^^^ a= ~~~a:=BitVec.allOnes_xor
lemma m125 {α} (a b: α->y9) (xs: List α) (op: Nat) :
   zd (ww xs.length*(BitVec.allOnes 768).toNat) op
     (h8 (fun x => (a x).2) xs) (h8 (fun x => (b x).2) xs) =
   h8 (fun x => (z7 op (a x) (b x)).2) xs:=by
 by_cases un: op=2
 · simp only [zd,un,ite_true,h8,y83,m92,x68,z7,j4,x61]
 · by_cases one: op=1 <;> simp [zd,un,one,h8,m82,m93,z7,j4,x44]
def c4 (c: wz) (a b: Nat) (un ka kb: Bool) :=
 let without1:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
 let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
 if un then (if ka then c.1 else without1 a)
 else if ka then (if kb then c.1 else without1 b)
 else if kb then without1 a else without2
lemma m67 {α} (c: α->Cov) (a b: α->h6) (xs: List α) (un ka kb: Bool) :
   c4 (j3 c xs) (z9 a xs) (z9 b xs) un ka kb =
   z9 (fun x => p9 (c x) (a x) (b x) un ka kb) xs:=by
 cases un <;> cases ka <;> cases kb <;>
   simp only [c4,j3,m93,m82,m92,z38,p9,p8,wv,
     Bool.false_eq_true,ite_false,ite_true]
def y5 (c: x6) (i: Nat):=c.2.2.1.getD i y3
def xk (c: x6) (i j op: Nat) (ka kb: Bool) :=
 let a:=y5 c i
 let b:=y5 c j
 d0 c op a b (z7 op a b) ka kb
def vd (c: x6) (d un ka kb: Bool) (op i j: Nat) :=
 let a:=y5 c i
 let b:=y5 c j
 p9 (yq c.2.2.2.1 d) (v8 d a.2) (v8 d b.2) un ka kb |||
   v8 d (z7 op a b).2
def xx {α: Type} (f: α->Bool) (mask: Nat): List α->Bool
 | [] => true
 | x::xs => if mask=0 then true else
   ((mask &&& 1==0)||f x)&&xx f (mask >>> 769) xs
lemma m126 {α} (f: α->Bool) (mask: Nat) (xs: List α) (i: Nat) (hi: i<xs.length)
   (bitOn: mask.testBit (769*i)=true) (ok: xx f mask xs=true): f xs[i]=true:=by
 induction xs generalizing mask i with
 | nil => simp at hi
 | cons x xs ih =>
   have ne: mask≠0:=by intro e; simp [e] at bitOn
   simp only [xx,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
   cases i with
   | zero =>
     have nonzero: mask &&& 1≠0:=by
       intro he
       have at0:=congrArg (fun n: Nat => n.testBit 0) he
       simp only [Nat.testBit_and] at at0
       change mask.testBit 0=true at bitOn
       simp [bitOn] at at0
     exact ok.1.resolve_left nonzero
   | succ i =>
     apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
     simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev qy:=Nat × Nat × Nat × List yg × wz × wz
def g2 (k n: Nat) (xs: List x6): qy :=
 (k,n,ww xs.length,(List.range n).map (fun i => h8 (fun c => (y5 c i).2) xs),
   j3 (fun c => c.2.2.2.1.1) xs,j3 (fun c => c.2.2.2.1.2) xs)
def f2 (b: qy) (i: Nat):=b.2.2.2.1.getD i (0,0)
lemma m94 (k n) (xs) {i: Nat} (h: i<n) :
   f2 (g2 k n xs) i=h8 (fun c => (y5 c i).2) xs:=by
 simp [f2,g2,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def qz (p: w7) (m: Sig) :=
 m==zero||m==p.domain||(p.wires.map (j2 p.domain)).any (fun v => v==m)
lemma m25 (p: w7) (x: Sig) :
   y8 p.domain p.wires x=qz p (j2 p.domain x):=rfl
def w6 (p: y9->Bool) (a: y9) (keep: Bool) :=
 if keep then 0 else (p a).toNat
lemma m127 (p: y9->Bool) (ws: List y9) (a: y9) (keep: Bool) :
   ws.countP p ≤ (zv ws a keep).countP p+w6 p a keep:=by
 cases keep
 · simp only [zv,Bool.false_eq_true,ite_false,w6,List.countP_erase]
   split
   next h => simp [h.2]; omega
   next => omega
 · simp [zv,w6]
lemma jw (p: y9->Bool) (ws: List y9) (a b: y9) (un ka kb: Bool) :
   ws.countP p - w6 p a ka - w6 p b (un||kb) ≤
   (g9 un ka kb a b ws).countP p:=by
 have h1:=m127 p ws a ka
 have h2:=m127 p (zv ws a ka) b kb
 cases un <;> simp only [g9,jk,Bool.false_eq_true,ite_false,ite_true,
   Bool.false_or,Bool.true_or] <;> first | omega | simp [w6]; omega
abbrev jh:=w7 × Nat × Bool
def d8 (ws: List y9) (p: w7): jh :=
 (p,ws.countP (fun w => z4 p.domain w.1),
    ws.all (fun w => y8 p.domain p.wires w.1))
def vq (s: jh) (k: Nat) (a b: y9) (op: Nat) (ka kb: Bool) :=
 if !s.2.2 then false else
 let p:=s.1
 let un:=op==2
 let const:=fun w: y9 => z4 p.domain w.1
 let z:=y4 (x1 op a b)
 let zm:=j2 p.domain z
 let zc:=z4 p.domain z
 let cm:=s.2.1 - w6 const a ka - w6 const b (un||kb)+zc.toNat
 let free:=zc||zm==j2 p.domain a.1||zm==j2 p.domain b.1
 decide (k+p.paid+(!free).toNat < p.bound+cm)
lemma m72 {p k ws a b op ka kb} (ha: a∈ws) (hb: b∈ws)
   (h: vq (d8 ws p) k a b op ka kb=true) :
   v5 p k ((g9 (op==2) ka kb a b ws).map Prod.fst) (x1 op a b)=true:=by
 let z:=y4 (x1 op a b)
 let const:=fun w: y9 => z4 p.domain w.1
 let free:=z4 p.domain z||j2 p.domain z==j2 p.domain a.1 ||
     j2 p.domain z==j2 p.domain b.1
 let rest:=g9 (op==2) ka kb a b ws
 have ck:=jw const ws a b (op==2) ka kb
 change ws.countP const - w6 const a ka - w6 const b ((op==2)||kb) ≤ rest.countP const at ck
 by_cases all: ws.all (fun w => y8 p.domain p.wires w.1)=true
 · have hav:=List.all_eq_true.mp all
   have ready: free=true->y8 p.domain p.wires z=true:=by
     intro f
     simp only [free,Bool.or_eq_true,beq_iff_eq] at f
     rcases f with (zc|za)|zb
     · simp only [y8,z4,Bool.or_eq_true] at zc ⊢
       exact Or.inl zc
     · rw [m25,za,←m25]
       exact hav _ ha
     · rw [m25,zb,←m25]
       exact hav _ hb
   have extra: (!y8 p.domain p.wires z).toNat ≤ (!free).toNat:=by
     cases hf: free <;> cases he: y8 p.domain p.wires z <;> simp_all
   have hs: (rest.map Prod.fst).all (y8 p.domain p.wires)=true:=by
     apply List.all_eq_true.mpr
     intro _ hm
     obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
     exact hav w ((m71 ws a b (op==2) ka kb).subset hw)
   have opOK: c2 p.domain p.wires (x1 op a b)=true:=by
     simp [c2,x1,hav _ ha,hav _ hb]
   simp only [vq,d8,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
   change k+p.paid+(!free).toNat < p.bound+(ws.countP const - w6 const a ka -
       w6 const b ((op==2)||kb)+(z4 p.domain z).toNat) at h
   dsimp only [rest] at hs
   simp only [v5,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
     List.countP_map,Function.comp_def]
   change k+p.paid+(!y8 p.domain p.wires z).toNat <
     p.bound+(rest.countP const+if z4 p.domain z then 1 else 0)
   cases hc: z4 p.domain z <;> simp [hc] at h ⊢ <;> omega
 · simp [vq,d8,all] at h
def y36 (c: x6) (i j op: Nat) (ka kb: Bool) :=
 let a:=y5 c i
 let b:=y5 c j
 (c.2.2.2.2.1.map (d8 c.2.2.1)).any (fun s => vq s (c.1-1) a b op ka kb)
lemma m123 {c i j op ka kb} (hi: i<c.2.2.1.length) (hj: j<c.2.2.1.length)
   (h: y36 c i j op ka kb=true): xk c i j op ka kb=true:=by
 have mem (t) (ht: t<c.2.2.1.length): y5 c t ∈ c.2.2.1:=by
   simp [y5,List.getD_eq_getElem?_getD,ht]
 obtain ⟨_,hm,ok⟩:=List.any_eq_true.mp h
 obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
 have closed:=m72 (mem _ hi) (mem _ hj) ok
 have cut: c.2.2.2.2.1.any (fun p => v5 p (c.1-1)
     ((g9 (op==2) ka kb (y5 c i) (y5 c j) c.2.2.1).map Prod.fst)
     (x1 op (y5 c i) (y5 c j)))=true :=
   List.any_eq_true.mpr ⟨p,hp,closed⟩
 simp only [xk,d0,zk,cut,Bool.or_true]
 repeat' split
 all_goals rfl
def wj (c: x6) (i j op: Nat) (ka kb: Bool) :=
 (if i<c.2.2.1.length /\ j<c.2.2.1.length then y36 c i j op ka kb else false) ||
   xk c i j op ka kb
lemma m102 {c i j op ka kb} (h: wj c i j op ka kb=true) :
   xk c i j op ka kb=true:=by
 simp only [wj,Bool.or_eq_true] at h
 rcases h with h | h
 · split at h
   next yes => exact m123 yes.1 yes.2 h
   next => contradiction
 · exact h
def xp (b: qy) (xs: List x6) (i j op: Nat) (ka kb: Bool) :=
 let (k,n,r,_,u,v):=b
 let un:=op==2
 let len:=1+(n-(if ka then 0 else 1)-(if un||kb then 0 else 1))
 if len>k then true else
   let d:=len==k
   let a:=f2 b i
   let b':=f2 b j
   let z:=zd (r*(BitVec.allOnes 768).toNat) op a b'
   let cov:=if d then v else u
   let mask:=zw r (c4 cov (v1 d a) (v1 d b') un ka kb ||| v1 d z)
   xx (fun c => wj c i j op ka kb) mask xs
lemma m133 (k n) (xs: List x6) {i j op: Nat} {ka kb}
   (hi: i<n) (hj: j<n) {q: Nat} (hq: q<xs.length)
   (budget: xs[q].1=k) (arity: xs[q].2.1=n)
   (pass: xp (g2 k n xs) xs i j op ka kb=true) :
   xk xs[q] i j op ka kb=true:=by
 let len:=1+(n-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))
 let d:=len==k
 have eval: xk xs[q] i j op ka kb =
     if len>k then true else if vd xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
     else if !k7 (z7 op (y5 xs[q] i) (y5 xs[q] j)).1 ||
       xs[q].2.2.1.any (fun v => v.1==(z7 op (y5 xs[q] i) (y5 xs[q] j)).1)
     then true else zk xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
       ((g9 (op==2) ka kb (y5 xs[q] i) (y5 xs[q] j) xs[q].2.2.1).map Prod.fst)
       (x1 op (y5 xs[q] i) (y5 xs[q] j)):=by
   simp only [xk,d0,budget,arity,len,d,vd] <;> rfl
 by_cases small: len>k
 · simp [eval,small]
 · let r:=ww xs.length
   let a:=f2 (g2 k n xs) i
   let b:=f2 (g2 k n xs) j
   let cov:=if d then j3 (fun c: x6 => c.2.2.2.1.2) xs
           else j3 (fun c: x6 => c.2.2.2.1.1) xs
   change (if len>k then true else xx _ (zw r
      (c4 cov (v1 d a) (v1 d b) (op==2) ka kb |||
       v1 d (zd (r*(BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
   rw [if_neg small] at pass
   have chosen: cov=j3 (fun c => yq c.2.2.2.1 d) xs:=by
     dsimp only [cov]
     cases d <;> rfl
   have ca: a=_:=m94 k n xs hi
   have cb: b=_:=m94 k n xs hj
   dsimp only [r] at pass
   rw [ca,cb,m125,m12,m12,m12,chosen,m67,m82] at pass
   by_cases hit: vd xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
   · apply m102
     apply m126 _ _ _ q hq _ pass
     rw [y42 _ _ _ hq]
     exact beq_iff_eq.mpr hit
   · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def xc (b: qy) (xs: List x6) (i j op: Nat) :=
 let f:=xp b xs i j op
 f false false&&f true false&&f false true&&f true true
def vk (b: qy) (xs: List x6) (i: Nat) (js: List Nat) :=
 xp b xs i i 2 false false&&xp b xs i i 2 true true &&
   js.all (fun j => xc b xs i j 0&&xc b xs i j 1)
def zj (b: qy) (xs: List x6): List Nat->Bool
 | [] => true
 | i::js => vk b xs i js&&zj b xs js
lemma m132 (k n) (xs: List x6) {q: Nat} (hq: q<xs.length)
   (budget: xs[q].1=k) (arity: xs[q].2.1=n) (js: List Nat)
   (bounds: ∀ j ∈ js,j<n) (allRows: zj (g2 k n xs) xs js=true) :
   c6 xs[q] (js.map (y5 xs[q]))=true:=by
 induction js with
 | nil => rfl
 | cons i js ih =>
   simp only [zj,Bool.and_eq_true,vk,List.all_eq_true] at allRows
   simp only [List.map_cons,c6,qb,Bool.and_eq_true,List.all_eq_true,List.mem_map]
   have hi:=bounds i List.mem_cons_self
   have check:=@m133 k n xs
   refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
     ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
   rintro _ ⟨j,hj,rfl⟩
   have hj':=bounds j (List.mem_cons_of_mem _ hj)
   have both:=allRows.1.2 j hj
   have opCheck (d: Bool) (pass: xc (g2 k n xs) xs i j (if d then 1 else 0)=true) :
       d7 xs[q] (y5 xs[q] i) (y5 xs[q] j) d=true:=by
     simp only [xc,Bool.and_eq_true] at pass
     simp only [d7,Bool.and_eq_true]
     exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
       check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
   exact ⟨opCheck false both.1,opCheck true both.2⟩
def kx (k n: Nat) (xs: List x6) :=
   zj (g2 k n xs) xs (List.range n)
lemma m136 {k n} {xs: List x6} {q} (hq: q<xs.length)
   (hb: xs[q].1=k) (ha: xs[q].2.1=n) (hn: xs[q].2.2.1.length=n)
   (pass: kx k n xs=true): c6 xs[q] xs[q].2.2.1=true:=by
 have all:=m132 k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
 have eq: (List.range n).map (y5 xs[q])=xs[q].2.2.1:=by
   apply List.ext_getElem
   · simp [hn]
   · intro i h1 h2
     simp [y5,List.getD_eq_getElem?_getD,h2]
 rwa [eq] at all
def yj (g: w3) (k i: Nat): x6 :=
 let raw:=wx g
 let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
 let (ops,bank,ws):=kw g k i
 let start:=num*(10*xy g depth+raw.length+depth)
 let pos:=start+num*offw+k3 data (start+i*offw) offw
 let nr:=k3 data pos 5
 let nl:=k3 data (pos+5) lw
 let st:=pos+5+lw
 let rules:=(vv data cw depth nr st).filterMap (fun (a,b) => yh g ops depth bank a b)
 let ls:=fun tag => ((g.index k tag).bind (yw g (k-1))).toList
 (k,ws.length,ws,zy ws,rules,ls)
def x56 (T: Sig) (c: x6) :=
 let ws:=c.2.2.1.map Prod.fst
 decide ws.Nodup&&!(ws.contains T)
lemma m128 (g: w3) (k i: Nat) :
   f5 g k i=(x56 (x0 g) (yj g k i) &&
     (if k=0 then true else c6 (yj g k i) (yj g k i).2.2.1)):=rfl
lemma y43 {g k start n} (h: ∀ (i: Nat),start ≤ i->i < start+n->f5 g k i=true) :
   x5 g k start n=true:=by
 induction n with
 | zero => rfl
 | succ n ih =>
   simp only [x5,Bool.and_eq_true]
   exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def yz (g: w3) (k start n: Nat) :=
 ((List.range n).map (start+·)).map (yj g k)
def x60 (g: w3) (k start n ar: Nat) :=
 (yz g k start n).all (fun c => c.2.1==ar&&x56 (x0 g) c)
def wb (g: w3) (k start n ar lo len: Nat) :=
 let xs:=yz g k start n
 let b:=g2 k ar xs
 (List.range len).all (fun d =>
   let i:=lo+d
   vk b xs i (List.range' (i+1) (ar-(i+1))))
lemma m84 {g k start n ar lo len} (h: wb g k start n ar lo len=true)
   (i: Nat) (l: lo ≤ i) (r: i < lo+len) :
   vk (g2 k ar (yz g k start n)) (yz g k start n)
     i (List.range' (i+1) (ar-(i+1)))=true:=by
 have ha:=List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
 simpa only [Nat.add_sub_of_le l] using ha
lemma m120 {g k start n ar lo a b}
   (h: wb g k start n ar lo a=true) (t: wb g k start n ar (lo+a) b=true) :
   wb g k start n ar lo (a+b)=true:=by
 apply List.all_eq_true.mpr
 intro j hj
 have jlt:=List.mem_range.mp hj
 by_cases first: j<a
 · exact m84 h (lo+j) (by omega) (by omega)
 · exact m84 t (lo+j) (by omega) (by omega)
lemma w24 {g k start n ar} (h: wb g k start n ar 0 ar=true) :
   kx k ar (yz g k start n)=true:=by
 let xs:=yz g k start n
 have go (lo num: Nat) (eq: lo+num=ar) :
     zj (g2 k ar xs) xs (List.range' lo num)=true:=by
   induction num generalizing lo with
   | zero => rfl
   | succ num ih =>
     simp only [List.range'_succ,zj,Bool.and_eq_true]
     refine ⟨?_,ih (lo+1) (by omega)⟩
     have ok:=m84 h lo (by omega) (by omega)
     simpa only [show ar-(lo+1)=num by omega] using ok
 unfold kx
 rw [List.range_eq_range']
 exact go 0 ar (by omega)
lemma y80 {g k start n ar} (hd: x60 g k start n ar=true)
   (h: wb g k start n ar 0 ar=true): x5 g k start n=true:=by
 apply y43
 intro i lo hi
 let xs:=yz g k start n
 have hm: yj g k i ∈ xs:=by
   apply List.mem_map.mpr
   exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
 obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
 have one:=List.all_eq_true.mp hd _ hm
 simp only [Bool.and_eq_true,beq_iff_eq] at one
 have hb: xs[q].1=k:=by rw [e]; rfl
 have ha: xs[q].2.1=ar:=e ▸ one.1
 have hn: xs[q].2.2.1.length=ar:=by rw [e]; exact one.1
 rw [m128,Bool.and_eq_true]
 refine ⟨one.2,?_⟩
 split
 · rfl
 · exact e ▸ m136 hq hb ha hn (w24 h)
def f0 (g: w3) (k start n ar lo num: Nat): Nat->Prop
 | 0 => wb g k start n ar lo num=true
 | d+1 => f0 g k start n ar lo (num/2) d /\ f0 g k start n ar (lo+num/2) (num-num/2) d
lemma x45 {g k start n ar lo num d} (h: f0 g k start n ar lo num d) :
   wb g k start n ar lo num=true:=by
 induction d generalizing lo num with
 | zero => exact h
 | succ d ih =>
   have v:=m120 (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def f4 (g: w3) (k start n ar rows: Nat): Nat->Prop
 | 0 => x60 g k start n ar=true /\ f0 g k start n ar 0 ar rows
 | d+1 => f4 g k start (n/2) ar rows d /\ f4 g k (start+n/2) (n-n/2) ar rows d
lemma m1 {g k start n ar rows d} (h: f4 g k start n ar rows d) :
   x5 g k start n=true:=by
 induction d generalizing start n with
 | zero => exact y80 h.1 (x45 h.2)
 | succ d ih =>
   have v:=m5 (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def j9 {α} (f: α->Bool) (xs: List α): Nat->Prop
 | 0 => xs.all f=true
 | d+1 => j9 f (xs.take (xs.length/2)) d /\ j9 f (xs.drop (xs.length/2)) d
lemma m3 {α f xs d} (h: @j9 α f xs d): xs.all f=true:=by
 induction d generalizing xs with
 | zero => exact h
 | succ d ih =>
   have ap: ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
     simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
   simpa only [List.take_append_drop] using ap
def v73 (i: Nat): Nat:=0xf
def v72: v4:=(1,0,0,0,1,0,0,v73)
def z87: Array (h6 × h6):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def z88: m2 w8:=(.leaf [])
def x42: Array (List Nat):=Array.mk [[],[33,48]]
def y66: Nat->v4
 | 3 => v72
 | _ => v2
def x41: Nat->Nat->Option (Nat × Nat)
 | 3 => fun _ => none
 | _ => fun _ => none
def g15: w3:=⟨15,3,fun j => z87[j]?.getD (0,0),z88,x42,y66,x41⟩
def x99 (i: Nat): Nat:=0x820007028af371d000003180048302e380000000003819155875690d58000003d
def v71 (i: Nat): Nat:=0x84001e90fd02fd01fa00
def v69: v4:=(3,1,3,0,4,4,0,v71)
def v70 (i: Nat): Nat:=0x11a20bf
def v68: v4:=(1,0,3,2,4,0,0,v70)
def z81: Array (h6 × h6):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def z82: m2 w8:=(.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def x40: Array (List Nat):=Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def y57: Nat->v4
 | 5 => v69
 | 6 => v68
 | _ => v2
def x39: Nat->Nat->Option (Nat × Nat)
 | 5 => fun _ => none
 | 6 => j8 5 25 2 10 2 4 (x99)
 | _ => fun _ => none
def g31: w3:=⟨31,6,fun j => z81[j]?.getD (0,0),z82,x40,y57,x39⟩
def z78: Array (h6 × h6):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def z79: m2 w8:=(.leaf [(8,0,39,0,4)])
def x38: Array (List Nat):=Array.mk [[],[83,32]]
def y54: Nat->v4
 | _ => v2
def x37: Nat->Nat->Option (Nat × Nat)
 | _ => fun _ => none
def g47: w3:=⟨47,4,fun j => z78[j]?.getD (0,0),z79,x38,y54,x37⟩
def z76: Array (h6 × h6):=Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def z77: m2 w8:=(.leaf [(16,0,39,0,4)])
def x36: Array (List Nat):=Array.mk [[],[84]]
def y53: Nat->v4
 | _ => v2
def x35: Nat->Nat->Option (Nat × Nat)
 | _ => fun _ => none
def g55: w3:=⟨55,4,fun j => z76[j]?.getD (0,0),z77,x36,y53,x35⟩
def z74: Array (h6 × h6):=Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def z75: m2 w8:=(.leaf [(32,0,31,0,7)])
def x34: Array (List Nat):=Array.mk [[],[50,65]]
def y52: Nat->v4
 | _ => v2
def x33: Nat->Nat->Option (Nat × Nat)
 | _ => fun _ => none
def g63: w3:=⟨63,7,fun j => z74[j]?.getD (0,0),z75,x34,y52,x33⟩
def w95 (i: Nat): Nat:=0x120ff
def w94: v4:=(1,0,2,0,1,0,0,w95)
def z31: Array (h6 × h6):=Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def z32: m2 w8:=(.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def y72: Array (List Nat):=Array.mk [[],[83,32]]
def z91: Nat->v4
 | 6 => w94
 | _ => v2
def y71: Nat->Nat->Option (Nat × Nat)
 | 6 => fun _ => none
 | _ => fun _ => none
def y73: w3:=⟨111,6,fun j => z31[j]?.getD (0,0),z32,y72,z91,y71⟩
def z29: Array (h6 × h6):=Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def z30: m2 w8:=(.leaf [(4,0,115,0,5)])
def y70: Array (List Nat):=Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def z90: Nat->v4
 | _ => v2
def y69: Nat->Nat->Option (Nat × Nat)
 | _ => fun _ => none
def g119: w3:=⟨119,5,fun j => z29[j]?.getD (0,0),z30,y70,z90,y69⟩
def x31 (i: Nat): Nat:=0xa81337040d4b600002948880000590cc33d41450272020001b1
def w93 (i: Nat): Nat:=0x82000f487f40bfa03fa00
def w91: v4:=(3,1,3,0,4,4,0,w93)
def w92 (i: Nat): Nat:=0x1f5859bf
def w90: v4:=(1,0,3,2,4,0,0,w92)
def z24: Array (h6 × h6):=Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def z25: m2 w8:=(.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def y65: Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def z86: Nat->v4
 | 6 => w91
 | 7 => w90
 | _ => v2
def y64: Nat->Nat->Option (Nat × Nat)
 | 6 => fun _ => none
 | 7 => j8 5 18 5 10 2 4 (x31)
 | _ => fun _ => none
def z26: w3:=⟨189,7,fun j => z24[j]?.getD (0,0),z25,y65,z86,y64⟩
def z27: Array (h6 × h6):=Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def z28: m2 w8:=(.leaf [(32,0,95,0,8)])
def y68: Array (List Nat):=Array.mk [[],[101,66,16]]
def z89: Nat->v4
 | _ => v2
def y67: Nat->Nat->Option (Nat × Nat)
 | _ => fun _ => none
def g127: w3:=⟨127,8,fun j => z27[j]?.getD (0,0),z28,y68,z89,y67⟩
def y50 (i: Nat): Nat:=0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def x28 (i: Nat): Nat:=0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def x29 (i: Nat): Nat:=0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def x30 (i: Nat): Nat:=0x2c
def w89 (i: Nat): Nat:=0x47d6448788a00
def w85: v4:=(1,4,6,0,2,0,0,w89)
def w88 (i: Nat): Nat:=0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def w84: v4:=(28,3,6,0,2,8,0,w88)
def w87 (i: Nat): Nat:=0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def w83: v4:=(100,2,6,5,2,12,0,w87)
def w86 (i: Nat): Nat:=0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def w82: v4:=(12,1,6,7,2,9,0,w86)
def w22 (i: Nat): Nat:=0x1f3c11ff
def w21: v4:=(1,0,6,4,2,0,0,w22)
def z22: Array (h6 × h6):=Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def z23: m2 w8:=(.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def y63: Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def z85: Nat->v4
 | 6 => w85
 | 7 => w84
 | 8 => w83
 | 9 => w82
 | 10 => w21
 | _ => v2
def y62: Nat->Nat->Option (Nat × Nat)
 | 6 => fun _ => none
 | 7 => j8 1 3 0 6 0 2 (x30)
 | 8 => j8 17 64 6 11 5 2 (x29)
 | 9 => j8 68 242 7 13 7 2 (x28)
 | 10 => j8 9 46 4 10 4 2 (y50)
 | _ => fun _ => none
def wk: w3:=⟨191,10,fun j => z22[j]?.getD (0,0),z23,y63,z85,y62⟩
def z20: Array (h6 × h6):=Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def z21: m2 w8:=(.leaf [(8,0,243,0,7)])
def y61: Array (List Nat):=Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def z84: Nat->v4
 | _ => v2
def y60: Nat->Nat->Option (Nat × Nat)
 | _ => fun _ => none
def g251: w3:=⟨251,7,fun j => z20[j]?.getD (0,0),z21,y61,z84,y60⟩
def z18: Array (h6 × h6):=Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def z19: m2 w8:=(.leaf [(64,0,191,0,11)])
def y59: Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def z83: Nat->v4
 | _ => v2
def y58: Nat->Nat->Option (Nat × Nat)
 | _ => fun _ => none
def g255: w3:=⟨255,11,fun j => z18[j]?.getD (0,0),z19,y59,z83,y58⟩
def y47 (i: Nat): Nat:=0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def y48 (i: Nat): Nat:=0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def y49 (i: Nat): Nat:=0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def x27 (i: Nat): Nat:=0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def w81 (i: Nat): Nat:=0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def w79: v4:=(25,4,6,0,3,8,0,w81)
def w80 (i: Nat): Nat:=0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def w78: v4:=(91,3,6,5,3,11,0,w80)
def w20 (i: Nat): Nat:=0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def w17: v4:=(41,2,6,7,3,12,0,w20)
def w19 (i: Nat): Nat:=0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def w16: v4:=(6,1,6,6,3,8,0,w19)
def w18 (i: Nat): Nat:=0x11b280e4ff
def w15: v4:=(1,0,6,3,3,0,0,w18)
def z16: Array (h6 × h6):=Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def z17: m2 w8:=(.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def y56: Array (List Nat):=Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def z80: Nat->v4
 | 8 => w79
 | 9 => w78
 | 10 => w17
 | 11 => w16
 | 12 => w15
 | _ => v2
def y55: Nat->Nat->Option (Nat × Nat)
 | 8 => fun _ => none
 | 9 => j8 17 68 7 12 5 3 (x27)
 | 10 => j8 57 200 7 14 7 3 (y49)
 | 11 => j8 30 108 6 13 6 3 (y48)
 | 12 => j8 6 61 1 10 3 3 (y47)
 | _ => fun _ => none
def yb: w3:=⟨383,12,fun j => z16[j]?.getD (0,0),z17,y56,z80,y55⟩
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma low3: k5 (f3 3) (y0 3) 1:=vj (hints:=1) (by decide +kernel)
def v56: List (Nat × List Nat):=[]
def x58:=w2 [] 1 v56
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w44: p2 x58:=m0 y85 low3 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma low7: k5 (f3 7) (y0 7) 2:=vj (hints:=257) (by decide +kernel)
def v55: List (Nat × List Nat):=[]
def z52:=w2 x58 2 v55
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma x55: p2 z52:=m0 w44 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma w77: w5 g15 (q7 z52)=true:=by
 simp only [w5,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=0) ?_⟩,m3 (d:=0) ?_⟩
 all_goals simp only [j9]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x73: x5 g15 3 0 1=true:=by
 apply m1 (ar:=4) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma v13: x5 g15 3 0 1=true:=x73
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y91: k1 g15 3:=by
 intro k hk
 interval_cases k
 · exact (rfl: x5 g15 0 0 0=true)
 · exact (rfl: x5 g15 1 0 0=true)
 · exact (rfl: x5 g15 2 0 0=true)
 · exact v13
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v67: k5 (f3 15) (y0 15) 4 :=
 m17 (g:=g15) (i:=0) (hints:=8449) (m4 z52 x55) w77 y91 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def w66: List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def y46:=w2 z52 4 w66
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma x67: p2 y46:=m0 x55 v67 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v65: k5 (f3 45) (y0 45) 3:=vj (hints:=8965) (by decide +kernel)
def w64: List (Nat × List Nat):=[]
def y45:=w2 y46 3 w64
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma x66: p2 y45:=m0 x67 v65 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v63: k5 (f3 51) (y0 51) 3:=vj (hints:=1) (by decide +kernel)
def w62: List (Nat × List Nat):=[]
def kq:=w2 y45 3 w62
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y19: p2 kq:=m0 x66 v63 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma w76: w5 g31 (q7 kq)=true:=by
 simp only [w5,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=1) ?_⟩,m3 (d:=2) ?_⟩
 all_goals simp only [j9]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x72: x5 g31 5 0 1=true:=by
 apply m1 (ar:=5) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x71: x5 g31 5 1 2=true:=by
 apply m1 (ar:=6) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma v12: x5 g31 5 0 3=true:=(@m5 g31 5 0 1 2 x72 x71)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x70: x5 g31 6 0 1=true:=by
 apply m1 (ar:=5) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma v11: x5 g31 6 0 1=true:=x70
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y90: k1 g31 6:=by
 intro k hk
 interval_cases k
 · exact (rfl: x5 g31 0 0 0=true)
 · exact (rfl: x5 g31 1 0 0=true)
 · exact (rfl: x5 g31 2 0 0=true)
 · exact (rfl: x5 g31 3 0 0=true)
 · exact (rfl: x5 g31 4 0 0=true)
 · exact v12
 · exact v11
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v66: k5 (f3 31) (y0 31) 7 :=
 m17 (g:=g31) (i:=0) (hints:=8449) (m4 kq y19) w76 y90 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def w65: List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def z15:=w2 kq 7 w65
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y21: p2 z15:=m0 y19 v66 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v64: k5 (f3 47) (y0 47) 5 :=
 m10 (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (m4 z15 y21) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def w63: List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def z14:=w2 z15 5 w63
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y20: p2 z14:=m0 y21 v64 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v62: k5 (f3 55) (y0 55) 5 :=
 m10 (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (m4 z14 y20) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def w61: List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def z13:=w2 z14 5 w61
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y18: p2 z13:=m0 y20 v62 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v61: k5 (f3 63) (y0 63) 8 :=
 m10 (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (m4 z13 y18) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def w60: List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def kv:=w2 z13 8 w60
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y17: p2 kv:=m0 y18 v61 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma w14: w5 y73 (q7 kv)=true:=by
 simp only [w5,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=0) ?_⟩,m3 (d:=0) ?_⟩
 all_goals simp only [j9]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x20: x5 y73 6 0 1=true:=by
 apply m1 (ar:=6) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w36: x5 y73 6 0 1=true:=x20
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y25: k1 y73 6:=by
 intro k hk
 interval_cases k
 · exact (rfl: x5 y73 0 0 0=true)
 · exact (rfl: x5 y73 1 0 0=true)
 · exact (rfl: x5 y73 2 0 0=true)
 · exact (rfl: x5 y73 3 0 0=true)
 · exact (rfl: x5 y73 4 0 0=true)
 · exact (rfl: x5 y73 5 0 0=true)
 · exact w36
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w75: k5 (f3 111) (y0 111) 7 :=
 m17 (g:=y73) (i:=0) (hints:=16785665) (m4 kv y17) w14 y25 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def x96: List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def kg:=w2 kv 7 x96
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z47: p2 kg:=m0 y17 w75 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w74: k5 (f3 119) (y0 119) 6 :=
 m10 (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (m4 kg z47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def x95: List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def vx:=w2 kg 6 x95
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z46: p2 vx:=m0 z47 w74 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma w13: w5 z26 (q7 vx)=true:=by
 simp only [w5,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=1) ?_⟩,m3 (d:=2) ?_⟩
 all_goals simp only [j9]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x19: x5 z26 6 0 1=true:=by
 apply m1 (ar:=6) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x18: x5 z26 6 1 2=true:=by
 apply m1 (ar:=7) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w35: x5 z26 6 0 3=true:=(@m5 z26 6 0 1 2 x19 x18)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x17: x5 z26 7 0 1=true:=by
 apply m1 (ar:=6) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w34: x5 z26 7 0 1=true:=x17
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y24: k1 z26 7:=by
 intro k hk
 interval_cases k
 · exact (rfl: x5 z26 0 0 0=true)
 · exact (rfl: x5 z26 1 0 0=true)
 · exact (rfl: x5 z26 2 0 0=true)
 · exact (rfl: x5 z26 3 0 0=true)
 · exact (rfl: x5 z26 4 0 0=true)
 · exact (rfl: x5 z26 5 0 0=true)
 · exact w35
 · exact w34
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w72: k5 (f3 189) (y0 189) 8 :=
 m17 (g:=z26) (i:=0) (hints:=536879876) (m4 vx z46) w13 y24 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def x93: List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def z53:=w2 vx 8 x93
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y88: p2 z53:=m0 z46 w72 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w70: k5 (f3 250) (y0 250) 5:=vj (hints:=1366507616) (by decide +kernel)
def x91: List (Nat × List Nat):=[]
def kj:=w2 z53 5 x91
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z43: p2 kj:=m0 y88 w70 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w73: k5 (f3 127) (y0 127) 9 :=
 m10 (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (m4 kj z43) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def x94: List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def vy:=w2 kj 9 x94
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z45: p2 vy:=m0 z43 w73 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma w12: w5 wk (q7 vy)=true:=by
 simp only [w5,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=4) ?_⟩,m3 (d:=1) ?_⟩
 all_goals simp only [j9]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x16: x5 wk 6 0 1=true:=by
 apply m1 (ar:=7) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w33: x5 wk 6 0 1=true:=x16
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x15: x5 wk 7 0 13=true:=by
 apply m1 (ar:=7) (rows:=0) (d:=1)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x14: x5 wk 7 13 15=true:=by
 apply m1 (ar:=8) (rows:=0) (d:=1)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w32: x5 wk 7 0 28=true:=(@m5 wk 7 0 13 15 x15 x14)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x13: x5 wk 8 0 7=true:=by
 apply m1 (ar:=7) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x12: x5 wk 8 7 61=true:=by
 apply m1 (ar:=8) (rows:=0) (d:=3)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma x11: x5 wk 8 68 32=true:=by
 apply m1 (ar:=9) (rows:=0) (d:=2)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w30: x5 wk 8 0 100=true:=(@m5 wk 8 0 68 32 (@m5 wk 8 0 7 61 x13 x12) x11)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y99: x5 wk 9 0 3=true:=by
 apply m1 (ar:=7) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y98: x5 wk 9 3 9=true:=by
 apply m1 (ar:=8) (rows:=0) (d:=1)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w29: x5 wk 9 0 12=true:=(@m5 wk 9 0 3 9 y99 y98)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y35: x5 wk 10 0 1=true:=by
 apply m1 (ar:=7) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma x50: x5 wk 10 0 1=true:=y35
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y23: k1 wk 10:=by
 intro k hk
 interval_cases k
 · exact (rfl: x5 wk 0 0 0=true)
 · exact (rfl: x5 wk 1 0 0=true)
 · exact (rfl: x5 wk 2 0 0=true)
 · exact (rfl: x5 wk 3 0 0=true)
 · exact (rfl: x5 wk 4 0 0=true)
 · exact (rfl: x5 wk 5 0 0=true)
 · exact w33
 · exact w32
 · exact w30
 · exact w29
 · exact x50
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w71: k5 (f3 191) (y0 191) 11 :=
 m17 (g:=wk) (i:=0) (hints:=536879361) (m4 vy z45) w12 y23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def x92: List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def kh:=w2 vy 11 x92
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z44: p2 kh:=m0 z45 w71 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w69: k5 (f3 251) (y0 251) 8 :=
 m10 (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (m4 kh z44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def x90: List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def kk:=w2 kh 8 x90
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z42: p2 kk:=m0 z44 w69 (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w68: k5 (f3 255) (y0 255) 12 :=
 m10 (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (m4 kk z42) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def x89: List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def vz:=w2 kk 12 x89
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z41: p2 vz:=m0 z42 w68 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma w11: w5 yb (q7 vz)=true:=by
 simp only [w5,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=4) ?_⟩,m3 (d:=2) ?_⟩
 all_goals simp only [j9]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y97: x5 yb 8 0 23=true:=by
 apply m1 (ar:=8) (rows:=0) (d:=2)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y96: x5 yb 8 23 2=true:=by
 apply m1 (ar:=9) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w28: x5 yb 8 0 25=true:=(@m5 yb 8 0 23 2 y97 y96)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y95: x5 yb 9 0 9=true:=by
 apply m1 (ar:=8) (rows:=0) (d:=1)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y94: x5 yb 9 9 75=true:=by
 apply m1 (ar:=9) (rows:=0) (d:=4)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y93: x5 yb 9 84 7=true:=by
 apply m1 (ar:=10) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma w27: x5 yb 9 0 91=true:=(@m5 yb 9 0 84 7 (@m5 yb 9 0 9 75 y95 y94) y93)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y34: x5 yb 10 0 5=true:=by
 apply m1 (ar:=8) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y33: x5 yb 10 5 16=true:=by
 apply m1 (ar:=9) (rows:=0) (d:=1)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y32: x5 yb 10 21 20=true:=by
 apply m1 (ar:=10) (rows:=0) (d:=2)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma x49: x5 yb 10 0 41=true:=(@m5 yb 10 0 21 20 (@m5 yb 10 0 5 16 y34 y33) y32)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y31: x5 yb 11 0 1=true:=by
 apply m1 (ar:=8) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y30: x5 yb 11 1 5=true:=by
 apply m1 (ar:=9) (rows:=0) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma x48: x5 yb 11 0 6=true:=(@m5 yb 11 0 1 5 y31 y30)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in set_option maxRecDepth 16384 in
lemma y29: x5 yb 12 0 1=true:=by
 apply m1 (ar:=8) (rows:=1) (d:=0)
 simp only [f4,f0,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
lemma x47: x5 yb 12 0 1=true:=y29
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma y22: k1 yb 12:=by
 intro k hk
 interval_cases k
 · exact (rfl: x5 yb 0 0 0=true)
 · exact (rfl: x5 yb 1 0 0=true)
 · exact (rfl: x5 yb 2 0 0=true)
 · exact (rfl: x5 yb 3 0 0=true)
 · exact (rfl: x5 yb 4 0 0=true)
 · exact (rfl: x5 yb 5 0 0=true)
 · exact (rfl: x5 yb 6 0 0=true)
 · exact (rfl: x5 yb 7 0 0=true)
 · exact w28
 · exact w27
 · exact x49
 · exact x48
 · exact x47
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma w67: k5 (f3 383) (y0 383) 13 :=
 m17 (g:=yb) (i:=0) (hints:=12901687553) (m4 vz z41) w11 y22 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def x88: List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def yf:=w2 vz 13 x88
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z40: p2 yf:=m0 z41 w67 (by decide +kernel)
def z35: Array (h6 × h6):=Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def z36: m2 w8:=(.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def vf: Array (List Nat):=Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def zq: w3:=⟨511,14,fun j => z35[j]?.getD (0,0),z36,vf,fun _ => v2,fun _ _ => none⟩
set_option maxHeartbeats 0 in
lemma z54: w5 zq (q7 yf)=true:=by
 simp only [w5,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=5) ?_⟩,m3 (d:=3) ?_⟩
 all_goals simp only [j9]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
def yc (op: GateOp): Bool :=
 match op with
 | .not => true
 | _ => false
private lemma y51 (w: List Sig) (g: Gate)
   (hg: g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) /\ g.inputs.length≤2) :
   w1 w (gv w g) ∨
     (if yc g.op then ∃ a,a∈w /\ x7 a /\ gv w g=neg a
      else ∃ d a b,a∈w /\ b∈w /\ x7 a /\ x7 b /\ a≠b /\ gv w g=bin d a b):=by
 have nx (a: Sig) (ha: w1 w a): w1 w (neg a) \/ ∃ x,x∈w /\ x7 x /\ neg a=neg x:=by
   rcases m13 ha with rfl | rfl | ⟨hm,hp⟩
   · exact Or.inl (Or.inr fun h => h.2 m70.1)
   · exact Or.inl (Or.inr fun h => h.1 m70.2)
   · exact Or.inr ⟨a,hm,hp,rfl⟩
 have bn (d: Bool) (a b: Sig) (ha: w1 w a) (hb: w1 w b) :
     w1 w (bin d a b) \/ ∃ d' x y,x∈w /\ y∈w /\ x7 x /\ x7 y /\ x≠y /\ bin d a b=bin d' x y:=by
   have bzero: ∀ v,bin false v zero=zero /\ bin true v zero=v:=fun v => ⟨(m16 v).2.2.1,(m16 v).2.1⟩
   have bone: ∀ v,bin false v one=v /\ bin true v one=one:=fun v => ⟨(m16 v).1,(m16 v).2.2.2.1⟩
   rcases m13 ha with rfl | rfl | ⟨hma,hpa⟩
   · rw [m24]
     cases d
     · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
     · rw [(bzero b).2]; exact Or.inl hb
   · rw [m24]
     cases d
     · rw [(bone b).1]; exact Or.inl hb
     · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
   · rcases m13 hb with rfl | rfl | ⟨hmb,hpb⟩
     · cases d
       · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
       · rw [(bzero a).2]; exact Or.inl (Or.inl hma)
     · cases d
       · rw [(bone a).1]; exact Or.inl (Or.inl hma)
       · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
     · by_cases eq: a=b
       · subst b
         cases d
         · rw [(m16 a).2.2.2.2.1]; exact Or.inl (Or.inl hma)
         · rw [(m16 a).2.2.2.2.2]; exact Or.inl (Or.inl hma)
       · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
 obtain ⟨ho,hl⟩:=hg
 rcases ho with ho | ho | ho
 · simp only [ho,yc,Bool.false_eq_true,ite_false]
   cases hi: g.inputs with
   | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv,ho,hi]))
   | cons i t =>
     cases t with
     | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).1] using yv w i)
     | cons j u =>
       cases u with
       | cons _ _ => simp [hi] at hl
       | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).1] using bn false _ _ (yv w i) (yv w j)
 · simp only [ho,yc,Bool.false_eq_true,ite_false]
   cases hi: g.inputs with
   | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv,ho,hi]))
   | cons i t =>
     cases t with
     | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).2.1] using yv w i)
     | cons j u =>
       cases u with
       | cons _ _ => simp [hi] at hl
       | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).2.1] using bn true _ _ (yv w i) (yv w j)
 · rw [Set.mem_singleton_iff] at ho
   simp only [ho,yc,ite_true]
   cases hi: g.inputs with
   | nil =>
     have hgv: gv w g=one:=by simp only [gv,ho,hi,List.map_nil,List.headD_nil,m70.1]
     exact Or.inl (Or.inr fun h => h.2 hgv)
   | cons i t =>
     have hgv: gv w g=neg (w.getD i zero):=by simp only [gv,ho,hi,List.map_cons,List.headD_cons]
     rw [hgv]; exact nx _ (yv w i)
private lemma z68 {w: List Sig} {z: Sig} {k t S} (isN: Bool) (h: j6 target k t S)
   (hz: w1 w z ∨
     (if isN then ∃ a,a∈w /\ x7 a /\ z=neg a
      else ∃ d a b,a∈w /\ b∈w /\ x7 a /\ x7 b /\ a≠b /\ z=bin d a b))
   (sub: ∀ a ∈ S,a ∈ w++[z]) :
   ∃ k' t' S',k' ≤ k+1 /\ t' ≤ t+isN.toNat /\ j6 target k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
 by_cases hm: z ∈ S
 · by_cases hw: z ∈ w
   · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
     intro a ha
     rcases (by simpa using sub a ha: a ∈ w \/ a=z) with hu | rfl
     · exact hu
     · exact hw
   · have hp:=m22 h z hm
     rcases hz with hr | hwit
     · exact False.elim ((hr.resolve_left hw) hp)
     · cases isN with
       | true =>
         simp only [ite_true] at hwit
         obtain ⟨a,ha,hp',eq⟩:=hwit
         subst z
         let U:=S.erase (neg a)
         have ht: j6 target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
         have hu: ∀ v ∈ U,v ∈ w:=fun v hv => by
           obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
         have hf: neg a ∉ insert a U:=fun hh => by
           rcases Finset.mem_insert.mp hh with eq | u
           · exact hw (eq.symm ▸ ha)
           · exact hw (hu _ u)
         exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by simp,j6.unary hp' hf ht,by simpa using And.intro ha hu⟩
       | false =>
         simp only [Bool.false_eq_true,ite_false] at hwit
         obtain ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩:=hwit
         subst z
         let U:=S.erase (bin d a b)
         have ht: j6 target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
         have hu: ∀ v ∈ U,v ∈ w:=fun v hv => by
           obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
         have hf: bin d a b ∉ insert a (insert b U):=fun hh => by
           rcases Finset.mem_insert.mp hh with eq | u
           · exact hw (eq.symm ▸ ha)
           rcases Finset.mem_insert.mp u with eq | u
           · exact hw (eq.symm ▸ hb)
           · exact hw (hu _ u)
         exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,by simp,j6.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
 · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
   intro a ha
   have hn: a≠z:=fun hh => hm (hh ▸ ha)
   simpa [hn] using sub a ha
private lemma x43 (gs: List Gate) (w: List Sig)
   (legal: ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) /\ g.inputs.length≤2)
   (hp: x7 target) (hout: target ∈ xq gs w) :
   ∃ k t S,k ≤ gs.length /\ t ≤ gs.countP (fun g => yc g.op) /\ j6 target k t S /\ ∀ a ∈ S,a ∈ w:=by
 induction gs generalizing w with
 | nil => exact ⟨0,0,{target},by simp,by simp,j6.stop hp,by simpa [xq] using hout⟩
 | cons g gs ih =>
   obtain ⟨k,t,S,hk,ht,hl,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
   obtain ⟨l,u,T,hl',hu',hlu,hT⟩:=z68 (yc g.op) hl (y51 w g (legal g (by simp))) hs
   refine ⟨l,u,T,by simp; omega,?_,hlu,hT⟩
   simp only [List.countP_cons]
   cases h: yc g.op <;> simp [h] at hu' ⊢ <;> omega
def I1 (T: Sig) (cap tm: Nat) (S: Finset Sig): Prop :=
 ∀ k t,k ≤ cap->t ≤ tm->¬j6 T k t S
lemma i2i1 {T cap tm S} (h: x2 T cap S): I1 T cap tm S :=
 fun k t hk _ => h k t hk
lemma re1 {T n tm} {ws: List Sig} (hi: I1 T n tm ws.toFinset)
   (p: List jg) (ok: yp T p=true): I1 T n tm (ws.map (y7 p.reverse)).toFinset:=by
 simp only [yp,Bool.and_eq_true,beq_iff_eq] at ok
 have onto: Function.Surjective (q1 p):=fun r => ⟨q1 p.reverse r,m42 ok.2 r⟩
 intro k t hk ht h
 have run:=m90 h (q1 p) onto
 have goal: q8 (q1 p) T=T:=(m20 p T).symm.trans ok.1.1
 have inv (x: Sig): q8 (q1 p) (y7 p.reverse x)=x:=by
   apply BitVec.eq_of_getLsbD_eq
   intro j hj
   change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
   rw [m7,m40,m42 ok.1.2]
 have back: (ws.map (y7 p.reverse)).toFinset.image (q8 (q1 p))=ws.toFinset:=by
   ext a
   simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
   constructor
   · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
   · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
 rw [goal,back] at run
 exact hi k t hk ht run
def d3 (tm cap len op: Nat): Nat :=
 if len==cap||op==2||tm==0 then 0 else 1
lemma es1 {T: Sig} {cap tm: Nat} {ws: List Sig} (htm1: tm ≤ 1) (hn: ws.Nodup) (out: T ∉ ws)
   (oneStep: tm > 0->∀ a ∈ ws,∀ keep,neg a ∉ ws->x7 (neg a) ->
     (k0 ws a keep).length ≤ cap ->
     I1 T (cap-1) (d3 tm cap (k0 ws a keep).length 2) (k0 ws a keep).toFinset)
   (twoStep: ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b->bin d a b ∉ ws ->
     x7 (bin d a b)->(w0 ws a b d ka kb).length ≤ cap ->
     I1 T (cap-1) (d3 tm cap (w0 ws a b d ka kb).length 0)
       (w0 ws a b d ka kb).toFinset) :
   I1 T cap tm ws.toFinset:=by
 classical
 intro k t hk ht h
 generalize he: ws.toFinset=S at h
 induction h using j6.recurse with
 | stop hp =>
   exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
 | @unary k t U a ha hf tail _ =>
   have am: a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
   have fresh: neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
   have hz:=m22 tail _ (Finset.mem_insert_self _ _)
   let keep:=decide (a ∈ U)
   have er:=m39 hn a
   have rest: (g6 keep a (ws.erase a)).toFinset=U:=by
     rw [m28,er,he]; by_cases hm: a ∈ U <;> simp [keep,hm]
   have nd: (k0 ws a keep).Nodup:=by
     have na: a ∉ ws.erase a:=hn.not_mem_erase
     refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
       g8 keep a (ws.erase a) (hn.erase _) na⟩
   have eq: (k0 ws a keep).toFinset=insert (neg a) U:=by simp [k0,rest]
   have sc:=(m26 tail).2
   have len: (k0 ws a keep).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
   have htm_pos: tm > 0:=by omega
   have ht': t ≤ d3 tm cap (k0 ws a keep).length 2:=by
     unfold d3; simp; omega
   exact oneStep htm_pos a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
 | @binary k t U a b d ha hb hab hf tail _ =>
   have am: a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
   have bm: b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
   have fresh: bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
   have hz:=m22 tail _ (Finset.mem_insert_self _ _)
   let ka:=decide (a ∈ U)
   let kb:=decide (b ∈ U)
   let rest:=(ws.erase a).erase b
   have er: rest.toFinset=(ws.toFinset.erase a).erase b:=by
     rw [show rest=(ws.erase a).erase b by rfl,m39 (hn.erase _) b,m39 hn a]
   have ke: (g6 ka a (g6 kb b rest)).toFinset=U:=by
     rw [m28,m28,er,he]
     ext j
     by_cases hja: j=a
     · subst j; by_cases aa: a ∈ U <;> by_cases bb: b ∈ U <;> simp [ka,kb,aa,bb,hab]
     · by_cases hjb: j=b
       · subst j; by_cases aa: a ∈ U <;> by_cases bb: b ∈ U <;> simp [ka,kb,aa,bb,hja]
       · by_cases aa: a ∈ U <;> by_cases bb: b ∈ U <;> simp [ka,kb,aa,bb,hja,hjb]
   have rn: rest.Nodup:=(hn.erase _).erase _
   have ar: a ∉ rest:=fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
   have br: b ∉ rest:=(hn.erase a).not_mem_erase
   have nk:=g8 kb b rest rn br
   have ax: a ∉ g6 kb b rest:=by cases kb <;> simp [g6,ar,hab]
   have nd: (w0 ws a b d ka kb).Nodup :=
     List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
       g8 ka a _ nk ax⟩
   have eq: (w0 ws a b d ka kb).toFinset=insert (bin d a b) U:=by
     change (bin d a b::g6 ka a (g6 kb b rest)).toFinset=_; simp [ke]
   have sc:=(m26 tail).2
   have len: (w0 ws a b d ka kb).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
   have ht': t ≤ d3 tm cap (w0 ws a b d ka kb).length 0:=by
     unfold d3
     by_cases hlen: (w0 ws a b d ka kb).length=cap
     · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; simp [hlen]; omega
     · by_cases htm0: tm=0
       · simp [htm0]; omega
       · have hne: ((w0 ws a b d ka kb).length==cap||0==2||tm==0)=false:=by
           simp [beq_eq_false_iff_ne.mpr hlen,beq_eq_false_iff_ne.mpr htm0]
         rw [hne]; simp; omega
   exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
def wq (a b: List Sig): Bool:=a.length==b.length&&a.all (fun x => b.contains x)
lemma ky {xs ys: List Sig} (hnd: xs.Nodup) (h: wq xs ys=true): xs.toFinset=ys.toFinset:=by
 simp only [wq,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
 have hsub: xs.toFinset ⊆ ys.toFinset:=fun x hx => List.mem_toFinset.mpr (h.2 x (List.mem_toFinset.mp hx))
 have hle: ys.toFinset.card ≤ xs.toFinset.card:=by
   rw [List.toFinset_card_of_nodup hnd,h.1]; exact List.toFinset_card_le ys
 exact Finset.eq_of_subset_of_card_le hsub hle
def yy (pools: List w7) (links: Nat->List (List Sig)) (k: Nat) (rest: List Sig) (op: p7) (z: Sig): Bool :=
 let ws:=z::rest
 (links (x59 ws)).any (wq ws)||pools.any (fun p => v5 p k rest op)
lemma cc1s {raw T pools links k tm rest op}
   (pValid: ∀ p ∈ pools,j5 raw T p)
   (lValid: ∀ tag xs,xs ∈ links tag->I1 T k tm (List.toFinset xs))
   (nd: (y4 op :: rest).Nodup)
   (h: yy pools links k rest op (y4 op)=true) :
   I1 T k tm (y4 op :: rest).toFinset:=by
 simp only [yy,Bool.or_eq_true,List.any_eq_true] at h
 rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
 · rw [ky nd ok]; exact lValid _ _ hx
 · exact i2i1 (m9 (pValid _ hp) nd ok)
abbrev x65:=Nat->List (List Sig)
abbrev yd:=w7 × Nat × Bool × List Sig
def qc (ws: List y9) (p: w7): yd :=
 let mw:=p.wires.map (j2 p.domain)
 (p,ws.countP (fun w => z4 p.domain w.1),
    ws.all (fun w => y8 p.domain p.wires w.1),mw)
def q9 (ws: List y9) (p: w7): yd :=
 let mw:=p.wires.map (j2 p.domain)
 (p,ws.countP (fun w => z4 p.domain w.1),
    ws.all (fun w => let m:=j2 p.domain w.1; m==zero||m==p.domain||mw.any (fun v => v==m)),mw)
lemma jf (ws: List y9) (p: w7): q9 ws p=qc ws p:=rfl
def d2 (s: yd) (k: Nat) (a b: y9) (z: Sig) (un ka kb: Bool): Bool :=
 if !s.2.2.1 then false else
 let p:=s.1
 let zm:=j2 p.domain z
 let zc:=zm==zero||zm==p.domain
 let la:=if ka then 0 else (z4 p.domain a.1).toNat
 let lb:=if un||kb then 0 else (z4 p.domain b.1).toNat
 let cm:=s.2.1 - la - lb+zc.toNat
 let free:=zc||s.2.2.2.any (fun v => v==zm)
 decide (k+p.paid+(!free).toNat < p.bound+cm)
lemma v57 {p k ws a b op ka kb} (ha: a∈ws) (hb: b∈ws)
   (h: d2 (q9 ws p) k a b (y4 (x1 op a b)) (op==2) ka kb=true) :
   v5 p k ((g9 (op==2) ka kb a b ws).map Prod.fst) (x1 op a b)=true:=by
 rw [jf] at h
 let z:=y4 (x1 op a b)
 let const:=fun w: y9 => z4 p.domain w.1
 let rest:=g9 (op==2) ka kb a b ws
 have ck:=jw const ws a b (op==2) ka kb
 change ws.countP const - w6 const a ka - w6 const b ((op==2)||kb) ≤ rest.countP const at ck
 by_cases all: ws.all (fun w => y8 p.domain p.wires w.1)=true
 · have hav:=List.all_eq_true.mp all
   have hs: (rest.map Prod.fst).all (y8 p.domain p.wires)=true:=by
     apply List.all_eq_true.mpr
     intro _ hm
     obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
     exact hav w ((m71 ws a b (op==2) ka kb).subset hw)
   have opOK: c2 p.domain p.wires (x1 op a b)=true:=by
     simp [c2,x1,hav _ ha,hav _ hb]
   simp only [d2,qc,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
   change k+p.paid+(!y8 p.domain p.wires z).toNat <
     p.bound+(ws.countP const - w6 const a ka - w6 const b ((op==2)||kb)+(z4 p.domain z).toNat) at h
   dsimp only [rest] at hs
   simp only [v5,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
     List.countP_map,Function.comp_def]
   change k+p.paid+(!y8 p.domain p.wires z).toNat <
     p.bound+(rest.countP const+if z4 p.domain z then 1 else 0)
   cases hc: z4 p.domain z <;> simp [hc] at h ⊢ <;> omega
 · simp [d2,qc,all] at h
abbrev NC1 :=
 Nat × Nat × Nat × List y9 × jy × List w7 × List yd × x65 × x65
def cw1 (c: NC1) (i: Nat): y9:=c.2.2.2.1.getD i y3
def em1 (c: NC1) (op: Nat) (a b z: y9) (ka kb: Bool): Bool :=
 let (cap,tm,n,ws,cov,pools,qpools,l0,l1):=c
 let un:=op==2
 let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
 if len > cap then true else
   let ct:=d3 tm cap len op
   let d:=ct==0
   if (p9 (yq cov d) (v8 d a.2) (v8 d b.2) un ka kb ||| v8 d z.2) != BitVec.allOnes 768 then true else
   if !k7 z.1||ws.any (fun v => v.1==z.1) then true else
   if qpools.any (fun qp => d2 qp (cap-1) a b z.1 un ka kb) then true else
     let rest:=(g9 un ka kb a b ws).map Prod.fst
     let links:=if d then l0 else l1
     yy pools links (cap-1) rest (x1 op a b) z.1
lemma e1s {raw T r s ws pools l0 l1 cap tm a b op ka kb}
   (pairs: h7 T r s) (faith: ∀ w ∈ ws,q2 r s w)
   (nd: (ws.map Prod.fst).Nodup) (ha: a ∈ ws) (hb: b ∈ ws)
   (ne: (op==2)=false->a≠b) (hcap: 0 < cap)
   (pv: ∀ p ∈ pools,j5 raw T p)
   (lv0: ∀ tag xs,xs ∈ l0 tag->I1 T (cap-1) 0 (List.toFinset xs))
   (lv1: ∀ tag xs,xs ∈ l1 tag->I1 T (cap-1) 1 (List.toFinset xs))
   (pro: x7 (z7 op a b).1) (fresh: (z7 op a b).1 ∉ ws.map Prod.fst)
   (test: em1 (cap,tm,ws.length,ws,zy ws,pools,pools.map (q9 ws),l0,l1)
     op a b (z7 op a b) ka kb=true) :
   I1 T (cap-1) (d3 tm cap (k9 ws op a b ka kb).length op)
     (k9 ws op a b ka kb).toFinset:=by
 let z:=z7 op a b
 let rest:=g9 (op==2) ka kb a b ws
 let child:=z.1 :: rest.map Prod.fst
 have sub: rest.Sublist ws:=m71 _ _ _ _ _ _
 have ndc: child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
 have val:=m54 op a b
 have fr: ws.any (fun v => v.1==z.1)=false:=by
   apply Bool.eq_false_iff.mpr; intro hh
   obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
   exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
 have pp: k7 z.1=true:=by simpa [k7,x7] using pro
 have leq: 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
   change _=(z.1::rest.map Prod.fst).length
   rw [List.length_cons,List.length_map,z51 _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
 intro k t hk ht h
 have hsz:=(m26 h).2
 change child.toFinset.card+t ≤ k+1 at hsz
 rw [List.toFinset_card_of_nodup ndc] at hsz
 have len: child.length ≤ cap:=by omega
 unfold em1 at test
 change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
 rw [leq,if_neg (by omega)] at test
 let ct:=d3 tm cap child.length op
 have ht0: (ct==0)=true->t=0:=fun hct => by have:=beq_iff_eq.mp hct; change t ≤ ct at ht; omega
 have sep:=m96 h rfl (z50 pairs) (ct==0) ht0
 let d:=ct==0
 have g: (q3 d rest).1=j0 d (g7 r s) (rest.map Prod.fst) :=
   z56 _ _ (fun v hv => faith _ (sub.subset hv))
 have rz:=m69 ha hb (op==2) ka kb d ne
 have hf:=m60 (faith _ ha) (faith _ hb) op
 change v8 d (g7 r s z.1) ||| j0 d (g7 r s) (rest.map Prod.fst)=_ at sep
 change z.2=g7 r s z.1 at hf
 rw [←hf,←g,rz,BitVec.or_comm] at sep
 have be: ((p9 (yq (zy ws) d) (v8 d a.2) (v8 d b.2) (op==2) ka kb ||| v8 d z.2) != BitVec.allOnes 768)=false:=by
   rw [sep,bne_self_eq_false]
 change (if (_ != _) then true else if !k7 z.1||ws.any (fun v => v.1==z.1) then true else if _ then true else _)=true at test
 rw [be,pp,fr] at test
 simp only [Bool.false_eq_true,ite_false,Bool.not_true,Bool.false_or] at test
 have nd': (y4 (x1 op a b) :: rest.map Prod.fst).Nodup:=val ▸ ndc
 have h': j6 T k t (y4 (x1 op a b) :: rest.map Prod.fst).toFinset:=val ▸ h
 by_cases hq: (pools.map (q9 ws)).any (fun qp => d2 qp (cap-1) a b z.1 (op==2) ka kb)=true
 · obtain ⟨qp,hqp,hfc⟩:=List.any_eq_true.mp hq
   obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hqp
   exact m9 (pv p hp) nd' (v57 ha hb (val ▸ hfc)) k t hk h'
 · have hqf: (pools.map (q9 ws)).any (fun qp => d2 qp (cap-1) a b z.1 (op==2) ka kb)=false :=
     Bool.eq_false_iff.mpr hq
   change (if ((pools.map (q9 ws)).any fun qp => d2 qp (cap-1) a b z.1 (op==2) ka kb)=true then true else _)=true at test
   rw [hqf] at test
   simp only [Bool.false_eq_true,ite_false] at test
   by_cases hd: d=true
   · dsimp only [d,ct] at hd; rw [hd] at test; simp only [ite_true] at test
     exact cc1s pv lv0 nd' (val ▸ test) k t hk (by have:=ht0 hd; omega) h'
   · have hdf: d=false:=Bool.eq_false_iff.mpr hd
     dsimp only [d,ct] at hdf; rw [hdf] at test; simp only [Bool.false_eq_true,ite_false] at test
     have hct1: ct ≤ 1:=by dsimp only [ct,d3]; split_ifs <;> omega
     exact cc1s pv lv1 nd' (val ▸ test) k t hk (by change t ≤ ct at ht; omega) h'
def tp1 (ctx: NC1) (a b: y9) (d: Bool): Bool :=
 let op:=if d then 1 else 0
 let z:=z7 op a b
 em1 ctx op a b z false false&&em1 ctx op a b z true false &&
   em1 ctx op a b z false true&&em1 ctx op a b z true true
def tr1 (ctx: NC1) (a: y9) (bs: List y9): Bool :=
 let unOk:=if ctx.2.1==0 then true else
   let n:=z7 2 a a
   em1 ctx 2 a a n false false&&em1 ctx 2 a a n true true
 unOk&&bs.all (fun b => tp1 ctx a b false&&tp1 ctx a b true)
def ta1 (ctx: NC1): List y9->Bool
 | [] => true
 | a :: ws => tr1 ctx a ws&&ta1 ctx ws
lemma au1 {ctx} {ws: List y9} (h: ta1 ctx ws=true) (ht: ctx.2.1 > 0) {a: y9} (ha: a ∈ ws) (keep: Bool) :
   em1 ctx 2 a a (z7 2 a a) keep keep=true:=by
 induction ws with
 | nil => cases ha
 | cons x xs ih =>
   simp only [ta1,Bool.and_eq_true] at h
   rcases List.mem_cons.mp ha with rfl | hm
   · have hr:=h.1
     simp only [tr1,Bool.and_eq_true] at hr
     have hne: (ctx.2.1==0)=false:=beq_eq_false_iff_ne.mpr (by omega)
     have hu:=hr.1
     rw [hne] at hu; simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true] at hu
     cases keep <;> [exact hu.1; exact hu.2]
   · exact ih h.2 hm
lemma ab1 {ctx} {ws: List y9} (h: ta1 ctx ws=true) {a b: y9} (ha: a ∈ ws) (hb: b ∈ ws) (ne: a≠b) (d: Bool) :
   tp1 ctx a b d=true \/ tp1 ctx b a d=true:=by
 induction ws with
 | nil => cases ha
 | cons x xs ih =>
   simp only [ta1,Bool.and_eq_true,tr1,List.all_eq_true] at h
   rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
   · exact False.elim (ne rfl)
   · left; cases d <;> [exact (h.1.2 b hb').1; exact (h.1.2 b hb').2]
   · right; cases d <;> [exact (h.1.2 a ha').1; exact (h.1.2 a ha').2]
   · exact ih h.2 ha' hb'
lemma w45 {ctx a b d} (h: tp1 ctx a b d=true) (ka kb: Bool) :
   em1 ctx (if d then 1 else 0) a b (z7 (if d then 1 else 0) a b) ka kb=true:=by
 simp only [tp1,Bool.and_eq_true] at h
 cases ka <;> cases kb <;> simp [h]
lemma n1s {raw T r s ws pools l0 l1 cap tm}
   (htm1: tm ≤ 1) (pairs: h7 T r s) (faith: ∀ w ∈ ws,q2 r s w)
   (nd: (ws.map Prod.fst).Nodup) (out: T ∉ ws.map Prod.fst)
   (pv: ∀ p ∈ pools,j5 raw T p)
   (lv0: ∀ tag xs,xs ∈ l0 tag->I1 T (cap-1) 0 (List.toFinset xs))
   (lv1: ∀ tag xs,xs ∈ l1 tag->I1 T (cap-1) 1 (List.toFinset xs))
   (checks: cap=0 \/ ta1 (cap,tm,ws.length,ws,zy ws,pools,pools.map (q9 ws),l0,l1) ws=true) :
   I1 T cap tm (ws.map Prod.fst).toFinset:=by
 rcases checks with rfl | checks
 · intro k t hk _ h
   have hk0: k=0:=by omega
   subst hk0
   generalize he: (ws.map Prod.fst).toFinset=S at h
   have eqS: S={_}:=h (fun k _ S => k=0->S={_}) (fun _ _ => rfl)
     (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
     (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
   exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
 by_cases hc: cap=0
 · subst hc
   intro k t hk _ h
   have hk0: k=0:=by omega
   subst hk0
   generalize he: (ws.map Prod.fst).toFinset=S at h
   have eqS: S={_}:=h (fun k _ S => k=0->S={_}) (fun _ _ => rfl)
     (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
     (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
   exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
 have hc': 0 < cap:=by omega
 apply es1 htm1 nd out
 · intro htpos v hv keep fresh pro len
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
   have hf:=m83 nd ha keep
   have hev:=e1s (op:=2) pairs faith nd ha ha (by simp) hc' pv lv0 lv1 pro fresh (au1 checks htpos ha keep)
   have hlenEq: (k9 ws 2 a a keep keep).length=(k0 (ws.map Prod.fst) a.1 keep).length:=by
     have nd1: (k9 ws 2 a a keep keep).Nodup:=by
       unfold k9
       have sub:=m71 ws a a true keep keep
       exact List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
     have nd2: (k0 (ws.map Prod.fst) a.1 keep).Nodup:=by
       unfold k0
       have na: a.1 ∉ (ws.map Prod.fst).erase a.1:=nd.not_mem_erase
       refine List.nodup_cons.mpr ⟨fun hm => ?_,g8 keep a.1 _ (nd.erase _) na⟩
       rw [m23] at hm
       rcases hm with ⟨heq,_⟩ | hm
       · exact fresh (heq.symm ▸ List.mem_map_of_mem ha)
       · exact fresh (List.mem_of_mem_erase hm)
     rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
   rw [hf,hlenEq] at hev
   exact hev
 · intro a ha b hb d ka kb ne fresh pro len
   obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
   obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
   have ab: a≠b:=fun e => ne (congrArg Prod.fst e)
   have one (a b: y9) (aa: a ∈ ws) (bb: b ∈ ws) (ne': a.1≠b.1) (ka kb: Bool)
       (pr: x7 (bin d a.1 b.1)) (fr: bin d a.1 b.1 ∉ ws.map Prod.fst)
       (test: tp1 (cap,tm,ws.length,ws,zy ws,pools,pools.map (q9 ws),l0,l1) a b d=true) :
       I1 T (cap-1) (d3 tm cap (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).length 0)
         (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
     have hf:=m78 nd aa bb ne' d ka kb
     have eq: (z7 (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
     have hop0: d3 tm cap (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).length (if d then 1 else 0)=d3 tm cap (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).length 0:=by cases d <;> rfl
     have hev:=e1s (op:=if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv0 lv1
       (eq ▸ pr) (eq ▸ fr) (w45 test ka kb)
     have hlenEq: (k9 ws (if d then 1 else 0) a b ka kb).length =
         (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).length:=by
       have nd1: (k9 ws (if d then 1 else 0) a b ka kb).Nodup:=by
         unfold k9
         have sub:=m71 ws a b ((if d then 1 else 0)==2) ka kb
         exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
       have nd2: (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
         unfold w0
         let r0:=((ws.map Prod.fst).erase a.1).erase b.1
         have rn: r0.Nodup:=(nd.erase _).erase _
         have ar: a.1 ∉ r0:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
         have br: b.1 ∉ r0:=(nd.erase a.1).not_mem_erase
         have nk:=g8 kb b.1 r0 rn br
         have ax: a.1 ∉ g6 kb b.1 r0:=by cases kb <;> simp [g6,ar,ne']
         refine List.nodup_cons.mpr ⟨fun hm => ?_,g8 ka a.1 _ nk ax⟩
         rw [m23] at hm
         rcases hm with ⟨heq,_⟩ | hm
         · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
         · rw [m23] at hm
           rcases hm with ⟨heq,_⟩ | hm
           · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
           · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
       rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
     rw [hf,hlenEq,hop0] at hev
     exact hev
   rcases ab1 checks haW hbW ab d with hh | hh
   · exact one a b haW hbW ne ka kb pro fresh hh
   · have hsw:=m73 (ws.map Prod.fst) nd a.1 b.1 d ka kb
     have hlenSw: (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).length =
         (w0 (ws.map Prod.fst) b.1 a.1 d kb ka).length:=by
       have ndA: (w0 (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
         unfold w0
         let rA:=((ws.map Prod.fst).erase a.1).erase b.1
         have rn: rA.Nodup:=(nd.erase a.1).erase b.1
         have ar: a.1 ∉ rA:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
         have br: b.1 ∉ rA:=(nd.erase a.1).not_mem_erase
         have nk:=g8 kb b.1 rA rn br
         have ax: a.1 ∉ g6 kb b.1 rA:=by cases kb <;> simp [g6,ar,ne]
         refine List.nodup_cons.mpr ⟨fun hm => ?_,g8 ka a.1 _ nk ax⟩
         rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
         · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
         · rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
           · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
           · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
       have ndB: (w0 (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup:=by
         unfold w0
         let rB:=((ws.map Prod.fst).erase b.1).erase a.1
         have rn: rB.Nodup:=(nd.erase b.1).erase a.1
         have br: b.1 ∉ rB:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
         have ar: a.1 ∉ rB:=(nd.erase b.1).not_mem_erase
         have nk:=g8 ka a.1 rB rn ar
         have bx: b.1 ∉ g6 ka a.1 rB:=by cases ka <;> simp [g6,br,Ne.symm ne]
         refine List.nodup_cons.mpr ⟨fun hm => ?_,g8 kb b.1 _ nk bx⟩
         rw [m24 d b.1 a.1] at hm
         rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
         · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
         · rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
           · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
           · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
       rw [←List.toFinset_card_of_nodup ndA,←List.toFinset_card_of_nodup ndB,hsw]
     rw [hsw,hlenSw]
     exact one b a hbW haW (Ne.symm ne) kb ka (m24 d a.1 b.1 ▸ pro) (m24 d a.1 b.1 ▸ fresh) hh
abbrev PT:=Nat × Nat × Nat × Nat × (Nat->Nat)
def ePT: PT:=(0,0,0,0,fun _ => 0)
def dW: List y9:=wx zq
def dS: List Sig:=dW.map Prod.fst
def dcS (n: Nat) (bits: Nat) (ws: List Sig): List Sig :=
 match n with
 | 0 => ws
 | k+1 =>
   let a:=ws.getD (bits &&& 15) zero
   let b:=ws.getD ((bits >>> 4) &&& 15) zero
   let op:=(bits >>> 8) &&& 3
   dcS k (bits >>> 10) (ws ++ [if op=2 then neg a else bin (op==1) a b])
lemma m116 (n bits: Nat) (ws: List y9) :
   dcS n bits (ws.map Prod.fst)=(c5 n bits ws).map Prod.fst:=by
 induction n generalizing bits ws with
 | zero => rfl
 | succ k ih =>
   simp only [dcS,c5]
   have hget: ∀ i,(ws.map Prod.fst).getD i zero=(ws.getD i y3).1:=by
     intro i
     rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
     cases ws[i]? <;> rfl
   have hcode: (if ((bits >>> 8) &&& 3)=2 then neg ((ws.map Prod.fst).getD (bits &&& 15) zero)
       else bin (((bits >>> 8) &&& 3)==1) ((ws.map Prod.fst).getD (bits &&& 15) zero) ((ws.map Prod.fst).getD ((bits >>> 4) &&& 15) zero)) =
       (j4 ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) y3) (ws.getD ((bits >>> 4) &&& 15) y3)).1:=by
     rw [hget,hget]
     unfold j4 x44 x61
     split
     · rfl
     · split <;> rfl
   rw [hcode,← List.map_singleton,← List.map_append]
   exact ih (bits >>> 10) _
lemma sLm {α β: Type} (f: α->β) (bits: Nat) (ws: List α) :
   k6 bits (ws.map f)=(k6 bits ws).map f:=by
 induction ws generalizing bits with
 | nil => rfl
 | cons x xs ih =>
   simp only [List.map_cons,k6]
   split <;> simp [ih]
def w23: PT:=(0,0,0,0,fun _ => 0)
def lw0 (nb slots sw vw iw pw: Nat) (data: Nat->Nat) (h: Nat): Option (Nat × Nat) :=
 let a:=h % nb
 let sh:=k3 data (a*sw) sw
 let row:=(h / nb+sh) % slots
 let word:=k3 data (nb*sw+row*vw) vw
 some (word &&& ((1 <<< iw) - 1),(word >>> iw) &&& ((1 <<< pw) - 1))
def x62 (t: Nat): Nat :=
 if t < 69 then
   if t < 39 then
     if t < 14 then (t+1) <<< 4
     else if t < 27 then ((t - 12) <<< 4) ||| 1
     else ((t - 24) <<< 4) ||| 2
   else if t < 50 then ((t - 35) <<< 4) ||| 3
   else if t < 60 then ((t - 45) <<< 4) ||| 4
   else ((t - 54) <<< 4) ||| 5
 else if t < 95 then
   if t < 77 then ((t - 62) <<< 4) ||| 6
   else if t < 84 then ((t - 69) <<< 4) ||| 7
   else if t < 90 then ((t - 75) <<< 4) ||| 8
   else ((t - 80) <<< 4) ||| 9
 else if t < 99 then ((t - 84) <<< 4) ||| 10
 else if t < 102 then ((t - 87) <<< 4) ||| 11
 else if t < 104 then ((t - 89) <<< 4) ||| 12
 else (14 <<< 4) ||| 13
def w98 (c: Nat): Nat :=
 if c ≥ 210 then 0x200 ||| (c - 210)
 else if c < 105 then x62 c
 else 0x100 ||| x62 (c - 105)
def y75: Nat->Nat->Nat
 | 0,_ => 0
 | n+1,bits => w98 (bits &&& 255) ||| (y75 n (bits >>> 8) <<< 10)
def vg (depth bits: Nat): Nat :=
 let c1:=bits &&& 3
 let op1:=if c1 == 0 then 0x121 else if c1 == 1 then 0x131 else 0x181
 0x200 ||| (op1 <<< 10) ||| (y75 (depth - 2) (bits >>> 2) <<< 20)
def rN (levels: Nat->PT) (slot i: Nat): Nat × List y9 × List y9 :=
 let raw:=dW
 let (_,depth,_,_,data):=levels slot
 let slen:=2+8*(depth-2)
 let width:=slen+raw.length+depth
 let recp:=k3 data (i*width) width
 let ops:=vg depth (recp &&& ((1 <<< slen) - 1))
 let bank:=c5 depth ops raw
 (ops,bank,k6 (recp >>> slen) bank)
def sS (levels: Nat->PT) (slot i: Nat): List Sig :=
 let (_,depth,_,_,data):=levels slot
 let slen:=2+8*(depth-2)
 let width:=slen+dS.length+depth
 let recp:=k3 data (i*width) width
 let ops:=vg depth (recp &&& ((1 <<< slen) - 1))
 k6 (recp >>> slen) (dcS depth ops dS)
lemma m119 (levels: Nat->PT) (slot i: Nat) :
   sS levels slot i=(rN levels slot i).2.2.map Prod.fst:=by
 unfold sS rN
 rcases levels slot with ⟨num,depth,cw,offw,data⟩
 dsimp only
 have hlen: dS.length=dW.length:=by simp [dS]
 rw [hlen]
 dsimp only [dS]
 rw [m116,sLm]
def y16: Sig:=inputs.getD 0 zero
def y15: Sig:=inputs.getD 1 zero
def y14: Sig:=inputs.getD 2 zero
def y13: Sig:=inputs.getD 3 zero
def y12: Sig:=inputs.getD 4 zero
def y11: Sig:=inputs.getD 5 zero
def y10: Sig:=inputs.getD 6 zero
def z99: Sig:=inputs.getD 7 zero
def z98: Sig:=inputs.getD 8 zero
def v36: List Sig:=[y16,y15,y14,y13,y12,y11,y10,z99,z98]
def v35: List Sig:=[y16,y11,z98,y13,y12,y15,z99,y10,y14]
def v34: List Sig:=[y15,y16,y11,z98,y10,y14,y12,z99,y13]
def v33: List Sig:=[y15,y14,y13,z98,y10,y16,z99,y12,y11]
def v32: List Sig:=[y14,y15,y16,y11,z99,y13,y10,y12,z98]
def v31: List Sig:=[y14,y13,z98,y11,z99,y15,y12,y10,y16]
def v30: List Sig:=[y13,y14,y15,y16,y12,z98,z99,y10,y11]
def v29: List Sig:=[y13,z98,y11,y16,y12,y14,y10,z99,y15]
def v28: List Sig:=[y11,y16,y15,y14,z99,z98,y12,y10,y13]
def v27: List Sig:=[y11,z98,y13,y14,z99,y16,y10,y12,y15]
def w47: List Sig:=[z98,y13,y14,y15,y10,y11,y12,z99,y16]
def w46: List Sig:=[z98,y11,y16,y15,y10,y13,z99,y12,y14]
def z64: Nat->Option (List Sig)
 | 0 => some v36
 | 1 => some v35
 | 2 => some v34
 | 3 => some v33
 | 4 => some v32
 | 5 => some v31
 | 6 => some v30
 | 7 => some v29
 | 8 => some v28
 | 9 => some v27
 | 10 => some w47
 | 11 => some w46
 | _ => none
lemma x21: (List.range 12).all (fun p =>
   match z64 p,zq.autos[p]? with
   | some xs,some perm => xs == dS.map (y7 (perm.map f1).reverse)
   | _,_ => false)=true:=by decide +kernel
lemma x22 (p: Nat): z64 p=(zq.autos[p]?).map (fun perm => dS.map (y7 (perm.map f1).reverse)):=by
 by_cases hp: p < 12
 · have h:=List.all_eq_true.mp x21 p (List.mem_range.mpr hp)
   cases h1: z64 p <;> cases h2: zq.autos[p]? <;> simp [h1,h2] at h ⊢
   exact h
 · have h1: z64 p=none:=by
     unfold z64
     match p with
     | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega
     | _+12 => rfl
   have h2: zq.autos[p]?=none:=Array.getElem?_eq_none (by change vf.size ≤ p; have: vf.size=12:=rfl; omega)
   rw [h1,h2]; rfl
lemma kd (ms: List jg) (n bits: Nat) (ws: List Sig) :
   dcS n bits (ws.map (y7 ms))=(dcS n bits ws).map (y7 ms):=by
 induction n generalizing bits ws with
 | zero => rfl
 | succ k ih =>
   simp only [dcS]
   have hget (i: Nat): (ws.map (y7 ms)).getD i zero=y7 ms (ws.getD i zero):=by
     rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
     cases ws[i]? with
     | none => exact ((m20 ms zero).trans (m79 (q1 ms)).1).symm
     | some x => rfl
   rw [hget,hget]
   have hop: (if ((bits >>> 8) &&& 3)=2 then neg (y7 ms (ws.getD (bits &&& 15) zero))
       else bin (((bits >>> 8) &&& 3)==1) (y7 ms (ws.getD (bits &&& 15) zero)) (y7 ms (ws.getD ((bits >>> 4) &&& 15) zero))) =
       y7 ms (if ((bits >>> 8) &&& 3)=2 then neg (ws.getD (bits &&& 15) zero)
       else bin (((bits >>> 8) &&& 3)==1) (ws.getD (bits &&& 15) zero) (ws.getD ((bits >>> 4) &&& 15) zero)):=by
     simp only [m20]; split
     · exact (qq _ _).symm
     · exact (qk _ _ _ _).symm
   rw [hop,← List.map_singleton,← List.map_append]
   exact ih (bits >>> 10) _
def jd (levels: Nat->PT) (slot i: Nat) (base: List Sig): List Sig :=
 let (_,depth,_,_,data):=levels slot
 let slen:=2+8*(depth-2)
 let width:=slen+dS.length+depth
 let recp:=k3 data (i*width) width
 let ops:=vg depth (recp &&& ((1 <<< slen) - 1))
 k6 (recp >>> slen) (dcS depth ops base)
lemma z63 (levels: Nat->PT) (slot i: Nat) (ms: List jg) :
   jd levels slot i (dS.map (y7 ms))=(sS levels slot i).map (y7 ms):=by
 unfold jd sS
 rcases levels slot with ⟨num,depth,cw,offw,data⟩
 dsimp only
 rw [kd,sLm]
def lS (levels: Nat->PT) (slot: Nat) (pair: Nat × Nat): Option (List Sig) :=
 if pair.1 ≥ (levels slot).1 then none else
   (z64 pair.2).map (jd levels slot pair.1)
lemma ls1s (levels: Nat->PT) (k tm: Nat)
   (names: ∀ x ∈ zq.autos.toList,yp (x0 zq) (x.map f1)=true)
   (earlier: ∀ i < (levels (3*k+tm)).1,I1 (x0 zq) k tm (sS levels (3*k+tm) i).toFinset)
   {pair out} (h: lS levels (3*k+tm) pair=some out) :
   I1 (x0 zq) k tm out.toFinset:=by
 unfold lS at h
 split at h
 · cases h
 next valid =>
   rw [x22] at h
   cases e: zq.autos[pair.2]? with
   | none => simp [e] at h
   | some perm =>
     simp only [e,Option.map_some,Option.some.injEq] at h
     rw [← h,z63]
     exact re1 (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def v20 (levels: Nat->PT) (idx0 idx1: Nat->Nat->Option (Nat × Nat)) (k tm i: Nat): NC1 :=
 let slot:=3*k+tm
 let raw:=dW
 let (num,depth,cw,offw,data):=levels slot
 let (ops,bank,ws):=rN levels slot i
 let start:=num*(2+8*(depth-2)+raw.length+depth)
 let c0:=k3 data (start+i*offw) offw
 let c1:=k3 data (start+(i+1)*offw) offw
 let nr:=c1 - c0
 let st:=start+(num+1)*offw+c0*(cw+depth)
 let rules:=(vv data cw depth nr st).filterMap (fun (a,b) => yh zq ops depth bank a b)
 let ls0:=fun tag => ((idx0 slot tag).bind (lS levels (3*(k-1)))).toList
 let ls1:=fun tag => ((idx1 slot tag).bind (lS levels (3*(k-1)+1))).toList
 (k,tm,ws.length,ws,zy ws,rules,rules.map (q9 ws),ls0,ls1)
def v37 (T: Sig) (c: NC1): Bool :=
 let ws:=c.2.2.2.1.map Prod.fst
 decide ws.Nodup&&!(ws.contains T)
def nv1 (levels: Nat->PT) (idx0 idx1: Nat->Nat->Option (Nat × Nat)) (k tm i: Nat): Bool :=
 let c:=v20 levels idx0 idx1 k tm i
 v37 (x0 zq) c&&(if k=0 then true else ta1 c c.2.2.2.1)
lemma nv1s (levels: Nat->PT) (idx0 idx1: Nat->Nat->Option (Nat × Nat)) (k tm i: Nat)
   (htm1: tm ≤ 1) (samples: h7 (x0 zq) (yx fun j => (zq.samples j).1) (yx fun j => (zq.samples j).2))
   (cols: ∀ ci ∈ zq.cols.values,kp (f3 zq.mask) (x0 zq) (c7 ci.1 ci.2.1) ci.2.2.2.2)
   (names: ∀ x ∈ zq.autos.toList,yp (x0 zq) (x.map f1)=true)
   (prior0: k > 0->∀ j < (levels (3*(k-1))).1,I1 (x0 zq) (k-1) 0 (sS levels (3*(k-1)) j).toFinset)
   (prior1: k > 0->∀ j < (levels (3*(k-1)+1)).1,I1 (x0 zq) (k-1) 1 (sS levels (3*(k-1)+1) j).toFinset)
   (checked: nv1 levels idx0 idx1 k tm i=true) :
   I1 (x0 zq) k tm (sS levels (3*k+tm) i).toFinset:=by
 rw [m119]
 simp only [nv1,v37,v20,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at checked
 have hN:=checked.1.1
 have hT: x0 zq ∉ (rN levels (3*k+tm) i).2.2.map Prod.fst:=checked.1.2
 by_cases h0: k=0
 · subst k
   intro k' t' hk' _ h
   have hk0: k'=0:=by omega
   subst k'
   generalize he: ((rN levels (3*0+tm) i).2.2.map Prod.fst).toFinset=S at h
   have eqS: S={_}:=h (fun k _ S => k=0->S={_}) (fun _ _ => rfl)
     (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
     (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
   exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
 apply n1s (raw:=f3 zq.mask) htm1 samples _ hN hT _ _ _ (Or.inr (by simpa only [h0,ite_false] using checked.2))
 · intro v hv
   apply m48 _ _ _ _ _ (m57 zq) v
   exact (m58 _ _).subset hv
 · intro p hp
   obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
   exact m51 zq cols h
 · intro tag xs hx
   have e: ((idx0 (3*k+tm) tag).bind (lS levels (3*(k-1))))=some xs:=by simpa using hx
   obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
   have h0': 3*(k-1)=3*(k-1)+0:=by omega
   rw [h0'] at h
   exact ls1s levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
 · intro tag xs hx
   have e: ((idx1 (3*k+tm) tag).bind (lS levels (3*(k-1)+1)))=some xs:=by simpa using hx
   obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
   exact ls1s levels (k-1) 1 names (prior1 (by omega)) h
def bk1 (levels: Nat->PT) (idx0 idx1: Nat->Nat->Option (Nat × Nat)) (k tm start: Nat): Nat->Bool
 | 0 => true
 | n+1 => nv1 levels idx0 idx1 k tm start&&bk1 levels idx0 idx1 k tm (start+1) n
lemma x63 {levels idx0 idx1 k tm start n} (h: bk1 levels idx0 idx1 k tm start n=true)
   (i: Nat) (lo: start ≤ i) (hi: i < start+n): nv1 levels idx0 idx1 k tm i=true:=by
 induction n generalizing start with
 | zero => omega
 | succ n ih =>
   simp only [bk1,Bool.and_eq_true] at h
   by_cases eq: i=start
   · exact eq ▸ h.1
   · exact ih h.2 (by omega) (by omega)
lemma m130 {levels idx0 idx1 k tm start a b}
   (ha: bk1 levels idx0 idx1 k tm start a=true)
   (hb: bk1 levels idx0 idx1 k tm (start+a) b=true) :
   bk1 levels idx0 idx1 k tm start (a+b)=true:=by
 induction a generalizing start with
 | zero => simpa [bk1] using hb
 | succ a ih =>
   simp only [bk1,Nat.succ_add,Bool.and_eq_true] at ha ⊢
   exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩
lemma mkB1 {levels idx0 idx1 k tm start n}
   (h: ∀ i,start ≤ i->i < start+n->nv1 levels idx0 idx1 k tm i=true) :
   bk1 levels idx0 idx1 k tm start n=true:=by
 induction n generalizing start with
 | zero => rfl
 | succ n ih =>
   simp only [bk1,Bool.and_eq_true]
   exact ⟨h _ (by omega) (by omega),ih (fun i lo hi => h i (by omega) (by omega))⟩
def v10 (c: NC1) (i j op: Nat) (ka kb: Bool): Bool :=
 let a:=cw1 c i
 let b:=cw1 c j
 em1 c op a b (z7 op a b) ka kb
def cf1 (c: NC1) (d un ka kb: Bool) (op i j: Nat): h6 :=
 let a:=cw1 c i
 let b:=cw1 c j
 p9 (yq c.2.2.2.2.1 d) (v8 d a.2) (v8 d b.2) un ka kb |||
   v8 d (z7 op a b).2
def fb1 (c: NC1) (i j op: Nat) (ka kb: Bool): Bool :=
 let (cap,tm,n,ws,_,pools,qpools,l0,l1):=c
 let a:=ws.getD i y3
 let b:=ws.getD j y3
 let un:=op==2
 let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
 let ct:=d3 tm cap len op
 let z1:=y4 (x1 op a b)
 if !k7 z1||ws.any (fun v => v.1==z1) then true else
 if qpools.any (fun qp => d2 qp (cap-1) a b z1 un ka kb) then true else
   let rest:=(g9 un ka kb a b ws).map Prod.fst
   let links:=if ct==0 then l0 else l1
   yy pools links (cap-1) rest (x1 op a b) z1
lemma fb1s {c i j op ka kb}
   (hlen: ¬(1+(c.2.2.1 - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > c.1))
   (h: fb1 c i j op ka kb=true) :
   v10 c i j op ka kb=true:=by
 rcases c with ⟨cap,tm,n,ws,cov,pools,qpools,l0,l1⟩
 dsimp only [v10,em1,cw1]
 dsimp only at hlen
 rw [if_neg hlen]
 dsimp only [fb1] at h
 have hz1: (z7 op (ws.getD i y3) (ws.getD j y3)).1 =
     y4 (x1 op (ws.getD i y3) (ws.getD j y3)) :=
   m54 op _ _
 set len:=1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
 set ct:=d3 tm cap len op
 set d:=ct==0
 by_cases hcomb: ((p9 (yq cov d) (v8 d (ws.getD i y3).2) (v8 d (ws.getD j y3).2) (op==2) ka kb ||| v8 d (z7 op (ws.getD i y3) (ws.getD j y3)).2) != BitVec.allOnes 768)=true
 · simp only [hcomb,ite_true]
 · simp only [hcomb,ite_false,hz1]
   exact h
def qw (k n: Nat) (xs: List NC1): qy :=
 (k,n,ww xs.length,
   (List.range n).map (fun i => h8 (fun c => (cw1 c i).2) xs),
   j3 (fun c => c.2.2.2.2.1.1) xs,
   j3 (fun c => c.2.2.2.2.1.2) xs)
lemma x57 (k n: Nat) (xs: List NC1) {i: Nat} (h: i < n) :
   f2 (qw k n xs) i=h8 (fun c => (cw1 c i).2) xs:=by
 simp [f2,qw,List.getD_eq_getElem?_getD,h]
def v21 (b: qy) (tm: Nat) (xs: List NC1) (i j op: Nat) (ka kb: Bool): Bool :=
 let (k,n,r,_,u,v):=b
 let un:=op==2
 let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
 if len > k then true else
   let d:=d3 tm k len op==0
   let a:=f2 b i
   let b':=f2 b j
   let z:=zd (r*(BitVec.allOnes 768).toNat) op a b'
   let cov:=if d then v else u
   let mask:=zw r (c4 cov (v1 d a) (v1 d b') un ka kb ||| v1 d z)
   xx (fun c => fb1 c i j op ka kb) mask xs
lemma v78 (k tm n: Nat) (xs: List NC1) {i j op: Nat} {ka kb}
   (hi: i < n) (hj: j < n) {q: Nat} (hq: q < xs.length)
   (budget: xs[q].1=k) (ht: xs[q].2.1=tm) (arity: xs[q].2.2.1=n)
   (pass: v21 (qw k n xs) tm xs i j op ka kb=true) :
   v10 xs[q] i j op ka kb=true:=by
 let len:=1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
 let d:=d3 tm k len op==0
 have eval: v10 xs[q] i j op ka kb =
     if len > k then true else if cf1 xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
     else fb1 xs[q] i j op ka kb:=by
   rcases hxq: xs[q] with ⟨cap,tmm,nn,ws,cov,pools,qpools,l0,l1⟩
   rw [hxq] at budget ht arity
   dsimp only at budget ht arity
   subst budget ht arity
   unfold v10 em1 cf1 fb1 cw1
   dsimp only [len,d]
   have hz1: (z7 op (ws.getD i y3) (ws.getD j y3)).1 =
       y4 (x1 op (ws.getD i y3) (ws.getD j y3)):=m54 op _ _
   rw [hz1]
 by_cases small: len > k
 · simp [eval,small]
 · let r:=ww xs.length
   let a:=f2 (qw k n xs) i
   let b:=f2 (qw k n xs) j
   let cov:=if d then j3 (fun c: NC1 => c.2.2.2.2.1.2) xs
              else j3 (fun c: NC1 => c.2.2.2.2.1.1) xs
   change (if len > k then true else xx _ (zw r
      (c4 cov (v1 d a) (v1 d b) (op==2) ka kb |||
       v1 d (zd (r*(BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
   rw [if_neg small] at pass
   have chosen: cov=j3 (fun c => yq c.2.2.2.2.1 d) xs:=by
     dsimp only [cov]; cases d <;> rfl
   have ca: a=_:=x57 k n xs hi
   have cb: b=_:=x57 k n xs hj
   dsimp only [r] at pass
   rw [ca,cb,m125,m12,m12,m12,chosen,m67,m82] at pass
   by_cases hit: cf1 xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
   · have hlenq: ¬(1+(xs[q].2.2.1 - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > xs[q].1):=by
       rw [budget,arity]; exact small
     apply fb1s hlenq
     apply m126 _ _ _ q hq _ pass
     rw [y42 _ _ _ hq]
     exact beq_iff_eq.mpr hit
   · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def bp1 (b: qy) (tm: Nat) (xs: List NC1) (i j op: Nat): Bool :=
 let f:=v21 b tm xs i j op
 f false false&&f true false&&f false true&&f true true
def br1 (b: qy) (tm: Nat) (xs: List NC1) (i: Nat) (js: List Nat): Bool :=
 let unOk:=if tm==0 then true else
   v21 b tm xs i i 2 false false&&v21 b tm xs i i 2 true true
 unOk&&js.all (fun j => bp1 b tm xs i j 0&&bp1 b tm xs i j 1)
def w41 (b: qy) (tm: Nat) (xs: List NC1): List Nat->Bool
 | [] => true
 | i :: js => br1 b tm xs i js&&w41 b tm xs js
lemma v77 (k tm n: Nat) (xs: List NC1) {q: Nat} (hq: q < xs.length)
   (budget: xs[q].1=k) (ht: xs[q].2.1=tm) (arity: xs[q].2.2.1=n) (js: List Nat)
   (bounds: ∀ j ∈ js,j < n) (allRows: w41 (qw k n xs) tm xs js=true) :
   ta1 xs[q] (js.map (cw1 xs[q]))=true:=by
 induction js with
 | nil => rfl
 | cons i js ih =>
   simp only [w41,Bool.and_eq_true,br1,List.all_eq_true] at allRows
   simp only [List.map_cons,ta1,tr1,Bool.and_eq_true,List.all_eq_true,List.mem_map]
   have hi:=bounds i List.mem_cons_self
   have check:=@v78 k tm n xs
   have hun: (if xs[q].2.1==0 then true else
       em1 xs[q] 2 (cw1 xs[q] i) (cw1 xs[q] i) (z7 2 (cw1 xs[q] i) (cw1 xs[q] i)) false false &&
       em1 xs[q] 2 (cw1 xs[q] i) (cw1 xs[q] i) (z7 2 (cw1 xs[q] i) (cw1 xs[q] i)) true true)=true:=by
     rw [ht]
     cases htm: (tm==0)
     · simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true]
       have h1:=allRows.1.1
       simp only [htm,Bool.false_eq_true,ite_false,Bool.and_eq_true] at h1
       exact ⟨check hi hi hq budget ht arity h1.1,check hi hi hq budget ht arity h1.2⟩
     · simp
   refine ⟨⟨hun,?_⟩,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
   rintro _ ⟨j,hj,rfl⟩
   have hj':=bounds j (List.mem_cons_of_mem _ hj)
   have both:=allRows.1.2 j hj
   have opCheck (d: Bool) (pass: bp1 (qw k n xs) tm xs i j (if d then 1 else 0)=true) :
       tp1 xs[q] (cw1 xs[q] i) (cw1 xs[q] j) d=true:=by
     simp only [bp1,Bool.and_eq_true] at pass
     simp only [tp1,Bool.and_eq_true]
     exact ⟨⟨⟨check hi hj' hq budget ht arity pass.1.1.1,check hi hj' hq budget ht arity pass.1.1.2⟩,
       check hi hj' hq budget ht arity pass.1.2⟩,check hi hj' hq budget ht arity pass.2⟩
   exact ⟨opCheck false both.1,opCheck true both.2⟩
def rb1 (k tm n: Nat) (xs: List NC1): Bool :=
 w41 (qw k n xs) tm xs (List.range n)
lemma rb1a {k tm n} {xs: List NC1} {q} (hq: q < xs.length)
   (hb: xs[q].1=k) (ht: xs[q].2.1=tm) (ha: xs[q].2.2.1=n) (hn: xs[q].2.2.2.1.length=n)
   (pass: rb1 k tm n xs=true): ta1 xs[q] xs[q].2.2.2.1=true:=by
 have all:=v77 k tm n xs hq hb ht ha (List.range n) (fun _ => List.mem_range.mp) pass
 have eq: (List.range n).map (cw1 xs[q])=xs[q].2.2.2.1:=by
   apply List.ext_getElem
   · simp [hn]
   · intro i h1 h2
     simp [cw1,List.getD_eq_getElem?_getD,h2]
 rwa [eq] at all
def w99 (levels: Nat->PT) (idx0 idx1: Nat->Nat->Option (Nat × Nat)) (k tm start n: Nat): List NC1 :=
 ((List.range n).map (start+·)).map (v20 levels idx0 idx1 k tm)
def cc1 (levels: Nat->PT) (idx0 idx1: Nat->Nat->Option (Nat × Nat)) (k tm start n ar: Nat): Bool :=
 let xs:=w99 levels idx0 idx1 k tm start n
 xs.all (fun c => c.2.2.1==ar&&v37 (x0 zq) c) &&
 let b:=qw k ar xs
 (List.range ar).all (fun i => br1 b tm xs i (List.range' (i+1) (ar - (i+1))))
lemma cb1 {levels idx0 idx1 k tm start n ar}
   (h: cc1 levels idx0 idx1 k tm start n ar=true) :
   bk1 levels idx0 idx1 k tm start n=true:=by
 unfold cc1 at h
 rw [Bool.and_eq_true] at h
 let xs:=w99 levels idx0 idx1 k tm start n
 have hrun: rb1 k tm ar xs=true:=by
   have go (lo num: Nat) (eq: lo+num=ar) :
       w41 (qw k ar xs) tm xs (List.range' lo num)=true:=by
     induction num generalizing lo with
     | zero => rfl
     | succ num ih =>
       simp only [List.range'_succ,w41,Bool.and_eq_true]
       refine ⟨?_,ih (lo+1) (by omega)⟩
       have ok:=List.all_eq_true.mp h.2 lo (List.mem_range.mpr (by omega))
       simpa only [show ar - (lo+1)=num by omega] using ok
   unfold rb1; rw [List.range_eq_range']; exact go 0 ar (by omega)
 apply mkB1
 intro i lo hi
 have hm: v20 levels idx0 idx1 k tm i ∈ xs:=by
   apply List.mem_map.mpr
   exact ⟨i,List.mem_map.mpr ⟨i - start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
 obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
 have one:=List.all_eq_true.mp h.1 _ hm
 simp only [Bool.and_eq_true,beq_iff_eq] at one
 have hb: xs[q].1=k:=by rw [e]; rfl
 have ht: xs[q].2.1=tm:=by rw [e]; rfl
 have ha: xs[q].2.2.1=ar:=e ▸ one.1
 have hn: xs[q].2.2.2.1.length=ar:=by rw [e]; exact one.1
 simp only [nv1,Bool.and_eq_true]
 refine ⟨one.2,?_⟩
 split
 · rfl
 · exact e ▸ rb1a hq hb ht ha hn hrun
def cs1 (levels: Nat->PT) (idx0 idx1: Nat->Nat->Option (Nat × Nat)) (k tm start n ar: Nat): Nat->Prop
 | 0 => cc1 levels idx0 idx1 k tm start n ar=true
 | d+1 => cs1 levels idx0 idx1 k tm start (n / 2) ar d /\ cs1 levels idx0 idx1 k tm (start+n / 2) (n - n / 2) ar d
lemma xh {levels idx0 idx1 k tm start n ar d}
   (h: cs1 levels idx0 idx1 k tm start n ar d) :
   bk1 levels idx0 idx1 k tm start n=true:=by
 induction d generalizing start n with
 | zero => exact cb1 h
 | succ d ih =>
   have v:=m130 (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
lemma w96 (levels: Nat->PT) (idx0 idx1: Nat->Nat->Option (Nat × Nat)) (top: Nat)
   (prior: Nat->Nat)
   (lo: ∀ m,k5 (f3 m) (y0 m) (prior m))
   (valid: w5 zq prior=true)
   (v18: ∀ k ≤ top,∀ tm ≤ 1,bk1 levels idx0 idx1 k tm 0 (levels (3*k+tm)).1=true) :
   ∀ k ≤ top,∀ tm ≤ 1,∀ i < (levels (3*k+tm)).1,I1 (x0 zq) k tm (sS levels (3*k+tm) i).toFinset:=by
 simp only [w5,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
 have pairs:=m66 valid.1.1.1 valid.1.1.2
 have cols: ∀ ci ∈ zq.cols.values,kp (f3 zq.mask) (x0 zq) (c7 ci.1 ci.2.1) ci.2.2.2.2 :=
   fun ci hc => m50 ci prior lo (valid.1.2 ci hc)
 have names:=valid.2
 intro k
 induction k with
 | zero =>
   intro hk tm htm i hi
   have hb:=v18 0 hk tm htm
   exact nv1s levels idx0 idx1 0 tm i htm pairs cols names
     (fun h => False.elim (Nat.lt_irrefl 0 h))
     (fun h => False.elim (Nat.lt_irrefl 0 h))
     (x63 hb i (Nat.zero_le i) (by simpa using hi))
 | succ k ih =>
   intro hk tm htm i hi
   have hb:=v18 (k+1) hk tm htm
   exact nv1s levels idx0 idx1 (k+1) tm i htm pairs cols names
     (fun _ j hj => ih (by omega) 0 (by decide) j hj)
     (fun _ j hj => ih (by omega) 1 (by decide) j hj)
     (x63 hb i (Nat.zero_le i) (by simpa using hi))
def v47 (i: Nat): Nat:=0x373268e197225eaec74ba7d6b5f70686be9172ca2772
def pL24: PT:=(3,7,7,1,v47)
def v46 (i: Nat): Nat:=0x310c02e017005801bab6d416a0b9520160068035e80016026eb1756dab69836b1750d5a4e739ce738420f735ac52508418a5294a5294a52908418841002c77d1addc44d73ae8d72261ab9db46b912f57cd9865c897ab0bfdcc6ad1f386feca3568f9c3ef2f1ab47ce1fe738d5a3e60ffb35fd4b53c7e57e19f5a983fecd7f52d651efa35bb889aa77d1addb44d53be8d6ee626957ec36683134deda35c897abef83c354335d73e5762619f5c2ff9174bee0ed76ba6b5f707e7a3eb5afb83f3d1f5ae19c1a3df46b753126d795c7cb68732fb31b5c8b81f74a45aa9dacfbe0f0d54ed651bf995cb2dca8dfaedb596e527be8d722772c37eb96513b961bf5cb286dcb0dfae59426e547be8d6ee356a3df46b763ab55afa35b48d5aaf6d1adbdeadc6fac9adab72a3df46b763aa51efa35ba9d52af6d1adbe6a906ff3d6d2372
def pL27: PT:=(42,6,7,5,v46)
def x86 (i: Nat): Nat:=0x424
def w59 (h: Nat): Option (Nat × Nat):=lw0 2 3 2 6 2 4 x86 h
def v45 (i: Nat): Nat:=0x170137a01d00e807403a01d00e80000fc05c02b805c01e01c02f01780bc05e02d80780bc05602f01780bc05700e015c03805c02022012ba01e02001f009e01e00f00533cd2c91c50c0fbcf3cf3cebae38e36db4cb0bacaaaa2692281e71c71c71c71c71a69861659659651249040e30c28820618618410205cd95d89867aa55f30d9973859b72198de9c2cd78c690f4e166bcbfb3176ab36e5fd58bb559bd2fe605daaedb17f0cf4d551be5dc8489ba55f30d9a0c4d7b62b062261abce5765f13095ef0822f8984af784c8c44c252ef186cc8deabdb11c8112f55ed88e3f897aaf6c561144bd57b63048e19eabdb182430cf576d86489867aaf6c2ec4c33d5fa61222619eaa7d546aa4770e2eebfa2552269b751aadc9134f3a8d56a889a7b51cab5444e6f2bf8d2c22717760512fc4b8dbaea897e25c6f97502bf12e3da8663a989756d605491433ad6aeaa48a19d5e4c1291308eef082c022846db95db044c237bc2095a2611d5e4c17d1308ebf060818984777860448bc237bc238ba25f5bde11c5912fadef09923897d7d6c54c4c33eb7bc2395611f5bde11ca908fadef0c122847d6ff05191423ebebc1862611f5bde0c31308fafeb04989847d75da304943bcb7bc3048a11e5e9e97efad6d4dfb0b424786b33bc5d550bb519de18ed9f1a8af7168c6f0d463b6492fa1be30bf2e2850d495ee2d09200b0c778c6957cf06fb0b32c237833dc31d943bc1bec18e4a1de0df60b9250ef057f0648984783d6c44c33ebd1ebc22611f5e0
def pL28: PT:=(71,6,7,6,v45)
def v44 (i: Nat): Nat:=(if i<2 then (if i<1 then 0xfecae0accf7eaae0accfbe86e0accfee32e0accff9cee0ac97fd72fe4ca7fd72fa4cb5fd72da4ca7fd72a64cefd5e17e4897fd72fe488ffd8efa48a7fd72fa4897fd72e6488ffd8ea648a7fd72a64897fd72fe44c7fd6afe448ffd8efa44a7fd72fa4497fd72e644c7fd6ee24497fd72ca44c7fd6ec644c7fd6e5a44b7dd725244e7dd6a5244a7fd72fa24a7fd72a624c7fd6ea624b7ed72da1cfde5f2da1cb7ed729e1cb7ed72521cb7ed72461c97fd72fe18a7fd72fa1897fd72ca18b7ed722618a7fd72fa1097fd72ca1097fd72aa10a7fd72a610b5fd72d9f0b7f5729df0b7f57295f0fee61e95f0b7f57251f0bef6ccadf0bf76acadf0bfb688adf0bfe634adf0bff1d0adf0b7f57249f0fee61e49f0b7f57245f0bdf6e959e0fed64abde0fee61eb9e0b7f5729de0bdf6e8f9e0bef6ccf9e0bfd660f9e0bfe634f9e0bff1d0f9e0b7f57295e0fee61e95e0fee61e49e0b7f57245e09ff58e25e0ffc61225e097ff0376a497fd8ea5c097fd8e45c0f37e9e45c0b7f9d245c0f7d9ae45c0a7ff269dacc7ff229dacf7e9aa9daca7fd72db72cefedacb72cefeca9f72cefeca9b72cefeca5372cefeca4f72cefeca4772cefec8a372a7fd722772cefeca2772a7fd721b72cefeca1b72a7fd721372cefeca1372a7fe616b5ea7fe356b5ec7fd6ec75ed6fd6d235ed7f56def5ea7fead6b56a7fd72e356c7fd6ee356c7fd6ec756d6fd6d2356d7f56def56e7f569eb56e7f9adab72c7fd6ebb71a7fd729f71c7fd6e9f71adfee8fb71aefeccfb71afde60fb71afee34fb71aff9d0fb71a7fd729771a7fd724771a7fd721b71c7fd6e1b71cfee321b71a7fe356b69a7fd72e369c7fd6ee3698ffe357f5da7fe356b5dc7fd6ec75dd7dd6e4b5dc7fe31c371a7fd72db70c7fd6edb70c7fd6ebf70a7fd729f70adfee8fb70aefeccfb70afbe88fb70afde60fb70afee34fb70aff9d0fb70a7fd729770a7fd725370c7fd6e5370adfee8af70aefeccaf70af7eacaf70afbe88af70afee34af70aff9d0af70a7fd724770c7fd6e477097fead6f6897fe616f68c7fd6ee368a7fd725b68c7fd6e5b68d7f56df368d7f56de368a7fe616b5cc7fd6ec75cd7ed6e1f5cc7fd6ec7548ffd8ea754a7fd72a754c7fd6ea754d7f56df354e3fe9dc370a7ff01b770e7f9c1b770a7feadaf70e7f9c1af7087ff7aa96987ff7afd6887ff7aa9688efecf76e287fd7376f98efecf76f98fee3776e187fdd376a587fd7376f88efecf76f88dfeeb76a487fd7376588eff312372c6fd6d237287fd72e772c6fd6ecb7287fd72cb72c6fd72cb7287fd72ab7287fd725f7287fd723372c6fec9af72c6fec9ab72a7be896f7187ff016f7187fead6f71c7be896f7187fe356f7187fd72ff7187fd72e77187fd72cb7187fd72ab7187fd7233718dfee97f5dc7ee321b7197be896f54 else 0x8ee24aa7fd72e24ac7fd6ee24ac7fd6a30a2c7fd6cb62ecefd225c8aa7fd72e226c7fd6ee226b3fd72da26d3fd6eda26b3fd72e626d3fd6ee626d3fd6eba26b3fd72aa26d3fd6eaa26bafecd0626bbbe890626fb6e190626eafd210226bbee350226abfd829626b9fee8ba26bafeccba26bb7eacba26bbbe88ba26bbf9d0ba26bbee34b626d3fd6e4e26d3fd6e4a26bbee34a22697fd72fe22e5fd6a4e22c7fd6ec61ad6fd6d221afaee25221ab3fd72261ae7ed6a221ac7fd6a5c76a7fd732212c7fd6ae612a7fd72e212ebee26e212c7fd6ec612d6fd6d2212faee252212d3fd6ebe12e7dd6a4e12fbce264e12c7fd6b7612c7fd6aa86eb5fd72d9f2b7f5724deeb7f57219eefbe62619eeb7f57211eefbe62611eeb7f572d9eae7f56a4deab7f57249eafaf6be49eab7f57225eab7f57211eae7f56a11eafbe62611eaf7e9aa19aecfec8d56e1cfec8d5ae18fff0376e1a7fd72fad9e5fd6ae2d9bdec92e2d9c7fd6b76d98ffd8edac5c7fd6edac5a7fd72e2bd97fd72feb9c7fd6afeb9a7fd72fab9e5fd6adab98ffd8edaa5c7fd6edaa5c7fd6ebaa5d5fee568f9d6fec968f9d7de5d68f9d7f9cd68f9c7fd6a5cf9b5fd72da99e5fd6ada9997fd72e695c7fd6ae695c7fd6ee295e6fd6abe95e6fd6aba95a7fd72fa51a7fd72e251c7fd6b765197fd72fe4dc7fd6afe4da7fd72fa4de5fd6ada4d97fd72fe49a7fd72fa4997fd72e649a7fd72e249a7fd72a649d7dd6eda4997fd72ca45c7fd6ec645d7dd6e4a45adfee9562da7fd732225adfee97e25a7fd72fa258ffd8ee225efce12e2258ffd8ec6258ffd8ea625a7fd72a625ffc6120225cefd7e961de6fd6a961da7fd72fa19c7fd6efa1997fd72ca19c7fd6ec619d7dd6e4a19bbef008a19bdeee88a19bfe9d08a19afed822619b7ed722619ebeefa2619a7fd72fa1197fd72ca1197fd72aa11a7fd72a611b7dd724611ebeefa2611fbce522611bddee95611bfce355611fbce26da11b7dd72ca11d7dd6ebe11b7dd72aa119fdf30fa11bddee8fa11bedeccfa11bfce34fa11bfd9d0fa11b7dd729611b7f57295f5faf6be95f59ff58e49f5faf6be49f5ffc61225f5b7f57219f5fbe62619f5fbe62611f5b5fd72d9f1e5fd6ad9f1c7ff217dc1b5fee97dc1f7d9ad7dc1a7fd8231c1f7d9ae19c1c7fd6cbaf8cefd24baf88ffe6376f8a7fd72fad8c7fd6efad8a7fd72dac497fd72feb8a7fd72fab88ffd8edaa4a7fd72daa4c7fd6edaa4c7fd6ebaa4c7fd6cbaa48ffe6376a4c7fd6a5cf897fd72fe98b5fd72da9897fd72fe9497fd72e694c7fd6ee2948ffd8eda58c7fd6eda58c7fd6ebe58c7fd6eba58adfee8fa58aefeccfa58afde60fa58afee34fa58aff9d0fa58a7fd7296588fff037658a7fd732250a7fd72fa50c7fd6ee250c7fd6ec650a7fd72a650c7fd6ea650c7fd6b7650ce) else (if i<3 then 0x1303c0b00bf6fcbeaf8bdef5bcef1bbeedbaeeaba2e6b92e2b82deb76dbb66d7b56d3b46cfb36cbb26c8b1ec6b1ac5b12c3b0ac0afabdaeab8adab4acab1abeafab6acaaaa9a9ea5a8aa0a7e9da729aa6298a5a94a4a90a3e8ea328aa2687a1a84a0e82a06819fe7d9ea799e6789de749ca709ba6d9ae6999e6598e6197e5d96e5995e559525394a519424f9364b926469164490e418fe3d8ee398de368d6348ce328ca318c22f8b62c8aa28896228821d86e1a86617856138460f83a0b8220580e01801fe7f5fb7e5f87e1f87d9f57d1f37c9f17c1ef7b9ed7b1eb7a9e8799e4789e177ddd771da765d8761d4749d0739cc729c8719c3705bf6f1ba6e1b76d5b36c5b06b9ac6a9a8699a4689a06799c669986599464d9163d8d62d8961d8560d815fd7d5ed795dd755d1725c16e5b16a5a166591625815e5715a5615655955551525414f5394d5314a5214651544509404f93c4ed394e1374d9354d1334c9314c12f4b92c4ad2a4a527495234851f4791c4691945d16451134390e4350d429084210641503404ff3f4fb3e4f83dcf53ccf13c0ee3b0ea3a0e7394e3384df374dc370db360d6350d2340ce330ca320c7314c2300be2f0b92dcb52ccb22c0ae2b0aa2a0a6290a22809e2709a26096250922408e2308a22086210822007e1f07b1e8781d8751cc711bc6d1b06b1a4681986518c601785b15c541404e12c48114410f83b0e4370c82e0b0280901f0701a060160501203c0d02c090180300400c7fd0a5d6ac7fd0a316a97fead6edad3fe9d6eda97fe616eda97fe356eda97ff796edaa7fe616a9aa7fe356a9a8ffe617e968ffe357e9697fe616e9697fe356e96a7fead6a4e8ffe357e4a97fead6e4ac7fea56e4a97fe356e4a97fead6e26b3fead6e26e3fd6ee2268ffe617e1e8ffe617e1aa7fe616a1af3ed72261a97fead6e12a7fead6a12f3f57225ea8ffe357ed997fead6ed9d3fe9d6ed9e5fee96ad9a7fead6ad9a7fe356ad9a7ff796ad9a7fe356abda7fead6ab9a7fe356ab9a7fe3568f9cfef2630f9dfce6230f9dfe60630f9a7fe356a998fff017e958ffe357e9597ff016e95a7fe356a95a7fead6a51a7fead6a4dd7de9d6e4997fead6e25a7fead6a258fff017e1d8fff017e1997ff016e19a7ff016a19c7fefea5a9f7e619f5a997fead6ed8d3fe9d6ed897fe616ed8a7fe616a9ccfdf265cf8dfd6065cf897ff016e9497fe616e9497fead6e50a7fead6a5097ff016e4897fead6e4897ff016e4497fead6e24c7fefe59b4c7fd82a9acc7fd8ea5acc7fefea5ace7faa5c1acb7ef0245a8f76e9e45a8f7ce5245a8c7fd6cbae2cefd24bae28ffe6376e2a7fd72a6dac7fd6ea6dacefd225d02cefd223102b5fd72da9acefd22e4b6a7fd72e0b6a7fd72a4b6cefd2230b6a7fd72e25297fd72fe4eb5fd72da4ec7fd6b764e8ffd else (if i<4 then 0x541ec85403400411c0f800411c03400400c0040340040340050de77400411c00411c034006c02c01208c000b411c11e6a400c004034006a1800d5080ac0adc0003400403400400c01003400403412811c0450e90e90e90e90e88e88e88e8057401c00187c00004034090148020326d142180000f81b419408c01c00419504504403401c15800c0ec00c00400c006a08037c00847c00134844035c0084436484419884421801c0048e800c01001c004014057208054326ae00f40140140b80b80b80172081b45d383b57c0fa8381e657fc0323b83803683bc0271411e209d03400190926c1801419815c035c02c3803400004c034006adb71400c11832400c00403400400403436400c118034004034005c0000400003d82400c00503000c00400c00400c0040040000340040340040340040af0000af0030000af0000ac00500000c004004001c0003400400c00400c00403400400c11803400692e80292e80292e80092c04000480000c0040340043250300341380f800c0040f80340340f800c0040040000340f800c0040340040000c403400400c00400c00400c00400c00400c0066a5c0001c00400c15f2090f320b2084df20800c01001c1588e80b801c0040f48e800c01001c00721800f32332017b21b32332332034332321817b3232380541e743b21b2181972181972181952181972181972180f343a4381e448832604819402400eca402401c5d416400c57c9740740400041c0010005c02c029aac02d5698ac02c001f2c001bec3ac00032c000b0006c18134180006c000a80340a801c00c0040ec00ead803c03403400400c0ec00c0040ec00ead8c180910640040440040901c40af0000af00003f0000af0000050000440040b404400506411801ef140ac05401c034006a1800413000400005401c00c006a080280040050300050300300040240040af0000af0000af0000af00001f00000500002400402400403000404f00004f00004f00004f00001f00000500002400403000402400c02400c00c00403400400c006b22a1805403400c006a0800c00400400003400400c11aa18c0000c004ca4004074c380ac07c0dc1f007c0ac07c3d41f007c0640dc1f007c3d41f007fd7f5540fc07c0340d00dc1f007c3d41f007fdd3c800c00641581e407c3801f007d5241cc0f411c0d01f007c11803c01c3d40d1c681f43800f40b00d00dc01c1f00d003c11c10c07eca6c1bd17c61181183d1407c00c05c18c0900ac09000405c0281480640040900040900901100040900640900d3dd0364092d5414805f92e4b92e438fe378be2787e1782e037edeb78dd773dc76edb36bdab68d9b64d8f61d7f5fd775bd6b59d5f55d4f51d3f4dd2747d1b44d0b40cfb3cceb38cdb36cd332cbf2ccab27c9322c831ec731ac6316c5312c430ec330ac2306c else 0xc1101101e4013ad97200100ec15403415401f4d80b010c00010c1801e41805140f40fc034139c1800403400c11000c0ec1800f40fc00c1100ba2180040340040001340bc0b800c11004801c00400004400c36400411c0ac01c8540041ec05401c0ac03405401e08c05403401c0ad8000b9a3819405401c00403400400004403401c8540ac03403412804400c0ac0583dc004035d7c00400004400f7140bc0fc0b805803405803402400c36731402400c0540340ad801a1819400c03002400c02400c0ac03400c03002400c02400c00c010054007c600c291407419d91643b000c3b000ca7001c02c3ac0000400003400400c11219c10e40010fada402538035c00035c0240219403400400c0efad80340040f80340340f800c0ec01c004035c0244a400004036ada723ada720014016a0801415c0b80b80b8036ca40340b83decd803418721818721b2181972181940141972084dc0f40b800c0ee61800c0040ec034980110035c00134134004035c0001c00401c00400c0054480349800340f6a0a61ad140340040bc037adb2d800f2d81134db2db4da7572a400c9d34a41b72a5c032a74a40fc11c14a88c14811c0040000340048)))
def pL30: PT:=(506,5,7,10,v44)
def x85 (i: Nat): Nat:=0xd0180e004540501c609040641ab081e07c24029c400c00008000a00b0002201c040300904d83604252091906c1225826074050841505c0013c230a400040c20200f058110801809c0005a101500083a336c70010220cf
def w58 (h: Nat): Option (Nat × Nat):=lw0 18 59 6 10 6 4 x85 h
def v43 (i: Nat): Nat:=(if i<6 then (if i<3 then (if i<1 then 0xfafd5a588ffb315258afba8952588ff98eda58cf7aa906588ffb30fe588ffb30fa58adfae8fa58aefaccfa58afba88fa58afda60fa58afea34fa58aff204fa588ffb26fcb48ffb26a8b48ffb32f8b08ffb32a4b0cff2fa00b0dfe09200b08ff9732250cef92b22508ffaad7e508ffb256e508ffb316a508ff97320ac8ffb3168accdf96ae4accef96ac8accefae2c8accf7b26a8accf796aa8accf7ae2a8ac8ffb32a4accdfae6a4accefacaa4accf7aaaa4accfb96a84accfbae284accfbaa684ac9fe97230accfe96a30accfeae230accfeaa630accff16a00accff2e200accff2a600ac8ff973224c8ffb017e4c8ffaad7e4c8ffb256e4c9ff2056e4ccdf97eda4c8ff97322488ffb017e488ffaad7e488ffb256e488ff98efa488ff98ea6488ff9732244cdf94722448ffb017e448ffb256e448ffb316a448ffb32fa448ff98efa448ff97320a08ffb3168a08ffb32f8a0cff16a00a0cff2fa00a09feb30f884afeb24f884bdeae8f884beeaccf884bfaa88f884bfca60f884bfe204f8849feb30ac84afeb24ac84bdeae8ac84beeaccac84bf6aacac84bfaa88ac84bfe204ac84afeb24a084bfe204a0849fba896e248ffb316a24bdf2e85e24dee96e961cbfe204b21cdee96e4a1cbfe204a21c8ffb316a188ffb316a108ffb256df48ffb3169f4aff32551f0bfb28951f0bdf172d9f0aff324adf0bef2ccadf0bf72acadf0bfb288adf0bfe234adf0fde2da1df0fee2961df0fee24a1df08ffb256de88ffb3169e897f972a9e48ffb256de08ffb3169e0beeacc8de0aff32559e0bdf2e959e0bfb28959e0cff18ef9e0eef12af9e0efd0bef9e0ebf2f955e0aff32551e0bfb28951e09ff330f9e0aff324f9e0bdf2e8f9e0bef2ccf9e0bfb288f9e0bfd260f9e0bfe234f9e0efd2f8b1e0bfd2ccb1e0bfd234b1e0aff18249e0efd18249e0bfd17249e0efd2fa49e0fed2be49e0fed27249e0aff18245e0bfe2cc8de0dfe2c88de0dfe2a88de0ffc0b08de0ffc2488de0bfe2cc85e0ffc24885e09ff18e25e0fed24a1de0bfe18e1de0bfe1721de0efe2fa1de0dfe2e61de0fee2ca1de0fee2ba1de0fee2961de0ffc0b21de0fee24a1de0bfd17211e0efd2fa11e0bfd2ce11e0ffc22611e0ffc21e11e0ffc21611e087ff32a5acf7e1d1e1a8e7eaa5ada8f7ca45ada8ebea2619f4ebea2611f4ebf225f5e8ef7219f5e88ff98e25e0cbfafe25e0efca2611e0cff2a9f5e0ebf225f5e0efd211f5e08ffb329ddc8ffb3251dc8ffb3245dccff2fde1dc9bf18de9c28ef982c8768ef982c86efae2261deefa72be95eafb622619ea8dfae97dc18dfae97da98efacd7da98dfae97e25ced97e4a1dbbcb008a11bf8a888a11fad2be49f5fbc22611f5f3d1f5c1adbde2e85da8bfc2605da89fe18df1a8fce2ba1df0bee2cc8de0fec24a1de0f7c1e1ada8 else (if i<2 then 0x7df5a9e7daa5ada9f7d1f5ada987fead6ef887fe616ef8c6fd6d26f8cef925cef887fd7322d887ff256ed887fd7322bc87ff016ea487fe616ea4c5fd6d42a4cdf941cea487fd73229c87ff316a9c87fd7320f887ff3168f8c5fd6ae4f8c6fd6ac8f8c7bd6a84f8c7dd6a5cf8c7ed6a30f8c7f56a00f8c7f969ccf887fd73229887fd73229487ff256e9487ff016e5887fead6e5887fd73225087ff256e5087ff316a5087fd73224c87fd73224887ff256e4887fd73224487ff256e4487ff316a4497be896e2487fd7321f4b5f572d9f0fce6ba1df087fd7321e8b7d57249e0bee6cc8de0bfe1d08de0fec64a1de0a7f972fdc8a7f972a9c88ffb30f9c8adfae8f9c8aefaccf9c8afba88f9c8afda60f9c8afea34f9c8aff204f9c88ffb30adc8adfae8adc8aefaccadc8af7aacadc8afba88adc8afea34adc8aff204adc88ffb30a1c8aff204a1c8c7f97321c0cef92b21c08ffaad7dc08ffa617dc0a7f972f9c08ffb017dbc8ffaad7dbc8ffa617dbcfde21df1bcfed249e1b8c7f97321b4cdf94721b48ffb32f9b4a7f972a5b48ffb32f9ac8ffb32a5aca7f972a5acefd2f9e1acdfd2c9e1acffc091e1acffc21de1aca7f972f9a8a7f972a5a8dfd25de1a8ffc211e1a8b7e972fda8b7e972f9a8b7e972a5a8e7e972a5a8ede946a5a89feb30f9a8afeb24f9a8bdeae8f9a8beeaccf9a8bfaa88f9a8bfca60f9a8bfe204f9a89feb30ada8afeb24ada8bdeae8ada8beeaccada8bf6aacada8bfaa88ada8bfe204ada8afeb24a1a8bfe204a1a8dfe2a85da8bfe2605da8dfe25c5da8fde2e5f1a8fde2d9f1a8dfe2c9f1a8fde2b9f1a8efe2a5f1a8afeb25e9a8dfe18de1a8bfe2e9e1a8dfe2c9e1a8ffc25de1a8ffc249e1a88ffb26fda4a7f972f9a48ffb26a9a4a7f972a5a48ffb265da4cef92afd688ffaad6ef88ffa616ef8cef96d26f8cefae526f8cef926aaf8cf7aa906f8cef92686f8afd8be86f8cef9265ef8cef924baf8cfda5cbaf88ffb016ee08ffaad6ee08ffa616ee0afba8952e08ff97322d88ffaad7ed88ffa617ed88ffb256ed88ffb016ec48ffaad6ec48ffa616ec48ff97322bc8ff98efaa48ffb016ea48ffa616ea4cbfafd5aa48ffb3152a4afba8952a4cdf96d42a4cdfafd42a4cdf95942a48ff98edaa4cdf942caa4a7f97286a4cdf94286a4cdf9425ea4cfda5cbaa48ffb265d008ffb32f8fc8ff973229ccef92b229c8ffa617e9c8ffb316a9c8ff97320f88ffb3168f8cdf96ae4f8cef96ac8f8cfb96a84f8cfdb265cf8cfd96a5cf8dfd2065cf89fe97230f8cfe96a30f8cff16a00f88ff97322988ff97322948ffb017e948ffa617e948ffb256e94af7aad6a948ff98eda80adfae8fa80aefaccfa80afda60fa80afea34fa80aff204fa808ffaad7e7897f973226c8ff98efa588ff98ea6588ffb016e588ffaad6e58cb else 0xfa258ff98ee2258ff98ec6258ff98ea6258ff98e8225cfd97cb225bfca34b225cbf97e5225ebdafa4a25cff17e02258ff97320818ffb3168818ffb32a4819fd9725c81cfdaa65c819fdb30b081cff2a60081dfd0b200818ff982fe218ffb017e1d8ffaad7e1d8ffb256e1d9fda616e1d8ff982fe1dcef97ec61dcef96ec61dcef97e961dcef97e4a1dded97e4a1dded96e4a1debeafa261d8ffb017e198ffb256e198ffb316a19af7aad6a19cdfb2142198ff982ca19cf797ea619cfeb208a19bbeb008a19bdeae88a19ef6aa48a19afe9822619ebeafa26198ff97320758ffb3168758ffb32f875cbfafef875cef96ac875cefafac875cfbafa8475cfbac68475cefaca80759fd9725c75cfd96a5c75cfdafa5c759fdb30b075cfdb20b075dedac8b075df9a864875cff16a0075cff2fa0075dfd0b20075dfd24a00758ffb017e158ffaad7e15cfd97e4a15bbeb008a11afe9822611ebeafa2611fbca522611dbdafd5a11bfd2055a11ebdaf95611bddae95611bf9a895611bfca355611bf9a895211bfca355211bfd20552119fd972ca11df5aa906119fdb30fa11afdb24fa11bddae8fa11bedaccfa11bf9a88fa11bfca34fa11bfd204fa119fd98e7a11bfcb008a11efcaf88a11afd9822611efc9822611bfc9822611fbc95a2611fbcafa2611efcae22611fbcada2611ffc2062611bfc9821611efcae21611bfd3005e11ffc2245e11ffc2145e118ffb256df58ffb3169f5abf98225f5fbca2611f5bbf23555f5bbf23551f5bfe092e1f5aff182d9f5def126a9f5aff32505f5cff18ea5f5ebf15ea5f5ebf152a5f5eef126a5f5ebf2bea5f5aff324fdf5faf2be95f5def12685f5bfd234b9f5fbd154b1f5fed124b1f5fbd2bcb1f5efd2a4b1f5bfd234b1f59ff18e49f5faf2be49f5bfd17249f59ff18e45f5def12631f5dfd0ba31f5bfd2608df5dfe2308df59ff33089f5bbf30089f5bdf2e889f5bef2cc89f5bf72ac89f5bfb28889f59ff33085f5bbf30085f5bfb28885f5bfd26085f5aff18225f5ebf18225f5bbf18225f5bbf17225f5faf12625f5ebf2c625f5ebf2a625f5fbd0ba25f5fbd0b225f5fbd24a25f5fbe08e25f5bbf3021df5fbe2261df5ef72a619f5fbe22619f59ff33075f5aff32475f5bbf30075f5bef2cc75f5bfb28875f5bfd26075f5fbe22611f5bfd17211f5fbd15611f5fbd15211f5fed12611f5fbd2be11f5ffc08a11f5ffc22611f5fbd22611f5ffc21611f5adf982d9f18ffb256de98ffb3169e9af798219e9bdf2e955e5bfe092e1e5aff324f9e5bdf2e8f9e5bef2ccf9e5bfd260f9e5bfe234f9e5fed2be49e5bbf30089e5bdf2e889e5bef2cc89e5bf72ac89e5bfd26081e5aff1821de5fed24a1de5bef2cc75e5bfd26075e5bfd2ce11e5ffc08a11e5ffc22611e587fead7dc1e7d6a5f5ad87fead7da9c7f5)) else (if i<4 then 0xadbfd20475adf7d169f5adfbd155f5adfed129f5adfbd2bdf5adefd2a5f5adfbd225f5adafdb25e9adb7d971e9ad9dfae97da99efacd7da98ffb017da98ffaad7da98ff982fda98ff982c9a98ff982a9a9cfd9825da9dfd0625da9cfe97e19a9ef6aa619a9cff17df5a9dbf2fdf5a9dfd25df5a98ffb26fda5a7f972f9a5a7f972e1a58ffb26a9a5a7f972a5a5e7f169e9a5cef92afd69cbfafd5969adfae95969cf7aa90569abfb008d69adfae88d69aefacc8d69af7aac8d69cfea308d698ffaad6ef98ffa356ef9afe892e6f9cef96d26f9cefae526f9cef926aaf9cf7aa906f9cef92686f9cef92632f9cfea308ef9abfb016955cdf96ae555cbfafa31558ff982e5518ff9823151afba8956e1cfe9688ee1cfeaf88ee1cfe9548ee18ffb016ee18ffaad6ee18ffa356ee1afba8952e1aff20552e1cfe96c8ee1cfe9588ee18ff97322d9cdfae97ed98ffaad7ed98ffa357ed98ffb256ed98ff98d6ad9cdf97ee2d9bde892e2d9cdf96ee2d9afe892e2c58ffb016ec58ffaad6ec58ffa356ec58ff98edac58ff97322bd8ff97322b98ff982feb98ff98efaa5adfae956a5afba8956a5afe892e2a58ffa356ea5abf95ecaa5a7f97286a5aefacc8ea5afba888ea5cfea308ea5af7aad6901cf7aa631018ffb32f8fd8ff97320f98ffb3168f9cdf96ae4f9cef96ac8f99fd9725cf9cfd96a5cf9cfeb2630f9cfe96a30f9dfca6230f9dfe20630f9cff16a00f98ff97322958ffb017e958ffa357e958ffb256e958ff982e695adfae95681afe892e2818ff98eda81adfae8fa81aefaccfa81afda60fa81afea34fa81aff204fa818ffaad7e798ffa357e79bddae954b1bfc892e0b19fdb30f8b1afdb24f8b1bddae8f8b1bedaccf8b1bfca34f8b1bfd204f8b18ffb316a51adf982da4d9fda356e49bfc892e249ef5aa502499fd98e7a49bfd2048e498ff98efa2dadfae9562dafba89562d8ff98ea62dafea3568898ffb26fc89cbf96afc89dbf206fc89cbfafd5489afba895489afea355489cdf96ae489cdfafae489cdf956e489cef96ac889cefafac889cbfafec489cdfae6c4898ffb26a889cf796aa889cf7afaa889cf7956a889cf7ac6a889cbfafea489cdfae6a489cefacaa489cfbafa8489cfb9568489cfbac68489cfbaa68489cbfafe8089cdfae68089cefaca8089cf7aaa8089dbdafcb089dddae4b089dedac8b089df5aa8b089bfca34b089dbdafe4889dddae64889df5aaa4889df9a8648898ff982fc858ffb32f885cbfafef8858ffb32a485cf7aaaa485cfbafa8485cfbac68485cfbaa68485df9a864885dfd24a0085adfae97e25afba897e259dfae97e25cbfb017e25cdfae97e258ffaad7e25cfba897e25cff2057e258ffb256e259ff2056e258ffb316a258ff98d6a25abfb016a25cbf97efa25cbf98efa25eaf92afa25ebe892 else (if i<5 then 0xfaf2261deefbe22619eebbf30075eebfb28875eefbe22611eeaff3246deebbf3006deebdf2e86deebf72ac6deebfb2886deebbf23559eabbf23551eaaff172e1ea9ff18ed9eaeef16921eaeef2e121eabf723501eafe7120fdeafb72bcfdeabf7234fdeafaf2be95eabf717295eaef72e295eab7f17285eadbf15a85eadbf15a5deaeef12259ea9ff330b5ea9ff330b1eafaf2be49eabbf3008deabef2cc8deabfb2888deaeef12089eabf72ac89eaefe22c89eabbf30085eabf72ac85eabfb28885ea9ff18e25eadbf18e25eabbf17225eadbf2ca25eafaf12225eafb710225eafb70fe25eafb729625eafbe08a25eaaff1821deabbf3021deafbe2261deafbe22619eaef716a19eafe712219eaff608e19eaff608619eafb722619eaff622219eafbe22611ea9ff3306deaaff3246deabbf3006deabdf2e86deabef2cc6deabf72ac6deabfb2886dea97f972a9e6c6fd2afd6987fead6ef987fe356ef9c6fd6d26f9cef925cef987ff016ee187fead6ee187fe356ee1c7ed6c8ee187fd7322d98ff9d17ed987ff256ed9c5fd6ee2d987ff016ec587fead6ec587fe356ec587fd7322bd87fd7322b987fe356ea587fd7320f987ff3168f9c5fd6ae4f9c6fd6ac8f9c7dd6a5cf9c7ed6a30f9c7f56a00f9c7f969ccf987fd7322958ff9d17e9587ff256e9597de356e498dfee97e258ff9d17e2587ff256e2597f6056e2587ff316a25a3ff016a258ff9d17e1dcedd7e4a1d8ff9d17e1987ff256e1987ff316a19a77ead6a1997dd72ca11bbcf008a1187fd7321f5bbf1d155f5bfd1d0b9f5b7d57249f5fad6be49f5b3f57225f5b7d57211f5fbc62611f587fd7321e987ff256de987ff3169e9adfae955c9afe892e1c9abfb0089c9adfae889c9aefacc89c9af7aac89c9a7f972fdc9cbfafd59c9a7f972e5c9afe892e5c98ff98ed9c9a7f972a9c9cf7aa905c98ffb30f9c9adfae8f9c9aefaccf9c9afda60f9c9afea34f9c9aff204f9c9cfea308dc98ff98e25c98ffb3081c98ffb3075c9aefacc75c9afda6075c9aff20475c9a7f971e9c9c7f97321c1cef92b21c19dfae97dc18ffaad7dc18ffa357dc1a7f972f9c1cbf97df5c1dbf17df5c1faf129f5c1ebf2c5f5c1fbd0bdf5c1fbd249f5c1fbd211f5c18ffb017dbd8ffaad7dbd8ff982fdbdcdf97ee1bdbde892e1bdcdf97e4dbdcdf97df1bd8ff982fdb98ff982e5b9dbf2fdf5b9c7f97321b58ff982e5b58ff982c9b5a7fb0169ada7f972f9ada7f972e1ada7f972a5adb7db0169adb7d972f9adbddae955adb7d972e1adbfc892e1adb7d972a9adb7d972a5ade7d96aa5ade7d972a5ad9fdb30f9adafdb24f9adbddae8f9adbedaccf9adbfca34f9adbfd204f9adbbdb0089adbddae889adbedacc89adbf5aac89adafd98225ad9fdb3081adbfd20481ad9fdb3075adafdb2475adbedacc75 else 0xf2fc5daabef2cc5daabf72ac5daabfd2605daadbf2fdedaa9ff18de9aadbf2fde9aadf72a9e9aaff6219e9aaa7f972e1a68ffaad6ee28ffa616ee28ffa356ee2cef96d26e2cef924bae28ffaad6ec68ffa616ec68ffa356ec6aefae96922aefaad6922aefa616922aefa356922aef972e1228ff97322bacef96d22a6cef9228502cef9225d02cef9223102cef92b20fecefb2120fedef12200fedbf2be00fecefb21229a8ffa617e968ffa357e968ffb256e969ff2056e96cefb21227697f973226ecefb21226ecef96d225a8ff98ea65acefae520b6cef922a8b6cef92230b6cef92b20b2cefb2120b2dbf15e00b2def12200b2dbf2be00b28ffaad7e4e8ffb256e4e9ff2056e4ecefb21224e8ffaad7e4a8ffa357e4a8ffb256e4a9ff2056e4a8ff98ee24a8ff97320a2cef92b20a28ffb3168a2cbfb2150a2cefb2120a2cff16a00a2dbf15200a2def12200a2dbf2be00a2cefb212242cef96d222e8ff98ea62e8ff98e5a2ecef922a88acef922848acef9225c8acef92b2086dbf062fc86cefb212086dafafd2086cfbac68486deb9228486dbbabe84869fba896e26bbba896e26dbba896e26daf96d2226eaf9692226eafae12226bafacd0626bbba890626bbf2050626eaf9210226bbea350226bbea34fe26bbf204fe26abf9829626bbd8be8626abfb24ba26b9fae8ba26bafaccba26bb7aacba26bbba88ba26dbda5cba26bbf204ba26eaf9225a26ebda58b626bbea34b626abfb24b226bbea34b226bbf204b226abfb24a226bbea34a226bbf204a226bbeaac8a26ebea808a26bbea608a26ebea588a26bbf2ac5e26bbf2605e26dbf25c5e26cefb2122228ffaad7e1e8ffa617e1e8ffb256e1e9bfb016e1e9bf972fe1eebeae2261e8ffa617e1a8ffb316a1acefb21221abbeb00861abbe972261afae922261afbe062261a8ff9732076cef92b20768ffb3168769bf972fc76cbf96afc769bfb315076cbfb2150769efb312076cefb212076dafafd2076cfb96a8476dbb9528476cfbac68476deb9228476dbbabe8476cefaca8076cff16a0076dbf1520076def1220076dbf2be00768ffaad7e168ffa617e16cefb2122168ffaad7e128ffb256e128ffb316a12bbea355212cefb212212ebeae22612fae9222612fbc8be2612fbca4e2612fbe06226128ff973206ecef92b206e8ffb31686e9bf972fc6ecbf96afc6e9bfb31506ecbfb21506ecdf96ae46ed9f952e46ecbfafec46ecdfae6c46e9efb31206ecefb21206edafafd206edcfae5206ecbfb22bc6ed9fae6bc6ecf7b26a86ecf796aa86edb7952a86ecf7ac6a86ede7922a86edb7abea86edf7206a86ecfb96a846edbb952846ecfbac6846edeb922846edbbabe846ecff16a006edbf152006ecff2c6006edef122006edbf2be006ebbf30085eebfb28885eebbf17225eebef1721dee))) else (if i<9 then (if i<7 then 0x23606b8d51a834c690d119e338660cb194324638c618830c610c11802fc5f0bd1782ec5d0b91702dc5b0b51682cc590b11602bc570ad1582ac550a915029c530a514828c510a114027c4f09d13826c4d09913025c4a8941262484909212023c4688b11221c430841042003f87e0fa1f03d87a0f21e03c0770ee1dc3b8760ea1cc388700de1b83686c0d41a4340660ca190310610be1782e0580ac14c2885009e1382684908e118220430841001f03c0740e01b0350660c41602b0540a41402604a08c1081d0280480800f01c0300480087fead6ee287fe616ee287fe356ee2c6fd6d26e2a6fd72e12287fd7322bac6fd6d22a6cef921cd028ff9d17e9687ff256e9697f6056e96c6fd6d225acef921ccb68ff9d17e4e87ff256e4e97f6056e4e8ff9d17e4a87ff256e4a97f6056e4a87fd7320a287ff3168a2c7f56a00a2c6fd6d222ecef921cc8a97be896e26b3be896e26d3be896e26d2fd6d22268ff9d17e1e93fd72fe1e8ff9d17e1a87ff316a1ab3ed72261a87fd73207687ff316876c3fd6afc768efd82c876c7bd6a8476c7f56a00768ff9d17e1287ff256e1287ff316a1287fd73206e87ff31686ec3fd6afc6ec5fd6ae46e8efd82c86ec77d6aa86ec7bd6a846ec7f56a006ec7f969cc6eb3f57225eefae6261deea7f572e1eabf71d101eab7757295eafa76be95eab3f57225eae7756a19eafb662619eaeaf92225caeef121e9caef7101e9caa7f972e5caaf790ae5cacefae525caa7f972a9cacef926a9cacf7aa905caa7f9725dcacef9265dcacef924b9cacfda5cb9ca8ff98e49ca8ffb30a1caaff204a1caa7f97231cacef92631cacfea308dca8ffb3075caabfb0075caaefacc75caafba8875caaff20475ca8ffb306dcaabfb006dcaadfae86dcaaefacc6dcaaf7aac6dcaafba886dcaaff2046dcaaff18de9caeef125e9caef7105e9caef7295e9caa7f972e1c2b3f972e5c2bb790ae5c2b3f972e1c2b9fae905c2bafacd05c2bbba8905c2bbda6105c2bbea3505c2bbf20505c2b3f972a5c2eaf922a5c2b9fae8b9c2bafaccb9c2dbda5cb9c2bbf204b9c2b3f97259c2eaf920b5c2abf98249c2abfb24a1c2bbf204a1c2b3f97231c2b3f9722dc2eaf9222dc29bfb3075c2abfb2475c2bafacc75c2bbba8875c2bbf20475c29bfb306dc2abfb246dc2b9fae86dc2bafacc6dc2bb7aac6dc2bbba886dc2bbf2046dc2dbf2e45dc2bbf2ac5dc2bbf2605dc2dbf25c5dc2dbf2305dc2faf21dedc2bbf2cde9c2faf121e9c2fb7101e9c2fb7295e9c28ffaad7dbe8ffa617dbecefb2121befaf225edbadbf2fde9bacefb2121b6f77171e9b6ef72e1e9b6fe7121e9b6fb72bde9b6fb7225e9b6cefb2121ae8ffaad7daa8ffa617daacbf982fdaad3f972fdaadbf062fdaacefb2121aadafafd21aab3f97225aadbeafe19aacff3205daadb else (if i<8 then 0x8f71ea3d4798f11de3ac758e91ce394718e11be37c6e8db1b235c6a8d319e334658c918e314618c31862fc5d8bb1722dc5a8b315e2bc568ab1562a4538a313e2744d89912e2544888f11a22c4488710a20c4087f0fa1ec3c8770ea1cc3886f0da1ac338650c61842f85d0b61642c8570aa14c2884f09a12c2484708a1041f83d0760ec1b8350620bc1582904e0941182103e0740e81b0360640b81502604c0880f01602402803006003ff7feffdff3fe7f8fe1fbbf67e8fc5f7bee7dafadf43e77ccf95f23e37c4f85efbdf7bcf71edbda7b2f61ebbd67aaf51e9bd27a2f41e73cd798f2de53c9792f25e3bc678af11e1bc2782f01dfbbd776ee9dcbb876eed9dabb4766ec9d8bb075eeb9d6bac756ea9d4ba874ee99d2ba4746e89d0ba073ee7dcf39c736e69ccb98730e5dcb394722e3dc738d716e21c3b85708e0dc13816fedf1bdb7a6f2de1bb3746e6dc9b8b706dedb9b6b6c6d6da9b43676ccd95b23606bcd71adb596aed59aab546a6d49a8b5069ad2da534868ad11a1340678ce99d33866ccd99ab34664cc597b2e65acb19632b654ca59432664ac8d9132063cc758e31b634c698cb1862ec598ab14626c498830e61ac318630b614c2584306608c0d813005fcbf57daf95f0bdd7b2f55e6bc978af05debb9762eb5d4ba5742e75ccb91712e05c0b7d6fadd5b6b656bad65a8b4d69ad159eb3565ac958eb15622c4586b05602be57caf15d2b856cad559ab3566ac958ab0560abd57aae558ab1552a9550a9d532a4546a855029f53ea7d4f29c536a694ca9852ea5d4aa95528a5149a9151ea394628b512a2143a8650ca1943285508a0d41282502a014027f4fc9f53e27a4f09dd3b2754e89cd392724e29c137a6f4dc9b53626c4d69a9352694d099d332654c898d312614c097d2f25d4b896d2d2594b095d2b2534a293925a4948e9152124047e8f51d23846a8c91822f45a8a9142264428710c21441e83504a0740a808ff9fd3f67e0fa9f33e27b8f61e93cc788f01dc3b0758ea1d33a4734e61cb394724e41c738c714e21c3384704e01bf37c6f4de1bb3746e4dc1b736c6d4da1b33646c0d79ae3586acd49a734a68cd11a2342680cf99e33866ccd19933065ccb19532864cc919132063cc718d31862cc518931061cc3185308608c09802fe5f8be97d2f65e4bb9752e85ccb89702de5b8b696c2d65a8b41682ce598b29642c858cb11612c057caf15d2b856cad1592b055caa9542a8548a814f29a530a514929051ca314628a50ca114027e4f49e13b2744e49c13726c4d0999322624c09792e25a4ac9512925049c9312524848c911212404788e91d23846c8d11a23045c8b1152284488810e21a4308510820a414821032044047f8fe1fa3f07d8fa1f03dc7b0f41e43c0770ed1d83a8748e81ce394720e31c23806f8de1ba3706d8da1b else 0x501067380701065d80664064b8005e70158005b701701380701701062d8058070106ef0138058005b70138050106168068068068068068068068068068068068068068068068058035c1013806db38025c66458058065c6e2ee2ce28686646646642646016016012ead80001d80580641049647601091e01601047580091843601047601643601643601091e4360124360104758005cd8060105cb8007be0160105c85c85c85cd80064e0105e14338007b86f14360160160105cb8060138004760105e04360105e00f60102f82282002a00881e8003aa8147a281a70070070070006484cf0004904370070006ff0070070070006e85b700062f000477000db816cd485e05e45c07b97a07b816e0178007b86ce8006c87b86c87b85e0490508490fa07b84960178007b833f9b00880813bc8d7a282200f95c00615c00602506f05c844844c4107bfa2f8c008f9b00609183d82200ff25e47c838ef1be33c5f8af14e27c438770ce17c2b83f04e07c037f6fcdf5be77bef6de7bc376eebdd5ba373ee4dc5b836f6dcdb5b636bed6da7b43676cbd93b1f626c2d81afb5e6bad6dad75a6b3d5dab3556a7d4da93526a3d43a7f4f69dd3ba734de9ad35a674be95d29a4f49e91d21a3b4668bd13a1f42e83d039ff3ee7bcf39e73c677ced9d73a673ce59c73866fcdd9b73666bcd59ab34e68ccd99331e62cc39832fe5ecbb9732de5acb39632be56cab95329e51ca193f2764dc9992b24e49c9191f23644c879072063fc7d8f71e63bc758e71c637c6d8d71a633c678cb18e30c5f8bb16e2cc558a313625c4988f11621c4187f0f61dc3986f0d619c3185f0b615c2984f09611c2183f0760dc1982f05609c1181f03605c0780b00e00bff7faff5fdbf97eefcdf6be97cef95f1be17baf6decbd77aaf4de8bcf79af2de4bc778af0de0bbf77aeedddbb976eed5d9bb175eeadd4ba774ae8dd0b9d732e55c9b9171ee2dc3b85702dfdbdb776eedcdb7b6f6dada5b3b656c2d7daeb5d6bad75aeb5d6bad75adb596aed55a9b5169ad2da3b43682cfd9eb3d676ce59bb35666cc597b2d656ca593b25646c858fb1b632c5d8ab13622c3d85b0960ac0d80aff5fabed7daf95f2bdd7aaf35e2bbd76aeb5d2b9d72ae35c2b7d6eadb5b2b5d69ad159eb3565ac958ab0d60abf57aaed5cab756aacd58aaf55aaad54aa754aa8d50a9f53aa6d4ca9752aa4d48a8f51ea3545a8b512a1541a814fe9f53ca774ea9c537a6b4d299d32a634be9752ea5b4ae94d29a534a293523a4748a90d21a3f4768e51ba354668cd18a2f45a8ad13a2343e86d0ca1542283503a033fa7e4fb9f13da79cef9db3b274ce69c73866f4dc9b535e6acd399f32e63cc39832f65dcba9712da59cb295f2b6554a794d28a50c9f9392664c49892d25a4b49491f23645c8790b20e40c808ff1fa3ec7c)) else (if i<10 then 0x803db701064b4770138005e7017017017013803db701064b477017017017017013db701064c11f01701701701701701580580580580011d805db5db5db5db06484ce8004905b68004368068004368035b6806806805db680701701701064849701064f01701050f0105084930158004758005b58006484cd8004904358005e70105e701064f0104cf01111d80050d8005087bb80580701380043701580043501380064f0107b85e70158065c05cb8070145c70138007bf01580062d800435807017012e2f010e470170106c84370138058005b70104370138005e70135b70170170138038004370158058058055c380043501380501411f01011e47050843043701047701049701641701641701641641580580241580380701041043701701641701641701641701641301241011bdb0648472470118c30c3701043064864f01247301011f0100f050d8065c60158064760154760107160160138046fe0160106fd8060155058005cd8058058060160138054760107b07164760164760107be47601111847580580111d8038060107ae0138007b85c87be0160104760104960160107b911e016013803806016016016016015805806cc6cc68d68d68d68d68d411ecc6cc6cc6cc601420a11e8d601220850c1180702f0395ba00f80702f03903581c81e817034bba00f81581e80003e80f81d81ed8000080f81b01682a00080f82701d00f82283d00f80681858000080f81b02a01e80080f81580f831cef823b1e01a031cefb2481c81a4ef891b2f01a4ef807b2f01a031cefb0112f01a10480f831cefb2f01a00080f80080f80702503902a81d00f81580f80080f81b01682a02282100f80080f80080f82f81682a00080f81b02503902f82e80fe6403c090c0600080f99bb804e286cfaf86cf9001e80080fb8d01ee8768701e794fa987b81e800800e80680680680680016816e80680680680680091091680091000e80680680000e8002568068001d05c800e8068006e80085b68d062e8d6cc000847680680680000800806009006002802802803e80016e8068068068068068009168068068068068068068068002568068002400668006f68068068068000404105c80900605ce8041d000862e80000e8d6805805803807015e2f0170170170170106f580580580380065f0158058058058038070105b580580062d80662d803803db701701062f01701001f0170170168006eb8006ef0170105b58038058038038038070138034330138038038038038005e701062d806db701701701701099099701001f0170105b580580580580701062d80701701701701044f01054f0104930105e06585b680062e8035b04768038070170158005b580380580380380701362f01380701062f01067701562f01701067380701362f01380380068701067380068 else (if i<11 then 0x680002e8068041d68035b68015c68068068068007b816e80041680680000d805805803807015805805805805805805803803803807010707016806804d4e8070107b06158067a701001f0138005b7017010707016806804c73db70105b58006775b5802c370107b07b58067a05b7013807015805807013803804c715c70138005e05e7017017016806802c36806803db67a6435805803803802e407be4370164330146ff0107b58058006f87be43701044e4370107be437016437016433014c370107b04358058058004370170130170105e05e58065c38005e064f01062d802e2f015803807013807015803803805805802c37012c338038070170135c05e7013803804c35017017012c770170105b58058058070170170170138070158038038058058038038005e7012c37012c370105e55c35b70138038070170135c06c30138038070170135c38038005e4c315c5806db3804db60160160165c60105e65c65c65c65c6015803803802ead8005cd8058060138006ce54801e016014d4e0107506fd80601016816816e0144107b580254d80654d8038006f87ac6fe0144138007b84107b84105c87be0138060138060160160106c601054e01654e01654e0107ba54e01654e0175b001bdb03e00f81580f82e81680f81d81ed8d01481d00f81580f83a01680fb8006482902680080fb8001b01680fd4338006c82281680f81580f83d81680f80080f80080f81b02503900080f81580f823b804fa01a4efb2481c81a324b014fa01a4ef92482181401580f8231804fa01a00080fb8002503901e8146ba06c81238000003e80f80701e82a81d00f80b003037a1d794ea407b81238002f03903a02500f80b00303681e80080fb8d01e8ba794fa985c81e83281eb8d01ef9483492801e80080f82f03901700fe8d68d68d68d68d68d000800e8d68028d000e8d68d68d09968d09968068d68d68d00600664c000800e8d680680680000c6fe8006fe8007be80680680064e8068068068068004105ca8d000e80680031800800ecc000806802e80002e80002802806806816e80680680680680680680680680680011806680006680680680006e80680680680680002e80680680680064e8005ce8068d06ce8068068007be80041680420800800e8d000801e8068068068068068058058005e70138005e701701701701380064e8006484ce800497013803db701064b4770105b580580580643580067643580380064b80701701701580064d8070154338070158058058007ab803807017017017014ea862d805db001f017013e285b680380580380380380380701380701341347301380380061701580701701701701701701099701099701411e8068068068068068068068035c7015806db01185ca5c70170170170107b380347301064d4770107b91187bb else 0x1580f81b01680f82100800f81d81e81d81e80080f81d81ed8021d02280800f82101e81d81ed8038001481d00f82775b01ea1d02281680f81f01e80080f81580f81e81d81e91d76a89183c58003c03282b83282202201ea1d05c81eb8001f02500f82b82200080f81580f80400682181e81580f806b8002a81d00f80003e80f80080f81d02d00f93b00fb3b00ffaac3401eb3b00fb3b00f93b00f80080f82201ef9483c02900f81e83001e93a7a2f9005c81e81701e83682682903901ea1d4d4e80000861680061680000e80000e8d68041d05b68065b091000e8005b68000605e68065b68000605b68065b00665b68005e68065b68065b68065b006061680061680680000802816802816816e80016816816802e80680680680002c6fe8006fe80680680002802e80006680680680680006680680680680680680016e80016e8068d680680033e8068007be806802d4e8068001685ce80006e8068068068068d68068))))
def pL31: PT:=(1392,5,7,11,v43)
def x84 (i: Nat): Nat:=0xf1601d0002509c0c0001c000130a00004012080000682914c2408c19088260601407815034f0890c1
def w57 (h: Nat): Option (Nat × Nat):=lw0 8 29 5 10 6 4 x84 h
def x78 (i: Nat): Nat:=0x841883400e0fc0002004c00c1803d0001101181b02e0d8088370760180c84005a2d02301f03810c0980b03a0881781501e0581c02e048048068420000f8208050022c00d00c072010000291780d45983a0200a8050320100958782c0280601400e21e09c0103308a0f00f00005602401d006c1020000da2166c80f0044489040cb00001e302
def w51 (h: Nat): Option (Nat × Nat):=lw0 26 81 7 11 7 4 x78 h
def v42 (i: Nat): Nat:=(if i<3 then (if i<1 then 0x98fbfdb531bffb1a62fff7f4a6ffefa94bffdcd29bffb8a53f7f5f4a7efeba94bffeed29bff569637ff6d2c6ffebe58dffd74b1bff419637fe7d2c6ffe9a58dffd2cb1bffc89437ff7d286ffee250dffd8ca1bffa99437ff2d285fff7650bffdc959bffb82b2fff54565ffe30acbffdfc99bffbe933eff6d266ffec64cdffd4c99bff96932fffbb266ffd7e48bffdfc91bffbe922fff73246ffee248fdfd7c91bffa99237ff2d247fde5248bffeec91bff5f913bfeb7225ffefe44dffdf4897ffb99137ff71225ffeca44dffd8c89bff96913fef29227fde4e44bffdf941bffbe282fff64506ffec4a0bffc6141bffbe8937ff63126ffea624dffcb449eff94892fffbb125ffefe1cfdfd2c39fbf92873ff7130e7feeda1cffdd3c39ffba6873ff7290e7fee4e1cffdc8c39ffb28872fff7f0c6ffefa18bffd9431bffb18637ff2d0c7f7e4618ffdc4c31ffb87862fff7f086ffefa10bffd9421bffb1842fff55086ffea610dffcb421ffb89843ff70f085fff7610fbfdb3e1ffdaf7c3ffb4ef87ff695f0ffeca3e1ffd2b7c3ffb24f87ff645f0ffeab3c1ffdb6783ffb5ef07ff6b9e0ffea0bc1ffda7783ffa7cf07ff699e0ffed2bc1ffd94783ffb26f07ff649e0ffec8bc1ffd89783ffb0cf07ff611e0effe4539dffa7723bff90e077fea9c0effd4b81dff97703bff2ce077fe45c0effe4369dff976d3bff2cda77fe51b4effe4359dffaa6b3bff52d677fe9dacdffdb6e5bffa7dcb7ff4db96ffe5372dffc9ee5bff91dcb7fe51b96ffe2772dffc36e5bff84dcb7ff63af7efd235effebdebdbffb8d5b7ff63ab7efd2356ffebdeadffd7ad5b7ff6db8effebf71dffd76e3bffa7dc77fe7db8effe9b71dffd2ee3bff94dc77ff27b8effe4b71dffc8ee3bff89dc77ff0db8effe1371effad6d3bffb8da7bfeb5aeeffec75dffbc96bbff784d77ffafbaef7fdc371effb6ee3bffb6dc37ff5fb86ffe9f70dff9f6e1bffa6dc37ff4bb86ffe5370dff95ee1bff93dc37ff25b86ffe4770dff946e1bffb8da37ff2db47ff5f368ffebc6d1bffbed737ff63ae6ffe5b5cffdc3eb9ffd78d737ff63aa6ffea754ffebe6a93ffddb8a7ffbb634fff76f99ffeedc33ffddb167ffbb52d7ff76a5cffeed4b3ffddbe27ffbb704fff76c49ffeed493ffdd962bffbb5267ff76a4affadee57bfb2dcb77e91b967fd6f729ffdcee5bbfb2dca7ff65b94ffeab729ffcbee53ff8cdcb3feb5af67fd6b56cffad6a59ff6bdcb3fed5b957fd6f71cffadee33ffbfdc67ff73b8cffecb719ffd56e33ff8cdc73feb5b4cffd7f5dcffad6bb3ff5fd473ff53b8e7fdcb71efbb5ee39ff86dc73fee1b8e7fdab71affaded19ff5ada33feb5ae57fd6f54cffd3ee19ff70dc33fedbb867fdaf708ffeed4b3bfb2dca3feb7b8c7feab718ffc66e31ff73dc63feb7b846fecb72 else (if i<2 then 0x3000dff975c5dff5bb6b7ff536d5fff76dabffcba057ff8c40beff6d4d6ffec69afdfa4535effafa6b7ff714b6ffd025abffdc96dbffb82dafff545b6ffea4b6bffc616dbffb894afffbb295ffefe4efbfdb49dbffb193bf7e91277bfebe4ebffeec9dbffb892afff7e516ffec4a2fdfa4145effaf28afff18516ffd022edff96c5d7ffaa22afff2e456ffee226f7fdb44deff9489afffbb137bfd7e26f7fdcc4deffb289bdff5d137bfeaa26f7fa0c4deff4089bdff4d137bfe9626f7fcbc4deff2e89bdfe5b137bfe4e26f7fc944deff2889bdffbb135ffefe22f7fd7c45f7f9388b7ff630d7efd221af7fc4c35ffb8886afff7e3b5ffe5c76dffe44257ffbf84afff73096ffee212dffd8c25fbf4884bdff5f097fde4e12ffdc4c25eff8984afffbb095ffefc6ebffd50ddf7fb67cbffb4cf77ff64deeffe943ddffd867bbffb08f77ff6d9eaffed73d5ffd2d7abffb28f57ff64deaffec93d5ffd897abffb08f577ff21aeeffc5b5ddff866bb7fe837cdffee555bffd52ab7ff8c5577feab70effd5ae1dffafdb3dff5ab677ff7d6cfdfee2d9bffeedb3bffb6b177fe8362effee2bdbffdfd73bffbeae7eff6d5ceffedaa5dffd754b7ffbf4077ff7c80dffec901dffd8a037ff8c407bfeb47cdffe5cf9bffc61f3dff5aa677ff7d4cfdfeda99dffd8d33bffbea56fff734aeffee295fdfd7d2bfbfaea56fffbb4aeffefa51dffdc4a3bffb1946fffbb28dffefe4ddffdf49bf7fb69377ff6326dfff764dbffdfc93bffbe926fff7324effee249fdfd7c93bffa9927fef2924ffde4e49bffeec93ff7b6927fee8324ffdd0249ffbd34937ffb29177ff6322ffde4a45dffaac5bbff408b6fff7e44dffea889dffe444bbff5f8977ff7d12effee225f7fdb44bbffb18977ff5312fbfe5225ffbc944bffd80896fffbb12dffea881bffcb9037ffbf887eff2710ffde4a21bffdfc3b7ffb9877f7f5d0efefe961dfdfc943bffb898777ff7d0cdffee619fbfa84337ffb28677ff630cff7e9a19ffbc9433ffb22867ff7130cffee2219bffdf8eb7ff971d6fff7f08effefa11bffdcc23bffb8846fff6508effec611bffd5423bffa9847fef2908ffde4e11ffbc9423ff791847ff71308dfff7611ffbafc23ff7bf847feead08ffdd5611ffbdcc23ff7b6847fef6508ffdebe11ffbd7423ff7aa847fee8308ffdd0211ffb9f423ff7a6847fef4b08ffde2611ffbc3423ff7dd847ffb6cfafff6b9f5ffea0bebffd407d7ffb4cfafff695f5ffeca3ebffd937d7ffb24fafff645f5ffec4bebffd867d7ffb08fafdfed9f1effc3393dffc8707bfebee0f7fe31c1effc5b83dff867077fe837c6ffcbaf8dffafdb1dff5bb637ff7d6c5fff76d8dffdb589bffb8af2fff7f5c6ffefab8fbfdb571bffb6a937ff5d526ffcbaa4bffcb9f17ff8c3e2fff7f4c6ffefa else 0x13b122b5363ae427603eca583458e8a0418d476011d163b01f00808c1203d04807faa8c20f21281275fe520f826824eaa3d41e824e901283d024ebe003aa83d0481ad24dd54b00558d5f40001e8ea8150e41b2efb000877540a834ebe003aa83e04807dafb5507c07c08b1a0481a4070110d2d7da282f0231d1208320a41b5afb2902d0180182b02a19fa2e38c400440400d0a41b4038670b21303e0153e8c6835863b536398d5df4bc1b2ef829b1c9781a07b2d410c2f12261d001807180dd17994b0e0dc19d8d45e6bec3a3102d635179afb298d40418d45e0da17c04638c401e6aa81fe53c3ba403d09a3838d0490861ec3a8230b08e98d05b0f207c33f360e4d540a85fe53c63a2f36e3405435745635cd82d8150860fd8d0de0dc16d20854019c3b83700e8bc60307c5f87f07defb8f6bec7d6faaf4de8fcf79af2de4fc7f8cf11e13bff7beefdcfb7f6cecfd93b075ceb3d57a8f4de95d1ba173ee75ccf9772be53c9f92721e3bc6b8bf13e21c3384f06e07c037def7de9bc375ee6dc5b776ced5da5b33636c2d7faef5c6b4d63ab7546a4d3fa734ce96d27a434768bd11a1740e7dcf59db3966dcd198b2fe5ccaf94f27e4cc9391720e3ec758d719e2ec5589b1161ec338530860ec1982302602bfd7eefbdf4bdf7aef3de2bbf772ec5d6ba373ae5dc8b896fedddb7b6b6ced8dadb556a2d2da1b3b66acc596b2563ec6d8ab0f612bfd7aaef5ceb756aacd58aaf55baad54ea7d4aa91512a0d3fa754de9a530a594a291d1fa3745e8950fa1742282d009f73e67a4f09db3a673ce39bf3726ccd59a533e664c898d30e604bd9772de5acb295f2ae54ca694527a4dc9792523e4648990d20e3fc7c8f51de3a4708db1a232c628bd16e2dc588ab14226c4b89111620c3d8750da19c308590aa13c248410760cc1582503a05c07809005ff3fa7ecfd1f8bee7d6fa5f2be17baf69eb3d279cf25e23c0778eddd93b0758ea1d1ba0738e61ca39271ce29c3b83700dedbc3746dedb5b53676c8d81adb566a2d39a5b47684cfd9e33866ccd198b2c650c9590b1e638c658b313620c3184b04600bf17c2f45e4bbd75ae85c6b816dad75a8b4566ac958eb095f2ba56eacd57aab552a9951aa053aa654aa9251ea29432824fc9f13d2764e89c53726c4d69a5342654c697d2ea5b4b495d2aa5249c9252224047a8e51b23245e8b11422544487d0e21942e85508a0d416821022003fa7e8fb1f23da7a4f29e13ba764eb1d239e730e51c6388708e01bb36e6d0d89ad350690d099e33465cc999031a624c39853045fcbe1792ee5d0b816c2d458caf95629e520a193e2704c4961272444688a90f21240c7f8fc1f03d4780eb1cc3886e8d71a432c638c31822f05b8b315e2a85189e12e2444688910c1f83906e0ca1782c05309a11c2083b0660b01081c02a03c0)) else (if i<4 then 0x80006015c0034064a4b08f4380800d2d43a816015e000549144b113800648ce56c0342904b31d033000c91bc034290ce094036280154000346844bc000346483e8740370043c0183dc1f83d8758006f0b907e0346f43ac000f0fa2c507e0341e43a02a0fa1d0f7c010f25c13701b8021e00ce000c41882c02b8181600c56c03437889c0092c64a4b1974390000d3be2251d23c1728f05e50e400034160150186a7036000a06a70024b02a0370000c0ca04c2180d07e2e42202ba1c040068152441851d0781788e96282d01b018038df02a03433086c010244140900e0343c4098740e85e03d0742f03c03c8743de1e43a8783de1d43c172d561d0f78790e82803d1730e86f43c172c3a1d0b961c0f4171c5059024022b68b0134168de4751606f23a8b00b40a84d10d8000a8583520270000c0b00306f06501b8020480456d0480800d07b0251d4121788e84160081213562c1201a0400aa040ca63b000150180f41e0124750244100712521b800cb6e8325804c86be365804c81b2cd9804c86013206480d1a0cd9804c861cc026448e2460543dd0e492326874866001e6873001bd239800156bf43b0348660048e4306501ad56433000a143a433000784883280d1a00f80618e0f24880900d0181952c013591c004925e01800d1e067412005258030cec610480102a00c3786d4968249900102a00c16c094120350480502e05008209e30015a29220260300f922a310250486401a11d3506401a3d81600d0f81913100d1ec11c0687c058034378f6800190068f60c80318302c09a3da0000d0560b0068e00888ea352b84740353b0f64000347000d4c08ea312b805aaa4370c50f611c068248001e406b5d08e035af82c01b0003182501a159aa82c01a10c5bb360580353100f0ce0900780d0a40901200f07c8e80780d022090124000cc0341201509a0910900f018c000681150c1ec2681105acd81582c01a5081750005c1b43706381d0080880d81d0080880301b002063740f4031af80d80003015b29113000068566aa0346584307903006c000182260001301a148068cb01b0001fc0c01a05406013020031258cb4000350000da00b20062860cb400160430560b00682b0580341723a61ca1a2c23c17880006ac5c0c800068cb1a197c65f0e0000f46c81f06e1f07b01f1ed57c2382c0480001e87c03fd7c65e0e0000f46c81f059ca70704d0743d40fe0e09a0b43d01f0620b434d5507a0c416811aaa1e40fd5f08e0b01e80c0f807faff0e0b23780ff29e1c1d46f01fe1c0002687a03fd7c16729a1c1341e80c03e0b406859878153a282d0121643d0540ce0e4260040e60f7a28b6e001cc7003de8a1cc7003d0f83dc0ff29e403d82687c1c007d9b755e403d41ef0ee903407b072e0c1f06c71a1edca4290f603f63ac35d54ec0d124da902772 else (if i<5 then 0x6d80006a76d6c184060d8d6c8c83700d0c1c017a3006ab3d1a2b009e8c3806cf460c1367a3009e8c003b1d507a1f47bd2901a3d83b4a96001bb2fca96001f19b5291ee1b6548760d997e94ca960048806805e6dc6032060e6c4880fa5868b8da11122a30ca421f0008e148120240220378006e049c000681508f4011185208fc00290470f7c00a4b000220343dd004757141260e0f65270704701a1ec6fd3660011f8003e1e8d154307901a0930760001b5746e80d87477423e0e8741ef0730008ed746ee0e8000341201101bc003702b0234011d03e4748e81f00ce000900a8236000580683105a3600686602cc000880da0015aaa87a35383823b3640015aaa80d01a1f421c3a04983b0000d50c8002180d3bb83b001f4c1d800ee937c00090220624751886f80d50c13e3103e474208078e281c11c0244e56c03ee287b38a0920742289c0f8079dd0a4208078ce07d0e81f43a07d0e9a2a8607d0e81f7003e80fa1d06207d0e82730007c7740780d07d0e83db009710e81f43a07c15d8035597077c1f23a07c8ea8003e5714000aa23a00c000a811e000903280de005601201101a1955b7000c22191181656c03443065e00198430521923270005201a3d41f87901a1b70706601b8000a80d0cc0fd5c0f707a1954701301b800120162b00930001501a0540607b04811c0b60002a7206f03f07a0903c8b902c37823816c001480683cc1d800068240f20541ee0002c3dc1e8d856d4180404d2b00901601625e2bc1601638a090160161b14182680807e148161c8b8b4194103fe00135089a90da0586c84dc00058e402402b8003280d02a0303280d1058000b2b6824034040d008e0582900de003400aa3a8242181f23a38a20816016824034044820ca0302701501e7200903e4752080a80c11c0578001510403c4901540921832a0411c0344948202a08d800d00f6141800c90248e9ba03d474d742823a78a04a4320460024a4130002aca41182e01ad56413000a01119b23a905c003280d2b036009300390238058920f6190efb5dc1c3de6f80d0dd2398006eabf2398007c66d8387ba221c557d1124e07dc00fa1df11c0343748e0ca036afe0e91cc182688e42418ce2e0e8080a01230609803402b400c80580286302a0352c06d2b0d200b329087c00068134181ef800c908e1ecafd0047571625e0001a3246f04a01b5d1000de01b8006f0c91ee37a1d0f78198006f04a1b30006f0d906084b800e201a1978002f4120b625889c0032680056aaa1eb001d50975550000d1bd0f01600c0fa3dc21c3ac003785c80d1bd0eb0003c3e8365066001bc4df0000c0880578007b0940347a07901b0006f00d02bc0091863056036000566aa0359b00d0868e8b12b6e00034b123a01892c65a0001a8f05e20001a38962e06400034b101501a8000600dc0d else 0x187700d6d7162fd004757163b1499e811c0686f01a3d806158e003d93b0d5c00bd02b00d0f803530700baa15eaaa3a1b21f42183d8740ad94c3a01a5383070078b4391d00d2001b83d0f66000347b00c225c007b46256c04006c76d6c208320e24ecbd0238044ec3db002f44ec3380687c1c09800687c4e81f11d65f293ad82380da6c0361d276d6c1889102ba1c040068640880345cd0e07a0bb5b02701a19415b29874036db01301a5608007a1ec44b8000d1ed17d5b1c8e001db5b0643901db5b00d9058003280c8ec0367a0640181843023a90c8103c23a6ba0f47bbc590c8106fb2905c0359482e01ac002bb550881f41e8f790c195020df90c19406c820ca0364115001a0fc1e8f761c0b8068611be02e4300d4ecbd0238044e95211d65fd6d800e42761b14190004d1c141b8026009a56006f0039197c26eb6c007213b6b60c20335b0270ca0355b112e009db5b00dc001940265f2a03435b60001a5415b02701a9d81380d1c1c013000d4e80f51d65fd6d800e4276e00bd006a82e001947b65fd)))
def pL33: PT:=(528,4,7,11,v42)
def x83 (i: Nat): Nat:=0x1c82b08fe08f01485e101c0a504f037c12803e09e867005e00d024b9f4004184064a07016c0430b784f01640e3037800c1040fe0a7843c17e0f008d063c2d801700a06402ac17321500a822c0640b731f434602606d045c11617a026841810e14d078830821c1300aa81ac06e17408486441a8113718857434211c05f30a011008002280e826200a08885901d601b00e830001e08a042046c146097082821424a04f70686940840b102c85848488180c1009423a00000905f81b210808c80d00dc0a205099f82b60e943f007817617103d811802613609005c020e03301e10942ca14822f81f48c4028060837007a0620bb058c0601530d4047c246e686408660ab216807104bc33c0ef07b05001ea19600c812816611004e81b02e418909f80140a40fa058180030a16b0ca10cc33215205682d0120073019039c18e10404b064c2f616d06705a41e60100c330a429214aa2982f418a18b06b81841741212140d6418c02d213860000c12c7ac806022a0d1054051c008e373150358076118041808020618809d82702fe00b0c713d412a14e01a83c804e0fd0af8d9034f62a0d30335cbe0db05c040428c0e80c3813886e17500a84d00ae0510a284a984e0ca033824c1240d804486280f40ae0af017824e1920ae04e41d40a001882900f215107e003800e0ed61202dc0d211e025826c2cc04c085039402c05506f13cc28810001f865404817c0b500240e810d0a5817c0d409803b84e81a411206e81c40ba13e05383302040b909584982a00e15ac82bc14c14222b05502c41570ac031003e84007fb0a815609a6129d6411a0f7073012003407c031b1582c005606801990c40f9020842c1aa0e401600d81900680a184a43340a913f03d1cc411421305dc1a609113e8070244183616860426e197039011c0180e0097016001005c0b385f41f008c08603ec02207803283b81780aa0d2016c0a6076040a1fc0fe19d09c032c11c09f0d006a419e132094030c2b20b503f00ac0801a2a1a05042480990bc81c02b403804350700c043109983b025a41b000b8d833640009a863031a05003a816808814c036815033e02e1600400002d888001d1986c3c0300858002d00000020100abc000800000141f1e28d720a0102746090098800080cac00a632c1641201000081001058802a020100038010a05022b9090c0761a0c83c00013f0041e350006404140d8740625326e45c44038201653068786e231407c00052505c20000006002000390400310195c001a00072781114004290be20681c11020040244048015c8f23810001703858021a1728cae01120f80127038bc0200020000000
def w56 (h: Nat): Option (Nat × Nat):=lw0 160 480 9 13 9 4 x83 h
def v41 (i: Nat): Nat:=(if i<10 then (if i<5 then (if i<2 then (if i<1 then 0x1af7d44c353fec81dadfd7e3b5efac876bf7508ed7fc801da7fcbf0b4ff97e12f7d44c253fec81badfd7e375dfae46ebdf590dd7deaa1bafdd42375ff2006ef7e44bddfbc877bb7f8b4f57bf159eaf7e2a3d5bfcb87aaff964f57ef121eaf7e57bd5fdc407abfb87ef57f7295eaf7e44bd5fdc867aa3ff7eb4c7fea9698ffc62d31ff5bbe63feb770c7fd6ec58ffadd4b5f75b926beeb708e7f96dc99ff643833fe5f707df8fae0cffb21bd9ff2fb7bb7eb86f67fd90dceefac5b9fdb493733fec86d73fcb4d6f7d969adbfb5935bbf6a96b7fe8fad6cff97da9bfb4bb539fe5a6967fd7eb4cffae5699ff592d33feaa5a67fd18b4cff96ef9ddf24df3afebe556efd72aadfba85559ff642a37eea1546ff900a8dfe88ee19ff2ddc3bfa23b867fd916ccff97ed9dbf5c5b33fe5bb167fd915ecffb22b99ff2dd4bbdea94067fd907ecffb20f9bbf5c9f37beb23e6fdd427cdfda5cf9bfd461f37fc803e67fd914acff97e959ff2fcf37f6b22c77ed5258dfda30b1bfb2dc93bf6be927f6d5f24feda7249b7f5f91377eb9226f7d6444df7aa889bf750913bfa8b2267fd9042dfba8485bfb4b90b7fc802167fcbf12ebfafa259ff641037f697206ff90040edfae2219ff2fc3bbbeb1877f6d250ecff97e199ff640eb7beb21d6fdd423adfda5c75bfe400eb3fe5f856fecb708efdae211bfb59423ff222847fe51308ffca1611ffa0bc23efc557d7df8a8fafef125f5dfe58bebefcaf7d77f952faffd0b9f5ffa163ebff4927d7df912faffd211f5ffa493cbff4847963febee0e7dea5adefabeb5bdf6706b63febed4f7d9ada98ffdfad11ffaa5a23ff2eb447fd6ef88ffadd491ff5b9627fd90e04ff97dc09ff643793fe5f6f3ef8f8de4ffb21b89ff643693fec86b3fe8f0d65feac9a8dfd54b51ff8176a3ff0f8d47fe1e1a89ff5fad13feb95a27fd64b44ffaa9689ff4bad13fe5bbe377c937c6bfaf9549ff642a17eea15427fcb7704ffb22d89ff2fdb13fe5bb127fd915e4ffb22b89ff2dd49b7e50a937bd52804ffb20fc9ff645393fe5fa727fd907c5dfae4f8bdf591f17eea13e2fed2e7c5fea30f8bfe401f13fec8a627fd914a4ff97e949ff2fcf13fe5b9637ed2c5a4ffb20b0bfe401613fec89427fcbf284ffb20acbbf5c9597beb22b2fbd54565fba84acbfd461597fc802b27fd91264ff97e4c9ff644913fe5f9227fd91224ff97e449ff641417fc80282ff564426feaa484bfd2dc39bfabe873f755d0e7eea961cfdd49439f7cb67c3ef95cf86ff2a5f0ffc43be1bfcbe782ff972f07fd0b5e0ffa163c1ff492783ff046f07fe085e0ffc43bc1ff4847823ff914e47ff21c08ffe43599fba96a3bf2f0d477e9ada89ff5fc21bfa898435fd12fa6ff1f5e89ff5fbc13feaa7837ed08f06ff1f5e09ff5fbb93feaa7727fd2eee6ff1e1dc else 0xfa18bff59431bfeb18637fd410c6ffa5a18fef48c31ffa89863ff50f0c5ffafe14dff5f4297feb28537fd630a5ffaaa14dff54c29fee9b8537fd2d0a7fba4214ffd43c297fe5b8437fcb5085ffafe10dff5f4217feb28437fd63085ffaaa10dff54c217fea1843ff513087fea1e10ffd42c217fe5b7d37fcb4fa7bf951f4dff5c3e9bfea97d37fd40fa6ffa59f4ffd10be9efe897d2ffd7ef86ffaf9f0fbf5b3e1bfea97c37fd40f86ffa59f0ffe3ebe1ffcbe7c3ff8a8f87ff2bdf0ffe54be1ffca77c3ff94af87ff281f0ffe4f3e1ffc9c7c3ff936f87ff259f0ffe163e1ffc947c3ff856f87ff249f0ffe48be1ffc907c2ffcb6f46ff969e8bff5fbd1bfebe7a2ffd72f46ffae1e8fef1fbd1bfea07a37fd2cf47fe885e8fef433d1ffc7d7a3ff8f8f45ffafde4dff5f3c97feb97937fd70f25ffaa9e4dff54bc9fee9e7937fd2cf27fba15e4ffe3e3c97fe5b7837fcb4f05ffafde0dff5f3c17feb97837fd70f05ffaa9e0dff54bc17fea1783fec58f07fe88de0ffd10bc1ff684783ff8faf07ff1f1e0ffe3d3c1ffc79783ff8bef07ff16de0ffe2d3c1ffcbf783ff8acf07ff2f9e0ffe2abc1ffc54783ff972f07ff2e1e0ffe5b3c1ffcb2783ff962f07ff2bde0ffe573c1ffcaa783ff882f07ff2a5e0ffe203c1ffc3f783ff94ef07ff0f9e0ffe533c1ffca5783ff942f07ff281e0ffe4f3c1ffc9d783ff938f07ff26de0ffe4a3c1ffc93783ff924f07ff245e0ffe463c1ffc89783ff90ef07ff219e0ffe42bc1ffc847833ff7d5267fefea4cffcbd499ff73a92bff914e67fef9c8cffd4b919ff967233ff7ee467fe5dc8cffe43815ffc87033ff52e067fe59c0affe43699ff966d33ff90d657ff21acaffd53599ffa96b3bfce0d677eefda8efddf351dfbaa6a3bf752d477ee9da8efdcbb51dfb966a3bf728d477ee45a8dff4bc49bfe808937fd7f086ffaaa10dff40421bfeaa7d37fd2efa6ffa31f4dff433e9bfe847d37fd2ef46ffa31e8dff44bd1bfe847a37fd7ef06ffaa9e0dff463c1bfe897837fd0cf06ffafddcdff553b9bfea77737fd2eee6ffa51dcdff48bb91ffaa5aa3ff2eb547fe316a8ffaddc54ff5b89b3fab4f56ef921caddf24b95bfc7a72bd7c90e17bf05dc2f7e3db85efc7a70a7fd90df4ff97dbe9ff643756febf6ebf78f6dd7f71e9b69ff2fb556febf6aa7fd72b54ffac96a9ff552d53fe975aa7fd18b55bfa31529ff2ddc5bbe49b8a7fcb7636ef96922ddf5c2453fec8aeb6fd715d6ef922a6ddf24205bdea940a7fd907f5ff200fe9ff2fd2debeafa5b77c91416ef9225addf2416dbf6962da7fd90595ff200b29ff2fc9d3fe5f92bd7d5f254ffb20a2bfe40145bbe488bb77c90456fea2c8a9ff6410d6febf21afdd42435bf96e26d7f5c44debe4889bdf445137bf05e269ff2fc3d6febf87bdf5130f4ff97e) else (if i<3 then 0xfafab8fbf5b5717fe5ba937fcb5526ffafaa4dff2ad49f7e50a937fd71526ffac6a4dff2dd49bfebfa937fcad526ff952a4dff5cd49bfeb6a937fd65526ffabea4dff57549bfea1a937fd2f526ff8baa4bff5fa01bfebe402ffd42805ffa5d00bff641f97febf3f37fd7c7e5ffac8fcdff589f97fe973f2ffd187e5ffa00fcbff64539bfe5aa72ffd907c6ff968f8bff509f17fe973e2ffd187c5ffa00f8bff64531bfe5aa62ffd7f4c6ffafa98fbf5b531bfeb1a62ffd914a5ff96e94dff2d5297febfa537fd7d4a5ffae694dff5c529fbeafa53f7d5d4a6ffaa694dff5f501bfe55a037fd71406ffac680dff54d01bfe40a037fd6d406ffabe80dff57501bfe3ea037fd4d406ffa9680bff644f1bfebe9e37fd713c6ffac678dff54cf17fec89d2ffd7f3a6ffafa74dff58ce9bfea99d2ffd91385ffafe70dff5f4e17feb99c37fd71386ffaa670ff74f4e17fec89b2ffd7f366ffafa6cbff5ccd9bfeb89b2ffd65366ffac66cdff54cd9fee9e9b3fdd3b365ff96e58dff2d4b1bfebe9637fcab2c6ffae258dff58cb1bfea99637fc812c6ffa8258dff2dcb1bfebf9637fcad2c6ff95258dff5ccb1bfeb69637fd652c6ffabe58dff574b1bfeaa9637fc832c6ff8fe58dff1f4b1bfea69637fd4b2c6ffa8658dff4f4b1bfe9d9637fd392c6ffa6e58bff5f969bfebe2d2ffd545a6ffaa4b4bff641617febf2c37fd7c585ffae4b0dff5c1617feb22c37fd62585ffaa8b0dff549617fe8c2c2ffd00586ffb2250bff644a17fe5b9437fcb5286ffafa50dff5c4a1bfeb19437fd53287bfa7a50dff4b4a17fec82b37fcb4565ffae4acdff5c1597feaa2b37fd52565ffa30acbff401597fec8932ffcb7266ff96a4cbff5fc99bfebe933efd6d266ffac64cdff54c99f7e9d9337fd2d265ffb2248dff2fc917fe5b9237fcb5245ffafe48dff5f4917feb99237fd71247efabe48dff54c91fbe9c9237fd2d247fda5248dff644897fec89137fcbf225ff96e44dff2d4897febf9137fd7d225ffae644dff5c4897feb29137fd63226ffaa644fef4dc89bfe96913fec59227fda5244ffb49c897fec82837fcb4505ffafca0dff5f1417feb22837fd62505ffa30a0bff401417fec8902ffd7f206ffafa40bff5cc81bfeb8902ffd65206ffac640bff55481bfea9903fdd3d207feaf884ffd57909ffaa9213ff54e427fe8f884ffd52909ffa96213ff528427fe8ac84ffd49109ffa91213ff450425ff96e24dff2d449bfeb18937fd53126ffa8224dff4b449efe94893ff82f125ffafe1cdff5f439bfea9873f7d4b0e6ffa821cdff4b439fbe92873ff5130e7feafa1cffd5b439ffaa9873ff47f0e7fea9e1cffd53439ffaa0873ff53d0e7fea761cffd4dc39ffa96873ff4590e7fea521cffd49c39ffa91873ff4510e7fea421cbff2dc31bfe5a862ffd7f0c6ffa else (if i<4 then 0xf7defdadefbdf35bdf7aa6b7bef52d6f7de31adefbc5b5bdf7866b6bff90d4e7fea5a9efebeb53dfe726a6bfeb77c67fd6ef8ddfa4df1bfe73be27ff916c57fd6ed89ffe45793ffc8ae2bfeb75267fd6ea4dbfa8549bfe73a927ff914e67fd6a9c9ffe41f19ff5a3e2eff727c5efec8f8bf7d09f17f7973e2ff7187c5ff600f8bff399f13ffc8a627ff914a57fd6e94dff39cb13ffc8942bfeb72867fd6a509ffe415977fb92b2f7f64565f7ea8acbf7d09597fb8c2b2ffb00565ff9ccac9ffe44993ffc8922bfeb7244fff2244affadc899ff5a9127ff90505ff600a0bff399415ff5b8937f77d0e7eeeba1cfddd2c39fbb928727ff90fa7df6d9f0fbed73e1bfda97c3ff30ef84fff21e8affadbd13ffc87837fb7cf05ff6e5e0ffac93c1ff923783ff30ef07fd611e0ffe39bc1bfebe7237fd70e46ffac5c8dff54b91bfe96723ff50ee47ff1f1c8ffe3c391bfebf7237fd72e46ffad9c8dff59391bfeaf7237fd5ce46ffaa9c8dff1f391bfea67237fd4ae46ffa5dc8dff4a391bfe2b7237fd26e46ffa49c8dff48b91bfe287237fd12e46ffa1dc8dff43391bfe847237fcfae46ff9f1c8dff3d391bfe787237fd90e05ffb21c0dff5f381bfeb87037fd62e06ffaa5c0dff4b381ffa87703dfcfae07ff1f1c0ffe3c3817fec86f2ffd7ede6ffaf9bcdff58b79bfea96f3efd4cde6ffa59bcfbf49b79ffa876f3efcf8de7ff1e1bcbff643717febf6e37fd7cdc5ffae5b8dff5c371bfea96e3f7d4adc6ffa59b8fdf49371ffc7c6e3ff8f0dc6ffb21b4bff643697febf6d37fd7cda5ffae5b4dff5c3697feb26d37fd62da6ffaa5b4dff4b369ffa876d3ff8f8da7f79e9b4ffe3c369bfec86b2ffd90d65ffafdacdff5f3597feb96b37fd70d65ffac9acdff58b597feaa6b37fd52d66ffa59acffb48b59ffa876b3ff8f8d67ff1e1acffb3c3597febf6a37fd7cd45ffac9a8dff58b517feaa6a37fd52d45ffa5da8dff4b351ffa896a3ff50ed47fea19a8ffd42351ffc786a3ff57ed47feaf9a8ffd5cb51ffab86a3ff56cd47feac9a8ffd58b51ffaaf6a3ff55cd47feaa9a8ffd54b51ffaa76a3ff47cd47fea99a8ffd52b51ffa976a3ff52cd47fea51a8ffd15b51ffa936a3ff524d47fea45a8ffd14351ffa7d6a3ff4f8d47fe9e9a8ffd3c3517febf6937fd7cd25ffae5a4dff5c3497feaa6937fd52d25ffa5da4dff4b349ffc7c693ff8f4d27ff1e1a4bff5fad17feaa5a2ffd2eb46ffafd68dff552d1bfe975a2ffcb77c6ff96af8fdf24df1bfe5bbe37fd737c6ffacaf8dff555f1bfe41be37fd437c6ffa5ef8dff175f17feaa552ffd42aa5ffa5d54bff642a17feb9542ffd54a85ffa5d50bff462a17fe805437fd7d706ff952e0bff645b1bfe5fb62ffcb76c6ff96ad8dff5f5b1bfebeb137fd6d625ffb22bcdff2d579bfeb8af2ffd7f5c6f else 0x44effac489bff55113bfea92277fd4044ffd8b089ffb49113ffa8b226ffd9042dffafc85dff5f10b7feb22177fd6242dffaa885dff5490b7fe97217fed2442dffa0085dff6444b7fec88977fcbf12dff97e25bff2dc4bbfe5a897dfd7d12effafa25dff5c44befeb68977fd6312effaa625dff5044bff62c897dfd2912ffda4a25ffe4044b7fec82077fcb440dffaa881dff54903bfea0206ffd2e40ffd8b081bff401037fec88877fcb510dffafe21dff5f443f7eb88877fd6310effaa621dff50443ff62c887efd2710ffda4a21bff6443b7fe5f876ffcb70eeff96a1dbff5fc3bbfebe876ffd730eeffae21dfdf58c3bfbeae8777fd530efefa961ddff5043bff62c877f7d250effea261ddff644337fec8866ffcbf0cdff96e19dff2d433bfebe866ffd730cfdf94219bff59433bfeb1867fbd530cff7a9a19dff50433ff62c867fed250cffe88a19ffd10c33ffa89867ff5110cdffb2075dff2d0eb7febf1d77fd7c3adffac875dff588ebbfea01d6ffd2e3affd8b075ffb490eb7fe801d6ffcbf0aeffafa15dff5c42bbfeb18577fd530affda4a15bff2dc23bfe5a846ffd7f08effafa11bff5cc23bfeb8846ffd6508effac611bff55423bfea9847fed2908ffda4e11ffb49423ff691847ff44508ffea2611ffb2fc23ff65b847fecb508ffdafe11ffb2b423ff6be847fecab08ffd95211ffb5cc23ff6b8847fed6d08ffdaca11ffb58c23ff6af847fed5d08ffdaaa11ffb20c23ff6a9847fec8108ffd8fe11ffb1f423ff6a6847fed4b08ffda8611ffb50423ff69e847fed3b08ffda7211ffb4dc23ff689847fed0f08ffda1a11ffb42c23ff680846ffcb6faeff969f5f7f2abebefe547d77fd70faeffaa5f5dff503ebff62c7d7dfd12faffda11f5ffe2fbebffc5b7d7ff8b4fafff2e5f5ffe5c3ebffcb67d7ff964fafff2c5f5ffe573ebffcaa7d7ff882fafff2a5f5ffe203ebffc3f7d7ff94cfafff295f5ffe50bebffca07d7ff93cfafff275f5ffe4e3ebffc9b7d7ff92efafff251f5ffe49bebffc927d7ff922fafff231f5ffe11bebffc8b7d7ff844fafff085f5ffe44bebffc887d7ff90efafff219f5ffe0ebebffc857d7ff908fadff96df1dff2d3e37febf7c77fd7cf8fdfad9f1dff54be3bfea07c7fec58f8fdfa21f1ffb423e3ffc7d7c6ffcb6f4eff969e9dff5f3d37feb97a77fd70f4ff7901e9fef1fbd3bfea07a7fec58f4ff7a19e9ffb423d3ffc7d7a7ff8f8f4effaf9e5dff5c3cbbfea9797fed08f2fff1f5e5ffe3e3cbffc7a797ff97cf2fff155e5ffe5c3cbffcb6797ff962f2fff2bde5ffe573cbffca9797ff880f2fff0f9e5ffe533cbffca5797ff916f2fff089e5ffe44bcbffc20797ff910f2fff21de5ffe433cbffc1d7973fee752e7fea62dcffe44335ffc8867bbf530ce7fef9c9cffd4b939ff8b726bff90e0))) else (if i<7 then (if i<6 then 0x26d6ffda49adffb48b5bff6846b7ff8fad6ffdafdadffb5f35bff6556b7fed72d6ffdae1adffb5b35bff6b26b7fed62d6ffdabdadffb5735bff6aa6b7fed52d6ffd901adffb1f35bff6a66b7fed4ad6ffda31adffb45b5bff6226b7fed12d6ffd881adffb4435bff6876b7fed0cd6ffd875adffb3eb5bff67c6b7fecf4d6effb21a9bff643537fe5f6a6ffd7ed4effaf9a9bff5cb53bfeb86a6ffd64d4effac5a9bff55353bfea96a7fed2ed4dffa5da9ffb49353ffa866a7fed08d4fff1f5a9bff5fb4bbfebe696ffd72d2effae1a5bff5534bbfea9697fed08d2fff1f5a5ffe3d34b7febf5a6ffd72b4dffac969bff552d37fe8c5a77fd7eb4eff95969dff5cad3bfeb25a77fd54b4eff90569dff462d3bfe235a6ffcb77ceff96af9fdf24df3bfe5bbe77fd737ceffacaf9dff555f3bfe41be77fd437ceffa32f9dff11df3bfe5a557dfd7caadffae555bff552ab7fe8c556ffd90a8dffae551bff552a37fe97546ffd18a8dffa0151bff2ddc3bfe5ab877fd7d70eff956e1ffd11dc3bfe5bb877fcad70eff952e1bff645b3bfe5fb66ffcbf6cdff96ed9dff2d5b3bfebeb67efd716cdff96ec5dff2d58bbfebeb177fd7162eff96ec5dff5b58bbfe41b177fc4762dffb22bddff2d57bbfeb8af6ffd915ceff96ab9bff5fd73bfebeae7efd6d5cdff96ea5dff2d54bbfebea977fcab52effae2a5dff58d4bbfe5ba977fd6552effabaa5dff50d4bbfe8ca977fc4752eff96901bff5fa03bfebe406ffd6480effac501fef54a037fe8c406ffd907edffafcfddff5f1fb7feb23f77fd627edffa5cfdbff461fb7fe803f6ffd907ceff968f9bff4b9f37fe8c3e6ffd007cdffb2299dff2d533bfebea67efd6d4ceffac699bff6452b7fe5fa56ffcb74aeff96a95dff5f52b7feb9a577fd714afefabe95fdf5752bbfebea077fcab40effae281dff58d03bfea9a077fc8140effada81dff57d03bfeaea077fc7d40effa9a81dff52d037fe5f9e77fd7d3ceffae279dff58cf3bfebe9d77fd633aeffafa71dff5c4e3bfea99c6ffcbf36effafa6ddff5c4dbbfeb19b7fed7c58ffd954b1ffb5c163ff6b62c7fed6258ffdabcb1ffb57163ff6a92c7fec8058ffd8f8b1ffb53163ff6a52c6ffcb728eff96a51f7f2aca3bfeb89477fd6328dff96e4ddff2d49b7febf9377fd7d26fdfada4ddff58c9b7fe5b9277fcb524dffafe49dff5f4937feb99277fd7124fefabe49dff54c93ff694927fed2724ffd96e49ffb2d493ff6be927fed7124ffdada49ffb20c93ff6a9927fec8124ffd8fe49ffb53493ff6a0927fed3d24ffda7649ffb4dc93ff6239277fcb522dffaca45dff58c8bff692917ff82f22dff96e2ddff2d45bbfebe8b77fcab16effae22ddff58c5bbfea98b77fc8116effa822dffb1645bff6928b77fcb444dffafc89dff5f113bfe55226ffd64 else 0xf850f77ff241eeffe45bddffc217bbff910f77ff219eeffe0ebddffc857bbff908f77ff06deebff2dbd5bfe5a7abdfca8f55ffae5eadff5c3d5fde3f7ab7fd40f57bfa25eaffe3e3d5ffc5f7abff8b6f57ff169eaffe5cbd5ffcb87abff96cf57ff2c9eaffe58bd5ffcae7abff952f57ff295eaffe50bd5ffca07abff93cf57ff275eaffe4e3d5ffc9b7abff92ef57ff0b9eaffe4b3d5ffc2d7abff858f57ff251eaffe49bd5ffc927abff920f57ff231eaffe11bd5ffc8b7abff844f57ff085eaffe44bd5ffc887abff90ef57ff219eaffe42bd5ffc847abff836f55ffae5e6dff5c3cd7feaa79bfdd3cf37bfa25e6ff742bcdffc7c79bff8f4f367fea5cacffcb3959ff8b72abff90d757fefd69affdcad35ffaa5a73ff7eb4e7fee569cffd52d35ff5bbe73feb57ce7fd6ef9ddfa4df3bfe73be75ff7caaddfee555bff39aab5ff5bb873feb570dfec8ee1cffaddc3bfb23b867ff916ccffd7ed9affaddb39ff5ab676ff716ccfff22bdcffad57b3ffc8ae73feb55cd7fd6ea5cffad54b9ff5ba977fce752ef7ea501bff39a033ffc83e73feb47cddfee4f9bdfd91f37f7973e6ff7187cdff600f9bff399f39ff5aa667ff914acffd7e95affadd2b9ff5aa573feb528e7fd6a4ddfbdf493fb7af9273feb522dbfefc89bbfdc9137bfb2226fbf5444efee2c89bff399133ff5f896bfeb712e7fd6a25d7fdf44b3ffc8206fef2e40dff60081bff399039ff5a8876ff7110cffd7e1dcffad43bbbfb1877f6f250ecffd7e19affadc339ff5a8667ff903adefec875bfbcb8eb7fd801d6ffce63aefdee211bfbd9423ff322847fe71308ffd45e11ffb39c233ffc87d73feb4faf7f569f5f7eaabebfbd497d77fb62fafbf6bdf5dfed4bebff52e7d7feb24fafbf625f5ffac23ebffc737d73feb4f8cfff21e9affadbd39ff5a7a77fd7ce4eff955c9dff5c393bfeb17277fd52e4eff901c9ffb49393bfe8b7277fc44e4ffda11c9ffe3eb93bfebf7277fcace4effae5c9dff5b393bfeb27277fd5ee4effab9c9dff55393bfe417277fc7ce4effa99c9dff52b93bfe947277fd26e4effa49c9dff46393bfe237277fd12e4eff881c9dff44393bfe877277fd0ce4eff875c9dff42393bfe7d7277fcf8e4eff9e9c9dff643837fec8706ffcbee0effaf9c1dff5c383bfeb1707fed24e0ffda11c1ffe3eb83efe7d706ffd90dedff97dbdbff5fb7bbfebe6f7efd70deeffac5bdfbf5337bf7e936f7fed24deffda11bdffe3eb7bf7e7c6f6ffd90dcdffafdb9dff5f3737feb96e77fd70dcfefac5b9dff54b73fbea56e7f7d24dcffda11b9ffe3eb73bfec86d6ffd90dadff97db5dff5f36b7feb96d77fd70dadffac9b5dff58b6bff6926d7fed08dafff1f5b5fef3d36b7febf6b77fd7cd6dffae5addff5c35b7feb26b77fd62d6dffaa9addff54b5bff6946b7fed) else (if i<8 then 0xaffcb7536ff96aa6f7f2a54dbfeb8a9bf7c93536ffac6a6fdf2454defeafa9affd42815ffa5d02bff462057fec83faffd7e7f6ffac4fefdf241fdefeaf3faffd2e7f5ffa30febff401fd7fec8a6b7fcb54d7bf9529afbf5b535bfeb1a6bf7c914d7bfabe9abff2dd2dbfeb8a5b7fd71417ef92682dff58d05fbe48a0bdfd5f416ffaa682dff20505bfeb6a0b7fd5d416ffa9a82dff52d05bfeb89ebdfd6d3d5ffb2276bff5fcedbfeb19dbf7c913b7bfabe76dff5c4e57fec89baffd73376ffae26edff58cddfbe489bbdfd5f377fba7a6eff74ecdd7fe5b96b7fcb52d7bf9525adff5c4b5fbe4996b7fd632d7ef9225af7f57cb5bfea996b7fc812d6ffa825abff5c96dbfeb82daffd545b6ffaa4b6bff4616d7fec82caffd7e595ffae4b2dff5c165bfeb12cbf7c90597bfabcb2bff551657fe8c2caffd00595ff96e52dff2d4a5bfeb894bdfd3d295ffb224ebff2dc9dbfe5a93affd7f277bf9524efbf5b49dbfeb193bf7c91277bfabe4efbf4ec9d7fe5b92b7fd71255ffb20a2dff2d1457febf28bdfca8516ffac4a2fdf24145efeaf28affd18515ffa00a2bff644857febf90affd73216ffae242dff58c85fbe4890bdfd5f217fba7a42bff2dc5dbfe5a8bbdfca9176ffae22efdf24c5dbfeb18bbf7c91177bfabe2edff54c5dbfe408bb7fd41176ffa5a2edff16c5d7feaa22b7fd52455ffa848adff501157fe9722b7fd2c455ffb2086bff5f90dbfeb121bf7c90437bfabc86bff5510d7fe9721affd00435ff96e26dff2d44dbfeb889bdfd6d136ffa8226f7f4f44defe9489bff82f137bf97e26f7f2dc4defe5a89bdfd73137bfae226f7f5944defeb189bdfd5d137bfaaa26f7f20c4defea989bdfc81137bf8fe26f7f5344defea589bdfd43137bfa8226f7f4ec4defe9c89bdfd37137bfa5e26f7f1744defe9689bdfc5b137bf8b226f7f49c4defe9289bdfc51137bfa4226f7f4044d7fec888b7fcb5115ffafe22f7f2a445bfeb188bf7c91117bfabe22dff50445f7e9388affcb70f6ffae21edff5043defe8987affd910d6ff96a1adff58c35fbe4886bff4430d7bfa261affd444357fec81db7fcb43b5ffafc76f7f2a0edbfeb11dbf7c903b7bfabc76bff508edbfea01daffd2e3b5ffa0076bff6442d7febf85affd730b6ffae216dff58c2dfbe4885bdfd5f0b5ffaaa16ff74ec2dfee9b85bfdd210b7bfa2616dff644257fec884affcb7096ff96a12bff5fc25efe5484affd73096ffae212dff58c25fbe4884bdfd5f095ffa8612ffb49c25ffa8984bdfd13097fea1612bff640ddbfe5a1baffd7e377bf9506edff588ddfbe481bbdfd5e375ffaa86ebff400dd7fe5b7cb7fcb4f97bf951f2fbf5b3e5bfea07cbdfd12f97dfa21f2ffe5c3ddffca97bbff87ef77ff299eeffe503ddffc9d7bbff936f77ff259eeffe163ddffc937bbf else (if i<9 then 0x4d025e12b095049423c11b08a843c21210307e83dc1e20ee07583a01ca0e006f83681ac0cf06603181800ba05a02b81500a104f026812e094047022c10e08304081fc0fc07c03d01dc0e807103781b40d806903381980c806002f016c0b0054026811c08203c01900a804c023010007403201500900400160070018002bfeb77167fd6ee2ddfa4dc55ff5bb6b77f70914fff22badbfdc5755ff5ba9b77e91536efd2102defd4a057fe7340b3feb54d4ffd7e96affadd2debfafa5abfeb72d6efd225addfa416dbf7962daffce65b4ffd7e4eaffadc9d9ff5a93a7febf2557fd6e4af5fd7c953ffc828b3feb4515ff600a2bff399455ff5b8bb77e91176efd208adfdc59157fe7322abfeb71373fd6e26d7fdc44debf4889bdf645137bf45e26f7f39c4d9ff5a88a7febf0f5bfefe1ef7dc4c3d3ff5f86b3feb50d7bee261a9ffe40ed9ff5a1dadff7e3b5efec876bf7d08ed7fd801daffce63b4ffd7e12affadc259ff5a84bdf713094fff206ecffad0dd6ffbf1baeff72375efec86ebefd50dd7efa11baffb00375ff9cc6ef7ec4bddfbd877babfeb6f577f56deadfedc3d57fdb27abf7a90f57bf6bdeafeea03d5fdda57abdfb12f57f7619eaffe39bd5bfeb872bf7c92e56ffac5cafdf24395efeaf72b7fd52e56ff901cadff4b395bfe2d72b7fd16e56ff889caf7f44b95ffc7b72bff8f4e56ffae5cadff5b395bfeb272b7fd5ce56ffaa9cadff20b95bfea672b7fd4ae56ffa5dcadff17395bfe9472b7fd26e56ffa49cadff14395bfe8c72b7fc46e56ffa25cadff44395bfe8772b7fc3ae56ffa11cadff0db95bfe7c72b7fcf4e56ffae1c2f7f5b385efe9470bdfd12e17ff1e9c2f7f5cb85efeb870bdfd64e17bfac5c2f7f57385efeaa70bdfc82e17bfaa5c2f7f20385efea670bdfd4ae17bfa5dc2f7f17385efe9670bdfc5ae17bfa4dc2f7f49385efe2870bdfd18e17bf88dc2f7f45b85efe2270bdfd10e17bfa1dc2f7f0eb85efe8470bdfc36e17bf9f1c2f7f3d3857fec86faffd7edf6ffac5befdf2437defeaf6fbefd4cdf7dfa4dbef7f44b7df7e7c6fbff8f6df7ff1e9bedff5c375efe896ebff8f4dd6ffb21b6bff6436d7feb96db7fd70db6ffac5b6fdf2436defeaf6dbdfd12db7ff1edb6ffe3d36dfde7a6db7fd90d75ffb21aebff5fb5d7feb96bb7fd70d76ffac5aefdf2435defeaf6bbdfd12d77ff1edaeffe3d35dbfec86aaffd90d57bfafdaabff5fb557feb96ab7fd70d56ffac5aafdf24355efeaf6aaffd54d55ffa5daaf7f44b55ffa866abff82ed57ff1edaaffe3d3557feb969b7fd70d35ffaa9a6f7f44b4dffc7a69affd72b55ffaa96abff4bad57fe8c5ab7fd72b56ffaa96adff4bad5bfe8c5aaffcb7716ff96ae2f7f2a5c5fbe49b8b7fcb7716ff8bae2bff2ddb5bfe5ab6bff82f6d6ffae2c6fdf5c245efeb8af else 0xc84442120f907883a41c20d506683141820bd05c82a414a09d04a821410207d03c81c40da06503081540a204501e80d406202900e804400a000ffc7fc3fd1fdcfec7f43f99fc4fe07ee3f59fa4fce7e43f09f7cfba7db3ec1f58fa87d23e81f38f967c93e31f14f867c23e01ef8f767b93db1ed0f647b13d81eb8f587a83d31e90f447a13d01e7cf3a79b3cc1e58f287923c79e38f1678a3c49e1cf0a7833c11e00efc77c3bd1de0eec7723b79db0ed67693b41d98eca7643b19d84ebe75d3ad1d60eac7553a99d3ce9a74a3a41d14e8673f39f1cf4e7873b39d1ce4e6e73639a9cd0e647313981cbce5c72d3951ca0e4c7243919c88e4271f38e1c6ce3471838b9c58e287123881c38e1870b3851c24e107073829c0ce006fe37e1becdf46f837b1bccde26ef3761ba8dd06e43711b7cdba6dc36d9b64dae6d536a1b4cda46d13681b38d966ca3641b18d886c235e9af0d746b935c1adcd6a6b23579ab4d586ab3549a9cd4a6a43519a88d4069e34e1a68d3269734a9a50d266923489a40d1c68d3451a24d106873431a14d0668033f99f8cfa67b33c99e0cec67233899bccda66c33599a4cce665332198ccc265f32e996ccb065732a994cc9e64d3259924c8e64532018f8c7463831b18ccc6262d315989cc4c6243119888c4061d30e1868c3261630a1840c1e60d3059820c0c6043011804bfe5fe2fe97f0bf45f82fb97d8bea5f32f897bcbda5ec2f41790bc05dc2ec9754ba25cd2e51718b845bf2dd16c0b5a5a62d09674b2858d2c3160cafe57b2bb95c8ada56b2b21574ab855b2ad1564ab05562aa1548a9e54d2a6152ca925472a31514a885432a09500a7e53d29e14e8a705312959494a38514286141ca064ff27e93e89f04f327713ac9ce4e5271937c9b44d726993449984c726112fc9764b925b12d095e4ad255929c9464a224e9264924490246122090848323f11e88ee47123791a88ca46122f11748b0455226912c892446222910c87e43d21d90e086442d214909483c41a20b905081c4072000fe87ec3f01f50f907c43e01ee0f687ae3d51e98f4079c3cd1e48f1c7823bb1d80e9c7423971c78e2470037b1ba8dcc6dc3691b28d846ba35a1ab8d546a434e1a60d286903461a10cf46723371990cbc6583281918c7863431918a0c406183081818bf85f42f61798bb45d42e61718b805b82dc16c0b485982c61610af056c2b01558a9c5462a11500a7453829a14c0a5452028b1428a004f827b13b89cc4de26b131897c4b6257129894449a24b125091447e23911a88c445c22a113889444621f10c8858428212107882c41220710188083fe1fc0fc07c43de1eb0f287803b21d10e4870837c1b90da86ac34419c0cb86543241900c6862430817e0bd05e02ec1730b785b02ce1650b185782b21540a8053c2941430a084f827613909b)))) else (if i<15 then (if i<12 then (if i<11 then 0x33915c88e4071f38f5c76e3871bb8d5c68e3371838bdc54e247113879c38e1870b384dc1ee0f7073835c16e09703b815c06e016ffb7f5bf6df96fb37cdbe2df06f737adbd2de76f33795bc8de36f0b77dbbaddc6edb765baedd56e9b749ba0dcf6e6b72db90dc76e2b709b80dbf6df36f5b78db96dc36d5b68db26d836b9b58daa6d3b695b46da16cfb675b36d996cbb655b24d8e6c5b625b0ed836c0b5fdaf8d7a6bc35ddaead736b8b5c1adcd6c6b535a1accd646b13581abcd5c6adb561aacd546a93541a9cd4c6a5351da8ad446a1b505a7ad3b69b34d1a66d2f69634ada52d28693348da42d1d68d3461a2ed1668a344da20d0e686b425a10d05681b4059fccfc67d33dd9e8cf267833b99d8ceb674b39d9c8ce3670b3799bacdc66c33599a6cd1667b335996cc9663330997ecbe65eb2f1976cb765b32cd962caf656b2b1954ca86533295946ca2650b27d93ac9c64d3259928c91646b22d912c87643320d902c8063f31f18f2c75639b1c58e0c6f636b1b18d4c66632b1918c2c5f62eb1718b6c5962c31558a6c4f6273131894c49623b115888c43620b0fd87cc3d61e30e9872c3861bb0d5868c3361930bd85ac2b61530a184cc24610b075832c15608b02d80ec025feafe57eabf05f62fa17ccbe05ee2f597a4bcf5e52f19780bbe5dc2eb9752ba45cfae69728b925c62e1d702b7d5bb2dbd6d4b635ae2d5569cb495a1acf1674b35596aca1642b1b58a2c3560caff57c2bc55d6ae556fab6d5a6acd5632b05580aba55aaac1556aa65502a6952aa90545aa19504a7b53b29c54d6a6a532a97d4b8a5952ba9554a4a4f5272935498a4a5242911484a3f51ea8ed472a36519a8c145ca2c514a899448a23511288543ea1e50e286d434a1950ba855426a10507282d412a08503a815406a024ff27e93ee9f54fa27c53dc9ed4f627a93d29e74f2a78d3c29de4ee27693b09d54e9a74539e9cd4e5272138c9c44e0a6fd37a9bc4dda6e536e9b54da26c935e9ac4d4a6993469a14cf267133699a4cc26593289934c8263d31a98b4c426193089824c025ed2ee9754b9a5c52de96e4b6a5ad2d49694b425912c095f4af25752b69584ab25552a89524a8253d29c94c4a5252528c9444a1250527e93e49e24e927093749a24c926092e49624ad254929494249d24c925491a48923e91d48da46523091748b2455228911487a435216909483a41120490047f23f11f48f947b23d51e68f1477a3b51d68ea474238d1c48e147023791ba8da46ca3591aa8d3468a3351968c9463a3151888c346123051808be45e22e916e8b5459a2c515e8ad45622a91508a6452228914289f44ea26513089644a224911e88d445a22510e88644222090fe87e43ea1f10f287843b21d10e487043721b10d286743221890bc85d42da15d0aa853429214109c84c425211d08 else 0xa544da26512a891447a22d10e885441a1fd0ee871434a1950c285d42da15509a849423a10d07a835416a0a504a82140fa06d02e815408a03500e8054009ffcffa7f93fa9fccfde7eb3f39f8cfba7d53e79f2cf8e7c33df9eecf6a7b13d69eacf4e7a13ce9e5cf2678d3c29dfcef27733b79db4eca7613ad9d5cea674f3a59d14e8273d39d9ccce5a7273919c84e367173899c3ce167073819bf4df26f33779ba4dc66df36d9b5cdaa6d13669b24d8a6c33609af4d766b935b9ad4d666af3569aa4d4e6a334f9a74d326953499a44d1668534099fccf267533899accce66332f996ccae6533279934c96649322990cc7e63931898b4c52627312987cc3a615309983cc166073029804bf25f52f697a4bca5e12ee976cbae5d32e79724b865bf2dc96dcb665af2d5969cb3a5932c495fcaee56d2b2957cab25532a39504a6e52b293949ca2e513286941c9f64f3273936c9924bd253926c92248323c91b48c6459228913c89e44b22090d484e4192058ff47e63e51ea8f1c77a3ad1cf8e4470e37d1b88d846aa34919e8cc46623231878bfc5e22e916e8b4c5962c91608adc54e29d1488a1c4fa271130895449624311d88e445e227112885442a20d10087e43e61f10f2876c3a61c90e386fc36e1ad0d2867432618b0c285fc2f61770b985bc2da16b0b2857c2b21530a785342921450a084ec26a13309884ac24a11f08d845c22a111087843421210307e83dc1e20ed07483941c20dd06c835c1a60cb063830c17e0bb05c82d41660ad052828c13a09904a824c11e08b043821410207d03c81c40da069031817c0b605702a814c0a204b02380fc07603501980bc056027011807c032015009803c0160070007febfedff0ff47f93fbdfdafeb7f43f9dfccfe47f13f85fc0fdd7ee3f6dfb2fd87ebbf4dfa2fce7e6bf31f96fc97e3bf15f86fc17e03ef9f7afbb7dd3eddf68fb27d83eb5f56fa97d3be95f46fa27cfbe75f36f997cb3e51f26f927c8be3df1af8b7c4be21f0ef867c23e09f02f807bfbdf9efaf7a7bcbdddeecf757b9bdc9ee0f6e7b63da9ed0f667b33d91ec4f617b03d79eb8f5a7acbd5deacf557a93d3de9cf4d7a63d21e8af437a0bd01e7cf3c79d3ce5e70f3779b3cd5e66f32798bcc1e5cf2a7943c99e4af23790bc81e3ef1b78cbc61e2cf1578a3c45e20f0e786bc31e14f08783bc19e0cf04781bc05dfeefc77cbbdddeaef37793bbdddaeeb774bb9ddcaee176fbb71db4ed976bbb51da4ed1766bb31d96ec8763bb19d8aec37613b05d7eebd75dbae5d6eeb675a3ac1d5ceab754ba9dd48ea2750ba75d32e9674a3a49d22e90747ba35d18e8b7453a21d0ee867423a09d00e7c73db9e9ceee7473939c1cdee6e736b9b1cd6e6a734399dccce65732398dcc4e61730397dcbae5c72db969cb2e5872b3955ca8e527283939c96e4872) else (if i<13 then 0xc388ead1a1922df0170018a284208ea0463784ce86d04088fa1d5d1da1b4161a3e875747686d05868ea9f4065a1b410233e875471686d05868ea9f41b1a384161a3e875416e8e10d868fa1d516c3a06488e1a63d45b0231bc3a28d0de1923147a8c2634224648c51ea30a8d6b6193400d00c916e267017001aa104000e81bc327416c805a7d0d00ced058006c9f4341aa741600d90680fa0ead05803641a03e9aa741600d907d0d06a9105800681f43403d864ea9c01b20fa1a01be3006c8ce19008c6f0c50643d45b0231bc3244ce021ea3778d0a90463787a83a3407575b02d1b26805c8dea353206f0f79707747b8899043dc44c821ee226430d93ba3646ccc81bd00b80023192b205e30034008c4708976c22543089634b205c8bc76c08c4708259157f8c022c901cb1c0540639203e51ac7015035648a358e03c85b6ab8e28d07a0a9d7c04729e8bcd80ab0ea340f42a010027d7fa2e386411781a6b61b237b0d6c55e9283002c89718026aaf4d8a3630d6b6d8a3d46f61a971869644a05e82a4476c5c35ad8716b6c35320756c5d6d86b5b2a0991851c26e12708983cc1b60c705b829c11e07f03f81dc0ce05302380bc02e002ff57fabfc5fcefdb7e5beedf62fa77cebe4df16f877bfbdcdecef677b1bd55e96f4379cbce5e72f33795bc75e26f09780bbcddbeed1765bb0dd76eb1754ba95d32e8b73fb9b5cbee59725b8f5c6ae2770cb82dbfadf36f3b765ba6dc96dfb6d5b56da96d0b665b1ad8b6c2b605afad7b6bcb5c5adad656b0b565aaad4d6a5b50da7ed3b69bb4c5a5ad29690b46da2ed15687b41da06cff67db3dd9e2ceb672b3859b6cd7669b33d996cc365cb2c5956ca5650b275936c99649b23d912c85641b2058f6c7963ab1c58dec6d635b19d8cac6162eb16d8b2c5762ab14d89ec4d623b0fd872c35619b0bd856c27611b08583ac1960bb055822c0d602affd7f2bf55f9afbd7dabe95f2af857babd95e8af25786bbf5deaee576ebb35d7aead752ba55ceae5d722b8d5c4ae056f6b755b8adbd6d6b675b0ad756b2b575a7ad2d68eb4359facf5676b3959bacd5666b31597acb5656b27591ac8563eb1d58dac6562ab13586ac2560ab0357fabf55f6af957aabbd5d2ae7571ab755aead1566ab2558eac355eaaed572ab5558aaad552aa7552aa8d536a97549aa3d512a85540a9f54f2a73536a9ad4d2a65530a96d4aaa4f525a92548aa4151fa8f5476a33517a8ad452a2550da85d422a0f505a82540aa034ffa7e53e29e94f1a7853ba9d74e8a72d38e9c54dea6dd3629ab4d2a67d33a9994c9a63d31a9894c2a6052fa97b4baa5cd2da96b4b3a5852b69574a8a52d28693d49da4e526a933498a4bd252925490a47d23a913487a41d1fa8f947ba3cd1e28ed475a39d1c68dd46ca35d1a68cd463a30d17a8b945aa2c51568 else (if i<14 then 0xc05c007bedf16e2a74103a390680710b9d53ad8061c8341b7f54eb6018680e46003906807bedf1b1ad8061c8341b7f54eb6018720d06a91ebad8061a03903da5c0b61ee3647b82d6000b57a0f6600bd0548d91eabd0705a95e83d97a0f61ee0b5801d576c3dc6f8d905b00841700153008417001ee3642684908a0f81b87c0840f40a87da341242283d0ea0f80a84d0f546824837f8beda8d0150ac1241e837d1c162fa04d088c682484306e1d01e8d90a4c6824df407ec682d83e0920f7410750bda382687a6357d01f85707c104329370a01118d015234054648b716c3628d0c916e238410670ce37c3b51a10c3d28d0d916e2081184a50d4006c8d8a343d6800f79041047b8c91ea37a8d11a02a4680a8f708303a8d40e1ee08a8d0c916e2644100c1720484151a082054648b716c3628d0f4a343646c51a1ee3247a8dea34324628f5185468648b716c3618d0c21bcedb8d1f4d1da0b8d0d93e83abe29f4046324fa0d8a35aa7641f40463d847686a347d2eafb6d40030e40b71d42f18d5c5f6de606c8861803646f8b71b008c20dc550c37c6c8df1923618d0981b02dc430671b23247a8de6343247a8dea342674768203c754fa68ed0da0b0d1d53e9a3b43682c34754fa6863aa7d0118e2d0c20b0d1d53e836347682c34754fa02dd0c2870d1d53e837c62db603c3dc64cb8046308648b70ce08c7b841a342e40251a0823dcfa1f41ee700118f71b1edb5000c390363db6a00187206c0bcd1dc687b9c81b1edb5000c390363db1c80467207a9c818546b54ef439008c490b9a3472047089a347205be02e0037c6c8c808208c64e02e002184c8323e8720490823e8720448a13e87206c9c8132218020de10c3dc7b8b710c208118d816e6a44c8f40647205e1a9d1c0c87b9c8de86a4e4023172248169c805a284e40c916e078118b9008c68649c81eeae3db0231246187b82311c21b0170010ce60118231243d8fa0f66347d07068ee007d07a9f41ec7d07ac02e0037c7b0f7600a8011bb61ee37e01082e0008c4908e80420b800f704610449082b3008c24f29e8bcd833815c70d568d0440d21821107beab469ba01f0cfd1408e022341edba034ebe1241bf29a918e31000c0220331c11a0f35201a031a341cc2f05f02b4683905e0c617a8d0150ac1242283d06e0c6fa04d088c682484507a1d41f02e09a1e98d04906e10d8d05b02a2dc470d91bb46a8d0de1bc3a06cd1a1bc224e28d915233a8d0f51922dc710dda34324628151ea30a8d0890440568d0b907501a8d04a570030040cba003200480ca342dc470d91bb468648de16e378648b71e833a8d0c918a3d46151a1922dc670c2635f14613b6e342f0470d9d907d28d067d53a0b640a1a007d04c8de11c3006c8c50463784c8de1aa2805b8de1b23245b8f419cc68677b6e34b20658b716 else 0x499180865ab69902a4e2ab816e37ae28a94473205488990c6a7014825057155c18e2462095b598571660918cb58b66301089b306815c00c113808412b6c042395c08e57020a646021a0208d02df31d80a47282570a08d000c178031640de58a37e5c5b61be88c6fcb8178224db4c856d322430cbb8b322e2bb6990edae28c9b8a326645c51b33206ccc83a7322644c8b8a326e2cc8600326644c89913200602d8042f15b402152b20ea82d15288e010a950d208449a990c009432c82462f15b5985916609188658b66201089b302264c2c8600031800898042f15b40211cb20472c810d20962c86804238431a01132094348210d20a410895bf2185c18e50c6396400231d219432863402254348e50cc018008976d23a0128691d009db48680463844c86600b2065c0219323a0128617921a010de91d0094348e804f164340231c2264330090d00a4340260121a0148680448d431a014268091923246388c70ce590638c728610d0085e2861b0b200f1a0124032aab740a9d17803740a8c3ba287a0a8c03a287a0a84012f054652dd0060546e8d5406054a0005406054e52dd02a35f6800302da36e1c9781a12947815033a0ec918e03906dabf4a40a80305619f2463864057d2f05405a1ac31815c918e28d25fe30974910342305a91e0542bf03801b2901219b24638a344a4318100db8e32451a0ce0430102bc90dd290132c7014994b36a34149afb53c70149af85e018150060136ab46b1c35f652c631c05202a14994b0e01801fa2d1ac70d7d8700c00ed571c51a51cae0490d0504aa75b28ed6ca1b5b0d858b2e0494b851cb2016e001258017a2a950d8006c2c817832c44e0011222700089c001241505009b4682d876092e382c051a341d824bc80634682a0760920f41b80ede81346c844635720220770ca15d8d03d0681352482d0dac682d81f0ec182d4d8eb901043b0c21bd4683b0d91534003004105a1802087607419c6f82d0ed4005488ea003006c84aa343d854d1a1a02dc1d0f736c3dc948f705b400648b7132208060b91054005b08ea343645b8f61922d87b8d0a343245b0f71b1468648f719c30a8d5001ec3d05b8c2124c6bcc0d91922647b31a1c0ea5c73866356d8500d916c366c75c8a34bd26fd00baa3807b0c916e2d86851a05a3d6801d51be324610991ee0e87b0f41ef6a6c75c80836a6e451a76d37e805a01c03d8648b716c3628d0f5d6d400d00231ec3406f8c91323dc1d0f61e83dc5b886074754d002d1ebad8ea9a0b1d7568d2f41c00e86f0f616e2386c8dda342e6801c8dbfaa40f682d6c286801c81eec00430d91c16195c0f61ecae04c8f7074378410f7b6c3dc118f61b037c43602e003dc6c8b7352284209c81d42e4c31d5c006a4e40f7dbe07b416b635208ce40891ea6a4e40c91ec078118f61a037c49086))) else (if i<18 then (if i<16 then 0xbc3a58a2de1d0b90742de1d0b90743254303a50c0e962d0038b40044d0056c0b6800891920b46c8891722dc16d0058b40016d00570b2044a8250d4000ad1aa342268d2b6a3404064889a343240851a16e2268d0b702146844d1a58a0428d015a3540020a86a34040d00895040315b482a00ae01e50038a03162c06a0066006015a010000603c570161e2809904030094825054020300c800031db50009012865d00078ae05e500a00161e2c00018f1406009a01402805001734000951a01805680500a00032800b9a014028000c5700328002d019400021b6018ada802c8097400062c5a0066006015a00b200490005aa180250017822680089a002f0448896002f05e30076cf15db3c576d8086160276ce61db602c04225cc089a00b14448c911340044d003be030ef80cb8a378658c96006dae28c5192226e28c9196adae29f418a2dc6f60216e2f05b8de1123247b8de1ee775805c560077ee2bb6353808658cb3aaed86f30078aedb016021bf315803c518a365e2bb61e93145be021ba365e2b9878b808676021122f1cc0893aa226805001843085c8b715340044d001b0754d482dc0477444b00c0422580032247808711a91b06a416e0219232c448c91aa3255b6023aa2dc6f1c5b6c225800b71136d8448b91843dc448b91b2308fa0d93bab16db1df76d663011d3380f14d4d98c04316118f4846376118a9846356118c28466d8c760256d66065899c042f07a86758a2670160211248c69ab61338084c8de1b234f010892462662088924626620ac5133104e01c5c0422491ab6064267010892460c86c8892460c84ce0258b660d4e023a6c01801df76c63b0160231cf14c73b678a6a4c7602c04681803b6c058086fb0078a32462e0276c3d05be0216e379e2e02c042a5800a9c04c006a8c9c042df010c273019c918d324630091832132c6844c86178226430cba00226802b6a00238448c91923415b0891722dc47500113402800ce31c248c7282018adb011b6c0422580089600238fa0cb1938085e0f51c4b170131a1be63b0108960033864d001a0327010eac054006718e1246387b6021a03246588919233864ab6c04638648b71bc3646731ab8b6d85b0b9112c005b889b6c2245c8b61ee2245c8b716c378fa0b7c04374e05b61ef2e162e0238b80b0108960022580089c04adb0108919232c6c9df56c2245c8bc16f80962e0211cc6b010a96006a7011d5c0563844e02c04308610b916e23b0118e12463816e0211248d5b0a013380844923140267010892462804ce0211248d628a0133808d00bca0032e8050017340280500a002e680500a00030449f458b8086f8df4478086fe02112a0a5c5b658b2e044c8290d2e2db0b81792e2db0f7970f16db0b9b6c3de5c0b99716da5c4b89716d85cdb61ef2e05e0b99702e65c0b99712e0060 else (if i<17 then 0x1800f63bf239804df76d0094748e3bef14ef8f63e83de6fbb6804a387b48e80477e4740291cc02474021eeed9501df54019d502231ee88d119f451c38a010ce3e877d474df76d009470821ed23a011df91d0084130091cc024740291d0087bbc591d00a474024470084908eb8a324115c51926da0108e56d714411c5b8b7144730039032ce428e00477e6282d05aada010a911c755431d53520b454aa051ca1a010828040b64728e3be2e0eaab6b30a1acc59804707020ca0941281db598143282cc51ab302868d51ab3166247423a3546acc08214346a4742391d08e8d0a1a34f168d48e846c6bae8696e95200a81fe8a8d8ac0722bf5201403da0c0fc0a84da52ca7a2b74a340f79b51a6aa1a69b555a3405434d5f281ca7a983d6aa08b1c069a00d541d06968bc60116380d2ca7aed000d3c63aae380d205434b2904819b1c348a344a4a983f0d297c04736c1cd540fb5fe8b8801e83f02a07c94b000a80301e8560f8c681ed5ff8a3083e23a03eed98055f11c0fc1d0d903e11c9be8e0b210c1e87b02b3218d0d50201f07a81febfc386c8de03e57d800540180f587300f8a1e80ff5fc0c0ff8003003ef158008e0a43143d03a03e192c702a63497b871df19d9209903d0c777d2f034e1da3b036093aa7d09970ed1d818eae4b3e84cb036093e8754919621c5818eae4b3e84cb8768e0b0824ea9f4265b178768e3bf9209903de1da3b031d5c967d0990c9e1c0406f07218a2df870101bc1cb6f849d1c1f403841284e600ad741aa1f01d01f093b149b80708600d801680c96a407b1a4bdca4549df09a0549103d0da3406c8153e848836f29d53b200a9f42445a87502cd90054fa1220dbca754ec802a7d09106de53aa5640153e848b94ea93bfb200a92207a1b794ea9d90054fa122ebe37c1f83a1b207f94d0e09a0b47a81fdbe12404ed56340fe2804a07a1c8248072ea00c3d07c0bcc6837ddf05403d8d25eebe37c1e8153aa4880ff5fe8a4c80a83d24457d8d078990194060b6e521507b83de53c386f71a1eeca78705e0823df94b0e0bc1047b95f1523383e44107ad7f8743c90dc686cf5f2bbc806c83debf717900d907bd7f94f201bc0f7870105901e80f92905a0301ef5fe52054750d087407daf88eeab4801ef5f5914806c83debe0fb94f1a0bc0f408f5f079d569003debfca78d0125900f64731a50ced806500096f141e3b678a032800150194000600c018ed80604b0183246280ca000f0060b70194005b8de78a03006500192032800b70180e9cc0150180328000ca003240650016e0301d00ca00488063b678a030063b6018f140600c56d400db50056d400658c9a002f07a86758b40033d0057003064ac850d400064c5352224648c956d400250b7a00128250d93aa3268004a192032802b801940064d001122e45bc3a1123245 else 0x2064882172022800b738b400045000240328001c172ae280012a00031475000742395b50019340047286a000b68040451c0108002d36d401e2d00571402803b6a0140011bc576d4028050050540011b00b6cc00fa30076cf15db3b6c0430b013b6730edb010bcc0408d800c978b80875602a01400648eaa00208efd0011c77d805c53beedae28c951d80ae2b0019237e433001926d8c3602193808efe02600c0064ab6b8a77f01300b6c7d0eeb001be3d45b8b7c042defa0f416ea1b01186c042deee8b91ee374649dd600c00efbb6353809476023aa6a5db30076c3745be02730f1701602601808753b6c04edb016021b140075500a00308610b776c2dc54d001046a46c1d511c6a7010a9046c00d48e2c04360d482d30d80864dd51aa3255b6021927546a8b7c0477edb602184c00610b7b6c3dc610b91842dd431dd3e8774efbb6b3108ce99c0353663014231e908c6ec2315308c6ac2318508c11ab694019c4ca8694019e118d356d08c69c231ef1046028684630211e0256c0c84cd1a064265431d30642668d3b6a0140011d00a014005cd00a0140280023a0140280004600011801df046325436021be7d2e28c900971464e02104adae29c511d716db03a9716da5c286b6c7d2db1f43bb2e01d5b63bb2e05ccb8b6d6dadb4b8b6d20811cb89702245c80460077d5c0a991cae2549a95712394130060077ddb186c04a3b011c830ced8d4986c05808c3398600eda41023601809db48ec0520a800c991ca3b015001ee2e55c48ec054005ce021b123b01482a012091180460008c5c88ea00ae280500a002f05e0b91782dc6c50010d400c3092172ed8c308956d808db60251c21b01186c0408c11b0060061b012b6c04218430c91927207ae02446c030108e5043dd47202c056186c60210d8084322330c2498018611380864dc8c0432464e021bc7205b8de192323010c8446c00e42b8c0461b010821782f1800b71722f07b8de1722f064986c046185c8bcc042dcc30b917888d800b936c238db0f758b808e2e0230d8086c300b8ac006c5c556d8086c0d819380b010af38a2e6e28b7c04360c3602192722e28d8447715805c5570720433003538086c9c8c0408ec30eac058085e0bc1722f05b886446618490236002e55c18611208d5b01e84607a1181e84607a11a8204601180004601808412b6c04218411c8390ae0432b838b21b01082c042196fe023bf21941282390ae301482352a0811c8e30d238c3282124c0241486c04a084709276d80a4118611d80a41482600340e4602192ae30148230d80a410de78b21b0128212580a41186c0520a41300c052098060290580a41486c04a0a4102330d20811c8204720811c820466185e2b81b07200f02330ca09800f6b6c3d9801df3be325430df97037e5c0dfb6ca80474b88042087b4b851c7d)) else (if i<19 then 0x340f6affc51841f11d01f76cc683685208fca7800153e809008b006001481e8150a40f7afdd502b7178d03d6003242901febfc00287b61b207f9b0868c40e86c81fabe3145b82ce520462f0670484dc08803086c683d87b0c88ded4852b8a036fa0150b2c6b072861bf1db8d0d918a0b43e0f503e1e92483702cc6afa03ec1c0207a8d903e1f41b8526357741f06d2bf7558d03dbbf7158d01107bf158007a03ec6808b001be1343113207a08c0b300bab7d01a706d0d80b071d53e84cb83686c05838ea9f4265c1b436020c4754fa1322b0363071d50a47d0990df09a1889903de0da1b0160e3aa7d09907c0928dc0880d0a4c002d8dfa6d83aaa84a1ea07c2381100010c1207ddbe5240b6c801e104a107d4920dc0b03e08211032249baa8081f31a02a1f10103e63414b94f53b6c3dc1e83ee527d3a40f70821beefa49b8a0a81f31a02a197aa811e000901ef5f2b00478002407bd7faa811e000901ef5f2b00478002407bd7c02755022c001203d1be11c5bf36059d54118650100909b8210221ec2180d6001a432237b520f9800520501ec4307307bca40a9c805a3a01ef290247207403de527203403d0180442484d051dd0e46201b2137af82ce52218120de8820f42901106e0f41403c10dd57100f507a0f394f531ee0f45bf740103601213701fbd006b1a2b177ee282a07e0bd80052051d7c6f8151bc0b40f8f73900549903d0f60549903d0f64c80a83d01904bba0d939007faaa411ee0f4118f711c21baa80d0f20578d39890c049410b61525a826a2207a8382d83e07ac000883d023a3b0707c3e9c681e8f5eab880fa03d2e9d571003d1bf57daae2007a183aab401ee0f432f55c400f794d5f4a1c681ecdf76cc014720e0221481ea0e09a8883d01fdbfb4c1683d0220b41e9df76d46811d1a38b4681f04135346a8d04102a61a8d282047468c351a00877c1151a76d46a8d3c5a343268d03e0823d05bd1a1ba2de8d51aa342a411d1a1aa3268d0c216e106800e8930f1420815a3546a8d086a343246451a1782de8d3c51b146811886a35468430df083261e2c9805aada8d1b6a354015b5000cea1a800c91ea19c5cab85054003395f00861a8d5003534006484a192ada805000942de800c9a00716802b8a003254750038b4028d0821723de1d0821720e85ba869712081d43a16e2de4103a9040e85ccb80743de8d51aa00ad816d001934006482d50c754410b916e0b6802b85054014750005b4028001c56d46864d00038a1a8d04107d46a8001c81d468312820441394150007c10411282a3404a41282a3404250062504089db50004740027282a354028003e0820fa80500a000894151aa0140011d00a01400110125054680ad0000808e80500a014005cd0078b40011d00044ae01150005a0568d51a105402802b601140025500192 else (if i<20 then 0x676c6a5db0e01eeed9cc0f61ec6da806b61046a45b8a9a016a45cbb6d6d4007b0d8d6c7575b02d3526db010c9baac035b1d51aa2df015d557030adb0c21b36d9db1d3b30702cc3b6b6ced8d4d985be3da5b3c51bb08c6acb684630a11ab6b31ad8e99b6c05ad8411d31a6267015d3570266209b6c043db5b12356c36419032133808706025700c97a6b63a6c007b0f6b6ced8c73c51eced8c73b61c03dddb5b676c6a4c76025be3dadb3b6340f166f8f61ed37c7b0f636d4035b18e1c433864eb6a003255b08ea002dc47500b1c2e5db6b6a003db5b092a0037d5c18e0093d07b0c956d808476b6504680db186c0433b5b30019c325800c95e8209800f65e83385be021c18095c6b66343dadb0b61ee6db0158ed6c6387130016e23b0158e172ae35b092c05ad8c702d36d80b5b0823403db5b12356c2804ce02140267015a0571ad8d03001ecbd2db3b63903d9db18676c381db5b676c6a4c36025be3dadb3b630ce62db3b631c61b012df1ec3da410f67312087b0f69043d8db500104bd0c30b71796185cbb6d6d4006c6b6125400c30bcd6c01180004600ad8e46b6390ad91188630d2198d4861e8a38c74825046195c4866003d9411c876c7215c0f61923dde2c86c04a086fc86c04edb0148230c37c7b48260180a410f790ce61413b6c05208c36029049070148290d809410df90d809803b6c05208c30df1ed209806021923df01482c052095c1b6c04326e46b6104721800b71bd7215c0de447ad8e40bc1783245e2231792e3011dd1b1715800d8b8a2df010e0b8b80b5b3001b07235b1c836d8087bd86d6c618750f76002f05bd86172ae35b01e2462f111eb6125808c30bc36c63b016b631c48c410f6d6c48d5b0c903c0784ce021c18095c0f638bad891eb6391ad8c3602d6c6830101e56d808db602d6c24980092600bd0413001a03275b60256c248648b7125808706025703db5b123d6c7207b2f412461b5b31a36d8087bb00d6c618710f76014005e0b7a0161a800b9571adb010d830c2f06f5c55be3d87b6b61ecadae28cb3903225c5b6b6c3d6db4b8b6d2e25c5b61eb6da5c0f59712e07bdb61eb6da5c3c59703d65c4b8970c007acb8d6cc0016b0005ab7c6feb63aaad8eaeb605aad854a238040b75b1d5352bd18002d6003d96f9d576c754eaaf41ec3647baf4184bd16f83273137ddb40235219d6fca98043dc994a9804b7c16cdf76d008d48f6952c00712df9530087bca9804f1654c025be20816cdf76d008d48821ed2a5804a98052a6010f71b075654c0295300a54c0260037f5b1d356d6635b0df2461040e4821ed2e1628415be070807360e6d541ef3621c02a8d07d66c1901e51a0fa463a2f360e60f4aad1a07c0f4a4811a001481e87ba340441ebd507c07c0884603e0441581fbbe0ac94fc56340f42d83e07a0ad94fc56 else 0x21d7558d03d61c3658d03dcbfc391d0d903fa3801dd50f6056e2b1a9e997f8738e7abc681ef0e8e80406c81f9e9c806c83d21d7558d03de1d63b2fdd5e340f66fdd548211030300092c693b05708f3d0218f78821047b87d0e81b78307c0823dc15929b1df158d03dcbf7543e71a07a1eb94f485e9639208606000b3948d0e343d89b803d6c5418d07c0a4126d4d8601f7158d2761be11c16729e900f87bc412920fd8d0f707c1d38307c0823dc5b6743aa4880f813b1d7553b034d6c7543403dd6c4882b07c6340f6c765fbaa1f38d03d0f5ca632dc84820f4020f629241b6a8030cac683c1496340343c0651b21cce403d0f01803e24107b21980282092c693b04d08e0b3877551ef1041ef451041cc5c83d0f1d57900f707bc387b71a1b0126c7007b8a1b58d2761ee9d8368df1b20344315807fc685b70e11d97c6f02d03f7213b81f0d45409903d2a04c87b83dd6d97cea92307b97ca813207bad80602ce52000680f604e1909bea9d6c0358d15009203eea8076349d87b8651be03443276eaa0578d0b6e522a72f9c82440f6e427703fadb94ea90c47209103dd6dca754e5f3904881ef552443dc1e9581b1adb2f9c82440f75b729d5397ce412207badb94ea9cbe7209103dd6dca754e5f3904881e878a6dd579003d1ea0f3aaf201e80f762eb6253a398d02d07ac001683dcbe367901d507a3d6aaf205e80f66ff200c15541e86d4e9c82aa83d0c0d77900f707a1b79055507b97c26f0e6901c81e82db6ced9e2876a001d9db06076d6d9db1a9a00b7c7b5b676c63a802df1ed6d9db186a00a087b5b630d400023b65bf6d83b1a976cf165b3c50eced86e8b7074eda800c2a0035464cb6a003085b83a76d46a804b6a00238670c996d4005b83a96c489db5001794025b50010c326800de1782dc1d0bca012d8495001794025b3c596c0b55b50038b209415000c463a41282a01ada41282a014003387678aa0a803b6a001d15c0f6a001a94150005b4003b3b6a0037e805001ee1894151aa00eda800dfa014007bd00505402803b6a00012805001ef40280500196a08169b6353400649a95e8208250b7a00382802b8d6d4035b5005054007b2b85714006c8b78743dc7bab6a006da800f6193ada802b605a3645b82da00382802b85054015c12905a0b55c2b6a346da8d2f40383d864eb6a343255b010a342dc0851a1c146820a82a3410554d1a56d400db500018bd0410c9d6d4007b2b60103245b808a003801d0b95707175b5001edad87b51a905400066b6a00ae07aab8553400648df970ada806b605b0103b6b6553401e2d001ed4007b5001ed401e28f61ec3d9800f61ed715800c9d6d714648f6b8a775e2db66016d9802f4b6ced8ea8f)))))
def pL34: PT:=(2346,4,7,13,v41)
def x82 (i: Nat): Nat:=0x2cc20208909b065439e00004f052c15417403805841201b909787982d40fc04f84c407c1f00ec051c22c0180ee845419e67e0e183202ba0e90d5016c26013b0af00f01c41a50b883f82d01cb0c80aa80a01e51bb8a9c55e16c081031036209d049817028819f07c83643e627d0c700c007e1df15c03ae80e15f01507a821607d0fc815c30a17e049068501e0c509085187862fb0930de408e059058007007a7c004a875465809906b0a0c21a17508b86e8100e1001583900441f762003a02360cd0a4058c08609708a0af030e08f0ac0c540681ee01185e86200af066078c2d60d707d05c83303640f8870054615c09f187c19c2b30fb006c0881bc04606801943b301d07203da26008f83600981690e703ec1aa141167030c1721d004301081762a60fa87702ec08d0a78a4427e1070b10c7035a1330d983f40a81e107f879c2c8137036828586c1e90db03cc26a1c50ed83485f806306589c82b4c2c07681fc0dc081124aa0465c1ef04b02881300410a6beb416204500004ad0ac00040404f02c011c04580002faa2607703be42219206d86500721b031c00000000d00ab87181681450e985b8392c621b286883b21c40a6109c3d60ad063022807608e3ac848c3d01e40a487818621390e383c812814308307502b61a9044069015c1cc0d4047835819b05ed02c3a40f512c06ac16a09a0b302703b41000e50cc033c2b72d6897c0bc118305009039a18d06f846463a0f8bd605b43701de09d034432e07e0df86b804a31115a04f43c40c9144021c4fc0dc02306f838414219686bc3a2109090065863609b0e0862c4503780a802942ee3ac00006d06ec0a807385482de1700db81f06241931548c783ac10509404882a80b708781a41cc2820da80000d00f10a98ad80000000000ad423405305582c837616708184443461b201080cc14c0da0f907b037a07418b01741ba1f80c4030033a00014006442aa19a0eb8a540b41f402436b892000001c02010b800000c0c800a82f010380c280080c00010488002120c0581af5020004e26008600a0804314040f0203d1200090e80401018000a030182019ad1184402050200c080b0000c180d00008100601168000e00078000d038e84000010802c0f2181810010603c020b2101c08ca04088260a0783c7c130d01d081d1484c0059050005a0b000501e185f008041a0f01800060f814062000000a404
def w55 (h: Nat): Option (Nat × Nat):=lw0 142 437 9 13 9 4 x82 h
def x77 (i: Nat): Nat:=(if i<2 then (if i<1 then 0x70a5601240f9c11304b2020e27c01df04c207fe15b029480c603d40a381af83d317fc0eb403600b5033e0b4015c8567096211880228a7c06800b1c14400ab095c0fc811e04d6189014c8268842002b20edc141055c06f0042810204ed05d412e416a03190396017c16203e205120e601a58171002e14f01b6839602b6037017904fa007207f817a802a02d20e1828a037e0a3e087841283e401ae08f4026003712e807a000681d302d613ac28a828708c2c09c04b028008bc12181a0822d093a09f000a80c301481000253001811f4123c1d50332005601380d581c404a60e1c22b02e6036e017425f848a012e0c080e800e7041804f422081760ac8022411608aa07580670ccc000605f2048811c80bc04c010d00c983140a8012440d601c904b60fac19483ca08d00674152815402fe0f800300467096a09a81ee0c4702d8100411c0198111e099c00d0539016407341fb84dc0366c09414a056b0080000000807800c0885e004004019310020a806800040180023330384380104e80c0040201e02c0302300b012b98008010780ec2d8040020889b8050080bc0000b0060201c8060087a40088d06c0f8058030661683600f25e018000480040000d9b505c114018000d40040d8050000480300000a00004918006a701502306402c00000002000039be0a401e1900f000000000170220346680000e1e4088000243007284b0420040a01c0060300901302c0680f0ea0100c0040090020400800f0c20004f00400001c1080100200403800000000270050383580580300e7c8000890500a4210000de0100000200419c0080002c0780200200015c010010020d80000100602800801000000028090d60281680a00c0000b0190002a01680100409c020090000000383a01e0240e80a0360381400d07e01c1c8660a400c04b5a0022040005400c1441100c0040f8298a104400079021868004210020a60002a8041800280e84005c0000000a01a000080320020240100804000c1d83d00003c1a0331d60047904100e70014269034064000000a000c0287f0020bc0001100401c0000303497c060000323ec090360020200983e58a0205d20a0460140680b0288b08f00626e620000070001142c00500656c0080d1a2058000c500e00016895002034de81a0063780180807a0940103003201c0d0030240dc0202000c16c000070760980200d0180040e0040160000100103a010010020aa0005d80a00e00c060400261442600202a0002c8140000240105c0760a42584c0b02400e0000020006280d00c0000c00000a85400006016008528120040000d0001500e80680302025c0081500210c000090261680080809c0f00900d0100802f83a0060303e0010ea1601300835e0180000e0408683380305802c0e0210140040680203059c3483402a02400000 else 0xd40ad41ac043a068804201a50112113e048c1fc80bd0a1622f01ad04b40a9c108413f818a073e0890196041704040fec03c049906fe0cf01db04ab0a300334033800c088c0f0411702bc030401dc17a042602f613d40430508057a0f0808f80aa09e40fd41a3801614fa8660167832e04c804180420819067407180d2048e0496009402c8334030203b012282f7023204cc100006f013c01c8814051d046e15b80bb81df0084609810c04cf07c2001c1ef854101f414cc19981c7133011341b982d1049e0c5412b031f0ac2153000f00d907d205841280459006c00c000202c6067609c0143016f098e04a00a80316020a0a9c22e00df03e2053817982f8062610241b2846f05d600140750020048614a0151834609e002e40e7050c05aa14f80f604ad086e0708072011a053610c01bd010b0280158817782b4065a137417d042804800f1c0dd056603600920093050a078a01ac1f2800205d2029c04c048907cc0858071004708300c70020829e11d80600060802701d613e014c006807fa20881248433058a098c07783f163340ac442f82b2178c0e901090948062e11d003a818c051a093820d807a1336033c0df821a09ae0ee42b4043b044e06401b703890a7403281b90408083e09d00af055e03e611084f983e809e6043c086823a138a068008d80b1079a0bc0081856509e20bc4100855b007a138014602c2092c04bc05d029a058610681178158030a0f2405281e20110048414584a90614052c0b000c7006801881c884cd07dc086c28c825f09040d4c0a1032709280aec06f0323103e09081af00910042088012e84c1042a0f54054835c0642148401700740a46097010180e802a202501c780fc0238020459681bd03fe27c4024030900f2109028d8361117c0cd809904f606ba14fc166821306d22734057850008380e8c11900e5014407982a6849b01fe01242190131010a14dc045039e081a04d402780a0079e0948286834909b610880b201e503c80e8801f027701760ec428f02710a5400980320266053210f453c8922027e09f425403550390134c1aa003b07ec06b42ad000908ea06680b504b005941014282010c08c00f8c1cd82cb06ee146810400b70a9209bc47c881806b604e82870535031c0d0c197810e0ade0b6c025017c0a580f7408c00fd0120107429800580796055815602f6013a0f181c50444041411c00bc8257056607b4183809303a4103c15c021405560b94139816d068a117c0fa01eb07180e401c002d705600ec01a103b305dc0d48203027901980ea42a2042303ec014402303d1044a05d42af810207041230235005c04220b3011482d8096e02fc00884de03ae0e200ae8383086c22ac0938326079c141c1a7002c04dc0c180ef0490168c0e5009701e30ad403f802800ae059c0e0421f81bb103a13940d) else (if i<3 then 0x22018408b4048010583bf01a20934157002d01a41310188032a022e05a00f08559048e2f2c0da814805fe03381bc833704b010f801482ba00a4055c2538115042e06a822181fb069e04f01808022082005240ee8300089e15545e603f4041c109c29581fa081812882ae81f215ba057018f03de007403d40fe81830662135009680a8073a10541cd037106e0027c1b20056090a0ce40bd054603a21124263035909c411cc0eb0003031a068c01c02a201360a985e40143008607540ca08a90a5e0c481ab838d054200502b0048106a2c66024b848b170c13400e50308092a10f024381b409cc087c0c304780294141829a052d086a115c28801a208060dd824985560a9006c416002e009d803e015f82ed00ae12700de054a050812e80c58501093002080a3849a070a03c8188827e00fc003c6250402017007001eb805b055e09ec0628163036c04d00e7826d10de053401202340896038c28b841102b42f240ec00660352059c0f48269006409d810e8230026c026851d80b4065609781b5807008f20ff01d580d409de2e501030296022605941fd04fb08ca22b016e033e099c04e014a84be085a01c40dc840401cc13dd414024a088a01d8236035000f60780092810109be123415484aa08c80e9c284807f0a4e047818c02b609660a0c1a68231052215a4080054b06080fbc2828189123011d809f00ad038a0cf40083197021202b0271823f09ce27bc05f030f05c40e8411400ed022201a8096015508a4116c2a383db604c0c880508210051403e4288800e0ac607504d98144038612780b981f007a4229823f050f00a807b80b903d907fc01540a601dc08aa050452301880ada155c23d01f700320234068039c00e6111c0cb817401e81324036824c04ea154411d813b01dc036027202c906ac1220169015307da05c02a8037b07a8114005983d809d427881d40083078603842a1047c00241038209000a01d2028c192001b03b40dd048c82b701e613680d404c5029e2f2818682070a6212481dc04c0047c063c0e601af04c200cc21702e308720b6810481b20a701284047014604540df023704190138150c216026809fa069812c83f807900af81d7039908940bec22984400a8a00bc01f8023086212ec27c848400a6002c000808f063414ec046016206ea0dbc16c82510000030802683da05be113025e829c00b401a416980d3066b465c13d046307980704043839708cc09b0256041e03b60e54215809909a403801e0053d076803100bc0063054806481b5046d063600a01d284c304e40bf40d084290a04049058f840a09aa13280d3805e006a11f41de8223093e0a4011983930a4c144807d83b506d0088425781be04b411200cd83bc09d20954082033000fa002017382fe08e20a3c11a83c4084a064410e02e10aa60e9814f845407 else 0xe02fc0aa80fcc1b302de0724083c00f84ff030e0a74250037d061c153c0a902ec05ba079c09b826508160ee827082c804820ebc1d904fe0a6c1480088011d03f00a4822c01ef01961360252015f01ba10a828e01950690029826c811603ea0b5804a8262080e11c80b3023608d613b82660558082c04ac25e013005c80b04078841302fc0864106b19903b20c0c18e83a0007811ec07b036309701200032822211440a4c25b030509060a8058b83bb01160ca01eb04a301900c9413584c8025209180d2808008d205f413c006e0a2c34d412a00d6028a10e01c7033806c02f1c27e09e701800e101a600b60a26248414b9828032c06e006d82ad050a0c2c0cc836209e80e2c2a9003100f80aa01158cc40a060354292052202280cfc26580440a5c1174064816e06ce14940cf0040003a3314095013908280fb007b82e805542ea81e80a4308fe012c06d0320050213a00fe0061089c03c018601f9002611441f8036c08ee02c04f90205094a10bc1))
def w50 (h: Nat): Option (Nat × Nat):=lw0 492 1474 11 15 11 4 x77 h
def v40 (i: Nat): Nat:=0x37f4520b001ccf60f676adb0ea398ec1a86618823da5f756b84ca76adb29aa5a9208f6d22c872062ae122adb29aa5a9c3a8e63a5f37dc8c683dd7c8e20b00d54110903d1b729aa5a980882d22c87220e091f4c6b5fb7ddfc1a8661824839d5ae132d7edf77f29aa5a92088e055c8c683d1b729aa5a9c3a8e63a068240cb21f4c6b5fb7ddfc3a8e63a098180cae1d54cb5fb7ddfca6a96a6c8ae01503122ca4a9c388ec18f4f140c3dc4d3db1ad7cdf137292a70621a8ef16b80903dc695fca700d163888015d7f29c388e3d0d537b1a03029c6306c8345c687601b5fca700057458e22017f29c6320c685ebcb5a79a8e86796e6255493e32251e150e0600fffdcbfff5efffd5bfff52fffdc7fff69fffd77fff51fffda3fff5cfffd52fff72bffdc77ff71bffdc27ff729ffdc67ff70
def pL36: PT:=(18,3,7,8,v40)
def x81 (i: Nat): Nat:=0x60013804c91cc07d017800c0154016202402b0065c6e000007f708406e6028805018802601bc01d01ac0780090029008005201b6810011405901ec07101d004201e80656025c6f01b2813010c02301400720100808018c057002c0580128027a11c006017e42500528199118064011c054004c05c0004440709005d00b4066a05000f0168018007801c01f802f01e4002008400e703c02ca00800d002804101a8811202807001a080c408c010000c048006c02860fc05301240730144069019d022610004b00898410094011001402e604801f0024012018402a01d40443030015002004fa15c076006801701f003f011880f01dc0046040056013405b91648228c00135f287d202801171a4f000500730200781900050700016640194402021f0000081025014e05472e0a001138001e02
def w54 (h: Nat): Option (Nat × Nat):=lw0 49 147 8 14 10 4 x81 h
def v39 (i: Nat): Nat:=(if i<2 then (if i<1 then 0xc88c60c34c10be0bb8b9cb80b54b48b20af4ae4abca94a80a70a68a44a38a20a149f09e49d09c49a099497c9549389249008e88c48ac89c8788588488308047e87c079c77475c74071c7106e86c469867066463c6286005e45bc5a458055c5385285044f44d44c44a047c46845443441c40c3f43d83bc3a838c36434031c2fc2e42d42c42ac28c27c26424823c21c2081f41d41b819c17c1641441381281180f80dc0bc0a008806c05003801c003ffee2fffb6bffec6fffaebffea6fff40bffe9afffa5bffe5afff2dbffe52fff93bffe4afff28bffe2efff22bffe26fff88bffe1efff86bffc76fff84bffc6efff7cbffdeafffbe7ffd55fffb87ffed9fffb17ffebdfffae7ffea5fff407ffcf9fffa67ffe95fff947ffe4dfff927ffe45fff8b7ffc89fff897ffc81fff887ffe1dfff867ffc75fff847ffdf5fff7c7ffde9fffbe3ffee0fffb63ffec4fffaf3ffeb8fffa93ffe9cfff3e3ffe98fffa53ffe58fff943ffcacfff933ffe48fff913ffca0fff893ffe1cfff863ffe10fff7d3ffdf0fff7a3ffde0bffb8affec6fbf48bbfebeeff89bff5eeffd7abff9caffe70bff9beffe6ebff9b6ffe6bbff9aaffe69bff96affeb8bffadaffeb1bffabaffea9bff902ffe3fbffa9affea5bffa82ffe9ebffa76ffe9cbffa6effe96bff8b6ffe2cbffa52ffe93bffa4affe28bffa42ffe8bbff88affe21bffa26ffe88bffa1effe86bff876ffe85bffa12ffe1bbff9f2ffe7abff9e6dff72b7fdaedff5a6ffef9bffb86ffec5bffa97fde49ff7847ff5f5ffe727ff9c1ffe6f7ff9b9ffe6d7ff9adffe6a7ff9a5ffe5a7ffaf9ffe557ff951ffeb87ffad9ffeb17ffabdffeae7ffaa5ffe407ff8fdffe3e7ffa99ffea57ffa81ffe9e7ffa75ffe9c7ffa6dffe947ffa4dffe927ffa45ffe8b7ff889ffe217ffa25ffe207ffa21ffe877ffa19ffe1d7ffa15ffe847ff9f5ffe7c7ff9e9ffe7977fea5dff8b77fe19dff7277fdc1dff6a6ffef8bffb82ffec4bffa92ffe58ffb873ff5f0ffd783ff9c8ffe703ff9bcffe6e3ff9b4ffe6b3ff9a8ffe693ff968ffebe3ff954ffe543ffae0ffeb63ffac4ffeaf3ffab8ffea93ff900ffe3f3ffa9cffe3e3ffa98ffea53ffa80ffe9e3ffa74ffe9c3ffa6cffe963ff8b4ffe2c3ffa50ffe2b3ffa4cffe923ffa44ffe283ffa40ffe893ffa1cffe863ffa14ffe843ff9f4ffe7c3ff9e8ffe793ff9e0dffa937fe9cdff7237fdc0dff6d37fdac9ff5aaff9caefe70aff96aefe54affae2bfeb1bef922efeafaffa82efe89bff1eeffc7aa7fd69bfe727fd9adbfe5a6ffaf9bfeb86ffac5bfea96ffa81ff62c7fda49ff6847ff1f5ffc7967fea5df76b67fd68bfe723fe9a8bfe5a2ffaf8bfeb82ffac4bfea92ffa80bfe963fe884ffa873ff1f0ffc7827fea49ff7237eda8bfe892ffa10bfe7d2ff9e8bfe782ff9dc else 0x21d52de8e638897d0c2b231a2e1df6a5a0b22b846aa96a58e19ec8ae0233791aaa6f408d1a321d3b7ed508c41b7ddf63ac8ae03208cde469df6a58e22602b22b8c6886c01a037adfaa6c8ae100681dfaa5a908d8e80ac8ae0e237b1aaa682802c8401f4682df77cce6a48908cd9ae31a320b7aa5a9225f408ec8c68b8b7ddf08e8680ab8639d537b1ab7e86ae300755a0b7ea908ec8ae11a682a96a68e638893d31a2e0c8c00b8379df3628e63889bd0a9c68b8321dfaa5a907af4680b83211a77ea96a42324af42e31a030a0320f66a68e63889b54dfc68c82e300320deb7ddf0b68e638893571a320b8b7e8eb5598106df77da908c89b548e3231a2e100d7f184a72007c5e5a86ac3a06c0202c61745565ed7f29c3b180305e19c09ca70e80a485d11a978090b75f81b0e8e15546a5e48822d7f2943a488e11a97849f151a1d8762d8a923886bd3c5ae11a1dbc5ae11a2d8a9238863dfc53d91af14f63d11a2d8a921823bd1c5ae31a364a9218233d8b82dfc53d041380b8f14413d0f62e3c5104f42d8a966086bd3c5ae02321a02209c8ae31af14f7104f437c022a6f47571a0dc74167c50f815468df2a486a3bc5ae11a03bc508ab8468df2a486a3bc5ae11a2d8a908c86809f4a83c5ae31a37ca908c86a81c5ae31a364df2a42321aa0f14b83dc4137c2321a02a81d5ae31a37ca921bc5ae023f148eae11af14f7c68b821a02209c8ae31a37c230088ef16a07d31a663c5ed823d7f06c01558e22008b5fd1755d2238468154685e37ca923809b22b80311a024c8ae00c4688e3d0d53791a2d8a9808237d2c8ae31a2a4f408cc83671a378df354232e0f7104de37cc580823756c8ae31a37ca9662c8ae02337ca908e02682c8ae31a3211a378f7c68de2e0d9c68de320232380221bb6682c8c6b5fc63204a71a8e2480335fca70e8e11a92041d7f29c380cd151a8e2a9a3a823d0c886adfaa68223ab63221aaa68ea1882b161a3d2dfa3a86354b886adfaa68623ac52e21a37ea9a38c82e0de86a6e66c669e68a67665a63e6165f25d25ba58655653650e4ee4d249a47645e41e3fe3ca3aa37e35a33a31e3022d62ba29227225624221e1fe1ca19e1721461160f60d20a2086066046009fedfb9f91f69f45f1df01ed1eb9e95e7de55e1ddf9dd5da5d81d51d2dcf9cc9c95c75c51c39c0dbe9bc5ba5b89b61b35b01addabda99a7da4da259f59c59bd99196593591d9158f18d18c18b589188186184182d8097e57c57b979176975973970d6e16c96a968566165163160d5ed5d95a958955d52d50d4e94c14ad48d4654554253fd3cd39d37d3593253052e12b92a528126524122920d1e51c11a91891651491311190f90d50bd09d08105d041021010ffcfd8fb4f90f6cf4cf2cf08ef0ecceb0e94e70e40e24e08de4db8d90d68d54d34d18cf4cd8cb) else (if i<3 then 0xb6c69c8639d56db1a3dedf716b66a68e63a023dcd9722b8c68f7b7e8ea0ab6c69a9722dfadaa96a41e638f772023ae11ab7eb6aa5a908c928098e3ddc8ae31a3dedfaa6b603100721a032e8e638df755c8c68b8714f60b68e63a86720df3571a2e2a9a3ac866041cd92943b06d151a1cc769d87648b45d565f43b488e11af143e46815134b6ca4a9c1886a0a8ef15f40f71ad7cdf2a486a383d716b83671a0f8b74db292a70621bc5a39f413441d7cdf0f68ec1886839d5ae04d1eb1a4db29c183ef143d3dc41d7f292181520ab87203dc687657cdf1372983b0623bc5a39f40f71a77da9a3986f1411ae11a19ea96a6c87228ea09f446adf77c4a6a586a38d9ae1c546adfaa482b2041b7ddfa19860ca8eae1d546aa90440ebd2c846822b7ddfaa5a90228eae1c846adfaa411b2100105df6a68e61bc5ae11a77db66a423a398680bc5ae31a3abc508e8ea088223b1a7d2a9a3a82b211a7d1df08e8e755c8ae31a714df6a42361a8e366b8c69c56a423619f4f171a2e2a908ec8c68b87d2df08cd9c68b8775df08e8e61a02756b8c68ea36023a388e20ab8c69d5b7e8ea1ab8469d508e8ea1a824031a755f4b7c23a3a86ae31a754c22de86619f408dd5c68b877da961bc5ed99808ea96a48e20ac8721f408ef4365d308edfaa6c808c41b7ddf0ca8661998ae1d508ce2aa5a9b21c8c00f42e0a077ccebd1d5723002e0a0716a96a686619f4f1700280b877e86bd1c8c00d52e0a077da908e8e809c8ae31a36023a3900ae08e20b1a722dfaa68eae11a722a96a423809dfa39c8ae31aaa423a3a82c69f4722dfaa423a3ab8c69c877cbcaa5a908cf77231a2e2df77dc56a42321a02a38d9722b8c6adf08e8eae1a9c69c8b7ddfaa5a9ae1c808ddfaa492bd1d5c00c82e0a03daa96a423a1986f14df23b1a2e2df77ccb08dd57208ec68b8716df77ca908ec87231a0b4a02e2dfaa6c808c4119b06c035f882385541fd7f29c0148cdb18054111635fc01068823855428d7f06d175546a381a4670472980900c1b455d2201041102016d7f29402205223807cb6ca4a9c388ea09f4b203dc6b5f12ca9c388e3d0c8034d937b1a37c3cca70e238d53d4de1075f37cc50f70e23a06756b81347ac6b5f37f292a41563ab8b203dc683cca70e0f4f737841d7f0e034d9378c8c6b2943a06dd0152380c63ac80f71a0251a03067aa5a9a398ea0ac87d0de46adf77c4a3268e63889756b8468c8b7e8eb5441b7ddfa398e22432a1ab87551ab7ddfaa5a9b22b80898e3791a024823211a030094000c1051a379df6d9a96388980ac8ae31a77f0037aa9a3a82b211a7d1c5c00de37cc9a398e225d5ae31a321b6c00dea3ad5c68b87d0ddc00de77dc56a58e22602b22b8c69a9c00deb7e8ea1ab8469d53aa8e63a86a0a027d1d537b1aa3a86a0900c69f47568ebd31a3 else (if i<4 then 0xf83a07c7a0fb29aa40dd22c8839f41043e035f4755c8839dd1046dd7ddf839d5c683ddd015c01d509306a1a0208e0e035d57d132d7edf7220e036b87571a77d423083ec1a865d0248380d1b5d510736aa5a9d56c8054f41884d2e022d7edf77c11209c875450ae1c508b29aa5a9c1a86619f4f143e2384177f3603a861b8a90540d1e9d52e022d7ddfca5a9f1415c683dd7f29209c808c11c00240f4dfca6a96a415838241940d722b8c6b29aa5df055c8c683dd7edf321d5ae050c684d0f329aa5f47220ec683dd7ddf7141541886560248386d3640d722b8c6b5fb7c23055c84c83dd7edf77ea96a755edb00134c82e01508b2937c2d83b00f148e1d8410f75fb7ddf12e0e239d57141c0f75fb7d290084d83b1a0b43d57db6ca70e639d512f1a0303dd7f29c380cc68cb0f44b11f0ea398e0300d7d1d5378c8c6b5fca70e0e8de07c7aca70ea380db545e7d041d7f29c380cc68ded7ddf4a70e639c512f1a0303d57f0ea398e826060b00d0316a3aac8ae31ac3a8e8190003609755f44cb5fc3a8ebd0c80345e7571a508c2c3a8e6380d7d06d031d517841d7ddfca5a9f171a0540c0f729aa5a9826060340c588e2b22b8c686dca6a9402c8034157d122d7ddf1404b6a40cbd00d364d0378c8c683e2df29aa5a9036c8639f40305e1075f77c8e826067550e0340c1b6c8ae31ad7edf402b80341575522ca5a963809ae065c68c80335fca70e378410f75f77f0e63809ae02c1631a3200cd7ddfca5a9ae015c68c803329c398e7547612c410303dd7dc5ca70ec680c32c3dd7d29c804b0302d0f75f77f296a482f171a0540c0f43d2d8a9c388e722f4136b83671a1d8b7ca4a9c388ec1886f14f63d04d10460ca70ec1bc5380f413441ca70ec18f6f143d3d0411db29c388620ab87203dc6b29c3b483d8f4134411d84d4a70ec1a7437c2d1e9d50f71a3dedf6d9a963986f1476ae11a19ea96a68e63a8661876f1482468f4b7c4aad9a9a398e618f7366b87151a104f7b7eb6a398ea19860c8f7ae1d546adfadaa96a6c8720223dd8eae11ab7eb6aa5a9a398e020823deb87211aaa68e1dac840041468f6b7db6638f7755c8ae1c5c6a8e639d572082c69c53d1b6c00f73da00774f7b7db663986808f7756b8c68dfc01d53d8f7b7e8ea1a82ad91a754f7b7e8ea1a82adb1a7558e7231a6d8f7b7db66a5863dfc5682b846867aa5a9b21c8680823d11a3dedfa08d9ad823469d308c413dedfad98eb21c83dc3208eb846adf6d9a96398680bc53deb8c68dfc01a03d8f7b7ea9a0ac8ad900680f638aa96a423b21c8c6882280f4b7cc9ad823619d53dcd0ae31a715a908dc8c69b63dcf7b7e86a0ab6c01d5680f7b7ea908e82b22b6469a0b7db66a58e808f7722b8c6882c01c83d8f7b7ea9a3a82ad91a720f6aa68e639d5208c8c68f43dedfaa68ea0a else 0x715b6c398e1d9d5c683dc3a8e638821d9d5721c53d31a3dc7c0e8f607f0e565dd104f76db0e638767571a0f4dfc3b06401d54c8f63de5fc3a8e722b6036767571a4db0e63b066186d754413ddb6ca5a963876f171a0f4dfca500d21223d862ca6a96a48ed22c81d8e2134823d31a9d847ada5f3ddd5540d0036b87171a4db296a50ed21c8104f73de5fc1a86402b603676755226d9a96386f1dbc5c683dca70e209c8c68f60f476ca6a96a68e638821940d720f6320f4c68f7c3a8e755c8ada74c684d0f30ed54413dc3d9d9c5adb0ea398e41a5f560f71b4d9035c8ae31aadb0ea390097dc84c83d9da5fadb29aa5a9248f71940d722b8c6ab6ca6a997dc8c01a00f44bc3a8e638dfc0076755c51043dad929c3a8ef1476c682d0f5b6ca5a977e0ef171a0f46dd5423057007d024d7ddf839d57171a0f47b11e027160e035d5091c87d31aca5a97d3c5)))
def pL37: PT:=(309,3,7,12,v39)
def x80 (i: Nat): Nat:=(if i<1 then 0xc8c06c45d5174c02403f402002441e9046008001c40cb017016313c816703d41ee06c8190051c13b00340bf02ac0bb01c809215080ad05dd88e04e8133083003b0479c6e610418306500d107ac1400530058025c03407900b6002805d01bc168038c811062406d05b008404f40c60729885000247303c010701640220000178003c01303bd1b301a4032055c0ed06ec000000010615f8000039c0c902a1881002c09b0404044045c000072c1a500001cc000004d01fc0a4013c12503301c6000009e000007602e00009118181135c00002f019c139c1c813581db008c166000006003380f6036000001d017504201d200e00e105e8104037407506f40ca07bc00000f01e306440fa005c18200381fc02d00250168103053811313544d905c091b06e008806104d2026405f06780e507c011d1518073023010501500f20000000036814a91640b912d001100040410544550052c04c049012c00fc143000003102f450d07d9db3149015805801d962081c703640810190185054800000000b3123809000f400005bc00003800c3a47c00003b8119071015c0000000610008506e400007d4000151c1c206884ad069c4a0155c11507381d805ac18a04dc1ab02b8000045000001240b203480fb04d400016f8000136016912941f806d00c814144b60634203001c05b122284732081c3049804e0458156079420b03f815a13440c105080ff03b004215444de05e455612dc0be15601fb020c18712cc198023401000649b301280d508040b002dc05020880350000063079c47701140ba01ac0947229005042c1651550555223018003140aa023c17300dc4ac01001de05fc91c033415007980a107e409f06d8055039810e075808e037c13e0050188154c00202281a003ac13c05541e8028808b60400e4077c206051012705d01d104a816d05d8039215c06515d8100073c046174809c07e84d0046816a00c01dc06a00c406e8164a6cc4b260fc18c05040c0002419305140e2024c122047004703f020f005409a06841ff30841ed056416e043005e13501c0043c1f1057814600cc4d30120123034c0f403000060000500323c000180b0180a0200203c3f028012880103c020ac5e008300083f0200d0000204415000000000303c000000403c10004000240a300870180700009060000000300802000340142c0040000405000010a40d018090140302c0b0000c01c0201814000140d8000003206074024071740c00020004070000200479004b90c805008130e8000040700c2200004000410002200c0f02800008060e802004820281d008050006e00807048110b800000012200402c0a09c000040000400014090501707c300440801ca80040004002024090682b138020701404c0306c3815414000040105c0c00600c03048180041009c270000d08403 else 0xf102b013801b80d4066c50901ec19605f055906f013904800a707f452f058801201480a002945d4061814902a403e01b01ea064803a04a415f22141280550112014413f06bc1fe622412b021c4c802c4209102c096021815b033c1f2012c02f06dc1ad04241d406d40a602d4110071414d019809512e41b306b080906380c206980e906c00d7065419a04d800802740ea065c17108281a3081085804bc02d0800207075446a042846305f80c701f00f8074c0e80378043003007904c011103dc16115d41aa06741d007cc47e11e814805f4172078419901840d6014c11f04c82080815c6f07dc1ec083405604c41be04b412e037057405ec1a400d8062521814f11501e002bc15d01a00db0341c8e22184b806fc10204d01ae07881f401dc18f00001da0774000019c18b12d449301f41c10260153048408212ec20206a411b03cc078126820e00001c9148819f04340f900004bf07341d70224070028d)
def w53 (h: Nat): Option (Nat × Nat):=lw0 202 641 10 14 10 4 x80 h
def x76 (i: Nat): Nat:=(if i<3 then (if i<1 then 0x150050180ac00b0000b700800600900300801300000c00106d00722c00002a0020002a401b14201600000e00000400d0ca00701f01600f01601700500200102600003b00200a00200d04d0380010020100160f401702700221e01802700201902a0190000180000000180150163bd0151cb03a07000f01b00200e00803e06a0011a701c01601101d0730240175400100aa00600d01d01f00f58a01000a00e02909000e03d08502b0020020000020030145c801e00600100b01000048702500505c00700f00901000800002e0070010130a004c00a08548300d00503202800400308c00e78e00001003701103423b00000900200100500403403b03100000000001f0020b800d00e00400211f00000005f01904d00802003000e00b00200004202000500c00001f00708700600102209100402c01e00b0030010f403a00603300f3b524c0050080f500001b03876900b00c04f00706400004d03600000200a00002a0ea01907f00805615700703304c00001800d15d00f00002302b0020200160171210020020680000c606800000000000100902a0720210090033260040060560140030710070280200140020060000cc00504900d0ab00100402200d0040040d600200b00200600f00100000b00300401500102815a00437200f01200031c0030000280c003501603300000000000a14400001901100109703500849601b05d08703200200102400a0170610d40060000020ef00000b00000000000700402b15d00100000a00200011a1410000d105900010b00600b03500000000500300200203c01601100200b00310000000000800a00104d0101a900d0ea00000900200700e0020ef00b00236b01e01003700100f00000003b00000200a0100110e53c71d70d100400000601700600600000c00500202700327d3b100727700305600705700500500d03b00900909705712c0e300302003300900900b17300301403101d0120490580140020130020100050563f41a300002000500f00505c02300007100107e04c0020000150230000310090b10030000bb01901509300002b0de0a80310120010030000090be08d00b0180050910040141431250af08b00502006100300000016c08700e00101101013200200048f00000c06500200302b00a00000000b00100001f01d01900b00000400402000000103200000200904c0025960040150040070000090010040610290080d403600301002800000300000301701100b01a0070002ba28e01c00100700100500000d00f0700030030000d044103201e00005100344000000900000159000b00200501100017400d00002004f02a0010ed0005e400704400000401502d00d03305c01e00200c0000031580470030510b103d03c02200700a00100606100108b003073002015006007025012000024000 else (if i<2 then 0x2015c0298056001ab04a5047b075f2172005500cc067e125807c401fe026106a202970363054506d2085900fd08d704f804fb06996427050f0384080e01c2035f064e0056090302a501a0068603090856025604eb0667086208580658054306e50202008708e706cd07550916045b062701b701ea13fe08d9028706920134127300f40544091c075e03be016d05cc05fa036101f005fe0506400e07af08f614d104b9055d077c0054105f06e6024c07a2092001f90726019e02d0036b07d4091306ff18f9049900b000d605f7086d0183004e177d04db05fb04ca00b70326008d083f039c042602c4b16e00e90419078f0442039700f7121304ce020e0467017c063d03f206f905570480070d02ce049f037b018ba4171345055b02130503026f06840542033c00da16c90592003e0003068104c8059f016a085701e0031e08a9040d03b006ab00e502e60030042000b3044402f3056d04e301e3122a05a602ea046505d703a60103046d01d4026205820355083703ec0878051404af03810294057e0821043e06a80092009f047802cd100206090790025e053e07520601028f041200970586007000fc04230567089f022d013d057f00df052504240244074d023f0243005d0382067b031f02ad14d81615091f0487032d0566026c052407c301ac08fb077d085c125e06fc07a008fa04e1079f5175001002f40770056804bd048e007a06773010068c02b81162057508d3092304ed0418082c065002a100d304860646018a066b002a07980169046a08f4000f057103d800dd090107fc02b903f90636013705490439077b00a5641a03ae062f07ec021602c107ff0237007c055002fb016008ed01af05f203b3061b014d04a00760027e0813052c015f076d0428018e006a08dc086e04d3a42203c4616f03ba013b064012041024004003440223177e06620759125405d5083601f2073f0227032c040006ec028405ec066d0350038d014405c408f80922007d1377085d078004d105d105720717027d05981164084005e5066f00200101100800200001600400100200003e01900400118701201200604800500f46500200000002c00000100000d00000600700902500449800108800200800193100001200300112900001100300200000000e0070000000101ef00b00100400403701801000000000900900300c06701a02505f11200404600100a04605911d00003e07004a0010010050020360be00700001c0080df0cd00f0623b300900313900002300300f03239e00300400400a01600d04206c00100206800400500000400625516f00002c00006400f00500004500004102017400700000003c05d05c0071cd01207800000001102236102f00300a00200800d00e00701700907b0bb0160311d300000800702e1c902100000002902601e0400 else 0xc028203f7046b2173103e025304c3033a067c05c154180817012300660127068506f20433080b04fc0527091204e012c100f30435066a069b11cf06eb042e05540332084c21750825089706c90603048d02780455033b04ff02c0022a02a9036a076f0167062c0470067d0724160208770178053a030200cb2073011301f6055e07ed034e06b1055f15fa01cd0809031d036e084201a1068d070108f207a906c6078a03aa0126090e050e086507860643052e02810263617400f5050d00ff01d907ba07510750003a002f04c2006b085b06a607950657039215ad001700bf00691368341e075b0318048314db002904bc02a70068153b03a8016c01a9b41c022800af0803026606f703c20380060602d4076a047d0743050b1448060c0062088b06cc0647083c070601ec0674077f115402ab02a808e208b9b165087008bf021b0772115102e0035b31641231046e036f008f059403d400e803cc024e06aa01091253028a14b7082a08ca069a053208b306590879088901620725089107aa07440536016503e906f403ff032f01f704ee00e108fc05be04e9025204a200ef08410651012903a5022906a1002c7168061404a106b2014f08a1120f038911c7020d0019135004f514de08f70277000e05b903dc08b6030604480848015307eb017f0404085f053c011d0151010702cf04160778050a08300454115e08c106b5027c00c200d7071a02650894061314d20649067f08b40484076e0663049e0174043b062311b406fd02df037905640704008e06bc06730148057d07fd11f8023c00280314166d003f083107d3072f04aa08000403117d03a902bd04b70621092708d10225089507e5010d07cb017a08460259600c03c7061a059b045f08920624114b05cf02b314da07cf035d083401d00784073c06ca034a086a05b5103d06c310ad04ae01eb04b30826817206290709071c08a408cd02753417069c030b045102f508cc072a142b01e7079c0515a4230815185e061008de07d60001035105f505cd016302a6035e00d9120a089608c8044c04d501e10450052a0463082706d308b701f50541023e085e070b0173058d02aa021e00b808ef059c1008145701bf0849058b075c0519022204b602d506d501e9040702f8123605b103fb06dc08df010c06300596020a137a0911044b09060083013f12ed056f071900be04d0081a01a80242070201cc015a1307083e04f4079d081e032e05ae03ef0289027a01dc006514e001c603ee06330270034b07be16341007087101a701df069e03de051f06340645070806020410071d01b405c3037e015b07f3057907cc034107bd0639069004de01b814c10782086b1156011c015e038705b4051b05a51488004803e3000500d2040e070a003308a2087a07d8079e02af617c0328080203ed06b7088e08c)) else (if i<5 then (if i<4 then 0xa03a1023201c00338035408c503f50632616c115807570845047914d302ee065b029e027203f0084a04e808d606cf06bf052105f006cb05df01ce0073010804a70102009c00ca011804df0431045aa41a02e2005904e40251026700f8081808c9616d04d804b40746000d03a40185017d08c61704023803bf06be01ff028d03e4024f02a0013106bb04fa0192026a065f1195054a022602c804b86416008b08cf02d106a40679017b04cd08bc04f901a5065e00ae05ab0523057700f60747054607c20756089e12cf02ed028e059a051d061202dc012e04da02ba037d018f029c05ff005f03ab073a0012071e090c03100325080d018206de0394029b076705260730014c063507e7049505ac139612f701120722008000d507150631006104b2045805e4073e177c009e010a020701540215086800270504125703bb05b60085012d07f5034d089b0347026b11f7082e05d908070184086403ce009d0300040c05bc06dd08cb004304b006e814f8136e03d9000203741267035204880288052b034802d90305006f09260593071301a404d2087205050839015d030a052200ce01064429064801c502a3077713de074a078b066007f8004c08ba02b105b2044605a8024602cc06af05eb070503f407e103e80303038f0067043c07cd13fd03e7087c07d907a8042c0094050107a5030d0432138e06710042070004fe076107b3022e020b09100481014212e005aa070e06df09140076022c0638003b01c10235087601550590090d08c7073d082f0293014900a6039e04c5054f084b11de059d01e8141814dd013e081103ea00e2066e055301c8044a002b059905a405ea084e008905d6049b0218079603d500f101990766047c217402b5040f0493019304bf12c41861044900c301f3027608af05f60409032107ca000a0096080803040866079202f71152063b0026022f033f01aa081d045e054804850196400f16071781091a00b9065307bc0388000706c101d600f208ce1408060b03e2038e024a042b03b8061f011a1009046c031c07fa024700a1007202ac026e027b036d025408e5002d0583004903c1034514e9048a027f120d033305690511049808ec089d61670869000809210146001c06e4616505c00334018d042d136d07b00018053805d4000603d20408074f0721073304d4044d0359000b08db003c0492021706fa023911bf07ad02800191061905da087d0020001113a203b6066c05f4120c025802b0082305c6021c07790086178013eb00c414d726f5039902e402b20098017705d3003803eb0687090907fe616802fc011e04e2090803af04b100b404a80824125b03b7008a04520024009a00cd07d0007f0179014008d2010f02c5035c06b00712063e07b103e6060f01b0041c031606f005a207db00eb0009077400fa1256045 else 0x1082208060395012c030f000006e10168085102da03f104bb04f605d0039b0286146007186166019d0559044500000000a42904370477000007e2054c0000091900000430000000000773043d06e006c800e7008811d301b601bb043800b104ba05fc0000004f0509074e078101d204ef04400000000008471572047507df05bf122006610322052006b8075402740576011705c841787177000006ee0436047604cc03db00e414690578000000dc000002de06e3025012ca041e05e2075a217102ae081f00000793064ba41f0748088300000500031302c703d6057c13b71490063707a708b0019f03530051072e007706b30881003206f505020230056500c507d7075300000563000003c507d507e80000074c02f00000058108ac13ec000005e108fd023104151606053f0925001a025f000000bb128f00000707064f00a7055c02bf010413bb01470269079b030c066408dd07da003103b5041a0472153914b202b70556029503c6033d07b60201002106b4071608da038b077e08f50417007102cb08e6081003df100a717504140132091801c901431442068a00e00539004700630110063f083b0421029603fc02fe04fd07b90121011b0187016f053d12f6086f06767010057016c10425009b031908b800e6033e07c90206053708d402dba41b016b078907ef090506d914d502f60644068004430882005b03b2038307f10776051a08a803d3028c08aa0013058a08ad0608059e028303bc0211038c00d0064d088a0323024502b40508025b0411006d01da0735070c0758616b08d80829043a0255039d05a7069f0260516f021903ad046f00fe05ad053b0875153a116e014a0335047f0902039f036607c61260053307b706b90698006e03120447032a08a0040b05a9004d04f2a41907e00729064c0844001f05e7073912e6169703a004ad0188079907b203d0086100c00204063a4011058401d7061c066908ab056b007b07230405058f05ef0749072c03b1071f00750025316e084f061107d2090408a706750833039006d4051c090f028b0234616e00ee02bc083806db032b07630023151b050c027105f308053418013c001407ea056102e7069d0510009303ca06d703fa300e07f002d704a30045017e0924035606ed125c069306074074078c00a404f00200048f017508730307073201bc01fd0122034007e4011503c003c80852012802e301ed01e402640654034c04530292058c068903cd0152033003c9034f06c0011602d8044e05de06ad08b506a70456003402eb0885b16404b5013603080625019501b3101c05d204f308a506f1008202e1088d004b01ee00d40893081400c7091e00d807e903720573091507f60212040204c707a6077a0111036217340156036c01d504be0365055803d703e00917018000ad062b025d055) else (if i<6 then 0x1062e01ca029103240208033905ca0337087e05ce0734076b087407c503f8037302fa05dc01a32177080c641708860855012f014101d307e3061502a200de08c3516e01a2018601cb0060086c0249127d0331025702030801007405f1065606a302a4033602dd01fb0367060006d802e501bd088808190835064206a90531052910290469001500ec0900125d046605f9066506c50398022002e8130a076804dd123d01d8009500ab06520311006c0236037a081600c803a206d00368022b03b9012b0119042200aa11e614d600f905a008e4010b043416ab08b1242107a108f1050707b400f00198a420017208e3051304d907a408bb0039036404cf153d088f11ee0037120e065c062808f3076206180720005701de0105089a0530049a081c021002c203c306c4076505e012850120023a0190031b0285001d06fb01502010049c01e50441341a1203000c02900691049d068b01cf02c9054b0133071b06ae082b0738052f0740024b051613dc1063074107e606a50714120b02d20641047307c102c300580899069501f1061e03e108e905b804ac1003130c072b01dd00e3032906b6060a03f3029d316a01fa1379048c06fe04cb05bb08ea017608ae0620086007ab040a07c7005005916176052d020f0164045d05a103fe12431308037f00ea034601b9035805d8010e017008be042701e602ef005e023d04c007b501590497066800a3007e0360042f044f031a0166a41d05340655004a05b307c000cf517205e8125508eb138806c201b5141a086300db107d04ea153c026d01f407f405550273060408a6017106970785054e087b04610626058707dd0044076c0248052803fd03490562020909280474a17201ef05a30867040105180084041b04c4124204c1070302ca003606ba021d05db089015a914b604e7089c005303e5019b07ee03700884040601db08b208502072022405af0588013a05c2060d0078013505851188088006ce0376116008f0164b02fd07280130071006bd07f2057b030e023b06e90589016112bb04e60791072d065a06ac077106e7019c02ec08bd01fc047a075d08ee0471049406ef01ad125a05520682024d14dc01b200d104a601c303ac019a0000051e01ba00911259039a03750460056c01a6067a00b500a8080f01b105bd0907a07401e2062d046404e56164054008ff08f906d10396054d0377065d02f2037c0000085a00ed0320008c0468012a026805ee0727716d0016001e02c600000000011f04570462042a216f092900b6076404d704c9038a04f108fe6172029a073b03dd02e9018903a30887079708e8069602bb02d603270342083d03cf05c7076900a20459020500b208d5060504d604ec0853090b07ae004105f8024007bb021f116805fd05c5070f154f091d04f7005c074506940214005a022 else 0x683035a041f05cb05ba002205740775064a120905b0059703d1053505170489084d037807de0099078d00a007ce004608c4177b000407f705c9048b014508e1023313ac08e001810138083a0843039107b802be0090014b016e047e058e05dd00a903a7316c078807fb089807110393135a01c707c808120279074b0124025a06d6080a043f030106da056e060e078303da037107ac020c08c00491012505ed090a029f079a14e301390299061703cb055104ab04dc01be0157080403b4081b15aa06ea0197038605b70820074208d005e3010102b6041d003d00c904a906a00616061d0580051200350052114c00fb05e602f9007906f8068f08a301940482641907a3018c067807dc121606f301f80736056a0081011404c6057a00ba05951768014e068e1263010006f6082d0547067006e20496024107f9091b05e901c4002e1210416e06880854062203170794087f062a04900064034307d101ae04290672121102ff08320413031507bf03bd001b066604a4038500bc01d10369082800ac0731b41a02d3063c00c600bd177f00c1015806c703f60737025c021a088c0787078e035702f)))
def w49 (h: Nat): Option (Nat × Nat):=lw0 869 2632 12 16 12 4 x76 h
def v38 (i: Nat): Nat:=0xec5f5b4a5530e474190cf4e2ae234b654a390c027a715711a3b4a631069017e8b1a1c57dbf295483a0c8647715711a6faa50c02e2a81711aafd160155a40e0415f6fca5530e470240cc85c03234df54a3804c85c46abf298740090388c179528e432098ab60d5b9d15e315288b0f0e03ffdffabff7ff7ff37fdffe7fe2ff8ff8
def pL40: PT:=(10,2,7,7,v38)
def x79 (i: Nat): Nat:=0x1c00000000c080a030340a000080004090004000000402c18000703c220204a010001
def w52 (h: Nat): Option (Nat × Nat):=lw0 9 27 5 9 5 4 x79 h
def x75 (i: Nat): Nat:=0x1c4100f5040048424c01a00ccac421600005e840404ec3609182b0050634079a82005a0bc007830800005b04103c80bc12403780001f4000804039017e12800008100480d301f837400007206500d41f602003f037c00003c08480c4022063029033c1b000000001540a808400000301062ef07000e42640ea00f036c00008906881a81aa09407b83042000180770348042117060003816b475053023812202c01c033421a0cb61b846101004209704200520c704a828405e08b0000800d600c904c02b425208a058026580c12d07781c41d809d00e883c0ba05c00d981c0b027602602f816200009500201c2004032847812008f034038c00002202330e426202a01b01e000011004d84541f803b05b000019802609290d007c00007e844c0380b303a80581ce0d701ebac409408d07483d019c246087019809611900002b802a11f04098184de06008380282600d002b043c066077093802c25804e01581000c400602681f41d0116000008c22243601d027825e0ba00000c80d611a08183e00200c606f024804a09333982bc140001006807e82e0e618281c0244048020817c1a811260402e146a20107583fc01206d00980001c411b06c81b1c6c0ab06e00b800608514022c4086000023905c256059b0b81d81da0b2090029000000200b81841e009f099b1d8000106034800023805005a00001880f904d080c0fe0e5053836818a06e02b819010e096000029414409c054841009210c120821800007903382200e80c800002dc06000002284d023a01202d045000004403e185c15407304b82ec1500000298bac0a20d6085000006e0f605181e820a00004601ec028102002800009e0c305c83c41fc0340200062013c87416030a0cc0e2e108680400150047c042c87c4612178440a0109b5c2e06020a00c0000838004a001a810076c00800dd2d138260f068c80407000000403028281809328e926563c800041206bd1f4702a05804191d000160035004bc3b
def w48 (h: Nat): Option (Nat × Nat):=lw0 88 383 9 13 9 4 x75 h
def pL: Nat -> PT
 | 24 => pL24
 | 27 => pL27
 | 28 => pL28
 | 30 => pL30
 | 31 => pL31
 | 33 => pL33
 | 34 => pL34
 | 36 => pL36
 | 37 => pL37
 | 40 => pL40
 | _ => w23
def pI0: Nat -> Nat -> Option (Nat × Nat)
 | 27 => w59
 | 30 => w58
 | 31 => w57
 | 33 => w56
 | 34 => w55
 | 36 => w54
 | 37 => w53
 | 40 => w52
 | _ => fun _ => none
def pI1: Nat -> Nat -> Option (Nat × Nat)
 | 31 => w51
 | 34 => w50
 | 37 => w49
 | 40 => w48
 | _ => fun _ => none
abbrev bk:=bk1 pL pI0 pI1
abbrev bm (k t s a b: Nat):=@m130 pL pI0 pI1 k t s a b
set_option maxHeartbeats 0 in
theorem c24_0: bk 8 0 0 3=true:=cb1 (ar:=9) (by decide +kernel)
theorem a24: bk 8 0 0 3=true:=c24_0
set_option maxHeartbeats 0 in
theorem c27_0: bk 9 0 0 1=true:=cb1 (ar:=9) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c27_1: bk 9 0 1 41=true:=by
 apply xh (ar:=10) (d:=2);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a27: bk 9 0 0 42=true:=(bm 9 0 0 1 41 c27_0 c27_1)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c28_0: bk 9 1 0 71=true:=by
 apply xh (ar:=9) (d:=3);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a28: bk 9 1 0 71=true:=c28_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c30_0: bk 10 0 0 36=true:=by
 apply xh (ar:=10) (d:=2);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c30_36: bk 10 0 36 470=true:=by
 apply xh (ar:=11) (d:=6);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a30: bk 10 0 0 506=true:=(bm 10 0 0 36 470 c30_0 c30_36)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c31_0: bk 10 1 0 23=true:=by
 apply xh (ar:=9) (d:=1);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c31_23: bk 10 1 23 768=true:=by
 apply xh (ar:=10) (d:=6);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c31_791: bk 10 1 791 601=true:=by
 apply xh (ar:=10) (d:=6);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a31: bk 10 1 0 1392=true:=(bm 10 1 0 23 1369 c31_0 (bm 10 1 23 768 601 c31_23 c31_791))
set_option maxHeartbeats 0 in
theorem c33_0: bk 11 0 0 1=true:=cb1 (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c33_1: bk 11 0 1 7=true:=cb1 (ar:=10) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c33_8: bk 11 0 8 55=true:=by
 apply xh (ar:=11) (d:=3);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c33_63: bk 11 0 63 465=true:=by
 apply xh (ar:=12) (d:=6);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a33: bk 11 0 0 528=true:=(bm 11 0 0 8 520 (bm 11 0 0 1 7 c33_0 c33_1) (bm 11 0 8 55 465 c33_8 c33_63))
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c34_0: bk 11 1 0 331=true:=by
 apply xh (ar:=10) (d:=5);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c34_331: bk 11 1 331 768=true:=by
 apply xh (ar:=11) (d:=6);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c34_1099: bk 11 1 1099 768=true:=by
 apply xh (ar:=11) (d:=6);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c34_1867: bk 11 1 1867 479=true:=by
 apply xh (ar:=11) (d:=6);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a34: bk 11 1 0 2346=true:=(bm 11 1 0 1099 1247 (bm 11 1 0 331 768 c34_0 c34_331) (bm 11 1 1099 768 479 c34_1099 c34_1867))
set_option maxHeartbeats 0 in
theorem c36_0: bk 12 0 0 3=true:=cb1 (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c36_3: bk 12 0 3 4=true:=cb1 (ar:=11) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c36_7: bk 12 0 7 11=true:=cb1 (ar:=12) (by decide +kernel)
theorem a36: bk 12 0 0 18=true:=(bm 12 0 0 3 15 c36_0 (bm 12 0 3 4 11 c36_3 c36_7))
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c37_0: bk 12 1 0 52=true:=by
 apply xh (ar:=10) (d:=3);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c37_52: bk 12 1 52 178=true:=by
 apply xh (ar:=11) (d:=4);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c37_230: bk 12 1 230 79=true:=by
 apply xh (ar:=12) (d:=3);simp only [cs1,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a37: bk 12 1 0 309=true:=(bm 12 1 0 52 257 c37_0 (bm 12 1 52 178 79 c37_52 c37_230))
set_option maxHeartbeats 0 in
theorem c40_0: bk 13 1 0 1=true:=cb1 (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c40_1: bk 13 1 1 2=true:=cb1 (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c40_3: bk 13 1 3 1=true:=cb1 (ar:=11) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c40_4: bk 13 1 4 2=true:=cb1 (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c40_6: bk 13 1 6 1=true:=cb1 (ar:=11) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c40_7: bk 13 1 7 2=true:=cb1 (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c40_9: bk 13 1 9 1=true:=cb1 (ar:=11) (by decide +kernel)
theorem a40: bk 13 1 0 10=true:=(bm 13 1 0 4 6 (bm 13 1 0 1 3 c40_0 (bm 13 1 1 2 1 c40_1 c40_3)) (bm 13 1 4 3 3 (bm 13 1 4 2 1 c40_4 c40_6) (bm 13 1 7 2 1 c40_7 c40_9)))
theorem v18: ∀ k ≤ 13,∀ t ≤ 1,bk k t 0 (pL (3*k+t)).1=true:=by
 intro k hk t ht;interval_cases k <;> interval_cases t
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact a24
 · rfl
 · exact a27
 · exact a28
 · exact a30
 · exact a31
 · exact a33
 · exact a34
 · exact a36
 · exact a37
 · rfl
 · exact a40
def w40 (a b i: Nat): Row × Row :=
 match a,b,i with
 | 1,2,1 => (⟨4,by decide⟩,⟨6,by decide⟩)
 | 1,3,1 => (⟨9,by decide⟩,⟨11,by decide⟩)
 | 1,3,3 => (⟨18,by decide⟩,⟨26,by decide⟩)
 | 1,8,1 => (⟨257,by decide⟩,⟨259,by decide⟩)
 | 1,8,8 => (⟨10,by decide⟩,⟨266,by decide⟩)
 | 5,2,2 => (⟨34,by decide⟩,⟨38,by decide⟩)
 | 5,2,5 => (⟨5,by decide⟩,⟨37,by decide⟩)
 | 5,3,3 => (⟨36,by decide⟩,⟨44,by decide⟩)
 | 5,3,5 => (⟨9,by decide⟩,⟨41,by decide⟩)
 | 5,8,5 => (⟨256,by decide⟩,⟨288,by decide⟩)
 | 5,8,8 => (⟨32,by decide⟩,⟨288,by decide⟩)
 | _,_,0 => (⟨2,by decide⟩,⟨3,by decide⟩)
 | _,_,1 => (⟨1,by decide⟩,⟨3,by decide⟩)
 | _,_,2 => (⟨2,by decide⟩,⟨6,by decide⟩)
 | _,_,3 => (⟨4,by decide⟩,⟨12,by decide⟩)
 | _,_,4 => (⟨1,by decide⟩,⟨17,by decide⟩)
 | _,_,5 => (⟨1,by decide⟩,⟨33,by decide⟩)
 | _,_,6 => (⟨2,by decide⟩,⟨66,by decide⟩)
 | _,_,7 => (⟨4,by decide⟩,⟨132,by decide⟩)
 | _,_,8 => (⟨8,by decide⟩,⟨264,by decide⟩)
 | _,_,_ => (⟨0,by decide⟩,⟨0,by decide⟩)
def z12: Sig:=neg (inputs.getD 0 zero)
def w31 (a b: Nat): Sig:=bin true (inputs.getD a zero) (inputs.getD b zero)
def y74 (a b: Nat): List Sig:=inputs ++ [z12,w31 a b]
def v19: List Sig:=(inputs.erase (inputs.getD 0 zero)) ++ [z12]
def v52 (a b: Nat): List Sig:=(inputs.erase (inputs.getD 0 zero)) ++ [z12,w31 a b]
lemma z34 (x: Fin 9->Bool) :
   g5 x=Binary.v7.yk Binary.v7.edges x:=by
 unfold g5 Binary.v7.yk Binary.v7.edges
 simp [List.any_cons,List.any_nil,Bool.or_assoc]
lemma qx :
   ([1,5]: List Nat).all (fun a =>
     ([2,3,8]: List Nat).all (fun b =>
       ([1,2,3,4,5,6,7,8]: List Nat).all (fun i =>
         let p:=w40 a b i
         (bit p.1 d4 != bit p.2 d4) &&
         (y74 a b).all (fun w => w == inputs.getD i zero||bit p.1 w == bit p.2 w))))=true:=by decide +kernel
lemma qd :
   ([1,5]: List Nat).all (fun a =>
     ([2,3,8]: List Nat).all (fun b =>
       let p:=w40 a b 0
       (bit p.1 d4 != bit p.2 d4) &&
       (y74 a b).all (fun w => w == inputs.getD 0 zero||w == z12||bit p.1 w == bit p.2 w)))=true:=by decide +kernel
lemma z62 (ci: w8) (hmem: zq.cols.values.contains ci=true) :
   j5 (f3 511) d4 ⟨c7 ci.1 ci.2.1,ci.2.2.2.2,0,f3 511⟩:=by
 have hgd:=z54
 simp only [w5,Bool.and_eq_true,List.all_eq_true] at hgd
 have hslice:=m50 ci (q7 yf) (m4 yf z40) (hgd.1.2 ci (List.contains_iff_mem.mp hmem))
 have htgt: g4 zq.mask=d4:=by decide +kernel
 rw [htgt] at hslice
 exact m37 (cs:=[]) hslice rfl
lemma cp31 (ci: w8) (head: Sig) (rest: List Sig)
   (hmem: zq.cols.values.contains ci=true)
   (heq: y4 (0,head,head)=head)
   (hnd0: decide (head :: rest).Nodup=true)
   (hcut: v5 ⟨c7 ci.1 ci.2.1,ci.2.2.2.2,0,f3 511⟩ 13 rest (0,head,head)=true) :
   x2 d4 13 (head :: rest).toFinset:=by
 have hvp:=z62 ci hmem
 have hnd: (y4 (0,head,head) :: rest).Nodup:=by
   rw [heq]; exact of_decide_eq_true hnd0
 have himp:=m9 hvp hnd hcut
 rwa [heq] at himp
lemma r31 (idx: Nat) (hi: idx < 10) :
   I1 d4 13 1 (sS pL 40 idx).toFinset:=by
 have hall:=w96 pL pI0 pI1 13 (q7 yf)
   (m4 yf z40) z54 v18 13 (by decide) 1 (by decide) idx hi
 have htgt: x0 zq=d4:=by decide +kernel
 rwa [htgt] at hall
lemma pk31: yp d4 ((zq.autos.getD 1 []).map f1)=true:=by decide +kernel
lemma v49: x2 d4 13 (inputs.getD 0 zero :: inputs.erase (inputs.getD 0 zero)).toFinset :=
 cp31 (16,0,495,0,13) (inputs.getD 0 zero) (inputs.erase (inputs.getD 0 zero)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
lemma v54: x2 d4 13 (z12 :: inputs).toFinset :=
 cp31 (1,0,510,0,12) z12 inputs (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
lemma v51: I1 d4 13 1 v19.toFinset:=by
 have h:=r31 0 (by decide)
 have hs: c8 (sS pL 40 0) v19=true:=by decide +kernel
 rwa [m11 hs] at h
lemma xf (idx: Nat) (hi: idx < 10) (ws: List Sig) (hs: c8 (sS pL 40 idx) ws=true) :
   I1 d4 13 1 ws.toFinset:=by
 have h:=r31 idx hi
 rwa [m11 hs] at h
lemma zf (idx: Nat) (hi: idx < 10) (ws: List Sig)
   (hs: c8 ((sS pL 40 idx).map (y7 ((zq.autos.getD 1 []).map f1).reverse)) ws=true) :
   I1 d4 13 1 ws.toFinset:=by
 have h:=re1 (r31 idx hi) ((zq.autos.getD 1 []).map f1) pk31
 rwa [m11 hs] at h
lemma v48 (a b: Nat) (ha: a ∈ ([1,5]: List Nat)) (hb: b ∈ ([2,3,8]: List Nat)) :
   I1 d4 13 1 (w31 a b :: inputs).toFinset:=by
 simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hb
 rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl
 · exact xf 1 (by decide) _ (by decide +kernel)
 · exact xf 4 (by decide) _ (by decide +kernel)
 · exact xf 7 (by decide) _ (by decide +kernel)
 · exact zf 7 (by decide) _ (by decide +kernel)
 · exact zf 4 (by decide) _ (by decide +kernel)
 · exact zf 1 (by decide) _ (by decide +kernel)
lemma v50 (a b: Nat) (ha: a ∈ ([1,5]: List Nat)) (hb: b ∈ ([2,3,8]: List Nat)) :
   I1 d4 13 1 (v52 a b).toFinset:=by
 simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hb
 rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl
 · exact xf 2 (by decide) _ (by decide +kernel)
 · exact xf 5 (by decide) _ (by decide +kernel)
 · exact xf 8 (by decide) _ (by decide +kernel)
 · exact zf 8 (by decide) _ (by decide +kernel)
 · exact zf 5 (by decide) _ (by decide +kernel)
 · exact zf 2 (by decide) _ (by decide +kernel)
lemma v53 (a b: Nat) (ha: a ∈ ([1,5]: List Nat)) (hb: b ∈ ([2,3,8]: List Nat)) :
   I1 d4 13 1 (w31 a b :: z12 :: inputs).toFinset:=by
 simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hb
 rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl
 · exact xf 3 (by decide) _ (by decide +kernel)
 · exact xf 6 (by decide) _ (by decide +kernel)
 · exact xf 9 (by decide) _ (by decide +kernel)
 · exact zf 9 (by decide) _ (by decide +kernel)
 · exact zf 6 (by decide) _ (by decide +kernel)
 · exact zf 3 (by decide) _ (by decide +kernel)
lemma jx {T k t S} (h: j6 T k t S) (r1 r2: Row)
   (hs: ∀ v ∈ S,bit r1 v=bit r2 v): bit r1 T=bit r2 T:=by
 induction h using j6.recurse with
 | stop => exact hs _ (Finset.mem_singleton_self _)
 | unary _ _ _ ih =>
   apply ih; intro v hv; simp only [Finset.mem_insert] at hv
   rcases hv with rfl | hv
   · simp only [zz,hs _ (Finset.mem_insert_self _ _)]
   · exact hs _ (Finset.mem_insert_of_mem hv)
 | binary _ _ _ _ _ ih =>
   apply ih; intro v hv; simp only [Finset.mem_insert] at hv
   rcases hv with rfl | hv
   · simp only [p0,hs _ (Finset.mem_insert_self _ _),
       hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))]
   · exact hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
lemma x26 {a b: Nat} (ha: a ∈ ([1,5]: List Nat)) (hb: b ∈ ([2,3,8]: List Nat))
   {k t S} (hk: k ≤ 13) (ht: t ≤ 1) (h: j6 d4 k t S) (sub: ∀ v ∈ S,v ∈ y74 a b): False:=by
 have hother: ∀ i: Fin 9,i.val ≠ 0->inputs.getD i.val zero ∈ S:=by
   intro i hi
   have hiMem: i.val ∈ ([1,2,3,4,5,6,7,8]: List Nat):=by simp; omega
   have h0:=List.all_eq_true.mp qx a ha
   have h1:=List.all_eq_true.mp h0 b hb
   have hh:=List.all_eq_true.mp h1 i.val hiMem
   simp only [Bool.and_eq_true,bne_iff_ne] at hh
   have h2:=List.all_eq_true.mp hh.2
   exact m32 h _ _ sub (w40 a b i.val).1 (w40 a b i.val).2 hh.1 (fun w hw hn => by
     have ha':=h2 w hw
     have hne: (w == inputs.getD i.val zero)=false:=beq_eq_false_iff_ne.mpr hn
     rw [hne] at ha'; simp only [Bool.false_or] at ha'; exact beq_iff_eq.mp ha')
 have hzero: inputs.getD 0 zero ∈ S ∨ z12 ∈ S:=by
   by_contra hneither
   push Not at hneither
   have h0:=List.all_eq_true.mp qd a ha
   have hh:=List.all_eq_true.mp h0 b hb
   simp only [Bool.and_eq_true,bne_iff_ne] at hh
   have h2:=List.all_eq_true.mp hh.2
   have hsub: ∀ v ∈ S,bit (w40 a b 0).1 v=bit (w40 a b 0).2 v:=by
     intro v hv
     have ha':=h2 v (sub v hv)
     have hn1: (v == inputs.getD 0 zero)=false:=beq_eq_false_iff_ne.mpr (fun e => hneither.1 (e ▸ hv))
     have hn2: (v == z12)=false:=beq_eq_false_iff_ne.mpr (fun e => hneither.2 (e ▸ hv))
     rw [hn1,hn2] at ha'; simp only [Bool.false_or] at ha'; exact beq_iff_eq.mp ha'
   exact hh.1 (jx h _ _ hsub)
 by_cases h0: inputs.getD 0 zero ∈ S
 · have haveIn: inputs.toFinset ⊆ S:=by
     intro v hv
     have hm:=List.mem_toFinset.mp hv
     rw [← m38,List.mem_ofFn] at hm
     obtain ⟨i,rfl⟩:=hm
     by_cases hi: i.val=0
     · rw [hi]; exact h0
     · exact hother i hi
   by_cases h9: z12 ∈ S
   · by_cases h10: w31 a b ∈ S
     · have eqS: S=(w31 a b :: z12 :: inputs).toFinset:=by
         apply Finset.Subset.antisymm
         · intro v hv
           have hm:=sub v hv
           simp only [y74,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
           rcases hm with hm | rfl | rfl <;> simp [*]
         · intro v hv
           simp only [List.toFinset_cons,Finset.mem_insert] at hv
           rcases hv with rfl | rfl | hv
           · exact h10
           · exact h9
           · exact haveIn hv
       exact v53 a b ha hb k t hk ht (eqS ▸ h)
     · have eqS: S=(z12 :: inputs).toFinset:=by
         apply Finset.Subset.antisymm
         · intro v hv
           have hm:=sub v hv
           simp only [y74,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
           rcases hm with hm | rfl | rfl
           · simp [hm]
           · simp
           · exact False.elim (h10 hv)
         · intro v hv
           simp only [List.toFinset_cons,Finset.mem_insert] at hv
           rcases hv with rfl | hv
           · exact h9
           · exact haveIn hv
       exact v54 k t hk (eqS ▸ h)
   · by_cases h10: w31 a b ∈ S
     · have eqS: S=(w31 a b :: inputs).toFinset:=by
         apply Finset.Subset.antisymm
         · intro v hv
           have hm:=sub v hv
           simp only [y74,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
           rcases hm with hm | rfl | rfl
           · simp [hm]
           · exact False.elim (h9 hv)
           · simp
         · intro v hv
           simp only [List.toFinset_cons,Finset.mem_insert] at hv
           rcases hv with rfl | hv
           · exact h10
           · exact haveIn hv
       exact v48 a b ha hb k t hk ht (eqS ▸ h)
     · have eqS: S=(inputs.getD 0 zero :: inputs.erase (inputs.getD 0 zero)).toFinset:=by
         apply Finset.Subset.antisymm
         · intro v hv
           have hm:=sub v hv
           simp only [y74,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
           rcases hm with hm | rfl | rfl
           · by_cases hv0: v=inputs.getD 0 zero
             · subst hv0; simp
             · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ((List.mem_erase_of_ne hv0).mpr hm))
           · exact False.elim (h9 hv)
           · exact False.elim (h10 hv)
         · intro v hv
           simp only [List.toFinset_cons,Finset.mem_insert] at hv
           rcases hv with rfl | hv
           · exact h0
           · exact haveIn (List.mem_toFinset.mpr (List.mem_of_mem_erase (List.mem_toFinset.mp hv)))
       exact v49 k t hk (eqS ▸ h)
 · have h9: z12 ∈ S:=hzero.resolve_left h0
   have hnd: inputs.Nodup:=of_decide_eq_true (by decide +kernel: decide inputs.Nodup=true)
   have hbaseSub: (inputs.erase (inputs.getD 0 zero)).toFinset ⊆ S:=by
     intro v hv
     have hm:=List.mem_toFinset.mp hv
     have hm':=List.mem_of_mem_erase hm
     have hne0: v ≠ inputs.getD 0 zero:=fun e => hnd.not_mem_erase (e ▸ hm)
     rw [← m38,List.mem_ofFn] at hm'
     obtain ⟨i,rfl⟩:=hm'
     exact hother i (fun hi => hne0 (by rw [hi]))
   by_cases h10: w31 a b ∈ S
   · have eqS: S=(v52 a b).toFinset:=by
       apply Finset.Subset.antisymm
       · intro v hv
         have hm:=sub v hv
         simp only [y74,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
         rcases hm with hm | rfl | rfl
         · have hne: v ≠ inputs.getD 0 zero:=fun e => h0 (e ▸ hv)
           exact List.mem_toFinset.mpr (List.mem_append_left _ ((List.mem_erase_of_ne hne).mpr hm))
         · exact List.mem_toFinset.mpr (List.mem_append_right _ (by simp))
         · exact List.mem_toFinset.mpr (List.mem_append_right _ (by simp))
       · intro v hv
         have hm:=List.mem_toFinset.mp hv
         simp only [v52,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
         rcases hm with hm | rfl | rfl
         · exact hbaseSub (List.mem_toFinset.mpr hm)
         · exact h9
         · exact h10
     exact v50 a b ha hb k t hk ht (eqS ▸ h)
   · have eqS: S=v19.toFinset:=by
       apply Finset.Subset.antisymm
       · intro v hv
         have hm:=sub v hv
         simp only [y74,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hm
         rcases hm with hm | rfl | rfl
         · have hne: v ≠ inputs.getD 0 zero:=fun e => h0 (e ▸ hv)
           exact List.mem_toFinset.mpr (List.mem_append_left _ ((List.mem_erase_of_ne hne).mpr hm))
         · exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
         · exact False.elim (h10 hv)
       · intro v hv
         have hm:=List.mem_toFinset.mp hv
         simp only [v19,List.mem_append,List.mem_singleton] at hm
         rcases hm with hm | rfl
         · exact hbaseSub (List.mem_toFinset.mpr hm)
         · exact h9
     exact v51 k t hk ht (eqS ▸ h)
lemma qj (a b: Nat) (ha: a ∈ ([1,5]: List Nat)) (hb: b ∈ ([2,3,8]: List Nat))
   (C: Circuit) (legal: PEqualNP.MetaComplexity.FanInTwo C) (hsz: C.size ≤ 13)
   (hno: ∀ x: Fin 9->Bool,
     let x9:=List.ofFn x ++ [!x 0]
     C.eval (x9 ++ [x9.getD a false||x9.getD b false])=g5 x): False:=by
 let g0: Gate:=⟨.not,[0]⟩
 let g1: Gate:=⟨.or,[a,b]⟩
 let Cfull: Circuit:=⟨g0 :: g1 :: C.gates,C.output⟩
 have hfanFull: PEqualNP.MetaComplexity.FanInTwo Cfull:=by
   intro g hg
   rcases List.mem_cons.mp hg with rfl | hg
   · exact ⟨by simp [g0],by simp [g0]⟩
   · rcases List.mem_cons.mp hg with rfl | hg
     · exact ⟨by simp [g1],by simp [g1]⟩
     · exact legal g hg
 have hstep (x: Fin 9->Bool) :
     Cfull.eval (List.ofFn x) =
       (let x9:=List.ofFn x ++ [!x 0]; C.eval (x9 ++ [x9.getD a false||x9.getD b false])):=by
   simp only [Circuit.eval,Circuit.wires,Cfull,List.foldl_cons,g0,g1,GateOp.eval,
     List.map_cons,List.map_nil,List.headD,List.any_cons,List.any_nil,id,Bool.or_false]
   have h0: (List.ofFn x).getD 0 false=x 0:=by
     rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp
   rw [h0]
 have hcomp: ∀ x: Fin 9->Bool,Cfull.eval (List.ofFn x)=Binary.v7.yk Binary.v7.edges x:=by
   intro x; rw [hstep x]; exact (hno x).trans (z34 x)
 have hlow:=Binary.petersen_binary_lower Cfull hfanFull hcomp
 have hnn: Binary.z2.z6 Cfull.gates=1+Binary.z2.z6 C.gates:=by
   change List.countP (fun q => !Binary.z2.q6 q.op) (g0 :: g1 :: C.gates) =
     1+List.countP (fun q => !Binary.z2.q6 q.op) C.gates
   rw [List.countP_cons,List.countP_cons]
   have h0: (!Binary.z2.q6 g0.op)=false:=rfl
   have h1: (!Binary.z2.q6 g1.op)=true:=rfl
   rw [h0,h1]; simp; omega
 rw [hnn] at hlow
 have hbound:=Binary.nonNotCount_add_notCount C.gates
 change Binary.z2.z6 C.gates+(C.gates.filter fun q => Binary.z2.q6 q.op).length=C.gates.length at hbound
 have hfeq: (fun q: Gate => yc q.op)=(fun q: Gate => Binary.z2.q6 q.op):=by
   funext q; cases q.op <;> rfl
 have hcntEq: C.gates.countP (fun q => yc q.op)=(C.gates.filter fun q => Binary.z2.q6 q.op).length:=by
   rw [List.countP_eq_length_filter,hfeq]
 have hlen: C.gates.length ≤ 13:=hsz
 have ht1: C.gates.countP (fun q => yc q.op) ≤ 1:=by omega
 have hbit_neg0 (r: Row): bit r z12=!(p3 r 0):=by simp only [z12,zz,p3]; rfl
 have hgetD_x9 (r: Row) (idx: Nat) (hidx: idx < 9) :
     ((List.ofFn (p3 r) ++ [!p3 r 0]).getD idx false)=bit r (inputs.getD idx zero):=by
   rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp [hidx]),List.getElem?_ofFn]
   simp [hidx,p3]
 have ha9: a < 9:=by simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha; rcases ha with rfl | rfl <;> omega
 have hb9: b < 9:=by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hb; rcases hb with rfl | rfl | rfl <;> omega
 let bank: List Sig:=y74 a b
 have goalEq: (xq C.gates bank).getD C.output zero=d4:=by
   apply BitVec.eq_of_getLsbD_eq
   intro m hm
   let r: Row:=⟨m,hm⟩
   change bit r ((xq C.gates bank).getD C.output zero)=bit r d4
   rw [← x64,m47 _ _ _ (fun g hg => (legal g hg).1)]
   have hmap: bank.map (bit r) =
       (List.ofFn (p3 r) ++ [!p3 r 0]) ++
       [(List.ofFn (p3 r) ++ [!p3 r 0]).getD a false ||
        (List.ofFn (p3 r) ++ [!p3 r 0]).getD b false]:=by
     simp only [bank,y74,List.map_append,List.map_cons,List.map_nil,← x69,hbit_neg0,w31,p0,ite_true]
     rw [hgetD_x9 r a ha9,hgetD_x9 r b hb9]; rfl
   rw [hmap]
   exact (hno (p3 r)).trans (z95 r).symm
 have out:=yv (xq C.gates bank) C.output
 rw [goalEq] at out
 have targetIn:=out.resolve_right (fun hn => hn m76)
 obtain ⟨k,t,S,hk,ht,run,hs⟩:=x43 C.gates bank legal m76 targetIn
 exact x26 ha hb (hk.trans hlen) (ht.trans ht1) run hs
lemma main3174 (pins: List Nat) (len: pins.length=2)
   (bounds: ∀ x3 ∈ pins,x3=1 ∨ x3=2 ∨ x3=3 ∨ x3=5 ∨ x3=8)
   (splitC: (¬∀ x4 ∈ pins,x4=1 ∨ x4=5) ∧ ¬∀ x4 ∈ pins,x4=2 ∨ x4=3 ∨ x4=8)
   (C: Circuit) (hc: PEqualNP.MetaComplexity.FanInTwo C) (hs: C.size ≤ 13) :
   ∃ x8: Fin 9->Bool,
     have x9: List Bool:=List.ofFn x8 ++ [!x8 0];
     C.eval (x9 ++ [GateOp.or.eval (List.map (fun x10: Nat => x9.getD x10 false) pins)]) ≠ g5 x8:=by
 by_contra hno; push Not at hno
 obtain ⟨u,v,rfl⟩: ∃ u v: Nat,pins=[u,v]:=by
   cases pins with
   | nil => simp at len
   | cons u rest =>
     cases rest with
     | nil => simp at len
     | cons v tail =>
       have h: tail=[]:=List.length_eq_zero_iff.mp (by simpa using len)
       exact ⟨u,v,by simp [h]⟩
 have hu:=bounds u (by simp)
 have hv:=bounds v (by simp)
 have hconv (x: Fin 9->Bool) :
     let x9:=List.ofFn x ++ [!x 0]
     C.eval (x9 ++ [x9.getD u false||x9.getD v false])=g5 x:=by
   have h:=Classical.byContradiction (hno x)
   simpa only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id,Bool.or_false,g5] using h
 have hconv_sw (x: Fin 9->Bool) :
     let x9:=List.ofFn x ++ [!x 0]
     C.eval (x9 ++ [x9.getD v false||x9.getD u false])=g5 x:=by
   have h:=hconv x
   simpa only [Bool.or_comm] using h
 have hcases: (u ∈ ([1,5]: List Nat) ∧ v ∈ ([2,3,8]: List Nat)) ∨ (v ∈ ([1,5]: List Nat) ∧ u ∈ ([2,3,8]: List Nat)):=by
   rcases splitC with ⟨hnot15,hnot238⟩
   rcases hu with rfl | rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp_all
 rcases hcases with ⟨h1,h2⟩ | ⟨h1,h2⟩
 · exact qj u v h1 h2 C hc hs hconv
 · exact qj v u h1 h2 C hc hs hconv_sw
end PEqualNP.Outside.L_meta_3174
theorem PEqualNP.Outside.L_meta_3174 : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3174.main3174
